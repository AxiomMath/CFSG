module

public import CFSG.Sporadic.Recognition.LyonsAS44Delta
public import CFSG.Sporadic.Recognition.LyonsAS44Gen
public import CFSG.Sporadic.Recognition.LyonsAS44DeltaGen

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

section Pts

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

omit [Finite G] in
theorem x₁_pow_three (S : LyStd ρ x₁ x₂ x₃) : (x₁ : G) ^ 3 = 1 := by
  simpa using congrArg Subtype.val S.pow₁

namespace LyData

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

omit [Finite G] in
theorem isConj_x₁_inv : IsConj (x₁ : G) (x₁ : G)⁻¹ := by
  obtain ⟨s, -, -, hs, -⟩ := F.inv
  exact isConj_iff.2 ⟨s, hs⟩

omit [Finite G] in
theorem Y_ne_one (i : Fin 10) : Y i ≠ 1 := by
  intro h
  have hc := F.mcl.norm.isConj i
  rw [h] at hc
  have h1 := isConj_one_left.1 hc
  have := D.orderOf_x₂Q S
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

noncomputable def zlift (i : Fin 10) : ↥(centralizer ({(x₁ : G)} : Set G)) :=
  Classical.choose (D.exists_lift_isConj S (F.mcl.norm.isConj i))

omit [Finite G] in
theorem zlift_proj (i : Fin 10) : projQ (x₁ : G) (D.zlift S F i) = Y i :=
  (Classical.choose_spec (D.exists_lift_isConj S (F.mcl.norm.isConj i))).1

omit [Finite G] in
theorem zlift_isConj (i : Fin 10) : IsConj (x₁ : G) (D.zlift S F i : G) :=
  (Classical.choose_spec (D.exists_lift_isConj S (F.mcl.norm.isConj i))).2

omit [Finite G] in
theorem zlift_mem (i : Fin 10) : (D.zlift S F i : G) ∈ preimQ (x₁ : G) A :=
  mem_preimQ.2 ⟨(D.zlift S F i).2, by
    rw [Subtype.coe_eta, D.zlift_proj S F]; exact F.mcl.norm.mem_A i⟩

theorem isConj_proj_of_isConj {u : ↥(centralizer ({(x₁ : G)} : Set G))}
    (hu : IsConj (x₁ : G) (u : G)) (h1 : projQ (x₁ : G) u ≠ 1) :
    IsConj (D.x₂Q S) (projQ (x₁ : G) u) := by
  obtain ⟨m, hm⟩ := D.exists_conj_eq_x₂ S F hu h1
  refine isConj_iff.2 ⟨projQ (x₁ : G) m, ?_⟩
  have : u = m * D.x₂M S * m⁻¹ := Subtype.ext (by simpa [LyData.x₂M] using hm)
  rw [this, map_mul, map_mul, map_inv]
  rfl

theorem mem_SG_iff (w : G) :
    (w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w) ↔
      w = (x₁ : G) ∨ w = (x₁ : G)⁻¹ ∨
        ∃ i, w = (D.zlift S F i : G) ∨ w = (D.zlift S F i : G)⁻¹ := by
  have hx3G := x₁_pow_three S
  constructor
  · rintro ⟨hwA, hwc⟩
    obtain ⟨hwM, hwq⟩ := mem_preimQ.1 hwA
    by_cases h1 : projQ (x₁ : G) ⟨w, hwM⟩ = 1
    · have hker : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈ (projQ (x₁ : G)).ker := h1
      rw [ker_projQ] at hker
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hker
      have hwj : w = (x₁ : G) ^ j := by
        have := congrArg Subtype.val hj
        simpa using this.symm
      rcases zpow_cases hx3G j with h | h | h
      · exfalso
        rw [hwj, h] at hwc
        have h1' : (x₁ : G) = 1 := isConj_one_left.1 hwc
        have h3 := orderOf_x₁ S
        rw [h1', orderOf_one] at h3
        exact absurd h3 (by norm_num)
      · exact Or.inl (hwj.trans h)
      · refine Or.inr (Or.inl ?_)
        rw [hwj, h]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx3G)
    · have hy := D.isConj_proj_of_isConj S F hwc h1
      obtain ⟨i, hi | hi⟩ := F.mcl.norm.cover _ hwq hy
      · have := D.eq_of_isConj_of_proj_eq S F (u := ⟨w, hwM⟩) (v := D.zlift S F i) hwc
          (D.zlift_isConj S F i) (by rw [hi, D.zlift_proj S F]) h1
        exact Or.inr (Or.inr ⟨i, Or.inl (congrArg Subtype.val this)⟩)
      · have hwinv : IsConj (x₁ : G) (w⁻¹) :=
          isConj_inv_of_isConj hwc (D.isConj_x₁_inv S F)
        have := D.eq_of_isConj_of_proj_eq S F (u := (⟨w, hwM⟩ : ↥(centralizer
          ({(x₁ : G)} : Set G)))⁻¹) (v := D.zlift S F i) hwinv (D.zlift_isConj S F i)
          (by rw [map_inv, hi, inv_inv, D.zlift_proj S F])
          (by rw [map_inv, hi, inv_inv]; exact D.Y_ne_one S F i)
        refine Or.inr (Or.inr ⟨i, Or.inr ?_⟩)
        have h2 := congrArg Subtype.val this
        simp only [Subgroup.coe_inv] at h2
        rw [← h2]; simp
  · rintro (rfl | rfl | ⟨i, rfl | rfl⟩)
    · exact ⟨x_mem_preimQ A, IsConj.refl _⟩
    · exact ⟨Subgroup.inv_mem _ (x_mem_preimQ A), D.isConj_x₁_inv S F⟩
    · exact ⟨D.zlift_mem S F i, D.zlift_isConj S F i⟩
    · exact ⟨Subgroup.inv_mem _ (D.zlift_mem S F i),
        isConj_inv_of_isConj (D.zlift_isConj S F i) (D.isConj_x₁_inv S F)⟩

omit [Finite G] in
theorem card_AG : Nat.card ↥(preimQ (x₁ : G) A) = 243 := by
  rw [card_preimQ, orderOf_x₁ S, F.mcl.A_card]

omit [Finite G] in
theorem AG_comm : ∀ a ∈ preimQ (x₁ : G) A, ∀ b ∈ preimQ (x₁ : G) A, a * b = b * a := by
  obtain ⟨s, -, -, -, hs⟩ := F.inv
  exact comm_of_inverted hs

omit [Finite G] in
theorem AG_eq_closure : preimQ (x₁ : G) A =
    closure {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} := by
  apply le_antisymm
  · set N : Subgroup G := closure {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} with hN
    have hx₁N : (x₁ : G) ∈ N := subset_closure ⟨x_mem_preimQ A, IsConj.refl _⟩
    have hA1 : A ≤ closure {q : CentQuot (x₁ : G) | ∃ i, q = Y i ∨ q = (Y i)⁻¹} := by
      conv_lhs => rw [F.mcl.A_gen]
      apply (closure_le _).2
      rintro z ⟨hzT, hzc⟩
      have hzA : z ∈ A := F.mcl.A_gen ▸ subset_closure ⟨hzT, hzc⟩
      exact subset_closure (F.mcl.norm.cover z hzA hzc)
    have hlift : ∀ q ∈ closure {q : CentQuot (x₁ : G) | ∃ i, q = Y i ∨ q = (Y i)⁻¹},
        ∃ n : ↥(centralizer ({(x₁ : G)} : Set G)), (n : G) ∈ N ∧ projQ (x₁ : G) n = q := by
      intro q hq
      induction hq using Subgroup.closure_induction with
      | mem q hq =>
        obtain ⟨i, rfl | rfl⟩ := hq
        · exact ⟨D.zlift S F i, subset_closure ⟨D.zlift_mem S F i, D.zlift_isConj S F i⟩,
            D.zlift_proj S F i⟩
        · refine ⟨(D.zlift S F i)⁻¹, ?_, by rw [map_inv, D.zlift_proj S F]⟩
          exact Subgroup.inv_mem _ (subset_closure ⟨D.zlift_mem S F i, D.zlift_isConj S F i⟩)
      | one => exact ⟨1, one_mem _, map_one _⟩
      | mul q₁ q₂ _ _ h₁ h₂ =>
        obtain ⟨n₁, hn₁, rfl⟩ := h₁
        obtain ⟨n₂, hn₂, rfl⟩ := h₂
        exact ⟨n₁ * n₂, Subgroup.mul_mem _ hn₁ hn₂, map_mul _ _ _⟩
      | inv q _ h =>
        obtain ⟨n, hn, rfl⟩ := h
        exact ⟨n⁻¹, Subgroup.inv_mem _ hn, map_inv _ _⟩
    intro a ha
    obtain ⟨haM, haq⟩ := mem_preimQ.1 ha
    obtain ⟨n, hn, hnq⟩ := hlift _ (hA1 haq)
    have hker : (⟨a, haM⟩ : ↥(centralizer ({(x₁ : G)} : Set G)))⁻¹ * n ∈ (projQ (x₁ : G)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnq, inv_mul_cancel]
    rw [ker_projQ] at hker
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hker
    have hj' : (x₁ : G) ^ j = a⁻¹ * (n : G) := by
      have := congrArg Subtype.val hj
      simpa using this
    have : a = (n : G) * ((x₁ : G) ^ j)⁻¹ := by
      rw [hj']; group
    rw [this]
    exact Subgroup.mul_mem _ hn (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hx₁N j))
  · exact (closure_le _).2 fun w hw => hw.1

omit [Finite G] in
theorem AG_pow_three : ∀ a ∈ preimQ (x₁ : G) A, a ^ 3 = 1 := by
  have hcomm := D.AG_comm S F
  intro a ha
  have ha' : a ∈ closure {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} :=
    (D.AG_eq_closure S F).le ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem w hw => exact pow_three_of_isConj_x₁ S hw.2
  | one => simp
  | mul a b ha hb iha ihb =>
    have haA : a ∈ preimQ (x₁ : G) A := (D.AG_eq_closure S F).ge ha
    have hbA : b ∈ preimQ (x₁ : G) A := (D.AG_eq_closure S F).ge hb
    rw [(show Commute a b from hcomm a haA b hbA).mul_pow, iha, ihb, one_mul]
  | inv a ha iha =>
    rw [inv_pow, iha, inv_one]

omit [Finite G] in
theorem card_TG : Nat.card ↥(preimQ (x₁ : G) T) = 3 ^ 7 := by
  rw [card_preimQ, orderOf_x₁ S, F.mcl.T_card]
  norm_num

theorem mem_AG_of_mem_TG {w : G} (hw : w ∈ preimQ (x₁ : G) T) (hc : IsConj (x₁ : G) w) :
    w ∈ preimQ (x₁ : G) A := by
  obtain ⟨hwM, hwT⟩ := mem_preimQ.1 hw
  have hyA : D.x₂Q S ∈ A := by
    have := F.mcl.norm.mem_A 0
    rwa [F.mcl.norm.zero] at this
  by_cases h1 : projQ (x₁ : G) ⟨w, hwM⟩ = 1
  · have hker : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈ (projQ (x₁ : G)).ker := h1
    rw [ker_projQ] at hker
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hker
    have hwj : w = (x₁ : G) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    rw [hwj]
    exact Subgroup.zpow_mem _ (x_mem_preimQ A) j
  · have hq3 : projQ (x₁ : G) ⟨w, hwM⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using pow_three_of_isConj_x₁ S hc)
      rw [this, map_one]
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf (projQ (x₁ : G) ⟨w, hwM⟩) = 3 := orderOf_eq_prime hq3 h1
    have hy := D.isConj_proj_of_isConj S F hc h1
    rcases F.mcl.order_three _ hwT hord with hR | hAA
    · rcases F.mcl.weakly_closed _ hR hy with h | h
      · exact mem_preimQ.2 ⟨hwM, by rw [h]; exact hyA⟩
      · exact mem_preimQ.2 ⟨hwM, by rw [h]; exact Subgroup.inv_mem _ hyA⟩
    · exact mem_preimQ.2 ⟨hwM, hAA⟩

omit [Finite G] in
theorem zlift_pow_three (i : Fin 10) : (D.zlift S F i : G) ^ 3 = 1 :=
  pow_three_of_isConj_x₁ S (D.zlift_isConj S F i)

omit [Finite G] in
theorem zlift_ne_one (i : Fin 10) : (D.zlift S F i : G) ≠ 1 := by
  intro h
  have : D.zlift S F i = 1 := Subtype.ext h
  have hh := D.zlift_proj S F i
  rw [this, map_one] at hh
  exact D.Y_ne_one S F i hh.symm

omit [Finite G] in
theorem zlift_notMem_zpowers_x₁ (j : Fin 10) : (D.zlift S F j : G) ∉ zpowers (x₁ : G) := by
  rintro ⟨k, hk⟩
  apply D.Y_ne_one S F j
  rw [← D.zlift_proj S F j]
  have : D.zlift S F j = (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
      ↥(centralizer ({(x₁ : G)} : Set G))) ^ k := Subtype.ext (by simpa using hk.symm)
  rw [this, map_zpow, projQ_self, one_zpow]

@[expose] noncomputable def pt (i : Option (Fin 10)) : Subgroup G :=
  match i with
  | none => zpowers (x₁ : G)
  | some j => zpowers (D.zlift S F j : G)

omit [Finite G] in
theorem pt_injective : Function.Injective (D.pt S F) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rintro (_ | i) (_ | j) h
  · rfl
  · exfalso
    have h' : zpowers (x₁ : G) = zpowers (D.zlift S F j : G) := h
    have := (h' ▸ mem_zpowers (D.zlift S F j : G) : (D.zlift S F j : G) ∈ zpowers (x₁ : G))
    exact D.zlift_notMem_zpowers_x₁ S F j this
  · exfalso
    have h' : zpowers (D.zlift S F i : G) = zpowers (x₁ : G) := h
    exact D.zlift_notMem_zpowers_x₁ S F i (h' ▸ mem_zpowers (D.zlift S F i : G))
  · have h' : zpowers (D.zlift S F i : G) = zpowers (D.zlift S F j : G) := h
    rcases (zpowers_eq_iff (D.zlift_pow_three S F j) (D.zlift_ne_one S F j)).1 h' with h1 | h1
    · refine congrArg some (F.mcl.norm.distinct i j (Or.inl ?_))
      rw [← D.zlift_proj S F i, ← D.zlift_proj S F j, Subtype.ext h1]
    · refine congrArg some (F.mcl.norm.distinct i j (Or.inr ?_))
      rw [← D.zlift_proj S F i, ← D.zlift_proj S F j, ← map_inv]
      exact congrArg _ (Subtype.ext (by simpa using h1))

theorem deltaIn_AG_eq : deltaIn (x₁ : G) (preimQ (x₁ : G) A) = Set.range (D.pt S F) := by
  ext B
  rw [mem_deltaIn_iff]
  constructor
  · rintro ⟨w, hwc, hwA, rfl⟩
    rcases (D.mem_SG_iff S F w).1 ⟨hwA, hwc⟩ with rfl | rfl | ⟨i, rfl | rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨none, zpowers_inv.symm⟩
    · exact ⟨some i, rfl⟩
    · exact ⟨some i, zpowers_inv.symm⟩
  · rintro ⟨i | i, rfl⟩
    · exact ⟨(x₁ : G), IsConj.refl _, x_mem_preimQ A, rfl⟩
    · exact ⟨(D.zlift S F i : G), D.zlift_isConj S F i, D.zlift_mem S F i, rfl⟩

theorem ncard_deltaIn_AG : (deltaIn (x₁ : G) (preimQ (x₁ : G) A)).ncard = 11 := by
  rw [D.deltaIn_AG_eq S F, ← Set.image_univ, Set.ncard_image_of_injective _ (D.pt_injective S F),
    Set.ncard_univ]
  simp

theorem deltaIn_TG_eq :
    deltaIn (x₁ : G) (preimQ (x₁ : G) T) = deltaIn (x₁ : G) (preimQ (x₁ : G) A) := by
  ext B
  rw [mem_deltaIn_iff, mem_deltaIn_iff]
  constructor
  · rintro ⟨w, hwc, hwT, rfl⟩
    exact ⟨w, hwc, D.mem_AG_of_mem_TG S F hwT hwc, rfl⟩
  · rintro ⟨w, hwc, hwA, rfl⟩
    exact ⟨w, hwc, preimQ_mono F.mcl.A_le_T hwA, rfl⟩

end LyData

end Pts

end CFSG.Sporadic.Recognition.LyonsSims
