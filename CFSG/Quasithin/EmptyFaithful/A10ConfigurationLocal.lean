module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationSetup
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def A : Subgroup G := A1.map E.ι
@[expose] def B : Subgroup G := A2.map E.ι
@[expose] def A₃ : Subgroup G := A3.map E.ι
@[expose] def A₄ : Subgroup G := A4.map E.ι
@[expose] def J : Subgroup G := Jh.map E.ι
@[expose] def T₁ : Subgroup G := T1h.map E.ι
@[expose] def T₂ : Subgroup G := T2h.map E.ι
@[expose] def M₁ : Subgroup G := M1h.map E.ι
@[expose] def M₂ : Subgroup G := M2h.map E.ι
@[expose] def z : G := E.ι z0
@[expose] def t : G := E.ι t0
@[expose] def s : G := E.ι s0

theorem mem_M {x : G} : x ∈ M ↔ ∃ w, E.ι w = x :=
  (SetLike.ext_iff.mp E.range_eq x).symm.trans MonoidHom.mem_range

theorem le_range_of_le_M {H : Subgroup G} (h : H ≤ M) : H ≤ E.ι.range :=
  fun x hx => (SetLike.ext_iff.mp E.range_eq x).2 (h hx)

include E in
theorem T_le_M : T ≤ M := by
  intro x hx
  rw [← E.map_Th] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact E.mem_M.2 ⟨w, rfl⟩

theorem map_comap_of_le {H : Subgroup G} (h : H ≤ M) : (H.comap E.ι).map E.ι = H :=
  Subgroup.map_comap_eq_self (E.le_range_of_le_M h)

theorem isMaxElemAbelian_iff (H : Subgroup G) :
    IsMaxElemAbelian T H ↔ H = E.A ∨ H = E.B ∨ H = E.A₃ ∨ H = E.A₄ := by
  constructor
  · intro h
    have hHM : H ≤ M := h.1.trans E.T_le_M
    have h' : IsMaxElemAbelian Th (H.comap E.ι) := by
      rw [← isMaxElemAbelian_map_iff E.injective, E.map_comap_of_le hHM, E.map_Th]
      exact h
    have hH := E.map_comap_of_le hHM
    rcases (isMaxElemAbelian_Th_iff _).1 h' with h1 | h1 | h1 | h1
    · left; rw [← hH, h1]; rfl
    · right; left; rw [← hH, h1]; rfl
    · right; right; left; rw [← hH, h1]; rfl
    · right; right; right; rw [← hH, h1]; rfl
  · intro h
    have key : ∀ F : Subgroup Wc, IsMaxElemAbelian Th F → IsMaxElemAbelian T (F.map E.ι) :=
      fun F hF => by
        have := (isMaxElemAbelian_map_iff E.injective).2 hF
        rwa [E.map_Th] at this
    rcases h with rfl | rfl | rfl | rfl
    · exact key _ ((isMaxElemAbelian_Th_iff _).2 (Or.inl rfl))
    · exact key _ ((isMaxElemAbelian_Th_iff _).2 (Or.inr (Or.inl rfl)))
    · exact key _ ((isMaxElemAbelian_Th_iff _).2 (Or.inr (Or.inr (Or.inl rfl))))
    · exact key _ ((isMaxElemAbelian_Th_iff _).2 (Or.inr (Or.inr (Or.inr rfl))))

@[expose] noncomputable def eM : Wc ≃* ↥M :=
  (MonoidHom.ofInjective E.injective).trans (MulEquiv.subgroupCongr E.range_eq)

theorem subtype_comp_eM : M.subtype.comp E.eM.toMonoidHom = E.ι := rfl

theorem pCoreOf_M : pCoreOf 2 M = (CFSG.Open.pCore 2 Wc).map E.ι := by
  have h := map_pCore_mulEquiv 2 E.eM
  unfold pCoreOf
  rw [← h, Subgroup.map_map, E.subtype_comp_eM]

theorem A_eq_pCoreOf : E.A = pCoreOf 2 M := by
  rw [E.pCoreOf_M, pCore_Wc]
  rfl

theorem map_le_normalizer {H K : Subgroup Wc} (h : H ≤ Subgroup.normalizer (K : Set Wc)) :
    H.map E.ι ≤ Subgroup.normalizer ((K.map E.ι : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp (h hx) k).mp hk, ?_⟩
    simp
  · intro hy
    obtain ⟨k', hk', hk'eq⟩ := hy
    have hy' : y = E.ι (x⁻¹ * k' * x) := by
      simp only [map_mul, map_inv]
      rw [hk'eq]
      group
    rw [hy']
    refine ⟨x⁻¹ * k' * x, ?_, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (h (Subgroup.inv_mem _ hx)) k').mp hk'
    simpa using this

theorem T_le_normalizer_A : T ≤ Subgroup.normalizer (E.A : Set G) := by
  have := E.map_le_normalizer Th_le_normalizer_A1
  rwa [E.map_Th] at this

theorem T_le_normalizer_B : T ≤ Subgroup.normalizer (E.B : Set G) := by
  have := E.map_le_normalizer Th_le_normalizer_A2
  rwa [E.map_Th] at this

theorem J_eq_A_sup_B : E.J = E.A ⊔ E.B := by
  unfold J A B
  rw [Jh_eq_A1_sup_A2, Subgroup.map_sup]

theorem J_le_T : E.J ≤ T := by
  have := Subgroup.map_mono (f := E.ι) Jh_le_Th
  rwa [E.map_Th] at this

theorem T_le_normalizer_J : T ≤ Subgroup.normalizer (E.J : Set G) := by
  have := E.map_le_normalizer Th_le_normalizer_Jh
  rwa [E.map_Th] at this

theorem J_isPGroup [Finite G] : IsPGroup 2 E.J := (Th_isPGroup.to_le Jh_le_Th).map E.ι

theorem normalizer_J_inf_M {x : G} (hxM : x ∈ M) (hx : x ∈ Subgroup.normalizer (E.J : Set G)) :
    x ∈ T := by
  obtain ⟨w, rfl⟩ := E.mem_M.1 hxM
  have : w ∈ Subgroup.normalizer (Jh : Set Wc) := (mem_normalizer_map_iff E.injective).1 hx
  rw [normalizer_Jh] at this
  have h := Subgroup.mem_map_of_mem E.ι this
  rwa [E.map_Th] at h

theorem normalizer_A_eq_M [Finite G] (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.normalizer (E.A : Set G) = M := by
  have hA2 : IsPGroup 2 E.A := isPGroup_A1.map E.ι
  have hAne : E.A ≠ ⊥ := by
    intro h
    have h1 : Nat.card E.A = 16 := by
      unfold A
      rw [card_map_of_inj E.injective, card_A1]
    rw [h, Subgroup.card_bot] at h1
    omega
  have hloc : IsTwoLocal (Subgroup.normalizer (E.A : Set G)) := ⟨E.A, hAne, hA2, rfl⟩
  have hMle : M ≤ Subgroup.normalizer (E.A : Set G) := by
    rw [E.A_eq_pCoreOf]
    exact le_normalizer_pCoreOf 2 M
  exact hM.2 _ hloc hMle

@[expose] def Ai (i : Fin 4) : Subgroup G := (CFSG.Quasithin.A10.Ai i).map E.ι

theorem Ai_zero : E.Ai 0 = E.A := rfl
theorem Ai_one : E.Ai 1 = E.B := rfl
theorem Ai_two : E.Ai 2 = E.A₃ := rfl
theorem Ai_three : E.Ai 3 = E.A₄ := rfl

theorem Ai_le_J (i : Fin 4) : E.Ai i ≤ E.J := by
  fin_cases i
  · exact Subgroup.map_mono A1_le_Jh
  · exact Subgroup.map_mono A2_le_Jh
  · exact Subgroup.map_mono A3_le_Jh
  · exact Subgroup.map_mono A4_le_Jh

theorem card_Ai_inf_Ai (i j : Fin 4) : Nat.card ↥(E.Ai i ⊓ E.Ai j) = interCard i j := by
  unfold Ai
  rw [← Subgroup.map_inf _ _ E.ι E.injective, card_map_of_inj E.injective, card_Ai_inf]

theorem isMaxElemAbelian_Ai (i : Fin 4) : IsMaxElemAbelian T (E.Ai i) :=
  (E.isMaxElemAbelian_iff _).2 (by fin_cases i <;> simp [Ai_zero, Ai_one, Ai_two, Ai_three])

theorem normalizer_J_eq [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.normalizer (E.J : Set G) = T := by
  refine le_antisymm ?_ E.T_le_normalizer_J
  have hfour : ∀ x ∈ Subgroup.normalizer (E.J : Set G), x ^ 4 ∈ T := by
    intro x hx
    set c : G →* G := (MulAut.conj x).toMonoidHom with hc
    have hJ : E.J.map c = E.J := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
    have hconj : ∀ i : Fin 4, ∃ j : Fin 4, (E.Ai i).map c = E.Ai j := by
      intro i
      have hle : (E.Ai i).map c ≤ T :=
        ((Subgroup.map_mono (E.Ai_le_J i)).trans hJ.le).trans E.J_le_T
      have hmax := isMaxElemAbelian_map_conj (E.isMaxElemAbelian_Ai i) x hle
      rcases (E.isMaxElemAbelian_iff _).1 hmax with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    choose σ hσ using hconj
    have hperm : ∀ i j, interCard (σ i) (σ j) = interCard i j := by
      intro i j
      rw [← E.card_Ai_inf_Ai, ← E.card_Ai_inf_Ai, ← hσ, ← hσ, ← Subgroup.map_inf _ _ c
        (MulAut.conj x).injective, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have h4 := interCard_perm σ hperm
    have hA : ∀ i, (E.Ai i).map (MulAut.conj (x ^ 4)).toMonoidHom = E.Ai i := by
      intro i
      have : (MulAut.conj (x ^ 4)).toMonoidHom = c.comp (c.comp (c.comp c)) := by
        ext y
        simp only [hc, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply,
          MulEquiv.coe_toMonoidHom, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      rw [this, ← Subgroup.map_map, ← Subgroup.map_map, ← Subgroup.map_map, hσ, hσ, hσ, hσ, h4]
    have hxA : x ^ 4 ∈ Subgroup.normalizer (E.A : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hA 0)
    have hx4 : x ^ 4 ∈ Subgroup.normalizer (E.J : Set G) := pow_mem hx 4
    rw [E.normalizer_A_eq_M hM] at hxA
    exact E.normalizer_J_inf_M hxA hx4
  have hX2 : IsPGroup 2 (Subgroup.normalizer (E.J : Set G)) := by
    intro x
    obtain ⟨k, hk⟩ := hT.1 ⟨(x : G) ^ 4, hfour x.1 x.2⟩
    refine ⟨k + 2, ?_⟩
    have h1 : ((x : G) ^ 4) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have h2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
    rw [h2, pow_mul]
    exact h1
  exact (eq_of_le_isPGroup hT hX2 E.T_le_normalizer_J).le

theorem J_le_normalizer_Ai (i : Fin 4) : E.J ≤ Subgroup.normalizer (E.Ai i : Set G) := by
  fin_cases i
  · exact E.map_le_normalizer Jh_le_normalizer_A1
  · exact E.map_le_normalizer Jh_le_normalizer_A2
  · exact E.map_le_normalizer Jh_le_normalizer_A3
  · exact E.map_le_normalizer Jh_le_normalizer_A4

theorem A_le_J : E.A ≤ E.J := E.Ai_le_J 0
theorem B_le_J : E.B ≤ E.J := E.Ai_le_J 1
theorem A_le_T : E.A ≤ T := E.A_le_J.trans E.J_le_T
theorem B_le_T : E.B ≤ T := E.B_le_J.trans E.J_le_T

theorem conjSubgroup_Ai_le_J_of_le_T {i : Fin 4} {g : G} (hle : conjSubgroup (E.Ai i) g ≤ T) :
    conjSubgroup (E.Ai i) g ≤ E.J := by
  have hmax : IsMaxElemAbelian T (conjSubgroup (E.Ai i) g) :=
    isMaxElemAbelian_map_conj (E.isMaxElemAbelian_Ai i) g⁻¹ hle
  rcases (E.isMaxElemAbelian_iff _).1 hmax with h | h | h | h <;> rw [h]
  · exact E.Ai_le_J 0
  · exact E.Ai_le_J 1
  · exact E.Ai_le_J 2
  · exact E.Ai_le_J 3

theorem conjSubgroup_Ai_le_J {i : Fin 4} {g : G} (hg : conjSubgroup E.J g ≤ T) :
    conjSubgroup (E.Ai i) g ≤ E.J :=
  E.conjSubgroup_Ai_le_J_of_le_T
    ((Subgroup.map_mono (E.Ai_le_J i) : conjSubgroup (E.Ai i) g ≤ conjSubgroup E.J g).trans hg)

theorem isWeaklyClosedIn_J [Finite G] : IsWeaklyClosedIn E.J T := by
  intro g hg
  have hA := E.conjSubgroup_Ai_le_J (i := 0) hg
  have hB := E.conjSubgroup_Ai_le_J (i := 1) hg
  have hsup : conjSubgroup E.J g = conjSubgroup E.A g ⊔ conjSubgroup E.B g := by
    unfold conjSubgroup
    rw [E.J_eq_A_sup_B, Subgroup.map_sup]
  have hJ : conjSubgroup E.J g ≤ E.J := by
    rw [hsup]
    exact sup_le hA hB
  refine Subgroup.eq_of_le_of_card_ge hJ ?_
  unfold conjSubgroup
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem coe_conjSubgroup (A : Subgroup G) (g : G) :
    (conjSubgroup A g : Set G) = conjSet (A : Set G) g := by
  ext x
  rw [SetLike.mem_coe, mem_conjSubgroup_iff, mem_conjSet_iff]
  rfl

theorem fusion_in_J [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (i : Fin 4) (g : G) (hg : conjSubgroup (E.Ai i) g ≤ E.J) :
    ∃ t ∈ T, conjSubgroup (E.Ai i) g = conjSubgroup (E.Ai i) t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hgT : conjSubgroup (E.Ai i) g ≤ T := hg.trans E.J_le_T
  have hmax : IsMaxElemAbelian T (conjSubgroup (E.Ai i) g) :=
    isMaxElemAbelian_map_conj (E.isMaxElemAbelian_Ai i) g⁻¹ hgT
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, conjSubgroup (E.Ai i) g = E.Ai j := by
    rcases (E.isMaxElemAbelian_iff _).1 hmax with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  have hJS : E.J ≤ (S : Subgroup G) := hS ▸ E.J_le_T
  have hwc : IsWeaklyClosedIn E.J (S : Subgroup G) := hS ▸ E.isWeaklyClosedIn_J
  have hA : ∀ w ∈ E.J, conjSet ((E.Ai i : Subgroup G) : Set G) w = (E.Ai i : Set G) := fun w hw =>
    conjSet_eq_iff_mem_normalizer.2 (E.J_le_normalizer_Ai i hw)
  have hB : ∀ w ∈ E.J, conjSet ((conjSubgroup (E.Ai i) g : Subgroup G) : Set G) w =
      (conjSubgroup (E.Ai i) g : Set G) := fun w hw => by
    rw [hj]
    exact conjSet_eq_iff_mem_normalizer.2 (E.J_le_normalizer_Ai j hw)
  obtain ⟨n, hn, hnB⟩ := burnside_fusion_lemma S hJS hwc hA hB
    (coe_conjSubgroup _ _).symm
  rw [E.normalizer_J_eq hT hM] at hn
  refine ⟨n, hn, ?_⟩
  apply SetLike.coe_injective
  rw [coe_conjSubgroup, coe_conjSubgroup, hnB]
  exact (coe_conjSubgroup _ _).symm

theorem isWeaklyClosedIn_Ai [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (i : Fin 4) (hNorm : T ≤ Subgroup.normalizer (E.Ai i : Set G)) :
    IsWeaklyClosedIn (E.Ai i) T := by
  intro g hg
  obtain ⟨t, ht, heq⟩ := E.fusion_in_J hT hM i g (E.conjSubgroup_Ai_le_J_of_le_T hg)
  rw [heq]
  exact conjSubgroup_eq_iff_mem_normalizer.2 (hNorm ht)

theorem isWeaklyClosedIn_A [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    IsWeaklyClosedIn E.A T :=
  E.isWeaklyClosedIn_Ai hT hM 0 E.T_le_normalizer_A

theorem isWeaklyClosedIn_B [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    IsWeaklyClosedIn E.B T :=
  E.isWeaklyClosedIn_Ai hT hM 1 E.T_le_normalizer_B

theorem A_commute : ∀ x ∈ E.A, ∀ y ∈ E.A, x * y = y * x := by
  have h : IsElemAbelian 2 E.A := isElemAbelian_map isElemAbelian_A1 E.ι
  have := h.1
  intro x hx y hy
  exact setLike_mul_comm hx hy

theorem B_commute : ∀ x ∈ E.B, ∀ y ∈ E.B, x * y = y * x := by
  have h : IsElemAbelian 2 E.B := isElemAbelian_map isElemAbelian_A2 E.ι
  have := h.1
  intro x hx y hy
  exact setLike_mul_comm hx hy

theorem fusion_A [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) {a : G}
    (ha : a ∈ E.A) {g : G} (hg : g⁻¹ * a * g ∈ E.A) : ∃ m ∈ M, m⁻¹ * a * m = g⁻¹ * a * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hAS : E.A ≤ (S : Subgroup G) := hS ▸ E.A_le_T
  have hwc : IsWeaklyClosedIn E.A (S : Subgroup G) := hS ▸ E.isWeaklyClosedIn_A hT hM
  have hx : a ∈ Subgroup.centralizer (E.A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => E.A_commute h hh a ha
  have hy : g⁻¹ * a * g ∈ Subgroup.centralizer (E.A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => E.A_commute h hh _ hg
  obtain ⟨n, hn, hn'⟩ := burnside_fusion_lemma_centralizer S hAS hwc hx hy rfl
  rw [E.normalizer_A_eq_M hM] at hn
  exact ⟨n, hn, hn'⟩

theorem fusion_B [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) {b : G}
    (hb : b ∈ E.B) {g : G} (hg : g⁻¹ * b * g ∈ E.B) :
    ∃ k ∈ Subgroup.normalizer (E.B : Set G), k⁻¹ * b * k = g⁻¹ * b * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hBS : E.B ≤ (S : Subgroup G) := hS ▸ E.B_le_T
  have hwc : IsWeaklyClosedIn E.B (S : Subgroup G) := hS ▸ E.isWeaklyClosedIn_B hT hM
  have hx : b ∈ Subgroup.centralizer (E.B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => E.B_commute h hh b hb
  have hy : g⁻¹ * b * g ∈ Subgroup.centralizer (E.B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => E.B_commute h hh _ hg
  exact burnside_fusion_lemma_centralizer S hBS hwc hx hy rfl

@[expose] def conjClassIn (X : Subgroup G) (x : G) : Set G := {y | ∃ g ∈ X, g⁻¹ * x * g = y}

theorem conjClassIn_M (w : Wc) :
    conjClassIn M (E.ι w) = E.ι '' {y | ∃ v : Wc, v⁻¹ * w * v = y} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨v, rfl⟩ := E.mem_M.1 hg
    exact ⟨v⁻¹ * w * v, ⟨v, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨E.ι v, E.mem_M.2 ⟨v, rfl⟩, by simp⟩

theorem z_mem_A : E.z ∈ E.A := ⟨z0, z0_mem_A1, rfl⟩
theorem t_mem_A : E.t ∈ E.A := ⟨t0, t0_mem_A1, rfl⟩
theorem z_mem_B : E.z ∈ E.B := ⟨z0, z0_mem_A2, rfl⟩
theorem t_mem_B : E.t ∈ E.B := ⟨t0, t0_mem_A2, rfl⟩

theorem t_not_conj_z [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    ¬ ∃ g : G, g⁻¹ * E.z * g = E.t := by
  rintro ⟨g, hg⟩
  obtain ⟨m, hm, hmeq⟩ := E.fusion_A hT hM E.z_mem_A (g := g) (by rw [hg]; exact E.t_mem_A)
  rw [hg] at hmeq
  obtain ⟨w, rfl⟩ := E.mem_M.1 hm
  have : w⁻¹ * z0 * w = t0 := E.injective (by simpa [z, t] using hmeq)
  exact t0_not_conj_z0 ⟨w, this⟩

theorem J_le_centralizer_t : E.J ≤ Subgroup.centralizer ({E.t} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  show E.ι t0 * E.ι y = E.ι y * E.ι t0
  rw [← map_mul, ← map_mul, t0_central_Jh y hy]

theorem isSylowTwoOf_J [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    CFSG.QuasithinUnique.IsSylowTwoOf E.J (Subgroup.centralizer ({E.t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({E.t} : Set G) with hC
  refine ⟨E.J_le_centralizer_t, E.J_isPGroup, ?_⟩
  have hJ'p : IsPGroup 2 (E.J.subgroupOf C) :=
    E.J_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe E.J_le_centralizer_t).symm
  obtain ⟨S, hS⟩ := hJ'p.exists_le_sylow
  have hEq : E.J.subgroupOf C = (S : Subgroup C) := by
    by_contra hne
    obtain ⟨y, ⟨hyS, hyN⟩, hyJ⟩ := exists_mem_inf_normalizer_not_mem S.isPGroup' hS hne
    have hyJnorm : (y : G) ∈ Subgroup.normalizer (E.J : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro j
      constructor
      · intro hj
        have hjC : j ∈ C := E.J_le_centralizer_t hj
        have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨j, hjC⟩).mp (Subgroup.mem_subgroupOf.2 hj)
        exact Subgroup.mem_subgroupOf.1 h1
      · intro hj
        have hjC : j ∈ C := by
          have h2 : (y : G)⁻¹ * ((y : G) * j * (y : G)⁻¹) * (y : G) ∈ C :=
            C.mul_mem (C.mul_mem (C.inv_mem y.2) (E.J_le_centralizer_t hj)) y.2
          simpa [mul_assoc] using h2
        have h3 : (⟨j, hjC⟩ : C) ∈ E.J.subgroupOf C := by
          refine (Subgroup.mem_normalizer_iff.mp hyN ⟨j, hjC⟩).mpr ?_
          exact Subgroup.mem_subgroupOf.2 hj
        exact Subgroup.mem_subgroupOf.1 h3
    have hyT : (y : G) ∈ T := by
      have := E.normalizer_J_eq hT hM
      rw [← this]
      exact hyJnorm
    have hyT' := hyT
    rw [← E.map_Th] at hyT'
    obtain ⟨w, hw, hwy⟩ := hyT'
    have hyC : (y : G) ∈ C := y.2
    have hcomm : E.t * (y : G) = (y : G) * E.t := Subgroup.mem_centralizer_iff.mp hyC E.t rfl
    have hwc : w * t0 = t0 * w := by
      apply E.injective
      rw [map_mul, map_mul]
      have : E.t * E.ι w = E.ι w * E.t := by rw [hwy]; exact hcomm
      exact this.symm
    have hwJ : w ∈ Jh := centralizer_t0_Th w hw hwc
    exact hyJ (Subgroup.mem_subgroupOf.2 (show (y : G) ∈ E.J from ⟨w, hwJ, hwy⟩))
  rw [hEq]
  exact S.not_dvd_index

end Emb

end CFSG.Quasithin.A10
