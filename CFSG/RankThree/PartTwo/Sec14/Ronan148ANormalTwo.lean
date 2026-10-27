module

import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG

variable {Γ : Type} [Group Γ] [Finite Γ]

private theorem injective_conj_hom (x : Γ) : Function.Injective (MulAut.conj x).toMonoidHom :=
  (MulAut.conj x).injective

private theorem card_map_conj (H : Subgroup Γ) (x : Γ) :
    Nat.card (H.map (MulAut.conj x).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (injective_conj_hom x)

private theorem isSimpleGroup_map_conj {H : Subgroup Γ} (hH : IsSimpleGroup ↥H) (x : Γ) :
    IsSimpleGroup ↥(H.map (MulAut.conj x).toMonoidHom) := by
  haveI := hH
  exact (H.equivMapOfInjective (MulAut.conj x).toMonoidHom
    (injective_conj_hom x)).symm.isSimpleGroup

private theorem isQuasisimple_of_simple_perfect {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hp : Group.IsPerfect Q) : CFSG.IsQuasisimple Q := by
  haveI := hs
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcent : (⊤ : Subgroup Q) ≤ Subgroup.centralizer ((⊤ : Subgroup Q) : Set Q) := by
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact hcon h x
    have h2 : commutator Q = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    rw [hp.commutator_eq_top] at h2
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    have hx' : x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top x
    rw [h2, Subgroup.mem_bot] at hx'
    exact hx hx'
  have hZ : Subgroup.center Q = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.1 ha) b).symm
  let eQ : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨hp, eQ.isSimpleGroup, eQ.symm a, eQ.symm b, fun h => hab ?_⟩
  simpa using congrArg eQ h

private theorem isComponent_of_simple_perfect {K : Subgroup Γ} (hKs : IsSimpleGroup ↥K)
    (hKp : Group.IsPerfect ↥K) (hKsn : K.IsSubnormal) : IsComponent K :=
  ⟨isQuasisimple_of_simple_perfect hKs hKp, hKsn⟩

private theorem le_of_isSimpleGroup_of_le_normalizer {D K : Subgroup Γ} {e : Γ}
    (hD : IsSimpleGroup ↥D) (hDN : D ≤ Subgroup.normalizer (K : Set Γ)) (heD : e ∈ D)
    (heK : e ∈ K) (he1 : e ≠ 1) : D ≤ K := by
  have hnorm : ((K ⊓ D).subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    obtain ⟨hhK, hhD⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨?_, D.mul_mem (D.mul_mem hk hhD) (D.inv_mem hk)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hDN hk) h).mp hhK
  haveI := hnorm
  rcases hD.eq_bot_or_eq_top_of_normal ((K ⊓ D).subgroupOf D) with h | h
  · exfalso
    have hmem : (⟨e, heD⟩ : ↥D) ∈ (K ⊓ D).subgroupOf D :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨heK, heD⟩)
    rw [h, Subgroup.mem_bot] at hmem
    exact he1 (congrArg Subtype.val hmem)
  · intro x hx
    exact (Subgroup.mem_inf.mp (Subgroup.subgroupOf_eq_top.mp h hx)).1

private theorem eq_of_isComponent_le {D K : Subgroup Γ} {e : Γ} (hD : IsComponent D)
    (hKs : IsSimpleGroup ↥K) (hDK : D ≤ K) (heD : e ∈ D) (heK : e ∈ K) (he1 : e ≠ 1) :
    D = K := by
  have hsn : (D.subgroupOf K).IsSubnormal := hD.2.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hKs hsn with h | h
  · exfalso
    have hmem : (⟨e, heK⟩ : ↥K) ∈ D.subgroupOf K := Subgroup.mem_subgroupOf.mpr heD
    rw [h, Subgroup.mem_bot] at hmem
    exact he1 (congrArg Subtype.val hmem)
  · exact le_antisymm hDK (Subgroup.subgroupOf_eq_top.mp h)

private theorem conj_mem_centralizer_iff {J : Subgroup Γ} {z : Γ}
    (hz : z ∈ Subgroup.normalizer (J : Set Γ)) (n : Γ) :
    z * n * z⁻¹ ∈ Subgroup.centralizer (J : Set Γ) ↔ n ∈ Subgroup.centralizer (J : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro H j hj
    have hj' : z * j * z⁻¹ ∈ (J : Set Γ) := (Subgroup.mem_normalizer_iff.mp hz j).mp hj
    have h1 := H (z * j * z⁻¹) hj'
    calc j * n = z⁻¹ * (z * j * z⁻¹ * (z * n * z⁻¹)) * z := by group
      _ = z⁻¹ * (z * n * z⁻¹ * (z * j * z⁻¹)) * z := by rw [h1]
      _ = n * j := by group
  · intro H h hh
    have hj' : z⁻¹ * h * z ∈ (J : Set Γ) := by
      refine (Subgroup.mem_normalizer_iff.mp hz (z⁻¹ * h * z)).mpr ?_
      have e1 : z * (z⁻¹ * h * z) * z⁻¹ = h := by group
      rw [e1]
      exact hh
    have h1 := H (z⁻¹ * h * z) hj'
    calc h * (z * n * z⁻¹) = z * (z⁻¹ * h * z * n) * z⁻¹ := by group
      _ = z * (n * (z⁻¹ * h * z)) * z⁻¹ := by rw [h1]
      _ = z * n * z⁻¹ * h := by group

theorem sup_map_conj_eq_of_two {J K Yb Y₁ A : Subgroup Γ} {e : Γ}
    (hJc : IsComponent J) (hJs : IsSimpleGroup ↥J) (hKs : IsSimpleGroup ↥K)
    (hKp : Group.IsPerfect ↥K) (hJY : J ≤ Yb) (hYn : Yb.Normal)
    (hY₁ : Y₁ = Yb ⊓ Subgroup.centralizer (J : Set Γ)) (hKY₁ : K ≤ Y₁)
    (hY₁K : Y₁ ≤ Subgroup.normalizer (K : Set Γ)) (hJK : J ⊓ K = ⊥)
    (heK : e ∈ K) (he1 : e ≠ 1)
    (hFP : ∀ D : Subgroup Γ, D ≤ Subgroup.centralizer (J : Set Γ) →
      A ≤ Subgroup.normalizer (D : Set Γ) → 3 ∣ Nat.card D → e ∈ D)
    (hAJ : ∀ x : Γ, A ≤ Subgroup.normalizer ((J.map (MulAut.conj x).toMonoidHom) : Set Γ))
    (hAK : IsComponent K →
      ∀ x : Γ, A ≤ Subgroup.normalizer ((K.map (MulAut.conj x).toMonoidHom) : Set Γ))
    (h3J : 3 ∣ Nat.card J) (h3K : 3 ∣ Nat.card K) {y : Γ} (hy : y ∈ Yb) :
    (J ⊔ K).map (MulAut.conj y).toMonoidHom = J ⊔ K := by
  have step1 : ∀ z ∈ Yb, J.map (MulAut.conj z).toMonoidHom = J ∨
      J.map (MulAut.conj z).toMonoidHom = K := by
    intro z hz
    by_cases h : J.map (MulAut.conj z).toMonoidHom = J
    · exact Or.inl h
    · refine Or.inr ?_
      have hDc : IsComponent (J.map (MulAut.conj z).toMonoidHom) :=
        Res2LBal.isComponent_conj hJc z
      have hDs : IsSimpleGroup ↥(J.map (MulAut.conj z).toMonoidHom) :=
        isSimpleGroup_map_conj hJs z
      have hJD : J ≠ J.map (MulAut.conj z).toMonoidHom := fun h' => h h'.symm
      have hDC : J.map (MulAut.conj z).toMonoidHom ≤ Subgroup.centralizer (J : Set Γ) :=
        fun d hd => Res2LBal.mem_centralizer_of_mem_of_ne hJc hDc hJD hd
      have hDYb : J.map (MulAut.conj z).toMonoidHom ≤ Yb := by
        rintro _ ⟨j, hj, rfl⟩
        exact hYn.conj_mem j (hJY hj) z
      have hDY₁ : J.map (MulAut.conj z).toMonoidHom ≤ Y₁ := by
        rw [hY₁]
        exact le_inf hDYb hDC
      have h3D : 3 ∣ Nat.card (J.map (MulAut.conj z).toMonoidHom) := by
        rw [card_map_conj]
        exact h3J
      have heD : e ∈ J.map (MulAut.conj z).toMonoidHom := hFP _ hDC (hAJ z) h3D
      have hDK : J.map (MulAut.conj z).toMonoidHom ≤ K :=
        le_of_isSimpleGroup_of_le_normalizer hDs (hDY₁.trans hY₁K) heD heK he1
      exact eq_of_isComponent_le hDc hKs hDK heD heK he1
  have hcase : (∃ y₀ ∈ Yb, J.map (MulAut.conj y₀).toMonoidHom = K) ∨
      ∀ y ∈ Yb, J.map (MulAut.conj y).toMonoidHom ≠ K := by
    by_cases h : ∃ y₀ ∈ Yb, J.map (MulAut.conj y₀).toMonoidHom = K
    · exact Or.inl h
    · exact Or.inr (fun y hy hyK => h ⟨y, hy, hyK⟩)
  have step2 : ∀ z ∈ Yb, K.map (MulAut.conj z).toMonoidHom = J ∨
      K.map (MulAut.conj z).toMonoidHom = K := by
    rcases hcase with ⟨y₀, hy₀, hJy₀⟩ | hno
    · intro z hz
      have hKz : K.map (MulAut.conj z).toMonoidHom =
          J.map (MulAut.conj (z * y₀)).toMonoidHom := by
        rw [← hJy₀, Res2LBal.map_conj_map_conj]
      rcases step1 (z * y₀) (Yb.mul_mem hz hy₀) with h | h
      · exact Or.inl (hKz.trans h)
      · exact Or.inr (hKz.trans h)
    ·
      have hJfix : ∀ z ∈ Yb, J.map (MulAut.conj z).toMonoidHom = J :=
        fun z hz => (step1 z hz).resolve_right (hno z hz)
      have hYbN : ∀ z ∈ Yb, z ∈ Subgroup.normalizer (J : Set Γ) :=
        fun z hz => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hJfix z hz)
      have hYbY₁N : Yb ≤ Subgroup.normalizer (Y₁ : Set Γ) := by
        intro z hz
        rw [Subgroup.mem_normalizer_iff]
        intro n
        show n ∈ Y₁ ↔ z * n * z⁻¹ ∈ Y₁
        rw [hY₁, Subgroup.mem_inf, Subgroup.mem_inf,
          conj_mem_centralizer_iff (hYbN z hz) n]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨hYn.conj_mem n h1 z, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          have h3 := hYn.conj_mem _ h1 z⁻¹
          have e1 : z⁻¹ * (z * n * z⁻¹) * z⁻¹⁻¹ = n := by group
          rw [e1] at h3
          exact h3
      have hY₁Yb : Y₁ ≤ Yb := by
        rw [hY₁]
        exact inf_le_left
      have hKsn : K.IsSubnormal := by
        have h1 : (K.subgroupOf Y₁).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hKY₁).mpr hY₁K
        have h2 : (Y₁.subgroupOf Yb).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hY₁Yb).mpr hYbY₁N
        exact Subgroup.IsSubnormal.trans hKY₁ (Subgroup.Normal.isSubnormal h1)
          (Subgroup.IsSubnormal.trans hY₁Yb (Subgroup.Normal.isSubnormal h2)
            (Subgroup.Normal.isSubnormal hYn))
      have hKc : IsComponent K := isComponent_of_simple_perfect hKs hKp hKsn
      have hKfix : ∀ z ∈ Yb, K.map (MulAut.conj z).toMonoidHom = K := by
        intro z hz
        have hK'Y₁ : K.map (MulAut.conj z).toMonoidHom ≤ Y₁ := by
          rintro _ ⟨k, hk, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp (hYbY₁N hz) k).mp (hKY₁ hk)
        have hK'C : K.map (MulAut.conj z).toMonoidHom ≤ Subgroup.centralizer (J : Set Γ) := by
          refine hK'Y₁.trans ?_
          rw [hY₁]
          exact inf_le_right
        have hK'N : ∀ y ∈ Y₁, y ∈ Subgroup.normalizer
            ((K.map (MulAut.conj z).toMonoidHom : Subgroup Γ) : Set Γ) := by
          intro y hy
          have hwY : z⁻¹ * y * z ∈ Y₁ := by
            have h1 := (Subgroup.mem_normalizer_iff.mp (hYbY₁N (Yb.inv_mem hz)) y).mp hy
            rw [inv_inv] at h1
            exact h1
          have hw : z⁻¹ * y * z ∈ Subgroup.normalizer (K : Set Γ) := hY₁K hwY
          have hw' : K.map (MulAut.conj (z⁻¹ * y * z)).toMonoidHom = K :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
          have hyz : y * z = z * (z⁻¹ * y * z) := by group
          have key : (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj y).toMonoidHom =
              K.map (MulAut.conj z).toMonoidHom := by
            rw [Res2LBal.map_conj_map_conj, hyz, ← Res2LBal.map_conj_map_conj, hw']
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
        have hKN : K ≤ Subgroup.normalizer
            ((K.map (MulAut.conj z).toMonoidHom : Subgroup Γ) : Set Γ) :=
          fun k hk => hK'N k (hKY₁ hk)
        have h3K' : 3 ∣ Nat.card (K.map (MulAut.conj z).toMonoidHom) := by
          rw [card_map_conj]
          exact h3K
        have heK' : e ∈ K.map (MulAut.conj z).toMonoidHom :=
          hFP _ hK'C (hAK hKc z) h3K'
        have hnorm : ((K ⊓ K.map (MulAut.conj z).toMonoidHom).subgroupOf K).Normal := by
          rw [Subgroup.normal_subgroupOf_iff inf_le_left]
          intro h k hh hk
          obtain ⟨hhK, hhK'⟩ := Subgroup.mem_inf.mp hh
          refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hhK) (K.inv_mem hk), ?_⟩
          exact (Subgroup.mem_normalizer_iff.mp (hKN hk) h).mp hhK'
        haveI := hnorm
        rcases hKs.eq_bot_or_eq_top_of_normal
            ((K ⊓ K.map (MulAut.conj z).toMonoidHom).subgroupOf K) with h | h
        · exfalso
          have hmem : (⟨e, heK⟩ : ↥K) ∈ (K ⊓ K.map (MulAut.conj z).toMonoidHom).subgroupOf K :=
            Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨heK, heK'⟩)
          rw [h, Subgroup.mem_bot] at hmem
          exact he1 (congrArg Subtype.val hmem)
        · have hle : K ≤ K.map (MulAut.conj z).toMonoidHom := by
            intro k hk
            exact (Subgroup.mem_inf.mp (Subgroup.subgroupOf_eq_top.mp h hk)).2
          exact (Subgroup.eq_of_le_of_card_ge hle (card_map_conj K z).le).symm
      intro z hz
      exact Or.inr (hKfix z hz)
  have hJne : J ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3J
    norm_num at h3J
  have hJK' : J ≠ K := by
    intro h
    apply hJne
    have h' := hJK
    rw [← h, inf_idem] at h'
    exact h'
  have hinj : ∀ P Q : Subgroup Γ,
      P.map (MulAut.conj y).toMonoidHom = Q.map (MulAut.conj y).toMonoidHom → P = Q :=
    fun P Q h => Subgroup.map_injective (injective_conj_hom y) h
  rw [Subgroup.map_sup]
  rcases step1 y hy with hJy | hJy <;> rcases step2 y hy with hKy | hKy
  · exact absurd (hinj _ _ (hJy.trans hKy.symm)) hJK'
  · rw [hJy, hKy]
  · rw [hJy, hKy, sup_comm]
  · exact absurd (hinj _ _ (hJy.trans hKy.symm)) hJK'

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
