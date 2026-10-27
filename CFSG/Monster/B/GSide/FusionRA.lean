module

public import CFSG.Monster.B.GSide.CommutatorTest

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem exists_odd_conjClass_of_odd {H : Type*} [Group H] [Finite H] {S : Set H}
    (hS : ∀ y ∈ S, ∀ y' : H, IsConj y y' → y' ∈ S) (hodd : Odd S.ncard) :
    ∃ y ∈ S, Odd (Nat.card (ConjClasses.mk y).carrier) := by
  classical
  have := Fintype.ofFinite H
  by_contra h0
  have h : ∀ y ∈ S, ¬ Odd (Nat.card (ConjClasses.mk y).carrier) := fun y hy hy' =>
    h0 ⟨y, hy, hy'⟩
  have hcl : S.toFinset = (S.toFinset.image ConjClasses.mk).biUnion
      (fun C => C.carrier.toFinset) := by
    ext y
    simp only [Set.mem_toFinset, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hy
      exact ⟨ConjClasses.mk y, ⟨y, hy, rfl⟩, ConjClasses.mem_carrier_mk⟩
    · rintro ⟨C, ⟨y₀, hy₀, rfl⟩, hyC⟩
      exact hS y₀ hy₀ y (ConjClasses.mk_eq_mk_iff_isConj.1
        (ConjClasses.mem_carrier_iff_mk_eq.1 hyC).symm)
  have hdisj : ∀ C ∈ S.toFinset.image ConjClasses.mk, ∀ C' ∈ S.toFinset.image ConjClasses.mk,
      C ≠ C' → Disjoint C.carrier.toFinset C'.carrier.toFinset := by
    intro C _ C' _ hne
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq] at hy hy'
    exact hne (hy.symm.trans hy')
  have heven : Even S.toFinset.card := by
    rw [hcl, Finset.card_biUnion hdisj]
    refine Finset.even_sum _ fun C hC => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hC
    have h1 := Nat.not_odd_iff_even.1 (h y₀ (Set.mem_toFinset.1 hy₀))
    rwa [Nat.card_eq_card_toFinset] at h1
  rw [← Set.ncard_eq_toFinset_card'] at heven
  exact (Nat.not_even_iff_odd.2 hodd) heven

variable {G : Type*} [Group G] {d : G}

theorem isConj_cV0_iff
    {y : vStab cv0} : IsConj y cV0 ↔ y = cV0 := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    have hc : g * cV0 = cV0 * g := Subgroup.mem_center_iff.1 cV0_mem_center_vStab g
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = g⁻¹ * cV0 * g := by rw [hg]
      _ = cV0 := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
  · rintro rfl
    exact IsConj.refl _

theorem orderOf_of_mem_dH
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (hd : orderOf d = 2)
    {y : vStab cv0} (hy : y ∈ dH ψ) : orderOf y = 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ((mem_dH_iff ψ y).1 hy)
  have h1 : orderOf ((ψ.symm y : Subgroup.centralizer {d}) : G) = 2 := by
    rw [← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hd
  rw [← MulEquiv.orderOf_eq ψ.symm, ← Subgroup.orderOf_coe]
  exact h1

theorem cV0_mem_dH
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) : cV0 ∈ dH ψ := by
  rw [mem_dH_iff, ← hψ, MulEquiv.symm_apply_apply]

theorem mem_RA_of_mem_dH
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    {y : vStab cv0} (hy : y ∈ dH ψ) (hyc : y ≠ cV0)
    (hcard : Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {lamW0H})) :
    y ∈ RA := by
  have h2 : 2 ^ 38 ∣ Nat.card (Subgroup.centralizer {y}) := by
    rw [hcard, natCard_centralizer_of_mem_RA_or_RB (Or.inl lamW0H_mem_RA)]
    exact ⟨280665, by norm_num⟩
  rcases mem_RA_or_RB_of_two_part (orderOf_of_mem_dH ψ hd hy) hyc h2 with h | h
  · exact h
  · exact absurd hy (not_mem_dH_of_mem_RB ψ hψ
      (fun _ h2' hc' hd' => mem_RA_or_RB_of_two_part h2' hc' hd') h)

theorem ncard_dH
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    (dH ψ).ncard = Nat.card {y : G // IsConj d y ∧ d * y = y * d} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun z => ⟨((ψ.symm z : Subgroup.centralizer {d}) : G), z.2,
        (Subgroup.mem_centralizer_singleton_iff.1 (ψ.symm z).2).symm⟩
      invFun := fun y => ⟨ψ ⟨y.1, Subgroup.mem_centralizer_singleton_iff.2 y.2.2.symm⟩, by
        rw [mem_dH_iff, MulEquiv.symm_apply_apply]
        exact y.2.1⟩
      left_inv := fun z => Subtype.ext (by simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply])
      right_inv := fun y => Subtype.ext (by simp only [MulEquiv.symm_apply_apply]) }

theorem RA_subset_dH
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index) : RA ⊆ dH ψ := by
  have hd2 : d ^ 2 = 1 := by rw [← hd, pow_orderOf_eq_one]
  have hpar := Recog.card_conj_commute_modEq_index hd2 d
  have heven : Even (dH ψ).ncard := by
    rw [ncard_dH ψ, Nat.even_iff]
    have h1 : Nat.card {y : G // IsConj d y ∧ d * y = y * d} % 2 =
        (Subgroup.centralizer {d}).index % 2 := hpar
    rw [h1]
    obtain ⟨k, hk⟩ := hidx
    omega
  have hc := cV0_mem_dH ψ hψ
  have hodd : Odd (dH ψ \ {cV0}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hc]
    have hpos : 0 < (dH ψ).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hc⟩
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  have hS : ∀ y ∈ dH ψ \ {cV0}, ∀ y' : vStab cv0, IsConj y y' → y' ∈ dH ψ \ {cV0} := by
    rintro y ⟨hy, hyc⟩ y' h
    refine ⟨mem_dH_of_isConj ψ hy h, fun hy'c => hyc ?_⟩
    rw [Set.mem_singleton_iff] at hy'c ⊢
    subst hy'c
    exact isConj_cV0_iff.1 h
  obtain ⟨y, ⟨hy, hyc⟩, hyodd⟩ := exists_odd_conjClass_of_odd hS hodd
  have hy2 := orderOf_of_mem_dH ψ hd hy
  have hyRA : y ∈ RA := by
    rcases (odd_card_involution_class_iff hy2).1 hyodd with h | h | h
    · exact absurd (Set.mem_singleton_iff.2 h) hyc
    · exact h
    · exact absurd hy (not_mem_dH_of_mem_RB ψ hψ
        (fun _ h2 hc' hd' => mem_RA_or_RB_of_two_part h2 hc' hd') h)
  intro r hr
  exact mem_dH_of_isConj ψ hy (RA_isConj y r hyRA hr)

theorem gAdj_symm_of_two_dvd
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index) {a b : G} (h : gAdj ψ a b) : gAdj ψ b a :=
  gAdj_symm ψ hψ (RA_subset_dH ψ hψ hd hidx)
    (fun _ hy hne hc => mem_RA_of_mem_dH ψ hψ hd hy hne hc) h

theorem gAdj_edge
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    gAdj ψ d ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) := by
  rw [gAdj_self_iff ψ (ψ.symm lamW0H).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  exact lamW0H_mem_RA

theorem exists_swap_edge
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index) :
    ∃ s : G, s * d * s⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
      s * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * s⁻¹ = d :=
  exists_swap_of_gAdj ψ (gAdj_edge ψ) (gAdj_symm_of_two_dvd ψ hψ hd hidx (gAdj_edge ψ))

end CFSG.Monster.B.GSide
