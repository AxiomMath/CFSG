module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1Act
public import CFSG.RankThree.PartOne.Q1327T.Perm3
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Quasithin.S15223P4.Y1

open CFSG.Open CFSG.QuasithinUnique

section Abstract

theorem nonempty_quot_perm_three {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] (φ : Γ →* Δ)
    (ψ : ↥φ.range ≃* Equiv.Perm (Fin 3)) (hker : IsPGroup 2 ↥φ.ker) :
    Nonempty (Γ ⧸ CFSG.Open.pCore 2 Γ ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.Open.pCore 2 Γ).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hkerπ : φ.rangeRestrict.ker = φ.ker := MonoidHom.ker_rangeRestrict φ
  have hle1 : φ.ker ≤ CFSG.Open.pCore 2 Γ :=
    CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker φ) hker
  have hfin : Finite ↥φ.range := Finite.of_surjective _ hsurj
  have hle2 : CFSG.Open.pCore 2 Γ ≤ φ.ker := by
    have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 φ.rangeRestrict hsurj
    have h2 : CFSG.Open.pCore 2 ↥φ.range = ⊥ :=
      CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot ψ _
        (CFSG.LieType.BorelTits.pCore_normal 2) (CFSG.LieType.BorelTits.pCore_isPGroup 2)
    rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    rwa [hkerπ] at h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hle2 hle1)).trans
    ((QuotientGroup.quotientMulEquivOfEq hkerπ.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).trans ψ))⟩

end Abstract

section Main

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem nonempty_autOn_perm_three (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) :
    Nonempty (↥(autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) (V154 T Mc M)) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨e, he3, hYe⟩ := exists_autOn_eq_zpowers c hN h3
  have hΓN : oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀ ≤ M ⊓ I :=
    sup_le (oPrimeResidualOf_le1516 3 _) c.S_le_N
  obtain ⟨b, hb1, hb2, hB⟩ := exists_zpowers_eq_of_card_two c.b0.2.1
  have hbB : b ∈ B₀ := hB ▸ Subgroup.mem_zpowers b
  have hbo : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have heΓ : e ∈ autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) (V154 T Mc M) :=
    A4.autOn_mono le_sup_left (hYe ▸ Subgroup.mem_zpowers e)
  have hbΓ : b ∈ autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) (V154 T Mc M) :=
    A4.autOn_mono le_sup_right (B₀_le_autOn_S152 c.setting c.b0 hbB)
  have hcard : Nat.card ↥(autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀)
      (V154 T Mc M)) = 6 := by
    have hdvd := Subgroup.card_dvd_of_le (A4.autOn_mono (V := V154 T Mc M) hΓN)
    rw [D1.card_autOn_inf c] at hdvd
    have h3d := Subgroup.orderOf_dvd_natCard _ heΓ
    have h2d := Subgroup.orderOf_dvd_natCard _ hbΓ
    rw [he3] at h3d
    rw [hbo] at h2d
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀)
      (V154 T Mc M)) := Nat.card_pos
    omega
  have hOm : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have heE : e ∈ oTwoUpper (autOn M (V154 T Mc M)) :=
    mem_oTwoUpper_of_odd (A4.autOn_mono (hΓN.trans inf_le_left) heΓ) (he3 ▸ (by decide : Odd 3))
  have hinv := B₀_inverts c.setting c.b0 c.inputs hOm b hbB hb1 e heE
  refine CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three
    (⟨e, heΓ⟩ : ↥(autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) (V154 T Mc M)))
    ⟨b, hbΓ⟩ (Subtype.ext ?_) (fun h => ?_) (Subtype.ext ?_) (fun h => hb1 (congrArg Subtype.val h))
    (Subtype.ext hinv) hcard
  · show e ^ 3 = 1
    rw [← he3]
    exact pow_orderOf_eq_one e
  · have : e = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at he3
    omega
  · show b * b = 1
    rw [← sq]
    exact hb2

theorem nonempty_quot (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) :
    Nonempty (OTwoQuot (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨ψ0⟩ := nonempty_autOn_perm_three c hN h3
  have hΓN : oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀ ≤ M ⊓ I :=
    sup_le (oPrimeResidualOf_le1516 3 _) c.S_le_N
  have hΓV : oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀ ≤
      Subgroup.normalizer (V154 T Mc M : Set G) :=
    (hΓN.trans inf_le_left).trans (le_normalizer_V154 T Mc M)
  set φ := A4.actionOn (V154 T Mc M) (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) hΓV with hφ
  have hrange : φ.range = autOn (oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀) (V154 T Mc M) := by
    ext a
    rw [A4.mem_autOn_iff hΓV, MonoidHom.mem_range]
  have hker : IsPGroup 2 ↥φ.ker := by
    rintro ⟨g, hg⟩
    have hgC : (g : G) ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
      (A4.actionOn_eq_one_iff hΓV g).mp (MonoidHom.mem_ker.mp hg)
    have hgS := mem_S_of_mem_centralizer c hN h3 g.2 hgC
    obtain ⟨k, hk⟩ := c.sylow.isPGroup ⟨g, hgS⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  exact nonempty_quot_perm_three φ ((MulEquiv.subgroupCongr hrange).trans ψ0) hker

end Main

end CFSG.Quasithin.S15223P4.Y1
