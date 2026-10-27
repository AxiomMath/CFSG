module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Sylow
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviModules
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviCentralizers
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.CGT.PushingUpLit.CGT6K1.Rank2
public import CFSG.Adapters.FrobeniusKernel
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndPass
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndTypes
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.CGT.PushingUpLit.CGT6.SixFour
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313L2
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Semidihedral.Local (map_centralizer_eq_of_coprime)

@[expose] def K_3D4RootLine : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), Is3D4 Y n →
    ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n - 1 →
    ∀ E : Subgroup Y, IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup Y, B ≤ E ∧ Nat.card B = r ∧
        ∃ Y₀ : Subgroup Y, Y₀ ≤ Subgroup.centralizer (B : Set Y) ∧ IsL2 ↥Y₀ (3 * n)

variable {G : Type} [Group G] [Finite G]

theorem exists_rootLine_lift_of_bar {X : Subgroup G} {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbar : ∀ E : Subgroup (Bar2 X), IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup (Bar2 X), B ≤ E ∧ Nat.card B = r ∧
        ∃ Y₀ : Subgroup (Bar2 X), Y₀ ≤ Subgroup.centralizer (B : Set (Bar2 X)) ∧ IsL2 ↥Y₀ m)
    {E : Subgroup G} (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
      ∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
        ∃ N₀ : Subgroup ↥Yt, ∃ _ : N₀.Normal, IsL2 (↥Yt ⧸ N₀) m := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hN2 : IsPGroup 2 (CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hπker : π.ker = CFSG.pCore 2 ↥X := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let E' : Subgroup ↥X := E.subgroupOf X
  have hE'el : IsElemAbelian r E' := hEel.comap X.subtype_injective
  have hE'card : Nat.card E' = r ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hdisj : Disjoint E' (CFSG.pCore 2 ↥X) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hE'card, hk]
    have hcop2 : Nat.Coprime r 2 := (Nat.Prime.coprime_iff_not_dvd hr).mpr (by
      intro h2
      have hle := Nat.le_of_dvd (by norm_num) h2
      exact hr2 (le_antisymm hle hr.two_le))
    exact (hcop2.pow_left 2).pow_right k
  have hĒel : IsElemAbelian r (E'.map π) := CFSG.SectionRank.isElemAbelian_map hE'el π
  have hĒcard : Nat.card (E'.map π) = r ^ 2 := by
    have h1 : Nat.card (E'.map π) = Nat.card E' :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π E' (by
        rw [hπker]; exact hdisj)
    rw [h1, hE'card]
  obtain ⟨Bb, hBbE, hBbcard, Y₀, hY₀le, hY₀L2⟩ := hbar (E'.map π) hĒel hĒcard
  let B₀ : Subgroup ↥X := Bb.comap π ⊓ E'
  have hB₀le : B₀ ≤ E' := inf_le_right
  have hB₀map : B₀.map π = Bb := by
    refine le_antisymm ?_ ?_
    · calc (Bb.comap π ⊓ E').map π ≤ (Bb.comap π).map π := Subgroup.map_mono inf_le_left
        _ = Bb := Subgroup.map_comap_eq_self_of_surjective hπsurj Bb
    · intro b hb
      obtain ⟨e, he, rfl⟩ := hBbE hb
      exact Subgroup.mem_map.mpr ⟨e, ⟨hb, he⟩, rfl⟩
  have hB₀card : Nat.card B₀ = r := by
    have hd : Disjoint B₀ π.ker := by
      rw [hπker]
      exact Disjoint.mono hB₀le le_rfl hdisj
    have h1 : Nat.card (B₀.map π) = Nat.card B₀ :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π B₀ hd
    rw [hB₀map, hBbcard] at h1
    exact h1.symm
  let B : Subgroup G := B₀.map X.subtype
  have hBE : B ≤ E := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hB₀le hy)
  have hBcard : Nat.card B = r := by
    rw [Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective, hB₀card]
  have hNcop : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    intro hdvd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hdvd
    have hle := Nat.le_of_dvd (by norm_num) h2
    exact hr2 (le_antisymm hle hr.two_le)
  have hB₀r : IsPGroup r B₀ := (hE'el.mono hB₀le).isPGroup
  let C : Subgroup ↥X := Subgroup.centralizer (B₀ : Set ↥X)
  have hCmap : C.map π = Subgroup.centralizer (Bb : Set (Bar2 X)) := by
    have h := map_centralizer_eq_of_coprime (p := r) (N := CFSG.pCore 2 ↥X) (G := ↥X)
      hNcop B₀ hB₀r
    simpa [C, π, hB₀map] using h
  let D : Subgroup ↥X := C ⊓ Y₀.comap π
  let ψ : ↥D →* ↥Y₀ := (π.comp D.subtype).codRestrict Y₀ (fun x => x.2.2)
  have hψsurj : Function.Surjective ψ := by
    intro z
    have hz : (z : Bar2 X) ∈ C.map π := by rw [hCmap]; exact hY₀le z.2
    obtain ⟨c, hc, hcz⟩ := hz
    have hcY : c ∈ Y₀.comap π := by rw [Subgroup.mem_comap, hcz]; exact z.2
    exact ⟨⟨c, ⟨hc, hcY⟩⟩, Subtype.ext hcz⟩
  let eD : ↥D ≃* ↥(D.map X.subtype) :=
    Subgroup.equivMapOfInjective D X.subtype X.subtype_injective
  let Yt : Subgroup G := D.map X.subtype
  let φ : ↥Yt →* ↥Y₀ := ψ.comp eD.symm.toMonoidHom
  have hφsurj : Function.Surjective φ := hψsurj.comp eD.symm.surjective
  let N₀ : Subgroup ↥Yt := φ.ker
  have hYtle : Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_inf (Subgroup.map_subtype_le D) ?_
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxC, -⟩ := hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact congrArg Subtype.val (hxC a ha)
  refine ⟨B, hBE, hBcard, Yt, hYtle, N₀, MonoidHom.normal_ker φ, ?_⟩
  have hq1 : ↥Yt ⧸ N₀ ≃* ↥Y₀ := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
  exact CFSG.Blueprint.LieModel.of_mulEquiv hq1.symm hY₀L2

theorem exists_rootLine_lift_3D4 (hRL : K_3D4RootLine) {X : Subgroup G} {n r : ℕ}
    (h3D4 : Is3D4 (Bar2 X) n) (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ 2 ^ n - 1)
    {E : Subgroup G} (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
      ∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
        ∃ N₀ : Subgroup ↥Yt, ∃ _ : N₀.Normal, IsL2 (↥Yt ⧸ N₀) (3 * n) :=
  exists_rootLine_lift_of_bar (m := 3 * n) hr (by omega)
    (fun _ hEel hEcard => hRL _ n h3D4 r hr hr3 hrd _ hEel hEcard) hEX hEel hEcard


theorem k_3D4RootLine_holds : K_3D4RootLine := by
  classical
  intro Y _ _ n h3D4 r hr hr3 hrd E hEel hEcard
  have hn : 1 ≤ n := h3D4.admissible.2.1
  obtain ⟨d⟩ := CFSG.LocalAnalysis.EvenBN.TrialityD4.nonempty_trialityD4Data_of_lieModel
    (f := n) hn h3D4
  set q : ℕ := 2 ^ n with hq
  have hq2 : 2 ≤ q := by simpa [hq] using d.two_le_q
  have hcardΓ : Nat.card d.Γ = q ^ 3 := by simpa [hq] using d.card_Γ
  have hcardΓ₀ : Nat.card d.Γ₀ = q := by simpa [hq] using d.card_Γ₀
  have hYcard : Nat.card Y = q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) *
      (q ^ 8 + q ^ 4 + 1) := by simpa [hq] using d.card_eq
  have hJcard : Nat.card d.J = (q - 1) * (q ^ 3 - 1) := by
    simpa [hq] using d.card_J
  have hq1 : r ∣ q - 1 := by simpa [hq] using hrd
  let M : ℕ := q ^ 12 * (q + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 8 + q ^ 4 + 1)
  have hsplit : Nat.card Y = Nat.card d.J * M := by
    have hq1' : 1 ≤ q := by omega
    have hq2' : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
    have hq6' : 1 ≤ q ^ 6 := Nat.one_le_pow 6 q (by omega)
    have hq3' : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
    have hqq : q ≤ q ^ 2 := by nlinarith
    have hZ : (Nat.card Y : ℤ) = (Nat.card d.J : ℤ) * (M : ℤ) := by
      rw [hYcard, hJcard]
      dsimp only [M]
      push_cast [Nat.cast_sub hq1', Nat.cast_sub hq2', Nat.cast_sub hq6',
        Nat.cast_sub hq3', Nat.cast_sub hqq]
      ring
    exact_mod_cast hZ
  have hq_cop : Nat.Coprime r q := by
    rw [hq]
    exact (hr.odd_of_ne_two (by omega)).coprime_two_right.pow_right n
  have hqp1_cop : Nat.Coprime r (q + 1) := by
    refine (hr.coprime_iff_not_dvd).2 ?_
    intro h
    have h2 : r ∣ 2 := by
      have hsub : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hq1
      have hEq : (q + 1) - (q - 1) = 2 := by omega
      rwa [hEq] at hsub
    have hle := Nat.le_of_dvd (by norm_num) h2
    have hr2 : r ≠ 2 := by omega
    exact hr2 (le_antisymm hle hr.two_le)
  have hq2q1_cop : Nat.Coprime r (q ^ 2 - q + 1) := by
    refine (hr.coprime_iff_not_dvd).2 ?_
    intro h
    have h2q : r ∣ q ^ 2 - q := by
      have hqq : q * (q - 1) = q ^ 2 - q := by
        rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
      rw [← hqq]
      exact dvd_mul_of_dvd_right hq1 q
    have h1 : r ∣ 1 := (Nat.dvd_add_iff_right h2q).2 h
    exact hr.not_dvd_one h1
  have hq8_cop : Nat.Coprime r (q ^ 8 + q ^ 4 + 1) := by
    refine (hr.coprime_iff_not_dvd).2 ?_
    intro h
    have h8 : r ∣ q ^ 8 - 1 := hq1.trans (Nat.sub_dvd_pow_sub_pow q 1 8)
    have h4 : r ∣ q ^ 4 - 1 := hq1.trans (Nat.sub_dvd_pow_sub_pow q 1 4)
    have h3 : r ∣ 3 := by
      have hsum : r ∣ (q ^ 8 - 1) + (q ^ 4 - 1) := dvd_add h8 h4
      have hEq : (q ^ 8 - 1) + (q ^ 4 - 1) + 3 = q ^ 8 + q ^ 4 + 1 := by
        have h8p : 1 ≤ q ^ 8 := Nat.one_le_pow 8 q (by omega)
        have h4p : 1 ≤ q ^ 4 := Nat.one_le_pow 4 q (by omega)
        omega
      have h' : r ∣ (q ^ 8 - 1) + (q ^ 4 - 1) + 3 := by rwa [hEq]
      exact (Nat.dvd_add_iff_right hsum).2 h'
    have hle := Nat.le_of_dvd (by norm_num) h3
    omega
  have hM_coprime : Nat.Coprime r M := by
    dsimp [M]
    exact (((hq_cop.pow_right 12).mul_right (hqp1_cop.pow_right 2)).mul_right
      hq2q1_cop).mul_right hq8_cop
  have hindexJ : d.J.index = M := by
    have h := d.J.card_mul_index
    rw [hsplit] at h
    exact Nat.mul_left_cancel (Nat.card_pos) h
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨P, hEP⟩ := hEel.isPGroup.exists_le_sylow
  let PJ0 : Sylow r ↥d.J := Classical.arbitrary _
  let PJ : Subgroup Y := Subgroup.map d.J.subtype (PJ0 : Subgroup ↥d.J)
  have hPJp : IsPGroup r PJ := PJ0.isPGroup'.map d.J.subtype
  have hPJindex : PJ.index = PJ0.index * d.J.index :=
    Subgroup.index_map_subtype (PJ0 : Subgroup ↥d.J)
  have hPJ0_cop : Nat.Coprime r PJ0.index := (hr.coprime_iff_not_dvd).2 PJ0.not_dvd_index
  have hPJ_cop : Nat.Coprime r PJ.index := by
    rw [hPJindex]
    exact hPJ0_cop.mul_right (by rw [hindexJ]; exact hM_coprime)
  have hPJ_idx : ¬ r ∣ PJ.index := (hr.coprime_iff_not_dvd).1 hPJ_cop
  let PJs : Sylow r Y := hPJp.toSylow hPJ_idx
  have hPJs_coe : (PJs : Subgroup Y) = PJ := IsPGroup.toSylow_coe hPJp hPJ_idx
  have hPJs_le_J : (PJs : Subgroup Y) ≤ d.J := by
    rw [hPJs_coe]
    exact Subgroup.map_subtype_le (PJ0 : Subgroup ↥d.J)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P PJs
  have hPconj : (P : Subgroup Y).conjBy g = (PJs : Subgroup Y) := by
    have h := congrArg (fun S : Sylow r Y => (S : Subgroup Y)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    rw [Subgroup.conjBy]
    convert h using 2
    ext x
    rfl
  have hEconj_le_J : E.conjBy g ≤ d.J := by
    have h1 : E.conjBy g ≤ (P : Subgroup Y).conjBy g := by
      simpa [Subgroup.conjBy] using Subgroup.map_mono hEP
    rw [hPconj] at h1
    exact h1.trans hPJs_le_J
  let T : Subgroup Y := Subgroup.map d.torus
    ((rootsOfUnity r d.Γ₀).prod (rootsOfUnity r d.Γ))
  have hroot₀ : Nat.card (rootsOfUnity r d.Γ₀) = r := by
    refine @CFSG.LinearGroups.card_rootsOfUnity_of_dvd d.Γ₀ _ _ r ⟨hr.ne_zero⟩ ?_
    rw [hcardΓ₀]
    exact hq1
  have hrootΓ : Nat.card (rootsOfUnity r d.Γ) = r := by
    refine @CFSG.LinearGroups.card_rootsOfUnity_of_dvd d.Γ _ _ r ⟨hr.ne_zero⟩ ?_
    rw [hcardΓ]
    rw [show q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) by
      simpa [hq] using d.pow_three_sub_one]
    exact dvd_mul_of_dvd_left hq1 _
  have hcardT : Nat.card T = r ^ 2 := by
    dsimp only [T]
    rw [Subgroup.card_map_of_injective d.torus_injective]
    rw [Nat.card_congr (Subgroup.prodEquiv (rootsOfUnity r d.Γ₀)
      (rootsOfUnity r d.Γ)).toEquiv, Nat.card_prod, hroot₀, hrootΓ]
    ring
  have mem_T_iff : ∀ x : Y, x ∈ T ↔ x ∈ d.J ∧ x ^ r = 1 := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨d.torus_mem_J u, ?_⟩
      rw [← map_pow]
      have hu' : u ^ r = 1 := by
        refine Prod.ext ?_ ?_
        · simpa using (mem_rootsOfUnity r u.1).mp (Subgroup.mem_prod.mp hu).1
        · simpa using (mem_rootsOfUnity r u.2).mp (Subgroup.mem_prod.mp hu).2
      rw [hu', map_one]
    · rintro ⟨hxJ, hxr⟩
      obtain ⟨u, rfl⟩ := (d.mem_J).1 hxJ
      have hu : u ^ r = 1 := d.torus_injective (by rw [map_pow, hxr, map_one])
      refine ⟨u, Subgroup.mem_prod.2 ⟨?_, ?_⟩, rfl⟩
      · exact (mem_rootsOfUnity r u.1).2 (by simpa using congrArg Prod.fst hu)
      · exact (mem_rootsOfUnity r u.2).2 (by simpa using congrArg Prod.snd hu)
  have hcard_Econj : Nat.card (E.conjBy g) = r ^ 2 := by
    rw [Subgroup.conjBy, Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
  have hEconj_le_T : E.conjBy g ≤ T := by
    intro x hx
    rw [mem_T_iff]
    refine ⟨hEconj_le_J hx, ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    change (MulAut.conj g y) ^ r = 1
    rw [← map_pow, hEel.2 y hy, map_one]
  have hEconj_eq_T : E.conjBy g = T :=
    Subgroup.eq_of_le_of_card_ge hEconj_le_T (by rw [hcardT, hcard_Econj])
  let B0 : Subgroup Y :=
    Subgroup.map (d.torus.comp (MonoidHom.inl (d.Γ₀)ˣ d.Γˣ)) (rootsOfUnity r d.Γ₀)
  have hB0card : Nat.card B0 = r := by
    dsimp only [B0]
    rw [Subgroup.card_map_of_injective (f := d.torus.comp (MonoidHom.inl _ _)) (by
      intro a b h
      exact congrArg Prod.fst (d.torus_injective h)), hroot₀]
  have hB0_le_J₁ : B0 ≤ d.J₁ := by
    rintro x ⟨a, ha, rfl⟩
    exact (d.torus_mem_J₁_iff (a, 1)).2 rfl
  have hB0_le_T : B0 ≤ T := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_T_iff]
    refine ⟨d.torus_mem_J (a, 1), ?_⟩
    rw [← map_pow]
    have har : a ^ r = 1 := (mem_rootsOfUnity r a).mp ha
    rw [har, map_one]
  have hlevB0 : d.leviShort ≤ Subgroup.centralizer (B0 : Set Y) :=
    d.leviShort_le_centralizer_J₁.trans (Subgroup.centralizer_le (by
      intro x hx
      exact hB0_le_J₁ hx))
  let B : Subgroup Y := Subgroup.map (MulAut.conj g⁻¹).toMonoidHom B0
  have hBE : B ≤ E := by
    have h1 : B0 ≤ E.conjBy g := by rw [hEconj_eq_T]; exact hB0_le_T
    have h2 : B ≤ (E.conjBy g).conjBy g⁻¹ := Subgroup.map_mono h1
    have h3 : (E.conjBy g).conjBy g⁻¹ = E := by
      rw [Subgroup.conjBy_conjBy, inv_mul_cancel, Subgroup.conjBy_one]
    rwa [h3] at h2
  have hBcard : Nat.card B = r := by
    dsimp only [B]
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hB0card]
  let Yt : Subgroup Y := Subgroup.map (MulAut.conj g⁻¹).toMonoidHom d.leviShort
  have hL2 : IsL2 ↥d.leviShort (3 * n) := by
    have hcard : Nat.card d.Γ = 2 ^ (3 * n) := by
      rw [d.card_Γ, ← pow_mul, mul_comm]
    let fintype : Fintype d.Γ := Fintype.ofFinite d.Γ
    have hF : @Fintype.card d.Γ fintype = 2 ^ (3 * n) := by
      rw [← @Nat.card_eq_fintype_card d.Γ fintype, hcard]
    have hStated : CFSG.Open.StatedClassicalModel ↥d.leviShort .PSL 2 2 (3 * n) :=
      @CFSG.CGT.PushingUpLit.CGT6K1.statedClassicalModel_psl_two_of_mulEquiv_specialLinear_two
        ↥d.leviShort _ (3 * n) (by omega) d.Γ _ fintype hF d.leviShortEquiv
    rw [IsL2]
    exact Or.inl ⟨by decide, hStated⟩
  have hYtL2 : IsL2 ↥Yt (3 * n) := by
    let e : ↥d.leviShort ≃* ↥Yt :=
      Subgroup.equivMapOfInjective d.leviShort (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective
    exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := 3 * n) e
      (by simpa [IsL2] using hL2)
  have hYt_le_cent : Yt ≤ Subgroup.centralizer (B : Set Y) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.1 hb
    have hcomm : b0 * y0 = y0 * b0 :=
      (Subgroup.mem_centralizer_iff.1 (hlevB0 hy0)) b0 hb0
    change (MulAut.conj g⁻¹ b0) * (MulAut.conj g⁻¹ y0) =
      (MulAut.conj g⁻¹ y0) * (MulAut.conj g⁻¹ b0)
    rw [← map_mul, ← map_mul, hcomm]
  exact ⟨B, hBE, hBcard, Yt, hYt_le_cent, hYtL2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
