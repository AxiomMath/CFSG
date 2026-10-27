module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenE8SevenSylow
public import CFSG.LocalAnalysis.StandardType.E8SevenLayerFamily
public import CFSG.LocalAnalysis.StandardType.QuasisimpleLayerPullback
public import CFSG.LocalAnalysis.StandardType.SigmaLayerComponents
public import CFSG.RankThree.PartOne.KE6.E8T3Perx
public import CFSG.RankThree.PartOne.KE6.E6LLayer
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate1952
public import Certificates.Certificate14972
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case

public noncomputable section

namespace CFSG.StandardType

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.Assembly
open scoped Matrix MatrixGroups

local instance : CharP (AlgebraicClosure (GaloisField 2 1)) 2 :=
  charP_of_injective_algebraMap (algebraMap (GaloisField 2 1)
    (AlgebraicClosure (GaloisField 2 1))).injective 2

local instance : IsAlgClosed (AlgebraicClosure (GaloisField 2 1)) :=
  IsAlgClosure.isAlgClosed (GaloisField 2 1)

theorem e8TwoSeven_centralizer_component_family_of_layers
    (F : Subgroup (ModGL .E8 (AlgebraicClosure (GaloisField 2 1))) → Prop)
    (hLayers : ∀ (n : ModGL .E8 (AlgebraicClosure (GaloisField 2 1)))
      (hnm : n ∈ monomialSubgroup .E8 (AlgebraicClosure (GaloisField 2 1))),
      n ∈ adjointGroup .E8 (AlgebraicClosure (GaloisField 2 1)) →
      (∀ x : Fin Tag.E8.rank → ℤ, weylQuotientHom .E8 (AlgebraicClosure (GaloisField 2 1))
        ⟨n, hnm⟩ • x = e8T3We 1 • x) →
      ∀ (u : WeylGroup .E8) (J : Finset (Fin Tag.E8.rank)), J ≠ Finset.univ →
      ∀ (S : Set (Fin Tag.E8.rank → ℤ)),
      (fun γ => u • γ) '' S = parabolicRoots .E8 (↑J : Set (Fin Tag.E8.rank)) →
      (∀ α ∈ S, -α ∈ S) → (∀ α ∈ S, e8T3We 1 • α ∈ S) →
      (S.ncard = 30 ∨ S.ncard = 72) →
      ∃ (ι' : Type) (P : ι' → Subgroup (ModGL .E8 (AlgebraicClosure (GaloisField 2 1))))
        (i₀ : ι'), Finite ι' ∧ (Nat.card ι' = 1 ∨ Nat.card ι' = 2) ∧
        IsSigmaFamily n (iterateFrobenius (AlgebraicClosure (GaloisField 2 1)) 2 1) S P ∧
        7 ^ 2 ∣ Nat.card (P i₀) ∧
        (∀ z ∈ P i₀, (∀ w ∈ P i₀, z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
        ∀ i, F (P i))
    (b : adjointGroup .E8 (GaloisField 2 1)) (hb : orderOf b = 7) :
    ∃ (ι' : Type)
      (P : ι' → Subgroup (ModGL .E8 (AlgebraicClosure (GaloisField 2 1))))
      (ψ : Subgroup.centralizer {b} →* ModGL .E8 (AlgebraicClosure (GaloisField 2 1))),
      Function.Injective ψ ∧ Finite ι' ∧ (Nat.card ι' = 1 ∨ Nat.card ι' = 2) ∧
      (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
      (∀ i, P i ≤ ψ.range) ∧
      (∀ i, ∀ d : Subgroup.centralizer {b}, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) ∧
      (∀ H : Subgroup (adjointGroup .E8 (GaloisField 2 1)),
        CFSG.Assembly.IsComponentOf H (Subgroup.centralizer {b}) →
        ∃ i, (H.subgroupOf (Subgroup.centralizer {b})).map ψ = P i ∧ Nonempty (H ≃* P i)) ∧
      (∃ i₀, 7 ^ 2 ∣ Nat.card (P i₀) ∧
        ∀ z ∈ P i₀, (∀ w ∈ P i₀, z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      ∀ i, F (P i)  := by
  classical
  have hp : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp⟩
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have : CharP (AlgebraicClosure (GaloisField 2 1)) 2 :=
    charP_of_injective_algebraMap (algebraMap (GaloisField 2 1)
      (AlgebraicClosure (GaloisField 2 1))).injective 2
  have : IsAlgClosed (AlgebraicClosure (GaloisField 2 1)) :=
    IsAlgClosure.isAlgClosed (GaloisField 2 1)
  set K := GaloisField 2 1 with hKdef
  set L := AlgebraicClosure K with hLdef
  set Fr : L →+* L := iterateFrobenius L 2 1 with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ 1) := fun c => iterateFrobenius_def 2 1 c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hcm := canonicalRep_mem_monomialSubgroup L (e8T3We 1)
  set n : ModGL .E8 L := canonicalRep (coxeterSystem .E8) L (e8T3We 1) with hn
  have hπ : weylQuotientHom .E8 L ⟨n, hcm⟩ = e8T3We 1 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hcm
  have hnW : ∀ x : Fin Tag.E8.rank → ℤ, weylQuotientHom .E8 L ⟨n, hcm⟩ • x = e8T3We 1 • x :=
    fun x => by rw [hπ]
  have hε : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hpf : ((7 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 * (Nat.card K : ℤ) + 1 := by
    rw [hK]
    norm_num
  have hT : twistedTorusOf n Φ =
      (fixedCharTuples (weylMatrix (e8T3We 1)) Fr).map (rootDiagUnitHom .E8 L) :=
    e8T3_twistedTorus n hcm hπ Fr
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e8T3_frame hε K le_rfl hK hp (by norm_num) hpf L n hcm hπ
  have hpg : IsPGroup 7 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh : g0⁻¹ * adjEmb .E8 K L (c * b * c⁻¹) * g0 ∈ twistedTorusOf n Φ :=
    (mem_subtorusImage_iff _ _ _ _).1 (hc b (Subgroup.mem_zpowers b))
  set ι : adjointGroup .E8 K →* ModGL .E8 L := adjEmb .E8 K L with hιdef
  set h : ModGL .E8 L := g0⁻¹ * ι (c * b * c⁻¹) * g0 with hhdef
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b', hb', hbh⟩ := hh'
  have hbh' : rootDiagUnit .E8 b' = h := hbh
  have hordh : orderOf h = 7 := by
    have e1 : orderOf h = orderOf (ι (c * b * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * b * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * b * c⁻¹)) = orderOf (c * b * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * b * c⁻¹) = orderOf b := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective b
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hb]
  have hbp : orderOf (rootDiagUnit .E8 b') = 7 := by rw [hbh']; exact hordh
  have hap := CFSG.RankThree.PartOne.KE.pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a = rootCharKernel b' := fun a ha => by
    have : a = b' := hinj0 (ha.trans hbh'.symm)
    rw [this]
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (weylMatrix (e8T3We 1)) Fr hFr hp hb' hap hb1
  have hU : ¬ 7 ∣ Nat.card (dualWeylStabilizer z) :=
    e8T3_dualStab_prime hp (by norm_num) hε hpf hz0 hzM
  have hbS : rootCharKernel b' = rootKernel z := by rw [hzk]; rfl
  have hr : ((1 : ℤ) : ZMod 7) * ((Nat.card K : ℕ) : ZMod 7) = 2 := by
    rw [hK]
    norm_num
  have hzM' := e8Vt7_of_eigencolumn hε hzM
  rw [hr] at hzM'
  have hcount : (rootCharKernel b').ncard = 30 ∨ (rootCharKernel b').ncard = 72 := by
    rw [hbS, ← e8Count7_eq_ncard]
    exact e8_eigen_count hz0 (Or.inl rfl) hzM'
  obtain ⟨u, J, hΦJ, hJne⟩ := exists_smul_rootKernel_eq_parabolicRoots_of_card z hU
  have hSneg : ∀ α ∈ rootCharKernel b', -α ∈ rootCharKernel b' := fun α hα =>
    ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hSw : ∀ α ∈ rootCharKernel b', e8T3We 1 • α ∈ rootCharKernel b' := fun α hα =>
    ⟨CFSG.LieType.Chevalley.IsRoot.smul hα.1 _, by
      rw [← weylMatrix_mulVec, mem_fixedCharTuples_iff.1 hb' α, hα.2]
      exact map_one _⟩
  set J' : Finset (Fin Tag.E8.rank) := Finset.univ.filter (fun i => i ∈ J) with hJ'
  have hJJ' : (↑J' : Set (Fin Tag.E8.rank)) = J := by
    ext i
    simp [hJ']
  have hJ'ne : J' ≠ Finset.univ := fun h1 => hJne hz0 (by rw [← hJJ', h1]; simp)
  have hΦJ' : (fun γ => u • γ) '' rootCharKernel b' =
      parabolicRoots Tag.E8 (↑J' : Set (Fin Tag.E8.rank)) := by
    rw [hbS, hJJ']
    exact hΦJ
  obtain ⟨ι', P, i₀, hι'fin, hι'card, hfam, hA, hB, hF⟩ :=
    hLayers n hcm hnC hnW u J' hJ'ne (rootCharKernel b') hΦJ' hSneg hSw hcount
  have hstab : ∀ a : Fin Tag.E8.rank → Lˣ, (∀ i, a i ^ 7 = 1) → a ≠ 1 →
      rootDiagUnit .E8 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup .E8)) := by
    intro a hap' ha1 hmem
    rw [hT] at hmem
    obtain ⟨a', ha', hae⟩ := hmem
    have haa : a' = a := hinj0 hae
    subst haa
    exact rootCharStabilizer_subset_closure_of_fixed (weylMatrix (e8T3We 1)) Fr hFr hp ha' hap'
      ha1 (fun z' hz' hzM' =>
        (dualWeylStabilizer_eq_closure_of_card z'
          (e8T3_dualStab_prime hp (by norm_num) hε hpf hz' hzM')).le)
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hsub : rootCharKernel b' ⊆ rootCharKernel b' := fun α hα => hα
  have hle := rootSpan_le_centralizer (K := L) b' hsub
  have hcS : c * b * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ (rootCharKernel b')) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hbh'] at h1
    exact h1
  have hkerZ : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a ⊆ rootCharKernel b' := fun a ha => by
    rw [hker a ha]
  obtain ⟨ψ, hψinj, -, hPψ, hnorm, hselect⟩ := sigma_components_of_stab ι adjEmb_injective
    adjEmb_mem Φ (adjEmb_frobenius Fr hFr) n g0 hg0C hg0 hperf hp hstab (fun α hα => hα.1) hSneg
    P hPfin hPq hPQ hPR hPadj hPnorm hPcent hb c hcS hkerZ
  exact ⟨ι', P, ψ, hψinj, hι'fin, hι'card, hPfin, hPq, hPψ, hnorm, hselect, ⟨i₀, hA, hB⟩, hF⟩

theorem e8TwoSeven_centralizer_component_family
    (b : adjointGroup .E8 (GaloisField 2 1)) (hb : orderOf b = 7) :
    ∃ (ι' : Type)
      (P : ι' → Subgroup (ModGL .E8 (AlgebraicClosure (GaloisField 2 1))))
      (ψ : Subgroup.centralizer {b} →* ModGL .E8 (AlgebraicClosure (GaloisField 2 1))),
      Function.Injective ψ ∧ Finite ι' ∧ (Nat.card ι' = 1 ∨ Nat.card ι' = 2) ∧
      (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
      (∀ i, P i ≤ ψ.range) ∧
      (∀ i, ∀ d : Subgroup.centralizer {b}, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) ∧
      (∀ H : Subgroup (adjointGroup .E8 (GaloisField 2 1)),
        CFSG.Assembly.IsComponentOf H (Subgroup.centralizer {b}) →
        ∃ i, (H.subgroupOf (Subgroup.centralizer {b})).map ψ = P i ∧ Nonempty (H ≃* P i)) ∧
      ∃ i₀, 7 ^ 2 ∣ Nat.card (P i₀) ∧
        ∀ z ∈ P i₀, (∀ w ∈ P i₀, z * w = w * z) → z ^ 7 = 1 → z = 1  := by
  have hD4 : D4TrialityLayer Tag.E8 := CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
  have hE6 : E6Layer Tag.E8 := e6Layer_E8
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  obtain ⟨ι', P, ψ, hinj, hfin, hcard, hPfin, hPq, hle, hnorm, hselect, hspec, _⟩ :=
    e8TwoSeven_centralizer_component_family_of_layers (fun _ => True) (by
      intro n hnm hnC hnW u J hJ S hS hSneg hSw hcount
      obtain ⟨ι', P, i₀, hfin, hcard, hfam, hA, hB⟩ :=
        e8T3_seven_layers hD4 hE6 hK n hnm hnC hnW u J hJ hS hSneg hSw hcount
      exact ⟨ι', P, i₀, hfin, hcard, hfam, hA, hB, fun _ => True.intro⟩) b hb
  exact ⟨ι', P, ψ, hinj, hfin, hcard, hPfin, hPq, hle, hnorm, hselect, hspec⟩

theorem ggSixSeventeenE8SevenCompInput_holds : GGSixSeventeenE8SevenCompInput := by
  classical
  intro b hb
  obtain ⟨ι', P, ψ, hψinj, _, _, _, hPq, hPψ, hnorm, _, i₀, hA, hB⟩ :=
    e8TwoSeven_centralizer_component_family b hb
  obtain ⟨Lc, hLc, _, ⟨e⟩⟩ := exists_component_map_eq_mulEquiv_of_normalized_layer ψ hψinj
    (hPψ i₀) (hPq i₀) (hnorm i₀)
  refine ⟨Lc, hLc, ?_, eq_one_of_pow_eq_one_of_central_of_mulEquiv e hB⟩
  rw [Nat.card_congr e.toEquiv]
  exact hA

theorem ggSixSeventeenE8SevenCentInput_holds : GGSixSeventeenE8SevenCentInput :=
  ggSixSeventeenE8SevenCentInput_of_comp ggSixSeventeenE8SevenCompInput_holds

section Labels


theorem e8TwoSeven_centralizer_component_family_with_labels
    (b : adjointGroup .E8 (GaloisField 2 1)) (hb : orderOf b = 7) :
    ∃ (ι' : Type)
      (P : ι' → Subgroup (ModGL .E8 (AlgebraicClosure (GaloisField 2 1))))
      (ψ : Subgroup.centralizer {b} →* ModGL .E8 (AlgebraicClosure (GaloisField 2 1))),
      Function.Injective ψ ∧ Finite ι' ∧ (Nat.card ι' = 1 ∨ Nat.card ι' = 2) ∧
      (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
      (∀ i, P i ≤ ψ.range) ∧
      (∀ i, ∀ d : Subgroup.centralizer {b}, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) ∧
      (∀ H : Subgroup (adjointGroup .E8 (GaloisField 2 1)),
        CFSG.Assembly.IsComponentOf H (Subgroup.centralizer {b}) →
        ∃ i, (H.subgroupOf (Subgroup.centralizer {b})).map ψ = P i ∧ Nonempty (H ≃* P i)) ∧
      (∃ i₀, 7 ^ 2 ∣ Nat.card (P i₀) ∧
        ∀ z ∈ P i₀, (∀ w ∈ P i₀, z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      ∀ i, ∃ lab : LargeEvenLabel,
        lab ∈ [⟨.E6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.A, 2, 1⟩] ∧
        GGHasLabel lab (P i ⧸ Subgroup.center (P i))  := by
  have hD4 : D4TrialityLayer Tag.E8 := CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
  have hE6 : E6Layer Tag.E8 := e6Layer_E8
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  exact e8TwoSeven_centralizer_component_family_of_layers (fun P =>
    ∃ lab : LargeEvenLabel,
      lab ∈ [⟨.E6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.A, 2, 1⟩] ∧
      GGHasLabel lab (P ⧸ Subgroup.center P)) (by
        intro n hnm hnC hnW u J hJ S hS hSneg hSw hcount
        exact e8T3_seven_layers_with_labels hD4 hE6 hK n hnm hnC hnW u J hJ
          hS hSneg hSw hcount) b hb

theorem e8TwoSeven_component_has_label
    (b : adjointGroup .E8 (GaloisField 2 1)) (hb : orderOf b = 7)
    (H : Subgroup (adjointGroup .E8 (GaloisField 2 1)))
    (hH : CFSG.Assembly.IsComponentOf H (Subgroup.centralizer {b})) :
    ∃ lab : LargeEvenLabel,
      lab ∈ [⟨.E6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.A, 2, 1⟩] ∧
      GGHasLabel lab (H ⧸ Subgroup.center H) := by
  obtain ⟨ι', P, ψ, _, _, _, _, _, _, _, hselect, _, hlabels⟩ :=
    e8TwoSeven_centralizer_component_family_with_labels b hb
  obtain ⟨i, _, ⟨eP⟩⟩ := hselect H hH
  obtain ⟨lab, hlist, hlabel⟩ := hlabels i
  let eQ := QuotientGroup.congr _ _ eP.symm (Subgroup.map_center_eq eP.symm)
  exact ⟨lab, hlist, largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨eQ.symm.trans f⟩) hlabel⟩

end Labels

end CFSG.StandardType
