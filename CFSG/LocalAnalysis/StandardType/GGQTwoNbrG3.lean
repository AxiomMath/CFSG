module
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxModel
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG3Aux
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxKb
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
public import CFSG.ClassicalInvolution.Q3.Q3T6FaField
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step25
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public section
namespace CFSG.StandardType.QTwo
open CFSG.StandardType
open CFSG.Assembly
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
private theorem qTwoNbrH_exists_perm {d : ℕ} (I0 I : Finset (Fin d)) (hI0 : I0.card = 4)
    (hI : I.card = 4) :
    ∃ σ : Equiv.Perm (Fin d), I0.map σ.toEmbedding = I :=
  Equiv.Perm.exists_map_finset_eq I0 I (by rw [hI0, hI])
private theorem qTwoNbrH_as_sc {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hBs : GGBstar 3 B Bs) (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    letI := hM.groupQ
    ∀ g ∈ Subgroup.centralizer (hM.As : Set hM.Q), g ^ 3 = 1 → g ∈ hM.As := by
  classical
  letI := hM.groupQ
  let H : Subgroup G := K ⊔ Bs
  let N : Subgroup ↥H := hM.Delta.subgroupOf H
  haveI hNnorm : N.Normal := by
    dsimp only [N]
    rw [← hM.hq_ker]
    exact MonoidHom.normal_ker hM.q
  have hH : K ≤ H := le_sup_left
  have hBsH : Bs ≤ H := le_sup_right
  have hNs : N ≤ K.subgroupOf H := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hM.hDelta_le_K (Subgroup.mem_subgroupOf.mp hz))
  have hBs_p : IsPGroup 3 (Bs.subgroupOf H) :=
    (CFSG.Open.IsElemAbelian.isPGroup hBs.2.1).comap_subtype
  have hpN : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hM.hDelta_pgroup.comap_subtype : IsPGroup 2 N)
    dsimp only [N] at hk ⊢
    change ¬ 3 ∣ Nat.card ↥(Subgroup.comap H.subtype hM.Delta)
    rw [hk]
    intro hdiv
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv)
  have hSC_H : ∀ z ∈ Subgroup.centralizer ((Bs.subgroupOf H : Subgroup H) : Set H),
      z ^ 3 = 1 → z ∈ Bs.subgroupOf H := by
    intro z hz hz3
    have hzG : (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbH : (⟨b, hBsH hb⟩ : ↥H) ∈ Bs.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
      have hcomm := (Subgroup.mem_centralizer_iff.mp hz) ⟨b, hBsH hb⟩ hbH
      exact congrArg (fun w : ↥H => (w : G)) hcomm
    have hz3G : (z : G) ^ 3 = 1 := by simpa using congrArg (fun w : ↥H => (w : G)) hz3
    exact Subgroup.mem_subgroupOf.mpr (hBs.2.2.2 (z : G) hzG hz3G)
  have hSC_quot := bstar_selfCent_map_mk'_of_coprime (p := 3) (N := N)
    (Bs := Bs.subgroupOf H) hpN hBs_p hSC_H
  let e : (↥H ⧸ N) ≃* hM.Q :=
    QuotientGroup.liftEquiv (N := N) (φ := hM.q) hM.hq_surj hM.hq_ker.symm
  have he_mk : ∀ z : ↥H, e (QuotientGroup.mk' N z) = hM.q z :=
    fun z => QuotientGroup.liftEquiv_mk (N := N) (φ := hM.q) hM.hq_surj hM.hq_ker.symm z
  have hAs_eq : hM.As = ((Bs.subgroupOf H).map (QuotientGroup.mk' N)).map e.toMonoidHom := by
    rw [hM.hAs]
    ext q
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨QuotientGroup.mk' N ⟨(b : G), hBsH b.2⟩, ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr b.2)
      · change e (QuotientGroup.mk' N ⟨(b : G), hBsH b.2⟩) =
          hM.q ⟨(b : G), hBsH b.2⟩
        exact he_mk ⟨(b : G), hBsH b.2⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
      refine ⟨⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩, ?_⟩
      change hM.q b = e (QuotientGroup.mk' N b)
      exact (he_mk b).symm
  intro g hg hg3
  let g' : ↥H ⧸ N := e.symm g
  have hg'C : g' ∈ Subgroup.centralizer
      ((Bs.subgroupOf H).map (QuotientGroup.mk' N) : Set (↥H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    apply e.injective
    rw [map_mul, map_mul, he_mk]
    have hbAs : hM.q b ∈ hM.As := by
      rw [hM.hAs]
      exact ⟨⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hg _ hbAs
    have hgg : e g' = g := MulEquiv.apply_symm_apply e g
    rw [hgg]
    exact hcomm
  have hg'3 : g' ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    have hgg : e g' = g := MulEquiv.apply_symm_apply e g
    rw [hgg]
    exact hg3
  have hg'mem := hSC_quot g' hg'C hg'3
  rw [hAs_eq]
  exact Subgroup.mem_map.mpr ⟨g', hg'mem, MulEquiv.apply_symm_apply e g⟩
private theorem qTwoNbrH_as_elemAbelian {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hBs : GGBstar 3 B Bs) (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    letI := hM.groupQ
    IsElemAbelian 3 hM.As := by
  letI := hM.groupQ
  rw [hM.hAs]
  constructor
  · refine IsMulCommutative.of_setLike_mul_comm ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact hBs.2.1.1.is_comm.comm a b
  · rintro _ ⟨a, rfl⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hBs.2.1.2 a a.2)
    rw [← map_pow (hM.q.comp (Subgroup.inclusion (le_sup_right : Bs ≤ K ⊔ Bs))) a 3, ha3,
      map_one]
theorem qTwoNbrH_as_normalizes {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    letI := hM.groupQ
    hM.As ≤ Subgroup.normalizer (hM.Kbar : Set hM.Q) := by
  letI := hM.groupQ
  intro b hb
  rw [hM.hAs] at hb
  obtain ⟨b', rfl⟩ := MonoidHom.mem_range.mp hb
  have hq := qTwoNbrRec_mem_normalizer_Kb hM.q hM.hBsN b'.2
  change hM.q ⟨(b' : G), (le_sup_right : Bs ≤ K ⊔ Bs) b'.2⟩ ∈
    Subgroup.normalizer (hM.Kbar : Set hM.Q)
  rw [show qTwoNbrRec_Kb hM.q = hM.Kbar from by rw [qTwoNbrRec_Kb, hM.hKbar]] at hq
  exact hq
private theorem qTwoNbrH_unitTBModel {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    letI := hM.groupQ
    letI := hM.fieldF0
    letI := hM.finiteF0
    letI := hM.charF0
    letI := hM.factF0
    UnitTB.Model ((hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom).codRestrict
      hM.Kbar (fun z => by
        rw [← hM.hψ_range]
        exact ⟨(qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z, rfl⟩)) := by
  classical
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  have hd5 : 5 ≤ hM.d := hM.hd
  let ψr : ↥(unitarySU 2 1 hM.F0 hM.d) →* hM.Kbar :=
    (hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom).codRestrict hM.Kbar
      (fun z => by
        rw [← hM.hψ_range]
        exact ⟨(qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z, rfl⟩)
  refine ⟨TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num), ?_, ?_⟩
  · intro y
    have hy : (y : hM.Q) ∈ hM.ψ.range := by
      rw [hM.hψ_range]
      exact y.2
    obtain ⟨w, hw⟩ := hy
    exact ⟨qTwoNbrRec_suEquiv hM.hcardF0 hM.d w, Subtype.ext hw⟩
  · intro z hz
    have hz1 : hM.ψ ((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z) = 1 := by
      have := congrArg Subtype.val hz
      simpa only [ψr, MonoidHom.codRestrict_apply, Subgroup.coe_one, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using this
    have hzker : (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z ∈ hM.ψ.ker :=
      MonoidHom.mem_ker.mpr hz1
    have hzcent := hM.hψ_ker hzker
    have hzcenterU : qTwoNbrRec_suEquiv hM.hcardF0 hM.d
        ((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z) ∈
        Subgroup.center (↥(unitarySU 2 1 hM.F0 hM.d)) := by
      rw [MulEquiv.apply_symm_apply]
      have hmapc : (Subgroup.center (Su hM.F0 2 1 hM.d)).map
          (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).toMonoidHom =
          Subgroup.center (↥(unitarySU 2 1 hM.F0 hM.d)) :=
        Subgroup.map_center_eq (qTwoNbrRec_suEquiv hM.hcardF0 hM.d)
      rw [← hmapc]
      exact Subgroup.mem_map_of_mem _ hzcent
    have hzcenterU' : z ∈ Subgroup.center (↥(unitarySU 2 1 hM.F0 hM.d)) := by
      simpa using hzcenterU
    have hscal := center_statedSU_le_scalars (n := 1) (d := hM.d) (F := hM.F0)
      (by simpa using hM.hcardF0) (by omega) hzcenterU' 
    obtain ⟨c, hc⟩ := hscal
    refine ⟨(c : hM.F0), ?_⟩
    change (((Open.StatedSU hM.d (2 ^ 1) hM.F0).subtype z : GL (Fin hM.d) hM.F0) :
      Matrix (Fin hM.d) (Fin hM.d) hM.F0) = Matrix.diagonal (fun _ => (c : hM.F0))
    rw [congrArg (fun g : GL (Fin hM.d) hM.F0 =>
      (g : Matrix (Fin hM.d) (Fin hM.d) hM.F0)) hc.symm, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
private theorem qTwoNbrH_actsDiagU {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    letI := hM.groupQ
    letI := hM.fieldF0
    letI := hM.finiteF0
    letI := hM.charF0
    letI := hM.factF0
    ∀ a ∈ (ggGamma hM.Kbar (qTwoNbrH_as_normalizes hM)).range,
      ∃ t : Fin hM.d → hM.F0,
        LineU.ActsDiagU
          ((hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom).codRestrict
            hM.Kbar (fun z => by
              rw [← hM.hψ_range]
              exact ⟨(qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z, rfl⟩)) a t := by
  classical
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  let hN : hM.As ≤ Subgroup.normalizer (hM.Kbar : Set hM.Q) := qTwoNbrH_as_normalizes hM
  have hd5 : 5 ≤ hM.d := hM.hd
  haveI : Finite hM.Q := Finite.of_surjective hM.q hM.hq_surj
  let ψr : ↥(unitarySU 2 1 hM.F0 hM.d) →* hM.Kbar :=
    (hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom).codRestrict hM.Kbar
      (fun z => by
        rw [← hM.hψ_range]
        exact ⟨(qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z, rfl⟩)
  intro a ha
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨g, hgdiag, hgind⟩ := hM.hdiag b b.2
  obtain ⟨t, ht⟩ := hgdiag
  refine ⟨t, ?_⟩
  have hNsuid : g ∈ Subgroup.normalizer
      (unitarySU 2 1 hM.F0 hM.d : Set (GL (Fin hM.d) hM.F0)) := by
    have h1 := InnerDiagSU.mem_normalizer_SUid (B := g)
      (σ := CFSG.LieType.BorelTits.unitaryInvolution hM.F0 2 1) (n := hM.d) hgind.1
    simpa [show unitarySU 2 1 hM.F0 hM.d = StatedSU hM.d (2 ^ 1) hM.F0 from rfl,
      ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1)
        (by simpa using hM.hcardF0) hM.d] using h1
  refine ⟨g, hNsuid, ht, ?_⟩
  intro z
  obtain ⟨y, hy, hyψ⟩ := hgind.2 ((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z)
  have hcoe : ∀ w : ↥(unitarySU 2 1 hM.F0 hM.d),
      (((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm w : Su hM.F0 2 1 hM.d) :
        GL (Fin hM.d) hM.F0) = (w : GL (Fin hM.d) hM.F0) := fun w => by
    have h := qTwoNbrRec_coe_suEquiv hM.hcardF0
      ((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm w)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hy_eq : y = (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm
      (LineU.conjN g hNsuid z) := by
    apply Subtype.ext
    rw [hy, hcoe z, hcoe, LineU.coe_conjN]
  apply Subtype.ext
  rw [ggGamma_coe]
  show (b : hM.Q) * hM.ψ ((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z) * (b : hM.Q)⁻¹ =
    hM.ψ ((qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm (LineU.conjN g hNsuid z))
  rw [hyψ, hy_eq]
private theorem qTwoNbrH_native_normalizer {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hGs : GGBstar 3 B Bs) (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    letI := hM.groupQ
    letI := hM.fieldF0
    letI := hM.finiteF0
    letI := hM.charF0
    letI := hM.factF0
    ∀ σ : Equiv.Perm (Fin hM.d),
      (hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom)
        (LineU.permSU (TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num)) σ) ∈
        Subgroup.normalizer (hM.As : Set hM.Q) := by
  classical
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  let hN : hM.As ≤ Subgroup.normalizer (hM.Kbar : Set hM.Q) := qTwoNbrH_as_normalizes hM
  have hd5 : 5 ≤ hM.d := hM.hd
  haveI : Finite hM.Q := Finite.of_surjective hM.q hM.hq_surj
  let ψr : ↥(unitarySU 2 1 hM.F0 hM.d) →* hM.Kbar :=
    (hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom).codRestrict hM.Kbar
      (fun z => by
        rw [← hM.hψ_range]
        exact ⟨(qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm z, rfl⟩)
  intro σ
  have h := qTwoNbrG3_weyl_normalizer_of_cover (d := hM.d) (by simpa using hM.hcardF0) hd5
    (qTwoNbrH_as_elemAbelian hGs hM) (qTwoNbrH_as_sc hGs hM) hN (ψ := ψr)
    (qTwoNbrH_unitTBModel hM) (qTwoNbrH_actsDiagU hM) σ
  simpa [ψr] using h
private theorem qTwoNbrH_sylow {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hM : QTwoNbrModel 3 B Bs x L D J y K)
    (hBs : GGBstar 3 B Bs) :
    letI := hM.groupQ
    ∀ {k : G} (hk : k ∈ K),
      hM.q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) hk⟩ ∈
        Subgroup.normalizer (hM.As : Set hM.Q) →
      ∃ n, ∃ hn : n ∈ K, n ∈ Subgroup.normalizer (Bs : Set G) ∧
        hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩ =
          hM.q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) hk⟩ := by
  classical
  letI := hM.groupQ
  let H : Subgroup G := K ⊔ Bs
  let N : Subgroup ↥H := hM.Delta.subgroupOf H
  haveI hNnorm : N.Normal := by
    dsimp only [N]
    rw [← hM.hq_ker]
    exact MonoidHom.normal_ker hM.q
  have hH : K ≤ H := le_sup_left
  have hBsH : Bs ≤ H := le_sup_right
  have hNs : N ≤ K.subgroupOf H := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hM.hDelta_le_K (Subgroup.mem_subgroupOf.mp hz))
  have hBs_p : IsPGroup 3 (Bs.subgroupOf H) :=
    (CFSG.Open.IsElemAbelian.isPGroup hBs.2.1).comap_subtype
  have hpN : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hM.hDelta_pgroup.comap_subtype : IsPGroup 2 N)
    dsimp only [N] at hk ⊢
    change ¬ 3 ∣ Nat.card ↥(Subgroup.comap H.subtype hM.Delta)
    rw [hk]
    intro hdiv
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv)
  let e : (↥H ⧸ N) ≃* hM.Q :=
    QuotientGroup.liftEquiv (N := N) (φ := hM.q) hM.hq_surj hM.hq_ker.symm
  have he_mk : ∀ z : ↥H, e (QuotientGroup.mk' N z) = hM.q z :=
    fun z => QuotientGroup.liftEquiv_mk (N := N) (φ := hM.q) hM.hq_surj hM.hq_ker.symm z
  have hAs_eq : hM.As = ((Bs.subgroupOf H).map (QuotientGroup.mk' N)).map e.toMonoidHom := by
    rw [hM.hAs]
    ext q
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨QuotientGroup.mk' N ⟨(b : G), hBsH b.2⟩, ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr b.2)
      · change e (QuotientGroup.mk' N ⟨(b : G), hBsH b.2⟩) =
          hM.q ⟨(b : G), hBsH b.2⟩
        exact he_mk ⟨(b : G), hBsH b.2⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
      refine ⟨⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩, ?_⟩
      change hM.q b = e (QuotientGroup.mk' N b)
      exact (he_mk b).symm
  intro k hk hnorm
  let kH : ↥H := ⟨k, hH hk⟩
  have hk_quot : QuotientGroup.mk' N kH ∈
      Subgroup.normalizer (((Bs.subgroupOf H).map (QuotientGroup.mk' N)) : Set (↥H ⧸ N)) := by
    have hnorm_map : (Subgroup.normalizer
        (((Bs.subgroupOf H).map (QuotientGroup.mk' N)) : Set (↥H ⧸ N))).map e.toMonoidHom =
        Subgroup.normalizer (hM.As : Set hM.Q) := by
      rw [Subgroup.map_normalizer_eq_of_bijective (H :=
        (((Bs.subgroupOf H).map (QuotientGroup.mk' N)) : Subgroup (↥H ⧸ N)))
        (f := e.toMonoidHom) e.bijective, hAs_eq]
    have h1 : e (QuotientGroup.mk' N kH) ∈
        Subgroup.map e.toMonoidHom (Subgroup.normalizer
          (((Bs.subgroupOf H).map (QuotientGroup.mk' N)) : Set (↥H ⧸ N))) := by
      rw [hnorm_map, he_mk]
      exact hnorm
    obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp h1
    have hzk : z = QuotientGroup.mk' N kH := e.injective hze
    rw [← hzk]
    exact hz
  have hk_inf : QuotientGroup.mk' N kH ∈
      (Subgroup.normalizer ((Bs.subgroupOf H : Subgroup H) : Set ↥H) ⊓
        K.subgroupOf H).map (QuotientGroup.mk' N) := by
    rw [normalizer_map_mk'_inf_eq (p := 3) (N := N) (H := K.subgroupOf H)
      (Bs := Bs.subgroupOf H) hpN hBs_p hNs]
    exact ⟨hk_quot, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)⟩
  obtain ⟨n, hn, hn_eq⟩ := Subgroup.mem_map.mp hk_inf
  have hnK : (n : G) ∈ K := Subgroup.mem_subgroupOf.mp hn.2
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hbH : (⟨b, hBsH hb⟩ : ↥H) ∈ Bs.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
      have hmem := (Subgroup.mem_normalizer_iff.mp hn.1) ⟨b, hBsH hb⟩ |>.mp hbH
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro hb
      have hbH : (⟨n * b * n⁻¹, hBsH hb⟩ : ↥H) ∈ Bs.subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr hb
      have hmem := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn.1))
        ⟨n * b * n⁻¹, hBsH hb⟩ |>.mp hbH
      simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp hmem
  refine ⟨(n : G), hnK, hnN, ?_⟩
  have hqeq : hM.q n = hM.q kH := by
    rw [← he_mk n, ← he_mk kH, hn_eq]
  simpa [kH] using hqeq
private theorem qTwoNbrH_block_conj {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel 3 B Bs x L D J y K)
    {I0 I : Finset (Fin hM.d)} {σ : Equiv.Perm (Fin hM.d)}
    (hσ : I0.map σ.toEmbedding = I) :
    letI := hM.groupQ
    letI := hM.fieldF0
    letI := hM.finiteF0
    letI := hM.charF0
    letI := hM.factF0
    ∀ {n : G} (hn : n ∈ K),
      hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩ =
        (hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom)
          (LineU.permSU (TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num)) σ) →
      (coordBlockSU hM.F0 2 1 I).map hM.ψ =
        ((coordBlockSU hM.F0 2 1 I0).map hM.ψ).map
          (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩)).toMonoidHom := by
  classical
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  intro n hn hqn
  let g : Su hM.F0 2 1 hM.d :=
    (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm
      (LineU.permSU (TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num)) σ)
  have hmat : ((g : GL (Fin hM.d) hM.F0) : Matrix (Fin hM.d) (Fin hM.d) hM.F0) =
      σ⁻¹.permMatrix hM.F0 := by
    change ((((LineU.permSU (TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num)) σ :
      ↥(unitarySU 2 1 hM.F0 hM.d)) : GL (Fin hM.d) hM.F0) :
        Matrix (Fin hM.d) (Fin hM.d) hM.F0)) = σ⁻¹.permMatrix hM.F0
    rw [LineU.coe_permSU, LineU.coe_permGL_matrix]
  have hmono : IsMonomialFor (suMat g) σ := by
    rw [show suMat g = σ⁻¹.permMatrix hM.F0 from hmat]
    simpa [Matrix.permMatrixHom_apply] using isMonomialFor_permMatrixHom (K := hM.F0) σ
  have hmap := map_coordBlockSU_of_monomial (F := hM.F0) (p := 2) (f := 1) hmono I0
  rw [hσ] at hmap
  have hqg : hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩ = hM.ψ g := hqn
  have hcomp : (MulAut.conj (hM.ψ g)).toMonoidHom.comp hM.ψ =
      hM.ψ.comp (MulAut.conj g).toMonoidHom := by
    ext z
    simp [MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [hqg, Subgroup.map_map, hcomp, ← Subgroup.map_map, hmap]
theorem qTwoNbr_normalTransport {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hBs : GGBstar 3 B Bs) (hM : QTwoNbrModel 3 B Bs x L D J y K) :
    ggQTwoNbrTransportProp hM := by
  classical
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  have hd5 : 5 ≤ hM.d := hM.hd
  let I0 : Finset (Fin hM.d) :=
    {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩}
  have hI0 : I0.card = 4 := by
    dsimp only [I0]
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]
  refine ⟨I0, hI0, ?_⟩
  intro I hI
  obtain ⟨σ, hσ⟩ := qTwoNbrH_exists_perm I0 I hI0 hI
  let s : hM.Q :=
    (hM.ψ.comp (qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm.toMonoidHom)
      (LineU.permSU (TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num)) σ)
  have hs : s ∈ Subgroup.normalizer (hM.As : Set hM.Q) := by
    dsimp only [s]
    exact qTwoNbrH_native_normalizer hBs hM σ
  have hsK : s ∈ hM.Kbar := by
    rw [← hM.hψ_range]
    exact ⟨(qTwoNbrRec_suEquiv hM.hcardF0 hM.d).symm
      (LineU.permSU (TableBU.unitaryFieldData_of_card hM.hcardF0 (by norm_num)) σ), rfl⟩
  rw [hM.hKbar] at hsK
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hsK
  have hkq : hM.q ⟨(k : G), (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ = s := hk
  have hnorm : hM.q ⟨(k : G), (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ ∈
      Subgroup.normalizer (hM.As : Set hM.Q) := by
    rw [hkq]
    exact hs
  obtain ⟨n, hn, hnN, hnq⟩ := qTwoNbrH_sylow hM hBs (k := (k : G)) k.2 hnorm
  refine ⟨n, hn, hnN, ?_⟩
  exact qTwoNbrH_block_conj hM hσ hn (hnq.trans hkq)
end CFSG.StandardType.QTwo
end
