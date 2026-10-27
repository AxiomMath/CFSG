module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.KGLangTorALangElt
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniCore
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
import CFSG.LocalAnalysis.StandardType.GGL45TGSU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem kgLangTorA_uni_cont
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .twA) (hd : 3 ≤ lab.rank + 1) (hq : ¬(lab.rank + 1 = 3 ∧ 2 ^ lab.n = 2))
    (hn : 1 ≤ lab.n) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ lab.n) ^ 2) :
    KGLangAxisTorACont p lab
      (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) F (2 ^ lab.n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) F (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) F (2 ^ lab.n)))
      (LargeEvenMatFieldImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) F (2 ^ lab.n)))) := by
  classical
  let d : ℕ := lab.rank + 1
  let SU : Subgroup (GL (Fin d) F) := LargeEvenSUGroup (Fin d) F (2 ^ lab.n)
  let R : Type := LargeEvenProj SU
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk SU) (LargeEvenGUSet (Fin d) F (2 ^ lab.n))
  let Fd : Set (MulAut R) := LargeEvenMatFieldImage (LargeEvenProjMk SU)
  have hd' : 3 ≤ d := by omega
  change KGLangAxisTorACont p lab R I Fd
  rw [KGLangAxisTorACont]
  intro K _ _ θ hK A hA hAIF α₀ hα₀ hα₀I hcard2 hcardSplit
  have hd2 : 2 ≤ d := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdq' : ¬(d = 3 ∧ 2 ^ lab.n = 2) := by
    intro h
    exact hq ⟨by simpa [d] using h.1, h.2⟩
  have hdq : (d, 2 ^ lab.n) ≠ (3, 2) := fun h => hdq' (Prod.mk.inj h)
  have hsimple : IsSimpleGroup R :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 lab.n hF d hd' hdq
  have hI1 : (1 : MulAut R) ∈ I := by
    refine ⟨1, ?_, ?_⟩
    · rw [LargeEvenGUSet]
      exact ⟨1, one_ne_zero, by simp, by simp⟩
    · intro h h' hh
      have hh' : h' = h := Subtype.ext (by simpa using hh)
      rw [hh']
      simp
  have hna : ∃ a b : R, a * b ≠ b * a :=
    kgLangTorA_nonabelian θ hK hI1 hα₀I
  have hdata : UnitaryFieldData 2 lab.n F := unitaryFieldData_of_card hn hF
  have hinn : GGRawInnField p R I Fd :=
    RecipeFieldSU.ggRawInnField_unitary hdata hF hd' hdq' hp.ne_one
  have hPC : GGRawPCyclic p R I Fd :=
    RecipeFieldSU.ggRawPCyclic_unitary hdata hF hd' hdq'
  have hFC : GGRawFieldConj p R I Fd :=
    RecipeFieldSpU.ggRawFieldConj_unitary hdata hF hd' hdq' hp hp2
  obtain ⟨B₀, X, u₀, f₀, hmem, hdec, hXcard, hu₀, hf₀, hf₀ord, hα₀eq, hXab, hXI, hXf, hXβ⟩ :=
    kgLangTorA_setup hp hsimple hna hinn hPC hFC θ hK hA hAIF hα₀ hα₀I
  have hXgt1 : 1 < Nat.card X := by
    rw [hXcard]
    exact lt_of_lt_of_le (by norm_num : 1 < 2 ^ 2)
      (le_trans (Nat.pow_le_pow_left hp.two_le 2) hcard2)
  have hp3 : 3 ≤ p := by
    have hodd := hp.odd_of_ne_two hp2
    have h2 := hp.two_le
    omega
  obtain ⟨σ, hσord, hσE⟩ := kgLangTorA_uni_field hF hn hd' hdq' hf₀ hf₀ord
  obtain ⟨hpn, -⟩ := kgLangTorA_card_fixed_unitary hn hp hp2 hF hσord
  have hn3 : 3 ≤ lab.n := by
    obtain ⟨m, hm⟩ := hpn
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    calc 3 ≤ p := hp3
      _ = p * 1 := by simp
      _ ≤ p * m := Nat.mul_le_mul_left p hm1
      _ = lab.n := hm.symm
  have hsplitX : p ∣ 2 ^ lab.n + 1 → p ^ (d / p + 2) ≤ Nat.card X := by
    intro hpdvd
    have hs : GGTypeASplitPrime p lab := Or.inr ⟨htag, hpdvd⟩
    have hc := hcardSplit hs
    calc p ^ (d / p + 2) = p ^ ((lab.rank + 1) / p + 2) := by simp [d]
      _ ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} := hc
      _ = Nat.card X := hXcard.symm
  obtain ⟨e, s, heSU, hsSU, heσ, hep, he_notscalar, hsσ, hcomm⟩ :=
    kgLangTorA_uni_core hF hn hd' hdq hp hp2 hσord hXab hXI hσE hXf hXgt1 hsplitX
  obtain ⟨κ, hκsurj, hκker, hκθ⟩ :=
    GGL45TG.SU.exists_cover_unitary hdata hd' (by omega : 2 ≤ lab.n) hK θ
  have hN : LargeEvenGUSet (Fin d) F (2 ^ lab.n) ⊆
      Subgroup.normalizer (SU : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer hdata
  obtain ⟨g₀, hg₀GU, hu₀eq⟩ := TableB.exists_eq_projConj hN hu₀
  have hg₀norm : g₀ ∈ Subgroup.normalizer (SU : Set (GL (Fin d) F)) := hN hg₀GU
  let ψ₀ : SU →* SU :=
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F),
        GGL45TG.SU.map_mem_su hdata σ g.2⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (Matrix.GeneralLinearGroup.map (σ : F →+* F))
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (Matrix.GeneralLinearGroup.map (σ : F →+* F)) _ _ }
  let cg₀ : SU →* SU := (SU.normalizerMonoidHom ⟨g₀, hg₀norm⟩).toMonoidHom
  let κ' : SU →* K := κ.comp cg₀
  have hκ' : ∀ h : SU, θ (QuotientGroup.mk (κ' h)) =
      TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU h) := by
    intro h
    rw [show κ' h = κ (cg₀ h) from rfl, hκθ (cg₀ h)]
    change LargeEvenProjMk SU (cg₀ h) =
      TableB.projConj SU ⟨g₀, hg₀norm⟩ ((h : LargeEvenProj SU))
    rw [TableB.projConj_mk]
    rfl
  have hα₀ψ : ∀ h : SU, kgInducedAut θ α₀ (θ (QuotientGroup.mk (κ' h))) =
      θ (QuotientGroup.mk (κ' (ψ₀ h))) := by
    intro h
    rw [hκ' h, hκ' (ψ₀ h), hα₀eq, hu₀eq]
    have h2 : ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ *
        (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹ : MulAut R) *
        TableB.projConj SU ⟨g₀, hg₀norm⟩) =
        TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ := by group
    calc (TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ *
            (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹)
              (TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU h))
          = ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ *
              (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹) *
              TableB.projConj SU ⟨g₀, hg₀norm⟩) (LargeEvenProjMk SU h) := rfl
        _ = (TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀) (LargeEvenProjMk SU h) := by rw [h2]
        _ = TableB.projConj SU ⟨g₀, hg₀norm⟩ (f₀ (LargeEvenProjMk SU h)) := rfl
        _ = TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU (ψ₀ h)) := by
              rw [hσE h (ψ₀ h) rfl]
  have hβψ : ∀ β ∈ B₀, ∃ ψ : SU →* SU, ψ ⟨e, heSU⟩ = ⟨e, heSU⟩ ∧
      ψ ⟨s, hsSU⟩ = ⟨s, hsSU⟩ ∧
      ∀ h : SU, kgInducedAut θ β (θ (QuotientGroup.mk (κ' h))) =
        θ (QuotientGroup.mk (κ' (ψ h))) := by
    intro β hβ
    have hxX : u₀⁻¹ * kgInducedAut θ β * u₀ ∈ X := hXβ β hβ
    have hxI : u₀⁻¹ * kgInducedAut θ β * u₀ ∈ I := hXI _ hxX
    obtain ⟨B, hBGU, hxIeq⟩ := TableB.exists_eq_projConj hN hxI
    have hBnorm : B ∈ Subgroup.normalizer (SU : Set (GL (Fin d) F)) := hN hBGU
    let ψ : SU →* SU := (SU.normalizerMonoidHom ⟨B, hBnorm⟩).toMonoidHom
    have hgraph : LargeEvenGraphAut (LargeEvenProjMk SU)
        (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹)
        (u₀⁻¹ * kgInducedAut θ β * u₀) := by
      rw [hxIeq]
      intro g g' hgg'
      change TableB.projConj SU ⟨B, hBnorm⟩ ((g : LargeEvenProj SU)) =
        LargeEvenProjMk SU g'
      rw [TableB.projConj_mk]
      have hrep : ((SU.normalizerMonoidHom ⟨B, hBnorm⟩) g : SU) = g' := by
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_coe, hgg']
      rw [hrep]
      rfl
    have hBe := (hcomm B hBGU (u₀⁻¹ * kgInducedAut θ β * u₀) hxX hgraph).1
    have hBs := (hcomm B hBGU (u₀⁻¹ * kgInducedAut θ β * u₀) hxX hgraph).2
    refine ⟨ψ, ?_, ?_, ?_⟩
    · apply Subtype.ext
      change B * e * B⁻¹ = e
      rw [hBe]
      group
    · apply Subtype.ext
      change B * s * B⁻¹ = s
      rw [hBs]
      group
    · intro h
      rw [hκ' h, hκ' (ψ h)]
      have hβeq : kgInducedAut θ β =
          u₀ * TableB.projConj SU ⟨B, hBnorm⟩ * u₀⁻¹ := by
        rw [← hxIeq]
        group
      rw [hβeq, hu₀eq]
      have h2 : ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU ⟨B, hBnorm⟩ *
          (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹ : MulAut R) *
          TableB.projConj SU ⟨g₀, hg₀norm⟩) =
          TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU ⟨B, hBnorm⟩ := by group
      calc (TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU ⟨B, hBnorm⟩ *
            (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹)
              (TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU h))
          = ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU ⟨B, hBnorm⟩ *
              (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹) *
              TableB.projConj SU ⟨g₀, hg₀norm⟩) (LargeEvenProjMk SU h) := rfl
        _ = (TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU ⟨B, hBnorm⟩)
              (LargeEvenProjMk SU h) := by rw [h2]
        _ = TableB.projConj SU ⟨g₀, hg₀norm⟩
              (TableB.projConj SU ⟨B, hBnorm⟩ (LargeEvenProjMk SU h)) := rfl
        _ = TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU (ψ h)) := by
              apply (TableB.projConj SU ⟨g₀, hg₀norm⟩).injective
              rw [show TableB.projConj SU ⟨B, hBnorm⟩ (LargeEvenProjMk SU h) =
                  LargeEvenProjMk SU (ψ h) from by
                change TableB.projConj SU ⟨B, hBnorm⟩ ((h : LargeEvenProj SU)) =
                  LargeEvenProjMk SU (ψ h)
                rw [TableB.projConj_mk]
                rfl]
  have heKne : κ' ⟨e, heSU⟩ ≠ 1 := by
    intro h
    have h1 : θ (QuotientGroup.mk (κ' ⟨e, heSU⟩)) = 1 := by
      rw [h, QuotientGroup.mk_one, map_one]
    rw [hκ' ⟨e, heSU⟩] at h1
    have hproj : LargeEvenProjMk SU ⟨e, heSU⟩ = 1 := by
      apply (TableB.projConj SU ⟨g₀, hg₀norm⟩).injective
      simpa using h1
    have hproj' : ((⟨e, heSU⟩ : SU) : LargeEvenProj SU) = 1 := by
      change LargeEvenProjMk SU ⟨e, heSU⟩ = 1
      exact hproj
    exact he_notscalar
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨e, heSU⟩).mp hproj'))
  have hep' : (⟨e, heSU⟩ : SU) ^ p = 1 := by
    apply Subtype.ext
    exact hep
  have he_fixed' : ψ₀ ⟨e, heSU⟩ = ⟨e, heSU⟩ := by
    apply Subtype.ext
    exact heσ
  have hs_fixed' : ψ₀ ⟨s, hsSU⟩ = ⟨s, hsSU⟩ * ⟨e, heSU⟩ := by
    apply Subtype.ext
    exact hsσ
  haveI hSUperf : Group.IsPerfect SU :=
    Subgroup.isPerfect_iff.mpr (GGL45TG.SU.commutator_su hdata hd' (by omega : 2 ≤ lab.n))
  have hSU : commutator SU = ⊤ := Group.IsPerfect.commutator_eq_top
  obtain ⟨k, eK, heKne', heKp, hAe, hBk, hke⟩ :=
    kgLangTorA_concl_of_lift (H := SU) (K := K) (R := R) hSU θ A B₀ hdec κ'
      ψ₀ hα₀ψ heKne hep' he_fixed' hs_fixed' hβψ
  refine ⟨k, eK, heKne', heKp, hAe, ?_, hke⟩
  intro α hα hαI
  exact hBk α (hmem α hα hαI)

end CFSG.StandardType
