module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofPGL
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONSeven
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONL37
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONTools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate8169
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Res148

open Matrix

theorem center_l37_eq_bot [Fact (Nat.Prime 7)] :
    Subgroup.center (projSL 3 (GaloisField 7 1)) = ⊥ := by
  have hS : IsSimpleGroup (projSL 3 (GaloisField 7 1)) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projSL 3 (GaloisField 7 1)))
      with h | h
  · exact h
  · exfalso
    have hτ := two_pow_three_galoisField_seven
    have hdL : ProjGenLinGroup.mk (Sec4.diagTau hτ) ∈ projSL 3 (GaloisField 7 1) :=
      ⟨_, diagTau_mem_ker_det hτ, rfl⟩
    have huL : ProjGenLinGroup.mk (uniGL (1 : GaloisField 7 1) 0 0) ∈
        projSL 3 (GaloisField 7 1) :=
      ⟨_, uniSub_le_ker_det (mem_uniSub_iff.mpr ⟨1, 0, 0, rfl⟩), rfl⟩
    have hc := Subgroup.mem_center_iff.mp
      (h ▸ Subgroup.mem_top (⟨_, hdL⟩ : projSL 3 (GaloisField 7 1)))
      (⟨_, huL⟩ : projSL 3 (GaloisField 7 1))
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    have h1 : ProjGenLinGroup.mk (Sec4.diagTau hτ * uniGL (1 : GaloisField 7 1) 0 0 *
        (Sec4.diagTau hτ)⁻¹ * (uniGL (1 : GaloisField 7 1) 0 0)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc']
      group
    rw [diagTau_mul_uniGL, uniGL_inv, uniGL_mul] at h1
    have h2 := eq_one_of_mem_uniSub_of_mk_eq_one (mem_uniSub_iff.mpr ⟨_, _, _, rfl⟩) h1
    have h3 := congrArg (fun g : GL (Fin 3) (GaloisField 7 1) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 7 1)) 0 1) h2
    simp only [coe_uniGL, Units.val_one, uniMat] at h3
    simp at h3
    have h7 : (7 : GaloisField 7 1) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (GaloisField 7 1) 7
    have h3' : (3 : GaloisField 7 1) = 0 := by linear_combination h3
    have h1' : (1 : GaloisField 7 1) = 0 := by linear_combination 5 * h3' - 2 * h7
    exact one_ne_zero h1'

theorem exists_surjective_range_of_ker_le {P Λ L : Type*} [Group P] [Group Λ] [Group L]
    (ι : P →* Λ) (f : P →* L) (hf : Function.Surjective f) (hker : ι.ker ≤ f.ker) :
    ∃ f' : ι.range →* L, Function.Surjective f' := by
  refine ⟨(QuotientGroup.lift ι.ker f hker).comp
    (QuotientGroup.quotientKerEquivRange ι).symm.toMonoidHom, fun z => ?_⟩
  obtain ⟨w, rfl⟩ := hf z
  refine ⟨⟨ι w, w, rfl⟩, ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivRange ι).symm ⟨ι w, w, rfl⟩ =
      ((w : P) : P ⧸ ι.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1,
    QuotientGroup.lift_mk]

end Res148

open Res148

section ON


theorem kf148ONInner_holds : KF148ONInner := by
  intro Λ _ _ hperf hT σ hσ3 P hPp hσP _ hf
  obtain ⟨f, hfs⟩ := hf
  set Z := Subgroup.center Λ with hZdef
  have hZ : ∀ z ∈ Z, σ z = z := fix_center_of_pow_three σ hσ3 hT.1
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  obtain ⟨y, hy⟩ := Sec13.ON134.aut_inner ψ σ hZ
  have hy3 : y ^ 3 ∈ Z := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (σ ^ 3) g = g := by rw [hσ3, MulAut.one_apply]
    have h2 : (σ ^ 3) g = y ^ 3 * g * (y ^ 3)⁻¹ := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hy, hy, hy]
      simp only [pow_three, mul_inv_rev, mul_assoc]
    rw [h2] at h1
    calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h1]
      _ = y ^ 3 * g := by group
  have hyP : y ∈ Subgroup.normalizer (P : Set Λ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hy]
      rw [← hσP]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hy] at hx
      rw [← hσP] at hx
      obtain ⟨x', hx', hxx'⟩ := hx
      rw [← σ.injective hxx']
      exact hx'
  set π : Λ →* Λ ⧸ Z := QuotientGroup.mk' Z with hπ
  suffices hclaim : π y ∈ P.map π by
    obtain ⟨p, hp, hpy⟩ := hclaim
    have hz : p⁻¹ * y ∈ Z := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hpy
      exact hpy
    refine ⟨p, hp, fun g => ?_⟩
    rw [hy g]
    have hc := Subgroup.mem_center_iff.mp hz g
    calc y * g * y⁻¹ = p * (p⁻¹ * y * g) * (p⁻¹ * y)⁻¹ * p⁻¹ := by group
      _ = p * (g * (p⁻¹ * y)) * (p⁻¹ * y)⁻¹ * p⁻¹ := by rw [hc]
      _ = p * g * p⁻¹ := by group
  by_contra hcon
  set Pb : Subgroup (Λ ⧸ Z) := P.map π with hPb
  have hyN : π y ∈ Subgroup.normalizer (Pb : Set (Λ ⧸ Z)) :=
    Subgroup.le_normalizer_map π ⟨y, hyP, rfl⟩
  have hyb3 : π y ^ 3 = 1 := by
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy3
  obtain ⟨χ⟩ := hT.2
  set φ : Λ ⧸ Z ≃* ONSchreier.Pv := χ.trans ONSchreier.onEquivPv with hφ
  set ι : P →* Λ ⧸ Z := π.comp P.subtype with hι
  have hιr : ι.range = Pb := by rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ι.ker ≤ f.ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have hpZ : (p : Λ) ∈ Z := by
      rw [hι, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hp
      exact hp
    have hfc : f p ∈ Subgroup.center (projSL 3 (GaloisField 7 1)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨q, rfl⟩ := hfs w
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp hpZ q)
    rw [center_l37_eq_bot] at hfc
    exact hfc
  obtain ⟨f₁, hf₁⟩ := exists_surjective_range_of_ker_le ι f hfs hker
  set NP := Subgroup.normalizer (Pb : Set (Λ ⧸ Z)) with hNP
  have hPbNP : Pb ≤ NP := Subgroup.le_normalizer
  set H : Subgroup NP := Pb.subgroupOf NP with hH
  have : H.Normal := Subgroup.normal_in_normalizer
  set eH : H ≃* ι.range :=
    (Subgroup.subgroupOfEquivOfLe hPbNP).trans (MulEquiv.subgroupCongr hιr.symm) with heH
  set fH : H →* projSL 3 (GaloisField 7 1) := f₁.comp eH.toMonoidHom with hfH
  have hfHs : Function.Surjective fH := hf₁.comp eH.surjective
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 7 H))
  have h3 : 3 ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup H) : Set H)) := by
    refine three_dvd_card_normalizer_of_surjective fH hfHs Q ?_
    have := three_dvd_card_normalizer_sylow_seven_l37 (Q.mapSurjective hfHs)
    rwa [Sylow.coe_mapSurjective] at this
  have hQcard : 7 ^ 3 ≤ Nat.card Q := by
    have h1 := card_sylow_seven_l37 (Q.mapSurjective hfHs)
    rw [Sylow.coe_mapSurjective] at h1
    rw [← h1]
    exact Subgroup.card_map_dvd _ _ |> Nat.le_of_dvd Nat.card_pos
  set g : NP := ⟨π y, hyN⟩ with hg
  have hgH : g ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]
    exact hcon
  have hg3 : g ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hg]; exact hyb3)
  have h9 := nine_dvd_card_normalizer_of_normal Q hgH hg3 h3
  set Qt : Subgroup NP := (Q : Subgroup H).map H.subtype with hQt
  set Qh : Subgroup (Λ ⧸ Z) := Qt.map NP.subtype with hQh
  have hQhcard : Nat.card Qh = Nat.card Q := by
    rw [hQh, Subgroup.card_map_of_injective NP.subtype_injective, hQt,
      Subgroup.card_map_of_injective H.subtype_injective]
  have h9' : 9 ∣ Nat.card (Subgroup.normalizer (Qh : Set (Λ ⧸ Z))) := by
    refine h9.trans ?_
    have hle : (Subgroup.normalizer (Qt : Set NP)).map NP.subtype ≤
        Subgroup.normalizer (Qh : Set (Λ ⧸ Z)) := Subgroup.le_normalizer_map _
    rw [← Subgroup.card_map_of_injective NP.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hQhp : IsPGroup 7 Qh := by
    have hQp : IsPGroup 7 (Q : Subgroup H) := Q.isPGroup'
    exact (hQp.map H.subtype).map NP.subtype
  obtain ⟨S, hS⟩ := hQhp.exists_le_sylow
  obtain ⟨hScard, hSN⟩ := sylow_seven_of_mulEquiv_Pv φ S
  have hQhS : Qh = S := by
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    rw [hScard, hQhcard]
    exact hQcard
  rw [hQhS] at h9'
  exact hSN h9'

end ON

section Steps


theorem step148PGLON_holds : Step148PGLON :=
  step148PGLON_of kf148ONInner_holds

end Steps

end CFSG.RankThree.PartTwo.Sec14
