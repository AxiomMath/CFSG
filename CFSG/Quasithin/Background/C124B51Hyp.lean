module

public import CFSG.Quasithin.Background.C124B51Ident
public import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.Background.B5Irr
public import CFSG.Quasithin.Background.C124AltL345
public import CFSG.Quasithin.Background.C124Offender

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Fitting

theorem pCoreOf_le_genFitting' {Γ : Type*} [Group Γ] [Finite Γ] (H : Subgroup Γ) :
    pCoreOf 2 H ≤ quasithinGenFitting H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold quasithinGenFitting
  refine le_sup_of_le_left (le_sSup ⟨pCoreOf_le 2 H, ?_, ?_⟩)
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr
      (le_normalizer_pCoreOf 2 H)
  · exact (pCoreOf_isPGroup 2 H).isNilpotent

theorem centerOf_le_genFitting' {W : Type} [CommGroup W] (G : Subgroup (MulAut W)) :
    centerOf G ≤ quasithinGenFitting G := by
  unfold quasithinGenFitting
  refine le_sup_of_le_left (le_sSup ⟨inf_le_left, ?_, ?_⟩)
  · refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hz : (g : MulAut W) * (x : MulAut W) * (g : MulAut W)⁻¹ = (x : MulAut W) :=
      mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hx.2 (g : MulAut W) g.2)
    simpa [hz] using hx
  · have : IsMulCommutative ↥(centerOf G) := ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 b.2.2 _ a.2.1)⟩⟩
    infer_instance

end Fitting

section Hyp

theorem ffJP_eq_ffJ {W : Type} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    {P : Set (Subgroup (MulAut W))} (hP : ∀ A ∈ P, IsFFStarOffender X A) :
    ffJP P X = ffJ (ffJP P X) := by
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hAP => iSup_le fun hAX => ?_
    have hAH : A ≤ ffJP P X := le_iSup_of_le A (le_iSup_of_le hAP (le_iSup_of_le hAX le_rfl))
    have hoff : IsFFStarOffender (ffJP P X) A :=
      ⟨hAH, (hP A hAP).2.1, (hP A hAP).2.2.1, (hP A hAP).2.2.2⟩
    exact le_iSup_of_le A (le_iSup_of_le hoff le_rfl)
  · exact iSup_le fun A => iSup_le fun hA => hA.1

variable {G : Type} [Group G] [Finite G]

theorem sqtk_autI {X L V : Subgroup G} (hV : IsElemAbelian 2 V) (hA21 : AsA21SQTKSection)
    (hSQ : SQTKGroup ↥X) (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X)
    (hq : CFSG.IsQuasisimple ↥(autI hV L)) : SQTKGroup ↥(autI hV L) := by
  let π : ↥(L.subgroupOf X) →* ↥(autI hV L) :=
    ((convHom hV X hXN).comp (L.subgroupOf X).subtype).codRestrict (autI hV L) fun g =>
      convI_mem_autI hV (Subgroup.mem_subgroupOf.1 g.2) (hXN g.1.2)
  refine B69.sqtk_of_surj hA21 hSQ π ?_ hq
  intro φ
  obtain ⟨g, hg, hgφ⟩ := (mem_autI hV).1 φ.2
  exact ⟨⟨⟨g, hLX hg⟩, Subgroup.mem_subgroupOf.2 hg⟩, Subtype.ext hgφ⟩

theorem b51Hyp_ffJP {X L V R : Subgroup G} (hV : IsElemAbelian 2 V) (hA21 : AsA21SQTKSection)
    (hSQ : SQTKGroup ↥X) (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X)
    (hstab : IsStableFF (autI hV X) (offenderImagesConjIn hV X R))
    (hF : quasithinGenFitting (ffJP (offenderImagesConjIn hV X R) (autI hV X)) = autI hV L)
    (hq : CFSG.IsQuasisimple ↥(autI hV L)) (hO2 : pCoreOf 2 (autI hV L) = ⊥) :
    B51Hyp (ffJP (offenderImagesConjIn hV X R) (autI hV X)) (autI hV L) := by
  set H := ffJP (offenderImagesConjIn hV X R) (autI hV X) with hH
  have hLH : autI hV L ≤ H := hF ▸ quasithinGenFitting_le H
  refine ⟨?_, hq, sqtk_autI hV hA21 hSQ hXN hLX hq, hLH, ?_, ffJP_eq_ffJ hstab.2.1⟩
  · rw [sup_eq_left.2 (hF ▸ centerOf_le_genFitting' H), hF]
  · refine eq_bot_iff.2 fun x hx => ?_
    have h1 : x ∈ quasithinGenFitting H := pCoreOf_le_genFitting' H hx
    rw [hF] at h1
    have hN : pCoreOf 2 H ⊓ autI hV L ≤ pCoreOf 2 (autI hV L) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pCoreOf 2 H (hLH hl), Subgroup.le_normalizer hl⟩)
        ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    have h2 : x ∈ pCoreOf 2 (autI hV L) := hN ⟨hx, h1⟩
    rw [hO2] at h2
    exact h2

theorem b51Case1i_ffJP {X L V R : Subgroup G} (hV : IsElemAbelian 2 V) (hI : B5.B51IrrInputs)
    (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover)
    (hSQ : SQTKGroup ↥X) (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X)
    (hstab : IsStableFF (autI hV X) (offenderImagesConjIn hV X R))
    (hF : quasithinGenFitting (ffJP (offenderImagesConjIn hV X R) (autI hV X)) = autI hV L)
    (hq : CFSG.IsQuasisimple ↥(autI hV L)) (hO2 : pCoreOf 2 (autI hV L) = ⊥) {m : ℕ}
    (hm : m = 5 ∨ m = 6 ∨ m = 7) {z : ℕ} (hz : Odd z)
    (hcard : Nat.card ↥(autI hV L) = Nat.card (alternatingGroup (Fin m)) * z) :
    B51Case1i (ffJP (offenderImagesConjIn hV X R) (autI hV X)) (autI hV L) := by
  have hHyp := b51Hyp_ffJP hV hA21 hSQ hXN hLX hstab hF hq hO2
  have hU : commV (autI hV L) ∈ IrrPlus (autI hV L) ⊤ := by
    by_contra hU
    exact not_isL345Type_of_alt hm hz hcard
      (B5.b51_ident hA21 hI.b42 hA36 IntMod.sq_eq_one hHyp hU)
  exact B5.b51_case1i hI IntMod.sq_eq_one hHyp hU

end Hyp

end CFSG.Quasithin.C124
