module

public import CFSG.Quasithin.Background.C116Three.Top
public import CFSG.Quasithin.Background.C116Three.GroupPairA38
public import CFSG.Quasithin.Background.C116Three.PairHypAutI
public import CFSG.Quasithin.Background.C116Three.AutIFacts
public import CFSG.Quasithin.Background.C116Three.NoBigSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Quot
public import CFSG.Quasithin.EmptyFaithful.R3c23Glue3

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fixedVector3_of_modulePairFV
    (hM : ModulePairFV) (h38 : A38ForSQTK) :
    FixedVector3Statement := by
  intro G _ _ H T V L hH hVred hT hSQ hL hq hnJ hTN
  obtain ⟨t, P⟩ := groupPair h38 hH hT hSQ hL hTN
  have hVe : IsElemAbelian 2 V := hVred.2.2.1
  have hVH : V ≤ H := hVred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hVred.2.1
  have hTH : T ≤ H := hT.1
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hVT : V ≤ T := le_of_isTwoReducedIn hVred hT
  have hTNV : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hqd : QuasiData V L := hq
  have PH := pairHyp_autI hVred hT hL hqd P
  have hO2 := L246C127.pCoreOf_autI_eq_bot hVe hVred
  have hJV : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) :=
    not_thompsonJ_le_centralizer' hHN hLH hnJ
  have hFF : IsFFModule (autI hVe H) := isFFModule_autI hVe hVH hHN hT hJV
  have hB53 := b53Hyp_autI hSQ hVred
  have hL₁J := le_ffJ_autI hVred hT hL hqd hnJ
  have hJn := ffJ_le_normalizer_autI hVred hL hqd
  have hno := noBigSL3_autI h38 hH hVred hT hSQ hL hqd P
  have hA : ∀ A ∈ offenderImages hVe T, IsFFStarOffender (autI hVe H) A := by
    intro A hA
    have h1 := offenderImages_isFFStarOffender hVe hVT hTNV hA
    refine ⟨?_, h1.2⟩
    exact h1.1.trans (autI_mono hVe hTH)
  have hQ2 : IsPGroup 2 (autI hVe (thompsonJ T)) := by
    have h1 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTNV).symm
    have h2 : IsPGroup 2 (autI hVe T) := h1.map (convI hVe)
    exact h2.to_le (autI_mono hVe (GammaExtra.thompsonJ_le_self T))
  have hAQ : ∀ A ∈ offenderImages hVe T, A ≤ autI hVe (thompsonJ T) := by
    rintro A ⟨A₀, hA₀, rfl⟩
    exact autI_mono hVe (GammaExtra.le_thompsonJ hA₀.1)
  have hQG : autI hVe (thompsonJ T) ≤ ffJ (autI hVe H) := by
    rw [autI_thompsonJ hVe hTNV]
    exact iSup_le fun A => iSup_le fun hAP => iSup_le fun _ => B6.le_ffJ (hA A hAP)
  obtain ⟨w, hwL₁, hwL₂, hwA⟩ := hM (IntMod V hVe) IntMod.sq_eq_one _ _ _ _ PH hO2 hFF hB53 hL₁J
    hJn hno (offenderImages hVe T) (autI hVe (thompsonJ T)) hQ2 hQG hA hAQ
  have hQfix : ∀ q ∈ autI hVe (thompsonJ T), q w = w := by
    intro q hq
    have hle : autI hVe (thompsonJ T) ≤
        MulAction.stabilizer (MulAut (IntMod V hVe)) w := by
      rw [autI_thompsonJ hVe hTNV]
      refine iSup_le fun A => iSup_le fun hAP => iSup_le fun _ => ?_
      intro a ha
      exact (MulAction.mem_stabilizer_iff).2 ((mem_fixV.mp (hwA A hAP)) a ha)
    exact (MulAction.mem_stabilizer_iff).1 (hle hq)
  refine ⟨w.val, w.val_mem, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hwL₁
    refine mem_fixV.mpr fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := (mem_autI hVe).1 hx
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h1 := hcon (k : G) hk
    rw [h1]
    group
  · intro j hj
    have hjT : j ∈ T := GammaExtra.thompsonJ_le_self T hj
    have h1 := hQfix _ (convI_mem_autI hVe hj (hTNV hjT))
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    calc j * w.val = (j * w.val * j⁻¹) * j := by group
      _ = w.val * j := by rw [h2]
  · intro x hxT hxN l hl
    have hxH : x ∈ H := hTH hxT
    have hLx : x * l * x⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := by
      rcases P.dich x hxH with h | h
      · exact absurd (A38.map_conj_eq_iff.mp h) hxN
      · rw [← h]
        exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have hgH : x * l * x⁻¹ ∈ H := le_of_mem_cComp P.hLt hLx
    have hmem : convI hVe ⟨x * l * x⁻¹, hHN hgH⟩ ∈
        autI hVe (L.map (MulAut.conj t).toMonoidHom) :=
      convI_mem_autI hVe hLx (hHN hgH)
    have h1 := (mem_fixV.mp hwL₂) _ hmem
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    calc (x * l * x⁻¹) * w.val
        = ((x * l * x⁻¹) * w.val * (x * l * x⁻¹)⁻¹) * (x * l * x⁻¹) := by group
      _ = w.val * (x * l * x⁻¹) := by rw [h2]

end CFSG.Quasithin.C116Three
