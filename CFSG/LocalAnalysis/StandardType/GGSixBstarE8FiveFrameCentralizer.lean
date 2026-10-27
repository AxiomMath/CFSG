module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameDiag
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveWeylFaithful
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveIsotropic
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality

namespace NoOffE8Five

local instance noOffE8FiveFactFiveFC : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankFC : NeZero Tag.E8.rank := ⟨by decide⟩

section FrameCharLemmas

variable {τ : Tag} {p : ℕ} [NeZero p] {K : Type} [Field K]

theorem rootChar_zetaVec {ζ : Kˣ} (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p)
    (γ : Fin τ.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ x) γ =
      CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (.ofAdd (∑ j, (γ j : ZMod p) * x j)) := by
  rw [rootChar]
  have hprod : (∏ i, TableBExc.E6Three.zetaVec ζ hζ x i ^ γ i) =
      ∏ i, CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (.ofAdd ((γ i : ZMod p) * x i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [TableBExc.E6Three.zetaVec, TableBExc.E6Three.zmodPowHom_zpow]
  rw [hprod, ← map_prod, ← ofAdd_sum]

end FrameCharLemmas

section FrameBformLemma

theorem bform_redMod_frameCoord (γ : Fin Tag.E8.rank → ℤ)
    (s : Fin Tag.E8.rank → ZMod 5) :
    NoOffRest.bform .E8 5 (TableBExc.redMod .E8 5 γ) s =
      ∑ j, (γ j : ZMod 5) * ExcFrames.frameCoord Tag.E8 5 s j := by
  rw [NoOffRest.bform_apply]
  simp only [ExcFrames.frameCoord, TableBExc.redMod, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rootChar_zetaVec_frameCoord {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 5 = 1)
    (s : Fin Tag.E8.rank → ZMod 5) (γ : Fin Tag.E8.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E8 5 s)) γ =
      CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (.ofAdd (NoOffRest.bform .E8 5 (TableBExc.redMod .E8 5 γ) s)) := by
  rw [rootChar_zetaVec, ← bform_redMod_frameCoord γ s]

end FrameBformLemma

section FrameCentralizer

variable {L : Type} [Field L]

theorem mem_torusGroup_of_commute_frameDiag {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1)
    {lam : ZMod 5} (hlam : lam * lam = -1) {z : ModGL Tag.E8 L}
    (hz : z ∈ adjointGroup Tag.E8 L)
    (hcomm : ∀ s ∈ NoOffRest.eigE8 5 lam,
      Commute z (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s)) :
    z ∈ torusGroup Tag.E8 L := by
  let a : NoOffRest.eigE8 5 lam → Fin Tag.E8.rank → Lˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord Tag.E8 5 (s : Fin Tag.E8.rank → ZMod 5))
  have hfam : z ∈ familyCentralizer Tag.E8 L a := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun s => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm s s.2).eq.symm
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul Tag.E8 L a hfam
  have hker : familyKernel a = (∅ : Set (Fin Tag.E8.rank → ℤ)) := by
    refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
    obtain ⟨hγr, hγtriv⟩ := hγ
    obtain ⟨y, hy, hbne⟩ := exists_mem_eigE8_bform_redMod_ne_zero hlam hγr
    have h1 : rootChar (a ⟨y, hy⟩) γ = 1 := hγtriv ⟨y, hy⟩
    dsimp only [a] at h1
    rw [rootChar_zetaVec_frameCoord (ζ := ζ) hζ y γ] at h1
    have h2 : NoOffRest.bform .E8 5 (TableBExc.redMod .E8 5 γ) y = 0 := by
      have h3 : Multiplicative.ofAdd
          (NoOffRest.bform .E8 5 (TableBExc.redMod .E8 5 γ) y) = 1 :=
        CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ
          (h1.trans (map_one (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ)).symm)
      exact Multiplicative.ofAdd.injective (by simpa using h3)
    exact hbne ((NoOffRest.bform_comm y (TableBExc.redMod .E8 5 γ)).trans h2)
  have hw1 : w = 1 := by
    have hfix : ∀ x ∈ NoOffRest.eigE8 5 lam, TableBExc.torusAct .E8 5 w⁻¹ x = x := by
      intro s hs
      have hb : ∀ y : Fin Tag.E8.rank → ZMod 5,
          NoOffRest.bform .E8 5 (TableBExc.torusAct .E8 5 w y) s =
            NoOffRest.bform .E8 5 y s := by
        intro y
        have h := hw ⟨s, hs⟩ (TableBExc.liftMod .E8 5 y)
        dsimp only [a] at h
        rw [rootChar_zetaVec_frameCoord (ζ := ζ) hζ s
              (w • TableBExc.liftMod .E8 5 y),
            rootChar_zetaVec_frameCoord (ζ := ζ) hζ s
              (TableBExc.liftMod .E8 5 y)] at h
        have h2 := Multiplicative.ofAdd.injective
          (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ h)
        simpa [TableBExc.torusAct, TableBExc.redMod_liftMod] using h2
      have hb' : ∀ y : Fin Tag.E8.rank → ZMod 5,
          NoOffRest.bform .E8 5 y (TableBExc.torusAct .E8 5 w⁻¹ s) =
            NoOffRest.bform .E8 5 y s := by
        intro y
        have hform := NoOffRest.bform_torusAct w y (TableBExc.torusAct .E8 5 w⁻¹ s)
        rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one] at hform
        exact hform.symm.trans (hb y)
      have hzero : TableBExc.torusAct .E8 5 w⁻¹ s - s = 0 :=
        (NoOffRest.bform_nondegenerate_E8 (p := 5)).2 _ fun y => by
          rw [map_sub]
          exact sub_eq_zero.mpr (hb' y)
      exact sub_eq_zero.mp hzero
    have hw1' : w⁻¹ = 1 := weylE8_eq_one_of_forall_fix_eigE8 hlam hfix
    rwa [inv_eq_one] at hw1'
  have hmT : m ∈ torusGroup Tag.E8 L := by
    have hm' : m ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (familyKernel a) := hm
    rw [hker] at hm'
    have hbot : rootSpan Tag.E8 L (∅ : Set (Fin Tag.E8.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hw1, canonicalRep_one, mul_one]
  exact hmT

theorem exists_centE8W_conj_frameDiag {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1)
    {lam : ZMod 5} (hlam : lam * lam = -1) {g : ModGL Tag.E8 L}
    (hg : g ∈ adjointGroup Tag.E8 L)
    (h : ∀ s ∈ NoOffRest.eigE8 5 lam, ∃ t ∈ NoOffRest.eigE8 5 lam,
      g * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ t) :
    ∃ u : NoOffRest.centE8W, ∀ s : NoOffRest.eigE8 5 lam,
      g * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) * g⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((NoOffRest.eigPerm 5 lam u s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) := by
  classical
  have hdet : IsUnit ((Tag.E8.symmetrizedCartan.det : ℤ) : ZMod 5) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) (by norm_num)
  let V : Set (ModGL Tag.E8 L) :=
    {d | ∃ s ∈ NoOffRest.eigE8 5 lam, d = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s}
  have hVD : ∀ x ∈ V, ∃ a : Fin Tag.E8.rank → Lˣ, x = rootDiagUnit Tag.E8 a := by
    rintro _ ⟨s, -, rfl⟩
    exact ⟨_, rfl⟩
  have hgV : ∀ x ∈ V, g * x * g⁻¹ ∈ V := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, he⟩ := h s hs
    exact ⟨t, ht, he⟩
  obtain ⟨w, hw⟩ := NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag hVD hg hgV
  have hmain : ∀ s ∈ NoOffRest.eigE8 5 lam,
      g * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (TableBExc.torusAct .E8 5 w s) := by
    intro s hs
    rw [hw _ ⟨s, hs, rfl⟩, ExcFrames.canonicalRep_conj_frameDiag]
  have hws : ∀ s ∈ NoOffRest.eigE8 5 lam,
      TableBExc.torusAct .E8 5 w s ∈ NoOffRest.eigE8 5 lam := by
    intro s hs
    obtain ⟨t, ht, he⟩ := h s hs
    have := ExcFrames.frameDiag_injective hζo hζ hdet (he.symm.trans (hmain s hs))
    rw [← this]
    exact ht
  have hwc : w ∈ NoOffRest.centE8W := mem_centE8W_of_torusAct_mem_eigE8 hlam hws
  exact ⟨⟨w, hwc⟩, fun s => hmain s s.2⟩

end FrameCentralizer

end NoOffE8Five

end CFSG.StandardType
