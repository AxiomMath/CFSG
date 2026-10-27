module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpPlaneBlocksTwoDefs

import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311h2
import CFSG.LocalAnalysis.StandardType.GGOrthFrameModelAux
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Odd
import CFSG.LocalAnalysis.StandardType.GGQTwoSpSmallBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerRowOne
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveSpPlaneBlocksTwo
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.CGT.Timmesfeld75.Form2
import CFSG.CGT.Timmesfeld75.Main
import CFSG.LargeExtraspecial.S97RZStar
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
import CFSG.Quasithin.Background.G1Basic

public section

namespace CFSG.StandardType

open CFSG.Open

private theorem sgnAut_eq_self_of_coord_eq_one {n p : ℕ} {i : Fin n}
    {f : Fin n → Multiplicative (ZMod p)} (h : f i = 1) :
    SpCoord.sgnAut i f = f := by
  funext j
  rw [SpCoord.sgnAut_apply]
  by_cases hj : j = i
  · subst hj
    simp [h]
  · rw [Function.update_of_ne hj]

private theorem closure_fix_of_fix {n p : ℕ}
    {Gens : Set (MulAut (Fin n → Multiplicative (ZMod p)))}
    {f : Fin n → Multiplicative (ZMod p)} (hGens : ∀ u ∈ Gens, u f = f) :
    ∀ u ∈ Subgroup.closure Gens, u f = f := by
  intro u hu
  refine Subgroup.closure_induction (p := fun u _ => u f = f) ?_ rfl ?_ ?_ hu
  · exact hGens
  · intro x y _ _ ihx ihy
    rw [MulAut.mul_apply, ihy, ihx]
  · intro x _ ihx
    calc x⁻¹ f = (x⁻¹ * x) f := by rw [MulAut.mul_apply, ihx]
      _ = f := by rw [inv_mul_cancel, MulAut.one_apply]

theorem IsSignedBlockOn.apply_eq_of_forall_eq_one {n p : ℕ} {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (hΓ : IsSignedBlockOn n p I Γ)
    {f : Fin n → Multiplicative (ZMod p)} (hf : ∀ i ∈ I, f i = 1) : ∀ u ∈ Γ, u f = f := by
  have hperm : ∀ a ∈ I, ∀ b ∈ I, SpCoord.permAut (Equiv.swap a b) f = f :=
    fun a ha b hb => OrthTorus.ggOFM_permAut_swap_eq_self_of_eq (by rw [hf a ha, hf b hb])
  intro u hu
  rcases hΓ with hB | ⟨hcard, hD⟩ | ⟨d, hd, hS⟩
  · rw [hB, bBlockOn] at hu
    exact closure_fix_of_fix (by
      rintro u (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, _hab, rfl⟩)
      · exact sgnAut_eq_self_of_coord_eq_one (hf i hi)
      · exact hperm a ha b hb) u hu
  · rw [hD, dBlockOn] at hu
    exact closure_fix_of_fix (by
      rintro u (⟨a, ha, b, hb, _hab, rfl⟩ | ⟨a, ha, b, hb, _hab, rfl⟩)
      · exact hperm a ha b hb
      · have hs : SpCoord.sgnAut a f = f := sgnAut_eq_self_of_coord_eq_one (hf a ha)
        have hsi : (SpCoord.sgnAut a)⁻¹ f = f := by
          calc (SpCoord.sgnAut a)⁻¹ f = (SpCoord.sgnAut a)⁻¹ (SpCoord.sgnAut a f) := by
                rw [hs]
            _ = f := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        rw [MulAut.mul_apply, MulAut.mul_apply, hsi, hperm a ha b hb, hs]) u hu
  · rw [hS] at hu
    refine (forall_map_conj_fix_iff (aPermutationOn n p I)
      (SpCoord.diagAut d hd) f).mpr ?_ u hu
    refine (forall_aPermutationOn_fix_iff I ((SpCoord.diagAut d hd)⁻¹ f)).mpr ?_
    have htriv : ∀ k ∈ I, (SpCoord.diagAut d hd)⁻¹ f k = 1 := by
      intro k hk
      have hdapply : (SpCoord.diagAut d hd)⁻¹ f k = SpCoord.diagAut d hd f k := rfl
      rw [hdapply, SpCoord.diagAut_apply, hf k hk, toAdd_one, mul_zero, ofAdd_zero]
    intro i hi j hj
    rw [htriv i hi, htriv j hj]

theorem IsSignedBlockOn.exists_eq_map_conj_of_univ {n : ℕ}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    (hΓ : IsSignedBlockOn n 3 Finset.univ Γ) {w : Fin n → Multiplicative (ZMod 3)} (hw : w ≠ 1)
    (hfix : ∀ u ∈ Γ, u w = w) :
    ∃ δ ∈ bSignedFull n 3, Γ = (aPermutationFull n 3).map (MulAut.conj δ).toMonoidHom := by
  rcases hΓ with hB | ⟨hcard, hD⟩ | ⟨d, hd, hS⟩
  · have hfix' : ∀ u ∈ bBlockOn n 3 Finset.univ, u w = w := by
      intro u hu
      exact hfix u (by rw [hB]; exact hu)
    have h1 : w = 1 := funext fun i =>
      (forall_bBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) Finset.univ w).mp hfix'
        i (Finset.mem_univ i)
    exact absurd h1 hw
  · have hfix' : ∀ u ∈ dBlockOn n 3 Finset.univ, u w = w := by
      intro u hu
      exact hfix u (by rw [hD]; exact hu)
    have h1 : w = 1 := funext fun i =>
      (forall_dBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) hcard w).mp hfix'
        i (Finset.mem_univ i)
    exact absurd h1 hw
  · exact ⟨SpCoord.diagAut d hd, diagAut_mem_bSignedFull hd, by rw [hS, aPermutationOn_univ]⟩

theorem le_ggBlockTwo_of_isComponentOf {G : Type} [Group G] [Finite G] {p n : ℕ}
    {Bs C K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {S : Set (Fin n)}
    (hK : CFSG.Assembly.IsComponentOf K C)
    (hKS : K ≤ Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G)) :
    K ≤ ggBlockTwo Bs eta S := by
  let two : Set ↥K := {x | ∃ n : ℕ, x ^ (2 ^ n) = 1}
  let gen : Set G := {g | g ∈ K ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1}
  have hq : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp
      hK.2.2
  have hgen : Subgroup.closure two = ⊤ := by
    simpa only [two] using
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_two_pow_eq_top_of_quasisimple
        hq
  have hsub : K.subtype '' two ⊆ gen := by
    rintro g ⟨x, ⟨n, hn⟩, rfl⟩
    exact ⟨x.2, n, by simpa using congrArg Subtype.val hn⟩
  have hmap : Subgroup.closure gen = K := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro g ⟨hg, -⟩
      exact hg
    · calc K = (Subgroup.closure two).map K.subtype := by
            rw [hgen, Subgroup.map_top, Subgroup.range_subtype]
        _ = Subgroup.closure (K.subtype '' two) := MonoidHom.map_closure _ _
        _ ≤ Subgroup.closure gen := Subgroup.closure_mono hsub
  rw [← hmap, Subgroup.closure_le]
  rintro g ⟨hgK, n, hn⟩
  exact Subgroup.subset_closure
    ⟨Subgroup.mem_centralizer_iff.mpr
        (fun h hh => Subgroup.mem_centralizer_iff.mp (hKS hgK) h hh), ⟨n, hn⟩⟩

theorem GGSecFiveBPermSpPlaneFrame.ggBlockTwo_compl_le_sup {G : Type} [Group G] [Finite G]
    {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) (hr : 2 ≤ r) {Bs L : Subgroup G} {x : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G))))
    (hxB : x ∈ Bs) (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p (π 0))
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (a : Fin n) :
    ggBlockTwo Bs eta {a}ᶜ ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  have hL' : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hL
  have h0 : ggBlockTwo Bs eta {π 0}ᶜ = L :=
    ggBlockTwo_compl_eq_of_planeFrame hp2 hF hr hBs hodd hxB hL' hκ
  have h1 : ggBlockTwo Bs eta {π 1}ᶜ = L.map (MulAut.conj g).toMonoidHom := by
    have himg : Equiv.swap (π 0) (π 1) '' ({π 0}ᶜ : Set (Fin n)) = {π 1}ᶜ := by
      rw [Equiv.image_compl, Set.image_singleton, Equiv.swap_apply_left]
    have hconj := ggBlockTwo_map_conj (p := p) (n := n) hg hgη {π 0}ᶜ
    rw [himg] at hconj
    rw [← hconj, h0]
  have h10 : π 1 ≠ π 0 := fun h => Fin.zero_ne_one' (n := r + 1) (π.injective h).symm
  by_cases ha0 : a = π 0
  · subst ha0
    rw [h0]
    exact le_sup_left
  by_cases ha1 : a = π 1
  · subst ha1
    rw [h1]
    exact le_sup_right
  have hmem : SpCoord.permAut (Equiv.swap (π 1) a) ∈
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure
      (Or.inr ⟨π 1, a, fun h => ha1 h.symm, h10, ha0, rfl⟩)
  obtain ⟨h, hgh, hhL, hhη⟩ := exists_mem_of_mem_map_congr eta hmem
  have himg : Equiv.swap (π 1) a '' ({π 1}ᶜ : Set (Fin n)) = {a}ᶜ := by
    rw [Equiv.image_compl, Set.image_singleton, Equiv.swap_apply_left]
  have hconj := ggBlockTwo_map_conj (p := p) (n := n) hgh hhη {π 1}ᶜ
  rw [himg] at hconj
  calc ggBlockTwo Bs eta {a}ᶜ
      = (ggBlockTwo Bs eta {π 1}ᶜ).map (MulAut.conj h).toMonoidHom := hconj.symm
    _ = (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom := by rw [h1]
    _ ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom := map_conj_le_sup (W := L) hhL

theorem GGSecFiveBPermSpPlaneFrame.ggBlockComm_le_of_card_eq_three {G : Type} [Group G]
    [Finite G] {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hr : 3 ≤ r) {Bs L : Subgroup G} {x : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxB : x ∈ Bs) (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ) {S : Finset (Fin n)} (hS : S.card = 3)
    (h0 : π 0 ∉ S) :
    ggBlockComm Bs eta (S : Set (Fin n)) ≤ L := by
  classical
  let N : Finset (Fin (r + 1)) := Finset.univ.filter fun m => π m.succ ∈ S
  have himg : (fun m : Fin (r + 1) => π m.succ) '' (N : Set (Fin (r + 1))) =
      (S : Set (Fin n)) := by
    ext s
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa [N] using hm
    · intro hs
      rw [Finset.mem_coe] at hs
      have hne : π.symm s ≠ 0 := by
        intro h
        apply h0
        rw [← h, Equiv.apply_symm_apply]
        exact hs
      obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr hne
      refine ⟨m, ?_, ?_⟩
      · simp [N, hm, hs]
      · simp [hm]
  have hinj : Function.Injective fun m : Fin (r + 1) => π m.succ :=
    fun a b h => Fin.succ_injective _ (π.injective h)
  have hNcard : N.card = 3 := by
    rw [← hS, ← Finset.card_image_of_injective N hinj]
    exact congrArg Finset.card (Finset.coe_injective (by rw [Finset.coe_image, himg]))
  have hNu : N ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    rw [hNcard, Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [← himg, hκ.ggBlockComm_image_succ_eq_map_spBlock_of_or hp2 hBs hxB
    (CFSG.Assembly.isComponentOf_iff_open.mp hL) (Or.inr hNcard.ge)
    (Finset.card_pos.mp (by omega)) hNu, ← hκ.2.1]
  exact Subgroup.map_le_range κ _

private theorem denseNbr_of_isSignedBlockOn_univ {G : Type} [Group G] {Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {K : Subgroup G}
    {I : Finset (Fin n)} {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    (hI : I = Finset.univ) (hΓ : IsSignedBlockOn n 3 I Γ)
    {w : Fin n → Multiplicative (ZMod 3)} (hw : w ≠ 1) (hfix : ∀ u ∈ Γ, u w = w)
    (hΓeq : Γ = (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) (hK𝒦 : K ∈ 𝒦) :
    GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K := by
  have hΓ' : IsSignedBlockOn n 3 Finset.univ Γ := hI ▸ hΓ
  obtain ⟨δ, hδ, hδeq⟩ := IsSignedBlockOn.exists_eq_map_conj_of_univ hΓ' hw hfix
  exact ⟨hK𝒦, δ, hδ, by rw [← hΓeq, hδeq]⟩

section CornerAbsorb

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
variable {n r : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
variable {π : Fin (r + 2) ≃ Fin n} {κ : StatedSp (r + 1) (GaloisField 2 1) →* G}
variable {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
variable {g : G} {K : Subgroup G}

private theorem le_centralizer_of_missing_coord (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G}
    (hn : GGNbr 3 B x D J y K) {I : Finset (Fin n)} {b : Fin n} (hb : b ∉ I)
    (hIsb : IsSignedBlockOn n 3 I ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom)) :
    K ≤ Subgroup.centralizer (ggBsCoordZeroOn Bs eta ({b}ᶜ : Set (Fin n)) : Set G) := by
  have hres : GGResHyp 3 B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K hn, Or.inr hR.2.1⟩
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨hhBs, hhoff⟩ := mem_ggBsCoordZeroOn.mp hh
  have hfixh : ∀ φ ∈ ggAutomizer K Bs, φ ⟨h, hhBs⟩ = ⟨h, hhBs⟩ := by
    refine (forall_map_congr_fix_iff eta (ggAutomizer K Bs) ⟨h, hhBs⟩).mp ?_
    refine IsSignedBlockOn.apply_eq_of_forall_eq_one hIsb ?_
    intro i hi
    exact hhoff i (by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hib
      exact hb (hib ▸ hi))
  exact (Subgroup.mem_centralizer_iff.mp
    (hFC G 3 B Bs x L D J y K hres ⟨h, hhBs⟩ hfixh) k hk).symm

private theorem le_sup_of_missing_coord (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hne : B ≠ Bs) (hr : 2 ≤ r)
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 (π 0))
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    {y : G} (hn : GGNbr 3 B x D J y K) {I : Finset (Fin n)} {b : Fin n} (hb : b ∉ I)
    (hIsb : IsSignedBlockOn n 3 I ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom))
    (hKy : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G))) :
    K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  have hKS := le_centralizer_of_missing_coord hFC hR hn hb hIsb
  have hle := GGSecFiveBPermSpPlaneFrame.ggBlockTwo_compl_le_sup (p := 3)
    (F := GaloisField 2 1) (by norm_num) (by simpa using GaloisField.card 2 1 one_ne_zero)
    hr hR.1.1.2.1.2.2.2 (QTwo.qtwoDL1_odd_centralizer_of_ne hR hne)
    (hR.1.1.2.1.1 hR.1.1.1.2.2.2.2.2.2.1.2.1)
    hR.1.1.1.2.2.2.2.2.2.1.2.2.2.1 hκ hA hg hgη b
  exact (le_ggBlockTwo_of_isComponentOf hKy hKS).trans hle

theorem GGSecFiveRouteCfg.le_sup_or_denseNbr (hX : GGResXDichotomyInput)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hne : B ≠ Bs) (hr : 2 ≤ r)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 (π 0))
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hK𝒦 : K ∈ 𝒦) :
    K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom ∨ GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K := by
  obtain ⟨y, hn⟩ := hR.2.2.2.1.2 K hK𝒦
  have hst : LargeEvenStandardType 3 B x L := hR.1.1.1.2.2.2.2.2.2.2
  have hKy : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hR.1.1.2.2 hn)).1
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hn.1.2.1
  let yb : ↥Bs := ⟨y, hyBs⟩
  have hxBs : x ∈ Bs := hR.1.1.2.1.1 hR.1.1.1.2.2.2.2.2.2.1.2.1
  let xb : ↥Bs := ⟨x, hxBs⟩
  have hdatum := GGSecFiveRouteCfg.signedNbrDatum hX hTCJ hRig hTPn hA8 hraw hiso hFC hR
    eta hEta hn (hNbr y K hn) (xb := xb) (yb := yb) rfl rfl
  obtain ⟨I, hIsb⟩ := hdatum.isSignedBlockOn
  by_cases hmiss : ∃ b : Fin n, b ∉ I
  · obtain ⟨b, hb⟩ := hmiss
    exact Or.inl (le_sup_of_missing_coord hFC hR hne hr hκ hA hg hgη hn hb hIsb hKy)
  · refine Or.inr (denseNbr_of_isSignedBlockOn_univ (I := I)
      (Γ := (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) ?_ hIsb ?_ hdatum.fix rfl hK𝒦)
    · exact Finset.eq_univ_of_forall fun i => by
        by_contra hi
        exact hmiss ⟨i, hi⟩
    · intro h
      apply hn.1.2.2.1
      exact congrArg Subtype.val (eta.injective (by simpa using h))

theorem GGSecFiveRouteCfg.ggBlockComm_le_of_corner (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ) (hr : 3 ≤ r) (S : Finset (Fin n))
    (hS : S.card = 3) (h0 : π 0 ∉ S) : ggBlockComm Bs eta (S : Set (Fin n)) ≤ L :=
  hκ.ggBlockComm_le_of_card_eq_three (by norm_num) hr hR.1.1.2.1.2.2.2
    (hR.1.1.2.1.1 hR.1.1.1.2.2.2.2.2.2.1.2.1) hR.1.1.1.2.2.2.2.2.2.1.2.2.2.1 hS h0

end CornerAbsorb

theorem ggSecFiveBCoordBCornerAbsorbInput_holds : GGSecFiveBCoordBCornerAbsorbInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC G _ _ B Bs x L D J 𝒦 hR hne n r hr eta hEta hNbr
    π κ ζ hκ hA g hg hgη K hK
  exact GGSecFiveRouteCfg.le_sup_or_denseNbr hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hne
    hr hEta hNbr hκ hA hg hgη hK

end CFSG.StandardType

end
