module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinDense
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LieType.Universal.SpecialLinear
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOddModel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLFrameSwap
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCrossing
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCrossingFour
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKReflect
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoRecFive
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoSingleton
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrGate
import CFSG.LocalAnalysis.StandardType.GGTypeAFarRealize

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

section Placement

variable {G : Type} [Group G]

private theorem ggSecFiveBCoordBLinQTwo_eq_sup_conj {J K : Subgroup G} {r : ℕ} (hr : 1 ≤ r)
    {σ : SL(r + 2, GaloisField 2 2) →* G} (hσ : σ.range = K)
    (hJ : J = (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 2)
      (Finset.univ.erase (0 : Fin (r + 2)))).map σ) :
    K = J ⊔ J.map
      (MulAut.conj (σ (TypeA.permSL (Equiv.swap (0 : Fin (r + 2)) 1)))).toMonoidHom := by
  classical
  let B0 : Subgroup (SL(r + 2, GaloisField 2 2)) :=
    CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 2)
      (Finset.univ.erase (0 : Fin (r + 2)))
  let P : SL(r + 2, GaloisField 2 2) := TypeA.permSL (Equiv.swap (0 : Fin (r + 2)) 1)
  have h01 : (0 : Fin (r + 2)) ≠ 1 := Fin.ne_of_val_ne (by simp)
  have hBtop : B0 ⊔ B0.map (MulAut.conj P).toMonoidHom = ⊤ := by
    simpa only [B0, P] using TypeA.coordBlockSL_erase_sup_conj_eq_top (K := GaloisField 2 2)
      (hd := (by omega : 3 ≤ r + 2)) (i := (0 : Fin (r + 2))) (j := 1) (hij := h01)
  have hcomp : σ.comp (MulAut.conj P).toMonoidHom = (MulAut.conj (σ P)).toMonoidHom.comp σ := by
    ext u
    simp [MulAut.conj_apply, map_mul]
  have hJ' : J = B0.map σ := hJ
  change K = J ⊔ J.map (MulAut.conj (σ P)).toMonoidHom
  calc K = (B0 ⊔ B0.map (MulAut.conj P).toMonoidHom).map σ := by
        rw [hBtop, Subgroup.map_top, hσ]
    _ = J ⊔ J.map (MulAut.conj (σ P)).toMonoidHom := by
        rw [Subgroup.map_sup, Subgroup.map_map, hcomp, ← Subgroup.map_map, ← hJ']

private theorem ggSecFiveBCoordBLinQTwo_sup_conj_eq_sup {L J K : Subgroup G} {g : G}
    (hgK : g ∈ K) (hJL : J ≤ L) (hK : K = J ⊔ J.map (MulAut.conj g).toMonoidHom) :
    L ⊔ L.map (MulAut.conj g).toMonoidHom = L ⊔ K := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rintro _ ⟨l, hl, rfl⟩
    have hg : g ∈ L ⊔ K := Subgroup.mem_sup_right hgK
    simpa [MulAut.conj_apply] using
      (L ⊔ K).mul_mem ((L ⊔ K).mul_mem hg (Subgroup.mem_sup_left hl)) ((L ⊔ K).inv_mem hg)
  · refine sup_le le_sup_left ?_
    rw [hK]
    exact sup_le (hJL.trans le_sup_left) ((Subgroup.map_mono hJL).trans le_sup_right)

private theorem ggSecFiveBCoordBLinQTwo_eigClass {r : ℕ}
    {d : Unit → Fin (r + 2) → (GaloisField 2 2)ˣ} (hd0 : d () 0 ≠ 1)
    (hd : ∀ j : Fin (r + 2), j ≠ 0 → d () j = 1) :
    LinSemisimple.eigClass d 0 = {0} ∧
      ∀ i : Fin (r + 2), i ≠ 0 → LinSemisimple.eigClass d i = Finset.univ.erase 0 := by
  classical
  refine ⟨?_, fun i hi => ?_⟩
  · ext j
    simp only [LinSemisimple.mem_eigClass, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hj
      exact hd0 ((h ()).symm.trans (hd j hj))
    · rintro rfl
      exact fun _ => rfl
  · ext j
    simp only [LinSemisimple.mem_eigClass, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h hj
      subst j
      exact hd0 ((h ()).trans (hd i hi))
    · intro hj u
      cases u
      rw [hd j hj, hd i hi]

variable [Finite G]

private theorem ggSecFiveBCoordBLinQTwo_eta_x {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {n : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {i0 : Fin n}
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {y : G} {K : Subgroup G} (hny : GGNbr 3 B x D J y K) (hxBs : x ∈ Bs) :
    eta ⟨x, hxBs⟩ i0 ≠ 1 ∧ ∀ j : Fin n, j ≠ i0 → eta ⟨x, hxBs⟩ j = 1 := by
  obtain ⟨-, -, -, hxL, -⟩ := hcfg.tableB_facts
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hxL hl)
  have hxcoords : ∀ j : Fin n, j ≠ i0 → eta ⟨x, hxBs⟩ j = 1 := fun j hj =>
    ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer (by norm_num : 3 ≠ 2) hAL hxC hj
  refine ⟨fun hzero => ?_, hxcoords⟩
  have heq : eta ⟨x, hxBs⟩ = 1 := by
    ext j
    by_cases hj : j = i0
    · simpa [hj] using hzero
    · exact hxcoords j hj
  have h : (⟨x, hxBs⟩ : Bs) = 1 := eta.injective (heq.trans eta.map_one.symm)
  exact (ggNbr_facts hcfg hny).2.2.2.2 (congrArg (fun b : Bs => (b : G)) h)

private theorem ggSecFiveBCoordBLinQTwo_J_eq_block {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {y : G} {K : Subgroup G} (hny : GGNbr 3 B x D J y K) (hJK : J ≤ K) {r : ℕ}
    (π : Fin (r + 2) ≃ Fin n) (hπ0 : π 0 = i0) {σ : SL(r + 2, GaloisField 2 2) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ}
    (hKF : GGSecFiveBPermSpLFrame Bs K eta π σ χ) :
    J = (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 2)
      (Finset.univ.erase (0 : Fin (r + 2)))).map σ := by
  classical
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  obtain ⟨hx0, hxcoords⟩ := ggSecFiveBCoordBLinQTwo_eta_x hcfg hAL hny hxBs
  let d : Unit → Fin (r + 2) → (GaloisField 2 2)ˣ := fun _ k => χ (eta ⟨x, hxBs⟩ (π k))
  have hd0 : d () 0 ≠ 1 := by
    intro h
    apply hx0
    apply hKF.2.2.1
    simpa [d, hπ0] using h
  have hd : ∀ j : Fin (r + 2), j ≠ 0 → d () j = 1 := by
    intro j hj
    have hj' : π j ≠ i0 := fun h => hj (π.injective (h.trans hπ0.symm))
    simp [d, hxcoords (π j) hj']
  obtain ⟨hI0, hIi⟩ := ggSecFiveBCoordBLinQTwo_eigClass hd0 hd
  have hJc : IsComponentOf J
      (σ.range ⊓ Subgroup.centralizer (Set.range (fun _ : Unit => x))) := by
    rw [Set.range_const, hKF.2.1]
    exact ggIsComponentOf_inf_centralizer_nbr hcfg hny hJK
  obtain ⟨i, hJi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf
    (m := r + 1) (ψ := σ) hKF.1 (d := d) (b := fun _ : Unit => x)
    (fun _ => LinFusion.mem_ggInducedPairs.mpr (hKF.2.2.2 ⟨x, hxBs⟩)) hJc
  have hi : i ≠ 0 := by
    intro hi
    rw [hi, hI0, CFSG.SeitzReduction.SymplecticPilot.blockSpecialLinear_singleton_eq_bot,
      Subgroup.map_bot] at hJi
    apply LinSemisimple.false_of_isQuasisimple_of_commute hJc.2.2
    intro a ha b hb
    simp only [hJi, Subgroup.mem_bot] at ha hb
    simp [ha, hb]
  rw [hIi i hi, ← blockSpecialLinear_eq_coordBlockSL] at hJi
  exact hJi

end Placement

section Rec


private theorem ggSecFiveBCoordBLinQTwo_crossing_four {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hBB : B = Bs) {r : ℕ} (hr : r = 2)
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod 3))} {m : ℕ}
    (hm : m = 2 * r + 2 ∨ m = 2 * r + 3) {y : G} {K : Subgroup G} (hny : GGNbr 3 B x D J y K)
    {ψ : SL(r + 2, GaloisField 2 2) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 2)) (hrange : ψ.range = K)
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull (r + 2) 3)
    (π : Fin (r + 2) ≃ Fin (r + 2)) {g : Polynomial (ZMod 2)} [Fact (Irreducible g)] {d : ℕ}
    {ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin (r + 1)) ⊕ Fin d}
    {hC : (CoordSL.rootMat g).det = 1} {hCp : CoordSL.rootMat g ^ 3 = 1} {κ : SL(m, ZMod 2) →* G}
    (hF : GGSecFiveBPermQTwoKFrame Bs L eta π ε hC hCp κ) (hdim : (CoordSL.rootPB g).dim = 2) :
    GGSecFiveBPermQTwoCrossing Bs eta π d := by
  classical
  subst hr
  have hcfg := hRt.1.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_iff_open.mp hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hyBs : y ∈ Bs := (ggNbr_facts hcfg hny).1
  have hKq : CFSG.IsQuasisimple ↥K := by
    rw [← hrange]
    refine CFSG.LocalCores.isQuasisimple_of_surjective
      (SpecialLinear.isQuasisimple 3 (GaloisField 2 2) (by omega)) ψ.rangeRestrict
      ψ.rangeRestrict_surjective ?_
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hKp : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) K := hny.1.2.2.2.2.1
  have := hKq.1
  have hKc : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    ⟨hKp.1, hKp.2.1, Group.IsPerfect.commutator_eq_top, hKq.2.1⟩
  obtain ⟨σ, χ, hKF⟩ := exists_ggSecFiveBPermSpLFrame ggInnerDiagMpInput_holds hp
    (by norm_num) hBs hBsC (hRt.1.2.2.1.2 y K hny) (hRt.card_inf_centralizer_nbr_le hBB hny)
    (by omega) eta hAK (f := 2) (by omega) hker hrange 2 π
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((CFSG.RankThree.CALinearPlane.coordBlockSL (AdjoinRoot g) {a, b}).map
          (CoordSL.theta g ε)).map κ := fun a b hab =>
    (hF.reflComm (by omega) hBsC hxBs hLc a b hab).trans (Subgroup.map_map _ _ _).symm
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨S, hSK, hSeq⟩ := hF.exists_singleton_family hKF hAK hBsC hxBs hLc le_rfl (by omega)
    exact hF.crossing_even_four_of_LFrame hBsC hxBs hLc hdim hd S hSK hSeq hRK hBc hyBs hKc hKF
      hAK
  · obtain ⟨S, hSK, hSeq⟩ := hF.exists_singleton_family hKF hAK hBsC hxBs hLc le_rfl (by omega)
    exact hF.crossing_odd_four_of_LFrame hBsC hxBs hLc hdim hd S hSK hSeq hRK hKF hAK

theorem ggSecFiveBCoordBLinQTwo_recognition (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hBB : B = Bs) {n : ℕ} (hn : 4 ≤ n) {m : ℕ} {K : Subgroup G} {i0 : Fin n}
    (hc : GGSecFiveBCoordBLinQTwoCell 3 Bs L 𝒦 n m K i0) :
    ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ K := by
  classical
  obtain ⟨-, hm, hK𝒦, ⟨ψ, hker, hrange⟩, ⟨eL⟩, eta, -, hAL, hAK⟩ := hc
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hcfg := hRt.1.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hm' : m = 2 * r + 2 ∨ m = 2 * r + 3 := by rcases hm with h | h <;> omega
  obtain ⟨y, hny⟩ := hRt.2.2.2.1.2 K hK𝒦
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 (hP G 3 B x L D J hcfg.1 hcfg.2.2) hny
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_iff_open.mp hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hlift : ∀ a b : Fin (r + 2), a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b) := by
    intro a b hab
    obtain ⟨w, -, hw, hwη⟩ := exists_mem_conjAut_eq_permAut_swap hAK hab
    exact ⟨w, hw, hwη⟩
  obtain ⟨π, hπ0, g₀, ⟨σ, χ, hKF, rfl⟩, Ψ, hΨ, hΨr⟩ := ggSecFiveBPermQTwo_recognition_of_pair hBsC
    (by omega) hm' hxBs hLc hRt.1.2.2.1.1.le_normalizer eL hAL
    (fun π g₀ => ∃ (σ : SL(r + 2, GaloisField 2 2) →* G)
      (χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ),
        GGSecFiveBPermSpLFrame Bs K eta π σ χ ∧
          g₀ = σ (TypeA.permSL (Equiv.swap (0 : Fin (r + 2)) 1)))
    (fun π _ => by
      obtain ⟨σ, χ, hKF⟩ := exists_ggSecFiveBPermSpLFrame ggInnerDiagMpInput_holds hp
        (by norm_num) hBs hBsC (hRt.1.2.2.1.2 y K hny) (hRt.card_inf_centralizer_nbr_le hBB hny)
        (by omega) eta hAK (f := 2) (by omega) hker hrange r π
      obtain ⟨hg₀, hg₀η⟩ := hKF.permSL_swap_normalizer hBsC hAK (by omega)
        (Fin.ne_of_val_ne (by simp) : (0 : Fin (r + 2)) ≠ 1)
      exact ⟨_, hg₀, hg₀η, σ, χ, hKF, rfl⟩)
    (fun π g _ d ε hC hCp κ hF hdim _ => by
      rcases (show r = 2 ∨ 3 ≤ r by omega) with hr | hr
      · exact ggSecFiveBCoordBLinQTwo_crossing_four hRt hBB hr hm' hny hker hrange hAK π hF hdim
      · exact ⟨fun hd => hF.crossing_even hBsC hxBs hLc hdim hr hlift hd,
          fun hd => hF.crossing_odd hBsC hxBs hLc hdim hr hlift hd⟩)
  have hg₀K : σ (TypeA.permSL (Equiv.swap (0 : Fin (r + 2)) 1)) ∈ K := by
    rw [← hKF.2.1]
    exact ⟨_, rfl⟩
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  refine ⟨Ψ, hΨ, hΨr.trans (ggSecFiveBCoordBLinQTwo_sup_conj_eq_sup hg₀K hJL ?_)⟩
  exact ggSecFiveBCoordBLinQTwo_eq_sup_conj (by omega) hKF.2.1
    (ggSecFiveBCoordBLinQTwo_J_eq_block hcfg hAL hny hJK π hπ0 hKF)

theorem ggSecFiveBCoordBLinQTwoRecInput_of_lBalance (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) : GGSecFiveBCoordBLinQTwoRecInput := by
  intro G _ _ p B Bs x L D J 𝒦 hRt _ n _ _ hn _ _ _ _ _ hB _ _ m K hc
  obtain rfl := hc.1
  exact ggSecFiveBCoordBLinQTwo_recognition hLB hP hRt hB hn hc

end Rec

end CFSG.StandardType

end
