module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwo
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCrossing
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCentralizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoPlacement
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLFrameSwap
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.FF81.TwoChartLinear
import CFSG.LieType.Universal.SpecialLinear
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal Polynomial Matrix
  CoordSL CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.CALinearPlane
open scoped MatrixGroups

attribute [-instance] CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

private theorem image_succ_pair {n r : ℕ} (π : Fin (r + 2) ≃ Fin n) (a b : Fin (r + 1)) :
    (fun k : Fin (r + 1) => π k.succ) '' (((({a, b} : Finset (Fin (r + 1)))) : Set (Fin (r + 1)))) =
      {π a.succ, π b.succ} := by
  rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]

private theorem image_succ_single {n r : ℕ} (π : Fin (r + 2) ≃ Fin n) (a : Fin (r + 1)) :
    (fun k : Fin (r + 1) => π k.succ) '' ((({a} : Finset (Fin (r + 1)))) : Set (Fin (r + 1))) =
      {π a.succ} := by
  rw [Finset.coe_singleton, Set.image_singleton]

private theorem coordBlockSL_mono' {N : ℕ} {J₁ J₂ : Finset (Fin N)} (h : J₁ ⊆ J₂) :
    coordBlockSL (ZMod 2) J₁ ≤ coordBlockSL (ZMod 2) J₂ := by
  intro u hu
  rw [mem_coordBlockSL_iff] at hu ⊢
  exact fun a b hab => hu a b (hab.imp (fun ha h' => ha (h h')) (fun hb h' => hb (h h')))

@[expose] def GGSecFiveBPermQTwoCrossing {G : Type} [Group G] (Bs : Subgroup G) {n r : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (π : Fin (r + 2) ≃ Fin n) (d : ℕ) : Prop :=
  (d = 0 → ∀ a ∈ ggBlockComm Bs eta {π 1, π 2},
      ∀ b ∈ ggBlockComm Bs eta {π (Fin.last (r + 1)), π 0}, a * b = b * a) ∧
    (d = 1 → ∀ a ∈ ggBlockComm Bs eta {π 1, π 2} ⊓
        Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G),
      ∀ b ∈ ggBlockComm Bs eta {π 0}, a * b = b * a)

theorem ggSecFiveBPermQTwo_recognition_of_pair {G : Type} [Group G] [Finite G] {Bs Y : Subgroup G}
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) {r : ℕ} (hr : 2 ≤ r)
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod 3))} {m : ℕ}
    (hm : m = 2 * r + 2 ∨ m = 2 * r + 3) {i0 : Fin (r + 2)} {y : G} (hyBs : y ∈ Bs)
    (hYc : CFSG.Open.IsComponentOf Y (Subgroup.centralizer ({y} : Set G)))
    (hNY : Bs ≤ Subgroup.normalizer (Y : Set G)) (eY : ↥Y ≃* SL(m, ZMod 2))
    (hAY : (ggAutomizer Y Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) 3 i0)
    (P : (Fin (r + 2) ≃ Fin (r + 2)) → G → Prop)
    (hlift : ∀ π : Fin (r + 2) ≃ Fin (r + 2), π 0 = i0 → ∃ g₀ : G,
      ∃ hg₀ : g₀ ∈ Subgroup.normalizer (Bs : Set G),
        MulAut.congr eta (ggConjAut Bs hg₀) = SpCoord.permAut (Equiv.swap (π 0) (π 1)) ∧ P π g₀)
    (hcr : ∀ (π : Fin (r + 2) ≃ Fin (r + 2)) (g : (ZMod 2)[X]) [Fact (Irreducible g)] (d : ℕ)
      (ε : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d) (hC : (rootMat g).det = 1)
      (hCp : rootMat g ^ 3 = 1) (κ : SL(m, ZMod 2) →* G),
      GGSecFiveBPermQTwoKFrame Bs Y eta π ε hC hCp κ → (rootPB g).dim = 2 → π 0 = i0 →
        GGSecFiveBPermQTwoCrossing Bs eta π d) :
    ∃ π : Fin (r + 2) ≃ Fin (r + 2), π 0 = i0 ∧ ∃ g₀ : G, P π g₀ ∧
      ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧
        Ψ.range = Y ⊔ Y.map (MulAut.conj g₀).toMonoidHom := by
  classical
  have hm8 : 6 ≤ m := by omega
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 2 := ⟨m - 2, by omega⟩
  obtain ⟨π, hπ0, g, _, d, ε, hC, hCp, κ, hdim, hd1, hF⟩ :=
    ggSecFiveBPermQTwoK_exists_frame rfl hr hm hNY eY eta hAY
  have hcard : M + 2 = 2 * (r + 1) + d := by
    have h := Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h
    rw [hdim] at h
    omega
  obtain ⟨ε', hε'⟩ : ∃ ε' : Fin (M + 2) ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d,
      QTwoCharts.IsPosFrame ε' := QTwoCharts.exists_isPosFrame hdim hcard
  obtain ⟨εo, hεo⟩ : ∃ εo : Fin M ≃ (Fin (rootPB g).dim × Fin r) ⊕ Fin d,
      QTwoCharts.IsPosFrame εo := QTwoCharts.exists_isPosFrame hdim (by omega)
  have hsh := hε'.shift hεo
  obtain ⟨κ', hF'⟩ : ∃ κ' : SL(M + 2, ZMod 2) →* G,
      GGSecFiveBPermQTwoKFrame Bs Y eta π ε' hC hCp κ' := ⟨_, hF.reframe ε'⟩
  obtain ⟨g₀, hg₀, hg₀η, hP⟩ := hlift π hπ0
  have hfix0 : ∀ q : Fin (M + 2), q ∈ SLNS.fixS ε' ({0} : Finset (Fin (r + 1))) ↔
      2 ≤ q.val ∧ q.val < 2 + M := by
    intro q
    rw [hε'.mem_fixS hdim]
    have := q.isLt
    constructor
    · intro h
      have h0 := h 0 (Finset.mem_singleton_self 0)
      simp only [Fin.val_zero] at h0
      omega
    · intro h k hk
      rw [Finset.mem_singleton] at hk
      subst hk
      simp only [Fin.val_zero]
      omega
  have hOv : (blockSL (ZMod 2) (M + 2) M 2 (by omega)).range =
      coordBlockSL (ZMod 2) (SLNS.fixS ε' ({0} : Finset (Fin (r + 1)))) :=
    FF81.range_blockSL_eq _ hfix0
  set S₀ : Set (Fin (r + 2)) := (fun k : Fin (r + 1) => π k.succ) ''
    (((({0} : Finset (Fin (r + 1)))ᶜ : Finset (Fin (r + 1))) : Set (Fin (r + 1)))) with hS₀
  have hY₀ : ggBlockComm Bs eta S₀ =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε' ({0} : Finset (Fin (r + 1))))).map κ' := by
    have h := hF'.blockComm hBsC hyBs hYc (S := ({0} : Finset (Fin (r + 1)))ᶜ)
      ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
      (fun h => by
        have h0 := Finset.mem_univ (0 : Fin (r + 1))
        rw [← h] at h0
        simp at h0)
      (by
        rw [QTwoBlocks.card_fixS_compl, hdim, Finset.card_compl, Finset.card_singleton,
          Fintype.card_fin]
        omega)
    rw [compl_compl] at h
    exact h
  have hS₀fix : Equiv.swap (π 0) (π 1) '' S₀ = S₀ := by
    rw [hS₀, Set.image_image]
    refine Set.image_congr fun k hk => Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · exact fun h => Fin.succ_ne_zero k (π.injective h)
    · intro h
      have hk0 : k ≠ 0 := by simpa using hk
      exact hk0 (Fin.succ_injective _ ((π.injective h).trans Fin.succ_zero_eq_one.symm))
  have hN : ∀ z : SL(M, ZMod 2), ∃ z' : SL(M, ZMod 2),
      g₀ * κ' (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * g₀⁻¹ =
        κ' (blockSL (ZMod 2) (M + 2) M 2 (by omega) z') := by
    intro z
    have h1 : κ' (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) ∈ ggBlockComm Bs eta S₀ := by
      rw [hY₀, ← hOv]
      exact ⟨_, ⟨z, rfl⟩, rfl⟩
    have h2 : g₀ * κ' (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * g₀⁻¹ ∈
        ggBlockComm Bs eta S₀ := by
      rw [← hS₀fix, ← ggBlockComm_map_conj hg₀ hg₀η]
      exact ⟨_, h1, rfl⟩
    rw [hY₀, ← hOv] at h2
    obtain ⟨_, ⟨z', rfl⟩, hz'⟩ := h2
    exact ⟨z', hz'.symm⟩
  obtain ⟨ψ₂, hψ₂, hψ₂r, hov, hblk⟩ := FF81.exists_overlap_chart (by omega : 3 ≤ M) κ' hF'.1 g₀ hN
  have hQnode : ∀ Tb : Finset (Fin r), (⟨M - 1, by omega⟩ : Fin M) ∈ SLNS.fixS εo Tb →
      ∀ j : Fin (M + 1), M - 1 ≤ j.val → ∀ B : SL(2, ZMod 2),
        ψ₂ (blockSL2 (ZMod 2) (M + 1) j B) ∈
          ((coordBlockSL (ZMod 2) (FF81.overlapJK (SLNS.fixS εo Tb))).map κ').map
            (MulAut.conj g₀).toMonoidHom := by
    intro Tb hTb j hj B
    obtain ⟨o, hP1, hP2⟩ := QTwoCharts.exists_compIndicator_eq_pow hF'.2.2.1 εo hC hCp Tb
    refine hblk _ _ o hP1 hP2 (hF'.overlap_conj_torus hsh hg₀ hg₀η hN Tb) ⟨_, ?_, rfl⟩
    refine FF81.range_blockSL_le_coordBlockSL (K := ZMod 2) (by omega) ?_ ⟨B, rfl⟩
    intro q hq1 hq2
    rw [FF81.mem_overlapJQ]
    intro hqM
    have e : (⟨q.val, hqM⟩ : Fin M) = ⟨M - 1, by omega⟩ := Fin.ext (show q.val = M - 1 by omega)
    rw [e]
    exact hTb
  have hKnode : ∀ J'' : Finset (Fin (M + 2)), (∀ q : Fin (M + 2), q.val ≤ 2 → q ∈ J'') →
      ∀ i : Fin (M + 1), i.val ≤ 1 → ∀ A : SL(2, ZMod 2),
        κ' (blockSL2 (ZMod 2) (M + 1) i A) ∈ (coordBlockSL (ZMod 2) J'').map κ' := by
    intro J'' hJ i hi A
    exact ⟨_, FF81.range_blockSL_le_coordBlockSL (K := ZMod 2) (by omega)
      (fun q _ hq2 => hJ q (by omega)) ⟨A, rfl⟩, rfl⟩
  have hQY : ∀ (S' : Finset (Fin (r + 1))) (J'' : Finset (Fin (M + 2))), S'.Nonempty →
      S' ≠ Finset.univ → 3 ≤ (SLNS.fixS ε' S'ᶜ).card → J'' ⊆ SLNS.fixS ε' S'ᶜ →
        ((coordBlockSL (ZMod 2) J'').map κ').map (MulAut.conj g₀).toMonoidHom ≤
          ggBlockComm Bs eta (Equiv.swap (π 0) (π 1) ''
            ((fun k => π k.succ) '' (S' : Set (Fin (r + 1))))) := by
    intro S' J'' hne hnu h3 hsub
    rw [← ggBlockComm_map_conj hg₀ hg₀η, hF'.blockComm hBsC hyBs hYc hne hnu h3]
    exact Subgroup.map_mono (Subgroup.map_mono (coordBlockSL_mono' hsub))
  have hKY : ∀ (S' : Finset (Fin (r + 1))) (J'' : Finset (Fin (M + 2))), S'.Nonempty →
      S' ≠ Finset.univ → 3 ≤ (SLNS.fixS ε' S'ᶜ).card → J'' ⊆ SLNS.fixS ε' S'ᶜ →
        (coordBlockSL (ZMod 2) J'').map κ' ≤
          ggBlockComm Bs eta ((fun k => π k.succ) '' (S' : Set (Fin (r + 1)))) := by
    intro S' J'' hne hnu h3 hsub
    rw [hF'.blockComm hBsC hyBs hYc hne hnu h3]
    exact Subgroup.map_mono (coordBlockSL_mono' hsub)
  have h1 : (⟨0, by omega⟩ : Fin (r + 1)).succ = (1 : Fin (r + 2)) := by
    apply Fin.ext
    change 1 = 1 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have h2 : (⟨1, by omega⟩ : Fin (r + 1)).succ = (2 : Fin (r + 2)) := by
    apply Fin.ext
    change 2 = 2 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have h3 : (⟨2, by omega⟩ : Fin (r + 1)).succ = (3 : Fin (r + 2)) := by
    apply Fin.ext
    change 3 = 3 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hπ01 : π 0 ≠ π 1 := π.injective.ne (Fin.ne_of_val_ne (by simp))
  have hπl0 : π (Fin.last (r + 1)) ≠ π 0 :=
    π.injective.ne (Fin.ne_of_val_ne (by simp))
  have hπl1 : π (Fin.last (r + 1)) ≠ π 1 :=
    π.injective.ne (Fin.ne_of_val_ne (by simp; omega))
  have hpair : ∀ q : Fin (M + 2), q.val ≤ 2 →
      q ∈ SLNS.fixS ε' ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (r + 1)))ᶜ := by
    intro q hq
    rw [hε'.mem_fixS hdim]
    intro k hk hc'
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hk0 : k.val ≠ 0 := fun h => hk.1 (Fin.ext h)
    have hk1 : k.val ≠ 1 := fun h => hk.2 (Fin.ext h)
    omega
  have hcard_pair : 3 ≤ (SLNS.fixS ε'
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (r + 1)))ᶜ).card := by
    rw [QTwoBlocks.card_fixS_compl, hdim, Finset.card_pair (by simp [Fin.ext_iff])]
    omega
  have hpair_ne : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have h0 := Finset.mem_univ (⟨2, by omega⟩ : Fin (r + 1))
    rw [← h] at h0
    simp [Fin.ext_iff] at h0
  have key : ∃ X Z : Subgroup G,
      (∀ i : Fin (M + 1), i.val ≤ 1 → ∀ A : SL(2, ZMod 2),
        κ' (blockSL2 (ZMod 2) (M + 1) i A) ∈ X) ∧
      (∀ j : Fin (M + 1), M - 1 ≤ j.val → ∀ B : SL(2, ZMod 2),
        ψ₂ (blockSL2 (ZMod 2) (M + 1) j B) ∈ Z) ∧
      ∀ a ∈ X, ∀ b ∈ Z, a * b = b * a := by
    rcases (by omega : d = 0 ∨ d = 1) with hd | hd
    ·
      refine ⟨ggBlockComm Bs eta {π 1, π 2}, ggBlockComm Bs eta {π (Fin.last (r + 1)), π 0},
        fun i hi A => ?_, fun j hj B => ?_,
        (hcr π g d ε' hC hCp κ' hF' hdim hπ0).1 hd⟩
      · have hX := hKY _ _ ⟨⟨0, by omega⟩, by simp⟩ hpair_ne hcard_pair
          (fun q hq => hq) (hKnode _ hpair i hi A)
        rwa [image_succ_pair, h1, h2] at hX
      ·
        set Tb : Finset (Fin r) := ({⟨r - 1, by omega⟩} : Finset (Fin r))ᶜ with hTb
        have hTbM : (⟨M - 1, by omega⟩ : Fin M) ∈ SLNS.fixS εo Tb := by
          rw [hεo.mem_fixS hdim]
          intro k hk hc'
          have hc'' : 2 * k.val ≤ M - 1 ∧ M - 1 < 2 * k.val + 2 := hc'
          simp only [hTb, Finset.mem_compl, Finset.mem_singleton] at hk
          exact hk (Fin.ext (show k.val = r - 1 by omega))
        have hsub : FF81.overlapJK (SLNS.fixS εo Tb) ⊆ SLNS.fixS ε'
            ({⟨0, by omega⟩, Fin.last r} : Finset (Fin (r + 1)))ᶜ := by
          intro p hp
          rw [FF81.mem_overlapJK] at hp
          rw [hε'.mem_fixS hdim]
          intro k hk hc'
          simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          have hk0 : k.val ≠ 0 := fun h => hk.1 (Fin.ext h)
          have hkr : k.val ≠ r := fun h => hk.2 (Fin.ext h)
          have hk' := k.isLt
          have h2p : 2 ≤ p.val := by omega
          have hp' := hp h2p
          rw [hεo.mem_fixS hdim] at hp'
          refine hp' ⟨k.val - 1, by omega⟩ ?_
            (show 2 * (k.val - 1) ≤ p.val - 2 ∧ p.val - 2 < 2 * (k.val - 1) + 2 by omega)
          simp only [hTb, Finset.mem_compl, Finset.mem_singleton, Fin.ext_iff]
          omega
        have hZ := hQY _ _ ⟨⟨0, by omega⟩, by simp⟩ (by
            intro h
            have h0 := Finset.mem_univ (⟨1, by omega⟩ : Fin (r + 1))
            rw [← h] at h0
            simp [Fin.ext_iff] at h0
            omega)
          (by
            rw [QTwoBlocks.card_fixS_compl, hdim,
              Finset.card_pair (by simp [Fin.ext_iff]; omega)]
            omega)
          hsub (hQnode Tb hTbM j hj B)
        rwa [image_succ_pair, h1, Fin.succ_last, Set.image_insert_eq, Set.image_singleton,
          Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hπl0 hπl1, Set.pair_comm] at hZ
    ·
      refine ⟨ggBlockComm Bs eta {π 1, π 2} ⊓
          Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G), ggBlockComm Bs eta {π 0},
        fun i hi A => ?_, fun j hj B => ?_,
        (hcr π g d ε' hC hCp κ' hF' hdim hπ0).2 hd⟩
      ·
        have hY12 := hF'.blockComm hBsC hyBs hYc ⟨⟨0, by omega⟩, by simp⟩ hpair_ne hcard_pair
        rw [image_succ_pair, h1, h2] at hY12
        have hcard3 : 3 ≤ (SLNS.fixS ε' ({⟨2, by omega⟩} : Finset (Fin (r + 1)))ᶜ).card := by
          rw [QTwoBlocks.card_fixS_compl, hdim, Finset.card_singleton]
          omega
        have hY3 := hF'.blockComm hBsC hyBs hYc ⟨⟨2, by omega⟩, by simp⟩
          (by
            intro h
            have h0 := Finset.mem_univ (⟨0, by omega⟩ : Fin (r + 1))
            rw [← h] at h0
            simp [Fin.ext_iff] at h0) hcard3
        rw [image_succ_single, h3] at hY3
        have hsd := coordBlockSL_map_inf_centralizer_eq_sdiff κ' hF'.1
          (SLNS.fixS ε' ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (r + 1)))ᶜ)
          (SLNS.fixS ε' ({⟨2, by omega⟩} : Finset (Fin (r + 1)))ᶜ) (by omega)
          ⟨⟨4, by omega⟩, by
            rw [hε'.mem_fixS hdim]
            intro k hk hc'
            have hc'' : 2 * k.val ≤ 4 ∧ 4 < 2 * k.val + 2 := hc'
            simp only [Finset.mem_compl, Finset.mem_singleton] at hk
            exact hk (Fin.ext (show k.val = 2 by omega)), by
            rw [hε'.mem_fixS hdim]
            intro h
            exact h ⟨2, by omega⟩ (by simp [Fin.ext_iff])
              (show 2 * 2 ≤ 4 ∧ 4 < 2 * 2 + 2 by omega)⟩
        rw [hY12, hY3, hsd]
        refine hKnode _ (fun q hq => Finset.mem_sdiff.mpr ⟨hpair q hq, ?_⟩) i hi A
        rw [hε'.mem_fixS hdim]
        intro h
        exact h ⟨q.val / 2, by omega⟩ (by simp [Fin.ext_iff]; omega)
          (show 2 * (q.val / 2) ≤ q.val ∧ q.val < 2 * (q.val / 2) + 2 by omega)
      ·
        have hTbM : (⟨M - 1, by omega⟩ : Fin M) ∈ SLNS.fixS εo (Finset.univ : Finset (Fin r)) := by
          rw [hεo.mem_fixS hdim]
          intro k _ hc'
          have := k.isLt
          have hc'' : 2 * k.val ≤ M - 1 ∧ M - 1 < 2 * k.val + 2 := hc'
          omega
        have hsub : FF81.overlapJK (SLNS.fixS εo (Finset.univ : Finset (Fin r))) ⊆ SLNS.fixS ε'
            ({⟨0, by omega⟩} : Finset (Fin (r + 1)))ᶜ := by
          intro p hp
          rw [FF81.mem_overlapJK] at hp
          rw [hε'.mem_fixS hdim]
          intro k hk hc'
          simp only [Finset.mem_compl, Finset.mem_singleton] at hk
          have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
          have hk' := k.isLt
          have h2p : 2 ≤ p.val := by omega
          have hp' := hp h2p
          rw [hεo.mem_fixS hdim] at hp'
          exact hp' ⟨k.val - 1, by omega⟩ (Finset.mem_univ _)
            (show 2 * (k.val - 1) ≤ p.val - 2 ∧ p.val - 2 < 2 * (k.val - 1) + 2 by omega)
        have hZ := hQY _ _ ⟨⟨0, by omega⟩, by simp⟩ (by
            intro h
            have h0 := Finset.mem_univ (⟨1, by omega⟩ : Fin (r + 1))
            rw [← h] at h0
            simp [Fin.ext_iff] at h0)
          (by
            rw [QTwoBlocks.card_fixS_compl, hdim, Finset.card_singleton]
            omega)
          hsub (hQnode _ hTbM j hj B)
        rwa [image_succ_single, h1, Set.image_singleton, Equiv.swap_apply_right] at hZ
  obtain ⟨X, Z, hX, hZ, hXZ⟩ := key
  obtain ⟨Ψ, hΨ, hΨr⟩ := FF81.exists_injective_of_two_charts (by omega) κ' ψ₂ hF'.1 hψ₂ hov
    fun i j hi hj A B => hXZ _ (hX i hi A) _ (hZ j hj B)
  refine ⟨π, hπ0, g₀, hP, Ψ, hΨ, ?_⟩
  rw [hΨr, hψ₂r, hF'.2.1]

section Rec


theorem ggSecFiveBPermQTwo_recognition_of_crossing (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {r : ℕ} (hr : 2 ≤ r)
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod 3))}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull (r + 2) 3)
    {m : ℕ} {K : Subgroup G} {i0 : Fin (r + 2)}
    (hc : GGSecFiveBPermQTwoCell 3 Bs L 𝒦 (r + 2) eta m K i0)
    (hcr : ∀ (π : Fin (r + 2) ≃ Fin (r + 2)) (g : (ZMod 2)[X]) [Fact (Irreducible g)] (d : ℕ)
      (ε : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d) (hC : (rootMat g).det = 1)
      (hCp : rootMat g ^ 3 = 1) (κ : SL(m, ZMod 2) →* G),
      GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ → (rootPB g).dim = 2 → π 0 = i0 →
        ∀ y ∈ Bs, CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) →
          GGSecFiveBPermQTwoCrossing Bs eta π d) :
    ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ K := by
  classical
  have hcfg := hRt.1.1
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hRt.1.1.2.1.2.2.2
  have hm : m = 2 * r + 2 ∨ m = 2 * r + 3 := by rcases hc.2.1 with h | h <;> omega
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 2 := ⟨m - 2, by omega⟩
  obtain ⟨y, hNy⟩ := hRt.2.2.2.1.2 K hc.2.2.1
  have hyBs : y ∈ Bs := hRt.1.1.2.1.1 hNy.1.2.1
  have hNK : Bs ≤ Subgroup.normalizer (K : Set G) := (hRt.1.2.2.1.2 y K hNy).le_normalizer
  have hKp : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) K := hNy.1.2.2.2.2.1
  obtain ⟨eK⟩ := hc.2.2.2.2.1
  have hSq : CFSG.Open.IsQuasisimple SL(M + 2, ZMod 2) := by
    have hq := SpecialLinear.isQuasisimple (M + 1) (ZMod 2) (by omega)
    have := hq.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
  have hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    ⟨hKp.1, isSubnormal_iff_open.mp hKp.2.1, CFSG.Open.IsQuasisimple.of_mulEquiv eK hSq⟩
  obtain ⟨ψL, hkerL, hrangeL⟩ := hc.2.2.2.1
  obtain ⟨π, hπ0, g₀, ⟨σ, χ, hLF, rfl⟩, Ψ, hΨ, hΨr⟩ := ggSecFiveBPermQTwo_recognition_of_pair hBsC hr
    hm hyBs hKc hNK eK hc.2.2.2.2.2
    (fun π g₀ => ∃ (σ : SL(r + 2, GaloisField 2 2) →* G)
      (χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ),
        GGSecFiveBPermSpLFrame Bs L eta π σ χ ∧ g₀ = σ (TypeA.permSL (Equiv.swap (0 : Fin (r + 2)) 1)))
    (fun π _ => by
      obtain ⟨σ, χ, hLF⟩ := exists_ggSecFiveBPermSpLFrame hMp hcfg.tableB_facts.1
        hcfg.1.2.2.2.2.2.1.2.1 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hRt.1.2.2.1.1
        hcfg.card_bstar_inf_centralizer_L.le (by omega) eta hLeta (f := 2) (by omega) hkerL hrangeL
        r π
      obtain ⟨hg₀, hg₀η⟩ := hLF.permSL_swap_normalizer hBsC hLeta (by omega)
        (show (0 : Fin (r + 2)) ≠ 1 from Fin.ne_of_val_ne (by simp))
      exact ⟨_, hg₀, hg₀η, σ, χ, hLF, rfl⟩)
    (fun π g _ d ε hC hCp κ hF hdim hπ0 => hcr π g d ε hC hCp κ hF hdim hπ0 y hyBs hKc)
  exact ⟨Ψ, ggSecFiveBPermQTwo_original_recognition_range hRt hc (by omega) π hπ0 hLF Ψ hΨ hΨr⟩

theorem ggSecFiveBPermQTwo_recognition_of_five (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {n : ℕ} (hn : 5 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    {m : ℕ} {K : Subgroup G} {i0 : Fin n} (hc : GGSecFiveBPermQTwoCell 3 Bs L 𝒦 n eta m K i0) :
    ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ K := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hRt.1.1.2.1.2.2.2
  have hlift : ∀ a b : Fin (r + 2), a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b) := by
    intro a b hab
    obtain ⟨w, -, hw, hwη⟩ := exists_mem_conjAut_eq_permAut_swap hLeta hab
    exact ⟨w, hw, hwη⟩
  refine ggSecFiveBPermQTwo_recognition_of_crossing hMp hRt (by omega) hLeta hc ?_
  intro π g _ d ε hC hCp κ hF hdim _ y hyBs hKc
  exact ⟨fun hd => GGSecFiveBPermQTwoKFrame.crossing_even hF hBsC hyBs hKc hdim (by omega) hlift hd,
    fun hd => GGSecFiveBPermQTwoKFrame.crossing_odd hF hBsC hyBs hKc hdim (by omega) hlift hd⟩

@[expose] def GGSecFiveBPermQTwoRecFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → n = 4 →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        B = Bs → GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel n p lab) p Bs L →
      ∀ (m : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermQTwoCell p Bs L 𝒦 n eta m K i0 →
        ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ K

theorem ggSecFiveBPermQTwoRecInput_of_mp (hMp : GGInnerDiagMpInput)
    (h4 : GGSecFiveBPermQTwoRecFourInput) : GGSecFiveBPermQTwoRecInput := by
  intro G _ _ p B Bs x L D J 𝒦 hRt hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab m K i0 hc
  rcases eq_or_lt_of_le hn with h | h
  · exact h4 G p B Bs x L D J 𝒦 hRt hT1 n e hP h.symm eta h𝒦 hLeta hRM hG0 hB hlab m K i0 hc
  · obtain rfl := hc.1
    exact ggSecFiveBPermQTwo_recognition_of_five hMp hRt h hLeta hc

end Rec

end CFSG.StandardType

end
