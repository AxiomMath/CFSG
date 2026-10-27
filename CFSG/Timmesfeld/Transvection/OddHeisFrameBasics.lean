module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.PresSU
public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.Transvection.GenerateRel
public import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.FrameResidue
public import CFSG.LieType.Universal.Unitary.Roots.Levels
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
import CFSG.Timmesfeld.Transvection.RelBuildField
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddNormalize
import CFSG.Timmesfeld.Transvection.OddSU3Torus
import CFSG.Timmesfeld.Transvection.OddResidueBlock
import CFSG.Timmesfeld.Transvection.PresSURankOne
import CFSG.Timmesfeld.Transvection.RankThreeA2Coords
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Timmesfeld.ARS.ConfigTransfer
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec8Levi
public import CFSG.Timmesfeld.Special.TwoCore
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres CFSG.LocalAnalysis.UniquenessCase
open scoped commutatorElement

namespace SURelations

variable {r : ℕ} {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F} {G : Type*} [Group G]

theorem eq_of_ξ_eq (R : SURelations r σ G) (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ x, σ x ≠ x) {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b)
    (hL : ∀ c, σ c = c → R.ξL a c = 1 → c = 0) {s s' : F}
    (h : R.ξ a b s = R.ξ a b s') : s = s' := by
  have hsq : R.ξ a b s * R.ξ a b s' = 1 := by
    simpa [h.symm, R.inv_eq hab s] using mul_inv_cancel (R.ξ a b s)
  have hzero : R.ξ a b (s + s') = 1 := by
    rw [R.add a b hab]
    exact hsq
  have htrace : ∀ x : F, σ (s + s') * x + σ (σ (s + s') * x) = 0 := by
    intro x
    have hfix : σ ((s + s') * σ x + σ (s + s') * x) =
        (s + s') * σ x + σ (s + s') * x := by
      rw [map_add, map_mul, map_mul, hσ, hσ, add_comm]
    have hξ : R.ξL a ((s + s') * σ x + σ (s + s') * x) = 1 := by
      have h' := R.trace a b hab (s + s') x
      rw [hzero, commutatorElement_one_left] at h'
      exact h'.symm
    have h := hL _ hfix hξ
    rw [map_mul, hσ, add_comm]
    exact h
  have hκ : σ (s + s') = 0 := RelBuild.eq_zero_of_trace_mul (σ := σ) hne htrace
  have hd : s + s' = 0 := (map_eq_zero σ).1 hκ
  have hss' := add_eq_zero_iff_eq_neg.mp hd
  rwa [CharTwo.neg_eq] at hss'

end SURelations

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

section

local notation "heis₃" => suHeis (unitaryInvolution F 2 n)
  (unitaryInvolution_involutive hFn) (m := 3) (Nat.not_even_two_mul_add_one 1 : ¬ Even 3)
  (Sum.inl (0 : Fin (3 / 2)))

namespace SURelations.HasFrameImages

theorem map_su3Top_su3Bot_of_comp
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm) :
    (su3Top (unitaryInvolution F 2 n)).map θ = P (cLastIdx r hr) ∧
      (su3Bot (unitaryInvolution F 2 n)).map θ = Q (cLastIdx r hr) :=
  map_su3Top_su3Bot_of_comp_su3Chord hθc
    (hR.map_lastBlock (F := F) (n := n) hFn (even_two_mul r) hm).1
    (hR.map_lastBlock (F := F) (n := n) hFn (even_two_mul r) hm).2

end SURelations.HasFrameImages

theorem IsMaxFrame.oddPrevLift_normalized
    (hΔ : IsRootClass Δ) (hF : IsMaxFrame Δ P Q)
    (hns : ¬IsSmallFrame Δ P Q (cLastIdx r hr))
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ) :
    Odd (Nat.card (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).ker) ∧
      (su3Top (unitaryInvolution F 2 n)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) = P (cPrevIdx r hr) ∧
      (su3Bot (unitaryInvolution F 2 n)).map
          (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) = Q (cPrevIdx r hr) := by
  have hker : (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).ker = θ.ker :=
    MonoidHom.ker_comp_of_injective θ _ (MulAut.conj _).injective
  have hlong := IsMaxFrame.su3_residue_oddPrevLift hFn hr hm hΔ hF hns hR hθr hθc hθmem
  have htop : (su3Top (unitaryInvolution F 2 n)).map
      (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) = P (cPrevIdx r hr) := by
    apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su3Top_iff (σ := unitaryInvolution F 2 n)).1 hx
      rw [(hlong.2.2.2 c hc).1]
      exact (hR.long (Sum.inl (cPrevIdx r hr)) _).2 ⟨c, hc, rfl⟩
    · intro g hg
      obtain ⟨c, hc, rfl⟩ :=
        (hR.long (Sum.inl (cPrevIdx r hr)) g).1 (by simpa using hg)
      exact ⟨suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c,
        (mem_su3Top_iff (σ := unitaryInvolution F 2 n)).2 ⟨c, hc, rfl⟩,
        (hlong.2.2.2 c hc).1⟩
  have hbot : (su3Bot (unitaryInvolution F 2 n)).map
      (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ) = Q (cPrevIdx r hr) := by
    apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su3Bot_iff (σ := unitaryInvolution F 2 n)).1 hx
      rw [(hlong.2.2.2 c hc).2]
      exact (hR.long (Sum.inr (cPrevIdx r hr)) _).2 ⟨c, hc, rfl⟩
    · intro g hg
      obtain ⟨c, hc, rfl⟩ :=
        (hR.long (Sum.inr (cPrevIdx r hr)) g).1 (by simpa using hg)
      exact ⟨suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c,
        (mem_su3Bot_iff (σ := unitaryInvolution F 2 n)).2 ⟨c, hc, rfl⟩,
        (hlong.2.2.2 c hc).2⟩
  exact ⟨hker.symm ▸ hθo, htop, hbot⟩

theorem OddFrameCompatible.ξL_inl_eq_map_suHeis
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {c : F}
    (hc : unitaryInvolution F 2 n c = c) :
    R.ξL (Sum.inl (cLastIdx r hr)) c = θ (heis₃ 0 c) ∧
      R.ξL (Sum.inl (cPrevIdx r hr)) c =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis₃ 0 c) := by
  constructor
  · rw [← R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cLastIdx r hr)) hc,
      (hd.long_last c hc).1,
      suHeis_zero_left (σ := unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2))) c]
  · rw [← R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cPrevIdx r hr)) hc,
      ← hd.oddPrevLift_suLong_inl hc,
      suHeis_zero_left (σ := unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2))) c]

end

section

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem IsMaxFrame.residueGroup_inf_shortRootGroup_eq_bot (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) :
    residueGroup Δ P Q i ⊓ shortRootGroup Δ (P i) (Q i) (P k) (Q k) = ⊥ := by
  apply le_antisymm
  · intro b hb
    obtain ⟨hbR, hbS⟩ := hb
    have hbY : b ∈ shortRootGroup Δ (P k) (Q k) (P i) (Q i) := by
      rwa [shortRootGroup_swap_pairs (P k) (Q k) (P i) (Q i)] at hbS
    have hbU : b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) :=
      Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_sup_right hbY))
    have hcb : conjSub (Q k) b = Q k :=
      conjSub_of_forall_commute fun x hx =>
        commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) (k := i) (i := k)
          (Ne.symm hik) b hbR x (Subgroup.mem_sup_right hx)
    rw [Subgroup.mem_bot]
    exact IsMaxFrame.eq_one_of_mem_map_heis_sup_of_conjSub_eq h hML hq hF hns hFn hcard
      hθr hθk hθt hθb hmem hik hbU hcb
  · exact bot_le

end

section

variable (R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H)

theorem SURelations.toHom_shortWeyl_cPrevIdx
    (hk : (cPrevIdx r hr).val + 1 < 2 * r / 2) (c : F) :
    R.toHom hFn (even_two_mul r) hm
      (shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) c) =
      R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
        R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
        R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c := by
  have hidx : (⟨(cPrevIdx r hr).val + 1, hk⟩ : Fin (2 * r / 2)) = cLastIdx r hr := by
    apply Fin.ext
    simp only [cPrevIdx, cLastIdx, Fin.val_mk]
    omega
  rw [← shortWeyl_eq (m := 2 * r) (σ := unitaryInvolution F 2 n) (i := cPrevIdx r hr)
    (unitaryInvolution_involutive hFn) hk c, map_mul, map_mul,
    R.toHom_suElt hFn (even_two_mul r) hm (idx_short hk) c,
    R.toHom_suElt hFn (even_two_mul r) hm (idx_short' hk) (-c⁻¹), hidx]

theorem SURelations.toHom_levelWeyl_cPrevIdx :
    R.toHom hFn (even_two_mul r) hm
      (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (cPrevIdx r hr)) =
      R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) 1 *
        R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-1⁻¹) *
        R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) 1 := by
  have hk : (cPrevIdx r hr).val + 1 < 2 * r / 2 := by
    simp only [cPrevIdx, Fin.val_mk]
    omega
  have hstep : levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      (cPrevIdx r hr) =
      shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) 1 := by
    rw [levelWeyl, dite_eq_left hk]
  rw [hstep]
  exact R.toHom_shortWeyl_cPrevIdx hFn hr hm hk 1

end

end CFSG.Timmesfeld.Transvection