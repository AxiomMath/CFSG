module

import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped Pointwise

namespace Res611Minus

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_thetaQuotCentralizer_of_pow (he : CFSG.Assembly.evenRank G = 3)
    {L B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBL : B ≤ L)
    (h81 : 81 ≤ Nat.card B) {k : ℕ} : ∀ {w : G}, w ∈ thetaQuotCentralizer L →
      w ^ (2 ^ k) = 1 → w = 1 := by
  induction k with
  | zero => intro w _ hk; simpa using hk
  | succ k ih =>
    intro w hw hk
    have h2 : w ^ 2 = 1 := ih (Subgroup.pow_mem _ hw 2)
      (by rw [← pow_mul, ← pow_succ']; exact hk)
    exact Res611Res3.eq_one_of_mem_thetaQuotCentralizer he hB hBL h81 hw h2

theorem inf_thetaQuotCentralizer_eq_bot_of_isPGroup (he : CFSG.Assembly.evenRank G = 3)
    {L B U : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBL : B ≤ L)
    (h81 : 81 ≤ Nat.card B) (hU : IsPGroup 2 U) : U ⊓ thetaQuotCentralizer L = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huU, huC⟩
  obtain ⟨k, hk⟩ := hU ⟨u, huU⟩
  have hk' : u ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact eq_one_of_mem_thetaQuotCentralizer_of_pow he hB hBL h81 huC hk'

theorem exists_invariant_two_subgroup_cover {L E V : Subgroup G}
    (hE3 : IsPGroup 3 E) (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hV2 : IsPGroup 2 V)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hVLC : V ≤ L ⊔ thetaQuotCentralizer L) :
    ∃ U ∈ invariantPiSubgroups L E (piOf 2),
      V ≤ U ⊔ thetaQuotCentralizer L ∧ U ≤ V ⊔ thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set C := thetaQuotCentralizer L with hC
  have hθN := normalizer_le_normalizer_theta L
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hθC := theta_le_thetaQuotCentralizer L
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  set Y := (V ⊔ C) ⊓ L with hY
  set Z := C ⊓ L with hZ
  have hZY : Z ≤ Y := inf_le_inf_right L le_sup_right
  have hYL : Y ≤ L := inf_le_right
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) :=
    (le_inf (hYL.trans (hLN.trans hCN)) (hYL.trans hLN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hYpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k) ∈ Z := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hV2 (hVL.trans hCN) hy.1
    exact ⟨k, hk, L.pow_mem hy.2 _⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 Y) := inferInstance
  set RG := (R : Subgroup Y).map Y.subtype with hRG
  have hRGY : RG ≤ Y := Subgroup.map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map Y.subtype
  have hYRZ : Y ≤ RG ⊔ Z := le_sylow_sup_of_forall_pow_mem hZY hYZ hYpow R
  set W := RG ⊔ θL with hW
  have hWL : W ≤ L := sup_le (hRGY.trans hYL) (theta_le L)
  have hRGW : RG ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro r hr x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hr) x).mp
        hx)
    · intro r hr x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_theta L (hYL (hRGY hr))) x).mp hx)
  have hZW : Z ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro z hz x hx
      have hxL : x ∈ L := hYL (hRGY hx)
      have h1 := (mem_thetaQuotCentralizer_iff.mp hz.1).2 x hxL
      rw [show z * x * z⁻¹ = x * (x⁻¹ * (z * x * z⁻¹)) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right h1)
    · intro z hz x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L hz.2)
        x).mp hx)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYRZ.trans (sup_le hRGW hZW)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := hEL.trans hCN
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    have h1 : E ≤ Subgroup.normalizer ((V ⊔ C : Subgroup G) : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro e he x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEV he) x).mp hx)
      · intro e he x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hEC he) x).mp hx)
    exact (le_inf h1 hEL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      set Re := RG.map (MulAut.conj e).toMonoidHom
      have hReY : Re ≤ Y := by
        rintro _ ⟨w, hw, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hEY he) w).mp (hRGY hw)
      obtain ⟨y, hyY, hle⟩ := exists_le_conj_sylow R hReY (hRG2.map _)
      have h1 : e * x * e⁻¹ ∈ RG.map (MulAut.conj y).toMonoidHom := hle ⟨x, hx, rfl⟩
      obtain ⟨w, hw, hwx⟩ := h1
      have h2 : y * w * y⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hYW hyY) w).mp (Subgroup.mem_sup_left hw)
      change y * w * y⁻¹ = e * x * e⁻¹ at hwx
      rw [← hwx]
      exact h2
    · intro e he x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hθN (hEL he)) x).mp hx)
  have hW3 : ¬ 3 ∣ Nat.card W := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hRG2
    ((hRGY.trans hYL).trans (le_normalizer_theta L)) (theta_solvable_and_not_dvd L).2
  obtain ⟨Q, hEQ⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three E W hE3 hW3 hEW 2 Nat.prime_two
  set U := (Q : Subgroup W).map W.subtype with hU
  have hUW : U ≤ W := Subgroup.map_subtype_le _
  have hU2 : IsPGroup 2 U := Q.isPGroup'.map W.subtype
  refine ⟨U, (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hUW.trans hWL, hU2, hEQ⟩,
    ?_, ?_⟩
  · have hWpow : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ θL := fun w hw =>
      exists_pow_mem_of_mem_sup hRG2 ((hRGY.trans hYL).trans (le_normalizer_theta L)) hw
    have hWU : W ≤ U ⊔ θL := le_sylow_sup_of_forall_pow_mem le_sup_right
      (sup_le ((hRGY.trans hYL).trans (le_normalizer_theta L)) Subgroup.le_normalizer) hWpow Q
    have hVYC : V ≤ Y ⊔ C := by
      intro v hv
      have hv' : v ∈ (L : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right L C (hLN.trans hCN)]
        exact hVLC hv
      obtain ⟨l, hl, z, hz, rfl⟩ := hv'
      have hlY : l ∈ Y :=
        ⟨by rw [show l = (l * z) * z⁻¹ by group]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
              (Subgroup.mem_sup_right (inv_mem hz)),
          hl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlY) (Subgroup.mem_sup_right hz)
    refine hVYC.trans (sup_le (hYRZ.trans (sup_le ?_ ?_)) le_sup_right)
    · exact (le_sup_left.trans hWU).trans (sup_le le_sup_left (hθC.trans le_sup_right))
    · exact inf_le_left.trans le_sup_right
  · exact hUW.trans (sup_le (hRGY.trans inf_le_left) (hθC.trans le_sup_right))

omit [Finite G] in
theorem exists_mul_eq_of_mem_sup {H C : Subgroup G} (hHC : H ≤ Subgroup.normalizer (C : Set G))
    {x : G} (hx : x ∈ H ⊔ C) : ∃ h ∈ H, ∃ z ∈ C, x = h * z := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H C hHC] at hx
  obtain ⟨h, hh, z, hz, rfl⟩ := hx
  exact ⟨h, hh, z, hz, rfl⟩

end Res611Minus

open Res611Minus

end CFSG.RankThree.PartTwo.Sec6
