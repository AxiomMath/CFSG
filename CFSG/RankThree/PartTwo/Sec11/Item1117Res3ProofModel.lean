module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
public import CFSG.RankThree.PartTwo.Sec11.Item119K

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

namespace Item1117Res3Proof


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem eq_one_of_mk_eq_one (h : Sec11Data G A c L a R Y d x s r g) {w : G}
    (hwP : w ∈ sec11P R g) (hwY : w ∈ Y)
    (hw : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨w, hwY⟩ = 1) : w = 1 := by
  obtain ⟨k, hk⟩ := h.isPGroup_sec11P ⟨w, hwP⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw
  have h2 := eq_one_of_mem_theta_of_pow_eq_one hw (k := k) (by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk)
  simpa using congrArg Subtype.val h2

theorem exists_inner_model (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {F : ∀ (X : Type) [Group X], Prop}
    (hNo : NoOuterType424For F)
    (hZ : ∃ (X : Type) (_ : Group X), F X ∧
      Nonempty ((Y ⧸ aschbacherSolvableCore 3 Y) ≃* _root_.commutator X))
    (hcen : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ z : Y ⧸ aschbacherSolvableCore 3 Y,
      MulAut.conj z = Item426.thetaAut Y hcN ∧ MulAut.conj z ^ 3 = 1 ∧
      ((sec11K L a).subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) ∈
        thetaComponentsIn (Item426.fixSub (MulAut.conj z)) ∧
      IsType424 ((((sec11K L a).subgroupOf Y).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) ⧸ aschbacherSolvableCore 3
          (((sec11K L a).subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)))) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩ *
          QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
            ⟨d, h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
            ⟨d, h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)⟩ *
          QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩ ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩ * z *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩)⁻¹ * z⁻¹ ∈
        Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
          ⟨d, h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)⟩) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩ * z ≠
        z * QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcA : c ∈ A := h.mem_A
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hgY : g ∈ Y := h.g_mem.1
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  have hK' := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
  have hT := kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  set J := ((sec11K L a).subgroupOf Y).map π with hJdef
  have hJα : J ∈ thetaComponentsIn (Item426.fixSub (Item426.thetaAut Y hcN)) :=
    Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK'
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J) := isType424_of_mulEquiv eK.symm hT
  have hα3 : Item426.thetaAut Y hcN ^ 3 = 1 := Item426.thetaAut_pow_eq_one Y hcN hc3
  have hin : Item426.thetaAut Y hcN ∈
      (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →* MulAut _).range := by
    by_contra hnot
    exact hNo _ hZ _ J hα3 hnot hJα hJT
  obtain ⟨z, hz⟩ := hin
  have hz3 : MulAut.conj z ^ 3 = 1 := by rw [hz]; exact hα3
  have hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) := by rw [hz]; exact hJα
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hdY : d ∈ Y := hKY hdK
  set v := π ⟨d, hdY⟩ with hv
  have hdpow : ∀ n : ℤ, π ⟨d ^ n, Y.zpow_mem hdY n⟩ = 1 → d ^ n = 1 := by
    intro n h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (by
      apply Subtype.ext
      simp only [pow_one, SubgroupClass.coe_pow, Subgroup.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow])
    simpa using congrArg Subtype.val h2
  set gb := π ⟨g, hgY⟩ with hgb
  obtain ⟨k, hk⟩ := h.pow_eq_one
  have hd3o : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hgd : g * d = d * g := Sec12.commute_of_conj_mem_zpowers hd3o
    ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h h.g_mem.2) d).mp
      (Subgroup.mem_zpowers d)) hk
  have hgbv : gb * v = v * gb := by
    rw [hgb, hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgd
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Item1117Proof.conj_g_c_mem h117 h)
  have hgN : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hgY
  have hconjg : MulAut.conj gb = Sec12.thetaBarAct Y ⟨g, hgN⟩ :=
    (Sec12.thetaBarAct_of_mem hgY).symm
  have hconjd : ∀ n : ℤ, MulAut.conj (v ^ n) =
      Sec12.thetaBarAct Y ⟨d ^ n, Subgroup.le_normalizer (Y.zpow_mem hdY n)⟩ := by
    intro n
    rw [Sec12.thetaBarAct_of_mem (Y.zpow_mem hdY n), hv, ← map_zpow]
    rfl
  have hcomm : MulAut.conj (gb * z * gb⁻¹ * z⁻¹) = MulAut.conj (v ^ j) := by
    rw [hconjd j, map_mul, map_mul, map_mul, map_inv, map_inv, hconjg, hz]
    change Sec12.thetaBarAct Y ⟨g, hgN⟩ * Sec12.thetaBarAct Y ⟨c, hcN⟩ *
      (Sec12.thetaBarAct Y ⟨g, hgN⟩)⁻¹ * (Sec12.thetaBarAct Y ⟨c, hcN⟩)⁻¹ = _
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [hj])
  have hcomm' : gb * z * gb⁻¹ * z⁻¹ = v ^ j := by
    have h1 : MulAut.conj ((v ^ j)⁻¹ * (gb * z * gb⁻¹ * z⁻¹)) = 1 := by
      rw [map_mul, map_inv, hcomm, inv_mul_cancel]
    have h2 := Sec12.mem_center_of_conj_eq_one h1
    rw [hcen, Subgroup.mem_bot] at h2
    calc gb * z * gb⁻¹ * z⁻¹ = v ^ j * ((v ^ j)⁻¹ * (gb * z * gb⁻¹ * z⁻¹)) := by group
      _ = v ^ j := by rw [h2, mul_one]
  have hgbzv : gb * z * gb⁻¹ * z⁻¹ ∈ Subgroup.zpowers v := by
    rw [hcomm']
    exact Subgroup.zpow_mem_zpowers v j
  have hgbz : gb * z ≠ z * gb := by
    intro h1
    have h2 : v ^ j = 1 := by rw [← hcomm', h1]; group
    have h3 : π ⟨d ^ j, Y.zpow_mem hdY j⟩ = 1 := by
      rw [← h2, hv, ← map_zpow]
      rfl
    have h4 := hdpow j h3
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have : g * c * g⁻¹ = c := by
      calc g * c * g⁻¹ = g * c * g⁻¹ * c⁻¹ * c := by group
        _ = c := by rw [← hj, h4, one_mul]
    rw [this]
    exact Subgroup.mem_zpowers c
  exact ⟨z, hz, hz3, hJ, hJT, hgbv, hgbzv, hgbz⟩

end Item1117Res3Proof

end CFSG.RankThree.PartTwo.Sec11
