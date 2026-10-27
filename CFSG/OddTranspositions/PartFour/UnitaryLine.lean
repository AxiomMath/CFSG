module

public import CFSG.OddTranspositions.PartFour.SeventeenFourSp
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.OddTranspositions.PartFour.UnitaryClass
import CFSG.OddTranspositions.PartFour.SpPlaneSL2
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsH

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.Open Matrix
open CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.WeakClosure81

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d f : ℕ}

private def unitaryLine_i0 (hd : 4 ≤ d) : Fin d := ⟨0, by omega⟩

private def unitaryLine_i1 (hd : 4 ≤ d) : Fin d := ⟨1, by omega⟩

private def unitaryLine_i2 (hd : 4 ≤ d) : Fin d := ⟨2, by omega⟩

private def unitaryLine_i3 (hd : 4 ≤ d) : Fin d := ⟨3, by omega⟩

private def unitaryLine_e (hd : 4 ≤ d) : Fin d → K :=
  Pi.single (unitaryLine_i0 hd) 1 + Pi.single (unitaryLine_i1 hd) 1

private def unitaryLine_e' (hd : 4 ≤ d) : Fin d → K :=
  Pi.single (unitaryLine_i2 hd) 1 + Pi.single (unitaryLine_i3 hd) 1

private theorem unitaryLine_i_ne (hd : 4 ≤ d) :
    unitaryLine_i0 hd ≠ unitaryLine_i1 hd ∧ unitaryLine_i0 hd ≠ unitaryLine_i2 hd ∧
      unitaryLine_i0 hd ≠ unitaryLine_i3 hd ∧ unitaryLine_i1 hd ≠ unitaryLine_i2 hd ∧
      unitaryLine_i1 hd ≠ unitaryLine_i3 hd ∧ unitaryLine_i2 hd ≠ unitaryLine_i3 hd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have h' := congrArg Fin.val h <;>
    simp [unitaryLine_i0, unitaryLine_i1, unitaryLine_i2, unitaryLine_i3] at h'

private noncomputable abbrev unitaryLine_class (hK : Nat.card K = (2 ^ f) ^ 2) :
    Set (StatedProj (StatedSU d (2 ^ f) K)) :=
  {y | ∃ c : Fin d → K, c ≠ 0 ∧ herm (unitaryInvolution K 2 f) c c = 0 ∧
    y = kFactsSuProjTv hK d c 1}

private noncomputable abbrev unitaryLine_v (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    StatedProj (StatedSU d (2 ^ f) K) :=
  kFactsSuProjTv hK d (unitaryLine_e hd) 1

private noncomputable abbrev unitaryLine_w (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    StatedProj (StatedSU d (2 ^ f) K) :=
  kFactsSuProjTv hK d (unitaryLine_e' hd) 1

private abbrev unitaryLine_off (hd : 4 ≤ d) (p : Fin d → K) : Prop :=
  p (unitaryLine_i0 hd) = 0 ∧ p (unitaryLine_i1 hd) = 0 ∧
    p (unitaryLine_i2 hd) = 0 ∧ p (unitaryLine_i3 hd) = 0

private theorem unitaryLine_one_add_sigma_one :
    (1 : K) + unitaryInvolution K 2 f 1 = 0 := by
  rw [map_one, CharTwo.add_self_eq_zero]

private theorem unitaryLine_coord_e (hd : 4 ≤ d) (p : Fin d → K) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e (K := K) hd) p =
      p (unitaryLine_i0 hd) + p (unitaryLine_i1 hd) := by
  simp [unitaryLine_e, herm_add_left, herm_single_left]

private theorem unitaryLine_coord_e' (hd : 4 ≤ d) (p : Fin d → K) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e' (K := K) hd) p =
      p (unitaryLine_i2 hd) + p (unitaryLine_i3 hd) := by
  simp [unitaryLine_e', herm_add_left, herm_single_left]

private theorem unitaryLine_e_isotropic (hd : 4 ≤ d) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e (K := K) hd) (unitaryLine_e hd) = 0 := by
  rw [unitaryLine_coord_e]
  simp [unitaryLine_e, (unitaryLine_i_ne hd).1, Ne.symm (unitaryLine_i_ne hd).1,
    Pi.single_apply, CharTwo.add_self_eq_zero]

private theorem unitaryLine_e'_isotropic (hd : 4 ≤ d) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e' (K := K) hd) (unitaryLine_e' hd) = 0 := by
  rw [unitaryLine_coord_e']
  simp [unitaryLine_e', (unitaryLine_i_ne hd).2.2.2.2.2,
    Ne.symm (unitaryLine_i_ne hd).2.2.2.2.2, Pi.single_apply, CharTwo.add_self_eq_zero]

private theorem unitaryLine_e_orthogonal_e' (hd : 4 ≤ d) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e (K := K) hd) (unitaryLine_e' hd) = 0 := by
  rw [unitaryLine_coord_e]
  simp [unitaryLine_e', (unitaryLine_i_ne hd).2.1, (unitaryLine_i_ne hd).2.2.1,
    (unitaryLine_i_ne hd).2.2.2.1, (unitaryLine_i_ne hd).2.2.2.2.1,
    Ne.symm (unitaryLine_i_ne hd).2.1, Ne.symm (unitaryLine_i_ne hd).2.2.1,
    Ne.symm (unitaryLine_i_ne hd).2.2.2.1, Ne.symm (unitaryLine_i_ne hd).2.2.2.2.1,
    Pi.single_apply]

private theorem unitaryLine_e_ne_zero (hd : 4 ≤ d) :
    unitaryLine_e (K := K) hd ≠ 0 := by
  intro h
  have h' := congrFun h (unitaryLine_i0 hd)
  simp [unitaryLine_e, (unitaryLine_i_ne hd).1, Ne.symm (unitaryLine_i_ne hd).1,
    Pi.single_apply] at h'

private theorem unitaryLine_e'_ne_zero (hd : 4 ≤ d) :
    unitaryLine_e' (K := K) hd ≠ 0 := by
  intro h
  have h' := congrFun h (unitaryLine_i2 hd)
  simp [unitaryLine_e', (unitaryLine_i_ne hd).2.2.2.2.2,
    Ne.symm (unitaryLine_i_ne hd).2.2.2.2.2, Pi.single_apply] at h'

private theorem unitaryLine_e'_not_smul_e (hd : 4 ≤ d) :
    ∀ μ : K, unitaryLine_e' (K := K) hd ≠ μ • unitaryLine_e hd := by
  intro μ h
  have h' := congrFun h (unitaryLine_i2 hd)
  simp [unitaryLine_e', unitaryLine_e, (unitaryLine_i_ne hd).2.1,
    (unitaryLine_i_ne hd).2.2.2.1, (unitaryLine_i_ne hd).2.2.2.2.2,
    Ne.symm (unitaryLine_i_ne hd).2.2.2.2.2, Pi.single_apply] at h'

private theorem unitaryLine_v_mem (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    unitaryLine_v hK hd ∈ unitaryLine_class hK :=
  ⟨unitaryLine_e hd, unitaryLine_e_ne_zero hd, unitaryLine_e_isotropic hd, rfl⟩

private theorem unitaryLine_w_mem (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    unitaryLine_w hK hd ∈ unitaryLine_class hK :=
  ⟨unitaryLine_e' hd, unitaryLine_e'_ne_zero hd, unitaryLine_e'_isotropic hd, rfl⟩

private theorem unitaryLine_commute_v_w (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    Commute (unitaryLine_v hK hd) (unitaryLine_w hK hd) := by
  refine (commute_kFactsSuProjTv_iff hK (unitaryLine_e_ne_zero hd)
    (unitaryLine_e_isotropic hd) (unitaryLine_e'_ne_zero hd) (unitaryLine_e'_isotropic hd)
    one_ne_zero unitaryLine_one_add_sigma_one one_ne_zero
    unitaryLine_one_add_sigma_one).mpr ?_
  exact unitaryLine_e_orthogonal_e' hd

private theorem unitaryLine_perp_ne (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    perpMem (unitaryLine_class hK) (unitaryLine_v hK hd) ≠
      perpMem (unitaryLine_class hK) (unitaryLine_w hK hd) := by
  intro h
  have h' := (perpMem_setOf_kFactsSuProjTv_eq_iff hK (unitaryLine_e_ne_zero hd)
    (unitaryLine_e_isotropic hd) (unitaryLine_e'_ne_zero hd)
    (unitaryLine_e'_isotropic hd)).mp h
  obtain ⟨μ, hμ⟩ := h'
  exact unitaryLine_e'_not_smul_e hd μ hμ

private theorem unitaryLine_herm_e_of_off (hd : 4 ≤ d) {p : Fin d → K}
    (hp : unitaryLine_off hd p) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e (K := K) hd) p = 0 := by
  rw [unitaryLine_coord_e, hp.1, hp.2.1, add_zero]

private theorem unitaryLine_herm_e'_of_off (hd : 4 ≤ d) {p : Fin d → K}
    (hp : unitaryLine_off hd p) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e' (K := K) hd) p = 0 := by
  rw [unitaryLine_coord_e', hp.2.2.1, hp.2.2.2, add_zero]

private theorem unitaryLine_herm_off_e (hd : 4 ≤ d) {p : Fin d → K}
    (hp : unitaryLine_off hd p) :
    herm (unitaryInvolution K 2 f) p (unitaryLine_e (K := K) hd) = 0 := by
  simp [unitaryLine_e, herm_add_right, herm_single_right, hp.1, hp.2.1]

private theorem unitaryLine_herm_off_e' (hd : 4 ≤ d) {p : Fin d → K}
    (hp : unitaryLine_off hd p) :
    herm (unitaryInvolution K 2 f) p (unitaryLine_e' (K := K) hd) = 0 := by
  simp [unitaryLine_e', herm_add_right, herm_single_right, hp.2.2.1, hp.2.2.2]

private theorem unitaryLine_off_add (hd : 4 ≤ d) {p q : Fin d → K}
    (hp : unitaryLine_off hd p) (hq : unitaryLine_off hd q) :
    unitaryLine_off hd (p + q) := by
  obtain ⟨p0, p1, p2, p3⟩ := hp
  obtain ⟨q0, q1, q2, q3⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [p0, p1, p2, p3, q0, q1, q2, q3]

private theorem unitaryLine_off_smul (hd : 4 ≤ d) {p : Fin d → K}
    (hp : unitaryLine_off hd p) (t : K) : unitaryLine_off hd (t • p) := by
  obtain ⟨p0, p1, p2, p3⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [p0, p1, p2, p3]

private def unitaryLine_g0 (hd : 4 ≤ d) (g : Fin d → K) : Fin d → K :=
  g - g (unitaryLine_i0 hd) • Pi.single (unitaryLine_i0 hd) 1 -
    g (unitaryLine_i1 hd) • Pi.single (unitaryLine_i1 hd) 1 -
    g (unitaryLine_i2 hd) • Pi.single (unitaryLine_i2 hd) 1 -
    g (unitaryLine_i3 hd) • Pi.single (unitaryLine_i3 hd) 1

private theorem unitaryLine_g0_off (hd : 4 ≤ d) (g : Fin d → K) :
    unitaryLine_off hd (unitaryLine_g0 hd g) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := unitaryLine_i_ne hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [unitaryLine_off, unitaryLine_g0, Pi.single_apply, h01, h02, h03, h12, h13, h23,
      Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]

private theorem unitaryLine_herm_z_g0 (hd : 4 ≤ d) {z : Fin d → K}
    (hz : unitaryLine_off hd z) (g : Fin d → K) :
    herm (unitaryInvolution K 2 f) z (unitaryLine_g0 (K := K) hd g) =
      herm (unitaryInvolution K 2 f) z g := by
  obtain ⟨z0, z1, z2, z3⟩ := hz
  simp [unitaryLine_g0, herm_sub_right, herm_smul_right, herm_single_right, z0, z1, z2, z3]

private def unitaryLine_z (hd : 4 ≤ d) (c : Fin d → K) : Fin d → K :=
  c - c (unitaryLine_i0 hd) • unitaryLine_e hd - c (unitaryLine_i2 hd) • unitaryLine_e' hd

private theorem unitaryLine_z_off (hd : 4 ≤ d) {c : Fin d → K}
    (hc01 : c (unitaryLine_i0 hd) = c (unitaryLine_i1 hd))
    (hc23 : c (unitaryLine_i2 hd) = c (unitaryLine_i3 hd)) :
    unitaryLine_off hd (unitaryLine_z (K := K) hd c) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := unitaryLine_i_ne hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [unitaryLine_z, unitaryLine_e, unitaryLine_e', Pi.single_apply, h01, h02, h03,
      Ne.symm h01, Ne.symm h02, Ne.symm h03]
  · simp [unitaryLine_z, unitaryLine_e, unitaryLine_e', Pi.single_apply, hc01.symm, h01, h02,
      h03, h12, h13, Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13]
  · simp [unitaryLine_z, unitaryLine_e, unitaryLine_e', Pi.single_apply, h02, h03, h12, h13,
      h23, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
  · simp [unitaryLine_z, unitaryLine_e, unitaryLine_e', Pi.single_apply, hc23.symm, h03, h13,
      h23, Ne.symm h03, Ne.symm h13, Ne.symm h23]

private theorem unitaryLine_z_isotropic (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {c : Fin d → K} (hc : herm (unitaryInvolution K 2 f) c c = 0)
    (hec : herm (unitaryInvolution K 2 f) (unitaryLine_e hd) c = 0)
    (he'c : herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) c = 0) :
    herm (unitaryInvolution K 2 f) (unitaryLine_z (K := K) hd c)
      (unitaryLine_z (K := K) hd c) = 0 := by
  have hinv := unitaryInvolution_involutive (p := 2) (f := f) hK
  have hce : herm (unitaryInvolution K 2 f) c (unitaryLine_e hd) = 0 :=
    herm_eq_zero_comm _ hinv hec
  have hce' : herm (unitaryInvolution K 2 f) c (unitaryLine_e' hd) = 0 :=
    herm_eq_zero_comm _ hinv he'c
  have hee' := unitaryLine_e_orthogonal_e' (K := K) (f := f) hd
  have he'e : herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) (unitaryLine_e hd) = 0 :=
    herm_eq_zero_comm _ hinv hee'
  have hz : unitaryLine_z (K := K) hd c =
      c + c (unitaryLine_i0 hd) • unitaryLine_e hd + c (unitaryLine_i2 hd) • unitaryLine_e' hd := by
    rw [unitaryLine_z, sub_eq_add_neg, sub_eq_add_neg, ← neg_smul, ← neg_smul,
      CharTwo.neg_eq, CharTwo.neg_eq]
  rw [hz]
  simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hc,
    unitaryLine_e_isotropic hd, unitaryLine_e'_isotropic hd, hee', he'e, hce, hce', hec, he'c]

private theorem unitaryLine_herm_center_of_mem_line (hK : Nat.card K = (2 ^ f) ^ 2)
    (hd : 4 ≤ d) {c : Fin d → K} (hc0 : c ≠ 0)
    (hc : herm (unitaryInvolution K 2 f) c c = 0)
    {x : StatedProj (StatedSU d (2 ^ f) K)}
    (hx : x ∈ lineMem (unitaryLine_class hK) (unitaryLine_v hK hd) (unitaryLine_w hK hd))
    (hxeq : x = kFactsSuProjTv hK d c 1) :
    herm (unitaryInvolution K 2 f) (unitaryLine_e hd) c = 0 ∧
      herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) c = 0 := by
  have hvw := unitaryLine_commute_v_w hK hd
  have hv_in : unitaryLine_v hK hd ∈
      perpMem (unitaryLine_class hK) (unitaryLine_v hK hd) ∩
        perpMem (unitaryLine_class hK) (unitaryLine_w hK hd) :=
    ⟨mem_perpMem_self (unitaryLine_v_mem hK hd),
      mem_perpMem.mpr ⟨unitaryLine_v_mem hK hd, hvw⟩⟩
  have hec : herm (unitaryInvolution K 2 f) (unitaryLine_e hd) c = 0 := by
    have hcomm : Commute (unitaryLine_v hK hd) x := (hx.2 hv_in).2
    rw [hxeq] at hcomm
    exact (commute_kFactsSuProjTv_iff hK (unitaryLine_e_ne_zero hd)
      (unitaryLine_e_isotropic hd) hc0 hc one_ne_zero unitaryLine_one_add_sigma_one
      one_ne_zero unitaryLine_one_add_sigma_one).mp hcomm
  have hw_in : unitaryLine_w hK hd ∈
      perpMem (unitaryLine_class hK) (unitaryLine_v hK hd) ∩
        perpMem (unitaryLine_class hK) (unitaryLine_w hK hd) :=
    ⟨mem_perpMem.mpr ⟨unitaryLine_w_mem hK hd, hvw.symm⟩,
      mem_perpMem_self (unitaryLine_w_mem hK hd)⟩
  have he'c : herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) c = 0 := by
    have hcomm : Commute (unitaryLine_w hK hd) x := (hx.2 hw_in).2
    rw [hxeq] at hcomm
    exact (commute_kFactsSuProjTv_iff hK (unitaryLine_e'_ne_zero hd)
      (unitaryLine_e'_isotropic hd) hc0 hc one_ne_zero unitaryLine_one_add_sigma_one
      one_ne_zero unitaryLine_one_add_sigma_one).mp hcomm
  exact ⟨hec, he'c⟩

private theorem unitaryLine_exists_off_isotropic (hK : Nat.card K = (2 ^ f) ^ 2)
    (hd : 4 ≤ d) {c : Fin d → K} (hc : herm (unitaryInvolution K 2 f) c c = 0)
    (hec : herm (unitaryInvolution K 2 f) (unitaryLine_e hd) c = 0)
    (he'c : herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) c = 0)
    (hz0 : unitaryLine_z (K := K) hd c ≠ 0) :
    ∃ p : Fin d → K, unitaryLine_off hd p ∧
      herm (unitaryInvolution K 2 f) p p = 0 ∧
      herm (unitaryInvolution K 2 f) c p = 1 := by
  have hc01 : c (unitaryLine_i0 hd) = c (unitaryLine_i1 hd) := by
    have hsum : c (unitaryLine_i0 hd) + c (unitaryLine_i1 hd) = 0 := by
      simpa [unitaryLine_coord_e] using hec
    have hneg := eq_neg_of_add_eq_zero_left hsum
    rwa [CharTwo.neg_eq] at hneg
  have hc23 : c (unitaryLine_i2 hd) = c (unitaryLine_i3 hd) := by
    have hsum : c (unitaryLine_i2 hd) + c (unitaryLine_i3 hd) = 0 := by
      simpa [unitaryLine_coord_e'] using he'c
    have hneg := eq_neg_of_add_eq_zero_left hsum
    rwa [CharTwo.neg_eq] at hneg
  let z := unitaryLine_z (K := K) hd c
  have hzoff : unitaryLine_off hd z := unitaryLine_z_off hd hc01 hc23
  have hziso : herm (unitaryInvolution K 2 f) z z = 0 :=
    unitaryLine_z_isotropic hK hd hc hec he'c
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨g, hgg, hzg⟩ := exists_partner hσ hz0 hziso
  let g0 := unitaryLine_g0 (K := K) hd g
  have hg0off : unitaryLine_off hd g0 := unitaryLine_g0_off hd g
  have hzg0 : herm (unitaryInvolution K 2 f) z g0 = 1 := by
    change herm (unitaryInvolution K 2 f) z (unitaryLine_g0 (K := K) hd g) = 1
    rw [unitaryLine_herm_z_g0 hd hzoff g, hzg]
  obtain ⟨t, ht⟩ := exists_isotropize hσ hziso hzg0
  let p := g0 + t • z
  have hp_off : unitaryLine_off hd p :=
    unitaryLine_off_add hd hg0off (unitaryLine_off_smul hd hzoff t)
  have hzp : herm (unitaryInvolution K 2 f) z p = 1 := by
    change herm (unitaryInvolution K 2 f) z (g0 + t • z) = 1
    rw [herm_add_right, herm_smul_right, hzg0, hziso, mul_zero, add_zero]
  have hz_eq : z = c + c (unitaryLine_i0 hd) • unitaryLine_e hd +
      c (unitaryLine_i2 hd) • unitaryLine_e' hd := by
    dsimp only [z]
    rw [unitaryLine_z, sub_eq_add_neg, sub_eq_add_neg, ← neg_smul, ← neg_smul,
      CharTwo.neg_eq, CharTwo.neg_eq]
  have hcp : herm (unitaryInvolution K 2 f) c p = 1 := by
    rw [hz_eq] at hzp
    simpa [unitaryLine_herm_e_of_off hd hp_off, unitaryLine_herm_e'_of_off hd hp_off] using hzp
  exact ⟨p, hp_off, ht, hcp⟩

private theorem unitaryLine_z_eq_zero_of_mem_line (hK : Nat.card K = (2 ^ f) ^ 2)
    (hd : 4 ≤ d) {c : Fin d → K} (hc0 : c ≠ 0)
    (hc : herm (unitaryInvolution K 2 f) c c = 0)
    (hec : herm (unitaryInvolution K 2 f) (unitaryLine_e hd) c = 0)
    (he'c : herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) c = 0)
    {x : StatedProj (StatedSU d (2 ^ f) K)}
    (hx : x ∈ lineMem (unitaryLine_class hK) (unitaryLine_v hK hd) (unitaryLine_w hK hd))
    (hxeq : x = kFactsSuProjTv hK d c 1) :
    unitaryLine_z (K := K) hd c = 0 := by
  by_contra hz0
  obtain ⟨p, hp_off, hpp, hcp⟩ :=
    unitaryLine_exists_off_isotropic hK hd hc hec he'c hz0
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hcp
    exact one_ne_zero hcp.symm
  let y := kFactsSuProjTv hK d p 1
  have hyS : y ∈ unitaryLine_class hK := ⟨p, hp0, hpp, rfl⟩
  have hyv : y ∈ perpMem (unitaryLine_class hK) (unitaryLine_v hK hd) := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    refine (commute_kFactsSuProjTv_iff hK hp0 hpp (unitaryLine_e_ne_zero hd)
      (unitaryLine_e_isotropic hd) one_ne_zero unitaryLine_one_add_sigma_one
      one_ne_zero unitaryLine_one_add_sigma_one).mpr ?_
    exact unitaryLine_herm_off_e hd hp_off
  have hyw : y ∈ perpMem (unitaryLine_class hK) (unitaryLine_w hK hd) := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    refine (commute_kFactsSuProjTv_iff hK hp0 hpp (unitaryLine_e'_ne_zero hd)
      (unitaryLine_e'_isotropic hd) one_ne_zero unitaryLine_one_add_sigma_one
      one_ne_zero unitaryLine_one_add_sigma_one).mpr ?_
    exact unitaryLine_herm_off_e' hd hp_off
  have hcomm_yx : Commute y x := (hx.2 ⟨hyv, hyw⟩).2
  rw [hxeq] at hcomm_yx
  have hpc : herm (unitaryInvolution K 2 f) p c = 0 :=
    (commute_kFactsSuProjTv_iff hK hp0 hpp hc0 hc one_ne_zero
      unitaryLine_one_add_sigma_one one_ne_zero unitaryLine_one_add_sigma_one).mp hcomm_yx
  have hcp0 : herm (unitaryInvolution K 2 f) c p = 0 :=
    herm_eq_zero_comm _ (unitaryInvolution_involutive (p := 2) (f := f) hK) hpc
  rw [hcp] at hcp0
  exact one_ne_zero hcp0

private theorem unitaryLine_center_eq_span (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {c : Fin d → K} (hc0 : c ≠ 0)
    (hc : herm (unitaryInvolution K 2 f) c c = 0)
    (hec : herm (unitaryInvolution K 2 f) (unitaryLine_e hd) c = 0)
    (he'c : herm (unitaryInvolution K 2 f) (unitaryLine_e' hd) c = 0)
    {x : StatedProj (StatedSU d (2 ^ f) K)}
    (hx : x ∈ lineMem (unitaryLine_class hK) (unitaryLine_v hK hd) (unitaryLine_w hK hd))
    (hxeq : x = kFactsSuProjTv hK d c 1) :
    ∃ α β : K, c = α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd := by
  have hz0 := unitaryLine_z_eq_zero_of_mem_line hK hd hc0 hc hec he'c hx hxeq
  refine ⟨c (unitaryLine_i0 hd), c (unitaryLine_i2 hd), ?_⟩
  have h := hz0
  rw [unitaryLine_z] at h
  linear_combination h

private theorem unitaryLine_mem_span (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {x : StatedProj (StatedSU d (2 ^ f) K)}
    (hx : x ∈ lineMem (unitaryLine_class hK) (unitaryLine_v hK hd) (unitaryLine_w hK hd)) :
    ∃ α β : K, (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd ≠ 0) ∧
      herm (unitaryInvolution K 2 f) (α • unitaryLine_e (K := K) hd +
          β • unitaryLine_e' (K := K) hd)
        (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) = 0 ∧
      x = kFactsSuProjTv hK d (α • unitaryLine_e (K := K) hd +
        β • unitaryLine_e' (K := K) hd) 1 := by
  obtain ⟨c, hc0, hc, hxeq⟩ := hx.1
  obtain ⟨hec, he'c⟩ := unitaryLine_herm_center_of_mem_line hK hd hc0 hc hx hxeq
  obtain ⟨α, β, hcz⟩ := unitaryLine_center_eq_span hK hd hc0 hc hec he'c hx hxeq
  refine ⟨α, β, ?_, ?_, ?_⟩
  · rw [← hcz]
    exact hc0
  · rw [← hcz]
    exact hc
  · rw [hxeq, hcz]

private noncomputable def unitaryLine_A (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    Set (Set (StatedProj (StatedSU d (2 ^ f) K))) :=
  insert (perpMem (unitaryLine_class hK)
    (kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) 1))
    (Set.range fun μ : K => perpMem (unitaryLine_class hK)
      (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
        unitaryLine_e' (K := K) hd) 1))

private theorem unitaryLine_P_mem_insert (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {α : K} (hαe0 : α • unitaryLine_e (K := K) hd ≠ 0)
    (hαeiso : herm (unitaryInvolution K 2 f) (α • unitaryLine_e (K := K) hd)
      (α • unitaryLine_e (K := K) hd) = 0) :
    perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d (α • unitaryLine_e (K := K) hd) 1) ∈
      unitaryLine_A hK hd := by
  have hiff := (perpMem_setOf_kFactsSuProjTv_eq_iff hK (unitaryLine_e_ne_zero hd)
    (unitaryLine_e_isotropic hd) hαe0 hαeiso).mpr ⟨α, rfl⟩
  rw [show perpMem (unitaryLine_class hK)
      (kFactsSuProjTv hK d (α • unitaryLine_e (K := K) hd) 1) =
      perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) 1) from hiff.symm]
  exact Set.mem_insert _ _

private theorem unitaryLine_P_mem_range (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {α β : K} (hβ : β ≠ 0)
    (hc0 : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd ≠ 0)
    (hc : herm (unitaryInvolution K 2 f)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) = 0) :
    perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d (α • unitaryLine_e (K := K) hd +
          β • unitaryLine_e' (K := K) hd) 1) ∈
      insert (perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) 1))
        (Set.range fun μ : K => perpMem (unitaryLine_class hK)
          (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
            unitaryLine_e' (K := K) hd) 1)) := by
  have hc' : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd =
      β • ((β⁻¹ * α) • unitaryLine_e (K := K) hd + unitaryLine_e' (K := K) hd) := by
    rw [smul_add, ← mul_smul, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
  have hμe0 : (β⁻¹ * α) • unitaryLine_e (K := K) hd +
      unitaryLine_e' (K := K) hd ≠ 0 := by
    intro h0
    have hcoord := congrFun h0 (unitaryLine_i2 hd)
    simp [unitaryLine_e, unitaryLine_e', Pi.single_apply,
      (unitaryLine_i_ne hd).2.1, (unitaryLine_i_ne hd).2.2.2.1,
      (unitaryLine_i_ne hd).2.2.2.2.2, Ne.symm (unitaryLine_i_ne hd).2.2.2.2.2] at hcoord
  have hμeiso : herm (unitaryInvolution K 2 f)
      ((β⁻¹ * α) • unitaryLine_e (K := K) hd + unitaryLine_e' (K := K) hd)
      ((β⁻¹ * α) • unitaryLine_e (K := K) hd + unitaryLine_e' (K := K) hd) = 0 := by
    have hinv := unitaryInvolution_involutive (p := 2) (f := f) hK
    have he'e : herm (unitaryInvolution K 2 f) (unitaryLine_e' (K := K) hd)
        (unitaryLine_e (K := K) hd) = 0 :=
      herm_eq_zero_comm _ hinv (unitaryLine_e_orthogonal_e' (K := K) (f := f) hd)
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
      unitaryLine_e_isotropic hd, unitaryLine_e'_isotropic hd,
      unitaryLine_e_orthogonal_e' (K := K) (f := f) hd, he'e]
  have hPeq : perpMem (unitaryLine_class hK)
      (kFactsSuProjTv hK d (α • unitaryLine_e (K := K) hd +
        β • unitaryLine_e' (K := K) hd) 1) =
      perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d ((β⁻¹ * α) • unitaryLine_e (K := K) hd +
          unitaryLine_e' (K := K) hd) 1) := by
    refine (perpMem_setOf_kFactsSuProjTv_eq_iff hK hc0 hc hμe0 hμeiso).mpr ?_
    refine ⟨β⁻¹, ?_⟩
    rw [hc', smul_smul, inv_mul_cancel₀ hβ, one_smul]
  rw [hPeq]
  exact Set.mem_insert_of_mem _ ⟨β⁻¹ * α, rfl⟩

private theorem unitaryLine_image_subset (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    perpMem (unitaryLine_class hK) '' lineMem (unitaryLine_class hK)
      (unitaryLine_v hK hd) (unitaryLine_w hK hd) ⊆ unitaryLine_A hK hd := by
  rintro _ ⟨x, hxline, rfl⟩
  obtain ⟨α, β, hc0, hc, hx⟩ := unitaryLine_mem_span hK hd hxline
  rw [hx]
  by_cases hβ : β = 0
  · have hαe0 : α • unitaryLine_e (K := K) hd ≠ 0 := by
      intro h0
      apply hc0
      rw [hβ, zero_smul, add_zero, h0]
    have hαeiso : herm (unitaryInvolution K 2 f) (α • unitaryLine_e (K := K) hd)
        (α • unitaryLine_e (K := K) hd) = 0 := by
      rw [herm_smul_left, herm_smul_right, unitaryLine_e_isotropic hd, mul_zero, mul_zero]
    rw [hβ, zero_smul, add_zero]
    exact unitaryLine_P_mem_insert hK hd hαe0 hαeiso
  · exact unitaryLine_P_mem_range hK hd hβ hc0 hc

private theorem unitaryLine_ncard_le (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    (perpMem (unitaryLine_class hK) '' lineMem (unitaryLine_class hK)
      (unitaryLine_v hK hd) (unitaryLine_w hK hd)).ncard ≤ (2 ^ f) ^ 2 + 1 := by
  have hsub := unitaryLine_image_subset hK hd
  have hrange : (Set.range fun μ : K => perpMem (unitaryLine_class hK)
      (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
        unitaryLine_e' (K := K) hd) 1)).ncard ≤ Nat.card K := by
    rw [← Set.image_univ]
    calc
      ((fun μ : K => perpMem (unitaryLine_class hK)
          (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
            unitaryLine_e' (K := K) hd) 1)) '' (Set.univ : Set K)).ncard ≤
          (Set.univ : Set K).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card K := Set.ncard_univ K
  have hA : (unitaryLine_A hK hd).ncard ≤ Nat.card K + 1 := by
    change (insert (perpMem (unitaryLine_class hK)
      (kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) 1))
      (Set.range fun μ : K => perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
          unitaryLine_e' (K := K) hd) 1))).ncard ≤ Nat.card K + 1
    calc
      (insert (perpMem (unitaryLine_class hK)
        (kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) 1))
        (Set.range fun μ : K => perpMem (unitaryLine_class hK)
          (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
            unitaryLine_e' (K := K) hd) 1))).ncard ≤
          (Set.range fun μ : K => perpMem (unitaryLine_class hK)
            (kFactsSuProjTv hK d (μ • unitaryLine_e (K := K) hd +
              unitaryLine_e' (K := K) hd) 1)).ncard + 1 :=
        Set.ncard_insert_le _ _
      _ ≤ Nat.card K + 1 := Nat.add_le_add_right hrange 1
  calc
    (perpMem (unitaryLine_class hK) '' lineMem (unitaryLine_class hK)
        (unitaryLine_v hK hd) (unitaryLine_w hK hd)).ncard ≤
        (unitaryLine_A hK hd).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card K + 1 := hA
    _ = (2 ^ f) ^ 2 + 1 := by rw [hK]

private noncomputable def unitaryLine_diag (ζ : Kˣ) (hd : 4 ≤ d) : Fin d → K :=
  fun i => if i = unitaryLine_i0 hd ∨ i = unitaryLine_i1 hd then ((ζ : K)⁻¹)
    else if i = unitaryLine_i2 hd ∨ i = unitaryLine_i3 hd then (ζ : K) else 1

private noncomputable def unitaryLine_D (ζ : Kˣ) (hd : 4 ≤ d) :
    Matrix (Fin d) (Fin d) K :=
  Matrix.diagonal (unitaryLine_diag (K := K) ζ hd)

private theorem unitaryLine_diag_norm {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) (i : Fin d) :
    unitaryInvolution K 2 f (unitaryLine_diag (K := K) ζ hd i) *
      unitaryLine_diag (K := K) ζ hd i = 1 := by
  by_cases h0 : i = unitaryLine_i0 hd ∨ i = unitaryLine_i1 hd
  · rw [unitaryLine_diag, if_pos h0, map_inv₀]
    rw [← mul_inv, hζ, inv_one]
  · rw [unitaryLine_diag, if_neg h0]
    by_cases h2 : i = unitaryLine_i2 hd ∨ i = unitaryLine_i3 hd
    · rw [if_pos h2]
      exact hζ
    · rw [if_neg h2]
      simp

private theorem unitaryLine_det_D (ζ : Kˣ) (hd : 4 ≤ d) :
    (unitaryLine_D (K := K) ζ hd).det = 1 := by
  rw [unitaryLine_D, Matrix.det_diagonal]
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := unitaryLine_i_ne hd
  have hprod : (∏ i : Fin d, unitaryLine_diag (K := K) ζ hd i) =
      unitaryLine_diag (K := K) ζ hd (unitaryLine_i0 hd) *
        unitaryLine_diag (K := K) ζ hd (unitaryLine_i1 hd) *
        unitaryLine_diag (K := K) ζ hd (unitaryLine_i2 hd) *
        unitaryLine_diag (K := K) ζ hd (unitaryLine_i3 hd) := by
    rw [← Finset.prod_subset
      (s₁ := ({unitaryLine_i0 hd, unitaryLine_i1 hd, unitaryLine_i2 hd,
        unitaryLine_i3 hd} : Finset (Fin d))) (s₂ := Finset.univ) (by simp)]
    · simp [Finset.prod_insert, h01, h02, h03, h12, h13, h23]
      ring
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [unitaryLine_diag, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  rw [hprod]
  have hd0 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i0 hd) = (ζ : K)⁻¹ := by
    simp [unitaryLine_diag]
  have hd1 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i1 hd) = (ζ : K)⁻¹ := by
    simp [unitaryLine_diag, Ne.symm h01]
  have hd2 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i2 hd) = (ζ : K) := by
    simp [unitaryLine_diag, Ne.symm h02, Ne.symm h12]
  have hd3 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i3 hd) = (ζ : K) := by
    simp [unitaryLine_diag, Ne.symm h03, Ne.symm h13, Ne.symm h23]
  rw [hd0, hd1, hd2, hd3]
  field_simp [ζ.ne_zero]

private theorem unitaryLine_D_isometry {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    ∀ x y : Fin d → K,
      herm (unitaryInvolution K 2 f) (unitaryLine_D (K := K) ζ hd *ᵥ x)
        (unitaryLine_D (K := K) ζ hd *ᵥ y) =
      herm (unitaryInvolution K 2 f) x y := by
  intro x y
  rw [herm_def, herm_def]
  simp only [unitaryLine_D, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdi := unitaryLine_diag_norm hζ hd i
  calc
    unitaryInvolution K 2 f (unitaryLine_diag (K := K) ζ hd i * x i) *
        (unitaryLine_diag (K := K) ζ hd i * y i) =
      (unitaryInvolution K 2 f (unitaryLine_diag (K := K) ζ hd i) *
        unitaryLine_diag (K := K) ζ hd i) *
        (unitaryInvolution K 2 f (x i) * y i) := by
        rw [map_mul]
        ring
    _ = unitaryInvolution K 2 f (x i) * y i := by rw [hdi, one_mul]

private noncomputable def unitaryLine_Dsu {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    SUid (unitaryInvolution K 2 f) d :=
  mkSU (unitaryInvolution K 2 f) (unitaryLine_D (K := K) ζ hd)
    (unitaryLine_det_D ζ hd) (unitaryLine_D_isometry hζ hd)

private theorem unitaryLine_Dsu_smul {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d)
    (v : Fin d → K) :
    unitaryLine_Dsu hζ hd • v = unitaryLine_D (K := K) ζ hd *ᵥ v :=
  rfl

private theorem unitaryLine_Dsu_pow_smul {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d)
    (k : ℕ) (v : Fin d → K) :
    (unitaryLine_Dsu (K := K) (f := f) (d := d) hζ hd ^ k) • v =
      (unitaryLine_D (K := K) ζ hd ^ k) *ᵥ v := by
  rw [smul_def]
  congr 1

private theorem unitaryLine_D_pow_mulVec_single (ζ : Kˣ) (hd : 4 ≤ d) (k : ℕ)
    (i : Fin d) :
    (unitaryLine_D (K := K) ζ hd ^ k) *ᵥ Pi.single i 1 =
      (unitaryLine_diag (K := K) ζ hd i) ^ k • Pi.single i 1 := by
  rw [unitaryLine_D, Matrix.diagonal_pow]
  funext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h, Pi.smul_apply]

private theorem unitaryLine_D_pow_mulVec_e (ζ : Kˣ) (hd : 4 ≤ d) (k : ℕ) :
    (unitaryLine_D (K := K) ζ hd ^ k) *ᵥ unitaryLine_e (K := K) hd =
      (((ζ : K)⁻¹) ^ k) • unitaryLine_e (K := K) hd := by
  rw [unitaryLine_e, Matrix.mulVec_add, unitaryLine_D_pow_mulVec_single,
    unitaryLine_D_pow_mulVec_single]
  have h0 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i0 hd) = (ζ : K)⁻¹ := by
    simp [unitaryLine_diag]
  have h1 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i1 hd) = (ζ : K)⁻¹ := by
    simp [unitaryLine_diag, Ne.symm (unitaryLine_i_ne hd).1]
  rw [h0, h1, ← smul_add]

private theorem unitaryLine_D_pow_mulVec_e' (ζ : Kˣ) (hd : 4 ≤ d) (k : ℕ) :
    (unitaryLine_D (K := K) ζ hd ^ k) *ᵥ unitaryLine_e' (K := K) hd =
      ((ζ : K) ^ k) • unitaryLine_e' (K := K) hd := by
  rw [unitaryLine_e', Matrix.mulVec_add, unitaryLine_D_pow_mulVec_single,
    unitaryLine_D_pow_mulVec_single]
  have h2 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i2 hd) = (ζ : K) := by
    simp [unitaryLine_diag, Ne.symm (unitaryLine_i_ne hd).2.1,
      Ne.symm (unitaryLine_i_ne hd).2.2.2.1]
  have h3 : unitaryLine_diag (K := K) ζ hd (unitaryLine_i3 hd) = (ζ : K) := by
    simp [unitaryLine_diag, Ne.symm (unitaryLine_i_ne hd).2.2.1,
      Ne.symm (unitaryLine_i_ne hd).2.2.2.2.1,
      Ne.symm (unitaryLine_i_ne hd).2.2.2.2.2]
  rw [h2, h3, ← smul_add]

private theorem unitaryLine_D_pow_mulVec_add (ζ : Kˣ) (hd : 4 ≤ d) (k : ℕ) (α β : K) :
    (unitaryLine_D (K := K) ζ hd ^ k) *ᵥ
        (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) =
      ((((ζ : K)⁻¹) ^ k * α) • unitaryLine_e (K := K) hd +
        (((ζ : K) ^ k * β) • unitaryLine_e' (K := K) hd)) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    unitaryLine_D_pow_mulVec_e, unitaryLine_D_pow_mulVec_e', smul_smul, smul_smul]
  congr 2 <;> ring

private noncomputable abbrev unitaryLine_g (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    StatedProj (StatedSU d (2 ^ f) K) :=
  kFactsSuProj hK d (unitaryLine_Dsu hζ hd)

private theorem unitaryLine_odd_two_pow_add_one (hK : Nat.card K = (2 ^ f) ^ 2) :
    Odd (2 ^ f + 1) := by
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_pow] at hK
    omega
  exact (Nat.even_pow.mpr ⟨even_two, hf⟩).add_one

private theorem unitaryLine_diag_pow_eq_one {ζ : Kˣ}
    (hζord : orderOf ζ = 2 ^ f + 1) (hd : 4 ≤ d) (i : Fin d) :
    unitaryLine_diag (K := K) ζ hd i ^ (2 ^ f + 1) = 1 := by
  have hζpow : (ζ : K) ^ (2 ^ f + 1) = 1 := by
    have h : (ζ : Kˣ) ^ (2 ^ f + 1) = 1 := by
      rw [← hζord, pow_orderOf_eq_one]
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  by_cases h0 : i = unitaryLine_i0 hd ∨ i = unitaryLine_i1 hd
  · rw [unitaryLine_diag, if_pos h0, inv_pow, hζpow, inv_one]
  · rw [unitaryLine_diag, if_neg h0]
    by_cases h2 : i = unitaryLine_i2 hd ∨ i = unitaryLine_i3 hd
    · rw [if_pos h2, hζpow]
    · rw [if_neg h2, one_pow]

private theorem unitaryLine_D_pow_eq_one {ζ : Kˣ} (hζord : orderOf ζ = 2 ^ f + 1)
    (hd : 4 ≤ d) :
    unitaryLine_D (K := K) ζ hd ^ (2 ^ f + 1) = 1 := by
  rw [unitaryLine_D, Matrix.diagonal_pow, Matrix.diagonal_eq_one]
  funext i
  exact unitaryLine_diag_pow_eq_one hζord hd i

private theorem unitaryLine_Dsu_pow_eq_one {ζ : Kˣ}
    (hζord : orderOf ζ = 2 ^ f + 1)
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    unitaryLine_Dsu hζ hd ^ (2 ^ f + 1) = 1 := by
  apply ext_smul
  intro v
  rw [unitaryLine_Dsu_pow_smul, unitaryLine_D_pow_eq_one hζord hd, Matrix.one_mulVec]
  simp

private theorem unitaryLine_D_pow_mul_scalar_apply (ζ : Kˣ) (hd : 4 ≤ d) (n : ℕ)
    (u : Kˣ) (i : Fin d) :
    ((unitaryLine_D (K := K) ζ hd ^ n) * ((u : K) • (1 : Matrix (Fin d) (Fin d) K))) i i =
      (unitaryLine_diag (K := K) ζ hd i) ^ n * (u : K) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [unitaryLine_D, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, Pi.pow_apply]
    ring
  · intro j _ hji
    have hdiag : (unitaryLine_D (K := K) ζ hd ^ n) i j = 0 := by
      rw [unitaryLine_D, Matrix.diagonal_pow]
      exact Matrix.diagonal_apply_ne _ (i := i) (j := j) (Ne.symm hji)
    rw [hdiag]
    simp
  · intro hi
    simp at hi

private theorem unitaryLine_dvd_orderOf_g (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζord : orderOf ζ = 2 ^ f + 1)
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    2 ^ f + 1 ∣ orderOf (unitaryLine_g hK hζ hd) := by
  set n := orderOf (unitaryLine_g hK hζ hd)
  have hgn : (unitaryLine_g hK hζ hd) ^ n = 1 := pow_orderOf_eq_one _
  rw [unitaryLine_g, ← map_pow, ← map_one (kFactsSuProj hK d)] at hgn
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hK _ _).mp hgn
  have hu' : (1 : Matrix (Fin d) (Fin d) K) =
      (unitaryLine_D (K := K) ζ hd ^ n) * ((u : K) • 1) := by
    have hco : ((↑(unitaryLine_Dsu hζ hd ^ n) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = (unitaryLine_D (K := K) ζ hd) ^ n := rfl
    rw [hco] at hu
    exact hu
  have h00 := congrFun (congrFun hu' (unitaryLine_i0 hd)) (unitaryLine_i0 hd)
  have h22 := congrFun (congrFun hu' (unitaryLine_i2 hd)) (unitaryLine_i2 hd)
  rw [unitaryLine_D_pow_mul_scalar_apply] at h00 h22
  simp only [Matrix.one_apply_eq] at h00 h22
  have hdiag_eq : unitaryLine_diag (K := K) ζ hd (unitaryLine_i0 hd) ^ n =
      unitaryLine_diag (K := K) ζ hd (unitaryLine_i2 hd) ^ n := by
    have h : unitaryLine_diag (K := K) ζ hd (unitaryLine_i0 hd) ^ n * (u : K) =
        unitaryLine_diag (K := K) ζ hd (unitaryLine_i2 hd) ^ n * (u : K) := by
      rw [← h00, ← h22]
    exact mul_right_cancel₀ (Units.ne_zero u) h
  rw [show unitaryLine_diag (K := K) ζ hd (unitaryLine_i0 hd) = (ζ : K)⁻¹ from by
    simp [unitaryLine_diag],
    show unitaryLine_diag (K := K) ζ hd (unitaryLine_i2 hd) = (ζ : K) from by
    simp [unitaryLine_diag, Ne.symm (unitaryLine_i_ne hd).2.1,
      Ne.symm (unitaryLine_i_ne hd).2.2.2.1]] at hdiag_eq
  rw [inv_pow] at hdiag_eq
  have hsq : (ζ : K) ^ (2 * n) = 1 := by
    have h := congrArg (fun x : K => x * (ζ : K) ^ n) hdiag_eq
    rw [inv_mul_cancel₀ (pow_ne_zero n (Units.ne_zero ζ))] at h
    rw [← pow_two, ← pow_mul, Nat.mul_comm n 2] at h
    exact h.symm
  have hsq' : (ζ : Kˣ) ^ (2 * n) = 1 := Units.ext hsq
  have hdvd2 : orderOf ζ ∣ 2 * n := orderOf_dvd_iff_pow_eq_one.mpr hsq'
  rw [hζord] at hdvd2
  exact (Nat.coprime_two_right.mpr (unitaryLine_odd_two_pow_add_one hK)).dvd_of_dvd_mul_left hdvd2

private theorem unitaryLine_orderOf_g (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζord : orderOf ζ = 2 ^ f + 1)
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    orderOf (unitaryLine_g hK hζ hd) = 2 ^ f + 1 := by
  refine Nat.dvd_antisymm ?_ (unitaryLine_dvd_orderOf_g hK hζord hζ hd)
  refine orderOf_dvd_iff_pow_eq_one.mpr ?_
  rw [unitaryLine_g, ← map_pow, unitaryLine_Dsu_pow_eq_one hζord hζ hd, map_one]

private theorem unitaryLine_Dsu_smul_e {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    unitaryLine_Dsu hζ hd • unitaryLine_e (K := K) hd =
      ((ζ : K)⁻¹) • unitaryLine_e (K := K) hd := by
  rw [unitaryLine_Dsu_smul]
  simpa using unitaryLine_D_pow_mulVec_e (K := K) ζ hd 1

private theorem unitaryLine_Dsu_smul_e' {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    unitaryLine_Dsu hζ hd • unitaryLine_e' (K := K) hd =
      (ζ : K) • unitaryLine_e' (K := K) hd := by
  rw [unitaryLine_Dsu_smul]
  simpa using unitaryLine_D_pow_mulVec_e' (K := K) ζ hd 1

private theorem unitaryLine_g_conj_tv_e (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) {s : K}
    (hs : s + unitaryInvolution K 2 f s = 0) :
    unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) s *
        (unitaryLine_g hK hζ hd)⁻¹ =
      kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) s := by
  calc
    unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) s *
        (unitaryLine_g hK hζ hd)⁻¹ =
      kFactsSuProjTv hK d (unitaryLine_Dsu hζ hd • unitaryLine_e (K := K) hd) s :=
        kFacts_suProj_conj_suProjTv hK _ (unitaryLine_e_isotropic hd) hs
    _ = kFactsSuProjTv hK d (((ζ : K)⁻¹) • unitaryLine_e (K := K) hd) s := by
        rw [unitaryLine_Dsu_smul_e]
    _ = kFactsSuProjTv hK d (unitaryLine_e (K := K) hd)
        (unitaryInvolution K 2 f ((ζ : K)⁻¹) * ((ζ : K)⁻¹) * s) :=
        kFacts_suProjTv_smul_vec hK (unitaryLine_e_isotropic hd) hs _
    _ = kFactsSuProjTv hK d (unitaryLine_e (K := K) hd) s := by
        congr 1
        rw [map_inv₀, ← mul_inv, hζ, inv_one, one_mul]

private theorem unitaryLine_g_conj_tv_e' (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) {s : K}
    (hs : s + unitaryInvolution K 2 f s = 0) :
    unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e' (K := K) hd) s *
        (unitaryLine_g hK hζ hd)⁻¹ =
      kFactsSuProjTv hK d (unitaryLine_e' (K := K) hd) s := by
  calc
    unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e' (K := K) hd) s *
        (unitaryLine_g hK hζ hd)⁻¹ =
      kFactsSuProjTv hK d (unitaryLine_Dsu hζ hd • unitaryLine_e' (K := K) hd) s :=
        kFacts_suProj_conj_suProjTv hK _ (unitaryLine_e'_isotropic hd) hs
    _ = kFactsSuProjTv hK d ((ζ : K) • unitaryLine_e' (K := K) hd) s := by
        rw [unitaryLine_Dsu_smul_e']
    _ = kFactsSuProjTv hK d (unitaryLine_e' (K := K) hd)
        (unitaryInvolution K 2 f (ζ : K) * (ζ : K) * s) :=
        kFacts_suProjTv_smul_vec hK (unitaryLine_e'_isotropic hd) hs _
    _ = kFactsSuProjTv hK d (unitaryLine_e' (K := K) hd) s := by
        congr 1
        rw [hζ, one_mul]

private theorem unitaryLine_commute_vmem_v (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    ∀ x ∈ Vmem (unitaryLine_class hK) (unitaryLine_v hK hd),
      Commute (unitaryLine_g hK hζ hd) x := by
  intro x hx
  rw [Vmem_setOf_kFactsSuProjTv hK (unitaryLine_e_ne_zero hd)
    (unitaryLine_e_isotropic hd)] at hx
  obtain ⟨s, hs0, hs, rfl⟩ := hx
  have h := unitaryLine_g_conj_tv_e hK hζ hd hs
  show unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e hd) s =
    kFactsSuProjTv hK d (unitaryLine_e hd) s * unitaryLine_g hK hζ hd
  calc
    unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e hd) s =
        (unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e hd) s *
          (unitaryLine_g hK hζ hd)⁻¹) * unitaryLine_g hK hζ hd := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = kFactsSuProjTv hK d (unitaryLine_e hd) s * unitaryLine_g hK hζ hd := by rw [h]

private theorem unitaryLine_commute_vmem_w (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    ∀ x ∈ Vmem (unitaryLine_class hK) (unitaryLine_w hK hd),
      Commute (unitaryLine_g hK hζ hd) x := by
  intro x hx
  rw [Vmem_setOf_kFactsSuProjTv hK (unitaryLine_e'_ne_zero hd)
    (unitaryLine_e'_isotropic hd)] at hx
  obtain ⟨s, hs0, hs, rfl⟩ := hx
  have h := unitaryLine_g_conj_tv_e' hK hζ hd hs
  show unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e' hd) s =
    kFactsSuProjTv hK d (unitaryLine_e' hd) s * unitaryLine_g hK hζ hd
  calc
    unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e' hd) s =
        (unitaryLine_g hK hζ hd * kFactsSuProjTv hK d (unitaryLine_e' hd) s *
          (unitaryLine_g hK hζ hd)⁻¹) * unitaryLine_g hK hζ hd := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = kFactsSuProjTv hK d (unitaryLine_e' hd) s * unitaryLine_g hK hζ hd := by rw [h]

private theorem unitaryLine_g_pow_conj_tv (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) (i : ℕ)
    {c : Fin d → K} (hc : herm (unitaryInvolution K 2 f) c c = 0) {s : K}
    (hs : s + unitaryInvolution K 2 f s = 0) :
    unitaryLine_g hK hζ hd ^ i * kFactsSuProjTv hK d c s *
        (unitaryLine_g hK hζ hd ^ i)⁻¹ =
      kFactsSuProjTv hK d ((unitaryLine_Dsu hζ hd ^ i) • c) s := by
  rw [unitaryLine_g, ← map_pow]
  exact kFacts_suProj_conj_suProjTv hK _ hc hs

private theorem unitaryLine_alpha_ne_zero (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {x : StatedProj (StatedSU d (2 ^ f) K)} {α β : K}
    (hc0 : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd ≠ 0)
    (hc : herm (unitaryInvolution K 2 f)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) = 0)
    (hxT : x = kFactsSuProjTv hK d
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) 1)
    (hxne_w : perpMem (unitaryLine_class hK) x ≠
      perpMem (unitaryLine_class hK) (unitaryLine_w hK hd)) :
    α ≠ 0 := by
  intro hα
  apply hxne_w
  have hcβ : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd =
      β • unitaryLine_e' (K := K) hd := by
    rw [hα, zero_smul, zero_add]
  have hβ0 : β ≠ 0 := by
    intro hβ
    exact hc0 (by rw [hα, hβ, zero_smul, zero_smul, add_zero])
  have hiff := (perpMem_setOf_kFactsSuProjTv_eq_iff hK (unitaryLine_e'_ne_zero hd)
    (unitaryLine_e'_isotropic hd) hc0 hc).mpr ⟨β, hcβ⟩
  rw [hxT]
  exact hiff.symm

private theorem unitaryLine_beta_ne_zero (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d)
    {x : StatedProj (StatedSU d (2 ^ f) K)} {α β : K}
    (hc0 : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd ≠ 0)
    (hc : herm (unitaryInvolution K 2 f)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) = 0)
    (hxT : x = kFactsSuProjTv hK d
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) 1)
    (hxne_v : perpMem (unitaryLine_class hK) x ≠
      perpMem (unitaryLine_class hK) (unitaryLine_v hK hd)) :
    β ≠ 0 := by
  intro hβ
  apply hxne_v
  have hcα : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd =
      α • unitaryLine_e (K := K) hd := by
    rw [hβ, zero_smul, add_zero]
  have hα0 : α ≠ 0 := by
    intro hα
    exact hc0 (by rw [hα, hβ, zero_smul, zero_smul, add_zero])
  have hiff := (perpMem_setOf_kFactsSuProjTv_eq_iff hK (unitaryLine_e_ne_zero hd)
    (unitaryLine_e_isotropic hd) hc0 hc).mpr ⟨α, hcα⟩
  rw [hxT]
  exact hiff.symm

private theorem unitaryLine_semiregular_mu (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d)
    {x : StatedProj (StatedSU d (2 ^ f) K)} {α β : K}
    (hc0 : α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd ≠ 0)
    (hc : herm (unitaryInvolution K 2 f)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd)
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) = 0)
    (hxT : x = kFactsSuProjTv hK d
      (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) 1) (i : ℕ)
    (hperp : perpMem (unitaryLine_class hK)
        (unitaryLine_g hK hζ hd ^ i * x * (unitaryLine_g hK hζ hd ^ i)⁻¹) =
      perpMem (unitaryLine_class hK) x) :
    ∃ μ : K, (unitaryLine_Dsu hζ hd ^ i) •
        (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) =
      μ • (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) := by
  let c : Fin d → K := α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd
  let c' : Fin d → K := (unitaryLine_Dsu hζ hd ^ i) • c
  have hc'0 : c' ≠ 0 := by
    intro h0
    have h1 : c = 0 := by
      have := congrArg (fun v => (unitaryLine_Dsu hζ hd ^ i)⁻¹ • v) h0
      dsimp only [c'] at this
      simpa using this
    exact hc0 h1
  have hc'iso : herm (unitaryInvolution K 2 f) c' c' = 0 := by
    dsimp only [c']
    rw [herm_smul_smul, hc]
  have hconj : unitaryLine_g hK hζ hd ^ i * x * (unitaryLine_g hK hζ hd ^ i)⁻¹ =
      kFactsSuProjTv hK d c' 1 := by
    rw [hxT]
    have h := unitaryLine_g_pow_conj_tv hK hζ hd i (c := c) hc
      (s := 1) unitaryLine_one_add_sigma_one
    simpa [c'] using h
  rw [hconj, hxT] at hperp
  obtain ⟨μ, hμ⟩ := (perpMem_setOf_kFactsSuProjTv_eq_iff hK hc0 hc hc'0 hc'iso).mp hperp.symm
  exact ⟨μ, by simpa [c, c'] using hμ⟩

private theorem unitaryLine_semiregular_zeta_eq (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d)
    {α β μ : K} (i : ℕ)
    (hμ : (unitaryLine_Dsu hζ hd ^ i) •
        (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd) =
      μ • (α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) :
    ((ζ : K)⁻¹) ^ i = (ζ : K) ^ i := by
  let c : Fin d → K := α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd
  have hμ' : (unitaryLine_Dsu hζ hd ^ i) • c = μ • c := by simpa [c] using hμ
  have hc'eq : (unitaryLine_Dsu hζ hd ^ i) • c =
      (((ζ : K)⁻¹) ^ i * α) • unitaryLine_e (K := K) hd +
        (((ζ : K) ^ i * β) • unitaryLine_e' (K := K) hd) := by
    dsimp only [c]
    rw [unitaryLine_Dsu_pow_smul, unitaryLine_D_pow_mulVec_add]
  have h0 : ((ζ : K)⁻¹) ^ i * α = μ * α := by
    have h := congrFun hμ' (unitaryLine_i0 hd)
    rw [hc'eq] at h
    simpa [Pi.smul_apply, Pi.add_apply, c, unitaryLine_e, unitaryLine_e', Pi.single_apply,
      (unitaryLine_i_ne hd).1, (unitaryLine_i_ne hd).2.1, (unitaryLine_i_ne hd).2.2.1,
      Ne.symm (unitaryLine_i_ne hd).1, Ne.symm (unitaryLine_i_ne hd).2.1,
      Ne.symm (unitaryLine_i_ne hd).2.2.1, smul_eq_mul] using h
  have h2 : (ζ : K) ^ i * β = μ * β := by
    have h := congrFun hμ' (unitaryLine_i2 hd)
    rw [hc'eq] at h
    simpa [Pi.smul_apply, Pi.add_apply, c, unitaryLine_e, unitaryLine_e', Pi.single_apply,
      (unitaryLine_i_ne hd).2.1, (unitaryLine_i_ne hd).2.2.2.1,
      (unitaryLine_i_ne hd).2.2.2.2.2,
      Ne.symm (unitaryLine_i_ne hd).2.1, Ne.symm (unitaryLine_i_ne hd).2.2.2.1,
      Ne.symm (unitaryLine_i_ne hd).2.2.2.2.2, smul_eq_mul] using h
  have hμ0 : ((ζ : K)⁻¹) ^ i = μ := mul_right_cancel₀ hα0 h0
  have hμ2 : (ζ : K) ^ i = μ := mul_right_cancel₀ hβ0 h2
  exact hμ0.trans hμ2.symm

private theorem unitaryLine_semiregular (hK : Nat.card K = (2 ^ f) ^ 2) {ζ : Kˣ}
    (hζord : orderOf ζ = 2 ^ f + 1)
    (hζ : unitaryInvolution K 2 f (ζ : K) * (ζ : K) = 1) (hd : 4 ≤ d) :
    ∀ x ∈ lineMem (unitaryLine_class hK) (unitaryLine_v hK hd) (unitaryLine_w hK hd),
      perpMem (unitaryLine_class hK) x ≠ perpMem (unitaryLine_class hK) (unitaryLine_v hK hd) →
      perpMem (unitaryLine_class hK) x ≠ perpMem (unitaryLine_class hK) (unitaryLine_w hK hd) →
      ∀ i : ℕ,
        perpMem (unitaryLine_class hK)
            (unitaryLine_g hK hζ hd ^ i * x * (unitaryLine_g hK hζ hd ^ i)⁻¹) =
          perpMem (unitaryLine_class hK) x →
        unitaryLine_g hK hζ hd ^ i = 1 := by
  intro x hxline hxne_v hxne_w i hperp
  obtain ⟨α, β, hc0, hc, hx⟩ := unitaryLine_mem_span hK hd hxline
  let c : Fin d → K := α • unitaryLine_e (K := K) hd + β • unitaryLine_e' (K := K) hd
  have hxT : x = kFactsSuProjTv hK d c 1 := by simpa [c] using hx
  have hα0 : α ≠ 0 :=
    unitaryLine_alpha_ne_zero hK hd hc0 hc hxT hxne_w
  have hβ0 : β ≠ 0 :=
    unitaryLine_beta_ne_zero hK hd hc0 hc hxT hxne_v
  obtain ⟨μ, hμ⟩ := unitaryLine_semiregular_mu hK hζ hd hc0 hc hxT i hperp
  have hζeq := unitaryLine_semiregular_zeta_eq hK hζ hd i hμ hα0 hβ0
  rw [inv_pow] at hζeq
  have hsq : (ζ : K) ^ (2 * i) = 1 := by
    have h := congrArg (fun x : K => x * (ζ : K) ^ i) hζeq
    rw [inv_mul_cancel₀ (pow_ne_zero i (Units.ne_zero ζ))] at h
    rw [← pow_two, ← pow_mul, Nat.mul_comm i 2] at h
    exact h.symm
  have hsq' : (ζ : Kˣ) ^ (2 * i) = 1 := Units.ext hsq
  have hdvd : 2 ^ f + 1 ∣ i := by
    have hdvd2 : orderOf ζ ∣ 2 * i := orderOf_dvd_iff_pow_eq_one.mpr hsq'
    rw [hζord] at hdvd2
    exact (Nat.coprime_two_right.mpr (unitaryLine_odd_two_pow_add_one hK)).dvd_of_dvd_mul_left hdvd2
  rw [← orderOf_dvd_iff_pow_eq_one, unitaryLine_orderOf_g hK hζord hζ hd]
  exact hdvd

end Model

section Transport

variable {X Y : Type} [Group X] [Group Y]

private theorem unitaryLine_perpMem_symm_eq (φ : X ≃* Y) {S : Set Y} {s : X}
    (hclass' : φ.symm '' S = {x | IsConj s x}) (a b : Y) :
    perpMem {x | IsConj s x} (φ.symm a) = perpMem {x | IsConj s x} (φ.symm b) ↔
      perpMem S a = perpMem S b := by
  have ha : perpMem {x | IsConj s x} (φ.symm a) = φ.symm '' perpMem S a := by
    rw [← hclass']
    exact perpMem_image_mulEquiv φ.symm S a
  have hb : perpMem {x | IsConj s x} (φ.symm b) = φ.symm '' perpMem S b := by
    rw [← hclass']
    exact perpMem_image_mulEquiv φ.symm S b
  rw [ha, hb]
  exact (Set.image_injective.mpr φ.symm.injective).eq_iff

private theorem unitaryLine_transport_perp_ne (φ : X ≃* Y) {S : Set Y} {v₀ w₀ : Y} {s : X}
    (hclass' : φ.symm '' S = {x | IsConj s x})
    (hne : perpMem S v₀ ≠ perpMem S w₀) :
    perpMem {x | IsConj s x} (φ.symm v₀) ≠
      perpMem {x | IsConj s x} (φ.symm w₀) := by
  intro h
  exact hne ((unitaryLine_perpMem_symm_eq φ hclass' v₀ w₀).mp h)

private theorem unitaryLine_transport_ncard (φ : X ≃* Y) {S : Set Y} {v₀ w₀ : Y} {s : X}
    (hclass' : φ.symm '' S = {x | IsConj s x}) :
    (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x}
        (φ.symm v₀) (φ.symm w₀)).ncard =
      (perpMem S '' lineMem S v₀ w₀).ncard := by
  rw [← hclass']
  exact ncard_perpMem_image_lineMem_mulEquiv φ.symm S v₀ w₀

private theorem unitaryLine_transport_order (φ : X ≃* Y) (g₀ : Y) {n : ℕ}
    (hord : orderOf g₀ = n) : orderOf (φ.symm g₀) = n := by
  rw [MulEquiv.orderOf_eq, hord]

private theorem unitaryLine_transport_vmem (φ : X ≃* Y) {S : Set Y} {u₀ : Y} {s : X}
    (hclass' : φ.symm '' S = {x | IsConj s x}) {g₀ : Y}
    (hcomm : ∀ x ∈ Vmem S u₀, Commute g₀ x) :
    ∀ x ∈ Vmem {x | IsConj s x} (φ.symm u₀), Commute (φ.symm g₀) x := by
  intro x hx
  have hx' : x ∈ φ.symm '' Vmem S u₀ := by
    rw [← Vmem_image_mulEquiv φ.symm S u₀, hclass']
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  exact (hcomm y hy).map φ.symm.toMonoidHom

private theorem unitaryLine_transport_semiregular (φ : X ≃* Y) {S : Set Y}
    {v₀ w₀ g₀ : Y} {s : X} (hclass' : φ.symm '' S = {x | IsConj s x})
    (hsemi : ∀ x ∈ lineMem S v₀ w₀,
      perpMem S x ≠ perpMem S v₀ → perpMem S x ≠ perpMem S w₀ →
      ∀ i : ℕ, perpMem S (g₀ ^ i * x * (g₀ ^ i)⁻¹) = perpMem S x → g₀ ^ i = 1) :
    ∀ x ∈ lineMem {x | IsConj s x} (φ.symm v₀) (φ.symm w₀),
      perpMem {x | IsConj s x} x ≠ perpMem {x | IsConj s x} (φ.symm v₀) →
      perpMem {x | IsConj s x} x ≠ perpMem {x | IsConj s x} (φ.symm w₀) →
      ∀ i : ℕ,
        perpMem {x | IsConj s x} ((φ.symm g₀) ^ i * x * ((φ.symm g₀) ^ i)⁻¹) =
          perpMem {x | IsConj s x} x → (φ.symm g₀) ^ i = 1 := by
  intro x hx hxv hxw i hperp
  have hx' : x ∈ φ.symm '' lineMem S v₀ w₀ := by
    rw [← lineMem_image_mulEquiv φ.symm S v₀ w₀, hclass']
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have hxv' : perpMem S y ≠ perpMem S v₀ := by
    intro h
    exact hxv ((unitaryLine_perpMem_symm_eq φ hclass' y v₀).mpr h)
  have hxw' : perpMem S y ≠ perpMem S w₀ := by
    intro h
    exact hxw ((unitaryLine_perpMem_symm_eq φ hclass' y w₀).mpr h)
  have hperp' : perpMem S (g₀ ^ i * y * (g₀ ^ i)⁻¹) = perpMem S y := by
    refine (unitaryLine_perpMem_symm_eq φ hclass' (g₀ ^ i * y * (g₀ ^ i)⁻¹) y).mp ?_
    simpa [map_mul, map_inv, map_pow] using hperp
  have hy1 := hsemi y hy hxv' hxw' i hperp'
  rw [← map_pow, hy1, map_one]

private theorem unitaryLine_transport_all (φ : X ≃* Y) {s : X} {S : Set Y}
    {v₀ w₀ g₀ : Y} {f : ℕ} (hclass' : φ.symm '' S = {x | IsConj s x})
    (hv₀ : v₀ ∈ S) (hw₀ : w₀ ∈ S) (hcomm : Commute v₀ w₀)
    (hne : perpMem S v₀ ≠ perpMem S w₀)
    (hncard : (perpMem S '' lineMem S v₀ w₀).ncard ≤ (2 ^ f) ^ 2 + 1)
    (hord : orderOf g₀ = 2 ^ f + 1)
    (hgv : ∀ x ∈ Vmem S v₀, Commute g₀ x)
    (hgw : ∀ x ∈ Vmem S w₀, Commute g₀ x)
    (hsem : ∀ x ∈ lineMem S v₀ w₀,
      perpMem S x ≠ perpMem S v₀ → perpMem S x ≠ perpMem S w₀ →
      ∀ i : ℕ, perpMem S (g₀ ^ i * x * (g₀ ^ i)⁻¹) = perpMem S x → g₀ ^ i = 1) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, Commute v w ∧
      perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w ∧
      (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ (2 ^ f) ^ 2 + 1 ∧
      ∃ g : X, orderOf g = 2 ^ f + 1 ∧
        (∀ x ∈ Vmem {x | IsConj s x} v, Commute g x) ∧
        (∀ x ∈ Vmem {x | IsConj s x} w, Commute g x) ∧
        ∀ x ∈ lineMem {x | IsConj s x} v w,
          perpMem {x | IsConj s x} x ≠ perpMem {x | IsConj s x} v →
          perpMem {x | IsConj s x} x ≠ perpMem {x | IsConj s x} w →
          ∀ i : ℕ, perpMem {x | IsConj s x} (g ^ i * x * (g ^ i)⁻¹) =
            perpMem {x | IsConj s x} x → g ^ i = 1 := by
  refine ⟨φ.symm v₀, ?_, φ.symm w₀, ?_, ?_, ?_, ?_, φ.symm g₀, ?_, ?_, ?_, ?_⟩
  · rw [← hclass']
    exact ⟨v₀, hv₀, rfl⟩
  · rw [← hclass']
    exact ⟨w₀, hw₀, rfl⟩
  · simpa using hcomm.map φ.symm.toMonoidHom
  · exact unitaryLine_transport_perp_ne φ hclass' hne
  · rw [unitaryLine_transport_ncard φ hclass']
    exact hncard
  · exact unitaryLine_transport_order φ g₀ hord
  · exact unitaryLine_transport_vmem φ hclass' hgv
  · exact unitaryLine_transport_vmem φ hclass' hgw
  · exact unitaryLine_transport_semiregular φ hclass' hsem

end Transport

theorem exists_lineMem_torus_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {d f : ℕ} (hd : 4 ≤ d)
    (hs : IsUnitaryTransvection X d f s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, Commute v w ∧
      perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w ∧
      (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ (2 ^ f) ^ 2 + 1 ∧
      ∃ g : X, orderOf g = 2 ^ f + 1 ∧
        (∀ x ∈ Vmem {x | IsConj s x} v, Commute g x) ∧
        (∀ x ∈ Vmem {x | IsConj s x} w, Commute g x) ∧
        ∀ x ∈ lineMem {x | IsConj s x} v w,
          perpMem {x | IsConj s x} x ≠ perpMem {x | IsConj s x} v →
          perpMem {x | IsConj s x} x ≠ perpMem {x | IsConj s x} w →
          ∀ i : ℕ, perpMem {x | IsConj s x} (g ^ i * x * (g ^ i)⁻¹) =
            perpMem {x | IsConj s x} x → g ^ i = 1 := by
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, φ, e₀, he₀, he₀i, hφs⟩ :=
    exists_mulEquiv_of_isUnitaryTransvection hZ hs
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hK : Nat.card K = (2 ^ f) ^ 2 := hKcard
  obtain ⟨ζ, hζnorm, hζord⟩ :=
    CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq (p := 2) (f := f) hK
  let S : Set (StatedProj (StatedSU d (2 ^ f) K)) :=
    unitaryLine_class (K := K) (d := d) hK
  let v₀ : StatedProj (StatedSU d (2 ^ f) K) := unitaryLine_v (K := K) hK hd
  let w₀ : StatedProj (StatedSU d (2 ^ f) K) := unitaryLine_w (K := K) hK hd
  let g₀ : StatedProj (StatedSU d (2 ^ f) K) := unitaryLine_g (K := K) hK hζnorm hd
  have hclass : φ '' {x | IsConj s x} = S := by
    rw [CFSG.Fischer.image_setOf_isConj φ s, hφs]
    simpa [S, unitaryLine_class] using
      setOf_isConj_kFactsSuProjTv (F := K) hK (by omega) he₀ he₀i
  have hclass' : φ.symm '' S = {x | IsConj s x} := by
    rw [← hclass]
    exact CFSG.Fischer.image_symm_image φ {x | IsConj s x}
  exact unitaryLine_transport_all φ hclass'
    (unitaryLine_v_mem (K := K) hK hd) (unitaryLine_w_mem (K := K) hK hd)
    (unitaryLine_commute_v_w (K := K) hK hd) (unitaryLine_perp_ne (K := K) hK hd)
    (unitaryLine_ncard_le (K := K) hK hd)
    (unitaryLine_orderOf_g (K := K) hK hζord hζnorm hd)
    (unitaryLine_commute_vmem_v (K := K) hK hζnorm hd)
    (unitaryLine_commute_vmem_w (K := K) hK hζnorm hd)
    (unitaryLine_semiregular (K := K) hK hζord hζnorm hd)
