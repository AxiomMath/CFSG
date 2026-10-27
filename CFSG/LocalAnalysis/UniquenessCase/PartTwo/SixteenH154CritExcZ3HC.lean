module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Jm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3J
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3P9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_exists_elem_nine_of_Z3_six_two {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hLA : L ≤ A) (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    (hev : Even (Nat.card ↥A)) (hm : E3.mParam A ≤ 2) {Q : Subgroup (MulAut W)} (hQA : Q ≤ A)
    (hQ : IsElemAbelian 3 Q)
    (hQ27 : 27 * Nat.card ↥(Q ⊓ centSub (commSub (⊤ : Subgroup W) L)) ≤ Nat.card ↥Q) :
    ∃ P : Subgroup (MulAut W), P ≤ A ⊓ centSub (commSub (⊤ : Subgroup W) L) ∧
      IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P := by
  classical
  obtain ⟨j, hjA, hj2, hj1, hjU₂, hjL⟩ :=
    s16h_z3_exists_j_of_mParam hW hB hL hrk hfix hev hm
  obtain ⟨J, hJA, hJU₂, hJL, hJn, hJgen, hJ2⟩ :=
    s16h_z3_exists_J hB hO2 hjA hj2 hj1 hjU₂ hjL
  have hQconj : ∀ q ∈ Q, L.map (MulAut.conj q).toMonoidHom = L := fun q hq =>
    (s16h_z3_commute_of_pow_three hB hL (hQA hq) (hQ.2 q hq)).1
  have hQcomm : ∀ q ∈ Q, ∀ l ∈ L, q * l = l * q := fun q hq =>
    (s16h_z3_commute_of_pow_three hB hL (hQA hq) (hQ.2 q hq)).2.1
  have hQinv3 : ∀ q ∈ Q, (q⁻¹) ^ 3 = 1 := by
    intro q hq
    rw [inv_pow, hQ.2 q hq, inv_one]
  have hQinvcomm : ∀ q ∈ Q, ∀ l ∈ L, q⁻¹ * l = l * q⁻¹ := by
    intro q hq l hl
    have h := hQcomm q hq l hl
    calc q⁻¹ * l = q⁻¹ * (l * q) * q⁻¹ := by group
      _ = q⁻¹ * (q * l) * q⁻¹ := by rw [← h]
      _ = l * q⁻¹ := by group
  have hQstab : Q ≤ stabSub (commSub (⊤ : Subgroup W) L) := by
    intro q hq
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := commSub_top_stable151b (X := L) (g := q⁻¹)
        (fun z hz => by
          rw [inv_inv]
          have hz' : q⁻¹ * z * q = z := by rw [hQinvcomm q hq z hz]; group
          rw [hz']; exact hz) (q u) hu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact commSub_top_stable151b (X := L) (g := q)
        (fun z hz => by
          have hz' : q * z * q⁻¹ = z := by rw [hQcomm q hq z hz]; group
          rw [hz']; exact hz) u hu
  have hLstab : L ≤ stabSub (commSub (⊤ : Subgroup W) L) := by
    intro l hl
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := commSub_top_stable151b (X := L) (g := l⁻¹)
        (fun z hz => by
          rw [inv_inv]
          exact L.mul_mem (L.mul_mem (L.inv_mem hl) hz) hl) (l u) hu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact commSub_top_stable151b (X := L) (g := l)
        (fun z hz => L.mul_mem (L.mul_mem hl hz) (L.inv_mem hl)) u hu
  have hJinvcomm : ∀ y ∈ J, ∀ l ∈ L, y⁻¹ * l = l * y⁻¹ := by
    intro y hy l hl
    have h := hJL y hy l hl
    calc y⁻¹ * l = y⁻¹ * (l * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * l) * y⁻¹ := by rw [← h]
      _ = l * y⁻¹ := by group
  have hJstab : J ≤ stabSub (commSub (⊤ : Subgroup W) L) := by
    intro y hy
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := commSub_top_stable151b (X := L) (g := y⁻¹)
        (fun z hz => by
          rw [inv_inv]
          have hz' : y⁻¹ * z * y = z := by rw [hJinvcomm y hy z hz]; group
          rw [hz']; exact hz) (y u) hu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact commSub_top_stable151b (X := L) (g := y)
        (fun z hz => by
          have hz' : y * z * y⁻¹ = z := by rw [hJL y hy z hz]; group
          rw [hz']; exact hz) u hu
  have hJc : J ⊓ centSub (commSub (⊤ : Subgroup W) L) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro y hy
    refine MulEquiv.ext fun w => ?_
    show y w = w
    have hw : w ∈ commSub (⊤ : Subgroup W) L ⊔ commSub (⊤ : Subgroup W) L₂ := by
      rw [hB.sup]; exact Subgroup.mem_top w
    obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp hw
    have hyU : y u = u := (mem_centSub.mp hy.2) u hu
    have hyU₂ : y v = v := (mem_centSub.mp (hJU₂ hy.1)) v hv
    calc y w = y (u * v) := by rw [huv]
      _ = y u * y v := map_mul y u v
      _ = u * v := by rw [hyU, hyU₂]
      _ = w := huv
  have hDJ : Q ≤ normalizer (J : Set (MulAut W)) := by
    intro q hq
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hJn q (hQA hq) (hQconj q hq) h hh
    · intro hh
      have hqinvA : q⁻¹ ∈ A := A.inv_mem (hQA hq)
      have hqinvnorm : L.map (MulAut.conj q⁻¹).toMonoidHom = L :=
        (s16h_z3_commute_of_pow_three hB hL hqinvA (hQinv3 q hq)).1
      have hh' := hJn q⁻¹ hqinvA hqinvnorm (q * h * q⁻¹) hh
      have heq : q⁻¹ * (q * h * q⁻¹) * (q⁻¹)⁻¹ = h := by rw [inv_inv]; group
      rwa [heq] at hh'
  obtain ⟨y, hyJ, hy3, hyL'⟩ :=
    s16h_exists_order_three_of_torus_res hW hrk hL hLstab hfix hQ hQstab hQ27 hQcomm
      hJstab hJL hJc hDJ hJgen hJ2
  exact s16h_z3_exists_elem_nine hB hLA hL (hJA hyJ) (hJU₂ hyJ) (hJL y hyJ) hy3 hyL'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
