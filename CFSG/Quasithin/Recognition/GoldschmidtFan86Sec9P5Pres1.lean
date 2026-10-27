module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg6
public import Mathlib.GroupTheory.Index
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg1c
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg2

public section

namespace CFSG.Quasithin.Fan86

macro "memsimp" : tactic =>
  `(tactic| simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
    exists_apply_eq_apply, true_or, or_true])

variable {H : Type*} [Group H]

theorem eq_of_relIndex_two {K E M : Subgroup H} (hKE : K ≤ E) (hEM : E ≤ M)
    (hKM : K.relIndex M = 2) {t : H} (htE : t ∈ E) (htK : t ∉ K) : E = M := by
  have h := Subgroup.relIndex_mul_relIndex K E M hKE hEM
  rw [hKM] at h
  have h1 : K.relIndex E ≠ 1 := fun h1 => htK ((Subgroup.relIndex_eq_one.1 h1) htE)
  have h2 : K.relIndex E ∣ 2 := ⟨E.relIndex M, h.symm⟩
  have h3 : K.relIndex E = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) h2
    have h0 : K.relIndex E ≠ 0 := by
      intro h0
      rw [h0] at h2
      omega
    omega
  rw [h3] at h
  have h4 : E.relIndex M = 1 := by omega
  exact le_antisymm hEM (Subgroup.relIndex_eq_one.1 h4)

variable {x w za c : H} {y z : Fin 5 → H}

theorem P1Rel.mul_za_pow (hR : P1Rel x w za y z) {e : ℕ} (he : e ≤ 1) :
    P1Rel x (w * za ^ e) za y z := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl
  · simpa using hR
  · simpa using hR.mul_za

theorem P1cRel.mul_za_pow (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) {d : ℕ} (hd : d ≤ 1) :
    P1cRel x za (c * za ^ d) y z := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with rfl | rfl
  · simpa using hC
  · simpa using P1cRel.mul_za hR hC

variable {xb t w2 ub : H} {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}

theorem P5Ids.mem_of_gens (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) {K : Subgroup H}
    (hw : w ∈ K) (hza : za ∈ K) (hy : ∀ j, y j ∈ K) (hz : ∀ j, z j ∈ K) :
    t ∈ K ∧ w2 ∈ K ∧ ub ∈ K ∧ (∀ i, zm i ∈ K) ∧ (∀ i, ym i ∈ K) ∧ (∀ i, za' i ∈ K) := by
  have ht : t ∈ K := h.t_eq ▸ hy 0
  have hza' : ∀ i, za' i ∈ K := by
    refine fin3_forall ?_ ?_ ?_
    · rw [h.za0]; exact hza
    · rw [h.za1]; exact K.mul_mem (hz 2) hza
    · rw [h.za2]; exact hz 2
  have hzm2 : zm 2 ∈ K := by
    rw [h.zm2]
    exact K.mul_mem (K.mul_mem hw hw) hza
  have hym2 : ym 2 ∈ K := by
    rw [h.ym2]
    exact K.mul_mem (hy 2) (hza' 2)
  have hym0 : ym 0 ∈ K := by
    rw [h.ym0]
    exact K.mul_mem (hz 0) (hz 1)
  refine ⟨ht, ?_, ?_, ?_, ?_, hza'⟩
  · rw [h.w2_eq]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (hy 3) (hy 4)) (hz 3))
      (K.pow_mem (hz 2) e₁)) (K.pow_mem hza e₂)
  · rw [h.ub_eq]
    exact K.mul_mem (K.mul_mem (hz 1) (hz 3)) hza
  · refine fin3_forall ?_ ?_ ?_
    · rw [h.zm0]; exact hz 0
    · rw [h.zm1]; exact K.mul_mem (K.mul_mem (K.inv_mem ht) hzm2) ht
    · exact hzm2
  · refine fin3_forall hym0 ?_ hym2
    rw [h.ym1]
    exact K.mul_mem hym0 hym2

theorem fcomm_norm (hwc : fcomm w c = 1) (hwz : fcomm w za = 1) (hcz : fcomm c za = 1) (e d : ℕ) :
    fcomm (w * za ^ e) (c * za ^ d) = 1 := by
  refine fcomm_eq_one_iff.2 ?_
  have h1 : Commute w c := (fcomm_eq_one_iff.1 hwc).symm
  have h2 : Commute w za := (fcomm_eq_one_iff.1 hwz).symm
  have h3 : Commute c za := (fcomm_eq_one_iff.1 hcz).symm
  have hA : Commute (w * za ^ e) c := h1.mul_left (h3.symm.pow_left e)
  have hB : Commute (w * za ^ e) (za ^ d) :=
    (h2.pow_right d).mul_left ((Commute.refl za).pow_pow e d)
  exact (hA.mul_right hB).eq.symm

theorem P5Ids.hcx_norm (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)
    (hC : P1cRel x za c y z) (_hwc : fcomm w c = 1) {d : ℕ} (hd : d ≤ 1)
    (hcx : xb⁻¹ * c * xb = y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 0) :
    xb⁻¹ * (c * za ^ d) * xb = y 1 * y 3 * z 3 * z 4 * (c * za ^ d) * z 2 ^ 0 * za ^ 0 := by
  have hc : xb⁻¹ * za * xb = za' 1 := by simpa [h.za0] using h.xa 0
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with rfl | rfl
  · simpa using hcx
  · calc xb⁻¹ * (c * za ^ 1) * xb = (xb⁻¹ * c * xb) * (xb⁻¹ * za * xb) := by group
      _ = y 1 * y 3 * z 3 * z 4 * (c * za ^ 1) * z 2 ^ 0 * za ^ 0 := by
        rw [hcx, hc, h.za1]
        collc hR hC _hwc

theorem P5Ids.link_ub (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z) :
    z 0 * z 4 * (z 2 * za) = ub := by
  rw [h.ub_eq]
  coll hR

theorem P5Ids.link_zm1 (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z) :
    y 0 * (w ^ 2 * za) * y 0 = zm 1 := by
  rw [h.zm1, h.zm2, h.t_eq]
  coll hR

theorem P5Ids.link_zm2 (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) :
    w ^ 2 * za = zm 2 := by
  rw [h.zm2, pow_two]

theorem P5Ids.link_ym1 (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) :
    z 0 * z 1 * (y 2 * z 2) = ym 1 := by
  rw [h.ym1, h.ym0, h.ym2, h.za2]

theorem P5Ids.link_ym2 (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) :
    y 2 * z 2 = ym 2 := by
  rw [h.ym2, h.za2]

theorem P5Ids.link_w2 (h : P5Ids w za y z xb t w2 ub zm ym za' 0 0) :
    y 3 * y 4 * z 3 = w2 := by
  rw [h.w2_eq]
  simp

end CFSG.Quasithin.Fan86
