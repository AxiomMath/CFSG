module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36Cc

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem S36_z_comm {t z u : G} (hz : z ∈ Subgroup.zpowers t) (hu : u ∈ Cen t) :
    z * u = u * z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hu' : t * u = u * t := S36_comm_of_cen hu
  have hc : Commute t u := hu'
  exact (hc.zpow_left m).eq

theorem S36_z_mul_self {t z : G} (ht : orderOf t = 2) (hz : z ∈ Subgroup.zpowers t) :
    z * z = 1 := by
  have := S36_sq_zpowers ht hz
  rwa [sq] at this

theorem F6_commute {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) :
    ∀ x ∈ Op 2 (Cen t) ⊓ Cen b₁, ∀ y ∈ Op 2 (Cen t) ⊓ Cen b₂, x * y = y * x := by
  intro x hx y hy
  obtain ⟨hxT, hx1⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hyT, hy2⟩ := Subgroup.mem_inf.1 hy
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₁).1
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₂).1
  have hb2L : b₂ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₂).2
  have hcom : Commute b₁ b₂ := comm_of_mem_B d.sec hb1B hb2B
  have p2 : b₂ ^ 3 = 1 := pow3_of_mem_B d.sec hb2B
  have htc' : ∀ z ∈ L, t * z = z * t := fun z hz =>
    (Subgroup.mem_centralizer_iff.1 d.htL z hz).symm
  have hb2Ct : b₂ ∈ Cen t := S36_mem_cen_of (htc' b₂ hb2L)
  have hTc : ∀ u ∈ Op 2 (Cen t), u ∈ Cen t := fun u hu => S36_op2_le _ hu
  have hZT : ∀ z ∈ Subgroup.zpowers t, ∀ u ∈ Op 2 (Cen t), z * u = u * z :=
    fun z hz u hu => S36_z_comm hz (hTc u hu)
  have hZb2 : ∀ z ∈ Subgroup.zpowers t, b₂ * z * b₂⁻¹ = z := by
    intro z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc : Commute b₂ t := (htc' b₂ hb2L).symm
    rw [(hc.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcZ : ∀ u ∈ Op 2 (Cen t), u * y * u⁻¹ * y⁻¹ ∈ Subgroup.zpowers t :=
    fun u hu => (F6_H d h31 h33).1 u hu y hyT
  have hcHom : ∀ u ∈ Op 2 (Cen t), ∀ v ∈ Op 2 (Cen t),
      (u * v) * y * (u * v)⁻¹ * y⁻¹ = (v * y * v⁻¹ * y⁻¹) * (u * y * u⁻¹ * y⁻¹) := by
    intro u hu v hv
    have hcv : u * (v * y * v⁻¹ * y⁻¹) * u⁻¹ = v * y * v⁻¹ * y⁻¹ := by
      rw [← hZT _ (hcZ v hv) u hu]; group
    calc (u * v) * y * (u * v)⁻¹ * y⁻¹
        = (u * (v * y * v⁻¹ * y⁻¹) * u⁻¹) * (u * y * u⁻¹ * y⁻¹) := by group
      _ = _ := by rw [hcv]
  have hcσ : ∀ u ∈ Op 2 (Cen t), (b₂ * u * b₂⁻¹) * y * (b₂ * u * b₂⁻¹)⁻¹ * y⁻¹ = u * y * u⁻¹ * y⁻¹ := by
    intro u hu
    have hcy : Commute b₂ y := S36_comm_of_cen hy2
    have e : b₂⁻¹ * y = y * b₂⁻¹ := hcy.inv_left.eq
    have e' : b₂⁻¹ * y⁻¹ = y⁻¹ * b₂⁻¹ := hcy.inv_left.inv_right.eq
    calc (b₂ * u * b₂⁻¹) * y * (b₂ * u * b₂⁻¹)⁻¹ * y⁻¹
        = b₂ * u * (b₂⁻¹ * y) * b₂ * u⁻¹ * b₂⁻¹ * y⁻¹ := by group
      _ = b₂ * u * (y * b₂⁻¹) * b₂ * u⁻¹ * b₂⁻¹ * y⁻¹ := by rw [e]
      _ = b₂ * u * y * u⁻¹ * (b₂⁻¹ * y⁻¹) := by group
      _ = b₂ * u * y * u⁻¹ * (y⁻¹ * b₂⁻¹) := by rw [e']
      _ = b₂ * (u * y * u⁻¹ * y⁻¹) * b₂⁻¹ := by group
      _ = u * y * u⁻¹ * y⁻¹ := hZb2 _ (hcZ u hu)
  have hσT : ∀ u ∈ Op 2 (Cen t), b₂ * u * b₂⁻¹ ∈ Op 2 (Cen t) :=
    fun u hu => S36_op2_conj hb2Ct hu
  obtain ⟨x₁, hx₁⟩ : ∃ g : G, g = b₂ * x * b₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ g : G, g = b₂ * x₁ * b₂⁻¹ := ⟨_, rfl⟩
  have hxT1 : x₁ ∈ Op 2 (Cen t) := by rw [hx₁]; exact hσT x hxT
  have hxT2 : x₂ ∈ Op 2 (Cen t) := by rw [hx₂]; exact hσT x₁ hxT1
  have p2' : b₂ * (b₂ * b₂) = 1 := (pow_three b₂).symm.trans p2
  have hσx₂ : b₂ * x₂ * b₂⁻¹ = x := by
    rw [hx₂, hx₁]
    calc b₂ * (b₂ * (b₂ * x * b₂⁻¹) * b₂⁻¹) * b₂⁻¹
        = (b₂ * (b₂ * b₂)) * x * (b₂ * (b₂ * b₂))⁻¹ := by group
      _ = x := by rw [p2']; simp
  have hq1 : x₁ * y * x₁⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    rw [hx₁]; exact hcσ x hxT
  have hq2 : x₂ * y * x₂⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    rw [hx₂]; exact (hcσ x₁ hxT1).trans hq1
  obtain ⟨N, hN⟩ : ∃ g : G, g = x * x₁ * x₂ := ⟨_, rfl⟩
  have hNT : N ∈ Op 2 (Cen t) := by rw [hN]; exact mul_mem (mul_mem hxT hxT1) hxT2
  have hN' : N = x * (x₁ * x₂) := by rw [hN, mul_assoc]
  have hb1x : Commute b₁ x := S36_comm_of_cen hx1
  have hb1x1 : Commute b₁ x₁ := by
    rw [hx₁]; exact (Commute.mul_right hcom hb1x).mul_right hcom.inv_right
  have hb1x2 : Commute b₁ x₂ := by
    rw [hx₂]; exact (Commute.mul_right hcom hb1x1).mul_right hcom.inv_right
  have hCb1N : Commute b₁ N := by
    rw [hN]; exact (Commute.mul_right hb1x hb1x1).mul_right hb1x2
  have hσN : b₂ * N * b₂⁻¹ = x₁ * x₂ * x := by
    rw [hN, show b₂ * (x * x₁ * x₂) * b₂⁻¹ = (b₂ * x * b₂⁻¹) * (b₂ * x₁ * b₂⁻¹) * (b₂ * x₂ * b₂⁻¹) by group, hσx₂, ← hx₁, ← hx₂]

  obtain ⟨w, hw⟩ : ∃ g : G, g = N⁻¹ * x⁻¹ * N * x := ⟨_, rfl⟩
  have hwZ : w ∈ Subgroup.zpowers t := by
    have h := (F6_H d h31 h33).1 N⁻¹ (Subgroup.inv_mem _ hNT) x⁻¹ (Subgroup.inv_mem _ hxT)
    rw [inv_inv, inv_inv] at h
    rw [hw]; exact h
  have hσN' : b₂ * N * b₂⁻¹ = N * w := by
    rw [hσN, hw, hN]; group
  have hσw : b₂ * w * b₂⁻¹ = w := hZb2 w hwZ
  have hσσN : b₂ * (b₂ * N * b₂⁻¹) * b₂⁻¹ = N * w * w := by
    rw [hσN', show b₂ * (N * w) * b₂⁻¹ = (b₂ * N * b₂⁻¹) * (b₂ * w * b₂⁻¹) by group, hσN', hσw]
  have hσσσN : b₂ * (b₂ * (b₂ * N * b₂⁻¹) * b₂⁻¹) * b₂⁻¹ = N * w * w * w := by
    rw [hσσN, show b₂ * (N * w * w) * b₂⁻¹
        = (b₂ * N * b₂⁻¹) * (b₂ * w * b₂⁻¹) * (b₂ * w * b₂⁻¹) by group, hσN', hσw]
  have hσσσN' : b₂ * (b₂ * (b₂ * N * b₂⁻¹) * b₂⁻¹) * b₂⁻¹ = N := by
    calc b₂ * (b₂ * (b₂ * N * b₂⁻¹) * b₂⁻¹) * b₂⁻¹
        = (b₂ * (b₂ * b₂)) * N * (b₂ * (b₂ * b₂))⁻¹ := by group
      _ = N := by rw [p2']; simp
  have hN3 : N * (w * w * w) = N * 1 := by
    calc N * (w * w * w) = N * w * w * w := by group
      _ = N := hσσσN.symm.trans hσσσN'
      _ = N * 1 := (mul_one N).symm
  have h3 : w * w * w = 1 := mul_left_cancel hN3
  have hww : w * w = 1 := S36_z_mul_self d.ht hwZ
  have hw1 : w = 1 := by
    calc w = w * w * w * (w * w)⁻¹ := by group
      _ = 1 := by rw [h3, hww, inv_one, mul_one]
  have hNb2 : b₂ * N * b₂⁻¹ = N := by rw [hσN', hw1, mul_one]
  have hCb2N : Commute b₂ N := mul_inv_eq_iff_eq_mul.1 hNb2
  have hCN : Commute (b₁ * b₂) N := Commute.mul_left hCb1N hCb2N
  have hNZ : N ∈ Subgroup.zpowers t := by
    have hNc : N ∈ Op 2 (Cen t) ⊓ Cen (b₁ * b₂) :=
      Subgroup.mem_inf.2 ⟨hNT, S36_mem_cen_of hCN⟩
    rw [(F6_CT_c d h31 h33).1] at hNc
    exact hNc
  have hcN : N * y * N⁻¹ * y⁻¹ = 1 := by
    have hNy : N * y = y * N := hZT N hNZ y hyT
    rw [hNy]; group
  have hcN2 : N * y * N⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by
    rw [hN', hcHom x hxT _ (mul_mem hxT1 hxT2), hcHom x₁ hxT1 x₂ hxT2, hq1, hq2]
  have hfin : x * y * x⁻¹ * y⁻¹ = 1 := by
    have hqZ : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers t := hcZ x hxT
    have hqq := S36_z_mul_self d.ht hqZ
    have hq3 : (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [← hcN2]; exact hcN
    set q := x * y * x⁻¹ * y⁻¹ with hq
    calc q = q * q * q * (q * q)⁻¹ := by group
      _ = 1 := by rw [hq3, hqq, inv_one, mul_one]
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hfin, one_mul]

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
