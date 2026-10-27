module

public import CFSG.Quasithin.EmptyFaithful.S153PDef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise MatrixGroups

namespace S153P

section Defs

variable {G : Type} [Group G]

namespace PA2

theorem sc_of {g a b : G} (h : g * a * g⁻¹ = b) : SemiconjBy g a b := mul_inv_eq_iff_eq_mul.1 h

theorem eq_of_sc {g a b : G} (h : SemiconjBy g a b) : g * a * g⁻¹ = b := mul_inv_eq_iff_eq_mul.2 h

theorem commute_of_sc {g a a' b b' : G} (ha : SemiconjBy g a a') (hb : SemiconjBy g b b')
    (h : Commute a' b') : Commute a b := by
  have : g * (a * b) = g * (b * a) := by
    calc g * (a * b) = (g * a) * b := (mul_assoc _ _ _).symm
      _ = (a' * g) * b := by rw [ha.eq]
      _ = a' * (g * b) := mul_assoc _ _ _
      _ = a' * (b' * g) := by rw [hb.eq]
      _ = (a' * b') * g := (mul_assoc _ _ _).symm
      _ = (b' * a') * g := by rw [h.eq]
      _ = b' * (a' * g) := mul_assoc _ _ _
      _ = b' * (g * a) := by rw [ha.eq]
      _ = (b' * g) * a := (mul_assoc _ _ _).symm
      _ = (g * b) * a := by rw [hb.eq]
      _ = g * (b * a) := mul_assoc _ _ _
  exact mul_left_cancel this

structure Rel (z p y : G) : Prop where
  z_sq : z * z = 1
  p_sq : p * p = 1
  comm : z * p = p * z
  y_z : y * z * y⁻¹ = z * p
  y_p : y * p * y⁻¹ = z

namespace Rel

variable {z p y : G} (h : Rel z p y)
include h

theorem zq : z * (z * p) = p := by rw [← mul_assoc, h.z_sq, one_mul]

theorem qp : z * p * p = z := by rw [mul_assoc, h.p_sq, mul_one]

theorem qz : z * p * z = p := by rw [h.comm, mul_assoc, h.z_sq, mul_one]

theorem scy_z : SemiconjBy y z (z * p) := sc_of h.y_z

theorem scy_p : SemiconjBy y p z := sc_of h.y_p

theorem scy_q : SemiconjBy y (z * p) p := by
  have := SemiconjBy.mul_right h.scy_z h.scy_p
  rwa [h.qz] at this

theorem scyi_z : SemiconjBy y⁻¹ z p := h.scy_p.inv_symm_left

theorem scyi_p : SemiconjBy y⁻¹ p (z * p) := h.scy_q.inv_symm_left

end Rel

structure YU (z p y u₀ : G) : Prop extends Rel z p y where
  u_z : u₀ * z * u₀⁻¹ = z
  u_p : u₀ * p * u₀⁻¹ = z * p

namespace YU

variable {z p y u₀ : G} (h : YU z p y u₀)
include h

theorem scu_z : SemiconjBy u₀ z z := sc_of h.u_z

theorem scu_p : SemiconjBy u₀ p (z * p) := sc_of h.u_p

theorem scu_q : SemiconjBy u₀ (z * p) p := by
  have := SemiconjBy.mul_right h.scu_z h.scu_p
  rwa [h.toRel.zq] at this

theorem scui_p : SemiconjBy u₀⁻¹ p (z * p) := h.scu_q.inv_symm_left

theorem scui_q : SemiconjBy u₀⁻¹ (z * p) p := h.scu_p.inv_symm_left

theorem scu'_z : SemiconjBy (y⁻¹ * u₀ * y) z (z * p) :=
  SemiconjBy.mul_left (SemiconjBy.mul_left h.toRel.scyi_p h.scu_q) h.toRel.scy_z

theorem scu'_p : SemiconjBy (y⁻¹ * u₀ * y) p p :=
  SemiconjBy.mul_left (SemiconjBy.mul_left h.toRel.scyi_z h.scu_z) h.toRel.scy_p

theorem scu'_q : SemiconjBy (y⁻¹ * u₀ * y) (z * p) z := by
  have := SemiconjBy.mul_right h.scu'_z h.scu'_p
  rwa [h.toRel.qp] at this

theorem scj_z : SemiconjBy ((y⁻¹ * u₀ * y) * u₀) z (z * p) := SemiconjBy.mul_left h.scu'_z h.scu_z

theorem scj_p : SemiconjBy ((y⁻¹ * u₀ * y) * u₀) p z := SemiconjBy.mul_left h.scu'_q h.scu_p

theorem scj_q : SemiconjBy ((y⁻¹ * u₀ * y) * u₀) (z * p) p := by
  have := SemiconjBy.mul_right h.scj_z h.scj_p
  rwa [h.toRel.qz] at this

theorem scji_z : SemiconjBy ((y⁻¹ * u₀ * y) * u₀)⁻¹ z p := h.scj_p.inv_symm_left

theorem scji_p : SemiconjBy ((y⁻¹ * u₀ * y) * u₀)⁻¹ p (z * p) := h.scj_q.inv_symm_left

theorem scc_z : SemiconjBy (y * ((y⁻¹ * u₀ * y) * u₀)⁻¹) z z :=
  SemiconjBy.mul_left h.toRel.scy_p h.scji_z

theorem scc_p : SemiconjBy (y * ((y⁻¹ * u₀ * y) * u₀)⁻¹) p p :=
  SemiconjBy.mul_left h.toRel.scy_q h.scji_p

theorem comm_cuc {c : G} (hcz : Commute c z) (hcp : Commute c p) :
    Commute (c⁻¹ * u₀ * c * u₀⁻¹) p := by
  have hcq : SemiconjBy c (z * p) (z * p) := Commute.mul_right hcz hcp
  have hci : SemiconjBy c⁻¹ p p := Commute.inv_left hcp
  exact SemiconjBy.mul_left (SemiconjBy.mul_left (SemiconjBy.mul_left hci h.scu_q) hcq) h.scui_p

theorem comm_rr {r : G} (hrz : Commute r z) (hrp : Commute r p) :
    Commute (u₀ * r * u₀⁻¹ * r⁻¹) p := by
  have hrq : SemiconjBy r (z * p) (z * p) := Commute.mul_right hrz hrp
  have hri : SemiconjBy r⁻¹ p p := Commute.inv_left hrp
  exact SemiconjBy.mul_left (SemiconjBy.mul_left (SemiconjBy.mul_left h.scu_q hrq) h.scui_p) hri

theorem split {u : G} (hu : u * p * u⁻¹ = z * p) : Commute (u₀⁻¹ * u) p :=
  SemiconjBy.mul_left h.scui_q (sc_of hu)

end YU

section Abs

variable {U Z Mc : Subgroup G} {z y : G}

theorem y_zp (z y : G) : y * zp z y * y⁻¹ = z := by simp only [zp]; group

theorem conj_cancel (y f : G) : y * (y⁻¹ * f * y) * y⁻¹ = f := by group

theorem commute_conj_zp_iff {x : G} : Commute (y * x * y⁻¹) z ↔ Commute x (zp z y) := by
  have h := SemiconjBy.conj_iff (a := x) (x := zp z y) (y := zp z y) (b := y)
  rw [y_zp] at h
  exact h

theorem zp_comm (A : Abs56 U Z Mc z y) : z * zp z y = zp z y * z := (A.Z_central _ A.zp_mem).symm

theorem zp_sq (A : Abs56 U Z Mc z y) : zp z y * zp z y = 1 := by
  have : zp z y * zp z y = y⁻¹ * (z * z) * y := by simp only [zp]; group
  rw [this, A.z_sq]
  group

theorem zp_ne_one (A : Abs56 U Z Mc z y) : zp z y ≠ 1 := by
  intro h
  apply A.z_ne
  calc z = y * zp z y * y⁻¹ := (y_zp z y).symm
    _ = 1 := by rw [h]; group

theorem rel (A : Abs56 U Z Mc z y) : Rel z (zp z y) y where
  z_sq := A.z_sq
  p_sq := zp_sq A
  comm := zp_comm A
  y_z := A.yz
  y_p := y_zp z y

theorem yu (A : Abs56 U Z Mc z y) {u₀ : G} (hu₀ : u₀ ∈ U) (h₀ : ⁅u₀, zp z y⁆ = z) :
    YU z (zp z y) y u₀ :=
  { rel A with
    u_z := mul_inv_eq_iff_eq_mul.2 (A.Z_central u₀ hu₀)
    u_p := mul_inv_eq_iff_eq_mul.1 h₀ }

theorem memZ (A : Abs56 U Z Mc z y) {x : G} : x ∈ Z ↔ x = 1 ∨ x = z := by
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact A.z_sq
  rw [A.Z_eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul]
      simp [hz2]
    · right
      rw [zpow_add, zpow_mul]
      simp [hz2]
  · rintro (h | h)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩

theorem mem_Mc (A : Abs56 U Z Mc z y) {g : G} : g ∈ Mc ↔ Commute g z := by
  rw [A.Mc_eq, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h z (by rw [SetLike.mem_coe, memZ A]; exact Or.inr rfl)).symm
  · intro h t ht
    rw [SetLike.mem_coe, memZ A] at ht
    rcases ht with ht | ht
    · rw [ht]; simp
    · rw [ht]; exact h.symm

theorem mem_Fg (A : Abs56 U Z Mc z y) {x : G} : x ∈ Fg U Mc y ↔ x ∈ U ∧ Commute x (zp z y) := by
  rw [Subgroup.mem_inf, mem_conjSubgroup_iff, mem_Mc A, commute_conj_zp_iff]

theorem Z_le_Fg (A : Abs56 U Z Mc z y) : Z ≤ Fg U Mc y := by
  intro x hx
  rcases (memZ A).1 hx with h | h
  · rw [h]; exact one_mem _
  · rw [h, mem_Fg A]
    exact ⟨A.z_mem, zp_comm A⟩

theorem Z_le_Xg (A : Abs56 U Z Mc z y) : Z ≤ Xg U Mc y := by
  intro x hx
  rcases (memZ A).1 hx with h | h
  · rw [h]; exact one_mem _
  · rw [h, Xg, mem_conjSubgroup_iff, A.yz, mem_Fg A]
    exact ⟨mul_mem A.z_mem A.zp_mem, Commute.mul_left (zp_comm A) (Commute.refl _)⟩

theorem Xg_cent (A : Abs56 U Z Mc z y) {x : G} (hx : x ∈ Xg U Mc y) :
    Commute x z ∧ Commute x (zp z y) := by
  have hw : y * x * y⁻¹ ∈ Fg U Mc y := mem_conjSubgroup_iff.1 hx
  obtain ⟨hwU, hwp⟩ := (mem_Fg A).1 hw
  have hxp : Commute x (zp z y) := commute_conj_zp_iff.1 (A.Z_central _ hwU)
  have hxq : Commute x (z * zp z y) :=
    commute_of_sc (SemiconjBy.conj_mk y x) (rel A).scy_q hwp
  have h2 := Commute.mul_right hxq (Commute.inv_right hxp)
  rw [mul_inv_cancel_right] at h2
  exact ⟨h2, hxp⟩

theorem mem_cent_pair {a b x : G} :
    x ∈ Subgroup.centralizer ({a, b} : Set G) ↔ Commute x a ∧ Commute x b := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  exact and_congr ⟨fun h => h.symm, fun h => h.symm⟩ ⟨fun h => h.symm, fun h => h.symm⟩

theorem Ng_cent (A : Abs56 U Z Mc z y) {r : G} (hr : r ∈ Ng U Mc y) :
    Commute r z ∧ Commute r (zp z y) := by
  have key : Ng U Mc y ≤ Subgroup.centralizer ({z, zp z y} : Set G) := by
    refine sup_le (fun f hf => ?_) (fun x hx => ?_)
    · obtain ⟨hfU, hfp⟩ := (mem_Fg A).1 hf
      exact mem_cent_pair.2 ⟨A.Z_central f hfU, hfp⟩
    · exact mem_cent_pair.2 (Xg_cent A hx)
  exact mem_cent_pair.1 (key hr)

theorem U_split (A : Abs56 U Z Mc z y) {u₀ : G} (hu₀ : u₀ ∈ U) (h₀ : ⁅u₀, zp z y⁆ = z) {u : G}
    (hu : u ∈ U) : Commute u (zp z y) ∨ Commute (u₀⁻¹ * u) (zp z y) := by
  have hY := yu A hu₀ h₀
  rcases (memZ A).1 (A.U_comm u hu _ A.zp_mem) with h | h
  · left
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  · right
    apply hY.split
    have h' : u * zp z y * u⁻¹ * (zp z y)⁻¹ = z := h
    exact mul_inv_eq_iff_eq_mul.1 h'

end Abs

end PA2

namespace Abs56

variable {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem exists_u₀ : ∃ u₀ ∈ U, ⁅u₀, zp z y⁆ = z := by
  have hnZ : zp z y ∉ Z := by
    rw [PA2.memZ A]
    rintro (h | h)
    · exact PA2.zp_ne_one A h
    · exact A.zp_ne h
  by_contra hcon
  push Not at hcon
  apply hnZ
  apply A.U_center _ A.zp_mem
  intro v hv
  rcases (PA2.memZ A).1 (A.U_comm v hv _ A.zp_mem) with h | h
  · rw [← commutatorElement_inv, h, inv_one]
  · exact absurd h (hcon v hv)

theorem pts {u₀ : G} (hu₀ : u₀ ∈ U) (h : ⁅u₀, zp z y⁆ = z) :
    Pts z (zp z y) u₀ (y⁻¹ * u₀ * y) := by
  have hY := PA2.yu A hu₀ h
  exact
    { z_sq := A.z_sq
      zp_sq := PA2.zp_sq A
      comm := PA2.zp_comm A
      z_ne_one := A.z_ne
      zp_ne_one := PA2.zp_ne_one A
      z_ne_zp := fun h => A.zp_ne h.symm
      u₀_z := hY.u_z
      u₀_zp := hY.u_p
      u₀'_z := PA2.eq_of_sc hY.scu'_z
      u₀'_zp := PA2.eq_of_sc hY.scu'_p }

set_option linter.unusedSectionVars false in
theorem u₀'_mem {u₀ : G} (hu₀ : u₀ ∈ U) : y⁻¹ * u₀ * y ∈ conjSubgroup U y := by
  rw [mem_conjSubgroup_iff]
  have e : y * (y⁻¹ * u₀ * y) * y⁻¹ = u₀ := PA2.conj_cancel y u₀
  rwa [e]

variable {u₀ : G} (hu₀ : u₀ ∈ U) (h₀ : ⁅u₀, zp z y⁆ = z)
include hu₀ h₀

theorem gen : ∀ x ∈ Jg U y, x ∈ Ng U Mc y ⊔ Subgroup.closure ({u₀, y⁻¹ * u₀ * y} : Set G) := by
  intro x hx
  have hu₀P : u₀ ∈ Ng U Mc y ⊔ Subgroup.closure ({u₀, y⁻¹ * u₀ * y} : Set G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))
  have hu₀'P : y⁻¹ * u₀ * y ∈ Ng U Mc y ⊔ Subgroup.closure ({u₀, y⁻¹ * u₀ * y} : Set G) :=
    Subgroup.mem_sup_right
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hF : ∀ f ∈ Fg U Mc y,
      f ∈ Ng U Mc y ⊔ Subgroup.closure ({u₀, y⁻¹ * u₀ * y} : Set G) :=
    fun f hf => Subgroup.mem_sup_left (Subgroup.mem_sup_left hf)
  have hX : ∀ x ∈ Xg U Mc y,
      x ∈ Ng U Mc y ⊔ Subgroup.closure ({u₀, y⁻¹ * u₀ * y} : Set G) :=
    fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
  have hJ : Jg U y ≤ Ng U Mc y ⊔ Subgroup.closure ({u₀, y⁻¹ * u₀ * y} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun x hx => ?_)
    · rcases PA2.U_split A hu₀ h₀ hu with h | h
      · exact hF u ((PA2.mem_Fg A).2 ⟨hu, h⟩)
      · have hf : u₀⁻¹ * u ∈ Fg U Mc y := (PA2.mem_Fg A).2 ⟨mul_mem (inv_mem hu₀) hu, h⟩
        have := mul_mem hu₀P (hF _ hf)
        rwa [mul_inv_cancel_left] at this
    · have hu : y * x * y⁻¹ ∈ U := mem_conjSubgroup_iff.1 hx
      rcases PA2.U_split A hu₀ h₀ hu with h | h
      · exact hX x (mem_conjSubgroup_iff.2 ((PA2.mem_Fg A).2 ⟨hu, h⟩))
      · have hf : u₀⁻¹ * (y * x * y⁻¹) ∈ Fg U Mc y :=
          (PA2.mem_Fg A).2 ⟨mul_mem (inv_mem hu₀) hu, h⟩
        have hfX : y⁻¹ * (u₀⁻¹ * (y * x * y⁻¹)) * y ∈ Xg U Mc y := by
          rw [Xg, mem_conjSubgroup_iff, PA2.conj_cancel]
          exact hf
        have := mul_mem hu₀'P (hX _ hfX)
        have e : y⁻¹ * u₀ * y * (y⁻¹ * (u₀⁻¹ * (y * x * y⁻¹)) * y) = x := by group
        rwa [e] at this
  exact hJ hx

set_option linter.unusedSectionVars false in
theorem u₀_sq : u₀ * u₀ ∈ Ng U Mc y :=
  Subgroup.mem_sup_left (PA2.Z_le_Fg A (A.U_sq u₀ hu₀))

set_option linter.unusedSectionVars false in
theorem u₀'_sq : (y⁻¹ * u₀ * y) * (y⁻¹ * u₀ * y) ∈ Ng U Mc y := by
  have e : (y⁻¹ * u₀ * y) * (y⁻¹ * u₀ * y) = y⁻¹ * (u₀ * u₀) * y := by group
  rw [e]
  apply Subgroup.mem_sup_right
  rw [Xg, mem_conjSubgroup_iff, PA2.conj_cancel]
  exact PA2.Z_le_Fg A (A.U_sq u₀ hu₀)

end Abs56

end Defs

end S153P

end CFSG.Quasithin
