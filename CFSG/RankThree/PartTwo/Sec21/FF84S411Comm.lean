module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411Rstar

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {s t : ↥S} {b : G}

abbrev Rstar (S : Subgroup G) (t : G) : Subgroup G :=
  Op 2 (Cen t) ⊓ Nor (S ⊓ Op 2 (Cen t))

@[expose] noncomputable def vecOf (e : ↥S ≃* Multiplicative F6) (x : G) : F6 := by
  classical exact if h : x ∈ S then Multiplicative.toAdd (e ⟨x, h⟩) else 0

theorem vecOf_of_mem {x : G} (h : x ∈ S) : vecOf e x = Multiplicative.toAdd (e ⟨x, h⟩) := by
  simp [vecOf, h]

theorem vecOf_mul {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    vecOf e (x * y) = vecOf e x + vecOf e y := by
  rw [vecOf_of_mem (S.mul_mem hx hy), vecOf_of_mem hx, vecOf_of_mem hy]
  exact toAdd_e_mul (e := e) ⟨x, hx⟩ ⟨y, hy⟩

theorem vecOf_conj (H : OmSet S e ψ) (m : ↥(Nor S)) {x : G} (hx : x ∈ S) :
    vecOf e ((m : G) * x * (m : G)⁻¹) = ψ m • vecOf e x := by
  rw [vecOf_of_mem hx, vecOf_of_mem ((Subgroup.mem_normalizer_iff.1 m.2 x).1 hx)]
  exact (H.smul_eq m ⟨x, hx⟩).symm

theorem vecOf_inv {x : G} (hx : x ∈ S) : vecOf e x⁻¹ = vecOf e x := by
  have h : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    exact congrArg Subtype.val (sq_S e ⟨x, hx⟩)
  rw [h]

theorem vecOf_one : vecOf e (1 : G) = 0 := by
  rw [vecOf_of_mem S.one_mem]
  show Multiplicative.toAdd (e 1) = 0
  simp

theorem eq_one_or_of_vec (het : Multiplicative.toAdd (e t) = tau0) {x : G} (hx : x ∈ S)
    (h : vecOf e x = 0 ∨ vecOf e x = tau0) : x = 1 ∨ x = (t : G) := by
  rw [vecOf_of_mem hx] at h
  rcases h with h | h
  · left
    exact congrArg Subtype.val (eq_one_of_toAdd_e_zero (e := e) h)
  · right
    rw [← het] at h
    exact congrArg Subtype.val ((toAdd_e_eq_iff (e := e) _ t).1 h)

@[expose] def prW (x : F6) : F6 := x + polarMinus x sig0 • tau0

theorem prW_add : ∀ x y : F6, prW (x + y) = prW x + prW y := by decide +kernel

theorem prW_zero : prW 0 = 0 := by decide

theorem prW_tau0 : prW tau0 = 0 := by decide

theorem prW_eq_zero : ∀ x : F6, prW x = 0 → x = 0 ∨ x = tau0 := by decide +kernel

theorem prW_mem : ∀ x : F6, polarMinus x tau0 = 0 →
    polarMinus (prW x) sig0 = 0 ∧ polarMinus (prW x) tau0 = 0 := by decide +kernel

theorem F6_neg : ∀ x : F6, -x = x := by decide +kernel

theorem prW_smul_E (hE : Nat.card Eτ = 16) {g : OmG} (hg : g ∈ Eτ) {x : F6}
    (hx : polarMinus x tau0 = 0) : prW (g • x) = prW x := by
  have h := (eich_move hE hg x).2 hx
  have h2 : g • x = x + (g • x - x) := by abel
  rw [h2, prW_add]
  rcases h with h | h
  · rw [h, prW_zero, add_zero]
  · rw [h, prW_tau0, add_zero]

theorem polarMinus_smul (g : OmG) (x y : F6) : polarMinus (g • x) (g • y) = polarMinus x y := by
  have h1 := qMinus_add (g • x) (g • y)
  have h2 := qMinus_add x y
  have h3 : g • x + g • y = g • (x + y) := (smul_add g x y).symm
  rw [h3] at h1
  have e1 : ∀ v : F6, qMinus (g • v) = qMinus v := fun v => qMinus_apply_of_mem g.2 v
  rw [e1, e1, e1, h2] at h1
  exact (add_left_cancel h1).symm

theorem prW_smul_P2 {h : OmG} (hh : h ∈ P2) (x : F6) : prW (h • x) = h • prW x := by
  have h1 : h • sig0 = sig0 := (mem_P2.1 hh).1
  have h2 : h • tau0 = tau0 := (mem_P2.1 hh).2
  have hp : polarMinus (h • x) sig0 = polarMinus x sig0 := by
    have := polarMinus_smul h x sig0
    rwa [h1] at this
  unfold prW
  rw [hp, smul_add]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (polarMinus x sig0) with hc | hc <;>
    rw [hc] <;> simp [h2]

@[expose] noncomputable def Fc (e : ↥S ≃* Multiplicative F6) (y₁ y₂ : G) : F6 :=
  prW (vecOf e (y₁ * y₂ * y₁⁻¹ * y₂⁻¹))

section
variable (C : Ctx411 S e ψ s t b)
include C

theorem Ctx411.hE : Nat.card Eτ = 16 := by
  have := (C.hPar qMinus_tau0 tau0_ne_zero).1.2
  show Nat.card ↥(Op 2 (MulAction.stabilizer OmG tau0)) = 16
  rw [this]
  norm_num

theorem Ctx411.E_comm {g g' : OmG} (hg : g ∈ Eτ) (hg' : g' ∈ Eτ) : g * g' = g' * g := by
  haveI := (C.hPar qMinus_tau0 tau0_ne_zero).1.1
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
    (⟨g, hg⟩ : ↥(Op 2 (MulAction.stabilizer OmG tau0))) ⟨g', hg'⟩)

theorem Ctx411.psi_mem_E {y : G} (hy : y ∈ Rstar S (t : G)) :
    ψ ⟨y, C.Rs_le_nor_S hy⟩ ∈ Eτ := C.psi_Rs_mem_E _ hy

theorem Ctx411.comm_mem_S {y₁ y₂ : G} (h₁ : y₁ ∈ Rstar S (t : G)) (h₂ : y₂ ∈ Rstar S (t : G)) :
    y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ S := by
  have e1 := C.psi_mem_E h₁
  have e2 := C.psi_mem_E h₂
  have hn : ψ (⟨y₁, C.Rs_le_nor_S h₁⟩ * ⟨y₂, C.Rs_le_nor_S h₂⟩ * ⟨y₁, C.Rs_le_nor_S h₁⟩⁻¹ *
      ⟨y₂, C.Rs_le_nor_S h₂⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, C.E_comm e1 e2]
    group
  exact (C.H.psi_eq_one_iff _).1 hn

theorem Ctx411.comm_mem_T {y₁ y₂ : G} (h₁ : y₁ ∈ Rstar S (t : G)) (h₂ : y₂ ∈ Rstar S (t : G)) :
    y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Op 2 (Cen (t : G)) :=
  mul_mem (mul_mem (mul_mem (Subgroup.mem_inf.1 h₁).1 (Subgroup.mem_inf.1 h₂).1)
    (inv_mem (Subgroup.mem_inf.1 h₁).1)) (inv_mem (Subgroup.mem_inf.1 h₂).1)

theorem Ctx411.vec_perp {x : G} (hxS : x ∈ S) (hxT : x ∈ Op 2 (Cen (t : G))) :
    polarMinus (vecOf e x) tau0 = 0 := by
  rw [vecOf_of_mem hxS]
  exact (C.R_perp ⟨x, hxS⟩).1 hxT

theorem Ctx411.vec_conj_Rs {y c : G} (hy : y ∈ Rstar S (t : G)) (hc : c ∈ S) :
    vecOf e (y * c * y⁻¹) = ψ ⟨y, C.Rs_le_nor_S hy⟩ • vecOf e c :=
  vecOf_conj C.H ⟨y, C.Rs_le_nor_S hy⟩ hc

theorem Ctx411.conj_mem_S {y c : G} (hy : y ∈ Rstar S (t : G)) (hc : c ∈ S) : y * c * y⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 (C.Rs_le_nor_S hy) c).1 hc

theorem Ctx411.comm_R_vec {y r : G} (hy : y ∈ Rstar S (t : G)) (hrS : r ∈ S)
    (hrT : r ∈ Op 2 (Cen (t : G))) :
    vecOf e (r * y * r⁻¹ * y⁻¹) = 0 ∨ vecOf e (r * y * r⁻¹ * y⁻¹) = tau0 := by
  have hmem : y * r⁻¹ * y⁻¹ ∈ S := C.conj_mem_S hy (inv_mem hrS)
  have h1 : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
  rw [h1, vecOf_mul hrS hmem, C.vec_conj_Rs hy (inv_mem hrS), vecOf_inv hrS]
  have hu : polarMinus (vecOf e r) tau0 = 0 := C.vec_perp hrS hrT
  have hg := C.psi_mem_E hy
  have h2 := (eich_move C.hE hg _).2 hu
  have h3 : vecOf e r + ψ ⟨y, C.Rs_le_nor_S hy⟩ • vecOf e r =
      ψ ⟨y, C.Rs_le_nor_S hy⟩ • vecOf e r - vecOf e r := by
    rw [sub_eq_add_neg, F6_neg, add_comm]
  rw [h3]
  exact h2

theorem Ctx411.Fc_mul_left {y₁ y₂ y₃ : G} (h₁ : y₁ ∈ Rstar S (t : G)) (h₂ : y₂ ∈ Rstar S (t : G))
    (h₃ : y₃ ∈ Rstar S (t : G)) : Fc e (y₁ * y₃) y₂ = Fc e y₁ y₂ + Fc e y₃ y₂ := by
  have c32S := C.comm_mem_S h₃ h₂
  have c32T := C.comm_mem_T h₃ h₂
  have c12S := C.comm_mem_S h₁ h₂
  have hid : (y₁ * y₃) * y₂ * (y₁ * y₃)⁻¹ * y₂⁻¹ =
      (y₁ * (y₃ * y₂ * y₃⁻¹ * y₂⁻¹) * y₁⁻¹) * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group
  unfold Fc
  rw [hid, vecOf_mul (C.conj_mem_S h₁ c32S) c12S, C.vec_conj_Rs h₁ c32S, prW_add,
    prW_smul_E C.hE (C.psi_mem_E h₁) (C.vec_perp c32S c32T)]
  exact add_comm _ _

theorem Ctx411.Fc_mul_right {y₁ y₂ y₃ : G} (h₁ : y₁ ∈ Rstar S (t : G)) (h₂ : y₂ ∈ Rstar S (t : G))
    (h₃ : y₃ ∈ Rstar S (t : G)) : Fc e y₁ (y₂ * y₃) = Fc e y₁ y₂ + Fc e y₁ y₃ := by
  have c13S := C.comm_mem_S h₁ h₃
  have c13T := C.comm_mem_T h₁ h₃
  have c12S := C.comm_mem_S h₁ h₂
  have hid : y₁ * (y₂ * y₃) * y₁⁻¹ * (y₂ * y₃)⁻¹ =
      (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (y₂ * (y₁ * y₃ * y₁⁻¹ * y₃⁻¹) * y₂⁻¹) := by group
  unfold Fc
  rw [hid, vecOf_mul c12S (C.conj_mem_S h₂ c13S), C.vec_conj_Rs h₂ c13S, prW_add,
    prW_smul_E C.hE (C.psi_mem_E h₂) (C.vec_perp c13S c13T)]

theorem Ctx411.Fc_self (y : G) : Fc e y y = 0 := by
  unfold Fc
  rw [show y * y * y⁻¹ * y⁻¹ = 1 by group, vecOf_one, prW_zero]

theorem Ctx411.R_le_Rstar {r : G} (hr : r ∈ S ⊓ Op 2 (Cen (t : G))) : r ∈ Rstar S (t : G) :=
  C.R_le_Rs hr

theorem Ctx411.Fc_congr_left {y₁ y₂ y₃ : G} (h₁ : y₁ ∈ Rstar S (t : G))
    (h₂ : y₂ ∈ Rstar S (t : G)) (h₃ : y₃ ∈ Rstar S (t : G))
    (h : ψ ⟨y₁, C.Rs_le_nor_S h₁⟩ = ψ ⟨y₂, C.Rs_le_nor_S h₂⟩) : Fc e y₁ y₃ = Fc e y₂ y₃ := by
  have hr1 : ψ (⟨y₁, C.Rs_le_nor_S h₁⟩⁻¹ * ⟨y₂, C.Rs_le_nor_S h₂⟩) = 1 := by
    rw [map_mul, map_inv, h]
    group
  have hrS : y₁⁻¹ * y₂ ∈ S := (C.H.psi_eq_one_iff _).1 hr1
  have hrT : y₁⁻¹ * y₂ ∈ Op 2 (Cen (t : G)) :=
    mul_mem (inv_mem (Subgroup.mem_inf.1 h₁).1) (Subgroup.mem_inf.1 h₂).1
  have hrR : y₁⁻¹ * y₂ ∈ Rstar S (t : G) := C.R_le_Rstar (Subgroup.mem_inf.2 ⟨hrS, hrT⟩)
  have h2 : y₂ = y₁ * (y₁⁻¹ * y₂) := by group
  have h3 := C.Fc_mul_left h₁ h₃ hrR
  rw [← h2] at h3
  rw [h3]
  have h4 : Fc e (y₁⁻¹ * y₂) y₃ = 0 := by
    unfold Fc
    rcases C.comm_R_vec h₃ hrS hrT with h5 | h5
    · rw [h5, prW_zero]
    · rw [h5, prW_tau0]
  rw [h4, add_zero]

theorem Ctx411.Fc_congr_right {y₁ y₂ y₃ : G} (h₁ : y₁ ∈ Rstar S (t : G))
    (h₂ : y₂ ∈ Rstar S (t : G)) (h₃ : y₃ ∈ Rstar S (t : G))
    (h : ψ ⟨y₁, C.Rs_le_nor_S h₁⟩ = ψ ⟨y₂, C.Rs_le_nor_S h₂⟩) : Fc e y₃ y₁ = Fc e y₃ y₂ := by
  have hr1 : ψ (⟨y₁, C.Rs_le_nor_S h₁⟩⁻¹ * ⟨y₂, C.Rs_le_nor_S h₂⟩) = 1 := by
    rw [map_mul, map_inv, h]
    group
  have hrS : y₁⁻¹ * y₂ ∈ S := (C.H.psi_eq_one_iff _).1 hr1
  have hrT : y₁⁻¹ * y₂ ∈ Op 2 (Cen (t : G)) :=
    mul_mem (inv_mem (Subgroup.mem_inf.1 h₁).1) (Subgroup.mem_inf.1 h₂).1
  have hrR : y₁⁻¹ * y₂ ∈ Rstar S (t : G) := C.R_le_Rstar (Subgroup.mem_inf.2 ⟨hrS, hrT⟩)
  have h2 : y₂ = y₁ * (y₁⁻¹ * y₂) := by group
  have h3 := C.Fc_mul_right h₃ h₁ hrR
  rw [← h2] at h3
  rw [h3]
  have h4 : Fc e y₃ (y₁⁻¹ * y₂) = 0 := by
    unfold Fc
    have hmem := C.comm_mem_S (C.R_le_Rstar (Subgroup.mem_inf.2 ⟨hrS, hrT⟩)) h₃
    have hinv : y₃ * (y₁⁻¹ * y₂) * y₃⁻¹ * (y₁⁻¹ * y₂)⁻¹ =
        ((y₁⁻¹ * y₂) * y₃ * (y₁⁻¹ * y₂)⁻¹ * y₃⁻¹)⁻¹ := by group
    rw [hinv, vecOf_inv hmem]
    rcases C.comm_R_vec h₃ hrS hrT with h5 | h5
    · rw [h5, prW_zero]
    · rw [h5, prW_tau0]
  rw [h4, add_zero]

theorem Ctx411.Fc_conj {y₁ y₂ m : G} (h₁ : y₁ ∈ Rstar S (t : G)) (h₂ : y₂ ∈ Rstar S (t : G))
    (hmN : m ∈ Nor S) (hmt : m ∈ Cen (t : G)) (hP : ψ ⟨m, hmN⟩ ∈ P2) :
    Fc e (m * y₁ * m⁻¹) (m * y₂ * m⁻¹) = ψ ⟨m, hmN⟩ • Fc e y₁ y₂ := by
  have cS := C.comm_mem_S h₁ h₂
  have hid : (m * y₁ * m⁻¹) * (m * y₂ * m⁻¹) * (m * y₁ * m⁻¹)⁻¹ * (m * y₂ * m⁻¹)⁻¹ =
      m * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * m⁻¹ := by group
  unfold Fc
  rw [hid, vecOf_conj C.H ⟨m, hmN⟩ cS, prW_smul_P2 hP]

end

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
