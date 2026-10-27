module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Sq

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D}

structure Hyp2 (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  gold : GoldHyp A B
  natural : IsNaturalAt A (A ⊓ B) z V
  central : ∀ y ∈ B, y * z * y⁻¹ = z
  U_le : conjClosure V B ≤ pCoreOf 2 B
  comm_U : ⁅conjClosure V B, conjClosure V B⁆ = Subgroup.zpowers z
  comm_Q : ⁅conjClosure V B, pCoreOf 2 B⁆ = Subgroup.zpowers z
  sq_U : ∀ x ∈ conjClosure V B, x * x ∈ Subgroup.zpowers z
  omega : ∀ ω ∈ centerOf (A ⊓ B), ω ^ 2 = 1 → ω = 1 ∨ ω = z

variable [Finite D] in
theorem Hyp2.of_critDist_two (h : GoldHyp A B) (h32 : 32 ≤ Nat.card ↥(A ⊓ B)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt A (A ⊓ B) z V) (hb : critDist (A ⊔ B) A B V = 2)
    (hA : ∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1) :
    Hyp2 A B z V where
  gold := h
  natural := hn
  central := centralizes_of_critDist_two h hn hb
  U_le := (critDist_two_structure_of_natural h hn hb).2.1
  comm_U := (two_structure_of_critDist_two h hn hb).2.2.2
  comm_Q := (two_structure_of_critDist_two h hn hb).2.2.1
  sq_U := fun _ hx => sq_mem_of_conjClosure h hn hb hx
  omega := ((omega_labelling_iff h h32 hn hb).2).1 hA

namespace Hyp2

variable {z : D} {V : Subgroup D} (h : Hyp2 A B z V)

include h

theorem z_comm {g : D} (hg : g ∈ B) : g * z = z * g := mul_eq_of_conj_eq (h.central g hg)

theorem mem_zpowers {w : D} (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact zpow_eq_one_or_self h.natural.z_sq k

theorem zpowers_comm {g w : D} (hg : g ∈ B) (hw : w ∈ Subgroup.zpowers z) : g * w = w * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ((show Commute g z from h.z_comm hg).zpow_right k).eq

theorem card_zpowers : Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime h.natural.z_sq h.natural.z_ne

theorem z_mem_U : z ∈ conjClosure V B := le_conjClosure V B h.natural.z_mem_V

variable [Finite D] in
theorem QA_le_T : pCoreOf 2 A ≤ A ⊓ B := h.gold.pCoreOf_left_le

variable [Finite D] in
theorem QB_le_T : pCoreOf 2 B ≤ A ⊓ B := h.gold.pCoreOf_right_le

variable [Finite D] in
theorem U_le_T : conjClosure V B ≤ A ⊓ B := h.U_le.trans h.QB_le_T

theorem isPGroup_T : IsPGroup 2 ↥(A ⊓ B) := h.gold.amalgam.toIsGoldschmidtVTriple.isPGroup_inf

theorem comm_UU {u w : D} (hu : u ∈ conjClosure V B) (hw : w ∈ conjClosure V B) :
    u * w * u⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
  have := Subgroup.commutator_mem_commutator hu hw
  rw [h.comm_U, commutatorElement_def] at this
  exact this

theorem comm_UQ {u q : D} (hu : u ∈ conjClosure V B) (hq : q ∈ pCoreOf 2 B) :
    u * q * u⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  have := Subgroup.commutator_mem_commutator hu hq
  rw [h.comm_Q, commutatorElement_def] at this
  exact this

theorem V_sq {v : D} (hv : v ∈ V) : v * v = 1 := h.natural.mul_self_of_mem hv

end Hyp2

end GoldAmL2S

end F6

end CFSG.Quasithin
