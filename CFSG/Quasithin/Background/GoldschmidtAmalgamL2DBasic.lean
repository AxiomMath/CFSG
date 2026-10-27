module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Label

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2D

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure B2Setup (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  gold : GoldHyp A B
  natural : IsNaturalAt A (A ⊓ B) z V
  central : ∀ y ∈ B, y * z * y⁻¹ = z
  V_le : V ≤ pCoreOf 2 B
  comm_UQ : ⁅conjClosure V B, pCoreOf 2 B⁆ = Subgroup.zpowers z
  comm_UU : ⁅conjClosure V B, conjClosure V B⁆ = Subgroup.zpowers z
  nc : ∃ x ∈ B, ⁅V, conjSub x V⁆ ≠ ⊥

theorem B2Setup.of_critDist_two [Finite D] (h : GoldHyp A B)
    (hn : IsNaturalAt A (A ⊓ B) z V) (hb : critDist (A ⊔ B) A B V = 2) : B2Setup A B z V where
  gold := h
  natural := hn
  central := centralizes_of_critDist_two h hn hb
  V_le := (le_conjClosure V B).trans (critDist_two_structure_of_natural h hn hb).2.1
  comm_UQ := (two_structure_of_critDist_two h hn hb).2.2.1
  comm_UU := (two_structure_of_critDist_two h hn hb).2.2.2
  nc := by
    obtain ⟨-, -, -, x, hxB, -, -, -, -, hcomm, -, hcard, -⟩ :=
      critDist_two_structure_of_natural h hn hb
    refine ⟨x, hxB, fun hbot => ?_⟩
    rw [hbot] at hcomm
    have h1 : Nat.card ↥(V ⊓ conjSub x V) = 1 := by rw [← hcomm]; simp
    omega

namespace B2Setup

variable (s : B2Setup A B z V)

include s

omit s in
theorem closure_comm {S : Set D} (hS : ∀ p ∈ S, ∀ q ∈ S, p * q = q * p) {u w : D}
    (hu : u ∈ Subgroup.closure S) (hw : w ∈ Subgroup.closure S) : u * w = w * u := by
  have h1 : ∀ p ∈ S, ∀ w ∈ Subgroup.closure S, p * w = w * p := by
    intro p hp w hw
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({p} : Set D) := by
      rw [Subgroup.closure_le]
      intro q hq
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hS y hp q hq
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) p rfl)
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({u} : Set D) := by
    rw [Subgroup.closure_le]
    intro q hq
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (h1 q hq y hu).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hw) u rfl)

theorem z_comm {g : D} (hg : g ∈ B) : g * z = z * g := mul_eq_of_conj_eq (s.central g hg)

theorem z_mul_z : z * z = 1 := by
  have := s.natural.z_sq
  rwa [pow_two] at this

theorem mem_zpowers {w : D} (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact zpow_eq_one_or_self s.natural.z_sq k

theorem QB_le_T [Finite D] : pCoreOf 2 B ≤ A ⊓ B := s.gold.pCoreOf_right_le

theorem comm_UQ' {u q : D} (hu : u ∈ conjClosure V B) (hq : q ∈ pCoreOf 2 B) :
    u * q * u⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  have := Subgroup.commutator_mem_commutator hu hq
  rw [s.comm_UQ, commutatorElement_def] at this
  exact this

theorem comm_UU' {u w : D} (hu : u ∈ conjClosure V B) (hw : w ∈ conjClosure V B) :
    u * w * u⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
  have := Subgroup.commutator_mem_commutator hu hw
  rw [s.comm_UU, commutatorElement_def] at this
  exact this

omit s in
theorem sq_comm_aux {u q c : D} (hcu : u * q * u⁻¹ * q⁻¹ = c) (hcq : c * q = q * c)
    (hcc : c * c = 1) : q * q * u = u * q * q := by
  have h1 : u * q = c * (q * u) := by
    calc u * q = (u * q * u⁻¹ * q⁻¹) * (q * u) := by group
      _ = c * (q * u) := by rw [hcu]
  have h2 : u * q * q = q * q * u := by
    calc u * q * q = (c * (q * u)) * q := by rw [h1]
      _ = c * q * (u * q) := by group
      _ = c * q * (c * (q * u)) := by rw [h1]
      _ = c * (q * c) * (q * u) := by group
      _ = c * (c * q) * (q * u) := by rw [← hcq]
      _ = (c * c) * (q * q * u) := by group
      _ = q * q * u := by rw [hcc, one_mul]
  exact h2.symm

theorem sq_comm {q : D} (hq : q ∈ pCoreOf 2 B) {u : D} (hu : u ∈ conjClosure V B) :
    q * q * u = u * q * q := by
  have hqB : q ∈ B := pCoreOf_le 2 B hq
  have hzq : z * q = q * z := (s.z_comm hqB).symm
  rcases s.mem_zpowers (s.comm_UQ' hu hq) with hc | hc
  · exact sq_comm_aux hc (by rw [one_mul, mul_one]) (by rw [mul_one])
  · exact sq_comm_aux hc hzq s.z_mul_z

end B2Setup

end GoldAmL2D

end F6

end CFSG.Quasithin
