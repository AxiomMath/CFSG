module

public import CFSG.Quasithin.Recognition.St84.G24Data
public import CFSG.GroupTheory.PGroup.ClassTwoCoordinates
public import Certificates.Data.A5GL42
import CFSG.Quasithin.Background.SpecialPGroupCenter

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single conj_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem exists_eElt_mul)
open Certificates.A5GL42 (aO bO)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def v1Diag (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j =>
    if (i.val < 4 ↔ j.val < 4) then
      X ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨j.val % 4, Nat.mod_lt _ (by norm_num)⟩
    else 0

@[expose] def v1Omega : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if i.val % 4 = j.val % 4 ∧ (4 ≤ i.val ∨ 4 ≤ j.val) then 1 else 0

@[expose] def v1Frame (k : G) (e : Fin 4 → G) (i : Fin 8) : G :=
  if i.val < 4 then e ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩
  else k * e ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ * k⁻¹

@[expose] def z1Frame (k z : G) : Fin 2 → G := ![z, k * z * k⁻¹]

structure G24Frame1 (L1 L2 S : Subgroup G) where
  k : G
  a : G
  b : G
  e : Fin 4 → G
  k_mem : k ∈ bigB L1 L2 S
  k_not_mem : k ∉ L1
  orderOf_k : orderOf k = 3
  comm_k : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S
  inf_centralizer : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥
  decomp : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
    ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c
  card_A : Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) = 180
  a_mem : a ∈ L1 ⊓ Subgroup.centralizer ({k} : Set G)
  b_mem : b ∈ L1 ⊓ Subgroup.centralizer ({k} : Set G)
  a_sq : a ^ 2 = 1
  b_cube : b ^ 3 = 1
  ab_five : (a * b) ^ 5 = 1
  closure_eq : Subgroup.closure ({a, b, k} : Set G) =
    (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)
  e_mem : ∀ i, e i ∈ dsQ L1 L2 S
  indep : ∀ v, eElt (v1Frame k e) v ∈ centerOf (dsQ L1 L2 S) → v = 0
  act_a : ∀ j, a * v1Frame k e j * a⁻¹ * (eElt (v1Frame k e) fun i => v1Diag aO i j)⁻¹ ∈
    centerOf (dsQ L1 L2 S)
  act_b : ∀ j, b * v1Frame k e j * b⁻¹ * (eElt (v1Frame k e) fun i => v1Diag bO i j)⁻¹ ∈
    centerOf (dsQ L1 L2 S)
  act_k : ∀ j, k * v1Frame k e j * k⁻¹ * (eElt (v1Frame k e) fun i => v1Omega i j)⁻¹ ∈
    centerOf (dsQ L1 L2 S)

theorem v1Frame_castAdd (k : G) (e : Fin 4 → G) (i : Fin 4) :
    v1Frame k e (Fin.castAdd 4 i) = e i := by
  simp [v1Frame, Fin.castAdd, Nat.mod_eq_of_lt i.isLt]

theorem v1Frame_natAdd (k : G) (e : Fin 4 → G) (i : Fin 4) :
    v1Frame k e (Fin.natAdd 4 i) = k * e i * k⁻¹ := by
  simp [v1Frame, Fin.natAdd, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

theorem eElt_v1Frame (k : G) (e : Fin 4 → G) (v : Fin 8 → ZMod 2) :
    eElt (v1Frame k e) v =
      eElt e (fun i => v (Fin.castAdd 4 i)) *
        eElt (fun i => k * e i * k⁻¹) (fun i => v (Fin.natAdd 4 i)) := by
  rw [CFSG.GroupTheory.eElt_eq_castAdd_mul_natAdd (m := 4) (n := 4)]
  congr 2
  · funext i
    exact v1Frame_castAdd k e i
  · funext i
    exact v1Frame_natAdd k e i

theorem v1Diag_castAdd_castAdd (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    v1Diag X (Fin.castAdd 4 i) (Fin.castAdd 4 j) = X i j := by
  simp [v1Diag, Fin.castAdd, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]

theorem v1Diag_natAdd_castAdd (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    v1Diag X (Fin.natAdd 4 i) (Fin.castAdd 4 j) = 0 := by
  rw [v1Diag]
  simp [Fin.castAdd, Fin.natAdd]

theorem v1Diag_castAdd_natAdd (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    v1Diag X (Fin.castAdd 4 i) (Fin.natAdd 4 j) = 0 := by
  rw [v1Diag]
  simp [Fin.castAdd, Fin.natAdd]

theorem v1Diag_natAdd_natAdd (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    v1Diag X (Fin.natAdd 4 i) (Fin.natAdd 4 j) = X i j := by
  simp [v1Diag, Fin.natAdd, Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]

theorem v1Omega_castAdd_castAdd (i j : Fin 4) :
    v1Omega (Fin.castAdd 4 i) (Fin.castAdd 4 j) = 0 := by
  simp [v1Omega, Fin.castAdd]

theorem v1Omega_natAdd_castAdd (i j : Fin 4) :
    v1Omega (Fin.natAdd 4 i) (Fin.castAdd 4 j) = (if i = j then (1 : ZMod 2) else 0) := by
  simp [v1Omega, Fin.natAdd, Fin.castAdd, Fin.ext_iff, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]

theorem v1Omega_castAdd_natAdd (i j : Fin 4) :
    v1Omega (Fin.castAdd 4 i) (Fin.natAdd 4 j) = (if i = j then (1 : ZMod 2) else 0) := by
  simp [v1Omega, Fin.natAdd, Fin.castAdd, Fin.ext_iff, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]

theorem v1Omega_natAdd_natAdd (i j : Fin 4) :
    v1Omega (Fin.natAdd 4 i) (Fin.natAdd 4 j) = (if i = j then (1 : ZMod 2) else 0) := by
  simp [v1Omega, Fin.natAdd, Fin.ext_iff, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]

section Local

variable {L1 L2 S : Subgroup G}

theorem G24Vertex1.commutator_mem_centerOf_dsQ (hD : G24LocalData L1 L2 S) :
    ∀ x ∈ dsQ L1 L2 S, ∀ y ∈ dsQ L1 L2 S, ⁅x, y⁆ ∈ centerOf (dsQ L1 L2 S) :=
  fun x hx y hy =>
    hD.special_left.1.commutator_le_centerOf (Subgroup.commutator_mem_commutator hx hy)

theorem G24Vertex1.sq_mem_centerOf_dsQ [Finite G] (hD : G24LocalData L1 L2 S) :
    ∀ x ∈ dsQ L1 L2 S, x ^ 2 ∈ centerOf (dsQ L1 L2 S) :=
  fun x hx => hD.special_left.1.pow_mem_centerOf hx

theorem G24Vertex1.centerOf_dsQ_comm {L1 L2 S : Subgroup G} :
    ∀ z ∈ centerOf (dsQ L1 L2 S), ∀ x ∈ dsQ L1 L2 S, z * x = x * z :=
  fun z hz x hx => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx).symm

end Local

section Frame

variable {L1 L2 S : Subgroup G} {F : G24Frame1 L1 L2 S}

private theorem frame_mem (hD : G24LocalData L1 L2 S) :
    ∀ i : Fin 8, v1Frame F.k F.e i ∈ dsQ L1 L2 S := by
  intro i
  rw [v1Frame]
  by_cases h : i.val < 4
  · rw [if_pos h]
    exact F.e_mem _
  · rw [if_neg h]
    exact (Subgroup.mem_normalizer_iff.mp
      (P_le_normalizer_dsQ_left L1 L2 S (Subgroup.mem_sup_right F.k_mem)) _).mp
      (F.e_mem _)

theorem G24Vertex1.frame_central (hD : G24LocalData L1 L2 S) :
    ∀ y ∈ centerOf (dsQ L1 L2 S), ∀ i : Fin 8,
      y * v1Frame F.k F.e i = v1Frame F.k F.e i * y := by
  intro y hy i
  exact G24Vertex1.centerOf_dsQ_comm y hy _ (frame_mem hD i)

private theorem card_dsQ_eq (hD : G24LocalData L1 L2 S) :
    Nat.card ↥(dsQ L1 L2 S) = 2 ^ 8 * Nat.card ↥(centerOf (dsQ L1 L2 S)) := by
  rw [hD.card_dsQ_left, hD.card_centerOf_dsQ_left]
  norm_num

theorem G24Frame1.special_data [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) ≤
        Subgroup.normalizer (dsQ L1 L2 S : Set G) ∧
    Disjoint (dsQ L1 L2 S) ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) ∧
    centerOf (dsQ L1 L2 S) ≤ dsQ L1 L2 S ∧
    (∀ z ∈ centerOf (dsQ L1 L2 S), ∀ x ∈ dsQ L1 L2 S, z * x = x * z) ∧
    (∀ z ∈ centerOf (dsQ L1 L2 S), z ^ 2 = 1) ∧
    (∀ x ∈ dsQ L1 L2 S, x ^ 2 ∈ centerOf (dsQ L1 L2 S)) ∧
    (∀ r ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G),
      ∀ z ∈ centerOf (dsQ L1 L2 S), r * z * r⁻¹ ∈ centerOf (dsQ L1 L2 S)) ∧
    dsQ L1 L2 S ⊔ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) =
      L1 ⊔ bigB L1 L2 S := by
  have hAN : (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) ≤
      Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    inf_le_left.trans (P_le_normalizer_dsQ_left L1 L2 S)
  have hdisj : Disjoint (dsQ L1 L2 S)
      ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc dsQ L1 L2 S ⊓ ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G))
        ≤ dsQ L1 L2 S ⊓ Subgroup.centralizer ({F.k} : Set G) :=
          inf_le_inf_left _ inf_le_right
      _ = ⊥ := F.inf_centralizer
  refine ⟨hAN, hdisj, inf_le_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz x hx
    exact G24Vertex1.centerOf_dsQ_comm z hz x hx
  · intro z hz
    exact hD.sq_eq_one_of_mem_centerOf_left hz
  · intro x hx
    exact G24Vertex1.sq_mem_centerOf_dsQ hD x hx
  · intro r hr z hz
    exact (Subgroup.mem_normalizer_iff.mp
      (P_le_normalizer_centerOf_dsQ_left L1 L2 S hr.1) z).mp hz
  · refine le_antisymm (sup_le ?_ inf_le_left) ?_
    · exact dsQ_le_P_left L1 L2 S
    · intro x hx
      obtain ⟨q, hq, c, hc, rfl⟩ := F.decomp x hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hc)

theorem G24Frame1.frame_spec [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) :
    (∀ i, v1Frame F.k F.e i ∈ dsQ L1 L2 S) ∧
    (∀ y ∈ centerOf (dsQ L1 L2 S), ∀ i, y * v1Frame F.k F.e i = v1Frame F.k F.e i * y) ∧
    (∀ i, v1Frame F.k F.e i ^ 2 ∈ centerOf (dsQ L1 L2 S)) ∧
    (∀ i j, ⁅v1Frame F.k F.e i, v1Frame F.k F.e j⁆ ∈ centerOf (dsQ L1 L2 S)) ∧
    Nat.card ↥(dsQ L1 L2 S) = 2 ^ 8 * Nat.card ↥(centerOf (dsQ L1 L2 S)) :=
  ⟨frame_mem hD, G24Vertex1.frame_central hD,
    fun i => G24Vertex1.sq_mem_centerOf_dsQ hD _ (frame_mem hD i),
    fun i j => G24Vertex1.commutator_mem_centerOf_dsQ hD _ (frame_mem hD i) _ (frame_mem hD j),
    card_dsQ_eq hD⟩

theorem G24Frame1.exists_eElt_mul [Finite G] {L1 L2 S : Subgroup G}
    (F : G24Frame1 L1 L2 S) (hD : G24LocalData L1 L2 S) :
    ∀ x ∈ dsQ L1 L2 S, ∃ v : Fin 8 → ZMod 2, ∃ y ∈ centerOf (dsQ L1 L2 S),
      x = eElt (v1Frame F.k F.e) v * y := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := F.frame_spec hD
  exact CFSG.GroupTheory.exists_eElt_mul inf_le_left h1 h2 h3 h4 F.indep h5

end Frame

section Cover

variable {L1 L2 S : Subgroup G}

theorem G24Vertex1.not_forall_exists_mul_centerOf_left (hD : G24LocalData L1 L2 S)
    {H : Set G} (hHQ : H ⊆ dsQ L1 L2 S) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    ¬ ∀ x ∈ dsQ L1 L2 S, ∃ a ∈ H, ∃ z ∈ centerOf (dsQ L1 L2 S), x = a * z := by
  intro hcov
  have hQab : ∀ x ∈ dsQ L1 L2 S, ∀ y ∈ dsQ L1 L2 S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, z, hz, rfl⟩ := hcov x hx
    obtain ⟨b, hb, w, hw, rfl⟩ := hcov y hy
    have hzb : z * b = b * z := G24Vertex1.centerOf_dsQ_comm z hz b (hHQ hb)
    have hwa : w * a = a * w := G24Vertex1.centerOf_dsQ_comm w hw a (hHQ ha)
    have hzw : z * w = w * z := G24Vertex1.centerOf_dsQ_comm z hz w (Subgroup.mem_inf.mp hw).1
    calc a * z * (b * w) = a * (z * b) * w := by group
      _ = a * (b * z) * w := by rw [hzb]
      _ = (a * b) * (z * w) := by group
      _ = (b * a) * (z * w) := by rw [hH a ha b hb]
      _ = b * (a * w) * z := by
          rw [hzw]
          group
      _ = b * (w * a) * z := by rw [hwa]
      _ = b * w * (a * z) := by group
  have heq : dsQ L1 L2 S = centerOf (dsQ L1 L2 S) := by
    refine le_antisymm (fun x hx => ?_) inf_le_left
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hQab x hx y hy).symm
  have hQcard : Nat.card ↥(dsQ L1 L2 S) = 2 ^ 10 := hD.card_dsQ_left
  have hZcard : Nat.card ↥(centerOf (dsQ L1 L2 S)) = 4 := hD.card_centerOf_dsQ_left
  rw [heq, hZcard] at hQcard
  norm_num at hQcard

end Cover

end CFSG.Quasithin.F112R.St84
