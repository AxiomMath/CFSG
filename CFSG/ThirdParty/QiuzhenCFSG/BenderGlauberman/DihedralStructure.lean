module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral structure facts for Hypothesis 1.1

The subgroup `S0` of index two in the dihedral Sylow subgroup `S`, its
unique involution `t`, and the containment `S ≤ C_G(t)`.  These facts are
shared by the Section 2 development and the proof of Theorem B.
-/

noncomputable section

namespace CFSG.BenderGlauberman

universe u

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type u} [Group G] [Finite G]

section DihedralStructure

variable (c : Hyp11 G)

/-- `|S| = 2·2^m`. -/
public lemma S_nat_card (c : Hyp11 G) : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
  rcases c.dihedralEquiv with ⟨e⟩
  have : NeZero (2 ^ c.m) := ⟨pow_ne_zero c.m (by norm_num)⟩
  calc
    Nat.card (c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) :=
      Nat.card_congr e.toEquiv
    _ = 2 * 2 ^ c.m := DihedralGroup.nat_card

/-- `|S0| = 2^m`. -/
public lemma S0_nat_card (c : Hyp11 G) : Nat.card (c.S0 : Subgroup G) = 2 ^ c.m := by
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) (by
    calc
      Nat.card (c.S0 : Subgroup G) * 2 = 2 * Nat.card (c.S0 : Subgroup G) := by rw [mul_comm]
      _ = Nat.card (c.S : Subgroup G) := c.S_index_two.symm
      _ = 2 * 2 ^ c.m := S_nat_card c
      _ = 2 ^ c.m * 2 := by rw [mul_comm])

/-- The type of elements of `S0` viewed inside `S` is equivalent to `S0` itself. -/
private def S0_subgroupOf_equiv (c : Hyp11 G) :
    ↥((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)) ≃ ↥(c.S0 : Subgroup G) where
  toFun x := ⟨(x.1 : G), (Subgroup.mem_subgroupOf.mp x.2)⟩
  invFun y := ⟨⟨(y : G), c.S0_le_S y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl

/-- `|S : S0| = 2`. -/
public lemma S0_index (c : Hyp11 G) :
    ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index = 2 := by
  have h0 : ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index *
      Nat.card (c.S0 : Subgroup G) = 2 * 2 ^ c.m := by
    calc
      ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index *
          Nat.card (c.S0 : Subgroup G)
          = ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index *
              Nat.card ↥((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)) := by
            congr 1
            exact (Nat.card_congr (S0_subgroupOf_equiv c)).symm
    _ = Nat.card (c.S : Subgroup G) := Subgroup.index_mul_card _
    _ = 2 * 2 ^ c.m := S_nat_card c
  have h : ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index * 2 ^ c.m =
      2 * 2 ^ c.m := by
    calc
      ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index * 2 ^ c.m
          = ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index *
              Nat.card (c.S0 : Subgroup G) := by rw [S0_nat_card c]
      _ = 2 * 2 ^ c.m := h0
  exact Nat.mul_right_cancel (by positivity : 0 < 2 ^ c.m) h

namespace Hyp11

/-- `S = ⟨t1, t2⟩` in the dihedral Sylow `2`-subgroup. -/
public lemma S_eq_closure_t1_t2 (c : Hyp11 G) :
    (c.S : Subgroup G) = Subgroup.closure ({c.t1, c.t2} : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  apply le_antisymm
  · intro s hs
    let K : Subgroup G := Subgroup.closure ({c.t1, c.t2} : Set G)
    have hKleS : K ≤ (c.S : Subgroup G) := by
      exact (Subgroup.closure_le (c.S : Subgroup G)).2 (by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact c.t1_mem_S
        · exact c.t2_mem_S)
    have hS0leK : (c.S0 : Subgroup G) ≤ K := by
      rw [c.S0_eq_zpowers]
      exact (Subgroup.zpowers_le).2 (K.mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)))
    have hKneS0 : K ≠ (c.S0 : Subgroup G) := by
      intro hEq
      exact c.t1_not_mem_S0 (by
        have ht1K : c.t1 ∈ K := Subgroup.subset_closure (by simp)
        simpa [hEq] using ht1K)
    let S0S : Subgroup ↥(c.S : Subgroup G) :=
      (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
    let KS : Subgroup ↥(c.S : Subgroup G) := K.subgroupOf (c.S : Subgroup G)
    have hS0S_le_KS : S0S ≤ KS := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hS0leK (Subgroup.mem_subgroupOf.mp hx))
    have hrel := Subgroup.relIndex_mul_index hS0S_le_KS
    have hrelS0 : S0S.relIndex KS = (c.S0 : Subgroup G).relIndex K :=
      Subgroup.relIndex_subgroupOf hKleS
    have hmul : (c.S0 : Subgroup G).relIndex K * KS.index = 2 := by
      rw [hrelS0] at hrel
      rw [S0_index c] at hrel
      exact hrel
    have hrelne : (c.S0 : Subgroup G).relIndex K ≠ 1 := by
      intro hEq1
      have hKleS0 : K ≤ (c.S0 : Subgroup G) := (Subgroup.relIndex_eq_one).mp hEq1
      exact hKneS0 (le_antisymm hKleS0 hS0leK)
    have hapos : 0 < (c.S0 : Subgroup G).relIndex K :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
        (H := (c.S0 : Subgroup G).subgroupOf K))
    have hbpos : 0 < KS.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := KS))
    have hb1 : KS.index = 1 := by
      have hb_le2 : (c.S0 : Subgroup G).relIndex K ≤ 2 := by
        exact Nat.le_of_dvd (by norm_num : 0 < 2) ⟨KS.index, hmul.symm⟩
      have hb2 : (c.S0 : Subgroup G).relIndex K = 2 := by omega
      have : 2 * KS.index = 2 := by rwa [hb2] at hmul
      omega
    have hKstop : KS = ⊤ := (Subgroup.index_eq_one).mp hb1
    have hsK : (⟨s, hs⟩ : ↥(c.S : Subgroup G)) ∈ KS := by
      rw [hKstop]
      trivial
    simpa using (Subgroup.mem_subgroupOf.mp hsK)
  · exact (Subgroup.closure_le (c.S : Subgroup G)).2 (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact c.t1_mem_S
      · exact c.t2_mem_S)

end Hyp11

/-- `S0` is normal in `S`. -/
public lemma S0_normal (c : Hyp11 G) :
    ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).Normal :=
  Subgroup.normal_of_index_eq_two (S0_index c)

/-- Conjugation by an element of `S` preserves `S0`. -/
public lemma S_conj_mem_S0 (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G))
    {y : G} (hy : y ∈ (c.S0 : Subgroup G)) : g * y * g⁻¹ ∈ (c.S0 : Subgroup G) := by
  let K := (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hyK : (⟨y, c.S0_le_S hy⟩ : ↥(c.S : Subgroup G)) ∈ K :=
    Subgroup.mem_subgroupOf.mpr hy
  have hmem : (⟨g, hg⟩ : ↥(c.S : Subgroup G)) * ⟨y, c.S0_le_S hy⟩ *
      (⟨g, hg⟩ : ↥(c.S : Subgroup G))⁻¹ ∈ K :=
    (S0_normal c).conj_mem ⟨y, c.S0_le_S hy⟩ hyK ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

/-- `S0` has exactly two elements of order dividing two: `1` and `t`. -/
public lemma S0_sq_eq_one_iff (c : Hyp11 G) {x : ↥(c.S0 : Subgroup G)} :
    x ^ 2 = 1 ↔ x = 1 ∨ x = ⟨c.t, c.t_mem_S0⟩ := by
  classical
  let α := ↥(c.S0 : Subgroup G)
  have hcyc : IsCyclic α := c.S0_cyclic
  have hcard2 : 2 ∣ Fintype.card α := by
    have hcard : Fintype.card α = 2 ^ c.m := by
      simpa [α] using S0_nat_card c
    refine ⟨2 ^ (c.m - 1), ?_⟩
    rw [hcard, mul_comm, ← pow_succ, Nat.sub_add_cancel c.one_le_m]
  have hcard1 : (Finset.univ.filter (fun a : α => orderOf a = 1)).card = 1 := by
    have h := IsCyclic.card_orderOf_eq_totient (α := α) (d := 1) (by norm_num : 1 ∣ Fintype.card α)
    simpa using h
  have hcard2' : (Finset.univ.filter (fun a : α => orderOf a = 2)).card = 1 := by
    have h := IsCyclic.card_orderOf_eq_totient (α := α) (d := 2) hcard2
    simpa using h
  have hS : (Finset.univ.filter (fun a : α => a ^ 2 = 1)).card = 2 := by
    have hset : Finset.univ.filter (fun a : α => a ^ 2 = 1) =
        Finset.univ.filter (fun a : α => orderOf a = 1) ∪
          Finset.univ.filter (fun a : α => orderOf a = 2) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ha
        have hdiv : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using ha)
        have hdiv' : orderOf a = 1 ∨ orderOf a = 2 :=
          (Nat.dvd_prime (p := 2) (m := orderOf a) Nat.prime_two).mp hdiv
        rcases hdiv' with h1 | h2
        · exact Or.inl h1
        · exact Or.inr h2
      · intro h
        rcases h with h1 | h2
        · have ha1 : a = 1 := orderOf_eq_one_iff.mp h1
          simp [ha1]
        · simpa [h2] using (pow_orderOf_eq_one a)
    rw [hset, Finset.card_union_of_disjoint]
    · rw [hcard1, hcard2']
    · rw [Finset.disjoint_iff_ne]
      intro a ha b hb hEq
      have ha1 : orderOf a = 1 := (Finset.mem_filter.mp ha).2
      have hb2 : orderOf b = 2 := (Finset.mem_filter.mp hb).2
      have : orderOf a = 2 := by simpa [hEq] using hb2
      exact (by norm_num : (1 : ℕ) ≠ 2) (ha1.symm.trans this)
  have htS : (⟨c.t, c.t_mem_S0⟩ : α) ∈ Finset.univ.filter (fun a : α => a ^ 2 = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (⟨c.t, c.t_mem_S0⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = (1 : ↥(c.S0 : Subgroup G))
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using c.t_involution.2
  have h1S : (1 : α) ∈ Finset.univ.filter (fun a : α => a ^ 2 = 1) := by
    simp
  have hset2 : Finset.univ.filter (fun a : α => a ^ 2 = 1) = ({1, ⟨c.t, c.t_mem_S0⟩} : Finset α) := by
    have hsubset : ({1, ⟨c.t, c.t_mem_S0⟩} : Finset α) ⊆
        Finset.univ.filter (fun a : α => a ^ 2 = 1) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haT
      · exact h1S
      · rw [Finset.mem_singleton.mp haT]
        exact htS
    have hcardle : (Finset.univ.filter (fun a : α => a ^ 2 = 1)).card ≤
        ({1, ⟨c.t, c.t_mem_S0⟩} : Finset α).card := by
      rw [hS]
      have hne : ⟨c.t, c.t_mem_S0⟩ ≠ (1 : α) := by
        intro h
        exact c.t_involution.1 (by simpa using (Subtype.ext_iff.mp h))
      rw [Finset.card_insert_of_notMem]
      · simp
      · intro h1
        apply hne
        exact (Finset.mem_singleton.mp h1).symm
    exact (Finset.eq_of_subset_of_card_le hsubset hcardle).symm
  constructor
  · intro hx
    have hx2 : x ∈ ({1, ⟨c.t, c.t_mem_S0⟩} : Finset α) := by
      rw [← hset2]
      simp [hx]
    rcases Finset.mem_insert.mp hx2 with rfl | hxt
    · exact Or.inl rfl
    · right
      exact Finset.mem_singleton.mp hxt
  · intro h
    rcases h with rfl | rfl
    · simp
    · simp [c.t_involution.2]

/-- Conjugation by any element of `S` fixes the unique involution `t` of `S0`. -/
public lemma S_conj_t (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G)) :
    g * c.t * g⁻¹ = c.t := by
  have hmem : g * c.t * g⁻¹ ∈ (c.S0 : Subgroup G) := S_conj_mem_S0 c hg c.t_mem_S0
  have hsq : (g * c.t * g⁻¹) ^ 2 = 1 := by
    calc
      (g * c.t * g⁻¹) ^ 2 = (g * c.t * g⁻¹) * (g * c.t * g⁻¹) := by rw [pow_two]
      _ = g * (c.t * c.t) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by
        rw [show c.t * c.t = 1 by simpa [pow_two] using c.t_involution.2]
      _ = 1 := by group
  have hne : g * c.t * g⁻¹ ≠ 1 := by
    intro h
    have ht1 : c.t = 1 := by
      calc
        c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact c.t_involution.1 ht1
  have hsq' : (⟨g * c.t * g⁻¹, hmem⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hsq
  rcases (S0_sq_eq_one_iff c (x := ⟨g * c.t * g⁻¹, hmem⟩)).1 hsq' with h1 | ht
  · exfalso
    exact hne (by simpa using (Subtype.ext_iff.mp h1))
  · exact Subtype.ext_iff.mp ht

/-- `s` centralizes `t`. -/
public lemma s_conj_t (c : Hyp11 G) : c.s * c.t * c.s⁻¹ = c.t :=
  S_conj_t c c.s_mem_S

/-- `S ≤ H = C_G(t)`. -/
public lemma S_le_H (c : Hyp11 G) : (c.S : Subgroup G) ≤ c.H := by
  intro g hg
  rw [c.H_eq_centralizer]
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  simp at hh
  rw [hh]
  have h := congrArg (fun x : G => x * g) (S_conj_t c hg)
  have h' : (g * c.t * g⁻¹) * g = g * c.t := by group
  exact h.symm.trans h'

/-- `s ∈ H = C_G(t)`. -/
public lemma s_mem_H (c : Hyp11 G) : c.s ∈ c.H := S_le_H c c.s_mem_S

end DihedralStructure

end CFSG.BenderGlauberman
