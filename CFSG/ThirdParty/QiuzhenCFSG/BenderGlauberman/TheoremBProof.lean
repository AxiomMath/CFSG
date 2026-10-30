module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.DihedralStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.IntervalCases

namespace CFSG
end CFSG
open CFSG

/-!
# Proof of Bender--Glauberman Theorem B

Theorem B says that a proper subgroup `G1` containing `H` and with a single
class of involutions forces `G/O(G) ≅ A₅`.  Following the paper, Theorem A
is applied to both `G` and `G1` to obtain `|G : G1| < 9`; the remaining
steps (odd intersections of distinct conjugates, and the permutation action
on the five conjugates) are the registered bridges below.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

variable {G : Type u} [Group G] [Finite G]

/-- `O(H.subgroupOf X) = O(H).subgroupOf X` when `H ≤ X`. -/
private lemma oddCoreOf_subgroupOf_eq (H X : Subgroup G) (hH : H ≤ X) :
    oddCoreOf (H.subgroupOf X) = (oddCoreOf H).subgroupOf X := by
  unfold oddCoreOf
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨u, hu, rfl⟩
    let e : H.subgroupOf X ≃* H := Subgroup.subgroupOfEquivOfLe hH
    have hmap : (pPrimeCore 2 (H.subgroupOf X)).map e.toMonoidHom = pPrimeCore 2 H :=
      pPrimeCore_map_iso (G := H.subgroupOf X) (G' := H) (p := 2) e
    have hmem : (e u : H) ∈ pPrimeCore 2 H := by
      have hu' : e u ∈ (pPrimeCore 2 (H.subgroupOf X)).map e.toMonoidHom :=
        ⟨u, hu, rfl⟩
      rw [hmap] at hu'
      exact hu'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨(⟨e u, hmem⟩ : pPrimeCore 2 H), hmem, ?_⟩
    change ((e u : H) : G) = ((u : X) : G)
    simp [Subgroup.subgroupOfEquivOfLe, e]
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
    rcases hx with ⟨v, hv, hxeq⟩
    let e : H.subgroupOf X ≃* H := Subgroup.subgroupOfEquivOfLe hH
    have hmap : (pPrimeCore 2 (H.subgroupOf X)).map e.toMonoidHom = pPrimeCore 2 H :=
      pPrimeCore_map_iso (G := H.subgroupOf X) (G' := H) (p := 2) e
    have hv' : v ∈ (pPrimeCore 2 (H.subgroupOf X)).map e.toMonoidHom := by
      rw [hmap]
      exact hv
    rcases Subgroup.mem_map.mp hv' with ⟨u, hu, rfl⟩
    rw [Subgroup.mem_map]
    refine ⟨u, hu, ?_⟩
    apply Subtype.ext
    simpa [Subgroup.subgroupOfEquivOfLe, e] using hxeq

/-- `O(H) ≤ H`. -/
private lemma U_le_H (c : Hyp11 G) : c.U ≤ c.H := by
  intro x hx
  simpa [Hyp11.U] using (Subgroup.map_subtype_le (pPrimeCore 2 c.H) hx)

/-- The centralizer of `t` inside a subgroup agrees with `H.subgroupOf G1`. -/
private lemma centralizer_subgroupOf_eq {t : G} {H G1 : Subgroup G}
    (ht : t ∈ G1) (hH : H ≤ G1) (hHc : H = Subgroup.centralizer ({t} : Set G)) :
    H.subgroupOf G1 = Subgroup.centralizer ({⟨t, ht⟩} : Set (↥G1)) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxG : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      simpa [hHc] using (Subgroup.mem_subgroupOf.mp hx)
    have hcomm := (Subgroup.mem_centralizer_singleton_iff (g := t) (k := (x : G))).mp hxG
    apply Subtype.ext
    simpa [mul_assoc] using hcomm
  · intro hx
    apply Subgroup.mem_subgroupOf.mpr
    rw [hHc]
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    apply (Subgroup.mem_centralizer_singleton_iff (g := t) (k := (x : G))).mpr
    simpa [mul_assoc] using congrArg Subtype.val hx

/-- The relative centralizer of an element in a subgroup containing it. -/
private lemma centralizerIn_subgroupOf_eq (H G1 : Subgroup G)
    (t : G) (ht : t ∈ G1) :
    centralizerIn (H.subgroupOf G1) ⟨t, ht⟩ = (centralizerIn H t).subgroupOf G1 := by
  ext x
  have hx : x ∈ Subgroup.centralizer ({⟨t, ht⟩} : Set (↥G1)) ↔
      (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      simpa [mul_assoc] using congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      simpa [mul_assoc] using h
  simp [centralizerIn, Subgroup.mem_subgroupOf, hx]

/-- A subgroup containing `H` inherits Hypothesis 1.1, with `S` viewed as a
Sylow subgroup of the subgroup. -/
private noncomputable def hyp11_of_subgroup (c : Hyp11 G) (G1 : Subgroup G)
    (hHG1 : c.H ≤ G1)
    (h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y) :
    Hyp11 (↥G1) := by
  classical
  let hSG1 : (c.S : Subgroup G) ≤ G1 := (S_le_H c).trans hHG1
  let hS0G1 : (c.S0 : Subgroup G) ≤ G1 := c.S0_le_S.trans hSG1
  let htG1 : c.t ∈ G1 := hSG1 (c.S0_le_S c.t_mem_S0)
  let hsG1 : c.s ∈ G1 := hSG1 c.s_mem_S
  let ht1G1 : c.t1 ∈ G1 := hSG1 c.t1_mem_S
  let ht2G1 : c.t2 ∈ G1 := hSG1 c.t2_mem_S
  let S1 : Sylow 2 (↥G1) := c.S.subtype hSG1
  let S01 : Subgroup (↥G1) := (c.S0 : Subgroup G).subgroupOf G1
  let H1 : Subgroup (↥G1) := c.H.subgroupOf G1
  refine {
    S := S1
    m := c.m
    one_le_m := c.one_le_m
    dihedralEquiv := by
      rcases c.dihedralEquiv with ⟨eS⟩
      exact ⟨(Subgroup.subgroupOfEquivOfLe hSG1).trans eS⟩
    S0 := S01
    S0_le_S := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (c.S0_le_S (Subgroup.mem_subgroupOf.mp hx))
    S0_cyclic := by
      exact (Subgroup.subgroupOfEquivOfLe hS0G1).isCyclic.mpr c.S0_cyclic
    S_index_two := by
      have hcardS : Nat.card (S1 : Subgroup (↥G1)) = Nat.card (c.S : Subgroup G) := by
        dsimp [S1]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG1).toEquiv
      have hcardS0 : Nat.card (S01 : Subgroup (↥G1)) = Nat.card (c.S0 : Subgroup G) := by
        dsimp [S01]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0G1).toEquiv
      rw [hcardS, hcardS0]
      exact c.S_index_two
    t := ⟨c.t, htG1⟩
    t_mem_S0 := Subgroup.mem_subgroupOf.mpr c.t_mem_S0
    t_involution := by
      refine ⟨?_, ?_⟩
      · intro h
        apply c.t_involution.1
        exact Subtype.ext_iff.mp h
      · ext
        simpa using c.t_involution.2
    one_involution_class := by
      intro x y hx hy
      have hxG : IsInvolution (x : G) := by
        refine ⟨?_, ?_⟩
        · intro h
          exact hx.1 (Subtype.ext h)
        · simpa using congrArg Subtype.val hx.2
      have hyG : IsInvolution (y : G) := by
        refine ⟨?_, ?_⟩
        · intro h
          exact hy.1 (Subtype.ext h)
        · simpa using congrArg Subtype.val hy.2
      rcases h1 (x : G) (y : G) hxG hyG x.2 y.2 with ⟨g, hgG1, hg⟩
      refine ⟨⟨g, hgG1⟩, ?_⟩
      · ext
        simpa [mul_assoc] using hg
    s := ⟨c.s, hsG1⟩
    s_mem_S := Subgroup.mem_subgroupOf.mpr c.s_mem_S
    s_not_mem_S0 := by
      intro h
      apply c.s_not_mem_S0
      exact Subgroup.mem_subgroupOf.mp h
    s_involution := by
      refine ⟨?_, ?_⟩
      · intro h
        apply c.s_involution.1
        exact Subtype.ext_iff.mp h
      · ext
        simpa using c.s_involution.2
    t1 := ⟨c.t1, ht1G1⟩
    t2 := ⟨c.t2, ht2G1⟩
    t1_mem_S := Subgroup.mem_subgroupOf.mpr c.t1_mem_S
    t1_not_mem_S0 := by
      intro h
      apply c.t1_not_mem_S0
      exact Subgroup.mem_subgroupOf.mp h
    t1_involution := by
      refine ⟨?_, ?_⟩
      · intro h
        apply c.t1_involution.1
        exact Subtype.ext_iff.mp h
      · ext
        simpa using c.t1_involution.2
    t2_mem_S := Subgroup.mem_subgroupOf.mpr c.t2_mem_S
    t2_not_mem_S0 := by
      intro h
      apply c.t2_not_mem_S0
      exact Subgroup.mem_subgroupOf.mp h
    t2_involution := by
      refine ⟨?_, ?_⟩
      · intro h
        apply c.t2_involution.1
        exact Subtype.ext_iff.mp h
      · ext
        simpa using c.t2_involution.2
    S0_eq_zpowers := by
      ext x
      constructor
      · intro hx
        have hxG : (x : G) ∈ c.S0 := Subgroup.mem_subgroupOf.mp hx
        rw [c.S0_eq_zpowers] at hxG
        rw [Subgroup.mem_zpowers_iff] at hxG ⊢
        rcases hxG with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        apply Subtype.ext
        simpa [mul_assoc] using hn
      · intro hx
        rw [Subgroup.mem_zpowers_iff] at hx
        rcases hx with ⟨n, hn⟩
        apply Subgroup.mem_subgroupOf.mpr
        rw [c.S0_eq_zpowers]
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨n, ?_⟩
        simpa [mul_assoc] using congrArg Subtype.val hn
    H := H1
    H_eq_centralizer := by
      exact centralizer_subgroupOf_eq (H := c.H) (G1 := G1) htG1 hHG1 c.H_eq_centralizer
    H_eq_US := by
      have hU : oddCoreOf H1 = (oddCoreOf c.H).subgroupOf G1 := by
        exact oddCoreOf_subgroupOf_eq c.H G1 hHG1
      have hS : (S1 : Subgroup (↥G1)) = (c.S : Subgroup G).subgroupOf G1 := rfl
      rw [hU, hS]
      calc
        (oddCoreOf c.H).subgroupOf G1 ⊔ (c.S : Subgroup G).subgroupOf G1 =
            (c.U ⊔ (c.S : Subgroup G)).subgroupOf G1 :=
          (Subgroup.subgroupOf_sup (hA := (U_le_H c).trans hHG1) (hA' := hSG1)).symm
        _ = c.H.subgroupOf G1 := by
          exact congrArg (fun K : Subgroup G => K.subgroupOf G1) c.H_eq_US
  }

/-- The inherited hypothesis has the same `k₁`, `k₂`, and `k`. -/
private lemma hyp11_k_eq (c : Hyp11 G) (G1 : Subgroup G) (hHG1 : c.H ≤ G1)
    (h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y) :
    (hyp11_of_subgroup c G1 hHG1 h1).k = c.k := by
  have hSG1 : (c.S : Subgroup G) ≤ G1 := (S_le_H c).trans hHG1
  have ht1G1 : c.t1 ∈ G1 := hSG1 c.t1_mem_S
  have ht2G1 : c.t2 ∈ G1 := hSG1 c.t2_mem_S
  have hk : (hyp11_of_subgroup c G1 hHG1 h1).k =
      (hyp11_of_subgroup c G1 hHG1 h1).k1 +
        (hyp11_of_subgroup c G1 hHG1 h1).k2 := by
    unfold BenderGlauberman.Hyp11.k
    rfl
  have hck : c.k = c.k1 + c.k2 := by
    unfold BenderGlauberman.Hyp11.k
    rfl
  rw [hk, hck]
  congr 1
  · simp [Hyp11.k1, hyp11_of_subgroup]
    rw [centralizerIn_subgroupOf_eq c.H G1 c.t1 ht1G1]
    exact Subgroup.relIndex_subgroupOf (G := G) (H := centralizerIn c.H c.t1)
      (K := c.H) (L := G1) hHG1
  · simp [Hyp11.k2, hyp11_of_subgroup]
    rw [centralizerIn_subgroupOf_eq c.H G1 c.t2 ht2G1]
    exact Subgroup.relIndex_subgroupOf (G := G) (H := centralizerIn c.H c.t2)
      (K := c.H) (L := G1) hHG1

/-- Theorem A applied to `G` and to a subgroup `G1` containing `H` gives
`|G : G1| < 9`. -/
private lemma theorem_B_index_lt_nine (c : Hyp11 G) (G1 : Subgroup G)
    (hHG1 : c.H ≤ G1)
    (h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y) :
    G1.index < 9 := by
  classical
  let c1 := hyp11_of_subgroup c G1 hHG1 h1
  have hA := theorem_A c
  have hA1 := theorem_A c1
  have hk : c1.k = c.k := hyp11_k_eq c G1 hHG1 h1
  have hrel : c.H.relIndex G1 * G1.index = c.H.index :=
    Subgroup.relIndex_mul_index hHG1
  have hrelq : (c1.H.index : ℚ) * (G1.index : ℚ) = (c.H.index : ℚ) := by
    change (c.H.subgroupOf G1).index * (G1.index : ℚ) = (c.H.index : ℚ)
    exact_mod_cast hrel
  have hbpos : (0 : ℚ) < (c1.H.index : ℚ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := c1.H)))
  have hgpos : (0 : ℚ) < (G1.index : ℚ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := G1)))
  have hbposG : (0 : ℚ) < (c.H.index : ℚ) := by
    nlinarith [hbpos, hgpos, hrelq]
  have hA1' : 2 * (c.k : ℚ) ^ 2 < 3 * (c1.H.index : ℚ) := by
    have hkq : (c1.k : ℚ) = (c.k : ℚ) := by exact_mod_cast hk
    have htmp : 2 * (c1.k : ℚ) ^ 2 < 3 * (c1.H.index : ℚ) :=
      (div_lt_iff₀ hbpos).1 hA1.2
    nlinarith [htmp, hkq]
  have ha : (c.H.index : ℚ) < 6 * (c.k : ℚ) ^ 2 := by
    have htmp : (1 / 3 : ℚ) * (c.H.index : ℚ) < 2 * (c.k : ℚ) ^ 2 :=
      (lt_div_iff₀ hbposG).1 hA.1
    nlinarith [htmp]
  have hbgt : (2 / 3 : ℚ) * (c.k : ℚ) ^ 2 < (c1.H.index : ℚ) := by
    nlinarith [hA1']
  have hn : (G1.index : ℚ) < 9 := by
    nlinarith [ha, hbgt, hrelq]
  exact_mod_cast hn

/-! ## Registered bridges

Both bridges are exactly the paper's remaining one-paragraph argument after
`|G : G1| < 9`: distinct conjugates of `G1` meet in odd order, and then the
permutation action on the five conjugates of `G1` is `A₅` modulo `O(G)`.
-/

/-- Distinct conjugates of `G1` meet in odd order.

Elimination condition: prove from Hypothesis 1.1 (dihedral Sylow 2, one
involution class) and the one-involution-class hypothesis on `G1`. -/
private lemma involution_mem_conj_imp_mem (c : Hyp11 G) (G1 : Subgroup G)
    (hHG1 : c.H ≤ G1)
    (h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y)
    {g x : G} (hx : IsInvolution x) (hxG1 : x ∈ G1)
    (hxg : x ∈ G1.map (MulAut.conj g).toMonoidHom) : g ∈ G1 := by
  classical
  have htG1 : c.t ∈ G1 := hHG1 (S_le_H c (c.S0_le_S c.t_mem_S0))
  -- `x` is conjugate to `t` inside `G1`
  rcases h1 c.t x c.t_involution hx htG1 hxG1 with ⟨u, huG1, hutx⟩
  -- `x` lies in the conjugate `G1^g`
  rcases Subgroup.mem_map.mp hxg with ⟨y, hyG1, hyx⟩
  let w : G := u⁻¹ * g
  have hzy : w⁻¹ * c.t * w = y := by
    have hyx' : g * y * g⁻¹ = x := by
      simpa using hyx
    calc
      w⁻¹ * c.t * w = (g⁻¹ * u) * c.t * (u⁻¹ * g) := by simp [w]
      _ = g⁻¹ * (u * c.t * u⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [hutx]
      _ = y := by
        calc
          g⁻¹ * x * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [← hyx']
          _ = y := by group
  have hzG1 : w⁻¹ * c.t * w ∈ G1 := by
    rw [hzy]
    exact hyG1
  have hzsq : (w⁻¹ * c.t * w) ^ 2 = 1 := by
    calc
      (w⁻¹ * c.t * w) ^ 2 = (w⁻¹ * c.t * w) * (w⁻¹ * c.t * w) := by rw [pow_two]
      _ = w⁻¹ * (c.t * c.t) * w := by group
      _ = 1 := by
        rw [show c.t * c.t = 1 by simpa [pow_two] using c.t_involution.2]
        group
  have hzne : w⁻¹ * c.t * w ≠ 1 := by
    intro h
    have ht1 : c.t = 1 := by
      calc
        c.t = w * (w⁻¹ * c.t * w) * w⁻¹ := by group
        _ = 1 := by rw [h]; group
    exact c.t_involution.1 ht1
  have hz : IsInvolution (w⁻¹ * c.t * w) := ⟨hzne, hzsq⟩
  -- `z := w⁻¹ t w` is an involution of `G1`, hence conjugate to `t` in `G1`
  rcases h1 c.t (w⁻¹ * c.t * w) c.t_involution hz htG1 hzG1 with ⟨v, hvG1, hvt⟩
  have hconj : (w * v) * c.t * (w * v)⁻¹ = c.t := by
    calc
      (w * v) * c.t * (w * v)⁻¹ = w * (v * c.t * v⁻¹) * w⁻¹ := by group
      _ = w * (w⁻¹ * c.t * w) * w⁻¹ := by rw [hvt]
      _ = c.t := by group
  have hcomm' : (w * v) * c.t = c.t * (w * v) := by
    calc
      (w * v) * c.t = ((w * v) * c.t * (w * v)⁻¹) * (w * v) := by group
      _ = c.t * (w * v) := by rw [hconj]
  have hwvH : w * v ∈ c.H := by
    rw [c.H_eq_centralizer]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz0
    rw [Set.mem_singleton_iff.mp hz0]
    exact hcomm'.symm
  have hwvG1 : w * v ∈ G1 := hHG1 hwvH
  have hg_eq : u * ((w * v) * v⁻¹) = g := by
    simp [w]
  rw [← hg_eq]
  exact Subgroup.mul_mem G1 huG1 (Subgroup.mul_mem G1 hwvG1 (G1.inv_mem hvG1))

private theorem strongEmbedding_intersections_odd (c : Hyp11 G) (G1 : Subgroup G)
    (hHG1 : c.H ≤ G1)
    (h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y) :
    ∀ g : G, g ∉ G1 → Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro g hg
  by_contra hodd
  let D : Subgroup G := G1 ⊓ G1.map (MulAut.conj g).toMonoidHom
  have h2 : 2 ∣ Nat.card D := by
    exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (by simpa [D] using hodd))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 h2
  have hxne : (x : G) ≠ 1 := by
    intro h
    exact (orderOf_eq_prime_iff.mp hx).2 (Subtype.ext (by simpa using h))
  have hxsq : (x : G) ^ 2 = 1 := by
    simpa [Subgroup.coe_pow] using
      congrArg (fun y : ↥D => (y : G)) (orderOf_eq_prime_iff.mp hx).1
  have hxinvol : IsInvolution (x : G) := ⟨hxne, hxsq⟩
  have hxG1 : (x : G) ∈ G1 := (Subgroup.mem_inf.mp x.2).1
  have hxconj : (x : G) ∈ G1.map (MulAut.conj g).toMonoidHom := (Subgroup.mem_inf.mp x.2).2
  exact hg (involution_mem_conj_imp_mem c G1 hHG1 h1 hxinvol hxG1 hxconj)

/-! ## The permutation action on the five cosets of `G1` -/

private structure SEContext (c : Hyp11 G) (G1 : Subgroup G) where
  hHG1 : c.H ≤ G1
  h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
    ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y
  hlt : G1.index < 9
  hodd : ∀ g : G, g ∉ G1 → Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G))
  hproper : G1 ≠ ⊤

private def seφ (G1 : Subgroup G) : G →* Equiv.Perm (G ⧸ G1) :=
  MulAction.toPermHom G (G ⧸ G1)

private lemma se_S_le_G1 (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    (c.S : Subgroup G) ≤ G1 :=
  (S_le_H c).trans e.hHG1

/-- An element of `S` fixes the coset `G1·g` iff it lies in the conjugate
`G1^g`. -/
private lemma se_stabilizer_mem_iff (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    (g : G) (s : ↥(c.S : Subgroup G)) :
    s ∈ MulAction.stabilizer (c.S : Subgroup G) (QuotientGroup.mk g : G ⧸ G1) ↔
      (s : G) ∈ G1.map (MulAut.conj g).toMonoidHom := by
  rw [MulAction.mem_stabilizer_iff]
  change (s : G) • (QuotientGroup.mk g : G ⧸ G1) = QuotientGroup.mk g ↔
    (s : G) ∈ G1.map (MulAut.conj g).toMonoidHom
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  rw [QuotientGroup.eq]
  constructor
  · intro h
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * (s : G) * g, ?_, ?_⟩
    · have h' : g⁻¹ * (s : G)⁻¹ * g ∈ G1 := by simpa [mul_assoc] using h
      exact (G1.inv_mem_iff).mp (by simpa [mul_assoc, mul_inv_rev] using h')
    · simp [mul_assoc]
  · intro h
    rcases Subgroup.mem_map.mp h with ⟨y, hyG1, hy⟩
    have hy' : g * y * g⁻¹ = (s : G) := by simpa using hy
    have hs : (s : G)⁻¹ = g * y⁻¹ * g⁻¹ := by
      calc
        (s : G)⁻¹ = (g * y * g⁻¹)⁻¹ := by rw [hy']
        _ = g * y⁻¹ * g⁻¹ := by group
    have hgoal : ((s : G) * g)⁻¹ * g = y⁻¹ := by
      calc
        ((s : G) * g)⁻¹ * g = g⁻¹ * (s : G)⁻¹ * g := by group
        _ = g⁻¹ * (g * y⁻¹ * g⁻¹) * g := by rw [hs]
        _ = y⁻¹ := by group
    simpa [← hgoal] using (G1.inv_mem hyG1)

/-- For `g ∉ G1`, the intersection `S ∩ G1^g` is trivial: it is a 2-subgroup
of the odd-order group `G1 ∩ G1^g`. -/
private lemma se_S_inter_conj_eq_bot (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    {g : G} (hg : g ∉ G1) :
    (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom = ⊥ := by
  let D : Subgroup G := G1 ⊓ G1.map (MulAut.conj g).toMonoidHom
  have hoddD : Odd (Nat.card D) := by
    simpa [D] using e.hodd g hg
  have hcop : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card D) := by
    rw [S_nat_card]
    have hcop2 : Nat.Coprime 2 (Nat.card D) := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro h2
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2)) hoddD
    exact Nat.Coprime.mul_left hcop2 (Nat.Coprime.pow_left c.m hcop2)
  calc
    (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom
        = (c.S : Subgroup G) ⊓ D := by
          rw [← inf_assoc, inf_eq_left.mpr (se_S_le_G1 c G1 e)]
    _ = ⊥ := by
          exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (G := G) hcop)

/-- For `g ∉ G1`, the stabilizer in `S` of the coset `G1·g` is trivial. -/
private lemma se_stabilizer_bot (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    {g : G} (hg : g ∉ G1) :
    MulAction.stabilizer (c.S : Subgroup G) (QuotientGroup.mk g : G ⧸ G1) = ⊥ := by
  apply Subgroup.ext
  intro s
  constructor
  · intro hs
    have hsG : (s : G) ∈ G1.map (MulAut.conj g).toMonoidHom :=
      (se_stabilizer_mem_iff c G1 e g s).mp hs
    have hsSG : (s : G) ∈ (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom :=
      ⟨s.2, hsG⟩
    have hbot : (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom = ⊥ :=
      se_S_inter_conj_eq_bot c G1 e hg
    have hs1 : (s : G) = 1 := by
      have hmem : (s : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact hsSG
      simpa [Subgroup.mem_bot] using hmem
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact hs1
  · intro hs
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_bot] at hs
    subst hs
    change (1 : G) • (QuotientGroup.mk g : G ⧸ G1) = QuotientGroup.mk g
    simp

/-- `|G : G1| = 5` and `|S| = 4`: `S` acts freely on the four non-base cosets,
so `|S| ∣ |G : G1| − 1`, and the index bound `< 9` forces both. -/
private lemma se_index_eq_five (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    G1.index = 5 ∧ Nat.card (c.S : Subgroup G) = 4 := by
  classical
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  let X := {q : Ω // q ≠ q0}
  have hfix : ∀ s : ↥(c.S : Subgroup G), (s : G) • q0 = q0 := by
    intro s
    exact MulAction.mem_stabilizer_iff.mp (by
      rw [MulAction.stabilizer_quotient G1]
      exact (se_S_le_G1 c G1 e) s.2)
  let : MulAction (c.S : Subgroup G) X := {
    smul := fun s x => ⟨(s : G) • x.1, by
      intro h
      apply x.2
      calc
        x.1 = (s : G)⁻¹ • ((s : G) • x.1) := by simp
        _ = (s : G)⁻¹ • q0 := by rw [h]
        _ = q0 := by simpa using hfix s⁻¹⟩
    one_smul := by
      intro x
      apply Subtype.ext
      change (1 : G) • x.1 = x.1
      simp
    mul_smul := by
      intro s t x
      apply Subtype.ext
      change ((s : G) * (t : G)) • x.1 = (s : G) • ((t : G) • x.1)
      simp [mul_smul] }
  have hstab : ∀ x : X, MulAction.stabilizer (c.S : Subgroup G) x = ⊥ := by
    intro x
    let g := Quotient.out x.1
    have hxg : (QuotientGroup.mk g : Ω) = x.1 := QuotientGroup.out_eq' x.1
    have hg : g ∉ G1 := by
      intro hgG1
      apply x.2
      -- `g ∈ G1` gives `mk g = mk 1 = q0`
      rw [← hxg]
      rw [QuotientGroup.eq]
      simpa using hgG1
    apply Subgroup.ext
    intro s
    constructor
    · intro hs
      have hsX : s • x = x := MulAction.mem_stabilizer_iff.mp hs
      have hsΩ : (s : G) • x.1 = x.1 := by
        change (s • x).1 = x.1
        exact congrArg Subtype.val hsX
      have hsG1 : (s : G) ∈ G1.map (MulAut.conj g).toMonoidHom :=
        (se_stabilizer_mem_iff c G1 e g s).mp (MulAction.mem_stabilizer_iff.mpr (by
          change (s : G) • (QuotientGroup.mk g : Ω) = QuotientGroup.mk g
          simpa [hxg] using hsΩ))
      have hsSG : (s : G) ∈ (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom :=
        ⟨s.2, hsG1⟩
      have hbot : (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom = ⊥ :=
        se_S_inter_conj_eq_bot c G1 e hg
      have hs1 : (s : G) = 1 := by
        have hmem : (s : G) ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact hsSG
        simpa [Subgroup.mem_bot] using hmem
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      exact hs1
    · intro hs
      rw [MulAction.mem_stabilizer_iff]
      rw [Subgroup.mem_bot] at hs
      subst hs
      apply Subtype.ext
      change (1 : G) • x.1 = x.1
      simp
  have hcardprod : Nat.card X =
      Nat.card (Quotient (MulAction.orbitRel (c.S : Subgroup G) X)) *
        Nat.card (c.S : Subgroup G) := by
    calc
      Nat.card X = Nat.card (Quotient (MulAction.orbitRel (c.S : Subgroup G) X) ×
          (c.S : Subgroup G)) :=
            Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd (G := (c.S : Subgroup G))
              (X := X) hstab)
      _ = Nat.card (Quotient (MulAction.orbitRel (c.S : Subgroup G) X)) *
          Nat.card (c.S : Subgroup G) := by rw [Nat.card_prod]
  have hcardX : Nat.card X = G1.index - 1 := by
    dsimp [X, Ω, q0]
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (p := fun q : G ⧸ G1 => q = (QuotientGroup.mk (1 : G) : G ⧸ G1))]
    rw [Fintype.card_subtype_eq]
    change Fintype.card (G ⧸ G1) - 1 = Nat.card (G ⧸ G1) - 1
    rw [Nat.card_eq_fintype_card]
  have hdvdd : Nat.card (c.S : Subgroup G) ∣ G1.index - 1 := by
    rw [← hcardX]
    exact ⟨Nat.card (Quotient (MulAction.orbitRel (c.S : Subgroup G) X)),
      by simpa [mul_comm] using hcardprod⟩
  have hSge4 : 4 ≤ Nat.card (c.S : Subgroup G) := by
    rw [S_nat_card]
    have h : 2 ≤ 2 ^ c.m := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) c.one_le_m
    nlinarith
  have hnpos : 0 < G1.index := by
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := G1))
  have hn1 : G1.index ≠ 1 := by
    intro h
    exact e.hproper ((Subgroup.index_eq_one).mp h)
  have h4dvdS : 4 ∣ Nat.card (c.S : Subgroup G) := by
    rw [S_nat_card]
    refine ⟨2 ^ (c.m - 1), ?_⟩
    have hpow : 2 * 2 ^ (c.m - 1) = 2 ^ c.m := by
      rw [mul_comm]
      rw [← pow_succ]
      rw [Nat.sub_add_cancel c.one_le_m]
    calc
      2 * 2 ^ c.m = 2 * (2 * 2 ^ (c.m - 1)) := by rw [hpow]
      _ = 4 * 2 ^ (c.m - 1) := by ring
  have h41 : 4 ∣ G1.index - 1 := dvd_trans h4dvdS hdvdd
  have hidx5 : G1.index = 5 := by
    have hpos : 0 < G1.index - 1 := by omega
    have hlt8 : G1.index - 1 < 8 := by
      have hle : G1.index ≤ 8 := Nat.le_of_lt_succ e.hlt
      omega
    have h4le : 4 ≤ G1.index - 1 := Nat.le_of_dvd hpos h41
    have hle4 : G1.index - 1 ≤ 4 := by
      rcases h41 with ⟨k, hk⟩
      have hklt : k < 2 := by omega
      have hkne0 : k ≠ 0 := by
        intro hk0
        have : G1.index - 1 = 0 := by simpa [hk0] using hk
        omega
      have hk1 : k = 1 := by omega
      omega
    have hsub : G1.index - 1 = 4 := le_antisymm hle4 h4le
    omega
  have hS4 : Nat.card (c.S : Subgroup G) = 4 := by
    have hdvd4 : Nat.card (c.S : Subgroup G) ∣ 4 := by
      simpa [hidx5] using hdvdd
    have hle : Nat.card (c.S : Subgroup G) ≤ 4 :=
      Nat.le_of_dvd (by norm_num : 0 < (4 : ℕ)) hdvd4
    exact le_antisymm hle hSge4
  exact ⟨hidx5, hS4⟩

/-- `S` fixes the base coset. -/
private lemma se_S_fix_base (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    (u : ↥(c.S : Subgroup G)) :
    (u : G) • (QuotientGroup.mk (1 : G) : G ⧸ G1) = QuotientGroup.mk (1 : G) := by
  exact MulAction.mem_stabilizer_iff.mp (by
    rw [MulAction.stabilizer_quotient G1]
    exact (se_S_le_G1 c G1 e) u.2)

/-- The stabilizer in `S` of any non-base coset is trivial. -/
private lemma se_stabilizer_bot_point (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    {x : G ⧸ G1} (hx : x ≠ QuotientGroup.mk (1 : G)) :
    MulAction.stabilizer (c.S : Subgroup G) x = ⊥ := by
  let g := Quotient.out x
  have hxg : (QuotientGroup.mk g : G ⧸ G1) = x := QuotientGroup.out_eq' x
  have hg : g ∉ G1 := by
    intro hgG1
    apply hx
    rw [← hxg]
    rw [QuotientGroup.eq]
    simpa using hgG1
  have h := se_stabilizer_bot c G1 e hg
  rwa [hxg] at h

/-- The number of non-base cosets is four. -/
private lemma se_card_compl (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    Nat.card {q : G ⧸ G1 // q ≠ QuotientGroup.mk (1 : G)} = 4 := by
  have hidx := (se_index_eq_five c G1 e).1
  have hcard : Nat.card {q : G ⧸ G1 // q ≠ QuotientGroup.mk (1 : G)} = G1.index - 1 := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (p := fun q : G ⧸ G1 =>
      q = (QuotientGroup.mk (1 : G) : G ⧸ G1))]
    rw [Fintype.card_subtype_eq]
    change Fintype.card (G ⧸ G1) - 1 = Nat.card (G ⧸ G1) - 1
    rw [Nat.card_eq_fintype_card]
  rw [hcard, hidx]

/-- `S` acts transitively on the four non-base cosets. -/
private lemma se_S_transitive_compl (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    {x y : G ⧸ G1} (hx : x ≠ QuotientGroup.mk (1 : G)) (hy : y ≠ QuotientGroup.mk (1 : G)) :
    ∃ u : ↥(c.S : Subgroup G), u • x = y := by
  classical
  let X' := {q : G ⧸ G1 // q ≠ QuotientGroup.mk (1 : G)}
  let f : ↥(c.S : Subgroup G) → X' := fun u => ⟨u • x, by
    intro h
    apply hx
    have h' : (u : G) • x = QuotientGroup.mk (1 : G) := by
      change (u • x : G ⧸ G1) = QuotientGroup.mk (1 : G)
      exact h
    calc
      x = (u : G)⁻¹ • ((u : G) • x) := by simp
      _ = (u : G)⁻¹ • QuotientGroup.mk (1 : G) := by rw [h']
      _ = QuotientGroup.mk (1 : G) := by simpa using se_S_fix_base c G1 e u⁻¹⟩
  have hf_inj : Function.Injective f := by
    intro u v h
    have hux : (u : G) • x = (v : G) • x := by
      change (f u).1 = (f v).1
      exact congrArg Subtype.val h
    have hfix' : ((v⁻¹ * u : ↥(c.S : Subgroup G)) : G) • x = x := by
      calc
        ((v⁻¹ * u : ↥(c.S : Subgroup G)) : G) • x = (v : G)⁻¹ • ((u : G) • x) := by
          change ((v : G)⁻¹ * (u : G)) • x = (v : G)⁻¹ • ((u : G) • x)
          simp [mul_smul]
        _ = (v : G)⁻¹ • ((v : G) • x) := by rw [hux]
        _ = x := by simp
    have hstab : (v⁻¹ * u : ↥(c.S : Subgroup G)) ∈
        MulAction.stabilizer (c.S : Subgroup G) x := by
      rw [MulAction.mem_stabilizer_iff]
      change ((v⁻¹ * u : ↥(c.S : Subgroup G)) : G) • x = x
      exact hfix'
    have hbot := se_stabilizer_bot_point c G1 e hx
    have h1 : (v⁻¹ * u : ↥(c.S : Subgroup G)) = 1 := by
      have hm : (v⁻¹ * u : ↥(c.S : Subgroup G)) ∈ (⊥ : Subgroup (↥(c.S : Subgroup G))) := by
        rw [← hbot]
        exact hstab
      simpa [Subgroup.mem_bot] using hm
    apply Subtype.ext
    have h1' : ((v⁻¹ * u : ↥(c.S : Subgroup G)) : G) = 1 := congrArg Subtype.val h1
    calc
      (u : G) = (v : G) * ((v : G)⁻¹ * (u : G)) := by group
      _ = (v : G) * 1 := by
        have : ((v : G)⁻¹ * (u : G)) = 1 := by simpa using h1'
        rw [this]
      _ = (v : G) := by simp
  have hcardS : Fintype.card ↥(c.S : Subgroup G) = 4 := by
    rw [← Nat.card_eq_fintype_card, (se_index_eq_five c G1 e).2]
  have hcardX : Fintype.card X' = 4 := by
    rw [← Nat.card_eq_fintype_card, se_card_compl c G1 e]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf_inj, by simpa [hcardS, hcardX]⟩
  let y' : X' := ⟨y, hy⟩
  rcases hbij.2 y' with ⟨u, hu⟩
  exact ⟨u, congrArg Subtype.val hu⟩

/-- Every element of `S` is an involution: `S` is a Klein four group. -/
private lemma se_S_exp_two (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    ∀ s : ↥(c.S : Subgroup G), (s : G) ^ 2 = 1 := by
  intro s
  have hS4 := (se_index_eq_five c G1 e).2
  have hm : c.m = 1 := by
    have h : 2 * 2 ^ c.m = 4 := by
      rw [← S_nat_card c, hS4]
    have h2 : 2 ^ c.m = 2 :=
      Nat.mul_left_cancel (by norm_num : 0 < 2) (by simpa [mul_comm] using h)
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using h2)
  have hExpD : ∀ x : DihedralGroup (2 ^ c.m), x ^ 2 = 1 := by
    rw [hm]
    intro x
    rcases x with i | i
    · rw [pow_two, DihedralGroup.r_mul_r]
      have hii : i + i = (0 : ZMod 2) := by fin_cases i <;> decide
      rw [hii, DihedralGroup.r_zero]
    · rw [pow_two, DihedralGroup.sr_mul_sr]
      have h : i - i = (0 : ZMod 2) := by fin_cases i <;> decide
      rw [h, DihedralGroup.r_zero]
  rcases c.dihedralEquiv with ⟨eD⟩
  have hs2 : s ^ 2 = 1 := by
    apply eD.injective
    rw [map_pow, hExpD (eD s), map_one]
  simpa using congrArg Subtype.val hs2

/-- The kernel of the permutation action has odd order. -/
private lemma se_ker_odd (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    Odd (Nat.card (seφ G1).ker) := by
  have hker : (seφ G1).ker = G1.normalCore := by
    simpa [seφ] using (Subgroup.normalCore_eq_ker (H := G1)).symm
  obtain ⟨g, hgnot⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr e.hproper)
  have hK_le : G1.normalCore ≤ G1 ⊓ G1.map (MulAut.conj g).toMonoidHom := by
    intro k hk
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.normalCore_le G1 hk, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · exact (Subgroup.normalCore_le G1)
        (by simpa using ((Subgroup.normalCore_normal G1).conj_mem k hk (g⁻¹)))
    · change g * (g⁻¹ * k * g) * g⁻¹ = k
      group
  have hdv : Nat.card (seφ G1).ker ∣
      Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
    rw [hker]
    exact Subgroup.card_dvd_of_le hK_le
  have hoddD : Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
    e.hodd g hgnot.2
  apply Nat.not_even_iff_odd.mp
  intro heven
  have h2ker : 2 ∣ Nat.card (seφ G1).ker := even_iff_two_dvd.mp heven
  exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_trans h2ker hdv))) hoddD

/-- The kernel of the permutation action meets `S` trivially. -/
private lemma se_ker_inter_S_bot (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    (seφ G1).ker ⊓ (c.S : Subgroup G) = ⊥ := by
  have hker : (seφ G1).ker = G1.normalCore := by
    simpa [seφ] using (Subgroup.normalCore_eq_ker (H := G1)).symm
  obtain ⟨g, hgnot⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr e.hproper)
  have hK_le : G1.normalCore ≤ G1 ⊓ G1.map (MulAut.conj g).toMonoidHom := by
    intro k hk
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.normalCore_le G1 hk, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · exact (Subgroup.normalCore_le G1)
        (by simpa using ((Subgroup.normalCore_normal G1).conj_mem k hk (g⁻¹)))
    · change g * (g⁻¹ * k * g) * g⁻¹ = k
      group
  have hoddK : Odd (Nat.card (seφ G1).ker) := by
    have hdv : Nat.card (seφ G1).ker ∣
        Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
      rw [hker]
      exact Subgroup.card_dvd_of_le hK_le
    have hoddD : Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
      e.hodd g hgnot.2
    apply Nat.not_even_iff_odd.mp
    intro heven
    have h2ker : 2 ∣ Nat.card (seφ G1).ker := even_iff_two_dvd.mp heven
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_trans h2ker hdv))) hoddD
  have hcop : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card (seφ G1).ker) := by
    rw [S_nat_card]
    have hcop2 : Nat.Coprime 2 (Nat.card (seφ G1).ker) := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro h2
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2)) hoddK
    exact Nat.Coprime.mul_left hcop2 (Nat.Coprime.pow_left c.m hcop2)
  rw [inf_comm]
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (G := G) hcop)

/-- `φ` is injective on `S`. -/
private lemma se_φ_injective_on_S (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    Function.Injective (fun s : ↥(c.S : Subgroup G) => seφ G1 (s : G)) := by
  intro s t h
  have hmem : ((s⁻¹ * t : ↥(c.S : Subgroup G)) : G) ∈ (seφ G1).ker := by
    rw [MonoidHom.mem_ker]
    have hmap : seφ G1 ((s : G)⁻¹ * (t : G)) = 1 := by
      rw [map_mul, map_inv]
      have h' : seφ G1 (s : G) = seφ G1 (t : G) := by simpa using h
      rw [h', inv_mul_cancel]
    simpa using hmap
  have hkerS : ((s⁻¹ * t : ↥(c.S : Subgroup G)) : G) ∈
      (seφ G1).ker ⊓ (c.S : Subgroup G) :=
    ⟨hmem, (s⁻¹ * t : ↥(c.S : Subgroup G)).2⟩
  have hbot : (seφ G1).ker ⊓ (c.S : Subgroup G) = ⊥ := se_ker_inter_S_bot c G1 e
  have h1 : ((s⁻¹ * t : ↥(c.S : Subgroup G)) : G) = 1 := by
    have hmem' : ((s⁻¹ * t : ↥(c.S : Subgroup G)) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hkerS
    simpa [Subgroup.mem_bot] using hmem'
  apply Subtype.ext
  have hst : (s : G)⁻¹ * (t : G) = 1 := by simpa using h1
  exact inv_mul_eq_one.mp hst

/-- The image of `S` in the permutation group, of order four. -/
private def seVS (c : Hyp11 G) (G1 : Subgroup G) : Subgroup (Equiv.Perm (G ⧸ G1)) :=
  (c.S : Subgroup G).map (seφ G1)

private lemma se_VS_card (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    Nat.card (seVS c G1) = 4 := by
  let φS : ↥(c.S : Subgroup G) →* Equiv.Perm (G ⧸ G1) :=
    (seφ G1).comp (c.S : Subgroup G).subtype
  have hφS : Function.Injective φS := se_φ_injective_on_S c G1 e
  have hmap : (⊤ : Subgroup (↥(c.S : Subgroup G))).map φS = seVS c G1 := by
    ext σ
    constructor
    · intro h
      rw [Subgroup.mem_map] at h
      rcases h with ⟨s, hs, rfl⟩
      dsimp [seVS]
      rw [Subgroup.mem_map]
      exact ⟨(s : G), s.2, rfl⟩
    · intro h
      dsimp [seVS] at h
      rw [Subgroup.mem_map] at h
      rcases h with ⟨s, hsS, rfl⟩
      rw [Subgroup.mem_map]
      exact ⟨⟨s, hsS⟩, Subgroup.mem_top _, by simpa [φS]⟩
  rw [← hmap, Subgroup.card_map_of_injective hφS]
  rw [Subgroup.card_top]
  exact (se_index_eq_five c G1 e).2

/-- `φ(S)` fixes the base coset. -/
private lemma se_VS_fix_base (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    seVS c G1 ≤
      MulAction.stabilizer (Equiv.Perm (G ⧸ G1)) (QuotientGroup.mk (1 : G) : G ⧸ G1) := by
  intro v hv
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hv
  rw [MulAction.mem_stabilizer_iff]
  change (seφ G1 s) (QuotientGroup.mk (1 : G) : G ⧸ G1) = QuotientGroup.mk (1 : G)
  simp [seφ, se_S_fix_base c G1 e ⟨s, hsS⟩]

/-- Nontrivial elements of `φ(S)` move every non-base coset. -/
private lemma se_VS_free (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    ∀ v : seVS c G1, v ≠ 1 → ∀ q : G ⧸ G1, q ≠ QuotientGroup.mk (1 : G) → v • q ≠ q := by
  intro v hv q hq hvq
  rcases Subgroup.mem_map.mp v.2 with ⟨s, hsS, hvs⟩
  let sS : ↥(c.S : Subgroup G) := ⟨s, hsS⟩
  have hs1 : s ≠ 1 := by
    intro hs
    apply hv
    apply Subtype.ext
    rw [← hvs, hs, map_one]
    rfl
  let g := Quotient.out q
  have hqg : (QuotientGroup.mk g : G ⧸ G1) = q := QuotientGroup.out_eq' q
  have hg : g ∉ G1 := by
    intro hgG1
    apply hq
    rw [← hqg]
    rw [QuotientGroup.eq]
    simpa using hgG1
  have hfixq : (s : G) • q = q := by
    have hvq' : (seφ G1 s) • q = q := by
      rw [hvs]
      exact hvq
    simpa [seφ] using hvq'
  have hstab : sS ∈ MulAction.stabilizer (c.S : Subgroup G) (QuotientGroup.mk g : G ⧸ G1) := by
    rw [MulAction.mem_stabilizer_iff]
    change (sS : G) • (QuotientGroup.mk g : G ⧸ G1) = QuotientGroup.mk g
    simpa [sS, hqg] using hfixq
  have hsG1 : (s : G) ∈ G1.map (MulAut.conj g).toMonoidHom :=
    (se_stabilizer_mem_iff c G1 e g sS).mp hstab
  have hsSG : (s : G) ∈ (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom :=
    ⟨hsS, hsG1⟩
  have hbot : (c.S : Subgroup G) ⊓ G1.map (MulAut.conj g).toMonoidHom = ⊥ :=
    se_S_inter_conj_eq_bot c G1 e hg
  have hs1' : (s : G) = 1 := by
    have hmem : (s : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hsSG
    simpa [Subgroup.mem_bot] using hmem
  exact hs1 hs1'

/-- `φ(S)` acts transitively on the four non-base cosets. -/
private lemma se_VS_transitive_compl (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    ∀ {x y : G ⧸ G1}, x ≠ QuotientGroup.mk (1 : G) → y ≠ QuotientGroup.mk (1 : G) →
      ∃ v : seVS c G1, v • x = y := by
  intro x y hx hy
  rcases se_S_transitive_compl c G1 e hx hy with ⟨u, hu⟩
  refine ⟨⟨seφ G1 (u : G), ?_⟩, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨(u : G), u.2, rfl⟩
  · change (u : G) • x = y
    exact hu

/-- The image of `S` lies inside the permutation image of `G`. -/
private lemma se_VS_le_range (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    seVS c G1 ≤ (seφ G1).range := by
  intro σ hσ
  dsimp [seVS] at hσ
  rw [Subgroup.mem_map] at hσ
  rcases hσ with ⟨s, hs, rfl⟩
  exact ⟨s, rfl⟩

/-- Every element of `φ(S)` squares to one. -/
private lemma se_VS_exp_two (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    ∀ v : seVS c G1, v ^ 2 = 1 := by
  intro v
  rcases Subgroup.mem_map.mp v.2 with ⟨s, hsS, hvs⟩
  apply Subtype.ext
  change ((v : Equiv.Perm (G ⧸ G1)) ^ 2) = 1
  rw [← hvs]
  rw [← map_pow]
  have hs2 : (s : G) ^ 2 = 1 := se_S_exp_two c G1 e ⟨s, hsS⟩
  simpa [hs2] using (map_one (seφ G1))

/-- The permutation image of `G` is transitive on the cosets of `G1`. -/
private lemma se_range_transitive (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    (x : G ⧸ G1) :
    ∃ σ : (seφ G1).range,
      (σ : Equiv.Perm (G ⧸ G1)) • (QuotientGroup.mk (1 : G) : G ⧸ G1) = x := by
  classical
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  have hbase : ∀ y : Ω, ∃ g : G, g • q0 = y :=
    (MulAction.isPretransitive_iff_base (G := G) (X := Ω) q0).mp
      (inferInstance : MulAction.IsPretransitive G Ω)
  rcases hbase x with ⟨g, hg⟩
  refine ⟨⟨seφ G1 g, ⟨g, rfl⟩⟩, ?_⟩
  change (seφ G1 g) • q0 = x
  simpa [seφ] using hg

/-- The stabilizer of the base coset in the permutation image acts transitively
on the four non-base cosets. -/
private lemma se_range_stabilizer_transitive (c : Hyp11 G) (G1 : Subgroup G)
    (e : SEContext c G1) {x y : G ⧸ G1}
    (hx : x ≠ QuotientGroup.mk (1 : G)) (hy : y ≠ QuotientGroup.mk (1 : G)) :
    ∃ σ : (seφ G1).range,
      (σ : Equiv.Perm (G ⧸ G1)) • (QuotientGroup.mk (1 : G) : G ⧸ G1) =
          QuotientGroup.mk (1 : G) ∧
        (σ : Equiv.Perm (G ⧸ G1)) • x = y := by
  rcases se_S_transitive_compl c G1 e hx hy with ⟨u, hu⟩
  refine ⟨⟨seφ G1 (u : G), ⟨u, rfl⟩⟩, ?_, ?_⟩
  · change (seφ G1 (u : G)) • (QuotientGroup.mk (1 : G) : G ⧸ G1) =
      QuotientGroup.mk (1 : G)
    simpa [seφ] using se_S_fix_base c G1 e u
  · change (seφ G1 (u : G)) • x = y
    change (u : G) • x = y
    exact hu

/-- The permutation image of `G` is two-transitive on the five cosets of `G1`. -/
private lemma se_range_two_pretransitive (c : Hyp11 G) (G1 : Subgroup G)
    (e : SEContext c G1) :
    MulAction.IsMultiplyPretransitive (seφ G1).range (G ⧸ G1) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c' d' hab hcd
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  obtain ⟨u, hu⟩ := se_range_transitive c G1 e a
  obtain ⟨v, hv⟩ := se_range_transitive c G1 e c'
  have ha' : u⁻¹ • b ≠ q0 := by
    intro h
    apply hab
    calc
      a = u • q0 := hu.symm
      _ = u • (u⁻¹ • b) := by rw [← h]
      _ = b := by simp
  have hd' : v⁻¹ • d' ≠ q0 := by
    intro h
    apply hcd
    calc
      c' = v • q0 := hv.symm
      _ = v • (v⁻¹ • d') := by rw [← h]
      _ = d' := by simp
  rcases se_range_stabilizer_transitive c G1 e ha' hd' with ⟨w, hwfix, hwmap⟩
  refine ⟨v * w * u⁻¹, ?_, ?_⟩
  · calc
      (v * w * u⁻¹) • a = v • (w • (u⁻¹ • a)) := by simp [mul_smul]
      _ = c' := by
        have huq : u⁻¹ • a = q0 := by
          rw [MulAction.subgroup_smul_def]
          rw [← hu]
          simpa [q0]
        calc
          v • (w • (u⁻¹ • a)) = v • (w • q0) := by rw [huq]
          _ = v • q0 := by
            have hwq : w • q0 = q0 := by
              change (w : Equiv.Perm Ω) • q0 = q0
              rw [Equiv.Perm.smul_def]
              exact hwfix
            rw [hwq]
          _ = c' := hv
  · calc
      (v * w * u⁻¹) • b = v • (w • (u⁻¹ • b)) := by simp [mul_smul]
      _ = v • (v⁻¹ • d') := by
        have hwm : w • (u⁻¹ • b) = v⁻¹ • d' := by
          change (w : Equiv.Perm Ω) • (u⁻¹ • b) = v⁻¹ • d'
          rw [Equiv.Perm.smul_def]
          exact hwmap
        rw [hwm]
      _ = d' := by simp

/-! ## The Klein four `φ(S)` inside `A₅` -/

private def fin5A : Equiv.Perm (Fin 5) :=
  Equiv.swap (1 : Fin 5) (2 : Fin 5) * Equiv.swap (3 : Fin 5) (4 : Fin 5)

private def fin5B : Equiv.Perm (Fin 5) :=
  Equiv.swap (1 : Fin 5) (3 : Fin 5) * Equiv.swap (2 : Fin 5) (4 : Fin 5)

private def fin5C : Equiv.Perm (Fin 5) :=
  Equiv.swap (1 : Fin 5) (4 : Fin 5) * Equiv.swap (2 : Fin 5) (3 : Fin 5)

/-- An involution of `Perm (Fin 5)` fixing `0` and with no other fixed point
is one of the three double transpositions. -/
private lemma fin5_doubleTransposition_of_involution_fix_zero {v : Equiv.Perm (Fin 5)}
    (hv0 : v (0 : Fin 5) = 0) (hvsq : v ^ 2 = 1) (hvne : v ≠ 1)
    (hvfix : ∀ i : Fin 5, i ≠ 0 → v i ≠ i) :
    v = fin5A ∨ v = fin5B ∨ v = fin5C := by
  have hvv (x : Fin 5) : v (v x) = x := by
    have hx := DFunLike.ext_iff.mp hvsq x
    rw [pow_two] at hx
    simpa using hx
  have hv10 : v (1 : Fin 5) ≠ 0 := by
    intro h
    have : (1 : Fin 5) = 0 := v.injective (by simpa [hv0] using h)
    norm_num at this
  have hv11 : v (1 : Fin 5) ≠ 1 := hvfix 1 (by norm_num)
  have h1 : ∃ j : Fin 5, v (1 : Fin 5) = j := ⟨v (1 : Fin 5), rfl⟩
  rcases h1 with ⟨j1, hj1⟩
  fin_cases j1
  · exfalso; exact hv10 (hj1.trans (Fin.ext rfl))
  · exfalso; exact hv11 (hj1.trans (Fin.ext rfl))
  · -- v 1 = 2
    have hv1 : v (1 : Fin 5) = (2 : Fin 5) := hj1.trans (Fin.ext rfl)
    have hv2 : v (2 : Fin 5) = 1 := by simpa [hv1] using hvv 1
    have hv31 : v (3 : Fin 5) ≠ 1 := by
      intro h
      have : (3 : Fin 5) = 2 := v.injective (by simpa [hv2] using h)
      exact (by decide : (3 : Fin 5) ≠ (2 : Fin 5)) this
    have hv32 : v (3 : Fin 5) ≠ 2 := by
      intro h
      have : (3 : Fin 5) = 1 := v.injective (by simpa [hv1] using h)
      exact (by decide : (3 : Fin 5) ≠ (1 : Fin 5)) this
    have hv33 : v (3 : Fin 5) ≠ 3 := hvfix 3 (by decide)
    have hv30 : v (3 : Fin 5) ≠ 0 := by
      intro h
      have : (3 : Fin 5) = 0 := v.injective (by simpa [hv0] using h)
      exact (by decide : (3 : Fin 5) ≠ (0 : Fin 5)) this
    have hv3 : v (3 : Fin 5) = 4 := by
      have h3 : ∃ j : Fin 5, v (3 : Fin 5) = j := ⟨v (3 : Fin 5), rfl⟩
      rcases h3 with ⟨j3, hj3⟩
      fin_cases j3
      · exfalso; exact hv30 (hj3.trans (Fin.ext rfl))
      · exfalso; exact hv31 (hj3.trans (Fin.ext rfl))
      · exfalso; exact hv32 (hj3.trans (Fin.ext rfl))
      · exfalso; exact hv33 (hj3.trans (Fin.ext rfl))
      · exact hj3.trans (Fin.ext rfl)
    have hv4 : v (4 : Fin 5) = 3 := by simpa [hv3] using hvv 3
    left
    ext i
    fin_cases i <;> (simp [fin5A, hv0, hv1, hv2, hv3, hv4]; decide)
  · -- v 1 = 3
    have hv1 : v (1 : Fin 5) = (3 : Fin 5) := hj1.trans (Fin.ext rfl)
    have hv3 : v (3 : Fin 5) = 1 := by simpa [hv1] using hvv 1
    have hv20 : v (2 : Fin 5) ≠ 0 := by
      intro h
      have : (2 : Fin 5) = 0 := v.injective (by simpa [hv0] using h)
      exact (by decide : (2 : Fin 5) ≠ (0 : Fin 5)) this
    have hv21 : v (2 : Fin 5) ≠ 1 := by
      intro h
      have : (2 : Fin 5) = 3 := v.injective (by simpa [hv3] using h)
      exact (by decide : (2 : Fin 5) ≠ (3 : Fin 5)) this
    have hv22 : v (2 : Fin 5) ≠ 2 := hvfix 2 (by decide)
    have hv23 : v (2 : Fin 5) ≠ 3 := by
      intro h
      have : (2 : Fin 5) = 1 := v.injective (by simpa [hv1] using h)
      exact (by decide : (2 : Fin 5) ≠ (1 : Fin 5)) this
    have hv2 : v (2 : Fin 5) = 4 := by
      have h2 : ∃ j : Fin 5, v (2 : Fin 5) = j := ⟨v (2 : Fin 5), rfl⟩
      rcases h2 with ⟨j2, hj2⟩
      fin_cases j2
      · exfalso; exact hv20 (hj2.trans (Fin.ext rfl))
      · exfalso; exact hv21 (hj2.trans (Fin.ext rfl))
      · exfalso; exact hv22 (hj2.trans (Fin.ext rfl))
      · exfalso; exact hv23 (hj2.trans (Fin.ext rfl))
      · exact hj2.trans (Fin.ext rfl)
    have hv4 : v (4 : Fin 5) = 2 := by simpa [hv2] using hvv 2
    right; left
    ext i
    fin_cases i <;> (simp [fin5B, hv0, hv1, hv2, hv3, hv4]; decide)
  · -- v 1 = 4
    have hv1 : v (1 : Fin 5) = (4 : Fin 5) := hj1.trans (Fin.ext rfl)
    have hv4 : v (4 : Fin 5) = 1 := by simpa [hv1] using hvv 1
    have hv20 : v (2 : Fin 5) ≠ 0 := by
      intro h
      have : (2 : Fin 5) = 0 := v.injective (by simpa [hv0] using h)
      exact (by decide : (2 : Fin 5) ≠ (0 : Fin 5)) this
    have hv21 : v (2 : Fin 5) ≠ 1 := by
      intro h
      have : (2 : Fin 5) = 4 := v.injective (by simpa [hv4] using h)
      exact (by decide : (2 : Fin 5) ≠ (4 : Fin 5)) this
    have hv22 : v (2 : Fin 5) ≠ 2 := hvfix 2 (by decide)
    have hv24 : v (2 : Fin 5) ≠ 4 := by
      intro h
      have : (2 : Fin 5) = 1 := v.injective (by simpa [hv1] using h)
      exact (by decide : (2 : Fin 5) ≠ (1 : Fin 5)) this
    have hv2 : v (2 : Fin 5) = 3 := by
      have h2 : ∃ j : Fin 5, v (2 : Fin 5) = j := ⟨v (2 : Fin 5), rfl⟩
      rcases h2 with ⟨j2, hj2⟩
      fin_cases j2
      · exfalso; exact hv20 (hj2.trans (Fin.ext rfl))
      · exfalso; exact hv21 (hj2.trans (Fin.ext rfl))
      · exfalso; exact hv22 (hj2.trans (Fin.ext rfl))
      · exact hj2.trans (Fin.ext rfl)
      · exfalso; exact hv24 (hj2.trans (Fin.ext rfl))
    have hv3 : v (3 : Fin 5) = 2 := by simpa [hv2] using hvv 2
    right; right
    ext i
    fin_cases i <;> (simp [fin5C, hv0, hv1, hv2, hv3, hv4]; decide)

/-- A 3-cycle in the subgroup generated by the rotation `finRotate 5` and a
double transposition `fin5A`. -/
private lemma fin5_wordA_mem (cl : Subgroup (Equiv.Perm (Fin 5)))
    (hρ : finRotate 5 ∈ cl) (hA : fin5A ∈ cl) :
    ∃ c : Equiv.Perm (Fin 5), Equiv.Perm.IsThreeCycle c ∧ c ∈ cl := by
  let ρ : Equiv.Perm (Fin 5) := finRotate 5
  let c : Equiv.Perm (Fin 5) := fin5A * (ρ * fin5A * (ρ⁻¹) ^ 2)
  refine ⟨c, ?_, ?_⟩
  · have hc : c = Equiv.swap (1 : Fin 5) (3 : Fin 5) * Equiv.swap (3 : Fin 5) (4 : Fin 5) := by
      decide
    rw [hc]
    simpa [Equiv.swap_comm] using
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (3 : Fin 5)) (b := (1 : Fin 5)) (c := (4 : Fin 5))
        (by decide : (3 : Fin 5) ≠ 1) (by decide : (3 : Fin 5) ≠ 4)
        (by decide : (1 : Fin 5) ≠ 4))
  · have hρinv2 : (ρ⁻¹) ^ 2 ∈ cl := by
      rw [pow_two]
      exact Subgroup.mul_mem cl (Subgroup.inv_mem cl hρ) (Subgroup.inv_mem cl hρ)
    dsimp [c]
    exact Subgroup.mul_mem cl hA (Subgroup.mul_mem cl (Subgroup.mul_mem cl hρ hA) hρinv2)

/-- A 3-cycle in the subgroup generated by the rotation `finRotate 5` and a
double transposition `fin5B`. -/
private lemma fin5_wordB_mem (cl : Subgroup (Equiv.Perm (Fin 5)))
    (hρ : finRotate 5 ∈ cl) (hB : fin5B ∈ cl) :
    ∃ c : Equiv.Perm (Fin 5), Equiv.Perm.IsThreeCycle c ∧ c ∈ cl := by
  let ρ : Equiv.Perm (Fin 5) := finRotate 5
  let c : Equiv.Perm (Fin 5) := fin5B * (ρ * fin5B * ρ⁻¹)
  refine ⟨c, ?_, ?_⟩
  · have hc : c = Equiv.swap (0 : Fin 5) (1 : Fin 5) * Equiv.swap (1 : Fin 5) (3 : Fin 5) := by
      decide
    rw [hc]
    exact card_support_eq_three_iff.mp (by decide)
  · dsimp [c]
    exact Subgroup.mul_mem cl hB
      (Subgroup.mul_mem cl (Subgroup.mul_mem cl hρ hB) (Subgroup.inv_mem cl hρ))

/-- A Klein-four subgroup of `Perm (Fin 5)` fixing `0` and acting freely on the
other four points generates a 3-cycle together with `finRotate 5`. -/
private lemma fin5_threeCycle_of_V4 (V : Subgroup (Equiv.Perm (Fin 5)))
    (hcard : Nat.card V = 4) (hexp : ∀ v : V, v ^ 2 = 1)
    (hfix0 : ∀ v : V, (v : Equiv.Perm (Fin 5)) (0 : Fin 5) = 0)
    (hfree : ∀ v : V, v ≠ 1 → ∀ i : Fin 5, i ≠ 0 →
      (v : Equiv.Perm (Fin 5)) i ≠ i) :
    ∃ c : Equiv.Perm (Fin 5), Equiv.Perm.IsThreeCycle c ∧
      c ∈ Subgroup.closure (({finRotate 5} : Set (Equiv.Perm (Fin 5))) ∪ V) := by
  classical
  let ρ : Equiv.Perm (Fin 5) := finRotate 5
  let cl : Subgroup (Equiv.Perm (Fin 5)) :=
    Subgroup.closure (({ρ} : Set (Equiv.Perm (Fin 5))) ∪ V)
  have hρ : ρ ∈ cl := Subgroup.subset_closure (by simp)
  have hcardF : Fintype.card V = 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have hone : 1 < Fintype.card V := by rw [hcardF]; norm_num
  obtain ⟨v, hvne1⟩ := Fintype.exists_ne_of_one_lt_card hone (1 : V)
  have hvclass : (v : Equiv.Perm (Fin 5)) = fin5A ∨ (v : Equiv.Perm (Fin 5)) = fin5B ∨
      (v : Equiv.Perm (Fin 5)) = fin5C := by
    exact fin5_doubleTransposition_of_involution_fix_zero (hfix0 v)
      (congrArg Subtype.val (hexp v)) (by simpa using hvne1)
      (fun i hi => hfree v hvne1 i hi)
  rcases hvclass with hvA | hvB | hvC
  · have hA : (fin5A : Equiv.Perm (Fin 5)) ∈ cl := Subgroup.subset_closure (by
      right
      exact hvA ▸ v.2)
    exact fin5_wordA_mem cl hρ hA
  · have hB : (fin5B : Equiv.Perm (Fin 5)) ∈ cl := Subgroup.subset_closure (by
      right
      exact hvB ▸ v.2)
    exact fin5_wordB_mem cl hρ hB
  · have hthird : ∃ w : V, w ≠ 1 ∧ w ≠ v := by
      by_contra h
      push Not at h
      let f : V → Fin 2 := fun w => if w = 1 then 0 else 1
      have hf : Function.Injective f := by
        intro a b hab
        by_cases ha : a = 1 <;> by_cases hb : b = 1
        · simp [ha, hb]
        · exfalso
          simp [f, ha, hb] at hab
        · exfalso
          simp [f, ha, hb] at hab
        · have ha' : a = v := h a ha
          have hb' : b = v := h b hb
          simp [ha', hb']
      have hle : Fintype.card V ≤ Fintype.card (Fin 2) :=
        Fintype.card_le_of_injective f hf
      have hle' : Fintype.card V ≤ 2 := by simpa using hle
      omega
    rcases hthird with ⟨w, hw1, hwv⟩
    have hwclass : (w : Equiv.Perm (Fin 5)) = fin5A ∨ (w : Equiv.Perm (Fin 5)) = fin5B ∨
        (w : Equiv.Perm (Fin 5)) = fin5C := by
      exact fin5_doubleTransposition_of_involution_fix_zero (hfix0 w)
        (congrArg Subtype.val (hexp w)) (by simpa using hw1)
        (fun i hi => hfree w hw1 i hi)
    rcases hwclass with hwA | hwB | hwC
    · have hA : (fin5A : Equiv.Perm (Fin 5)) ∈ cl := Subgroup.subset_closure (by
        right
        exact hwA ▸ w.2)
      exact fin5_wordA_mem cl hρ hA
    · have hB : (fin5B : Equiv.Perm (Fin 5)) ∈ cl := Subgroup.subset_closure (by
        right
        exact hwB ▸ w.2)
      exact fin5_wordB_mem cl hρ hB
    · exfalso
      apply hwv
      apply Subtype.ext
      simpa [hwC, hvC]

/-- Conjugation by an equivalence preserves the support size of a permutation. -/
private lemma permCongr_support_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (p : Equiv.Perm α) :
    (e.permCongr p).support.card = p.support.card := by
  have h : (e.permCongr p).support = p.support.map ⟨e, e.injective⟩ := by
    ext x
    rw [Finset.mem_map]
    constructor
    · intro hx
      refine ⟨e.symm x, ?_, ?_⟩
      · rw [Equiv.Perm.mem_support]
        intro h
        apply (Equiv.Perm.mem_support.mp hx)
        rw [Equiv.permCongr_apply, h]
        simp
      · simp
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      rw [Equiv.Perm.mem_support]
      rw [Equiv.permCongr_apply]
      intro h
      apply (Equiv.Perm.mem_support.mp hy)
      exact e.injective (by simpa using h)
  rw [h]
  simp

/-- Conjugation by an equivalence preserves being a three-cycle. -/
private lemma permCongr_isThreeCycle {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) {p : Equiv.Perm α}
    (hp : Equiv.Perm.IsThreeCycle p) : Equiv.Perm.IsThreeCycle (e.permCongr p) := by
  rw [← card_support_eq_three_iff]
  rw [permCongr_support_card]
  exact card_support_eq_three_iff.mpr hp

/-- Five divides the order of the permutation image of `G`. -/
private lemma se_five_dvd_range_card (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    5 ∣ Nat.card (seφ G1).range := by
  have hker : (seφ G1).ker = G1.normalCore := by
    simpa [seφ] using (Subgroup.normalCore_eq_ker (H := G1)).symm
  have hcard : Nat.card (seφ G1).range = (seφ G1).ker.index := by
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (seφ G1)).toEquiv).symm
  have hdvd : G1.index ∣ (seφ G1).ker.index := by
    rw [hker]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le G1)
  rw [hcard]
  rw [(se_index_eq_five c G1 e).1] at hdvd
  exact hdvd

/-- The permutation image contains an element of order five. -/
private lemma se_exists_order_five (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    ∃ σ : (seφ G1).range, orderOf σ = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card' (G := (seφ G1).range) 5
    (se_five_dvd_range_card c G1 e)

/-- The point stabilizer of `Perm Ω` at the base coset has order `4! = 24`. -/
private lemma se_stabilizer_perm_card (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (G ⧸ G1))
      (QuotientGroup.mk (1 : G) : G ⧸ G1)) = 24 := by
  classical
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  have hrange : (Equiv.Perm.ofSubtype :
        Equiv.Perm {x : Ω // x ≠ q0} →* Equiv.Perm Ω).range =
      MulAction.stabilizer (Equiv.Perm Ω) q0 := by
    ext σ
    rw [MonoidHom.mem_range, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      rcases h with ⟨τ, rfl⟩
      by_contra hfix
      have hq : q0 ∈ ((Equiv.Perm.ofSubtype τ : Equiv.Perm Ω).support : Set Ω) := by
        change q0 ∈ (Equiv.Perm.ofSubtype τ : Equiv.Perm Ω).support
        rw [Equiv.Perm.mem_support]
        exact hfix
      rcases (Equiv.Perm.mem_support_ofSubtype q0 τ).mp hq with ⟨hq0, _⟩
      exact hq0 rfl
    · intro hfix
      have hsub : ((σ.support : Set Ω) : Set Ω) ⊆ {x : Ω | x ≠ q0} := by
        intro x hx
        rw [Set.mem_setOf_eq]
        intro hxq
        rw [hxq] at hx
        exact ((Equiv.Perm.mem_support.mp hx) hfix)
      have hmem : σ ∈ (Equiv.Perm.ofSubtype :
          Equiv.Perm {x : Ω // x ≠ q0} →* Equiv.Perm Ω).range :=
        Equiv.Perm.mem_range_ofSubtype_iff.mpr hsub
      exact MonoidHom.mem_range.mp hmem
  have hcard : Nat.card (MulAction.stabilizer (Equiv.Perm Ω) q0) =
      Nat.card (Equiv.Perm {x : Ω // x ≠ q0}) := by
    rw [← hrange]
    have hinj : Function.Injective
        (Equiv.Perm.ofSubtype : Equiv.Perm {x : Ω // x ≠ q0} →* Equiv.Perm Ω) :=
      Equiv.Perm.ofSubtype_injective
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hperm : Nat.card (Equiv.Perm {x : Ω // x ≠ q0}) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have h4 : Fintype.card {x : Ω // x ≠ q0} = 4 := by
      rw [← Nat.card_eq_fintype_card, se_card_compl c G1 e]
    rw [h4]
    norm_num
  rw [hcard, hperm]

/-- An element of order five in the permutation image moves the base coset. -/
private lemma se_order_five_not_fix_base (c : Hyp11 G) (G1 : Subgroup G)
    (e : SEContext c G1) {σ : (seφ G1).range} (hσ : orderOf σ = 5) :
    (σ : Equiv.Perm (G ⧸ G1)) (QuotientGroup.mk (1 : G)) ≠ QuotientGroup.mk (1 : G) := by
  classical
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  intro hfix
  have hmem : (σ : Equiv.Perm Ω) ∈ MulAction.stabilizer (Equiv.Perm Ω) q0 := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfix
  let τ : ↥(MulAction.stabilizer (Equiv.Perm Ω) q0) := ⟨σ, hmem⟩
  have hdvd : orderOf (σ : Equiv.Perm Ω) ∣
      Nat.card (MulAction.stabilizer (Equiv.Perm Ω) q0) := by
    have h := orderOf_dvd_natCard τ
    rw [← Subgroup.orderOf_coe τ] at h
    simpa [τ] using h
  have hdvd24 : orderOf (σ : Equiv.Perm Ω) ∣ 24 := by
    change orderOf (σ : Equiv.Perm Ω) ∣
      Nat.card (MulAction.stabilizer (Equiv.Perm (G ⧸ G1))
        (QuotientGroup.mk (1 : G) : G ⧸ G1)) at hdvd
    rw [se_stabilizer_perm_card c G1 e] at hdvd
    exact hdvd
  have hord5 : orderOf (σ : Equiv.Perm Ω) = 5 := by simpa using hσ
  have : (5 : ℕ) ∣ 24 := by
    rwa [hord5] at hdvd24
  norm_num at this

/-- Label the five cosets by the powers of an order-five element of the image,
so that it becomes the rotation `finRotate 5`. -/
private lemma se_orbit_equiv (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1)
    {σ : (seφ G1).range} (hσ : orderOf σ = 5) :
    ∃ E : (G ⧸ G1) ≃ Fin 5,
      E (QuotientGroup.mk (1 : G)) = 0 ∧
        E.permCongr (σ : Equiv.Perm (G ⧸ G1)) = finRotate 5 := by
  classical
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  let f : Fin 5 → Ω := fun i => (σ : Equiv.Perm Ω) ^ i.val • q0
  have hσP : orderOf (σ : Equiv.Perm Ω) = 5 := by simpa using hσ
  have hf_inj : Function.Injective f := by
    have hpow_not_fix : ∀ {i j : Fin 5}, f i = f j → i.val < j.val → False := by
      intro i j h hlt
      let d : ℕ := j.val - i.val
      have hd : 1 ≤ d := by
        dsimp [d]
        omega
      have hd5 : d < 5 := by
        dsimp [d]
        omega
      have hdsum : i.val + d = j.val := by
        dsimp [d]
        omega
      have hh : (σ : Equiv.Perm Ω) ^ i.val • q0 =
          (σ : Equiv.Perm Ω) ^ i.val • ((σ : Equiv.Perm Ω) ^ d • q0) := by
        calc
          (σ : Equiv.Perm Ω) ^ i.val • q0 = (σ : Equiv.Perm Ω) ^ j.val • q0 := h
          _ = ((σ : Equiv.Perm Ω) ^ i.val * (σ : Equiv.Perm Ω) ^ d) • q0 := by
            congr 1
            rw [← hdsum, pow_add]
          _ = (σ : Equiv.Perm Ω) ^ i.val • ((σ : Equiv.Perm Ω) ^ d • q0) := by
            simp [smul_smul]
      have hfixd : (σ : Equiv.Perm Ω) ^ d • q0 = q0 := by
        have hh' : ((σ : Equiv.Perm Ω) ^ i.val) ((σ : Equiv.Perm Ω) ^ d • q0) =
            ((σ : Equiv.Perm Ω) ^ i.val) q0 := by
          simpa [Equiv.Perm.smul_def] using hh.symm
        exact ((σ : Equiv.Perm Ω) ^ i.val).injective hh'
      -- `σ^d` lies in the image and has order five
      let τ : (seφ G1).range := σ ^ d
      have hτmem : (τ : Equiv.Perm Ω) = (σ : Equiv.Perm Ω) ^ d := by
        simp [τ, Subgroup.coe_pow]
      have hfixτ : (τ : Equiv.Perm Ω) • q0 = q0 := by
        rw [hτmem]
        exact hfixd
      have hcop : Nat.Coprime 5 d := by
        rw [Nat.prime_five.coprime_iff_not_dvd]
        intro h5d
        rcases h5d with ⟨k, hk⟩
        have : d = 0 := by omega
        omega
      have hgcd : Nat.gcd 5 d = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
      have hord' : orderOf ((σ : Equiv.Perm Ω) ^ d) = 5 := by
        have hord := orderOf_pow' (σ : Equiv.Perm Ω) (by omega : d ≠ 0)
        rw [hσP, hgcd] at hord
        simpa using hord
      have hordτ : orderOf τ = 5 := by
        rw [← Subgroup.orderOf_coe τ, hτmem]
        exact hord'
      exact (se_order_five_not_fix_base c G1 e hordτ) (by simpa [hfixτ])
    intro i j h
    by_cases hij : i = j
    · exact hij
    · exfalso
      by_cases hle : i.val ≤ j.val
      · exact hpow_not_fix h (lt_of_le_of_ne hle (by
          intro hle'
          apply hij
          exact Fin.ext hle'))
      · exact hpow_not_fix h.symm (by omega)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf_inj, ?_⟩
    have hΩ : Fintype.card Ω = 5 := by
      rw [← Nat.card_eq_fintype_card]
      exact (se_index_eq_five c G1 e).1
    simp [hΩ]
  let E : Ω ≃ Fin 5 := (Equiv.ofBijective f hbij).symm
  refine ⟨E, ?_, ?_⟩
  · have hf0 : f (0 : Fin 5) = q0 := by simp [f]
    change (Equiv.ofBijective f hbij).symm q0 = 0
    rw [← hf0]
    exact Equiv.symm_apply_apply (Equiv.ofBijective f hbij) (0 : Fin 5)
  · ext i
    rw [Equiv.permCongr_apply]
    dsimp [E]
    have hstep : (σ : Equiv.Perm Ω) • (f i) = f (finRotate 5 i) := by
      by_cases hi : i.val < 4
      · have hfr : finRotate 5 i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hi
        rw [hfr]
        change (σ : Equiv.Perm Ω) • ((σ : Equiv.Perm Ω) ^ i.val • q0) =
          (σ : Equiv.Perm Ω) ^ (i.val + 1) • q0
        rw [← mul_smul]
        rw [← pow_succ']
      · have hi4 : i.val = 4 := by omega
        have hfr : finRotate 5 i = (0 : Fin 5) := by
          have hlast : i = Fin.last (4 : ℕ) := by
            ext
            simp [hi4]
          rw [hlast]
          exact finRotate_last (n := 4)
        rw [hfr]
        change (σ : Equiv.Perm Ω) • ((σ : Equiv.Perm Ω) ^ i.val • q0) = q0
        rw [hi4]
        rw [← mul_smul]
        rw [← pow_succ']
        have hσ5 : (σ : Equiv.Perm Ω) ^ 5 = 1 := by
          simpa [hσP] using (pow_orderOf_eq_one (x := (σ : Equiv.Perm Ω)))
        rw [hσ5]
        simp
    have hstep_app : (σ : Equiv.Perm Ω) (f i) = f (finRotate 5 i) := by
      simpa [Equiv.Perm.smul_def] using hstep
    rw [hstep_app]
    simpa using (Equiv.symm_apply_apply (Equiv.ofBijective f hbij) (finRotate 5 i))

/-- The permutation image of `G` contains a three-cycle. -/
private lemma se_threeCycle_mem (c : Hyp11 G) (G1 : Subgroup G) (e : SEContext c G1) :
    ∃ τ : Equiv.Perm (G ⧸ G1), Equiv.Perm.IsThreeCycle τ ∧ τ ∈ (seφ G1).range := by
  classical
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  obtain ⟨σ, hσ⟩ := se_exists_order_five c G1 e
  rcases se_orbit_equiv c G1 e hσ with ⟨E, hE0, hEσ⟩
  let V : Subgroup (Equiv.Perm Ω) := seVS c G1
  let W : Subgroup (Equiv.Perm (Fin 5)) := V.map E.permCongrHom.toMonoidHom
  have hVcard : Nat.card V = 4 := se_VS_card c G1 e
  have hWcard : Nat.card W = 4 := by
    have hmap : Nat.card (V.map E.permCongrHom.toMonoidHom) = Nat.card V :=
      Subgroup.card_map_of_injective (f := E.permCongrHom.toMonoidHom) (K := V)
        E.permCongrHom.injective
    change Nat.card (V.map E.permCongrHom.toMonoidHom) = 4
    rw [hmap]
    exact hVcard
  have hVexp : ∀ v : V, v ^ 2 = 1 := se_VS_exp_two c G1 e
  have hWexp : ∀ w : W, w ^ 2 = 1 := by
    intro w
    rcases Subgroup.mem_map.mp w.2 with ⟨v, hvV, hvw⟩
    apply Subtype.ext
    change ((w : Equiv.Perm (Fin 5)) ^ 2) = 1
    rw [← hvw]
    rw [← map_pow]
    have hv2 : (v : Equiv.Perm Ω) ^ 2 = 1 := by
      simpa using congrArg Subtype.val (hVexp ⟨v, hvV⟩)
    rw [hv2, map_one]
  have hWfix0 : ∀ w : W, (w : Equiv.Perm (Fin 5)) (0 : Fin 5) = 0 := by
    intro w
    rcases Subgroup.mem_map.mp w.2 with ⟨v, hvV, hvw⟩
    change E.permCongr v = ↑w at hvw
    rw [← hvw]
    rw [Equiv.permCongr_apply]
    have hEsymm0 : E.symm (0 : Fin 5) = q0 := by
      rw [← hE0]
      simp [q0]
    rw [hEsymm0]
    rw [← hE0]
    exact congrArg E (by
      have hfixV : (v : Equiv.Perm Ω) • q0 = q0 :=
        MulAction.mem_stabilizer_iff.mp (se_VS_fix_base c G1 e hvV)
      simpa [Equiv.Perm.smul_def] using hfixV)
  have hWfree : ∀ w : W, w ≠ 1 → ∀ i : Fin 5, i ≠ 0 →
      (w : Equiv.Perm (Fin 5)) i ≠ i := by
    intro w hwne i hi0
    rcases Subgroup.mem_map.mp w.2 with ⟨v, hvV, hvw⟩
    change E.permCongr v = ↑w at hvw
    rw [← hvw]
    intro h
    have hvne : (v : Equiv.Perm Ω) ≠ 1 := by
      intro hv1
      apply hwne
      apply Subtype.ext
      rw [← hvw]
      change E.permCongr (v : Equiv.Perm Ω) = 1
      rw [hv1]
      exact map_one (E.permCongrHom.toMonoidHom)
    have hneq : E.symm i ≠ q0 := by
      intro hq
      apply hi0
      calc
        i = E (E.symm i) := by simp
        _ = E q0 := by rw [hq]
        _ = 0 := hE0
    have hvfix : (v : Equiv.Perm Ω) (E.symm i) = E.symm i := by
      have hE : E ((v : Equiv.Perm Ω) (E.symm i)) = E (E.symm i) := by
        rw [Equiv.permCongr_apply] at h
        simpa using h
      exact E.injective hE
    have hvneV : (⟨v, hvV⟩ : V) ≠ 1 := by
      intro h
      apply hvne
      exact congrArg Subtype.val h
    exact (se_VS_free c G1 e ⟨v, hvV⟩ hvneV (E.symm i) hneq)
      (by simpa [Equiv.Perm.smul_def] using hvfix)
  rcases fin5_threeCycle_of_V4 W hWcard hWexp hWfix0 hWfree with ⟨c3, hc3, hcin⟩
  have hρH' : finRotate 5 ∈ (seφ G1).range.map E.permCongrHom.toMonoidHom := by
    rw [Subgroup.mem_map]
    exact ⟨σ, σ.2, hEσ⟩
  have hWleH' : W ≤ (seφ G1).range.map E.permCongrHom.toMonoidHom := by
    intro w hw
    rw [Subgroup.mem_map] at hw ⊢
    rcases hw with ⟨v, hvV, hvw⟩
    change E.permCongr v = w at hvw
    exact ⟨v, se_VS_le_range c G1 e hvV, hvw⟩
  have hcl : Subgroup.closure (({finRotate 5} : Set (Equiv.Perm (Fin 5))) ∪ W) ≤
      (seφ G1).range.map E.permCongrHom.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hρH'
    · exact hWleH' hx
  have hcH' : c3 ∈ (seφ G1).range.map E.permCongrHom.toMonoidHom := hcl hcin
  rcases Subgroup.mem_map.mp hcH' with ⟨τ, hτH, hτeq⟩
  change E.permCongr τ = c3 at hτeq
  refine ⟨τ, ?_, hτH⟩
  have hc3' : Equiv.Perm.IsThreeCycle (E.symm.permCongr c3) :=
    permCongr_isThreeCycle (E.symm) hc3
  have hτ : τ = E.symm.permCongr c3 := by
    apply (E.permCongr).injective
    rw [hτeq]
    ext x
    simp [Equiv.permCongr_apply]
  rwa [hτ]

/-- Given the index bound and odd intersections, the quotient `G/O(G)` is
`A₅`.

Elimination condition: derive `|G : G1| = 5` from `|S| ∣ |G:G1|−1`, identify
the permutation action on the conjugates of `G1` with `A₅` (all involutions
are even, and the double transpositions generate `A₅`), and identify the
action kernel with `O(G)` using simplicity of `A₅`. -/
private theorem quotient_a5_of_stronglyEmbedded (c : Hyp11 G) (G1 : Subgroup G)
    (hHG1 : c.H ≤ G1)
    (h1 : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y)
    (hproper : G1 ≠ ⊤)
    (hlt : G1.index < 9)
    (hodd : ∀ g : G, g ∉ G1 → Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj g).toMonoidHom : Subgroup G))) :
    Nonempty (G ⧸ pPrimeCore 2 G ≃* alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  let se : SEContext c G1 :=
    { hHG1 := hHG1, h1 := h1, hlt := hlt, hodd := hodd, hproper := hproper }
  let Ω := G ⧸ G1
  let q0 : Ω := QuotientGroup.mk (1 : G)
  let H : Subgroup (Equiv.Perm Ω) := (seφ G1).range
  obtain ⟨σ, hσ⟩ := se_exists_order_five c G1 se
  rcases se_orbit_equiv c G1 se hσ with ⟨E, hE0, hEσ⟩
  have hprim : MulAction.IsPreprimitive H Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive (se_range_two_pretransitive c G1 se)
  rcases se_threeCycle_mem c G1 se with ⟨τ, hτ3, hτH⟩
  have hA_le_H : alternatingGroup Ω ≤ H :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hτ3 hτH
  let K : Subgroup G := (seφ G1).ker
  have hoddK : Odd (Nat.card K) := by
    simpa [K] using se_ker_odd c G1 se
  have hcard_mul : Nat.card K * Nat.card H = Nat.card G := by
    have hindex : K.index = Nat.card H := by
      simpa [K, H] using Subgroup.index_ker (seφ G1)
    calc
      Nat.card K * Nat.card H = Nat.card K * K.index := by rw [hindex]
      _ = Nat.card G := K.card_mul_index
  have h8_not_dvd_G : ¬ (8 : ℕ) ∣ Nat.card G := by
    intro h8
    have h8S : (8 : ℕ) ∣ Nat.card (c.S : Subgroup G) :=
      c.S.pow_dvd_card_of_pow_dvd_card (p := 2) (n := 3) (by simpa using h8)
    have hS4 : Nat.card (c.S : Subgroup G) = 4 := (se_index_eq_five c G1 se).2
    have hS4' : Fintype.card (c.S : Subgroup G) = 4 := by
      rw [← Nat.card_eq_fintype_card, hS4]
    norm_num [hS4'] at h8S
  have h8_not_dvd_H : ¬ (8 : ℕ) ∣ Nat.card H := by
    intro h8H
    apply h8_not_dvd_G
    have h8mul : (8 : ℕ) ∣ Nat.card K * Nat.card H :=
      dvd_mul_of_dvd_right h8H _
    rwa [hcard_mul] at h8mul
  have hcardA : Nat.card (alternatingGroup Ω) = 60 := by
    have hΩ : Fintype.card Ω = 5 := by
      rw [← Nat.card_eq_fintype_card]
      exact (se_index_eq_five c G1 se).1
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hΩ]; norm_num)
    have hperm : Nat.card (Equiv.Perm Ω) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hΩ]
      norm_num
    have hindex : (alternatingGroup Ω).index = 2 := alternatingGroup.index_eq_two
    have hmul : (alternatingGroup Ω).index * Nat.card (alternatingGroup Ω) =
        Nat.card (Equiv.Perm Ω) :=
      (alternatingGroup Ω).index_mul_card
    rw [hindex, hperm] at hmul
    omega
  have h60_dvd : (60 : ℕ) ∣ Nat.card H := by
    have h := Subgroup.card_dvd_of_le hA_le_H
    rwa [hcardA] at h
  have hH_dvd_120 : Nat.card H ∣ 120 := by
    have hperm : Nat.card (Equiv.Perm Ω) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      have hΩ : Fintype.card Ω = 5 := by
        rw [← Nat.card_eq_fintype_card]
        exact (se_index_eq_five c G1 se).1
      rw [hΩ]
      norm_num
    have h := Subgroup.card_dvd_of_le (le_top : H ≤ ⊤)
    rw [Subgroup.card_top] at h
    rwa [hperm] at h
  have hcard_le_60 : Nat.card H ≤ 60 := by
    rcases h60_dvd with ⟨n, hn⟩
    rcases hH_dvd_120 with ⟨m, hm⟩
    have htotal : 60 * n * m = 120 := by
      calc
        60 * n * m = Nat.card H * m := by rw [hn]
        _ = 120 := hm.symm
    have hnm : n * m = 2 :=
      mul_right_cancel₀ (by norm_num : (60 : ℕ) ≠ 0) (by
        calc
          n * m * 60 = 60 * n * m := by ring
          _ = 120 := htotal)
    have hndvd : n ∣ 2 := ⟨m, hnm.symm⟩
    have hn_le : n ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) hndvd
    have hnpos : 0 < n := by
      have hpos : 0 < Nat.card H := Nat.card_pos
      rw [hn] at hpos
      omega
    have hn_cases : n = 1 ∨ n = 2 := by omega
    rcases hn_cases with hn1 | hn2
    · rw [hn, hn1]
    · exfalso
      apply h8_not_dvd_H
      rw [hn, hn2]
      norm_num
  have hA_eq_H : alternatingGroup Ω = H :=
    Subgroup.eq_of_le_of_card_ge (H := alternatingGroup Ω) (K := H) hA_le_H
      (by
        rw [hcardA]
        exact hcard_le_60)
  have hH_eq_A : H = alternatingGroup Ω := hA_eq_H.symm
  let eQ : G ⧸ (seφ G1).ker ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientKerEquivRange (seφ G1)).trans
      ((MulEquiv.subgroupCongr hH_eq_A).trans (Equiv.altCongrHom E.symm).symm)
  have hK_le_O : (seφ G1).ker ≤ pPrimeCore 2 G := by
    have hK_norm : (seφ G1).ker.Normal := inferInstance
    have hK_cop : Nat.Coprime 2 (Nat.card (seφ G1).ker) := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro h2
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2)) hoddK
    change (seφ G1).ker ≤
      sSup {K' : Subgroup G | K'.Normal ∧ Nat.Coprime 2 (Nat.card K')}
    exact le_sSup ⟨hK_norm, hK_cop⟩
  have hO_le_K : pPrimeCore 2 G ≤ (seφ G1).ker := by
    have hcoreQ : pPrimeCore 2 (G ⧸ (seφ G1).ker) = ⊥ := by
      have hmap : (pPrimeCore 2 (G ⧸ (seφ G1).ker)).map eQ.toMonoidHom = ⊥ := by
        rw [pPrimeCore_map_iso 2 eQ]
        rw [pPrimeCore_two_alternatingGroupFive]
      exact (Subgroup.map_eq_bot_iff_of_injective (f := eQ.toMonoidHom)
        (H := pPrimeCore 2 (G ⧸ (seφ G1).ker)) eQ.injective).mp hmap
    exact pPrimeCore_le_of_quotient_eq_bot (G := G) (p := 2)
      (N := (seφ G1).ker) hcoreQ
  have hker : (seφ G1).ker = pPrimeCore 2 G := le_antisymm hK_le_O hO_le_K
  let qcore : G ⧸ (seφ G1).ker ≃* G ⧸ pPrimeCore 2 G :=
    QuotientGroup.quotientMulEquivOfEq hker
  exact ⟨qcore.symm.trans eQ⟩

/-- **Theorem B**: a proper subgroup `G1` containing `H` with only one class
of involutions forces `G/O(G) ≅ A₅`. -/
public theorem theorem_B {G : Type u} [Group G] [Finite G] (c : Hyp11 G)
    (G1 : Subgroup G) (hG1 : G1 ≠ ⊤) (hHG1 : c.H ≤ G1)
    (h1class : ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ G1 → y ∈ G1 →
      ∃ g : G, g ∈ G1 ∧ g * x * g⁻¹ = y) :
    Nonempty (G ⧸ pPrimeCore 2 G ≃* alternatingGroup (Fin 5)) := by
  classical
  have hlt := theorem_B_index_lt_nine c G1 hHG1 h1class
  have hodd := strongEmbedding_intersections_odd c G1 hHG1 h1class
  exact quotient_a5_of_stronglyEmbedded c G1 hHG1 h1class hG1 hlt hodd

end CFSG.BenderGlauberman
