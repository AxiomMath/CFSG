module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group

public section

namespace CFSG.Monster.AxisCount

open MulAction Pointwise

section Counting

variable {G : Type*} [Group G]

theorem card_mul_card_filter_eq [DecidableEq G] (Nf Df : Finset G)
    (hN : ∀ n ∈ Nf, ∀ x, n * x ∈ Df ↔ x ∈ Df) (P : G → Prop) [DecidablePred P] (m : ℕ)
    (hm : ∀ x ∈ Df, (Nf.filter fun n => P (n * x)).card = m) :
    Nf.card * (Df.filter P).card = m * Df.card := by
  have h1 : ∀ n ∈ Nf, (Df.filter fun x => P (n * x)).card = (Df.filter P).card := by
    intro n hn
    refine Finset.card_bij (fun x _ => n * x) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(hN n hn x).2 hx.1, hx.2⟩
    · intro x _ y _ hxy
      exact mul_left_cancel hxy
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨n⁻¹ * y, ?_, by simp⟩
      rw [Finset.mem_filter]
      refine ⟨?_, by simpa using hy.2⟩
      rw [← hN n hn]
      simpa using hy.1
  calc Nf.card * (Df.filter P).card = ∑ n ∈ Nf, (Df.filter P).card := by simp
    _ = ∑ n ∈ Nf, (Df.filter fun x => P (n * x)).card :=
        Finset.sum_congr rfl fun n hn => (h1 n hn).symm
    _ = ∑ n ∈ Nf, ∑ x ∈ Df, if P (n * x) then 1 else 0 :=
        Finset.sum_congr rfl fun n _ => Finset.card_filter _ _
    _ = ∑ x ∈ Df, ∑ n ∈ Nf, if P (n * x) then 1 else 0 := Finset.sum_comm
    _ = ∑ x ∈ Df, m := Finset.sum_congr rfl fun x hx => by
        rw [← Finset.card_filter]
        exact hm x hx
    _ = m * Df.card := by simp [mul_comm]

theorem card_mul_ncard_filter_eq (N : Subgroup G) [Finite N] {D : Set G} (hDfin : D.Finite)
    (hD : ∀ n ∈ N, ∀ x, n * x ∈ D ↔ x ∈ D) (P : G → Prop) {m : ℕ}
    (hm : ∀ x ∈ D, {n | n ∈ N ∧ P (n * x)}.ncard = m) :
    Nat.card N * {x | x ∈ D ∧ P x}.ncard = m * D.ncard := by
  classical
  have hNfin : (N : Set G).Finite := Set.toFinite _
  have h := card_mul_card_filter_eq hNfin.toFinset hDfin.toFinset (P := P) (m := m)
    (fun n hn x => by
      have := hD n (by simpa using hn) x
      simpa using this)
    (fun x hx => by
      rw [← hm x (by simpa using hx)]
      rw [← Set.ncard_coe_finset]
      congr 1
      ext n
      simp)
  have e1 : Nat.card N = hNfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card (N : Set G) hNfin]
    exact Nat.card_coe_set_eq (N : Set G)
  have e2 : {x | x ∈ D ∧ P x}.ncard = (hDfin.toFinset.filter P).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp
  rw [e1, e2, Set.ncard_eq_toFinset_card D hDfin]
  exact h

theorem card_dvd_card_of_mul_mem (N : Subgroup G) {D : Set G}
    (hD : ∀ n ∈ N, ∀ x, n * x ∈ D ↔ x ∈ D) : Nat.card N ∣ Nat.card D := by
  have h : (D⁻¹ * (N : Set G) : Set G) = D⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, n, hn, rfl⟩
      rw [Set.mem_inv] at hx ⊢
      rw [mul_inv_rev]
      exact (hD n⁻¹ (N.inv_mem hn) _).2 hx
    · intro hy
      exact ⟨y, hy, 1, N.one_mem, by simp⟩
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient N D⁻¹
  rw [h] at h1
  have e : Nat.card (D⁻¹ : Set G) = Nat.card D :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.inv G) fun x => Set.mem_inv)
  rw [← e, h1]
  exact dvd_mul_right _ _

theorem card_iUnion_of_pairwise_disjoint {α β : Type*} [Fintype α] {s : α → Set β}
    (hs : Pairwise (Function.onFun Disjoint s)) [∀ a, Finite (s a)] :
    Nat.card (⋃ a, s a) = ∑ a, Nat.card (s a) := by
  rw [Nat.card_congr (Set.unionEqSigmaOfDisjoint hs), Nat.card_sigma]

end Counting

section Orbit

variable {K X : Type*} [Group K] [MulAction K X]

theorem card_filter_smul (x : X) (P : X → Prop) :
    Nat.card {g : K // P (g • x)} =
      Nat.card {w : orbit K x // P (w : X)} * Nat.card (stabilizer K x) := by
  classical
  let s := stabilizer K x
  let e := orbitEquivQuotientStabilizer K x
  let t : Set (K ⧸ s) := {q | P (e.symm q : X)}
  have h1 : {g : K // P (g • x)} ≃ (QuotientGroup.mk ⁻¹' t : Set K) :=
    Equiv.subtypeEquivRight fun g => Iff.rfl
  have h2 : t ≃ {w : orbit K x // P (w : X)} := Equiv.subtypeEquiv e.symm fun q => Iff.rfl
  rw [Nat.card_congr h1, Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet s t),
    Nat.card_prod, Nat.card_congr h2, mul_comm]

theorem card_orbit_mul_card_stabilizer (x : X) :
    Nat.card (orbit K x) * Nat.card (stabilizer K x) = Nat.card K := by
  rw [mul_comm, ← Subgroup.card_mul_index (stabilizer K x), MulAction.index_stabilizer,
    Nat.card_coe_set_eq]

end Orbit

section Constructing

variable {G : Type*} [Group G]

theorem relIndex_eq_two_of_card_eq {N' N : Subgroup G} [Finite N] (hle : N' ≤ N)
    (hcard : Nat.card N = 2 * Nat.card N') : N'.relIndex N = 2 := by
  have := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have h := Subgroup.relIndex_mul_card N' N
  rw [inf_of_le_left hle, hcard] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem conj_inv_mem_of_conj_mem {N' : Subgroup G} [Finite N'] {τ : G}
    (h : ∀ n ∈ N', τ * n * τ⁻¹ ∈ N') : ∀ n ∈ N', τ⁻¹ * n * τ ∈ N' := by
  have hf : Function.Injective (fun n : N' => (⟨τ * n * τ⁻¹, h n n.2⟩ : N')) := by
    intro x y hxy
    have h' : τ * (x : G) * τ⁻¹ = τ * (y : G) * τ⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h')
  intro n hn
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.1 hf ⟨n, hn⟩
  have hm' : τ * (m : G) * τ⁻¹ = n := congrArg Subtype.val hm
  have : τ⁻¹ * n * τ = m := by rw [← hm']; group
  rw [this]
  exact m.2

theorem subset_iUnion_doubleCoset_of_card_eq {ι : Type*} [Fintype ι] {H N U : Subgroup G}
    [Finite H] (hN : N ≤ H) (hU : U ≤ H) {h : ι → G} (hh : ∀ r, h r ∈ H)
    (hdisj : Pairwise (Function.onFun Disjoint fun r =>
      DoubleCoset.doubleCoset (h r) (N : Set G) (U : Set G)))
    (hcard : ∑ r, Nat.card (DoubleCoset.doubleCoset (h r) (N : Set G) (U : Set G)) =
      Nat.card H) :
    (H : Set G) ⊆ ⋃ r, DoubleCoset.doubleCoset (h r) (N : Set G) (U : Set G) := by
  have hsub : (⋃ r, DoubleCoset.doubleCoset (h r) (N : Set G) (U : Set G)) ⊆ (H : Set G) := by
    refine Set.iUnion_subset fun r g hg => ?_
    obtain ⟨n, hn, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    exact H.mul_mem (H.mul_mem (hN hn) (hh r)) (hU hu)
  have hfin : ∀ r, Finite (DoubleCoset.doubleCoset (h r) (N : Set G) (U : Set G)) := fun r =>
    ((Set.toFinite (H : Set G)).subset
      (fun g hg => hsub (Set.mem_iUnion.2 ⟨r, hg⟩))).to_subtype
  have hc : (⋃ r, DoubleCoset.doubleCoset (h r) (N : Set G) (U : Set G)).ncard =
      (H : Set G).ncard := by
    rw [← Nat.card_coe_set_eq, card_iUnion_of_pairwise_disjoint hdisj, hcard,
      ← Nat.card_coe_set_eq]
    rfl
  exact (Set.eq_of_subset_of_ncard_le hsub hc.ge (Set.toFinite _)).symm.subset

end Constructing

section Setting

@[expose] def tpow {G : Type*} [Group G] (τ : G) : Bool → G
  | true => τ
  | false => τ⁻¹

variable {G : Type*} [Group G]

@[simp] theorem tpow_true (τ : G) : tpow τ true = τ := rfl

@[simp] theorem tpow_false (τ : G) : tpow τ false = τ⁻¹ := rfl

theorem tpow_not (τ : G) (ε : Bool) : tpow τ (!ε) = (tpow τ ε)⁻¹ := by
  cases ε <;> simp

variable (G) (X : Type*) [MulAction G X] (I : Type*) (R : I → Type*)

structure Setup where
  H : Subgroup G
  N' : Subgroup G
  N : Subgroup G
  τ : G
  a : G
  v : I → X
  U : I → Subgroup G
  h : (i : I) → R i → G
  κ : (i : I) → R i → Bool → G
  t : (i : I) → R i → Bool → I
  N'_le_N : N' ≤ N
  N_le_H : N ≤ H
  relIndex_N'_N : N'.relIndex N = 2
  conj_mem : ∀ n ∈ N', τ * n * τ⁻¹ ∈ N'
  conj_inv_mem : ∀ n ∈ N', τ⁻¹ * n * τ ∈ N'
  a_mem : a ∈ N
  a_notMem : a ∉ N'
  a_conj : a⁻¹ * τ * a = τ⁻¹
  U_le_H : ∀ i, U i ≤ H
  U_le_stabilizer : ∀ i, U i ≤ stabilizer G (v i)
  h_mem : ∀ i r, h i r ∈ H
  κ_mem : ∀ i r ε, κ i r ε ∈ H
  cover : ∀ i, (H : Set G) ⊆
    ⋃ r : R i, DoubleCoset.doubleCoset (h i r) (N : Set G) (U i : Set G)
  spec : ∀ i r ε, (κ i r ε * tpow τ ε * h i r) • v i = v (t i r ε)

variable {G X I R}

namespace Setup

variable (S : Setup G X I R)

@[expose] def D (i : I) (r : R i) : Set G :=
  DoubleCoset.doubleCoset (S.h i r) (S.N : Set G) (S.U i : Set G)

theorem mem_D_iff {i : I} {r : R i} {g : G} :
    g ∈ S.D i r ↔ ∃ n ∈ S.N, ∃ u ∈ S.U i, g = n * S.h i r * u :=
  DoubleCoset.mem_doubleCoset

@[expose] def orb (i : I) : Set X := MulAction.orbit S.H (S.v i)

theorem mem_orb_iff {i : I} {x : X} : x ∈ S.orb i ↔ ∃ c ∈ S.H, c • S.v i = x := by
  constructor
  · rintro ⟨⟨c, hc⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩

theorem smul_mem_orb {i : I} {c : G} (hc : c ∈ S.H) : c • S.v i ∈ S.orb i :=
  S.mem_orb_iff.2 ⟨c, hc, rfl⟩

theorem v_mem_orb (i : I) : S.v i ∈ S.orb i := by
  simpa using S.smul_mem_orb (i := i) S.H.one_mem

theorem eq_of_mem_orb (hO : Function.Injective S.orb) {i j : I} {x : X} (hi : x ∈ S.orb i)
    (hj : x ∈ S.orb j) : i = j := by
  apply hO
  have h1 : MulAction.orbit S.H x = S.orb i := MulAction.orbit_eq_iff.2 hi
  have h2 : MulAction.orbit S.H x = S.orb j := MulAction.orbit_eq_iff.2 hj
  exact h1.symm.trans h2

theorem orb_injective_of_forall (h : ∀ i j, ∀ c ∈ S.H, c • S.v j = S.v i → i = j) :
    Function.Injective S.orb := by
  intro i j hij
  have hmem : S.v i ∈ S.orb j := by
    rw [← hij]
    exact S.v_mem_orb i
  obtain ⟨c, hc, hcv⟩ := S.mem_orb_iff.1 hmem
  exact h i j c hc hcv

theorem orb_injective_of_invariant {α : Type*} (f : X → α)
    (hf : ∀ c ∈ S.H, ∀ x, f (c • x) = f x) (hinj : Function.Injective fun i => f (S.v i)) :
    Function.Injective S.orb :=
  S.orb_injective_of_forall fun i j c hc hcv =>
    hinj (by
      show f (S.v i) = f (S.v j)
      rw [← hcv, hf c hc])

@[expose] def X0 : Set X := ⋃ i, S.orb i

theorem mem_X0_iff {x : X} : x ∈ S.X0 ↔ ∃ i, ∃ c ∈ S.H, c • S.v i = x := by
  simp [X0, mem_orb_iff]

theorem orb_subset_X0 (i : I) : S.orb i ⊆ S.X0 := Set.subset_iUnion S.orb i

theorem smul_mem_orb_of_mem {i : I} {c : G} (hc : c ∈ S.H) {x : X} (hx : x ∈ S.orb i) :
    c • x ∈ S.orb i := by
  obtain ⟨d, hd, rfl⟩ := S.mem_orb_iff.1 hx
  exact S.mem_orb_iff.2 ⟨c * d, S.H.mul_mem hc hd, mul_smul _ _ _⟩

theorem smul_mem_X0_of_mem {c : G} (hc : c ∈ S.H) {x : X} (hx : x ∈ S.X0) : c • x ∈ S.X0 := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact S.orb_subset_X0 i (S.smul_mem_orb_of_mem hc hi)

theorem conj_mem_N {x n : G} (hx : x ∈ S.N') (hn : n ∈ S.N) : n * x * n⁻¹ ∈ S.N' := by
  have hnorm : (S.N'.subgroupOf S.N).Normal := Subgroup.normal_of_index_eq_two S.relIndex_N'_N
  exact (Subgroup.normal_subgroupOf_iff S.N'_le_N).1 hnorm x n hx hn

theorem tpow_conj_mem (ε : Bool) {n : G} (hn : n ∈ S.N') :
    tpow S.τ ε * n * (tpow S.τ ε)⁻¹ ∈ S.N' := by
  cases ε
  · simpa using S.conj_inv_mem n hn
  · simpa using S.conj_mem n hn

theorem tpow_mul_a (ε : Bool) : tpow S.τ ε * S.a = S.a * tpow S.τ (!ε) := by
  have h1 : S.τ * S.a = S.a * S.τ⁻¹ := by
    rw [← S.a_conj]
    group
  cases ε
  · simp only [tpow_false, Bool.not_false, tpow_true]
    calc S.τ⁻¹ * S.a = S.τ⁻¹ * (S.a * S.τ⁻¹) * S.τ := by group
      _ = S.τ⁻¹ * (S.τ * S.a) * S.τ := by rw [h1]
      _ = S.a * S.τ := by group
  · simpa using h1

theorem inv_mul_mem {n : G} (hn : n ∈ S.N) (hn' : n ∉ S.N') : S.a⁻¹ * n ∈ S.N' := by
  obtain ⟨b, hbN, hb⟩ := Subgroup.relIndex_eq_two_iff.1 S.relIndex_N'_N
  have key : ∀ x ∈ S.N, x ∉ S.N' → x * b ∈ S.N' := by
    intro x hx hx'
    rcases hb x hx with h | h
    · exact h.1
    · exact absurd h.1 hx'
  have h1 : n * S.a⁻¹ ∈ S.N' := by
    have := S.N'.mul_mem (key n hn hn') (S.N'.inv_mem (key S.a S.a_mem S.a_notMem))
    simpa [mul_assoc] using this
  have h2 := S.conj_mem_N h1 (S.N.inv_mem S.a_mem)
  simpa [mul_assoc] using h2

theorem exists_tpow_mul (ε : Bool) {n : G} (hn : n ∈ S.N) :
    ∃ (ε' : Bool) (n'' : G), n'' ∈ S.N ∧ (n ∈ S.N' → ε' = ε) ∧ (n ∉ S.N' → ε' = !ε) ∧
      tpow S.τ ε * n = n'' * tpow S.τ ε' := by
  by_cases hn' : n ∈ S.N'
  · refine ⟨ε, tpow S.τ ε * n * (tpow S.τ ε)⁻¹, S.N'_le_N (S.tpow_conj_mem ε hn'),
      fun _ => rfl, fun h => absurd hn' h, ?_⟩
    group
  · have ha : S.a⁻¹ * n ∈ S.N' := S.inv_mul_mem hn hn'
    refine ⟨!ε, S.a * (tpow S.τ (!ε) * (S.a⁻¹ * n) * (tpow S.τ (!ε))⁻¹),
      S.N.mul_mem S.a_mem (S.N'_le_N (S.tpow_conj_mem (!ε) ha)), fun h => absurd h hn',
      fun _ => rfl, ?_⟩
    calc tpow S.τ ε * n = (tpow S.τ ε * S.a) * (S.a⁻¹ * n) := by group
      _ = (S.a * tpow S.τ (!ε)) * (S.a⁻¹ * n) := by rw [S.tpow_mul_a ε]
      _ = _ := by group

theorem transition (ε : Bool) (i : I) (r : R i) {n : G} (hn : n ∈ S.N) :
    ∃ (ε' : Bool) (c' : G), c' ∈ S.H ∧ (n ∈ S.N' → ε' = ε) ∧ (n ∉ S.N' → ε' = !ε) ∧
      tpow S.τ ε * (n * S.h i r) = c' * (S.κ i r ε' * tpow S.τ ε' * S.h i r) := by
  obtain ⟨ε', n'', hn'', h1, h2, h3⟩ := S.exists_tpow_mul ε hn
  refine ⟨ε', n'' * (S.κ i r ε')⁻¹, S.H.mul_mem (S.N_le_H hn'')
    (S.H.inv_mem (S.κ_mem i r ε')), h1, h2, ?_⟩
  calc tpow S.τ ε * (n * S.h i r) = (tpow S.τ ε * n) * S.h i r := by group
    _ = (n'' * tpow S.τ ε') * S.h i r := by rw [h3]
    _ = _ := by group

theorem tpow_smul_of_eq {ε ε' : Bool} {i : I} {r : R i} {n u c' : G} (hu : u ∈ S.U i)
    (hK : tpow S.τ ε * (n * S.h i r) = c' * (S.κ i r ε' * tpow S.τ ε' * S.h i r)) :
    tpow S.τ ε • ((n * S.h i r * u) • S.v i) = c' • S.v (S.t i r ε') := by
  have hu' : u • S.v i = S.v i := MulAction.mem_stabilizer_iff.1 (S.U_le_stabilizer i hu)
  calc tpow S.τ ε • ((n * S.h i r * u) • S.v i)
      = (tpow S.τ ε * (n * S.h i r) * u) • S.v i := by rw [← mul_smul]; group
    _ = (c' * (S.κ i r ε' * tpow S.τ ε' * S.h i r) * u) • S.v i := by rw [hK]
    _ = c' • ((S.κ i r ε' * tpow S.τ ε' * S.h i r) • (u • S.v i)) := by
        simp only [mul_smul]
    _ = c' • S.v (S.t i r ε') := by rw [hu', S.spec]

theorem exists_tpow_smul (ε : Bool) (i : I) (r : R i) {n u : G} (hn : n ∈ S.N) (hu : u ∈ S.U i) :
    ∃ (ε' : Bool) (c' : G), c' ∈ S.H ∧ (n ∈ S.N' → ε' = ε) ∧ (n ∉ S.N' → ε' = !ε) ∧
      tpow S.τ ε • ((n * S.h i r * u) • S.v i) = c' • S.v (S.t i r ε') := by
  obtain ⟨ε', c', hc', h1, h2, h3⟩ := S.transition ε i r hn
  exact ⟨ε', c', hc', h1, h2, S.tpow_smul_of_eq hu h3⟩

theorem tpow_smul_mem_X0 (ε : Bool) {x : X} (hx : x ∈ S.X0) : tpow S.τ ε • x ∈ S.X0 := by
  obtain ⟨i, c, hc, rfl⟩ := S.mem_X0_iff.1 hx
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 (S.cover i hc)
  obtain ⟨n, hn, u, hu, rfl⟩ := S.mem_D_iff.1 hr
  obtain ⟨ε', c', hc', -, -, h⟩ := S.exists_tpow_smul ε i r hn hu
  rw [h]
  exact S.orb_subset_X0 _ (S.smul_mem_orb hc')

theorem tau_smul_mem_X0 {x : X} (hx : x ∈ S.X0) : S.τ • x ∈ S.X0 :=
  S.tpow_smul_mem_X0 true hx

theorem tau_inv_smul_mem_X0 {x : X} (hx : x ∈ S.X0) : S.τ⁻¹ • x ∈ S.X0 :=
  S.tpow_smul_mem_X0 false hx

theorem closure_invariant {g : G} (hg : g ∈ Subgroup.closure ((S.H : Set G) ∪ {S.τ})) {x : X}
    (hx : x ∈ S.X0) : g • x ∈ S.X0 := by
  induction hg using Subgroup.closure_induction'' generalizing x with
  | mem y hy =>
    rcases hy with hy | hy
    · exact S.smul_mem_X0_of_mem hy hx
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact S.tau_smul_mem_X0 hx
  | inv_mem y hy =>
    rcases hy with hy | hy
    · exact S.smul_mem_X0_of_mem (S.H.inv_mem hy) hx
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact S.tau_inv_smul_mem_X0 hx
  | one => simpa using hx
  | mul y z _ _ hy hz =>
    rw [mul_smul]
    exact hy (hz hx)

theorem X0_eq_orbit (i₀ : I)
    (hv : ∀ i, S.v i ∈ MulAction.orbit (Subgroup.closure ((S.H : Set G) ∪ {S.τ})) (S.v i₀)) :
    S.X0 = MulAction.orbit (Subgroup.closure ((S.H : Set G) ∪ {S.τ})) (S.v i₀) := by
  set C := Subgroup.closure ((S.H : Set G) ∪ {S.τ}) with hC
  have hHC : S.H ≤ C := fun c hc => Subgroup.subset_closure (Or.inl hc)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, c, hc, rfl⟩ := S.mem_X0_iff.1 hx
    obtain ⟨⟨g, hgC⟩, hg⟩ := hv i
    refine ⟨⟨c * g, C.mul_mem (hHC hc) hgC⟩, ?_⟩
    change (c * g) • S.v i₀ = c • S.v i
    rw [mul_smul]
    rw [show g • S.v i₀ = S.v i from hg]
  · rintro x ⟨⟨g, hgC⟩, rfl⟩
    exact S.closure_invariant hgC (S.orb_subset_X0 i₀ (S.v_mem_orb i₀))

theorem X0_eq_orbit_of_exists (i₀ : I) (γ : I → G)
    (hγ : ∀ i, γ i • S.v i₀ = S.v i)
    (hγC : ∀ i, γ i ∈ Subgroup.closure ((S.H : Set G) ∪ {S.τ})) :
    S.X0 = MulAction.orbit (Subgroup.closure ((S.H : Set G) ∪ {S.τ})) (S.v i₀) :=
  S.X0_eq_orbit i₀ fun i => ⟨⟨γ i, hγC i⟩, hγ i⟩

section Cardinalities

@[expose] noncomputable def k (i : I) (r : R i) : ℕ := Nat.card (S.D i r) / Nat.card S.N

@[expose] noncomputable def L : ℕ := 2 * Nat.card S.H / Nat.card S.N

@[expose] def trans (i t : I) : Set X := {w | w ∈ S.orb i ∧ S.τ • w ∈ S.orb t}

theorem finite_of_le {K : Subgroup G} [Finite S.H] (hK : K ≤ S.H) : Finite K :=
  Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)

theorem D_subset_H (i : I) (r : R i) : S.D i r ⊆ S.H := by
  intro g hg
  obtain ⟨n, hn, u, hu, rfl⟩ := S.mem_D_iff.1 hg
  exact S.H.mul_mem (S.H.mul_mem (S.N_le_H hn) (S.h_mem i r)) (S.U_le_H i hu)

theorem finite_D [Finite S.H] (i : I) (r : R i) : (S.D i r).Finite :=
  (Set.toFinite (S.H : Set G)).subset (S.D_subset_H i r)

theorem finite_orb [Finite S.H] (i : I) : (S.orb i).Finite := Set.finite_range _

theorem card_N_eq : Nat.card S.N = 2 * Nat.card S.N' := by
  have h := Subgroup.relIndex_mul_card S.N' S.N
  rw [S.relIndex_N'_N, inf_of_le_left S.N'_le_N] at h
  exact h.symm

theorem N_dvd_card_H : Nat.card S.N ∣ Nat.card S.H := Subgroup.card_dvd_of_le S.N_le_H

theorem L_mul_card_N : S.L * Nat.card S.N = 2 * Nat.card S.H :=
  Nat.div_mul_cancel ((S.N_dvd_card_H).mul_left 2)

theorem card_N_pos [Finite S.H] : 0 < Nat.card S.N := by
  have := S.finite_of_le S.N_le_H
  exact Nat.card_pos

theorem mul_mem_D_iff (i : I) (r : R i) {n : G} (hn : n ∈ S.N) (x : G) :
    n * x ∈ S.D i r ↔ x ∈ S.D i r := by
  constructor
  · intro hx
    obtain ⟨m, hm, u, hu, hx⟩ := S.mem_D_iff.1 hx
    refine S.mem_D_iff.2 ⟨n⁻¹ * m, S.N.mul_mem (S.N.inv_mem hn) hm, u, hu, ?_⟩
    calc x = n⁻¹ * (n * x) := by group
      _ = n⁻¹ * (m * S.h i r * u) := by rw [hx]
      _ = n⁻¹ * m * S.h i r * u := by group
  · intro hx
    obtain ⟨m, hm, u, hu, rfl⟩ := S.mem_D_iff.1 hx
    exact S.mem_D_iff.2 ⟨n * m, S.N.mul_mem hn hm, u, hu, by group⟩

theorem card_D_eq (i : I) (r : R i) : Nat.card S.N * S.k i r = Nat.card (S.D i r) :=
  Nat.mul_div_cancel' (card_dvd_card_of_mul_mem S.N fun _ hn x => S.mul_mem_D_iff i r hn x)

theorem k_eq [Finite S.H] {i : I} {r : R i} {k' : ℕ}
    (h : Nat.card (S.D i r) = Nat.card S.N * k') : S.k i r = k' := by
  rw [k, h]
  exact Nat.mul_div_cancel_left k' S.card_N_pos

theorem L_eq [Finite S.H] {l : ℕ} (h : 2 * Nat.card S.H = Nat.card S.N * l) : S.L = l := by
  rw [L, h]
  exact Nat.mul_div_cancel_left l S.card_N_pos

theorem card_orb_mul_card_stabilizer (i : I) :
    Nat.card (S.orb i) * Nat.card (stabilizer S.H (S.v i)) = Nat.card S.H :=
  card_orbit_mul_card_stabilizer (K := S.H) (S.v i)

end Cardinalities

section Counting

theorem tau_smul_mem_orb_iff (hO : Function.Injective S.orb) (i : I) (r : R i) {n u : G}
    (hn : n ∈ S.N) (hu : u ∈ S.U i) (t : I) :
    S.τ • ((n * S.h i r * u) • S.v i) ∈ S.orb t ↔
      (n ∈ S.N' ∧ S.t i r true = t) ∨ (n ∉ S.N' ∧ S.t i r false = t) := by
  obtain ⟨ε', c', hc', h1, h2, h⟩ := S.exists_tpow_smul true i r hn hu
  rw [tpow_true] at h
  rw [h]
  by_cases hn' : n ∈ S.N'
  · have hε : ε' = true := h1 hn'
    subst hε
    simp only [hn', true_and, not_true_eq_false, false_and, or_false]
    exact ⟨fun hmem => S.eq_of_mem_orb hO (S.smul_mem_orb hc') hmem,
      fun h => by rw [← h]; exact S.smul_mem_orb hc'⟩
  · have hε : ε' = false := by simpa using h2 hn'
    subst hε
    simp only [hn', false_and, not_false_eq_true, true_and, false_or]
    exact ⟨fun hmem => S.eq_of_mem_orb hO (S.smul_mem_orb hc') hmem,
      fun h => by rw [← h]; exact S.smul_mem_orb hc'⟩

theorem two_mul_ncard_sign [Finite S.H] (p₁ p₂ : Prop) [Decidable p₁] [Decidable p₂] :
    2 * {n | n ∈ S.N ∧ ((n ∈ S.N' ∧ p₁) ∨ (n ∉ S.N' ∧ p₂))}.ncard =
      ((if p₁ then 1 else 0) + (if p₂ then 1 else 0)) * Nat.card S.N := by
  have := S.finite_of_le S.N_le_H
  have := S.finite_of_le (S.N'_le_N.trans S.N_le_H)
  have hN' : (S.N' : Set G).ncard = Nat.card S.N' := (Nat.card_coe_set_eq _).symm
  have hN : (S.N : Set G).ncard = Nat.card S.N := (Nat.card_coe_set_eq _).symm
  have h2 := S.card_N_eq
  have hsub : (S.N' : Set G) ⊆ S.N := S.N'_le_N
  have hdiff : ((S.N : Set G) \ S.N').ncard = Nat.card S.N' := by
    rw [Set.ncard_sdiff hsub, hN, hN', h2]
    omega
  by_cases hp : p₁ <;> by_cases hm : p₂
  · have : {n | n ∈ S.N ∧ ((n ∈ S.N' ∧ p₁) ∨ (n ∉ S.N' ∧ p₂))} = (S.N : Set G) := by
      ext n
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
      refine ⟨fun h => h.1, fun hn => ⟨hn, ?_⟩⟩
      by_cases hn' : n ∈ S.N'
      · exact Or.inl ⟨hn', hp⟩
      · exact Or.inr ⟨hn', hm⟩
    have e : ((if p₁ then 1 else 0) + (if p₂ then 1 else 0) : ℕ) = 2 := by simp [hp, hm]
    rw [this, hN, e]
  · have : {n | n ∈ S.N ∧ ((n ∈ S.N' ∧ p₁) ∨ (n ∉ S.N' ∧ p₂))} = (S.N' : Set G) := by
      ext n
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
      constructor
      · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩
        · exact h
        · exact absurd h hm
      · intro hn'
        exact ⟨S.N'_le_N hn', Or.inl ⟨hn', hp⟩⟩
    have e : ((if p₁ then 1 else 0) + (if p₂ then 1 else 0) : ℕ) = 1 := by simp [hp, hm]
    rw [this, hN', e]
    omega
  · have : {n | n ∈ S.N ∧ ((n ∈ S.N' ∧ p₁) ∨ (n ∉ S.N' ∧ p₂))} = (S.N : Set G) \ S.N' := by
      ext n
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Set.mem_sdiff]
      constructor
      · rintro ⟨hn, ⟨h, hb⟩ | ⟨h, -⟩⟩
        · exact absurd hb hp
        · exact ⟨hn, h⟩
      · rintro ⟨hn, hn'⟩
        exact ⟨hn, Or.inr ⟨hn', hm⟩⟩
    have e : ((if p₁ then 1 else 0) + (if p₂ then 1 else 0) : ℕ) = 1 := by simp [hp, hm]
    rw [this, hdiff, e]
    omega
  · have : {n | n ∈ S.N ∧ ((n ∈ S.N' ∧ p₁) ∨ (n ∉ S.N' ∧ p₂))} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩
      · exact hp h
      · exact hm h
    have e : ((if p₁ then 1 else 0) + (if p₂ then 1 else 0) : ℕ) = 0 := by simp [hp, hm]
    rw [this, e]
    simp

theorem two_mul_ncard_filter [DecidableEq I] [Finite S.H] (hO : Function.Injective S.orb)
    (i t : I) (r : R i) :
    2 * {g | g ∈ S.D i r ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard =
      ((if S.t i r true = t then 1 else 0) + (if S.t i r false = t then 1 else 0)) *
        (S.D i r).ncard := by
  classical
  have := S.finite_of_le S.N_le_H
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Set G, Φ = {n | n ∈ S.N ∧
      ((n ∈ S.N' ∧ S.t i r true = t) ∨ (n ∉ S.N' ∧ S.t i r false = t))} := ⟨_, rfl⟩
  have hΦ2 : 2 * Φ.ncard = ((if S.t i r true = t then 1 else 0) +
      (if S.t i r false = t then 1 else 0)) * Nat.card S.N := by
    rw [hΦ]
    exact S.two_mul_ncard_sign _ _
  have hmx : ∀ x ∈ S.D i r,
      {n | n ∈ S.N ∧ S.τ • ((n * x) • S.v i) ∈ S.orb t}.ncard = Φ.ncard := by
    intro x hx
    obtain ⟨n₀, hn₀, u₀, hu₀, rfl⟩ := S.mem_D_iff.1 hx
    have himg : (fun n => n * n₀) '' {n | n ∈ S.N ∧
        S.τ • ((n * (n₀ * S.h i r * u₀)) • S.v i) ∈ S.orb t} = Φ := by
      rw [hΦ]
      ext n'
      constructor
      · rintro ⟨n, ⟨hn, hP⟩, rfl⟩
        refine ⟨S.N.mul_mem hn hn₀, ?_⟩
        rw [show n * (n₀ * S.h i r * u₀) = n * n₀ * S.h i r * u₀ by group] at hP
        exact (S.tau_smul_mem_orb_iff hO i r (S.N.mul_mem hn hn₀) hu₀ t).1 hP
      · rintro ⟨hn', hφ⟩
        refine ⟨n' * n₀⁻¹, ⟨S.N.mul_mem hn' (S.N.inv_mem hn₀), ?_⟩, by simp⟩
        rw [show n' * n₀⁻¹ * (n₀ * S.h i r * u₀) = n' * S.h i r * u₀ by group]
        exact (S.tau_smul_mem_orb_iff hO i r hn' hu₀ t).2 hφ
    rw [← himg, Set.ncard_image_of_injective _ (mul_left_injective n₀)]
  have havg := card_mul_ncard_filter_eq S.N (S.finite_D i r)
    (fun n hn x => S.mul_mem_D_iff i r hn x) (fun g => S.τ • (g • S.v i) ∈ S.orb t)
    (m := Φ.ncard) hmx
  have hpos := S.card_N_pos
  have hD' : (S.D i r).ncard = Nat.card (S.D i r) := (Nat.card_coe_set_eq _).symm
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card S.N * (2 * {g | g ∈ S.D i r ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard)
      = 2 * (Nat.card S.N * {g | g ∈ S.D i r ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard) := by ring
    _ = 2 * (Φ.ncard * (S.D i r).ncard) := by rw [havg]
    _ = (2 * Φ.ncard) * (S.D i r).ncard := by ring
    _ = _ := by rw [hΦ2]; ring

theorem card_X0_eq_sum [Fintype I] [Finite S.H] (hO : Function.Injective S.orb) :
    Nat.card S.X0 = ∑ i, Nat.card (S.orb i) := by
  have hdisj : Pairwise (Function.onFun Disjoint S.orb) := fun i j hij =>
    Set.disjoint_left.2 fun x hxi hxj => hij (S.eq_of_mem_orb hO hxi hxj)
  have hfin : ∀ i, Finite (S.orb i) := fun i => (S.finite_orb i).to_subtype
  exact card_iUnion_of_pairwise_disjoint hdisj

end Counting

section Matrix

variable [DecidableEq I] [∀ i, Fintype (R i)]

@[expose] noncomputable def M (t i : I) : ℕ :=
  ∑ r : R i, S.k i r * ((if S.t i r true = t then 1 else 0) + (if S.t i r false = t then 1 else 0))

theorem two_mul_ncard_filter_H [Finite S.H] (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i)))
    (hO : Function.Injective S.orb) (i t : I) :
    2 * {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard = Nat.card S.N * S.M t i := by
  classical
  obtain ⟨E, hE⟩ : ∃ E : R i → Set G,
      ∀ r, E r = {g | g ∈ S.D i r ∧ S.τ • (g • S.v i) ∈ S.orb t} := ⟨_, fun _ => rfl⟩
  have hunion : {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t} = ⋃ r, E r := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hE]
    constructor
    · rintro ⟨hg, hP⟩
      obtain ⟨r, hr⟩ := Set.mem_iUnion.1 (S.cover i hg)
      exact ⟨r, hr, hP⟩
    · rintro ⟨r, hr, hP⟩
      exact ⟨S.D_subset_H i r hr, hP⟩
  have hsub : ∀ r, E r ⊆ S.D i r := fun r g hg => by rw [hE r] at hg; exact hg.1
  have hdisj : Pairwise (Function.onFun Disjoint E) := fun r r' hrr' =>
    (hD i hrr').mono (hsub r) (hsub r')
  have hfin : ∀ r, Finite (E r) := fun r => ((S.finite_D i r).subset (hsub r)).to_subtype
  have hcard : {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard = ∑ r, (E r).ncard := by
    rw [hunion, ← Nat.card_coe_set_eq, card_iUnion_of_pairwise_disjoint hdisj]
    exact Finset.sum_congr rfl fun r _ => Nat.card_coe_set_eq _
  rw [hcard, M, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hD' : (S.D i r).ncard = Nat.card (S.D i r) := (Nat.card_coe_set_eq _).symm
  rw [hE r, S.two_mul_ncard_filter hO i t r, hD', ← S.card_D_eq i r]
  ring

theorem card_transition_mul [Finite S.H] (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i)))
    (hO : Function.Injective S.orb) (i t : I) :
    Nat.card (S.trans i t) * S.L = Nat.card (S.orb i) * S.M t i := by
  have h1 : Nat.card (S.trans i t) * Nat.card (stabilizer S.H (S.v i)) =
      {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard := by
    have h : Nat.card {g : S.H // S.τ • ((g : S.H) • S.v i) ∈ S.orb t} =
        Nat.card {w : MulAction.orbit S.H (S.v i) // S.τ • (w : X) ∈ S.orb t} *
          Nat.card (stabilizer S.H (S.v i)) :=
      card_filter_smul (K := S.H) (S.v i) (fun w => S.τ • w ∈ S.orb t)
    rw [← Nat.card_coe_set_eq]
    have e1 : {g : S.H // S.τ • ((g : S.H) • S.v i) ∈ S.orb t} ≃
        {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ S.H)
        (fun g => S.τ • (g • S.v i) ∈ S.orb t)
    have e2 : {w : MulAction.orbit S.H (S.v i) // S.τ • (w : X) ∈ S.orb t} ≃ S.trans i t :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun w => w ∈ S.orb i) (fun w => S.τ • w ∈ S.orb t)
    rw [← Nat.card_congr e1, h, Nat.card_congr e2]
  have h2 := S.card_orb_mul_card_stabilizer i
  have h3 := S.two_mul_ncard_filter_H hD hO i t
  have h4 := S.L_mul_card_N
  have hpos : 0 < Nat.card S.N * Nat.card (stabilizer S.H (S.v i)) :=
    Nat.mul_pos S.card_N_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (S.trans i t) * S.L * (Nat.card S.N * Nat.card (stabilizer S.H (S.v i)))
      = (Nat.card (S.trans i t) * Nat.card (stabilizer S.H (S.v i))) * (S.L * Nat.card S.N) := by
        ring
    _ = {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard * (2 * Nat.card S.H) := by rw [h1, h4]
    _ = (2 * {g | g ∈ S.H ∧ S.τ • (g • S.v i) ∈ S.orb t}.ncard) * Nat.card S.H := by ring
    _ = (Nat.card S.N * S.M t i) * (Nat.card (S.orb i) * Nat.card (stabilizer S.H (S.v i))) := by
        rw [h3, h2]
    _ = Nat.card (S.orb i) * S.M t i * (Nat.card S.N * Nat.card (stabilizer S.H (S.v i))) := by
        ring

theorem sum_transition_eq [Fintype I] [Finite S.H]
    (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i))) (hO : Function.Injective S.orb)
    (t : I) : ∑ i, S.M t i * Nat.card (S.orb i) = S.L * Nat.card (S.orb t) := by
  have hdisj : Pairwise (Function.onFun Disjoint fun i => S.trans i t) := fun i j hij =>
    Set.disjoint_left.2 fun x hxi hxj => hij (S.eq_of_mem_orb hO hxi.1 hxj.1)
  have hfin : ∀ i, Finite (S.trans i t) := fun i =>
    ((S.finite_orb i).subset fun w hw => hw.1).to_subtype
  have hU : (⋃ i, S.trans i t) = {w | S.τ • w ∈ S.orb t} := by
    ext w
    simp only [Set.mem_iUnion, trans, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, -, h⟩
      exact h
    · intro h
      have hw : w ∈ S.X0 := by
        simpa using S.tau_inv_smul_mem_X0 (S.orb_subset_X0 t h)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hw
      exact ⟨i, hi, h⟩
  have h1 : ∑ i, Nat.card (S.trans i t) = Nat.card (S.orb t) := by
    rw [← card_iUnion_of_pairwise_disjoint hdisj, hU]
    exact Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm S.τ) fun w => Iff.rfl)
  calc ∑ i, S.M t i * Nat.card (S.orb i) = ∑ i, Nat.card (S.trans i t) * S.L := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [S.card_transition_mul hD hO i t, mul_comm]
    _ = (∑ i, Nat.card (S.trans i t)) * S.L := (Finset.sum_mul _ _ _).symm
    _ = S.L * Nat.card (S.orb t) := by rw [h1, mul_comm]

theorem sum_transition_eq_int [Fintype I] [Finite S.H]
    (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i))) (hO : Function.Injective S.orb)
    (t : I) :
    ∑ i, (S.M t i : ℤ) * (Nat.card (S.orb i) : ℤ) = (S.L : ℤ) * (Nat.card (S.orb t) : ℤ) := by
  exact_mod_cast S.sum_transition_eq hD hO t

end Matrix

section Schreier

variable (γ : I → G)

@[expose] def lam (i : I) (r : R i) (ε : Bool) : G :=
  (γ (S.t i r ε))⁻¹ * S.κ i r ε * tpow S.τ ε * S.h i r * γ i

@[expose] def schreierGens (i₀ : I) : Set G :=
  {g | g ∈ S.H ∧ g • S.v i₀ = S.v i₀} ∪ {g | ∃ i, ∃ u ∈ S.U i, g = (γ i)⁻¹ * u * γ i} ∪
    {g | ∃ (i : I) (r : R i) (ε : Bool), g = S.lam γ i r ε}

variable {γ}

theorem mem_schreierGens_iff {i₀ : I} {g : G} :
    g ∈ S.schreierGens γ i₀ ↔ (g ∈ S.H ∧ g • S.v i₀ = S.v i₀) ∨
      (∃ i, ∃ u ∈ S.U i, g = (γ i)⁻¹ * u * γ i) ∨
        ∃ (i : I) (r : R i) (ε : Bool), g = S.lam γ i r ε := by
  simp only [schreierGens, Set.mem_union, Set.mem_ofPred_eq, or_assoc]

theorem schreierGens_subset_stabilizer {i₀ : I} (hγ : ∀ i, γ i • S.v i₀ = S.v i) :
    S.schreierGens γ i₀ ⊆ MulAction.stabilizer G (S.v i₀) := by
  intro g hg
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  rcases S.mem_schreierGens_iff.1 hg with ⟨-, h⟩ | ⟨i, u, hu, rfl⟩ | ⟨i, r, ε, rfl⟩
  · exact h
  · have hu' : u • S.v i = S.v i := MulAction.mem_stabilizer_iff.1 (S.U_le_stabilizer i hu)
    calc ((γ i)⁻¹ * u * γ i) • S.v i₀ = (γ i)⁻¹ • (u • (γ i • S.v i₀)) := by simp only [mul_smul]
      _ = (γ i)⁻¹ • (u • S.v i) := by rw [hγ i]
      _ = (γ i)⁻¹ • S.v i := by rw [hu']
      _ = S.v i₀ := by rw [← hγ i, inv_smul_smul]
  · calc S.lam γ i r ε • S.v i₀
        = (γ (S.t i r ε))⁻¹ • ((S.κ i r ε * tpow S.τ ε * S.h i r) • (γ i • S.v i₀)) := by
          simp only [lam, mul_smul]
      _ = (γ (S.t i r ε))⁻¹ • ((S.κ i r ε * tpow S.τ ε * S.h i r) • S.v i) := by rw [hγ i]
      _ = (γ (S.t i r ε))⁻¹ • S.v (S.t i r ε) := by rw [S.spec]
      _ = S.v i₀ := by rw [← hγ (S.t i r ε), inv_smul_smul]

theorem closure_schreierGens_le {K : Subgroup G} {i₀ : I}
    (h₁ : ∀ g ∈ S.H, g • S.v i₀ = S.v i₀ → g ∈ K)
    (h₂ : ∀ i, ∀ u ∈ S.U i, (γ i)⁻¹ * u * γ i ∈ K) (h₃ : ∀ i r ε, S.lam γ i r ε ∈ K) :
    Subgroup.closure (S.schreierGens γ i₀) ≤ K := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases S.mem_schreierGens_iff.1 hg with ⟨hg₁, hg₂⟩ | ⟨i, u, hu, rfl⟩ | ⟨i, r, ε, rfl⟩
  · exact h₁ g hg₁ hg₂
  · exact h₂ i u hu
  · exact h₃ i r ε

theorem step_H (T : Subgroup G) {g : G} (hg : g ∈ S.H) (i : I) {c : G} (hc : c ∈ S.H) :
    ∃ (i' : I) (c' : G), c' ∈ S.H ∧ g • (c • S.v i) = c' • S.v i' ∧
      (c' * γ i')⁻¹ * g * (c * γ i) ∈ T := by
  refine ⟨i, g * c, S.H.mul_mem hg hc, by rw [mul_smul], ?_⟩
  have : (g * c * γ i)⁻¹ * g * (c * γ i) = 1 := by group
  rw [this]
  exact T.one_mem

theorem step_tpow (T : Subgroup G) (hlam : ∀ i r ε, S.lam γ i r ε ∈ T)
    (hU : ∀ i, ∀ u ∈ S.U i, (γ i)⁻¹ * u * γ i ∈ T) (ε : Bool) (i : I) {c : G} (hc : c ∈ S.H) :
    ∃ (i' : I) (c' : G), c' ∈ S.H ∧ tpow S.τ ε • (c • S.v i) = c' • S.v i' ∧
      (c' * γ i')⁻¹ * tpow S.τ ε * (c * γ i) ∈ T := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 (S.cover i hc)
  obtain ⟨n, hn, u, hu, rfl⟩ := S.mem_D_iff.1 hr
  obtain ⟨ε', c', hc', -, -, hK⟩ := S.transition ε i r hn
  refine ⟨S.t i r ε', c', hc', S.tpow_smul_of_eq hu hK, ?_⟩
  have key : (c' * γ (S.t i r ε'))⁻¹ * tpow S.τ ε * (n * S.h i r * u * γ i) =
      S.lam γ i r ε' * ((γ i)⁻¹ * u * γ i) := by
    calc (c' * γ (S.t i r ε'))⁻¹ * tpow S.τ ε * (n * S.h i r * u * γ i)
        = (γ (S.t i r ε'))⁻¹ * c'⁻¹ * (tpow S.τ ε * (n * S.h i r)) * u * γ i := by group
      _ = (γ (S.t i r ε'))⁻¹ * c'⁻¹ * (c' * (S.κ i r ε' * tpow S.τ ε' * S.h i r)) * u * γ i := by
        rw [hK]
      _ = S.lam γ i r ε' * ((γ i)⁻¹ * u * γ i) := by simp only [lam]; group
  rw [key]
  exact T.mul_mem (hlam i r ε') (hU i u hu)

theorem step_closure (T : Subgroup G) (hlam : ∀ i r ε, S.lam γ i r ε ∈ T)
    (hU : ∀ i, ∀ u ∈ S.U i, (γ i)⁻¹ * u * γ i ∈ T) {g : G}
    (hg : g ∈ Subgroup.closure ((S.H : Set G) ∪ {S.τ})) :
    ∀ (i : I) {c : G}, c ∈ S.H → ∃ (i' : I) (c' : G), c' ∈ S.H ∧
      g • (c • S.v i) = c' • S.v i' ∧ (c' * γ i')⁻¹ * g * (c * γ i) ∈ T := by
  induction hg using Subgroup.closure_induction'' with
  | mem y hy =>
    intro i c hc
    rcases hy with hy | hy
    · exact S.step_H T hy i hc
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact S.step_tpow T hlam hU true i hc
  | inv_mem y hy =>
    intro i c hc
    rcases hy with hy | hy
    · exact S.step_H T (S.H.inv_mem hy) i hc
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact S.step_tpow T hlam hU false i hc
  | one =>
    intro i c hc
    refine ⟨i, c, hc, by rw [one_smul], ?_⟩
    have : (c * γ i)⁻¹ * 1 * (c * γ i) = 1 := by group
    rw [this]
    exact T.one_mem
  | mul y z _ _ hy hz =>
    intro i c hc
    obtain ⟨i₂, c₂, hc₂, h₂, f₂⟩ := hz i hc
    obtain ⟨i₃, c₃, hc₃, h₃, f₃⟩ := hy i₂ hc₂
    refine ⟨i₃, c₃, hc₃, by rw [mul_smul, h₂, h₃], ?_⟩
    have : (c₃ * γ i₃)⁻¹ * (y * z) * (c * γ i) =
        ((c₃ * γ i₃)⁻¹ * y * (c₂ * γ i₂)) * ((c₂ * γ i₂)⁻¹ * z * (c * γ i)) := by group
    rw [this]
    exact T.mul_mem f₃ f₂

theorem stabilizer_inf_closure_eq (hO : Function.Injective S.orb) {i₀ : I}
    (hγ : ∀ i, γ i • S.v i₀ = S.v i)
    (hγC : ∀ i, γ i ∈ Subgroup.closure ((S.H : Set G) ∪ {S.τ})) (hγ₀ : γ i₀ ∈ S.H) :
    MulAction.stabilizer G (S.v i₀) ⊓ Subgroup.closure ((S.H : Set G) ∪ {S.τ}) =
      Subgroup.closure (S.schreierGens γ i₀) := by
  set T := Subgroup.closure (S.schreierGens γ i₀) with hT
  have hH : ∀ c ∈ S.H, c • S.v i₀ = S.v i₀ → c ∈ T := fun c hc hcv =>
    Subgroup.subset_closure (S.mem_schreierGens_iff.2 (Or.inl ⟨hc, hcv⟩))
  have hU : ∀ i, ∀ u ∈ S.U i, (γ i)⁻¹ * u * γ i ∈ T := fun i u hu =>
    Subgroup.subset_closure (S.mem_schreierGens_iff.2 (Or.inr (Or.inl ⟨i, u, hu, rfl⟩)))
  have hlam : ∀ i r ε, S.lam γ i r ε ∈ T := fun i r ε =>
    Subgroup.subset_closure (S.mem_schreierGens_iff.2 (Or.inr (Or.inr ⟨i, r, ε, rfl⟩)))
  apply le_antisymm
  · rintro g ⟨hgs, hgC⟩
    obtain ⟨i', c', hc', hpt, hF⟩ := S.step_closure T hlam hU hgC i₀ S.H.one_mem
    have hg0 : g • S.v i₀ = S.v i₀ := MulAction.mem_stabilizer_iff.1 hgs
    rw [one_smul, hg0] at hpt
    have hi' : i' = i₀ :=
      S.eq_of_mem_orb hO (S.mem_orb_iff.2 ⟨c', hc', hpt.symm⟩) (S.v_mem_orb i₀)
    rw [hi'] at hpt hF
    have hc'T : c' ∈ T := hH c' hc' hpt.symm
    have hγ0T : γ i₀ ∈ T := hH _ hγ₀ (hγ i₀)
    have hg' : g = (c' * γ i₀) * ((c' * γ i₀)⁻¹ * g * (1 * γ i₀)) * (γ i₀)⁻¹ := by group
    rw [hg']
    exact T.mul_mem (T.mul_mem (T.mul_mem hc'T hγ0T) hF) (T.inv_mem hγ0T)
  · rw [Subgroup.closure_le]
    intro g hg
    refine Subgroup.mem_inf.2 ⟨S.schreierGens_subset_stabilizer hγ hg, ?_⟩
    have hτ : ∀ ε, tpow S.τ ε ∈ Subgroup.closure ((S.H : Set G) ∪ {S.τ}) := by
      intro ε
      cases ε
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))
      · exact Subgroup.subset_closure (Or.inr rfl)
    have hHC : ∀ c ∈ S.H, c ∈ Subgroup.closure ((S.H : Set G) ∪ {S.τ}) := fun c hc =>
      Subgroup.subset_closure (Or.inl hc)
    rcases S.mem_schreierGens_iff.1 hg with ⟨h1, -⟩ | ⟨i, u, hu, rfl⟩ | ⟨i, r, ε, rfl⟩
    · exact hHC g h1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hγC i))
        (hHC u (S.U_le_H i hu))) (hγC i)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (hγC _)) (hHC _ (S.κ_mem i r ε))) (hτ ε)) (hHC _ (S.h_mem i r)))
        (hγC i)

theorem stabilizer_eq_closure (hO : Function.Injective S.orb) {i₀ : I}
    (hG : Subgroup.closure ((S.H : Set G) ∪ {S.τ}) = ⊤)
    (hγ : ∀ i, γ i • S.v i₀ = S.v i) (hγ₀ : γ i₀ ∈ S.H) :
    MulAction.stabilizer G (S.v i₀) = Subgroup.closure (S.schreierGens γ i₀) := by
  have h := S.stabilizer_inf_closure_eq hO hγ (fun i => by rw [hG]; exact Subgroup.mem_top _) hγ₀
  rwa [hG, inf_top_eq] at h

end Schreier

end Setup

end Setting

end CFSG.Monster.AxisCount
