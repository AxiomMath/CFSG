module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.RingTheory.RootsOfUnity.Basic

public section

namespace CFSG.RankThree.PartOne.BRANCH

theorem exists_stabilizer_card_ge {E Ω : Type} [Group E] [Finite E] [MulAction E Ω] [Finite Ω]
    {r a : ℕ} (hr : r.Prime) (hE : IsPGroup r E) (hΩ : ¬ r ^ (a + 1) ∣ Nat.card Ω) :
    ∃ x : Ω, Nat.card E ≤ r ^ a * Nat.card (MulAction.stabilizer E x) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype E := Fintype.ofFinite E
  have : Fintype Ω := Fintype.ofFinite Ω
  obtain ⟨m, hm⟩ := hE.exists_card_eq
  by_contra hcon
  push Not at hcon
  apply hΩ
  rw [Nat.card_eq_fintype_card, MulAction.card_eq_sum_card_group_div_card_stabilizer E Ω]
  refine Finset.dvd_sum fun ω _ => ?_
  set x : Ω := ω.out with hx
  have hlt := hcon x
  have hdvd : Nat.card (MulAction.stabilizer E x) ∣ Nat.card E :=
    Subgroup.card_subgroup_dvd_card _
  have hpos : 0 < Nat.card (MulAction.stabilizer E x) := Nat.card_pos
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  set o := Nat.card E / Nat.card (MulAction.stabilizer E x) with ho
  have hmul : o * Nat.card (MulAction.stabilizer E x) = Nat.card E := Nat.div_mul_cancel hdvd
  have hodvd : o ∣ r ^ m := ⟨Nat.card (MulAction.stabilizer E x), by rw [← hm, ← hmul, mul_comm]⟩
  obtain ⟨j, hjm, hj⟩ := (Nat.dvd_prime_pow hr).1 hodvd
  have hao : r ^ a < o := by
    refine Nat.lt_of_mul_lt_mul_right (a := Nat.card (MulAction.stabilizer E x)) ?_
    rw [hmul]
    exact hlt
  rw [hj] at hao
  have haj : a < j := (Nat.pow_lt_pow_iff_right hr.one_lt).1 hao
  rw [hj]
  exact pow_dvd_pow r haj

theorem exists_conj_le_of_not_dvd_index {G : Type} [Group G] [Finite G] (T : Subgroup G)
    {r a : ℕ} (hr : r.Prime) (hT : ¬ r ^ (a + 1) ∣ T.index) {E : Subgroup G} (hE : IsPGroup r E) :
    ∃ (g : G) (E₁ : Subgroup G), E₁ ≤ E ∧ Nat.card E ≤ r ^ a * Nat.card E₁ ∧
      ∀ y ∈ E₁, g⁻¹ * y * g ∈ T := by
  classical
  have hΩ : ¬ r ^ (a + 1) ∣ Nat.card (G ⧸ T) := hT
  obtain ⟨x, hx⟩ := exists_stabilizer_card_ge (E := E) (Ω := G ⧸ T) hr hE hΩ
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨g, (MulAction.stabilizer E (g : G ⧸ T)).map E.subtype, Subgroup.map_subtype_le _, ?_,
      ?_⟩
    · rwa [Subgroup.card_map_of_injective E.subtype_injective]
    · rintro _ ⟨e, he, rfl⟩
      have h1 : (e : G) • (g : G ⧸ T) = (g : G ⧸ T) := he
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
      have h2 := T.inv_mem h1
      simpa [mul_assoc] using h2

theorem card_le_pow_of_injective_units {E : Type} {L : Type} [Field L] {k r : ℕ} (hr : 0 < r)
    (φ : E → (Fin k → Lˣ)) (hφ : Function.Injective φ) (hpow : ∀ x i, φ x i ^ r = 1) :
    Nat.card E ≤ r ^ k := by
  classical
  have : NeZero r := ⟨hr.ne'⟩
  let ψ : E → (Fin k → rootsOfUnity r L) := fun x i =>
    ⟨φ x i, (mem_rootsOfUnity r _).2 (hpow x i)⟩
  have hψ : Function.Injective ψ := fun x y h => hφ (funext fun i =>
    congrArg (fun z : rootsOfUnity r L => (z : Lˣ)) (congrFun h i))
  have hR : Nat.card (rootsOfUnity r L) ≤ r := card_rootsOfUnity L r
  calc Nat.card E ≤ Nat.card (Fin k → rootsOfUnity r L) := Nat.card_le_card_of_injective ψ hψ
    _ = Nat.card (rootsOfUnity r L) ^ k := by rw [Nat.card_fun]; simp
    _ ≤ r ^ k := Nat.pow_le_pow_left hR k

theorem card_le_of_torus' {G : Type} [Group G] [Finite G] {T : Subgroup G} {r a k : ℕ}
    (hr : r.Prime) {L : Type} [Field L] (φ : T → (Fin k → Lˣ)) (hφ : Function.Injective φ)
    (hφr : ∀ t : T, t ^ r = 1 → ∀ i, φ t i ^ r = 1) (hT : ¬ r ^ (a + 1) ∣ T.index)
    {E : Subgroup G} (hE : ∀ x ∈ E, x ^ r = 1) : Nat.card E ≤ r ^ (a + k) := by
  have hP : IsPGroup r E := fun x => ⟨1, Subtype.ext (by simpa using hE x.1 x.2)⟩
  obtain ⟨g, E₁, hE₁, hcard, hmem⟩ := exists_conj_le_of_not_dvd_index T hr hT hP
  let c : E₁ →* T := MonoidHom.codRestrict ((MulAut.conj g⁻¹).toMonoidHom.comp E₁.subtype) T
    fun y => by simpa [MulAut.conj_apply] using hmem y.1 y.2
  have hc : Function.Injective c := fun y z h => by
    have h1 : g⁻¹ * (y : G) * g = g⁻¹ * (z : G) * g := by
      simpa [c, MulAut.conj_apply] using congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hb := card_le_pow_of_injective_units hr.pos (fun y : E₁ => φ (c y))
    (hφ.comp hc) fun y i => by
      refine hφr (c y) ?_ i
      refine Subtype.ext ?_
      have h2 : ((y : G)) ^ r = 1 := hE y.1 (hE₁ y.2)
      have : (c y : G) ^ r = g⁻¹ * (y : G) ^ r * g := by
        have h5 := conj_pow (a := g⁻¹) (b := (y : G)) (i := r)
        simpa [c, MulAut.conj_apply] using h5
      rw [Subgroup.coe_pow, this, h2]
      simp
  calc Nat.card E ≤ r ^ a * Nat.card E₁ := hcard
    _ ≤ r ^ a * r ^ k := Nat.mul_le_mul_left _ hb
    _ = r ^ (a + k) := (pow_add r a k).symm

theorem card_le_of_torus {G : Type} [Group G] [Finite G] {T : Subgroup G} {r a k : ℕ}
    (hr : r.Prime) {L : Type} [Field L] (ψ : T →* (Fin k → Lˣ)) (hψ : Function.Injective ψ)
    (hT : ¬ r ^ (a + 1) ∣ T.index) {E : Subgroup G} (hE : ∀ x ∈ E, x ^ r = 1) :
    Nat.card E ≤ r ^ (a + k) :=
  card_le_of_torus' hr (fun t => ψ t) hψ (fun t ht i => by
    have h3 := congrFun (congrArg ψ ht) i
    rw [map_pow, map_one] at h3
    simpa using h3) hT hE

end CFSG.RankThree.PartOne.BRANCH
