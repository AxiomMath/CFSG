module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveDefs

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs vtype)

variable {G₀ G₁ G₂ : Subgroup G} {X : Subgroup G} {δ : CosetGeom G₀ G₁ G₂}

theorem mem_torusComp_self (X : Subgroup G) (δ : CosetGeom G₀ G₁ G₂) : δ ∈ torusComp X δ :=
  Relation.ReflTransGen.refl

theorem le_stab_of_mem_torusComp (hδ : X ≤ stab δ) {v : CosetGeom G₀ G₁ G₂}
    (hv : v ∈ torusComp X δ) : X ≤ stab v := by
  rcases Relation.ReflTransGen.cases_tail hv with rfl | ⟨c, -, hcv⟩
  · exact hδ
  · exact hcv.2.1

theorem mem_torusComp_of_adj (hδ : X ≤ stab δ) {u v : CosetGeom G₀ G₁ G₂}
    (hu : u ∈ torusComp X δ) (huv : (graph G₀ G₁ G₂).Adj u v) (hv : X ≤ stab v) :
    v ∈ torusComp X δ :=
  Relation.ReflTransGen.tail hu ⟨le_stab_of_mem_torusComp hδ hu, hv, huv⟩

theorem exists_adj_of_mem_torusComp {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ torusComp X δ)
    (hne : v ≠ δ) : ∃ u ∈ torusComp X δ, (graph G₀ G₁ G₂).Adj u v := by
  rcases Relation.ReflTransGen.cases_tail hv with hvd | ⟨u, hu, huv⟩
  · exact absurd hvd hne
  · exact ⟨u, hu, huv.2.2⟩

theorem torusComp_reflTransGen {u v : CosetGeom G₀ G₁ G₂} (hu : u ∈ torusComp X δ)
    (hv : v ∈ torusComp X δ) :
    Relation.ReflTransGen
      (fun a b => a ∈ torusComp X δ ∧ b ∈ torusComp X δ ∧ (graph G₀ G₁ G₂).Adj a b) u v := by
  let R' : CosetGeom G₀ G₁ G₂ → CosetGeom G₀ G₁ G₂ → Prop :=
    fun a b => a ∈ torusComp X δ ∧ b ∈ torusComp X δ ∧ (graph G₀ G₁ G₂).Adj a b
  have key : ∀ {v : CosetGeom G₀ G₁ G₂},
      Relation.ReflTransGen (fun a b => X ≤ stab a ∧ X ≤ stab b ∧ (graph G₀ G₁ G₂).Adj a b)
        δ v → Relation.ReflTransGen R' δ v := by
    intro v h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      exact ih.tail ⟨hab, hab.tail hbc, hbc.2.2⟩
  haveI : Std.Symm R' := ⟨fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  haveI : Std.Symm (Relation.ReflTransGen R') := Relation.ReflTransGen.symmetric
  exact (Std.Symm.symm δ u (key hu)).trans (key hv)

theorem le_stab_smul_of_mem_normalizer {n : ↥G₀}
    (hn : (n : G) ∈ Subgroup.normalizer (X : Set G)) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : X ≤ stab γ) : X ≤ stab (n • γ) := by
  intro x hx
  rw [CosetGeom.stab_smul, mem_conjSub]
  refine hγ ?_
  have hn' : (n : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).inv_mem hn
  simpa using (Subgroup.mem_normalizer_iff.mp hn' x).mp hx

theorem le_ballStab_one_of_ncard_nbrs_eq_three [Finite G] (hG : G₀ = G₁ ⊔ G₂)
    (hX : Odd (Nat.card X)) {y ν : CosetGeom G₀ G₁ G₂} (hy : (nbrs y).ncard = 3)
    (hν : ν ∈ nbrs y) (hXy : X ≤ stab y) (hXν : X ≤ stab ν) : X ≤ ballStab 1 y := by
  intro x hx
  rw [CosetGeom.mem_ballStab]
  intro ε hε
  rcases (CosetGeom.dist_le_one_iff hG).mp hε with rfl | hεadj
  · exact hXy hx
  have hxG₀ : x ∈ G₀ := CosetGeom.stab_le y (hXy hx)
  let g : ↥G₀ := ⟨x, hxG₀⟩
  have hgy : g • y = y := CosetGeom.smul_eq_of_mem_stab (hXy hx)
  have hgν : g • ν = ν := CosetGeom.smul_eq_of_mem_stab (hXν hx)
  have hεnbr : ε ∈ nbrs y := hεadj
  by_cases hεν : ε = ν
  · rw [hεν]
    exact CosetGeom.mem_stab_of_smul_eq hgν
  have hνε : ν ≠ ε := Ne.symm hεν
  refine CosetGeom.mem_stab_of_smul_eq (γ := ε) (g := g) ?_
  by_contra hne
  have hηε : g • ε ≠ ε := hne
  set η : CosetGeom G₀ G₁ G₂ := g • ε with hη
  have hηnbr : η ∈ nbrs y := by
    rw [hη, ← hgy]
    exact (CosetGeom.smul_adj g).mpr hεnbr
  have hην : η ≠ ν := by
    intro h
    exact hεν (MulAction.injective g (h.trans hgν.symm))
  have hηne : η ≠ ε := by
    rw [hη]
    exact hηε
  have hset : nbrs y = {ν, ε, η} := by
    have hsub : ({ν, ε, η} : Set (CosetGeom G₀ G₁ G₂)) ⊆ nbrs y := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hν
      · exact hεnbr
      · exact hηnbr
    have hs : ({ν, ε, η} : Set (CosetGeom G₀ G₁ G₂)).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨ν, ε, η, hνε, Ne.symm hην, Ne.symm hηne, rfl⟩
    have hfin : (nbrs y).Finite := Set.finite_of_ncard_ne_zero (by rw [hy]; norm_num)
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hy, hs]) hfin).symm
  have hgη : g • η = ε := by
    have hmem : g • η ∈ nbrs y := by
      rw [← hgy]
      exact (CosetGeom.smul_adj g).mpr hηnbr
    rw [hset] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd (MulAction.injective g (h.trans hgν.symm)) hην
    · exact h
    · exfalso
      apply hηε
      have h' : g • η = g • ε := h.trans hη
      simpa [hη] using MulAction.injective g h'
  have hg2 : g ^ 2 • ε = ε := by
    rw [pow_two, mul_smul, ← hη, hgη]
  have hodd : Odd (orderOf g) := by
    have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hx)
    have hcoe : orderOf (g : G) = orderOf g := Subgroup.orderOf_coe g
    rw [show (g : G) = x from rfl] at hcoe
    rwa [← hcoe]
  have hfix : ∀ k : ℕ, (g ^ 2) ^ k • ε = ε := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hg2, ih]
  have hpow : g = (g ^ 2) ^ (orderOf g / 2 + 1) := by
    have h1 : g ^ (orderOf g / 2 * 2 + 1) = 1 := by
      rw [Nat.div_two_mul_two_add_one_of_odd hodd, pow_orderOf_eq_one]
    have h2 : g ^ (orderOf g / 2 * 2 + 1 + 1) = g := by
      rw [pow_succ, h1, one_mul]
    have h3 : 2 * (orderOf g / 2 + 1) = orderOf g / 2 * 2 + 1 + 1 := by ring
    calc g = g ^ (orderOf g / 2 * 2 + 1 + 1) := h2.symm
      _ = g ^ (2 * (orderOf g / 2 + 1)) := by rw [h3]
      _ = (g ^ 2) ^ (orderOf g / 2 + 1) := pow_mul g 2 _
  exact hηε (by rw [hη, hpow]; exact hfix (orderOf g / 2 + 1))

end CFSG.Quasithin.F112Crit

end
