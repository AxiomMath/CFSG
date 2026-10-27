module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.LocalAnalysis.StandardType.GGSporKRestEval

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_mem_closure_iff_mem_table {K : Type} [Group K] (sg T : List K)
    (h1 : (1 : K) ∈ T) (hcl : ∀ t ∈ T, ∀ g ∈ sg, t * g ∈ T ∧ t * g⁻¹ ∈ T)
    (hgen : ∀ t ∈ T, t ∈ Subgroup.closure {g | g ∈ sg}) (x : K) :
    x ∈ Subgroup.closure {g | g ∈ sg} ↔ x ∈ T := by
  constructor
  · intro hx
    have hmul : ∀ t ∈ T, t * x ∈ T :=
      Subgroup.closure_induction'' (s := {g | g ∈ sg}) (p := fun y _ => ∀ t ∈ T, t * y ∈ T)
        (fun y hy t ht => (hcl t ht y hy).1)
        (fun y hy t ht => (hcl t ht y hy).2)
        (fun t ht => by simpa using ht)
        (fun y₁ y₂ _ _ ih₁ ih₂ t ht => by
          have h1' : t * y₁ ∈ T := ih₁ t ht
          have h2' : (t * y₁) * y₂ ∈ T := ih₂ (t * y₁) h1'
          rw [← mul_assoc]
          exact h2')
        hx
    simpa using hmul 1 h1
  · intro hx
    exact hgen x hx

theorem sporKRest_card_closure_of_table {K : Type} [Group K] (sg T : List K)
    (h1 : (1 : K) ∈ T) (hcl : ∀ t ∈ T, ∀ g ∈ sg, t * g ∈ T ∧ t * g⁻¹ ∈ T)
    (hgen : ∀ t ∈ T, t ∈ Subgroup.closure {g | g ∈ sg}) (hnd : T.Nodup) :
    Nat.card (Subgroup.closure {g | g ∈ sg}) = T.length := by
  classical
  have hiff : ∀ x : K, x ∈ Subgroup.closure {g | g ∈ sg} ↔ x ∈ T :=
    fun x => sporKRest_mem_closure_iff_mem_table sg T h1 hcl hgen x
  have h1' : Nat.card (Subgroup.closure {g | g ∈ sg}) = Nat.card {x : K // x ∈ T} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have h2' : Nat.card {x : K // x ∈ T} = T.toFinset.card :=
    calc Nat.card {x : K // x ∈ T}
        = Nat.card ↥(T.toFinset) :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun x => (List.mem_toFinset).symm))
      _ = T.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have h3' : T.toFinset.card = T.length := List.toFinset_card_of_nodup hnd
  exact h1'.trans (h2'.trans h3')

theorem sporKRest_generating_of_data {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (a b : K) (hab : Subgroup.closure ({a, b} : Set K) = ⊤)
    (S : Sylow p K) (sg : List K) (hS : (S : Subgroup K) = Subgroup.closure {g | g ∈ sg})
    (x₀ : K) (ent : List (K × K × List K))
    (hent : ∀ e ∈ ent, e.1 ∈ (S : Subgroup K) ∧ e.2.1⁻¹ * x₀ * e.2.1 = e.1 ∧
      ∀ z ∈ e.2.2, z * e.1 = e.1 * z)
    (wa wb : List ℤ) (ha : sporKRestEval (sg ++ ent.flatMap fun e => e.2.2) wa = a)
    (hb : sporKRestEval (sg ++ ent.flatMap fun e => e.2.2) wb = b)
    {x : K} (hx : IsConj x₀ x) : SporKRestGenerating p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ggSporKRest_generating_of_closure hp S hx
    {z : K | z ∈ ent.flatMap fun e => e.2.2} ?_ ?_
  · intro z hz
    rw [Set.mem_setOf_eq, List.mem_flatMap] at hz
    obtain ⟨e, he, hze⟩ := hz
    obtain ⟨he1S, he2, hzcent⟩ := hent e he
    exact ⟨e.2.1, e.1, he1S, he2,
      (Subgroup.mem_centralizer_singleton_iff).mpr (hzcent z hze)⟩
  · set L : Subgroup K :=
      Subgroup.closure ((S : Set K) ∪ {z : K | z ∈ ent.flatMap fun e => e.2.2}) with hL
    have hSL : (S : Subgroup K) ≤ L := by
      rw [hL]
      intro y hy
      exact Subgroup.subset_closure (Set.mem_union_left _ hy)
    have hTL : ∀ z ∈ ent.flatMap (fun e => e.2.2), z ∈ L := by
      intro z hz
      rw [hL]
      exact Subgroup.subset_closure (Set.mem_union_right _ hz)
    rw [eq_top_iff, ← hab]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hmem : ∀ g ∈ sg ++ ent.flatMap (fun e => e.2.2), g ∈ L := by
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hgsg | hgflat
      · apply hSL
        rw [hS]
        exact Subgroup.subset_closure hgsg
      · exact hTL g hgflat
    rcases hz with rfl | rfl
    · have h := sporKRestEval_mem (sg ++ ent.flatMap fun e => e.2.2) wa L hmem
      simpa [ha] using h
    · have h := sporKRestEval_mem (sg ++ ent.flatMap fun e => e.2.2) wb L hmem
      simpa [hb] using h

theorem sporKRest_cover_of_data {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (S : Sylow p K) (T : List K) (hT : ∀ x ∈ (S : Subgroup K), x ∈ T) (reps : List K)
    (hreps : ∀ r ∈ reps, ∀ x : K, IsConj r x → SporKRestGenerating p x)
    (hcensus : ∀ t ∈ T, t ≠ 1 → ∃ r ∈ reps, ∃ g : K, g⁻¹ * r * g = t) : SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E _hE hcard
  have hlt : 1 < Nat.card E := by
    rw [hcard]
    nlinarith [hp.two_le]
  have hbot : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp hlt
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hbot
  obtain ⟨x, hxE, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial E
  have hEp : IsPGroup p ↥E := IsPGroup.of_card hcard
  have hzp : IsPGroup p ↥(Subgroup.zpowers x) :=
    hEp.to_le (Subgroup.zpowers_le.mpr hxE)
  obtain ⟨Q, hxQ⟩ := hzp.exists_le_sylow
  have hxQmem : x ∈ Q := hxQ (Subgroup.mem_zpowers x)
  letI : MulAction.IsPretransitive K (Sylow p K) :=
    Sylow.isPretransitive_of_finite (p := p) (G := K)
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := K) S Q
  have hxS : g⁻¹ * x * g ∈ (S : Subgroup K) := by
    have hxg : x ∈ ((g • S : Sylow p K) : Subgroup K) := by rw [hg]; exact hxQmem
    rw [Sylow.coe_subgroup_smul] at hxg
    refine (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj g)
      (S := (S : Subgroup K)) (x := g⁻¹ * x * g)).mp ?_
    have hax : (MulAut.conj g) • (g⁻¹ * x * g) = x := by
      change (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group
    rw [hax]
    exact hxg
  have htT : g⁻¹ * x * g ∈ T := hT _ hxS
  have ht1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  obtain ⟨r, hr, g', hg'⟩ := hcensus _ htT ht1
  refine ⟨x, hxE, hx1, hreps r hr x ?_⟩
  rw [isConj_iff]
  refine ⟨g * g'⁻¹, ?_⟩
  calc (g * g'⁻¹) * r * (g * g'⁻¹)⁻¹
      = g * (g'⁻¹ * r * g') * g⁻¹ := by group
    _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hg']
    _ = x := by group

end CFSG.StandardType.SporadicShape
