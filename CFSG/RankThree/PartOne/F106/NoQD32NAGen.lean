module

public import CFSG.RankThree.PartOne.F106.ThreeRankGen
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup

section Closure

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_closure_of_mul_closed {L : Set G} (h1 : (1 : G) ∈ L)
    (hL : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) : ∀ g ∈ Subgroup.closure L, g ∈ L :=
  mem_of_closure_of_right_closed h1 fun x hx g hg => hL x hx g hg

theorem mem_closure_iff_of_mul_closed {L : Set G} (h1 : (1 : G) ∈ L)
    (hL : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) (g : G) : g ∈ Subgroup.closure L ↔ g ∈ L :=
  ⟨mem_of_closure_of_mul_closed h1 hL g, fun h => Subgroup.subset_closure h⟩

theorem card_le_of_lt {H K : Subgroup G} (hHK : H ≤ K) (hne : H ≠ K) {k : ℕ}
    (hK : Nat.card K = 3 ^ k) : Nat.card H ≤ 3 ^ (k - 1) := by
  have hdvd : Nat.card H ∣ 3 ^ k := hK ▸ Subgroup.card_dvd_of_le hHK
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hjk : j ≠ k := by
    rintro rfl
    apply hne
    exact Subgroup.eq_of_le_of_card_ge hHK (by rw [hK, hjeq])
  rw [hjeq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Closure

section Table

variable {G : Type*} [Group G]

theorem table_subgroup [Finite G] {ι : Type*} (gens : ι → G) (sel : ℕ → G) (hone : sel 0 = 1)
    (hinj : ∀ i < 729, ∀ j < 729, sel i = sel j → i = j)
    (hmem : ∀ i < 729, sel i ∈ Subgroup.closure (Set.range gens))
    (hrt : ∀ i < 729, ∀ k, ∃ j < 729, sel i * gens k = sel j) :
    ∃ S : Subgroup G, Nat.card S = 3 ^ 6 ∧ (∀ i < 729, sel i ∈ S) ∧
      ∀ y ∈ S, ∃ i < 729, y = sel i := by
  classical
  set S : Subgroup G := Subgroup.closure (Set.range gens) with hSdef
  have hexists : ∀ y ∈ S, ∃ i < 729, y = sel i := by
    intro y hy
    exact mem_of_closure_of_right_closed (gens := Set.range gens)
      (L := {x | ∃ i < 729, x = sel i}) ⟨0, by norm_num, hone.symm⟩
      (by
        rintro x ⟨i, hi, rfl⟩ g ⟨k, rfl⟩
        obtain ⟨j, hj, hij⟩ := hrt i hi k
        exact ⟨j, hj, hij⟩) y hy
  refine ⟨S, ?_, hmem, hexists⟩
  have hset : (S : Set G) = Set.range (fun i : Fin 729 => sel i) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, rfl⟩ := hexists y hy
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact hmem i i.2
  have hinj' : Function.Injective (fun i : Fin 729 => sel i) :=
    fun a b h => Fin.ext (hinj a a.2 b b.2 h)
  calc Nat.card S = Nat.card (S : Set G) := rfl
    _ = Nat.card (Set.range (fun i : Fin 729 => sel i)) := by rw [hset]
    _ = Nat.card (Fin 729) := Nat.card_range_of_injective hinj'
    _ = 3 ^ 6 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num

theorem card_eq_filter (S H : Subgroup G) (sel : ℕ → G)
    [DecidablePred fun i => sel i ∈ H]
    (hinj : ∀ i < 729, ∀ j < 729, sel i = sel j → i = j)
    (hS : ∀ y ∈ S, ∃ i < 729, y = sel i) (hHS : H ≤ S) :
    Nat.card H = ((Finset.range 729).filter fun i => sel i ∈ H).card := by
  let Idx : Finset ℕ := (Finset.range 729).filter fun i => sel i ∈ H
  have hb : Function.Bijective (fun i : Idx => (⟨sel i, (Finset.mem_filter.mp i.2).2⟩ : H)) := by
    constructor
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (hinj a (Finset.mem_range.mp (Finset.mem_filter.mp a.2).1) b
        (Finset.mem_range.mp (Finset.mem_filter.mp b.2).1) h1)
    · intro h
      obtain ⟨i, hi, hhi⟩ := hS h (hHS h.2)
      refine ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hhi ▸ h.2⟩⟩, Subtype.ext hhi.symm⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_set_eq_filter (S : Subgroup G) (sel : ℕ → G) (P : G → Prop)
    [DecidablePred fun i => P (sel i)]
    (hinj : ∀ i < 729, ∀ j < 729, sel i = sel j → i = j)
    (hS : ∀ y ∈ S, ∃ i < 729, y = sel i) (hsel : ∀ i < 729, sel i ∈ S) :
    Nat.card {g : G // g ∈ S ∧ P g} = ((Finset.range 729).filter fun i => P (sel i)).card := by
  let Idx : Finset ℕ := (Finset.range 729).filter fun i => P (sel i)
  have hb : Function.Bijective
      (fun i : Idx => (⟨sel i, hsel i (Finset.mem_range.mp (Finset.mem_filter.mp i.2).1),
        (Finset.mem_filter.mp i.2).2⟩ : {g : G // g ∈ S ∧ P g})) := by
    constructor
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (hinj a (Finset.mem_range.mp (Finset.mem_filter.mp a.2).1) b
        (Finset.mem_range.mp (Finset.mem_filter.mp b.2).1) h1)
    · intro h
      obtain ⟨i, hi, hhi⟩ := hS h.1 h.2.1
      refine ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hhi ▸ h.2.2⟩⟩,
        Subtype.ext hhi.symm⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_coe]

end Table

theorem card_filter_range_eq_length (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (q : ℕ → Bool)
    (h : ∀ i < n, p i ↔ q i = true) :
    ((Finset.range n).filter p).card = ((List.range n).filter q).length := by
  have : (Finset.range n).filter p = ((List.range n).filter q).toFinset := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, List.mem_filter,
      List.mem_range]
    constructor
    · rintro ⟨hi, hp⟩
      exact ⟨hi, (h i hi).mp hp⟩
    · rintro ⟨hi, hq⟩
      exact ⟨hi, (h i hi).mpr hq⟩
  rw [this, List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range))]

section Conj

theorem exists_mulEquiv_conj {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (g : X')
    (E : Subgroup X) (E₀ : Subgroup X')
    (h : (E.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = E₀) :
    ∃ ψ : ↥E ≃* ↥E₀, ∀ x : ↥E, ((ψ x : ↥E₀) : X') = g * e (x : X) * g⁻¹ := by
  refine ⟨((E.equivMapOfInjective e.toMonoidHom e.injective).trans
    ((E.map e.toMonoidHom).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).trans (MulEquiv.subgroupCongr h), fun x => rfl⟩

theorem map_comm_of_comm {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (E : Subgroup G)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∀ x ∈ E.map φ, ∀ y ∈ E.map φ, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hcomm a ha b hb]

theorem map_pow_of_pow {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (E : Subgroup G) (n : ℕ)
    (hcube : ∀ a ∈ E, a ^ n = 1) : ∀ x ∈ E.map φ, x ^ n = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hcube a ha, map_one]

end Conj

end CFSG.RankThree.PartOne.F106
