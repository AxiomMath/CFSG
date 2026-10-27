module

public import CFSG.OddTranspositions.QHypTransvection
public import CFSG.Timmesfeld.Transvection.QTwoThin
public import CFSG.Fischer.Classification.Basic.Reduced

public section

namespace CFSG.OddTranspositions

open CFSG.Blueprint.Fischer CFSG.Timmesfeld.Transvection.QTwo
open CFSG.Fischer.Classification Equiv

theorem swap_eq_swap_of_mem_pair {α : Type*} [DecidableEq α] {p q x y : α}
    (hx : x ∈ ({p, q} : Finset α)) (hy : y ∈ ({p, q} : Finset α)) (hxy : x ≠ y) :
    swap x y = swap p q := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · rfl
  · exact (swap_comm _ _).symm
  · exact absurd rfl hxy

theorem exists_swap_thick {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 6)
    {σ τ : Perm α} (hσ : σ.IsSwap) (hτ : τ.IsSwap) (hστ : σ ≠ τ)
    (hc : σ * τ = τ * σ) :
    ∃ γ : Perm α, γ.IsSwap ∧ γ ≠ σ ∧ γ ≠ τ ∧
      ∀ δ : Perm α, δ.IsSwap → δ * σ = σ * δ → δ * τ = τ * δ → δ * γ = γ * δ := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  obtain ⟨hac, had, hbc, hbd⟩ := disjoint_of_swap_commute hab hcd hστ hc
  have hcard4 : ({a, b, c, d} : Finset α).card = 4 :=
    Finset.card_eq_four.2 ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have hcompl : ({a, b, c, d} : Finset α)ᶜ.card = 2 := by
    rw [Finset.card_compl, hcard4, hα]
  obtain ⟨p, q, hpq, hpq_eq⟩ := Finset.card_eq_two.1 hcompl
  have hp_not : p ∉ ({a, b, c, d} : Finset α) := by
    rw [← Finset.mem_compl, hpq_eq]
    simp
  have hq_not : q ∉ ({a, b, c, d} : Finset α) := by
    rw [← Finset.mem_compl, hpq_eq]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp_not hq_not
  obtain ⟨hpa, hpb, hpc, hpd⟩ := hp_not
  obtain ⟨hqa, hqb, hqc, hqd⟩ := hq_not
  have hmem : ∀ z : α, z ∉ ({a, b, c, d} : Finset α) → z ∈ ({p, q} : Finset α) := by
    intro z hz
    rw [← hpq_eq, Finset.mem_compl]
    exact hz
  have hσγ : swap a b * swap p q = swap p q * swap a b :=
    swap_commute_of_ne hab hpq (Ne.symm hpa) (Ne.symm hqa) (Ne.symm hpb) (Ne.symm hqb)
  have hτγ : swap c d * swap p q = swap p q * swap c d :=
    swap_commute_of_ne hcd hpq (Ne.symm hpc) (Ne.symm hqc) (Ne.symm hpd) (Ne.symm hqd)
  refine ⟨swap p q, ⟨p, q, hpq, rfl⟩, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun f : Perm α => f p) h
    rw [swap_apply_left, swap_apply_of_ne_of_ne hpa hpb] at h1
    exact hpq h1.symm
  · intro h
    have h1 := congrArg (fun f : Perm α => f p) h
    rw [swap_apply_left, swap_apply_of_ne_of_ne hpc hpd] at h1
    exact hpq h1.symm
  · intro δ hδ hδσ hδτ
    obtain ⟨x, y, hxy, rfl⟩ := hδ
    by_cases hδe : swap x y = swap a b
    · rw [hδe]
      exact hσγ
    by_cases hδf : swap x y = swap c d
    · rw [hδf]
      exact hτγ
    obtain ⟨hax, hay, hbx, hby⟩ := disjoint_of_swap_commute hab hxy (Ne.symm hδe) hδσ.symm
    obtain ⟨hcx, hcy, hdx, hdy⟩ := disjoint_of_swap_commute hcd hxy (Ne.symm hδf) hδτ.symm
    have hx_not : x ∉ ({a, b, c, d} : Finset α) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hax, Ne.symm hbx, Ne.symm hcx, Ne.symm hdx⟩
    have hy_not : y ∉ ({a, b, c, d} : Finset α) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hay, Ne.symm hby, Ne.symm hcy, Ne.symm hdy⟩
    have hγeq : swap x y = swap p q :=
      swap_eq_swap_of_mem_pair (hmem x hx_not) (hmem y hy_not) hxy
    rw [hγeq]

theorem qHyp_perm_six {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    (φ : G ≃* Equiv.Perm (Fin 6)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) :
    QHyp G D := by
  have hna' : ¬ ∀ a b : commutator G, a * b = b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact fun hall => hab (hall a b)
  refine { hyp := ⟨hP, hZ, hS⟩, rank := ?_, points := ?_, thick := ?_ }
  · exact Pair.exists_ne_commute hP hS hna'
  · intro e he f hf h
    exact Pair.eq_of_forall_commute_iff hP hZ hS he hf h
  · intro e he f hf hef hc
    have hστ : φ e ≠ φ f := fun h => hef (φ.injective h)
    have hc' : φ e * φ f = φ f * φ e := by rw [← map_mul, ← map_mul, hc]
    obtain ⟨γ, hγswap, hγe, hγf, hall⟩ :=
      exists_swap_thick (α := Fin 6) (Fintype.card_fin 6) ((hφ e).1 he) ((hφ f).1 hf) hστ hc'
    have hφγ : φ (φ.symm γ) = γ := MulEquiv.apply_symm_apply φ γ
    refine ⟨φ.symm γ, ?_, ?_, ?_, ?_⟩
    · exact (hφ (φ.symm γ)).2 (by rw [hφγ]; exact hγswap)
    · intro h
      exact hγe (by rw [← hφγ, h])
    · intro h
      exact hγf (by rw [← hφγ, h])
    · intro d hd hde hdf
      refine φ.injective ?_
      rw [map_mul, map_mul, hφγ]
      exact hall (φ d) ((hφ d).1 hd) (by rw [← map_mul, ← map_mul, hde])
        (by rw [← map_mul, ← map_mul, hdf])

theorem transvectionHyp_of_perm_six {G : Type} [Group G] {D : Set G}
    (hP : CFSG.Blueprint.Fischer.Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    (φ : G ≃* Equiv.Perm (Fin 6)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) :
    CFSG.Timmesfeld.Transvection.TransvectionHyp G
      {A | ∃ d ∈ D, A = Subgroup.zpowers d} :=
  CFSG.OddTranspositions.transvectionHyp_of_qHyp (qHyp_perm_six hP hZ hS hna φ hφ)

end CFSG.OddTranspositions
