module

public import CFSG.Timmesfeld.Transvection.QTwoThin
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq

public section

namespace CFSG.OddTranspositions

open CFSG.Blueprint.Fischer CFSG.Timmesfeld.Transvection.QTwo

theorem eq_of_isSwap_commute_three {σ τ : Equiv.Perm (Fin 3)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hc : σ * τ = τ * σ) : σ = τ := by
  by_contra hne
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  obtain ⟨hac, had, hbc, hbd⟩ :=
    disjoint_of_swap_commute hab hcd (by simpa using hne) hc
  have hinj : Function.Injective ![a, b, c, d] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem noSqE1_of_pair_perm_three {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (φ : G ≃* Equiv.Perm (Fin 3)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  intro d hd
  have hcen : CFSG.RankThree.GF2n.Tim79a.cenGen D d = Subgroup.zpowers d := by
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen]
    have hsingle : D ∩ (Subgroup.centralizer ({d} : Set G) : Set G) = {d} := by
      ext f
      constructor
      · rintro ⟨hf, hfd⟩
        have hcomm : Commute f d := Subgroup.mem_centralizer_singleton_iff.mp hfd
        have hswap : φ f = φ d := by
          refine eq_of_isSwap_commute_three ((hφ f).1 hf) ((hφ d).1 hd) ?_
          rw [← map_mul, ← map_mul, hcomm.eq]
        exact Set.mem_singleton_iff.mpr (φ.injective hswap)
      · intro hf
        rw [Set.mem_singleton_iff] at hf
        rw [hf]
        exact ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl d)⟩
    rw [hsingle]
    exact (Subgroup.zpowers_eq_closure d).symm
  rw [hcen]
  exact (Subgroup.map_subtype_le (CFSG.pCore 2 (Subgroup.zpowers d))).trans le_sup_left

end CFSG.OddTranspositions
