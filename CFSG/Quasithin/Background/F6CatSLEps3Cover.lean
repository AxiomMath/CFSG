module

public import CFSG.Quasithin.Background.F6CatRecogInputs2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Ch1 CFSG.SectionRank.OddCover

theorem bijective_of_scalar_cover_of_map_ne_bot {H L : Type} [Group H] [Finite H] [Group L]
    {D : Subgroup H} {φ : H →* L} (hφ : Function.Surjective φ) (hker : φ.ker ≤ D)
    (hD : Nat.card D ∣ 3) (hmap : D.map φ ≠ ⊥) : Function.Bijective φ := by
  refine ⟨(MonoidHom.ker_eq_bot_iff φ).1 ?_, hφ⟩
  by_contra hne
  refine hmap ?_
  have h1 : Nat.card φ.ker ∣ 3 := (Subgroup.card_dvd_of_le hker).trans hD
  have h2 : Nat.card φ.ker ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have h3 : Nat.card φ.ker = 3 := ((Nat.dvd_prime Nat.prime_three).1 h1).resolve_left h2
  have hD3 : Nat.card D ≤ 3 := Nat.le_of_dvd (by norm_num) hD
  have hkD : φ.ker = D := Subgroup.eq_of_le_of_card_ge hker (by omega)
  exact (Subgroup.map_eq_bot_iff D).2 hkD.ge

theorem slEps3CoverFact_holds : SLEps3CoverFact := by
  intro L _ _ hL hZ3 hZ p hp hp2
  have hperf : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  refine ⟨?_, ?_⟩
  · rintro ⟨-, F, _, _, hF, ⟨e⟩⟩
    have hF' : Nat.card F = p := by rw [hF, pow_one]
    obtain ⟨φ, hφ, hker, hmap⟩ := exists_cover_map_of_odd_splitting hodd e
      fun E _ _ π hπ hC hodd' => by
        obtain ⟨⟨s, hs, -⟩, -⟩ := prime_classical_three_central_odd_extension_splitting hp hp2
          (Or.inl ⟨rfl, hF', rfl⟩) π hπ hC hodd'
        exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    have hbij := bijective_of_scalar_cover_of_map_ne_bot hφ hker
      (card_scalars_dvd_three (p := p) (f := 1) (Or.inl ⟨hF, rfl⟩)) (by rw [hmap]; exact hZ)
    exact ⟨F, inferInstance, inferInstance, hF', ⟨(MulEquiv.ofBijective φ hbij).symm⟩⟩
  · rintro ⟨-, F, _, _, hF, ⟨e⟩⟩
    have := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hF]
      ring)
    have hF' : Nat.card F = p ^ 2 := by rw [hF, pow_one]
    have hsplit : ∀ q : ℕ, q = p → ∀ (E : Type) [Group E] [Finite E]
        (π : E →* StatedSU 3 q F), Function.Surjective π → π.ker ≤ Subgroup.center E →
        Odd (Nat.card π.ker) → ∃ s : StatedSU 3 q F →* E, ∀ g, π (s g) = g := by
      rintro q rfl E _ _ π hπ hC hodd'
      obtain ⟨⟨s, hs, -⟩, -⟩ := prime_classical_three_central_odd_extension_splitting hp hp2
        (Or.inr ⟨rfl, hF', rfl⟩) π hπ hC hodd'
      exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    obtain ⟨φ, hφ, hker, hmap⟩ := exists_cover_map_of_odd_splitting hodd e
      (hsplit (p ^ 1) (pow_one p))
    have hbij := bijective_of_scalar_cover_of_map_ne_bot hφ hker
      (card_scalars_dvd_three (p := p) (f := 1) (Or.inr ⟨hF, rfl⟩)) (by rw [hmap]; exact hZ)
    refine ⟨F, inferInstance, inferInstance, hF', ⟨?_⟩⟩
    rw [← pow_one p]
    exact (MulEquiv.ofBijective φ hbij).symm

end CFSG.Quasithin.F6
