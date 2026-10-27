module

public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem ordinary_E_split_torus_actual_central_cover_two_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Fintype K]
    (hp : p.Prime) (hp3 : 3 < p) (_hpq : p ∣ Fintype.card K - 1) (φ : Y →* adjointGroup τ K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {ζ : Kˣ}
    (hζo : orderOf ζ = p) :
    ∃ D : Subgroup (adjointGroup τ K), (∀ g, g ∈ D ↔ ∃ a : Fin τ.rank → ZMod p,
        (g : ModGL τ K) = (List.ofFn fun i => torusElt τ K i (ζ ^ (a i).val)).prod) ∧
      IsElemAbelian p D ∧ Nat.card D = p ^ τ.rank ∧
      (∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) ∧
      ∃ R : Subgroup G, R ≤ Y ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ ∃ A₀ : Subgroup G,
        A₀ ≤ Y ⊓ Subgroup.normalizer (R : Set G) ∧ IsElemAbelian p A₀ ∧
        Nat.card A₀ = p ^ τ.rank ∧ τ.rank ≤ localRank p G := by
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  have hcop : ∀ n : ℕ, n < p → 0 < n → Nat.Coprime n p := fun n hn hn0 =>
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      absurd (Nat.le_of_dvd hn0 h) (by omega))
  obtain ⟨hdet, i₀, j₀, hodd⟩ : IsUnit ((τ.cartan.det : ℤ) : ZMod p) ∧
      ∃ i₀ j₀ : Fin τ.rank, Odd (τ.cartan i₀ j₀) := by
    rcases hτ with rfl | rfl | rfl
    · refine ⟨?_, ⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩
      rw [det_cartan_E6, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num]
      exact isUnit_natCast_of_coprime (hcop 3 hp3 (by norm_num))
    · refine ⟨?_, ⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩
      rw [det_cartan_E7, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num]
      exact isUnit_natCast_of_coprime (hcop 2 (by omega) (by norm_num))
    · refine ⟨?_, ⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩
      rw [det_cartan_E8, Int.cast_one]
      exact isUnit_one
  obtain ⟨hDab, hcard, hF, R, hRY, hR1, hR2, A₀, hA, hAab, hAcard, hrank⟩ :=
    chevalley_split_torus_witness Y hp (by omega) hdet i₀ j₀ hodd φ hφ hker hζo hζ
  exact ⟨_, mem_range_chevTorus_iff ζ hζ, hDab, hcard, hF, R, hRY, hR1, hR2, A₀, hA, hAab,
    hAcard, hrank⟩

end CFSG.RankThree.CentralCover
