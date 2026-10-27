module

public import CFSG.Quasithin.Background.Harris.G2.Numerics
public import CFSG.Quasithin.Background.Harris.G2.Setup
public import CFSG.Quasithin.Background.SmithB42G2FNat

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
  CFSG.Quasithin.B42G2F
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing finite_endRing)

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

omit [CharP K 2] [Fintype K] in
theorem six_le_card_idx (l : G2L) (hl : l ≠ .one) : 6 ≤ Fintype.card l.idx := by
  rw [card_idx]
  cases l
  · exact absurd rfl hl
  all_goals norm_num

omit [CharP K 2] [Fintype K] in
theorem fourteen_le_card_idx (l : G2L) (h1 : l ≠ .one) (h2 : l ≠ .nat) :
    14 ≤ Fintype.card l.idx := by
  rw [card_idx]
  cases l
  · exact absurd rfl h1
  · exact absurd rfl h2
  · norm_num
  · norm_num

omit [CharP K 2] [Fintype K] in
theorem six_pow_le_prod {f : ℕ} (lab : Fin f → G2L) :
    6 ^ (Finset.univ.filter fun j => lab j ≠ .one).card ≤ ∏ j, Fintype.card (lab j).idx := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => lab j ≠ .one)]
  have h1 : ∏ j ∈ Finset.univ.filter (fun j => ¬ lab j ≠ .one), Fintype.card (lab j).idx = 1 :=
    Finset.prod_eq_one fun j hj => by
      have hj' : lab j = .one := by simpa using hj
      rw [hj', card_idx]
  rw [h1, mul_one]
  calc 6 ^ (Finset.univ.filter fun j => lab j ≠ .one).card
      = ∏ _j ∈ Finset.univ.filter (fun j => lab j ≠ .one), 6 := by simp
    _ ≤ _ := Finset.prod_le_prod fun j hj => six_le_card_idx _ (by simpa using hj)


theorem exists_natural_of_bound {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 2 ≤ f)
    (ρ : Representation (ZMod 2) ↥(cayleyGroup K) M) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (hb : Module.finrank (ZMod 2) M ≤ 6 * f + 2) :
    Nat.card (EndRing ρ) = 2 ^ f ∧ Module.finrank (EndRing ρ) M = 6 ∧
      ∃ φ : M ≃+ (Ix3 → K), ∀ g w, φ (ρ g w) = g2Act g (φ w) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := g2_descent hK (by omega) hnt
  have : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, lab, ⟨Φ⟩, hshift, hne, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) M)
  set S := Finset.univ.filter fun j => lab j ≠ .one with hS
  have hfS : f ≤ S.card * d := le_card_support_mul lab hd1 hshift hne
  have hdimV : Module.finrank (ZMod 2) M = d * ∏ j, Fintype.card (lab j).idx := by
    rw [finrank_eq_mul_of_card hDcard, hdim]
  rw [hdimV] at hb
  have hSpos : 1 ≤ S.card := by
    obtain ⟨j, hj⟩ := hne
    exact Finset.card_pos.mpr ⟨j, by simpa [hS] using hj⟩
  have hS1 : S.card = 1 :=
    one_of_numerics hd1 hSpos hfS (six_pow_le_prod lab) hb
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hS1
  have hother : ∀ j ≠ j₀, lab j = .one := fun j hj => by
    by_contra h
    have : j ∈ S := by simpa [hS] using h
    rw [hj₀] at this
    exact hj (Finset.mem_singleton.mp this)
  have hj₀S : lab j₀ ≠ .one := by
    have : j₀ ∈ S := by rw [hj₀]; exact Finset.mem_singleton_self j₀
    simpa [hS] using this
  have hfd : f ∣ d := dvd_of_single lab j₀ hshift hj₀S hother
  have hdf : f ≤ d := Nat.le_of_dvd (by omega) hfd
  have hprod := prod_card_single lab j₀ hother
  rw [hprod] at hb hdim
  have hnat : lab j₀ = .nat := by
    by_contra hn
    have h14 := fourteen_le_card_idx _ hj₀S hn
    nlinarith
  have hc6 : Fintype.card (lab j₀).idx = 6 := by rw [card_idx, hnat]
  have h6 : Module.finrank (EndRing ρ) M = 6 := by rw [hdim, hc6]
  have hdf' : d = f := by
    rw [hc6] at hb
    omega
  subst hdf'
  exact ⟨hDcard, h6, exists_natural_of_six hK hDcard hfd h6⟩

end CFSG.Quasithin.G11.Harris.G2
