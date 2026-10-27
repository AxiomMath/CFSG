module

public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher.S43

namespace Odd

namespace F

variable {G : Type} [Group G]

theorem pow_comm_mem {E : Subgroup G} {h v : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    (hv : h * v * h⁻¹ * v⁻¹ ∈ E) (n : ℕ) : h ^ n * v * (h ^ n)⁻¹ * v⁻¹ ∈ E := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : h ^ (n + 1) * v * (h ^ (n + 1))⁻¹ * v⁻¹ =
        h * (h ^ n * v * (h ^ n)⁻¹ * v⁻¹) * h⁻¹ * (h * v * h⁻¹ * v⁻¹) := by
      rw [pow_succ']; group
    rw [e]
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hh _).mp ih) hv

theorem comm_mem_of_odd {E₀ E₁ : Subgroup G} {g v : G} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hg : g ∈ Subgroup.normalizer (E₀ : Set G))
    (h₁ : ∀ c ∈ E₁, g * c * g⁻¹ * c⁻¹ ∈ E₀) (hsq : ∀ c ∈ E₁, c * c ∈ E₀)
    (hv : g * v * g⁻¹ * v⁻¹ ∈ E₁) : g * v * g⁻¹ * v⁻¹ ∈ E₀ := by
  have h2 : g ^ 2 * v * (g ^ 2)⁻¹ * v⁻¹ ∈ E₀ := by
    have e : g ^ 2 * v * (g ^ 2)⁻¹ * v⁻¹ =
        (g * (g * v * g⁻¹ * v⁻¹) * g⁻¹ * (g * v * g⁻¹ * v⁻¹)⁻¹) *
          ((g * v * g⁻¹ * v⁻¹) * (g * v * g⁻¹ * v⁻¹)) := by
      simp only [pow_two]; group
    rw [e]
    exact E₀.mul_mem (h₁ _ hv) (hsq _ hv)
  obtain ⟨k, rfl⟩ := hm
  have hgg : (g ^ 2) ^ (k + 1) = g := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hgm, one_mul]
  have := pow_comm_mem ((Subgroup.normalizer (E₀ : Set G)).pow_mem hg 2) h2 (k + 1)
  rwa [hgg] at this

theorem comm_mem_of_odd_chain {E : ℕ → Subgroup G} {g : G} {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg : g ∈ Subgroup.normalizer (E 0 : Set G)) {s : ℕ}
    (hstep : ∀ i, i < s → ∀ v ∈ E (i + 1), g * v * g⁻¹ * v⁻¹ ∈ E i)
    (hsq : ∀ i, i ≤ s → ∀ c ∈ E i, c * c ∈ E 0) :
    ∀ v ∈ E s, g * v * g⁻¹ * v⁻¹ ∈ E 0 := by
  suffices h : ∀ j, j ≤ s → ∀ v ∈ E j, g * v * g⁻¹ * v⁻¹ ∈ E 0 from h s le_rfl
  intro j
  induction j with
  | zero =>
    intro _ v hv
    exact (E 0).mul_mem ((Subgroup.mem_normalizer_iff.mp hg v).mp hv) ((E 0).inv_mem hv)
  | succ j ih =>
    intro hj v hv
    exact comm_mem_of_odd hm hgm hg (ih (by omega)) (hsq j (by omega)) (hstep j (by omega) v hv)

theorem comm_mem_of_oTwoRes {X E : Subgroup G} {v : G}
    (hXE : X ≤ Subgroup.normalizer (E : Set G))
    (h : ∀ l ∈ X, ∀ m : ℕ, Odd m → l ^ m = 1 → l * v * l⁻¹ * v⁻¹ ∈ E) :
    ∀ l ∈ oTwoRes X, l * v * l⁻¹ * v⁻¹ ∈ E := by
  have hle : oTwoRes X ≤ fixer E v := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro l ⟨hlX, m, hm, hlm⟩
    exact mem_fixer_iff.mpr ⟨hXE hlX, h l hlX m hm hlm⟩
  exact fun l hl => (mem_fixer_iff.mp (hle hl)).2

theorem commutator_le_left_of_le_normalizer {V Q : Subgroup G}
    (hQ : Q ≤ Subgroup.normalizer (V : Set G)) : ⁅V, Q⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv q hq
  have h1 : q * v⁻¹ * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hQ hq) _).mp (V.inv_mem hv)
  have e : ⁅v, q⁆ = v * (q * v⁻¹ * q⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hv h1

end F

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
