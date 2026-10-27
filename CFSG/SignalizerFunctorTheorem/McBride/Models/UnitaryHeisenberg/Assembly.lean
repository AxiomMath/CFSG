module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Arith
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Pair

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

section Proj

variable {p : ℕ}

noncomputable abbrev SU3 (hp : 1 ≤ p) : Subgroup (GL (Fin 3) (GaloisField 2 (2 * p))) :=
  gramSU (unitaryFieldData_galoisField hp) (antidiagGram (GaloisField 2 (2 * p)))

theorem mk_mem_psu3 (hp : 1 ≤ p) (g : SU3 hp) :
    ProjGenLinGroup.mk (g : GL (Fin 3) (GaloisField 2 (2 * p))) ∈ PSU3 2 p :=
  (SetLike.ext_iff.mp (psu3_eq_map_gramSU hp) _).mpr (Subgroup.mem_map_of_mem _ g.2)

noncomputable def projSU3 (hp : 1 ≤ p) : SU3 hp →* PSU3 2 p :=
  (ProjGenLinGroup.mk.comp (SU3 hp).subtype).codRestrict (PSU3 2 p) (mk_mem_psu3 hp)

theorem projSU3_surjective (hp : 1 ≤ p) : Function.Surjective (projSU3 hp) := by
  intro y
  have hy := (SetLike.ext_iff.mp (psu3_eq_map_gramSU hp)
    (y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p)))).mp y.2
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩

theorem projSU3_eq_one_iff (hp : 1 ≤ p) (g : SU3 hp) :
    projSU3 hp g = 1 ↔ (g : GL (Fin 3) (GaloisField 2 (2 * p))) ∈
      Subgroup.center (GL (Fin 3) (GaloisField 2 (2 * p))) := by
  rw [← ProjGenLinGroup.mk_eq_one]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Proj

section Sylow

variable {p : ℕ}

theorem exists_conj_of_card_nine (hp : p.Prime) (h5 : 5 ≤ p) (P P₀ : Subgroup (PSU3 2 p))
    (hP : Nat.card P = 9) (hP₀ : Nat.card P₀ = 9) :
    ∃ y : PSU3 2 p, P = P₀.map (MulAut.conj y).toMonoidHom := by
  obtain ⟨T, hT, hT3⟩ := exists_card_psu3 hp h5
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT0 : T ≠ 0 := by
    rintro rfl
    simp at hT
    exact absurd hT (Nat.card_pos.ne')
  have hfac : (Nat.card (PSU3 2 p)).factorization 3 = 2 := by
    rw [hT, show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.factorization_mul (by positivity) hT0,
      Nat.Prime.factorization_pow Nat.prime_three]
    simp [Nat.factorization_eq_zero_of_not_dvd hT3]
  have h9 : 3 ^ (Nat.card (PSU3 2 p)).factorization 3 = 9 := by rw [hfac]; norm_num
  let S₁ : Sylow 3 (PSU3 2 p) := Sylow.ofCard P (by rw [h9]; exact hP)
  let S₀ : Sylow 3 (PSU3 2 p) := Sylow.ofCard P₀ (by rw [h9]; exact hP₀)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (PSU3 2 p) S₀ S₁
  refine ⟨y, ?_⟩
  have := congrArg (fun S : Sylow 3 (PSU3 2 p) => (S : Subgroup (PSU3 2 p))) hy
  simp only [Sylow.coe_subgroup_smul] at this
  rw [show (S₁ : Subgroup (PSU3 2 p)) = P from rfl, show (S₀ : Subgroup (PSU3 2 p)) = P₀ from rfl,
    Subgroup.pointwise_smul_def] at this
  exact this.symm

theorem pow_eq_one_of_commute_conj {G : Type*} [Group G] {a : G} {n : ℕ}
    (h : ∀ x : G, Commute x a → x ^ n = 1) (g : G) :
    ∀ x : G, Commute x (g * a * g⁻¹) → x ^ n = 1 := by
  intro x hx
  have h1 := h _ (commute_inv_conj hx)
  have h2 : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
    simpa using conj_pow (a := g⁻¹) (b := x) (i := n)
  rw [h2] at h1
  calc x ^ n = g * (g⁻¹ * x ^ n * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_pair_of_card_nine_pow (hp : p.Prime) (h5 : 5 ≤ p) (P : Subgroup (PSU3 2 p))
    (hP : Nat.card P = 9) :
    ∃ a b ζ : SU3 hp.one_le, IsHeisPair a b ζ ∧
      (∀ g : SU3 hp.one_le, projSU3 hp.one_le g = 1 ↔ g ∈ Subgroup.zpowers ζ) ∧
      (∀ g : SU3 hp.one_le, Commute g a → Commute g b → g ∈ Subgroup.zpowers ζ) ∧
      (∀ x y : SU3 hp.one_le, Commute x a → Commute y b → Commute x y →
        x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ) ∧
      P = (Subgroup.closure {a, b}).map (projSU3 hp.one_le) ∧
      (∀ g : SU3 hp.one_le, Commute g a → g ^ (2 ^ p + 1) = 1) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨a₀, b₀, ζ, h₀, hcent, hCP₀, hMU₀, hpow₀⟩ :=
    exists_pair_SU3_pow (unitaryFieldData_galoisField hp.one_le) hodd
  have hker : ∀ g : SU3 hp.one_le, projSU3 hp.one_le g = 1 ↔ g ∈ Subgroup.zpowers ζ :=
    fun g => (projSU3_eq_one_iff hp.one_le g).trans (hcent g)
  have hP₀ := h₀.card_map_E (projSU3 hp.one_le) hker
  obtain ⟨y, hy⟩ := exists_conj_of_card_nine hp h5 P _ hP hP₀
  obtain ⟨g, rfl⟩ := projSU3_surjective hp.one_le y
  refine ⟨g * a₀ * g⁻¹, g * b₀ * g⁻¹, ζ, h₀.conj g, hker, h₀.commute_conj hCP₀ g,
    h₀.mu_conj hMU₀ g, ?_, pow_eq_one_of_commute_conj hpow₀ g⟩
  rw [← (h₀.conj g).E_eq_closure, h₀.E_conj g, Subgroup.map_map, hy, Subgroup.map_map]
  congr 1

theorem exists_pair_of_card_nine (hp : p.Prime) (h5 : 5 ≤ p) (P : Subgroup (PSU3 2 p))
    (hP : Nat.card P = 9) :
    ∃ a b ζ : SU3 hp.one_le, IsHeisPair a b ζ ∧
      (∀ g : SU3 hp.one_le, projSU3 hp.one_le g = 1 ↔ g ∈ Subgroup.zpowers ζ) ∧
      (∀ g : SU3 hp.one_le, Commute g a → Commute g b → g ∈ Subgroup.zpowers ζ) ∧
      (∀ x y : SU3 hp.one_le, Commute x a → Commute y b → Commute x y →
        x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ) ∧
      P = (Subgroup.closure {a, b}).map (projSU3 hp.one_le) := by
  obtain ⟨a, b, ζ, hH, hker, hCP, hMU, hPeq, -⟩ := exists_pair_of_card_nine_pow hp h5 P hP
  exact ⟨a, b, ζ, hH, hker, hCP, hMU, hPeq⟩

end Sylow

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
