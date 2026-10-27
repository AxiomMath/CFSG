module

public import CFSG.Walter.Ree.Thompson3.FE
public import CFSG.Walter.Ree.Thompson3.ThompsonAut
public import CFSG.Walter.Ree.Thompson2.Alg.Defs

public section

namespace CFSG.Walter.Ree.T2.RType

variable {k : Type} [Field k] [CharP k 3] [Fintype k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem exists_isS :
    ∃ S : k → k × k × k, IsS R S := by
  have h : ∀ x : k, ∃ v : k × k × k, ∃ ν : ThompsonN k σ,
      R.K * R.ι (pp σ 0 x 1) * R.K = R.ι ν * R.K * R.ι (ppv σ v) := fun x =>
    R.exists_pres' fun hm => by
      have := congrArg ThompsonN.γ
        (R.eq_one_of_K_mul_mem (show pp σ 0 x 1 ∈ ThompsonN.P σ from rfl) hm)
      simp [pp] at this
  choose S hS using h
  exact ⟨S, hS⟩

include R in
theorem sigmaTwo_eq_one
    {x : k} (hx : σ x * x ^ 2 = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have := R.sigmaTwo_injective (t := Units.mk0 x hx0) (by simpa using hx)
  simpa using congrArg Units.val this

variable {R} {S : k → k × k × k} (hS : IsS R S)
include hS

theorem fe1C
    {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) : Alg.FE1C a S :=
  fun _ hx => R.fe1_coords hS ha haσ hx

theorem fe2C : Alg.FE2C σ d S := by
  obtain ⟨a, ha, haσ⟩ := R.exists_a'
  exact fun _ hx => R.fe2_coords hS ha haσ hx

theorem gf3C : Alg.GF3C d S := by
  obtain ⟨a, ha, haσ⟩ := R.exists_a'
  exact ⟨R.s_neg_one hS, R.s_zero hS ha haσ, R.s_one hS ha haσ⟩

theorem t81C1 :
    Alg.T81C1 σ S := fun _ _ _ hz hy hE => (R.components_thm81 hS hz hy hE).1

theorem t81C2 :
    ∀ z y u : k, z ≠ 0 → y ≠ 0 → (z, y, u) ∈ hopkinsE σ →
      (S u).2.1 * (z * σ z) = (S (-u)).2.1 * (y * σ y) + (S (-u)).1 * y - σ ((S (-u)).1 * y) :=
  fun _ _ _ hz hy hE => (R.components_thm81 hS hz hy hE).2.1

theorem t81C3 :
    Alg.T81C3 σ d S := fun _ _ _ hz hy hE => (R.components_thm81 hS hz hy hE).2.2

end CFSG.Walter.Ree.T2.RType
