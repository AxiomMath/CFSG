module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.S15223

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjAction (X : Subgroup G) : MulAction X G :=
  MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp X.subtype)

theorem exists_fixed_mul_of_odd [Finite G] {X A U : Subgroup G} {z : G} (hz2 : z ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hzA : ∀ a ∈ A, a * z = z * a)
    (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hUz : ∀ u ∈ U, u * z = z * u) (hodd : ¬ 2 ∣ (U.subgroupOf X).index)
    (hc : ∀ x ∈ X, z⁻¹ * (x * z * x⁻¹) ∈ A) :
    ∃ b ∈ A, ∀ x ∈ X, x * (z * b) * x⁻¹ = z * b := by
  classical
  let _ : MulAction X G := conjAction X
  have hsmul : ∀ (x : X) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := fun x g => rfl
  set k : Set G := (A : Set G) ∪ {z} with hk
  have hkc : k.Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hAc x hx y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hzA x hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hzA y hy).symm
    · rw [Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  have hcomm : IsMulCommutative (Subgroup.closure k) := Subgroup.isMulCommutative_closure hkc
  set E : Subgroup G := Subgroup.closure k with hE
  have hAE : ∀ a ∈ A, a ∈ E := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hzE : z ∈ E := Subgroup.subset_closure (Or.inr rfl)
  have hxE : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    have hle : E ≤ E.comap (MulAut.conj x).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with hy | hy
      · exact hAE _ ((Subgroup.mem_normalizer_iff.mp (hXA hx) y).mp hy)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        have : x * y * x⁻¹ = y * (y⁻¹ * (x * y * x⁻¹)) := by group
        show x * y * x⁻¹ ∈ E
        rw [this]
        exact mul_mem hzE (hAE _ (hc x hx))
    exact hle he
  have hmem : ∀ σ : MulAction.orbit X z, z⁻¹ * (σ : G) ∈ A := by
    rintro ⟨σ, hσ⟩
    obtain ⟨x, rfl⟩ := MulAction.mem_orbit_iff.mp hσ
    exact hc x x.2
  have hσE : ∀ σ : MulAction.orbit X z, (σ : G) ∈ E := by
    intro σ
    have : (σ : G) = z * (z⁻¹ * (σ : G)) := by group
    rw [this]
    exact mul_mem hzE (hAE _ (hmem σ))
  have : Fintype (MulAction.orbit X z) := Fintype.ofFinite _
  have hodd' : ¬ 2 ∣ Fintype.card (MulAction.orbit X z) := by
    have h1 : (MulAction.stabilizer X z).index = (MulAction.orbit X z).ncard :=
      MulAction.index_stabilizer X z
    have h2 : U.subgroupOf X ≤ MulAction.stabilizer X z := by
      intro u hu
      rw [MulAction.mem_stabilizer_iff, hsmul]
      have hu' : (u : G) ∈ U := hu
      have := hUz _ hu'
      calc (u : G) * z * (u : G)⁻¹ = (u * z) * (u : G)⁻¹ := by group
        _ = (z * u) * (u : G)⁻¹ := by rw [this]
        _ = z := by group
    have h3 : (MulAction.stabilizer X z).index ∣ (U.subgroupOf X).index :=
      Subgroup.index_dvd_of_le h2
    have h4 : Fintype.card (MulAction.orbit X z) = (MulAction.orbit X z).ncard := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    rw [h4, ← h1]
    exact fun h => hodd (h.trans h3)
  let f : MulAction.orbit X z → E := fun σ => ⟨(σ : G), hσE σ⟩
  let ζ : E := ∏ σ, f σ
  have hfix : ∀ x : X, (x : G) * (ζ : G) * (x : G)⁻¹ = (ζ : G) := by
    intro x
    let ψ : E →* E :=
      { toFun := fun e => ⟨(x : G) * (e : G) * (x : G)⁻¹, hxE x x.2 e e.2⟩
        map_one' := by ext; simp
        map_mul' := by
          intro a b
          ext
          simp only [Subgroup.coe_mul]
          group }
    have h2 : ψ ζ = ζ := by
      calc ψ ζ = ∏ σ, ψ (f σ) := map_prod ψ _ _
        _ = ∏ σ, f (x • σ) := by
          refine Finset.prod_congr rfl fun σ _ => ?_
          ext
          simp [ψ, f]
          rfl
        _ = ∏ σ, f σ := Equiv.prod_comp (MulAction.toPerm x) f
    exact congrArg Subtype.val h2
  let zE : E := ⟨z, hzE⟩
  let g : MulAction.orbit X z → E := fun σ => ⟨z⁻¹ * (σ : G), hAE _ (hmem σ)⟩
  let bE : E := ∏ σ, g σ
  have hfg : ∀ σ, f σ = zE * g σ := by
    intro σ
    ext
    simp [f, zE, g]
  have hζ : ζ = zE ^ Fintype.card (MulAction.orbit X z) * bE := by
    show ∏ σ, f σ = _
    simp_rw [hfg]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hzE2 : zE ^ 2 = 1 := by
    ext
    simpa [zE] using hz2
  have hzodd : zE ^ Fintype.card (MulAction.orbit X z) = zE := by
    obtain ⟨m, hm⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd')
    rw [hm, pow_succ, pow_mul, hzE2, one_pow, one_mul]
  have hbA : (bE : G) ∈ A := by
    have : bE ∈ A.subgroupOf E :=
      Subgroup.prod_mem (A.subgroupOf E) fun σ _ => by
        rw [Subgroup.mem_subgroupOf]
        exact hmem σ
    exact this
  refine ⟨(bE : G), hbA, fun x hx => ?_⟩
  have h1 := hfix ⟨x, hx⟩
  rw [hζ, hzodd] at h1
  simpa using h1

end CFSG.Quasithin.S15223
