module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.ASSimple

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.MS93
open scoped Pointwise

namespace C45

variable {G : Type} [Group G]

theorem not_le_of_isSum {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {α : ↥A →* ↥Γ} {d : Bool} {k : ℕ} (hk : 0 < k)
    (h : IsSumOfNaturalModulesVia A V Z α d k) : ¬ V ≤ Z := by
  obtain ⟨-, -, β, hβ, hker, -⟩ := h
  intro hVZ
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd fun _ _ => (1 : F))
  have hv1 : v ∈ β.ker := by
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr (hVZ v.2)
  rw [MonoidHom.mem_ker, hv] at hv1
  have := congrArg (fun m : Multiplicative (Fin k → ι → F) => Multiplicative.toAdd m ⟨0, hk⟩ i) hv1
  simp only [toAdd_ofAdd, toAdd_one, Pi.zero_apply] at this
  exact one_ne_zero this

theorem comm_of_isSum_bot {A V : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ}
    {d : Bool} {k : ℕ} (h : IsSumOfNaturalModulesVia A V ⊥ α d k) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  obtain ⟨-, -, β, -, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  have := hinj (a₁ := ⟨x, hx⟩ * ⟨y, hy⟩) (a₂ := ⟨y, hy⟩ * ⟨x, hx⟩)
    (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val this

theorem eq_zero_of_fixed {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)}
    (hΓ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F,
      (g : Matrix (Fin 3) (Fin 3) F).det = 1 → g ∈ Γ) {v : Fin 3 → F}
    (h : ∀ g ∈ Γ, (g : Matrix (Fin 3) (Fin 3) F).mulVec v = v) : v = 0 := by
  have key : ∀ i j : Fin 3, i ≠ j → v j = 0 := by
    intro i j hij
    set t : Matrix (Fin 3) (Fin 3) F := Matrix.transvection i j 1 with ht
    have hdet : t.det = 1 := Matrix.det_transvection_of_ne i j hij 1
    set g := Matrix.GeneralLinearGroup.mkOfDetNeZero t (by rw [hdet]; exact one_ne_zero) with hg
    have hgt : (g : Matrix (Fin 3) (Fin 3) F) = t := rfl
    have hfix := h g (hΓ g (by rw [hgt, hdet]))
    rw [hgt, ht, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec] at hfix
    have hi := congrFun hfix i
    simpa using hi
  funext j
  fin_cases j
  · exact key 1 0 (by decide)
  · exact key 0 1 (by decide)
  · exact key 0 2 (by decide)

theorem eq_one_of_mem_centralizer {A V : Subgroup G} {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)}
    (hΓ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F,
      (g : Matrix (Fin 3) (Fin 3) F).det = 1 → g ∈ Γ) {α : ↥A →* ↥Γ}
    (hα : Function.Surjective α) (h : IsSumOfNaturalModulesVia A V ⊥ α false 1) {z : G}
    (hz : z ∈ V) (hzA : z ∈ Subgroup.centralizer (A : Set G)) : z = 1 := by
  obtain ⟨-, -, β, -, hker, hact⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  have hfix : ∀ g ∈ Γ, (g : Matrix (Fin 3) (Fin 3) F).mulVec
      (Multiplicative.toAdd (β ⟨z, hz⟩) 0) = Multiplicative.toAdd (β ⟨z, hz⟩) 0 := by
    intro g hgΓ
    obtain ⟨a, ha⟩ := hα ⟨g, hgΓ⟩
    have hza : (z : G) = (a : G) * z * (a : G)⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp hzA a a.2, mul_inv_cancel_right]
    have := hact a ⟨z, hz⟩ ⟨z, hz⟩ hza 0
    rw [ha] at this
    exact this.symm
  have h0 := eq_zero_of_fixed hΓ hfix
  have hβ1 : β ⟨z, hz⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    exact h0
  have := hinj (hβ1.trans (map_one β).symm)
  exact congrArg Subtype.val this

theorem card_of_isE2 {X : Type} [Group X] {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

end C45

end CFSG.Quasithin.H13.A5
