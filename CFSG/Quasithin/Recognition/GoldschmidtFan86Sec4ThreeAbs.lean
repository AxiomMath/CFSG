module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocTwoLocal
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

section Norm

variable {X Y : Type*} [Group X] [Group Y]

theorem normalizer_map_mulEquiv (e : X ≃* Y) (Q : Subgroup X) :
    (Subgroup.normalizer (Q : Set X)).map (e : X →* Y) =
      Subgroup.normalizer ((Q.map (e : X →* Y) : Subgroup Y) : Set Y) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  constructor
  · rintro ⟨x', hx', hx'e⟩
    have : x' = x := e.injective hx'e
    subst this
    have hx'' := Subgroup.mem_normalizer_iff.1 hx'
    refine Subgroup.mem_normalizer_iff.2 fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    constructor
    · rintro ⟨q, hq, hqe⟩
      have : q = w := e.injective hqe
      subst this
      exact ⟨x' * q * x'⁻¹, (hx'' q).1 hq, by simp⟩
    · rintro ⟨q, hq, hqe⟩
      have h1 : q = x' * w * x'⁻¹ := e.injective (by simpa using hqe)
      subst h1
      exact ⟨w, (hx'' w).2 hq, rfl⟩
  · intro h
    have h' := Subgroup.mem_normalizer_iff.1 h
    refine ⟨x, Subgroup.mem_normalizer_iff.2 fun w => ?_, rfl⟩
    constructor
    · intro hw
      obtain ⟨q, hq, hqe⟩ := (h' (e w)).1 ⟨w, hw, rfl⟩
      have : q = x * w * x⁻¹ := e.injective (by simpa using hqe)
      subst this
      exact hq
    · intro hw
      obtain ⟨q, hq, hqe⟩ := (h' (e w)).2 ⟨_, hw, by simp⟩
      have : q = w := e.injective hqe
      subst this
      exact hq

end Norm

theorem exists_mulEquiv_perm_prod {X : Type} [Group X] {n : ℕ} (hn : n = 3 ∨ n = 4)
    {C : Type} [Group C] [Finite C] (hC : IsPGroup 2 C) (e : X ≃* Equiv.Perm (Fin n) × C)
    {Q₀ : Subgroup X} (hQ0 : Q₀ ≠ ⊥) (hQ2 : IsPGroup 2 Q₀)
    (h3 : 3 ∣ Nat.card ↥(Subgroup.normalizer (Q₀ : Set X))) :
    ∃ n' : ℕ, (n' = 3 ∨ n' = 4) ∧ ∃ (C' : Type) (_ : Group C') (_ : Finite C'), IsPGroup 2 C' ∧
      Nonempty (↥(Subgroup.normalizer (Q₀ : Set X)) ≃* Equiv.Perm (Fin n') × C') := by
  have hM : IsTwoLocal
      ((Subgroup.normalizer (Q₀ : Set X)).map (e : X →* Equiv.Perm (Fin n) × C)) :=
    ⟨Q₀.map (e : X →* Equiv.Perm (Fin n) × C),
      fun h => hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q₀ e.injective).1 h),
      hQ2.map _, normalizer_map_mulEquiv e Q₀⟩
  let eM := e.subgroupMap (Subgroup.normalizer (Q₀ : Set X))
  have h3' : 3 ∣ Nat.card ↥((Subgroup.normalizer (Q₀ : Set X)).map
      (e : X →* Equiv.Perm (Fin n) × C)) := by
    rw [← Nat.card_congr eM.toEquiv]
    exact h3
  obtain ⟨C₀, hC₀⟩ := isTwoLocal_perm_prod hn hC hM h3'
  rcases hC₀ with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact ⟨3, Or.inl rfl, ↥C₀, inferInstance, inferInstance, hC.to_subgroup C₀, ⟨eM.trans f⟩⟩
  · exact ⟨4, Or.inr rfl, ↥C₀, inferInstance, inferInstance, hC.to_subgroup C₀, ⟨eM.trans f⟩⟩

theorem nonempty_oTwoQuot_equiv {X : Type*} [Group X] [Finite X] {α : Type*}
    (φ : X →* Equiv.Perm α) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hcore : pCore 2 X ≤ φ.ker) : Nonempty (oTwoQuot X ≃* Equiv.Perm α) := by
  have h : pCore 2 X = φ.ker := le_antisymm hcore (le_pCore 2 (MonoidHom.normal_ker φ) hker)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end CFSG.Quasithin.Fan86
