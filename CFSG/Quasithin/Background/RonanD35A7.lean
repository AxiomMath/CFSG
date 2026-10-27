module

public import CFSG.Quasithin.Background.RonanD35
public import CFSG.Quasithin.EmptyFaithfulMultiple.FixFactsA7
public import CFSG.Quasithin.Background.G64SymSec

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin Matrix
open CFSG.Quasithin.EmptyFaithfulMultiple.FFL (a7e₁ a7e₂ a7t a7_relations altLift7_injective'
  sq_eq_one_of_mem_closure_pair exists_fixed_pair inW_of_fixed_eq_zero)
open CFSG.Quasithin.SteinbergCB.I16 (Vec4 Mat4 indep_W fixed_eq_zero_of_fourGroup)

@[expose] def a7d35FixSub (E₁ E₂ : Mat4) : Subgroup (Multiplicative Vec4) where
  carrier := {x | E₁ *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x ∧
    E₂ *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    simp only [Set.mem_setOf_eq, toAdd_mul, mulVec_add, hx₁, hx₂, hy₁, hy₂, and_self]
  inv_mem' := by
    rintro x ⟨hx₁, hx₂⟩
    simp only [Set.mem_setOf_eq, toAdd_inv, mulVec_neg, hx₁, hx₂, and_self]

theorem a7d35_mem_fixSub {E₁ E₂ : Mat4} {x : Multiplicative Vec4} :
    x ∈ a7d35FixSub E₁ E₂ ↔ E₁ *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x ∧
      E₂ *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x := Iff.rfl

theorem a7d35_four_le_card_fixSub {X E₁ E₂ : Mat4} (hX3 : X ^ 3 = 1)
    (hfix : ∀ v : Vec4, X *ᵥ v = v → v = 0) (hXE₁ : X * E₁ = E₁ * X) (hXE₂ : X * E₂ = E₂ * X)
    {v₀ : Vec4} (hv₀ : v₀ ≠ 0) (h₁ : E₁ *ᵥ v₀ = v₀) (h₂ : E₂ *ᵥ v₀ = v₀) :
    4 ≤ Nat.card ↥(a7d35FixSub E₁ E₂) := by
  have hE : ∀ {E : Mat4}, X * E = E * X → E *ᵥ v₀ = v₀ → ∀ a b : ZMod 2,
      E *ᵥ (a • v₀ + b • (X *ᵥ v₀)) = a • v₀ + b • (X *ᵥ v₀) := by
    intro E hXE hv a b
    have hXv : E *ᵥ (X *ᵥ v₀) = X *ᵥ v₀ := by
      rw [mulVec_mulVec, ← hXE, ← mulVec_mulVec, hv]
    rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hXv]
  let f : ZMod 2 × ZMod 2 → ↥(a7d35FixSub E₁ E₂) := fun p =>
    ⟨Multiplicative.ofAdd (p.1 • v₀ + p.2 • (X *ᵥ v₀)),
      a7d35_mem_fixSub.mpr ⟨hE hXE₁ h₁ p.1 p.2, hE hXE₂ h₂ p.1 p.2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : a • v₀ + b • (X *ᵥ v₀) = a' • v₀ + b' • (X *ᵥ v₀) :=
      Multiplicative.ofAdd.injective (congrArg Subtype.val h)
    have h0 : (a - a') • v₀ + (b - b') • (X *ᵥ v₀) = 0 := by
      calc (a - a') • v₀ + (b - b') • (X *ᵥ v₀)
          = (a • v₀ + b • (X *ᵥ v₀)) - (a' • v₀ + b' • (X *ᵥ v₀)) := by module
        _ = 0 := by rw [h', sub_self]
    obtain ⟨ha, hb⟩ := indep_W hX3 (inW_of_fixed_eq_zero hX3 hfix v₀) hv₀ _ _ h0
    rw [sub_eq_zero.mp ha, sub_eq_zero.mp hb]
  have h4 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_zmod] at h4

theorem a7d35_four_le_card_fix (M : ↥(alternatingGroup (Fin 7)) →* GL (Fin 4) (ZMod 2))
    (hM : Function.Injective M) :
    4 ≤ Nat.card ↥(a7d35FixSub ((M a7e₁ : GL (Fin 4) (ZMod 2)) : Mat4)
      ((M a7e₂ : GL (Fin 4) (ZMod 2)) : Mat4)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := a7_relations
  set m : ↥(alternatingGroup (Fin 7)) → Mat4 := fun σ => ((M σ : GL (Fin 4) (ZMod 2)) : Mat4)
    with hm
  have hmul : ∀ σ τ, m (σ * τ) = m σ * m τ := fun σ τ => by
    simp only [hm, map_mul, Units.val_mul]
  have hone : m 1 = 1 := by simp only [hm, map_one, Units.val_one]
  have hpow3 : ∀ σ, m (σ ^ 3) = m σ ^ 3 := fun σ => by
    simp only [hm, map_pow, Units.val_pow_eq_pow_val]
  have hne : ∀ σ τ, σ ≠ τ → m σ ≠ m τ := fun σ τ hστ h => hστ (hM (Units.ext h))
  set X := m a7t with hX
  set E₁ := m a7e₁ with hE₁
  set E₂ := m a7e₂ with hE₂
  have hX3 : X ^ 3 = 1 := by rw [hX, ← hpow3, h7, hone]
  have hE₁₁ : E₁ * E₁ = 1 := by rw [hE₁, ← hmul, h1, hone]
  have hE₂₂ : E₂ * E₂ = 1 := by rw [hE₂, ← hmul, h2, hone]
  have hE₁₂ : E₁ * E₂ = E₂ * E₁ := by rw [hE₁, hE₂, ← hmul, ← hmul, h3]
  have hXE₁ : X * E₁ = E₁ * X := by rw [hX, hE₁, ← hmul, ← hmul, h9]
  have hXE₂ : X * E₂ = E₂ * X := by rw [hX, hE₂, ← hmul, ← hmul, h10]
  have hE₁1 : E₁ ≠ 1 := by rw [hE₁, ← hone]; exact hne _ _ h4
  have hX1 : X ≠ 1 := by rw [hX, ← hone]; exact hne _ _ h8
  have hfixX : ∀ v : Vec4, X *ᵥ v = v → v = 0 := fun v hv =>
    fixed_eq_zero_of_fourGroup hX3 hX1 hE₁₁ hE₂₂ hXE₁ hXE₂ hE₁₂ hE₁1
      (by rw [hE₂, ← hone]; exact hne _ _ h5) (by rw [hE₁, hE₂]; exact hne _ _ h6) hv
  obtain ⟨v₀, hv₀, hE₁v₀, hE₂v₀⟩ := exists_fixed_pair hE₁₁ hE₂₂ hE₁₂ hE₁1
  exact a7d35_four_le_card_fixSub hX3 hfixX hXE₁ hXE₂ hv₀ hE₁v₀ hE₂v₀

theorem a7d35_four_le_card_closure :
    4 ≤ Nat.card ↥(Subgroup.closure ({a7e₁, a7e₂} : Set ↥(alternatingGroup (Fin 7)))) := by
  set A₀ := Subgroup.closure ({a7e₁, a7e₂} : Set ↥(alternatingGroup (Fin 7)))
  have h₁ : a7e₁ ∈ A₀ := Subgroup.subset_closure (Set.mem_insert _ _)
  have h₂ : a7e₂ ∈ A₀ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hS : ((({1, a7e₁, a7e₂, a7e₁ * a7e₂} : Finset ↥(alternatingGroup (Fin 7)))) :
      Set ↥(alternatingGroup (Fin 7))) ⊆ A₀ := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact A₀.one_mem
    · exact h₁
    · exact h₂
    · exact A₀.mul_mem h₁ h₂
  have hcard : ({1, a7e₁, a7e₂, a7e₁ * a7e₂} : Finset ↥(alternatingGroup (Fin 7))).card = 4 := by
    decide +kernel
  calc 4 = ((({1, a7e₁, a7e₂, a7e₁ * a7e₂} : Finset ↥(alternatingGroup (Fin 7)))) :
        Set ↥(alternatingGroup (Fin 7))).ncard := by rw [Set.ncard_coe_finset, hcard]
    _ ≤ (A₀ : Set ↥(alternatingGroup (Fin 7))).ncard := Set.ncard_le_ncard hS (Set.toFinite _)
    _ = Nat.card ↥A₀ := (Nat.card_coe_set_eq _).symm

theorem isFFModule_of_a7Four {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {V : Subgroup W} (hLs : L ≤ stabSub V)
    {α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    {π : ↥(alternatingGroup (Fin 7)) →* ↥L}
    (hπ : (FFModel.a7Four α).RealizesVia L V ⊥ π) : IsFFModule (autSub L V) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := a7_relations
  obtain ⟨M, hM, hMe⟩ : ∃ M : ↥(alternatingGroup (Fin 7)) →* GL (Fin 4) (ZMod 2),
      Function.Injective M ∧ ∀ σ, M σ = α (altLift7 σ) :=
    ⟨α.toMonoidHom.comp altLift7, α.injective.comp altLift7_injective', fun _ => rfl⟩
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_ambMap (D := FFModel.a7Four α) rfl hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  set A₀ := Subgroup.closure ({a7e₁, a7e₂} : Set ↥(alternatingGroup (Fin 7)))
  have hA₀2 : ∀ a ∈ A₀, a * a = 1 := fun a ha => sq_eq_one_of_mem_closure_pair h1 h2 h3 ha
  have hinv : ∀ a ∈ A₀, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hA₀2 a ha)
  have hA₀c : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := fun a ha b hb => by
    rw [← hinv (a * b) (A₀.mul_mem ha hb), _root_.mul_inv_rev, hinv a ha, hinv b hb]
  have hA₀1 : A₀ ≠ ⊥ := by
    intro h
    have he₁ : a7e₁ ∈ A₀ := Subgroup.subset_closure (Set.mem_insert _ _)
    rw [h, Subgroup.mem_bot] at he₁
    exact h4 he₁
  set P := a7d35FixSub ((M a7e₁ : GL (Fin 4) (ZMod 2)) : Mat4)
    ((M a7e₂ : GL (Fin 4) (ZMod 2)) : Mat4)
  have hP4 : 4 ≤ Nat.card ↥P := a7d35_four_le_card_fix M hM
  have hcard : Nat.card (Multiplicative Vec4) = 16 := by
    show Nat.card (Fin 4 → ZMod 2) = 16
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hidx : P.index ≤ Nat.card ↥A₀ := by
    have h := Subgroup.card_mul_index P
    rw [hcard] at h
    have h' : 4 * P.index ≤ 16 := h ▸ Nat.mul_le_mul_right _ hP4
    have hA4 : 4 ≤ Nat.card ↥A₀ := a7d35_four_le_card_closure
    omega
  have hLV : ∀ h : ↥L, ∀ u ∈ V, (h : MulAut W) u ∈ V := hπ.2.2.2.1
  have hfix : ∀ v : ↥V, β v ∈ P → ∀ a ∈ A₀, ((π a : ↥L) : MulAut W) (v : W) = v := by
    intro v hv a ha
    have key : ∀ e : ↥(alternatingGroup (Fin 7)),
        ((M e : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ Multiplicative.toAdd (β v) =
          Multiplicative.toAdd (β v) → e ∈ fixSub π {(v : W)} := by
      intro e he
      rintro _ rfl
      have hu := hLV (π e) v v.2
      have h1 : β ⟨((π e : ↥L) : MulAut W) (v : W), hu⟩ = β v := by
        refine (hβe e v hu).trans ?_
        show Multiplicative.ofAdd (((α (altLift7 e) : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ
          Multiplicative.toAdd (β v)) = β v
        rw [← hMe e, he]
        rfl
      exact congrArg Subtype.val (hβinj h1)
    have hgen : ({a7e₁, a7e₂} : Set ↥(alternatingGroup (Fin 7))) ⊆ fixSub π {(v : W)} := by
      rintro e (rfl | rfl)
      · exact key _ (a7d35_mem_fixSub.mp hv).1
      · exact key _ (a7d35_mem_fixSub.mp hv).2
    exact (Subgroup.closure_le _).mpr hgen ha (v : W) (Set.mem_singleton _)
  exact isFFModule_of_realizesVia (G64.a7Four_faithful α) hLs hπ β (fun m => hβs m trivial) A₀
    hA₀c hA₀2 hA₀1 P hidx hfix

end CFSG.Quasithin.RonanD35
