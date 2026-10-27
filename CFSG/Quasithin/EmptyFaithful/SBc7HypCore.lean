module

public import CFSG.Quasithin.EmptyFaithful.SBd5UL
public import CFSG.Quasithin.EmptyFaithful.SBd6Tw

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SBc7

section Summand

variable {G : Type} [Group G] {F : Type} [Field F] {k : ℕ} {Q : Subgroup G}

@[expose] def summand (β : ↥Q →* Multiplicative (Fin k → Fin 3 → F)) (i : Fin k) : Subgroup G where
  carrier := {u | ∃ h : u ∈ Q, ∀ j, j ≠ i → Multiplicative.toAdd (β ⟨u, h⟩) j = 0}
  one_mem' := ⟨Q.one_mem, fun j _ => by
    have : β ⟨1, Q.one_mem⟩ = 1 := map_one β
    rw [show (⟨1, Q.one_mem⟩ : ↥Q) = 1 from rfl, map_one]
    rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Q.mul_mem ha hb, fun j hj => ?_⟩
    have : (⟨a * b, Q.mul_mem ha hb⟩ : ↥Q) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, toAdd_mul, Pi.add_apply, ha' j hj, hb' j hj, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Q.inv_mem ha, fun j hj => ?_⟩
    have : (⟨a⁻¹, Q.inv_mem ha⟩ : ↥Q) = (⟨a, ha⟩ : ↥Q)⁻¹ := rfl
    rw [this, map_inv, toAdd_inv, Pi.neg_apply, ha' j hj, neg_zero]

variable (β : ↥Q →* Multiplicative (Fin k → Fin 3 → F)) {i : Fin k}

theorem summand_le : summand β i ≤ Q := fun _ hu => hu.1

end Summand

section Core

variable {G : Type} [Group G] {F : Type} [Field F] [Fintype F] {k : ℕ} {L Q Yp : Subgroup G}

theorem hyperplane_core (hF : Fintype.card F = 2)
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hαs : Function.Surjective α)
    (β : ↥Q →* Multiplicative (Fin k → Fin 3 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = ⊥) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hβe : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hQY : Q ≤ Subgroup.normalizer (Yp : Set G))
    (hy : ∃ y ∈ Yp, ∃ hyL : y ∈ L, α ⟨y, hyL⟩ ≠ 1) :
    Q ≤ ⨆ (W : Subgroup G) (_ : W ≤ Q ∧ L ≤ Subgroup.normalizer (W : Set G) ∧ W ⊓ Yp ≠ ⊥ ∧
      ∀ W' : Subgroup G, W' ≤ W → L ≤ Subgroup.normalizer (W' : Set G) → W' = ⊥ ∨ W' = W), W := by
  classical
  have hβi : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hβk
  have hβe' : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i) := fun a u v h i => by
    simpa [moduleAct] using hβe a u v h i
  have hmap : ∀ i : Fin k, ∀ a ∈ L, ∀ u ∈ summand β i, a * u * a⁻¹ ∈ summand β i := by
    intro i a ha u hu
    obtain ⟨huQ, hu'⟩ := hu
    have hauQ : a * u * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ ha) u).mp huQ
    refine ⟨hauQ, fun j hj => ?_⟩
    rw [hβe' ⟨a, ha⟩ ⟨u, huQ⟩ ⟨a * u * a⁻¹, hauQ⟩ rfl j, hu' j hj]
    simp
  have hnorm : ∀ i : Fin k, L ≤ Subgroup.normalizer (summand β i : Set G) := by
    intro i a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hmap i a ha y hy, fun hy => ?_⟩
    have := hmap i a⁻¹ (L.inv_mem ha) _ hy
    simpa [mul_assoc] using this
  have hirr : ∀ i : Fin k, ∀ W' : Subgroup G, W' ≤ summand β i →
      L ≤ Subgroup.normalizer (W' : Set G) → W' = ⊥ ∨ W' = summand β i := by
    intro i W' hW' hLW'
    let X : AddSubgroup (Fin 3 → F) :=
      { carrier := {v | ∃ u ∈ W', ∃ h : u ∈ Q, Multiplicative.toAdd (β ⟨u, h⟩) i = v}
        zero_mem' := ⟨1, W'.one_mem, Q.one_mem, by
          rw [show (⟨1, Q.one_mem⟩ : ↥Q) = 1 from rfl, map_one]; rfl⟩
        add_mem' := by
          rintro _ _ ⟨u, hu, huQ, rfl⟩ ⟨u', hu', hu'Q, rfl⟩
          refine ⟨u * u', W'.mul_mem hu hu', Q.mul_mem huQ hu'Q, ?_⟩
          rw [show (⟨u * u', Q.mul_mem huQ hu'Q⟩ : ↥Q) = ⟨u, huQ⟩ * ⟨u', hu'Q⟩ from rfl, map_mul,
            toAdd_mul]
          rfl
        neg_mem' := by
          rintro _ ⟨u, hu, huQ, rfl⟩
          refine ⟨u⁻¹, W'.inv_mem hu, Q.inv_mem huQ, ?_⟩
          rw [show (⟨u⁻¹, Q.inv_mem huQ⟩ : ↥Q) = (⟨u, huQ⟩ : ↥Q)⁻¹ from rfl, map_inv, toAdd_inv]
          rfl }
    have hX : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ x ∈ X,
        (g : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ X := by
      rintro g _ ⟨u, hu, huQ, rfl⟩
      obtain ⟨a, ha⟩ := SBd5.act_surj hαs g
      have hauW' : (a : G) * u * (a : G)⁻¹ ∈ W' := (Subgroup.mem_normalizer_iff.mp (hLW' a.2) u).mp hu
      have hauQ : (a : G) * u * (a : G)⁻¹ ∈ Q := (hW' hauW').1
      refine ⟨_, hauW', hauQ, ?_⟩
      rw [hβe' a ⟨u, huQ⟩ ⟨_, hauQ⟩ rfl i, ha]
    rcases SBd6.irreducible_vec hF X hX with hXb | hXt
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨huQ, hu'⟩ := hW' hu
      have h0 : Multiplicative.toAdd (β ⟨u, huQ⟩) i = 0 := by
        have : Multiplicative.toAdd (β ⟨u, huQ⟩) i ∈ X := ⟨u, hu, huQ, rfl⟩
        rw [hXb] at this
        simpa using this
      have hβ1 : β ⟨u, huQ⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        funext j
        by_cases hj : j = i
        · subst hj; exact h0
        · exact hu' j hj
      have : (⟨u, huQ⟩ : ↥Q) = 1 := hβi (by rw [hβ1, map_one])
      have h1 : u = 1 := congrArg Subtype.val this
      rw [h1]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hW' ?_
      intro u hu
      obtain ⟨huQ, hu'⟩ := hu
      have : Multiplicative.toAdd (β ⟨u, huQ⟩) i ∈ X := by rw [hXt]; trivial
      obtain ⟨u₁, hu₁, hu₁Q, h1⟩ := this
      obtain ⟨_, hu₁'⟩ := hW' hu₁
      have hβeq : β ⟨u₁, hu₁Q⟩ = β ⟨u, huQ⟩ := by
        apply Multiplicative.toAdd.injective
        funext j
        by_cases hj : j = i
        · subst hj; exact h1
        · rw [hu₁' j hj, hu' j hj]
      have : (⟨u₁, hu₁Q⟩ : ↥Q) = ⟨u, huQ⟩ := hβi hβeq
      have h2 : u₁ = u := congrArg Subtype.val this
      rw [← h2]
      exact hu₁
  have hmeet : ∀ i : Fin k, summand β i ⊓ Yp ≠ ⊥ := by
    intro i
    obtain ⟨y, hyY, hyL, hα1⟩ := hy
    have hmv : ∃ v : Fin 3 → F,
        ((α ⟨y, hyL⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v ≠ v := by
      by_contra hcon
      push Not at hcon
      apply hα1
      apply Subtype.ext
      apply Units.ext
      ext a b
      have h1 := congrFun (hcon (Pi.single b 1)) a
      simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply, Pi.single_apply] using h1
    obtain ⟨v, hv⟩ := hmv
    obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd (Pi.single i v))
    have hu₀W : (u₀ : G) ∈ summand β i := by
      refine ⟨u₀.2, fun j hj => ?_⟩
      rw [show (⟨(u₀ : G), u₀.2⟩ : ↥Q) = u₀ from rfl, hu₀]
      simp [hj]
    have hu₀i : Multiplicative.toAdd (β u₀) i = v := by
      rw [hu₀]
      simp
    set u : G := (u₀ : G) with hu
    have hyu : y * u * y⁻¹ ∈ summand β i := hmap i y hyL u hu₀W
    have hyuQ : y * u * y⁻¹ ∈ Q := (summand_le β hyu)
    have hne : y * u * y⁻¹ * u⁻¹ ≠ 1 := by
      intro h1
      have h2 : y * u * y⁻¹ = u := by
        have := congrArg (fun z => z * u) h1
        simpa [mul_assoc] using this
      have h3 : Multiplicative.toAdd (β ⟨y * u * y⁻¹, hyuQ⟩) i = Multiplicative.toAdd (β u₀) i := by
        have : (⟨y * u * y⁻¹, hyuQ⟩ : ↥Q) = u₀ := Subtype.ext h2
        rw [this]
      rw [hβe' ⟨y, hyL⟩ u₀ ⟨y * u * y⁻¹, hyuQ⟩ rfl i, hu₀i] at h3
      exact hv h3
    have hcW : y * u * y⁻¹ * u⁻¹ ∈ summand β i :=
      (summand β i).mul_mem hyu ((summand β i).inv_mem hu₀W)
    have hcY : y * u * y⁻¹ * u⁻¹ ∈ Yp := by
      have h1 : u * y⁻¹ * u⁻¹ ∈ Yp :=
        (Subgroup.mem_normalizer_iff.mp (hQY u₀.2) y⁻¹).mp (Yp.inv_mem hyY) |> fun h => by
          have := (Subgroup.mem_normalizer_iff.mp (hQY u₀.2) y).mp hyY
          simpa [mul_assoc] using Yp.inv_mem (by simpa [mul_assoc] using this : u * y * u⁻¹ ∈ Yp)
      have := Yp.mul_mem hyY h1
      simpa [mul_assoc] using this
    intro hbot
    have : y * u * y⁻¹ * u⁻¹ ∈ summand β i ⊓ Yp := ⟨hcW, hcY⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hne this
  have hgen : ∀ s : Finset (Fin k), ∀ u : ↥Q, (∀ j, j ∉ s → Multiplicative.toAdd (β u) j = 0) →
      (u : G) ∈ ⨆ i ∈ s, summand β i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u hu
      have : β u = 1 := by
        apply Multiplicative.toAdd.injective
        funext j
        exact hu j (Finset.notMem_empty j)
      have h1 : u = 1 := hβi (by rw [this, map_one])
      rw [h1]
      exact Subgroup.one_mem _
    | insert a s ha ih =>
      intro u hu
      obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd (Pi.single a (Multiplicative.toAdd (β u) a)))
      have hu₀W : (u₀ : G) ∈ summand β a := by
        refine ⟨u₀.2, fun j hj => ?_⟩
        rw [show (⟨(u₀ : G), u₀.2⟩ : ↥Q) = u₀ from rfl, hu₀]
        simp [hj]
      have hu₀a : Multiplicative.toAdd (β u₀) a = Multiplicative.toAdd (β u) a := by
        rw [hu₀]
        simp
      have hrest : ∀ j, j ∉ s → Multiplicative.toAdd (β (u * u₀⁻¹)) j = 0 := by
        intro j hj
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
        by_cases hja : j = a
        · subst hja
          rw [hu₀a]
          simp
        · have h1 : Multiplicative.toAdd (β u₀) j = 0 := by
            rw [hu₀]
            simp [hja]
          rw [h1, hu j (by simp [hja, hj])]
          simp
      have h2 := ih (u * u₀⁻¹) hrest
      have h3 : (u : G) = ((u * u₀⁻¹ : ↥Q) : G) * (u₀ : G) := by simp
      rw [h3]
      have hsub : (⨆ i ∈ s, summand β i) ≤ ⨆ i ∈ insert a s, summand β i :=
        biSup_mono fun i hi => Finset.mem_insert_of_mem hi
      have hmem : summand β a ≤ ⨆ i ∈ insert a s, summand β i :=
        le_iSup₂_of_le a (Finset.mem_insert_self a s) le_rfl
      exact Subgroup.mul_mem _ (hsub h2) (hmem hu₀W)
  intro u hu
  have h1 := hgen Finset.univ ⟨u, hu⟩ (fun j hj => absurd (Finset.mem_univ j) hj)
  refine (?_ : (⨆ i ∈ (Finset.univ : Finset (Fin k)), summand β i) ≤ _) h1
  refine iSup₂_le fun i _ => ?_
  exact le_iSup₂_of_le (summand β i) ⟨summand_le β, hnorm i, hmeet i, hirr i⟩ le_rfl

end Core

end SBc7

end CFSG.Quasithin
