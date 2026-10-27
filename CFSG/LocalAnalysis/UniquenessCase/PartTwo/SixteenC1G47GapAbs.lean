module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c1_G47_fix_of_prime_iterate {α : Type*} {f : α → α} {S : Set α} (hS4 : S.ncard ≤ 4)
    (hSfin : S.Finite) {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hfq : ∀ x, f^[q] x = x)
    (hmaps : ∀ x ∈ S, f x ∈ S) : ∀ x ∈ S, f x = x := by
  intro x hx
  by_contra hne
  haveI : Fact q.Prime := ⟨hq⟩
  have hper : Function.IsPeriodicPt f q x := hfq x
  have hmp : Function.minimalPeriod f x = q := Function.minimalPeriod_eq_prime hper hne
  have hmem : ∀ i : ℕ, f^[i] x ∈ S := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact hmaps _ ih
  have hinj : Set.InjOn (fun i : ℕ => f^[i] x) (Set.Iio q) := by
    have h := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
    rwa [hmp] at h
  have hcard : (Set.Iio q).ncard ≤ S.ncard :=
    Set.ncard_le_ncard_of_injOn (fun i : ℕ => f^[i] x) (fun i _ => hmem i) hinj hSfin
  have hIio : (Set.Iio q).ncard = q := by
    rw [← Finset.coe_Iio, Set.ncard_coe_finset, Nat.card_Iio]
  omega

theorem s16c1_G47_normCl {Hs : Type} [Group Hs] [Finite Hs] (hO2 : CFSG.pCore 2 Hs = ⊥) {u : Hs}
    (hu2 : u * u = 1) (hcomm : ∀ g : Hs, g * u * g⁻¹ * u = u * (g * u * g⁻¹)) : u = 1 := by
  classical
  set X : Subgroup Hs := Subgroup.normalClosure {u} with hXdef
  haveI hXn : X.Normal := Subgroup.normalClosure_normal
  set T : Set Hs := Group.conjugatesOfSet ({u} : Set Hs) with hT
  have hTX : Subgroup.closure T = X := rfl
  have hTmem : ∀ a ∈ T, ∃ g : Hs, a = g * u * g⁻¹ := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := Group.mem_conjugatesOfSet_iff.1 ha
    rw [Set.mem_singleton_iff.1 hb] at hab
    obtain ⟨g, hg⟩ := isConj_iff.1 hab
    exact ⟨g, hg.symm⟩
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ (⊥ : Subgroup Hs) := by
    intro a ha b hb
    obtain ⟨g, rfl⟩ := hTmem a ha
    obtain ⟨k, rfl⟩ := hTmem b hb
    have h := hcomm (k⁻¹ * g)
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc g * u * g⁻¹ * (k * u * k⁻¹) * (g * u * g⁻¹)⁻¹ * (k * u * k⁻¹)⁻¹
        = k * ((k⁻¹ * g) * u * (k⁻¹ * g)⁻¹ * u * ((k⁻¹ * g) * u * (k⁻¹ * g)⁻¹)⁻¹ * u⁻¹) * k⁻¹ := by
          group
      _ = 1 := by
          rw [h]
          group
  have hsqT : ∀ a ∈ T, a ^ 2 ∈ (⊥ : Subgroup Hs) := by
    intro a ha
    obtain ⟨g, rfl⟩ := hTmem a ha
    rw [Subgroup.mem_bot]
    calc (g * u * g⁻¹) ^ 2 = g * (u * u) * g⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [hu2]; group
  have hZ : ∀ c ∈ (⊥ : Subgroup Hs), ∀ y ∈ X, c * y = y * c := fun c hc y _ => by
    rw [Subgroup.mem_bot] at hc
    rw [hc, one_mul, mul_one]
  obtain ⟨-, hsq⟩ := s16c1_closure_comm_sq (T := T) (X := X) (Z := ⊥) hTX hZ hcommT hsqT
  have hXp : IsPGroup 2 X := fun g => ⟨1, by
    have h := Subgroup.mem_bot.1 (hsq (g : Hs) g.2)
    apply Subtype.ext
    simpa using h⟩
  have hXle : X ≤ CFSG.pCore 2 Hs := le_sSup ⟨hXn, hXp⟩
  rw [hO2] at hXle
  have huX : u ∈ X := Subgroup.subset_normalClosure (Set.mem_singleton u)
  exact Subgroup.mem_bot.1 (hXle huX)

theorem s16c1_G47_two_elems {Hs : Type} [Group Hs] {W : Subgroup Hs} (h : Nat.card ↥W = 2)
    {u : Hs} (hu : u ∈ W) (hu1 : u ≠ 1) : ∀ v ∈ W, v = 1 ∨ v = u := by
  obtain ⟨⟨u', hu'⟩, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).1 h
  intro v hv
  by_cases hv1 : v = 1
  · exact Or.inl hv1
  · refine Or.inr ?_
    have h1 := huniq ⟨v, hv⟩ (fun h' => hv1 (congrArg Subtype.val h'))
    have h2 := huniq ⟨u, hu⟩ (fun h' => hu1 (congrArg Subtype.val h'))
    exact (congrArg Subtype.val h1).trans (congrArg Subtype.val h2).symm

theorem s16c1_G47_conj_eq_of_two {Hs : Type} [Group Hs] {W : Subgroup Hs} {u : Hs} (hu1 : u ≠ 1)
    (hW : ∀ v ∈ W, v = 1 ∨ v = u) {b : Hs} (hb : b * u * b⁻¹ ∈ W) : b * u * b⁻¹ = u := by
  refine (hW _ hb).resolve_left fun h => hu1 ?_
  calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
    _ = 1 := by rw [h]; group

theorem s16c1_G47_ker_conj {Hs F : Type} [Group Hs] [Finite Hs] [Group F] (ρ : Hs →* MulAut F)
    (hF : ∀ e : F, e * e = 1) {B : Subgroup Hs} {u : Hs} (hB : ∀ v : Hs, ρ v = 1 → v ∈ B)
    (hBu : ∀ b ∈ B, b * u * b⁻¹ = u) (hall : ∀ e : F, ρ u e * e = 1)
    (hO2 : CFSG.pCore 2 Hs = ⊥) (hu2 : u * u = 1) : u = 1 := by
  have hρu : ρ u = 1 := by
    refine MulEquiv.ext fun e => ?_
    have h2 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hF e)
    rw [MulAut.one_apply]
    exact (mul_eq_one_iff_eq_inv.1 (hall e)).trans h2
  refine s16c1_G47_normCl hO2 hu2 fun g => ?_
  have hker : ρ (g * u * g⁻¹) = 1 := by
    rw [map_mul, map_mul, hρu, mul_one, map_inv, mul_inv_cancel]
  exact mul_inv_eq_iff_eq_mul.1 (hBu _ (hB _ hker))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
