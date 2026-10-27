module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Heisenberg
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open Module Module.End CFSG.SignalizerFunctorTheorem.NonLocal
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {F W G : Type*} [Field F] [AddCommGroup W] [Module F W] [Group G]


theorem exists_maximal_abelian [Finite G] (Zs : Subgroup G) (hZ : IsMulCommutative Zs) :
    ∃ A : Subgroup G, Zs ≤ A ∧ IsMulCommutative A ∧
      ∀ g : G, (∀ a ∈ A, g * a = a * g) → g ∈ A := by
  classical
  let S : Set (Subgroup G) := {B | Zs ≤ B ∧ IsMulCommutative B}
  have hne : S.Nonempty := ⟨Zs, le_rfl, hZ⟩
  obtain ⟨A, ⟨hZA, hA⟩, hmax⟩ := (wellFounded_gt (α := Subgroup G)).has_min S hne
  refine ⟨A, hZA, hA, fun g hg => ?_⟩
  let B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {g})
  have hcomm : ∀ x ∈ (A : Set G) ∪ {g}, ∀ y ∈ (A : Set G) ∪ {g}, x * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
    · rw [Set.mem_singleton_iff.mp hy]; exact (hg x hx).symm
    · rw [Set.mem_singleton_iff.mp hx]; exact hg y hy
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  have hB : IsMulCommutative B :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm x hx y hy)
  have hAB : A ≤ B := fun x hx => Subgroup.subset_closure (Set.mem_union_left _ hx)
  have hBS : B ∈ S := ⟨hZA.trans hAB, hB⟩
  by_contra hgA
  apply hmax B hBS
  refine lt_of_le_of_ne hAB (fun h => hgA ?_)
  rw [h]
  exact Subgroup.subset_closure (Set.mem_union_right _ rfl)

variable [IsAlgClosed F] [FiniteDimensional F W]

theorem card_le_sq_of_nondegenerate [Finite G] [Nontrivial W]
    (ρ : G →* End F W) (hρ : Function.Injective ρ) (Zs : Subgroup G)
    (hZs : ∀ g, g ∈ Zs ↔ ∃ c : F, ρ g = c • 1)
    (hcomm : ∀ a b : G, ⁅a, b⁆ ∈ Zs)
    (hcenter : ∀ a : G, (∀ b, a * b = b * a) → a ∈ Zs)
    (hinv : (Nat.card G : F) ≠ 0) :
    ∃ e : ℕ, e ≤ finrank F W ∧ Nat.card Zs * e ∣ Nat.card G ∧
      Nat.card G ≤ Nat.card Zs * e ^ 2 := by
  classical
  have hd : 1 ≤ finrank F W := Module.finrank_pos
  have hcentral : ∀ z ∈ Zs, ∀ g : G, z * g = g * z := by
    intro z hz g
    obtain ⟨c, hc⟩ := (hZs z).mp hz
    apply hρ
    rw [map_mul, map_mul, hc]
    ext x
    simp [LinearMap.smul_apply]
  have hZcomm : IsMulCommutative Zs :=
    ⟨⟨fun x y => Subtype.ext (hcentral x x.2 y)⟩⟩
  let ζ : G → F := fun g => if h : g ∈ Zs then ((hZs g).mp h).choose else 1
  have hζ : ∀ z ∈ Zs, ρ z = ζ z • 1 := by
    intro z hz
    simp only [ζ, hz, ↓reduceDIte]
    exact ((hZs z).mp hz).choose_spec
  have hone : (1 : End F W) ≠ 0 := one_ne_zero
  have hζmul : ∀ z ∈ Zs, ∀ z' ∈ Zs, ζ (z * z') = ζ z * ζ z' := by
    intro z hz z' hz'
    have h1 := hζ (z * z') (Zs.mul_mem hz hz')
    rw [map_mul, hζ z hz, hζ z' hz', smul_mul_smul_comm, one_mul] at h1
    have : ζ (z * z') • (1 : End F W) = (ζ z * ζ z') • 1 := h1.symm
    exact (smul_left_injective F hone this)
  have hζone : ζ 1 = 1 := by
    have h1 := hζ 1 Zs.one_mem
    rw [map_one] at h1
    have : ζ 1 • (1 : End F W) = (1 : F) • 1 := by rw [← h1, one_smul]
    exact smul_left_injective F hone this
  have hζinj : ∀ z ∈ Zs, ∀ z' ∈ Zs, ζ z = ζ z' → z = z' := by
    intro z hz z' hz' h
    apply hρ
    rw [hζ z hz, hζ z' hz', h]
  by_cases hall : ∀ g : G, g ∈ Zs
  · have hG : Zs = ⊤ := (Subgroup.eq_top_iff' Zs).mpr hall
    refine ⟨1, hd, ?_, ?_⟩
    · rw [hG, Subgroup.card_top, mul_one]
    · rw [hG, Subgroup.card_top]
      simp
  push Not at hall
  obtain ⟨g₀, hg₀⟩ := hall
  obtain ⟨Ã, hZA, hA, hcent⟩ := exists_maximal_abelian Zs hZcomm
  have hnormal : Ã.Normal := ⟨fun a ha g => by
    have : g * a * g⁻¹ = ⁅g, a⁆ * a := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Ã.mul_mem (hZA (hcomm g a)) ha⟩
  have hdvd : Nat.card Ã ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Ã
  have hinvA : (Nat.card Ã : F) ≠ 0 := by
    intro h
    apply hinv
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul, h, zero_mul]
  have hQ : Nat.card (G ⧸ Ã) ≤ finrank F W := by
    have hnt : ∃ z ∈ Zs, ρ z ≠ 1 := by
      have hnc : ¬ ∀ b, g₀ * b = b * g₀ := fun h => hg₀ (hcenter g₀ h)
      push Not at hnc
      obtain ⟨b, hb⟩ := hnc
      refine ⟨⁅g₀, b⁆, hcomm g₀ b, fun h1 => hb ?_⟩
      have h2 : ⁅g₀, b⁆ = 1 := hρ (by rw [h1, map_one])
      rw [commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    refine card_le_finrank_of_translations ρ Ã Zs hA hinvA hZA
      (fun i : G ⧸ Ã => (Quotient.out i)⁻¹) (fun i a _ => by simpa using hcomm _ a) hnt ?_
    intro ξ _ _ _ ⟨w, hw0, hw⟩ i j hij
    have hξζ : ∀ z ∈ Zs, ξ z = ζ z := by
      intro z hz
      have h1 := hw z hz
      rw [hζ z hz, LinearMap.smul_apply, Module.End.one_apply] at h1
      exact (smul_left_injective F hw0 h1).symm
    by_contra hcon
    push Not at hcon
    apply hij
    have hg : (Quotient.out j : G)⁻¹ * Quotient.out i ∈ Ã := by
      apply hcent
      intro a ha
      have h1 := hcon a ha
      simp only [inv_inv] at h1
      rw [hξζ _ (hcomm _ a), hξζ _ (hcomm _ a)] at h1
      have h2 := hζinj _ (hcomm _ a) _ (hcomm _ a) h1
      simp only [commutatorElement_def] at h2
      have h3 : (Quotient.out i : G) * a * (Quotient.out i)⁻¹ =
          (Quotient.out j) * a * (Quotient.out j)⁻¹ := mul_right_cancel h2
      calc (Quotient.out j : G)⁻¹ * Quotient.out i * a
          = (Quotient.out j)⁻¹ * ((Quotient.out i) * a * (Quotient.out i)⁻¹) *
              (Quotient.out i) := by group
        _ = (Quotient.out j)⁻¹ * ((Quotient.out j) * a * (Quotient.out j)⁻¹) *
              (Quotient.out i) := by rw [h3]
        _ = a * ((Quotient.out j)⁻¹ * Quotient.out i) := by group
    have h4 := (QuotientGroup.eq (s := Ã)).mpr hg
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h4
    exact h4.symm
  have hA' : Nat.card Ã ≤ Nat.card Zs * Nat.card (G ⧸ Ã) := by
    have hcommmul : ∀ a g h : G, ⁅a, g * h⁆ = ⁅a, g⁆ * ⁅a, h⁆ := by
      intro a g h
      have h1 : ⁅a, g * h⁆ = ⁅a, g⁆ * (g * ⁅a, h⁆ * g⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      have h2 : g * ⁅a, h⁆ * g⁻¹ = ⁅a, h⁆ := by
        rw [← hcentral _ (hcomm a h) g, mul_inv_cancel_right]
      rw [h1, h2]
    let pair : G → (G →* F) := fun a =>
      { toFun := fun g => ζ ⁅a, g⁆
        map_one' := by simp [hζone]
        map_mul' := fun g h => by
          rw [hcommmul]
          exact hζmul _ (hcomm a g) _ (hcomm a h) }
    have hpair : ∀ a g, pair a g = ζ ⁅a, g⁆ := fun a g => rfl
    let Θ : Ã → (G ⧸ Ã →* F) := fun a =>
      QuotientGroup.lift Ã (pair a) (fun b hb => by
        rw [MonoidHom.mem_ker, hpair]
        have : ⁅(a : G), b⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact congrArg Subtype.val (mul_comm' a ⟨b, hb⟩)
        rw [this, hζone])
    have hΘ : ∀ (a : Ã) (g : G), Θ a (QuotientGroup.mk g) = ζ ⁅(a : G), g⁆ := fun a g => rfl
    let Zs' : Subgroup Ã := Zs.subgroupOf Ã
    have hkey : ∀ a b : Ã, Θ a = Θ b ↔ (a⁻¹ * b : Ã) ∈ Zs' := by
      intro a b
      constructor
      · intro h
        have h1 : ∀ g : G, ζ ⁅(a : G), g⁆ = ζ ⁅(b : G), g⁆ := fun g => by
          rw [← hΘ, ← hΘ, h]
        have h2 : ∀ g : G, ⁅(a : G), g⁆ = ⁅(b : G), g⁆ := fun g =>
          hζinj _ (hcomm _ g) _ (hcomm _ g) (h1 g)
        have h3 : ∀ g : G, ((a⁻¹ * b : Ã) : G) * g = g * ((a⁻¹ * b : Ã) : G) := by
          intro g
          have h5 := h2 g
          simp only [commutatorElement_def] at h5
          have h4 : (a : G) * g * (a : G)⁻¹ = (b : G) * g * (b : G)⁻¹ := mul_right_cancel h5
          calc ((a⁻¹ * b : Ã) : G) * g = (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹) * b := by
                simp [mul_assoc]
            _ = (a : G)⁻¹ * ((a : G) * g * (a : G)⁻¹) * b := by rw [h4]
            _ = g * ((a⁻¹ * b : Ã) : G) := by simp [mul_assoc]
        exact hcenter _ h3
      · intro h
        have hz : ((a⁻¹ * b : Ã) : G) ∈ Zs := h
        have hc := hcentral _ hz
        refine MonoidHom.ext (fun x => ?_)
        induction x using QuotientGroup.induction_on with
        | H g =>
          rw [hΘ, hΘ]
          congr 1
          have hb : (b : G) = a * ((a⁻¹ * b : Ã) : G) := by simp
          have hzg : ((a⁻¹ * b : Ã) : G) * g * ((a⁻¹ * b : Ã) : G)⁻¹ = g := by
            rw [hc g]; group
          rw [hb]
          calc ⁅(a : G), g⁆ = (a : G) * (((a⁻¹ * b : Ã) : G) * g * ((a⁻¹ * b : Ã) : G)⁻¹) *
                (a : G)⁻¹ * g⁻¹ := by rw [hzg]; simp [commutatorElement_def, mul_assoc]
            _ = ⁅(a : G) * ((a⁻¹ * b : Ã) : G), g⁆ := by
                simp [commutatorElement_def, mul_assoc]
    let Θ' : Ã ⧸ Zs' → (G ⧸ Ã →* F) :=
      Quotient.lift Θ (fun a b hab => (hkey a b).mpr (QuotientGroup.leftRel_apply.mp hab))
    have hΘ'inj : Function.Injective Θ' := by
      intro x y hxy
      induction x using Quotient.inductionOn with
      | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hkey a b).mp hxy))
    have := Fintype.ofFinite (G ⧸ Ã)
    have hli := linearIndependent_monoidHom (G ⧸ Ã) F
    have hfin : Finite (G ⧸ Ã →* F) := hli.finite
    have hartin : Nat.card (G ⧸ Ã →* F) ≤ Nat.card (G ⧸ Ã) := by
      have := Fintype.ofFinite (G ⧸ Ã →* F)
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      have := hli.fintype_card_le_finrank
      simpa using this
    have hq : Nat.card (Ã ⧸ Zs') ≤ Nat.card (G ⧸ Ã →* F) :=
      Nat.card_le_card_of_injective Θ' hΘ'inj
    have hZ : Nat.card Zs' = Nat.card Zs :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zs', hZ, mul_comm]
    exact Nat.mul_le_mul_left _ (hq.trans hartin)

  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup Ã
  refine ⟨Nat.card (G ⧸ Ã), hQ, ?_, ?_⟩
  · rw [hsplit, mul_comm (Nat.card Zs)]
    exact Nat.mul_dvd_mul_left _ (Subgroup.card_dvd_of_le hZA)
  · calc Nat.card G = Nat.card (G ⧸ Ã) * Nat.card Ã := hsplit
      _ ≤ Nat.card (G ⧸ Ã) * (Nat.card Zs * Nat.card (G ⧸ Ã)) := Nat.mul_le_mul_left _ hA'
      _ = Nat.card Zs * Nat.card (G ⧸ Ã) ^ 2 := by ring


end CFSG.SignalizerFunctorTheorem.NonLocal
