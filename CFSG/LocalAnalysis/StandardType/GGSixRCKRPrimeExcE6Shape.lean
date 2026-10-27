module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.GGFinModel

section Transport

variable {τ : Tag} {M₁ M₂ : Type*} [CommGroup M₁] [CommGroup M₂]
  {χ₁ : Multiplicative (Fin τ.rank → ℤ) →* M₁} {χ₂ : Multiplicative (Fin τ.rank → ℤ) →* M₂}

theorem rckE6_class_transfer (hker : kernelRoots χ₁ ⊆ kernelRoots χ₂) {a b : kernelRoots χ₁}
    (h : (⟦a⟧ : KernelComponent χ₁) = ⟦b⟧) :
    (⟦⟨a.1, hker a.2⟩⟧ : KernelComponent χ₂) = ⟦⟨b.1, hker b.2⟩⟧ := by
  have h' := Quotient.exact h
  clear h
  apply Quotient.sound
  change Relation.EqvGen _ _ _ at h' ⊢
  induction h' with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ hxy
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem rckE6_exists_component_eq (hker : kernelRoots χ₁ = kernelRoots χ₂) (i₁ : KernelComponent χ₁) :
    ∃ i₂ : KernelComponent χ₂, componentRoots χ₁ i₁ = componentRoots χ₂ i₂ := by
  induction i₁ using Quotient.inductionOn with
  | _ a =>
    have ha2 : a.1 ∈ kernelRoots χ₂ := hker ▸ a.2
    refine ⟨⟦⟨a.1, ha2⟩⟧, ?_⟩
    ext β
    constructor
    · rintro ⟨hβ, hβa⟩
      exact ⟨hker ▸ hβ, rckE6_class_transfer hker.le hβa⟩
    · rintro ⟨hβ, hβa⟩
      exact ⟨hker ▸ hβ, rckE6_class_transfer hker.ge (a := ⟨β, hβ⟩) (b := ⟨a.1, ha2⟩) hβa⟩

end Transport

section Torus

variable {τ : Tag} {L : Type} [Field L]

@[expose] def rckE6_rootCharEval (v : Fin τ.rank → ℤ) : (Fin τ.rank → Lˣ) →* Lˣ where
  toFun a := rootChar a v
  map_one' := by simp [rootChar]
  map_mul' a b := by simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rckE6_coord_rootDiagUnit
    (b : Fin τ.rank → Lˣ) : rckTorusCoord (rootDiagUnit τ b) = b :=
  Function.leftInverse_invFun (f := (rootDiagUnitHom τ L : (Fin τ.rank → Lˣ) → ModGL τ L))
    CFSG.LieType.Chevalley.rootDiagUnit_injective b

theorem rckE6_kernelRoots_zpowers_eq
    (g x₀ : ModGL τ L) (hT : g⁻¹ * x₀ * g ∈ torusGroup τ L) :
    kernelRoots (rckFamChar g (fun x : Subgroup.zpowers x₀ => (x : ModGL τ L))) =
      kernelRoots (rootCharHom (rckTorusCoord (g⁻¹ * x₀ * g))) := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hcoord : rckTorusCoord (g⁻¹ * x₀ * g) = a := by rw [ha, rckE6_coord_rootDiagUnit]
  ext α
  constructor
  · rintro ⟨hr, h1⟩
    refine ⟨hr, ?_⟩
    have h2 := congrFun h1 ⟨x₀, Subgroup.mem_zpowers x₀⟩
    exact h2
  · rintro ⟨hr, h1⟩
    refine ⟨hr, ?_⟩
    funext ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    have hconj : g⁻¹ * x₀ ^ k * g = (g⁻¹ * x₀ * g) ^ k := by
      have := conj_zpow (a := g⁻¹) (b := x₀) (i := k)
      rw [inv_inv] at this
      rw [this]
    have hco : rckTorusCoord ((g⁻¹ * x₀ * g) ^ k) = a ^ k := by
      have hz : rootDiagUnit τ a ^ k = rootDiagUnit τ (a ^ k) :=
        (map_zpow (rootDiagUnitHom τ L) a k).symm
      rw [ha, hz]
      exact rckE6_coord_rootDiagUnit _
    show rootChar (rckTorusCoord (g⁻¹ * x₀ ^ k * g)) α = 1
    rw [hconj, hco]
    rw [hcoord] at h1
    have h3 : rootChar a α = 1 := h1
    have h4 : rootChar (a ^ k) α = (rootChar a α) ^ k := map_zpow (rckE6_rootCharEval α) a k
    rw [h4, h3, one_zpow]

end Torus

theorem rckE6_kacCount_four_ne_48 : ∀ C : Finset (Option (Fin Tag.E6.rank)), C.card = 4 →
    kacCount .E6 ![1, 2, 2, 3, 2, 1] C ≠ 48 := by
  decide +kernel

theorem rckE6_class_not_big {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E6.rank → GGLˣ}
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ ((compRank (componentRoots (rootCharHom a) i) = 4 ∧
          (componentRoots (rootCharHom a) i).ncard = 48) ∨
      (compRank (componentRoots (rootCharHom a) i) = 6 ∧
          (componentRoots (rootCharHom a) i).ncard = 72) ∨
      (compRank (componentRoots (rootCharHom a) i) = 7 ∧
          (componentRoots (rootCharHom a) i).ncard = 126) ∨
      (compRank (componentRoots (rootCharHom a) i) = 8 ∧
          (componentRoots (rootCharHom a) i).ncard = 240)) := by
  have hpL : (p : GGL) ≠ 0 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ((CharP.cast_eq_zero_iff GGL 2 p).1 h)).symm
  obtain ⟨v, μ, -, hall⟩ := exists_pinnedT_of_pos (L := GGL) hp.pos hpL (K := kacE6) facts_E6 hTp
  obtain ⟨x, C, -, hCp, -, hrank, hcount⟩ := hall i
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  have hroot : Tag.E6.rootCount = 72 := by decide
  rintro (⟨h4, h48⟩ | ⟨h6, h72⟩ | ⟨h7, -⟩ | ⟨h8, -⟩)
  · rw [hrank] at h4
    rw [hcount] at h48
    exact rckE6_kacCount_four_ne_48 C h4 h48
  · apply h1
    exact rootDiagUnit_eq_one_of_ncard i (by rw [hroot]; omega)
  · have : Tag.E6.rank = 6 := rfl
    omega
  · have : Tag.E6.rank = 6 := rfl
    omega

theorem rckE6_iterate_two_mul {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ2 : ∀ γ, IsRoot Tag.E6 γ → ρ (ρ γ) = γ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (n : ℕ) : (ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * n] γ = γ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rw [hρ2 γ hγ]
    exact ih

theorem rckE6_zpowers_class_not_excShape
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g x₀ : ModGL Tag.E6 GGL} {S : Subgroup (ModGL Tag.E6 GGL)}
    (hS : S = Subgroup.zpowers x₀) (hx₁ : x₀ ≠ 1) (hxp : x₀ ^ p = 1)
    (hT : g⁻¹ * x₀ * g ∈ torusGroup Tag.E6 GGL) {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ2 : ∀ γ, IsRoot Tag.E6 γ → ρ (ρ γ) = γ)
    (iK : KernelComponent (rckFamChar g (fun x : S => (x : ModGL Tag.E6 GGL)))) :
    ¬ RCKExcShape ρ
      (componentRoots (rckFamChar g (fun x : S => (x : ModGL Tag.E6 GGL))) iK) := by
  subst hS
  have hker := rckE6_kernelRoots_zpowers_eq g x₀ hT
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hcoord : rckTorusCoord (g⁻¹ * x₀ * g) = a := by rw [ha, rckE6_coord_rootDiagUnit]
  rw [hcoord] at hker
  obtain ⟨i₂, hi₂⟩ := rckE6_exists_component_eq hker iK
  rw [hi₂]
  have hTp : rootDiagUnit Tag.E6 a ^ p = 1 := by
    rw [← ha]
    have := conj_pow (a := g⁻¹) (b := x₀) (i := p)
    rw [inv_inv] at this
    rw [this, hxp]
    group
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    rw [← ha]
    intro h
    apply hx₁
    have h' : g⁻¹ * x₀ * g = 1 := h
    calc x₀ = g * (g⁻¹ * x₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  intro hshape
  unfold RCKExcShape at hshape
  rcases hshape with h | h | h | h | ⟨-, -, hout⟩
  · exact rckE6_class_not_big hp hp2 hTp h1 i₂ (Or.inl h)
  · exact rckE6_class_not_big hp hp2 hTp h1 i₂ (Or.inr (Or.inl h))
  · exact rckE6_class_not_big hp hp2 hTp h1 i₂ (Or.inr (Or.inr (Or.inl h)))
  · exact rckE6_class_not_big hp hp2 hTp h1 i₂ (Or.inr (Or.inr (Or.inr h)))
  · apply hout
    refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
    rw [one_smul]
    exact rckE6_iterate_two_mul hρ2 hγ.1.1 _

theorem rckE6_famClass_not_excShape
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : ModGL Tag.E6 GGL} (S : Subgroup (ModGL Tag.E6 GGL))
    (hS : Nat.card S = p) (hT : ∀ x ∈ S, g⁻¹ * x * g ∈ torusGroup Tag.E6 GGL)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ2 : ∀ γ, IsRoot Tag.E6 γ → ρ (ρ γ) = γ)
    (iK : KernelComponent (rckFamChar g (fun x : S => (x : ModGL Tag.E6 GGL)))) :
    ¬ RCKExcShape ρ
      (componentRoots (rckFamChar g (fun x : S => (x : ModGL Tag.E6 GGL))) iK) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := (isCyclic_of_prime_card hS).exists_generator
  have hSeq : S = Subgroup.zpowers (y : ModGL Tag.E6 GGL) := by
    refine le_antisymm (fun z hz => ?_) ((Subgroup.zpowers_le).2 y.2)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hy ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hy1 : (y : ModGL Tag.E6 GGL) ≠ 1 := by
    intro h1
    have hy1' : y = 1 := Subtype.ext h1
    have hsub : Subsingleton S := by
      refine ⟨fun u v => ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hy u)
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 (hy v)
      rw [hy1', one_zpow] at hk hl
      rw [← hk, ← hl]
    have : Nat.card S = 1 := Nat.card_unique
    rw [hS] at this
    exact hp.ne_one this
  have hxp : (y : ModGL Tag.E6 GGL) ^ p = 1 := by
    have := pow_card_eq_one' (G := S) (x := y)
    rw [hS] at this
    exact congrArg Subtype.val this
  exact rckE6_zpowers_class_not_excShape hp hp2 hSeq hy1 hxp (hT y y.2) hρ2 iK

end CFSG.StandardType.RCKRP

end
