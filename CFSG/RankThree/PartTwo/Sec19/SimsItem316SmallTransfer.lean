module

public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Matrix

variable {G : Type*} [Group G]

@[expose] def IsMatrixType (L : Subgroup G) {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : Prop :=
  ∃ α : L →* H, Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
  ∃ β : blockU L →* Multiplicative (ι → ZMod 2), Function.Surjective β ∧
    β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ Multiplicative.toAdd (β u)

theorem isMatrixType_of_isOmegaPlusType {L : Subgroup G} {m : ℕ} (h : IsOmegaPlusType L m) :
    IsMatrixType L (omegaPlusTwo m) := h

theorem isMatrixType_of_isOmegaMinusType {L : Subgroup G} {m : ℕ} (h : IsOmegaMinusType L m) :
    IsMatrixType L (omegaMinusTwo m) := h

theorem isAltNaturalType_of_isMatrixType {L : Subgroup G} {n : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] {H : Subgroup (GL ι (ZMod 2))} (φ : H ≃* alternatingGroup (Fin n))
    (ψ : (ι → ZMod 2) ≃+ altHeart n)
    (hψ : ∀ (g : H) (w : ι → ZMod 2) (x : evenWeight n), ψ w = (x : altHeart n) →
      ψ (((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w) =
        (evenWeightPerm (φ g : Equiv.Perm (Fin n)) x : altHeart n))
    (h : IsMatrixType L H) : IsAltNaturalType L n := by
  obtain ⟨α, hα, hker, β, hβ, hβker, heq⟩ := h
  refine ⟨φ.toMonoidHom.comp α, φ.surjective.comp hα, ?_,
    (AddEquiv.toMultiplicative ψ).toMonoidHom.comp β,
    (AddEquiv.toMultiplicative ψ).surjective.comp hβ, ?_, ?_⟩
  · rw [← hker]
    ext x
    simp [MonoidHom.mem_ker]
  · rw [← hβker]
    ext x
    simp [MonoidHom.mem_ker]
  · intro ℓ u v huv x hx
    have hx' : ψ (Multiplicative.toAdd (β u)) = (x : altHeart n) := hx
    change ψ (Multiplicative.toAdd (β v)) = _
    rw [heq ℓ u v huv]
    exact hψ (α ℓ) _ x hx'

theorem false_of_invariant_addSubgroup [Finite G] {L : Subgroup G} (hL : IsShort L) {ι : Type}
    [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι (ZMod 2))} (h : IsMatrixType L H)
    (A : AddSubgroup (ι → ZMod 2)) (hA0 : A ≠ ⊥) (hA1 : A ≠ ⊤)
    (hAinv : ∀ g ∈ H, ∀ w ∈ A, ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w ∈ A) :
    False := by
  obtain ⟨α, -, -, β, hβ, hβker, heq⟩ := h
  let W : Subgroup G := ((AddSubgroup.toSubgroup A).comap β).map (blockU L).subtype
  have hmem : ∀ u : blockU L, (u : G) ∈ W ↔ Multiplicative.toAdd (β u) ∈ A := fun u =>
    (Subgroup.mem_map_iff_mem (blockU L).subtype_injective).trans Iff.rfl
  have hWU : W ≤ blockU L := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hZW : blockZ L ≤ W := by
    intro z hz
    have hzU : z ∈ blockU L := blockZ_le_blockU L hz
    have hk : (⟨z, hzU⟩ : blockU L) ∈ β.ker := by
      rw [hβker]
      exact hz
    have h1 : β ⟨z, hzU⟩ = 1 := hk
    refine (hmem ⟨z, hzU⟩).2 ?_
    rw [h1]
    exact A.zero_mem
  have hconj : ∀ ℓ ∈ L, ∀ x ∈ W, ℓ * x * ℓ⁻¹ ∈ W := by
    rintro ℓ hℓ _ ⟨u, hu, rfl⟩
    have hv : ℓ * (u : G) * ℓ⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.QuasithinUnique.C1.le_normalizer_blockU L hℓ) u).mp u.2
    refine (hmem ⟨_, hv⟩).2 ?_
    rw [heq ⟨ℓ, hℓ⟩ u ⟨_, hv⟩ rfl]
    exact hAinv _ (α ⟨ℓ, hℓ⟩).2 _ hu
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj ℓ hℓ x, fun hx => ?_⟩
    have := hconj ℓ⁻¹ (L.inv_mem hℓ) _ hx
    simpa [mul_assoc] using this
  rcases hL.irreducible W hZW hWU hLW with hW | hW
  · obtain ⟨a, haA, ha0⟩ : ∃ a ∈ A, a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hA0 ((AddSubgroup.eq_bot_iff_forall A).2 hcon)
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd a)
    have huW : (u : G) ∈ W := (hmem u).2 (by rw [hu]; exact haA)
    rw [hW] at huW
    have hk : u ∈ β.ker := by
      rw [hβker]
      exact huW
    have h1 : β u = 1 := hk
    rw [hu] at h1
    exact ha0 (by simpa using congrArg Multiplicative.toAdd h1)
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ A := by
      by_contra hcon
      push Not at hcon
      exact hA1 (eq_top_iff.2 fun w _ => hcon w)
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have huW : (u : G) ∈ W := by
      rw [hW]
      exact u.2
    rw [hmem u, hu] at huW
    exact hw huW

theorem false_of_isMatrixType_of_isEmpty {L : Subgroup G} (hL : IsShort L) {ι : Type}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι] {H : Subgroup (GL ι (ZMod 2))}
    (h : IsMatrixType L H) : False := by
  obtain ⟨-, -, -, β, -, hβker, -⟩ := h
  have hle : blockU L ≤ blockZ L := by
    intro u hu
    have hk : (⟨u, hu⟩ : blockU L) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      exact isEmptyElim i
    rw [hβker] at hk
    exact hk
  exact absurd hle (not_le_of_gt hL.blockZ_lt_blockU)

end CFSG.RankThree.PartTwo.Sec19.SimsItem316Small
