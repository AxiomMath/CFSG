module

public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.RankThree.PartOne.KE.A2Block
public import CFSG.RankThree.PartOne.KE.TwoA2Exchange
public import CFSG.RankThree.PartOne.KE.SLnShapeHom
public import CFSG.RankThree.PartOne.KE.A2Shape

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Generic

variable {τ : Tag} {L : Type} [Field L]

theorem rootSpan_commute_of_orth
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {S₁ S₂ : Set (Fin τ.rank → ℤ)}
    (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) :
    ∀ x ∈ rootSpan τ L S₁, ∀ y ∈ rootSpan τ L S₂, x * y = y * x := by
  have h1 : ∀ α ∈ S₁, ∀ β ∈ S₂, ∀ x ∈ rootSubgroup τ L α, ∀ y ∈ rootSubgroup τ L β,
      x * y = y * x := fun α hα β hβ x hx y hy =>
    (simply_laced_orthogonal_root_commutation τ hτ).2 L α β (hS₁ α hα) (hS₂ β hβ) (horth α hα β hβ)
      x hx y hy
  have h2 : ∀ α ∈ S₁, rootSpan τ L S₂ ≤ Subgroup.centralizer (rootSubgroup τ L α : Set (ModGL τ L)) :=
    fun α hα => iSup₂_le fun β hβ y hy =>
      Subgroup.mem_centralizer_iff.2 fun x hx => h1 α hα β hβ x hx y hy
  have h3 : rootSpan τ L S₁ ≤ Subgroup.centralizer (rootSpan τ L S₂ : Set (ModGL τ L)) :=
    iSup₂_le fun α hα => Subgroup.le_centralizer_iff.2 (h2 α hα)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h3 hx) y hy).symm

theorem twist_pinnedX
    (Fr : L →+* L) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (n : ModGL τ L)
    (hn : n ∈ monomialSubgroup τ L)
    (hnW : ∀ u, weylQuotientHom τ L ⟨n, hn⟩ • u = M *ᵥ u) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    ∃ μ : Lˣ, ∀ c : L, n * Units.map (entrywiseHom Fr) (pinnedX τ L α c) * n⁻¹ =
      pinnedX τ L (M *ᵥ α) ((μ : L) * Fr c) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hα
  refine ⟨μ, fun c => ?_⟩
  rw [units_map_entrywiseHom_pinnedX, hμ, hnW]

theorem twist_rootSpan_le
    (Fr : L →+* L) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (n : ModGL τ L)
    (hn : n ∈ monomialSubgroup τ L)
    (hnW : ∀ u, weylQuotientHom τ L ⟨n, hn⟩ • u = M *ᵥ u) {S S' : Set (Fin τ.rank → ℤ)}
    (hS : ∀ r ∈ S, IsRoot τ r) (hmap : ∀ α ∈ S, M *ᵥ α ∈ S') :
    ∀ x ∈ rootSpan τ L S, n * Units.map (entrywiseHom Fr) x * n⁻¹ ∈ rootSpan τ L S' := by
  set Tm : ModGL τ L →* ModGL τ L :=
    (MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr)) with hTm
  have hle : rootSpan τ L S ≤ (rootSpan τ L S').comap Tm :=
    iSup₂_le fun α hα x hx => by
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨μ, hμ⟩ := twist_pinnedX Fr M n hn hnW (hS α hα)
      have h1 : Tm (pinnedX τ L α c) = pinnedX τ L (M *ᵥ α) ((μ : L) * Fr c) := by
        rw [← hμ c]
        simp [hTm, MulAut.conj_apply]
      rw [Subgroup.mem_comap, h1]
      exact Subgroup.mem_iSup_of_mem (M *ᵥ α) (Subgroup.mem_iSup_of_mem (hmap α hα)
        (mem_rootSubgroup.2 ⟨_, rfl⟩))
  intro x hx
  have := hle hx
  rw [Subgroup.mem_comap] at this
  simpa [hTm, MulAut.conj_apply] using this

end Generic

section E8

variable {L : Type} [Field L]

theorem e8_two_A2_family [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {k₂ : Type} [Field k₂] [Algebra k₂ L] [IsAlgClosure k₂ L] (hk₂ : Nat.card k₂ = ℓ ^ (2 * f))
    (M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) (n : ModGL Tag.E8 L)
    (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ u, weylQuotientHom Tag.E8 L ⟨n, hn⟩ • u = M *ᵥ u) (v₁ v₂ : WeylGroup Tag.E8)
    (h12 : ∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
      M *ᵥ sigmaRootE8 v₁ i j = sigmaRootE8 v₂ i' j')
    (h21 : ∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
      M *ᵥ sigmaRootE8 v₂ i j = sigmaRootE8 v₁ i' j')
    (hπ₁ : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
      (M * M) *ᵥ sigmaRootE8 v₁ i j = sigmaRootE8 v₁ (π j) (π i))
    (hπ₂ : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
      (M * M) *ᵥ sigmaRootE8 v₂ i j = sigmaRootE8 v₂ (π j) (π i))
    (horth : ∀ α ∈ sigmaSetE8 v₁, ∀ β ∈ sigmaSetE8 v₂,
      α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L),
      IsSigmaFamily n Fr (sigmaSetE8 v₁ ∪ sigmaSetE8 v₂) P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set Fr₂ : L →+* L := Fr.comp Fr with hFr₂def
  have hFr₂ : ∀ c, Fr₂ c = c ^ (ℓ ^ (2 * f)) := fun c => by
    rw [hFr₂def, RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, two_mul]
  have hFr₂bij : Function.Bijective Fr₂ := ⟨Fr₂.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ (2 * f) from pow_pos hℓ.pos _)
    exact ⟨x, by rw [hFr₂, hx]⟩⟩
  set Φ₂ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr₂) with hΦ₂
  set n₂ : ModGL Tag.E8 L := n * Φ n with hn₂
  have hFeFe : ∀ x, Φ (Φ x) = Φ₂ x := fun x => by
    refine Units.ext ?_
    simp only [hΦ, hΦ₂, Units.coe_map]
    exact entrywise_entrywise Fr Fr _
  have hT2 : ∀ x, n₂ * Φ₂ x * n₂⁻¹ = n * Φ (n * Φ x * n⁻¹) * n⁻¹ := fun x => by
    rw [← hFeFe, hn₂, map_mul, map_mul, map_inv]
    group
  have hS : ∀ v : WeylGroup Tag.E8, ∀ r ∈ sigmaSetE8 v, IsRoot Tag.E8 r := fun v r hr => by
    rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    exact isRoot_sigmaRootE8 v hij
  have hmap12 : ∀ α ∈ sigmaSetE8 v₁, M *ᵥ α ∈ sigmaSetE8 v₂ := by
    intro α hα
    rw [sigmaSetE8_eq] at hα
    obtain ⟨i, j, hij, rfl⟩ := hα
    obtain ⟨i', j', hij', h⟩ := h12 i j hij
    rw [h, sigmaSetE8_eq]
    exact ⟨i', j', hij', rfl⟩
  have hmap21 : ∀ α ∈ sigmaSetE8 v₂, M *ᵥ α ∈ sigmaSetE8 v₁ := by
    intro α hα
    rw [sigmaSetE8_eq] at hα
    obtain ⟨i, j, hij, rfl⟩ := hα
    obtain ⟨i', j', hij', h⟩ := h21 i j hij
    rw [h, sigmaSetE8_eq]
    exact ⟨i', j', hij', rfl⟩
  have hT₁₂ := twist_rootSpan_le (L := L) Fr M n hn hnW (hS v₁) hmap12
  have hT₂₁ := twist_rootSpan_le (L := L) Fr M n hn hnW (hS v₂) hmap21
  have hcomm := rootSpan_commute_of_orth (L := L) (τ := Tag.E8) (Or.inr (Or.inr (Or.inr rfl)))
    (hS v₁) (hS v₂) horth
  set Tm : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj n).toMonoidHom.comp Φ with hTm
  have hTapp : ∀ x, Tm x = n * Φ x * n⁻¹ := fun x => by simp [hTm, MulAut.conj_apply]
  have hTinj : Function.Injective Tm :=
    (MulAut.conj n).injective.comp (Units.map_injective (f := entrywiseHom Fr)
      (entrywise_injective Fr))
  have hblock : ∀ (u u' : WeylGroup Tag.E8) (π : Equiv.Perm (Fin 3)),
      (∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
        M *ᵥ sigmaRootE8 u i j = sigmaRootE8 u' i' j') →
      (∀ i j : Fin 3, i ≠ j → (M * M) *ᵥ sigmaRootE8 u i j = sigmaRootE8 u (π j) (π i)) →
      Finite ↥((rootSpan Tag.E8 L (sigmaSetE8 u)) ⊓ twistedFixedPoints n₂ Φ₂) ∧
        CFSG.IsQuasisimple ↥((rootSpan Tag.E8 L (sigmaSetE8 u)) ⊓ twistedFixedPoints n₂ Φ₂) ∧
        ∀ y ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (sigmaSetE8 u),
          (∀ w ∈ (rootSpan Tag.E8 L (sigmaSetE8 u)) ⊓ twistedFixedPoints n₂ Φ₂, y * w = w * y) →
          y ∈ torusGroup Tag.E8 L ∧
            y ∈ Subgroup.centralizer (rootSpan Tag.E8 L (sigmaSetE8 u) : Set (ModGL Tag.E8 L)) := by
    intro u u' π hexch hpi
    choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) =>
      rhoSigmaE8_transvection (L := L) u i j hij
    have hΨ : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        (Tm.comp Tm) (pinnedX Tag.E8 L (sigmaRootE8 u i j) c) =
          pinnedX Tag.E8 L (sigmaRootE8 u (π j) (π i)) ((b : L) * Fr₂ c) := by
      intro i j hij
      obtain ⟨i', j', hij', hMα⟩ := hexch i j hij
      obtain ⟨μ, hμ⟩ := twist_pinnedX Fr M n hn hnW (isRoot_sigmaRootE8 u hij)
      have hroot' : IsRoot Tag.E8 (M *ᵥ sigmaRootE8 u i j) := by
        rw [hMα]
        exact isRoot_sigmaRootE8 u' hij'
      obtain ⟨μ', hμ'⟩ := twist_pinnedX Fr M n hn hnW hroot'
      refine ⟨μ' * Units.map (Fr : L →* L) μ, fun c => ?_⟩
      have e1 : ∀ x, (Tm.comp Tm) x = Tm (Tm x) := fun x => rfl
      rw [e1, hTapp, hTapp, hμ c, hμ', Matrix.mulVec_mulVec, hpi i j hij]
      congr 1
      simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, map_mul, hFr₂def,
        RingHom.comp_apply]
      ring
    obtain ⟨Φ', hΦ'1, b, hshape⟩ := exists_aut_of_rootData_hom (rhoSigmaE8 L u)
      (rhoSigmaE8_injective u) (sigmaRootE8 u) ε hε Fr₂ hFr₂bij (Tm.comp Tm)
      (hTinj.comp hTinj) (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
      (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hΨ
    have hΦ'2 : ∀ X, n₂ * Φ₂ (rhoSigmaE8 L u X) * n₂⁻¹ = rhoSigmaE8 L u (Φ' X) := fun X => by
      rw [hT2, ← hTapp, ← hTapp]
      exact hΦ'1 X
    have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ (2 * f)) :=
      fun i j hij t => by rw [hshape i j hij t, hFr₂]
    have hq2 : 2 < ℓ ^ (2 * f) := by
      have h1 : 2 ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
      have h2 : ℓ ^ 2 ≤ ℓ ^ (2 * f) := Nat.pow_le_pow_right hℓ.pos (by omega)
      omega
    have htor : ∀ b' : Fin Tag.E8.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
        rootDiagUnit Tag.E8 b' * rhoSigmaE8 L u A * (rootDiagUnit Tag.E8 b')⁻¹ =
          rhoSigmaE8 L u (conjDiag3 d A) := fun b' =>
      ⟨fun i => rootChar b' (wbE8 u i), fun A => rhoSigmaE8_torus u b' A⟩
    have hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
        rhoSigmaE8 L u A ∈ torusGroup Tag.E8 L := fun A hA => rhoSigmaE8_diagonal u A hA
    have := a2_block_unitary (f := 2 * f) hℓ (by omega) hk₂ hq2 (hS u) (rhoSigmaE8 L u)
      (rhoSigmaE8_injective u) (rhoSigmaE8_range u) htor hdiag Fr₂ n₂ Φ' hΦ'2 π b hshape'
    rwa [rhoSigmaE8_range] at this
  obtain ⟨π₁, hπ₁'⟩ := hπ₁
  obtain ⟨π₂, hπ₂'⟩ := hπ₂
  obtain ⟨hfin₁, hq₁, hc₁⟩ := hblock v₁ v₂ π₁ h12 hπ₁'
  obtain ⟨-, -, hc₂⟩ := hblock v₂ v₁ π₂ h21 hπ₂'
  exact two_family_exchange Fr n (hS v₁) (hS v₂) hT₁₂ hT₂₁ hcomm n₂ Φ₂ hT2 hfin₁ hq₁ hc₁ hc₂
end E8

end CFSG.RankThree.PartOne.KE
