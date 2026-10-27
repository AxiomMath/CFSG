module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24C4Frame
import TauCeti.FieldTheory.Finite.Four
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Frame
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

@[expose] def IsLin (φ : MulAut (Vtil V₀ V hV)) : Prop :=
  ∀ (c : F.K) (x : Fin 4 → F.K), F.rho φ (c • x) = c • F.rho φ x

@[expose] def IsSemi (φ : MulAut (Vtil V₀ V hV)) : Prop :=
  ∀ (c : F.K) (x : Fin 4 → F.K), F.rho φ (c • x) = c ^ 2 • F.rho φ x

theorem exists_omega :
    ∃ ω : F.K, ω ^ 2 + ω + 1 = 0 ∧ ∀ c : F.K, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  classical
  haveI : Fintype F.K := Fintype.ofFinite F.K
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four F.card_K
  refine ⟨ω, hω, ?_⟩
  intro c
  have hc : c ∈ ({0, 1, ω, ω ^ 2} : Finset F.K) := by
    rw [← TauCeti.univ_eq_zero_one_root_sq (F := F.K) F.card_K hω]
    exact Finset.mem_univ c
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hc

theorem isLin_or_isSemi {φ : MulAut (Vtil V₀ V hV)}
    (hφ : φ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) :
    F.IsLin φ ∨ F.IsSemi φ := by
  obtain ⟨θ, hθ⟩ := F.rho_semilinear_of_mem_normalizer hφ
  obtain ⟨ω, hω, hspan⟩ := F.exists_omega
  haveI : CharP F.K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero F.two_eq_zero
  have hθpoly : θ ω ^ 2 + θ ω + 1 = 0 := by
    have h := congrArg θ hω
    simpa using h
  have hcases : θ ω = ω ∨ θ ω = ω ^ 2 := by
    rcases hspan (θ ω) with h | h | h | h
    · exfalso
      rw [h] at hθpoly
      simpa using hθpoly
    · exfalso
      rw [h] at hθpoly
      rw [one_pow, CharTwo.add_self_eq_zero, zero_add] at hθpoly
      exact one_ne_zero hθpoly
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with hcase | hcase
  · left
    have hfix : ∀ c, θ c = c := by
      intro c
      rcases hspan c with h | h | h | h
      · rw [h, map_zero]
      · rw [h, map_one]
      · rw [h]; exact hcase
      · rw [h, map_pow, hcase]
    intro c x
    rw [hθ c x, hfix c]
  · right
    have hsq : ∀ c, θ c = c ^ 2 := by
      intro c
      rcases hspan c with h | h | h | h
      · rw [h, map_zero]; simp
      · rw [h, map_one]; simp
      · rw [h]; exact hcase
      · rw [h, map_pow, hcase]
    intro c x
    rw [hθ c x, hsq c]

theorem not_isSemi_of_isLin {φ : MulAut (Vtil V₀ V hV)} (hl : F.IsLin φ) (hs : F.IsSemi φ) :
    False := by
  obtain ⟨ω, hω, -⟩ := F.exists_omega
  haveI : CharP F.K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero F.two_eq_zero
  let x : Fin 4 → F.K := Pi.single 0 1
  have hx0 : x ≠ 0 := by
    intro h
    have h1 : (1 : F.K) = 0 := by simpa [x] using congrFun h 0
    exact one_ne_zero h1
  have hy0 : F.rho φ x ≠ 0 := by
    intro hy
    exact hx0 ((F.rho φ).injective (by rw [hy]; simp))
  have h1 : ω • F.rho φ x = ω ^ 2 • F.rho φ x := by
    rw [← hl ω x, ← hs ω x]
  have h2 : (ω ^ 2 + ω) • F.rho φ x = 0 := by
    rw [add_smul, h1]
    exact CharTwo.add_self_eq_zero _
  have hsum : ω ^ 2 + ω = 1 := CharTwo.add_eq_zero.mp hω
  exact hy0 (by rw [← one_smul F.K (F.rho φ x), ← hsum]; exact h2)

theorem isLin_of_mem_lBar {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ lBar V₀ V hV L) :
    F.IsLin φ := by
  obtain ⟨γ, hγ⟩ := F.π.surjective ⟨φ, hφ⟩
  have hφeq : (F.π γ : MulAut (Vtil V₀ V hV)) = φ := congrArg Subtype.val hγ
  have hrho : ∀ x : Fin 4 → F.K,
      F.rho φ x = ((γ : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x := by
    intro x
    have h := F.rho_vec (F.π γ) (F.ofVec x)
    rw [F.vec_ofVec, F.vec_action, F.vec_ofVec,
      CFSG.ClassicalGroups.Unitary.smul_def] at h
    rw [hφeq] at h
    exact h
  intro c x
  rw [hrho (c • x), hrho x, Matrix.mulVec_smul]

theorem mem_lBar_of_isLin {φ : MulAut (Vtil V₀ V hV)}
    (hφ : φ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) (hφ2 : φ * φ = 1)
    (hl : F.IsLin φ) : φ ∈ lBar V₀ V hV L := by
  have hK : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  let lin : (Fin 4 → F.K) →ₗ[F.K] (Fin 4 → F.K) :=
    { toFun := F.rho φ
      map_add' := fun x y => map_add (F.rho φ) x y
      map_smul' := hl }
  let A : Matrix (Fin 4) (Fin 4) F.K := LinearMap.toMatrix' lin
  have hA : ∀ x, A *ᵥ x = F.rho φ x := by
    intro x
    show LinearMap.toMatrix' lin *ᵥ x = F.rho φ x
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hlinlin : lin * lin = 1 := by
    refine LinearMap.ext fun x => ?_
    change F.rho φ (F.rho φ x) = x
    rw [← F.rho_mul φ φ x, hφ2]
    simp [UFrame.rho]
  have hAA : A * A = 1 := by
    show LinearMap.toMatrix' lin * LinearMap.toMatrix' lin = 1
    rw [← LinearMap.toMatrix'_mul, hlinlin, LinearMap.toMatrix'_one]
  have hπrho : ∀ (δ : ↥(SUid F.σ 4)) (x : Fin 4 → F.K),
      F.rho (F.π δ) x = ((δ : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x := by
    intro δ x
    have h := F.rho_vec (F.π δ) (F.ofVec x)
    rw [F.vec_ofVec, F.vec_action, F.vec_ofVec,
      CFSG.ClassicalGroups.Unitary.smul_def] at h
    exact h
  have hnorm : ∀ g ∈ StatedSU 4 (2 ^ 1) F.K,
      ∃ g' ∈ StatedSU 4 (2 ^ 1) F.K, ∀ x : Fin 4 → F.K,
        A *ᵥ (((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x) =
          ((g' : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ (A *ᵥ x) := by
    intro g hg
    have hgSU : g ∈ SUid F.σ 4 := by rw [F.suid_eq_statedSU]; exact hg
    let γ : ↥(SUid F.σ 4) := ⟨g, hgSU⟩
    have hmem : φ * (F.π γ) * φ⁻¹ ∈ lBar V₀ V hV L := by
      have h := (Subgroup.mem_set_normalizer_iff.1 hφ (F.π γ)).1 (F.π γ).2
      simpa using h
    let γ' : ↥(SUid F.σ 4) := F.π.symm ⟨φ * (F.π γ) * φ⁻¹, hmem⟩
    have hπγ' : (F.π γ' : MulAut (Vtil V₀ V hV)) = φ * (F.π γ) * φ⁻¹ := by
      simp [γ']
    refine ⟨(γ' : GL (Fin 4) F.K), ?_, ?_⟩
    · rw [← F.suid_eq_statedSU]; exact γ'.2
    · intro x
      have hconj : φ * (F.π γ) = (F.π γ') * φ := by
        rw [hπγ']; group
      have hγg : ((γ : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) =
          ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) := rfl
      rw [← hγg]
      calc A *ᵥ (((γ : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x)
          = A *ᵥ (F.rho (F.π γ) x) := by rw [hπrho γ x]
        _ = F.rho φ (F.rho (F.π γ) x) := by rw [hA (F.rho (F.π γ) x)]
        _ = F.rho (φ * F.π γ) x := (F.rho_mul φ (F.π γ) x).symm
        _ = F.rho ((F.π γ') * φ) x := by rw [hconj]
        _ = F.rho (F.π γ') (F.rho φ x) := F.rho_mul (F.π γ') φ x
        _ = ((γ' : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ (F.rho φ x) :=
              hπrho γ' (F.rho φ x)
        _ = ((γ' : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ (A *ᵥ x) := by
              rw [hA x]
  obtain ⟨g₀, hg₀SU, hg₀A⟩ := exists_mem_statedSU_of_normalizes hK A hAA hnorm
  let γ₀ : ↥(SUid F.σ 4) := ⟨g₀, by rw [F.suid_eq_statedSU]; exact hg₀SU⟩
  have hγ₀A : ((γ₀ : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) = A := hg₀A
  have hrhoeq : F.rho (F.π γ₀) = F.rho φ := by
    ext x
    rw [hπrho γ₀ x, hγ₀A, hA x]
  have heq : (F.π γ₀ : MulAut (Vtil V₀ V hV)) = φ := by
    refine MulEquiv.ext fun w => F.vec_injective ?_
    rw [← F.rho_vec (F.π γ₀) w, ← F.rho_vec φ w, hrhoeq]
  rw [← heq]
  exact (F.π γ₀).2

theorem isLin_mul_of_isSemi {φ ψ : MulAut (Vtil V₀ V hV)} (hφ : F.IsSemi φ) (hψ : F.IsSemi ψ) :
    F.IsLin (φ * ψ) := by
  haveI : Fintype F.K := Fintype.ofFinite F.K
  have h4 : ∀ c : F.K, (c ^ 2) ^ 2 = c := by
    intro c
    rw [← pow_mul, show (2 * 2 : ℕ) = Fintype.card F.K by
      rw [Fintype.card_eq_nat_card, F.card_K]]
    exact FiniteField.pow_card c
  intro c x
  rw [F.rho_mul φ ψ (c • x), hψ c x, hφ (c ^ 2) (F.rho ψ x), ← F.rho_mul φ ψ x, h4 c]

theorem exists_isSemi_of_not_le {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) (hout : ¬ E ≤ lBar V₀ V hV L) : ∃ τ ∈ E, F.IsSemi τ := by
  obtain ⟨φ, hφE, hφout⟩ := IsConcreteLE.not_le_iff_exists.1 hout
  have hφN : φ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := hEN hφE
  have hφ2 : φ * φ = 1 := by
    have h := hE2.2 φ hφE
    rwa [pow_two] at h
  rcases F.isLin_or_isSemi hφN with hl | hs
  · exact absurd (F.mem_lBar_of_isLin hφN hφ2 hl) hφout
  · exact ⟨φ, hφE, hs⟩

theorem card_le_two_mul_card_inf {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) {τ : MulAut (Vtil V₀ V hV)} (hτE : τ ∈ E) (hτ : F.IsSemi τ) :
    Nat.card E ≤
      2 * Nat.card (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) := by
  let E₀ : Subgroup (MulAut (Vtil V₀ V hV)) := E ⊓ lBar V₀ V hV L
  have hτ2 : τ * τ = 1 := by
    have h := hE2.2 τ hτE
    rwa [pow_two] at h
  have hsquare : ∀ φ ∈ E, φ * φ = 1 := by
    intro φ hφ
    have h := hE2.2 φ hφ
    rwa [pow_two] at h
  let f : ↥E₀ ⊕ ↥E₀ → ↥E := fun s =>
    match s with
    | Sum.inl y => ⟨y.1, y.2.1⟩
    | Sum.inr y => ⟨τ * y.1, E.mul_mem hτE y.2.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨φ, hφE⟩
    rcases F.isLin_or_isSemi (hEN hφE) with hl | hs
    · refine ⟨Sum.inl ⟨φ, ⟨hφE, ?_⟩⟩, Subtype.ext rfl⟩
      exact F.mem_lBar_of_isLin (hEN hφE) (hsquare φ hφE) hl
    · have hlin : F.IsLin (τ * φ) := F.isLin_mul_of_isSemi hτ hs
      have hcomm : τ * φ = φ * τ := hE2.1 τ hτE φ hφE
      have hmemN : τ * φ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
        hEN (E.mul_mem hτE hφE)
      have hsq : (τ * φ) * (τ * φ) = 1 := by
        calc (τ * φ) * (τ * φ) = τ * (φ * τ) * φ := by group
          _ = τ * (τ * φ) * φ := by rw [← hcomm]
          _ = (τ * τ) * (φ * φ) := by group
          _ = 1 := by rw [hτ2, hsquare φ hφE, one_mul]
      have hmemL : τ * φ ∈ lBar V₀ V hV L := F.mem_lBar_of_isLin hmemN hsq hlin
      refine ⟨Sum.inr ⟨τ * φ, ⟨E.mul_mem hτE hφE, hmemL⟩⟩, ?_⟩
      show (⟨τ * (τ * φ), E.mul_mem hτE (E.mul_mem hτE hφE)⟩ : ↥E) = ⟨φ, hφE⟩
      refine Subtype.ext ?_
      change τ * (τ * φ) = φ
      rw [← mul_assoc, hτ2, one_mul]
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sum] at hcard
  calc Nat.card E ≤ Nat.card E₀ + Nat.card E₀ := hcard
    _ = 2 * Nat.card E₀ := (two_mul _).symm
    _ = 2 * Nat.card (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) := rfl

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
