module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckMat
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCover
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCoverPow
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCoverE

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly Equiv

theorem sporKRest_cover_of_permModelMat {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkMat (φ a) (φ b) sylowOrder d = true) : SporKRestCover p K :=
  sporKRest_cover_of_permModel φ hφ a b hab hp sylowOrder hord d
    (PermCover.check_of_spec (PermCover.checkMat_sound hcheck))

theorem sporKRest_cover_of_permModelPowMat {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkPowMat p (φ a) (φ b) sylowOrder d = true) : SporKRestCover p K :=
  sporKRest_cover_of_permModelPow φ hφ a b hab hp sylowOrder hord d
    (PermCover.checkPow_of_spec (PermCover.checkPowMat_sound hcheck))

theorem sporKRest_cover_of_permModelEMat {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.DataE)
    (hcheck : PermCover.checkEMat p (φ a) (φ b) sylowOrder d = true) : SporKRestCover p K :=
  sporKRest_cover_of_permModelE φ hφ a b hab hp sylowOrder hord d
    (PermCover.checkE_of_spec (PermCover.checkEMat_sound hcheck))

theorem sporKRest_toPermHom_injective {K : Type} [Group K] {n : ℕ} [MulAction K (Fin n)]
    (hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1) :
    Function.Injective (MulAction.toPermHom K (Fin n)) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => hfaith g fun i => ?_
  simpa using congrArg (fun σ : Perm (Fin n) => σ i) hg

theorem sporKRest_cover_of_actionMat {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1) (a b : K) (α β : Perm (Fin n))
    (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkMat α β sylowOrder d = true) : SporKRestCover p K := by
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  refine sporKRest_cover_of_permModelMat (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab hp sylowOrder hord d ?_
  rw [hφa, hφb]
  exact hcheck

theorem sporKRest_cover_of_actionPowMat {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1) (a b : K) (α β : Perm (Fin n))
    (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkPowMat p α β sylowOrder d = true) : SporKRestCover p K := by
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  refine sporKRest_cover_of_permModelPowMat (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab hp sylowOrder hord d ?_
  rw [hφa, hφb]
  exact hcheck

theorem sporKRest_cover_of_actionEMat {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1) (a b : K) (α β : Perm (Fin n))
    (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.DataE)
    (hcheck : PermCover.checkEMat p α β sylowOrder d = true) : SporKRestCover p K := by
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  refine sporKRest_cover_of_permModelEMat (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab hp sylowOrder hord d ?_
  rw [hφa, hφb]
  exact hcheck

end CFSG.StandardType.SporadicShape
