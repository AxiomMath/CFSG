module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.StatementB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Least
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem leastParabolic_map {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] (φ : G₁ ≃* G₂)
    {U Qα Q₀ : Subgroup G₁} {S : Subgroup G₂} (hUS : U.map φ.toMonoidHom = S)
    (hpar : IsParabolicTwo G₁ Qα) (hUQ : U ≤ Qα) (hnot : ¬ Qα ≤ Q₀)
    (hleast : ∀ P : Subgroup G₁, IsParabolicTwo G₁ P → U ≤ P → ¬ P ≤ Q₀ → Qα ≤ P) :
    IsParabolicTwo G₂ (Qα.map φ.toMonoidHom) ∧ S ≤ Qα.map φ.toMonoidHom ∧
      ¬ Qα.map φ.toMonoidHom ≤ Q₀.map φ.toMonoidHom ∧
      ∀ P : Subgroup G₂, IsParabolicTwo G₂ P → S ≤ P → ¬ P ≤ Q₀.map φ.toMonoidHom →
        Qα.map φ.toMonoidHom ≤ P := by
  refine ⟨IsParabolicTwo.map hpar φ.toMonoidHom φ.surjective, ?_, ?_, ?_⟩
  · rw [← hUS]
    exact Subgroup.map_mono hUQ
  · intro hle
    exact hnot ((Subgroup.map_le_map_iff_of_injective φ.injective).1 hle)
  · intro P hparP hSP hnotP
    let P' : Subgroup G₁ := P.comap φ.toMonoidHom
    have hparP' : IsParabolicTwo G₁ P' :=
      IsParabolicTwo.comap φ.toMonoidHom φ.surjective hparP
    have hUP' : U ≤ P' := by
      intro u hu
      exact hSP (hUS ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hu)
    have hnotP' : ¬ P' ≤ Q₀ := by
      intro hle
      apply hnotP
      intro y hy
      have hy' : φ.symm y ∈ P' :=
        Subgroup.mem_comap.mpr (by simpa using hy)
      have hq : φ.symm y ∈ Q₀ := hle hy'
      simpa using Subgroup.mem_map_of_mem φ.toMonoidHom hq
    have hQαP' : Qα ≤ P' := hleast P' hparP' hUP' hnotP'
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_comap.mp (hQαP' hx)

theorem symm_mem_Hinf_inf_of_mem_map {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (φ : G₁ ≃* G₂) {A B : Subgroup G₁} {t : G₂}
    (ht : t ∈ Hinf (A.map φ.toMonoidHom) ⊓ B.map φ.toMonoidHom) : φ.symm t ∈ Hinf A ⊓ B := by
  rw [Subgroup.mem_inf] at ht ⊢
  obtain ⟨htA, htB⟩ := ht
  constructor
  · rwa [← Hinf_map φ.toMonoidHom A, Subgroup.mem_map_equiv] at htA
  · rwa [Subgroup.mem_map_equiv] at htB

theorem kAdjAt_of_model {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n m : ℕ)
    (hm : m = n ∨ m = 2 * n ∨ (n = 2 * m ∧ IsSUn ↥H 4 m ∧ NatSUn H ⊤ ⊥ 4 m))
    {Γ : Type} [Group Γ] [Finite Γ] (U Qα Q₀ : Subgroup Γ)
    (hmodel : ∀ S : Sylow 2 ↥H, ∃ φ : Γ ≃* ↥H,
      U.map φ.toMonoidHom = (S : Subgroup ↥H) ∧ KTabD.pointStab H S = Q₀.map φ.toMonoidHom)
    (hpar : IsParabolicTwo Γ Qα) (hUQ : U ≤ Qα) (hnot : ¬ Qα ≤ Q₀)
    (hleast : ∀ P : Subgroup Γ, IsParabolicTwo Γ P → U ≤ P → ¬ P ≤ Q₀ → Qα ≤ P)
    (hline : ∀ r : ℕ, r.Prime → r ≠ 2 →
      ((∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨ (∃ k : ℕ, n = 2 ^ k ∧ r = 3)) →
      ∀ t ∈ Hinf Qα ⊓ Q₀, orderOf t = r → KAdjConcl (Hinf Q₀) t r m) :
    KAdjAt W H n := by
  unfold KAdjAt
  intro S
  obtain ⟨φ, hφU, hφP⟩ := hmodel S
  intro ℓ Pℓ Kstar _ Tstar hTH hT hST Good Pstar hmin r hr hr2 hrcond t ht hord _
  have hPℓ_eq : Pℓ = Q₀.map φ.toMonoidHom := by
    rw [show Pℓ = KTabD.pointStab H S from rfl, hφP]
  have hPℓ_fix : ∀ u ∈ Tstar,
      (Pℓ.map H.subtype).map (MulAut.conj u).toMonoidHom = Pℓ.map H.subtype :=
    map_conj_stabilizer_fixedPoint_eq H S Tstar hTH hT hST
  obtain ⟨hpar', hSP', hnot', hleast'⟩ := leastParabolic_map φ hφU hpar hUQ hnot hleast
  have hnotPα : ¬ Qα.map φ.toMonoidHom ≤ Pℓ := by
    rwa [hPℓ_eq]
  have hle : ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P → (S : Subgroup ↥H) ≤ P →
      ¬ P ≤ Pℓ → Qα.map φ.toMonoidHom ≤ P := by
    intro P hparP hSP hnotP
    exact hleast' P hparP hSP (by rwa [hPℓ_eq] at hnotP)
  have hPeq : Pstar = Qα.map φ.toMonoidHom :=
    minimal_good_eq_of_least_parabolic H S Pℓ Tstar hTH hT hST hPℓ_fix hpar' hSP'
      hnotPα hle hmin
  refine ⟨m, hm, ?_⟩
  change KAdjConcl Kstar t r m
  have ht' : t ∈ Hinf (Qα.map φ.toMonoidHom) ⊓ Q₀.map φ.toMonoidHom := by
    rwa [hPeq, hPℓ_eq] at ht
  have ht₀ : φ.symm t ∈ Hinf Qα ⊓ Q₀ :=
    symm_mem_Hinf_inf_of_mem_map (A := Qα) (B := Q₀) φ ht'
  have hord₀ : orderOf (φ.symm t) = r := by
    rw [← MulEquiv.orderOf_eq φ (φ.symm t), MulEquiv.apply_symm_apply, hord]
  have hmodel_concl : KAdjConcl (Hinf Q₀) (φ.symm t) r m :=
    hline r hr hr2 hrcond (φ.symm t) ht₀ hord₀
  have hmap_concl : KAdjConcl ((Hinf Q₀).map φ.toMonoidHom) (φ (φ.symm t)) r m :=
    kAdjConcl_map φ hmodel_concl
  have hKstar : Kstar = (Hinf Q₀).map φ.toMonoidHom := by
    show Hinf Pℓ = (Hinf Q₀).map φ.toMonoidHom
    rw [hPℓ_eq, Hinf_map φ.toMonoidHom Q₀]
  rw [hKstar, ← MulEquiv.apply_symm_apply φ t]
  exact hmap_concl

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
