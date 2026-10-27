module

public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KE.CTBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL diagUnitOne coe_diagUnitOne)
open CFSG.RankThree.QuadraticSL2 (eq_scalar_of_commute commute_of_conjSL_eq)
open CFSG.RankThree.Lattice (pair)
open scoped Matrix Polynomial

section Centralizer

variable {τ : Tag} {L : Type} [Field L]

theorem rootDiagUnit_mem_centralizer_iff {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (a : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a ∈ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L)) ↔
      rootChar a θ = 1 := by
  have hinj : Function.Injective (rootSL2 τ L θ) := rootSL2_injective_of_field θ
  have hconj := rootDiagUnit_conj_rootSL2 (K := L) a hθ
  constructor
  · intro h
    have hc : ∀ A : SL2 L, conjSL (diagUnitOne (rootChar a θ)) A = A := fun A => by
      apply hinj
      rw [← hconj A]
      have h1 := Subgroup.mem_centralizer_iff.1 h (rootSL2 τ L θ A) ⟨A, rfl⟩
      rw [← h1, mul_inv_cancel_right]
    have hu := commute_of_conjSL_eq _ (hc (uSL 1))
    have hv := commute_of_conjSL_eq _ (hc (vSL 1))
    have hsc := eq_scalar_of_commute _ hu hv
    have h11 := congrFun (congrFun hsc 1) 1
    rw [coe_diagUnitOne] at h11
    simp [Matrix.scalar_apply] at h11
    exact Units.ext h11.symm
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    have hD : diagUnitOne (rootChar a θ) = 1 := by
      rw [h]
      apply Units.ext
      rw [coe_diagUnitOne]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h1 := hconj A
    rw [hD, CFSG.RankThree.Classical.conjSL_one] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem subtorusA1_eq_map_fixedBlockTuples {n : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
    (hT : twistedTorusOf n Φ = (fixedCharTuples M Fr).map (rootDiagUnitHom τ L))
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    subtorusA1 n Φ θ = (fixedBlockTuples M Fr {θ}).map (rootDiagUnitHom τ L) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [hT] at hx1
    obtain ⟨a, ha, rfl⟩ := hx1
    refine ⟨a, ⟨ha, fun u hu => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact (rootDiagUnit_mem_centralizer_iff hθ a).1 hx2
  · rintro ⟨a, ⟨ha, hθa⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact ⟨a, ha, rfl⟩
    · exact (rootDiagUnit_mem_centralizer_iff hθ a).2 (hθa θ rfl)

end Centralizer

structure A1BlockData (τ : Tag) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (θ : Fin τ.rank → ℤ) where
  c : Fin τ.rank → Fin τ.rank → ℤ
  β : Fin τ.rank → ℤ
  P : ℤ[X]
  hk : 1 < τ.rank
  hlin : LinearIndependent ℤ c
  hspan : Submodule.span ℤ (Set.range c) = ⊤
  hc0 : c ⟨0, lt_trans zero_lt_one hk⟩ = θ
  hβ : ∀ j : Fin τ.rank, 1 ≤ (j : ℕ) → c j = (M ^ ((j : ℕ) - 1)) *ᵥ β
  hθM : ∃ e : ℤ, M *ᵥ θ = e • θ
  hP : P.Monic
  hPdeg : P.natDegree = τ.rank - 1
  hrel : (Polynomial.aeval M P) *ᵥ β = 0
  hdet : P.coeff 0 = 1 ∨ P.coeff 0 = -1

namespace A1BlockData

variable {τ : Tag} {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {θ : Fin τ.rank → ℤ}

theorem zero_lt_rank (D : A1BlockData τ M θ) : 0 < τ.rank := lt_trans zero_lt_one D.hk

theorem image_lt_one (D : A1BlockData τ M θ) :
    D.c '' {i : Fin τ.rank | (i : ℕ) < 1} = {θ} := by
  ext u
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i = ⟨0, D.zero_lt_rank⟩ := Fin.ext (by simpa using hi)
    subst this
    exact D.hc0
  · rintro rfl
    exact ⟨⟨0, D.zero_lt_rank⟩, by simp, D.hc0⟩

theorem isCyclic_and_card (D : A1BlockData τ M θ) {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hne : D.P.eval (q : ℤ) ≠ 0) :
    IsCyclic (fixedBlockTuples M Fr {θ}) ∧
      Nat.card (fixedBlockTuples M Fr {θ}) = (D.P.eval (q : ℤ)).natAbs := by
  have h := isCyclic_and_card_fixedBlockTuples (L := L) M D.c (k := 1) D.hk D.β D.hlin D.hspan
    D.hβ ?_ D.P D.hP D.hPdeg ?_ Fr hFr hℓ hℓq D.hdet hne
  · rw [D.image_lt_one] at h
    exact h
  · intro j hj
    have hj0 : j = ⟨0, D.zero_lt_rank⟩ := Fin.ext (show (j : ℕ) = 0 by omega)
    obtain ⟨e, he⟩ := D.hθM
    rw [hj0, D.hc0, he]
    exact Submodule.smul_mem _ e (Submodule.subset_span ⟨⟨0, D.zero_lt_rank⟩, by simp, D.hc0⟩)
  · rw [D.hrel]
    exact Submodule.zero_mem _

theorem rootCharKernel_eq {L : Type} [Field L] (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    {p : ℕ} (hp : p.Prime)
    (hz : ∀ z : Fin τ.rank → ZMod p, z ≠ 0 →
      (M.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = (q : ZMod p) • z →
        {α | IsRoot τ α ∧ pair α z = 0} = {θ, -θ})
    {a : Fin τ.rank → Lˣ} (ha : a ∈ fixedCharTuples M Fr) (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) : rootCharKernel a = {θ, -θ} := by
  obtain ⟨z, hz0, hzM, hker⟩ := exists_eigencolumn_of_mem_fixedCharTuples M Fr hFr hp ha hap ha1
  rw [hker]
  exact hz z hz0 hzM

end A1BlockData

end CFSG.RankThree.PartOne.KE
