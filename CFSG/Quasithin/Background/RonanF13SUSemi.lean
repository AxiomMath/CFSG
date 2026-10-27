module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.RonanF13

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (hom_eq_of_central_ker_perfect)

section SU

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝟙" => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem isPrimeFormGram_one3 : IsPrimeFormGram (1 : GL (Fin 3) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

@[expose] noncomputable def suTheta (A : primeFormUnitary h 𝟙) (σ : K ≃+* K) :
    MulAut (gramSU h 𝟙) :=
  primeFormConjSU h 𝟙 A * primeFormFieldSU h isPrimeFormGram_one3 σ

theorem suTheta_apply_mk (A : primeFormUnitary h 𝟙) (σ : K ≃+* K) (g : gramSU h 𝟙) :
    (primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one3 σ :
        MulAut (primeFormP h 𝟙)) (g : primeFormP h 𝟙) =
      ((suTheta h A σ g : gramSU h 𝟙) : primeFormP h 𝟙) := by
  rw [MulAut.mul_apply]
  change primeFormConjAut h 𝟙 A (primeFormFieldAut h isPrimeFormGram_one3 σ _) = _
  rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  rfl

variable [Finite K]

theorem isPerfect_gramSU_three (hnq : ¬(3 = 3 ∧ p ^ f = 2)) : Group.IsPerfect (gramSU h 𝟙) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hnq' : (3, p ^ f) ≠ (3, 2) := fun e => hnq ⟨rfl, (Prod.mk.inj e).2⟩
  have hP := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) h.card_eq_sq (n := 3)
    (by norm_num) hnq'
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).toMonoidHom)
    (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).surjective

theorem center_primeFormP_three_eq_bot' (hnq : ¬(3 = 3 ∧ p ^ f = 2)) :
    Subgroup.center (primeFormP h 𝟙) = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hnq' : (3, p ^ f) ≠ (3, 2) := fun e => hnq ⟨rfl, (Prod.mk.inj e).2⟩
  obtain ⟨e₁⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one3 (K := K))
  have e : primeFormP h 𝟙 ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) :=
    e₁.trans (unitaryPSUEquiv h (by omega))
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f h.card_eq_sq 3
    (by norm_num) hnq'
  have hP := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) h.card_eq_sq (n := 3)
    (by norm_num) hnq'
  have hP' : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hsimple : IsSimpleGroup (primeFormP h 𝟙) := e.isSimpleGroup
  have hperf : Group.IsPerfect (primeFormP h 𝟙) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (primeFormP h 𝟙)) with h0 | h1
  · exact h0
  · exfalso
    have h1' := (commutator_eq_bot_iff_center_eq_top (primeFormP h 𝟙)).2 h1
    rw [Group.IsPerfect.commutator_eq_top] at h1'
    exact top_ne_bot h1'

theorem center_gramSU_three (hnq : ¬(3 = 3 ∧ p ^ f = 2)) :
    Subgroup.center (gramSU h 𝟙) = normOneScalars h (gramSU h 𝟙) 3 := by
  apply le_antisymm
  · intro z hz
    have h1 : (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3) z : primeFormP h 𝟙) ∈
        Subgroup.center (primeFormP h 𝟙) :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨z, hz, rfl⟩
    rw [center_primeFormP_three_eq_bot' h hnq, Subgroup.mem_bot] at h1
    have h2 : z ∈ (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)).ker := h1
    rwa [QuotientGroup.ker_mk'] at h2
  · exact normOneScalars_le_center h _ 3

theorem aut_gramSU_semilinear (hnq : ¬(3 = 3 ∧ p ^ f = 2)) (α : MulAut (gramSU h 𝟙)) :
    ∃ (A : primeFormUnitary h 𝟙) (φ : K ≃+* K), α = suTheta h A φ ∧
      ∀ r : ℕ, α ^ r = 1 → φ ^ r = 1 := by
  have hperf := isPerfect_gramSU_three h hnq
  set Z := normOneScalars h (gramSU h 𝟙) 3 with hZ
  have hcen : Subgroup.center (gramSU h 𝟙) = Z := center_gramSU_three h hnq
  have hmapZ : Z.map α.toMonoidHom = Z := by
    rw [← hcen]
    exact Subgroup.map_center_eq α
  set ᾱ : MulAut (primeFormP h 𝟙) := QuotientGroup.congr Z Z α hmapZ with hᾱ
  have hmk : ∀ g : gramSU h 𝟙, ᾱ (g : primeFormP h 𝟙) = ((α g : gramSU h 𝟙) : primeFormP h 𝟙) :=
    fun g => QuotientGroup.congr_mk Z Z α hmapZ g
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := hnq
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h
    (isPrimeFormGram_one3 (K := K)) (n := 3) le_rfl hq ᾱ
  refine ⟨A, φ, ?_, ?_⟩
  · have hker : (QuotientGroup.mk' Z).ker ≤ Subgroup.center (gramSU h 𝟙) := by
      rw [QuotientGroup.ker_mk', hcen]
    have := hom_eq_of_central_ker_perfect (θ := QuotientGroup.mk' Z) hker α.toMonoidHom
      (suTheta h A φ).toMonoidHom (fun x => by
        change (((α x : gramSU h 𝟙)) : primeFormP h 𝟙) = ((suTheta h A φ x : gramSU h 𝟙) : primeFormP h 𝟙)
        rw [← hmk, ← suTheta_apply_mk, ← hA])
    exact MulEquiv.ext fun x => DFunLike.congr_fun this x
  · intro r hr
    have hpow : ∀ (j : ℕ) (g : gramSU h 𝟙),
        (ᾱ ^ j) (g : primeFormP h 𝟙) = (((α ^ j) g : gramSU h 𝟙) : primeFormP h 𝟙) := by
      intro j
      induction j with
      | zero => intro g; simp
      | succ j ih =>
        intro g
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hmk, ih]
    have h1 : ᾱ ^ r = 1 := by
      refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
      rw [hpow, hr]
      simp
    have h2 := primeFormFieldFactor_apply h (isPrimeFormGram_one3 (K := K)) (n := 3) le_rfl hq A φ
    rw [← hA] at h2
    rw [← h2, ← map_pow, h1, map_one]

end SU

end CFSG.Quasithin.RonanF13
