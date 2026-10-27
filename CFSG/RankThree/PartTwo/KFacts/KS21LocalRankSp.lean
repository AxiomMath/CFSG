module

public import CFSG.RankThree.PartTwo.Sec4.Census.Symplectic46
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp localRank)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torusHom_injective)
open CFSG.RankThree.Classical (siegelGL torusGL coe_torusGL torusGL_conj_siegelGL siegelSpHom
  siegelMat)

variable {K : Type} [Field K]

theorem le_localRank_statedSp_three [Finite K] [CharP K 2] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hK : r ∣ Nat.card Kˣ) :
    3 ≤ localRank r (StatedProj (StatedSp 3 K)) := by
  have hμ := CFSG.RankThree.PartTwo.Census.card_rootsOfUnity_of_dvd hr hK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set τ : (Fin 3 → μ) →* StatedSp 3 K := torusHom.comp (incl.compLeft (Fin 3))
  have hτ : Function.Injective τ := torusHom_injective.comp fun s t hst =>
    funext fun j => Subtype.ext (congrFun hst j)
  have hτGL : ∀ s, ((τ s : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) =
      torusGL (incl.compLeft (Fin 3) s) := fun s =>
    CFSG.RankThree.PartTwo.Sec4.Census.coe_torusHom_eq_torusGL _
  have hroot : ∀ x : μ, (x : Kˣ) ^ r = 1 := fun x => by
    rw [← Subgroup.coe_pow, CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one,
      OneMemClass.coe_one]
  have hcop : Nat.gcd r 2 = 1 :=
    (Nat.coprime_primes hr Nat.prime_two).mpr hr2
  refine CFSG.RankThree.PartTwo.Census.le_localRank_quotient_of_le_normalizer _ hr
    (E := τ.range) (P := (siegelSpHom 3 K).range)
    (CFSG.RankThree.PartTwo.Census.isElemAbelian_range
      (fun s => funext fun j => CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one (s j)) τ)
    ?_ ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv]
    exact CFSG.RankThree.PartTwo.Census.card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxN⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hxN
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c =
        torusGL (incl.compLeft (Fin 3) s) := hc.trans (hτGL s)
    have hs : ∀ i, s i = 1 := by
      intro i
      have h1 := congrArg (fun A : GL (Fin 3 ⊕ Fin 3) K =>
        (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl i) (Sum.inl i)) hc'
      have h2 := congrArg (fun A : GL (Fin 3 ⊕ Fin 3) K =>
        (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inr i) (Sum.inr i)) hc'
      simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        coe_torusGL, fromBlocks_apply₁₁, fromBlocks_apply₂₂, MonoidHom.compLeft_apply,
        Function.comp_apply] at h1 h2
      have hinv : ((incl (s i) : Kˣ) : K) = (((incl (s i))⁻¹ : Kˣ) : K) := h1.symm.trans h2
      have hsq : (incl (s i) : Kˣ) ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [Units.ext hinv]
        exact mul_inv_cancel _
      have h3 : (incl (s i) : Kˣ) ^ r = 1 := hroot (s i)
      have h1' : (incl (s i) : Kˣ) = 1 := by
        have := pow_gcd_eq_one.mpr ⟨h3, hsq⟩
        rwa [hcop, pow_one] at this
      exact Subtype.ext h1'
    rw [Subgroup.mem_bot, show s = 1 from funext hs, map_one]
  · intro y
    obtain ⟨B, hB⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hB, ← map_mul, OneMemClass.coe_one]
    have hBB : B * B = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      ext i j
      simp only [toAdd_mul, toAdd_one, AddSubgroup.coe_add, Matrix.add_apply,
        ZeroMemClass.coe_zero, Matrix.zero_apply, CharTwo.add_self_eq_zero]
    rw [hBB, map_one]
  · intro hP
    have hsym : (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : K))ᵀ = Matrix.single 0 0 1 := by
      rw [Matrix.transpose_single]
    have h1 : siegelSpHom 3 K (Multiplicative.ofAdd ⟨Matrix.single 0 0 1, hsym⟩) ∈
        (siegelSpHom 3 K).range := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hP h1)
    have := congrArg (fun A : GL (Fin 3 ⊕ Fin 3) K =>
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl 0) (Sum.inr 0)) hc
    change (Matrix.scalar (Fin 3 ⊕ Fin 3) (c : K)) (Sum.inl 0) (Sum.inr 0) =
      siegelMat (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : K)) (Sum.inl 0) (Sum.inr 0) at this
    rw [scalar_apply, diagonal_apply_ne _ Sum.inl_ne_inr, siegelMat, fromBlocks_apply₁₂,
      Matrix.single_apply_same] at this
    exact zero_ne_one this
  · refine CFSG.RankThree.PartTwo.Census.le_normalizer_of_conj_mem ?_
    rintro _ ⟨s, rfl⟩ _ ⟨B, rfl⟩
    set D : Matrix (Fin 3) (Fin 3) K := diagonal fun i => ((incl.compLeft (Fin 3) s i : Kˣ) : K)
    have hsym : (D * (B.toAdd : Matrix (Fin 3) (Fin 3) K) * D)ᵀ =
        D * (B.toAdd : Matrix (Fin 3) (Fin 3) K) * D := by
      rw [transpose_mul, transpose_mul, B.toAdd.2, diagonal_transpose, mul_assoc]
    refine ⟨Multiplicative.ofAdd ⟨_, hsym⟩, ?_⟩
    apply Subtype.ext
    change siegelGL (D * (B.toAdd : Matrix (Fin 3) (Fin 3) K) * D) =
      ((τ s : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) *
        siegelGL (B.toAdd : Matrix (Fin 3) (Fin 3) K) *
          ((τ s : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K)⁻¹
    rw [hτGL, torusGL_conj_siegelGL]

end CFSG.RankThree.PartTwo.KFacts.KS21LocalRank
