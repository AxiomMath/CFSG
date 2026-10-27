module

public import CFSG.RankThree.Classical.SiegelRadical
import CFSG.RankThree.PartTwo.Census.Exceptional.Basic
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSp localRank)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam commute_lam_lam pairMat
  pairMat_apply_of_ne pairMat_apply_pair torusHom coe_torusHom torusHom_injective)
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open CFSG.RankThree.Classical (siegelGL torusGL coe_torusGL torusGL_conj_siegelGL siegelSpHom
  symMatrices coe_siegelGL siegelMat)

variable {K : Type} [Field K]

noncomputable def statedSpEquivProjSp (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSp n K) ≃* projSp n K :=
  CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp n K)

theorem mk_lam_injective_of_ne {n : ℕ} {j l : Fin n} (hlj : l ≠ j) :
    Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
      (StatedSp n K))).comp (lam (k := K) j)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨d, hd⟩ := hg
  have hd' : ∀ x y, Matrix.scalar (Fin n ⊕ Fin n) (d : K) x y =
      pairMat (Sum.inl j) (Sum.inr j) (g : Matrix (Fin 2) (Fin 2) K) x y := fun x y => by
    have := congrFun (congrFun (congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hd) x) y
    rw [Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [this]
    rfl
  have hi1 : (Sum.inl l : Fin n ⊕ Fin n) ≠ Sum.inl j := fun h => hlj (Sum.inl_injective h)
  have hd1 : (d : K) = 1 := by
    have := hd' (Sum.inl l) (Sum.inl l)
    rwa [pairMat_apply_of_ne hi1 Sum.inl_ne_inr, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at this
  obtain ⟨h00, h01, h10, h11⟩ := pairMat_apply_pair
    (Sum.inl_ne_inr : (Sum.inl j : Fin n ⊕ Fin n) ≠ Sum.inr j) (g : Matrix (Fin 2) (Fin 2) K)
  have e00 := hd' (Sum.inl j) (Sum.inl j)
  have e01 := hd' (Sum.inl j) (Sum.inr j)
  have e10 := hd' (Sum.inr j) (Sum.inl j)
  have e11 := hd' (Sum.inr j) (Sum.inr j)
  rw [h00, Matrix.scalar_apply, Matrix.diagonal_apply_eq, hd1] at e00
  rw [h01, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ Sum.inl_ne_inr] at e01
  rw [h10, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ Sum.inr_ne_inl] at e10
  rw [h11, Matrix.scalar_apply, Matrix.diagonal_apply_eq, hd1] at e11
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b
  · simpa using e00.symm
  · simpa using e01.symm
  · simpa using e10.symm
  · simpa using e11.symm

theorem three_le_localRank_statedSp_four [Finite K] [CharP K 2] :
    3 ≤ localRank 3 (StatedProj (StatedSp 4 K)) := by
  set π := QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K))
  have hlast : ∀ i : Fin 3, (Fin.last 3 : Fin 4) ≠ Fin.castSucc i := fun i h =>
    (Fin.castSucc_lt_last i).ne h.symm
  let φ : Fin 3 → SL(2, K) →* StatedProj (StatedSp 4 K) := fun i =>
    π.comp (lam (k := K) (Fin.castSucc i))
  have hinj3 := mk_lam_injective_of_ne (K := K) (j := Fin.last 3) (l := 0) (by decide)
  have hu : orderOf ((π.comp (lam (k := K) (Fin.last 3))) (sl2Upper 1)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, ← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero, map_one]
    · intro h
      rw [← map_one (π.comp (lam (k := K) (Fin.last 3)))] at h
      have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) (hinj3 h)
      simp [coe_sl2Upper] at this
  have h := CFSG.RankThree.PartTwo.Census.Exceptional.card_le_localRank_three_of_commuting_SL2 φ
    (fun i => mk_lam_injective_of_ne (hlast i))
    (fun i j hij A B => by
      change π (lam _ A) * π (lam _ B) = π (lam _ B) * π (lam _ A)
      rw [← map_mul, ← map_mul,
        (commute_lam_lam ((Fin.castSucc_injective 3).ne hij) A B).eq])
    hu
    (fun i A => by
      change π (lam _ A) * π (lam _ (sl2Upper 1)) = π (lam _ (sl2Upper 1)) * π (lam _ A)
      rw [← map_mul, ← map_mul, (commute_lam_lam (hlast i).symm A (sl2Upper 1)).eq])
  simpa using h

theorem three_le_localRank_projSp_four_two [Finite (projSp 4 (GaloisField 2 1))] :
    3 ≤ localRank 3 (projSp 4 (GaloisField 2 1)) := by
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (statedSpEquivProjSp 4 (GaloisField 2 1)) Nat.prime_three]
  exact three_le_localRank_statedSp_four

theorem coe_torusHom_eq_torusGL {n : ℕ} (t : Fin n → Kˣ) :
    ((torusHom t : StatedSp n K) : GL (Fin n ⊕ Fin n) K) = torusGL t := by
  apply Units.ext
  rw [coe_torusGL, fromBlocks_diagonal]
  exact coe_torusHom t

theorem three_le_localRank_statedSp_three [Finite K] [CharP K 2] (hK : 3 ∣ Nat.card Kˣ) :
    3 ≤ localRank 3 (StatedProj (StatedSp 3 K)) := by
  have hμ := CFSG.RankThree.PartTwo.Census.card_rootsOfUnity_of_dvd Nat.prime_three hK
  set μ := rootsOfUnity 3 K
  set incl := μ.subtype
  set τ : (Fin 3 → μ) →* StatedSp 3 K := torusHom.comp (incl.compLeft (Fin 3))
  have hτ : Function.Injective τ := torusHom_injective.comp fun s t hst =>
    funext fun j => Subtype.ext (congrFun hst j)
  have hτGL : ∀ s, ((τ s : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) =
      torusGL (incl.compLeft (Fin 3) s) := fun s => coe_torusHom_eq_torusGL _
  have hroot : ∀ x : μ, (x : Kˣ) ^ 3 = 1 := fun x => by
    rw [← Subgroup.coe_pow, CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one,
      OneMemClass.coe_one]
  refine CFSG.RankThree.PartTwo.Census.le_localRank_quotient_of_le_normalizer _ Nat.prime_three
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
      have h3 := hroot (s i)
      have h1' : (incl (s i) : Kˣ) = 1 := by
        calc (incl (s i) : Kˣ) = (incl (s i) : Kˣ) ^ 3 * ((incl (s i) : Kˣ) ^ 2)⁻¹ := by group
          _ = 1 := by
            change ((s i : μ) : Kˣ) ^ 3 * (((s i : μ) : Kˣ) ^ 2)⁻¹ = 1
            rw [h3, show ((s i : μ) : Kˣ) ^ 2 = 1 from hsq, inv_one, mul_one]
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

theorem three_le_localRank_projSp_three_four [Finite (projSp 3 (GaloisField 2 2))] :
    3 ≤ localRank 3 (projSp 3 (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2)ˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (statedSpEquivProjSp 3 (GaloisField 2 2)) Nat.prime_three]
  exact three_le_localRank_statedSp_three (by rw [hK])

end CFSG.RankThree.PartTwo.Sec4.Census
