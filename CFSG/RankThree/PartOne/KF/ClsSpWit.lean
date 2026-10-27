module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
import CFSG.RankThree.PartTwo.Sec4.Census.Symplectic46

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSp localRank)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam commute_lam_lam pairMat
  pairMat_apply_of_ne pairMat_apply_pair torusHom coe_torusHom torusHom_injective)
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open CFSG.RankThree.Classical (siegelGL torusGL coe_torusGL torusGL_conj_siegelGL siegelSpHom
  symMatrices coe_siegelGL siegelMat)

variable {K : Type} [Field K]

theorem le_localRank_statedSp_torus [Finite K] [CharP K 2] {r n : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrK : r ∣ Nat.card Kˣ) (hn : 1 ≤ n) :
    n ≤ localRank r (StatedProj (StatedSp n K)) := by
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set τ : (Fin n → μ) →* StatedSp n K := torusHom.comp (incl.compLeft (Fin n))
  have hτ : Function.Injective τ := torusHom_injective.comp fun s t hst =>
    funext fun j => Subtype.ext (congrFun hst j)
  have hτGL : ∀ s, ((τ s : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      torusGL (incl.compLeft (Fin n) s) := fun s => by
    apply Units.ext
    rw [coe_torusGL, fromBlocks_diagonal]
    exact coe_torusHom _
  have hroot : ∀ x : μ, (x : Kˣ) ^ r = 1 := fun x => by
    rw [← Subgroup.coe_pow, rootsOfUnity_pow_eq_one, OneMemClass.coe_one]
  have h0 : (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ := rfl
  refine le_localRank_quotient_of_le_normalizer _ hr
    (E := τ.range) (P := (siegelSpHom n K).range)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) τ)
    ?_ ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxN⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hxN
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c =
        torusGL (incl.compLeft (Fin n) s) := hc.trans (hτGL s)
    have hs : ∀ i, s i = 1 := by
      intro i
      have h1 := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl i) (Sum.inl i)) hc'
      have h2 := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inr i) (Sum.inr i)) hc'
      simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        coe_torusGL, fromBlocks_apply₁₁, fromBlocks_apply₂₂, MonoidHom.compLeft_apply,
        Function.comp_apply] at h1 h2
      have hinv : ((incl (s i) : Kˣ) : K) = (((incl (s i))⁻¹ : Kˣ) : K) := h1.symm.trans h2
      have hsq : (incl (s i) : Kˣ) ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [Units.ext hinv]
        exact mul_inv_cancel _
      have h3 := hroot (s i)
      have hg : (incl (s i) : Kˣ) ^ Nat.gcd r 2 = 1 := pow_gcd_eq_one.mpr ⟨h3, hsq⟩
      have hcop : Nat.gcd r 2 = 1 := by
        rw [Nat.gcd_comm]
        exact (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
      rw [hcop, pow_one] at hg
      exact Subtype.ext hg
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
    have hsym : (Matrix.single (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) (1 : K))ᵀ =
        Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1 := by
      rw [Matrix.transpose_single]
    have h1 : siegelSpHom n K (Multiplicative.ofAdd ⟨Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1, hsym⟩) ∈
        (siegelSpHom n K).range := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hP h1)
    have := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩)) hc
    change (Matrix.scalar (Fin n ⊕ Fin n) (c : K)) (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩) =
      siegelMat (Matrix.single (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) (1 : K))
        (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩) at this
    rw [scalar_apply, diagonal_apply_ne _ Sum.inl_ne_inr, siegelMat, fromBlocks_apply₁₂,
      Matrix.single_apply_same] at this
    exact zero_ne_one this
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨s, rfl⟩ _ ⟨B, rfl⟩
    set D : Matrix (Fin n) (Fin n) K := diagonal fun i => ((incl.compLeft (Fin n) s i : Kˣ) : K)
    have hsym : (D * (B.toAdd : Matrix (Fin n) (Fin n) K) * D)ᵀ =
        D * (B.toAdd : Matrix (Fin n) (Fin n) K) * D := by
      rw [transpose_mul, transpose_mul, B.toAdd.2, diagonal_transpose, mul_assoc]
    refine ⟨Multiplicative.ofAdd ⟨_, hsym⟩, ?_⟩
    apply Subtype.ext
    change siegelGL (D * (B.toAdd : Matrix (Fin n) (Fin n) K) * D) =
      ((τ s : StatedSp n K) : GL (Fin n ⊕ Fin n) K) *
        siegelGL (B.toAdd : Matrix (Fin n) (Fin n) K) *
          ((τ s : StatedSp n K) : GL (Fin n ⊕ Fin n) K)⁻¹
    rw [hτGL, torusGL_conj_siegelGL]

theorem mk_lam_injective_of_ne {n : ℕ} {j l : Fin n} (hlj : l ≠ j) :
    Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
      (StatedSp n K))).comp (lam (k := K) j)) :=
  CFSG.RankThree.PartTwo.Sec4.Census.mk_lam_injective_of_ne hlj

theorem le_localRank_three_statedSp_blocks [Finite K] [CharP K 2] {m : ℕ} (hm : 1 ≤ m) :
    m ≤ localRank 3 (StatedProj (StatedSp (m + 1) K)) := by
  set π := QuotientGroup.mk'
    ((StatedScalars (Fin (m + 1) ⊕ Fin (m + 1)) K).subgroupOf (StatedSp (m + 1) K))
  have hlast : ∀ i : Fin m, (Fin.last m : Fin (m + 1)) ≠ Fin.castSucc i := fun i h =>
    (Fin.castSucc_lt_last i).ne h.symm
  let φ : Fin m → SL(2, K) →* StatedProj (StatedSp (m + 1) K) := fun i =>
    π.comp (lam (k := K) (Fin.castSucc i))
  have hinj3 := mk_lam_injective_of_ne (K := K) (j := Fin.last m) (l := 0) (by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega)
  have hu : orderOf ((π.comp (lam (k := K) (Fin.last m))) (sl2Upper 1)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, ← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero, map_one]
    · intro h
      rw [← map_one (π.comp (lam (k := K) (Fin.last m)))] at h
      have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) (hinj3 h)
      simp [coe_sl2Upper] at this
  have h := CFSG.RankThree.PartTwo.Census.Exceptional.card_le_localRank_three_of_commuting_SL2 φ
    (fun i => mk_lam_injective_of_ne (hlast i))
    (fun i j hij A B => by
      change π (lam _ A) * π (lam _ B) = π (lam _ B) * π (lam _ A)
      rw [← map_mul, ← map_mul,
        (commute_lam_lam ((Fin.castSucc_injective m).ne hij) A B).eq])
    hu
    (fun i A => by
      change π (lam _ A) * π (lam _ (sl2Upper 1)) = π (lam _ (sl2Upper 1)) * π (lam _ A)
      rw [← map_mul, ← map_mul, (commute_lam_lam (hlast i).symm A (sl2Upper 1)).eq])
  simpa using h

end CFSG.RankThree.PartOne.KFU
