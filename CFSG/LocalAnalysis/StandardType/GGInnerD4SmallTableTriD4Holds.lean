module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.GGTriD4InnerCompHolds
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriCentHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
public import CFSG.LocalAnalysis.StandardType.GGTCJLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.Assembly.ComponentFreeOddCores
public import CFSG.GH74.Uniqueness.Section15HeringEnd2

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.TableBExcSmallRest
open CFSG.StandardType.D4Inner
open CFSG.StandardType.S2MathAs51600Small
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private def ltrsm7_TriD4SmallProp (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I _ => ∀ τ : MulAut R, τ ∈ I → τ ^ 3 = 1 → τ ≠ 1 →
    ∀ L : Subgroup R, IsComponentOf L (ggAutFixedSubgroup τ) →
      ∃ out : LargeEvenLabel, LargeEvenInLambda2 out ∧ TableComponentLabel lab out ∧
        GGHasLabel out (↥L ⧸ Subgroup.center ↥L)

private theorem ltrsm7_ggHasLabel_A1 {X : Type} [Group X] {m : ℕ}
    {E : Type} [Field E] [Finite E] (hE : Nat.card E = (2 : ℕ) ^ m)
    (e : X ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) E)) :
    GGHasLabel (⟨.A, 1, m⟩ : LargeEvenLabel) X := by
  unfold GGHasLabel
  change LargeEvenRecipeLinear 2 (2 ^ m) (fun R' _ _ _ => Nonempty (X ≃* R'))
  exact ⟨E, inferInstance, inferInstance, hE, ⟨e⟩⟩

private theorem ltrsm7_ggHasLabel_A2 {X : Type} [Group X] {m : ℕ}
    {E : Type} [Field E] [Finite E] (hE : Nat.card E = (2 : ℕ) ^ m)
    (e : X ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) :
    GGHasLabel (⟨.A, 2, m⟩ : LargeEvenLabel) X := by
  unfold GGHasLabel
  change LargeEvenRecipeLinear 3 (2 ^ m) (fun R' _ _ _ => Nonempty (X ≃* R'))
  exact ⟨E, inferInstance, inferInstance, hE, ⟨e⟩⟩

private theorem ltrsm7_three_dvd_two_pow_sub_one {n : ℕ} (he : Even n) :
    3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := he
  have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have hk : 4 ^ k ≡ 1 [MOD 3] := by simpa using h4.pow k
  have hd : 3 ∣ 4 ^ k - 1 :=
    (Nat.modEq_iff_dvd'
      (Nat.succ_le_of_lt (pow_pos (by norm_num : (0 : ℕ) < 4) k))).mp hk.symm
  have hpow : 2 ^ (k + k) = 4 ^ k := by rw [pow_add, ← mul_pow]; norm_num
  rwa [hpow]

private theorem ltrsm7_center_top_eq_bot {R : Type*} [Group R]
    (hZ : Subgroup.center R = ⊥) : Subgroup.center ↥(⊤ : Subgroup R) = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hmem : (x : R) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hx ⟨y, Subgroup.mem_top y⟩)
    rwa [hZ, Subgroup.mem_bot] at hmem
  · intro hx
    rw [Subgroup.mem_bot] at hx
    subst hx
    exact Subgroup.mem_center_iff.mpr (fun y => by simp)

private theorem ltrsm7_conj_pow_three_eq_one {R : Type*} [Group R]
    (hZ : Subgroup.center R = ⊥) {s : R} {τ : MulAut R}
    (hs : MulAut.conj s = τ) (hτ3 : τ ^ 3 = 1) : s ^ 3 = 1 := by
  have h3 : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hs, hτ3]
  have hmem : s ^ 3 ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun f : MulAut R => f y) h3
    rw [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rwa [hZ, Subgroup.mem_bot] at hmem

private theorem ltrsm7_conj_ne_one {R : Type*} [Group R] {s : R} {τ : MulAut R}
    (hs : MulAut.conj s = τ) (hτ1 : τ ≠ 1) : s ≠ 1 :=
  fun h1 => hτ1 (by rw [← hs, h1, map_one])

private theorem ltrsm7_finite_triD4R
    (n : ℕ) (K : Type) [Field K] [Finite K]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) :
    Finite (GGTriD4R n K) := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := n * 3) (by omega) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n :=
    fun c => by rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := nonempty_triD4_equiv hn K hK σ hσ
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact Finite.of_equiv _ e.symm.toEquiv

private theorem ltrsm7_labelOf_triD4_recipe (n : ℕ) (K : Type) [Field K] [Finite K]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hS : IsSimpleGroup (GGTriD4R n K))
    (hna : ∃ a b : GGTriD4R n K, a * b ≠ b * a) :
    LabelOf (⊤ : Subgroup (GGTriD4R n K)) (⟨.triD4, 0, n⟩ : LargeEvenLabel) := by
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hcomm : commutator (GGTriD4R n K) = ⊤ :=
    CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hna
  have hmark : CFSG.Assembly.LargeEvenMarking (GGTriD4R n K)
      (fun lab' _ _ _ _ _ => lab' = (⟨.triD4, 0, n⟩ : LargeEvenLabel)) := by
    refine ⟨hcomm, ⟨.triD4, 0, n⟩, ⟨hn, rfl⟩, ?_⟩
    refine ⟨K, inferInstance, inferInstance, hK, hS, hna, ⟨?_, rfl⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_congr
    (Subgroup.topEquiv : ↥(⊤ : Subgroup (GGTriD4R n K)) ≃* GGTriD4R n K)
    (fun l : LargeEvenLabel => l = (⟨.triD4, 0, n⟩ : LargeEvenLabel))).2 hmark

private theorem ltrsm7_innerComp_even
    (hIC : GGTriD4InnerCompInput) {n : ℕ} (hn : 1 ≤ n) (h : n = 1 ∨ 3 ∣ 2 ^ n - 1) :
    LargeEvenLabelAll (⟨.triD4, 0, n⟩ : LargeEvenLabel)
      (LargeEvenSimpleGuard (ltrsm7_TriD4SmallProp ⟨.triD4, 0, n⟩)) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeTwisted_and (m := 3) (n := n)
    (P := LargeEvenSimpleGuard (ltrsm7_TriD4SmallProp ⟨.triD4, 0, n⟩)) ?_ hQ
  intro K _ _ hKcard
  intro hS hna τ hτ hτ3 hτ1 L hL
  obtain ⟨s, hs⟩ := chevIDImage_subset_inn_triD4 hn K hKcard hτ
  have hfix : ggAutFixedSubgroup τ =
      Subgroup.centralizer ({s} : Set (GGTriD4R n K)) := by
    rw [← hs, ggAutFixedSubgroup_conj_eq_centralizer]
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hs3 : s ^ 3 = 1 := ltrsm7_conj_pow_three_eq_one hZ hs hτ3
  have hs1 : s ≠ 1 := ltrsm7_conj_ne_one hs hτ1
  have hL' : IsComponentOf L (Subgroup.centralizer ({s} : Set (GGTriD4R n K))) := by
    rwa [hfix] at hL
  rcases hIC n hn h K (by simpa using hKcard) s hs1 hs3 L hL' with
    ⟨E, hEfield, hEfin, hEcard, he⟩ | ⟨h2, E, hEfield, hEfin, hEcard, he⟩
  · obtain ⟨he⟩ := he
    refine ⟨⟨.A, 1, 3 * n⟩, ⟨by show 1 ≤ 3 * n; omega, by norm_num,
        fun _ => by show 2 ≤ 3 * n; omega⟩,
      Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), ?_⟩
    have hEcard' : Nat.card E = 2 ^ (3 * n) := by
      rw [hEcard]
      calc (2 ^ n) ^ 3 = 2 ^ (n * 3) := (pow_mul 2 n 3).symm
        _ = 2 ^ (3 * n) := by rw [mul_comm]
    exact ltrsm7_ggHasLabel_A1 (m := 3 * n) hEcard' he
  · obtain ⟨he⟩ := he
    have hn1 : n ≠ 1 := by omega
    have heven : Even n := by
      rcases h with h1 | hdiv
      · exact absurd h1 hn1
      · by_contra hne
        exact (CFSG.GH74.Uniqueness.Hering.three_not_dvd_two_pow_sub_one
          (Nat.not_even_iff_odd.mp hne)) hdiv
    have hA2 : A2Label n = (⟨.A, 2, n⟩ : LargeEvenLabel) := by
      unfold A2Label
      rw [if_pos heven]
    refine ⟨A2Label n, ?_, ?_, ?_⟩
    · rw [hA2]
      exact ⟨by simpa using hn, by norm_num, fun _ => by simpa using h2⟩
    · rw [hA2]
      exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨by simpa using h2, by simpa using hA2.symm⟩⟩)
    · rw [hA2]
      exact ltrsm7_ggHasLabel_A2 (m := n) hEcard he

private theorem ltrsm7_innerComp_odd
    (htri : TriD4Cent3) {n : ℕ} (hodd : Odd n) (hn3 : 3 ≤ n) :
    LargeEvenLabelAll (⟨.triD4, 0, n⟩ : LargeEvenLabel)
      (LargeEvenSimpleGuard (ltrsm7_TriD4SmallProp ⟨.triD4, 0, n⟩)) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeTwisted_and (m := 3) (n := n)
    (P := LargeEvenSimpleGuard (ltrsm7_TriD4SmallProp ⟨.triD4, 0, n⟩)) ?_ hQ
  intro K _ _ hKcard
  intro hS hna τ hτ hτ3 hτ1 L hL
  have hn : 1 ≤ n := by omega
  obtain ⟨s, hs⟩ := chevIDImage_subset_inn_triD4 hn K hKcard hτ
  have hfix : ggAutFixedSubgroup τ =
      Subgroup.centralizer ({s} : Set (GGTriD4R n K)) := by
    rw [← hs, ggAutFixedSubgroup_conj_eq_centralizer]
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hs3 : s ^ 3 = 1 := ltrsm7_conj_pow_three_eq_one hZ hs hτ3
  have hs1 : s ≠ 1 := ltrsm7_conj_ne_one hs hτ1
  have hL' : IsComponentOf L (Subgroup.centralizer ({s} : Set (GGTriD4R n K))) := by
    rwa [hfix] at hL
  have hZtop : Subgroup.center ↥(⊤ : Subgroup (GGTriD4R n K)) = ⊥ :=
    ltrsm7_center_top_eq_bot hZ
  have hlabelOf : LabelOf (⊤ : Subgroup (GGTriD4R n K))
      (⟨.triD4, 0, n⟩ : LargeEvenLabel) :=
    ltrsm7_labelOf_triD4_recipe n K hn hKcard hS hna
  have hcomp : CFSG.Open.IsComponentOf L
      (⊤ ⊓ Subgroup.centralizer ({s} : Set (GGTriD4R n K))) := by
    simpa using (CFSG.Assembly.isComponentOf_iff_open.1 hL')
  have hInner : InnerOn (⊤ : Subgroup (GGTriD4R n K)) s :=
    ⟨s, Subgroup.mem_top s, fun j _ => rfl⟩
  have hbC : s ∉ Subgroup.centralizer (⊤ : Set (GGTriD4R n K)) := by
    intro hmem
    apply hs1
    have : s ∈ Subgroup.center (GGTriD4R n K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subgroup.mem_centralizer_iff.mp hmem y (Subgroup.mem_top y)
    rwa [hZ, Subgroup.mem_bot] at this
  haveI : Finite (GGTriD4R n K) := ltrsm7_finite_triD4R n K hn hKcard
  rcases htri (GGTriD4R n K) ⊤ L s (⟨.triD4, 0, n⟩ : LargeEvenLabel)
      hlabelOf rfl hodd hn3 hZtop (Subgroup.le_normalizer (Subgroup.mem_top s)) hs3 hbC hcomp with
    ⟨hnot, -⟩ | ⟨-, hin⟩
  · exact absurd hInner hnot
  · have hnotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
    rcases hin with hA1 | htwA
    · refine ⟨⟨.A, 1, 3 * n⟩, ⟨by show 1 ≤ 3 * n; omega, le_rfl,
          fun _ => by show 2 ≤ 3 * n; omega⟩,
        Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), ?_⟩
      exact CFSG.StandardType.TCJ.tcj_ggHasLabel_of_hasLabel hA1
    · have hA2 : A2Label n = (⟨.twA, 2, n⟩ : LargeEvenLabel) := by
        unfold A2Label
        rw [if_neg hnotEven]
      refine ⟨A2Label n, ?_, ?_, ?_⟩
      · rw [hA2]
        exact ⟨by simpa using hn, by norm_num, fun _ => by show 2 ≤ n; omega⟩
      · rw [hA2]
        exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨by show 2 ≤ n; omega,
          by simpa using hA2.symm⟩⟩)
      · rw [hA2]
        exact CFSG.StandardType.TCJ.tcj_ggHasLabel_of_hasLabel htwA

theorem smallTableTriD4_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .triD4 →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∀ τ : MulAut R, τ ∈ I → τ ^ 3 = 1 → τ ≠ 1 →
          ∀ L : Subgroup R, IsComponentOf L (ggAutFixedSubgroup τ) →
            ∃ out : LargeEvenLabel, LargeEvenInLambda2 out ∧
              S2MathAs51600Small.TableComponentLabel lab out ∧
              GGHasLabel out (↥L ⧸ Subgroup.center ↥L)) := by
  intro lab hlab htag
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .triD4 := htag
  subst ht
  have hl : l = 0 := by
    have := hlab.2
    simpa using this
  subst hl
  have hn : 1 ≤ n := hlab.1
  have hIC : GGTriD4InnerCompInput := ggTriD4InnerCompInput_holds
  have htri : TriD4Cent3 := triD4Cent3_holds
  by_cases hodd : Odd n
  · by_cases hn3 : 3 ≤ n
    · exact ltrsm7_innerComp_odd htri hodd hn3
    · have hn1 : n = 1 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      exact ltrsm7_innerComp_even hIC hn (Or.inl hn1)
  · have heven : Even n := Nat.not_odd_iff_even.mp hodd
    exact ltrsm7_innerComp_even hIC hn
      (Or.inr (ltrsm7_three_dvd_two_pow_sub_one heven))

end CFSG.StandardType.GGInnerD4SmallParts

end
