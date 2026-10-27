module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Unitary
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.Coprime.EvenCenterSectionCover
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PartTwo.Sec17.HeadProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

section Ranks

theorem finite_projGenLinGroup_three (K : Type) [Field K] [Finite K] :
    Finite (ProjGenLinGroup (Fin 3) K) :=
  inferInstanceAs (Finite (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)))

variable (K : Type) [Field K]

@[expose] def radL3 : (Fin 2 → K) →+ Matrix (Fin 3) (Fin 3) K where
  toFun v := !![0, 0, v 0; 0, 0, v 1; 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem radL3_injective : Function.Injective (radL3 K) := by
  intro v w h
  funext i
  have h02 := congrFun (congrFun h 0) 2
  have h12 := congrFun (congrFun h 1) 2
  simp [radL3] at h02 h12
  fin_cases i <;> assumption

theorem radL3_mul (v w : Fin 2 → K) : radL3 K v * radL3 K w = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radL3, mul_apply, Fin.sum_univ_three]

theorem two_mul_le_pRank_projSL_three [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {k : ℕ}
    (hk : Nat.card K = p ^ k) : 2 * k ≤ CFSG.pRank p (projSL 3 K) := by
  refine Sec4.Census.le_pRank_of_sqZero (radL3 K) (radL3_injective K) (radL3_mul K)
    (fun v => funext fun i => by simp [nsmul_eq_mul]) (projSL 3 K) (fun v => ?_) ?_
  · refine ⟨Sec4.Census.sqZeroUnit (radL3 K) (radL3_mul K) v, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    change (1 + radL3 K v).det = 1
    rw [det_of_isUpperTriangular]
    · simp [Fin.prod_univ_three, radL3]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [radL3]
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, hk, ← pow_mul,
      mul_comm]

theorem two_mul_le_pRank_projSU_three {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    have := finite_projGenLinGroup_three (GaloisField p (2 * e))
    2 * e ≤ CFSG.Open.pRank p (⊤ : Subgroup (projSU 3 p e)) := by
  intro _
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have h := CFSG.SectionRank.ClassicalOdd.two_mul_le_pRank_SU_three
    (K := GaloisField p (2 * e)) (p := p) (f := e) hp2 hK
  have e₂ : CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) (GaloisField p (2 * e))) ≃* projSU 3 p e :=
    (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans (MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 p e))
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e₂] at h

theorem two_mul_le_open_pRank_of_isoLThreePi {X : Type} [Group X] [Finite X] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) :
    2 * e ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have := finite_projGenLinGroup_three (GaloisField p e)
  have := finite_projGenLinGroup_three (GaloisField p (2 * e))
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have h := two_mul_le_pRank_projSL_three (GaloisField p e) (p := p)
      (GaloisField.card p e (by omega))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ]
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ]
    exact two_mul_le_pRank_projSU_three hp2

end Ranks

section Prime

variable {G : Type} [Group G] [Finite G]

theorem open_pRank_top_le_localRank {T : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.normalizer (T : Set G))) ≤
      CFSG.Assembly.RankThreeEven.localRank p G := by
  set K := Subgroup.normalizer (T : Set G) with hK
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p K := by
    have := CFSG.SectionRank.pRank_le_map hp.one_lt K.subtype K.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have hbdd : BddAbove {j | ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧
      CFSG.Assembly.pRank p H = j} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    refine csSup_le' ?_
    rintro j ⟨F, -, -, hj⟩
    have h1 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    change j ≤ Nat.card G
    omega
  exact h1.trans (le_csSup hbdd ⟨K, ⟨T, hT, hT2, rfl⟩, rfl⟩)

theorem claim1715Prime_of (h41 : Sec4.Item4_1) : Claim1715Prime := by
  intro G _ _ A c L Y₀ h p e _ hp3 he hiso
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set T := CFSG.Open.pCoreOf 2 Y₀ with hT
  have hT1 : T ≠ ⊥ := h.mem_y0Star.prop.2.2
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  set K := Subgroup.normalizer (T : Set G) with hK
  have hKtop : K ≠ ⊤ := normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hT1 hT2
  have hLK : L ≤ K := h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hK4 : SectionFourHyp K := h.toTheoremFourHyp.sectionFourHyp hKtop
  have hpK : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
    have h1 := open_pRank_top_le_localRank hT1 hT2 hp
    have h2 := h.localRank_lt p hp hp3
    rw [← hK] at h1
    omega
  set H : Subgroup K := L.subgroupOf K with hH
  have eH : H ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  set N : Subgroup H := aschbacherSolvableCore 3 H with hN
  have hNc : N.Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).2.1
  have : N.Normal := inferInstance
  have hθ : N.map eH.toMonoidHom = aschbacherSolvableCore 3 L :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eH
  have eQ : (H ⧸ N) ≃* (L ⧸ aschbacherSolvableCore 3 L) := QuotientGroup.congr N _ eH hθ
  have hqL := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_lA.1
  have hq : CFSG.IsQuasisimple (H ⧸ N) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hqL
  have hlayer : layer (H ⧸ N) = ⊤ := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hq
  obtain ⟨-, h2⟩ := h41 K hK4 H N hlayer
  have h5 := (h2 p hp (hpK.trans (by norm_num))).1 hp3
  have h6 := two_mul_le_open_pRank_of_isoLThreePi hp2 he hiso
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eQ] at h6
  omega

end Prime

end CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

theorem item1715_of_item4_1
    (h1514 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1514 A (lB A) c L)
    (h1714 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1714 L)
    (h41 : Sec4.Item4_1) (hMeets : Claim1715Meets) (hAY : Claim1715A) : Item1715 :=
  item1715_of h1514 h1714 hMeets (HeadProof.claim1715Prime_of h41) hAY

end CFSG.RankThree.PartTwo.Sec17
