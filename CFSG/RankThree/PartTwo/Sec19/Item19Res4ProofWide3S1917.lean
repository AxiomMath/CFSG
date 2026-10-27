module

public import CFSG.RankThree.PartTwo.Sec19.Step1917ProofTools
public import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2
public import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsZ2
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofWide3
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec19.Step1915W
public import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofEnd

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Item19Res4Proof

open Step1917Proof

variable {G : Type} [Group G] [Finite G]

theorem false_of_isTripleA6_of_alt1915W
    (h1913 : Step1913) {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (halt : Alt1915W L K c)
    (htriple : IsTripleA6 (K ⧸ CFSG.pCore 2 K)) : False := by
  have hperf : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := by
    have := isPerfect_of_mem_oTwoComponentsIn hK
    infer_instance
  obtain ⟨z, hz, hz1⟩ := exists_mem_center_ne_one htriple
  rcases halt with hKL | ⟨p, e, _, he, -, hiso, -⟩ | ⟨n, -, -, hD4, -⟩
  ·
    obtain ⟨-, hZL, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
    have hZ3 : ∀ w ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K), w ^ 3 = 1 := fun w hw =>
      pow_three_eq_one_of_mem_center htriple hw
    have hθ := Step1911EndProof.phiL_eq_one_iff_mem_theta hK hLK hKL hZ3
    obtain ⟨l, hl⟩ := Step1911EndProof.phiL_surjective hLK hKL z
    have hlZ : (l : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, ← hθ, map_mul,
        map_inv, map_mul, map_mul, hl, Subgroup.mem_center_iff.mp hz]
      group
    rw [hZL, Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← hθ, hl] at hlZ
    exact hz1 hlZ
  ·
    obtain ⟨hs, -⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega) hiso
    have hbot := Step1914TriProof.center_eq_bot_of_isSimpleGroup_of_isPerfect
      (X := K ⧸ CFSG.pCore 2 K)
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 hz
  · exact not_isTripleA6_of_trialityD4 htriple hD4

theorem gammaOne_le_of_W_wide3
    (h1913 : Step1913) (h181 : Sec18.Item181_1) (h1812 : Sec18.Item181_2)
    (h194 : Item194UsedWide3) (h1915 : Step1915W) (hZ2 : Step1917Z2W) (hJ : Step1917J)
    (hPush : Step1917Push) (hLift : Step1917Lift)
    {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M) (hLM : L ≤ M) :
    gammaOne (A ⊓ E) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  obtain ⟨-, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  have hE := Step1916Proof2.isE27_E hctx
  have hA := Step1916Proof2.isE27_A hctx
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set D := A ⊓ E with hDdef
  have hD9 : Nat.card D = 9 := step1916D_of h1913 G A c L E M hctx
  have hD3 : IsPGroup 3 D := hA.isPGroup.to_le inf_le_left
  have hDE : D ≤ E := inf_le_right
  have hgam : ∀ X : Subgroup G, X ≤ E → 9 ≤ Nat.card X →
      Subgroup.normalizer (X : Set G) ≤ M := fun X hXE hX9 =>
    (normalizer_le_gamma hXE (two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hXE)
      hX9)).trans hctx.mem_scriptM.2
  have hAM : A ≤ M := fun a ha => hgam D hDE hD9.ge
    ((Subgroup.centralizer_le_normalizer (D : Set G))
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hAc x hx.1 a ha))
  rw [gammaOne_le_iff hD3]
  intro X hXD hX1
  have hXdvd : Nat.card X ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hD9]
    exact Subgroup.card_dvd_of_le hXD
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hXdvd
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.mp (by rw [hk]; rfl)) hX1
  swap
  · exact hgam X (hXD.trans hDE) (by rw [hk]; norm_num)
  obtain ⟨⟨d, hdX⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdD : d ∈ A ⊓ E := hXD hdX
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdD.1
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1'
  have hXd : X = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdX)
      (by rw [hk, Nat.card_zpowers, hdo, pow_one])).symm
  rw [hXd]
  by_contra hN
  have hdc : d ∉ Subgroup.zpowers c := by
    intro h
    apply hN
    have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hdo, Step1916Proof2.orderOf_eq hctx])
    rw [heq]
    exact step1916_of h1913 G A c L E M hctx hLM
  obtain ⟨P, hPEAL, hP3, hdP, hd2, hdZ⟩ := hZ2 G A c L E M hctx hLM d hdD hdc
  have hPM : P ≤ M := hPEAL.trans (sup_le (sup_le hEM hAM) hLM)
  have hM2 : CFSG.Assembly.IsTwoLocal M := hctx.mem_scriptM.1.1
  have hfaith : ∀ x ∈ P, (∀ s ∈ CFSG.Open.pCoreOf 2 M, x * s = s * x) → x = 1 := by
    intro x hx hxs
    have hxC : x ∈ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 M : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => (hxs s hs).symm
    have hxO : x ∈ CFSG.Open.pCoreOf 2 M := hctx.charTwoType M hM2 ⟨hPM hx, hxC⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨x, hxO⟩
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    exact eq_one_of_pow_two_pow_of_pow_three_pow (by simpa using congrArg Subtype.val hj)
      (by simpa using congrArg Subtype.val hk)
  have hO2 := two_lt_card_of_mem_upperCentralSeries hP3
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (hPM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hfaith hdP hdo hd2 hdZ
  have h18 : Sec18Std G E M := ⟨hst, hctx.partTwoS_eq, hEE, hctx.mem_scriptM⟩
  have hQ := pCoreOf_centralizer_ne_bot h181 h1812 hctx.hyp191 h18 hdD.2 hd1' hO2
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  obtain ⟨H, hH, -⟩ := exists_mem_scriptM_of_isTwoLocal
    (X := (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G))
    (H := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Cd : Set G))
    ⟨CFSG.Open.pCoreOf 2 Cd, hQ, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Cd, rfl⟩
    (normalizer_zpowers_le d)
  have hNH : Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ H := fun x hx => hH.2 hx
  have hHM : H ≠ M := fun h => hN (h ▸ hNH)
  obtain ⟨K, hK, hLK, halt⟩ := h1915 G A c L E M hctx hLM
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hKn : ∀ m ∈ M, K.map (MulAut.conj m).toMonoidHom = K := fun m hm =>
    Step1918Proof.map_conj_eq_of_mem hctx hZ hK hLK hFL hF hF9 hm
  have hHK : ¬ H ≤ Subgroup.normalizer (K : Set G) := by
    intro hle
    apply hN
    intro x hx
    exact Step1918Proof.mem_of_map_conj_eq hctx hK hKn
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hle (hNH hx)))
  by_cases hKH : K ≤ H
  ·
    rcases hPush G A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH with h | hiso
    · exact hHK h
    · have hKH' := hLift G A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH hHK hiso
      exact hHK fun h hh => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_eq_of_mem_of_isMaximalTwoLocal hst hH.1 hZ hKH' hLK hFL hF hF9 hh)
  ·
    have hEH : E ≤ H := fun x hx => hNH ((centralizer_le_normalizer_zpowers d)
      (le_centralizer_of_mem hE.1.1 hdD.2 hx))
    obtain ⟨-, hJall⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
      (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
    obtain ⟨hlist3, hpar⟩ := hJall K ⟨hK, hKH⟩
    have hlist : IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) := by
      rcases hlist3 with h | h | htriple
      · exact Or.inl h
      · exact Or.inr h
      · exact (false_of_isTripleA6_of_alt1915W h1913 hctx hK hLK halt htriple).elim
    exact hJ G A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt ⟨hK, hKH⟩ hlist hpar

end Item19Res4Proof

theorem step1917_of_W_wide3
    (h1913 : Step1913) (h181 : Sec18.Item181_1) (h1812 : Sec18.Item181_2)
    (h194 : Item194UsedWide3) (h1915 : Step1915W) (hZ2 : Step1917Z2W) (hJ : Step1917J)
    (hPush : Step1917Push) (hLift : Step1917Lift) : Step1917 := by
  intro G _ _ A c L E M hctx hLM
  exact Item19Res4Proof.gammaOne_le_of_W_wide3 h1913 h181 h1812 h194 h1915 hZ2 hJ hPush hLift
    hctx hLM

end CFSG.RankThree.PartTwo.Sec19
