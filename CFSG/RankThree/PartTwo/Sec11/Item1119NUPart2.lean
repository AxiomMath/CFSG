module

public import CFSG.RankThree.PartTwo.Sec11.Item1119NUOut
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUGlue
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUCard
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUCtx
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSymTypes
import CFSG.RankThree.PartTwo.Sec11.Item1119SymStruct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter

namespace Item1119NU

section Part2


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_r_le_9 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hx27 : orderOf x ≤ 27)
    (hL3n : ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n))
    (hctx : Sym1119Ctx G A c L a R Y d x s r g) : orderOf r ≤ 9 := by
  have hbig := hctx.big
  have h := hbig.toSec11Data
  by_contra hgt
  push Not at hgt
  have hrR : r ∈ R := sym1119_r_mem_R h
  obtain ⟨k, hk⟩ := sym1119_pow_R h hrR
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have he3 : 3 ≤ e := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [he] at hgt
    omega
  have hrc : r * c = c * r := sym1119_R_comm_c h r hrR
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hsc : s ∈ Subgroup.zpowers c := hctx.s_eq_c ▸ Subgroup.mem_zpowers s
  have ha : a ∈ Subgroup.closure ({r, c} : Set G) := by
    refine ((Subgroup.closure_le _).mpr ?_) h.a_mem_closure
    rintro y (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsc
  have hac : a ∉ Subgroup.zpowers c := (sym1119_indep h).1
  obtain ⟨hfmem, hfnot⟩ := pow_three_pow_pred_mem (by omega : 2 ≤ e) he hrc ha3 hc3 ha hac
  have hrN : r ∈ Subgroup.normalizer (L : Set G) :=
    (Item1116Proof.le_centralizer_and_normalizer h45 h).2 hrR
  have hfN : r ^ 3 ^ (e - 1) ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hrN _
  have hnotinner := not_isInnerAut_of_mem_closure h hfmem hfnot hfN
  set ω := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨r, hrN⟩) with hω
  have hωpow : ∀ (m : ℕ) (hm : r ^ m ∈ Subgroup.normalizer (L : Set G)),
      ω ^ m = Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨r ^ m, hm⟩) := by
    intro m hm
    have h1 : (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ m = ⟨r ^ m, hm⟩ :=
      Subtype.ext (by simp)
    rw [hω, ← map_pow, ← map_pow, h1]
  have hr1 : r ^ 3 ^ e = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one r
  have hω1 : ω ^ 3 ^ e = 1 := by
    have h1 : (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ e = 1 :=
      Subtype.ext (by simpa using hr1)
    rw [hω, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hω2 : ¬ KFacts.IsInnerAut (ω ^ 3 ^ (e - 1)) := by
    rw [hωpow _ hfN]
    exact hnotinner
  obtain ⟨F, _, _, hF3, hF4, ⟨eL⟩⟩ :=
    exists_mulEquiv_psl2_of_isList1016 h.isList1016 hL3n
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpn, hFn⟩ := FiniteField.card F (ringChar F)
  have hFn' : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hFn
  have hω'1 : MulAut.congr eL ω ^ 3 ^ e = 1 := by
    rw [← map_pow, hω1, map_one]
  have hinn' := isInnerAut_pow_of_pow_three (K := F) (p := ringChar F) (n := (n : ℕ)) hpn hFn'
    hω'1
  have hinn : KFacts.IsInnerAut (ω ^ (n : ℕ)) := by
    rw [← KFacts.isInnerAut_congr eL, map_pow]
    exact hinn'
  have hdvd : 3 ^ e ∣ (n : ℕ) := three_pow_dvd_of_pow_mem (S := (MulAut.conj :
    L ⧸ aschbacherSolvableCore 3 L →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range)
    (by omega) hω1 hω2 hinn
  have hlte : 3 ^ (e + 1) ∣ (ringChar F ^ (n : ℕ)) ^ 2 - 1 :=
    three_pow_succ_dvd_sq_sub_one hpn hF3 n.pos.ne' hdvd
  have hcard : 3 ^ (e + 1) ∣ Nat.card (PSL2 F) :=
    three_pow_dvd_card_psl2 (by rw [hFn']; exact hlte)
  have hcardL : 3 ^ (e + 1) ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Nat.card_congr eL.toEquiv]
    exact hcard
  have hx : 3 ^ (e + 1) ∣ orderOf x := three_pow_dvd_orderOf_x h hcardL
  have hle : 3 ^ (e + 1) ≤ orderOf x := Nat.le_of_dvd (orderOf_pos x) hx
  have h81 : 3 ^ 4 ≤ 3 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Part2

end Item1119NU

end CFSG.RankThree.PartTwo.Sec11

end
