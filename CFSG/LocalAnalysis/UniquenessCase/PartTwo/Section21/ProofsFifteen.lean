module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

section Fifteen

variable {G : Type} [Group G] [Finite G]

private theorem shape_conj {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  exact hshape.imp (fun h => CFSG.Blueprint.LieModel.of_mulEquiv e h)
    (fun h => CFSG.Blueprint.LieModel.of_mulEquiv e h)

omit [Finite G] in
theorem conjClosure_eq_self_of_ncard_eq_one {M L : Subgroup G}
    (h : (conjSetOf M L).ncard = 1) : conjClosure M L = L := by
  obtain ⟨K, hK⟩ := Set.ncard_eq_one.mp h
  have hLmem : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext x; simp⟩
  have hKL : K = L := by
    have : L ∈ ({K} : Set (Subgroup G)) := hK ▸ hLmem
    have hLK : L = K := by simpa using this
    exact hLK.symm
  unfold conjClosure
  rw [hK, hKL]
  simp

theorem five_lt_of_dvd_two_pow_sub_one {s r : ℕ} (hs : Odd s) (hr : r.Prime)
    (hrdvd : r ∣ 2 ^ s - 1) : 5 < r := by
  have hr3 : r ≠ 3 := by
    intro h3
    subst h3
    exact CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one hs hrdvd
  have hr5 : r ≠ 5 := by
    intro h5
    subst h5
    obtain ⟨m, rfl⟩ := hs
    exact CFSG.SignalizerFunctorTheorem.McBride.SzModel.not_five_dvd_two_pow_sub_one m hrdvd
  have hr2 : r ≠ 2 := by
    have hs0 : 0 < s := by
      obtain ⟨k, hk⟩ := hs
      omega
    have hodd : Odd r := (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hs0).of_dvd_nat hrdvd
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  by_contra h
  have hrle : r ≤ 5 := by omega
  have hrge : 2 ≤ r := hr.two_le
  interval_cases r <;> simp_all
  norm_num at hr

theorem s21_15_ncard_ne_three {D : Data G} {L : Subgroup G} {n s r : ℕ}
    (h899 : F08.R899 D) (hL : L ∈ calC D.M)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hnotStrong : ¬ IsStronglyPEmbedded r D.M) (hsOdd : Odd s) (hsdvd : s ∣ n)
    (hrPrime : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (h3 : (conjSetOf D.M L).ncard = 3) : False := by
  obtain ⟨L0, L1, L2, h01, h02, h12, hset⟩ := Set.ncard_eq_three.mp h3
  let f : Fin 3 → Subgroup G := fun i =>
    if i = 0 then L0 else if i = 1 then L1 else L2
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hfmem : ∀ i, f i ∈ calC D.M := by
    intro i
    fin_cases i <;>
      exact uc22p2214_calC_of_mem_conjSetOf hL (by rw [hset]; simp [f])
  have hfshape : ∀ i, IsSz (Bar2 (f i)) n ∨ IsL2 (Bar2 (f i)) n := by
    intro i
    have hmem : f i ∈ conjSetOf D.M L := by
      fin_cases i <;> (rw [hset]; simp [f])
    rcases shape_conj hmem hshape with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hrange : Set.range f = {N | ∃ m ∈ D.M, N = (f 0).map (MulAut.conj m).toMonoidHom} ∨
      ∀ i, D.M ≤ normalizer (f i : Set G) := by
    left
    have hf0 : f 0 ∈ conjSetOf D.M L := by rw [hset]; simp [f]
    calc Set.range f = ({L0, L1, L2} : Set (Subgroup G)) := by
          ext K
          constructor
          · rintro ⟨i, rfl⟩
            fin_cases i <;> simp [f]
          · intro hK
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
            rcases hK with rfl | rfl | rfl
            · exact ⟨0, by simp [f]⟩
            · exact ⟨1, by simp [f]⟩
            · exact ⟨2, by simp [f]⟩
      _ = conjSetOf D.M L := hset.symm
      _ = conjSetOf D.M (f 0) := (uc22p2214_conjSetOf_eq hf0).symm
  exact hnotStrong (h899 f (fun _ => n) s r hf_inj hfmem hfshape hsOdd
    (fun _ => hsdvd) hrPrime hrdvd hrange)

theorem s21_15_not_strong_of_torus {D : Data G} {Ch : Choice2011 G} {L : Subgroup G} {n s r : ℕ}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) (hL : L ∈ calC D.M)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hne : conjClosure D.M L ≠ L)
    (hsOdd : Odd s) (hsdvd : s ∣ n) (hrPrime : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (htor : S21_15Torus D Ch) : ¬ IsStronglyPEmbedded r D.M := by
  obtain ⟨X, hXcard, hXM, hXN⟩ :=
    htor h1930 c L hL n hshape hne s hsOdd hsdvd r hrPrime hrdvd
  have hs0 : 0 < s := by
    obtain ⟨k, hk⟩ := hsOdd
    omega
  have hrOdd : Odd r := (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hs0).of_dvd_nat hrdvd
  have hpX : (Nat.card X).Prime := by rw [hXcard]; exact hrPrime
  have hoddX : Odd (Nat.card X) := by rw [hXcard]; exact hrOdd
  have hXnotU : X ∉ uniqueSet D.M :=
    not_mem_uniqueSet_of_le_normalizer D Ch h211 h1930 c hpX hoddX hXM hXN
  have hXne : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card X = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hXcard] at h1
    exact hrPrime.ne_one h1
  have hXp : IsPGroup r ↥X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  intro hstr
  exact hXnotU (mem_uniqueSet_of_isStronglyPEmbedded hrPrime hstr hXM hXne hXp)

theorem s21_15_pRank_le_three {D : Data G} {r : ℕ} (hSg : UC6S846.SigmaStd D)
    (hrPrime : r.Prime) (hr2 : r ≠ 2) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnotStrong : ¬ IsStronglyPEmbedded r D.M) : CFSG.Open.pRank r D.M ≤ 3 := by
  by_contra h
  have h4 : 4 ≤ CFSG.Open.pRank r D.M := by omega
  have hpSig : r ∈ D.sig := hSg.four_mem r hrPrime hr2 h4
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  exact hnotStrong (hSg.sig1_sp r (UC6S846.sig_subset_sig1 hSg hns hpSig))

theorem ncard_eq_two_of_bounds {M L : Subgroup G}
    (h3 : (conjSetOf M L).ncard ≤ 3) (h1 : (conjSetOf M L).ncard ≠ 1)
    (h3ne : (conjSetOf M L).ncard ≠ 3) : (conjSetOf M L).ncard = 2 := by
  have hpos : 0 < (conjSetOf M L).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2
      ⟨L, ⟨1, M.one_mem, by ext x; simp⟩⟩
  have hge : 2 ≤ (conjSetOf M L).ncard := by omega
  omega

end Fifteen

end CFSG.LocalAnalysis.UniquenessCase.UC22
