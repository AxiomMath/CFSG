module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
import CFSG.RankThree.PartTwo.Sec3.Item318

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL)


variable {G : Type} [Group G] [Finite G]

theorem statedClassicalModel_psl189 {X : Type} [Group X] {n p f : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n) (hf : 1 ≤ f) (h2 : (n, p ^ f) ≠ (2, 2)) (h3 : (n, p ^ f) ≠ (2, 3))
    (e : X ≃* projSL n (GaloisField p f)) : StatedClassicalModel X .PSL n p f :=
  ⟨⟨Fact.out, hf, hn, h2, h3⟩, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by omega),
    ⟨e.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSL n _)).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSL_eq_projSL n _))).symm⟩⟩

theorem statedClassicalModel_psu189 {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (hq : p ^ f ≠ 2) (e : X ≃* projSU 3 p f) :
    StatedClassicalModel X .PSU 3 p f :=
  ⟨⟨Fact.out, hf, le_rfl, fun h => hq (congrArg Prod.snd h)⟩, GaloisField p (2 * f),
    inferInstance, inferInstance,
    by rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul],
    ⟨e.trans (Sec4.projSUEquivStatedProj 3 p f)⟩⟩

theorem aschbacherSolvableCore_eq_pCore189 {K : Subgroup G}
    (h3 : inSubgroup (CFSG.pPrimeCore 3) K = CFSG.Open.pCoreOf 2 K) :
    aschbacherSolvableCore 3 ↥K = CFSG.pCore 2 ↥K := by
  have hpp : CFSG.pPrimeCore 3 ↥K = CFSG.pCore 2 ↥K := by
    apply Subgroup.map_injective K.subtype_injective
    exact h3
  have hchar := solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  refine le_antisymm ?_ (hchar.2.2.2.2.2.2 2 Nat.prime_two (by norm_num))
  rw [← hpp]
  exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hchar.2.2.1⟩

theorem step189O2_of
    (hK0 : Step189K0) (hType : Step189KType) (hQ : Step189Q) (hL3 : Sec3.L3SingerFact)
    (hJ1 : Sec3.J1SevenFact) : Sec20.Step189O2 := by
  intro G _ _ A M H c h h7 hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKθ, hrank⟩ := hK0 G A M H c h h7
  have htype := hType G A M H c h h7 hKθ hrank
  obtain ⟨h3, V, _, _, _, _, ρ, hfix⟩ := hQ G A M H c h h7 hKθ hrank hO
  have hθ := aschbacherSolvableCore_eq_pCore189 h3
  have hperf := isPerfect_of_mem_thetaComponentsIn189 hKθ
  set Q := ↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c) with hQdef
  let eθ : Q ≃* ↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c) :=
    QuotientGroup.quotientMulEquivOfEq hθ.symm
  have hK318 : (∃ p f, StatedClassicalModel Q .PSL 2 p f ∧ p ≠ 3) ∨
      (∃ p f, StatedClassicalModel Q .PSL 3 p f ∧ p ^ f % 3 = 2) ∨
      (∃ p f, StatedClassicalModel Q .PSU 3 p f ∧ p ^ f % 3 = 1) ∨
      Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J1) := by
    rcases htype with ⟨p, f, hp, hp3, hf, ⟨e⟩⟩ | ⟨p, f, hp, hf, hq, ⟨e⟩⟩ |
        ⟨p, f, hp, hf, hq, ⟨e⟩⟩ | hJ
    · have hq3 : p ^ f ≠ 3 := by
        intro h33
        have hpd : p ∣ 3 := h33 ▸ dvd_pow_self p (by omega)
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hpd)
      have hq2 : p ^ f ≠ 2 := by
        intro h22
        have hpd : p ∣ 2 := h22 ▸ dvd_pow_self p (by omega)
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hpd
        subst hp2
        have hf1 : f = 1 := Nat.pow_right_injective le_rfl (h22.trans (pow_one 2).symm)
        subst hf1
        exact not_nonempty_equiv_projSL_two_one189 ⟨eθ.trans e⟩
      exact Or.inl ⟨p, f, statedClassicalModel_psl189 le_rfl hf
        (fun h => hq2 (congrArg Prod.snd h)) (fun h => hq3 (congrArg Prod.snd h)) (eθ.trans e),
        hp3⟩
    · exact Or.inr (Or.inl ⟨p, f, statedClassicalModel_psl189 (by norm_num) hf
        (fun h => absurd (congrArg Prod.fst h) (by norm_num))
        (fun h => absurd (congrArg Prod.fst h) (by norm_num)) (eθ.trans e), hq⟩)
    · have hq2 : p ^ f ≠ 2 := fun h22 => by rw [h22] at hq; norm_num at hq
      exact Or.inr (Or.inr (Or.inl ⟨p, f, statedClassicalModel_psu189 hf hq2 (eθ.trans e), hq⟩))
    · obtain ⟨e⟩ := hJ
      exact Or.inr (Or.inr (Or.inr ⟨eθ.trans e⟩))
  have hcK : c ∈ normalClosureIn M c := Sec20.self_mem_normalClosureIn M c
  have hc3 := pow_three_of_sec18H189 h
  have hc1 := ne_one_of_pRank_eq_one189 hrank
  set x : Q := ((⟨c, hcK⟩ : ↥(normalClosureIn M c)) : Q) with hxdef
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← QuotientGroup.mk_pow]
    have : (⟨c, hcK⟩ : ↥(normalClosureIn M c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, QuotientGroup.mk_one]
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hxdef, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(normalClosureIn M c))) ⟨_, h1⟩
    have hc2k : c ^ (2 ^ k) = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥(normalClosureIn M c)) =>
        ((y : ↥(normalClosureIn M c)) : G)) hk
      simpa using this
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc3) with h1' | h3'
    · exact hc1 (orderOf_eq_one_iff.mp h1')
    · have h32 : 3 ∣ 2 ^ k := h3' ▸ orderOf_dvd_of_pow_eq_one hc2k
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h32)
      omega
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨n, hadm, F, _, _, hF, ⟨e⟩⟩ := Sec3.rank3II_3_18_of_singer_j1 hL3 hJ1 hK318 hx ρ
    (hfix ⟨c, hcK⟩ rfl)
  exact ⟨n, hadm.2.1, ⟨(e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n
    hadm.2.1 hF)).trans (Sec4.projSLEquivPSL (GaloisField 2 n)).symm⟩⟩

section Certs


theorem item189_of_frontier (h1812 : Item181_2) (h1813 : Item181_3) (h184 : Item184_1)
    (h186 : Item186H) (h187 : Item187) (hL3 : Sec3.L3SingerFact) (hJ1 : Sec3.J1SevenFact)
    (h1411 : Asc82Item1411And1412) (hK0 : Step189K0)
    (hType : Step189KType) (hQ : Step189Q) (hO2B : Step189O2Bound) (hList : Step189List)
    (hrk : Step189TwoRank) (hOdd : Step189OddL2) (hInsp : Step189InspectI)
    (hIdx : Step189IndexI) (hL16 : Step189L16) (hL4 : Step189L4) (hO3 : Step189O3) :
    Item189 :=
  item189_of h1812 h1813 h184 h186 h187 hK0 hType (step189O2_of hK0 hType hQ hL3 hJ1) hO2B
    hList (step189FourNe_of hrk) hOdd hInsp hIdx h1411 hL16 hL4 hO3

end Certs

end CFSG.RankThree.PartTwo.Sec18
