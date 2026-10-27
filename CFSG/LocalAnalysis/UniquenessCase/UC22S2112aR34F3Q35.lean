module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Inn
import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.Adapters.TauCetiExceptional.ReeCatalog
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35Frame
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35FrameOrthEven
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35FrameExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie (IsSmallThreeTag)
open scoped Pointwise


@[expose] def KQ35PermFunCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p : ℕ),
    (p = 3 ∨ p = 5) → StatedLieAdmissible t n p 1 → FunManyType t n → LieModel X t n p 1 →
    ∀ (P : Sylow 2 X) (r : ℕ), r.Prime → 5 ≤ r → r ≠ p → ∀ B : Subgroup X, IsPGroup r B →
      (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X) →
      (∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) → B = ⊥


theorem uc22f3q35_card_dvd_of_mem_funSet (hKc : KFunCount) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f) (ht : FunManyType t n)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    Nat.card K ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨⟨t', n', p', e, hp', hp2', hq, hfund, hadm', ψ, hsurj, hker, R, hR, rfl⟩, -⟩ := hK
  have : Fact p'.Prime := ⟨hp'⟩
  have he : 1 ≤ e := hadm'.2.1
  rcases ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2' hfund hadm' hR with hR' | ⟨rfl, -⟩
  · obtain ⟨eR⟩ := hR'
    have hcard : Nat.card (GaloisField p' e) = p ^ f := by
      rw [GaloisField.card p' e (by omega), hq]
    calc Nat.card (R.map ψ) ∣ Nat.card R := Subgroup.card_map_dvd R ψ
      _ = p ^ f * ((p ^ f) ^ 2 - 1) := by
        rw [Nat.card_congr eR.toEquiv,
          CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hcard]
  ·
    exfalso
    have hZK : center (CFSG.ClassicalInvolution.Generic.modelUniv .trialityD4 n' p' e hp').K = ⊥ :=
      CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2' (Or.inr rfl) n' he
    have hinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).1 (le_bot_iff.1 (hker.trans hZK.le))
    have hLK := CFSG.Timmesfeld.lieModel_of_center_eq_bot hZK
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .trialityD4 n' p' e hp' hfund hadm').2
    have hX' : LieModel X .trialityD4 n' p' e :=
      LieModel.of_mulEquiv (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩) hLK
    have h2 := (hKc X .trialityD4 n' p' e hp' hp2' hadm' hX' P).1 trivial
    have h3 := (hKc X t n p f hp hp2 hadm hX P).2 ht
    rw [← hq] at h2
    omega

variable {G : Type} [Group G] [Finite G]

theorem s21_12aFR34F3Q35_of_kFacts {D : Data G} {Ch : Choice2011 G}
    (hGA : GriessAllModelsStatement) (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (h5 : S21_5 D Ch) (h207 : S20_7 D) (hKF1 : KFieldAutOdd) (hKc : KFunCount)
    (hKS : KFunSplit) (hKP : KQ35PermFunCent) : S21_12aFR34F3Q35 D Ch := by
  intro hH c L hL p hp hp2 t n f hadm ht hq5 hX _ hfaith
  exfalso
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hf1 : f = 1 := by
    have hf := hadm.2.1
    by_contra hf1
    have h9 : 3 ^ 2 ≤ p ^ f :=
      (Nat.pow_le_pow_left hp3 2).trans (Nat.pow_le_pow_right hp.pos (by omega))
    norm_num at h9
    omega
  subst hf1
  have hp35 : p = 3 ∨ p = 5 := by
    rw [pow_one] at hq5
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    omega
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunManyType] at ht
  have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ 1 = 1) := by
    rintro ⟨rfl | rfl, rfl, -⟩ <;> simp [FunManyType] at ht
  have hRee : t ≠ .twistedG2 := by
    rintro rfl
    simp [FunManyType] at ht
  have hcl : (5 ≤ p ^ 1 ∧ ¬ (t = .PSL ∧ n = 2)) ∨ (p = 3 ∧ 1 = 1 ∧ ¬ IsSmallThreeTag t n) := by
    rcases hp35 with rfl | rfl
    · refine Or.inr ⟨rfl, rfl, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩) <;> simp [FunManyType] at ht
    · exact Or.inl ⟨by norm_num, hA1⟩
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX hcl)
  have h4 : 4 ≤ Open.pRank p L := by
    obtain ⟨-, ⟨⟨rfl, rfl⟩ | rfl, -⟩ | h4⟩ :=
      uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1 hA2 hRee hpN
    · simp [FunManyType] at ht
    · simp [FunManyType] at ht
    · exact h4
  obtain ⟨hpσ, hMs⟩ := uc22s2112r34_sig_of_le_pRank hσ hL hp hp2 h4
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  obtain ⟨r, hr, hr5, hrd⟩ := CFSG.exists_prime_five_le_dvd_two_pow_sub_one
    (uc22p20g_hn3_of uc22p20g_excFacts D Ch h207 hH c)
  have hrB : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hr, hrd⟩
  obtain ⟨R, hRB, -, hrR, hR2, hRT, hRr⟩ :=
    uc22s2112r34_exists_rSub_calB1 c.hB0 D.sylowM.isPGroup hr hrB.2
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' r hrR
  rw [← Subgroup.orderOf_coe] at hx₀
  have hrσ : r ∉ D.sig := by
    intro hrσ
    have hMr := UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hrσ
    obtain ⟨-, hNM, -, -⟩ := uc22s2112r2_normalizer hH c hL.1.le (hRB x₀.2) (hx₀ ▸ hr)
    refine hNM (hMr.normalizer_le ?_ (IsPGroup.of_card (n := 1) ?_)
      (zpowers_le.2 (c.hBM (hRB x₀.2))))
    · rw [Ne, zpowers_eq_bot]
      intro h
      rw [h, orderOf_one] at hx₀
      exact hr.one_lt.ne hx₀
    · rw [Nat.card_zpowers, hx₀, pow_one]
  have hrL : Open.pRank r L ≤ 3 := by
    by_contra h
    exact hrσ (uc22s2112r34_sig_of_le_pRank hσ hL hr (by omega) (by omega)).1
  have hrp : r ≠ p := fun h => hrσ (h ▸ hpσ)
  have hrg : ¬ r ∣ (genericOrders t n p 1).1 := by
    intro hrg
    obtain ⟨hPU, -, hn⟩ := uc22s2112r34_le_pRank_of_dvd hGA hL hX hr hr5 hrg
    have hn6 : 6 ≤ n := by rcases hPU with rfl | rfl <;> exact ht
    have := hn (by omega)
    omega
  have hrN := not_dvd_card_solvableRadical hL.2.2 hr (by omega)
    (uc22s2112r34_not_dvd_center hGA CFSG.TauCetiBridge.typewiseBridges hL hp hp2 hX hr hr5 hrg)
  obtain ⟨hsimp, hnc⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  have := hsimp
  have hZ : center (BarInf L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (BarInf L)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      have hb : b ∈ center (BarInf L) := h ▸ mem_top b
      exact absurd (mem_center_iff.1 hb a) hab
  obtain ⟨P, ψ, hψ, hperm⟩ := uc22s2112r34_exists_innerHom_permutes hZ (hRB.trans hBN)
    (fun x hx => uc22s2112r34_inner_of_mem hKF1 hKF7 hH c hL hp hp2 hadm hX hA1 hRee hpσ hMs hpN
      hBN hfaith hr hr5 hrg hrN hRB hRr hx)
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hRT
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine Subtype.ext (hfaith x (hRB x.2)
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 ((hRB.trans hBN) x.2) ?_))
    rw [← hψ x, hx, map_one]
  have hdvd : Nat.card ψ.range ∣ r ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm ▸ hR2
  have hprime : ∀ s : ℕ, s.Prime → s ∣ Nat.card ψ.range → s = r := fun s hs h =>
    (Nat.prime_dvd_prime_iff_eq hs hr).1 (hs.dvd_of_dvd_pow (h.trans hdvd))
  have hB1 : ψ.range ≠ ⊥ := by
    rw [Ne, ← Subgroup.card_eq_one, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    intro h
    rw [h] at hrR
    exact hr.one_lt.ne' (Nat.dvd_one.1 hrR)
  have hBc : IsMulCommutative ψ.range := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    have hxy : x * y = y * x := by
      have h := congrArg Subtype.val
        (c.hB0.2.1.is_comm.comm (⟨x, hRB x.2⟩ : c.B0) ⟨y, hRB y.2⟩)
      exact Subtype.ext h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, hxy]
  have hrk : ∀ s : ℕ, s.Prime → s ∣ Nat.card ψ.range →
      CFSG.pRank s ψ.range ≤ 2 ∧ CFSG.pRank s (⊤ : Subgroup (BarInf L)) ≤ 3 := by
    intro s hs h
    obtain rfl := hprime s hs h
    constructor
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      refine (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
        hs).trans ?_
      have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (pow_ne_zero 2 hs.ne_zero)).2 hdvd s
      simpa [hs.factorization_self] using this
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hs hrN]
      exact hrL
  have hcop : Nat.Coprime (r ^ 2) (p ^ 1 * ((p ^ 1) ^ 2 - 1)) := by
    refine Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hr).2 fun h => ?_)
    have := Nat.le_of_dvd (by rcases hp35 with rfl | rfl <;> norm_num) h
    rcases hp35 with rfl | rfl <;> interval_cases r <;> first | omega | norm_num at hr
  have hcent : ∀ K ∈ FunSet (fundPred (p ^ 1)) (BarInf L) (P : Subgroup (BarInf L)),
      ψ.range ≤ centralizer (K : Set (BarInf L)) := by
    intro K hK
    have hs := hKS (BarInf L) t n p 1 hp hp2 hadm hX hA1 hRee P ψ.range hB1 hBc
      (Odd.of_dvd_nat (hr.odd_of_ne_two (by omega)).pow hdvd)
      (fun h => by have := hprime 3 Nat.prime_three h; omega)
      (fun h => hrp (hprime p hp h).symm) hperm hrk K hK
    have hBK : ψ.range ⊓ K = ⊥ := by
      rw [← Subgroup.card_eq_one]
      exact Nat.eq_one_of_dvd_coprimes hcop
        ((Subgroup.card_dvd_of_le inf_le_left).trans hdvd)
        ((Subgroup.card_dvd_of_le inf_le_right).trans
          (uc22f3q35_card_dvd_of_mem_funSet hKc hp hp2 hadm hX ht P hK))
    rw [hBK, bot_sup_eq] at hs
    intro y hy
    exact (hs.le hy).2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 hdvd
  exact hB1 (hKP (BarInf L) t n p hp35 hadm ht hX P r hr hr5 hrp ψ.range
    (IsPGroup.of_card hk) hperm (by simpa only [pow_one] using hcent))


theorem kQ35PermFunCent_holds : KQ35PermFunCent := by
  intro X _ _ _ t n p hp35 hadm ht hX P r hr hr5 hrp B hB hperm hcent
  by_cases hrow : t = .PSp ∨ t = .PSL
  · exact eq_bot_of_forall_funSet_psp_or_psl hp35 hadm ht hX hrow P hr hr5 hB hcent
  by_cases hU : t = .PSU
  · subst hU
    exact eq_bot_of_forall_funSet_psu hp35 hadm ht hX P hr hr5 hB hcent
  by_cases hO : t = .POmegaOdd
  · subst hO
    exact eq_bot_of_forall_funSet_pOmegaOdd hp35 hadm hX P hr hr5 hrp hB hcent
  by_cases hPl : t = .POmegaPlus
  · subst hPl
    exact eq_bot_of_forall_funSet_pOmegaPlus hp35 hadm hX P hr hr5 hrp hB hcent
  by_cases hMi : t = .POmegaMinus
  · subst hMi
    exact eq_bot_of_permutes_of_forall_funSet_pOmegaMinus hp35 hadm hX P hr hr5 hrp hB hperm hcent
  have : Fact p.Prime := ⟨hadm.1⟩
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> decide
  have hq : 0 < p ^ 1 - 1 ∧ p ^ 1 - 1 < 5 ∧ ((p ^ 1) ^ 2 - 1 = 8 ∨ (p ^ 1) ^ 2 - 1 = 24) := by
    rcases hp35 with rfl | rfl <;> norm_num
  have hrq : ¬ r ∣ p ^ 1 - 1 := fun h => by
    have := Nat.le_of_dvd hq.1 h
    omega
  have hrq2 : ¬ r ∣ (p ^ 1) ^ 2 - 1 := fun h => by
    have h24 : r ∣ 2 ^ 3 * 3 := by
      rcases hq.2.2 with h8 | h8 <;> rw [h8] at h
      · exact h.mul_right 3
      · exact h
    rcases (Nat.Prime.dvd_mul hr).1 h24 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  have hr2 : r ≠ 2 := by omega
  have hcent' : ∀ K ∈ FunSet (fundPred (p ^ 1)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X) := by
    simpa only [pow_one] using hcent
  cases t
  case F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact eq_bot_of_forall_funSet_f4 hp2 hadm hX P hr hr2 hB hcent'
  case E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact eq_bot_of_forall_funSet_e6 hp2 hadm hX P hr hrq hB hcent'
  case E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact eq_bot_of_forall_funSet_e7 hp2 hadm hX P hr hrq hB hcent'
  case E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact eq_bot_of_forall_funSet_e8 hp2 hadm hX P hr hrq hB hcent'
  case twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact eq_bot_of_forall_funSet_twistedE6 hp2 hadm hX P hr hrq2 hB hcent'
  all_goals first
    | exact absurd (Or.inl rfl) hrow
    | exact absurd (Or.inr rfl) hrow
    | exact absurd rfl hU
    | exact absurd rfl hO
    | exact absurd rfl hPl
    | exact absurd rfl hMi
    | exact absurd ht (by simp [FunManyType])

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
