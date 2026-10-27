module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Many
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Inn
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.Adapters.TauCetiExceptional.ReeCatalog
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]


theorem s21_12aFR34F3_of {D : Data G} {Ch : Choice2011 G} (hGA : GriessAllModelsStatement)
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (h5 : S21_5 D Ch) (h207 : S20_7 D)
    (hree : ∀ (_ : H1930 D) (_ : Ctx21 D Ch), ∀ L ∈ calC D.M, ∀ f : ℕ,
      LieModel (BarInf L) .twistedG2 0 3 f → False)
    (hKFun : PartTwo.Inputs1719.K_FunCommute) (hKF1 : KFieldAutOdd) (hKc : KFunCount)
    (hKS : KFunSplit) (h35 : S21_12aFR34F3Q35 D Ch) : S21_12aFR34F3 D Ch := by
  intro hH c L hL p hp hp2 t n f hadm ht hX hno hfaith
  by_cases hq5 : p ^ f ≤ 5
  · exact h35 hH c L hL p hp hp2 t n f hadm ht hq5 hX hno hfaith
  exfalso
  have hq7 : 7 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
    omega
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunManyType] at ht
  have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1) := by
    rintro ⟨rfl | rfl, rfl, -⟩ <;> simp [FunManyType] at ht
  have hRee : t ≠ .twistedG2 := by
    rintro rfl
    simp [FunManyType] at ht
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by omega, hA1⟩))
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
  have hrg : ¬ r ∣ (genericOrders t n p f).1 := by
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
  obtain ⟨y, hyB, hy1, K₂, K₃, h₂, h₃, hc, hK⟩ := uc22s2112r34_exists_fixed_pair hKFun hKc hKS
    hnc hp hp2 hadm ht hX hno (by rw [← pRank_eq_pRank_barInf hp hpN]; exact h4)
    (fun f hm => hree hH c L hL f hm) (by omega) P hB1 hBc
    (Odd.of_dvd_nat (hr.odd_of_ne_two (by omega)).pow hdvd)
    (fun h => by have := hprime 3 Nat.prime_three h; omega)
    (fun h => hrp (hprime p hp h).symm) hperm hrk
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hyB
  rw [hψ x] at hK
  have hx1 : (x : G) ≠ 1 := fun h => hy1 (by rw [show x = 1 from Subtype.ext h, map_one])
  have hord := hRr x x.2 hx1
  exact uc22s2112r34_false_of_pair hKF7 hH c hL.1.le hp hp2 hq7 hpσ hMs (hRB x.2) _
    (hord ▸ hr) (hord ▸ hrN) hpN h₂ h₃ hc hK

section Setup


theorem s21_12aFR34F3_dataOfSetup4 (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) {Ch : Choice2011 G}
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → Ch L₀ B₀)
    (hKF7 : KF7Use (UC6.dataOfSetup4 hS hU S)) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch)
    (h207 : S20_7 (UC6.dataOfSetup4 hS hU S)) (h82 : F08.R82 (UC6.dataOfSetup4 hS hU S))
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (hKFun : PartTwo.Inputs1719.K_FunCommute)
    (hKF1 : KFieldAutOdd) (hKc : KFunCount) (hKS : KFunSplit)
    (h35 : S21_12aFR34F3Q35 (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S))) :
    S21_12aFR34F3 (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S)) :=
  s21_12aFR34F3_of hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hKF7
    (fun hH c => h5 hH (c.mono hCh)) h207
    (fun hH c _ hL _ hm => uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm)
    hKFun hKF1 hKc hKS h35

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
