module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34AlphaDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2Uniq
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34FixOdd
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Swap
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Ident
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitInnerModels
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
import CFSG.GroupTheory.SquarefreeOrder
import CFSG.GroupTheory.PRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

section Defs


@[expose] def S21_12aFR34L3E2Inner3 (D : Data G) : Prop :=
  H1930 D → ∀ c : Ctx21 D (Choice214U D), ∀ L ∈ calC D.M,
    ∀ hBN : c.B0 ≤ normalizer (L : Set G), (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    ∀ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime → p ≠ 2 → 2 ≤ f →
    LieModel (BarInf L) t 3 p f → p ∈ D.sig → IsStronglyPEmbedded p D.M →
    ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L) → 3 ∣ (genericOrders t 3 p f).1 →
    ∀ y (hy : y ∈ c.B0), orderOf y = 3 →
    ∀ (K : Subgroup (BarInf L)) (x : BarInf L), IsFundamentalOver (p ^ f) K → x ∈ K →
      (orderOf x).Prime → 5 ≤ orderOf x → orderOf x ≠ p →
      inducedBarInfAutHom L ⟨y, hBN hy⟩ * MulAut.conj x =
        MulAut.conj x * inducedBarInfAutHom L ⟨y, hBN hy⟩ →
      inducedBarInfAutHom L ⟨y, hBN hy⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range

end Defs

section Main


private theorem uc22s2112r34_l3E2_map_conj_eq_of_acts {X : Type} [Group X]
    {K : Subgroup X} {u v : X} (hv : v ∈ K)
    (h : ∀ z ∈ K, MulAut.conj u z = MulAut.conj v z) :
    K.map (MulAut.conj u).toMonoidHom = K := by
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    change MulAut.conj u y ∈ K
    rw [h y hy, MulAut.conj_apply]
    exact K.mul_mem (K.mul_mem hv hy) (K.inv_mem hv)
  · intro z hz
    let y : X := (MulAut.conj v)⁻¹ z
    have hy : y ∈ K := by
      dsimp [y]
      exact K.mul_mem (K.mul_mem (K.inv_mem hv) hz) hv
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    change MulAut.conj u y = z
    rw [h y hy]
    dsimp [y]
    group

private theorem uc22s2112r34_l3E2_exists_inverter {X : Type} [Group X] [Finite X]
    {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K R Q : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K)
    (hRK : R ≤ K) (hR1 : R ≠ ⊥)
    (hRQ : Permutes R Q)
    (hcardR : Nat.card R ∣ r ^ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) :
    ∃ t ∈ Q, ∀ y ∈ K ⊓ centralizer (R : Set X), t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨p', e₀, e, hp'fact, hp'2, he₀, hq', he, φ, hφrange, hφker⟩ :=
    uc22s2112r34_exists_sl2_cover hK
  have hp' : p'.Prime := hp'fact.out
  have hpp' : p' = p := by
    have hd : p' ∣ p ^ f := by
      rw [hq']
      exact dvd_pow_self p' (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp' hp).1 (hp'.dvd_of_dvd_pow hd)
  subst p'
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> omega
  have hr6 : ¬ r ∣ 6 := by
    intro h
    rw [show 6 = 2 * 3 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hr).mp h with h2 | h3
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
      have := Nat.prime_two.two_le
      omega
    · have := Nat.le_of_dvd (by norm_num : 0 < 3) h3
      have := Nat.prime_three.two_le
      omega
  have hrp' : ¬ r ∣ p := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)
  have hcop6 : Nat.Coprime r 6 := (Nat.Prime.coprime_iff_not_dvd hr).2 hr6
  have hcopp : Nat.Coprime r p := (Nat.Prime.coprime_iff_not_dvd hr).2 hrp'
  have hcop' : Nat.Coprime r (6 * p) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hcop6, hcopp⟩
  have hcop : Nat.Coprime (r ^ 2) (6 * p) := hcop'.pow_left 2
  have hRc : Nat.Coprime (Nat.card R) (6 * p) :=
    Nat.Coprime.of_dvd_left hcardR hcop
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 2 Q φ.range := by
    rwa [hφrange]
  have hRK' : R ≤ φ.range := by rwa [hφrange]
  let hpFact : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htQ, htInv⟩ :=
    @uc22s2112r34_exists_inv_centralizer_sl2
      X _ _ p e hpFact hp2 he1 φ hφker Q R hQ' hRK' hRQ hR1 hRc
  exact ⟨t, htQ, by simpa [hφrange] using htInv⟩

private theorem uc22s2112r34_l3E2_normalizes {X : Type} [Group X] [Finite X]
    {p f r : ℕ} {K R : Subgroup X} (hK : IsFundamentalOver (p ^ f) K)
    (hRK : R ≤ K) {x y : X} (hxc : x ∈ centralizer (R : Set X))
    (hyR : y ∈ R) (hord : orderOf y = r)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p)
    (huniq : ∀ K K' : Subgroup X, IsFundamentalOver (p ^ f) K →
      IsFundamentalOver (p ^ f) K' → ∀ z ∈ K ⊓ K', (orderOf z).Prime → 5 ≤ orderOf z →
        orderOf z ≠ p → K = K') :
    x ∈ normalizer (K : Set X) := by
  have hK' : IsFundamentalOver (p ^ f) (K.map (MulAut.conj x).toMonoidHom) :=
    isFundamentalOver_map_mulEquiv (MulAut.conj x) hK
  have hyK : y ∈ K := hRK hyR
  have hyK' : y ∈ K.map (MulAut.conj x).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨y, hyK, ?_⟩
    change MulAut.conj x y = y
    rw [MulAut.conj_apply]
    have h := mem_centralizer_iff.1 hxc y hyR
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h]
      _ = y := by group
  have hEq : K = K.map (MulAut.conj x).toMonoidHom :=
    huniq K (K.map (MulAut.conj x).toMonoidHom) hK hK' y ⟨hyK, hyK'⟩
      (by rw [hord]; exact hr) (by rw [hord]; exact hr5) (by rw [hord]; exact hrp)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hEq.symm

private theorem uc22s2112r34_l3E2_inner_on {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    {K R : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hRK : R ≤ K) {x : X}
    (hxN : x ∈ normalizer (K : Set X)) (hxo : Odd (orderOf x))
    (hxc : x ∈ centralizer (R : Set X)) :
    ∃ k : ↥K, (∀ a ∈ K, x * a * x⁻¹ = (k : X) * a * (k : X)⁻¹) ∧
      (k : X) ∈ centralizer (R : Set X) := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (odd_normalizer_inner_of_isFundamentalOver_general hK hxN hxo)
  have hk' : K.normalizerMonoidHom ⟨x, hxN⟩ = MulAut.conj k := hk.symm
  have hact : ∀ a ∈ K, x * a * x⁻¹ = (k : X) * a * (k : X)⁻¹ := by
    intro a ha
    rw [← Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hxN⟩ ⟨a, ha⟩, hk']
    simp [MulAut.conj_apply]
  refine ⟨k, hact, ?_⟩
  rw [mem_centralizer_iff]
  intro y hy
  have hyK : y ∈ K := hRK hy
  have hxy : x * y = y * x := (mem_centralizer_iff.1 hxc y hy).symm
  have hfix : x * y * x⁻¹ = y := by rw [hxy]; group
  have hky : (k : X) * y * (k : X)⁻¹ = y := by rw [← hact y hyK, hfix]
  calc y * (k : X) = ((k : X) * y * (k : X)⁻¹) * (k : X) := by rw [hky]
    _ = (k : X) * y := by group

theorem uc22s2112r34_false_l3E2 (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hGA : GriessAllModelsStatement)
    {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {p f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf2 : 2 ≤ f) (hX : LieModel (BarInf L) t 3 p f)
    (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f)
    (hG1 : S21_12aFR34L3E2Inner3 D) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (t : StatedLieTag), (t = .PSL ∨ t = .PSU) →
      StatedLieAdmissible t 3 p f → LieModel (BarInf L) t 3 p f → False := by
    intro t ht hadm hX
    have hRee : t ≠ .twistedG2 := by rcases ht with rfl | rfl <;> nofun
    have hA1 : ¬ (t = .PSL ∧ 3 = 2) := fun h => absurd h.2 (by norm_num)
    have : IsSimpleGroup (BarInf L) :=
      (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
    have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hq9 : 9 ≤ p ^ f :=
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
    have hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
      not_dvd_card_solvableRadical hL.2.2 hp hp2
        (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by omega, hA1⟩))
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1
      (fun h => by have := h.2.2; omega) hRee hpN
    have h4' : 4 ≤ CFSG.Open.pRank p L := by rcases h4 with ⟨-, h1⟩ | h4 <;> omega
    obtain ⟨hpσ, hMs⟩ := uc22s2112r34_sig_of_le_pRank hσ hL hp hp2 h4'
    have hL3 : ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsL3EpsOdd17 (BarInf L) p :=
      uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
    have hZ3 : Nat.card (center (Bar2 L)) ∣ 3 :=
      uc22s213_card_center_bar2_dvd_three hGA hL ht hX
    have hN5 : ∀ s : ℕ, s.Prime → 5 ≤ s →
        ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
      intro s hs hs5
      refine not_dvd_card_solvableRadical hL.2.2 hs (by omega) (fun h => ?_)
      have h3 : s ∣ 3 := h.trans hZ3
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    have hg3 : (genericOrders t 3 p f).1 ∣ 3 := by
      rcases ht with rfl | rfl <;> simpa [genericOrders] using Nat.gcd_dvd_left 3 _
    obtain ⟨r, hrπ, hrp, hr5, -⟩ :=
      uc22s2112r34_exists_prime_mem_piSet hσ hH c hn3 hL hpσ
    have hr : r.Prime := hrπ.1
    have hrN : ¬ r ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := hN5 r hr hr5
    have hrg : ¬ r ∣ (genericOrders t 3 p f).1 := by
      intro h
      have h3 : r ∣ 3 := h.trans hg3
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    obtain ⟨R, hRB, -, hrR, hRr2, hRT, hRr⟩ :=
      uc22s2112r34_exists_rSub_calB1 c.hB0 D.sylowM.isPGroup hr hrπ.2
    have hRN : R ≤ normalizer (L : Set G) := hRB.trans hBN
    have hinnR : ∀ x (hx : x ∈ R),
        inducedBarInfAutHom L ⟨x, hRN hx⟩ ∈
          (MulAut.conj : BarInf L →* MulAut (BarInf L)).range :=
      fun x hx => uc22s2112r34_inner_of_mem hKF1 hKF7 hH c hL hp hp2 hadm hX hA1 hRee hpσ
        hMs hpN hBN hfaith hr hr5 hrg hrN hRB hRr (x := x) hx
    obtain ⟨P, ψ, -, hψ, -, hperm, -, hPT⟩ :=
      uc22s2112r34_exists_innerHom_permutes_of_T (B := R) hZ hRN hinnR hRN hinnR
        (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hRT hRT
    have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hzc : z ∈ center (BarInf L) := by
        rw [mem_center_iff]
        intro w
        have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc w * z = z * w * z⁻¹ * z := by rw [h]
          _ = z * w := by group
      rwa [hZ, mem_bot] at hzc
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ = 1 := by
        rw [← hψ x, hx, map_one]
      exact Subtype.ext (hfaith x (hRB x.2)
        (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 _ h1))
    have hcardB : Nat.card ψ.range = Nat.card R :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    have hne : ψ.range ≠ ⊥ := fun h => by
      rw [h, card_bot] at hcardB
      rw [← hcardB] at hrR
      exact hr.one_lt.ne' (Nat.dvd_one.1 hrR)
    have : IsMulCommutative ↥c.B0 := c.hB0.2.1
    have : IsMulCommutative ↥R := isMulCommutative_anti hRB
    have hoddB : Odd (Nat.card ψ.range) := by
      rw [hcardB]
      exact (hr.odd_of_ne_two (by omega)).pow.of_dvd_nat hRr2
    have h3B : ¬ 3 ∣ Nat.card ψ.range := fun h => by
      rw [hcardB] at h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
        (Nat.prime_three.dvd_of_dvd_pow (h.trans hRr2))
      omega
    have hpB : ¬ p ∣ Nat.card ψ.range := fun h => by
      rw [hcardB] at h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow (h.trans hRr2))).symm
    have hrank : ∀ s : ℕ, s.Prime → s ∣ Nat.card ψ.range →
        CFSG.pRank s ψ.range ≤ 2 ∧ CFSG.pRank s (⊤ : Subgroup (BarInf L)) ≤ 3 := by
      intro s hs hsd
      rw [hcardB] at hsd
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hs hr).1 (hs.dvd_of_dvd_pow (hsd.trans hRr2))
      refine ⟨?_, ?_⟩
      · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
        refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hs fun h => ?_
        rw [hcardB] at h
        have := (Nat.pow_dvd_pow_iff_le_right hs.one_lt).1 (h.trans hRr2)
        omega
      · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hs hrN]
        exact (CFSG.SectionRank.pRank_mono hs.one_lt hL.1.le).trans
          (uc22s2112r34_pRank_le_three hσ hH c hL hrπ (by omega))
    obtain ⟨K, hK⟩ :=
      uc22s2112r34_funSet_nonempty_barInf hL hp hp2 hX hno hL3 hree (by omega) P
    have hspl := hKS (BarInf L) t 3 p f hp hp2 hadm hX hA1 hRee P ψ.range hne inferInstance
      hoddB h3B hpB hperm hrank K hK
    have hR0 : ψ.range ⊓ centralizer (K : Set (BarInf L)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      by_contra hyne
      obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨a, ha, rfl⟩ := MonoidHom.mem_range.1 hyR
      have ha1 : (a : G) ≠ 1 := by
        intro h
        apply hyne
        rw [show a = 1 from Subtype.ext h, map_one]
        exact Subgroup.mem_bot.mpr rfl
      have hfix : ∀ k ∈ K, inducedBarInfAutHom L ⟨(a : G), hRN a.2⟩ k = k := by
        intro k hk
        rw [← hψ a, MulAut.conj_apply, ← mem_centralizer_iff.1 hyC k hk, mul_inv_cancel_right]
      have hKb : K ≤ signalizerFixedSubgroup
          (inducedBarInfAutHom L ⟨(a : G), hRN a.2⟩) := fun k hk => hfix k hk
      exact uc22s2112r34_false_of_fund hKF7 hH c hL.1.le hp hp2 hf2 hpσ hMs (hRB a.2)
        (hRN a.2) (by rw [hRr a a.2 ha1]; exact hr) (by rw [hRr a a.2 ha1]; exact hrN)
        hpN hK.1 hKb
    have hRK : ψ.range ≤ K := by
      rw [hspl, hR0, sup_bot_eq]
      exact inf_le_right
    have hcardR : Nat.card ψ.range ∣ r ^ 2 := by
      rw [hcardB]
      exact hRr2
    let Psub : Subgroup (BarInf L) := P
    have hpermP : Permutes ψ.range Psub := hperm
    have hpermQ : Permutes ψ.range (Psub ⊓ K) := by
      rw [Permutes] at hpermP
      rw [Permutes, Subgroup.mul_inf_assoc ψ.range Psub K hRK, inf_comm Psub K,
        Subgroup.inf_mul_assoc K Psub ψ.range hRK, hpermP, Set.inter_comm]
    obtain ⟨u, huQ, hu_inv⟩ :=
      uc22s2112r34_l3E2_exists_inverter hp hp2 hK.1 (by simpa [Psub] using hK.2) hRK hne hpermQ
        hcardR hr hr5 hrp
    have huP : u ∈ (P : Subgroup (BarInf L)) := huQ.1
    have huK : u ∈ K := huQ.2
    obtain ⟨s, hsT, hsN, hsu⟩ := hPT u huP
    obtain ⟨y₁, hy₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨a₁, hψa₁⟩ := MonoidHom.mem_range.1 y₁.2
    have hy₁1' : (y₁ : BarInf L) ≠ 1 := fun h => hy₁1 (Subtype.ext h)
    have ha₁G1 : (a₁ : G) ≠ 1 := by
      intro h
      apply hy₁1'
      rw [← hψa₁, show a₁ = 1 from Subtype.ext h, map_one]
    have hord₁ : orderOf (y₁ : BarInf L) = r := by
      rw [← hψa₁]
      calc orderOf (ψ a₁) = orderOf a₁ := orderOf_injective ψ hψinj a₁
        _ = orderOf (a₁ : G) := (Subgroup.orderOf_coe a₁).symm
        _ = r := hRr a₁ a₁.2 ha₁G1
    have hprime_case : ∀ b (hb : b ∈ c.B0), (orderOf b).Prime →
        inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈
          (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
      intro b hb hbp
      have hodd : Odd (orderOf b) :=
        Odd.of_dvd_nat (ch214_odd_card c.hpi) (Subgroup.orderOf_dvd_natCard c.B0 hb)
      by_cases hb5 : 5 ≤ orderOf b
      · have hrg' : ¬ orderOf b ∣ (genericOrders t 3 p f).1 := by
          intro h
          have h3 : orderOf b ∣ 3 := h.trans hg3
          have := Nat.le_of_dvd (by norm_num) h3
          omega
        by_cases hθ1 : inducedBarInfAutHom L ⟨b, hBN hb⟩ = 1
        · exact ⟨1, by rw [hθ1, map_one]⟩
        · exact uc22s2112r34_inner_of_kFieldAutOdd hKF1 hKF7 hH c hL hp hp2 hadm hX hA1 hRee
            hpσ hMs hpN hb (hBN hb) hbp hb5 rfl hrg' (hN5 (orderOf b) hbp hb5) hθ1
      · have hb3 : orderOf b = 3 := by
          obtain ⟨k, hk⟩ := hodd
          have := hbp.two_le
          omega
        by_cases h3g : 3 ∣ (genericOrders t 3 p f).1
        ·
          have hba : b * (a₁ : G) = (a₁ : G) * b := by
            have := c.hB0.2.1.is_comm.comm ⟨b, hb⟩ ⟨(a₁ : G), hRB a₁.2⟩
            exact congrArg Subtype.val this
          have hcommN : (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G))) *
              ⟨(a₁ : G), hRN a₁.2⟩ =
              ⟨(a₁ : G), hRN a₁.2⟩ * ⟨b, hBN hb⟩ := Subtype.ext hba
          have hθcomm : inducedBarInfAutHom L ⟨b, hBN hb⟩ *
              inducedBarInfAutHom L ⟨(a₁ : G), hRN a₁.2⟩ =
              inducedBarInfAutHom L ⟨(a₁ : G), hRN a₁.2⟩ *
                inducedBarInfAutHom L ⟨b, hBN hb⟩ := by
            rw [← map_mul, ← map_mul, hcommN]
          rw [← hψ a₁] at hθcomm
          refine hG1 hH c L hL hBN hfaith t p f ht hp hp2 hf2 hX hpσ hMs hpN h3g b hb hb3
            K (ψ a₁) hK.1 (hRK (by rw [hψa₁]; exact y₁.2))
            (by rw [hψa₁, hord₁]; exact hr) (by rw [hψa₁, hord₁]; exact hr5)
            (by rw [hψa₁, hord₁]; exact hrp) hθcomm
        ·
          exact uc22s2112r34_inner_of_ne_two hKF7 hH c hL ht hp hp2 hadm hX hA1 hpσ hMs hpN
            hb (hBN hb) Nat.prime_three (by norm_num) hb3 h3g
    have hinn : ∀ b (hb : b ∈ c.B0), inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
      intro b hb
      let N : Subgroup G := normalizer (L : Set G)
      let θN : ↥N →* MulAut (BarInf L) := inducedBarInfAutHom L
      let H : Subgroup ↥N :=
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range.comap θN
      have hsq : Squarefree (orderOf (⟨b, hBN hb⟩ : ↥N)) := by
        rw [Subgroup.orderOf_mk]
        exact Ctx23L.orderOf_squarefree_of_mem_calB1 c.hB0 hb
      have hmem : (⟨b, hBN hb⟩ : ↥N) ∈ H := by
        refine CFSG.GroupTheory.mem_of_forall_prime_orderOf_pow_mem hsq ?_
        intro k hk
        have hb' : b ^ k ∈ c.B0 := c.B0.pow_mem hb k
        have hsub : (⟨b, hBN hb⟩ : ↥N) ^ k = ⟨b ^ k, hBN hb'⟩ := Subtype.ext rfl
        have hord : orderOf ((⟨b, hBN hb⟩ : ↥N) ^ k) = orderOf (b ^ k) := by
          rw [hsub]
          exact Subgroup.orderOf_mk (b ^ k) (hBN hb')
        have hbp' : (orderOf (b ^ k)).Prime := hord ▸ hk
        have hpow : θN ((⟨b, hBN hb⟩ : ↥N) ^ k) =
            inducedBarInfAutHom L ⟨b ^ k, hBN hb'⟩ := by
          rw [hsub]
        refine Subgroup.mem_comap.2 ?_
        rw [hpow]
        exact hprime_case (b ^ k) hb' hbp'
      rw [Subgroup.mem_comap] at hmem
      exact hmem
    have huniq : ∀ K K' : Subgroup (BarInf L), IsFundamentalOver (p ^ f) K →
        IsFundamentalOver (p ^ f) K' → ∀ z ∈ K ⊓ K', (orderOf z).Prime → 5 ≤ orderOf z →
          orderOf z ≠ p → K = K' := by
      intro K K' hK hK' z hz hzprime hz5 hzp
      have hz2 : orderOf z ≠ 2 := by omega
      have hz3 : orderOf z ≠ 3 := by omega
      rcases ht with rfl | rfl
      · exact uc22s2112r34_eq_of_mem_inf_psl3 hp hp2 hadm hX hK hK' hz.1 hz.2 hzprime hz2 hz3 hzp
      · exact uc22s2112r34_eq_of_mem_inf_psu3 hp hp2 hadm hX hK hK' hz.1 hz.2 hzprime hz2 hz3 hzp
    have hdata : ∀ b (hb : b ∈ c.B0),
        (∀ z ∈ K, (MulAut.conj u * inducedBarInfAutHom L ⟨b, hBN hb⟩ *
          (MulAut.conj u)⁻¹) z = (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ z) ∧
        K.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K := by
      intro b hb
      obtain ⟨x, hxb⟩ := MonoidHom.mem_range.1 (hinn b hb)
      have hxcomm : ∀ a : ↥R, x * ψ a = ψ a * x := by
        intro a
        have hba : b * (a : G) = (a : G) * b := by
          have := c.hB0.2.1.is_comm.comm ⟨b, hb⟩ ⟨(a : G), hRB a.2⟩
          exact congrArg Subtype.val this
        have hcommN : (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G))) *
            ⟨(a : G), hRN a.2⟩ = ⟨(a : G), hRN a.2⟩ * ⟨b, hBN hb⟩ := Subtype.ext hba
        have hθcomm : inducedBarInfAutHom L ⟨b, hBN hb⟩ *
            inducedBarInfAutHom L ⟨(a : G), hRN a.2⟩ =
            inducedBarInfAutHom L ⟨(a : G), hRN a.2⟩ *
              inducedBarInfAutHom L ⟨b, hBN hb⟩ := by
          rw [← map_mul, ← map_mul, hcommN]
        rw [← hxb, ← hψ a] at hθcomm
        apply hinj
        rw [map_mul, map_mul]
        exact hθcomm
      have hxcentR : x ∈ centralizer (ψ.range : Set (BarInf L)) := by
        rw [mem_centralizer_iff]
        intro y hy
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hy
        exact (hxcomm a).symm
      have hxodd : Odd (orderOf x) := by
        have hdvd : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) ∣ orderOf b := by
          have h := orderOf_map_dvd (inducedBarInfAutHom L)
            (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
          simpa [Subgroup.orderOf_mk] using h
        have hord : orderOf x = orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) := by
          rw [← hxb]
          exact (orderOf_injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) hinj x).symm
        rw [hord]
        exact Odd.of_dvd_nat (ch214_odd_card c.hpi)
          (hdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb))
      have hxN : x ∈ normalizer (K : Set (BarInf L)) :=
        uc22s2112r34_l3E2_normalizes hK.1 hRK hxcentR y₁.2 hord₁ hr hr5 hrp huniq
      obtain ⟨k, hkact, hkcent⟩ :=
        uc22s2112r34_l3E2_inner_on t 3 p f hp hp2 hadm hX hA1 hRee hK.1 hRK hxN hxodd hxcentR
      have hθ : ∀ z ∈ K, inducedBarInfAutHom L ⟨b, hBN hb⟩ z =
          (k : BarInf L) * z * (k : BarInf L)⁻¹ := by
        intro z hz
        rw [← hxb]
        exact hkact z hz
      have hmap : K.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K := by
        rw [← hxb]
        refine uc22s2112r34_l3E2_map_conj_eq_of_acts k.2 fun z hz => ?_
        simpa [MulAut.conj_apply] using hkact z hz
      have huk : u * (k : BarInf L) * u⁻¹ = (k : BarInf L)⁻¹ :=
        hu_inv (k : BarInf L) ⟨k.2, hkcent⟩
      refine ⟨?_, hmap⟩
      intro z hz
      have huz : u⁻¹ * z * u ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem huK) hz) huK
      have harg : (k : BarInf L)⁻¹ * z * (k : BarInf L) ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem k.2) hz) k.2
      have hθinv : (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ z =
          (k : BarInf L)⁻¹ * z * (k : BarInf L) := by
        have hz' : inducedBarInfAutHom L ⟨b, hBN hb⟩
            ((k : BarInf L)⁻¹ * z * (k : BarInf L)) = z := by
          rw [hθ _ harg]
          group
        have := congrArg (fun w => (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ w) hz'
        simpa using this.symm
      have harg_eq : (MulAut.conj u)⁻¹ z = u⁻¹ * z * u := by
        simp
      calc (MulAut.conj u * inducedBarInfAutHom L ⟨b, hBN hb⟩ * (MulAut.conj u)⁻¹) z
          = MulAut.conj u (inducedBarInfAutHom L ⟨b, hBN hb⟩ ((MulAut.conj u)⁻¹ z)) := rfl
        _ = MulAut.conj u (inducedBarInfAutHom L ⟨b, hBN hb⟩ (u⁻¹ * z * u)) := by
            rw [harg_eq]
        _ = MulAut.conj u ((k : BarInf L) * (u⁻¹ * z * u) * (k : BarInf L)⁻¹) := by
            rw [hθ _ huz]
        _ = u * ((k : BarInf L) * (u⁻¹ * z * u) * (k : BarInf L)⁻¹) * u⁻¹ := rfl
        _ = (k : BarInf L)⁻¹ * z * (k : BarInf L) := by
            have hukinv : u * (k : BarInf L)⁻¹ * u⁻¹ = (k : BarInf L) := by
              calc u * (k : BarInf L)⁻¹ * u⁻¹ =
                  (u * (k : BarInf L) * u⁻¹)⁻¹ := by group
                _ = ((k : BarInf L)⁻¹)⁻¹ := by rw [huk]
                _ = (k : BarInf L) := by group
            calc u * ((k : BarInf L) * (u⁻¹ * z * u) * (k : BarInf L)⁻¹) * u⁻¹ =
                (u * (k : BarInf L) * u⁻¹) * (u * (u⁻¹ * z * u) * u⁻¹) *
                  (u * (k : BarInf L)⁻¹ * u⁻¹) := by group
              _ = (k : BarInf L)⁻¹ * z * (k : BarInf L) := by rw [huk, hukinv]; group
        _ = (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ z := hθinv.symm
    have hfaithK : ∀ b (hb : b ∈ c.B0),
        (∀ k ∈ K, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) → b = 1 := by
      intro b hb hfix
      by_contra hb1
      have hbord : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
      obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hbord
      let e := orderOf b / s
      let b' : G := b ^ e
      have hordb' : orderOf b' = s :=
        orderOf_pow_orderOf_div (orderOf_pos b).ne' hsdvd
      have hb'B : b' ∈ c.B0 := c.B0.pow_mem hb e
      have hb'N : b' ∈ normalizer (L : Set G) := hBN hb'B
      have hfix' : ∀ k ∈ K, inducedBarInfAutHom L ⟨b', hb'N⟩ k = k := by
        intro k hk
        have hpow : inducedBarInfAutHom L ⟨b', hb'N⟩ =
            (inducedBarInfAutHom L ⟨b, hBN hb⟩) ^ e := by
          rw [show (⟨b', hb'N⟩ : ↥(normalizer (L : Set G))) = ⟨b, hBN hb⟩ ^ e from
            Subtype.ext rfl, map_pow]
        rw [hpow]
        have hfixpow : ∀ n : ℕ, ((inducedBarInfAutHom L ⟨b, hBN hb⟩) ^ n) k = k := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
              rw [pow_succ, MulAut.mul_apply, hfix k hk, ih]
        exact hfixpow e
      have hb'2 : orderOf b' ≠ 2 := fun h2 => by
        have hodd : Odd (orderOf b') :=
          Odd.of_dvd_nat (ch214_odd_card c.hpi) (Subgroup.orderOf_dvd_natCard c.B0 hb'B)
        rw [h2] at hodd
        exact (Nat.not_odd_iff_even.2 even_two) hodd
      exact uc22s2112r34_false_of_fund_odd hKF7 hH c hL hp hp2 hf2 hpσ hMs hb'B hb'N
        (by rw [hordb']; exact hs) hb'2 hpN hK.1 fun k hk => hfix' k hk
    have hB0 : c.B0 ≠ ⊥ := by
      have hdvdB : r ∣ Nat.card c.B0 := hrπ.2
      intro h
      rw [h, card_bot] at hdvdB
      exact hr.one_lt.ne' (Nat.dvd_one.1 hdvdB)
    have hsK : K.map (inducedBarInfAutHom L ⟨s, hsN⟩).toMonoidHom = K := by
      rw [← hsu]
      exact uc22s2112r34_l3E2_map_conj_eq_of_acts huK fun z hz => rfl
    exact uc22s2112r34_false_of_inverts_on c hBN hB0 (fun b hb => (hdata b hb).2)
      hfaithK hsT hsN hsK fun b hb k hk => by
        simpa [hsu] using (hdata b hb).1 k hk
  exact key t ht hX.admissible hX

theorem s21_12aFR34L3E2_of_inner3 (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch)
    (h82 : F08.R82 D) (h211 : S21_1 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hG1 : S21_12aFR34L3E2Inner3 D) :
    S21_12aFR34L3E2 D (Choice214U D) := by
  intro hH c _heven _hpow L hL p hp hp2 f hf2 hm hno hfaith
  exfalso
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c.mono hCh with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  have hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f := fun f hm =>
    uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm
  rcases hm with hX | hX
  · exact uc22s2112r34_false_l3E2 hKF1 hKS hGA hσ hKF7 hH c (hn3 hH (c.mono hCh)) hL hBN
      hfaith (Or.inl rfl) hp hp2 hf2 hX hno hree hG1
  · exact uc22s2112r34_false_l3E2 hKF1 hKS hGA hσ hKF7 hH c (hn3 hH (c.mono hCh)) hL hBN
      hfaith (Or.inr rfl) hp hp2 hf2 hX hno hree hG1

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
