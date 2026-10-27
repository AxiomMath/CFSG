module

public import CFSG.RankThree.PartTwo.Sec8.HeringU3nReduce
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizerAut
import CFSG.GH74.Uniqueness.Section128Bender
import CFSG.LocalAnalysis.RankFourTheoremC.PPointMaxPair
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU3n

open CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Group K] [Finite K]

theorem bender_sylow_data {n e : ℕ} (h : BenderType K n 3 e)
    {s : K} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) :
    ∃ P : Sylow 2 K, (∀ Q : Sylow 2 K, s ∈ (Q : Subgroup K) → Q = P) ∧ s ∈ (P : Subgroup K) ∧
      s ∈ rootCenter (P : Subgroup K) ∧ qOf s = (P : Subgroup K) ∧
      Nat.card (rootCenter (P : Subgroup K)) = 2 ^ n ∧
      (∀ x ∈ (P : Subgroup K), x ^ 2 = 1 → x ∈ rootCenter (P : Subgroup K)) ∧
      CFSG.Assembly.IsElemAbelian 2 (rootCenter (P : Subgroup K)) ∧
      (∀ E : Subgroup K, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E = 2 ^ n → s ∈ E →
        E = rootCenter (P : Subgroup K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨P, hsP⟩ := CFSG.GH74.Uniqueness.Sec128B.exists_sylow_mem_of_orderOf_eq_two hord
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  have hss : s * s = 1 := by rw [← sq]; exact hs2
  have hsz : s ∈ rootCenter (P : Subgroup K) := hc.mem_rootCenter_of_mul_self hsP hss
  have hzs : Subgroup.zpowers s ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
  have hCs : Subgroup.centralizer ({s} : Set K) = (P : Subgroup K) ⊔ fixCartan (P : Subgroup K) t :=
    hc.centralizer_eq hsz hs1
  have hPC : (P : Subgroup K) ≤ Subgroup.centralizer ({s} : Set K) := hCs ▸ le_sup_left
  have hCnorm : Subgroup.centralizer ({s} : Set K) ≤
      Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    rw [hCs]
    exact sup_le Subgroup.le_normalizer
      ((fixCartan_le_cartan _ t).trans (cartan_le_borel _ t))
  have huniq : ∀ Q : Sylow 2 K, s ∈ (Q : Subgroup K) → Q = P := fun Q hsQ =>
    hc.sylow_eq_of_ne_bot hzs (Subgroup.zpowers_le.mpr hsP) (Subgroup.zpowers_le.mpr hsQ)
  refine ⟨P, huniq, hsP, hsz, ?_, hc.card_center,
    fun x hxP hx2 => hc.mem_rootCenter_of_mul_self hxP (by rw [← sq]; exact hx2), ?_, ?_⟩
  · apply le_antisymm
    ·
      have hQ2 : IsPGroup 2 (qOf s) := isPGroup_qOf s
      have hPn : (P : Subgroup K) ≤ Subgroup.normalizer (qOf s : Set K) :=
        hPC.trans (centralizer_le_normalizer_qOf s)
      have hsup : IsPGroup 2 ↥(qOf s ⊔ (P : Subgroup K)) :=
        CFSG.LocalAnalysis.RankFourTheoremC.isPGroup_sup_of_le_normalizer hQ2 P.isPGroup' hPn
      exact (P.is_maximal' hsup le_sup_right ▸ le_sup_left)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPC hCnorm P.isPGroup'
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have := (mem_rootCenter_iff.mp a.2).2 b (rootCenter_le _ b.2)
      exact this.symm
    · rw [sq]
      exact hc.center_sq x hx
  · intro E hE hEc hsE
    have hE2 : IsPGroup 2 E := IsPGroup.of_card hEc
    obtain ⟨Q, hEQ⟩ := hE2.exists_le_sylow
    have hQP : Q = P := huniq Q (hEQ hsE)
    subst hQP
    have hEz : E ≤ rootCenter (Q : Subgroup K) :=
      hc.elemAbelian_le_rootCenter hEQ (fun x hx => by rw [← sq]; exact hE.2 x hx)
    exact Subgroup.eq_of_le_of_card_ge hEz (by rw [hEc, hc.card_center])

theorem odd_two_pow_sub_one_add_one {n : ℕ} (hn : 1 ≤ n) :
    Odd (2 ^ n - 1) ∧ Odd (2 ^ n + 1) := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  constructor <;> rw [Nat.odd_iff] <;> omega

theorem bender_card_mulAut {n e : ℕ} (hn : Odd n)
    (h : BenderType K n 3 e) :
    ∃ u : ℕ, Odd u ∧ Nat.card (MulAut K) = 2 * (2 ^ n) ^ 3 * u := by
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨hodd1, hodd2⟩ := odd_two_pow_sub_one_add_one hn1
  have hcen : Subgroup.center K = ⊥ := h.center_eq_bot
  have hA := CFSG.SeitzReduction.RankOne.card_mulAut_of_center_eq_bot hcen
  have hK := h.card_eq
  have he : Odd e := by
    rcases h.cases' with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨-, he, -⟩
    · exact absurd hi (by norm_num)
    · exact absurd hi (by norm_num)
    · rw [he]
      exact Odd.of_dvd_nat hodd2 (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 _))
  obtain ⟨Dd, hDd, -, hDdc, -, hq⟩ := h.outer_unitary
  have hOut : Nat.card (Outer K) = 2 * n * Nat.gcd 3 (2 ^ n + 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hq, hDdc]
  have hg : Odd (Nat.gcd 3 (2 ^ n + 1)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  refine ⟨((2 ^ n) ^ 3 + 1) * ((2 ^ n - 1) * e) * (n * Nat.gcd 3 (2 ^ n + 1)), ?_, ?_⟩
  · have h2n : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have ha : Odd ((2 ^ n) ^ 3 + 1) := (Nat.even_pow.mpr ⟨h2n, by norm_num⟩).add_one
    exact (ha.mul (hodd1.mul he)).mul (hn.mul hg)
  · rw [hA, hK, hOut]
    ring

theorem map_rootCenter_of_map_iff {P : Subgroup K} {f : MulAut K}
    (hf : ∀ x, f x ∈ P ↔ x ∈ P) {z : K} (hz : z ∈ rootCenter P) : f z ∈ rootCenter P := by
  rw [mem_rootCenter_iff] at hz ⊢
  refine ⟨(hf z).mpr hz.1, fun p hp => ?_⟩
  obtain ⟨p', rfl⟩ := f.surjective p
  rw [← map_mul, ← map_mul, hz.2 p' ((hf p').mp hp)]

theorem bender_card_autCentralizer {n e : ℕ}
    (h : BenderType K n 3 e) (P : Sylow 2 K) :
    Nat.card (autCentralizer (rootCenter (P : Subgroup K))) = (2 ^ n) ^ 3 * (2 * (2 ^ n + 1)) := by
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  obtain ⟨D, hinf, hsup, hnorm, hDc, -⟩ := h.lemma_3_6_c_unitary P
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.RankThree.PartTwo.Sec8.Item82OneProof.conj_injective_of_center_eq_bot h.center_eq_bot
  have hAle : (P : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤
      autCentralizer (rootCenter (P : Subgroup K)) := hsup ▸ le_sup_left
  have hDnorm : D ≤ Subgroup.normalizer
      (((P : Subgroup K).map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)) :=
    (hsup ▸ le_sup_right : D ≤ autCentralizer (rootCenter (P : Subgroup K))).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAle).mp hnorm)
  rw [← hsup, card_sup_eq_mul_of_le_normalizer hDnorm hinf, hDc,
    Subgroup.card_map_of_injective hinj, hc.card_eq]

theorem bender_autCentralizer_eq {n e : ℕ} (hn : Odd n)
    (h : BenderType K n 3 e) (P : Sylow 2 K) {H : Subgroup (MulAut K)}
    (hCH : autCentralizer (rootCenter (P : Subgroup K)) ≤ H) {k : ℕ}
    (hH : Nat.card H ∣ Nat.card (autCentralizer (rootCenter (P : Subgroup K))) * 2 ^ k) :
    H = autCentralizer (rootCenter (P : Subgroup K)) := by
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  obtain ⟨u, hu, hAcard⟩ := bender_card_mulAut hn h
  have hC := bender_card_autCentralizer h P
  set C := autCentralizer (rootCenter (P : Subgroup K)) with hCdef
  have hHdvd : Nat.card H ∣ Nat.card (MulAut K) := Subgroup.card_subgroup_dvd_card H
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hCH
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have ht2 : t ∣ 2 ^ k := by
    rw [ht] at hH
    exact Nat.dvd_of_mul_dvd_mul_left hCpos hH
  rw [ht, hC, hAcard] at hHdvd
  have hapos : 0 < 2 * (2 ^ n) ^ 3 := by positivity
  have hdv : (2 ^ n + 1) * t ∣ u := by
    have h2 : 2 * (2 ^ n) ^ 3 * ((2 ^ n + 1) * t) ∣ 2 * (2 ^ n) ^ 3 * u := by
      have e : 2 * (2 ^ n) ^ 3 * ((2 ^ n + 1) * t) = (2 ^ n) ^ 3 * (2 * (2 ^ n + 1)) * t := by
        ring
      rwa [e]
    exact Nat.dvd_of_mul_dvd_mul_left hapos h2
  have htodd : Odd t := Odd.of_dvd_nat hu ((Dvd.intro_left _ rfl).trans hdv)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ht2
  have hj0 : j = 0 := by
    by_contra hj0
    have : 2 ∣ t := hj ▸ dvd_pow_self 2 hj0
    exact (Nat.not_even_iff_odd.mpr htodd) (even_iff_two_dvd.mpr this)
  rw [hj0, pow_zero] at hj
  exact (Subgroup.eq_of_le_of_card_ge hCH (by rw [ht, hj, mul_one])).symm

theorem map_iff_of_fix {P : Sylow 2 K} {s : K}
    (huniq : ∀ Q : Sylow 2 K, s ∈ (Q : Subgroup K) → Q = P) (hsP : s ∈ (P : Subgroup K))
    {f : MulAut K} (hfs : f s = s) (x : K) : f x ∈ (P : Subgroup K) ↔ x ∈ (P : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Sylow 2 K := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hQ' : (Q' : Subgroup K) = (P : Subgroup K).map f.toMonoidHom :=
    Sylow.coe_mapSurjective f.surjective P
  have hsQ' : s ∈ (Q' : Subgroup K) := by
    rw [hQ']
    exact ⟨s, hsP, hfs⟩
  have hQP : (Q' : Subgroup K) = (P : Subgroup K) := by rw [huniq Q' hsQ']
  rw [hQ'] at hQP
  constructor
  · intro hx
    rw [← hQP] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := f.injective hyx
    rwa [this] at hy
  · intro hx
    rw [← hQP]
    exact ⟨x, hx, rfl⟩

theorem bender_aut_le_autCentralizer {n e : ℕ} (hn : Odd n)
    (h : BenderType K n 3 e) {s : K} {P : Sylow 2 K}
    (huniq : ∀ Q : Sylow 2 K, s ∈ (Q : Subgroup K) → Q = P) (hsP : s ∈ (P : Subgroup K))
    {F : Subgroup (MulAut K)} (hF : IsPGroup 2 F) (hFs : ∀ f ∈ F, f s = s) :
    F ≤ autCentralizer (rootCenter (P : Subgroup K)) := by
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  set C := autCentralizer (rootCenter (P : Subgroup K)) with hCdef
  have hFn : F ≤ Subgroup.normalizer (C : Set (MulAut K)) := by
    intro f hf
    apply Subgroup.mem_normalizer_fintype
    intro g hg z hz
    have hf1 : ∀ x, f x ∈ (P : Subgroup K) ↔ x ∈ (P : Subgroup K) :=
      map_iff_of_fix huniq hsP (hFs f hf)
    have hfinv : ∀ x, f⁻¹ x ∈ (P : Subgroup K) ↔ x ∈ (P : Subgroup K) :=
      map_iff_of_fix huniq hsP (hFs f⁻¹ (F.inv_mem hf))
    have hz' : f⁻¹ z ∈ rootCenter (P : Subgroup K) := map_rootCenter_of_map_iff hfinv hz
    have : (f * g * f⁻¹) z = z := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hg _ hz', ← MulAut.mul_apply, mul_inv_cancel,
        MulAut.one_apply]
    exact this
  obtain ⟨k, hk⟩ := hF.exists_card_eq
  have hdvd := CFSG.LocalAnalysis.RankFourTheoremC.card_sup_dvd_mul_of_le_normalizer hFn
  have hCF : C ⊔ F = C := by
    refine bender_autCentralizer_eq hn h P (le_sup_left) (k := k) ?_
    rw [← hk]
    exact hdvd
  exact hCF ▸ le_sup_right

theorem bender_aut_pgroup {n e : ℕ} (hn : Odd n)
    (h : BenderType K n 3 e) {s : K} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    {F : Subgroup (MulAut K)} (hF : IsPGroup 2 F) (hFs : ∀ f ∈ F, f s = s)
    (hFn : ∀ x ∈ Subgroup.centralizer ({s} : Set K), ∀ f ∈ F,
      MulAut.conj x * f * (MulAut.conj x)⁻¹ ∈ F) :
    ∀ f ∈ F, ∃ u ∈ qOf s, f = MulAut.conj u := by
  obtain ⟨P, huniq, hsP, hsz, hq, -⟩ := bender_sylow_data h hs1 hs2
  have hFC := bender_aut_le_autCentralizer hn h huniq hsP hF hFs
  have hXn : ∀ k ∈ Subgroup.centralizer (rootCenter (P : Subgroup K) : Set K),
      MulAut.conj k ∈ Subgroup.normalizer (F : Set (MulAut K)) := by
    intro k hk
    have hks : k ∈ Subgroup.centralizer ({s} : Set K) := by
      rw [Subgroup.mem_centralizer_iff] at hk ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hk s hsz
    have : Finite (MulAut K) :=
      Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
    exact Subgroup.mem_normalizer_fintype (fun f hf => hFn k hks f hf)
  have hle := CFSG.SeitzReduction.RankOne.le_map_conj_of_isPGroup_unitary h P hFC hF hXn
  intro f hf
  obtain ⟨u, hu, hfu⟩ := hle hf
  exact ⟨u, hq ▸ hu, hfu.symm⟩

end CFSG.RankThree.PartTwo.Sec8.HeringU3n
