module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.HeisCount
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.SPEBasics
import CFSG.GroupTheory.CentralizerNotLeOfIndex
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.LargeExtraspecial.OutSixBasic
import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.SylowConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GroupTheory (conj_mem_centralizer_of_le_normalizer)
open CFSG.EvenSporadicStandard.HNRecog.Harada.L27 (exists_conj_mem_zpowers_of_five)

theorem exists_pow_conj_eq_pow_mul_mem {G : Type*} [Group G] {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {μ : ℕ}
    (h : ∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G), g * x * g⁻¹ = x ^ μ * z) :
    ∀ (k : ℕ) {x : G}, x ∈ R →
      ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G), g ^ k * x * (g ^ k)⁻¹ = x ^ (μ ^ k) * z := by
  intro k
  induction k with
  | zero =>
    intro x hx
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ k ih =>
    intro x hx
    obtain ⟨z, hz, hzx⟩ := ih hx
    obtain ⟨u, hu, hgu⟩ := h x hx
    have hcomm : Commute (x ^ μ) u :=
      Subgroup.mem_centralizer_iff.mp hu.2 (x ^ μ) (Subgroup.pow_mem _ hx μ)
    refine ⟨u ^ (μ ^ k) * (g * z * g⁻¹),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hu _) (Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1,
          conj_mem_centralizer_of_le_normalizer le_rfl le_rfl g hg z hz.2⟩), ?_⟩
    calc
      g ^ (k + 1) * x * (g ^ (k + 1))⁻¹
          = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by rw [pow_succ']; group
      _ = g * (x ^ (μ ^ k) * z) * g⁻¹ := by rw [hzx]
      _ = (g * x ^ (μ ^ k) * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * x * g⁻¹) ^ (μ ^ k) * (g * z * g⁻¹) := by rw [conj_pow]
      _ = (x ^ μ * u) ^ (μ ^ k) * (g * z * g⁻¹) := by rw [hgu]
      _ = ((x ^ μ) ^ (μ ^ k) * u ^ (μ ^ k)) * (g * z * g⁻¹) := by
            rw [Commute.mul_pow hcomm]
      _ = x ^ (μ ^ (k + 1)) * (u ^ (μ ^ k) * (g * z * g⁻¹)) := by
            rw [← pow_mul, ← pow_succ']
            group

theorem dvd_of_pow_mem_inf_centralizer {G : Type*} [Group G] {R : Subgroup G}
    {p : ℕ} [Fact p.Prime] {x : G} (hx : x ∈ R)
    (hxZ : x ∉ R ⊓ Subgroup.centralizer (R : Set G))
    (hexp : ∀ r ∈ R, r ^ p = 1) {a : ℕ}
    (ha : x ^ a ∈ R ⊓ Subgroup.centralizer (R : Set G)) : p ∣ a := by
  classical
  let Z : Subgroup ↥R := Subgroup.center ↥R
  let x' : ↥R := ⟨x, hx⟩
  let W := ↥R ⧸ Z
  have hcenter : Subgroup.map R.subtype (Subgroup.center ↥R) =
      R ⊓ Subgroup.centralizer (R : Set G) := CFSG.center_map_subtype_eq_inf_centralizer R
  have hx'Z : x' ∉ Z := by
    intro h
    apply hxZ
    rw [← hcenter]
    exact Subgroup.mem_map.mpr ⟨x', h, rfl⟩
  have hwne : (QuotientGroup.mk' Z x' : W) ≠ 1 := by
    intro h
    exact hx'Z ((QuotientGroup.eq_one_iff x').mp h)
  have hwp : (QuotientGroup.mk' Z x' : W) ^ p = 1 := by
    rw [← map_pow]
    have hxp : x' ^ p = 1 := Subtype.ext (hexp x hx)
    rw [hxp, map_one]
  have hwa : (QuotientGroup.mk' Z x' : W) ^ a = 1 := by
    rw [← map_pow]
    have hxa : x' ^ a ∈ Z := by
      rw [← hcenter] at ha
      obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
      have : y = x' ^ a := Subtype.ext (by simpa using hya)
      rwa [this] at hy
    exact (QuotientGroup.eq_one_iff (x' ^ a)).mpr hxa
  have hord : orderOf (QuotientGroup.mk' Z x' : W) = p :=
    orderOf_eq_prime hwp hwne
  have hdvd : orderOf (QuotientGroup.mk' Z x' : W) ∣ a :=
    orderOf_dvd_of_pow_eq_one hwa
  rwa [hord] at hdvd

theorem exists_conj_pow_of_orderOf_eq_five {H : Type*} [Group H] [Finite H] {y y0 : H}
    (hy : orderOf y = 5) (hy0 : orderOf y0 = 5) (h25 : ¬ 25 ∣ Nat.card H) :
    ∃ n : H, ∃ j : ℕ, ¬ 5 ∣ j ∧ y = n * y0 ^ j * n⁻¹ := by
  obtain ⟨e, -, he⟩ := exists_conj_mem_zpowers_of_five (⊤ : Subgroup H)
    (by rwa [Subgroup.card_top]) (Subgroup.mem_top y) (Subgroup.mem_top y0) hy hy0
  obtain ⟨j, hj⟩ := ((isOfFinOrder_of_finite y0).mem_powers_iff_mem_zpowers).mpr he
  replace hj : y0 ^ j = e * y * e⁻¹ := hj
  refine ⟨e⁻¹, j, fun h5 => ?_, ?_⟩
  · have h1 : e * y * e⁻¹ = 1 := by
      rw [← hj]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hy0]; exact h5)
    rw [conj_eq_one_iff] at h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  · rw [hj]
    group

variable {p : ℕ} [Fact p.Prime]

theorem good_of_heis (hp : p = 5 ∨ p = 11) {i : TauCeti.CFSGIndex}
    (hH : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) (h9 : 9 ∣ Nat.card X)
    (h25 : p = 11 → ¬ 25 ∣ Nat.card X) : Good p N := by
  classical
  set K : Subgroup X := CFSG.generalizedFitting X with hKdef
  obtain ⟨hKs, hKnab, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := p) Fact.out hO hN
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  let R : Sylow p X := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hRcoe : (R : Subgroup X) = P :=
    IsPGroup.toSylow_coe hP.2.1 (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hRN : (R : Subgroup X) ≤ N := hRcoe ▸ hPN
  obtain ⟨hout, hcard, hmax, hC, hZ, hcomm, hexp, hsolv, hlines⟩ :=
    hH X K hKn hKC ⟨e⟩ p rfl R
  let M : Subgroup X := Subgroup.normalizer ((R : Subgroup X) : Set X)
  have hRne : (R : Subgroup X) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (R : Subgroup X) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcard] at h1
    have h8 : 8 ≤ p ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le 3
    omega
  have hMleN : M ≤ N := hN.normalizer_le hRne R.isPGroup' hRN
  have hNM : N = M := by
    rcases hmax N hMleN with h | h
    · exact h
    · exact absurd h hN.1
  have hNnorm : N ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := hNM.le
  constructor
  · exact pPrimeCore_eq_bot_of_centralizer_le hRN R.isPGroup' hNnorm hC
  · intro x y hxN hyN hx1 hxp hyprime hy2 hyp hxy
    set r : ℕ := orderOf y with hrdef
    have hry : orderOf y = r := rfl
    haveI : Fact r.Prime := ⟨hyprime⟩
    have hrN : r ∣ Nat.card N := by
      have h := orderOf_dvd_natCard (⟨y, hyN⟩ : ↥N)
      rw [← Subgroup.orderOf_coe] at h
      simpa [hry] using h
    have hNdvd : Nat.card N ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 2 - p)) := by
      rw [hNM]
      exact Heis.card_normalizer_dvd hcard hZ hcomm hexp hC
    have hr_cases : r = 3 ∨ r = 5 := by
      have hnotp : ¬ r ∣ p := by
        intro h
        rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h with h1 | hp'
        · exact hyprime.ne_one h1
        · exact hyp hp'
      have hcop : Nat.Coprime r p := (Nat.Prime.coprime_iff_not_dvd hyprime).mpr hnotp
      have hrdvd1 : r ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
        exact (hcop.pow_right 3).dvd_of_dvd_mul_left (by simpa using hrN.trans hNdvd)
      have hsmall : r ∣ p + 1 ∨ r ∣ p - 1 := by
        have h1 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
          simpa using Nat.sq_sub_sq p 1
        have h2 : p ^ 2 - p = p * (p - 1) := by
          rw [pow_two, Nat.mul_sub_left_distrib]
          norm_num
        rcases hyprime.dvd_mul.mp hrdvd1 with h | h
        · rw [h1] at h
          rcases hyprime.dvd_mul.mp h with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rw [h2] at h
          rcases hyprime.dvd_mul.mp h with h | h
          · exact absurd h hnotp
          · exact Or.inr h
      rcases hp with rfl | rfl
      · left
        have hle : r ≤ 6 := by
          rcases hsmall with h | h
          · exact Nat.le_of_dvd (by norm_num) h
          · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
        interval_cases r <;> norm_num at *
      · rcases hsmall with h | h
        · have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) h
          interval_cases r <;> norm_num at *
        · have hle : r ≤ 10 := Nat.le_of_dvd (by norm_num) h
          interval_cases r <;> norm_num at *
    have h9N : ¬ 9 ∣ Nat.card N := by
      intro h
      rcases hp with rfl | rfl
      · exact (by norm_num : ¬ 9 ∣ 5 ^ 3 * ((5 ^ 2 - 1) * (5 ^ 2 - 5)))
          (h.trans hNdvd)
      · exact (by norm_num : ¬ 9 ∣ 11 ^ 3 * ((11 ^ 2 - 1) * (11 ^ 2 - 11)))
          (h.trans hNdvd)
    have h3index : 3 ∣ N.index := by
      by_contra h3
      have hcop3 : Nat.Coprime 3 N.index :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr h3
      have hcop9 : Nat.Coprime 9 N.index := by
        simpa using hcop3.pow_left 2
      have hdvd9 : 9 ∣ N.index * Nat.card N := by
        rw [Subgroup.index_mul_card N]
        exact h9
      exact h9N (hcop9.dvd_of_dvd_mul_left hdvd9)
    rcases hr_cases with hr3 | hr5
    ·
      have h3index' : r ∣ N.index := by rw [hr3]; exact h3index
      have h9N' : ¬ r ^ 2 ∣ Nat.card N := by rw [hr3]; exact h9N
      have hCnotle : ¬ Subgroup.centralizer ({y} : Set X) ≤ N :=
        CFSG.GroupTheory.centralizer_not_le_of_dvd_index hyN hry h3index' h9N'
      obtain ⟨c, hcy, hcp, hcN⟩ :=
        exists_pElement_not_mem_of_centralizer_not_le hN hx1 hxp hxy hCnotle
      have hnotdvdK : ¬ p ∣ Nat.card (X ⧸ K) := by
        rw [← Subgroup.index_eq_card]
        intro h
        have hdvd : K.index ∣
            Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
          CFSG.LargeExtraspecial.S14.index_dvd_card_outer K (by rw [hKC]; exact bot_le)
        exact hout (h.trans hdvd)
      have hcK : c ∈ K := by
        have hle : Subgroup.zpowers c ≤ K :=
          CFSG.RankThree.PartOne.CTP.le_of_isPGroup_of_not_dvd_card_quotient hcp hnotdvdK
        exact hle (Subgroup.mem_zpowers c)
      exact ⟨c, hKdef ▸ hcK, hcy, hcp, hcN⟩
    ·
      have hp11 : p = 11 := by
        rcases hp with h5 | h11
        · subst h5
          exact absurd (hry.trans hr5) hyp
        · exact h11
      subst hp11
      obtain ⟨t, htM, m, lam, ee, hm, hlam, he, hact, hinv, hno⟩ := hlines
      have htN : t ∈ N := by rw [hNM]; exact htM
      let u : X := t ^ (2 * m)
      have huN : u ∈ N := Subgroup.pow_mem N htN _
      have huNorm : u ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) := by
        show u ∈ M
        rw [← hNM]
        exact huN
      have hu_eq : u = t ^ m * t ^ m := by
        change t ^ (2 * m) = t ^ m * t ^ m
        rw [show 2 * m = m + m by omega, pow_add]
      have hu_action : ∀ x ∈ (R : Subgroup X),
          ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            u * x * u⁻¹ = x ^ (lam ^ 2) * z := by
        intro x hx
        obtain ⟨z, hz, hzx⟩ := hact x hx
        have htmNorm : t ^ m ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) :=
          Subgroup.pow_mem _ htM m
        have htz : t ^ m * z * (t ^ m)⁻¹ ∈
            (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :=
          Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htmNorm z).mp hz.1,
            conj_mem_centralizer_of_le_normalizer le_rfl le_rfl _ htmNorm z hz.2⟩
        refine ⟨z ^ lam * (t ^ m * z * (t ^ m)⁻¹),
          Subgroup.mul_mem _ (Subgroup.pow_mem _ hz lam) htz, ?_⟩
        have hcomm : Commute (x ^ lam) z :=
          Subgroup.mem_centralizer_iff.mp hz.2 (x ^ lam) (Subgroup.pow_mem _ hx lam)
        calc
          u * x * u⁻¹ = t ^ m * (t ^ m * x * (t ^ m)⁻¹) * (t ^ m)⁻¹ := by
            rw [hu_eq]; group
          _ = t ^ m * (x ^ lam * z) * (t ^ m)⁻¹ := by rw [hzx]
          _ = (t ^ m * x ^ lam * (t ^ m)⁻¹) * (t ^ m * z * (t ^ m)⁻¹) := by group
          _ = (t ^ m * x * (t ^ m)⁻¹) ^ lam * (t ^ m * z * (t ^ m)⁻¹) := by
            rw [conj_pow]
          _ = (x ^ lam * z) ^ lam * (t ^ m * z * (t ^ m)⁻¹) := by rw [hzx]
          _ = ((x ^ lam) ^ lam * z ^ lam) * (t ^ m * z * (t ^ m)⁻¹) := by
            rw [Commute.mul_pow hcomm]
          _ = x ^ (lam ^ 2) * (z ^ lam * (t ^ m * z * (t ^ m)⁻¹)) := by
            rw [← pow_mul, pow_two]
            group
      have hiter : ∀ (k : ℕ) {z : X}, z ∈ (R : Subgroup X) →
          ∃ w ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            u ^ k * z * (u ^ k)⁻¹ = z ^ ((lam ^ 2) ^ k) * w :=
        fun k z hz => exists_pow_conj_eq_pow_mul_mem huNorm hu_action k hz
      have h25N : ¬ 25 ∣ Nat.card ↥N := by
        have hNX : Nat.card ↥N ∣ Nat.card X := by
          simpa using Subgroup.card_dvd_of_le (le_top : N ≤ (⊤ : Subgroup X))
        exact fun h => h25 rfl (h.trans hNX)
      have hxR : x ∈ (R : Subgroup X) := by
        have hcomap : (Subgroup.zpowers x).comap N.subtype =
            Subgroup.zpowers (⟨x, hxN⟩ : ↥N) := by
          ext a
          rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
          constructor
          · rintro ⟨k, hk⟩
            refine ⟨k, ?_⟩
            apply Subtype.ext
            simpa using hk
          · rintro ⟨k, hk⟩
            refine ⟨k, ?_⟩
            have := congrArg (fun t : ↥N => (t : X)) hk
            simpa using this
        have hZxp : IsPGroup 11 (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) := by
          rw [← hcomap]
          exact hxp.comap_of_injective N.subtype N.subtype_injective
        haveI : (R.subgroupOf N).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr hNnorm
        have hnotdvd : ¬ 11 ∣ Nat.card (↥N ⧸ R.subgroupOf N) := by
          rw [← Subgroup.index_eq_card]
          exact fun h => R.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hRN))
        have hle : Subgroup.zpowers (⟨x, hxN⟩ : ↥N) ≤ R.subgroupOf N :=
          CFSG.RankThree.PartOne.CTP.le_of_isPGroup_of_not_dvd_card_quotient hZxp hnotdvd
        exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_zpowers _))
      have hlam0 : lam ≠ 0 := by
        intro h0
        have h : (lam : ZMod 11) = 0 := by simpa [h0]
        rw [h] at hlam
        norm_num at hlam
      have h5dvd : 5 ∣ orderOf u := by
        by_contra h5d
        have hnotle : ¬ (R : Subgroup X) ≤
            (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
          intro hle
          have heq : (R : Subgroup X) ⊓
              Subgroup.centralizer ((R : Subgroup X) : Set X) = (R : Subgroup X) :=
            le_antisymm inf_le_left hle
          have hc := congrArg (fun S : Subgroup X => Nat.card ↥S) heq
          rw [hZ, hcard] at hc
          norm_num at hc
        obtain ⟨x0, hx0R, hx0Z⟩ := Set.not_subset.mp hnotle
        obtain ⟨z, hz, hzx⟩ := hiter (orderOf u) hx0R
        have hud : u ^ orderOf u = 1 := pow_orderOf_eq_one u
        rw [hud] at hzx
        have hx_eq : x0 = x0 ^ ((lam ^ 2) ^ orderOf u) * z := by simpa using hzx
        have hnpos : 0 < (lam ^ 2) ^ orderOf u :=
          pow_pos (pow_pos (Nat.pos_of_ne_zero hlam0) 2) _
        have hxpowZ : x0 ^ ((lam ^ 2) ^ orderOf u - 1) ∈
            (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
          have hzx_comm : z * x0 = x0 * z :=
            (Subgroup.mem_centralizer_iff.mp hz.2 x0 hx0R).symm
          have h_eq : x0 ^ ((lam ^ 2) ^ orderOf u - 1) = z⁻¹ := by
            have h1 : x0 = x0 ^ ((lam ^ 2) ^ orderOf u - 1) * z * x0 := by
              calc
                x0 = x0 ^ ((lam ^ 2) ^ orderOf u) * z := hx_eq
                _ = x0 ^ (((lam ^ 2) ^ orderOf u - 1) + 1) * z := by
                  rw [Nat.sub_add_cancel hnpos]
                _ = (x0 ^ ((lam ^ 2) ^ orderOf u - 1) * x0) * z := by rw [pow_succ]
                _ = x0 ^ ((lam ^ 2) ^ orderOf u - 1) * (x0 * z) := by group
                _ = x0 ^ ((lam ^ 2) ^ orderOf u - 1) * (z * x0) := by rw [hzx_comm.symm]
                _ = x0 ^ ((lam ^ 2) ^ orderOf u - 1) * z * x0 := by group
            have h2 : x0 ^ ((lam ^ 2) ^ orderOf u - 1) * z = 1 := by
              have h3 : x0 * x0⁻¹ =
                  (x0 ^ ((lam ^ 2) ^ orderOf u - 1) * z * x0) * x0⁻¹ :=
                congrArg (fun t => t * x0⁻¹) h1
              simpa [mul_assoc] using h3.symm
            exact eq_inv_of_mul_eq_one_left h2
          rw [h_eq]
          exact ⟨Subgroup.inv_mem _ hz.1, Subgroup.inv_mem _ hz.2⟩
        have h11dvd : 11 ∣ (lam ^ 2) ^ orderOf u - 1 :=
          dvd_of_pow_mem_inf_centralizer hx0R hx0Z hexp hxpowZ
        have hpow_one : (((lam : ZMod 11) ^ 2) ^ orderOf u) = 1 := by
          have hmod : ((lam ^ 2) ^ orderOf u : ℕ) ≡ 1 [MOD 11] :=
            ((Nat.modEq_iff_dvd' (n := 11) (a := 1)
              (b := (lam ^ 2) ^ orderOf u) hnpos).mpr h11dvd).symm
          have hcast : (((lam ^ 2) ^ orderOf u : ℕ) : ZMod 11) = 1 := by
            have h1 : (((lam ^ 2) ^ orderOf u : ℕ) : ZMod 11) = ((1 : ℕ) : ZMod 11) := by
              rw [ZMod.natCast_eq_natCast_iff]
              exact hmod
            simpa using h1
          simpa [Nat.cast_pow] using hcast
        have hdvd : orderOf ((lam : ZMod 11) ^ 2) ∣ orderOf u :=
          orderOf_dvd_of_pow_eq_one hpow_one
        have hlam10 : orderOf (lam : ZMod 11) = 10 := by simpa using hlam
        have hlam2ord : orderOf ((lam : ZMod 11) ^ 2) = 5 := by
          rw [orderOf_pow' _ (by norm_num : 2 ≠ 0), hlam10]
          norm_num
        rw [hlam2ord] at hdvd
        exact h5d hdvd
      set d : ℕ := orderOf u with hd
      set k : ℕ := d / 5 with hk
      set y0 : X := u ^ k with hy0
      have hdk : 5 * k = d := by
        rw [hd, hk]
        exact Nat.mul_div_cancel' h5dvd
      have hk0 : k ≠ 0 := by
        intro h
        have hd0 : d = 0 := by rw [← hdk, h, mul_zero]
        have hpos : 0 < d := by rw [hd]; exact orderOf_pos u
        omega
      have h5k : ¬ 5 ∣ k := by
        intro h5k
        have h25d : 25 ∣ d := by
          rw [← hdk]
          exact Nat.mul_dvd_mul_left 5 h5k
        have hdvdN : d ∣ Nat.card ↥N := by
          rw [hd]
          have := orderOf_dvd_natCard (⟨u, huN⟩ : ↥N)
          rwa [← Subgroup.orderOf_coe] at this
        exact h25N (h25d.trans hdvdN)
      have hy0ord : orderOf y0 = 5 := by
        have hgcd : Nat.gcd d k = k := by
          apply Nat.gcd_eq_right
          rw [hk]
          exact Nat.div_dvd_of_dvd h5dvd
        rw [hy0, orderOf_pow' u hk0, ← hd, hgcd, hk]
        exact Nat.div_div_self h5dvd (by rw [hd]; exact (orderOf_pos u).ne')
      have hy0N : y0 ∈ N := Subgroup.pow_mem N huN k
      have hy0ne : y0 ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hy0ord
        norm_num at hy0ord
      have hyord5 : orderOf y = 5 := hry.trans hr5
      have hyN' : orderOf (⟨y, hyN⟩ : ↥N) = 5 := by
        rw [← Subgroup.orderOf_coe]; exact hyord5
      have hy0N' : orderOf (⟨y0, hy0N⟩ : ↥N) = 5 := by
        rw [← Subgroup.orderOf_coe]; exact hy0ord
      obtain ⟨n, j, h5j, hconj⟩ :=
        exists_conj_pow_of_orderOf_eq_five (H := ↥N) hyN' hy0N' h25N
      have hconjX : y = (n : X) * y0 ^ j * (n : X)⁻¹ := by
        have h := congrArg (fun t : ↥N => (t : X)) hconj
        simpa using h
      have hnN : (n : X) ∈ N := n.2
      have hnxR : (n : X)⁻¹ * x * (n : X) ∈ (R : Subgroup X) := by
        have hnNorm : (n : X) ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) := hNnorm hnN
        have hninvNorm : (n : X)⁻¹ ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) :=
          Subgroup.inv_mem _ hnNorm
        have h := (Subgroup.mem_normalizer_iff.mp hninvNorm x).mp hxR
        simpa using h
      have hcomm' : ((n : X)⁻¹ * x * (n : X)) * y0 ^ j =
          y0 ^ j * ((n : X)⁻¹ * x * (n : X)) := by
        have hxy' : x * y = y * x := hxy
        rw [hconjX] at hxy'
        have h := congrArg (fun t => (n : X)⁻¹ * t * (n : X)) hxy'
        simpa [mul_assoc] using h
      have hk_mul_j_ne : k * j ≠ 0 := mul_ne_zero hk0 (by rintro rfl; exact h5j (dvd_zero 5))
      have hcopk : Nat.Coprime 5 k :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5k
      have hcopj : Nat.Coprime 5 j :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5j
      have hcopkj : Nat.Coprime 5 (k * j) := hcopk.mul_right hcopj
      have hlam10 : orderOf (lam : ZMod 11) = 10 := by simpa using hlam
      have hlam2ord : orderOf ((lam : ZMod 11) ^ 2) = 5 := by
        rw [orderOf_pow' _ (by norm_num : 2 ≠ 0), hlam10]
        norm_num
      set μ : ℕ := (lam ^ 2) ^ (k * j) with hμdef
      have hμcast : ((μ : ZMod 11)) = ((lam : ZMod 11) ^ 2) ^ (k * j) := by
        simp [μ, Nat.cast_pow]
      have hμord : orderOf (((lam : ZMod 11) ^ 2) ^ (k * j)) = 5 := by
        rw [orderOf_pow' _ hk_mul_j_ne, hlam2ord, Nat.Coprime.gcd_eq_one hcopkj]
      have hμ : ((μ : ZMod 11)) ≠ 1 := by
        intro h
        rw [← hμcast, h, orderOf_one] at hμord
        norm_num at hμord
      have hcop2 : Nat.Coprime 5 (2 * (k * j)) :=
        (by norm_num : Nat.Coprime 5 2).mul_right hcopkj
      have hμ2cast : ((μ : ZMod 11)) ^ 2 = ((lam : ZMod 11) ^ 2) ^ (2 * (k * j)) := by
        rw [hμcast, ← pow_mul]
        congr 1
        ring
      have hμ2ord : orderOf (((lam : ZMod 11) ^ 2) ^ (2 * (k * j))) = 5 := by
        rw [orderOf_pow' _ (mul_ne_zero (by norm_num : 2 ≠ 0) hk_mul_j_ne), hlam2ord,
          Nat.Coprime.gcd_eq_one hcop2]
      have hμ2 : ((μ : ZMod 11)) ^ 2 ≠ 1 := by
        intro h
        rw [← hμ2cast, h, orderOf_one] at hμ2ord
        norm_num at hμ2ord
      have haction_j : ∀ z ∈ (R : Subgroup X),
          ∃ w ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            y0 ^ j * z * (y0 ^ j)⁻¹ = z ^ μ * w := by
        intro z hz
        obtain ⟨w, hw, hwz⟩ := hiter (k * j) hz
        refine ⟨w, hw, ?_⟩
        simpa [μ, pow_mul, ← hy0] using hwz
      have hx1' : (n : X)⁻¹ * x * (n : X) = 1 :=
        Heis.eq_one_of_commute_scalar hcomm hexp hμ hμ2 haction_j hnxR hcomm'.symm
      have hxeq1 : x = 1 := by
        have h := congrArg (fun t => (n : X) * t * (n : X)⁻¹) hx1'
        simpa [mul_assoc] using h
      exfalso
      exact hx1 hxeq1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
