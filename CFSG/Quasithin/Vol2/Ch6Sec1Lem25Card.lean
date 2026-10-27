module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Faith
public import CFSG.Quasithin.Background.B69Num
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Three
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

theorem card_sylow_two_psl_ch625 {X : Type} [Group X] [Finite X] {p : ℕ} (hX : IsPSL 2 p 1 X)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) {P : Subgroup X} (hP : IsSylowTwoOf P ⊤) :
    Nat.card P = 4 := by
  have h1 := B69.card_psl_two_mul hX
  simp only [pow_one] at h1
  obtain ⟨m, hm, hmo⟩ : ∃ m : ℕ, Nat.card X = 4 * m ∧ m % 2 = 1 := by
    rcases hp8 with h3 | h5
    · obtain ⟨k, rfl⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
      have hg : Nat.gcd 2 (8 * k + 3 - 1) = 2 :=
        Nat.gcd_eq_left ⟨4 * k + 1, by omega⟩
      rw [hg] at h1
      refine ⟨(8 * k + 3) * (4 * k + 1) * (2 * k + 1), ?_, ?_⟩
      · ring_nf at h1 ⊢
        omega
      · have e : (8 * k + 3) * (4 * k + 1) * (2 * k + 1) =
            2 * (32 * k ^ 3 + 36 * k ^ 2 + 13 * k + 1) + 1 := by ring
        omega
    · obtain ⟨k, rfl⟩ : ∃ k, p = 8 * k + 5 := ⟨p / 8, by omega⟩
      have hg : Nat.gcd 2 (8 * k + 5 - 1) = 2 :=
        Nat.gcd_eq_left ⟨4 * k + 2, by omega⟩
      rw [hg] at h1
      refine ⟨(8 * k + 5) * (2 * k + 1) * (4 * k + 3), ?_, ?_⟩
      · ring_nf at h1 ⊢
        omega
      · have e : (8 * k + 5) * (2 * k + 1) * (4 * k + 3) =
            2 * (32 * k ^ 3 + 60 * k ^ 2 + 37 * k + 7) + 1 := by ring
        omega
  obtain ⟨-, hP2, hidx⟩ := hP
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hP2
  have hidx' : ¬ 2 ∣ P.index := by
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at hidx
  have hcm := P.card_mul_index
  rw [ha, hm] at hcm
  have hcop : Nat.Coprime 2 m := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hmo
  have hcop' : Nat.Coprime 2 P.index := (Nat.prime_two.coprime_iff_not_dvd).mpr hidx'
  have hle : 2 ^ a ∣ 2 ^ 2 := by
    have h1 : 2 ^ a ∣ 4 * m := ⟨P.index, hcm.symm⟩
    exact (Nat.Coprime.pow_left a hcop).dvd_of_dvd_mul_right h1
  have hge : 2 ^ 2 ∣ 2 ^ a := by
    have h1 : 2 ^ 2 ∣ 2 ^ a * P.index := ⟨m, by rw [hcm]; ring⟩
    exact (Nat.Coprime.pow_left 2 hcop').dvd_of_dvd_mul_right h1
  have h2 := Nat.le_of_dvd (by positivity) hle
  have h3 := Nat.le_of_dvd (by positivity) hge
  rw [ha]
  have : 2 ^ a = 2 ^ 2 := le_antisymm h2 h3
  rw [this]
  norm_num

theorem eq_of_ne_one_of_card_two_ch625 {Q : Type*} [Group Q] {H : Subgroup Q}
    (h2 : Nat.card H = 2) {a c : Q} (ha : a ∈ H) (hc : c ∈ H) (ha1 : a ≠ 1) (hc1 : c ≠ 1) :
    a = c := by
  obtain ⟨x, y, hxy, hU⟩ := Nat.card_eq_two_iff.mp h2
  have hmem : ∀ w : ↥H, w = x ∨ w = y := by
    intro w
    have : w ∈ ({x, y} : Set ↥H) := hU ▸ Set.mem_univ w
    simpa using this
  have h1 := hmem 1
  have ha' := hmem ⟨a, ha⟩
  have hc' := hmem ⟨c, hc⟩
  have hane : (⟨a, ha⟩ : ↥H) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hcne : (⟨c, hc⟩ : ↥H) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have key : (⟨a, ha⟩ : ↥H) = ⟨c, hc⟩ := by
    rcases h1 with h1 | h1 <;> rcases ha' with ha' | ha' <;> rcases hc' with hc' | hc'
    all_goals first
      | exact ha'.trans hc'.symm
      | exact absurd (ha'.trans h1.symm) hane
      | exact absurd (hc'.trans h1.symm) hcne
  exact congrArg Subtype.val key

variable {G : Type} [Group G] [Finite G]

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

include hI in
theorem inner_center_of_three (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) {x : G}
    (hx : x ∈ DL) (hxr : orderOf x = 3) :
    phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K) ∧ Subgroup.center (KQ K) = ⊥ ∧
      ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 (KBar K) := by
  rcases d.kf2_cases hI kf1 kf2 h23 hx Nat.prime_three (by norm_num) hxr with hL |
      ⟨h7, -⟩ | ⟨-, hinn, hJ⟩ | ⟨-, hinn, p, hp, hp11, hp8, hK⟩
  · exact absurd hL (hLie _ T M L V n l DL K hI d)
  · norm_num at h7
  · exact (d.false_of_J2 hI kf3 hx hxr hinn hJ).elim
  · exact ⟨hinn, d.center_KQ_of_L2 l2MultiplierFact hp (by omega) hK, p, hp, hp11, hp8, hK⟩

include hI in
theorem mem_CH_of_phi_eq_one (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) (hn : n = 2)
    {r : G} (hr : r ∈ ch6R T L V l) (h1 : phiK K ⟨r, d.R_le_NK hI hr⟩ = 1) :
    r ∈ ch6CH T L V := by
  have hCH := d.hyp.ch6CH_eq hI.h432 hI.h6111 hI.h6119
  refine d.hyp.mem_CH_of_comm hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not hr ?_
  intro K₀ hK₀ hq k hk
  by_cases hK₀K : K₀ = K
  · rw [hK₀K] at hk
    have h2 := (phiK_eq_one_iff d.quasi _).mp h1 k hk
    rw [hCH]
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp d.comp) h2
  · by_cases hR : ⁅K₀, ch6R T L V l⁆ ≤ ch6CH T L V
    · have hc := hR (Subgroup.commutator_mem_commutator hk hr)
      have e : r * k * r⁻¹ * k⁻¹ = ⁅k, r⁆⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.inv_mem _ hc
    · exfalso
      have d₀ : Dat625 T M L V n l DL K₀ := ⟨d.hyp, d.l_mem, d.l_not, d.hall, hK₀, hq, hR⟩
      obtain ⟨x, hx, hxr⟩ := d.exists_mem_DL_orderOf Nat.prime_three (by subst hn; norm_num)
      obtain ⟨hinn, hZ, -⟩ := d.inner_center_of_three hI kf1 kf2 kf3 h23 hLie hx hxr
      obtain ⟨hinn₀, hZ₀, -⟩ := d₀.inner_center_of_three hI kf1 kf2 kf3 h23 hLie hx hxr
      exact d.false_of_two_inner hI d₀ hK₀K hx Nat.prime_three (by norm_num) hxr hinn hinn₀ hZ
        hZ₀

noncomputable abbrev phiR (hI : In625) : ↥(ch6R T L V l) →* MulAut (KBar K) :=
  (phiK K).comp (Subgroup.inclusion (d.R_le_NK hI))

include hI in
theorem card_range_phiR (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) (hn : n = 2) :
    Nat.card (d.phiR hI).range = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := d.phiR hI with hρ
  have hinj : Function.Injective (MulAut.conj : KBar K →* MulAut (KBar K)) := by
    intro a b hab
    exact d.eq_of_conj_eq hab
  obtain ⟨x, hx, hxr⟩ := d.exists_mem_DL_orderOf Nat.prime_three (by subst hn; norm_num)
  obtain ⟨-, -, p, -, -, hp8, hK⟩ := d.inner_center_of_three hI kf1 kf2 kf3 h23 hLie hx hxr
  have hS4 : Nat.card (SBar T L V K) = 4 :=
    card_sylow_two_psl_ch625 hK hp8 (d.isSylowTwoOf_SBar hI.h432)
  have hle : ρ.range ≤ (SBar T L V K).map (MulAut.conj : KBar K →* MulAut (KBar K)) := by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    obtain ⟨s, hs, hrs⟩ := d.exists_phi_R_eq_conj hI kf1 h23 hr
    exact ⟨s, hs, hrs.symm⟩
  have hcard : Nat.card ρ.range ∣ 4 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective hinj, hS4] at this
  have hne1 : Nat.card ρ.range ≠ 1 := by
    intro h1
    obtain ⟨r, hr, hr1⟩ := d.exists_phi_R_ne_one hI
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    apply hr1
    have hmem : ρ ⟨r, hr⟩ ∈ ρ.range := ⟨⟨r, hr⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hne2 : Nat.card ρ.range ≠ 2 := by
    intro h2
    obtain ⟨r₀, hr₀, hr₀1⟩ := d.exists_phi_R_ne_one hI
    have hRN : DL ≤ Subgroup.normalizer (ch6R T L V l : Set G) :=
      (d.hyp.DL_le_MV d.hall).trans
        (d.hyp.MV_le_normalizer_R hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).1
    have hcomm : ∀ y (hy : y ∈ DL) (r : ↥(ch6R T L V l)),
        phiK K ⟨y, d.DL_le_NK hI hy⟩ * ρ r = ρ r * phiK K ⟨y, d.DL_le_NK hI hy⟩ := by
      intro y hy r
      have hr' : y * (r : G) * y⁻¹ ∈ ch6R T L V l :=
        (Subgroup.mem_normalizer_iff.mp (hRN hy) r).mp r.2
      have e : phiK K ⟨y, d.DL_le_NK hI hy⟩ * ρ r * (phiK K ⟨y, d.DL_le_NK hI hy⟩)⁻¹ =
          ρ ⟨_, hr'⟩ := by
        rw [hρ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
        congr 1
      by_cases ha : ρ r = 1
      · rw [ha, mul_one, one_mul]
      · have hc1 : ρ ⟨_, hr'⟩ ≠ 1 := by
          rw [← e]
          intro h0
          apply ha
          have h1 := congrArg (fun w => (phiK K ⟨y, d.DL_le_NK hI hy⟩)⁻¹ * w *
            phiK K ⟨y, d.DL_le_NK hI hy⟩) h0
          simpa [mul_assoc] using h1
        have heq := eq_of_ne_one_of_card_two_ch625 h2 ⟨r, rfl⟩ ⟨_, rfl⟩ ha hc1
        rw [← e] at heq
        calc phiK K ⟨y, d.DL_le_NK hI hy⟩ * ρ r =
            (phiK K ⟨y, d.DL_le_NK hI hy⟩ * ρ r * (phiK K ⟨y, d.DL_le_NK hI hy⟩)⁻¹) *
              phiK K ⟨y, d.DL_le_NK hI hy⟩ := by group
          _ = ρ r * phiK K ⟨y, d.DL_le_NK hI hy⟩ := by rw [← heq]
    have hR24 := (d.hyp.lemma_6_1_24_two hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).2.2 DL
      d.hall DL le_rfl (d.hyp.DL_ne_bot d.hall)
    set Ker : Subgroup G := ((phiK K).ker).map (Subgroup.normalizer (K : Set G)).subtype
      with hKer
    have hmemKer : ∀ (z : G) (hz : z ∈ Subgroup.normalizer (K : Set G)),
        phiK K ⟨z, hz⟩ = 1 → z ∈ Ker := fun z hz h => ⟨⟨z, hz⟩, h, rfl⟩
    have hRK : ch6R T L V l ≤ Ker := by
      have hR' : ch6R T L V l = ⁅ch6R T L V l, DL⁆ ⊔
          (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)) := hR24
      rw [hR']
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro r hr y hy
        have hrN := d.R_le_NK hI hr
        have hyN := d.DL_le_NK hI hy
        have hcN : ⁅r, y⁆ ∈ Subgroup.normalizer (K : Set G) := by
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hyN)
            (Subgroup.inv_mem _ hrN)) (Subgroup.inv_mem _ hyN)
        refine hmemKer _ hcN ?_
        have e : (⟨⁅r, y⁆, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
            ⁅(⟨r, hrN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨y, hyN⟩⁆ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        have hc := hcomm y hy ⟨r, hr⟩
        have hρr : ρ ⟨r, hr⟩ = phiK K ⟨r, hrN⟩ := rfl
        rw [hρr] at hc
        rw [e, map_commutatorElement, commutatorElement_def, ← hc]
        group
      · intro z hz
        have hzO : z ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
          (d.hyp.lemma_6_1_20_one hI.h432).1 hz.1
        exact hmemKer _ _ (d.phi_eq_one_of_mem_pCoreOf hzO)
    obtain ⟨⟨z, hzN⟩, hz1, hzr⟩ := hRK hr₀
    have e : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨r₀, d.R_le_NK hI hr₀⟩ :=
      Subtype.ext hzr
    rw [e] at hz1
    exact hr₀1 hz1
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card ρ.range ∣ 2 ^ 2
    from hcard)
  interval_cases i
  · exact absurd hie hne1
  · exact absurd hie hne2
  · exact hie


include hI in
theorem relIndex_CUV (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) (hn : n = 2) :
    (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)).relIndex (ch6R T L V l) = 4 := by
  have h1 := d.hyp.lemma_6_1_24_one hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not
  have hCH := d.hyp.ch6CH_eq hI.h432 hI.h6111 hI.h6119
  have hRH : ch6R T L V l ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    (d.hyp.R_le_I hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).trans
      (Subgroup.centralizer_le_normalizer _)
  have hker : (d.phiR hI).ker =
      (centralizerMod (ch6ZS T L V) (ch6R T L V l) (ch6U T L V)).subgroupOf (ch6R T L V l) := by
    ext ⟨r, hr⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h0
      have hm := d.mem_CH_of_phi_eq_one hI kf1 kf2 kf3 h23 hLie hn hr h0
      exact ⟨hr, hm.2.1, hm.2.2⟩
    · intro hm
      have hm' : r ∈ ch6CH T L V := ⟨hRH hr, hm.2.1, hm.2.2⟩
      rw [hCH] at hm'
      exact d.phi_eq_one_of_mem_pCoreOf hm'
  rw [h1, Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact d.card_range_phiR hI kf1 kf2 kf3 h23 hLie hn

include hI in
theorem relIndex_E (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) (hn : n = 2) :
    (ch6U T L V ⊓ conjSubgroup (ch6U T L V) l).relIndex (ch6R T L V l) = 2 ^ n * 2 ^ n := by
  have h2 := (d.hyp.lemma_6_1_24_two hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).2.1
  have h4 := d.relIndex_CUV hI kf1 kf2 kf3 h23 hLie hn
  have h2' : (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)).relIndex (ch6R T L V l) *
      (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)).relIndex (ch6R T L V l) =
      (ch6U T L V ⊓ conjSubgroup (ch6U T L V) l).relIndex (ch6R T L V l) := h2
  rw [← h2', h4, hn]
  norm_num

end Dat625

end CFSG.Quasithin.H13
