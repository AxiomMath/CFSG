module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410Module
public import CFSG.Quasithin.EmptyFaithfulMultiple.Families

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) :
    Nat.card ↥(T ⊔ D) = Nat.card D * D.relIndex T := by
  have h1 := Subgroup.relIndex_mul_card D (T ⊔ D)
  rw [inf_eq_left.mpr le_sup_right, A4.relIndex_sup_eq_of_le_normalizer' hT] at h1
  rw [← h1, mul_comm]

omit [Finite G] in
theorem relIndex_eq_card_of_inf_eq_bot {D Z : Subgroup G} (h : D ⊓ Z = ⊥) :
    D.relIndex Z = Nat.card Z := by
  have h1 := Subgroup.relIndex_mul_card D Z
  rw [h, Subgroup.card_bot, mul_one] at h1
  exact h1

omit [Finite G] in
theorem inf_zpowers_eq_bot {D : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxD : x ∉ D) :
    D ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzD, hzx⟩
  by_contra hz1
  exact hxD ((Subgroup.zpowers_le.mpr hzD) (mem_zpowers_symm hx3 hz1 hzx))

theorem two_lt_qhatInt_of_section {H W Y Q : Subgroup G} {x : G} (hW : IsTwoReducedIn H W)
    (hYH : Y ≤ H) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hYW : Y ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 Y)
    (h9 : (pCoreOf 2 Y).relIndex Y = 9) (hpow : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y)
    (hcomm : ⁅Y, Y⁆ ≤ pCoreOf 2 Y) (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hxY : ∃ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 Y) (hQH : Q ≤ H)
    (hirr : ∀ Y₁ : Subgroup G, pCoreOf 2 Y ≤ Y₁ → Y₁ ≤ Y →
      Q ≤ Subgroup.normalizer (Y₁ : Set G) → Y₁ = pCoreOf 2 Y ∨ Y₁ = Y)
    {n : ℕ} (hH : Nat.card H ∣ 27 * 2 ^ n) :
    ((2 : ℚ) : WithTop ℚ) < qhatInt H W hW.2.2.1 ∧
      IsPGroup 2 (H ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) := by
  classical
  have hWel := hW.2.2.1
  let _ : CommGroup W := commGroupOfElemAbelian hWel
  have hV : ∀ v : W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hWel.2 v v.2)
  have hHN : H ≤ Subgroup.normalizer (W : Set G) := hW.2.1
  set CW := Subgroup.centralizer (W : Set G) with hCW
  let c : H →* MulAut W := (conjAct W).comp (Subgroup.inclusion hHN)
  have hc1 : ∀ h : H, c h = 1 ↔ (h : G) ∈ CW := fun h => A4.normalizerMonoidHom_eq_one_iff
  set K := autOn H W with hK
  set P := autOn Y W with hP
  have hmemK : ∀ g, g ∈ K ↔ ∃ h : H, c h = g := by
    intro g
    rw [hK, autOn, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨Subgroup.inclusion hHN h, h.2, rfl⟩
  have hmemP : ∀ g, g ∈ P ↔ ∃ h : H, (h : G) ∈ Y ∧ c h = g := by
    intro g
    rw [hP, autOn, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hYH hm⟩, hm, rfl⟩
    · rintro ⟨h, hhY, rfl⟩
      exact ⟨Subgroup.inclusion hHN h, hhY, rfl⟩
  have hPK : P ≤ K := autOn_le_autOn W hYH
  have hcY : ∀ h : H, (h : G) ∈ pCoreOf 2 Y → c h = 1 := fun h hh =>
    (hc1 h).mpr (by rw [← hYW] at hh; exact hh.2)
  have hPcard : Nat.card P = 9 := by
    rw [hP, card_autOn_eq_relIndex (hYH.trans hHN), hYW, h9]
  have hPE : IsE9 P := by
    refine ⟨?_, ?_, hPcard⟩
    · intro a ha b hb
      obtain ⟨y₁, hy₁, rfl⟩ := (hmemP a).mp ha
      obtain ⟨y₂, hy₂, rfl⟩ := (hmemP b).mp hb
      have h1 : c ⁅y₁, y₂⁆ = 1 :=
        hcY _ (hcomm (Subgroup.commutator_mem_commutator hy₁ hy₂))
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := (hmemP a).mp ha
      rw [← map_pow]
      exact hcY _ (hpow _ hy)
  have hKP : ∀ k ∈ K, ∀ g ∈ P, k * g * k⁻¹ ∈ P := by
    intro k hk g hg
    obtain ⟨h, rfl⟩ := (hmemK k).mp hk
    obtain ⟨y, hy, rfl⟩ := (hmemP g).mp hg
    refine (hmemP _).mpr ⟨h * y * h⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHY h.2) y).mp hy
  have hKPn : ∀ k ∈ K, k ∈ Subgroup.normalizer (P : Set (MulAut W)) := fun k hk =>
    A4.mem_normalizer_of_conj_mem (hKP k hk)
  set x₀ := c ⟨x, hxH⟩ with hx₀
  have hx₀K : x₀ ∈ K := (hmemK _).mpr ⟨_, rfl⟩
  have hx₀3 : x₀ ^ 3 = 1 := by
    rw [hx₀, ← map_pow, ← map_one c]
    congr 1
    exact Subtype.ext hx3
  have hx₀P : ∃ g ∈ P, x₀ * g ≠ g * x₀ := by
    obtain ⟨y, hy, hxy⟩ := hxY
    refine ⟨c ⟨y, hYH hy⟩, (hmemP _).mpr ⟨_, hy, rfl⟩, fun h => hxy ?_⟩
    have h1 : c ⁅(⟨x, hxH⟩ : H), ⟨y, hYH hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h
    have h2 := (hc1 _).mp h1
    rw [← hYW]
    refine ⟨?_, h2⟩
    have hxyx : x * y * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hHY hxH) y).mp hy
    exact Y.mul_mem hxyx (Y.inv_mem hy)
  have hx₀1 : x₀ ≠ 1 := by
    rintro h
    obtain ⟨g, -, hg⟩ := hx₀P
    exact hg (by rw [h, one_mul, mul_one])
  have hx₀P' : x₀ ∉ P := by
    intro h
    obtain ⟨g, hg, hne⟩ := hx₀P
    exact hne (hPE.comm _ h _ hg)
  have hZcard : Nat.card (Subgroup.zpowers x₀) = 3 := by
    rw [Nat.card_zpowers]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx₀3 hx₀1
  have hKH : Nat.card K * Nat.card (H ⊓ CW : Subgroup G) = Nat.card H := by
    rw [hK, card_autOn_eq_relIndex hHN]
    have h1 := Subgroup.relIndex_mul_card (H ⊓ CW) H
    rwa [inf_eq_left.mpr inf_le_left] at h1
  have hKdvd : Nat.card K ∣ Nat.card H := ⟨_, hKH.symm⟩
  have hK27 : 27 ∣ Nat.card K := by
    have hZN : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr (hKPn x₀ hx₀K)
    have h1 := card_sup_eq_of_le_normalizer hZN
    rw [relIndex_eq_card_of_inf_eq_bot (inf_zpowers_eq_bot hx₀3 hx₀P'), hPcard, hZcard] at h1
    have h2 : Subgroup.zpowers x₀ ⊔ P ≤ K := sup_le (Subgroup.zpowers_le.mpr hx₀K) hPK
    rw [← show 9 * 3 = 27 by norm_num, ← h1]
    exact Subgroup.card_dvd_of_le h2
  have h2grp : IsPGroup 2 (H ⊓ CW : Subgroup G) := by
    have h1 : 27 * Nat.card (H ⊓ CW : Subgroup G) ∣ 27 * 2 ^ n :=
      (Nat.mul_dvd_mul_right hK27 _).trans (hKH ▸ hH)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
    exact IsPGroup.of_card hk
  refine ⟨?_, h2grp⟩
  have hirrK : ∀ d ∈ P, d ≠ 1 → ∃ k ∈ K, k * d * k⁻¹ ∉ Subgroup.zpowers d := by
    intro d hd hd1
    by_contra hcon
    push Not at hcon
    obtain ⟨y₀, hy₀, rfl⟩ := (hmemP d).mp hd
    set Y₁ : Subgroup G := Y ⊓ ((Subgroup.zpowers (c y₀)).comap c).map H.subtype with hY₁
    have hmemY₁ : ∀ g, g ∈ Y₁ ↔ g ∈ Y ∧ ∃ hg : g ∈ H, c ⟨g, hg⟩ ∈ Subgroup.zpowers (c y₀) := by
      intro g
      rw [hY₁, Subgroup.mem_inf]
      constructor
      · rintro ⟨hgY, ⟨h, hh, rfl⟩⟩
        exact ⟨hgY, h.2, hh⟩
      · rintro ⟨hgY, hg, hh⟩
        exact ⟨hgY, ⟨⟨g, hg⟩, hh, rfl⟩⟩
    have hO : pCoreOf 2 Y ≤ Y₁ := by
      intro g hg
      have hgY : g ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y hg
      refine (hmemY₁ g).mpr ⟨hgY, hYH hgY, ?_⟩
      rw [hcY ⟨g, hYH hgY⟩ hg]
      exact Subgroup.one_mem _
    have hQY₁ : Q ≤ Subgroup.normalizer (Y₁ : Set G) := by
      intro q hq
      refine A4.mem_normalizer_of_conj_mem fun g hg => ?_
      obtain ⟨hgY, hgH, hgc⟩ := (hmemY₁ g).mp hg
      refine (hmemY₁ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hHY (hQH hq)) g).mp hgY,
        H.mul_mem (H.mul_mem (hQH hq) hgH) (H.inv_mem (hQH hq)), ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hgc
      have h1 : c ⟨q * g * q⁻¹, H.mul_mem (H.mul_mem (hQH hq) hgH) (H.inv_mem (hQH hq))⟩ =
          (c ⟨q, hQH hq⟩ * c y₀ * (c ⟨q, hQH hq⟩)⁻¹) ^ m := by
        rw [conj_zpow, hm, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1]
      exact Subgroup.zpow_mem _ (hcon _ ((hmemK _).mpr ⟨_, rfl⟩)) m
    rcases hirr Y₁ hO inf_le_left hQY₁ with h | h
    · apply hd1
      have hy₀Y₁ : (y₀ : G) ∈ Y₁ := (hmemY₁ _).mpr ⟨hy₀, y₀.2, Subgroup.mem_zpowers _⟩
      rw [h] at hy₀Y₁
      exact hcY y₀ hy₀Y₁
    · have hle : P ≤ Subgroup.zpowers (c y₀) := by
        intro g hg
        obtain ⟨y, hy, rfl⟩ := (hmemP g).mp hg
        have hyY₁ : (y : G) ∈ Y₁ := h ▸ hy
        obtain ⟨_, hyH, hyc⟩ := (hmemY₁ _).mp hyY₁
        exact hyc
      have h1 := Subgroup.card_le_of_le hle
      rw [hPcard, Nat.card_zpowers] at h1
      have h2 : orderOf (c y₀) ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hPE.pow _ hd)
      omega
  have hinvK : ∀ a ∈ K, a ^ 2 = 1 → a ≠ 1 → ∃ g ∈ P, a * g ≠ g * a := by
    intro a haK ha2 ha1
    by_contra hcon
    push Not at hcon
    set C := K ⊓ Subgroup.centralizer (P : Set (MulAut W)) with hCdef
    have haC : a ∈ C := ⟨haK, Subgroup.mem_centralizer_iff.mpr fun g hg => (hcon g hg).symm⟩
    have hPC : P ≤ C := fun g hg =>
      ⟨hPK hg, Subgroup.mem_centralizer_iff.mpr fun g' hg' => hPE.comm g' hg' g hg⟩
    have hCn : ∀ k ∈ K, ∀ g ∈ C, k * g * k⁻¹ ∈ C := by
      intro k hk g hg
      refine ⟨K.mul_mem (K.mul_mem hk hg.1) (K.inv_mem hk),
        Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hu' : k⁻¹ * u * k ∈ P := by
        have := hKP k⁻¹ (K.inv_mem hk) u hu
        rwa [inv_inv] at this
      have h1 := Subgroup.mem_centralizer_iff.mp hg.2 _ hu'
      calc u * (k * g * k⁻¹) = k * ((k⁻¹ * u * k) * g) * k⁻¹ := by group
        _ = k * (g * (k⁻¹ * u * k)) * k⁻¹ := by rw [h1]
        _ = k * g * k⁻¹ * u := by group
    have hx₀C : x₀ ∉ C := by
      intro h
      obtain ⟨g, hg, hne⟩ := hx₀P
      exact hne (Subgroup.mem_centralizer_iff.mp h.2 g hg).symm
    have hC27 : ¬ 27 ∣ Nat.card C := by
      intro h27
      have hZN : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (C : Set (MulAut W)) :=
        Subgroup.zpowers_le.mpr (A4.mem_normalizer_of_conj_mem (hCn x₀ hx₀K))
      have h1 := card_sup_eq_of_le_normalizer hZN
      rw [relIndex_eq_card_of_inf_eq_bot (inf_zpowers_eq_bot hx₀3 hx₀C), hZcard] at h1
      have h2 : Subgroup.zpowers x₀ ⊔ C ≤ K := sup_le (Subgroup.zpowers_le.mpr hx₀K) inf_le_left
      have h3 : 81 ∣ Nat.card K := by
        have := Subgroup.card_dvd_of_le h2
        rw [h1] at this
        exact (Nat.mul_dvd_mul_right h27 3).trans this
      have h4 : 81 ∣ 27 * 2 ^ n := (h3.trans hKdvd).trans hH
      have h5 : 3 ∣ 2 ^ n := by
        have : 27 * 3 ∣ 27 * 2 ^ n := by simpa using h4
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
      omega
    have ha2' : IsPGroup 2 (Subgroup.zpowers a) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime ha2 ha1
    obtain ⟨S, hS, haS⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr haC) ha2'
    obtain ⟨hSC, hS2, hSodd⟩ := hS
    obtain ⟨s, hs⟩ := hS2.exists_card_eq
    have hCS : Nat.card C = 2 ^ s * S.relIndex C := by
      have h1 := Subgroup.relIndex_mul_card S C
      rw [inf_eq_left.mpr hSC, hs] at h1
      rw [← h1, mul_comm]
    have hCdvd : Nat.card C ∣ 27 * 2 ^ n :=
      ((Subgroup.card_dvd_of_le (inf_le_left : C ≤ K)).trans hKdvd).trans hH
    have hiodd : ¬ 2 ∣ S.relIndex C := hSodd
    have hi27 : S.relIndex C ∣ 27 := by
      have h1 : S.relIndex C ∣ 27 * 2 ^ n := (Dvd.intro_left _ hCS.symm).trans hCdvd
      have hcop : Nat.Coprime (S.relIndex C) (2 ^ n) :=
        Nat.Coprime.pow_right n ((Nat.coprime_comm.mp
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hiodd)))
      exact hcop.dvd_of_dvd_mul_right h1
    have hi9 : 9 ∣ S.relIndex C := by
      have h1 : 9 ∣ 2 ^ s * S.relIndex C := hCS ▸ (hPcard ▸ Subgroup.card_dvd_of_le hPC)
      have hcop : Nat.Coprime 9 (2 ^ s) := Nat.Coprime.pow_right s (by norm_num)
      exact hcop.dvd_of_dvd_mul_left h1
    have hi : S.relIndex C = 9 := by
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show S.relIndex C ∣ 3 ^ 3 by simpa using hi27)
      interval_cases j
      · rw [hj'] at hi9; norm_num at hi9
      · rw [hj'] at hi9; norm_num at hi9
      · rw [hj']; norm_num
      · exfalso
        apply hC27
        rw [hCS, hj']
        exact Dvd.intro_left _ rfl
    have hPS : P ⊓ S = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hgP, hgS⟩
      have h1 : g ^ 3 = 1 := hPE.pow g hgP
      obtain ⟨k, hk⟩ := hS2 ⟨g, hgS⟩
      have h2 : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
    have hSN : S ≤ Subgroup.normalizer (P : Set (MulAut W)) := fun g hg =>
      hKPn g (hSC hg).1
    have hPSC : S ⊔ P = C := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hSC hPC) ?_
      rw [card_sup_eq_of_le_normalizer hSN, hPcard,
        relIndex_eq_card_of_inf_eq_bot hPS, hs, hCS, hi, mul_comm]
    have hdecomp : ∀ g ∈ C, ∃ u ∈ S, ∃ v ∈ P, g = u * v := by
      intro g hg
      rw [← hPSC] at hg
      have hg' : g ∈ ((S ⊔ P : Subgroup (MulAut W)) : Set (MulAut W)) := hg
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S P hSN] at hg'
      obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hg'
      exact ⟨u, hu, v, hv, rfl⟩
    have h2elt : ∀ g ∈ C, ∀ m : ℕ, g ^ 2 ^ m = 1 → g ∈ S := by
      intro g hg m hm
      obtain ⟨u, hu, v, hv, rfl⟩ := hdecomp g hg
      have huv : Commute u v :=
        (Subgroup.mem_centralizer_iff.mp (hSC hu).2 v hv).symm
      rw [huv.mul_pow] at hm
      have hv2 : v ^ 2 ^ m ∈ P ⊓ S := by
        refine ⟨P.pow_mem hv _, ?_⟩
        have : v ^ 2 ^ m = (u ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hm
        rw [this]
        exact S.inv_mem (S.pow_mem hu _)
      rw [hPS, Subgroup.mem_bot] at hv2
      have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
      have hv1 : v = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one (hPE.pow v hv)) (orderOf_dvd_of_pow_eq_one hv2))
      rw [hv1, mul_one]
      exact hu
    have hSK : ∀ k ∈ K, ∀ u ∈ S, k * u * k⁻¹ ∈ S := by
      intro k hk u hu
      obtain ⟨m, hm⟩ := hS2 ⟨u, hu⟩
      have hm' : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      refine h2elt _ (hCn k hk u (hSC hu)) m ?_
      rw [conj_pow, hm', mul_one, mul_inv_cancel]
    set D₂ : Subgroup G := (S.comap c).map H.subtype with hD₂
    have hD₂H : D₂ ≤ H := Subgroup.map_subtype_le _
    have hHD₂ : H ≤ Subgroup.normalizer (D₂ : Set G) := by
      intro h hh
      refine A4.mem_normalizer_of_conj_mem fun d hd => ?_
      obtain ⟨d', hd', rfl⟩ := hd
      refine ⟨⟨h, hh⟩ * d' * ⟨h, hh⟩⁻¹, ?_, by simp⟩
      show c _ ∈ S
      rw [map_mul, map_mul, map_inv]
      exact hSK _ ((hmemK _).mpr ⟨_, rfl⟩) _ hd'
    have hD₂C : D₂ ≤ CW := by
      refine hW.2.2.2 D₂ hD₂H hHD₂ fun d hd => ?_
      obtain ⟨d', hd', rfl⟩ := hd
      obtain ⟨m, hm⟩ := hS2 ⟨c d', hd'⟩
      have hm' : c d' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      refine ⟨m, ?_⟩
      have h1 : c (d' ^ 2 ^ m) = 1 := by rw [map_pow]; exact hm'
      exact (hc1 _).mp h1
    apply ha1
    obtain ⟨h, rfl⟩ := (hmemK a).mp haK
    have haS' : c h ∈ S := haS (Subgroup.mem_zpowers _)
    exact (hc1 h).mpr (hD₂C ⟨h, haS', rfl⟩)
  exact two_lt_qhatOf_of_isE9 hV hPE hKP hinvK hx₀K hx₀3 hx₀P hirrK

end CFSG.Quasithin.EmptyFaithfulMultiple
