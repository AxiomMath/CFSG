module

public import CFSG.Quasithin.EmptyFaithful.S152Y17

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

section Generic

theorem pCoreOf_eq_inf_of_normalizer {Y M : Subgroup G} (hYM : Y ≤ M)
    (hn : M ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y = Y ⊓ pCoreOf 2 M := by
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 Y) ?_
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYM) ?_ (pCoreOf_isPGroup 2 Y)
    exact hn.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
    intro g hg
    have hgM : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M (hYM hg)
    have hgM' : g⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      (Subgroup.normalizer (pCoreOf 2 M : Set G)).inv_mem hgM
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxY, hxQ⟩
      exact ⟨Y.mul_mem (Y.mul_mem hg hxY) (Y.inv_mem hg),
        (Subgroup.mem_normalizer_iff.mp hgM x).mp hxQ⟩
    · rintro ⟨h1, h2⟩
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      refine ⟨?_, ?_⟩
      · have := Y.mul_mem (Y.mul_mem (Y.inv_mem hg) h1) hg
        simpa [mul_assoc] using this
      · have := (Subgroup.mem_normalizer_iff.mp hgM' (g * x * g⁻¹)).mp h2
        rwa [e] at this

omit [Finite G] in
theorem mk_commute_iff_of_normal {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (a b : H) :
    (QuotientGroup.mk a : H ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a ↔
      a * b * a⁻¹ * b⁻¹ ∈ N := by
  have e : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : H ⧸ N) =
      ⁅(QuotientGroup.mk a : H ⧸ N), (QuotientGroup.mk b : H ⧸ N)⁆ := by
    simp [commutatorElement_def]
  rw [← QuotientGroup.eq_one_iff, e]
  exact commutatorElement_eq_one_iff_mul_comm.symm

omit [Finite G] in
theorem mem_oTwoZIn_iff {Y : Subgroup G} {g : G} :
    g ∈ oTwoZIn Y ↔ ∃ hg : g ∈ Y, ∀ w : ↥Y,
      ((⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹ * w⁻¹ : ↥Y) : G) ∈ pCoreOf 2 Y := by
  have hcore : ∀ c : ↥Y, c ∈ CFSG.pCore 2 ↥Y ↔ (c : G) ∈ pCoreOf 2 Y := by
    intro c
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem Y.subtype_injective).symm
  unfold oTwoZIn preimageModTwoCore
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun w => ?_⟩
    have hy' := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hy) (QuotientGroup.mk w)
    exact (hcore _).mp ((mk_commute_iff_of_normal (CFSG.pCore 2 ↥Y) y w).mp hy'.symm)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    exact ((mk_commute_iff_of_normal (CFSG.pCore 2 ↥Y) ⟨g, hg⟩ w).mpr
      ((hcore _).mpr (hc w))).symm

theorem mem_oTwoZIn_iff_star {Y M : Subgroup G} (hYM : Y ≤ M)
    (hn : M ≤ Subgroup.normalizer (Y : Set G)) {g : G} :
    g ∈ oTwoZIn Y ↔ ∃ hg : g ∈ Y, ∀ u ∈ imageOTwoQuot M Y,
      u * (QuotientGroup.mk ⟨g, hYM hg⟩ : OTwoQuot M) = QuotientGroup.mk ⟨g, hYM hg⟩ * u := by
  rw [mem_oTwoZIn_iff]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun u hu => ?_⟩
    obtain ⟨w, hwM, hwY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have h1 := hc ⟨w, hwY⟩
    rw [pCoreOf_eq_inf_of_normalizer hYM hn] at h1
    exact ((mk_commute_iff (M := M) ⟨g, hYM hg⟩ ⟨w, hwM⟩).mpr h1.2).symm
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun w => ?_⟩
    rw [pCoreOf_eq_inf_of_normalizer hYM hn]
    refine ⟨?_, ?_⟩
    · exact Y.mul_mem (Y.mul_mem (Y.mul_mem hg w.2) (Y.inv_mem hg)) (Y.inv_mem w.2)
    · have := hc (QuotientGroup.mk ⟨(w : G), hYM w.2⟩)
        (mem_imageOTwoQuot_iff.mpr ⟨w, hYM w.2, w.2, rfl⟩)
      exact (mk_commute_iff (M := M) ⟨g, hYM hg⟩ ⟨w, hYM w.2⟩).mp this.symm

theorem mem_of_mk_mem_of_odd {Y M : Subgroup G}
    (hn : M ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hxM : x ∈ M)
    (hodd : Odd (orderOf x))
    (hx : (QuotientGroup.mk ⟨x, hxM⟩ : OTwoQuot M) ∈ imageOTwoQuot M Y) : x ∈ Y := by
  obtain ⟨y, hyM, hyY, hy⟩ := mem_imageOTwoQuot_iff.mp hx
  have hqM : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem hyM) hxM
  have hq : y⁻¹ * x ∈ pCoreOf 2 M := by
    have h1 : (QuotientGroup.mk ⟨y⁻¹ * x, hqM⟩ : OTwoQuot M) = 1 := by
      have e : (⟨y⁻¹ * x, hqM⟩ : ↥M) = (⟨y, hyM⟩ : ↥M)⁻¹ * ⟨x, hxM⟩ := rfl
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy, inv_mul_cancel]
    exact (mk_eq_one_iff_mem_pCoreOf _).mp h1
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨y⁻¹ * x, hq⟩
  have hqk : (y⁻¹ * x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hnorm : (Y.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  let φ : ↥M →* ↥M ⧸ Y.subgroupOf M := QuotientGroup.mk' (Y.subgroupOf M)
  have hφy : φ ⟨y, hyM⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hyY
  have hφx : φ ⟨x, hxM⟩ = φ ⟨y⁻¹ * x, hqM⟩ := by
    have e : (⟨x, hxM⟩ : ↥M) = ⟨y, hyM⟩ * ⟨y⁻¹ * x, hqM⟩ := by
      apply Subtype.ext
      simp
    rw [e, map_mul, hφy, one_mul]
  have hz : φ ⟨x, hxM⟩ ^ 2 ^ k = 1 := by
    rw [hφx, ← map_pow]
    have : (⟨y⁻¹ * x, hqM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hqk)
    rw [this, map_one]
  have hodd' : Odd (orderOf (φ ⟨x, hxM⟩)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd φ ⟨x, hxM⟩)
    have e : orderOf (⟨x, hxM⟩ : ↥M) = orderOf x := (Subgroup.orderOf_coe ⟨x, hxM⟩).symm
    rw [e]
    exact hodd
  have hz1 : φ ⟨x, hxM⟩ = 1 := eq_one_of_odd_of_two_power hodd' hz
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
  exact hz1

end Generic

section Main

variable {T Mc M : Subgroup G}

theorem oTwoUpper_oTwoZIn_eq_theta (h : Data T Mc M)
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    (hYnorm : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G))
    (hnonab : ¬ ∀ a ∈ Ys T Mc M, ∀ c ∈ Ys T Mc M, a * c = c * a)
    (hP : IsPOnePlusTwo 3 ↥(Ys T Mc M)) :
    oTwoUpper (oTwoZIn (yOf152 T Mc M)) =
      thetaOf (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYM : yOf152 T Mc M ≤ M := h.yOf_le_M
  have hexp : ∀ y ∈ Ys T Mc M, y ^ 3 = 1 := fun y hy => congrArg Subtype.val (hP.2.2 ⟨y, hy⟩)
  have hKc := K_central_Ys h
  have hcomm_le := Data.commutator_le_K h hEab
  obtain ⟨a, ha, a', ha', hne⟩ : ∃ a ∈ Ys T Mc M, ∃ a' ∈ Ys T Mc M, a * a' ≠ a' * a := by
    by_contra hcon
    push Not at hcon
    exact hnonab hcon
  have hz₀Y : ⁅a, a'⁆ ∈ Ys T Mc M :=
    (Ys T Mc M).mul_mem ((Ys T Mc M).mul_mem ((Ys T Mc M).mul_mem ha ha')
      ((Ys T Mc M).inv_mem ha)) ((Ys T Mc M).inv_mem ha')
  have hz₀K : ⁅a, a'⁆ ∈ Ys T Mc M ⊓ (piStar h).ker :=
    hcomm_le (Subgroup.commutator_mem_commutator ha ha')
  have hz₀1 : ⁅a, a'⁆ ≠ 1 := fun h1 => hne (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hz₀3 : ⁅a, a'⁆ ^ 3 = 1 := hexp _ hz₀Y
  have haK : a ∉ Ys T Mc M ⊓ (piStar h).ker := fun haK => hne (hKc a haK a' ha').symm
  have ha1 : a ≠ 1 := fun h1 => haK (h1 ▸ (Ys T Mc M ⊓ (piStar h).ker).one_mem)
  have hao : orderOf a = 3 := orderOf_eq_prime (hexp a ha) ha1
  have hEz : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers ⁅a, a'⁆) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz₀3, one_zpow]
  have hzle : Subgroup.zpowers ⁅a, a'⁆ ≤ Ys T Mc M ⊓ (piStar h).ker :=
    Subgroup.zpowers_le.mpr hz₀K
  have haz : a ∉ Subgroup.zpowers ⁅a, a'⁆ := fun hh => haK (hzle hh)
  obtain ⟨hA1, hA1card⟩ := exists_elemAbelian_sup_zpowers (p := 3) hEz hao
    (fun e he => (hKc e (hzle he) a ha).symm) haz
  have hA1Y : Subgroup.zpowers ⁅a, a'⁆ ⊔ Subgroup.zpowers a ≤ Ys T Mc M :=
    sup_le (Subgroup.zpowers_le.mpr hz₀Y) (Subgroup.zpowers_le.mpr ha)
  have hzcard : Nat.card (Subgroup.zpowers ⁅a, a'⁆) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz₀3 hz₀1]
  have hZcard : Nat.card (Subgroup.center ↥(Ys T Mc M)) = 3 := by
    have := hP.1
    exact CFSG.IsExtraspecial.center_order_p 3 ↥(Ys T Mc M)
  have hZK : ∀ u ∈ Ys T Mc M, (∀ v ∈ Ys T Mc M, v * u = u * v) →
      u ∈ Ys T Mc M ⊓ (piStar h).ker := by
    intro u hu hcen
    by_contra huK
    have hu1 : u ≠ 1 := fun h1 => huK (h1 ▸ (Ys T Mc M ⊓ (piStar h).ker).one_mem)
    have huo : orderOf u = 3 := orderOf_eq_prime (hexp u hu) hu1
    have huz : u ∉ Subgroup.zpowers ⁅a, a'⁆ := fun hh => huK (hzle hh)
    obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers (p := 3) hEz huo
      (fun e he => hcen e (hzle he).1) huz
    have hAY : Subgroup.zpowers ⁅a, a'⁆ ⊔ Subgroup.zpowers u ≤ Ys T Mc M :=
      sup_le (Subgroup.zpowers_le.mpr hz₀Y) (Subgroup.zpowers_le.mpr hu)
    have hAc : Subgroup.zpowers ⁅a, a'⁆ ⊔ Subgroup.zpowers u ≤
        Subgroup.centralizer (Ys T Mc M : Set (OTwoQuot M)) := by
      refine sup_le ?_ ?_
      · intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact hKc e (hzle he) v hv
      · intro e he
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (Commute.zpow_right (show Commute v u from hcen v hv) k).eq
    have hle : (Subgroup.zpowers ⁅a, a'⁆ ⊔ Subgroup.zpowers u).subgroupOf (Ys T Mc M) ≤
        Subgroup.center ↥(Ys T Mc M) := by
      intro w hw
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_centralizer_iff.mp (hAc hw) (g : OTwoQuot M) g.2
      exact Subtype.ext this
    have hc1 := Subgroup.card_le_of_le hle
    rw [hZcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hAcard, hzcard] at hc1
    omega
  have hZ : ∀ g, g ∈ oTwoZIn (yOf152 T Mc M) → ∃ hg : g ∈ yOf152 T Mc M,
      (QuotientGroup.mk ⟨g, hYM hg⟩ : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := by
    intro g hg
    obtain ⟨hgY, hc⟩ := (mem_oTwoZIn_iff_star hYM hYnorm).mp hg
    refine ⟨hgY, hZK _ (mem_imageOTwoQuot_iff.mpr ⟨g, hYM hgY, hgY, rfl⟩) ?_⟩
    intro v hv
    exact hc v hv
  apply le_antisymm
  ·
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgX, hgodd⟩
    obtain ⟨hgY, hgK⟩ := hZ g hgX
    have hgM : g ∈ M := hYM hgY
    have hgC : g ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
      (piStar_mk_eq_one_iff h hgM).mp (MonoidHom.mem_ker.mp hgK.2)
    have hg3 : g ^ 3 = 1 := by
      have h2 : g ^ 3 ∈ pCoreOf 2 M := by
        have h1 : (QuotientGroup.mk (⟨g, hgM⟩ ^ 3 : ↥M) : OTwoQuot M) = 1 := by
          rw [QuotientGroup.mk_pow]
          exact hexp _ hgK.1
        exact (mk_eq_one_iff_mem_pCoreOf _).mp h1
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨g ^ 3, h2⟩
      have hk' : (g ^ 3) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hodd3 : Odd (orderOf (g ^ 3)) := Odd.of_dvd_nat hgodd (orderOf_pow_dvd 3)
      exact eq_one_of_odd_of_two_power hodd3 hk'
    by_cases hg1 : g = 1
    · rw [hg1]; exact (thetaOf _).one_mem
    · exact Subgroup.subset_closure ⟨⟨hgM, hgC⟩, orderOf_eq_prime hg3 hg1⟩
  ·
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨⟨hxM, hxC⟩, hxo⟩
    have hxodd : Odd (orderOf x) := by rw [hxo]; decide
    have hxs : (QuotientGroup.mk ⟨x, hxM⟩ : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := by
      by_contra hxsK
      set xs : OTwoQuot M := QuotientGroup.mk ⟨x, hxM⟩ with hxsdef
      have hx3 : x ^ 3 = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hxo] at this
      have hxs3 : xs ^ 3 = 1 := by
        rw [hxsdef, ← QuotientGroup.mk_pow]
        have : (⟨x, hxM⟩ ^ 3 : ↥M) = 1 := Subtype.ext (by simpa using hx3)
        rw [this]
        rfl
      have hxs1 : xs ≠ 1 := by
        intro hone
        have hmem : x ∈ pCoreOf 2 M := (mk_eq_one_iff_mem_pCoreOf ⟨x, hxM⟩).mp hone
        obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨x, hmem⟩
        have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have hd := orderOf_dvd_of_pow_eq_one hk'
        rw [hxo] at hd
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
        omega
      have hxsord : orderOf xs = 3 := orderOf_eq_prime hxs3 hxs1
      have hxsker : xs ∈ (piStar h).ker := MonoidHom.mem_ker.mpr ((piStar_mk_eq_one_iff h hxM).mpr hxC)
      have hxsY : xs ∉ Ys T Mc M := fun hY => hxsK ⟨hY, hxsker⟩
      have hxsC : xs ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
        mem_imageOTwoQuot_iff.mpr ⟨x, hxM, ⟨hxM, hxC⟩, rfl⟩
      have hcommY : ∀ e ∈ Ys T Mc M, Commute e xs := by
        intro y hy
        have h0 := Data.Ys_Rcs_centralize h
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
        exact Subgroup.mem_centralizer_iff.mp (h0 hxsC) y (Subgroup.mem_sup_left hy)
      have hxsA : xs ∉ Subgroup.zpowers ⁅a, a'⁆ ⊔ Subgroup.zpowers a := fun hh => hxsY (hA1Y hh)
      obtain ⟨hA2, hA2card⟩ := exists_elemAbelian_sup_zpowers (p := 3) hA1 hxsord
        (fun e he => hcommY e (hA1Y he)) hxsA
      have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) :=
        le_pRank Nat.prime_three le_top hA2 (k := 3) (by rw [hA2card, hA1card, hzcard]; norm_num)
      have h4 := pRank_Mstar_le_two h Nat.prime_three (by norm_num)
      omega
    have hxY : x ∈ yOf152 T Mc M := mem_of_mk_mem_of_odd hYnorm hxM hxodd hxs.1
    have hxX : x ∈ oTwoZIn (yOf152 T Mc M) :=
      (mem_oTwoZIn_iff_star hYM hYnorm).mpr ⟨hxY, fun u hu => hKc _ hxs u hu⟩
    exact mem_oTwoUpper_of_odd hxX hxodd

end Main

end S152Y

end CFSG.Quasithin
