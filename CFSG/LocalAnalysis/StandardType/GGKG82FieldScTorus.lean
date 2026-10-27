module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankTorus
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.StandardType.KG82

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed CFSG.StandardType.TwE6Lang

variable {k : Type} [Field k]

theorem map_nt
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c)) (i : Fin (Tag.rank .E6))
    (t : kˣ) : φ (e6Data_valid.nt k i t) = e6Data_valid.nt k i (Units.map (δ : k →* k) t) := by
  simp only [MinData.Valid.nt, map_mul, hφ, Units.coe_map, MonoidHom.coe_coe, map_neg,
    Units.val_inv_eq_inv_val, map_inv₀]

theorem map_hm
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c)) (i : Fin (Tag.rank .E6))
    (t : kˣ) : φ (e6Data_valid.hm k i t) = e6Data_valid.hm k i (Units.map (δ : k →* k) t) := by
  rw [MinData.Valid.hm, map_mul, map_inv, map_nt hφ, map_nt hφ, map_one, MinData.Valid.hm]

theorem map_torusHom
    {δ : k →+* k} {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c))
    (u : Fin (Tag.rank .E6) → kˣ) :
    φ (torusHom k u) = torusHom k fun a => Units.map (δ : k →* k) (u a) := by
  have h : φ.comp (torusHom k) =
      (torusHom k).comp (MonoidHom.compLeft (Units.map (δ : k →* k)) (Fin (Tag.rank .E6))) := by
    refine MonoidHom.pi_ext fun a t => ?_
    simp only [MonoidHom.comp_apply, torusHom_mulSingle, map_hm hφ]
    rw [← torusHom_mulSingle]
    congr 1
    funext b
    rw [MonoidHom.compLeft_apply, Function.comp_apply]
    by_cases hb : b = a
    · subst hb
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hb, Pi.mulSingle_eq_of_ne hb, map_one]
  exact DFunLike.congr_fun h u

theorem map_nm
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c))
    (i : Fin (Tag.rank .E6)) : φ (e6Data_valid.nm k i) = e6Data_valid.nm k i := by
  rw [MinData.Valid.nm, map_nt hφ, map_one]

theorem map_nHatE
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c))
    (i : Fin (Tag.rank .F4)) : φ (nHatE k i) = nHatE k i := by
  fin_cases i
  · exact map_nm hφ (nd 1)
  · exact map_nm hφ (nd 3)
  · change φ (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4)) =
      e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4)
    rw [map_mul, map_nm hφ, map_nm hφ]
  · change φ (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)) =
      e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)
    rw [map_mul, map_nm hφ, map_nm hφ]

theorem map_nWord
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c))
    (L : List (Fin (Tag.rank .F4))) : φ (nWord k L) = nWord k L := by
  induction L with
  | nil => rw [nWord_nil, map_one]
  | cons i L ih => rw [nWord_cons, map_mul, map_nHatE hφ, ih]

theorem map_langOne
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c)) (θ : k →+* k) {l : k}
    (hl : δ l = l) (hθl : δ (θ l) = θ l) : φ (langOne k θ l) = langOne k θ l := by
  simp only [langOne, map_mul, hφ, map_sub, map_one, map_inv₀, hl, hθl]

theorem map_langG3
    {δ : k →+* k}
    {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c)) (θ : k →+* k) {l : k}
    (hl : δ l = l) (hθl : δ (θ l) = θ l) : φ (langG3 k θ l) = langG3 k θ l := by
  have hG : ∀ j, φ (frameG k θ l j) = frameG k θ l j := fun j => by
    rw [frameG, map_mul, map_mul, map_inv, map_nWord hφ, map_langOne hφ θ hl hθl]
  rw [langG3, map_mul, map_mul, hG, hG, hG]

theorem map_torusConj3
    {δ : k →+* k} {φ : e6Data_valid.minGroup k →* e6Data_valid.minGroup k}
    (hφ : ∀ γ c, φ (e6Data_valid.xm k γ c) = e6Data_valid.xm k γ (δ c)) (θ : k →+* k) {l : k}
    (hl : δ l = l) (hθl : δ (θ l) = θ l) {η : kˣ} {i : ℕ}
    (hη : Units.map (δ : k →* k) η = η ^ i) (w : Fin (Tag.rank .E6) → Subgroup.zpowers η) :
    φ (torusConj3 k θ l η w) = torusConj3 k θ l η (w ^ i) := by
  have hw : (fun a => Units.map (δ : k →* k) (w a : kˣ)) = fun a => ((w ^ i) a : kˣ) := by
    funext a
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (w a).2
    rw [Pi.pow_apply, SubgroupClass.coe_pow, ← hm, map_zpow, hη, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  change φ (langG3 k θ l * torusHom k (fun a => (w a : kˣ)) * (langG3 k θ l)⁻¹) =
    langG3 k θ l * torusHom k (fun a => ((w ^ i) a : kˣ)) * (langG3 k θ l)⁻¹
  rw [map_mul, map_mul, map_inv, map_langG3 hφ θ hl hθl, map_torusHom hφ, hw]

@[expose] def cubeHom (η : kˣ) :
    (Fin (Tag.rank .E6) → Subgroup.zpowers η) →* (Fin (Tag.rank .E6) → kˣ) :=
  (MonoidHom.compLeft (Subgroup.zpowers η).subtype _).comp (powMonoidHom 3)

@[expose] def rankSixCond (η : kˣ) : Subgroup (Fin (Tag.rank .E6) → Subgroup.zpowers η) :=
  sCond η ⊓ (centerChars .E6 k).comap (cubeHom η)

theorem mem_rankSixCond {η : kˣ} {w : Fin (Tag.rank .E6) → Subgroup.zpowers η} :
    w ∈ rankSixCond η ↔ w ∈ sCond η ∧ (fun a => (w a : kˣ) ^ 3) ∈ centerChars .E6 k :=
  Iff.rfl

@[expose] def centreVec (η : kˣ) : Fin (Tag.rank .E6) → Subgroup.zpowers η :=
  fun a => ⟨η ^ e6c a, zpow_mem (Subgroup.mem_zpowers η) _⟩

theorem centreVec_mem {η : kˣ} (hη : η ^ 9 = 1) : centreVec η ∈ rankSixCond η := by
  refine mem_rankSixCond.2 ⟨mem_sCond.2 ?_, ?_⟩
  · apply Subtype.ext
    change η ^ e6c (nd 3) = (η ^ e6c (nd 1)) ^ 2
    rw [show e6c (nd 3) = 0 from rfl, show e6c (nd 1) = 0 from rfl, zpow_zero, one_pow]
  · have h : (fun a => ((centreVec η a : Subgroup.zpowers η) : kˣ) ^ 3) = tvec (η ^ 3) e6c := by
      funext a
      rw [tvec, centreVec, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h]
    exact tvec_mem_centerChars (n := 3) (by rw [← pow_mul]; exact hη) e6c_dvd

theorem isPGroup_zpowers_pi {η : kˣ} (hη : η ^ 9 = 1) :
    IsPGroup 3 (Fin (Tag.rank .E6) → Subgroup.zpowers η) := by
  intro w
  refine ⟨2, funext fun a => Subtype.ext ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (w a).2
  rw [Pi.pow_apply, SubgroupClass.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    show ((3 ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, hη, one_zpow]
  rfl

theorem card_rankSixCond [Finite k] {η : kˣ} (hη : orderOf η = 9) :
    3 ^ 6 ≤ Nat.card (rankSixCond η) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : η ^ 9 = 1 := by rw [← hη]; exact pow_orderOf_eq_one η
  have hζ3 : orderOf (η ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hη]; norm_num), hη]
  have hle : Subgroup.zpowers (η ^ 3) ≤ Subgroup.zpowers η :=
    Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers η) 3)
  let ι : (Fin (Tag.rank .E6) → Subgroup.zpowers (η ^ 3)) →*
      (Fin (Tag.rank .E6) → Subgroup.zpowers η) :=
    MonoidHom.compLeft (Subgroup.inclusion hle) _
  have hι : Function.Injective ι := fun w w' h => funext fun a =>
    Subgroup.inclusion_injective hle (congrFun h a)
  set V₁ := (sCond (η ^ 3)).map ι with hV₁
  have hcard₁ : Nat.card V₁ = 3 ^ 5 := by
    rw [hV₁, Subgroup.card_map_of_injective hι, card_sCond hζ3]
  have hV₁le : V₁ ≤ rankSixCond η := by
    rintro _ ⟨w, hw, rfl⟩
    refine mem_rankSixCond.2 ⟨mem_sCond.2 ?_, ?_⟩
    · have h := congrArg (Subgroup.inclusion hle) (mem_sCond.1 hw)
      rwa [map_pow] at h
    · have h1 : (fun a => ((ι w a : Subgroup.zpowers η) : kˣ) ^ 3) = 1 := by
        funext a
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (w a).2
        change ((w a : Subgroup.zpowers (η ^ 3)) : kˣ) ^ 3 = 1
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
          show 3 * 3 = 9 by norm_num, h9, one_zpow]
      rw [h1]
      exact one_mem _
  have hnot : centreVec η ∉ V₁ := by
    rintro ⟨w, -, hw⟩
    have h0 := congrArg (fun v : Fin (Tag.rank .E6) → Subgroup.zpowers η =>
      ((v (nd 0) : Subgroup.zpowers η) : kˣ)) hw
    change ((w (nd 0) : Subgroup.zpowers (η ^ 3)) : kˣ) = η ^ e6c (nd 0) at h0
    rw [show e6c (nd 0) = 1 from rfl, zpow_one] at h0
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (w (nd 0)).2
    rw [← hm] at h0
    have h3 : η ^ 3 = 1 := by
      rw [← h0, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
        show 3 * 3 = 9 by norm_num, h9, one_zpow]
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hη] at this
    norm_num at this
  have hP : IsPGroup 3 (rankSixCond η) :=
    (isPGroup_zpowers_pi h9).to_subgroup (rankSixCond η)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : 3 ^ 5 ∣ 3 ^ a := by
    rw [← hcard₁, ← ha]
    exact Subgroup.card_dvd_of_le hV₁le
  have ha5 : 5 ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  rcases Nat.lt_or_ge 5 a with h | h
  · rw [ha]
    exact Nat.pow_le_pow_right (by norm_num) h
  · have ha' : a = 5 := le_antisymm h ha5
    have heq : V₁ = rankSixCond η :=
      Subgroup.eq_of_le_of_card_ge hV₁le (by rw [ha, ha', hcard₁])
    exact absurd (heq ▸ centreVec_mem h9) hnot

theorem torusHom_eq_minTorus :
    torusHom k = minTorus e6Data_valid k :=
  rfl

theorem torusConj3_pow_three_mem_center
    (θ : k →+* k) (l : k) {η : kˣ} {w : Fin (Tag.rank .E6) → Subgroup.zpowers η}
    (hw : w ∈ rankSixCond η) :
    torusConj3 k θ l η w ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup k) := by
  have hz : torusHom k (fun a => (w a : kˣ) ^ 3) ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    rw [torusHom_eq_minTorus]
    exact (minTorus_mem_center_iff e6Data_valid k _).2 (mem_rankSixCond.1 hw).2
  have hw3 : (fun a => ((w ^ 3) a : kˣ)) = fun a => (w a : kˣ) ^ 3 :=
    funext fun a => by rw [Pi.pow_apply, SubgroupClass.coe_pow]
  have e : torusConj3 k θ l η w ^ 3 =
      langG3 k θ l * torusHom k (fun a => (w a : kˣ) ^ 3) * (langG3 k θ l)⁻¹ := by
    rw [← map_pow, ← hw3]
    rfl
  rw [e, Subgroup.mem_center_iff.1 hz (langG3 k θ l), mul_inv_cancel_right]
  exact hz

theorem exists_units_map_eq_pow {K : Type} [Field K] {δ : K ≃+* K} (hδ : δ ^ 3 = 1) {η : Kˣ}
    (hη : orderOf η = 9) :
    ∃ i : ℕ, i % 3 = 1 ∧ Units.map (δ.toRingHom : K →* K) η = η ^ i := by
  have hprim : IsPrimitiveRoot (η : K) 9 := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
    exact hη
  have h9 : (δ (η : K)) ^ 9 = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hη, pow_orderOf_eq_one, Units.val_one, map_one]
  obtain ⟨i, hi9, hi⟩ := hprim.eq_pow_of_pow_eq_one h9
  have hδη : Units.map (δ.toRingHom : K →* K) η = η ^ i :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val, hi]; rfl)
  refine ⟨i, ?_, hδη⟩
  have hpow : ∀ m : ℕ, Units.map (δ.toRingHom : K →* K) (η ^ m) = η ^ (i * m) := fun m => by
    rw [map_pow, hδη, ← pow_mul]
  have h3 : Units.map (δ.toRingHom : K →* K) (Units.map (δ.toRingHom : K →* K)
      (Units.map (δ.toRingHom : K →* K) η)) = η := by
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact congrArg (fun φ : RingAut K => φ (η : K)) hδ
  have e1 : Units.map (δ.toRingHom : K →* K) η = η ^ (i * 1) := by rw [mul_one]; exact hδη
  rw [e1, hpow, hpow] at h3
  have hmod : i * (i * (i * 1)) ≡ 1 [MOD 9] := by
    rw [← hη]
    exact (pow_eq_pow_iff_modEq).1 (h3.trans (pow_one η).symm)
  unfold Nat.ModEq at hmod
  interval_cases i <;> simp_all

end CFSG.StandardType.KG82
