module

public import CFSG.Quasithin.EmptyFaithful.S14113Case
public import CFSG.Quasithin.Background.C129Used
public import CFSG.Quasithin.Background.C2PushA3
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.EmptyFaithful.S152He9A5
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.He16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c2_6_two_used (hC129 : ASC129StatementUsed G) {H R M : Subgroup G} (h : HypC23 H R M)
    (hF : CharTwo (oTwoFIn H)) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G),
      (∀ i, IsBlock2 (oTwoFIn H) (Lb i) ∧ IsAltType (Lb i) 3) ∧
      ∀ x ∈ oTwoFIn H, ∃ m ∈ M ⊓ oTwoFIn H, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
        x = m * (List.ofFn y).prod := by
  have hRH : R ≤ H := h.radical.1
  have hRp : IsPGroup 2 R := h.radical.isPGroup
  have hXH : oTwoFIn H ⊔ R ≤ H := sup_le C2Six.oTwoFIn_le hRH
  have hYX : oTwoFIn H ≤ oTwoFIn H ⊔ R := le_sup_left
  have hcgs : cgsIn (oTwoFIn H ⊔ R) R ≤ M ⊓ (oTwoFIn H ⊔ R) :=
    le_inf ((C2Nine.cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le _ R)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 (oTwoFIn H ⊔ R) R (M ⊓ (oTwoFIn H ⊔ R))
    (h.sqtk.mono hXH) (C2Six.charTwo_oTwoFIn_sup hRH hRp hF) (c2_6_one h) hcgs inf_le_right
  have hLY : ∀ i, Lb i ≤ oTwoFIn H := fun i =>
    C2Six.le_oTwoFIn_of_isShort2 hRH hRp (hLb i).1.1.1 (hLb i).1.1.2.1
  refine ⟨r, Lb, fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨hchi, -, -⟩ := hLb i
    have hA3 : IsAltType (Lb i) 3 := C2Six.isAltType_three_of_isChi0Block hchi (hLY i)
    refine ⟨⟨hchi.1.1, hLY i, ?_⟩, hA3⟩
    have hsub : IsSubnormal (Lb i) (oTwoFIn H ⊔ R) := IsBlock2.isSubnormal hchi.1
    exact (isSubnormal_iff_subgroupOf (hLY i)).mp (A3.subnormal_of_le_of_le hsub (hLY i) hYX)
  · obtain ⟨m, hm, y, hy, hxy⟩ := hprod x (hYX hx)
    have hprodY : (List.ofFn y).prod ∈ oTwoFIn H := by
      refine Subgroup.list_prod_mem _ fun z hz => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hLY i (hy i)
    have hmY : m ∈ oTwoFIn H := by
      have : m = x * ((List.ofFn y).prod)⁻¹ := by rw [hxy]; group
      rw [this]
      exact (oTwoFIn H).mul_mem hx ((oTwoFIn H).inv_mem hprodY)
    exact ⟨m, ⟨hm.1, hmY⟩, y, hy, hxy⟩

theorem le_of_forall_eq_mul_prod_of_threePrime {X : Type*} [Group X] {K M₀ Q : Subgroup X}
    (hK3 : ∀ x ∈ K, ¬ 3 ∣ orderOf x) (hQ : IsPGroup 3 Q) {r : ℕ} (B : Fin r → Subgroup X)
    (hBQ : ∀ i, B i ≤ Q) (hcomm : ∀ i, ∀ x ∈ K, ∀ y ∈ B i, Commute x y)
    (hx : ∀ x ∈ K, ∃ m ∈ M₀, ∃ b : Fin r → X, (∀ i, b i ∈ B i) ∧ x = m * (List.ofFn b).prod) :
    K ≤ M₀ := by
  intro x hxK
  obtain ⟨m, hm, b, hb, hxm⟩ := hx x hxK
  set f : X := (List.ofFn b).prod with hf
  have hfQ : f ∈ Q :=
    Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact hBQ i (hb i)
  have hfk : ∃ k : ℕ, f ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hQ ⟨f, hfQ⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hfc : Commute x f :=
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact hcomm i x hxK (b i) (hb i)
  have hm' : m = x * f⁻¹ := by rw [hxm]; group
  have := C2Push.mem_zpowers_mul_inv_of_commute hfc (hK3 x hxK) hfk
  rw [← hm'] at this
  exact Subgroup.zpowers_le.mpr hm this

theorem le_of_threePrime (hC129 : ASC129StatementUsed G) {G₀ R M₁ F₁ : Subgroup G}
    (hyp : HypC23 G₀ R M₁) (hF : CharTwo (oTwoFIn G₀)) (hF₁ : F₁ ≤ oTwoFIn G₀)
    (hn : (F₁.subgroupOf G₀).Normal)
    (h3 : ∀ (x : G) (hx : x ∈ G₀), x ∈ F₁ →
      ¬ 3 ∣ orderOf (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot G₀)) : F₁ ≤ M₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two_used hC129 hyp hF
  have hRG : R ≤ G₀ := hyp.radical.1
  have hOR : pCoreOf 2 G₀ ≤ R := c2_1_pCore_le hyp.radical
  have hRM : R ≤ M₁ := fun x hx =>
    hyp.cgs (inf_normalizer_le_cgsIn hyp.radical.2.1 ⟨hRG hx, Subgroup.le_normalizer hx⟩)
  have hOM : pCoreOf 2 G₀ ≤ M₁ := hOR.trans hRM
  have hLb' : ∀ i, IsBlock2 G₀ (Lb i) := fun i => isBlock2_of_oTwoFIn (hLb i).1
  have hKn : (imageOTwoQuot G₀ F₁).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  have hB3 : ∀ i, IsPGroup 3 (imageOTwoQuot G₀ (Lb i)) := by
    intro i
    obtain ⟨e⟩ := C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (IsBlock2.isSubnormal (hLb' i))
    have hcard : Nat.card ↥(imageOTwoQuot G₀ (Lb i)) = 3 ^ 1 :=
      ((Nat.card_congr e.toEquiv).symm.trans
        (C2Six.natCard_pCore_quotient_of_isAltType_three (hLb i).2)).trans (pow_one 3).symm
    exact IsPGroup.of_card hcard
  have hBsub : ∀ i, (imageOTwoQuot G₀ (Lb i)).IsSubnormal := fun i =>
    (hLb' i).2.2.map (QuotientGroup.mk'_surjective _)
  have hBQ : ∀ i, imageOTwoQuot G₀ (Lb i) ≤ pCoreOf 3 (⊤ : Subgroup (OTwoQuot G₀)) := by
    intro i
    have hsub : IsSubnormal (imageOTwoQuot G₀ (Lb i)) ⊤ := A3.subnormal_top_iff.mpr (hBsub i)
    have h1 : imageOTwoQuot G₀ (Lb i) ≤ pCoreOf 3 (imageOTwoQuot G₀ (Lb i)) :=
      le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer (hB3 i)
    exact h1.trans (A4.pCoreOf_le_of_subnormal 3 hsub)
  have hQn : (pCoreOf 3 (⊤ : Subgroup (OTwoQuot G₀))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 3 ⊤))
  have hK3 : ∀ u ∈ imageOTwoQuot G₀ F₁, ¬ 3 ∣ orderOf u := by
    intro u hu
    obtain ⟨x, hx, hxF, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact h3 x hx hxF
  have hcomm : ∀ i, ∀ x ∈ imageOTwoQuot G₀ F₁, ∀ y ∈ imageOTwoQuot G₀ (Lb i), Commute x y := by
    intro i x hx y hy
    have hyQ := hBQ i hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ imageOTwoQuot G₀ F₁ := by
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact (imageOTwoQuot G₀ F₁).mul_mem hx (hKn.conj_mem _ ((imageOTwoQuot G₀ F₁).inv_mem hx) y)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 3 (⊤ : Subgroup (OTwoQuot G₀)) :=
      (pCoreOf 3 ⊤).mul_mem (hQn.conj_mem y hyQ x) ((pCoreOf 3 ⊤).inv_mem hyQ)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 3 (⊤ : Subgroup (OTwoQuot G₀))) ⟨_, h2⟩
    have hk' : (x * y * x⁻¹ * y⁻¹) ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hcop : Nat.Coprime (orderOf (x * y * x⁻¹ * y⁻¹)) (3 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hK3 _ h1)).symm
    have hord : orderOf (x * y * x⁻¹ * y⁻¹) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk')
    have h3' := orderOf_eq_one_iff.mp hord
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h3')
  have hx : ∀ x ∈ imageOTwoQuot G₀ F₁, ∃ m ∈ imageOTwoQuot G₀ M₁,
      ∃ b : Fin r → OTwoQuot G₀, (∀ i, b i ∈ imageOTwoQuot G₀ (Lb i)) ∧
        x = m * (List.ofFn b).prod := by
    intro x hx
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    obtain ⟨m, hm, xs, hxs, hlm⟩ := hprod l (hF₁ hlL)
    have hmG : m ∈ G₀ := C2Six.oTwoFIn_le hm.2
    have hxsY : ∀ i, xs i ∈ G₀ := fun i => (hLb' i).2.1 (hxs i)
    refine ⟨QuotientGroup.mk ⟨m, hmG⟩, mem_imageOTwoQuot_iff.mpr ⟨m, hmG, hm.1, rfl⟩,
      fun i => QuotientGroup.mk ⟨xs i, hxsY i⟩,
      fun i => mem_imageOTwoQuot_iff.mpr ⟨xs i, hxsY i, hxs i, rfl⟩, ?_⟩
    have h1 : (⟨l, hl⟩ : ↥G₀) =
        ⟨m, hmG⟩ * (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥G₀)).prod := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubmonoidClass.coe_list_prod, List.map_ofFn]
      exact hlm
    rw [h1, QuotientGroup.mk_mul]
    congr 1
    have := map_list_prod (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥G₀))
      (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥G₀))
    rw [List.map_ofFn] at this
    exact this
  have hle := le_of_forall_eq_mul_prod_of_threePrime hK3
    (pCoreOf_isPGroup 3 (⊤ : Subgroup (OTwoQuot G₀)))
    (fun i => imageOTwoQuot G₀ (Lb i)) hBQ hcomm hx
  intro l hl
  have hlG : l ∈ G₀ := C2Six.oTwoFIn_le (hF₁ hl)
  exact mem_of_mk_mem_imageOTwoQuot hOM
    (hle (mem_imageOTwoQuot_iff.mpr ⟨l, hlG, hl, rfl⟩) : (QuotientGroup.mk ⟨l, hlG⟩ : OTwoQuot G₀) ∈
      imageOTwoQuot G₀ M₁)


theorem Y_le_of_centralizes {G₀ F₁ Y : Subgroup G} (hY5 : (pCoreOf 2 Y).relIndex Y = 5)
    (hYo : Y = oTwoUpper Y) (hYG : Y ≤ G₀)
    (hF₁N : G₀ ≤ Subgroup.normalizer (F₁ : Set G)) (hFY : F₁ ≤ Subgroup.normalizer (Y : Set G))
    (hO2 : ∀ x ∈ F₁, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ pCoreOf 2 G₀)
    (hC : ∀ y ∈ Y, (∀ f ∈ F₁, y * f * y⁻¹ * f⁻¹ ∈ pCoreOf 2 G₀) → y ∈ F₁) : Y ≤ F₁ := by
  set P := pCoreOf 2 Y with hP
  set Z := (Y ⊓ F₁) ⊔ P with hZ
  have hZY : Z ≤ Y := sup_le inf_le_left (pCoreOf_le 2 Y)
  have hPZ : P ≤ Z := le_sup_right
  have hmul : P.relIndex Z * Z.relIndex Y = P.relIndex Y :=
    Subgroup.relIndex_mul_relIndex P Z Y hPZ hZY
  rw [hY5] at hmul
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (Dvd.intro_left _ hmul) with h1 | h5
  · have hYZ : Y ≤ Z := Subgroup.relIndex_eq_one.mp h1
    have hPN : P ≤ Subgroup.normalizer ((Y ⊓ F₁ : Subgroup G) : Set G) := fun p hp =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (pCoreOf_le 2 Y hp),
        hF₁N (hYG (pCoreOf_le 2 Y hp))⟩
    have hle : oTwoUpper Y ≤ Y ⊓ F₁ := by
      refine oTwoUpper_le_of_pow_mem fun x hx => ?_
      obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hPN).1 (hYZ hx)
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨p, hp⟩
      have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hPN hp) (2 ^ k)
      exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩
    rw [← hYo] at hle
    exact fun x hx => (hle hx).2
  · have h1 : P.relIndex Z = 1 := by
      rw [h5] at hmul
      omega
    have hYF : Y ⊓ F₁ ≤ P := le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)
    intro y hy
    refine hC y hy fun f hf => ?_
    have hfN : f ∈ Subgroup.normalizer (Y : Set G) := hFY hf
    have hc1 : y * f * y⁻¹ * f⁻¹ ∈ Y := by
      have : y * f * y⁻¹ * f⁻¹ = y * (f * y⁻¹ * f⁻¹) := by group
      rw [this]
      exact Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp hfN y⁻¹).mp (Y.inv_mem hy))
    have hc2 : y * f * y⁻¹ * f⁻¹ ∈ F₁ :=
      F₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hF₁N (hYG hy)) f).mp hf) (F₁.inv_mem hf)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hYF ⟨hc1, hc2⟩⟩
    exact hO2 _ hc2 k (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem mem_preimageModTwoCore {H : Subgroup G} {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} {x : G} :
    x ∈ preimageModTwoCore H P ↔
      ∃ hx : x ∈ H, (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ P := by
  unfold preimageModTwoCore
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

omit [Finite G] in
theorem preimageModTwoCore_le {H : Subgroup G} {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} :
    preimageModTwoCore H P ≤ H := Subgroup.map_subtype_le _

omit [Finite G] in
theorem normal_preimageModTwoCore {H : Subgroup G} {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} [P.Normal] :
    ((preimageModTwoCore H P).subgroupOf H).Normal := by
  have : (preimageModTwoCore H P).subgroupOf H =
      P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    unfold preimageModTwoCore Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [this]
  exact Subgroup.Normal.comap inferInstance _

omit [Finite G] in
theorem preimageModTwoCore_mono {H : Subgroup G} {P P' : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (h : P ≤ P') : preimageModTwoCore H P ≤ preimageModTwoCore H P' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite G] in
theorem orderOf_mk_open_eq {H : Subgroup G} (g : ↥H) :
    orderOf (QuotientGroup.mk g : OTwoQuot H) =
      orderOf (QuotientGroup.mk g : ↥H ⧸ CFSG.pCore 2 ↥H) := by
  let e : (↥H ⧸ CFSG.pCore 2 ↥H) ≃* OTwoQuot H :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥H 2)
  exact MulEquiv.orderOf_eq e (QuotientGroup.mk g)


omit [Finite G] in
theorem mem_modO2Image_iff {H X : Subgroup G} {u : ↥H ⧸ CFSG.pCore 2 ↥H} :
    u ∈ modO2Image H X ↔
      ∃ (x : G) (hx : x ∈ H), x ∈ X ∧
        (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = u := by
  unfold modO2Image
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩

omit [Finite G] in
theorem mk_eq_one_iff_mem_pCoreOf' {H : Subgroup G} (x : ↥H) :
    (QuotientGroup.mk x : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.eq_one_iff]
  exact C2Six.mem_pCore_two_iff

omit [Finite G] in
theorem mk_commute_iff' {H : Subgroup G} (a b : ↥H) :
    (QuotientGroup.mk a : ↥H ⧸ CFSG.pCore 2 ↥H) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a ↔
      ((a * b * a⁻¹ * b⁻¹ : ↥H) : G) ∈ pCoreOf 2 H := by
  rw [← mk_eq_one_iff_mem_pCoreOf']
  have e : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : ↥H ⧸ CFSG.pCore 2 ↥H) =
      ⁅(QuotientGroup.mk a : ↥H ⧸ CFSG.pCore 2 ↥H), (QuotientGroup.mk b : ↥H ⧸ CFSG.pCore 2 ↥H)⁆ := by
    simp [commutatorElement_def]
  rw [e]
  exact commutatorElement_eq_one_iff_mul_comm.symm

theorem not_two_dvd_card_of_forall_odd {Γ : Type*} [Group Γ] [Finite Γ] (H : Subgroup Γ)
    (h : ∀ x ∈ H, Odd (orderOf x)) : ¬ 2 ∣ Nat.card H := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := h x x.2
  rw [Subgroup.orderOf_coe, hx] at this
  exact absurd this (by decide)

@[expose] def fMap (H L : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  (CFSG.fittingSubgroup ↥(modO2Image H L)).map (modO2Image H L).subtype

omit [Finite G] in
theorem normal_modO2Image {H L : Subgroup G} (hLn : (L.subgroupOf H).Normal) :
    (modO2Image H L).Normal := hLn.map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem normal_fMap {H L : Subgroup G} (hLn : (L.subgroupOf H).Normal) : (fMap H L).Normal := by
  have := normal_modO2Image hLn
  unfold fMap
  infer_instance

theorem fMap_le_fitting {H L : Subgroup G} (hLn : (L.subgroupOf H).Normal) :
    fMap H L ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := by
  have hn := normal_fMap hLn
  refine le_sSup ⟨hn, ?_⟩
  let e : ↥(CFSG.fittingSubgroup ↥(modO2Image H L)) ≃* ↥(fMap H L) :=
    Subgroup.equivMapOfInjective _ _ (modO2Image H L).subtype_injective
  exact Group.nilpotent_of_mulEquiv e

omit [Finite G] in
theorem mem_fMap_iff {H L : Subgroup G} {u : ↥H ⧸ CFSG.pCore 2 ↥H} :
    u ∈ fMap H L ↔ ∃ h : u ∈ modO2Image H L,
      (⟨u, h⟩ : ↥(modO2Image H L)) ∈ CFSG.fittingSubgroup ↥(modO2Image H L) := by
  unfold fMap
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f.2, hf⟩
  · rintro ⟨h, hf⟩
    exact ⟨⟨u, h⟩, hf, rfl⟩

omit [Finite G] in
theorem orderOf_dvd_of_mem_fMap {H L : Subgroup G} {u : ↥H ⧸ CFSG.pCore 2 ↥H} (hu : u ∈ fMap H L) :
    orderOf u ∣ Nat.card (CFSG.fittingSubgroup ↥(modO2Image H L)) := by
  obtain ⟨h, hf⟩ := mem_fMap_iff.mp hu
  have := Subgroup.orderOf_dvd_natCard _ hf
  rwa [Subgroup.orderOf_mk] at this

omit [Finite G] in
theorem odd_orderOf_of_mem_fMap {H L : Subgroup G}
    (hodd : ∀ x ∈ CFSG.fittingSubgroup ↥(modO2Image H L), Odd (orderOf x))
    {u : ↥H ⧸ CFSG.pCore 2 ↥H} (hu : u ∈ fMap H L) : Odd (orderOf u) := by
  obtain ⟨h, hf⟩ := mem_fMap_iff.mp hu
  have := hodd _ hf
  rwa [Subgroup.orderOf_mk] at this

omit [Finite G] in
theorem mem_pCoreOf_of_pow_eq_one {H L : Subgroup G}
    (hodd : ∀ x ∈ CFSG.fittingSubgroup ↥(modO2Image H L), Odd (orderOf x))
    {x : G} (hxF : x ∈ preimageModTwoCore H (fMap H L)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ pCoreOf 2 H := by
  obtain ⟨hxG, hmem⟩ := mem_preimageModTwoCore.mp hxF
  have hodd' := odd_orderOf_of_mem_fMap hodd hmem
  have hk' : (QuotientGroup.mk (⟨x, hxG⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxG⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have hcop : Nat.Coprime
      (orderOf (QuotientGroup.mk (⟨x, hxG⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd')
  have h1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk')
  exact (mk_eq_one_iff_mem_pCoreOf' ⟨x, hxG⟩).mp (orderOf_eq_one_iff.mp h1)

theorem mem_preimage_fMap_of_centralizes {H L Y : Subgroup G}
    (hgf : CFSG.generalizedFitting ↥(modO2Image H L) = CFSG.fittingSubgroup ↥(modO2Image H L))
    (hYL : Y ≤ L) (hYH : Y ≤ H) {y : G} (hy : y ∈ Y)
    (hcomm : ∀ f ∈ preimageModTwoCore H (fMap H L), y * f * y⁻¹ * f⁻¹ ∈ pCoreOf 2 H) :
    y ∈ preimageModTwoCore H (fMap H L) := by
  have hyH : y ∈ H := hYH hy
  have hyL : (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ modO2Image H L :=
    mem_modO2Image_iff.mpr ⟨y, hyH, hYL hy, rfl⟩
  have hcent : (⟨_, hyL⟩ : ↥(modO2Image H L)) ∈
      Subgroup.centralizer (CFSG.generalizedFitting ↥(modO2Image H L) : Set ↥(modO2Image H L)) := by
    rw [hgf, Subgroup.mem_centralizer_iff]
    intro f hf
    have hfm : f.1 ∈ fMap H L := mem_fMap_iff.mpr ⟨f.2, hf⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective f.1
    have hgF : (g : G) ∈ preimageModTwoCore H (fMap H L) :=
      mem_preimageModTwoCore.mpr ⟨g.2, by simpa [hg] using hfm⟩
    have h1 := (mk_commute_iff' ⟨y, hyH⟩ g).mpr (hcomm g hgF)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hg]
    exact h1.symm
  have hmem := CFSG.centralizer_generalizedFitting_le _ hcent
  rw [hgf] at hmem
  exact mem_preimageModTwoCore.mpr ⟨hyH, mem_fMap_iff.mpr ⟨hyL, hmem⟩⟩

omit [Finite G] in
theorem exists_modO2_surjection_of_le' {H L : Subgroup G} (hLH : L ≤ H) :
    ∃ ψ : ↥L →* ↥(modO2Image H L), Function.Surjective ψ ∧ IsPGroup 2 ψ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  let φ : ↥L →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH)
  have hrange : φ.range = modO2Image H L := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkp : IsPGroup 2 φ.ker := by
    intro x
    have hx : Subgroup.inclusion hLH (x : ↥L) ∈ CFSG.pCore 2 ↥H := by
      have := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
      exact this
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (Subgroup.inclusion hLH (x : ↥L)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (Subgroup.inclusion_injective hLH) (by simpa using h1)
  refine ⟨((MulEquiv.subgroupCongr hrange).toMonoidHom).comp φ.rangeRestrict, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hrange).surjective.comp φ.rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hrange).injective,
      MonoidHom.ker_rangeRestrict]
    exact hkp

theorem card_modO2Image_eq_five {H Y : Subgroup G} (hYH : Y ≤ H)
    (hY5 : (pCoreOf 2 Y).relIndex Y = 5) (hodd : ¬ 2 ∣ Nat.card (modO2Image H Y)) :
    Nat.card (modO2Image H Y) = 5 := by
  obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection_of_le' hYH
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top] at h1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hker
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 Y) (K := Y)
  rw [hY5, inf_eq_left.mpr (pCoreOf_le 2 _)] at hmul
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 Y)
  rw [ha] at hmul
  rw [hb, ← hmul] at h1
  have hm : Odd (Nat.card (modO2Image H Y)) := Nat.odd_iff.mpr (by omega)
  have hd1 : Nat.card (modO2Image H Y) ∣ 5 := by
    have : Nat.card (modO2Image H Y) ∣ 5 * 2 ^ a := Dvd.intro_left _ h1
    exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)).dvd_of_dvd_mul_right this
  have hd2 : 5 ∣ Nat.card (modO2Image H Y) := by
    have : 5 ∣ 2 ^ b * Nat.card (modO2Image H Y) := h1 ▸ Dvd.intro _ rfl
    exact (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 5 2)).dvd_of_dvd_mul_left this
  exact Nat.dvd_antisymm hd1 hd2

omit [Finite G] in
theorem mk_mem_normalizer_modO2Image {H Y : Subgroup G} {x : G} (hx : x ∈ H)
    (hn : x ∈ Subgroup.normalizer (Y : Set G)) :
    (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
      Subgroup.normalizer (modO2Image H Y : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have h1 : (⟨x, hx⟩ : ↥H) ∈ Subgroup.normalizer ((Y.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    Subgroup.le_normalizer_comap H.subtype hn
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨_, h1, rfl⟩

theorem isSylowTwoOf_modO2Image_inf {H S L : Subgroup G} (hS : IsSylowTwoOf S H)
    (hLn : (L.subgroupOf H).Normal) :
    IsSylowTwoOf (modO2Image H S ⊓ modO2Image H L) (modO2Image H L) := by
  have := normal_modO2Image hLn
  exact A4.isSylowTwoOf_inf_normal
    (isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _))
    le_top (Subgroup.le_normalizer_of_normal)

end CFSG.Quasithin.He16
