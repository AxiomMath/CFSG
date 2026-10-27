module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowB42
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowD5
public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.InternalSecBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Helpers

variable {V : Type} [CommGroup V]

theorem le_stabSub_bot (X : Subgroup (MulAut V)) : X ≤ stabSub (⊥ : Subgroup V) := by
  intro g _ u
  simp [Subgroup.mem_bot]

theorem commV_le_of_le_centSec {K : Subgroup (MulAut V)} {Y : Subgroup V}
    (h : K ≤ centSec ⊤ Y) : commV K ≤ Y := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨k, hk, v, rfl⟩
  exact (h hk).2 v trivial

theorem not_le_centSec_bot {K : Subgroup (MulAut V)} {U : Subgroup V} (hU : U ≠ ⊥)
    (hfix : U ⊓ fixV K = ⊥) : ¬ K ≤ centSec U ⊥ := by
  intro h
  apply hU
  rw [eq_bot_iff]
  intro u hu
  have hu' : u ∈ U ⊓ fixV K := ⟨hu, fun k hk => by
    have h1 := (h hk).2 u hu
    rw [Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.mp h1⟩
  rw [hfix] at hu'
  exact hu'

theorem fixV_autSec_bot {K : Subgroup (MulAut V)} {U : Subgroup V} (hKU : K ≤ stabSub U)
    (hfix : U ⊓ fixV K = ⊥) : fixV (autSec K U ⊥) = ⊥ := by
  have hKs : K ≤ stabSub U ⊓ stabSub ⊥ := le_inf hKU (le_stabSub_bot K)
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : (w : V) ∈ U ⊓ fixV K := ⟨w.2, fun k hk => by
    have h1 := hq _ (Bridge.secHom_mem_autSec hKs (g := ⟨k, hKs hk⟩) hk)
    rw [Bridge.secHom_apply] at h1
    have h2 := (mk_eq_mk_iff (U := (⊥ : Subgroup V).subgroupOf U) _ _).1 h1
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h2
    have h3 : k (w : V) * (w : V)⁻¹ = 1 := by simpa using h2
    exact mul_inv_eq_one.mp h3⟩
  rw [hfix, Subgroup.mem_bot] at hw
  rw [Subgroup.mem_bot]
  have hw1 : w = 1 := Subtype.ext hw
  rw [hw1]
  rfl

theorem card_sec_bot [Finite V] (U : Subgroup V) : Nat.card (Sec U ⊥) = Nat.card U := by
  have h := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ U)
  rwa [Subgroup.card_bot, mul_one] at h

theorem card_mul_card_fixV_le_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card V ↔ rk A ≤ rkIdx (fixV A) := by
  have h1 : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.isPGroup
  have h2 : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV _
  have h3 : Nat.card V = 2 ^ rk V :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have h4 := rk_add_rkIdx (fixV A)
  rw [h1, h2, h3, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  omega

theorem card_le_card_mul_card_fixV_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    Nat.card V ≤ Nat.card A * Nat.card (fixV A) ↔ rkIdx (fixV A) ≤ rk A := by
  have h1 : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.isPGroup
  have h2 : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV _
  have h3 : Nat.card V = 2 ^ rk V :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have h4 := rk_add_rkIdx (fixV A)
  rw [h1, h2, h3, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  omega

theorem card_of_binaryNaturalSL [Finite V] {H : Subgroup (MulAut V)} {d a : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ d a) : Nat.card V = (2 ^ a) ^ d := by
  obtain ⟨F, _, _, hF, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  rw [← Subgroup.card_top (G := V), Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  have h1 : Nat.card (↥(FFModel.nat (StatedSL d F)).sec ⧸
      (FFModel.nat (StatedSL d F)).ker.subgroupOf (FFModel.nat (StatedSL d F)).sec) =
      Nat.card (Fin d → F) := by
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin d → F))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin d → F))).subgroupOf ⊤) = _
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top]
    rfl
  rw [h1, Nat.card_fun, Nat.card_fin, hF]

end Helpers

structure LowData (V : Type) [CommGroup V] [Finite V] (X K A : Subgroup (MulAut V))
    (I : Subgroup V) (n : ℕ) : Prop where
  set : L2Set V X K n
  fix : fixV K = ⊥
  isA2 : IsA2 X A
  r : rkIdx (fixV A) ≤ 2 * rk A
  stabI : X ≤ stabSub I
  irr : ∀ J : Subgroup V, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → ⊥ ≤ J → J ≤ I → J = ⊥ ∨ J = I
  ne : I ≠ ⊥
  le : I ≤ commV K
  lt : I ≠ commV K

namespace LowData

variable {V : Type} [CommGroup V] [Finite V] {X K A : Subgroup (MulAut V)} {I : Subgroup V}
  {n : ℕ}

theorem fixV_autSec_top_eq_bot (h : L2Set V X K n) {V₁ : Subgroup V}
    (hXV₁ : X ≤ stabSub V₁) (hf : X ⊓ centSec ⊤ V₁ = ⊥)
    (hmax : ∀ Y : Subgroup V, X ≤ stabSub Y → V₁ ≤ Y → Y ≠ V₁ → commV K ≤ Y) :
    fixV (autSec K ⊤ V₁) = ⊥ := by
  have hQ := h.sec (InternalSec.le_stabSub_top X) hXV₁ hf
  have hXs : X ≤ stabSub ⊤ ⊓ stabSub V₁ := le_inf (InternalSec.le_stabSub_top X) hXV₁
  have hKs : K ≤ stabSub ⊤ ⊓ stabSub V₁ := h.le.trans hXs
  by_contra hne
  set F := fixV (autSec K ⊤ V₁) with hF
  set Y : Subgroup V :=
    (F.comap (QuotientGroup.mk' (V₁.subgroupOf ⊤))).map (⊤ : Subgroup V).subtype with hY
  have hmemY : ∀ v : V, v ∈ Y ↔
      (QuotientGroup.mk (⟨v, trivial⟩ : ↥(⊤ : Subgroup V)) : Sec ⊤ V₁) ∈ F := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, trivial⟩, hv, rfl⟩
  have hFinv : ∀ y ∈ autSec X ⊤ V₁, ∀ q ∈ F, y q ∈ F := by
    intro y hy q hq k hk
    have hk' : y⁻¹ * k * y ∈ autSec K ⊤ V₁ := by
      simpa using hQ.normal y⁻¹ ((autSec X ⊤ V₁).inv_mem hy) k hk
    have := hq _ hk'
    calc k (y q) = y ((y⁻¹ * k * y) q) := by simp [MulAut.mul_apply]
      _ = y q := by rw [this]
  have hfwd : ∀ x ∈ X, ∀ v ∈ Y, x v ∈ Y := by
    intro x hx v hv
    rw [hmemY] at hv ⊢
    have h1 := hFinv _ (Bridge.secHom_mem_autSec hXs (g := ⟨x, hXs hx⟩) hx) _ hv
    rw [Bridge.secHom_apply] at h1
    exact h1
  have hXY : X ≤ stabSub Y := fun x hx v =>
    ⟨fun hxv => by simpa using hfwd x⁻¹ (X.inv_mem hx) _ hxv, hfwd x hx v⟩
  have hV₁Y : V₁ ≤ Y := by
    intro v hv
    rw [hmemY]
    have : (QuotientGroup.mk (⟨v, trivial⟩ : ↥(⊤ : Subgroup V)) : Sec ⊤ V₁) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hv
    rw [this]
    exact F.one_mem
  have hYne : Y ≠ V₁ := by
    intro hYV
    apply hne
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hw : (w : V) ∈ Y := (hmemY w).2 hq
    rw [hYV] at hw
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hw
  have hUY := hmax Y hXY hV₁Y hYne
  have hcF : commV (autSec K ⊤ V₁) ≤ F := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨y, hy, q, rfl⟩
    obtain ⟨g, hgK, rfl⟩ := (Bridge.mem_autSec_iff_secHom hKs).1 hy
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Bridge.secHom_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hc : (g : MulAut V) (w : V) * (w : V)⁻¹ ∈ Y :=
      hUY (Subgroup.subset_closure ⟨g, hgK, w, rfl⟩)
    exact (hmemY _).1 hc
  have hperf : ⁅autSec K ⊤ V₁, autSec K ⊤ V₁⁆ = autSec K ⊤ V₁ := by
    have : Group.IsPerfect ↥(autSec K ⊤ V₁) := hQ.quasi.1
    exact Subgroup.commutator_eq_self
  have h1 : commSub (commV (autSec K ⊤ V₁)) (autSec K ⊤ V₁) = ⊥ :=
    commSub_eq_bot_iff.2 hcF
  rw [B5.commSub_commV_eq hperf] at h1
  obtain ⟨a, b, hab⟩ := hQ.exists_noncomm
  apply hab
  have htriv : ∀ y ∈ autSec K ⊤ V₁, y = 1 := by
    intro y hy
    ext q
    have h2 : y q * q⁻¹ ∈ commV (autSec K ⊤ V₁) := Subgroup.subset_closure ⟨y, hy, q, rfl⟩
    rw [h1, Subgroup.mem_bot] at h2
    simpa using mul_inv_eq_one.mp h2
  have ha : a = 1 := Subtype.ext (htriv a a.2)
  rw [ha, one_mul, mul_one]

theorem commV_eq_top_of_intDirect {W : Type} [CommGroup W] {X' K' : Subgroup (MulAut W)}
    (hKX : K' ≤ X') (hfix : fixV K' = ⊥) (hD : IsIntDirect (commV K') (fixV X') ⊤) :
    commV K' = ⊤ := by
  have h1 : fixV X' = ⊥ := le_bot_iff.mp (hfix ▸ B1.fixV_le_fixV hKX)
  have h2 := hD.1
  rwa [h1, sup_bot_eq] at h2

theorem isSylowTwoOf_of_autSec {W Y : Subgroup V} (hXW : X ≤ stabSub W)
    (hXY : X ≤ stabSub Y) (hf : X ⊓ centSec W Y = ⊥) (hKX : K ≤ X) (hAX : A ≤ X)
    (hA2 : IsElemAbelian2 A) (h : IsSylowTwoOf (autSec A W Y) (autSec K W Y)) :
    IsSylowTwoOf A K := by
  have hAK : A ≤ K := B5.le_of_autSec_le hXW hXY hf hKX hAX h.1
  have hfA : A ⊓ centSec W Y = ⊥ := le_bot_iff.mp (hf ▸ inf_le_inf_right _ hAX)
  have hfK : K ⊓ centSec W Y = ⊥ := le_bot_iff.mp (hf ▸ inf_le_inf_right _ hKX)
  have eA := B5.secEquiv A (hAX.trans hXW) (hAX.trans hXY) hfA
  have eK := B5.secEquiv K (hKX.trans hXW) (hKX.trans hXY) hfK
  refine ⟨hAK, hA2.isPGroup, ?_⟩
  have h1 := Subgroup.index_mul_card (A.subgroupOf K)
  have h2 := Subgroup.index_mul_card ((autSec A W Y).subgroupOf (autSec K W Y))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv, ← Nat.card_congr eA.toEquiv,
    ← Nat.card_congr eK.toEquiv] at h2
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h3 : (A.subgroupOf K).index = ((autSec A W Y).subgroupOf (autSec K W Y)).index :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  rw [h3]
  exact h.2.2

theorem nat_or_s5 (hF : L2FFModuleFact) (h42 : AsB42) (d : LowData V X K A I n) :
    (BinaryNaturalSL K I ⊥ 2 n ∧ BinaryNaturalSL K ⊤ I 2 n ∧ IsSylowTwoOf A K) ∨
      (n = 2 ∧ Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧ SymmetricNatural X I ⊥ 5 ∧
        SymmetricNatural X ⊤ I 5 ∧ ¬ A ≤ K ∧
        Nat.card A * Nat.card ↥(I ⊓ fixV A) ≤ Nat.card I) := by
  have h := d.set
  have hV := h.sq
  obtain ⟨hAX, hA1, hA2⟩ := d.isA2
  set S : Set (Subgroup V) := {Y | X ≤ stabSub Y ∧ I ≤ Y ∧ ¬ commV K ≤ Y} with hS
  have hIS : I ∈ S := ⟨d.stabI, le_rfl, fun hle => d.lt (le_antisymm d.le hle)⟩
  obtain ⟨V₁, ⟨hXV₁, hIV₁, hUV₁⟩, hV₁max⟩ :=
    Set.exists_max_image S (fun Y => Nat.card Y) S.toFinite ⟨I, hIS⟩
  have hmax : ∀ Y : Subgroup V, X ≤ stabSub Y → V₁ ≤ Y → Y ≠ V₁ → commV K ≤ Y := by
    intro Y hXY hV₁Y hne
    by_contra hUY
    exact hne (Subgroup.eq_of_le_of_card_ge hV₁Y (hV₁max Y ⟨hXY, hIV₁.trans hV₁Y, hUY⟩)).symm
  have hXtop : X ≤ stabSub (⊤ : Subgroup V) := InternalSec.le_stabSub_top X
  have hXbot : X ≤ stabSub (⊥ : Subgroup V) := le_stabSub_bot X
  have hfQ : X ⊓ centSec ⊤ V₁ = ⊥ :=
    h.inf_centSec_eq_bot hXtop hXV₁ fun hle => hUV₁ (commV_le_of_le_centSec hle)
  have hfixI : I ⊓ fixV K = ⊥ := by rw [d.fix, inf_bot_eq]
  have hfixV₁ : V₁ ⊓ fixV K = ⊥ := by rw [d.fix, inf_bot_eq]
  have hV₁ne : V₁ ≠ ⊥ := fun h0 => d.ne (le_bot_iff.mp (h0 ▸ hIV₁))
  have hfI : X ⊓ centSec I ⊥ = ⊥ :=
    h.inf_centSec_eq_bot d.stabI hXbot (not_le_centSec_bot d.ne hfixI)
  have hf₁ : X ⊓ centSec V₁ ⊥ = ⊥ :=
    h.inf_centSec_eq_bot hXV₁ hXbot (not_le_centSec_bot hV₁ne hfixV₁)
  have hQ := h.sec hXtop hXV₁ hfQ
  have hSI := h.sec d.stabI hXbot hfI
  have hS₁ := h.sec hXV₁ hXbot hf₁
  have hfixQ : fixV (autSec K ⊤ V₁) = ⊥ := fixV_autSec_top_eq_bot h hXV₁ hfQ hmax
  have hfixSI : fixV (autSec K I ⊥) = ⊥ := fixV_autSec_bot (h.le.trans d.stabI) hfixI
  have hfixS₁ : fixV (autSec K V₁ ⊥) = ⊥ := fixV_autSec_bot (h.le.trans hXV₁) hfixV₁
  have hAU : ∀ {U Y : Subgroup V}, X ≤ stabSub U → X ≤ stabSub Y → X ⊓ centSec U Y = ⊥ →
      autSec A U Y ≤ autSec X U Y ∧ autSec A U Y ≠ ⊥ ∧ IsElemAbelian2 (autSec A U Y) ∧
        rk (autSec A U Y) = rk A := by
    intro U Y hXU hXY hf
    have hAs : A ≤ stabSub U ⊓ stabSub Y := le_inf (hAX.trans hXU) (hAX.trans hXY)
    have hfA : A ⊓ centSec U Y = ⊥ := le_bot_iff.mp (hf ▸ inf_le_inf_right _ hAX)
    refine ⟨autSec_mono hAX U Y, Bridge.autSec_ne_bot hAs fun hle => hA1 ?_,
      Bridge.isElemAbelian2_autSec hA2 hAs,
      B5.rk_autSec_eq (hAX.trans hXU) (hAX.trans hXY) hfA⟩
    exact le_bot_iff.mp (hfA ▸ le_inf le_rfl hle)
  obtain ⟨hAIX, hAI1, hAI2, hrkI⟩ := hAU d.stabI hXbot hfI
  obtain ⟨hAQX, hAQ1, hAQ2, hrkQ⟩ := hAU hXtop hXV₁ hfQ
  obtain ⟨hA1X, hA11, hA12, hrk₁⟩ := hAU hXV₁ hXbot hf₁
  have e1 := B5.rk_mu_section hV (le_top : V₁ ≤ ⊤) (hAX.trans hXtop)
  rw [top_inf_eq, rk_top] at e1
  have e1' := rk_add_rkIdx (fixV A)
  have e2 := B5.rk_mu_section hV hIV₁ (hAX.trans hXV₁)
  have e3 := B5.rk_mu_section hV (bot_le : (⊥ : Subgroup V) ≤ I) (hAX.trans d.stabI)
  have e4 := B5.rk_mu_section hV (bot_le : (⊥ : Subgroup V) ≤ V₁) (hAX.trans hXV₁)
  have hrkbot : rk (⊥ : Subgroup V) = 0 := rk_bot
  have hr := d.r
  have hirrI : XMod.IsIrrSec ↥(autSec K I ⊥) (⊥ : Subgroup (Sec I ⊥)) ⊤ :=
    B5.isIrrSec_autSec (bot_lt_iff_ne_bot.mpr d.ne) (fun J hJ hJ0 hJI => d.irr J hJ hJ0 hJI)
      (h.le.trans d.stabI) (h.le.trans hXbot)
  have hrI : rk A ≤ rkIdx (fixV (autSec A I ⊥)) := by
    have := hSI.card_mul_card_fixV_le h42 hirrI hAIX hAI1 hAI2
    rwa [card_mul_card_fixV_le_iff (Bridge.sec_sq_eq_one hV I ⊥) hAI2, hrkI] at this
  have hμQ : rkIdx (fixV (autSec A ⊤ V₁)) ≤ rk (autSec A ⊤ V₁) := by
    rw [hrkQ]
    omega
  have hFFQ : IsFFModule (autSec X ⊤ V₁) := ⟨autSec A ⊤ V₁, hAQX, hAQ1, hAQ2,
    (card_le_card_mul_card_fixV_iff (Bridge.sec_sq_eq_one hV ⊤ V₁) hAQ2).2 hμQ⟩
  have hQtype := hQ.ff hF hFFQ
  rw [hfixQ] at hQtype
  have hc60 : ∀ {W : Type} [CommGroup W] [Finite W] {X' K' : Subgroup (MulAut W)},
      L2Set W X' K' n → n = 2 → Nat.card K' = 60 := by
    intro W _ _ X' K' hS hn2
    rw [hS.card, hn2]
    norm_num
  have hcommQ : n = 2 → IsIntDirect (commV (autSec K ⊤ V₁)) (fixV (autSec X ⊤ V₁)) ⊤ →
      commV (autSec K ⊤ V₁) = ⊤ := fun _ hD => commV_eq_top_of_intDirect hQ.le hfixQ hD
  have hQirr : XMod.IsIrrSec ↥(autSec K ⊤ V₁) (⊥ : Subgroup (Sec ⊤ V₁)) ⊤ := by
    rcases hQtype with hnat | ⟨hn2, hD, -, hs5⟩
    · exact isIrrSec_of_binaryNaturalSL hnat
    · rw [hcommQ hn2 hD] at hs5
      exact isIrrSec_of_alternatingNatural_five
        (alternatingNatural_of_symmetricNatural_five hs5 hQ.le (hc60 hQ hn2))
  have hrQ : rk A ≤ rkIdx (fixV (autSec A ⊤ V₁)) := by
    have := hQ.card_mul_card_fixV_le h42 hQirr hAQX hAQ1 hAQ2
    rwa [card_mul_card_fixV_le_iff (Bridge.sec_sq_eq_one hV ⊤ V₁) hAQ2, hrkQ] at this
  have hFFI : IsFFModule (autSec X I ⊥) := ⟨_, hAIX, hAI1, hAI2,
    (card_le_card_mul_card_fixV_iff (Bridge.sec_sq_eq_one hV I ⊥) hAI2).2 (by rw [hrkI]; omega)⟩
  have hFF₁ : IsFFModule (autSec X V₁ ⊥) := ⟨_, hA1X, hA11, hA12,
    (card_le_card_mul_card_fixV_iff (Bridge.sec_sq_eq_one hV V₁ ⊥) hA12).2
      (by rw [hrk₁]; omega)⟩
  have hcard : ∀ {U : Subgroup V}, L2Set (Sec U ⊥) (autSec X U ⊥) (autSec K U ⊥) n →
      fixV (autSec K U ⊥) = ⊥ → IsFFModule (autSec X U ⊥) → Nat.card U = (2 ^ n) ^ 2 := by
    intro U hS hfx hFF
    rw [← card_sec_bot U]
    rcases hS.ff hF hFF with hnat | ⟨hn2, hD, -, hs5⟩
    · rw [hfx] at hnat
      exact card_of_binaryNaturalSL hnat
    · rw [commV_eq_top_of_intDirect hS.le hfx hD] at hs5
      rw [card_of_symmetricNatural_five hs5, hn2]
      norm_num
  have hIeq : I = V₁ := Subgroup.eq_of_le_of_card_ge hIV₁
    (by rw [hcard hS₁ hfixS₁ hFF₁, hcard hSI hfixSI hFFI])
  subst hIeq
  have hPI : IsFFStarOffender (autSec X I ⊥) (autSec A I ⊥) := by
    refine ⟨hAIX, hAI1, hAI2, fun B hB => ?_⟩
    have heq : Nat.card (Sec I ⊥) = Nat.card (autSec A I ⊥) * Nat.card (fixV (autSec A I ⊥)) :=
      le_antisymm ((card_le_card_mul_card_fixV_iff (Bridge.sec_sq_eq_one hV I ⊥) hAI2).2
        (by rw [hrkI]; omega)) (hSI.card_mul_card_fixV_le h42 hirrI hAIX hAI1 hAI2)
    rw [← heq]
    by_cases hB1 : B = ⊥
    · subst hB1
      rw [B1.card_bot_mul_card_fixV]
    · exact hSI.card_mul_card_fixV_le h42 hirrI (hB.trans hAIX) hB1
        ⟨fun a ha b hb => hAI2.1 a (hB ha) b (hB hb), fun a ha => hAI2.2 a (hB ha)⟩
  have hPQ : IsFFStarOffender (autSec X ⊤ I) (autSec A ⊤ I) := by
    refine ⟨hAQX, hAQ1, hAQ2, fun B hB => ?_⟩
    have heq : Nat.card (Sec ⊤ I) = Nat.card (autSec A ⊤ I) * Nat.card (fixV (autSec A ⊤ I)) :=
      le_antisymm ((card_le_card_mul_card_fixV_iff (Bridge.sec_sq_eq_one hV ⊤ I) hAQ2).2
        (by rw [hrkQ]; omega)) (hQ.card_mul_card_fixV_le h42 hQirr hAQX hAQ1 hAQ2)
    rw [← heq]
    by_cases hB1 : B = ⊥
    · subst hB1
      rw [B1.card_bot_mul_card_fixV]
    · exact hQ.card_mul_card_fixV_le h42 hQirr (hB.trans hAQX) hB1
        ⟨fun a ha b hb => hAQ2.1 a (hB ha) b (hB hb), fun a ha => hAQ2.2 a (hB ha)⟩
  have hAK_I : autSec A I ⊥ ≤ autSec K I ⊥ → A ≤ K :=
    B5.le_of_autSec_le d.stabI hXbot hfI h.le hAX
  have hAK_Q : autSec A ⊤ I ≤ autSec K ⊤ I → A ≤ K :=
    B5.le_of_autSec_le hXtop hXV₁ hfQ h.le hAX
  have hnotS5 : ∀ {U Y : Subgroup V} (hS : L2Set (Sec U Y) (autSec X U Y) (autSec K U Y) n),
      n = 2 → fixV (autSec K U Y) = ⊥ → commV (autSec K U Y) = ⊤ →
      SymmetricNatural (autSec X U Y) ⊤ ⊥ 5 → IsFFStarOffender (autSec X U Y) (autSec A U Y) →
      ¬ autSec A U Y ≤ autSec K U Y := by
    intro U Y hS hn2 hfx hcm hs5 hP hle
    have halt := alternatingNatural_of_symmetricNatural_five hs5 hS.le (hc60 hS hn2)
    have hD : IsIntDirect (commV (autSec K U Y)) (fixV (autSec K U Y)) ⊤ := by
      rw [hcm, hfx]
      exact ⟨sup_bot_eq ⊤, inf_bot_eq ⊤⟩
    rw [← hcm] at halt
    have hlt := card_mul_card_fixV_lt_of_altDn_five hD halt hle hP.2.1 hP.2.2.1
    have hge := hP.2.2.2 ⊥ bot_le
    rw [B1.card_bot_mul_card_fixV] at hge
    omega
  have hItype := hSI.ff hF hFFI
  rw [hfixSI] at hItype
  have hfK : ∀ {U Y : Subgroup V}, X ⊓ centSec U Y = ⊥ → K ⊓ centSec U Y = ⊥ :=
    fun hf => le_bot_iff.mp (hf ▸ inf_le_inf_right _ h.le)
  rcases hItype with hnatI | ⟨hn2, hDI, -, hs5I⟩ <;>
    rcases hQtype with hnatQ | ⟨hn2', hDQ, ⟨eQ⟩, hs5Q⟩
  ·
    left
    obtain ⟨F, _, _, hFc, πI, hπI⟩ := hnatI
    obtain ⟨F', _, _, hFc', πQ, hπQ⟩ := hnatQ
    refine ⟨⟨F, inferInstance, inferInstance, hFc, _,
      B5.realizesVia_of_autSec bot_le (h.le.trans d.stabI) (h.le.trans hXbot) (hfK hfI) hπI⟩,
      ⟨F', inferInstance, inferInstance, hFc', _,
      B5.realizesVia_of_autSec le_top (h.le.trans hXtop) (h.le.trans hXV₁) (hfK hfQ) hπQ⟩, ?_⟩
    exact isSylowTwoOf_of_autSec d.stabI hXbot hfI h.le hAX hA2
      (hSI.isSylowTwoOf_of_natural h42 ⟨F, inferInstance, inferInstance, hFc, πI, hπI⟩ hPI)
  ·
    exfalso
    have hAK := hAK_I (hSI.isSylowTwoOf_of_natural h42 hnatI hPI).1
    rw [hcommQ hn2' hDQ] at hs5Q
    exact hnotS5 hQ hn2' hfixQ (hcommQ hn2' hDQ) hs5Q hPQ (autSec_mono hAK ⊤ I)
  ·
    exfalso
    have hAK := hAK_Q (hQ.isSylowTwoOf_of_natural h42 hnatQ hPQ).1
    have hcm := commV_eq_top_of_intDirect hSI.le hfixSI hDI
    rw [hcm] at hs5I
    exact hnotS5 hSI hn2 hfixSI hcm hs5I hPI (autSec_mono hAK I ⊥)
  ·
    right
    have hcmI := commV_eq_top_of_intDirect hSI.le hfixSI hDI
    have hcmQ := hcommQ hn2' hDQ
    rw [hcmI] at hs5I
    rw [hcmQ] at hs5Q
    obtain ⟨πI, hπI⟩ := hs5I
    obtain ⟨πQ, hπQ⟩ := hs5Q
    refine ⟨hn2, ⟨(B5.secEquiv X hXtop hXV₁ hfQ).trans eQ⟩,
      ⟨_, B5.realizesVia_of_autSec bot_le d.stabI hXbot hfI hπI⟩,
      ⟨_, B5.realizesVia_of_autSec le_top hXtop hXV₁ hfQ hπQ⟩, fun hAK => ?_, ?_⟩
    · exact hnotS5 hSI hn2 hfixSI hcmI ⟨πI, hπI⟩ hPI (autSec_mono hAK I ⊥)
    ·
      have hfA : A ⊓ centSec I ⊥ = ⊥ := le_bot_iff.mp (hfI ▸ inf_le_inf_right _ hAX)
      have hcA : Nat.card (autSec A I ⊥) = Nat.card A :=
        (Nat.card_congr (B5.secEquiv A (hAX.trans d.stabI) (hAX.trans hXbot) hfA).toEquiv).symm
      have h1 := hSI.card_mul_card_fixV_le h42 hirrI hAIX hAI1 hAI2
      have h2 := card_inf_fixV_le_autSec (A := A) (bot_le : (⊥ : Subgroup V) ≤ I)
        (hAX.trans d.stabI)
      rw [bot_inf_eq, Subgroup.card_bot, mul_one] at h2
      rw [hcA, card_sec_bot] at h1
      calc Nat.card A * Nat.card ↥(I ⊓ fixV A) ≤
          Nat.card A * Nat.card (fixV (autSec A I ⊥)) := Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card I := h1

end LowData

end CFSG.Quasithin.H13
