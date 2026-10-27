module

public import CFSG.Quasithin.H13.A6S13826d
public import CFSG.Quasithin.H13.A6S13822c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem le_pCoreOf_of_triv (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ T)
    (hsimp : IsSimpleGroup ↥(S.KSt H K)) {X Y : Subgroup G} (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hQ : ∀ q ∈ pCoreOf 2 H, ∀ x ∈ X, q * x * q⁻¹ * x⁻¹ ∈ Y)
    (hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ Y) {h : G} (hh : h ∈ H)
    (htriv : ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Y) : h ∈ pCoreOf 2 H := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF1 := (hS.hF H hH).toHypF91
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  set φ := actH hV₁ hIH with hφ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  let C : Subgroup G :=
    { carrier := {c | c ∈ H ∧ ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ Y}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, fun x hx => ?_⟩
        have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hHY ha) _).mp (hb' x hx)
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact Y.mul_mem h1 (ha' x hx)
      one_mem' := ⟨H.one_mem, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, fun x hx => ?_⟩
        have hxi : x⁻¹ ∈ X := X.inv_mem hx
        have h1 := ha' _ hxi
        have hax : a⁻¹ * x ∈ H := H.mul_mem (H.inv_mem ha) (hXH hx)
        have h2 := (Subgroup.mem_normalizer_iff.mp (hHY hax) _).mp h1
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
            (a⁻¹ * x) * (a * x⁻¹ * a⁻¹ * x⁻¹⁻¹) * (a⁻¹ * x)⁻¹ := by group
        rw [e]
        exact h2 }
  have hQC : pCoreOf 2 H ≤ C := fun q hq => ⟨pCoreOf_le 2 H hq, hQ q hq⟩
  have hconjC : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    rintro g hg c ⟨hc, hc'⟩
    refine ⟨H.mul_mem (H.mul_mem hg hc) (H.inv_mem hg), fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hHX (H.inv_mem hg)) x).mp hx
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHY hg) _).mp (hc' _ hx')
    have e : g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ =
        g * (c * (g⁻¹ * x * g) * c⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconjC g hg c hc, fun hc => ?_⟩
    have := hconjC g⁻¹ (H.inv_mem hg) _ hc
    simpa [mul_assoc] using this
  have hKst : S.KSt H K = (K.subgroupOf H).map φ := autOn_tilde_eq_map_actH hV₁ hIH hKH
  have hKC : K ⊓ C ≤ pCoreOf 2 H := by
    set M := ((K ⊓ C).subgroupOf H).map φ with hM
    have hMn : (M.subgroupOf (S.KSt H K)).Normal := by
      refine ⟨fun m hm a => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      obtain ⟨y, hy, hym⟩ := hm
      obtain ⟨k, hk, hka⟩ := hKst.le a.2
      have hyK := (Subgroup.mem_subgroupOf.1 hy).1
      have hyC := (Subgroup.mem_subgroupOf.1 hy).2
      have hkK := Subgroup.mem_subgroupOf.1 hk
      refine ⟨k * y * k⁻¹, Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩, ?_⟩
      · exact K.mul_mem (K.mul_mem hkK hyK) (K.inv_mem hkK)
      · exact hconjC _ (hKH hkK) _ hyC
      · rw [map_mul, map_mul, map_inv, hka, hym]
        simp
    have := hsimp
    rcases hMn.eq_bot_or_eq_top with hb | ht
    · intro y hy
      have hyH : y ∈ H := hKH hy.1
      have hφy : φ ⟨y, hyH⟩ ∈ S.KSt H K := by
        rw [hKst]
        exact ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.2 hy.1, rfl⟩
      have hmem : (⟨φ ⟨y, hyH⟩, hφy⟩ : ↥(S.KSt H K)) ∈ M.subgroupOf (S.KSt H K) :=
        Subgroup.mem_subgroupOf.2 ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact (hker _).1 (congrArg Subtype.val hmem)
    · exfalso
      obtain ⟨k, hk, x, hx, hkx⟩ := hKnt
      apply hkx
      have hkH : k ∈ H := hKH hk
      have hφk : φ ⟨k, hkH⟩ ∈ S.KSt H K := by
        rw [hKst]
        exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
      have hmem : (⟨φ ⟨k, hkH⟩, hφk⟩ : ↥(S.KSt H K)) ∈ M.subgroupOf (S.KSt H K) := by
        rw [ht]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_subgroupOf.1 hmem
      have hq : ((y⁻¹ * ⟨k, hkH⟩ : ↥H) : G) ∈ pCoreOf 2 H :=
        (hker _).1 (by rw [map_mul, map_inv, hyk, inv_mul_cancel])
      have hkC : k ∈ C := by
        have h1 := C.mul_mem (Subgroup.mem_subgroupOf.1 hy).2 (hQC hq)
        simpa using h1
      exact hkC.2 x hx
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hTn : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKn
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right T K hTn
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hCp : IsPGroup 2 C := by
    intro c
    have hc' : (c : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm, ← hHK]
      exact c.2.1
    rw [hset] at hc'
    obtain ⟨t, ht, k, hk, htk⟩ := hc'
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have h1 := A6Gen.pow_mul_inv_mem (hTn ht) hk (2 ^ a)
    have htk' : t * k = (c : G) := htk
    rw [hta, inv_one, mul_one, htk'] at h1
    have h3 : (c : G) ^ 2 ^ a ∈ pCoreOf 2 H := hKC ⟨h1, C.pow_mem c.2 _⟩
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 H ⟨_, h3⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((c : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have hCH : C ≤ H := fun c hc => hc.1
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCH hCn hCp ⟨hh, htriv⟩

theorem mem_pCoreOf_of_comm (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ T)
    (hsimp : IsSimpleGroup ↥(S.KSt H K))
    (hnab : ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H) {h : G} (hh : h ∈ H)
    (hc : ∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : h ∈ pCoreOf 2 H := by
  refine S.le_pCoreOf_of_triv hS hH hKH hKn hHK hsimp hKH hKn
    (fun g hg => le_normalizer_pCoreOf 2 H hg) (fun q hq k hk => ?_) hnab hh hc
  have h1 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hk)) _).mp
      ((pCoreOf 2 H).inv_mem hq)
  have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 H).mul_mem hq h1

structure SecHyp (H K X W : Subgroup G) : Prop where
  hS : S.Hyp138
  hH : H ∈ S.Hz
  hKH : K ≤ H
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hHK : H = K ⊔ T
  hsimp : IsSimpleGroup ↥(S.KSt H K)
  hnab : ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H
  hWX : W ≤ X
  hXH : X ≤ H
  hHX : H ≤ Subgroup.normalizer (X : Set G)
  hHW : H ≤ Subgroup.normalizer (W : Set G)
  hQ : ∀ q ∈ pCoreOf 2 H, ∀ x ∈ X, q * x * q⁻¹ * x⁻¹ ∈ W
  hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ W
  hsq : ∀ x ∈ X, x * x ∈ W

namespace SecHyp

variable {S} {H K X W : Subgroup G} (hs : S.SecHyp H K X W)
include hs

theorem hHXW : H ≤ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) := by
  rw [inf_eq_right.2 hs.hWX]
  exact hs.hHW

variable [IsMulCommutative ↥X]

@[expose] noncomputable def act : ↥H →* MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) :=
  A6Mod.secAct hs.hHX hs.hHXW

theorem act_secMk (h : ↥H) (x : ↥X) :
    hs.act h (InternalSec.secMk (W.subgroupOf X) x) =
      InternalSec.secMk (W.subgroupOf X) (Setup.rho X H hs.hHX h x) := rfl

theorem act_eq_one_iff (h : ↥H) : hs.act h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
  unfold act
  rw [A6Mod.secAct_eq_one_iff]
  exact ⟨fun h1 => S.le_pCoreOf_of_triv hs.hS hs.hH hs.hKH hs.hKn hs.hHK hs.hsimp hs.hXH hs.hHX
    hs.hHW hs.hQ hs.hKnt h.2 h1, fun h1 => hs.hQ h h1⟩

theorem mem_autSec_iff {F : Subgroup G} (hFH : F ≤ H)
    {ψ : MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))} :
    ψ ∈ autSec (autOn F X) ⊤ (W.subgroupOf X) ↔ ∃ f : ↥H, (f : G) ∈ F ∧ hs.act f = ψ :=
  A6Mod.mem_autSec_iff hs.hHX hs.hHXW hFH

theorem autSec_le {F F' : Subgroup G} (hFF' : F ≤ F') (hF'H : F' ≤ H) :
    autSec (autOn F X) ⊤ (W.subgroupOf X) ≤ autSec (autOn F' X) ⊤ (W.subgroupOf X) := by
  intro ψ hψ
  obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff (hFF'.trans hF'H)).1 hψ
  exact (hs.mem_autSec_iff hF'H).2 ⟨f, hFF' hf, rfl⟩

theorem card_autSec {F : Subgroup G} (hFH : F ≤ H) :
    Nat.card (autSec (autOn F X) ⊤ (W.subgroupOf X)) = (F ⊓ pCoreOf 2 H).relIndex F := by
  refine A6Mod.card_autSec_eq hs.hHX hs.hHXW hFH fun f hf => ?_
  have h1 := hs.act_eq_one_iff ⟨f, hFH hf⟩
  unfold act at h1
  rw [A6Mod.secAct_eq_one_iff] at h1
  exact h1.symm

omit [Finite G] hs in
theorem card_sec : Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) = W.relIndex X := by
  show ((W.subgroupOf X).subgroupOf ⊤).index = W.relIndex X
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rfl

theorem sec_sq (y : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) : y * y = 1 := by
  obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) y
  rw [← map_mul, A6Mod.secMk_eq_one_iff]
  exact hs.hsq x x.2

theorem top_ne_bot : (⊤ : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) ≠ ⊥ := by
  intro h
  obtain ⟨k, hk, x, hx, hkx⟩ := hs.hKnt
  apply hkx
  have hkxX : k * x * k⁻¹ * x⁻¹ ∈ X := by
    have h1 : k * x * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hs.hHX (hs.hKH hk)) x).mp hx
    exact X.mul_mem h1 (X.inv_mem hx)
  have h1 : InternalSec.secMk (W.subgroupOf X) ⟨_, hkxX⟩ ∈ (⊤ : Subgroup (Sec _ _)) := trivial
  rw [h, Subgroup.mem_bot, A6Mod.secMk_eq_one_iff] at h1
  exact h1

theorem irr (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    (J : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))
    (hJ : ∀ h : ↥H, ∀ y ∈ J, hs.act h y ∈ J) : J = ⊥ ∨ J = ⊤ := by
  set P : Subgroup G := (J.comap (InternalSec.secMk (W.subgroupOf X))).map X.subtype with hP
  have hmemP : ∀ x : ↥X, (x : G) ∈ P ↔ InternalSec.secMk (W.subgroupOf X) x ∈ J := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx⟩
      rw [Subtype.ext hxx] at hx'
      exact hx'
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hWP : W ≤ P := by
    intro w hw
    have hwX : w ∈ X := hs.hWX hw
    rw [show w = ((⟨w, hwX⟩ : ↥X) : G) from rfl, hmemP]
    have : InternalSec.secMk (W.subgroupOf X) ⟨w, hwX⟩ = 1 := (A6Mod.secMk_eq_one_iff _).2 hw
    rw [this]
    exact J.one_mem
  have hPX : P ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P := by
      rintro h hh _ ⟨x, hx, rfl⟩
      have hhx : h * x * h⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hs.hHX hh) x).mp x.2
      show h * (x : G) * h⁻¹ ∈ P
      rw [show h * (x : G) * h⁻¹ = ((⟨h * x * h⁻¹, hhx⟩ : ↥X) : G) from rfl, hmemP]
      have := hJ ⟨h, hh⟩ _ hx
      rw [act_secMk] at this
      exact this
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨key h hh p, fun hp => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hp
    simpa [mul_assoc] using this
  rcases hirr P hWP hPX hHP with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) y
    have hxP : (x : G) ∈ P := (hmemP x).2 hy
    rw [h] at hxP
    rw [Subgroup.mem_bot, A6Mod.secMk_eq_one_iff]
    exact hxP
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) y
    have hxP : (x : G) ∈ P := by rw [h]; exact x.2
    exact (hmemP x).1 hxP

theorem secMk_mem_fixV {F : Subgroup G} (hFH : F ≤ H) {x : ↥X}
    (hx : ∀ f ∈ F, f * (x : G) * f⁻¹ * (x : G)⁻¹ ∈ W) :
    InternalSec.secMk (W.subgroupOf X) x ∈ fixV (autSec (autOn F X) ⊤ (W.subgroupOf X)) := by
  intro ψ hψ
  obtain ⟨f, hfF, rfl⟩ := (hs.mem_autSec_iff hFH).1 hψ
  show hs.act f (InternalSec.secMk (W.subgroupOf X) x) = InternalSec.secMk (W.subgroupOf X) x
  rw [act_secMk]
  have h1 : InternalSec.secMk (W.subgroupOf X) (Setup.rho X H hs.hHX f x) *
      (InternalSec.secMk (W.subgroupOf X) x)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
    simp only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
    exact hx f hfF
  exact mul_inv_eq_one.1 h1

theorem index_fixV_le {F : Subgroup G} (hFH : F ≤ H) :
    (fixV (autSec (autOn F X) ⊤ (W.subgroupOf X))).index ≤
      (centralizerMod W X F).relIndex X := by
  set C' := centralizerMod W X F with hC'
  have hle : (C'.subgroupOf X).map (InternalSec.secMk (W.subgroupOf X)) ≤
      fixV (autSec (autOn F X) ⊤ (W.subgroupOf X)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine hs.secMk_mem_fixV hFH fun f hf => ?_
    have h1 := (Subgroup.mem_subgroupOf.1 hx).2.2 f hf
    have e : f * (x : G) * f⁻¹ * (x : G)⁻¹ = ((x : G) * f * (x : G)⁻¹ * f⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1
  calc (fixV (autSec (autOn F X) ⊤ (W.subgroupOf X))).index
      ≤ ((C'.subgroupOf X).map (InternalSec.secMk (W.subgroupOf X))).index :=
        Subgroup.index_antitone hle
    _ ≤ (C'.subgroupOf X).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
    _ = C'.relIndex X := rfl

theorem isElemAbelian2_autSec {F : Subgroup G} (hFH : F ≤ H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) :
    IsElemAbelian2 (autSec (autOn F X) ⊤ (W.subgroupOf X)) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hFH).1 ha
    obtain ⟨f', hf', rfl⟩ := (hs.mem_autSec_iff hFH).1 hb
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hs.act_eq_one_iff]
    have e : ((f * f' * (f' * f)⁻¹ : ↥H) : G) = (f : G) * f' * (f : G)⁻¹ * (f' : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      group
    rw [e]
    exact hFc f hf f' hf'
  · obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hFH).1 ha
    rw [← map_pow, hs.act_eq_one_iff, pow_two]
    exact hFs f hf

theorem autSec_ne_bot {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H) :
    autSec (autOn F X) ⊤ (W.subgroupOf X) ≠ ⊥ := by
  intro h
  apply hF
  intro f hf
  have h1 : hs.act ⟨f, hFH hf⟩ ∈ autSec (autOn F X) ⊤ (W.subgroupOf X) :=
    (hs.mem_autSec_iff hFH).2 ⟨⟨f, hFH hf⟩, hf, rfl⟩
  rw [h, Subgroup.mem_bot, hs.act_eq_one_iff] at h1
  exact h1

theorem ctx {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    A6Md.Ctx (autSec (autOn H X) ⊤ (W.subgroupOf X)) (autSec (autOn K X) ⊤ (W.subgroupOf X)) := by
  refine ⟨hs.autSec_le hs.hKH le_rfl, fun g hg l hl => ?_, ?_, fun g hg hcomm => ?_⟩
  · obtain ⟨h, -, rfl⟩ := (hs.mem_autSec_iff le_rfl).1 hg
    obtain ⟨k, hk, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hl
    refine (hs.mem_autSec_iff hs.hKH).2 ⟨h * k * h⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hs.hKn h.2) k).mp hk
  ·
    set LX := autSec (autOn K X) ⊤ (W.subgroupOf X) with hLX
    let φ : ↥K →* ↥LX := (hs.act.comp (Subgroup.inclusion hs.hKH)).codRestrict LX fun k =>
      (hs.mem_autSec_iff hs.hKH).2 ⟨_, k.2, rfl⟩
    have hφs : Function.Surjective φ := by
      rintro ⟨ψ, hψ⟩
      obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
      exact ⟨⟨f, hf⟩, rfl⟩
    have hker : φ.ker = α.ker := by
      ext k
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hαk]
      have : φ k = 1 ↔ hs.act (Subgroup.inclusion hs.hKH k) = 1 := by
        rw [← Subtype.coe_inj]
        rfl
      rw [this, hs.act_eq_one_iff]
      rfl
    exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩
  · obtain ⟨h, -, rfl⟩ := (hs.mem_autSec_iff le_rfl).1 hg
    rw [show hs.act h = 1 ↔ _ from hs.act_eq_one_iff h]
    refine S.mem_pCoreOf_of_comm hs.hS hs.hH hs.hKH hs.hKn hs.hHK hs.hsimp hs.hnab h.2
      fun k hk => ?_
    have h1 := hcomm _ ((hs.mem_autSec_iff hs.hKH).2 ⟨⟨k, hs.hKH hk⟩, hk, rfl⟩)
    have h2 : hs.act (h * ⟨k, hs.hKH hk⟩ * h⁻¹ * (⟨k, hs.hKH hk⟩ : ↥H)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    rw [hs.act_eq_one_iff] at h2
    simpa using h2

theorem fixV_eq_bot
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X) :
    fixV (autSec (autOn K X) ⊤ (W.subgroupOf X)) = ⊥ := by
  have hinv : ∀ h : ↥H, ∀ y ∈ fixV (autSec (autOn K X) ⊤ (W.subgroupOf X)),
      hs.act h y ∈ fixV (autSec (autOn K X) ⊤ (W.subgroupOf X)) := by
    intro h y hy l hl
    obtain ⟨k, hk, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hl
    have hk' : (h⁻¹ * k * h : ↥H) ∈ K.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (hs.hKn (H.inv_mem h.2)) k).mp hk
      simpa [mul_assoc] using this
    have h1 := hy (hs.act (h⁻¹ * k * h))
      ((hs.mem_autSec_iff hs.hKH).2 ⟨_, Subgroup.mem_subgroupOf.1 hk', rfl⟩)
    have e : hs.act k (hs.act h y) = hs.act h (hs.act (h⁻¹ * k * h) y) := by
      rw [map_mul, map_mul, map_inv]
      simp only [MulAut.mul_apply]
      simp
    show hs.act k (hs.act h y) = hs.act h y
    rw [e, h1]
  rcases hs.irr hirr (fixV (autSec (autOn K X) ⊤ (W.subgroupOf X))) hinv with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk, x, hx, hkx⟩ := hs.hKnt
    apply hkx
    have h1 : InternalSec.secMk (W.subgroupOf X) ⟨x, hx⟩ ∈
        fixV (autSec (autOn K X) ⊤ (W.subgroupOf X)) := by rw [h]; trivial
    have h2 := h1 (hs.act ⟨k, hs.hKH hk⟩) ((hs.mem_autSec_iff hs.hKH).2 ⟨_, hk, rfl⟩)
    rw [act_secMk] at h2
    have h3 : InternalSec.secMk (W.subgroupOf X) (Setup.rho X H hs.hHX ⟨k, hs.hKH hk⟩ ⟨x, hx⟩) *
        (InternalSec.secMk (W.subgroupOf X) ⟨x, hx⟩)⁻¹ = 1 := by
      rw [h2, mul_inv_cancel]
    rw [← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff] at h3
    simpa only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] using h3

theorem irr_autSec
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    (J : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))
    (hJ : ∀ g ∈ autSec (autOn H X) ⊤ (W.subgroupOf X), ∀ y ∈ J, g y ∈ J) : J = ⊥ ∨ J = ⊤ :=
  hs.irr hirr J fun h y hy => hJ _ ((hs.mem_autSec_iff le_rfl).2 ⟨h, h.2, rfl⟩) y hy

theorem natural_of_le
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hF : ¬ F ≤ pCoreOf 2 H) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H)
    (hle : (centralizerMod W X F).relIndex X ≤ (F ⊓ pCoreOf 2 H).relIndex F) :
    W.relIndex X = 16 := by
  have h1 := A6Md.natural_of_index_le hs.sec_sq (hs.ctx hαs hαk) (hs.fixV_eq_bot hirr)
    (hs.irr_autSec hirr) hs.top_ne_bot (hs.autSec_le hFH le_rfl) (hs.autSec_ne_bot hFH hF)
    (hs.isElemAbelian2_autSec hFH hFc hFs)
    ((hs.index_fixV_le hFH).trans (hle.trans (hs.card_autSec hFH).symm.le))
  rw [← (card_sec (X := X) (W := W))]
  exact h1.1

theorem rank
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (h16 : W.relIndex X = 16)
    {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 8 ∧
      ((F ⊓ pCoreOf 2 H).relIndex F) ^ 2 ≤ ((centralizerMod W X F).relIndex X) ^ 3 := by
  obtain ⟨r, i, hr, hi, -, hr3, h23⟩ := A6Md.exists_rank (hs.ctx hαs hαk) (hs.fixV_eq_bot hirr)
    (by rw [(card_sec (X := X) (W := W)), h16]) (hs.autSec_le hFH le_rfl) (hs.autSec_ne_bot hFH hF)
    (hs.isElemAbelian2_autSec hFH hFc hFs)
  rw [hs.card_autSec hFH] at hr
  rw [hr]
  refine ⟨?_, ?_⟩
  · calc 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr3
      _ = 8 := by norm_num
  · have hle := hs.index_fixV_le hFH
    rw [hi] at hle
    calc (2 ^ r) ^ 2 = 2 ^ (2 * r) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (3 * i) := Nat.pow_le_pow_right (by norm_num) h23
      _ = (2 ^ i) ^ 3 := by rw [← pow_mul, mul_comm]
      _ ≤ ((centralizerMod W X F).relIndex X) ^ 3 := Nat.pow_le_pow_left hle 3

theorem card_le_two
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (h16 : W.relIndex X = 16)
    {F : Subgroup G} (hFH : F ≤ H) {z : G} (hzX : z ∈ X)
    (hz : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 2 := by
  have C := hs.ctx hαs hαk
  obtain ⟨ι⟩ := C.iso
  have hcard : Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) = 16 := by
    rw [(card_sec (X := X) (W := W)), h16]
  obtain ⟨-, hirrL⟩ := A6Md.natural_of_card_le hs.sec_sq C (hs.fixV_eq_bot hirr)
    (hs.irr_autSec hirr) hs.top_ne_bot (by rw [hcard]; norm_num)
  obtain ⟨M⟩ := A6Md.exists_n6Model hs.sec_sq ι hirrL.2 (by rw [hcard]; norm_num)
  rw [← hs.card_autSec hFH]
  refine A6Md.card_le_two_of_center hs.sec_sq C M (hs.autSec_le hFH le_rfl)
    (z := InternalSec.secMk (W.subgroupOf X) ⟨z, hzX⟩) fun b hb v => ?_
  obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hFH).1 hb
  obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) v
  rw [act_secMk, ← map_inv, ← map_mul]
  have hfx : ((Setup.rho X H hs.hHX f x * x⁻¹ : ↥X) : G) = (f : G) * x * (f : G)⁻¹ * (x : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
  rcases hz f hf x x.2 with h | h
  · left
    rw [A6Mod.secMk_eq_one_iff, hfx]
    exact h
  · right
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    exact h

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
