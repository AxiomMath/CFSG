module

public import CFSG.RankThree.GF2n.Tim79a34TwDefs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

variable {G : Type} [Group G]

theorem twb_card_barOf_mul [Finite G] {V H K : Subgroup G} (hK : K ≤ H) :
    Nat.card ↥(barOf V H K) * Nat.card ↥(K ⊓ wOf V H) = Nat.card ↥K := by
  have hgr : ((piBar V H).comp (K.subgroupOf H).subtype).range = barOf V H K := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hinj : Function.Injective (H.subtype.comp (K.subgroupOf H).subtype) :=
    H.subtype_injective.comp (K.subgroupOf H).subtype_injective
  have hgk : ((piBar V H).comp (K.subgroupOf H).subtype).ker.map
      (H.subtype.comp (K.subgroupOf H).subtype) = K ⊓ wOf V H := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : piBar V H k.1 = 1 := hk
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp k.2, (piBar_eq_one_iff k.1).mp h1⟩
    · intro hx
      obtain ⟨hxK, hxW⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨⟨x, hK hxK⟩, Subgroup.mem_subgroupOf.mpr hxK⟩, ?_, rfl⟩
      exact (piBar_eq_one_iff _).mpr hxW
  have hcardk : Nat.card ((piBar V H).comp (K.subgroupOf H).subtype).ker
      = Nat.card ↥(K ⊓ wOf V H) := by
    rw [← hgk, Subgroup.card_map_of_injective hinj]
  have hcardL : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have key := Subgroup.card_ker_mul_card_range ((piBar V H).comp (K.subgroupOf H).subtype)
  rw [hgr, hcardk, hcardL] at key
  rw [mul_comm]
  exact key

theorem twb_barOf_sup {V H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    barOf V H (A ⊔ B) = barOf V H A ⊔ barOf V H B := by
  unfold barOf
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem twb_barOf_eq_bot {V H S : Subgroup G} (hS : S ≤ wOf V H) : barOf V H S = ⊥ := by
  rw [eq_bot_iff]
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := mem_barOf_iff.mp hy
  rw [Subgroup.mem_bot, (piBar_eq_one_iff x).mpr (hS hx)]

theorem twb_barOf_zpowers {V H : Subgroup G} {p : G} (hp : p ∈ H) :
    barOf V H (Subgroup.zpowers p) = Subgroup.zpowers (piBar V H ⟨p, hp⟩) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_barOf_iff.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine mem_barOf_iff.mpr ⟨⟨p, hp⟩ ^ k, ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact zpow_mem (Subgroup.mem_zpowers p) k
    · rw [map_zpow]

theorem twb_barOf_inf_X {V H P : Subgroup G} :
    barOf V H (P ⊓ xOf V H) = barOf V H P ⊓ barOf V H (xOf V H) := by
  refine le_antisymm (le_inf (barOf_mono inf_le_left) (barOf_mono inf_le_right)) ?_
  rintro y ⟨hyP, hyX⟩
  obtain ⟨p, hp, hpy⟩ := mem_barOf_iff.mp hyP
  obtain ⟨x, hx, hxy⟩ := mem_barOf_iff.mp hyX
  have h1 : piBar V H (x⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, hpy, hxy, inv_mul_cancel]
  have h2 : ((x⁻¹ * p : H) : G) ∈ wOf V H := (piBar_eq_one_iff _).mp h1
  have hpX : (p : G) ∈ xOf V H := by
    have h3 : (p : G) = (x : G) * ((x⁻¹ * p : H) : G) := by simp
    rw [h3]
    exact (xOf V H).mul_mem hx (wOf_le_xOf V H h2)
  exact mem_barOf_iff.mpr ⟨p, Subgroup.mem_inf.mpr ⟨hp, hpX⟩, hpy⟩

theorem twb_wOf_le_cX {V H : Subgroup G} (hVH : V ≤ H) : wOf V H ≤ cX V H := by
  intro w hw
  refine ⟨wOf_le_H V H hw, fun y hy => ?_⟩
  have hyN : y ∈ Subgroup.normalizer (wOf V H : Set G) :=
    H_le_normalizer_wOf V H (xOf_le_H hVH hy)
  have h1 : y * w⁻¹ * y⁻¹ ∈ wOf V H :=
    (Subgroup.mem_normalizer_iff.mp hyN w⁻¹).mp ((wOf V H).inv_mem hw)
  have h2 : ⁅w, y⁆ = w * (y * w⁻¹ * y⁻¹) := by
    simp [commutatorElement_def, mul_assoc]
  rw [h2]
  exact (wOf V H).mul_mem hw h1

theorem twb_mem_sup_mul {N S H : Subgroup G} (hSH : S ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {x : G} (hx : x ∈ N ⊔ S) :
    ∃ y ∈ N, ∃ c ∈ S, x = y * c := by
  have hinv : ∀ y ∈ N, ∀ c ∈ S, (y * c)⁻¹ ∈ {g : G | ∃ y ∈ N, ∃ c ∈ S, g = y * c} := by
    intro y hy c hc
    have h := hN c⁻¹ (H.inv_mem (hSH hc)) y⁻¹ (N.inv_mem hy)
    rw [inv_inv] at h
    exact ⟨c⁻¹ * y⁻¹ * c⁻¹⁻¹, by rw [inv_inv]; exact h, c⁻¹, S.inv_mem hc, by group⟩
  let T : Subgroup G :=
    { carrier := {g | ∃ y ∈ N, ∃ c ∈ S, g = y * c}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, c₁, hc₁, rfl⟩ ⟨y₂, hy₂, c₂, hc₂, rfl⟩
        exact ⟨y₁ * (c₁ * y₂ * c₁⁻¹), N.mul_mem hy₁ (hN c₁ (hSH hc₁) y₂ hy₂),
          c₁ * c₂, S.mul_mem hc₁ hc₂, by group⟩
      one_mem' := ⟨1, N.one_mem, 1, S.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨y, hy, c, hc, rfl⟩
        exact hinv y hy c hc }
  have hNT : N ⊔ S ≤ T := sup_le (fun n hn => ⟨n, hn, 1, S.one_mem, by group⟩)
    (fun s hs => ⟨1, N.one_mem, s, hs, by group⟩)
  obtain ⟨y, hy, c, hc, hxyc⟩ := hNT hx
  exact ⟨y, hy, c, hc, hxyc⟩

theorem twb_card_mul_map_projZ {V H : Subgroup G} [Finite G] (R : Subgroup (Xbar V H))
    (hR : Subgroup.center (Xbar V H) ≤ R) :
    Nat.card ↥R = Nat.card ↥(Subgroup.center (Xbar V H)) * Nat.card ↥(R.map (projZ V H)) := by
  have hr : ((projZ V H).comp R.subtype).range = R.map (projZ V H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : ((projZ V H).comp R.subtype).ker = (Subgroup.center (Xbar V H)).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (r : Xbar V H)
  have hk' : Nat.card ↥(((projZ V H).comp R.subtype).ker)
      = Nat.card ↥(Subgroup.center (Xbar V H)) := by
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have key := Subgroup.card_ker_mul_card_range ((projZ V H).comp R.subtype)
  rw [hr, hk'] at key
  exact key.symm

theorem twb_exists_p {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
    {z₀ : Xbar V H} (hz : z₀ ∈ Rbar V H P) :
    ∃ p : G, ∃ hpX : p ∈ xOf V H, p ∈ P ∧ xToXbar hc.V_le_H ⟨p, hpX⟩ = z₀ := by
  obtain ⟨x, hxP, hxz⟩ := mem_barOf_iff.mp (mem_Rbar.mp hz)
  have hxX : (x : G) ∈ xOf V H :=
    preimOf_le_xOf (S := barOf V H (xOf V H)) le_rfl
      (mem_preimOf.mpr ⟨x, rfl, by rw [hxz]; exact z₀.2⟩)
  refine ⟨(x : G), hxX, hxP, Subtype.ext ?_⟩
  rw [coe_xToXbar, ← hxz]
  rfl

theorem twb_card_sup_zpowers {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y)
    (hA : Nat.card ↥A = 2) {z : Y} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hcomm : ∀ a ∈ A, a * z = z * a) (hinf : ∀ a ∈ A, a ∈ Subgroup.zpowers z → a = 1) :
    Nat.card ↥(A ⊔ Subgroup.zpowers z) = 4 := by
  have hZ : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
  have hcommAZ : ∀ a ∈ A, ∀ w ∈ Subgroup.zpowers z, Commute a w := by
    intro a ha w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (show Commute a z from hcomm a ha).zpow_right k
  let ψ : ↥A × ↥(Subgroup.zpowers z) →* Y :=
    MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers z).subtype
      (fun a w => hcommAZ a.1 a.2 w.1 w.2)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, w⟩ h
    have h' : (a : Y) * (w : Y) = 1 := h
    have ha : (a : Y) = (w : Y)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have haZ : (a : Y) ∈ Subgroup.zpowers z := by
      rw [ha]
      exact (Subgroup.zpowers z).inv_mem w.2
    have ha1 : (a : Y) = 1 := hinf _ a.2 haZ
    have hw1 : (w : Y) = 1 := by
      rw [ha1, one_mul] at h'
      exact h'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hw1)
  have hrange : ψ.range = A ⊔ Subgroup.zpowers z := by
    apply le_antisymm
    · rintro _ ⟨⟨a, w⟩, rfl⟩
      exact (A ⊔ Subgroup.zpowers z).mul_mem (Subgroup.mem_sup_left a.2)
        (Subgroup.mem_sup_right w.2)
    · apply sup_le
      · intro a ha
        refine ⟨(⟨a, ha⟩, 1), ?_⟩
        show A.subtype ⟨a, ha⟩ * (Subgroup.zpowers z).subtype 1 = a
        simp
      · intro w hw
        refine ⟨(1, ⟨w, hw⟩), ?_⟩
        show A.subtype 1 * (Subgroup.zpowers z).subtype ⟨w, hw⟩ = w
        simp
  have hcardeq := Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
  rw [← hrange, ← hcardeq, Nat.card_prod, hA, hZ]

theorem twb_inf_bot_of_center {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
    (hd : Sec23Data V H) {z : Xbar V H} (hz : z ∈ Subgroup.center (Xbar V H))
    {a : Hbar V H} (ha : a ∈ barOf V H V) (haz : a ∈ Subgroup.zpowers (z : Hbar V H)) :
    a = 1 := by
  by_contra ha1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
  have hXa : a ∈ barOf V H (xOf V H) := barOf_V_le V H ha
  have hyc : (⟨a, hXa⟩ : Xbar V H) ∈ Subgroup.center (Xbar V H) := by
    have heq : (⟨a, hXa⟩ : Xbar V H) = z ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [heq]
    exact zpow_mem hz k
  exact hd.noncentral ⟨a, hXa⟩ (hc.barOf_V_subset_dbarOf ha ha1) hyc

theorem twb_mul_self_mem_V {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
    {r : G} (hr : r ∈ P) : r * r ∈ V := by
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hmem : ((⟨r, hr⟩ : ↥P) ^ 2) ∈ frattini ↥P :=
    CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨r, hr⟩ : ↥P)
  exact hc.frattini_P_le ⟨_, hmem, by simp [pow_two]⟩

theorem twistedBound_holds (hB4 : SpRadFactsStatement) (hCP : CommPairingStatement) :
    TwistedBoundStatement := by
  intro G _ _ M V Q P H hs hq hP hC n Φ a T z₀ hd hz
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hVP : V ≤ P := hc.V_le_P
  have hPH : P ≤ H := hc.PleH
  have hWX : wOf V H ≤ xOf V H := wOf_le_xOf V H
  have hVX : V ≤ xOf V H := le_xOf (V_mem_omegaOf V H)
  have hXH : xOf V H ≤ H := xOf_le_H hVH
  have hcPH : cPbar V H P ≤ H := inf_le_left.trans hPH
  have hn1 : 1 ≤ n := by have := hd.three_le; omega
  obtain ⟨p, hpX, hpP, hpz⟩ := twb_exists_p hc hz
  have hpH : p ∈ H := hXH hpX
  have hpzb : piBar V H ⟨p, hpH⟩ = (z₀ : Hbar V H) := by
    have h := coe_xToXbar hVH ⟨p, hpX⟩
    rw [hpz] at h
    exact h.symm
  have hpcX : p ∈ cX V H := by
    refine mem_cX_of_centralizes hVH hpH (fun w => ?_)
    rw [hpzb]
    have h := congrArg (fun y : Xbar V H => (y : Hbar V H))
      (Subgroup.mem_center_iff.mp hd.z_mem w)
    simp only [Subgroup.coe_mul] at h
    rw [← h]
    group
  have hpcP : p ∈ cPbar V H P := Subgroup.mem_inf.mpr ⟨hpP, hpcX⟩
  have hzb_ne : (z₀ : Hbar V H) ≠ 1 := fun h => hd.z_ne (Subtype.ext h)
  have hzb_sq : (z₀ : Hbar V H) ^ 2 = 1 := by
    have h := congrArg (fun y : Xbar V H => (y : Hbar V H)) hd.z_sq
    simpa [pow_two] using h
  have hzb_card : Nat.card ↥(Subgroup.zpowers (z₀ : Hbar V H)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzb_sq hzb_ne]
  have hZ_card : Nat.card ↥(Subgroup.center (Xbar V H)) = 2 := by
    rw [hd.center_eq, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hd.z_sq) hd.z_ne
  have hVbar : Nat.card ↥(barOf V H V) = 2 := hq
  have hinf : ∀ a ∈ barOf V H V, a ∈ Subgroup.zpowers (z₀ : Hbar V H) → a = 1 :=
    fun a ha haz => twb_inf_bot_of_center hc hs.data hd.z_mem ha haz
  have hcomm : ∀ a ∈ barOf V H V, a * (z₀ : Hbar V H) = (z₀ : Hbar V H) * a := by
    intro a ha
    have hXa : a ∈ barOf V H (xOf V H) := barOf_V_le V H ha
    exact congrArg (fun y : Xbar V H => (y : Hbar V H))
      (Subgroup.mem_center_iff.mp hd.z_mem ⟨a, hXa⟩)
  have hcenter_le : Subgroup.center (Xbar V H) ≤ Rbar V H P := by
    rw [hd.center_eq]
    exact Subgroup.zpowers_le.mpr hz
  set A : Subgroup G := V ⊓ wOf V H with hA
  set Bg : Subgroup G := (P ⊓ wOf V H) ⊔ Subgroup.zpowers p with hBg
  set Px : Subgroup G := P ⊓ xOf V H with hPx
  set K0 : Subgroup G := ((P ⊓ wOf V H) ⊔ V) ⊔ Subgroup.zpowers p with hK0
  have hBgP : Bg ≤ P := sup_le inf_le_left (Subgroup.zpowers_le.mpr hpP)
  have hBgcP : Bg ≤ cPbar V H P :=
    sup_le (le_inf inf_le_left (inf_le_right.trans (twb_wOf_le_cX hVH)))
      (Subgroup.zpowers_le.mpr hpcP)
  have hBgX : Bg ≤ xOf V H := sup_le (inf_le_right.trans hWX) (Subgroup.zpowers_le.mpr hpX)
  have hBgH : Bg ≤ H := hBgX.trans hXH
  have hAB : A ≤ Bg := (inf_le_inf hVP (le_refl (wOf V H))).trans le_sup_left
  have hPxW : Px ⊓ wOf V H = P ⊓ wOf V H := by
    rw [hPx, inf_assoc, inf_eq_right.mpr hWX]
  have hK0P : K0 ≤ P := sup_le (sup_le inf_le_left hVP) (Subgroup.zpowers_le.mpr hpP)
  have hK0Px : K0 ≤ Px :=
    sup_le (sup_le (le_inf inf_le_left (inf_le_right.trans hWX)) (le_inf hVP hVX))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hpP, hpX⟩))
  have hK0H : K0 ≤ H := hK0P.trans hPH
  have hVK0 : V ≤ K0 := le_sup_right.trans le_sup_left
  have hPWK0 : P ⊓ wOf V H ≤ K0 := le_sup_left.trans le_sup_left
  have hpK0 : p ∈ K0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers p)
  have hcomm1 : ∀ b ∈ Bg, ∀ r ∈ Px, ⁅b, r⁆ ∈ A := by
    intro b hb r hr
    rw [hA]
    refine Subgroup.mem_inf.mpr
      ⟨hc.commutator_mem_V_of_mem_P (hBgP hb) (Subgroup.mem_inf.mp hr).1, ?_⟩
    exact ((Subgroup.mem_inf.mp (hBgcP hb)).2).2 r (Subgroup.mem_inf.mp hr).2
  have hcomm2 : ∀ a ∈ A, ∀ x ∈ Bg ⊔ Px, a * x = x * a := by
    intro a ha x hx
    have hxP : x ∈ P := (sup_le hBgP inf_le_left) hx
    have haV : a ∈ V := by
      rw [hA] at ha
      exact (Subgroup.mem_inf.mp ha).1
    exact hc.commute_of_mem_P hxP haV
  have hcomm3 : ∀ b ∈ Bg, ∀ k ∈ K0, b * k = k * b := by
    intro b hb k hk
    have hbP : b ∈ P := hBgP hb
    have hbcP : b ∈ cPbar V H P := hBgcP hb
    have hle : K0 ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact hc.cPbar_centralizes_wOf hbcP w (Subgroup.mem_inf.mp hw).2
      · intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact (hc.commute_of_mem_P hbP hv).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact hC.2.2.comm (Subgroup.mem_sup_right hbcP) (Subgroup.mem_sup_right hpcP)
    exact Subgroup.mem_centralizer_iff.mp (hle hk) b (Set.mem_singleton b)
  have hBgbar : barOf V H Bg = Subgroup.zpowers (z₀ : Hbar V H) := by
    rw [hBg, twb_barOf_sup (inf_le_left.trans hPH) (Subgroup.zpowers_le.mpr hpH),
      twb_barOf_eq_bot (inf_le_right : P ⊓ wOf V H ≤ wOf V H), bot_sup_eq,
      twb_barOf_zpowers hpH, hpzb]
  have hcomm4 : ∀ b ∈ Bg, (∀ r ∈ Px, b * r = r * b) → b ∈ A := by
    intro b hb hbc
    have hbP : b ∈ P := hBgP hb
    have hbcP : b ∈ cPbar V H P := hBgcP hb
    have hbH : b ∈ H := hPH hbP
    have hbV : b ∈ V := by
      rw [← hc.centralizer_P_eq, Subgroup.mem_centralizer_iff]
      intro x hx
      have hxS : x ∈ xOf V H ⊔ cPbar V H P := by
        rw [hC.2.1]
        exact hPH hx
      have hN : ∀ h ∈ H, ∀ n ∈ xOf V H, h * n * h⁻¹ ∈ xOf V H := fun h hh n hn =>
        (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H hh) n).mp hn
      obtain ⟨y, hy, c, hc', rfl⟩ := twb_mem_sup_mul hcPH hN hxS
      have hyP : y ∈ P := by
        have h := P.mul_mem hx (P.inv_mem (Subgroup.mem_inf.mp hc').1)
        simpa using h
      have hyPX : y ∈ Px := Subgroup.mem_inf.mpr ⟨hyP, hy⟩
      have h1 : b * y = y * b := hbc y hyPX
      have h2 : c * b = b * c :=
        hC.2.2.comm (Subgroup.mem_sup_right hc') (Subgroup.mem_sup_right hbcP)
      rw [mul_assoc, h2, ← mul_assoc, ← h1, mul_assoc]
    have hbV' : piBar V H ⟨b, hbH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨⟨b, hbH⟩, hbV, rfl⟩
    have hbz : piBar V H ⟨b, hbH⟩ ∈ Subgroup.zpowers (z₀ : Hbar V H) := by
      have h : piBar V H ⟨b, hbH⟩ ∈ barOf V H Bg := mem_barOf_iff.mpr ⟨⟨b, hbH⟩, hb, rfl⟩
      rw [hBgbar] at h
      exact h
    have hbW : b ∈ wOf V H := (piBar_eq_one_iff ⟨b, hbH⟩).mp (hinf _ hbV' hbz)
    rw [hA]
    exact Subgroup.mem_inf.mpr ⟨hbV, hbW⟩
  have hconj : ∀ r ∈ Px, ∀ k ∈ K0, r * k * r⁻¹ ∈ K0 := by
    intro r hr k hk
    have hrP : r ∈ P := (Subgroup.mem_inf.mp hr).1
    have hrH : r ∈ H := hPH hrP
    have hle : K0 ≤ K0.comap (MulAut.conj r).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro w hw
        rw [Subgroup.mem_comap]
        change r * w * r⁻¹ ∈ K0
        obtain ⟨hwP, hwW⟩ := Subgroup.mem_inf.mp hw
        exact hPWK0 (Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hrP hwP) (P.inv_mem hrP),
          (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hrH) w).mp hwW⟩)
      · intro v hv
        rw [Subgroup.mem_comap]
        change r * v * r⁻¹ ∈ K0
        have hrv : r * v = v * r := (hc.commute_of_mem_P hrP hv).symm
        rw [hrv, mul_inv_cancel_right]
        exact hVK0 hv
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        change r * p * r⁻¹ ∈ K0
        have h1 : ⁅r, p⁆ * p = r * p * r⁻¹ := by
          simp [commutatorElement_def]
        rw [← h1]
        exact K0.mul_mem (hVK0 (hc.commutator_mem_V_of_mem_P hrP hpP)) hpK0
    have h := hle hk
    rw [Subgroup.mem_comap] at h
    exact h
  have hcomm5 : ∀ r ∈ Px, ∀ r' ∈ Px, ⁅r, r'⁆ ∈ K0 := fun r hr r' hr' =>
    hVK0 (hc.commutator_mem_V_of_mem_P (Subgroup.mem_inf.mp hr).1 (Subgroup.mem_inf.mp hr').1)
  have hsq : ∀ r ∈ Px, r * r ∈ K0 :=
    fun r hr => hVK0 (twb_mul_self_mem_V hc (Subgroup.mem_inf.mp hr).1)
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hRt_eq : Rtilde V H P = (spRad a).map Φ := by
    have hP' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := hP
    have hVZ : VZ V H = T.map Φ := hd.map_eq.symm
    have hnorm : Subgroup.normalizer ((T.map Φ : Subgroup (XbarZ V H)) : Set (XbarZ V H)) =
        (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))).map Φ :=
      (Subgroup.map_normalizer_eq_of_bijective T hd.bij).symm
    have hpc : pCoreOf 2 ((Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))).map Φ) =
        (pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1))))).map Φ :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective Φ hd.bij)
        (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1))))
    have hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))) =
        spRad a :=
      spCoreStmt_holds n (GaloisField 2 1) hd.ne_zero hd.trans
    rw [hP', hVZ, hnorm, hpc, hcore]
  have hRt_card : Nat.card ↥(Rtilde V H P) = 2 ^ (2 * n - 1) := by
    rw [hRt_eq, Subgroup.card_map_of_injective hd.bij.1]
    exact (hB4 n hn1 (GaloisField 2 1) hF2 a hd.ne_zero).2.2
  have hRbar_eq : Nat.card ↥(Rbar V H P) = 2 ^ (2 * n) := by
    have h := twb_card_mul_map_projZ (Rbar V H P) hcenter_le
    rw [hZ_card] at h
    have h2 : (Rbar V H P).map (projZ V H) = Rtilde V H P := rfl
    rw [h2, hRt_card] at h
    rw [h, ← pow_succ']
    congr 1
    omega
  have hRbar_map : (Rbar V H P).map (barOf V H (xOf V H)).subtype =
      barOf V H P ⊓ barOf V H (xOf V H) := by
    unfold Rbar
    exact Subgroup.subgroupOf_map_subtype _ _
  have hRbar_card' : Nat.card ↥(barOf V H P ⊓ barOf V H (xOf V H)) = 2 ^ (2 * n) := by
    rw [← hRbar_map, Subgroup.card_map_of_injective (barOf V H (xOf V H)).subtype_injective,
      hRbar_eq]
  have hPx_card : Nat.card ↥(barOf V H Px) * Nat.card ↥(P ⊓ wOf V H) = Nat.card ↥Px := by
    have h := twb_card_barOf_mul (V := V) (H := H) (K := Px) (inf_le_right.trans hXH)
    rw [hPxW] at h
    exact h
  have hbarPx : barOf V H Px = barOf V H P ⊓ barOf V H (xOf V H) := twb_barOf_inf_X
  rw [hbarPx, hRbar_card'] at hPx_card
  have hPx_eq : Nat.card ↥Px = 2 ^ (2 * n) * Nat.card ↥(P ⊓ wOf V H) := hPx_card.symm
  have hK0W : K0 ⊓ wOf V H = P ⊓ wOf V H :=
    le_antisymm (inf_le_inf hK0P le_rfl) (le_inf hPWK0 inf_le_right)
  have hK0bar : barOf V H K0 = barOf V H V ⊔ Subgroup.zpowers (z₀ : Hbar V H) := by
    have h1 : barOf V H ((P ⊓ wOf V H) ⊔ V) = barOf V H V := by
      rw [twb_barOf_sup (inf_le_left.trans hPH) hVH,
        twb_barOf_eq_bot (inf_le_right : P ⊓ wOf V H ≤ wOf V H), bot_sup_eq]
    rw [hK0, twb_barOf_sup (sup_le (inf_le_left.trans hPH) hVH)
      (Subgroup.zpowers_le.mpr hpH), h1, twb_barOf_zpowers hpH, hpzb]
  have hK0_card : Nat.card ↥K0 = 4 * Nat.card ↥(P ⊓ wOf V H) := by
    have h := twb_card_barOf_mul (V := V) (H := H) (K := K0) hK0H
    rw [hK0W, hK0bar] at h
    rw [twb_card_sup_zpowers (barOf V H V) hVbar hzb_ne hzb_sq hcomm hinf] at h
    exact h.symm
  have hrel := Subgroup.relIndex_mul_card (H := K0) (K := Px)
  rw [inf_eq_left.mpr hK0Px] at hrel
  have hBg_card : Nat.card ↥Bg = 2 * Nat.card ↥(P ⊓ wOf V H) := by
    have h := twb_card_barOf_mul (V := V) (H := H) (K := Bg) hBgH
    have hBgW : Bg ⊓ wOf V H = P ⊓ wOf V H :=
      le_antisymm (inf_le_inf hBgP le_rfl) (le_inf le_sup_left inf_le_right)
    rw [hBgW, hBgbar] at h
    rw [hzb_card] at h
    exact h.symm
  have hidx : K0.relIndex Px = 2 ^ (2 * n - 2) := by
    have hn2 : 2 ^ (2 * n) = 2 ^ (2 * n - 2) * 4 := by
      rw [show 2 * n = (2 * n - 2) + 2 by omega, pow_add]
      norm_num
    have hpos : 0 < 4 * Nat.card ↥(P ⊓ wOf V H) := by
      have := Nat.card_pos (α := ↥(P ⊓ wOf V H))
      omega
    apply Nat.eq_of_mul_eq_mul_right hpos
    have e1 : K0.relIndex Px * Nat.card ↥K0 = 2 ^ (2 * n) * Nat.card ↥(P ⊓ wOf V H) :=
      hrel.trans hPx_eq
    rw [hK0_card, hn2] at e1
    rw [e1]
    ring
  have hcP := hCP G A Bg Px K0 (2 * n - 2) hAB hK0Px hcomm1 hcomm2 hcomm3 hcomm4 hconj hcomm5
    hsq hidx
  rw [hBg_card, ← pow_succ', show 2 * n - 2 + 1 = 2 * n - 1 by omega] at hcP
  exact hcP

end CFSG.RankThree.GF2n.Tim79a
