module

public import CFSG.Quasithin.Background.D14Chief
public import CFSG.Quasithin.Background.D14Dual
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.D14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mul_conj_commutator {a b v : G} (h1 : a * (b * v * b⁻¹ * v⁻¹) = (b * v * b⁻¹ * v⁻¹) * a)
    (h2 : (a * v * a⁻¹ * v⁻¹) * (b * v * b⁻¹ * v⁻¹) = (b * v * b⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹)) :
    (a * b) * v * (a * b)⁻¹ * v⁻¹ = (a * v * a⁻¹ * v⁻¹) * (b * v * b⁻¹ * v⁻¹) :=
  calc (a * b) * v * (a * b)⁻¹ * v⁻¹ = (a * (b * v * b⁻¹ * v⁻¹)) * (v * a⁻¹ * v⁻¹) := by group
    _ = ((b * v * b⁻¹ * v⁻¹) * a) * (v * a⁻¹ * v⁻¹) := by rw [h1]
    _ = (b * v * b⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
    _ = (a * v * a⁻¹ * v⁻¹) * (b * v * b⁻¹ * v⁻¹) := h2.symm

theorem conj_commutator_eq {t q v e : G} (he : t * v * t⁻¹ = e * v)
    (h1 : (t * q * t⁻¹) * e = e * (t * q * t⁻¹))
    (h2 : e * ((t * q * t⁻¹) * v * (t * q * t⁻¹)⁻¹ * v⁻¹) =
      ((t * q * t⁻¹) * v * (t * q * t⁻¹)⁻¹ * v⁻¹) * e) :
    t * (q * v * q⁻¹ * v⁻¹) * t⁻¹ = (t * q * t⁻¹) * v * (t * q * t⁻¹)⁻¹ * v⁻¹ :=
  calc t * (q * v * q⁻¹ * v⁻¹) * t⁻¹
      = (t * q * t⁻¹) * (t * v * t⁻¹) * (t * q * t⁻¹)⁻¹ * (t * v * t⁻¹)⁻¹ := by group
    _ = (t * q * t⁻¹) * (e * v) * (t * q * t⁻¹)⁻¹ * (e * v)⁻¹ := by rw [he]
    _ = ((t * q * t⁻¹) * e) * v * (t * q * t⁻¹)⁻¹ * v⁻¹ * e⁻¹ := by group
    _ = (e * (t * q * t⁻¹)) * v * (t * q * t⁻¹)⁻¹ * v⁻¹ * e⁻¹ := by rw [h1]
    _ = (e * ((t * q * t⁻¹) * v * (t * q * t⁻¹)⁻¹ * v⁻¹)) * e⁻¹ := by group
    _ = (((t * q * t⁻¹) * v * (t * q * t⁻¹)⁻¹ * v⁻¹) * e) * e⁻¹ := by rw [h2]
    _ = (t * q * t⁻¹) * v * (t * q * t⁻¹)⁻¹ * v⁻¹ := by group

theorem conjClosure_le_commutator_sup {H T V : Subgroup G} (hTP : T ⊔ oTwoUpper H = H)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    conjClosure V H ≤ ⁅conjClosure V H, oTwoUpper H⁆ ⊔ V := by
  have hTH : T ≤ H := le_sup_left.trans hTP.le
  have hTP' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper H)
  refine conjClosure_le fun g hg v hv => ?_
  have hg' : g ∈ ((oTwoUpper H ⊔ T : Subgroup G) : Set G) := by
    rw [sup_comm, hTP]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTP'] at hg'
  obtain ⟨p, hp, t, ht, rfl⟩ := hg'
  have hv' : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV ht) v).mp hv
  have hpv : ⁅p, t * v * t⁻¹⁆ ∈ ⁅conjClosure V H, oTwoUpper H⁆ := by
    have := Subgroup.inv_mem _
      (Subgroup.commutator_mem_commutator (le_conjClosure V H hv') hp)
    rwa [commutatorElement_inv] at this
  have e : p * t * v * (p * t)⁻¹ = ⁅p, t * v * t⁻¹⁆ * (t * v * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpv) (Subgroup.mem_sup_right hv')

variable [Finite G]

theorem inf_pCoreOf_normal {G₁ G₂ T V M₂ : Subgroup G} (h : D11Hyp G₁ G₂ T V M₂)
    (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.reduced.2.2.1
  set R := pCoreOf 2 G₁ with hRdef
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  set P := oTwoUpper G₂ with hPdef
  set C := R ⊓ R₂ with hCdef
  set Q := conjClosure C G₂ with hQdef
  have hTG₁ : T ≤ G₁ := h.sylow₁.1
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hRT : R ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₁
  have hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G) := h.reduced.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hTG₁.trans hG₁V
  have hVR : V ≤ R :=
    le_pCoreOf_of_le_normalizer 2 h.reduced.1 hG₁V (B6.isPGroup_of_isElemAbelian hV)
  have hRC : R ≤ Subgroup.centralizer (V : Set G) := by
    rw [hRdef, h.centralizer]
    exact inf_le_right
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hR₂G₂ : R₂ ≤ G₂ := pCoreOf_le 2 G₂
  have hR₂2 : IsPGroup 2 R₂ := pCoreOf_isPGroup 2 G₂
  have hVT : V ≤ T := hVR.trans hRT
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    (B6.isElemAbelian_iff.mp hV).1
  have hVnot : ¬ G₂ ≤ Subgroup.normalizer (V : Set G) := by
    intro hG₂V
    exact h.nontrivial (h.no_normal V hVR
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (h.reduced.1.trans le_sup_left)).mpr
        (sup_le hG₁V hG₂V)))
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUG₂ : U ≤ G₂ := hUR₂.trans hR₂G₂
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hU2 : IsPGroup 2 U := hR₂2.to_le hUR₂
  have hVU : V ≤ U := le_conjClosure V G₂
  have hCR : C ≤ R := inf_le_left
  have hCR₂ : C ≤ R₂ := inf_le_right
  have hCQ : C ≤ Q := le_conjClosure C G₂
  have hQR₂ : Q ≤ R₂ := conjClosure_le fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) c).mp (hCR₂ hc)
  have hQT : Q ≤ T := hQR₂.trans hR₂T
  have hQG₂ : Q ≤ G₂ := hQT.trans hTG₂
  have hQ2 : IsPGroup 2 Q := hR₂2.to_le hQR₂
  have hG₂Q : G₂ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_conjClosure C G₂
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := hQT.trans hTV
  have hUQ : U ≤ Q := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂Q hg) v).mp (hCQ ⟨hVR hv, hVR₂ hv⟩)
  have hG₂P : G₂ ≤ Subgroup.normalizer (P : Set G) := le_normalizer_oTwoUpper G₂
  have hTP : T ⊔ P = G₂ := by
    rw [hPdef, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq h.sylow₂
  have hnorm : ∀ X : Subgroup G, T ≤ Subgroup.normalizer (X : Set G) →
      P ≤ Subgroup.normalizer (X : Set G) → G₂ ≤ Subgroup.normalizer (X : Set G) :=
    fun X hT hP => hTP ▸ sup_le hT hP
  have hUIV : U ≤ ⁅U, P⁆ ⊔ V := conjClosure_le_commutator_sup hTP hTV
  set D := V ⊓ Subgroup.centralizer (P : Set G) with hDdef
  have hDV : D ≤ V := inf_le_left
  have hPD : ∀ p ∈ P, ∀ d ∈ D, p * d = d * p := fun p hp d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 p hp
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTV ht, A4.mem_normalizer_centralizer ((hTG₂.trans hG₂P) ht)⟩
  have hPDn : ∀ X : Subgroup G, X ≤ D → P ≤ Subgroup.normalizer (X : Set G) :=
    fun X hXD p hp => B6.mem_normalizer_of_forall_mem
      (fun x hx => by rw [hPD p hp x (hXD hx), mul_inv_cancel_right]; exact hx)
      (fun x hx => by rw [mul_assoc, ← hPD p hp x (hXD hx), inv_mul_cancel_left]; exact hx)
  have hG₂D : G₂ ≤ Subgroup.normalizer (D : Set G) := hnorm D hTD (hPDn D le_rfl)
  have hQD : ∀ q ∈ Q, ∀ d ∈ D, q * d = d * q := by
    have hle : Q ≤ Subgroup.centralizer (D : Set G) := conjClosure_le fun g hg c hc => by
      have hc' : c ∈ Subgroup.centralizer (D : Set G) :=
        Subgroup.centralizer_le (fun x hx => hDV hx) (hRC (hCR hc))
      exact (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer (hG₂D hg)) c).mp hc'
    intro q hq d hd
    exact (Subgroup.mem_centralizer_iff.mp (hle hq) d hd).symm
  have hVQ : ∀ q ∈ Q, ∀ v ∈ V, q * v * q⁻¹ * v⁻¹ ∈ V := fun q hq v hv =>
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQV hq) v).mp hv) (V.inv_mem hv)
  have hclaim : ∀ q ∈ Q, ∀ v ∈ V, q * v * q⁻¹ * v⁻¹ ∈ D := by
    intro q hq v hv
    rw [hDdef, Subgroup.mem_inf]
    refine ⟨hVQ q hq v hv, ?_⟩
    by_contra hnot
    apply hVnot
    have hZU : ⁅U, Q⁆ ≤ U :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hQG₂.trans hG₂U)
    have hG₂Z : G₂ ≤ Subgroup.normalizer ((⁅U, Q⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator hG₂U hG₂Q
    have hZP : ⁅⁅U, Q⁆, P⁆ ≠ ⊥ := by
      intro hbot
      apply hnot
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hqv : q * v * q⁻¹ * v⁻¹ ∈ ⁅U, Q⁆ := by
        have := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (hVU hv) hq)
        rwa [commutatorElement_inv, commutatorElement_def] at this
      have hmem := Subgroup.commutator_mem_commutator hqv hp
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem.symm
    have hIZ := commutator_le_of_ne_bot hU2 hUG₂ hG₂U hchief hZU hG₂Z hZP
    have hUV : U ≤ V :=
      le_of_le_commutator_sup hQ2 hUQ hQV (hUIV.trans (sup_le_sup_right hIZ V))
    have hUV' : U = V := le_antisymm hUV hVU
    rw [← hUV']
    exact hG₂U
  have hDltV : D < V := by
    refine lt_of_le_of_ne hDV fun hDV' => hVnot (hnorm V hTV ?_)
    rw [← hDV']
    exact hPDn D le_rfl
  obtain ⟨v₀, hv₀V, hv₀D, hv₀T⟩ := exists_fixed_of_lt h.sylow₂.2.1 hVT hDltV hTV hTD
  have hfD : ∀ q ∈ Q, q * v₀ * q⁻¹ * v₀⁻¹ ∈ D := fun q hq => hclaim q hq v₀ hv₀V
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    hVcomm x (hDV hx) y (hDV hy)
  let f₀ : Q →* G := MonoidHom.mk' (fun q => (q : G) * v₀ * (q : G)⁻¹ * v₀⁻¹) (fun a b =>
    mul_conj_commutator (hQD a a.2 _ (hfD b b.2)) (hDcomm _ (hfD a a.2) _ (hfD b b.2)))
  have hf₀ : ∀ q : Q, f₀ q = (q : G) * v₀ * (q : G)⁻¹ * v₀⁻¹ := fun q => rfl
  set Cq := f₀.range with hCq
  have hCqD : Cq ≤ D := by
    rintro _ ⟨q, rfl⟩
    exact hfD q q.2
  have hTCq : ∀ t ∈ T, ∀ x ∈ Cq, t * x * t⁻¹ ∈ Cq := by
    rintro t ht _ ⟨q, rfl⟩
    have hq' : t * (q : G) * t⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hG₂Q (hTG₂ ht)) q).mp q.2
    refine ⟨⟨t * q * t⁻¹, hq'⟩, ?_⟩
    rw [hf₀, hf₀]
    have heD : t * v₀ * t⁻¹ * v₀⁻¹ ∈ D := hv₀T t ht
    exact (conj_commutator_eq (by group) (hQD _ hq' _ heD)
      (hDcomm _ heD _ (hfD _ hq'))).symm
  have hG₂Cq : G₂ ≤ Subgroup.normalizer (Cq : Set G) :=
    hnorm Cq (fun t ht => B6.mem_normalizer_of_forall_mem (hTCq t ht)
      (fun x hx => by simpa using hTCq t⁻¹ (T.inv_mem ht) x hx)) (hPDn Cq hCqD)
  set Y := conjClosure (Subgroup.zpowers v₀) G₂ with hYdef
  have hZV : Subgroup.zpowers v₀ ≤ V := Subgroup.zpowers_le.mpr hv₀V
  have hYU : Y ≤ U := conjClosure_mono hZV le_rfl
  have hG₂Y : G₂ ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_conjClosure _ G₂
  have hYP : ⁅Y, P⁆ ≠ ⊥ := by
    intro hbot
    apply hv₀D
    refine ⟨hv₀V, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hmem : ⁅v₀, p⁆ ∈ ⁅Y, P⁆ :=
      Subgroup.commutator_mem_commutator (le_conjClosure _ G₂ (Subgroup.mem_zpowers v₀)) hp
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  have hIY : ⁅U, P⁆ ≤ Y := commutator_le_of_ne_bot hU2 hUG₂ hG₂U hchief hYU hG₂Y hYP
  have hUYV : U ≤ Y ⊔ V := hUIV.trans (sup_le_sup_right hIY V)
  have hZQ : ⁅Subgroup.zpowers v₀, Q⁆ ≤ Cq := by
    rw [Subgroup.zpowers_eq_closure]
    refine commutator_closure_le ?_ ?_
    · rw [← Subgroup.zpowers_eq_closure]
      exact (hZV.trans (hVU.trans hUG₂)).trans hG₂Cq
    · intro s hs q hq
      rw [Set.mem_singleton_iff.mp hs]
      have e : ⁅v₀, q⁆ = (f₀ ⟨q, hq⟩)⁻¹ := by
        rw [hf₀, commutatorElement_def]
        group
      rw [e]
      exact Cq.inv_mem ⟨_, rfl⟩
  have hYQ : ⁅Y, Q⁆ ≤ Cq := by
    refine commutator_closure_le (S := {x | ∃ h ∈ G₂, ∃ z ∈ Subgroup.zpowers v₀, h * z * h⁻¹ = x})
      ((hYU.trans hUG₂).trans hG₂Cq) ?_
    rintro _ ⟨g, hg, z, hz, rfl⟩ q hq
    have hq' : g⁻¹ * q * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp (hG₂Q hg) q).mp hq
    have hzq : ⁅z, g⁻¹ * q * g⁆ ∈ Cq := hZQ (Subgroup.commutator_mem_commutator hz hq')
    have e : ⁅g * z * g⁻¹, q⁆ = g * ⁅z, g⁻¹ * q * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hG₂Cq hg) _).mp hzq
  have hUQCq : ⁅U, Q⁆ ≤ Cq := by
    refine commutator_le_closure (S := {x | ∃ h ∈ G₂, ∃ z ∈ C, h * z * h⁻¹ = x})
      (hQG₂.trans hG₂Cq) ?_
    rintro u hu _ ⟨g, hg, c, hc, rfl⟩
    have hu' : g⁻¹ * u * g ∈ ((Y ⊔ V : Subgroup G) : Set G) :=
      hUYV ((Subgroup.mem_normalizer_iff''.mp (hG₂U hg) u).mp hu)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Y V ((hYU.trans hUQ).trans hQV)] at hu'
    obtain ⟨y, hy, w, hw, hyw⟩ := hu'
    have hyw : y * w = g⁻¹ * u * g := hyw
    have hwc : w * c = c * w := Subgroup.mem_centralizer_iff.mp (hRC (hCR hc)) w hw
    have hyc : ⁅y, c⁆ ∈ Cq := hYQ (Subgroup.commutator_mem_commutator hy (hCQ hc))
    have hu_eq : u = g * (y * w) * g⁻¹ := by
      rw [hyw]
      group
    have e : ⁅u, g * c * g⁻¹⁆ = g * ⁅y, c⁆ * g⁻¹ := by
      rw [hu_eq]
      simp only [commutatorElement_def]
      calc g * (y * w) * g⁻¹ * (g * c * g⁻¹) * (g * (y * w) * g⁻¹)⁻¹ * (g * c * g⁻¹)⁻¹
          = g * (y * (w * c) * w⁻¹ * y⁻¹ * c⁻¹) * g⁻¹ := by group
        _ = g * (y * (c * w) * w⁻¹ * y⁻¹ * c⁻¹) * g⁻¹ := by rw [hwc]
        _ = g * (y * c * y⁻¹ * c⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hG₂Cq hg) _).mp hyc
  have hcomm : ∀ q ∈ Q, ∀ v ∈ V, ∃ q' ∈ Q, q * v * q⁻¹ * v⁻¹ = q' * v₀ * q'⁻¹ * v₀⁻¹ := by
    intro q hq v hv
    have hmem : q * v * q⁻¹ * v⁻¹ ∈ Cq := by
      have h1 := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (hVU hv) hq)
      rw [commutatorElement_inv, commutatorElement_def] at h1
      exact hUQCq h1
    obtain ⟨q', hq'⟩ := hmem
    exact ⟨q', q'.2, hq'.symm⟩
  have hquad : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ v ∈ V,
      q * (q' * v * q'⁻¹ * v⁻¹) * q⁻¹ = q' * v * q'⁻¹ * v⁻¹ := fun q hq q' hq' v hv => by
    rw [hQD q hq _ (hclaim q' hq' v hv), mul_inv_cancel_right]
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hnc
    exact hdual (isDualFFInt_of_commutator hV (hQT.trans hTG₁) hQV hnc hquad hv₀V hcomm)
  have hQR : Q ≤ R := by
    rw [hRdef, h.centralizer]
    exact le_inf hQT hQC
  have hCeq : C = Q := le_antisymm hCQ (le_inf hQR hQR₂)
  rw [hCeq]
  exact hG₂Q

end CFSG.Quasithin.D14
