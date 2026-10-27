module

public import CFSG.Sporadic.SuzRecog.LocalRCent
public import CFSG.Sporadic.SuzRecog.LocalRModel
public import CFSG.Sporadic.SuzRecog.LocalRTrans
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification

variable {G : Type} [Group G] {z : G} {A R : Subgroup G} {H : Type*} [Group H]

theorem eq_sup_zpowers_of_relIndex_eq_two [Finite G] {L K : Subgroup G} (hLK : L ≤ K)
    (h2 : L.relIndex K = 2) {x : G} (hxK : x ∈ K) (hxL : x ∉ L) : K = L ⊔ zpowers x := by
  have hle : L ⊔ zpowers x ≤ K := sup_le hLK ((zpowers_le).2 hxK)
  have h1 := Subgroup.relIndex_mul_relIndex L (L ⊔ zpowers x) K le_sup_left hle
  rw [h2] at h1
  have hne : L.relIndex (L ⊔ zpowers x) ≠ 1 := fun h =>
    hxL (relIndex_eq_one.1 h (mem_sup_right (mem_zpowers x)))
  have hb : (L ⊔ zpowers x).relIndex K = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ h1) with hb | hb
    · exact hb
    · rw [hb] at h1
      omega
  exact le_antisymm (relIndex_eq_one.1 hb) hle

theorem orderOf_eq_two_of_mul_self {x : G} (h : x * x = 1) (h1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h) h1

theorem exists_normalize (σ : ↥(centralizer ({z} : Set G)) ≃* H) {l : H}
    (r : ↥(centralizer ({z} : Set G))) (h : IsConj (σ r) l) :
    ∃ σ' : ↥(centralizer ({z} : Set G)) ≃* H, σ' r = l ∧ ∀ t, IsConj (σ' t) (σ t) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨σ.trans (MulAut.conj c), ?_, fun t => ?_⟩
  · simpa [MulAut.conj_apply] using hc
  · refine isConj_iff.2 ⟨c⁻¹, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem trS_M (σ : ↥(centralizer ({z} : Set G)) ≃* H) :
    trS σ (centralizer ({z} : Set G)) = ⊤ :=
  eq_top_iff.2 fun y _ => mem_trS_iff.2 (σ.symm y).2

theorem mem_four [Finite G] {R : Subgroup G} (hR : Nat.card R = 4) {r s : G} (hr : r ∈ R)
    (hs : s ∈ R) (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hrs : s ≠ r) (hrr : r * r = 1) {u : G}
    (hu : u ∈ R) : u = 1 ∨ u = r ∨ u = s ∨ u = r * s := by
  classical
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hrs1 : r * s ≠ 1 := fun e => hrs (by
    calc s = r * r * s := by rw [hrr, one_mul]
      _ = r * (r * s) := by group
      _ = r := by rw [e, mul_one])
  have hrs2 : r * s ≠ r := fun e => hs1 (by simpa using e)
  have hrs3 : r * s ≠ s := fun e => hr1 (by simpa using e)
  let F : Finset G := {1, r, s, r * s, u}
  have hF : F.card = 5 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem (by simp [hr1.symm, hs1.symm, hrs1.symm, h1.symm]),
      Finset.card_insert_of_notMem (by simp [hrs.symm, hrs2.symm, h2.symm]),
      Finset.card_insert_of_notMem (by simp [hrs3.symm, h3.symm]),
      Finset.card_insert_of_notMem (by simp [h4.symm]), Finset.card_singleton]
  have hsub : (F : Set G) ⊆ (R : Set G) := by
    intro x hx
    simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact hr
    · exact hs
    · exact R.mul_mem hr hs
    · exact hu
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hR] at hle
  omega

section Tau

variable [Finite G]

omit [Finite G] in
theorem Comp.conj_mem_T (hc : Comp z A R) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) {x t : G}
    (hx : x ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G))
    (ht : t ∈ A ⊓ centralizer ({z} : Set G)) :
    x * t * x⁻¹ ∈ A ⊓ centralizer ({z} : Set G) := by
  rw [mem_inf] at hx ht ⊢
  exact ⟨(mem_normalizer_iff.1 (hc.le_normalizer r hr hr1 hx.1) t).1 ht.1,
    mul_mem (mul_mem hx.2 ht.2) (inv_mem hx.2)⟩

theorem Comp.conj_mem_R (hc : Comp z A R) (hM : Nat.card (centralizer ({z} : Set G)) = 3317760)
    (hH : NonCentralSylow z) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) {x s : G}
    (hx : x ∈ centralizer ({r} : Set G)) (hs : s ∈ R) : x * s * x⁻¹ ∈ R := by
  have hxN := hc.le_normalizer r hr hr1 hx
  rw [← hc.centralizer_inf_eq hM hH hr hr1]
  refine mem_inf.2 ⟨mul_mem (mul_mem hx (hc.R_le_centralizer_of_mem hr hs)) (inv_mem hx), ?_⟩
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : x⁻¹ * a * x⁻¹⁻¹ ∈ A := (mem_normalizer_iff.1 (inv_mem hxN) a).1 ha
  have hc' := mem_centralizer_iff.1 (hc.R_le_centralizer hs) _ ha'
  calc a * (x * s * x⁻¹) = x * ((x⁻¹ * a * x⁻¹⁻¹) * s) * x⁻¹ := by group
    _ = x * (s * (x⁻¹ * a * x⁻¹⁻¹)) * x⁻¹ := by rw [hc']
    _ = x * s * x⁻¹ * a := by group

theorem Comp.isSylowOf_T (hc : Comp z A R) (hZ : center A = ⊥) (hz : orderOf z = 2) :
    IsSylowOf 2 (A ⊓ centralizer ({z} : Set G)) A := by
  have h1 := Subgroup.relIndex_mul_card (H := A ⊓ centralizer ({z} : Set G)) (K := A)
  rw [inf_of_le_left (inf_le_left.trans le_rfl), hc.card_inf_M hZ hz, hc.card_A hZ] at h1
  refine isSylowOf_iff.2 ⟨inf_le_left, IsPGroup.of_card (n := 6) ?_, ?_⟩
  · rw [hc.card_inf_M hZ hz]
    norm_num
  · have : (A ⊓ centralizer ({z} : Set G)).relIndex A = 315 := by omega
    rw [this]
    norm_num

variable (hc : Comp z A R) (hz : orderOf z = 2)
  (hM : Nat.card (centralizer ({z} : Set G)) = 3317760) (hH : NonCentralSylow z)
  {σ : ↥(centralizer ({z} : Set G)) ≃* H} {l : H} {T : Subgroup H}
  (hiff : ∀ t : ↥(centralizer ({z} : Set G)), orderOf t = 2 →
    (¬ IsConj (t : G) z ↔ IsConj (σ t) l))
  {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hσr : σ ⟨r, hc.R_le_M hr⟩ = l)

omit [Finite G] in
include hσr in
theorem trS_V :
    trS σ (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) = centralizer ({l} : Set H) := by
  rw [trS_inf, trS_centralizer_singleton (hc.R_le_M hr), trS_M, inf_top_eq, hσr]

include hz hM hH hiff hσr in
theorem trS_T (hMF : LocModel l T) : trS σ (A ⊓ centralizer ({z} : Set G)) = T := by
  have hZ := hc.center_eq_bot hM hH
  obtain ⟨V₁, V₂, hV₁, hV₂, -, -, he₁, he₂, -, -, -, h12, -, -, -, -⟩ :=
    CFSG.OddStandard.Seitz77.exists_parabolic_radicals_of_isSylowOf hc.odd
      (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) (hc.isSylowOf_T hZ hz)
  have hTM : A ⊓ centralizer ({z} : Set G) ≤ centralizer ({z} : Set G) := inf_le_right
  have hrad : ∀ W : Subgroup G, W ≤ A ⊓ centralizer ({z} : Set G) → IsElemAbelian 2 W →
      trS σ W ≤ T := by
    intro W hW heW y hy
    rw [mem_trS_iff] at hy
    set x := σ.symm y with hx
    have hxA : (x : G) ∈ A := (hW hy).1
    by_cases hx1 : (x : G) = 1
    · have : y = 1 := by
        rw [← σ.apply_symm_apply y, ← hx, show x = 1 from Subtype.ext hx1, map_one]
      rw [this]
      exact one_mem _
    have hx2 : orderOf (x : G) = 2 :=
      orderOf_eq_prime (heW.2 _ hy) hx1
    obtain ⟨a, ha, hax⟩ := CFSG.OddStandard.Seitz77.involutions_conj_of_mem hc.odd
      (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) hxA hc.z_mem hx2 hz
    have hconj : IsConj (x : G) z := isConj_iff.2 ⟨a, hax⟩
    have hxo : orderOf x = 2 := by rwa [← Subgroup.orderOf_coe]
    have hnot : ¬ IsConj (σ x) l := fun h => ((hiff x hxo).2 h) hconj
    rw [hx, MulEquiv.apply_symm_apply] at hnot
    have hyV : y ∈ centralizer ({l} : Set H) := by
      rw [← trS_V hc hr hσr, mem_trS_iff]
      exact ⟨hc.le_centralizer_of_mem hr hxA, (x : ↥(centralizer ({z} : Set G))).2⟩
    have hyo : orderOf y = 2 := by
      rw [← σ.apply_symm_apply y, MulEquiv.orderOf_eq, ← hx, hxo]
    exact hMF.mem_T y hyV hyo hnot
  have hle : trS σ (A ⊓ centralizer ({z} : Set G)) ≤ T := by
    rw [← h12, trS_sup (hV₁.trans hTM) (hV₂.trans hTM)]
    exact sup_le (hrad V₁ hV₁ he₁) (hrad V₂ hV₂ he₂)
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hMF.card_T]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hMF.card_T, card_trS hTM, hc.card_inf_M hZ hz]

include hz hM hH hiff hσr in
theorem trS_CV (hMF : LocModel l T) :
    trS σ ((centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) = locC l T := by
  rw [trS_inf, trS_V hc hr hσr, trS_centralizer inf_le_right, trS_T hc hz hM hH hiff hr hσr hMF]
  rfl

include hz hM hH hiff hσr in
theorem CV_eq (hMF : LocModel l T) :
    (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) =
    ((A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) ⊔ R := by
  have hZ := hc.center_eq_bot hM hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hZ4, -, -, -⟩ :=
    CFSG.OddStandard.Seitz77.exists_parabolic_radicals_of_isSylowOf hc.odd
      (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) (hc.isSylowOf_T hZ hz)
  have hTA : A ⊓ centralizer ({z} : Set G) ≤ A := inf_le_left
  have hRT : R ≤ centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    hc.R_le_centralizer.trans (centralizer_le hTA)
  have hle : ((A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) ⊔ R ≤
      (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓
        centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    refine sup_le (le_inf (le_inf ?_ (inf_le_left.trans inf_le_right)) inf_le_right)
      (le_inf (le_inf (hc.R_le_centralizer_of_mem hr) hc.R_le_M) hRT)
    exact inf_le_left.trans (inf_le_left.trans (hc.le_centralizer_of_mem hr))
  have hcomm : ∀ x ∈ (A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G), ∀ y ∈ R,
      x * y = y * x := fun x hx y hy => hc.commute_R x hx.1.1 y hy
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ R hcomm).1
  have hbot : ((A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) ⊓ R = ⊥ :=
    eq_bot_iff.2 fun x hx => by
      rw [← hc.inf_R_eq_bot hZ]
      exact ⟨hx.1.1.1, hx.2⟩
  rw [hbot, Subgroup.card_bot, hZ4, hc.card] at hcard
  have hCV : Nat.card ((centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) : Subgroup G) = 16 := by
    rw [← card_trS (σ := σ) (inf_le_left.trans inf_le_right), trS_CV hc hz hM hH hiff hr hσr hMF,
      hMF.card_C]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hCV]; omega)).symm

include hz hM hH hiff hσr in
theorem trS_TR (hMF : LocModel l T) :
    trS σ ((A ⊓ centralizer ({z} : Set G)) ⊔ R) = T ⊔ locC l T := by
  have hTM : A ⊓ centralizer ({z} : Set G) ≤ centralizer ({z} : Set G) := inf_le_right
  rw [← trS_CV hc hz hM hH hiff hr hσr hMF, ← trS_T hc hz hM hH hiff hr hσr hMF,
    CV_eq hc hz hM hH hiff hr hσr hMF, trS_sup hTM hc.R_le_M,
    trS_sup (inf_le_left.trans hTM) hc.R_le_M]
  apply le_antisymm
  · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  · exact sup_le (le_sup_left) (sup_le ((trS_mono inf_le_left).trans le_sup_left) le_sup_right)

include hz hM hH hiff hr1 hσr in
theorem exists_tau (hMF : LocModel l T) :
    ∃ τ : ↥(centralizer ({z} : Set G)),
      (τ : G) ∈ centralizer ({r} : Set G) ∧ (τ : G) * τ = 1 ∧ (τ : G) ∉ A ⊔ R ∧
      centralizer ({r} : Set G) = (A ⊔ R) ⊔ zpowers (τ : G) ∧
      σ τ ∈ centralizer ({l} : Set H) ∧ σ τ ∉ T ⊔ locC l T ∧
      (∃ s ∈ R, s ≠ 1 ∧ s ≠ r ∧ (τ : G) * s * (τ : G)⁻¹ = r * s) ∧
      ∃ E₁ E₂ : Subgroup G, E₁ ≤ A ⊓ centralizer ({z} : Set G) ∧
        E₂ ≤ A ⊓ centralizer ({z} : Set G) ∧ IsElemAbelian 2 E₁ ∧ IsElemAbelian 2 E₂ ∧
        Nat.card E₁ = 16 ∧ Nat.card E₂ = 16 ∧ E₁ ≠ E₂ ∧
        (∀ E : Subgroup G, E ≤ A ⊓ centralizer ({z} : Set G) → IsElemAbelian 2 E →
          Nat.card E = 16 → E = E₁ ∨ E = E₂) ∧
        E₁.map (MulAut.conj (τ : G)).toMonoidHom = E₂ := by
  have hZ := hc.center_eq_bot hM hH
  obtain ⟨x, hxV, hxout, hx2⟩ := hMF.exists_inv
  have hστ : σ (σ.symm x) = x := σ.apply_symm_apply x
  have hτV : ((σ.symm x : ↥(centralizer ({z} : Set G))) : G) ∈
      centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [← trS_V hc hr hσr] at hxV
    exact mem_trS_iff.1 hxV
  have hτout : ((σ.symm x : ↥(centralizer ({z} : Set G))) : G) ∉
      (A ⊓ centralizer ({z} : Set G)) ⊔ R := fun h => by
    apply hxout
    rw [← trS_TR hc hz hM hH hiff hr hσr hMF, mem_trS_iff]
    exact h
  have hτAR : ((σ.symm x : ↥(centralizer ({z} : Set G))) : G) ∉ A ⊔ R := fun h =>
    hτout (by rw [← hc.inf_sup_R_eq hr]; exact ⟨hτV, h⟩)
  have hτ2 : ((σ.symm x : ↥(centralizer ({z} : Set G))) : G) * (σ.symm x : _) = 1 := by
    have e : σ.symm x * σ.symm x = 1 := by rw [← map_mul, hx2, map_one]
    exact congrArg Subtype.val e
  set τ := σ.symm x with hτdef
  refine ⟨τ, hτV.1, hτ2, hτAR,
    eq_sup_zpowers_of_relIndex_eq_two (hc.sup_R_le hr) (hc.relIndex_sup_R hM hH hz hr hr1)
      hτV.1 hτAR, by rw [hστ]; exact hxV, by rw [hστ]; exact hxout, ?_, ?_⟩
  ·
    obtain ⟨c, hcC, hcnot⟩ := hMF.act_C x hxV hxout
    have hcCV : ((σ.symm c : ↥(centralizer ({z} : Set G))) : G) ∈
        (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓
          centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
      rw [← trS_CV hc hz hM hH hiff hr hσr hMF] at hcC
      exact mem_trS_iff.1 hcC
    rw [CV_eq hc hz hM hH hiff hr hσr hMF] at hcCV
    have hcomm : ∀ a ∈ (A ⊓ centralizer ({z} : Set G)) ⊓
        centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G), ∀ b ∈ R,
        a * b = b * a := fun a ha b hb => hc.commute_R a ha.1.1 b hb
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ R hcomm).2
    have hc' : ((σ.symm c : ↥(centralizer ({z} : Set G))) : G) ∈
        ((((A ⊓ centralizer ({z} : Set G)) ⊓
          centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) ⊔ R :
          Subgroup G) : Set G) := hcCV
    rw [hset] at hc'
    obtain ⟨t, ht, s, hs, hts⟩ := hc'
    have hmove : (τ : G) * s * (τ : G)⁻¹ ≠ s := by
      intro hfix
      apply hcnot
      have hmem : ((τ * σ.symm c * τ⁻¹ * (σ.symm c)⁻¹ : ↥(centralizer ({z} : Set G))) : G) ∈
          A ⊓ centralizer ({z} : Set G) := by
        have e : ((τ * σ.symm c * τ⁻¹ * (σ.symm c)⁻¹ : ↥(centralizer ({z} : Set G))) : G) =
            ((τ : G) * t * (τ : G)⁻¹) * t⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hts]
          calc (τ : G) * (t * s) * (τ : G)⁻¹ * (t * s)⁻¹
              = ((τ : G) * t * (τ : G)⁻¹) * ((τ : G) * s * (τ : G)⁻¹) * s⁻¹ * t⁻¹ := by group
            _ = ((τ : G) * t * (τ : G)⁻¹) * t⁻¹ := by rw [hfix]; group
        rw [e]
        exact mul_mem (hc.conj_mem_T hr hr1 hτV ht.1) (inv_mem ht.1)
      have e2 : x * c * x⁻¹ * c⁻¹ = σ (τ * σ.symm c * τ⁻¹ * (σ.symm c)⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hστ, MulEquiv.apply_symm_apply]
      rw [e2, ← trS_T hc hz hM hH hiff hr hσr hMF, mem_trS_iff, MulEquiv.symm_apply_apply]
      exact hmem
    have hs1 : s ≠ 1 := fun h => hmove (by rw [h]; group)
    have hsr : s ≠ r := fun h => hmove (by
      rw [h]
      have := mem_centralizer_singleton_iff.1 hτV.1
      calc (τ : G) * r * (τ : G)⁻¹ = r * (τ : G) * (τ : G)⁻¹ := by rw [this]
        _ = r := by group)
    have hu := hc.conj_mem_R hM hH hr hr1 hτV.1 hs
    have hrr : r * r = 1 := by rw [← sq]; exact hc.elem.2 r hr
    rcases mem_four hc.card hr hs hr1 hs1 hsr hrr hu with h | h | h | h
    · exfalso
      apply hs1
      calc s = (τ : G)⁻¹ * ((τ : G) * s * (τ : G)⁻¹) * (τ : G) := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hsr
      have := mem_centralizer_singleton_iff.1 hτV.1
      calc s = (τ : G)⁻¹ * ((τ : G) * s * (τ : G)⁻¹) * (τ : G) := by group
        _ = (τ : G)⁻¹ * r * (τ : G) := by rw [h]
        _ = (τ : G)⁻¹ * ((τ : G) * r) := by rw [mul_assoc, this]
        _ = r := by group
    · exact absurd h hmove
    · exact ⟨s, hs, hs1, hsr, h⟩
  ·
    obtain ⟨V₁, V₂, hV₁, hV₂, -, -, he₁, he₂, hc₁, hc₂, h12inf, -, hZ4, -, hE16, hinv⟩ :=
      CFSG.OddStandard.Seitz77.exists_parabolic_radicals_of_isSylowOf hc.odd
        (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) (hc.isSylowOf_T hZ hz)
    have hne : V₁ ≠ V₂ := fun h => by
      rw [h, inf_idem] at h12inf
      rw [← h12inf, hc₂] at hZ4
      omega
    set f := (MulAut.conj (τ : G)).toMonoidHom with hf
    have hfapp : ∀ y, f y = (τ : G) * y * (τ : G)⁻¹ := fun y => rfl
    have hmapT : ∀ W : Subgroup G, W ≤ A ⊓ centralizer ({z} : Set G) →
        W.map f ≤ A ⊓ centralizer ({z} : Set G) := fun W hW => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hfapp]
      exact hc.conj_mem_T hr hr1 hτV (hW hy)
    have hcardmap : ∀ W : Subgroup G, Nat.card (W.map f) = Nat.card W := fun W =>
      Subgroup.card_map_of_injective (MulAut.conj (τ : G)).injective
    have hcases : ∀ W : Subgroup G, W ≤ A ⊓ centralizer ({z} : Set G) → IsElemAbelian 2 W →
        Nat.card W = 16 → W.map f = V₁ ∨ W.map f = V₂ := fun W hW heW hcW =>
      hE16 _ (hmapT W hW) (CFSG.OddStandard.Seitz77.L34.isElemAbelian_map f heW)
        (by rw [hcardmap, hcW])
    obtain ⟨e, heT, he2, hene⟩ := hMF.swap x hxV hxout
    have he'T : ((σ.symm e : ↥(centralizer ({z} : Set G))) : G) ∈
        A ⊓ centralizer ({z} : Set G) := by
      rw [← trS_T hc hz hM hH hiff hr hσr hMF] at heT
      exact mem_trS_iff.1 heT
    have he'2 : ((σ.symm e : ↥(centralizer ({z} : Set G))) : G) ^ 2 = 1 := by
      have : σ.symm e * σ.symm e = 1 := by rw [← map_mul, he2, map_one]
      rw [sq]
      exact congrArg Subtype.val this
    have hcomm_false : ∀ W : Subgroup G, IsElemAbelian 2 W →
        ((σ.symm e : ↥(centralizer ({z} : Set G))) : G) ∈ W →
        (τ : G) * (σ.symm e : _) * (τ : G)⁻¹ ∈ W → False := by
      intro W heW hw1 hw2
      apply hene
      have hcG := congrArg Subtype.val (heW.1.is_comm.comm ⟨_, hw1⟩ ⟨_, hw2⟩)
      have hcM : σ.symm e * (τ * σ.symm e * τ⁻¹) = τ * σ.symm e * τ⁻¹ * σ.symm e :=
        Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcG)
      have := congrArg σ hcM
      simpa only [map_mul, map_inv, hστ, MulEquiv.apply_symm_apply] using this
    refine ⟨V₁, V₂, hV₁, hV₂, he₁, he₂, hc₁, hc₂, hne,
      fun E hE heE hcE => hE16 E hE heE hcE, ?_⟩
    rcases hcases V₁ hV₁ he₁ hc₁ with h1 | h1
    · exfalso
      have h2 : V₂.map f = V₂ := by
        rcases hcases V₂ hV₂ he₂ hc₂ with h2 | h2
        · exact absurd (Subgroup.map_injective (MulAut.conj (τ : G)).injective (h2.trans h1.symm))
            hne.symm
        · exact h2
      rcases hinv _ he'T he'2 with hv | hv
      · have hmem : f (σ.symm e : _) ∈ V₁.map f := Subgroup.mem_map_of_mem f hv
        rw [h1, hfapp] at hmem
        exact hcomm_false V₁ he₁ hv hmem
      · have hmem : f (σ.symm e : _) ∈ V₂.map f := Subgroup.mem_map_of_mem f hv
        rw [h2, hfapp] at hmem
        exact hcomm_false V₂ he₂ hv hmem
    · exact h1

end Tau

end CFSG.Sporadic.SuzRecog.LocalR
