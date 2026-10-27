module

public import CFSG.RankThree.Co2.C4Data
public import CFSG.RankThree.Co2.Lemma210
public import CFSG.RankThree.Co2.Three

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

theorem exists_sylow_conj_mem {G : Type*} [Group G] [Finite G] {X : Subgroup G} {w : G}
    (hw2 : w * w = 1) (hwX : ∀ x ∈ X, w * x * w⁻¹ ∈ X) :
    ∃ P : Sylow 2 X, ∀ x : X, x ∈ (P : Subgroup X) →
      (⟨w * x * w⁻¹, hwX x x.2⟩ : X) ∈ (P : Subgroup X) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hinvol : ∀ x : G, w * (w * x * w⁻¹) * w⁻¹ = x := fun x => by
    rw [hwinv]
    calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw2]; group
  let σ : MulAut X :=
    { toFun := fun x => ⟨w * x * w⁻¹, hwX x x.2⟩
      invFun := fun x => ⟨w * x * w⁻¹, hwX x x.2⟩
      left_inv := fun x => Subtype.ext (hinvol x)
      right_inv := fun x => Subtype.ext (hinvol x)
      map_mul' := fun x y => Subtype.ext (by
        show w * ((x : G) * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹)
        group) }
  have hσ2 : σ ^ 2 = 1 := by
    rw [sq]
    exact MulEquiv.ext fun x => Subtype.ext (hinvol x)
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hσ2
  have hQ : IsPGroup 2 (Subgroup.zpowers σ) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hmod := hQ.card_modEq_card_fixedPoints (Sylow 2 X)
  have hsyl := card_sylow_modEq_one 2 X
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) (Sylow 2 X)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd (hsyl.symm.trans hmod) (by decide)
  obtain ⟨⟨P, hP⟩, -⟩ := Nat.card_ne_zero.1 hfix
  refine ⟨P, fun x hx => ?_⟩
  have h1 : (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) • P = P := hP _
  have h2 : σ • P = P := h1
  have h4 : σ • (P : Subgroup X) = (P : Subgroup X) :=
    Sylow.pointwise_smul_def.symm.trans (congrArg (fun Q : Sylow 2 X => (Q : Subgroup X)) h2)
  have h3 : σ • x ∈ σ • (P : Subgroup X) := Subgroup.smul_mem_pointwise_smul x σ _ hx
  rw [h4] at h3
  exact h3

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem rG_seven_mul_z : h.rG 7 * h.z = h.rG 8 := by
  have e1 : h.rG 7 * h.rG 0 = h.rG 8 := by
    show ((h.φ.symm (rep 7) * h.φ.symm (rep 0) : h.H) : G) = ((h.φ.symm (rep 8) : h.H) : G)
    rw [← map_mul, rep_zero, rep8_eq]
  rwa [h.rG_zero] at e1

theorem z_mul_rG_eight : h.z * h.rG 8 = h.rG 7 := by
  rw [← h.rG_seven_mul_z, ← mul_assoc]
  have hz : h.z * h.rG 7 = h.rG 7 * h.z :=
    (Subgroup.mem_centralizer_singleton_iff.1 (h.φ.symm (rep 7)).2).symm
  rw [hz, mul_assoc, h.sq_eq_one_of_isConj_z (IsConj.refl _), mul_one]

theorem rG_eight_mem_H : h.rG 8 ∈ h.H := (h.φ.symm (rep 8)).2

theorem z_comm_eight : h.z * h.rG 8 = h.rG 8 * h.z :=
  (Subgroup.mem_centralizer_singleton_iff.1 h.rG_eight_mem_H).symm

theorem rG_seven_ne_z : h.rG 7 ≠ h.z := by
  intro e
  have : (h.φ.symm (rep 7) : h.H) = h.zG := Subtype.ext e
  have e' := congrArg h.φ this
  rw [MulEquiv.apply_symm_apply, h.φ_zG] at e'
  exact not_isConj_rCr_rep (i := 7) (by norm_num) (by decide) (by rw [e'])

theorem exists_swap_seven : ∃ y : G, y * h.z * y⁻¹ = h.rG 7 ∧ y * h.rG 7 * y⁻¹ = h.z := by
  have ht : IsConj h.z (h.rG 7) := h.fusesTwo_and_fusesSeven.2
  have htz : h.φ.symm (rep 7) ≠ h.zG := by
    intro e
    exact h.rG_seven_ne_z (congrArg Subtype.val e)
  obtain ⟨s, hs, -, Ψ, h1, h2, c, hc1, hc2, -⟩ := h.exists_partner ht htz
  obtain ⟨hs2, hs1⟩ := h.φ_invol hs
  obtain ⟨j, hj, hsj⟩ := exists_isConj_rep (h.φ s) hs2 hs1
  have hp : PartnerPair 7 j :=
    PartnerElts.of_conj ⟨Ψ, h1, h2⟩ (by rw [MulEquiv.apply_symm_apply]) hsj
  obtain rfl : j = 7 := by
    have := classSizes_eq_of_partnerPair (by norm_num) hj hp
    have hj78 : j = 7 ∨ j = 8 := by
      interval_cases j <;> first | (left; rfl) | (right; rfl) | (simp [classSizes] at this)
    rcases hj78 with h' | rfl
    · exact h'
    · exact absurd (PartnerElts.symm hp)
        (not_partnerPair (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by norm_num))
  obtain ⟨g, hg⟩ := isConj_iff.1 hsj.symm
  have hs' : (s : G) = (h.φ.symm g : G) * h.rG 7 * (h.φ.symm g : G)⁻¹ := by
    have : s = h.φ.symm g * h.φ.symm (rep 7) * (h.φ.symm g)⁻¹ := by
      apply h.φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hg]
    rw [this]
    rfl
  have hhz : (h.φ.symm g : G) * h.z = h.z * (h.φ.symm g : G) :=
    Subgroup.mem_centralizer_singleton_iff.1 (h.φ.symm g).2
  refine ⟨(h.φ.symm g : G)⁻¹ * c⁻¹, ?_, ?_⟩
  · calc (h.φ.symm g : G)⁻¹ * c⁻¹ * h.z * ((h.φ.symm g : G)⁻¹ * c⁻¹)⁻¹ =
        (h.φ.symm g : G)⁻¹ * (c⁻¹ * h.z * c) * (h.φ.symm g : G) := by group
      _ = (h.φ.symm g : G)⁻¹ * ((h.φ.symm g : G) * h.rG 7 * (h.φ.symm g : G)⁻¹) *
          (h.φ.symm g : G) := by rw [← hc2, hs']
      _ = h.rG 7 := by group
  · have hct : c⁻¹ * h.rG 7 * c = h.z := by
      rw [show h.rG 7 = c * h.z * c⁻¹ from hc1.symm]
      group
    calc (h.φ.symm g : G)⁻¹ * c⁻¹ * h.rG 7 * ((h.φ.symm g : G)⁻¹ * c⁻¹)⁻¹ =
        (h.φ.symm g : G)⁻¹ * (c⁻¹ * h.rG 7 * c) * (h.φ.symm g : G) := by group
      _ = (h.φ.symm g : G)⁻¹ * (h.z * (h.φ.symm g : G)) := by rw [hct, mul_assoc]
      _ = h.z := by rw [← hhz]; group

theorem eq_of_lam {w : G} (hwH : w ∈ h.H) (hw8 : w * h.rG 8 = h.rG 8 * w)
    (hwz : IsConj h.z w) (hwz' : IsConj h.z (w * h.rG 8)) : w = h.z ∨ w = h.rG 7 := by
  set u : h.H := ⟨w, hwH⟩
  rcases (h.isConj_z_iff u).1 hwz with e | e | e
  · left
    have : u = h.zG := by
      apply h.φ.injective
      rw [e, h.φ_zG]
    exact congrArg Subtype.val this
  all_goals right
  all_goals
    have hc8 : h.φ u * rep 8 = rep 8 * h.φ u := by
      have := (h.commute_iff u (rep 8)).1 hw8
      exact this
    have hwu : (⟨w * h.rG 8, h.H.mul_mem hwH h.rG_eight_mem_H⟩ : h.H) =
        u * h.φ.symm (rep 8) := rfl
    have hA := (h.isConj_z_iff ⟨w * h.rG 8, h.H.mul_mem hwH h.rG_eight_mem_H⟩).1 hwz'
    rw [hwu, map_mul, MulEquiv.apply_symm_apply] at hA
    have hA' : h.φ u * rep 8 = rCr ∨ IsConj (rep 2) (h.φ u * rep 8) ∨
        IsConj (rep 7) (h.φ u * rep 8) := by
      rcases hA with a | a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a.symm)
      · exact Or.inr (Or.inr a.symm)
  · have := eq_rep7_of_lam (c := 2) (Or.inl rfl) e.symm hc8 hA'
    have hu : u = h.φ.symm (rep 7) := by rw [← this, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val hu
  · have := eq_rep7_of_lam (c := 7) (Or.inr rfl) e.symm hc8 hA'
    have hu : u = h.φ.symm (rep 7) := by rw [← this, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val hu

open _root_.Classical in
@[expose] def gl (x : G) : ℕ :=
  if IsConj h.z x then 1 else if IsConj (h.rG 1) x then 2 else if IsConj (h.rG 8) x then 3 else 0

theorem gl_conj (x y : G) : h.gl (y * x * y⁻¹) = h.gl x := by
  unfold gl
  rw [isConj_conj_right, isConj_conj_right, isConj_conj_right]

theorem gl_eq {x : G} {c : ℕ} (hA : IsConj h.z x ↔ inA c = true)
    (hB : IsConj (h.rG 1) x ↔ inB c = true) (hC : IsConj (h.rG 8) x ↔ inC c = true ∨ c = 9) :
    h.gl x = gLab c := by
  unfold gl gLab
  by_cases a : inA c = true
  · rw [if_pos (hA.2 a), if_pos a]
  · rw [if_neg (fun e => a (hA.1 e)), if_neg a]
    by_cases b : inB c = true
    · rw [if_pos (hB.2 b), if_pos b]
    · rw [if_neg (fun e => b (hB.1 e)), if_neg b]
      by_cases cc : (inC c || c == 9) = true
      · rw [if_pos (hC.2 (by simpa only [Bool.or_eq_true, beq_iff_eq] using cc)), if_pos cc]
      · rw [if_neg (fun e => cc (by simpa only [Bool.or_eq_true, beq_iff_eq] using hC.1 e)),
          if_neg cc]

abbrev zx (m : ℕ) : G := ((h.φ.symm (zuPt m) : h.H) : G)

theorem zx_mul {m m' : ℕ} (hm : m < 16) (hm' : m' < 16) : h.zx m * h.zx m' = h.zx (m ^^^ m') := by
  show ((h.φ.symm (zuPt m) * h.φ.symm (zuPt m') : h.H) : G) = _
  rw [← map_mul, zuPt_mul hm hm']

theorem zx_inj {m m' : ℕ} (hm : m < 16) (hm' : m' < 16) (e : h.zx m = h.zx m') : m = m' :=
  zuPt_inj hm hm' (h.φ.symm.injective (Subtype.ext e))

theorem zx_zero : h.zx 0 = 1 := by
  show ((h.φ.symm (zuPt 0) : h.H) : G) = 1
  rw [zuPt_zero, map_one]
  rfl

theorem zx_one : h.zx 1 = h.z := by
  show ((h.φ.symm (zuPt 1) : h.H) : G) = h.z
  rw [zuPt_one, h.φ_symm_rCr]
  rfl

theorem zx_two : h.zx 2 = h.rG 7 := by
  show ((h.φ.symm (zuPt 2) : h.H) : G) = ((h.φ.symm (rep 7) : h.H) : G)
  rw [zuPt_two]

theorem zuLab_eq {m : ℕ} (hm : m < 16) : zuLab m = h.gl (h.zx m) := by
  by_cases hm0 : m = 0
  · subst hm0
    rw [h.zx_zero]
    have hz1 : h.z ≠ 1 := h.ne_one_of_isConj_z (IsConj.refl _)
    rw [zuLab, if_pos rfl]
    unfold gl
    rw [if_neg (fun e => hz1 (isConj_one_left.1 e)),
      if_neg (fun e => h.rG_ne_one (by norm_num) (isConj_one_left.1 e)),
      if_neg (fun e => h.rG_ne_one (by norm_num) (isConj_one_left.1 e))]
  · have hcls := zuCls_lt hm
    have hcj : IsConj (rep zuCls[m]!) (h.φ (h.φ.symm (zuPt m))) := by
      rw [MulEquiv.apply_symm_apply]
      exact zuPt_isConj hm hm0
    obtain ⟨hA, hB, hC⟩ := h.isConj_iff_of_class hcls hcj
    rw [zuLab, if_neg hm0]
    exact (h.gl_eq hA hB hC).symm

abbrev XG : Subgroup G := Subgroup.centralizer {h.z} ⊓ Subgroup.centralizer {h.rG 8}

theorem XG_eq : h.XG = h.liftG (Subgroup.centralizer {rep 8}) := h.inf_centralizer (rep 8)

theorem card_XG : Nat.card h.XG = 737280 := by
  rw [h.XG_eq, card_liftG]
  exact card_C 8 (by norm_num) (m := 737280) (by decide) (classSizes_pos (by norm_num))

abbrev UG : Subgroup G := h.liftG (subW pWords8)

theorem UG_le : h.UG ≤ h.XG := by
  rw [h.XG_eq]
  intro g hg
  obtain ⟨hgH, hgS⟩ := h.mem_liftG.1 hg
  exact h.mem_liftG.2 ⟨hgH, sylLe8 (by simp) hgS⟩

theorem card_UG : Nat.card h.UG = 16384 := by
  rw [card_liftG, sylCard8]
  norm_num

theorem zx_mem_UG {m : ℕ} (hm : m < 16) : h.zx m ∈ h.UG := h.φ_symm_mem_liftG (zuPt_mem hm)

theorem zx_central {m : ℕ} (hm : m < 16) {u : G} (hu : u ∈ h.UG) : h.zx m * u = u * h.zx m := by
  obtain ⟨huH, huS⟩ := h.mem_liftG.1 hu
  have hc := zuPt_central hm huS
  have e : u = ((h.φ.symm (h.φ ⟨u, huH⟩) : h.H) : G) := by rw [MulEquiv.symm_apply_apply]
  rw [e]
  show ((h.φ.symm (zuPt m) * h.φ.symm (h.φ ⟨u, huH⟩) : h.H) : G) =
    ((h.φ.symm (h.φ ⟨u, huH⟩) * h.φ.symm (zuPt m) : h.H) : G)
  rw [← map_mul, ← map_mul, hc]

theorem exists_zx {y : G} (hy : y ∈ h.UG) (hc : ∀ u ∈ h.UG, y * u = u * y) :
    ∃ m < 16, y = h.zx m := by
  obtain ⟨hyH, hyS⟩ := h.mem_liftG.1 hy
  have hc' : ∀ u ∈ subW pWords8, h.φ ⟨y, hyH⟩ * u = u * h.φ ⟨y, hyH⟩ := by
    intro u hu
    have hcu := hc _ (h.φ_symm_mem_liftG hu)
    have := (h.commute_iff ⟨y, hyH⟩ u).1 hcu
    exact this
  obtain ⟨m, hm, e⟩ := exists_zuPt hyS hc'
  refine ⟨m, hm, ?_⟩
  show y = ((h.φ.symm (zuPt m) : h.H) : G)
  rw [← e, MulEquiv.symm_apply_apply]

theorem smith_contra {w a : G} (hw2 : w * w = 1) (hwz : IsConj h.z w) (ha2 : a * a = 1)
    (hab : a * (w * a * w⁻¹) = (w * a * w⁻¹) * a) (hs : IsConj h.z (a * (w * a * w⁻¹))) :
    w = a * (w * a * w⁻¹) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  set b := w * a * w⁻¹ with hbdef
  set s := a * b with hsdef
  have hb' : w * b * w⁻¹ = a := by
    rw [hbdef, hwinv]
    calc w * (w * a * w) * w = (w * w) * a * (w * w) := by group
      _ = a := by rw [hw2]; group
  have hws : w * s = s * w := by
    have : w * s * w⁻¹ = s := by
      rw [hsdef]
      calc w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
        _ = b * a := by rw [hb']
        _ = a * b := hab.symm
    calc w * s = w * s * w⁻¹ * w := by group
      _ = s * w := by rw [this]
  have haw : a * w * a⁻¹ = s * w := by
    rw [hainv, hsdef, hbdef]
    group
  by_contra hne
  obtain ⟨g, hg⟩ := isConj_iff.1 hs.symm
  have hw''H : g * w * g⁻¹ ∈ h.H := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← hg]
    calc g * w * g⁻¹ * (g * s * g⁻¹) = g * (w * s) * g⁻¹ := by group
      _ = g * (s * w) * g⁻¹ := by rw [hws]
      _ = g * s * g⁻¹ * (g * w * g⁻¹) := by group
  have hw''z : IsConj h.z (g * w * g⁻¹) := hwz.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hzw'' : IsConj h.z (h.z * (g * w * g⁻¹)) := by
    have e : h.z * (g * w * g⁻¹) = g * (a * w * a⁻¹) * g⁻¹ := by
      rw [haw, ← hg]
      group
    rw [e]
    exact hwz.trans ((isConj_iff.2 ⟨a, rfl⟩).trans (isConj_iff.2 ⟨g, rfl⟩))
  have hw''ne : g * w * g⁻¹ ≠ h.z := by
    intro e
    apply hne
    have : g * w * g⁻¹ = g * s * g⁻¹ := by rw [e, hg]
    simpa using this
  set u : h.H := ⟨g * w * g⁻¹, hw''H⟩
  rcases (h.isConj_z_iff u).1 hw''z with e | e | e
  · apply hw''ne
    have : u = h.zG := by
      apply h.φ.injective
      rw [e, h.φ_zG]
    exact congrArg Subtype.val this
  · obtain ⟨c, hc⟩ := isConj_iff.1 e.symm
    have h3 : IsConj (rep 3) (h.φ (h.zG * u)) := by
      have hcr : c * rCr = rCr * c := Subgroup.mem_center_iff.1 rCr_mem_center c
      refine isConj_iff.2 ⟨c, ?_⟩
      rw [map_mul, h.φ_zG, ← hc, ← rep3_eq]
      calc c * (rCr * rep 2) * c⁻¹ = (c * rCr) * rep 2 * c⁻¹ := by group
        _ = (rCr * c) * rep 2 * c⁻¹ := by rw [hcr]
        _ = rCr * (c * rep 2 * c⁻¹) := by group
    have hG3 : IsConj (h.rG 3) (h.z * (g * w * g⁻¹)) := by
      have := h.isConj_φ_symm h3
      rw [MulEquiv.symm_apply_apply] at this
      exact this
    have := (h.isConj_z_rG_iff (c := 3) (by norm_num)).1 (hzw''.trans hG3.symm)
    exact absurd this (by decide)
  · obtain ⟨c, hc⟩ := isConj_iff.1 e.symm
    have h8 : IsConj (rep 8) (h.φ (h.zG * u)) := by
      have hconj : c * rCr * c⁻¹ = rCr := conj_rCr c
      have hcomm : (c * rep 7 * c⁻¹) * rCr = rCr * (c * rep 7 * c⁻¹) :=
        Subgroup.mem_center_iff.1 rCr_mem_center _
      refine isConj_iff.2 ⟨c, ?_⟩
      rw [map_mul, h.φ_zG, ← hc, ← rep8_eq]
      calc c * (rep 7 * rCr) * c⁻¹ = (c * rep 7 * c⁻¹) * (c * rCr * c⁻¹) := by group
        _ = rCr * (c * rep 7 * c⁻¹) := by rw [hconj, hcomm]
    have hG8 : IsConj (h.rG 8) (h.z * (g * w * g⁻¹)) := by
      have := h.isConj_φ_symm h8
      rw [MulEquiv.symm_apply_apply] at this
      exact this
    have := (h.isConj_z_rG_iff (c := 8) (by norm_num)).1 (hzw''.trans hG8.symm)
    exact absurd this (by decide)

theorem not_swap {w : G} (hw8 : w * h.rG 8 = h.rG 8 * w) (hwz : IsConj h.z w)
    (hwπ : w * h.z * w⁻¹ = h.rG 7) : False := by
  haveI := h.finite
  have hw2 : w * w = 1 := h.sq_eq_one_of_isConj_z hwz
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hπ8 : h.rG 7 * h.rG 8 = h.z := by
    rw [← h.rG_seven_mul_z, ← mul_assoc]
    have h77 : h.rG 7 * h.rG 7 = 1 :=
      h.sq_eq_one_of_isConj_z h.fusesTwo_and_fusesSeven.2
    rw [h77, one_mul]
  have hwπ' : w * h.rG 7 * w⁻¹ = h.z := by
    rw [← h.z_mul_rG_eight]
    calc w * (h.z * h.rG 8) * w⁻¹ = (w * h.z * w⁻¹) * (w * h.rG 8 * w⁻¹) := by group
      _ = h.rG 7 * h.rG 8 := by rw [hwπ, hw8, mul_inv_cancel_right]
      _ = h.z := hπ8
  have hwX : ∀ x ∈ h.XG, w * x * w⁻¹ ∈ h.XG := by
    intro x hx
    obtain ⟨hxz, hx8⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxz hx8
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · have hxπ : x * h.rG 7 = h.rG 7 * x := by
        rw [← h.z_mul_rG_eight]
        calc x * (h.z * h.rG 8) = (x * h.z) * h.rG 8 := by group
          _ = h.z * (x * h.rG 8) := by rw [hxz, mul_assoc]
          _ = h.z * (h.rG 8 * x) := by rw [hx8]
          _ = h.z * h.rG 8 * x := by group
      rw [← hwπ']
      calc w * x * w⁻¹ * (w * h.rG 7 * w⁻¹) = w * (x * h.rG 7) * w⁻¹ := by group
        _ = w * (h.rG 7 * x) * w⁻¹ := by rw [hxπ]
        _ = w * h.rG 7 * w⁻¹ * (w * x * w⁻¹) := by group
    · have c1 : Commute w (h.rG 8) := hw8
      have c2 : Commute x (h.rG 8) := hx8
      exact ((c1.mul_left c2).mul_left c1.inv_left).eq
  obtain ⟨P, hP⟩ := exists_sylow_conj_mem hw2 hwX
  have hUcard : Nat.card (h.UG.subgroupOf h.XG) =
      2 ^ (Nat.card h.XG).factorization 2 := by
    rw [card_subgroupOf_eq h.UG_le, h.card_UG, h.card_XG,
      factorization_two_eq (by norm_num : 737280 = 2 ^ 14 * 45) (by decide)]
    norm_num
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq h.XG (Sylow.ofCard _ hUcard) P
  have hyz : (y : G) * h.z = h.z * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).1
  have hy8 : (y : G) * h.rG 8 = h.rG 8 * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
  have hyπ : (y : G) * h.rG 7 = h.rG 7 * y := by
    rw [← h.z_mul_rG_eight]
    calc (y : G) * (h.z * h.rG 8) = h.z * (y * h.rG 8) := by rw [← mul_assoc, hyz, mul_assoc]
      _ = h.z * h.rG 8 * y := by rw [hy8, mul_assoc]
  set w' : G := (y : G)⁻¹ * w * y with hw'def
  have hw'2 : w' * w' = 1 := by
    calc w' * w' = (y : G)⁻¹ * (w * w) * y := by rw [hw'def]; group
      _ = 1 := by rw [hw2]; group
  have hw'inv : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right hw'2
  have hw'z : w' * h.z * w'⁻¹ = h.rG 7 := by
    calc w' * h.z * w'⁻¹ = (y : G)⁻¹ * (w * ((y : G) * h.z * (y : G)⁻¹) * w⁻¹) * y := by
          rw [hw'def]; group
      _ = (y : G)⁻¹ * (h.rG 7 * y) := by
          rw [hyz, mul_inv_cancel_right, hwπ, mul_assoc]
      _ = h.rG 7 := by rw [← hyπ]; group
  have hw'π : w' * h.rG 7 * w'⁻¹ = h.z := by
    calc w' * h.rG 7 * w'⁻¹ =
        (y : G)⁻¹ * (w * ((y : G) * h.rG 7 * (y : G)⁻¹) * w⁻¹) * y := by
          rw [hw'def]; group
      _ = (y : G)⁻¹ * (h.z * y) := by
          rw [hyπ, mul_inv_cancel_right, hwπ', mul_assoc]
      _ = h.z := by rw [← hyz]; group
  have hw'zG : IsConj h.z w' :=
    hwz.trans (isConj_iff.2 ⟨(y : G)⁻¹, by rw [hw'def]; group⟩)
  have hw'U : ∀ u ∈ h.UG, w' * u * w'⁻¹ ∈ h.UG := by
    intro u hu
    have huX : u ∈ h.XG := h.UG_le hu
    have hmem : (⟨(y : G) * u * (y : G)⁻¹, h.XG.mul_mem (h.XG.mul_mem y.2 huX)
        (h.XG.inv_mem y.2)⟩ : h.XG) ∈ (P : Subgroup h.XG) := by
      rw [← hy, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (⟨u, huX⟩ : h.XG) (MulAut.conj y) _
        (Subgroup.mem_subgroupOf.2 hu)
    have h2 := hP _ hmem
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
    have h3 := Subgroup.mem_subgroupOf.1 h2
    have e : ((((MulAut.conj y)⁻¹ • (⟨w * ((y : G) * u * (y : G)⁻¹) * w⁻¹,
        hwX _ (h.XG.mul_mem (h.XG.mul_mem y.2 huX) (h.XG.inv_mem y.2))⟩ : h.XG)) : h.XG) : G) =
        w' * u * w'⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
      show (y : G)⁻¹ * (w * ((y : G) * u * (y : G)⁻¹) * w⁻¹) * (y : G) = w' * u * w'⁻¹
      rw [hw'def]
      group
    rw [e] at h3
    exact h3
  have hex : ∀ m, ∃ m', m < 16 → m' < 16 ∧ w' * h.zx m * w'⁻¹ = h.zx m' := by
    intro m
    by_cases hm : m < 16
    · have hcen : ∀ u ∈ h.UG, w' * h.zx m * w'⁻¹ * u = u * (w' * h.zx m * w'⁻¹) := by
        intro u hu
        have hu'' : w'⁻¹ * u * w' ∈ h.UG := by
          have := hw'U u hu
          rw [hw'inv] at this ⊢
          exact this
        have hc := h.zx_central hm hu''
        calc w' * h.zx m * w'⁻¹ * u = w' * (h.zx m * (w'⁻¹ * u * w')) * w'⁻¹ := by group
          _ = w' * ((w'⁻¹ * u * w') * h.zx m) * w'⁻¹ := by rw [hc]
          _ = u * (w' * h.zx m * w'⁻¹) := by group
      obtain ⟨m', hm', e⟩ := h.exists_zx (hw'U _ (h.zx_mem_UG hm)) hcen
      exact ⟨m', fun _ => ⟨hm', e⟩⟩
    · exact ⟨0, fun h' => absurd h' hm⟩
  choose p hp using hex
  have hplt : ∀ m < 16, p m < 16 := fun m hm => (hp m hm).1
  have hpe : ∀ m < 16, w' * h.zx m * w'⁻¹ = h.zx (p m) := fun m hm => (hp m hm).2
  have hlin : ∀ a < 16, ∀ b < 16, p (a ^^^ b) = p a ^^^ p b := by
    intro a ha b hb
    have hab := xor_lt16 ha hb
    apply h.zx_inj (hplt _ hab) (xor_lt16 (hplt a ha) (hplt b hb))
    rw [← hpe _ hab, ← h.zx_mul (hplt a ha) (hplt b hb), ← hpe a ha, ← hpe b hb,
      ← h.zx_mul ha hb]
    group
  have hp0 : p 0 = 0 := by
    apply h.zx_inj (hplt 0 (by norm_num)) (by norm_num)
    rw [← hpe 0 (by norm_num), h.zx_zero]
    group
  have hp1 : p 1 = 2 := by
    apply h.zx_inj (hplt 1 (by norm_num)) (by norm_num)
    rw [← hpe 1 (by norm_num), h.zx_one, h.zx_two, hw'z]
  have hp2 : p 2 = 1 := by
    apply h.zx_inj (hplt 2 (by norm_num)) (by norm_num)
    rw [← hpe 2 (by norm_num), h.zx_two, h.zx_one, hw'π]
  have hpp : ∀ m < 16, p (p m) = m := by
    intro m hm
    apply h.zx_inj (hplt _ (hplt m hm)) hm
    rw [← hpe _ (hplt m hm), ← hpe m hm, hw'inv]
    calc w' * (w' * h.zx m * w') * w' = (w' * w') * h.zx m * (w' * w') := by group
      _ = h.zx m := by rw [hw'2]; group
  have hlab : ∀ m < 16, zuLab (p m) = zuLab m := by
    intro m hm
    rw [h.zuLab_eq (hplt m hm), h.zuLab_eq hm, ← hpe m hm, h.gl_conj]
  have hσ : ∀ m < 16, p m = sigma (p 4) (p 8) m := fun m hm => eq_sigma hlin hp0 hp1 hp2 hm
  obtain ⟨m, hm, hm1⟩ := zu_aut (p 4) (hplt 4 (by norm_num)) (p 8)
    (hplt 8 (by norm_num)) (fun m hm => by
      rw [← hσ m hm, ← hσ _ (hplt m hm)]
      exact ⟨hpp m hm, hlab m hm⟩)
  rw [← hσ m hm] at hm1
  have hmp := xor_lt16 hm (hplt m hm)
  have hs : IsConj h.z (h.zx (m ^^^ p m)) := by
    rw [h.zuLab_eq hmp] at hm1
    by_contra hns
    unfold gl at hm1
    rw [if_neg hns] at hm1
    split_ifs at hm1 <;> omega
  have ha2 : h.zx m * h.zx m = 1 := by rw [h.zx_mul hm hm, Nat.xor_self, h.zx_zero]
  have hb : w' * h.zx m * w'⁻¹ = h.zx (p m) := hpe m hm
  have hab : h.zx m * (w' * h.zx m * w'⁻¹) = (w' * h.zx m * w'⁻¹) * h.zx m := by
    rw [hb, h.zx_mul hm (hplt m hm), h.zx_mul (hplt m hm) hm, Nat.xor_comm]
  have hs' : IsConj h.z (h.zx m * (w' * h.zx m * w'⁻¹)) := by
    rw [hb, h.zx_mul hm (hplt m hm)]
    exact hs
  have hws := h.smith_contra hw'2 hw'zG ha2 hab hs'
  have hsH : h.zx m * (w' * h.zx m * w'⁻¹) ∈ h.H := by
    rw [hb, h.zx_mul hm (hplt m hm)]
    exact (h.φ.symm (zuPt (m ^^^ p m))).2
  have hw'H : w' ∈ h.H := by
    rw [hws]
    exact hsH
  have : w' * h.z * w'⁻¹ = h.z := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hw'H, mul_inv_cancel_right]
  rw [hw'z] at this
  exact h.rG_seven_ne_z this

theorem mem_map_conj_inv {N : Subgroup G} {c y : G} :
    y ∈ N.map (MulAut.conj c⁻¹).toMonoidHom ↔ c * y * c⁻¹ ∈ N := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa [mul_assoc] using hn
  · intro hy
    refine ⟨c * y * c⁻¹, hy, ?_⟩
    simp [mul_assoc]

theorem exists_class_seven_mem_J : ∃ π₀ ∈ subW jWords, IsConj (rep 7) π₀ := by
  have h : 0 < Nat.card {j : subW jWords // IsConj (rep 7) (j : Cr)} := by
    rw [card_J_class_seven]
    norm_num
  obtain ⟨⟨j, hj⟩⟩ := (Nat.card_pos_iff.1 h).1
  exact ⟨j, j.2, hj⟩

theorem exists_conj_JG_le : ∃ c : G, ∀ j ∈ h.JG,
    c * j * c⁻¹ ∈ Subgroup.centralizer ({h.rG 8} : Set G) := by
  obtain ⟨π₀, hπ₀J, hπ₀⟩ := exists_class_seven_mem_J
  obtain ⟨g, hg⟩ := isConj_iff.1 hπ₀.symm
  have hrJ := rCr_mem_J
  have h8 : g * (π₀ * rCr) * g⁻¹ = rep 8 := by
    calc g * (π₀ * rCr) * g⁻¹ = (g * π₀ * g⁻¹) * (g * rCr * g⁻¹) := by group
      _ = rep 7 * rCr := by rw [hg, conj_rCr]
      _ = rep 8 := rep8_eq
  refine ⟨(h.φ.symm g : G), fun j hj => ?_⟩
  obtain ⟨j', hj', rfl⟩ := h.mem_JG.1 hj
  have hc : j' * (π₀ * rCr) = (π₀ * rCr) * j' :=
    elemTwo_J.2 _ hj' _ ((subW jWords).mul_mem hπ₀J hrJ)
  have key : (g * j' * g⁻¹) * rep 8 = rep 8 * (g * j' * g⁻¹) := by
    rw [← h8]
    calc g * j' * g⁻¹ * (g * (π₀ * rCr) * g⁻¹) = g * (j' * (π₀ * rCr)) * g⁻¹ := by group
      _ = g * ((π₀ * rCr) * j') * g⁻¹ := by rw [hc]
      _ = g * (π₀ * rCr) * g⁻¹ * (g * j' * g⁻¹) := by group
  have ha : h.φ (h.φ.symm g * h.φ.symm j' * (h.φ.symm g)⁻¹) = g * j' * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (h.commute_iff (h.φ.symm g * h.φ.symm j' * (h.φ.symm g)⁻¹) (rep 8)).2
    (by rw [ha]; exact key)

theorem eq_bot_of_odd_normal {N : Subgroup G}
    (hnorm : ∀ m ∈ Subgroup.centralizer ({h.rG 8} : Set G), ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨c, hc⟩ := h.exists_conj_JG_le
  have hnorm' : ∀ m ∈ Subgroup.centralizer ({h.rG 8} : Set G), ∀ n ∈ N, m⁻¹ * n * m ∈ N :=
    fun m hm n hn => by simpa using hnorm m⁻¹ (Subgroup.inv_mem _ hm) n hn
  have hY : N.map (MulAut.conj c⁻¹).toMonoidHom = ⊥ := by
    apply h.eq_bot_of_odd_normalized
    · rwa [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    · intro j hj
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_map_conj_inv, mem_map_conj_inv]
      have hm := hc j hj
      constructor
      · intro hy
        have := hnorm _ hm _ hy
        have e : c * (j * y * j⁻¹) * c⁻¹ = (c * j * c⁻¹) * (c * y * c⁻¹) * (c * j * c⁻¹)⁻¹ := by
          group
        rw [e]
        exact this
      · intro hy
        have e : c * (j * y * j⁻¹) * c⁻¹ = (c * j * c⁻¹) * (c * y * c⁻¹) * (c * j * c⁻¹)⁻¹ := by
          group
        rw [e] at hy
        have := hnorm' _ hm _ hy
        simpa [mul_assoc] using this
  rw [eq_bot_iff]
  intro n hn
  have : c⁻¹ * n * c⁻¹⁻¹ ∈ N.map (MulAut.conj c⁻¹).toMonoidHom := ⟨n, hn, rfl⟩
  rw [hY, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  calc n = c * (c⁻¹ * n * c⁻¹⁻¹) * c⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem exists_normal_of_quotient {L : Type*} [Group L] [Finite L] {t : L} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htc : ∀ x : L, x * t = t * x) [(Subgroup.zpowers t).Normal]
    (Nb : Subgroup (L ⧸ Subgroup.zpowers t)) [Nb.Normal] (hodd : Odd (Nat.card Nb)) :
    ∃ Y : Subgroup L, (∀ y ∈ Y, ∀ g : L, g * y * g⁻¹ ∈ Y) ∧ Nat.card Y = Nat.card Nb := by
  set K := Subgroup.zpowers t
  set N := Nb.comap (QuotientGroup.mk' K)
  have hKN : K ≤ N := fun x hx => by
    show (QuotientGroup.mk' K x) ∈ Nb
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact Nb.one_mem
  have hot : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hKcard : Nat.card K = 2 := by rw [Nat.card_zpowers, hot]
  have hNcard : Nat.card N = Nat.card K * Nat.card Nb :=
    QuotientGroup.card_preimage_mk K (Nb : Set (L ⧸ K))
  haveI : (K.subgroupOf N).Normal := Subgroup.normal_comap N.subtype
  have hK'card : Nat.card (K.subgroupOf N) = 2 := by rw [card_subgroupOf_eq hKN, hKcard]
  have hK'idx : (K.subgroupOf N).index = Nat.card Nb := by
    have := (K.subgroupOf N).card_mul_index
    rw [hK'card, hNcard, hKcard] at this
    omega
  obtain ⟨H₀, hH₀⟩ := Subgroup.exists_right_complement'_of_coprime (N := K.subgroupOf N)
    (by rw [hK'card, hK'idx]; exact Nat.coprime_two_left.2 hodd)
  have hH₀card : Nat.card H₀ = Nat.card Nb := by
    have := hH₀.card_mul_card
    rw [hK'card, hNcard, hKcard] at this
    omega
  have hchar : ∀ n : N, n ∈ H₀ ↔ Odd (orderOf n) := by
    intro n
    constructor
    · intro hn
      have h1 : orderOf (⟨n, hn⟩ : H₀) ∣ Nat.card H₀ := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hH₀card] at h1
      exact Odd.of_dvd_nat hodd h1
    · intro hn
      obtain ⟨⟨⟨k, hk⟩, ⟨h₀, hh₀⟩⟩, hkh, -⟩ := hH₀.existsUnique n
      simp only at hkh
      have hkK : (k : L) ∈ K := Subgroup.mem_subgroupOf.1 hk
      obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hkK
      have hk2 : k * k = 1 := by
        apply Subtype.ext
        show (k : L) * k = 1
        rw [← he, ← zpow_add, ← two_mul, zpow_mul, zpow_two, ht2, one_zpow]
      have hkc : Commute k h₀ := Subtype.ext (by
        show (k : L) * h₀ = h₀ * k
        rw [← he]
        exact ((Commute.zpow_left (Commute.symm (htc (h₀ : L))) e)).eq)
      by_cases hk1 : k = 1
      · rw [hk1, one_mul] at hkh
        rw [← hkh]
        exact hh₀
      · exfalso
        obtain ⟨o, ho⟩ := hn
        have hkpow : k ^ (2 * o + 1) = k := by
          rw [pow_succ, pow_mul, sq, hk2, one_pow, one_mul]
        have hpow : (k * h₀) ^ (2 * o + 1) = 1 := by
          rw [hkh, ← ho]
          exact pow_orderOf_eq_one n
        rw [hkc.mul_pow, hkpow] at hpow
        have hkH : k ∈ H₀ := by
          rw [eq_inv_of_mul_eq_one_left hpow]
          exact H₀.inv_mem (H₀.pow_mem hh₀ _)
        have := Subgroup.disjoint_def.1 hH₀.disjoint hk hkH
        exact hk1 this
  refine ⟨H₀.map N.subtype, fun y hy g => ?_, ?_⟩
  · obtain ⟨n, hn, rfl⟩ := hy
    have hgn : g * (n : L) * g⁻¹ ∈ N := (Subgroup.normal_comap (QuotientGroup.mk' K)).conj_mem _
      n.2 g
    refine ⟨⟨g * n * g⁻¹, hgn⟩, (hchar _).2 ?_, rfl⟩
    have h1 := (hchar n).1 hn
    rw [Subgroup.orderOf_mk, show g * (n : L) * g⁻¹ = MulAut.conj g (n : L) from rfl,
      MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    exact h1
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hH₀card]

theorem rG_eight_sq : h.rG 8 * h.rG 8 = 1 := by
  show ((h.φ.symm (rep 8) * h.φ.symm (rep 8) : h.H) : G) = 1
  rw [← map_mul, rep_mul_self (by norm_num), map_one]
  rfl

theorem conj_z_mem {m : G} (hm : m ∈ Subgroup.centralizer ({h.rG 8} : Set G)) :
    m * h.z * m⁻¹ = h.z ∨ m * h.z * m⁻¹ = h.rG 7 := by
  haveI := h.finite
  set M := Subgroup.centralizer ({h.rG 8} : Set G) with hMdef
  have h88 := h.rG_eight_sq
  have hz2 : h.z * h.z = 1 := h.sq_eq_one_of_isConj_z (IsConj.refl _)
  have h77 : h.rG 7 * h.rG 7 = 1 := h.sq_eq_one_of_isConj_z h.fusesTwo_and_fusesSeven.2
  set t8M : M := ⟨h.rG 8, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with ht8M
  set zM : M := ⟨h.z, Subgroup.mem_centralizer_singleton_iff.2 h.z_comm_eight⟩ with hzM
  have htc : ∀ x : M, x * t8M = t8M * x := fun x =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2)
  have ht2 : t8M * t8M = 1 := Subtype.ext h88
  have ht1 : t8M ≠ 1 := fun e => h.rG_ne_one (by norm_num) (congrArg Subtype.val e)
  set K : Subgroup M := Subgroup.zpowers t8M with hKdef
  haveI hKn : K.Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g t8M := htc g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers t8M k⟩
  have hK : ∀ x : M, x ∈ K ↔ x = 1 ∨ x = t8M := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h2 : t8M ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
      rw [zpow_eq_zpow_emod k h2]
      rcases Int.emod_two_eq_zero_or_one k with e | e
      · left
        rw [e, zpow_zero]
      · right
        rw [e, zpow_one]
    · rintro (rfl | rfl)
      · exact K.one_mem
      · exact Subgroup.mem_zpowers t8M
  have hzK : zM ∉ K := by
    intro hz
    rcases (hK zM).1 hz with e | e
    · exact h.ne_one_of_isConj_z (IsConj.refl _) (congrArg Subtype.val e)
    · have e' : h.z = h.rG 8 := congrArg Subtype.val e
      have : h.rG 7 = 1 := by rw [← h.z_mul_rG_eight, ← e', hz2]
      exact h.rG_ne_one (by norm_num) this
  haveI : Fintype (M ⧸ K) := Fintype.ofFinite _
  have hzb1 : (zM : M ⧸ K) ≠ 1 := fun e => hzK ((QuotientGroup.eq_one_iff zM).1 e)
  have hzb2 : (zM : M ⧸ K) * (zM : M ⧸ K) = 1 := by
    rw [← QuotientGroup.mk_mul, show zM * zM = 1 from Subtype.ext hz2, QuotientGroup.mk_one]
  have hiso : ∀ gb : M ⧸ K, gb * (zM : M ⧸ K) * gb⁻¹ * (zM : M ⧸ K) =
      (zM : M ⧸ K) * (gb * (zM : M ⧸ K) * gb⁻¹) → gb * (zM : M ⧸ K) * gb⁻¹ = (zM : M ⧸ K) := by
    intro gb hcomm
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have hq : ((g * zM * g⁻¹ * zM : M) : M ⧸ K) = ((zM * (g * zM * g⁻¹) : M) : M ⧸ K) := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hcomm
    rw [QuotientGroup.eq] at hq
    set w : G := (g : G) * h.z * (g : G)⁻¹ with hwdef
    have hwM : w * h.rG 8 = h.rG 8 * w := by
      have hg8 : (g : G) * h.rG 8 = h.rG 8 * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
      have c1 : Commute (g : G) (h.rG 8) := hg8
      have c2 : Commute h.z (h.rG 8) := h.z_comm_eight
      exact ((c1.mul_left c2).mul_left c1.inv_left).eq
    have hwz : IsConj h.z w := isConj_iff.2 ⟨g, rfl⟩
    have hw2 : w * w = 1 := h.sq_eq_one_of_isConj_z hwz
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hzinv : h.z⁻¹ = h.z := inv_eq_of_mul_eq_one_right hz2
    have hgoal : ((g * zM * g⁻¹ : M) : M ⧸ K) = (zM : M ⧸ K) → (g : M ⧸ K) * (zM : M ⧸ K) *
        (g : M ⧸ K)⁻¹ = (zM : M ⧸ K) := fun e => by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using e
    apply hgoal
    rw [QuotientGroup.eq]
    rcases (hK _).1 hq with hd | hd
    ·
      have hd' : (w * h.z)⁻¹ * (h.z * w) = 1 := congrArg Subtype.val hd
      have hwz' : w * h.z = h.z * w := inv_mul_eq_one.1 hd'
      have hwH : w ∈ h.H := Subgroup.mem_centralizer_singleton_iff.2 hwz'
      have hw8 : IsConj h.z (w * h.rG 8) := by
        have e : w * h.rG 8 = (g : G) * h.rG 7 * (g : G)⁻¹ := by
          rw [hwdef, ← h.z_mul_rG_eight]
          have hg8 : (g : G) * h.rG 8 = h.rG 8 * g :=
            Subgroup.mem_centralizer_singleton_iff.1 g.2
          calc (g : G) * h.z * (g : G)⁻¹ * h.rG 8 = (g : G) * h.z * ((g : G)⁻¹ * h.rG 8) := by
                group
            _ = (g : G) * h.z * (h.rG 8 * (g : G)⁻¹) := by
                rw [show (g : G)⁻¹ * h.rG 8 = h.rG 8 * (g : G)⁻¹ by
                  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg8, mul_assoc, mul_inv_cancel,
                    mul_one]]
            _ = (g : G) * (h.z * h.rG 8) * (g : G)⁻¹ := by group
        rw [e]
        exact h.fusesTwo_and_fusesSeven.2.trans (isConj_iff.2 ⟨g, rfl⟩)
      rcases h.eq_of_lam hwH hwM hwz hw8 with e | e
      · apply (hK _).2
        left
        apply Subtype.ext
        show (w)⁻¹ * h.z = 1
        rw [e, hzinv, hz2]
      · apply (hK _).2
        right
        apply Subtype.ext
        show (w)⁻¹ * h.z = h.rG 8
        rw [e, inv_eq_of_mul_eq_one_right h77, h.rG_seven_mul_z]
    ·
      exfalso
      have hd' : (w * h.z)⁻¹ * (h.z * w) = h.rG 8 := congrArg Subtype.val hd
      have hswap : w * h.z * w⁻¹ = h.rG 7 := by
        rw [mul_inv_rev, hwinv, hzinv] at hd'
        rw [← h.z_mul_rG_eight, ← hd', hwinv]
        calc w * h.z * w = (h.z * h.z) * (w * h.z * w) := by rw [hz2, one_mul]
          _ = h.z * (h.z * w * (h.z * w)) := by group
      exact h.not_swap hwM hwz hswap
  obtain ⟨Nb, hNb, hNbodd, hNbz⟩ := CFSG.ZStar.glauberman_zStar (M ⧸ K) (zM : M ⧸ K) hzb1 hzb2
    hiso
  have hNbot : Nb = ⊥ := by
    haveI := hNb
    obtain ⟨Y, hYn, hYcard⟩ := exists_normal_of_quotient ht2 ht1 htc Nb hNbodd
    have hYG : Y.map M.subtype = ⊥ := by
      apply h.eq_bot_of_odd_normal
      · rintro m hm _ ⟨y, hy, rfl⟩
        exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hYn y hy _, rfl⟩
      · rw [Subgroup.card_map_of_injective M.subtype_injective, hYcard]
        exact hNbodd
    have h1 : Nat.card Y = 1 := by
      rw [← Subgroup.card_map_of_injective M.subtype_injective, hYG, Subgroup.card_bot]
    rw [hYcard] at h1
    exact Subgroup.card_eq_one.1 h1
  have hmem := hNbz ((⟨m, hm⟩ : M) : M ⧸ K)
  rw [hNbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  have hq : ((⟨m, hm⟩ * zM * (⟨m, hm⟩ : M)⁻¹ : M) : M ⧸ K) = (zM : M ⧸ K) := by
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hmem
  rw [QuotientGroup.eq] at hq
  rcases (hK _).1 hq with hd | hd
  · left
    have hd' : (m * h.z * m⁻¹)⁻¹ * h.z = 1 := congrArg Subtype.val hd
    exact inv_mul_eq_one.1 hd'
  · right
    have hd' : (m * h.z * m⁻¹)⁻¹ * h.z = h.rG 8 := congrArg Subtype.val hd
    have : m * h.z * m⁻¹ = h.z * (h.rG 8)⁻¹ := by
      rw [← hd']
      group
    rw [this, inv_eq_of_mul_eq_one_right h88, h.z_mul_rG_eight]

theorem card_centralizer_eight :
    Nat.card (Subgroup.centralizer ({h.rG 8} : Set G)) = 1474560 := by
  haveI := h.finite
  set M := Subgroup.centralizer ({h.rG 8} : Set G) with hMdef
  letI := conjActG M
  obtain ⟨u, hu1, hu2⟩ := h.exists_swap_seven
  have huM : u ∈ M := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← h.rG_seven_mul_z]
    calc u * (h.rG 7 * h.z) = (u * h.rG 7 * u⁻¹) * (u * h.z * u⁻¹) * u := by group
      _ = h.z * h.rG 7 * u := by rw [hu1, hu2]
      _ = h.rG 7 * h.z * u := by
          rw [(Subgroup.mem_centralizer_singleton_iff.1 (h.φ.symm (rep 7)).2).symm]
  have horb : MulAction.orbit M h.z = {h.z, h.rG 7} := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rcases h.conj_z_mem m.2 with e | e
      · exact Or.inl e
      · exact Or.inr e
    · rintro (rfl | rfl)
      · exact MulAction.mem_orbit_self _
      · exact ⟨⟨u, huM⟩, hu1⟩
  have hidx : (MulAction.stabilizer M h.z).index = 2 := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_pair h.rG_seven_ne_z.symm]
  have hstab : Nat.card (MulAction.stabilizer M h.z) = 737280 := by
    rw [← h.card_XG]
    refine Nat.card_congr
      { toFun := fun m => ⟨(m : M), Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
          (m : M).2⟩⟩
        invFun := fun x => ⟨⟨x, (Subgroup.mem_inf.1 x.2).2⟩, ?_⟩
        left_inv := fun m => rfl
        right_inv := fun x => rfl }
    · have hm := m.2
      rw [MulAction.mem_stabilizer_iff] at hm
      change ((m : M) : G) * h.z * ((m : M) : G)⁻¹ = h.z at hm
      calc ((m : M) : G) * h.z = ((m : M) : G) * h.z * ((m : M) : G)⁻¹ * (m : M) := by group
        _ = h.z * (m : M) := by rw [hm]
    · rw [MulAction.mem_stabilizer_iff]
      change (x : G) * h.z * (x : G)⁻¹ = h.z
      rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).1,
        mul_inv_cancel_right]
  have := (MulAction.stabilizer M h.z).index_mul_card
  rw [hidx, hstab] at this
  omega

end Co2CentHyp

end CFSG.RankThree.Co2
