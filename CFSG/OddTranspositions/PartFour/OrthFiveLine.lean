module

public import CFSG.OddTranspositions.PartFour.LinePolar
import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

section Model

open TableE1Five

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem exists_norm_eq_one_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 3 ≤ n) : ∃ x, b x x = 1 := by
  obtain ⟨z, -, hz⟩ := exists_aniso_perp hsym hnd (k := 0) (by omega) ![]
    (fun i => i.elim0) (fun i => i.elim0)
  obtain ⟨x, -, hx⟩ := exists_norm_eq_perp hsym hnd hn hz (c := 1) (by decide)
  exact ⟨x, hx⟩

private theorem exists_norm_eq_perp_perp_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {u₁ u₂ : Fin n → ZMod 5}
    (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0) (h₁₂ : b u₁ u₂ = 0) {c : ZMod 5} (hc : c ≠ 0) :
    ∃ t, b t u₁ = 0 ∧ b t u₂ = 0 ∧ b t t = c := by
  obtain ⟨z₁, hz₁u₁, hz₁u₂, hz₁⟩ := exists_aniso_perp₂ hsym hnd (by omega) h₁ h₂ h₁₂
  obtain ⟨z₂, hz₂u₁, hz₂u₂, hz₂z₁, hz₂⟩ := exists_aniso_perp₃ hsym hnd hn h₁ h₂ hz₁ h₁₂
    (by rw [hsym]; exact hz₁u₁) (by rw [hsym]; exact hz₁u₂)
  have key : ∀ a d t : ZMod 5, a ≠ 0 → d ≠ 0 → t ≠ 0 →
      ∃ l m : ZMod 5, l * l * a + m * m * d = t := by decide
  obtain ⟨l, m, hlm⟩ := key _ _ _ hz₁ hz₂ hc
  refine ⟨l • z₁ + m • z₂, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hz₁u₁, hz₂u₁]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hz₁u₂, hz₂u₂]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hz₂z₁, hsym z₁ z₂]
    rw [← hlm]
    ring

private theorem exists_norm_one_perp_not_perp_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {x y : Fin n → ZMod 5}
    (hx : b x x = 1) (hy : b y y = 1) (hxy : y ≠ x ∧ y ≠ -x) :
    ∃ z, b z z = 1 ∧ b z x = 0 ∧ b z y ≠ 0 ∧ y ≠ z ∧ y ≠ -z := by
  by_cases h0 : b y x = 0
  ·
    obtain ⟨t, htx, hty, htt⟩ := exists_norm_eq_perp_perp_five hsym hnd hn (u₁ := x) (u₂ := y)
      (by rw [hx]; decide) (by rw [hy]; decide) (by rw [hsym]; exact h0) (c := 2) (by decide)
    have hyt : b y t = 0 := by rw [hsym]; exact hty
    have hzt : b ((2 : ZMod 5) • y + t) t = 2 := by
      rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hyt, htt]
      decide
    refine ⟨(2 : ZMod 5) • y + t, ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
    · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hy, hyt, hty, htt]
      decide
    · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, h0, htx]
      decide
    · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hy, hty]
      decide
    · have h1 : b y t = b ((2 : ZMod 5) • y + t) t := by rw [← h]
      rw [hyt, hzt] at h1
      exact absurd h1 (by decide)
    · have h1 : b y t = -b ((2 : ZMod 5) • y + t) t := by
        rw [← LinearMap.BilinForm.neg_left, ← h]
      rw [hyt, hzt] at h1
      exact absurd h1 (by decide)
  ·
    have hu : b (y - b y x • x) x = 0 := by
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hx, mul_one, sub_self]
    obtain ⟨z, hz, hzx, hzy⟩ : ∃ z, b z z = 1 ∧ b z x = 0 ∧ b (y - b y x • x) z ≠ 0 := by
      by_contra! hall
      have hy' : y = b y x • x :=
        sub_eq_zero.1 (eq_zero_of_forall_norm_one_perp hsym hnd (by omega) hx hu hall)
      have hc : b y x * b y x = 1 := by
        have h1 := hy
        rw [hy', LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hx] at h1
        linear_combination h1
      have hc' : b y x = 1 ∨ b y x = -1 := by
        revert hc; generalize b y x = c; revert c; decide
      rcases hc' with hc' | hc'
      · exact hxy.1 (by rw [hy', hc', one_smul])
      · exact hxy.2 (by rw [hy', hc', neg_one_smul])
    have hxz : b x z = 0 := by rw [hsym]; exact hzx
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hxz, mul_zero,
      sub_zero] at hzy
    refine ⟨z, hz, hzx, by rwa [hsym], fun h => h0 ?_, fun h => h0 ?_⟩
    · rw [h]; exact hzx
    · rw [h, LinearMap.BilinForm.neg_left, hzx, neg_zero]

private theorem exists_norm_one_inner_eq_one_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {x : Fin n → ZMod 5} (hx : b x x = 1) :
    ∃ y, b y y = 1 ∧ b x y = 1 ∧ y ≠ x := by
  obtain ⟨s, hsx, hs⟩ := exists_norm_eq_perp hsym hnd (by omega) (v := x) (by rw [hx]; decide)
    (c := 1) (by decide)
  obtain ⟨t, htx, hts, ht⟩ := exists_norm_eq_perp_perp_five hsym hnd hn (u₁ := x) (u₂ := s)
    (by rw [hx]; decide) (by rw [hs]; decide) (by rw [hsym]; exact hsx) (c := -1) (by decide)
  have hxs : b x s = 0 := by rw [hsym]; exact hsx
  have hxt : b x t = 0 := by rw [hsym]; exact htx
  have hst : b s t = 0 := by rw [hsym]; exact hts
  refine ⟨x + (s + t), ?_, ?_, fun h => ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hx, hs, ht, hxs, hxt,
      hsx, htx, hst, hts]
    decide
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, hx, hxs, hxt]
    decide
  · have h1 : b (x + (s + t)) s = b x s := by rw [h]
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left, hxs, hs, hts] at h1
    exact absurd h1 (by decide)

private theorem refl_mul_refl_pow_five_of_eq_one (hsym : ∀ x y, b x y = b y x)
    {u w : Fin n → ZMod 5} (hu : b u u = 1) (hw : b w w = 1) (huw : b u w = 1) :
    (refl b u * refl b w) ^ 5 = 1 := by
  have hwu : b w u = 1 := by rw [hsym]; exact huw
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e5 : ∀ x y : Fin n → ZMod 5, refl b x * refl b y * refl b x * refl b y * refl b x =
      refl b (act (refl b x * refl b y) x) := fun x y => by
    rw [← conj_refl ((isomGroup b).mul_mem (refl_mem_isomGroup hsym x)
      (refl_mem_isomGroup hsym y)), _root_.mul_inv_rev, refl_inv, refl_inv]
    group
  have hb : refl b u * refl b w * refl b u * refl b w * refl b u =
      refl b w * refl b u * refl b w * refl b u * refl b w := by
    rw [e5 u w, e5 w u]
    congr 1
    simp only [act_mul, act_refl hu, act_refl hw, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hu, hw, hwu, huw]
    linear_combination (norm := module) h5 • (u - w)
  calc (refl b u * refl b w) ^ 5 = (refl b u * refl b w * refl b u * refl b w * refl b u) *
        (refl b w * refl b u * refl b w * refl b u * refl b w) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [hb, e5 w u, refl_mul_self]

private theorem mk_refl_eq_mk_refl_iff_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {u w : Fin n → ZMod 5}
    (hu : b u u = 1) (hw : b w w = 1) {g h : reflGroup b}
    (hg : (g : GL (Fin n) (ZMod 5)) = refl b u) (hh : (h : GL (Fin n) (ZMod 5)) = refl b w) :
    (QuotientGroup.mk g : reflGroup b ⧸ Subgroup.center (reflGroup b)) = QuotientGroup.mk h ↔
      w = u ∨ w = -u := by
  rw [QuotientGroup.eq]
  constructor
  · intro hz
    rcases coe_eq_of_mem_center hsym hnd hn hu hz with h1 | h1
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one, hg, hh] at h1
      exact (refl_eq_refl_iff hu hw).1 h1
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, mul_neg_one, hg, hh] at h1
      exact absurd h1 (refl_ne_neg_refl (by omega) u w)
  · intro h2
    have hgh : g = h := Subtype.ext (by
      rw [hg, hh]
      rcases h2 with h2 | h2
      · rw [h2]
      · rw [h2, refl_neg])
    rw [hgh, inv_mul_cancel]
    exact Subgroup.one_mem _

private theorem commute_mk_refl_iff_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {u w : Fin n → ZMod 5}
    (hu : b u u = 1) (hw : b w w = 1) {g h : reflGroup b}
    (hg : (g : GL (Fin n) (ZMod 5)) = refl b u) (hh : (h : GL (Fin n) (ZMod 5)) = refl b w) :
    Commute (QuotientGroup.mk g : reflGroup b ⧸ Subgroup.center (reflGroup b))
      (QuotientGroup.mk h) ↔ b u w = 0 ∨ w = u ∨ w = -u := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  constructor
  · intro hc
    have hz : (g * h)⁻¹ * (h * g) ∈ Subgroup.center (reflGroup b) := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hc.eq
    rcases coe_eq_of_mem_center hsym hnd hn hu hz with h1 | h1 <;>
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, hg, hh] at h1
    · rw [inv_mul_eq_one] at h1
      rcases act_eq_or_of_commute (refl_mem_isomGroup hsym w) hu h1 with h2 | h2 <;>
        rw [act_refl hw] at h2
      · left
        have h3 : b (u + (-2 * b u w) • w) w = b u w := by rw [h2]
        rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw] at h3
        revert h3; generalize b u w = c; revert c; decide
      · right
        have h3 : u = b u w • w := by
          linear_combination (norm := module) (3 : ZMod 5) • h2 + h5 • (b u w • w - u)
        have hc : b u w * b u w = 1 := by
          have h4 := hu
          rw [h3, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw] at h4
          linear_combination h4
        have hc' : b u w = 1 ∨ b u w = -1 := by
          revert hc; generalize b u w = c; revert c; decide
        rcases hc' with hc' | hc'
        · left; rw [h3, hc', one_smul]
        · right; rw [h3, hc', neg_one_smul, neg_neg]
    · exfalso
      rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at h1
      apply refl_ne_neg_refl (b := b) (by omega) u (act (refl b w) u)
      rw [← conj_refl (refl_mem_isomGroup hsym w), refl_inv, h1, neg_mul, mul_assoc,
        refl_mul_self w, mul_one]
  · intro h2
    have hgh : g * h = h * g := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hg, hh]
      rcases h2 with h2 | h2 | h2
      · exact refl_comm_of_perp hsym h2
      · rw [h2]
      · rw [h2, refl_neg]
    show (QuotientGroup.mk g : reflGroup b ⧸ Subgroup.center (reflGroup b)) * QuotientGroup.mk h =
      QuotientGroup.mk h * QuotientGroup.mk g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hgh]

private theorem orderOf_mk_refl_mul_refl_eq_five (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {u w : Fin n → ZMod 5}
    (hu : b u u = 1) (hw : b w w = 1) (huw : b u w = 1) (hne : w ≠ u) {g h : reflGroup b}
    (hg : (g : GL (Fin n) (ZMod 5)) = refl b u) (hh : (h : GL (Fin n) (ZMod 5)) = refl b w) :
    orderOf (QuotientGroup.mk (g * h) : reflGroup b ⧸ Subgroup.center (reflGroup b)) = 5 := by
  refine orderOf_eq_prime (hp := ⟨by norm_num⟩) ?_ ?_
  · have h5 : (g * h) ^ 5 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul, hg, hh, Subgroup.coe_one]
      exact refl_mul_refl_pow_five_of_eq_one hsym hu hw huw)
    rw [← QuotientGroup.mk_pow, h5, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff]
    intro hz
    rcases coe_eq_of_mem_center hsym hnd hn hu hz with h1 | h1 <;>
      rw [Subgroup.coe_mul, hg, hh] at h1
    · have h2 : refl b u = refl b w := by
        calc refl b u = refl b u * (refl b w * refl b w) := by rw [refl_mul_self w, mul_one]
          _ = refl b w := by rw [← mul_assoc, h1, one_mul]
      rcases (refl_eq_refl_iff hu hw).1 h2 with h3 | h3
      · exact hne h3
      · rw [h3, LinearMap.BilinForm.neg_right, hu] at huw
        exact absurd huw (by decide)
    · have h2 : refl b w = -refl b u := by
        calc refl b w = refl b u * (refl b u * refl b w) := by
              rw [← mul_assoc, refl_mul_self u, one_mul]
          _ = -refl b u := by rw [h1, mul_neg_one]
      exact refl_ne_neg_refl (by omega) u w h2

private theorem exists_reflModel_five {X : Type} [Group X] {E : Set X} (hn : 4 ≤ n)
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    ∃ ρ : (Fin n → ZMod 5) → X, (∀ g, g ∈ E ↔ ∃ v, b v v = 1 ∧ ρ v = g) ∧
      (∀ v, ρ (-v) = ρ v) ∧
      (∀ u w, b u u = 1 → b w w = 1 → (ρ u = ρ w ↔ w = u ∨ w = -u)) ∧
      (∀ u w, b u u = 1 → b w w = 1 → (Commute (ρ u) (ρ w) ↔ b u w = 0 ∨ w = u ∨ w = -u)) ∧
      (∀ u w, b u u = 1 → b w w = 1 → b u w = 1 → w ≠ u → orderOf (ρ u * ρ w) = 5) := by
  obtain ⟨φ, hφ⟩ := hM
  obtain ⟨r, hr⟩ : ∃ r : (Fin n → ZMod 5) → reflGroup b,
      ∀ v, (r v : GL (Fin n) (ZMod 5)) = refl b v :=
    ⟨fun v => ⟨refl b v, refl_mem_reflGroup v⟩, fun _ => rfl⟩
  have hE : ∀ g, g ∈ E ↔ ∃ v, b v v = 1 ∧ φ.symm (QuotientGroup.mk (r v)) = g := by
    intro g
    rw [hφ g]
    constructor
    · rintro ⟨h, hh, hgh⟩
      obtain ⟨v, hv, hvh⟩ := mem_reflSet_iff.1 hh
      have hrv : r v = h := Subtype.ext ((hr v).trans hvh)
      exact ⟨v, hv, by rw [hrv, ← hgh, MulEquiv.symm_apply_apply]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨r v, ?_, MulEquiv.apply_symm_apply _ _⟩
      rw [hr v]
      exact refl_mem_reflSet hv
  have hneg : ∀ v, φ.symm (QuotientGroup.mk (r (-v))) = φ.symm (QuotientGroup.mk (r v)) := by
    intro v
    have hrv : r (-v) = r v := Subtype.ext (by rw [hr, hr, refl_neg])
    rw [hrv]
  have hEq : ∀ u w, b u u = 1 → b w w = 1 → (φ.symm (QuotientGroup.mk (r u)) =
      φ.symm (QuotientGroup.mk (r w)) ↔ w = u ∨ w = -u) := fun u w hu hw =>
    φ.symm.injective.eq_iff.trans (mk_refl_eq_mk_refl_iff_five hsym hnd hn hu hw (hr u) (hr w))
  have hComm : ∀ u w, b u u = 1 → b w w = 1 → (Commute (φ.symm (QuotientGroup.mk (r u)))
      (φ.symm (QuotientGroup.mk (r w))) ↔ b u w = 0 ∨ w = u ∨ w = -u) := fun u w hu hw =>
    (commute_map_iff φ.symm.injective).trans
      (commute_mk_refl_iff_five hsym hnd hn hu hw (hr u) (hr w))
  have hOrd : ∀ u w, b u u = 1 → b w w = 1 → b u w = 1 → w ≠ u →
      orderOf (φ.symm (QuotientGroup.mk (r u)) * φ.symm (QuotientGroup.mk (r w))) = 5 := by
    intro u w hu hw huw hne
    rw [← map_mul φ.symm, MulEquiv.orderOf_eq, ← QuotientGroup.mk_mul]
    exact orderOf_mk_refl_mul_refl_eq_five hsym hnd hn hu hw huw hne (hr u) (hr w)
  exact ⟨fun v => φ.symm (QuotientGroup.mk (r v)), hE, hneg, hEq, hComm, hOrd⟩

private theorem perpMem_ne_of_reflModel_five {X : Type} [Group X] {E : Set X} (hn : 4 ≤ n)
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {ρ : (Fin n → ZMod 5) → X} (hE : ∀ g, g ∈ E ↔ ∃ v, b v v = 1 ∧ ρ v = g)
    (hComm : ∀ u w, b u u = 1 → b w w = 1 → (Commute (ρ u) (ρ w) ↔ b u w = 0 ∨ w = u ∨ w = -u))
    {x y : Fin n → ZMod 5} (hx : b x x = 1) (hy : b y y = 1) (hxy : y ≠ x ∧ y ≠ -x) :
    perpMem E (ρ x) ≠ perpMem E (ρ y) := by
  intro hperp
  obtain ⟨z, hz, hzx, hzy, hyz, hyz'⟩ :=
    exists_norm_one_perp_not_perp_five hsym hnd hn hx hy hxy
  have h1 : ρ z ∈ perpMem E (ρ x) := ⟨(hE _).2 ⟨z, hz, rfl⟩, (hComm z x hz hx).2 (Or.inl hzx)⟩
  rw [hperp] at h1
  rcases (hComm z y hz hy).1 h1.2 with h | h | h
  · exact hzy h
  · exact hyz h
  · exact hyz' h

end Model

theorem exists_lineMem_ncard_le_four_of_fischerCentralQuotientModel_five {X : Type} [Group X]
    {E : Set X} {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    ∃ v ∈ E, ∃ w ∈ E, Commute v w ∧ perpMem E v ≠ perpMem E w ∧
      (perpMem E '' lineMem E v w).ncard ≤ 4 := by
  obtain ⟨ρ, hE, hneg, -, hComm, -⟩ := exists_reflModel_five hn hsym hnd hM
  obtain ⟨x, hx⟩ := exists_norm_eq_one_five hsym hnd (by omega)
  obtain ⟨y, hyx, hy⟩ := TableE1Five.exists_norm_eq_perp hsym hnd (by omega) (v := x)
    (by rw [hx]; decide) (c := 1) (by decide)
  have hxy : b x y = 0 := by rw [hsym]; exact hyx
  have hmemE : ∀ v, b v v = 1 → ρ v ∈ E := fun v hv => (hE _).2 ⟨v, hv, rfl⟩
  have hxyc : Commute (ρ x) (ρ y) := (hComm x y hx hy).2 (Or.inl hxy)
  have hin : ∀ s, b s s = 1 → b s x = 0 → b s y = 0 →
      ρ s ∈ perpMem E (ρ x) ∩ perpMem E (ρ y) := fun s hs hsx hsy =>
    ⟨⟨hmemE s hs, (hComm s x hs hx).2 (Or.inl hsx)⟩, ⟨hmemE s hs, (hComm s y hs hy).2 (Or.inl hsy)⟩⟩
  have hxin : ρ x ∈ perpMem E (ρ x) ∩ perpMem E (ρ y) :=
    ⟨⟨hmemE x hx, Commute.refl _⟩, ⟨hmemE x hx, hxyc⟩⟩
  have hyin : ρ y ∈ perpMem E (ρ x) ∩ perpMem E (ρ y) :=
    ⟨⟨hmemE y hy, hxyc.symm⟩, ⟨hmemE y hy, Commute.refl _⟩⟩
  have hperpL : ∀ s v, b s s = 1 → b v v = 1 → ρ s ∈ lineMem E (ρ x) (ρ y) →
      ρ v ∈ perpMem E (ρ x) ∩ perpMem E (ρ y) → ρ s ≠ ρ v → b s v = 0 := by
    intro s v hs hv hL hvin hne
    rcases (hComm v s hv hs).1 (hL.2 hvin).2 with h | h | h
    · rw [hsym]; exact h
    · exact absurd (by rw [h]) hne
    · exact absurd (by rw [h, hneg]) hne
  have hmemL : ∀ g ∈ lineMem E (ρ x) (ρ y), g ≠ ρ x → g ≠ ρ y →
      ∃ s, b s s = 1 ∧ ρ s = g ∧ b s x = 0 ∧ b s y = 0 := by
    intro g hg hgx hgy
    obtain ⟨s, hs, rfl⟩ := (hE g).1 hg.1
    exact ⟨s, hs, rfl, hperpL s x hs hx hg hxin hgx, hperpL s y hs hy hg hyin hgy⟩
  have hthree : ∀ s₁ s₂ s₃ : Fin n → ZMod 5, b s₁ s₁ = 1 → b s₂ s₂ = 1 → b s₃ s₃ = 1 →
      b s₁ x = 0 → b s₁ y = 0 → b s₂ x = 0 → b s₂ y = 0 → b s₃ x = 0 → b s₃ y = 0 →
      ρ s₁ ∈ lineMem E (ρ x) (ρ y) → ρ s₂ ∈ lineMem E (ρ x) (ρ y) →
      ρ s₃ ∈ lineMem E (ρ x) (ρ y) → ρ s₁ = ρ s₂ ∨ ρ s₁ = ρ s₃ ∨ ρ s₂ = ρ s₃ := by
    intro s₁ s₂ s₃ hs₁ hs₂ hs₃ hs₁x hs₁y hs₂x hs₂y hs₃x hs₃y hL₁ hL₂ hL₃
    by_contra! hne
    obtain ⟨h12, h13, h23⟩ := hne
    have o21 : b s₂ s₁ = 0 := hperpL s₂ s₁ hs₂ hs₁ hL₂ (hin s₁ hs₁ hs₁x hs₁y) (Ne.symm h12)
    have o31 : b s₃ s₁ = 0 := hperpL s₃ s₁ hs₃ hs₁ hL₃ (hin s₁ hs₁ hs₁x hs₁y) (Ne.symm h13)
    have o32 : b s₃ s₂ = 0 := hperpL s₃ s₂ hs₃ hs₂ hL₃ (hin s₂ hs₂ hs₂x hs₂y) (Ne.symm h23)
    have o12 : b s₁ s₂ = 0 := by rw [hsym]; exact o21
    have o13 : b s₁ s₃ = 0 := by rw [hsym]; exact o31
    have o23 : b s₂ s₃ = 0 := by rw [hsym]; exact o32
    obtain ⟨t, ht⟩ : ∃ t, t = (2 : ZMod 5) • s₁ + s₂ + s₃ := ⟨_, rfl⟩
    have htt : b t t = 1 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hs₁, hs₂, hs₃, o12, o13,
        o23, o21, o31, o32]
      decide
    have htx : b t x = 0 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hs₁x, hs₂x,
        hs₃x]
      decide
    have hty : b t y = 0 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hs₁y, hs₂y,
        hs₃y]
      decide
    have hts₁ : b t s₁ = 2 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hs₁, o21, o31]
      decide
    have hts₂ : b t s₂ = 1 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, o12, hs₂, o32]
      decide
    rcases (hComm t s₁ htt hs₁).1 (hL₁.2 (hin t htt htx hty)).2 with h | h | h
    · rw [hts₁] at h
      exact absurd h (by decide)
    · have h1 : b s₁ s₂ = b t s₂ := by rw [h]
      rw [o12, hts₂] at h1
      exact absurd h1 (by decide)
    · have h1 : b s₁ s₂ = -b t s₂ := by rw [h, LinearMap.BilinForm.neg_left]
      rw [o12, hts₂] at h1
      exact absurd h1 (by decide)
  obtain ⟨a, c, hac⟩ : ∃ a c : X, ∀ g ∈ lineMem E (ρ x) (ρ y),
      g = ρ x ∨ g = ρ y ∨ g = a ∨ g = c := by
    by_contra! hcon
    obtain ⟨g₁, hg₁, h1x, h1y, -, -⟩ := hcon (ρ x) (ρ x)
    obtain ⟨g₂, hg₂, h2x, h2y, h21, -⟩ := hcon g₁ g₁
    obtain ⟨g₃, hg₃, h3x, h3y, h31, h32⟩ := hcon g₁ g₂
    obtain ⟨s₁, hs₁, rfl, hs₁x, hs₁y⟩ := hmemL g₁ hg₁ h1x h1y
    obtain ⟨s₂, hs₂, rfl, hs₂x, hs₂y⟩ := hmemL g₂ hg₂ h2x h2y
    obtain ⟨s₃, hs₃, rfl, hs₃x, hs₃y⟩ := hmemL g₃ hg₃ h3x h3y
    rcases hthree s₁ s₂ s₃ hs₁ hs₂ hs₃ hs₁x hs₁y hs₂x hs₂y hs₃x hs₃y hg₁ hg₂ hg₃ with h | h | h
    · exact h21 h.symm
    · exact h31 h.symm
    · exact h32 h.symm
  refine ⟨ρ x, hmemE x hx, ρ y, hmemE y hy, hxyc,
    perpMem_ne_of_reflModel_five hn hsym hnd hE hComm hx hy ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [h, hx] at hxy
    exact absurd hxy (by decide)
  · rw [h, LinearMap.BilinForm.neg_right, hx] at hxy
    exact absurd hxy (by decide)
  · have hsub : perpMem E '' lineMem E (ρ x) (ρ y) ⊆
        {perpMem E (ρ x), perpMem E (ρ y), perpMem E a, perpMem E c} := by
      rintro _ ⟨g, hg, rfl⟩
      rcases hac g hg with h | h | h | h <;> simp [h]
    have h1 := Set.ncard_insert_le (perpMem E (ρ x)) {perpMem E (ρ y), perpMem E a, perpMem E c}
    have h2 := Set.ncard_insert_le (perpMem E (ρ y)) {perpMem E a, perpMem E c}
    have h3 := Set.ncard_insert_le (perpMem E a) {perpMem E c}
    rw [Set.ncard_singleton] at h3
    have h4 := Set.ncard_le_ncard hsub
    omega

theorem Vmem_eq_singleton_of_fischerCentralQuotientModel_five {X : Type} [Group X]
    {E : Set X} {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    ∀ v ∈ E, Vmem E v = {v} := by
  obtain ⟨ρ, hE, -, hEq, hComm, -⟩ := exists_reflModel_five hn hsym hnd hM
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (hE v).1 hv
  ext g
  constructor
  · rintro ⟨hg, hperp⟩
    obtain ⟨y, hy, rfl⟩ := (hE g).1 hg
    rw [Set.mem_singleton_iff, hEq y x hy hx]
    by_contra hne
    exact perpMem_ne_of_reflModel_five hn hsym hnd hE hComm hy hx (not_or.1 hne) hperp
  · intro hg
    rw [Set.mem_singleton_iff.1 hg]
    exact mem_Vmem_self hv

theorem exists_orderOf_mul_eq_five_of_fischerCentralQuotientModel_five {X : Type} [Group X]
    {E : Set X} {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    ∃ u ∈ E, ∃ w ∈ E, orderOf (u * w) = 5 := by
  obtain ⟨ρ, hE, -, -, -, hOrd⟩ := exists_reflModel_five hn hsym hnd hM
  obtain ⟨x, hx⟩ := exists_norm_eq_one_five hsym hnd (by omega)
  obtain ⟨y, hy, hxy, hne⟩ := exists_norm_one_inner_eq_one_five hsym hnd hn hx
  exact ⟨ρ x, (hE _).2 ⟨x, hx, rfl⟩, ρ y, (hE _).2 ⟨y, hy, rfl⟩, hOrd x y hx hy hxy hne⟩

end CFSG.OddTranspositions.PartFour
