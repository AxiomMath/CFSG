module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.QAbelian
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G : Type*} [Group G] [Finite G]

theorem mul_sq_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) * (a * b) = 1 := by
  rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab,
    show a * (a * b) * b = (a * a) * (b * b) by group, ha, hb, one_mul]

theorem fix_pow {W : Set G} {a : G} (ha : ∀ w ∈ W, a * w * a⁻¹ = w) (k : ℕ) :
    ∀ w ∈ W, a ^ k * w * (a ^ k)⁻¹ = w := by
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    rw [pow_succ, show a ^ k * a * w * (a ^ k * a)⁻¹ = a ^ k * (a * w * a⁻¹) * (a ^ k)⁻¹ by group,
      ha w hw, ih w hw]

theorem pm_decomp {W : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {n : ℕ}
    (hn : Nat.card W = 2 * n + 1) {u : G} (hu : u * u = 1) (huW : ∀ w ∈ W, u * w * u⁻¹ ∈ W)
    {w : G} (hw : w ∈ W) :
    (w * (u * w * u⁻¹)) ^ (n + 1) ∈ W ∧ (w * (u * w * u⁻¹)⁻¹) ^ (n + 1) ∈ W ∧
      w = (w * (u * w * u⁻¹)) ^ (n + 1) * (w * (u * w * u⁻¹)⁻¹) ^ (n + 1) ∧
      u * (w * (u * w * u⁻¹)) ^ (n + 1) * u⁻¹ = (w * (u * w * u⁻¹)) ^ (n + 1) ∧
      u * (w * (u * w * u⁻¹)⁻¹) ^ (n + 1) * u⁻¹ = ((w * (u * w * u⁻¹)⁻¹) ^ (n + 1))⁻¹ := by
  have huu : ∀ y, u * (u * y * u⁻¹) * u⁻¹ = y := fun y => by
    rw [show u * (u * y * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ by group, hu]; group
  have hw' := huW w hw
  have hcomm : w * (u * w * u⁻¹) = (u * w * u⁻¹) * w := hWab _ hw _ hw'
  have hsqrt : (w ^ 2) ^ (n + 1) = w := by
    have h1 : w ^ Nat.card W = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard W hw)
    rw [← pow_mul, show 2 * (n + 1) = Nat.card W + 1 by omega, pow_succ, h1, one_mul]
  have hpm : w * (u * w * u⁻¹)⁻¹ ∈ W := W.mul_mem hw (W.inv_mem hw')
  refine ⟨pow_mem (W.mul_mem hw hw') _, pow_mem hpm _, ?_, ?_, ?_⟩
  · have hc' : Commute (w * (u * w * u⁻¹)) (w * (u * w * u⁻¹)⁻¹) :=
      hWab _ (W.mul_mem hw hw') _ hpm
    rw [← hc'.mul_pow]
    have : w * (u * w * u⁻¹) * (w * (u * w * u⁻¹)⁻¹) = w ^ 2 := by
      rw [show w * (u * w * u⁻¹) * (w * (u * w * u⁻¹)⁻¹) =
        w * ((u * w * u⁻¹) * w) * (u * w * u⁻¹)⁻¹ by group, ← hcomm, sq]
      group
    rw [this, hsqrt]
  · rw [← conj_pow, show u * (w * (u * w * u⁻¹)) * u⁻¹ = (u * w * u⁻¹) * (u * (u * w * u⁻¹) * u⁻¹)
      by group, huu, ← hcomm]
  · rw [← conj_pow, show u * (w * (u * w * u⁻¹)⁻¹) * u⁻¹ =
      (u * w * u⁻¹) * (u * (u * w * u⁻¹) * u⁻¹)⁻¹ by group, huu, ← inv_pow, mul_inv_rev, inv_inv]

theorem pm_inv {W : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {n : ℕ} {u e : G}
    (huW : ∀ w ∈ W, u * w * u⁻¹ ∈ W) (heu : e * u = u * e) {w : G} (hw : w ∈ W)
    (hew : e * w * e⁻¹ = w⁻¹) :
    e * (w * (u * w * u⁻¹)) ^ (n + 1) * e⁻¹ = ((w * (u * w * u⁻¹)) ^ (n + 1))⁻¹ ∧
      e * (w * (u * w * u⁻¹)⁻¹) ^ (n + 1) * e⁻¹ = ((w * (u * w * u⁻¹)⁻¹) ^ (n + 1))⁻¹ := by
  have hw' := huW w hw
  have heuw : e * (u * w * u⁻¹) * e⁻¹ = (u * w * u⁻¹)⁻¹ := by
    calc e * (u * w * u⁻¹) * e⁻¹ = (e * u) * w * (e * u)⁻¹ := by group
      _ = (u * e) * w * (u * e)⁻¹ := by rw [heu]
      _ = u * (e * w * e⁻¹) * u⁻¹ := by group
      _ = (u * w * u⁻¹)⁻¹ := by rw [hew]; group
  constructor
  · rw [← conj_pow, show e * (w * (u * w * u⁻¹)) * e⁻¹ = (e * w * e⁻¹) * (e * (u * w * u⁻¹) * e⁻¹)
      by group, hew, heuw, ← inv_pow]
    congr 1
    rw [mul_inv_rev w (u * w * u⁻¹)]
    exact hWab _ (W.inv_mem hw) _ (W.inv_mem hw')
  · rw [← conj_pow, show e * (w * (u * w * u⁻¹)⁻¹) * e⁻¹ =
      (e * w * e⁻¹) * (e * (u * w * u⁻¹) * e⁻¹)⁻¹ by group, hew, heuw, inv_inv, ← inv_pow,
      mul_inv_rev, inv_inv]
    congr 1
    exact hWab _ (W.inv_mem hw) _ hw'

theorem conj_acts_alike {W R : Subgroup G} [hWn : W.Normal] (hRodd : Odd (Nat.card R)) {c : G}
    (hcc : c * c = 1) (hcR : ∀ g : G, c⁻¹ * (g * c * g⁻¹) ∈ R)
    (hRc : ∀ r ∈ R, ∀ w ∈ W, (r * c * r⁻¹ * c⁻¹) * w * (r * c * r⁻¹ * c⁻¹)⁻¹ = w) :
    ∀ g : G, ∀ w ∈ W, (g * c * g⁻¹) * w * (g * c * g⁻¹)⁻¹ = c * w * c⁻¹ := by
  have hcw : ∀ y, c * (c * y * c⁻¹) * c⁻¹ = y := fun y => by
    rw [show c * (c * y * c⁻¹) * c⁻¹ = (c * c) * y * (c * c)⁻¹ by group, hcc]; group
  intro g
  have hr := hcR g
  set r := c⁻¹ * (g * c * g⁻¹) with hrdef
  have hgc : g * c * g⁻¹ = c * r := by rw [hrdef]; group
  have hRc' : ∀ w ∈ W, (r * c) * w * (r * c)⁻¹ = (c * r) * w * (c * r)⁻¹ := by
    intro w hw
    have := hRc r hr _ (hWn.conj_mem w hw (c * r))
    rwa [show (r * c * r⁻¹ * c⁻¹) * ((c * r) * w * (c * r)⁻¹) * (r * c * r⁻¹ * c⁻¹)⁻¹ =
      (r * c) * w * (r * c)⁻¹ by group] at this
  have hcr2 : (c * r) * (c * r) = 1 := by
    rw [← hgc, show g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ by group, hcc]; group
  have hr2 : ∀ w ∈ W, (r * r) * w * (r * r)⁻¹ = w := by
    intro w hw
    have hw' : c * w * c⁻¹ ∈ W := hWn.conj_mem w hw c
    have e1 : (c * r) * ((c * r) * (c * w * c⁻¹) * (c * r)⁻¹) * (c * r)⁻¹ = c * w * c⁻¹ := by
      rw [show (c * r) * ((c * r) * (c * w * c⁻¹) * (c * r)⁻¹) * (c * r)⁻¹ =
        ((c * r) * (c * r)) * (c * w * c⁻¹) * ((c * r) * (c * r))⁻¹ by group, hcr2]
      group
    rw [← hRc' _ hw', show (c * r) * ((r * c) * (c * w * c⁻¹) * (r * c)⁻¹) * (c * r)⁻¹ =
      c * (r * r * (c * (c * w * c⁻¹) * c⁻¹) * (r * r)⁻¹) * c⁻¹ by group, hcw] at e1
    calc r * r * w * (r * r)⁻¹ = c⁻¹ * (c * (r * r * w * (r * r)⁻¹) * c⁻¹) * c := by group
      _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [e1]
      _ = w := by group
  have hrW : ∀ w ∈ W, r * w * r⁻¹ = w := by
    intro w hw
    obtain ⟨k, hk⟩ := exists_pow_sq hRodd hr
    have := fix_pow (W := (W : Set G)) (a := r ^ 2) (fun w hw => by rw [sq]; exact hr2 w hw) k
      w hw
    rwa [hk] at this
  intro w hw
  rw [hgc, show c * r * w * (c * r)⁻¹ = c * (r * w * r⁻¹) * c⁻¹ by group, hrW w hw]

theorem s3_core {W R : Subgroup G} [hWn : W.Normal] (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hWodd : Odd (Nat.card W)) (hmin : ∀ N : Subgroup G, N.Normal → N ≤ W → N = ⊥ ∨ N = W)
    (hRodd : Odd (Nat.card R)) {d : Fin 3 → G} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i)
    (hcR : ∀ g : G, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ R)
    (hRc : ∀ r ∈ R, ∀ w ∈ W, (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹) * w *
      (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ = w)
    (hLA : ∀ i j, i ≠ j → ∀ w ∈ W, (d i * d j) * w * (d i * d j)⁻¹ = w → d i * w * (d i)⁻¹ = w)
    (hS1 : ∃ w ∈ W, d 0 * w * (d 0)⁻¹ ≠ w) :
    (∀ w ∈ W, (d 0 * d 1 * d 2) * w * (d 0 * d 1 * d 2)⁻¹ = w⁻¹) ∧
      ∀ w ∈ W, (d 1 * d 2) * w * (d 1 * d 2)⁻¹ = w → (d 2 * d 0) * w * (d 2 * d 0)⁻¹ = w →
        w = 1 := by
  have hdinv : ∀ i, (d i)⁻¹ = d i := fun i => inv_eq_of_mul_eq_one_right (hd i)
  have hcc : (d 0 * d 1 * d 2) * (d 0 * d 1 * d 2) = 1 :=
    mul_sq_eq_one (mul_sq_eq_one (hd 0) (hd 1) (hdc 0 1)) (hd 2)
      (by rw [mul_assoc, hdc 1 2, ← mul_assoc, hdc 0 2, mul_assoc])
  obtain ⟨c, hcdef⟩ : ∃ c, c = d 0 * d 1 * d 2 := ⟨_, rfl⟩
  rw [← hcdef] at hcc hcR hRc ⊢
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcw : ∀ y, c * (c * y * c⁻¹) * c⁻¹ = y := fun y => by
    rw [show c * (c * y * c⁻¹) * c⁻¹ = (c * c) * y * (c * c)⁻¹ by group, hcc]; group
  have hconjc := conj_acts_alike hRodd hcc hcR hRc
  let N : Subgroup G :=
    { carrier := {w | w ∈ W ∧ c * w * c⁻¹ = w}
      mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, by
        rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group, ha.2, hb.2]⟩
      one_mem' := ⟨W.one_mem, by simp⟩
      inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, by
        rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group, ha.2]⟩ }
  have hNn : N.Normal := ⟨fun n hn g => ⟨hWn.conj_mem n hn.1 g, by
    have := hconjc g⁻¹ n hn.1
    rw [inv_inv, hn.2] at this
    calc c * (g * n * g⁻¹) * c⁻¹ = g * ((g⁻¹ * c * g) * n * (g⁻¹ * c * g)⁻¹) * g⁻¹ := by group
      _ = g * n * g⁻¹ := by rw [this]⟩⟩
  have hdd : ∀ i j, (d i * d j) * (d i * d j) = 1 := fun i j =>
    mul_sq_eq_one (hd i) (hd j) (hdc i j)
  have hdW : ∀ i, ∀ w ∈ W, d i * w * (d i)⁻¹ ∈ W := fun i w hw => hWn.conj_mem w hw _
  have hddW : ∀ i j, ∀ w ∈ W, (d i * d j) * w * (d i * d j)⁻¹ ∈ W := fun i j w hw =>
    hWn.conj_mem w hw _
  have hWodd' := hWodd
  obtain ⟨n, hn⟩ := hWodd'
  have hinv1 : ∀ w ∈ W, w = w⁻¹ → w = 1 := fun w hw h =>
    eq_one_of_mul_self hWodd hw (by nth_rewrite 2 [h]; exact mul_inv_cancel w)
  have hd0 : d 0 = c * (d 2 * d 1) := by
    rw [hcdef, show d 0 * d 1 * d 2 * (d 2 * d 1) = d 0 * d 1 * (d 2 * d 2) * d 1 by group, hd 2,
      mul_one, mul_assoc, hd 1, mul_one]
  have hd1 : d 1 = c * (d 0 * d 2) := by
    rw [hcdef, show d 0 * d 1 * d 2 * (d 0 * d 2) = d 0 * (d 1 * (d 2 * d 0)) * d 2 by group,
      hdc 2 0, show d 0 * (d 1 * (d 0 * d 2)) * d 2 = d 0 * (d 1 * d 0) * (d 2 * d 2) by group,
      hd 2, mul_one, hdc 1 0, ← mul_assoc, hd 0, one_mul]
  have conj2 : ∀ a b w : G, (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := fun a b w => by
    group
  rcases hmin N hNn (fun x hx => hx.1) with hN | hN
  ·
    have hcW : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹ := by
      intro w hw
      have hw' : c * w * c⁻¹ ∈ W := hWn.conj_mem w hw c
      have hx : w * (c * w * c⁻¹) ∈ N := ⟨W.mul_mem hw hw', by
        rw [show c * (w * (c * w * c⁻¹)) * c⁻¹ = (c * w * c⁻¹) * (c * (c * w * c⁻¹) * c⁻¹) by
          group, hcw]
        exact hWab _ hw' _ hw⟩
      rw [hN, mem_bot] at hx
      exact eq_inv_of_mul_eq_one_right hx
    refine ⟨hcW, fun w hw h12 h20 => ?_⟩
    have h0 : d 0 * w * (d 0)⁻¹ = w⁻¹ := by
      rw [hd0, conj2, show d 2 * d 1 = d 1 * d 2 from hdc 2 1, h12, hcW w hw]
    have h1 : d 1 * w * (d 1)⁻¹ = w⁻¹ := by
      rw [hd1, conj2, show d 0 * d 2 = d 2 * d 0 from hdc 0 2, h20, hcW w hw]
    have h01 : (d 0 * d 1) * w * (d 0 * d 1)⁻¹ = w := by
      rw [conj2, h1, show d 0 * w⁻¹ * (d 0)⁻¹ = (d 0 * w * (d 0)⁻¹)⁻¹ by group, h0, inv_inv]
    have := hLA 0 1 (by decide) w hw h01
    rw [h0] at this
    exact hinv1 w hw this.symm
  ·
    exfalso
    have hcfix : ∀ w ∈ W, c * w * c⁻¹ = w := fun w hw => by
      rw [← hN] at hw; exact hw.2
    obtain ⟨w, hw, hmove⟩ := hS1
    apply hmove
    have hu : (d 1 * d 2) * (d 1 * d 2) = 1 := hdd 1 2
    obtain ⟨haW, hbW, hwab, ha, hb⟩ := pm_decomp hWab hn hu (hddW 1 2) hw
    set a := (w * ((d 1 * d 2) * w * (d 1 * d 2)⁻¹)) ^ (n + 1)
    set b := (w * ((d 1 * d 2) * w * (d 1 * d 2)⁻¹)⁻¹) ^ (n + 1)
    have ha1 : d 1 * a * (d 1)⁻¹ = a := hLA 1 2 (by decide) a haW ha
    have ha2 : d 2 * a * (d 2)⁻¹ = a := hLA 2 1 (by decide) a haW (by rw [hdc 2 1]; exact ha)
    have ha0 : d 0 * a * (d 0)⁻¹ = a := by
      rw [hd0, conj2, conj2, ha1, ha2, hcfix a haW]
    have hb0 : d 0 * b * (d 0)⁻¹ = b⁻¹ := by
      rw [hd0, conj2, show d 2 * d 1 = d 1 * d 2 from hdc 2 1, hb, hcfix _ (W.inv_mem hbW)]
    obtain ⟨heW, hfW, hbef, he, hf⟩ := pm_decomp hWab hn (hd 1) (hdW 1) hbW
    obtain ⟨he0, hf0⟩ := pm_inv (n := n) hWab (hdW 1) (hdc 0 1) hbW hb0
    obtain ⟨he12, hf12⟩ := pm_inv (n := n) hWab (hdW 1)
      (by rw [mul_assoc, hdc 2 1])
      hbW hb
    set e := (b * (d 1 * b * (d 1)⁻¹)) ^ (n + 1)
    set f := (b * (d 1 * b * (d 1)⁻¹)⁻¹) ^ (n + 1)
    have he2 : d 2 * e * (d 2)⁻¹ = e⁻¹ := by
      have hd2 : d 2 = d 1 * (d 1 * d 2) := by rw [← mul_assoc, hd 1, one_mul]
      rw [hd2, conj2, he12, show d 1 * e⁻¹ * (d 1)⁻¹ = (d 1 * e * (d 1)⁻¹)⁻¹ by group, he]
    have he02 : (d 0 * d 2) * e * (d 0 * d 2)⁻¹ = e := by
      rw [conj2, he2, show d 0 * e⁻¹ * (d 0)⁻¹ = (d 0 * e * (d 0)⁻¹)⁻¹ by group, he0, inv_inv]
    have he1 : e = 1 := by
      have := hLA 0 2 (by decide) e heW he02
      rw [he0] at this
      exact hinv1 e heW this.symm
    have hf01 : (d 0 * d 1) * f * (d 0 * d 1)⁻¹ = f := by
      rw [conj2, hf, show d 0 * f⁻¹ * (d 0)⁻¹ = (d 0 * f * (d 0)⁻¹)⁻¹ by group, hf0, inv_inv]
    have hf1 : f = 1 := by
      have := hLA 0 1 (by decide) f hfW hf01
      rw [hf0] at this
      exact hinv1 f hfW this.symm
    have hb1 : b = 1 := by rw [hbef, he1, hf1, one_mul]
    rw [hwab, hb1, mul_one, ha0]

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

