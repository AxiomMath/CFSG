module

public import CFSG.Quasithin.Background.Harris.R1.QbetaVert

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert
open scoped commutatorElement

structure QD {G : Type*} [Group G] (P S Q W Z M D : Subgroup G) (g y z : G) : Prop where
  vh : Vert.Hyp P S Q W Z M
  hS2 : IsPGroup 2 S
  hMS : M ≤ S
  hg : g ∈ P
  hyg : y ∈ conjSub g S
  hyS : y ∉ S
  hgg : g * g ∈ S
  hzZ : z ∈ Z
  hz1 : z ≠ 1
  hZcases : ∀ x ∈ Z, x = 1 ∨ x = z
  hZZ : Z ⊓ conjSub g Z = ⊥
  hSZ : S ≤ Subgroup.centralizer (Z : Set G)
  hsqW : ∀ w ∈ W, w * w ∈ Z
  hVab : ∀ a ∈ Z ⊔ conjSub g Z, ∀ b ∈ Z ⊔ conjSub g Z, a * b = b * a
  hVN : P ≤ Subgroup.normalizer ((Z ⊔ conjSub g Z : Subgroup G) : Set G)
  hQV : ∀ s ∈ S, (∀ v ∈ Z ⊔ conjSub g Z, s * v = v * s) → s ∈ Q
  hVQ : ∀ v ∈ Z ⊔ conjSub g Z, ∀ q ∈ Q, q * v = v * q
  hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Z
  hD : D ≤ M
  hDc : ∀ d ∈ D, ∀ w ∈ W, d * w = w * d
  hDW : D ⊓ W ≤ Z
  hDS : S ≤ Subgroup.normalizer (D : Set G)
  hMWD : ∀ m ∈ M, ∃ w ∈ W, ∃ d ∈ D, m = w * d

namespace QD

variable {G : Type*} [Group G] {P S Q W Z M D : Subgroup G} {g y z : G}
variable (h : QD P S Q W Z M D g y z)
include h

theorem conj_cases {x : G} (hx : x ∈ conjSub g Z) : x = 1 ∨ x = g * z * g⁻¹ := by
  have hx' : g⁻¹ * x * g ∈ Z := mem_conjSub.mp hx
  rcases h.hZcases _ hx' with h1 | h1
  · left
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]
    group
  · right
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]

theorem V_le_W : Z ⊔ conjSub g Z ≤ W :=
  sup_le (VertT.Z_le_W h.vh) (h.vh.zw g h.hg)

theorem V_le_Q : Z ⊔ conjSub g Z ≤ Q := fun v hv =>
  h.hQV v (h.vh.ws (h.V_le_W hv)) (fun v' hv' => h.hVab v hv v' hv')

theorem z_sq : z * z = 1 := by
  rcases h.hZcases (z * z) (Z.mul_mem h.hzZ h.hzZ) with h1 | h1
  · exact h1
  · exact absurd (mul_eq_right.mp h1) h.hz1

theorem zg_mem : g * z * g⁻¹ ∈ conjSub g Z := mul_mem_conjSub h.hzZ

theorem z_comm_zg : z * (g * z * g⁻¹) = (g * z * g⁻¹) * z :=
  h.hVab z (Subgroup.mem_sup_left h.hzZ) _ (Subgroup.mem_sup_right h.zg_mem)

theorem zg_sq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
  calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [h.z_sq]; group

theorem V_cases {v : G} (hv : v ∈ Z ⊔ conjSub g Z) :
    v = 1 ∨ v = z ∨ v = g * z * g⁻¹ ∨ v = z * (g * z * g⁻¹) := by
  set z' := g * z * g⁻¹ with hz'
  have hzz : z * z' = z' * z := h.z_comm_zg
  have hz2 : z * z = 1 := h.z_sq
  have hz'2 : z' * z' = 1 := h.zg_sq
  have p1 : z * (z * z') = z' := by rw [← mul_assoc, hz2, one_mul]
  have p2 : z' * z = z * z' := hzz.symm
  have p3 : z' * (z * z') = z := by
    rw [← mul_assoc, p2, mul_assoc, hz'2, mul_one]
  have p4 : (z * z') * z = z' := by rw [mul_assoc, ← hzz, ← mul_assoc, hz2, one_mul]
  have p5 : (z * z') * z' = z := by rw [mul_assoc, hz'2, mul_one]
  have p6 : (z * z') * (z * z') = 1 := by
    calc (z * z') * (z * z') = ((z * z') * z) * z' := by simp only [mul_assoc]
      _ = z' * z' := by rw [p4]
      _ = 1 := hz'2
  let K0 : Subgroup G :=
    { carrier := {v | v = 1 ∨ v = z ∨ v = z' ∨ v = z * z'}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
        · simp
        · simp
        · simp
        · simp
        · simp
        · left; exact hz2
        · right; right; right; rfl
        · right; right; left; exact p1
        · simp
        · right; right; right; exact p2
        · left; exact hz'2
        · right; left; exact p3
        · simp
        · right; right; left; exact p4
        · right; left; exact p5
        · left; exact p6
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right hz2
        · right; right; left; exact inv_eq_of_mul_eq_one_right hz'2
        · right; right; right; exact inv_eq_of_mul_eq_one_right p6 }
  have hZ : Z ≤ K0 := fun x hx => by
    rcases h.hZcases x hx with h1 | h1
    · left; exact h1
    · right; left; exact h1
  have hZg : conjSub g Z ≤ K0 := fun x hx => by
    rcases h.conj_cases hx with h1 | h1
    · left; exact h1
    · right; right; left; exact h1
  exact (sup_le hZ hZg) hv

theorem inv_mul_mem_Q {a b : G} (ha : a ∈ S) (hb : b ∈ S) (haQ : a ∉ Q) (hbQ : b ∉ Q) :
    a⁻¹ * b ∈ Q := by
  have h2 : (Q.subgroupOf S).index = 2 := h.vh.q2
  obtain ⟨a0, ha0⟩ := Subgroup.index_eq_two_iff.mp h2
  have e1 := ha0 ⟨a, ha⟩
  have e2 := ha0 ⟨b, hb⟩
  have h1 : a * (a0 : G) ∈ Q := by
    rcases e1 with ⟨h1, -⟩ | ⟨h1, h1'⟩
    · exact h1
    · exact absurd h1 haQ
  have h1' : b * (a0 : G) ∈ Q := by
    rcases e2 with ⟨h1, -⟩ | ⟨h1, h1'⟩
    · exact h1
    · exact absurd h1 hbQ
  have h3 : (b * (a0 : G)) * (a * (a0 : G))⁻¹ ∈ Q := Q.mul_mem h1' (Q.inv_mem h1)
  have e : b * (a0 : G) * (a * (a0 : G))⁻¹ = b * a⁻¹ := by group
  rw [e] at h3
  have hN : a⁻¹ ∈ Subgroup.normalizer (Q : Set G) := h.vh.qn (h.vh.sp (S.inv_mem ha))
  have := (Subgroup.mem_normalizer_iff.mp hN (b * a⁻¹)).mp h3
  have e' : a⁻¹ * (b * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * b := by group
  rw [e'] at this
  exact this

theorem mem_V_of_mem_center {x : G} (hxQ : x ∈ Q) (hxc : ∀ q ∈ Q, q * x = x * q)
    (hx2 : x * x = 1) : x ∈ Z ⊔ conjSub g Z := by
  have hVQ' := h.V_le_Q
  have hxM : x ∈ M := by
    refine h.vh.b1 x hxQ (fun w hw => ?_)
    have e : x * w * x⁻¹ * w⁻¹ = 1 := by
      rw [(hxc w (Subgroup.mem_inf.mp hw).2).symm]
      group
    rw [e]
    exact Z.one_mem
  obtain ⟨w0, hw0W, hw0Q⟩ := IsConcreteLE.not_le_iff_exists.mp h.vh.wq
  have hw0S : w0 ∈ S := h.vh.ws hw0W
  have hxS : x ∈ S := h.vh.qs hxQ
  have hcZ : x * w0 * x⁻¹ * w0⁻¹ ∈ Z := by
    have := h.vh.mw (Subgroup.commutator_mem_commutator hxM hw0W)
    rwa [commutatorElement_def] at this
  have hcent : ∀ u : G, (∀ q ∈ Q, q * u = u * q) → u * w0 = w0 * u →
      ∀ s ∈ S, u * s = s * u := by
    intro u hu hw s hs
    by_cases hsQ : s ∈ Q
    · exact (hu s hsQ).symm
    · have hq : w0⁻¹ * s ∈ Q := h.inv_mul_mem_Q hw0S hs hw0Q hsQ
      have e : s = w0 * (w0⁻¹ * s) := by group
      rw [e]
      calc u * (w0 * (w0⁻¹ * s)) = (u * w0) * (w0⁻¹ * s) := by rw [mul_assoc]
        _ = (w0 * u) * (w0⁻¹ * s) := by rw [hw]
        _ = w0 * (u * (w0⁻¹ * s)) := by rw [mul_assoc]
        _ = w0 * ((w0⁻¹ * s) * u) := by rw [← hu _ hq]
        _ = (w0 * (w0⁻¹ * s)) * u := (mul_assoc _ _ _).symm
  rcases h.hZcases _ hcZ with hc1 | hcz
  ·
    have hxw : x * w0 = w0 * x := by
      calc x * w0 = (x * w0 * x⁻¹ * w0⁻¹) * (w0 * x) := by group
        _ = w0 * x := by rw [hc1, one_mul]
    have hxZ : x ∈ Z := h.hZS x hxS
      (hcent x (fun q hq => hxc q hq) hxw) hx2
    exact Subgroup.mem_sup_left hxZ
  · set z' := g * z * g⁻¹ with hz'
    have hz'V : z' ∈ Z ⊔ conjSub g Z := Subgroup.mem_sup_right h.zg_mem
    have hzV : z ∈ Z ⊔ conjSub g Z := Subgroup.mem_sup_left h.hzZ
    have hz'Q : z' ∈ Q := hVQ' hz'V
    have hzQ : z ∈ Q := hVQ' hzV
    have hzw : z * w0 = w0 * z :=
      Subgroup.mem_centralizer_iff.mp (h.hSZ hw0S) z h.hzZ
    have hz2 : z * z = 1 := h.z_sq
    have hz'2 : z' * z' = 1 := h.zg_sq
    have hzz : z * z' = z' * z := h.z_comm_zg
    have huV : w0 * z' * w0⁻¹ ∈ Z ⊔ conjSub g Z :=
      (Subgroup.mem_normalizer_iff.mp (h.hVN (h.vh.sp hw0S)) z').mp hz'V
    have hz'1 : z' ≠ 1 := by
      intro h1
      apply h.hz1
      have : z = g⁻¹ * z' * g := by rw [hz']; group
      rw [this, h1]
      group
    have hu1 : w0 * z' * w0⁻¹ ≠ 1 := by
      intro h1
      apply hz'1
      have : z' = w0⁻¹ * (w0 * z' * w0⁻¹) * w0 := by group
      rw [this, h1]
      group
    have hu2 : w0 * z' * w0⁻¹ ≠ z' := by
      intro h1
      apply hw0Q
      refine h.hQV w0 hw0S (fun v hv => ?_)
      rcases h.V_cases hv with h2 | h2 | h2 | h2
      · rw [h2]; simp
      · rw [h2]; exact hzw.symm
      · rw [h2]
        calc w0 * z' = (w0 * z' * w0⁻¹) * w0 := by group
          _ = z' * w0 := by rw [h1]
      · rw [h2]
        have e1 : w0 * z' = z' * w0 := by
          calc w0 * z' = (w0 * z' * w0⁻¹) * w0 := by group
            _ = z' * w0 := by rw [h1]
        calc w0 * (z * z') = (w0 * z) * z' := by rw [mul_assoc]
          _ = (z * w0) * z' := by rw [hzw]
          _ = z * (w0 * z') := by rw [mul_assoc]
          _ = z * (z' * w0) := by rw [e1]
          _ = (z * z') * w0 := (mul_assoc _ _ _).symm
    have hu3 : w0 * z' * w0⁻¹ ≠ z := by
      intro h1
      have h2 : z' = z := by
        have : z' = w0⁻¹ * (w0 * z' * w0⁻¹) * w0 := by group
        rw [this, h1]
        calc w0⁻¹ * z * w0 = w0⁻¹ * (z * w0) := by rw [mul_assoc]
          _ = w0⁻¹ * (w0 * z) := by rw [hzw]
          _ = z := by group
      have hzg : z ∈ Z ⊓ conjSub g Z := ⟨h.hzZ, by rw [← h2]; exact h.zg_mem⟩
      rw [h.hZZ, Subgroup.mem_bot] at hzg
      exact h.hz1 hzg
    have hu : w0 * z' * w0⁻¹ = z * z' := by
      rcases h.V_cases huV with h1 | h1 | h1 | h1
      · exact absurd h1 hu1
      · exact absurd h1 hu3
      · exact absurd h1 hu2
      · exact h1
    have hwx : w0 * x * w0⁻¹ = z * x := by
      have h1 : x * w0 * x⁻¹ * w0⁻¹ = z := hcz
      have h2 : w0 * x⁻¹ * w0⁻¹ = x⁻¹ * z := by
        calc w0 * x⁻¹ * w0⁻¹ = x⁻¹ * (x * w0 * x⁻¹ * w0⁻¹) := by group
          _ = x⁻¹ * z := by rw [h1]
      have h3 : (w0 * x⁻¹ * w0⁻¹)⁻¹ = w0 * x * w0⁻¹ := by group
      rw [← h3, h2]
      have : (x⁻¹ * z)⁻¹ = z⁻¹ * x := by group
      rw [this, inv_eq_of_mul_eq_one_right hz2]
    set x'' := x * z' with hx''
    have hx''Q : ∀ q ∈ Q, q * x'' = x'' * q := by
      intro q hq
      have h1 := hxc q hq
      have h2 := h.hVQ z' hz'V q hq
      calc q * (x * z') = (q * x) * z' := by rw [mul_assoc]
        _ = (x * q) * z' := by rw [h1]
        _ = x * (q * z') := by rw [mul_assoc]
        _ = x * (z' * q) := by rw [h2]
        _ = (x * z') * q := (mul_assoc _ _ _).symm
    have hxz : z * x = x * z := hxc z hzQ
    have hx''w : x'' * w0 = w0 * x'' := by
      have h1 : w0 * x'' * w0⁻¹ = x'' := by
        calc w0 * (x * z') * w0⁻¹ = (w0 * x * w0⁻¹) * (w0 * z' * w0⁻¹) := by group
          _ = (z * x) * (z * z') := by rw [hwx, hu]
          _ = z * (x * z) * z' := by simp only [mul_assoc]
          _ = z * (z * x) * z' := by rw [← hxz]
          _ = (z * z) * x * z' := by simp only [mul_assoc]
          _ = x * z' := by rw [hz2, one_mul]
      calc x'' * w0 = (w0 * x'' * w0⁻¹) * w0 := by rw [h1]
        _ = w0 * x'' := by group
    have hx''S : x'' ∈ S := S.mul_mem hxS (h.vh.ws (h.V_le_W hz'V))
    have hx''2 : x'' * x'' = 1 := by
      have h1 : z' * x = x * z' := hxc z' hz'Q
      calc (x * z') * (x * z') = x * (z' * x) * z' := by simp only [mul_assoc]
        _ = x * (x * z') * z' := by rw [h1]
        _ = (x * x) * (z' * z') := by simp only [mul_assoc]
        _ = 1 := by rw [hx2, hz'2, one_mul]
    have hx''Z : x'' ∈ Z := h.hZS x'' hx''S (hcent x'' hx''Q hx''w) hx''2
    have e : x = x'' * z' := by
      rw [hx'', mul_assoc, hz'2, mul_one]
    rw [e]
    exact (Z ⊔ conjSub g Z).mul_mem (Subgroup.mem_sup_left hx''Z) hz'V

end QD

end CFSG.Quasithin.Background.Harris.R1
