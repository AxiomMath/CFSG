module

public import CFSG.Quasithin.Recognition.M12AscModel

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

@[expose] def fourGroup (z s : G) (hz : z * z = 1) (hs : s * s = 1) (hzs : z * s = s * z) :
    Subgroup G where
  carrier := {x | x = 1 ∨ x = z ∨ x = s ∨ x = z * s}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h1 : z * (z * s) = s := by rw [← mul_assoc, hz, one_mul]
    have h2 : (z * s) * z = s := by rw [hzs, mul_assoc, hz, mul_one]
    have h3 : s * (z * s) = z := by rw [hzs, ← mul_assoc, hs, one_mul]
    have h4 : (z * s) * s = z := by rw [mul_assoc, hs, mul_one]
    have h5 : (z * s) * (z * s) = 1 := by rw [mul_assoc, h3, hz]
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [hz, hs, h1, h2, h3, h4, h5, hzs.symm]
  inv_mem' := by
    have h3 : s * (z * s) = z := by rw [hzs, ← mul_assoc, hs, one_mul]
    have h5 : (z * s) * (z * s) = 1 := by rw [mul_assoc, h3, hz]
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hz))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hs)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right h5)))

theorem mem_fourGroup {z s : G} {hz : z * z = 1} {hs : s * s = 1} {hzs : z * s = s * z} {x : G} :
    x ∈ fourGroup z s hz hs hzs ↔ x = 1 ∨ x = z ∨ x = s ∨ x = z * s := Iff.rfl

theorem card_fourGroup {z s : G} {hz : z * z = 1} {hs : s * s = 1} {hzs : z * s = s * z}
    (hz1 : z ≠ 1) (hs1 : s ≠ 1) (hsz : s ≠ z) : Nat.card (fourGroup z s hz hs hzs) = 4 := by
  classical
  have e1 : z * s ≠ 1 := by
    intro h
    apply hsz
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hz
  have e2 : z * s ≠ z := by
    intro h; apply hs1; simpa using h
  have e3 : z * s ≠ s := by
    intro h; apply hz1; simpa using h
  have hset : ((fourGroup z s hz hs hzs : Subgroup G) : Set G) = {1, z, s, z * s} := by
    ext x; simp [mem_fourGroup]
  have h4 : (({1, z, s, z * s} : Set G)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair e3.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hsz.symm, e2.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1.symm, hs1.symm, e1.symm⟩
  have e : Nat.card (fourGroup z s hz hs hzs) = ((fourGroup z s hz hs hzs : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [e, hset, h4]

variable {z : G}

@[expose] def ascE (z g : G) : Subgroup G := ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom

open CFSG.GH74.M12 (Asc03Hyp)

namespace AscModel

variable (m : AscModel z)

include m

theorem z_comm_conj [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) : z * (g * z * g⁻¹) = (g * z * g⁻¹) * z :=
  (m.fSub_elab m.z_mem_fSub (m.conj_mem_fSub hyp hgz hsQ)).2

@[expose] def ascV [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) : Subgroup G :=
  fourGroup z (g * z * g⁻¹) (asc_z_sq hyp) (asc_conj_sq hyp g) (m.z_comm_conj hyp hgz hsQ)

theorem mem_ascV [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {x : G} :
    x ∈ m.ascV hyp hgz hsQ ↔ x = 1 ∨ x = z ∨ x = g * z * g⁻¹ ∨ x = z * (g * z * g⁻¹) :=
  Iff.rfl

theorem card_ascV [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) : Nat.card (m.ascV hyp hgz hsQ) = 4 :=
  card_fourGroup (asc_z_ne_one hyp) (asc_conj_ne_one hyp g) hgz

theorem ascV_le_fSub [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) : m.ascV hyp hgz hsQ ≤ m.fSub := by
  intro x hx
  rcases (m.mem_ascV hyp hgz hsQ).1 hx with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact m.z_mem_fSub
  · exact m.conj_mem_fSub hyp hgz hsQ
  · exact mul_mem m.z_mem_fSub (m.conj_mem_fSub hyp hgz hsQ)

theorem ascV_le_E [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) : ∀ x ∈ m.ascV hyp hgz hsQ, x ∈ ascE z g := by
  obtain ⟨hzQ', -, -, -, -⟩ := config_of_conj hyp hgz hsQ
  have hzQg : z ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := (mem_map_conj_iff _ g z).2 hzQ'
  have hzE : z ∈ ascE z g := ⟨(extraspecialAt_ascQ hyp).mem, hzQg⟩
  have hsE : g * z * g⁻¹ ∈ ascE z g :=
    ⟨hsQ, (mem_map_conj_iff _ g _).2 (by
      rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
      exact (extraspecialAt_ascQ hyp).mem)⟩
  intro x hx
  rcases (m.mem_ascV hyp hgz hsQ).1 hx with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact hzE
  · exact hsE
  · exact mul_mem hzE hsE

omit m in
theorem exists_q [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    ∃ q ∈ ascQ z, q * (g * z * g⁻¹) * q⁻¹ = z * (g * z * g⁻¹) := by
  have hE := extraspecialAt_ascQ hyp
  by_contra hno
  push Not at hno
  have hcen : g * z * g⁻¹ = 1 ∨ g * z * g⁻¹ = z := by
    refine hE.center_le _ hsQ (fun y hy => ?_)
    by_contra hne
    apply hno y hy
    rcases hE.comm_mem y hy _ hsQ with h | h
    · exfalso
      apply hne
      have h' : y * (g * z * g⁻¹) * y⁻¹ = g * z * g⁻¹ := by
        calc y * (g * z * g⁻¹) * y⁻¹ = (y * (g * z * g⁻¹) * y⁻¹ * (g * z * g⁻¹)⁻¹) *
            (g * z * g⁻¹) := by group
          _ = g * z * g⁻¹ := by rw [h, one_mul]
      calc (g * z * g⁻¹) * y = (y * (g * z * g⁻¹) * y⁻¹) * y := by rw [h']
        _ = y * (g * z * g⁻¹) := by group
    · calc y * (g * z * g⁻¹) * y⁻¹ = (y * (g * z * g⁻¹) * y⁻¹ * (g * z * g⁻¹)⁻¹) *
          (g * z * g⁻¹) := by group
        _ = z * (g * z * g⁻¹) := by rw [h]
  rcases hcen with h | h
  · exact asc_conj_ne_one hyp g h
  · exact hgz h

theorem exists_q' [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    ∃ q' ∈ (ascQ z).map (MulAut.conj g).toMonoidHom, q' * z * q'⁻¹ = z * (g * z * g⁻¹) := by
  have hEg := (extraspecialAt_ascQ hyp).conj g
  obtain ⟨hzQ', -, -, -, -⟩ := config_of_conj hyp hgz hsQ
  have hzQg : z ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := (mem_map_conj_iff _ g z).2 hzQ'
  have hcomm := m.z_comm_conj hyp hgz hsQ
  by_contra hno
  push Not at hno
  have hcen : z = 1 ∨ z = g * z * g⁻¹ := by
    refine hEg.center_le z hzQg (fun y hy => ?_)
    by_contra hne
    apply hno y hy
    rcases hEg.comm_mem y hy z hzQg with h | h
    · exfalso
      apply hne
      have h' : y * z * y⁻¹ = z := by
        calc y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
          _ = z := by rw [h, one_mul]
      calc z * y = (y * z * y⁻¹) * y := by rw [h']
        _ = y * z := by group
    · calc y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
        _ = (g * z * g⁻¹) * z := by rw [h]
        _ = z * (g * z * g⁻¹) := hcomm.symm
  rcases hcen with h | h
  · exact asc_z_ne_one hyp h
  · exact hgz h.symm

omit m in
theorem E_norm_Q [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {q e : G} (hq : q ∈ ascQ z) (he : e ∈ ascE z g) :
    q * e * q⁻¹ ∈ ascE z g := by
  have hE := extraspecialAt_ascQ hyp
  obtain ⟨hzQ', -, -, -, -⟩ := config_of_conj hyp hgz hsQ
  have hzQg : z ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := (mem_map_conj_iff _ g z).2 hzQ'
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hq he.1) (Subgroup.inv_mem _ hq), ?_⟩
  have hc : q * e * q⁻¹ = (q * e * q⁻¹ * e⁻¹) * e := by group
  rw [hc]
  refine Subgroup.mul_mem _ ?_ he.2
  rcases hE.comm_mem q hq e he.1 with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hzQg

theorem Q_conj_iff [Finite G] (hyp : Asc03Hyp G z) {c1 c2 : G}
    (h : c1 * z * c1⁻¹ = c2 * z * c2⁻¹) (x : G) :
    c1⁻¹ * x * c1 ∈ ascQ z ↔ c2⁻¹ * x * c2 ∈ ascQ z := by
  have hu : c1⁻¹ * c2 ∈ ascH z := by
    rw [ascH, Subgroup.mem_centralizer_singleton_iff]
    calc c1⁻¹ * c2 * z = c1⁻¹ * (c2 * z * c2⁻¹) * c2 := by group
      _ = c1⁻¹ * (c1 * z * c1⁻¹) * c2 := by rw [h]
      _ = z * (c1⁻¹ * c2) := by group
  have e1 : c1⁻¹ * x * c1 = (c1⁻¹ * c2) * (c2⁻¹ * x * c2) * (c1⁻¹ * c2)⁻¹ := by group
  rw [m.ascQ_eq_qSub hyp]
  constructor
  · intro hx
    have := m.qSub_normal (inv_mem hu) hx
    rwa [show (c1⁻¹ * c2)⁻¹ * (c1⁻¹ * x * c1) * (c1⁻¹ * c2)⁻¹⁻¹ = c2⁻¹ * x * c2 by group] at this
  · intro hx
    have := m.qSub_normal hu hx
    rwa [← e1] at this

theorem E_le_conjQ [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {c : G} (hc : c * z * c⁻¹ ∈ m.ascV hyp hgz hsQ) {e : G}
    (he : e ∈ ascE z g) : c⁻¹ * e * c ∈ ascQ z := by
  obtain ⟨q, hq, hqs⟩ := exists_q hyp hgz hsQ
  rcases (m.mem_ascV hyp hgz hsQ).1 hc with h | h | h | h
  · exfalso
    apply asc_z_ne_one hyp
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · have h1 : c * z * c⁻¹ = 1 * z * (1 : G)⁻¹ := by rw [h]; group
    have := (m.Q_conj_iff hyp h1 e).2
    refine this ?_
    simpa using he.1
  · refine (m.Q_conj_iff hyp (c2 := g) h e).2 ?_
    exact (mem_map_conj_iff _ g e).1 he.2
  · have hc2 : c * z * c⁻¹ = (q * g) * z * (q * g)⁻¹ := by rw [h, ← hqs]; group
    refine (m.Q_conj_iff hyp hc2 e).2 ?_
    have hE' : q⁻¹ * e * q ∈ ascE z g := by
      have := E_norm_Q hyp hgz hsQ (Subgroup.inv_mem _ hq) he
      simpa using this
    have := (mem_map_conj_iff _ g _).1 hE'.2
    rwa [show g⁻¹ * (q⁻¹ * e * q) * g = (q * g)⁻¹ * e * (q * g) by group] at this

theorem mem_E_of_normalizer [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {n : G}
    (hn : n ∈ Subgroup.normalizer (m.ascV hyp hgz hsQ : Set G)) {e : G} (he : e ∈ ascE z g) :
    n * e * n⁻¹ ∈ ascE z g := by
  have hzV : z ∈ m.ascV hyp hgz hsQ := (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inl rfl))
  have hsV : g * z * g⁻¹ ∈ m.ascV hyp hgz hsQ :=
    (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hVz : n⁻¹ * z * n ∈ m.ascV hyp hgz hsQ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) z).1 hzV
    simpa using this
  have hVs : n⁻¹ * (g * z * g⁻¹) * n ∈ m.ascV hyp hgz hsQ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) _).1 hsV
    simpa using this
  refine ⟨?_, ?_⟩
  · have h1 := m.E_le_conjQ hyp hgz hsQ (c := n⁻¹) (by simpa using hVz) he
    simpa using h1
  · refine (mem_map_conj_iff _ g _).2 ?_
    have hc : (n⁻¹ * g) * z * (n⁻¹ * g)⁻¹ ∈ m.ascV hyp hgz hsQ := by
      rw [show (n⁻¹ * g) * z * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * z * g⁻¹) * n by group]
      exact hVs
    have h2 := m.E_le_conjQ hyp hgz hsQ hc he
    rwa [show (n⁻¹ * g)⁻¹ * e * (n⁻¹ * g) = g⁻¹ * (n * e * n⁻¹) * g by group] at h2

end AscModel

theorem no_order3_cent : ∀ s ∈ FTabs, s ≠ tid → s ≠ zTab → ∀ h ∈ ascHTabs,
    tmul h s = tmul s h → tmul h (tmul h h) = tid → h = tid := by decide +kernel

theorem exists_fixed_of_cube_eq_id {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ x, f (f (f x)) = x) (hcard : Nat.card α = 4) : ∃ x, f x = x := by
  classical
  have := Fintype.ofFinite α
  let g : Function.End α := f
  have hf3 : g ^ 3 = 1 := by
    funext x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := g) (by simpa using hf3)
  by_contra hno
  push Not at hno
  have hfix : Fintype.card g.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hno x.1 x.2⟩
  rw [hfix, Fintype.card_eq_nat_card, hcard] at hmod
  exact absurd hmod (by decide)

theorem mem_normalizer_of_forall_conj_mem [Finite G] {V : Subgroup G} {w : G}
    (h : ∀ v ∈ V, w * v * w⁻¹ ∈ V) : w ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hle : V.map (MulAut.conj w).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have hcard : Nat.card (V.map (MulAut.conj w).toMonoidHom) = Nat.card V :=
    (Nat.card_congr (Subgroup.equivMapOfInjective V (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).toEquiv).symm
  have heq : V.map (MulAut.conj w).toMonoidHom = V :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [← heq] at hx
  obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.1 hx
  have hvx' : v = x := by
    have : w * v * w⁻¹ = w * x * w⁻¹ := by simpa [MulAut.conj_apply] using hvx
    calc v = w⁻¹ * (w * v * w⁻¹) * w := by group
      _ = w⁻¹ * (w * x * w⁻¹) * w := by rw [this]
      _ = x := by group
  rw [← hvx']
  exact hv

theorem three_dvd_orderOf_of_cycle {n z s : G} (hz : n * z * n⁻¹ = s) (hs : n * s * n⁻¹ = z * s)
    (hzs : n * (z * s) * n⁻¹ = z) (hsz : s ≠ z) (hzsz : z * s ≠ z) : 3 ∣ orderOf n := by
  have hcyc : ∀ k : ℕ, n ^ k * z * (n ^ k)⁻¹ =
      if k % 3 = 0 then z else if k % 3 = 1 then s else z * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : n ^ (k + 1) * z * (n ^ (k + 1))⁻¹ = n * (n ^ k * z * (n ^ k)⁻¹) * n⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      by_cases h0 : k % 3 = 0
      · have h1 : (k + 1) % 3 = 1 := by omega
        simp [h0, h1, hz]
      · by_cases h1 : k % 3 = 1
        · have h2 : (k + 1) % 3 = 2 := by omega
          simp [h1, h2, hs]
        · have h2 : k % 3 = 2 := by omega
          have h3 : (k + 1) % 3 = 0 := by omega
          simp [h0, h1, h3, hzs]
  have h := hcyc (orderOf n)
  rw [pow_orderOf_eq_one] at h
  by_contra hne
  have h0 : orderOf n % 3 ≠ 0 := by omega
  by_cases h1 : orderOf n % 3 = 1
  · have h' : z = s := by simpa [h0, h1] using h
    exact hsz h'.symm
  · have h' : z = z * s := by simpa [h0, h1] using h
    exact hzsz h'.symm

namespace AscModel

variable {z : G} (m : AscModel z)

include m

theorem no_order3_cent_fSub [Finite G] {s h : G} (hs : s ∈ m.fSub) (hs1 : s ≠ 1) (hsz : s ≠ z)
    (hh : h ∈ ascH z) (hc : h * s = s * h) (h3 : h * h * h = 1) : h = 1 := by
  have hh' : m.tb h ∈ ascHTabs := m.tb_mem hh
  have e : m.tb (h * (h * h)) = tmul (m.tb h) (tmul (m.tb h) (m.tb h)) := by
    rw [m.tb_mul hh (mul_mem hh hh), m.tb_mul hh hh]
  have h3' : h * (h * h) = 1 := by rw [← mul_assoc]; exact h3
  rw [h3', m.tb_one] at e
  have hs' := m.mem_fSub_iff.1 hs
  have := no_order3_cent _ hs'.2 (fun e' => hs1 ((m.eq_one_iff hs'.1).2 e'))
    (fun e' => hsz ((m.eq_z_iff hs'.1).2 e')) _ hh' ((m.comm_iff hh hs'.1).1 hc) e.symm
  exact (m.eq_one_iff hh).2 this

theorem exists_order_three_fixing [Finite G] (hyp : Asc03Hyp G z) {g : G}
    (hgz : g * z * g⁻¹ ≠ z) (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    ∃ y t : G, y ∈ Subgroup.normalizer (m.ascV hyp hgz hsQ : Set G) ∧ y * y * y = 1 ∧
      y * z * y⁻¹ ≠ z ∧ t ∈ ascE z g ∧ t ∉ m.ascV hyp hgz hsQ ∧ y * t * y⁻¹ = t := by
  classical
  set s := g * z * g⁻¹ with hs
  set V := m.ascV hyp hgz hsQ with hV
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hz1 : z ≠ 1 := asc_z_ne_one hyp
  have hcomm : z * s = s * z := m.z_comm_conj hyp hgz hsQ
  have hs2 : s * s = 1 := asc_conj_sq hyp g
  have hs1 : s ≠ 1 := asc_conj_ne_one hyp g
  have hsF : s ∈ m.fSub := m.conj_mem_fSub hyp hgz hsQ
  have hzV : z ∈ V := (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inl rfl))
  have hsV : s ∈ V := (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hzsV : z * s ∈ V := (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨q, hq, hqs⟩ := exists_q hyp hgz hsQ
  obtain ⟨q', hq', hq'z⟩ := m.exists_q' hyp hgz hsQ
  have hqz : q * z = z * q :=
    Subgroup.mem_centralizer_singleton_iff.1 (ascQ_le_ascH z hq)
  have hq's : q' * s = s * q' := by
    obtain ⟨w, hw, hwq⟩ := Subgroup.mem_map.1 hq'
    have hwq' : g * w * g⁻¹ = q' := by simpa [MulAut.conj_apply] using hwq
    have hwz : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.1 (ascQ_le_ascH z hw)
    rw [← hwq']
    calc g * w * g⁻¹ * (g * z * g⁻¹) = g * (w * z) * g⁻¹ := by group
      _ = g * (z * w) * g⁻¹ := by rw [hwz]
      _ = (g * z * g⁻¹) * (g * w * g⁻¹) := by group
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hqzq : q * z * q⁻¹ = z := by rw [hqz]; group
  have hq'sq : q' * s * q'⁻¹ = s := by rw [hq's]; group
  have hqN : q ∈ Subgroup.normalizer (V : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    rcases (m.mem_ascV hyp hgz hsQ).1 hv with h | h | h | h <;> rw [h]
    · simp
    · rw [hqzq]; exact hzV
    · rw [hqs]; exact hzsV
    · have : q * (z * s) * q⁻¹ = s := by
        calc q * (z * s) * q⁻¹ = (q * z * q⁻¹) * (q * s * q⁻¹) := by group
          _ = z * (z * s) := by rw [hqzq, hqs]
          _ = s := by rw [← mul_assoc, hz2, one_mul]
      rw [this]; exact hsV
  have hq'N : q' ∈ Subgroup.normalizer (V : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    rcases (m.mem_ascV hyp hgz hsQ).1 hv with h | h | h | h <;> rw [h]
    · simp
    · rw [hq'z]; exact hzsV
    · rw [hq'sq]; exact hsV
    · have : q' * (z * s) * q'⁻¹ = z := by
        calc q' * (z * s) * q'⁻¹ = (q' * z * q'⁻¹) * (q' * s * q'⁻¹) := by group
          _ = (z * s) * s := by rw [hq'z, hq'sq]
          _ = z := by rw [mul_assoc, hs2, mul_one]
      rw [this]; exact hzV
  set n := q * q' with hn
  have hnN : n ∈ Subgroup.normalizer (V : Set G) := mul_mem hqN hq'N
  have hn1 : n * z * n⁻¹ = s := by
    calc n * z * n⁻¹ = q * (q' * z * q'⁻¹) * q⁻¹ := by rw [hn]; group
      _ = q * (z * s) * q⁻¹ := by rw [hq'z]
      _ = (q * z * q⁻¹) * (q * s * q⁻¹) := by group
      _ = s := by rw [hqzq, hqs, ← mul_assoc, hz2, one_mul]
  have hn2 : n * s * n⁻¹ = z * s := by
    calc n * s * n⁻¹ = q * (q' * s * q'⁻¹) * q⁻¹ := by rw [hn]; group
      _ = q * s * q⁻¹ := by rw [hq'sq]
      _ = z * s := hqs
  have hn3 : n * (z * s) * n⁻¹ = z := by
    calc n * (z * s) * n⁻¹ = q * ((q' * z * q'⁻¹) * (q' * s * q'⁻¹)) * q⁻¹ := by rw [hn]; group
      _ = q * ((z * s) * s) * q⁻¹ := by rw [hq'z, hq'sq]
      _ = q * z * q⁻¹ := by rw [mul_assoc z s s, hs2, mul_one]
      _ = z := hqzq
  have hzsz : z * s ≠ z := by
    intro h; apply hs1; simpa using h
  have h3n : 3 ∣ orderOf n := three_dvd_orderOf_of_cycle hn1 hn2 hn3 hgz hzsz
  have h3N : 3 ∣ Nat.card (Subgroup.normalizer (V : Set G)) := by
    have := orderOf_dvd_natCard (⟨n, hnN⟩ : Subgroup.normalizer (V : Set G))
    rw [Subgroup.orderOf_mk] at this
    exact h3n.trans this
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y0, hy0⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.normalizer (V : Set G)) 3 h3N
  set y : G := (y0 : G) with hy
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := y0.2
  have hyord : orderOf y = 3 := by rw [hy, Subgroup.orderOf_coe, hy0]
  have hy3 : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hyord, show y ^ 3 = y * y * y by simp [pow_succ, mul_assoc]] at this
  have hymove : y * z * y⁻¹ ≠ z := by
    intro hyz
    have hyH : y ∈ ascH z := by
      rw [ascH, Subgroup.mem_centralizer_singleton_iff]
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz]
    have hysV : y * s * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hyN s).1 hsV
    rcases (m.mem_ascV hyp hgz hsQ).1 hysV with h | h | h | h
    · apply hs1
      calc s = y⁻¹ * (y * s * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    · apply hgz
      calc s = y⁻¹ * (y * s * y⁻¹) * y := by group
        _ = y⁻¹ * z * y := by rw [h]
        _ = z := by
          calc y⁻¹ * z * y = y⁻¹ * (y * z * y⁻¹) * y := by rw [hyz]
            _ = z := by group
    · have hys : y * s = s * y := by
        calc y * s = (y * s * y⁻¹) * y := by group
          _ = s * y := by rw [h]
      have := m.no_order3_cent_fSub hsF hs1 hgz hyH hys hy3
      rw [this, orderOf_one] at hyord
      omega
    · have h1 : y * (z * s) * y⁻¹ = s := by
        calc y * (z * s) * y⁻¹ = (y * z * y⁻¹) * (y * s * y⁻¹) := by group
          _ = z * (z * s) := by rw [hyz, h]
          _ = s := by rw [← mul_assoc, hz2, one_mul]
      have hzs : s = z * s := by
        calc s = (y * y * y) * s * (y * y * y)⁻¹ := by rw [hy3]; group
          _ = y * (y * (y * s * y⁻¹) * y⁻¹) * y⁻¹ := by group
          _ = y * (y * (z * s) * y⁻¹) * y⁻¹ := by rw [h]
          _ = y * s * y⁻¹ := by rw [h1]
          _ = z * s := h
      apply hz1
      have : z * s = 1 * s := by rw [one_mul]; exact hzs.symm
      exact mul_right_cancel this
  have hVE : ∀ x ∈ V, x ∈ ascE z g := by
    obtain ⟨hzQ', -, -, -, -⟩ := config_of_conj hyp hgz hsQ
    have hzQg : z ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := (mem_map_conj_iff _ g z).2 hzQ'
    have hzE : z ∈ ascE z g := ⟨(extraspecialAt_ascQ hyp).mem, hzQg⟩
    have hsE : s ∈ ascE z g :=
      ⟨hsQ, (mem_map_conj_iff _ g s).2 (by
        rw [show g⁻¹ * s * g = z by rw [hs]; group]
        exact (extraspecialAt_ascQ hyp).mem)⟩
    intro x hx
    rcases (m.mem_ascV hyp hgz hsQ).1 hx with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact hzE
    · exact hsE
    · exact mul_mem hzE hsE
  have hEcard : Nat.card (ascE z g) = 8 := (config_of_conj hyp hgz hsQ).2.1
  have hVcard : Nat.card V = 4 := m.card_ascV hyp hgz hsQ
  have hcardα : Nat.card {x : G // x ∈ ascE z g ∧ x ∉ V} = 4 := by
    have hsub : (V : Set G) ⊆ (ascE z g : Set G) := fun x hx => hVE x hx
    have h1 : Nat.card {x : G // x ∈ ascE z g ∧ x ∉ V} = ((ascE z g : Set G) \ (V : Set G)).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)
    have h2 := Set.ncard_sdiff hsub (Set.toFinite _)
    have e1 : Nat.card (ascE z g) = (ascE z g : Set G).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card V = (V : Set G).ncard := Nat.card_coe_set_eq _
    omega
  let f : {x : G // x ∈ ascE z g ∧ x ∉ V} → {x : G // x ∈ ascE z g ∧ x ∉ V} := fun x =>
    ⟨y * x.1 * y⁻¹, m.mem_E_of_normalizer hyp hgz hsQ hyN x.2.1, fun hx =>
      x.2.2 ((Subgroup.mem_normalizer_iff.1 hyN x.1).2 hx)⟩
  have hf : ∀ x, f (f (f x)) = x := by
    intro x
    apply Subtype.ext
    show y * (y * (y * x.1 * y⁻¹) * y⁻¹) * y⁻¹ = x.1
    calc y * (y * (y * x.1 * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x.1 * (y * y * y)⁻¹ := by group
      _ = x.1 := by rw [hy3]; group
  have : Finite {x : G // x ∈ ascE z g ∧ x ∉ V} := inferInstance
  obtain ⟨t, ht⟩ := exists_fixed_of_cube_eq_id f hf hcardα
  exact ⟨y, t.1, hyN, hy3, hymove, t.2.1, t.2.2, congrArg Subtype.val ht⟩

end AscModel

end CFSG.Quasithin
