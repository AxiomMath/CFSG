module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBAlg
public import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvSign
public import Mathlib.LinearAlgebra.StdBasis

public section

namespace CFSG.StandardType.LinTwoTB

open Multiplicative

structure TorusData (G : Type*) [Group G] (s : ℕ) where
  ι : Multiplicative (Fin s → ZMod 3) →* G
  inj : Function.Injective ι
  sg : Fin s → G
  sg_sq : ∀ i, sg i * sg i = 1
  sg_act : ∀ i t, sg i * ι (ofAdd t) * (sg i)⁻¹ = ι (ofAdd (signV i t))
  sw : Fin s → Fin s → G
  sw_sq : ∀ i j, sw i j * sw i j = 1
  sw_act : ∀ i j t, sw i j * ι (ofAdd t) * (sw i j)⁻¹ = ι (ofAdd (swapV i j t))

namespace TorusData

variable {G : Type*} [Group G] {s : ℕ} (D : TorusData G s)

@[expose] def el (v : Fin s → ZMod 3) : G := D.ι (ofAdd v)

theorem el_add (v w : Fin s → ZMod 3) : D.el (v + w) = D.el v * D.el w := by
  simp [el, ofAdd_add]

theorem el_zero : D.el 0 = 1 := by
  simp [el]

theorem el_neg (v : Fin s → ZMod 3) : D.el (-v) = (D.el v)⁻¹ := by
  simp [el, ofAdd_neg]

theorem el_comm (v w : Fin s → ZMod 3) : D.el v * D.el w = D.el w * D.el v := by
  rw [← el_add, ← el_add, add_comm]

theorem el_cube (v : Fin s → ZMod 3) : D.el v ^ 3 = 1 := by
  have h : (3 : ℕ) • v = 0 := by
    funext k
    have : ∀ x : ZMod 3, (3 : ℕ) • x = 0 := by decide
    exact this (v k)
  have h2 : D.el ((3 : ℕ) • v) = D.el v ^ 3 := by
    rw [el, el, ofAdd_nsmul, map_pow]
  rw [← h2, h, el_zero]

theorem el_inj {v w : Fin s → ZMod 3} (h : D.el v = D.el w) : v = w :=
  ofAdd.injective (D.inj h)

theorem sg_inv (i : Fin s) : (D.sg i)⁻¹ = D.sg i := inv_eq_of_mul_eq_one_right (D.sg_sq i)

theorem sg_conj (i : Fin s) (v : Fin s → ZMod 3) :
    D.sg i * D.el v * (D.sg i)⁻¹ = D.el (signV i v) :=
  D.sg_act i v

theorem sw_conj (i j : Fin s) (v : Fin s → ZMod 3) :
    D.sw i j * D.el v * (D.sw i j)⁻¹ = D.el (swapV i j v) :=
  D.sw_act i j v

@[expose] def map {G' : Type*} [Group G'] (e : G ≃* G') : TorusData G' s where
  ι := e.toMonoidHom.comp D.ι
  inj := e.injective.comp D.inj
  sg i := e (D.sg i)
  sg_sq i := by rw [← map_mul, D.sg_sq, map_one]
  sg_act i t := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, D.sg_act]
  sw i j := e (D.sw i j)
  sw_sq i j := by rw [← map_mul, D.sw_sq, map_one]
  sw_act i j t := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, D.sw_act]

theorem el_map {G' : Type*} [Group G'] (e : G ≃* G') (v : Fin s → ZMod 3) :
    (D.map e).el v = e (D.el v) := rfl

@[expose] def tor : Subgroup G := D.ι.range

theorem mem_tor {x : G} : x ∈ D.tor ↔ ∃ v, x = D.el v := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨toAdd y, by simp [el]⟩
  · rintro ⟨v, rfl⟩
    exact ⟨ofAdd v, rfl⟩

@[expose] def nrm : Subgroup G := Subgroup.normalizer (D.tor : Set G)

theorem mem_nrm_of_involution {g : G} (hg : g * g = 1) (f : (Fin s → ZMod 3) → (Fin s → ZMod 3))
    (hf : ∀ v, g * D.el v * g⁻¹ = D.el (f v)) : g ∈ D.nrm := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [nrm, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := D.mem_tor.mp hx
    rw [hf]
    exact D.mem_tor.mpr ⟨_, rfl⟩
  · intro hx
    obtain ⟨v, hv⟩ := D.mem_tor.mp hx
    have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have h2 : x = g * D.el v * g⁻¹ := by
      rw [hv] at h1
      rw [h1, hinv]
    rw [h2, hf]
    exact D.mem_tor.mpr ⟨_, rfl⟩

theorem sg_mem_nrm (i : Fin s) : D.sg i ∈ D.nrm :=
  D.mem_nrm_of_involution (D.sg_sq i) (signV i) (D.sg_conj i)

theorem sw_mem_nrm (i j : Fin s) : D.sw i j ∈ D.nrm :=
  D.mem_nrm_of_involution (D.sw_sq i j) (swapV i j) (D.sw_conj i j)

@[expose] def gens : Set G :=
  Set.range D.sg ∪ Set.range fun p : Fin s × Fin s => D.sw p.1 p.2

theorem sq_of_mem_gens {g : G} (hg : g ∈ D.gens) : g * g = 1 := by
  rcases hg with ⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
  · exact D.sg_sq i
  · exact D.sw_sq i j

@[expose] def wsub : Subgroup G := Subgroup.closure D.gens

theorem sg_mem_wsub (i : Fin s) : D.sg i ∈ D.wsub :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem sw_mem_wsub (i j : Fin s) : D.sw i j ∈ D.wsub :=
  Subgroup.subset_closure (Or.inr ⟨(i, j), rfl⟩)

theorem wsub_le_nrm : D.wsub ≤ D.nrm := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g (⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
  · exact D.sg_mem_nrm i
  · exact D.sw_mem_nrm i j

theorem conj_mem_tor {n : G} (hn : n ∈ D.nrm) (v : Fin s → ZMod 3) :
    ∃ w, n * D.el v * n⁻¹ = D.el w := by
  have h := (Subgroup.mem_normalizer_iff.mp hn (D.el v)).mp (D.mem_tor.mpr ⟨v, rfl⟩)
  obtain ⟨w, hw⟩ := D.mem_tor.mp h
  exact ⟨w, hw⟩

section Aut

variable (A : Subgroup (MulAut G))

@[expose] def IsTorusAut : Prop := ∀ a : MulAut G, a ∈ A ↔ ∃ v, a = MulAut.conj (D.el v)

variable {D A}

theorem weyl_fix (hA : D.IsTorusAut A) {n : G} (hn : n ∈ D.nrm) {a : MulAut G} (ha : a ∈ A) :
    (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  obtain ⟨v, rfl⟩ := (hA _).mp ha
  obtain ⟨w, hw⟩ := D.conj_mem_tor hn v
  have hz : n * ((MulAut.conj (D.el v)) n)⁻¹ = D.el (w - v) := by
    rw [MulAut.conj_apply, sub_eq_add_neg, D.el_add, D.el_neg, ← hw]
    group
  rw [hz]
  refine ⟨D.el_cube _, fun a' ha' => ?_⟩
  obtain ⟨u, rfl⟩ := (hA _).mp ha'
  rw [MulAut.conj_apply]
  have := D.el_comm u (w - v)
  calc D.el u * D.el (w - v) * (D.el u)⁻¹ = D.el (w - v) * D.el u * (D.el u)⁻¹ := by rw [this]
    _ = D.el (w - v) := by group

theorem eq_of_invariant (hA : D.IsTorusAut A) {A' : Subgroup (MulAut G)} (hle : A' ≤ A)
    (hne : A' ≠ ⊥)
    (hinv : ∀ n ∈ D.wsub, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') : A ≤ A' := by
  classical
  let F : AddSubgroup (Fin s → ZMod 3) :=
    { carrier := {v | MulAut.conj (D.el v) ∈ A'}
      add_mem' := by
        intro v w hv hw
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [D.el_add, map_mul]
        exact A'.mul_mem hv hw
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [D.el_zero, map_one]
        exact A'.one_mem
      neg_mem' := by
        intro v hv
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [D.el_neg, map_inv]
        exact A'.inv_mem hv }
  have hmem : ∀ v, v ∈ F ↔ MulAut.conj (D.el v) ∈ A' := fun v => Iff.rfl
  have hsg : ∀ i v, v ∈ F → signV i v ∈ F := by
    intro i v hv
    rw [hmem, ← D.sg_conj, map_mul, map_mul, map_inv]
    exact hinv (D.sg i) (D.sg_mem_wsub i) _ ((hmem v).mp hv)
  have hsw : ∀ i j v, v ∈ F → swapV i j v ∈ F := by
    intro i j v hv
    rw [hmem, ← D.sw_conj, map_mul, map_mul, map_inv]
    exact hinv (D.sw i j) (D.sw_mem_wsub i j) _ ((hmem v).mp hv)
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  obtain ⟨v₀, hv₀⟩ := (hA a₀).mp (hle ha₀)
  have hv₀F : v₀ ∈ F := by
    rw [hmem, ← hv₀]
    exact ha₀
  have hv₀0 : v₀ ≠ 0 := by
    rintro rfl
    apply ha₀1'
    rw [hv₀, D.el_zero, map_one]
  have htop : F = ⊤ := eq_top_of_signed F hsg hsw ⟨v₀, hv₀F, hv₀0⟩
  intro a ha
  obtain ⟨v, rfl⟩ := (hA a).mp ha
  have : v ∈ F := htop ▸ AddSubgroup.mem_top v
  exact (hmem v).mp this

theorem module_core (hA : D.IsTorusAut A) (h3 : 3 ^ 3 ≤ Nat.card A) :
    ∃ (H : Subgroup (MulAut G)) (W : Set G), H ≤ A ∧ H ≠ ⊥ ∧ Nat.card A ≤ 3 * Nat.card H ∧
      (∀ n : G, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut G)) →
        ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ A' : Subgroup (MulAut G), A' ≤ A → A' ≠ ⊥ →
        (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A' := by
  refine ⟨A, (D.wsub : Set G), le_rfl, ?_, Nat.le_mul_of_pos_left _ (by norm_num), ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  · intro n hn h hh
    exact (Subgroup.mem_normalizer_iff.mp hn h).mp hh
  · intro n hn a ha
    exact weyl_fix hA (D.wsub_le_nrm hn) ha
  · intro A' hle hne hinv
    exact eq_of_invariant hA hle hne hinv

section Wt

theorem mulAut_conj_conj (ψ : MulAut G) (b : G) :
    ψ * MulAut.conj b * ψ⁻¹ = MulAut.conj (ψ b) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem fix_of_commute_conj (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h)
    {ψ : MulAut G} {y : G} (h : ψ * MulAut.conj y = MulAut.conj y * ψ) : ψ y = y := by
  apply hZ
  rw [← mulAut_conj_conj, h, mul_inv_cancel_right]

theorem eq_one_of_inv_apply {ψ : MulAut G} {y : G} (hy3 : y ^ 3 = 1) (hψ : ψ y = y⁻¹) {m : ℕ}
    (hm : Odd m) (hfix : (ψ ^ m) y = y) : y = 1 := by
  obtain ⟨n, rfl⟩ := hm
  have h2 : (ψ ^ 2) y = y := by
    rw [pow_two, MulAut.mul_apply, hψ, map_inv, hψ, inv_inv]
  have h2n : ∀ n : ℕ, (ψ ^ (2 * n)) y = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, MulAut.mul_apply, h2, ih]
  have h3 : (ψ ^ (2 * n + 1)) y = y⁻¹ := by
    rw [pow_succ', MulAut.mul_apply, h2n, hψ]
  rw [h3] at hfix
  have hsq : y ^ 2 = 1 := by
    calc y ^ 2 = y * y := sq y
      _ = y * y⁻¹ := by rw [hfix]
      _ = 1 := mul_inv_cancel y
  calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
    _ = 1 := by rw [hy3, hsq]; simp

theorem comm_apply_of_ne {φ : MulAut G} {i j : Fin s} (hji : j ≠ i) {c : ZMod 3}
    (hφ : φ (D.el (Pi.single i 1)) = D.el (Pi.single j c)) :
    (MulAut.conj (D.sg i) * φ * (MulAut.conj (D.sg i))⁻¹ * φ⁻¹) (D.el (Pi.single j c)) =
      (D.el (Pi.single j c))⁻¹ := by
  have h1 : φ⁻¹ (D.el (Pi.single j c)) = D.el (Pi.single i 1) := by
    rw [← hφ, MulAut.inv_apply_self]
  have h2 : (MulAut.conj (D.sg i))⁻¹ (D.el (Pi.single i 1)) = (D.el (Pi.single i 1))⁻¹ := by
    rw [MulAut.conj_inv_apply]
    have e : (D.sg i)⁻¹ * D.el (Pi.single i 1) * D.sg i =
        D.sg i * D.el (Pi.single i 1) * (D.sg i)⁻¹ := by rw [D.sg_inv]
    rw [e, D.sg_conj, signV_single_self, ← D.el_neg, Pi.single_neg]
  have h3 : D.sg i * (D.el (Pi.single j c))⁻¹ * (D.sg i)⁻¹ = (D.el (Pi.single j c))⁻¹ := by
    calc D.sg i * (D.el (Pi.single j c))⁻¹ * (D.sg i)⁻¹
        = (D.sg i * D.el (Pi.single j c) * (D.sg i)⁻¹)⁻¹ := by group
      _ = (D.el (signV i (Pi.single j c)))⁻¹ := by rw [D.sg_conj]
      _ = (D.el (Pi.single j c))⁻¹ := by rw [signV_single_of_ne hji]
  simp only [MulAut.mul_apply]
  rw [h1, h2, map_inv, hφ, MulAut.conj_apply, h3]

theorem nbr_core (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h) (hA : D.IsTorusAut A)
    {wt : G → ℕ} {e : ℕ} (he : 0 < e) (hwι : ∀ v, wt (D.el v) = e * LinTwoTv.hamWt v)
    (hwt : ∀ (φ : MulAut G) (g : G), wt (φ g) = wt g) :
    ∃ W : Set G,
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ Y : Subgroup (MulAut G),
        (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
        (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
        (∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) →
        (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ 3 ^ k * a = a * φ ^ 3 ^ k) →
        ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ := by
  refine ⟨D.wsub, fun n hn a ha => weyl_fix hA (D.wsub_le_nrm hn) ha, ?_⟩
  intro Y _ hYW hYA hYp φ hφ a ha
  have hstab : ∀ ψ ∈ Y, ∀ v, ∃ w, ψ (D.el v) = D.el w := by
    intro ψ hψ v
    have h1 := hYA ψ hψ (MulAut.conj (D.el v)) ((hA _).mpr ⟨v, rfl⟩)
    rw [mulAut_conj_conj] at h1
    obtain ⟨w, hw⟩ := (hA _).mp h1
    exact ⟨w, hZ _ _ hw⟩
  have hpow : ∀ ψ ∈ Y, ∃ m : ℕ, Odd m ∧ ∀ v, (ψ ^ m) (D.el v) = D.el v := by
    intro ψ hψ
    obtain ⟨k, hk⟩ := hYp ψ hψ
    refine ⟨3 ^ k, Odd.pow (by decide), fun v => ?_⟩
    exact fix_of_commute_conj hZ (hk _ ((hA _).mpr ⟨v, rfl⟩))
  have hel1 : ∀ i, D.el (Pi.single i (1 : ZMod 3)) ≠ 1 := by
    intro i h1
    have h2 : (Pi.single i (1 : ZMod 3) : Fin s → ZMod 3) = 0 := D.el_inj (h1.trans D.el_zero.symm)
    have := congrFun h2 i
    simp at this
  have hfixbasis : ∀ i, φ (D.el (Pi.single i 1)) = D.el (Pi.single i 1) := by
    intro i
    obtain ⟨w, hw⟩ := hstab φ hφ (Pi.single i 1)
    have hwt1 : LinTwoTv.hamWt w = 1 := by
      have h1 : wt (φ (D.el (Pi.single i 1))) = wt (D.el (Pi.single i 1)) := hwt φ _
      rw [hw, hwι, hwι, LinTwoTv.hamWt_single i one_ne_zero] at h1
      exact Nat.eq_of_mul_eq_mul_left he (by simpa using h1)
    obtain ⟨j, hj0, hjw⟩ := LinTwoTv.exists_single_of_hamWt_eq_one hwt1
    rw [hjw] at hw
    have hji : j = i := by
      by_contra hne
      have hκY : MulAut.conj (D.sg i) * φ * (MulAut.conj (D.sg i))⁻¹ * φ⁻¹ ∈ Y :=
        Y.mul_mem (hYW (D.sg i) (D.sg_mem_wsub i) φ hφ) (Y.inv_mem hφ)
      have hκy := comm_apply_of_ne (D := D) hne hw
      obtain ⟨m, hm, hfix⟩ := hpow _ hκY
      have h1 := eq_one_of_inv_apply (D.el_cube _) hκy hm (hfix _)
      have h0 : (Pi.single j (w j) : Fin s → ZMod 3) = 0 := D.el_inj (h1.trans D.el_zero.symm)
      apply hj0
      have := congrFun h0 j
      simpa using this
    subst hji
    have hc12 : w j = 1 ∨ w j = 2 := by
      have : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
      exact this _ hj0
    rcases hc12 with h | h
    · rw [hw, h]
    · exfalso
      have hinv : φ (D.el (Pi.single j 1)) = (D.el (Pi.single j 1))⁻¹ := by
        rw [hw, h, ← D.el_neg, ← Pi.single_neg]
        congr 2
      obtain ⟨m, hm, hfix⟩ := hpow φ hφ
      exact hel1 j (eq_one_of_inv_apply (D.el_cube _) hinv hm (hfix _))
  have hfix : ∀ v, φ (D.el v) = D.el v := by
    let S : AddSubgroup (Fin s → ZMod 3) :=
      { carrier := {v | φ (D.el v) = D.el v}
        add_mem' := by
          intro v w hv hw
          simp only [Set.mem_setOf_eq] at hv hw ⊢
          rw [D.el_add, map_mul, hv, hw]
        zero_mem' := by
          simp only [Set.mem_setOf_eq]
          rw [D.el_zero, map_one]
        neg_mem' := by
          intro v hv
          simp only [Set.mem_setOf_eq] at hv ⊢
          rw [D.el_neg, map_inv, hv] }
    have hS : S = ⊤ := eq_top_of_single_one S hfixbasis
    intro v
    have : v ∈ S := hS ▸ AddSubgroup.mem_top v
    exact this
  obtain ⟨v, rfl⟩ := (hA a).mp ha
  have h1 : φ * MulAut.conj (D.el v) * φ⁻¹ = MulAut.conj (D.el v) := by
    rw [mulAut_conj_conj, hfix]
  calc φ * MulAut.conj (D.el v) = φ * MulAut.conj (D.el v) * φ⁻¹ * φ := by group
    _ = MulAut.conj (D.el v) * φ := by rw [h1]

end Wt

section Gen

theorem el_nsmul (n : ℕ) (v : Fin s → ZMod 3) : D.el (n • v) = D.el v ^ n := by
  rw [el, el, ofAdd_nsmul, map_pow]

theorem exists_move_to (i l : Fin s) {c : ZMod 3} (hc : c ≠ 0)
    (hne : D.el (Pi.single l c) ≠ D.el (Pi.single i 1)) :
    ∃ g ∈ D.wsub, g * D.el (Pi.single l c) * g⁻¹ = D.el (Pi.single i 1) ∧
      ∀ k, k ≠ i → k ≠ l → g * D.el (Pi.single k 1) * g⁻¹ = D.el (Pi.single k 1) := by
  have hm2 : (-(2 : ZMod 3)) = 1 := by decide
  by_cases hli : l = i
  · subst hli
    have hc2 : c = 2 := by
      have key : ∀ x : ZMod 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide
      exact key c hc fun h1 => hne (by rw [h1])
    refine ⟨D.sg l, D.sg_mem_wsub l, ?_, fun k hk _ => ?_⟩
    · rw [D.sg_conj, signV_single_self, hc2, hm2]
    · rw [D.sg_conj, signV_single_of_ne hk]
  · have hc12 : c = 1 ∨ c = 2 := by
      have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
      exact key c hc
    rcases hc12 with rfl | rfl
    · refine ⟨D.sw i l, D.sw_mem_wsub i l, ?_, fun k hki hkl => ?_⟩
      · rw [D.sw_conj, swapV_single_right]
      · rw [D.sw_conj, swapV_single_of_ne hki hkl]
    · refine ⟨D.sg i * D.sw i l, D.wsub.mul_mem (D.sg_mem_wsub i) (D.sw_mem_wsub i l), ?_, ?_⟩
      · have e : D.sg i * D.sw i l * D.el (Pi.single l 2) * (D.sg i * D.sw i l)⁻¹ =
            D.sg i * (D.sw i l * D.el (Pi.single l 2) * (D.sw i l)⁻¹) * (D.sg i)⁻¹ := by group
        rw [e, D.sw_conj, swapV_single_right, D.sg_conj, signV_single_self, hm2]
      · intro k hki hkl
        have e : D.sg i * D.sw i l * D.el (Pi.single k 1) * (D.sg i * D.sw i l)⁻¹ =
            D.sg i * (D.sw i l * D.el (Pi.single k 1) * (D.sw i l)⁻¹) * (D.sg i)⁻¹ := by group
        rw [e, D.sw_conj, swapV_single_of_ne hki hkl, D.sg_conj, signV_single_of_ne hki]

theorem exists_wsub_fix {wt : G → ℕ} {e : ℕ} (he : 0 < e)
    (hwι : ∀ v, wt (D.el v) = e * LinTwoTv.hamWt v)
    (hwt : ∀ (φ : MulAut G) (g : G), wt (φ g) = wt g) {n : G} (hn : n ∈ D.nrm) :
    ∃ w ∈ D.wsub, ∀ v, (n * w⁻¹) * D.el v = D.el v * (n * w⁻¹) := by
  classical
  let moved : G → Finset (Fin s) := fun n => Finset.univ.filter fun i =>
    n * D.el (Pi.single i 1) * n⁻¹ ≠ D.el (Pi.single i 1)
  have key : ∀ m : ℕ, ∀ n ∈ D.nrm, (moved n).card ≤ m → ∃ w ∈ D.wsub, ∀ i,
      (n * w⁻¹) * D.el (Pi.single i 1) * (n * w⁻¹)⁻¹ = D.el (Pi.single i 1) := by
    intro m
    induction m with
    | zero =>
      intro n _ hcard
      refine ⟨1, D.wsub.one_mem, fun i => ?_⟩
      have h0 : moved n = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hi : i ∉ moved n := by rw [h0]; exact Finset.notMem_empty i
      simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simpa using hi
    | succ m ih =>
      intro n hn hcard
      by_cases hall : ∀ i, n * D.el (Pi.single i 1) * n⁻¹ = D.el (Pi.single i 1)
      · exact ⟨1, D.wsub.one_mem, fun i => by simpa using hall i⟩
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      obtain ⟨u, hu⟩ := D.conj_mem_tor (D.nrm.inv_mem hn) (Pi.single i 1)
      rw [inv_inv] at hu
      have hwu : LinTwoTv.hamWt u = 1 := by
        have h1 : wt ((MulAut.conj n⁻¹) (D.el (Pi.single i 1))) = wt (D.el (Pi.single i 1)) :=
          hwt _ _
        rw [MulAut.conj_apply, inv_inv, hu, hwι, hwι, LinTwoTv.hamWt_single i one_ne_zero] at h1
        exact Nat.eq_of_mul_eq_mul_left he (by simpa using h1)
      obtain ⟨l, hl0, hul⟩ := LinTwoTv.exists_single_of_hamWt_eq_one hwu
      rw [hul] at hu
      have hzx : D.el (Pi.single l (u l)) ≠ D.el (Pi.single i 1) := by
        intro h
        apply hi
        have hu' : n⁻¹ * D.el (Pi.single i 1) * n = D.el (Pi.single i 1) := hu.trans h
        calc n * D.el (Pi.single i 1) * n⁻¹
            = n * (n⁻¹ * D.el (Pi.single i 1) * n) * n⁻¹ := by rw [hu']
          _ = D.el (Pi.single i 1) := by group
      have hxz : n * D.el (Pi.single l (u l)) * n⁻¹ = D.el (Pi.single i 1) := by
        rw [← hu]
        group
      have hlmoved : n * D.el (Pi.single l 1) * n⁻¹ ≠ D.el (Pi.single l 1) := by
        intro hfix
        have hpow : n * D.el (Pi.single l (u l)) * n⁻¹ = D.el (Pi.single l (u l)) := by
          have h1 : n * D.el (Pi.single l (u l)) * n⁻¹ =
              (n * D.el (Pi.single l 1) * n⁻¹) ^ (u l).val := by
            rw [single_eq_nsmul l (u l), el_nsmul, conj_pow]
          rw [h1, hfix, ← el_nsmul, ← single_eq_nsmul]
        exact hzx (hpow.symm.trans hxz)
      obtain ⟨g, hg, hgz, hgk⟩ := exists_move_to i l hl0 hzx
      have hgz' : g⁻¹ * D.el (Pi.single i 1) * g = D.el (Pi.single l (u l)) := by
        calc g⁻¹ * D.el (Pi.single i 1) * g
            = g⁻¹ * (g * D.el (Pi.single l (u l)) * g⁻¹) * g := by rw [hgz]
          _ = D.el (Pi.single l (u l)) := by group
      have hgk' : ∀ k, k ≠ i → k ≠ l →
          g⁻¹ * D.el (Pi.single k 1) * g = D.el (Pi.single k 1) := by
        intro k hki hkl
        calc g⁻¹ * D.el (Pi.single k 1) * g
            = g⁻¹ * (g * D.el (Pi.single k 1) * g⁻¹) * g := by rw [hgk k hki hkl]
          _ = D.el (Pi.single k 1) := by group
      have hn' : n * g⁻¹ ∈ D.nrm := D.nrm.mul_mem hn (D.nrm.inv_mem (D.wsub_le_nrm hg))
      have hmoved : (moved (n * g⁻¹)).card ≤ m := by
        have hsub : moved (n * g⁻¹) ⊆ (moved n).erase i := by
          intro k hk
          simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · rintro rfl
            apply hk
            calc n * g⁻¹ * D.el (Pi.single k 1) * (n * g⁻¹)⁻¹
                = n * (g⁻¹ * D.el (Pi.single k 1) * g) * n⁻¹ := by group
              _ = D.el (Pi.single k 1) := by rw [hgz', hxz]
          · simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and]
            intro hkn
            apply hk
            have hki : k ≠ i := by
              rintro rfl
              exact hi hkn
            have hkl : k ≠ l := by
              rintro rfl
              exact hlmoved hkn
            calc n * g⁻¹ * D.el (Pi.single k 1) * (n * g⁻¹)⁻¹
                = n * (g⁻¹ * D.el (Pi.single k 1) * g) * n⁻¹ := by group
              _ = D.el (Pi.single k 1) := by rw [hgk' k hki hkl, hkn]
        have hi' : i ∈ moved n := by simpa [moved] using hi
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hi'] at this
        omega
      obtain ⟨w', hw', hw'fix⟩ := ih (n * g⁻¹) hn' hmoved
      refine ⟨w' * g, D.wsub.mul_mem hw' hg, fun k => ?_⟩
      have e : n * (w' * g)⁻¹ = n * g⁻¹ * w'⁻¹ := by group
      rw [e]
      exact hw'fix k
  obtain ⟨w, hw, hfix⟩ := key _ n hn le_rfl
  refine ⟨w, hw, ?_⟩
  let S : AddSubgroup (Fin s → ZMod 3) :=
    { carrier := {v | (n * w⁻¹) * D.el v * (n * w⁻¹)⁻¹ = D.el v}
      add_mem' := by
        intro v v' hv hv'
        simp only [Set.mem_setOf_eq] at hv hv' ⊢
        calc n * w⁻¹ * D.el (v + v') * (n * w⁻¹)⁻¹
            = (n * w⁻¹ * D.el v * (n * w⁻¹)⁻¹) * (n * w⁻¹ * D.el v' * (n * w⁻¹)⁻¹) := by
              rw [D.el_add]; group
          _ = D.el (v + v') := by rw [hv, hv', D.el_add]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [D.el_zero]
        group
      neg_mem' := by
        intro v hv
        simp only [Set.mem_setOf_eq] at hv ⊢
        calc n * w⁻¹ * D.el (-v) * (n * w⁻¹)⁻¹
            = (n * w⁻¹ * D.el v * (n * w⁻¹)⁻¹)⁻¹ := by rw [D.el_neg]; group
          _ = D.el (-v) := by rw [hv, D.el_neg] }
  have hS : S = ⊤ := eq_top_of_single_one S hfix
  intro v
  have h1 : v ∈ S := hS ▸ AddSubgroup.mem_top v
  have h2 : (n * w⁻¹) * D.el v * (n * w⁻¹)⁻¹ = D.el v := h1
  calc (n * w⁻¹) * D.el v = (n * w⁻¹) * D.el v * (n * w⁻¹)⁻¹ * (n * w⁻¹) := by group
    _ = D.el v * (n * w⁻¹) := by rw [h2]

end Gen

section Act

theorem conj_mem_A (hA : D.IsTorusAut A) {n : G} (hn : n ∈ D.nrm) {a : MulAut G} (ha : a ∈ A) :
    MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A := by
  obtain ⟨v, rfl⟩ := (hA a).mp ha
  obtain ⟨w, hw⟩ := D.conj_mem_tor hn v
  rw [← map_inv, ← map_mul, ← map_mul, hw]
  exact (hA _).mpr ⟨w, rfl⟩

theorem mem_nrm_of_normalizer (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h)
    (hA : D.IsTorusAut A) {n : G}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut G))) : n ∈ D.nrm := by
  rw [nrm, Subgroup.mem_normalizer_iff]
  intro x
  have e : MulAut.conj n * MulAut.conj x * (MulAut.conj n)⁻¹ = MulAut.conj (n * x * n⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := D.mem_tor.mp hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (MulAut.conj (D.el v))).mp
      ((hA _).mpr ⟨v, rfl⟩)
    rw [e] at h1
    obtain ⟨w, hw⟩ := (hA _).mp h1
    exact D.mem_tor.mpr ⟨w, hZ _ _ hw⟩
  · intro hx
    obtain ⟨w, hw⟩ := D.mem_tor.mp hx
    have h2 : MulAut.conj n * MulAut.conj x * (MulAut.conj n)⁻¹ ∈ A := by
      rw [e, hw]
      exact (hA _).mpr ⟨w, rfl⟩
    have h3 := (Subgroup.mem_normalizer_iff.mp hn (MulAut.conj x)).mpr h2
    obtain ⟨v, hv⟩ := (hA _).mp h3
    exact D.mem_tor.mpr ⟨v, hZ _ _ hv⟩

theorem endo_core (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h)
    (hA : D.IsTorusAut A) (f : MulAut G → MulAut G) (hfA : ∀ a ∈ A, f a ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b)
    (hW : ∀ n ∈ (D.wsub : Set G), ∀ a ∈ A,
      f (MulAut.conj n * a * (MulAut.conj n)⁻¹) = MulAut.conj n * f a * (MulAut.conj n)⁻¹) :
    ∃ c : ℕ, ∀ a ∈ A, f a = a ^ c := by
  classical
  have hex : ∀ v, ∃ w, f (MulAut.conj (D.el v)) = MulAut.conj (D.el w) := fun v =>
    (hA _).mp (hfA _ ((hA _).mpr ⟨v, rfl⟩))
  choose F hF using hex
  have hinj : ∀ v w, MulAut.conj (D.el v) = MulAut.conj (D.el w) → v = w := fun v w h =>
    D.el_inj (hZ _ _ h)
  have hFadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w
    apply hinj
    calc MulAut.conj (D.el (F (v + w))) = f (MulAut.conj (D.el (v + w))) := (hF _).symm
      _ = f (MulAut.conj (D.el v) * MulAut.conj (D.el w)) := by rw [D.el_add, map_mul]
      _ = f (MulAut.conj (D.el v)) * f (MulAut.conj (D.el w)) :=
          hmul _ ((hA _).mpr ⟨v, rfl⟩) _ ((hA _).mpr ⟨w, rfl⟩)
      _ = MulAut.conj (D.el (F v + F w)) := by rw [hF, hF, D.el_add, map_mul]
  have hFsg : ∀ i v, F (signV i v) = signV i (F v) := by
    intro i v
    apply hinj
    calc MulAut.conj (D.el (F (signV i v))) = f (MulAut.conj (D.el (signV i v))) := (hF _).symm
      _ = f (MulAut.conj (D.sg i) * MulAut.conj (D.el v) * (MulAut.conj (D.sg i))⁻¹) := by
          rw [← D.sg_conj, map_mul, map_mul, map_inv]
      _ = MulAut.conj (D.sg i) * f (MulAut.conj (D.el v)) * (MulAut.conj (D.sg i))⁻¹ :=
          hW _ (D.sg_mem_wsub i) _ ((hA _).mpr ⟨v, rfl⟩)
      _ = MulAut.conj (D.el (signV i (F v))) := by
          rw [hF v, ← D.sg_conj, map_mul, map_mul, map_inv]
  have hFsw : ∀ i j v, F (swapV i j v) = swapV i j (F v) := by
    intro i j v
    apply hinj
    calc MulAut.conj (D.el (F (swapV i j v))) = f (MulAut.conj (D.el (swapV i j v))) :=
          (hF _).symm
      _ = f (MulAut.conj (D.sw i j) * MulAut.conj (D.el v) * (MulAut.conj (D.sw i j))⁻¹) := by
          rw [← D.sw_conj, map_mul, map_mul, map_inv]
      _ = MulAut.conj (D.sw i j) * f (MulAut.conj (D.el v)) * (MulAut.conj (D.sw i j))⁻¹ :=
          hW _ (D.sw_mem_wsub i j) _ ((hA _).mpr ⟨v, rfl⟩)
      _ = MulAut.conj (D.el (swapV i j (F v))) := by
          rw [hF v, ← D.sw_conj, map_mul, map_mul, map_inv]
  obtain ⟨c, hc⟩ := exists_scalar_of_commute F hFadd hFsg hFsw
  refine ⟨c.val, fun a ha => ?_⟩
  obtain ⟨v, rfl⟩ := (hA a).mp ha
  have hcv : c • v = c.val • v := by
    funext k
    simp [nsmul_eq_mul]
  rw [hF v, hc v, hcv, el_nsmul, map_pow]

theorem action_core (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h)
    (hA : D.IsTorusAut A) {wt : G → ℕ} {e : ℕ} (he : 0 < e)
    (hwι : ∀ v, wt (D.el v) = e * LinTwoTv.hamWt v)
    (hwt : ∀ (φ : MulAut G) (g : G), wt (φ g) = wt g) (h3 : 3 ^ 3 ≤ Nat.card A) :
    ∃ (H : Subgroup (MulAut G)) (W : Set G), H ≤ A ∧ H ≠ ⊥ ∧
      (∀ n : G, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut G)) →
        ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      (∀ A' : Subgroup (MulAut G), A' ≤ A → A' ≠ ⊥ →
        (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A') ∧
      (∀ a ∈ A, (∀ n ∈ W, MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1) ∧
      (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ ∈ H) ∧
      (∀ n : G, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut G)) →
        ∃ w ∈ W, ∀ a ∈ A, a (n * w⁻¹) = n * w⁻¹) ∧
      (∀ n ∈ W, n ∈ Subgroup.closure {m | m ∈ W ∧ m * m = 1}) ∧
      ∀ f : MulAut G → MulAut G, (∀ a ∈ H, f a ∈ H) →
        (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b) →
        (∀ n ∈ W, ∀ a ∈ H, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
          MulAut.conj n * f a * (MulAut.conj n)⁻¹) → ∃ c : ℕ, ∀ a ∈ H, f a = a ^ c := by
  refine ⟨A, (D.wsub : Set G), le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  · intro n hn h hh
    exact (Subgroup.mem_normalizer_iff.mp hn h).mp hh
  · intro n hn a ha
    exact weyl_fix hA (D.wsub_le_nrm hn) ha
  · intro A' hle hne hinv
    exact eq_of_invariant hA hle hne hinv
  · intro a ha hfix
    obtain ⟨v, rfl⟩ := (hA a).mp ha
    have hv : v = 0 := by
      apply eq_zero_of_signFixed
      intro i
      have h1 := hfix (D.sg i) (D.sg_mem_wsub i)
      have e : MulAut.conj (D.sg i) * MulAut.conj (D.el v) * (MulAut.conj (D.sg i))⁻¹ =
          MulAut.conj (D.sg i * D.el v * (D.sg i)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [e, D.sg_conj] at h1
      exact D.el_inj (hZ _ _ h1)
    rw [hv, D.el_zero, map_one]
  · intro n hn a ha
    exact A.mul_mem (conj_mem_A hA (D.wsub_le_nrm hn) ha) (A.inv_mem ha)
  · intro n hn
    obtain ⟨w, hw, hfix⟩ := exists_wsub_fix he hwι hwt (mem_nrm_of_normalizer hZ hA hn)
    refine ⟨w, hw, fun a ha => ?_⟩
    obtain ⟨v, rfl⟩ := (hA a).mp ha
    rw [MulAut.conj_apply, ← hfix v]
    group
  · intro n hn
    refine Subgroup.closure_mono (fun g hg => ?_) hn
    exact ⟨Subgroup.subset_closure hg, D.sq_of_mem_gens hg⟩
  · intro f hfA hmul hW
    exact endo_core hZ hA f hfA hmul hW

end Act

end Aut

end TorusData

end CFSG.StandardType.LinTwoTB

end
