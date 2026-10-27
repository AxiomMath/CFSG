module

public import CFSG.Quasithin.Background.RonanE114D4LowBN
public import CFSG.GH74.GLS.Stage4.HexCoordD4

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.Quasithin.H13.F431.BN CFSG.Open
  CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage4.Hex CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

variable {X : Type} [Group X] {K : Type} [Field K] {σ : K →+* K} {hσ : ∀ c, σ (σ (σ c)) = c}
  (D : RankTwoSystem X 6) {ψ : ∀ i : Fin 6, d43Par σ i → X}

theorem conj_mi_true_inv {k : ℤ} (hk1 : 2 ≤ k) (hk6 : k ≤ 6) {y : X} (hy : y ∈ D.root k) :
    (mi D true)⁻¹ * y * mi D true ∈ D.root (8 - k) := by
  have hm : ((D.lift (gen D.w₁ D.w₂ true) : D.N) : D.Weyl) = D.w₁ := D.lift_mk _
  have h := D.conj_mem_root₁ _ (D.inv_lift₁ _ hm) hk1 (by exact_mod_cast hk6) hy
  have e : ((6 : ℕ) : ℤ) + 2 - k = 8 - k := by push_cast; ring
  rw [e] at h
  simpa [mi] using h

theorem conj_mi_true {k : ℤ} (hk1 : 2 ≤ k) (hk6 : k ≤ 6) {y : X} (hy : y ∈ D.root k) :
    mi D true * y * (mi D true)⁻¹ ∈ D.root (8 - k) := by
  have hm : ((D.lift (gen D.w₁ D.w₂ true) : D.N) : D.Weyl) = D.w₁ := D.lift_mk _
  have h := D.conj_mem_root₁ _ hm hk1 (by exact_mod_cast hk6) hy
  have e : ((6 : ℕ) : ℤ) + 2 - k = 8 - k := by push_cast; ring
  rw [e] at h
  simpa [mi] using h

theorem conj_mi_false_inv {k : ℤ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) {y : X} (hy : y ∈ D.root k) :
    (mi D false)⁻¹ * y * mi D false ∈ D.root (6 - k) := by
  have hm : ((D.lift (gen D.w₁ D.w₂ false) : D.N) : D.Weyl) = D.w₂ := D.lift_mk _
  have h := D.conj_mem_root₂ _ (D.inv_lift₂ _ hm) hk1 (by push_cast; omega) hy
  have e : ((6 : ℕ) : ℤ) - k = 6 - k := by push_cast; ring
  rw [e] at h
  simpa [mi] using h

theorem conj_mi_false {k : ℤ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) {y : X} (hy : y ∈ D.root k) :
    mi D false * y * (mi D false)⁻¹ ∈ D.root (6 - k) := by
  have hm : ((D.lift (gen D.w₁ D.w₂ false) : D.N) : D.Weyl) = D.w₂ := D.lift_mk _
  have h := D.conj_mem_root₂ _ hm hk1 (by push_cast; omega) hy
  have e : ((6 : ℕ) : ℤ) - k = 6 - k := by push_cast; ring
  rw [e] at h
  simpa [mi] using h

theorem root_le_Q_true {k : ℤ} (hk1 : 2 ≤ k) (hk6 : k ≤ 6) [Finite X]
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) : D.root k ≤ Q D true := by
  intro x hx
  rw [Q_eq_Uplus D hU true, ← SetLike.mem_coe, coe_Uplus_true]
  exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨hk1, by exact_mod_cast hk6⟩) hx

theorem root_le_Q_false {k : ℤ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) [Finite X]
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) : D.root k ≤ Q D false := by
  intro x hx
  rw [Q_eq_Uplus D hU false, ← SetLike.mem_coe, coe_Uplus_false]
  exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨hk1, by push_cast; omega⟩) hx

section Coords

variable {D} (hψ : D4Coords D hσ ψ)
include hψ

theorem mem_root_iff (i : Fin 6) {k : ℤ} (hk : k = (i : ℤ) + 1) (y : X) :
    y ∈ D.root k ↔ ∃ c, ψ i c = y := by
  subst hk
  exact ⟨fun hy => hψ.surj i y hy, fun ⟨c, hc⟩ => hc ▸ hψ.mem i c⟩

theorem psi_zero (i : Fin 6) : ψ i 0 = 1 := by
  have h := hψ.rel.add i 0 0
  simp only [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem exists_psi0 {y : X} (hy : y ∈ D.root 1) : ∃ s : K, ψ 0 s = y := hψ.surj 0 y hy

theorem exists_psi1 {y : X} (hy : y ∈ D.root 2) : ∃ c : fixedField σ, ψ 1 c = y :=
  hψ.surj 1 y hy

theorem exists_psi2 {y : X} (hy : y ∈ D.root 3) : ∃ t : K, ψ 2 t = y := hψ.surj 2 y hy

theorem psi0_zero : ψ 0 (0 : K) = 1 := psi_zero hψ 0

theorem psi1_zero : ψ 1 (0 : fixedField σ) = 1 := psi_zero hψ 1

theorem psi2_zero : ψ 2 (0 : K) = 1 := psi_zero hψ 2

theorem commute_three_six {a b : X} (ha : a ∈ D.root 3) (hb : b ∈ D.root 6) : a * b = b * a := by
  obtain ⟨s, rfl⟩ := (mem_root_iff hψ 2 (by norm_num) a).1 ha
  obtain ⟨t, rfl⟩ := (mem_root_iff hψ 5 (by norm_num) b).1 hb
  exact (hψ.rel.c25 s t).eq

theorem commute_five_six {a b : X} (ha : a ∈ D.root 5) (hb : b ∈ D.root 6) : a * b = b * a := by
  obtain ⟨s, rfl⟩ := (mem_root_iff hψ 4 (by norm_num) a).1 ha
  obtain ⟨t, rfl⟩ := (mem_root_iff hψ 5 (by norm_num) b).1 hb
  exact (hψ.rel.c45 s t).eq

variable [CharP K 2]

theorem psi_zero_mul_self (s : K) : ψ 0 s * ψ 0 s = 1 := by
  have h := hψ.rel.add 0 s s
  have h0 : ((s : d43Par σ 0) + (s : d43Par σ 0) : d43Par σ 0) = 0 :=
    CharTwo.add_self_eq_zero (R := K) s
  have h1 : ψ 0 ((s : d43Par σ 0) + (s : d43Par σ 0)) = ψ 0 0 := congrArg (ψ 0) h0
  calc ψ 0 s * ψ 0 s = ψ 0 ((s : d43Par σ 0) + (s : d43Par σ 0)) := h.symm
    _ = ψ 0 0 := h1
    _ = 1 := psi_zero hψ 0

theorem psi_zero_inv (s : K) : (ψ 0 s)⁻¹ = ψ 0 s :=
  inv_eq_of_mul_eq_one_right (psi_zero_mul_self hψ s)

theorem conj_psi_zero_two (s t : K) :
    (ψ 0 s)⁻¹ * ψ 2 t * ψ 0 s = ψ 1 (d43Tr hσ (s * t)) * ψ 2 t := by
  have h := hψ.rel.r02 s t
  rw [commutatorElement_def] at h
  rw [psi_zero_inv hψ s]
  calc ψ 0 s * ψ 2 t * ψ 0 s = ψ 0 s * ψ 2 t * (ψ 0 s)⁻¹ * (ψ 2 t)⁻¹ * ψ 2 t := by
        rw [psi_zero_inv hψ s]; group
    _ = ψ 1 (d43Tr hσ (s * t)) * ψ 2 t := by rw [h]

end Coords

section Trace

variable [CharP K 2]

theorem d43Tr_fixed (e : fixedField σ) : d43Tr hσ (e : K) = e := by
  apply Subtype.ext
  rw [coe_d43Tr]
  have h1 : σ (e : K) = e := e.2
  rw [h1, h1]
  have : (e : K) + e = 0 := CharTwo.add_self_eq_zero _
  rw [this, zero_add]

theorem exists_trace_eq {s : K} (hs : s ≠ 0) (e : fixedField σ) :
    ∃ t : K, d43Tr hσ (s * t) = e :=
  ⟨s⁻¹ * e, by rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul, d43Tr_fixed]⟩

theorem exists_trace_eq_zero (hσ1 : ∃ c : K, σ c ≠ c) {s : K} (hs : s ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ d43Tr hσ (s * t) = 0 := by
  obtain ⟨c, hc⟩ := hσ1
  refine ⟨s⁻¹ * (c + d43Tr hσ c), ?_, ?_⟩
  · refine mul_ne_zero (inv_ne_zero hs) fun h => hc ?_
    have h' : c = (d43Tr hσ c : K) := by
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this
    have hfix : σ (d43Tr hσ c : K) = d43Tr hσ c := (d43Tr hσ c).2
    calc σ c = σ (d43Tr hσ c : K) := congrArg σ h'
      _ = d43Tr hσ c := hfix
      _ = c := h'.symm
  · rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    apply Subtype.ext
    show ((d43Tr hσ (c + d43Tr hσ c) : fixedField σ) : K) = 0
    have hadd : (d43Tr hσ (c + (d43Tr hσ c : K)) : K) =
        (d43Tr hσ c : K) + (d43Tr hσ ((d43Tr hσ c : K)) : K) := by
      simp only [coe_d43Tr, map_add]
      ring
    rw [hadd, d43Tr_fixed, CharTwo.add_self_eq_zero]

end Trace

section Lemma61

variable [Finite X] (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) {D} (hψ : D4Coords D hσ ψ)
include hU hψ

theorem root_three_le_rad_of_adj {p : V D} (hp : (Γ D).Adj (v D false) p) :
    D.root 3 ≤ rad D p := by
  have h6 : ((6 : ℕ) : ℤ) = 6 := rfl
  rcases nbr_false D hp with rfl | ⟨x, hx, rfl⟩
  · rw [rad_v]
    exact root_le_Q_true D (by norm_num) (by norm_num) hU
  · intro a ha
    rw [mem_rad_smul_iff, rad_v]
    rw [h6] at hx
    have hxa : x⁻¹ * a * x = a := by
      rw [mul_assoc, commute_three_six hψ ha hx, ← mul_assoc, inv_mul_cancel, one_mul]
    have e : (x * mi D false)⁻¹ * a * (x * mi D false) = (mi D false)⁻¹ * a * mi D false := by
      calc (x * mi D false)⁻¹ * a * (x * mi D false)
          = (mi D false)⁻¹ * (x⁻¹ * a * x) * mi D false := by group
        _ = (mi D false)⁻¹ * a * mi D false := by rw [hxa]
    rw [e]
    have := conj_mi_false_inv D (k := 3) (by norm_num) (by norm_num) ha
    have h3 : (mi D false)⁻¹ * a * mi D false ∈ D.root 3 := by simpa using this
    exact root_le_Q_true D (k := 3) (by norm_num) (by norm_num) hU h3

theorem exists_normalizing_of_adj {p : V D} (hp : (Γ D).Adj (v D false) p) :
    ∃ g ∈ P D false, g • v D true = p ∧ ∀ a ∈ D.root 3, g * a * g⁻¹ ∈ D.root 3 ∧
      g⁻¹ * a * g ∈ D.root 3 := by
  have h6 : ((6 : ℕ) : ℤ) = 6 := rfl
  rcases nbr_false D hp with rfl | ⟨x, hx, rfl⟩
  · exact ⟨1, (P D false).one_mem, one_smul _ _, fun a ha => by simpa using ha⟩
  · rw [h6] at hx
    refine ⟨x * mi D false, (P D false).mul_mem (B_le_P D false (D.root_le_B (by norm_num)
      (by norm_num) hx)) (mi_mem_P D false), rfl, fun a ha => ⟨?_, ?_⟩⟩
    · have hb := conj_mi_false D (k := 3) (by norm_num) (by norm_num) ha
      have hb' : mi D false * a * (mi D false)⁻¹ ∈ D.root 3 := by simpa using hb
      have hxb : x * (mi D false * a * (mi D false)⁻¹) * x⁻¹ = mi D false * a * (mi D false)⁻¹ := by
        rw [← commute_three_six hψ hb' hx, mul_assoc, mul_inv_cancel, mul_one]
      rw [show x * mi D false * a * (x * mi D false)⁻¹ =
          x * (mi D false * a * (mi D false)⁻¹) * x⁻¹ by group, hxb]
      exact hb'
    · have hxa : x⁻¹ * a * x = a := by
        rw [mul_assoc, commute_three_six hψ ha hx, ← mul_assoc, inv_mul_cancel, one_mul]
      have hb := conj_mi_false_inv D (k := 3) (by norm_num) (by norm_num) ha
      rw [show (x * mi D false)⁻¹ * a * (x * mi D false) =
          (mi D false)⁻¹ * (x⁻¹ * a * x) * mi D false by group, hxa]
      simpa using hb

theorem root_three_le_rad_arm : D.root 3 ≤ rad D (mi D true • v D false) := by
  intro a ha
  rw [mem_rad_smul_iff, rad_v]
  have := conj_mi_true_inv D (k := 3) (by norm_num) (by norm_num) ha
  have h5 : (mi D true)⁻¹ * a * mi D true ∈ D.root 5 := by simpa using this
  exact root_le_Q_false D (k := 5) (by norm_num) (by norm_num) hU h5

theorem arm_point [CharP K 2] {z : V D} (hz : (Γ D).Adj (mi D true • v D false) z)
    (hz1 : z ≠ v D true) :
    D.root 3 ⊓ rad D z = ⊥ ∧ ∀ w w' : V D, (Γ D).Adj z w → (Γ D).Adj z w' →
      w ≠ mi D true • v D false → w' ≠ mi D true • v D false → ∃ a ∈ D.root 3, a • w = w' := by
  have h6 : ((6 : ℕ) : ℤ) = 6 := rfl
  set m₁ := mi D true with hm₁
  set m₂ := mi D false with hm₂
  have hadj : ∀ (g : X) {y z : V D}, (Γ D).Adj y z → (Γ D).Adj (g • y) (g • z) :=
    fun g y z h => (GraphAction.adj_smul (Γ := Γ D) g y z).2 h
  have hz' : (Γ D).Adj (v D false) (m₁⁻¹ • z) := by
    have := hadj m₁⁻¹ hz
    rwa [inv_smul_smul] at this
  rcases nbr_false D hz' with h1 | ⟨x, hx, hxz⟩
  · exfalso
    apply hz1
    rw [← smul_inv_smul m₁ z, h1, (smul_v_eq_iff D m₁ true).2 (mi_mem_P D true)]
  rw [h6] at hx
  set h : X := m₁ * x * m₂ with hh
  have hzh : z = h • v D true := by
    rw [hh, mul_assoc, mul_smul, ← hxz, smul_inv_smul]
  have hconj : ∀ a ∈ D.root 3, h⁻¹ * a * h ∈ D.root 1 := by
    intro a ha
    have hb := conj_mi_true_inv D (k := 3) (by norm_num) (by norm_num) ha
    have hb' : m₁⁻¹ * a * m₁ ∈ D.root 5 := by simpa using hb
    have hxb : x⁻¹ * (m₁⁻¹ * a * m₁) * x = m₁⁻¹ * a * m₁ := by
      rw [mul_assoc, commute_five_six hψ hb' hx, ← mul_assoc, inv_mul_cancel, one_mul]
    have hc := conj_mi_false_inv D (k := 5) (by norm_num) (by norm_num) hb'
    rw [show h⁻¹ * a * h = m₂⁻¹ * (x⁻¹ * (m₁⁻¹ * a * m₁) * x) * m₂ by rw [hh]; group, hxb]
    simpa using hc
  have hconj' : ∀ y ∈ D.root 1, h * y * h⁻¹ ∈ D.root 3 := by
    intro y hy
    have hb := conj_mi_false D (k := 1) (by norm_num) (by norm_num) hy
    have hb' : m₂ * y * m₂⁻¹ ∈ D.root 5 := by simpa using hb
    have hxb : x * (m₂ * y * m₂⁻¹) * x⁻¹ = m₂ * y * m₂⁻¹ := by
      rw [← commute_five_six hψ hb' hx, mul_assoc, mul_inv_cancel, mul_one]
    have hc := conj_mi_true D (k := 5) (by norm_num) (by norm_num) hb'
    rw [show h * y * h⁻¹ = m₁ * (x * (m₂ * y * m₂⁻¹) * x⁻¹) * m₁⁻¹ by rw [hh]; group, hxb]
    simpa using hc
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro a hai
    obtain ⟨ha, haz⟩ := Subgroup.mem_inf.1 hai
    rw [Subgroup.mem_bot]
    rw [hzh, mem_rad_smul_iff, rad_v] at haz
    have h1 : h⁻¹ * a * h ∈ D.root 1 ⊓ Q D true := ⟨hconj a ha, haz⟩
    rw [root_one_inf_Q D hU, Subgroup.mem_bot] at h1
    have : a = h * (h⁻¹ * a * h) * h⁻¹ := by group
    rw [this, h1]
    group
  · intro w w' hw hw' hwe hw'e
    have hhv : h • v D false = m₁ • v D false := by
      rw [hh, mul_assoc, mul_smul, (smul_v_eq_iff D (x * m₂) false).2
        ((P D false).mul_mem (B_le_P D false (D.root_le_B (by norm_num) (by norm_num) hx))
          (mi_mem_P D false))]
    have key : ∀ {w : V D}, (Γ D).Adj z w → w ≠ m₁ • v D false →
        ∃ y ∈ D.root 1, h⁻¹ • w = (y * m₁) • v D false := by
      intro w hw hwe
      have hw1 : (Γ D).Adj (v D true) (h⁻¹ • w) := by
        have := hadj h⁻¹ hw
        rwa [hzh, inv_smul_smul] at this
      rcases nbr_true D hw1 with h2 | h2
      · exfalso
        apply hwe
        rw [← hhv, ← h2, smul_inv_smul]
      · exact h2
    obtain ⟨y, hy, hyw⟩ := key hw hwe
    obtain ⟨y', hy', hyw'⟩ := key hw' hw'e
    refine ⟨h * (y' * y⁻¹) * h⁻¹, hconj' _ ((D.root 1).mul_mem hy' ((D.root 1).inv_mem hy)), ?_⟩
    calc (h * (y' * y⁻¹) * h⁻¹) • w = h • ((y' * y⁻¹) • (h⁻¹ • w)) := by
          rw [mul_smul, mul_smul]
      _ = h • (h⁻¹ • w') := by
          congr 1
          rw [hyw, smul_smul, show y' * y⁻¹ * (y * m₁) = y' * m₁ by group, ← hyw']
      _ = w' := smul_inv_smul h w'

theorem active_line [CharP K 2] (hσ1 : ∃ c : K, σ c ≠ c) {x : X} (hx : x ∈ D.root 1)
    (hx1 : x ≠ 1) :
    ¬ D.root 3 ≤ rad D ((x * mi D true) • v D false) ∧
      (∀ w w' : V D, (Γ D).Adj ((x * mi D true) • v D false) w →
        (Γ D).Adj ((x * mi D true) • v D false) w' → w ≠ v D true → w' ≠ v D true →
          ∃ a ∈ D.root 3, a • w = w') ∧
      ∀ p p' : V D, (Γ D).Adj ((x * mi D true) • v D false) p →
        (Γ D).Adj ((x * mi D true) • v D false) p' → p ≠ p' →
          ¬ D.root 3 ⊓ rad D ((x * mi D true) • v D false) ≤ rad D p ⊓ rad D p' := by
  set m₁ := mi D true with hm₁
  set m₂ := mi D false with hm₂
  have hX6 : D.root 6 ⊓ Q D false = ⊥ := root_n_inf_Q D hU
  have hadj : ∀ (g : X) {y z : V D}, (Γ D).Adj y z → (Γ D).Adj (g • y) (g • z) :=
    fun g y z h => (GraphAction.adj_smul (Γ := Γ D) g y z).2 h
  have hgP : x * m₁ ∈ P D true :=
    (P D true).mul_mem (B_le_P D true (D.root_le_B le_rfl (by norm_num) hx)) (mi_mem_P D true)
  obtain ⟨s, rfl⟩ := exists_psi0 hψ hx
  have hs : s ≠ 0 := by
    rintro rfl
    exact hx1 (psi0_zero hψ)
  set g : X := ψ 0 s * m₁ with hg
  have hf : ∀ c, m₁⁻¹ * ψ 1 c * m₁ ∈ D.root 6 := fun c => by
    have := conj_mi_true_inv D (k := 2) (by norm_num) (by norm_num) (hψ.mem 1 c)
    simpa using this
  have hh5 : ∀ t : K, m₁⁻¹ * ψ 2 t * m₁ ∈ D.root 5 := fun t => by
    have := conj_mi_true_inv D (k := 3) (by norm_num) (by norm_num) (hψ.mem 2 t)
    simpa using this
  have hconj : ∀ t : K, g⁻¹ * ψ 2 t * g =
      (m₁⁻¹ * ψ 1 (d43Tr hσ (s * t)) * m₁) * (m₁⁻¹ * ψ 2 t * m₁) := by
    intro t
    rw [show g⁻¹ * ψ 2 t * g = m₁⁻¹ * ((ψ 0 s)⁻¹ * ψ 2 t * ψ 0 s) * m₁ by rw [hg]; group,
      conj_psi_zero_two hψ s t]
    group
  have hmemQ : ∀ t : K, g⁻¹ * ψ 2 t * g ∈ Q D false ↔ d43Tr hσ (s * t) = 0 := by
    intro t
    rw [hconj t]
    have h5 : m₁⁻¹ * ψ 2 t * m₁ ∈ Q D false :=
      root_le_Q_false D (k := 5) (by norm_num) (by norm_num) hU (hh5 t)
    constructor
    · intro h
      have h1 : m₁⁻¹ * ψ 1 (d43Tr hσ (s * t)) * m₁ ∈ D.root 6 ⊓ Q D false := by
        refine ⟨hf _, ?_⟩
        have e : m₁⁻¹ * ψ 1 (d43Tr hσ (s * t)) * m₁ =
            (m₁⁻¹ * ψ 1 (d43Tr hσ (s * t)) * m₁ * (m₁⁻¹ * ψ 2 t * m₁)) *
              (m₁⁻¹ * ψ 2 t * m₁)⁻¹ := by group
        rw [e]
        exact (Q D false).mul_mem h ((Q D false).inv_mem h5)
      rw [hX6, Subgroup.mem_bot] at h1
      have h2 : ψ 1 (d43Tr hσ (s * t)) = 1 := by
        calc ψ 1 (d43Tr hσ (s * t)) = m₁ * (m₁⁻¹ * ψ 1 (d43Tr hσ (s * t)) * m₁) * m₁⁻¹ := by
              group
          _ = 1 := by rw [h1]; group
      exact hψ.inj 1 (h2.trans (psi_zero hψ 1).symm)
    · intro h
      rw [h, psi1_zero hψ, mul_one, inv_mul_cancel, one_mul]
      exact h5
  have key : ∀ {w : V D}, (Γ D).Adj (g • v D false) w → w ≠ v D true →
      ∃ z ∈ D.root 6, g⁻¹ • w = (z * m₂) • v D true := by
    intro w hw hwv
    have hw1 : (Γ D).Adj (v D false) (g⁻¹ • w) := by
      have := hadj g⁻¹ hw
      rwa [inv_smul_smul] at this
    rcases nbr_false D hw1 with h2 | h2
    · exfalso
      apply hwv
      rw [← smul_inv_smul g w, h2, (smul_v_eq_iff D g true).2 hgP]
    · exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro hle
    have h1 : ψ 2 (s⁻¹ : K) ∈ rad D (g • v D false) := hle (hψ.mem 2 _)
    rw [mem_rad_smul_iff, rad_v, hmemQ, mul_inv_cancel₀ hs] at h1
    have h2 : d43Tr hσ (1 : K) = 1 := by
      have := d43Tr_fixed (hσ := hσ) (1 : fixedField σ)
      simpa using this
    rw [h2] at h1
    exact one_ne_zero h1
  · intro w w' hw hw' hwv hw'v
    obtain ⟨z, hz, hzw⟩ := key hw hwv
    obtain ⟨z', hz', hzw'⟩ := key hw' hw'v
    have hd : z' * z⁻¹ ∈ D.root 6 := (D.root 6).mul_mem hz' ((D.root 6).inv_mem hz)
    have hd2 : m₁ * (z' * z⁻¹) * m₁⁻¹ ∈ D.root 2 := by
      have := conj_mi_true D (k := 6) (by norm_num) (by norm_num) hd
      simpa using this
    obtain ⟨c, hc⟩ := exists_psi1 hψ hd2
    obtain ⟨t, ht⟩ := exists_trace_eq (hσ := hσ) hs c
    refine ⟨ψ 2 t, hψ.mem 2 t, ?_⟩
    obtain ⟨h5, hh5def⟩ : ∃ h5 : X, h5 = m₁⁻¹ * ψ 2 t * m₁ := ⟨_, rfl⟩
    have hgt : g⁻¹ * ψ 2 t * g = (z' * z⁻¹) * h5 := by
      rw [hconj t, ht, hc, hh5def]
      group
    have hcomm := commute_five_six hψ (hh5def ▸ hh5 t) hz
    have hm : (m₂⁻¹ * h5 * m₂) • v D true = v D true := by
      have := conj_mi_false_inv D (k := 5) (by norm_num) (by norm_num) (hh5def ▸ hh5 t)
      exact (smul_v_eq_iff D _ true).2 (B_le_P D true (D.root_le_B le_rfl (by norm_num)
        (by simpa using this)))
    calc ψ 2 t • w = g • ((g⁻¹ * ψ 2 t * g) • (g⁻¹ • w)) := by
          simp only [mul_smul, smul_inv_smul]
      _ = g • (((z' * z⁻¹) * h5 * (z * m₂)) • v D true) := by
          rw [hgt, hzw]
          congr 1
          rw [smul_smul]
      _ = g • ((z' * m₂) • v D true) := by
          congr 1
          calc ((z' * z⁻¹) * h5 * (z * m₂)) • v D true
              = (z' * m₂ * (m₂⁻¹ * h5 * m₂)) • v D true := by
                congr 1
                calc (z' * z⁻¹) * h5 * (z * m₂) = z' * z⁻¹ * (h5 * z) * m₂ := by group
                  _ = z' * z⁻¹ * (z * h5) * m₂ := by rw [hcomm]
                  _ = z' * m₂ * (m₂⁻¹ * h5 * m₂) := by group
            _ = (z' * m₂) • v D true := by rw [mul_smul, hm]
      _ = w' := by rw [← hzw', smul_inv_smul]
  · intro p p' hp hp' hpp hle
    obtain ⟨t₀, ht₀, htr⟩ := exists_trace_eq_zero (hσ := hσ) hσ1 hs
    have ha₀ : ψ 2 t₀ ≠ 1 := fun h => ht₀ (hψ.inj 2 (h.trans (psi2_zero hψ).symm))
    have ha₀e : ψ 2 t₀ ∈ rad D (g • v D false) := by
      rw [mem_rad_smul_iff, rad_v, hmemQ]
      exact htr
    have hmem := hle (Subgroup.mem_inf.2 ⟨hψ.mem 2 t₀, ha₀e⟩)
    have hex : ∃ p₁, (Γ D).Adj (g • v D false) p₁ ∧ p₁ ≠ v D true ∧ ψ 2 t₀ ∈ rad D p₁ := by
      by_cases hp1 : p = v D true
      · exact ⟨p', hp', fun h => hpp (hp1.trans h.symm), (Subgroup.mem_inf.1 hmem).2⟩
      · exact ⟨p, hp, hp1, (Subgroup.mem_inf.1 hmem).1⟩
    obtain ⟨p₁, hp₁, hp₁v, hap⟩ := hex
    obtain ⟨z, hz, hzp⟩ := key hp₁ hp₁v
    have hp₁eq : p₁ = (g * (z * m₂)) • v D true := by
      rw [mul_smul, ← hzp, smul_inv_smul]
    rw [hp₁eq, mem_rad_smul_iff, rad_v] at hap
    obtain ⟨h5, hh5def⟩ : ∃ h5 : X, h5 = m₁⁻¹ * ψ 2 t₀ * m₁ := ⟨_, rfl⟩
    have hg0 : g⁻¹ * ψ 2 t₀ * g = h5 := by
      rw [hconj t₀, htr, psi1_zero hψ, hh5def]
      group
    have hcomm := commute_five_six hψ (hh5def ▸ hh5 t₀) hz
    have e : (g * (z * m₂))⁻¹ * ψ 2 t₀ * (g * (z * m₂)) = m₂⁻¹ * h5 * m₂ := by
      calc (g * (z * m₂))⁻¹ * ψ 2 t₀ * (g * (z * m₂))
          = m₂⁻¹ * z⁻¹ * (g⁻¹ * ψ 2 t₀ * g) * z * m₂ := by group
        _ = m₂⁻¹ * (z⁻¹ * (h5 * z)) * m₂ := by rw [hg0]; group
        _ = m₂⁻¹ * h5 * m₂ := by rw [hcomm]; group
    rw [e] at hap
    have h1 : m₂⁻¹ * h5 * m₂ ∈ D.root 1 ⊓ Q D true := by
      refine ⟨?_, hap⟩
      have := conj_mi_false_inv D (k := 5) (by norm_num) (by norm_num) (hh5def ▸ hh5 t₀)
      simpa using this
    rw [root_one_inf_Q D hU, Subgroup.mem_bot] at h1
    apply ha₀
    calc ψ 2 t₀ = m₁ * (m₂ * (m₂⁻¹ * h5 * m₂) * m₂⁻¹) * m₁⁻¹ := by rw [hh5def]; group
      _ = 1 := by rw [h1]; group

end Lemma61

end CFSG.Quasithin.RonanE114Low
