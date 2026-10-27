module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4SylowStruct
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open scoped commutatorElement

namespace D4Syl

variable {K : Type} [Field K] {σ : K ≃+* K} {k : Subfield K} {P : Type} [Group P]
  (D : D4Syl K σ k P)

include D in
theorem σ_of_mem (c : k) : σ (c : K) = c := (D.hk c).1 c.2

theorem Tr_add (a b : K) : D.Tr (a + b) = D.Tr a + D.Tr b := by
  apply Subtype.ext
  rw [Subfield.coe_add, D.hTr, D.hTr, D.hTr]
  simp only [map_add]
  ring

theorem Tr_smul (c : k) (a : K) : D.Tr ((c : K) * a) = c * D.Tr a := by
  apply Subtype.ext
  rw [Subfield.coe_mul, D.hTr, D.hTr]
  simp only [map_mul, D.σ_of_mem]
  ring

theorem Tr_zero : D.Tr 0 = 0 := by
  have h := D.Tr_add 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem Tr_one : D.Tr 1 = 1 := by
  apply Subtype.ext
  rw [D.hTr, map_one, map_one]
  have h := D.add_self (1 : K)
  rw [Subfield.coe_one]
  linear_combination (1 : K) * h + (1 : K) * 0

theorem Tr_mul_inv {x : K} (hx : x ≠ 0) : D.Tr (x * x⁻¹) = 1 := by
  rw [mul_inv_cancel₀ hx, D.Tr_one]

@[expose] noncomputable def BT : LinearMap.BilinForm k K :=
  LinearMap.mk₂ k (fun s v : K => D.Tr (s * v))
    (fun m₁ m₂ n => by rw [add_mul, D.Tr_add])
    (fun c m n => by
      rw [Subfield.smul_def, smul_eq_mul, mul_assoc, D.Tr_smul, smul_eq_mul])
    (fun m n₁ n₂ => by rw [mul_add, D.Tr_add])
    (fun c m n => by
      rw [Subfield.smul_def, smul_eq_mul, mul_left_comm, D.Tr_smul, smul_eq_mul])

theorem BT_apply (s v : K) : D.BT s v = D.Tr (s * v) := rfl

theorem BT_nondegenerate : D.BT.Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · by_contra hne
    have h := hx x⁻¹
    rw [D.BT_apply, D.Tr_mul_inv hne] at h
    exact one_ne_zero h
  · by_contra hne
    have h := hy y⁻¹
    rw [D.BT_apply, mul_comm, D.Tr_mul_inv hne] at h
    exact one_ne_zero h

@[expose] def omega (w w' : k × K × K × k) : k :=
  w.1 * w'.2.2.2 + w'.1 * w.2.2.2 + D.Tr (w.2.1 * w'.2.2.1 + w'.2.1 * w.2.2.1)

theorem omega_comm (w w' : k × K × K × k) : D.omega w w' = D.omega w' w := by
  unfold omega
  have : w.2.1 * w'.2.2.1 + w'.2.1 * w.2.2.1 = w'.2.1 * w.2.2.1 + w.2.1 * w'.2.2.1 := add_comm _ _
  rw [this]
  ring

@[expose] noncomputable def omegaB : LinearMap.BilinForm k (k × K × K × k) :=
  LinearMap.mk₂ k (fun w w' => D.omega w w')
    (fun m₁ m₂ n => by
      unfold omega
      have : (m₁ + m₂).2.1 * n.2.2.1 + n.2.1 * (m₁ + m₂).2.2.1 =
          (m₁.2.1 * n.2.2.1 + n.2.1 * m₁.2.2.1) + (m₂.2.1 * n.2.2.1 + n.2.1 * m₂.2.2.1) := by
        simp only [Prod.fst_add, Prod.snd_add]; ring
      rw [this, D.Tr_add]
      simp only [Prod.fst_add, Prod.snd_add]
      ring)
    (fun c m n => by
      unfold omega
      have : (c • m).2.1 * n.2.2.1 + n.2.1 * (c • m).2.2.1 =
          (c : K) * (m.2.1 * n.2.2.1 + n.2.1 * m.2.2.1) := by
        simp only [Prod.smul_snd, Prod.smul_fst, Subfield.smul_def, smul_eq_mul]; ring
      rw [this, D.Tr_smul]
      simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
      ring)
    (fun m n₁ n₂ => by
      unfold omega
      have : m.2.1 * (n₁ + n₂).2.2.1 + (n₁ + n₂).2.1 * m.2.2.1 =
          (m.2.1 * n₁.2.2.1 + n₁.2.1 * m.2.2.1) + (m.2.1 * n₂.2.2.1 + n₂.2.1 * m.2.2.1) := by
        simp only [Prod.fst_add, Prod.snd_add]; ring
      rw [this, D.Tr_add]
      simp only [Prod.fst_add, Prod.snd_add]
      ring)
    (fun c m n => by
      unfold omega
      have : m.2.1 * (c • n).2.2.1 + (c • n).2.1 * m.2.2.1 =
          (c : K) * (m.2.1 * n.2.2.1 + n.2.1 * m.2.2.1) := by
        simp only [Prod.smul_snd, Prod.smul_fst, Subfield.smul_def, smul_eq_mul]; ring
      rw [this, D.Tr_smul]
      simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
      ring)

theorem omegaB_apply (w w' : k × K × K × k) : D.omegaB w w' = D.omega w w' := rfl

theorem omegaB_separatingLeft : D.omegaB.SeparatingLeft := by
  rintro ⟨b, u, v, e⟩ h
  have h1 := h (0, 0, 0, 1)
  have h2 := h (1, 0, 0, 0)
  have h3 : ∀ v' : K, D.Tr (u * v') = 0 := fun v' => by
    have := h (0, 0, v', 0)
    simpa [omegaB_apply, omega] using this
  have h4 : ∀ u' : K, D.Tr (u' * v) = 0 := fun u' => by
    have := h (0, u', 0, 0)
    simpa [omegaB_apply, omega] using this
  simp [omegaB_apply, omega, D.Tr_zero] at h1 h2
  have hu : u = 0 := by
    by_contra hne
    have := h3 u⁻¹
    rw [D.Tr_mul_inv hne] at this
    exact one_ne_zero this
  have hv : v = 0 := by
    by_contra hne
    have := h4 v⁻¹
    rw [mul_comm, D.Tr_mul_inv hne] at this
    exact one_ne_zero this
  rw [h1, h2, hu, hv]
  rfl

theorem omegaB_nondegenerate : D.omegaB.Nondegenerate := by
  refine ⟨D.omegaB_separatingLeft, fun y hy => D.omegaB_separatingLeft y fun x => ?_⟩
  rw [omegaB_apply, omega_comm, ← omegaB_apply]
  exact hy x

end D4Syl

theorem finrank_sub_three {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hK3 : Nat.card K = Nat.card k ^ 3) : Module.finrank k K = 3 := by
  have h := Module.natCard_eq_pow_finrank (K := k) (V := K)
  have hk : 2 ≤ Nat.card k := by
    have : 1 < Nat.card k := Finite.one_lt_card
    omega
  rw [hK3] at h
  exact (Nat.pow_right_injective hk h).symm

theorem finrank_V_eq {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hK3 : Nat.card K = Nat.card k ^ 3) : Module.finrank k (k × K × K × k) = 8 := by
  have := finrank_sub_three k hK3
  simp [Module.finrank_prod, this]

theorem card_le_span {K : Type} [Field K] [Finite K] (k : Subfield K) {α : Type}
    [AddCommGroup α] [Module k α] [Finite α] (S : Set α) :
    Nat.card S ≤ Nat.card k ^ Module.finrank k (Submodule.span k S) := by
  have h1 : Nat.card S ≤ Nat.card (Submodule.span k S : Set α) :=
    Nat.card_mono (Set.toFinite _) Submodule.subset_span
  have h2 := Module.natCard_eq_pow_finrank (K := k) (V := ↥(Submodule.span k S))
  exact h1.trans h2.le

namespace D4Syl

variable {K : Type} [Field K] {σ : K ≃+* K} {k : Subfield K} {P : Type} [Group P]
  (D : D4Syl K σ k P) [Finite K]

theorem card_ann_le (hK3 : Nat.card K = Nat.card k ^ 3) (S : Set K) :
    Nat.card {v : K // ∀ s ∈ S, D.Tr (s * v) = 0} ≤
      Nat.card k ^ (3 - Module.finrank k (Submodule.span k S)) := by
  have h1 : Nat.card {v : K // ∀ s ∈ S, D.Tr (s * v) = 0} ≤
      Nat.card (D.BT.orthogonal (Submodule.span k S)) := by
    refine Nat.card_le_card_of_injective (fun v => ⟨v.1, ?_⟩) ?_
    · show v.1 ∈ (Submodule.span k S).orthogonalBilin D.BT
      rw [Submodule.mem_orthogonalBilin_span]
      intro s hs
      exact v.2 s hs
    · intro x y h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have h2 := Module.natCard_eq_pow_finrank (K := k)
    (V := ↥(D.BT.orthogonal (Submodule.span k S)))
  rw [LinearMap.BilinForm.finrank_orthogonal D.BT_nondegenerate, finrank_sub_three k hK3] at h2
  exact h1.trans h2.le

theorem card_isotropic_le (hK3 : Nat.card K = Nat.card k ^ 3) (W : Set (k × K × K × k))
    (hW : ∀ w ∈ W, ∀ w' ∈ W, D.omega w w' = 0) : Nat.card W ≤ Nat.card k ^ 4 := by
  have hle : Submodule.span k W ≤ D.omegaB.orthogonal (Submodule.span k W) := by
    refine Submodule.span_le.2 fun w hw => ?_
    show w ∈ (Submodule.span k W).orthogonalBilin D.omegaB
    rw [Submodule.mem_orthogonalBilin_span]
    intro x hx
    exact hW x hx w hw
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal D.omegaB_nondegenerate, finrank_V_eq k hK3] at h1
  have h2 : Module.finrank k (Submodule.span k W) ≤ 4 := by omega
  have hk : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  exact (card_le_span k W).trans (Nat.pow_le_pow_right hk h2)

theorem Tr_coe (a : k) : D.Tr (a : K) = a := by
  apply Subtype.ext
  rw [D.hTr, D.σ_of_mem, D.σ_of_mem]
  have h := D.add_self (a : K)
  linear_combination (a : K) + h

theorem fix_eqs {s : K} {w : k × K × K × k} (h : D.Mfun s w = w) :
    (w.1 : K) * s = 0 ∧
    (σ s * σ (σ w.2.1) + σ (σ s) * σ w.2.1) + (w.1 : K) * (σ s * σ (σ s)) = 0 ∧
    D.Tr (s * w.2.2.1) + D.Tr (s * σ s * σ (σ w.2.1)) + w.1 * D.Nm s = 0 := by
  obtain ⟨b, u, v, e⟩ := w
  simp only [Mfun, Prod.mk.injEq] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa using h2
  · rw [add_assoc] at h3
    exact add_eq_left.mp h3
  · rw [add_assoc, add_assoc] at h4
    have h5 := add_eq_left.mp h4
    linear_combination h5

theorem fix_b_zero {s : K} (hs : s ≠ 0) {w : k × K × K × k} (h : D.Mfun s w = w) : w.1 = 0 := by
  have := (D.fix_eqs h).1
  rcases mul_eq_zero.1 this with h0 | h0
  · exact Subtype.ext h0
  · exact absurd h0 hs

include D in
theorem B_eq_zero {s u : K} (h : σ s * σ (σ u) + σ (σ s) * σ u = 0) : s * σ u = σ s * u := by
  have h1 := congrArg (fun x => σ (σ x)) h
  simp only [map_add, map_mul, D.hσ3, map_zero] at h1
  have h8 := D.add_self (σ s * u)
  linear_combination h1 - h8

theorem fix_u_rel {s : K} {w : k × K × K × k} (h : D.Mfun s w = w) (hb : w.1 = 0) :
    s * σ w.2.1 = σ s * w.2.1 := by
  have := (D.fix_eqs h).2.1
  rw [hb] at this
  simp only [Subfield.coe_zero, zero_mul, add_zero] at this
  exact D.B_eq_zero this

theorem fix_v_eq {s : K} {w : k × K × K × k} (h : D.Mfun s w = w) (hb : w.1 = 0) :
    D.Tr (s * w.2.2.1) = D.Tr (s * σ s * σ (σ w.2.1)) := by
  have := (D.fix_eqs h).2.2
  rw [hb] at this
  simp only [zero_mul, add_zero] at this
  have h2 := D.add_self_k (D.Tr (s * σ s * σ (σ w.2.1)))
  linear_combination this - h2

theorem mem_k_of_rel {s0 u : K} (hs0 : s0 ≠ 0) (h : s0 * σ u = σ s0 * u) :
    σ (u * s0⁻¹) = u * s0⁻¹ := by
  have hσs0 : σ s0 ≠ 0 := fun h0 => hs0 (σ.injective (by rw [h0, map_zero]))
  rw [map_mul, map_inv₀]
  field_simp
  linear_combination h

theorem Nm_ne_zero {s0 : K} (hs0 : s0 ≠ 0) : D.Nm s0 ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  rw [D.hNm] at this
  have hσs0 : σ s0 ≠ 0 := fun h0 => hs0 (σ.injective (by rw [h0, map_zero]))
  have hσσs0 : σ (σ s0) ≠ 0 := fun h0 => hσs0 (σ.injective (by rw [h0, map_zero]))
  exact mul_ne_zero (mul_ne_zero hs0 hσs0) hσσs0 this

theorem card_W_of_u_zero (S : AddSubgroup K) (W : AddSubgroup (k × K × K × k))
    (hfix : ∀ s ∈ S, ∀ w ∈ W, D.Mfun s w = w) {s0 : K} (hs0S : s0 ∈ S) (hs0 : s0 ≠ 0)
    (T : Set K) (hT : ∀ s ∈ T, s ∈ S) (hu : ∀ w ∈ W, w.2.1 = 0) :
    Nat.card W ≤ Nat.card {v : K // ∀ s ∈ T, D.Tr (s * v) = 0} * Nat.card k := by
  have hb : ∀ w ∈ W, w.1 = 0 := fun w hw => D.fix_b_zero hs0 (hfix s0 hs0S w hw)
  have hmem : ∀ w : W, ∀ s ∈ T, D.Tr (s * w.1.2.2.1) = 0 := by
    intro w s hsT
    have h := D.fix_v_eq (hfix s (hT s hsT) w.1 w.2) (hb w.1 w.2)
    rw [h, hu w.1 w.2]
    simp [D.Tr_zero]
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun w : W => ((⟨w.1.2.2.1, hmem w⟩ : {v : K // ∀ s ∈ T, D.Tr (s * v) = 0}), w.1.2.2.2)) ?_
  intro x y hxy
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
  obtain ⟨⟨b, u, v, e⟩, hx⟩ := x
  obtain ⟨⟨b', u', v', e'⟩, hy⟩ := y
  have h1 := hb _ hx
  have h2 := hb _ hy
  have h3 := hu _ hx
  have h4 := hu _ hy
  simp only at h1 h2 h3 h4 hxy
  apply Subtype.ext
  simp only
  rw [h1, h2, h3, h4, hxy.1, hxy.2]

include D in
theorem exists_k_mul {s0 u : K} (hs0 : s0 ≠ 0) (h : s0 * σ u = σ s0 * u) :
    ∃ c : k, (c : K) * s0 = u :=
  ⟨⟨u * s0⁻¹, (D.hk _).2 (mem_k_of_rel hs0 h)⟩, by
    simp [mul_assoc, inv_mul_cancel₀ hs0]⟩

theorem u_zero_B1 (S : AddSubgroup K) (W : AddSubgroup (k × K × K × k))
    (hfix : ∀ s ∈ S, ∀ w ∈ W, D.Mfun s w = w) {s0 s1 : K} (hs0S : s0 ∈ S) (hs0 : s0 ≠ 0)
    (hs1S : s1 ∈ S) (hrel : σ s1 * s0 ≠ σ s0 * s1) {w : k × K × K × k} (hw : w ∈ W) :
    w.2.1 = 0 := by
  obtain ⟨b, u, v, e⟩ := w
  have hb : b = 0 := D.fix_b_zero hs0 (hfix s0 hs0S _ hw)
  have hu0 : s0 * σ u = σ s0 * u := D.fix_u_rel (hfix s0 hs0S _ hw) hb
  have hu1 : s1 * σ u = σ s1 * u := D.fix_u_rel (hfix s1 hs1S _ hw) hb
  by_contra hne
  have h : u * (s1 * σ s0 - s0 * σ s1) = 0 := by linear_combination s0 * hu1 - s1 * hu0
  rcases mul_eq_zero.1 h with h0 | h0
  · exact hne h0
  · apply hrel
    linear_combination -h0

theorem u_zero_B2a (S : AddSubgroup K) (W : AddSubgroup (k × K × K × k))
    (hfix : ∀ s ∈ S, ∀ w ∈ W, D.Mfun s w = w) {s0 s1 : K} (hs0S : s0 ∈ S) (hs0 : s0 ≠ 0)
    (hs1S : s1 ∈ S) (hs1 : s1 ≠ 0) (hne : s1 ≠ s0) (hrel : σ s1 * s0 = σ s0 * s1)
    {w : k × K × K × k} (hw : w ∈ W) : w.2.1 = 0 := by
  obtain ⟨b, u, v, e⟩ := w
  have hb : b = 0 := D.fix_b_zero hs0 (hfix s0 hs0S _ hw)
  have hu0 : s0 * σ u = σ s0 * u := D.fix_u_rel (hfix s0 hs0S _ hw) hb
  have E0 : D.Tr (s0 * v) = D.Tr (s0 * σ s0 * σ (σ u)) := D.fix_v_eq (hfix s0 hs0S _ hw) hb
  have E1 : D.Tr (s1 * v) = D.Tr (s1 * σ s1 * σ (σ u)) := D.fix_v_eq (hfix s1 hs1S _ hw) hb
  obtain ⟨c, hc⟩ := D.exists_k_mul hs0 hu0
  obtain ⟨tk, htk⟩ := D.exists_k_mul hs0 (show s0 * σ s1 = σ s0 * s1 by linear_combination hrel)
  have hσs1 : σ s1 = (tk : K) * σ s0 := by rw [← htk, map_mul, D.σ_of_mem]
  have hY : D.Tr (s1 * v) = tk * D.Tr (s0 * v) := by
    have : s1 * v = (tk : K) * (s0 * v) := by rw [← htk]; ring
    rw [this, D.Tr_smul]
  have hX1 : D.Tr (s1 * σ s1 * σ (σ u)) = tk * (tk * D.Tr (s0 * σ s0 * σ (σ u))) := by
    have : s1 * σ s1 * σ (σ u) = (tk : K) * ((tk : K) * (s0 * σ s0 * σ (σ u))) := by
      rw [hσs1, ← htk]; ring
    rw [this, D.Tr_smul, D.Tr_smul]
  have hX : D.Tr (s0 * σ s0 * σ (σ u)) = c * D.Nm s0 := by
    have : s0 * σ s0 * σ (σ u) = ((c * D.Nm s0 : k) : K) := by
      rw [← hc, Subfield.coe_mul, D.hNm]
      simp only [map_mul, D.σ_of_mem]
      ring
    rw [this, D.Tr_coe]
  have htk0 : tk ≠ 0 := by
    intro h0
    rw [h0] at htk
    simp at htk
    exact hs1 htk.symm
  have htk1 : tk ≠ 1 := by
    intro h1
    rw [h1] at htk
    simp at htk
    exact hne htk.symm
  rw [hY, hX1] at E1
  have hXX : D.Tr (s0 * σ s0 * σ (σ u)) = 0 := by
    have h2 : D.Tr (s0 * σ s0 * σ (σ u)) * (tk * (1 - tk)) = 0 := by
      rw [← E0] at *
      linear_combination E1
    rcases mul_eq_zero.1 h2 with h0 | h0
    · exact h0
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 htk0
      · exact absurd (by linear_combination -h1) htk1
  rw [hX] at hXX
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 hXX with h0 | h0
    · exact h0
    · exact absurd h0 (D.Nm_ne_zero hs0)
  rw [hc0] at hc
  simp at hc
  exact hc.symm

theorem card_ann_singleton_le (hK3 : Nat.card K = Nat.card k ^ 3) {s0 : K} (hs0 : s0 ≠ 0) :
    Nat.card {v : K // ∀ s ∈ ({s0} : Set K), D.Tr (s * v) = 0} ≤ Nat.card k ^ 2 := by
  have h := D.card_ann_le hK3 ({s0} : Set K)
  have h1 : Module.finrank k (Submodule.span k ({s0} : Set K)) = 1 := finrank_span_singleton hs0
  rw [h1] at h
  exact h

theorem card_W_le (hK3 : Nat.card K = Nat.card k ^ 3) (S : AddSubgroup K)
    (W : AddSubgroup (k × K × K × k)) (hfix : ∀ s ∈ S, ∀ w ∈ W, D.Mfun s w = w)
    {s0 : K} (hs0S : s0 ∈ S) (hs0 : s0 ≠ 0) : Nat.card W ≤ Nat.card k ^ 4 := by
  let ψ : W →+ K :=
    (AddMonoidHom.fst K (K × k)).comp ((AddMonoidHom.snd k (K × K × k)).comp W.subtype)
  have hmul := AddSubgroup.card_ker_mul_card_range ψ
  have hb : ∀ w ∈ W, w.1 = 0 := fun w hw => D.fix_b_zero hs0 (hfix s0 hs0S w hw)
  have hrel : ∀ x : ψ.range, s0 * σ x.1 = σ s0 * x.1 := by
    rintro ⟨x, w, rfl⟩
    exact D.fix_u_rel (hfix s0 hs0S w.1 w.2) (hb w.1 w.2)
  have hrange : Nat.card ψ.range ≤ Nat.card k := by
    refine Nat.card_le_card_of_injective
      (fun x : ψ.range => (⟨x.1 * s0⁻¹, (D.hk _).2 (mem_k_of_rel hs0 (hrel x))⟩ : k)) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only at this
    exact Subtype.ext (mul_right_cancel₀ (inv_ne_zero hs0) this)
  let U0 : AddSubgroup (k × K × K × k) :=
    (⊥ : AddSubgroup K).comap
      ((AddMonoidHom.fst K (K × k)).comp (AddMonoidHom.snd k (K × K × k)))
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(W ⊓ U0) := by
    refine Nat.card_le_card_of_injective
      (fun w : ψ.ker => (⟨w.1.1, w.1.2, w.2⟩ : ↥(W ⊓ U0))) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hW0 := D.card_W_of_u_zero S (W ⊓ U0) (fun s hs w hw => hfix s hs w hw.1) hs0S hs0
    ({s0} : Set K) (fun s hs => by rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hs0S)
    (fun w hw => hw.2)
  have hA0 := D.card_ann_singleton_le hK3 hs0
  calc Nat.card W = Nat.card ψ.ker * Nat.card ψ.range := hmul.symm
    _ ≤ (Nat.card {v : K // ∀ s ∈ ({s0} : Set K), D.Tr (s * v) = 0} * Nat.card k) *
        Nat.card k := Nat.mul_le_mul (hker.trans hW0) hrange
    _ ≤ (Nat.card k ^ 2 * Nat.card k) * Nat.card k :=
        Nat.mul_le_mul (Nat.mul_le_mul hA0 le_rfl) le_rfl
    _ = Nat.card k ^ 4 := by ring

theorem key_card (hK3 : Nat.card K = Nat.card k ^ 3) (S : AddSubgroup K)
    (W : AddSubgroup (k × K × K × k)) (hfix : ∀ s ∈ S, ∀ w ∈ W, D.Mfun s w = w)
    (hiso : ∀ w ∈ W, ∀ w' ∈ W, D.omega w w' = 0) :
    Nat.card S * Nat.card W ≤ 2 * Nat.card k ^ 4 := by
  have hq1 : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  by_cases hS : ∀ s ∈ S, s = 0
  ·
    have hSb : S = ⊥ := (AddSubgroup.eq_bot_iff_forall S).2 hS
    have hS1 : Nat.card S = 1 := by rw [hSb]; simp
    have hW : Nat.card W ≤ Nat.card k ^ 4 := D.card_isotropic_le hK3 W hiso
    rw [hS1, one_mul]
    omega
  · push Not at hS
    obtain ⟨s0, hs0S, hs0⟩ := hS
    by_cases hB1 : ∃ s1 ∈ S, σ s1 * s0 ≠ σ s0 * s1
    ·
      obtain ⟨s1, hs1S, hrel⟩ := hB1
      have hu : ∀ w ∈ W, w.2.1 = 0 := fun w hw => D.u_zero_B1 S W hfix hs0S hs0 hs1S hrel hw
      have hW := D.card_W_of_u_zero S W hfix hs0S hs0 (S : Set K) (fun s hs => hs) hu
      have hA := D.card_ann_le hK3 (S : Set K)
      have hSle := card_le_span k (S : Set K)
      have hd : Module.finrank k (Submodule.span k (S : Set K)) ≤ 3 := by
        have := Submodule.finrank_le (Submodule.span k (S : Set K))
        rwa [finrank_sub_three k hK3] at this
      set d := Module.finrank k (Submodule.span k (S : Set K)) with hd'
      calc Nat.card S * Nat.card W ≤ Nat.card k ^ d * (Nat.card k ^ (3 - d) * Nat.card k) :=
            Nat.mul_le_mul hSle (hW.trans (Nat.mul_le_mul hA le_rfl))
        _ = Nat.card k ^ 4 := by
            rw [← pow_succ, ← pow_add]
            congr 1
            omega
        _ ≤ 2 * Nat.card k ^ 4 := by omega
    · push Not at hB1
      by_cases hB2a : ∃ s1 ∈ S, s1 ≠ 0 ∧ s1 ≠ s0
      · obtain ⟨s1, hs1S, hs1, hne⟩ := hB2a
        have hu : ∀ w ∈ W, w.2.1 = 0 := fun w hw =>
          D.u_zero_B2a S W hfix hs0S hs0 hs1S hs1 hne (hB1 s1 hs1S) hw
        have hW := D.card_W_of_u_zero S W hfix hs0S hs0 ({s0} : Set K)
          (fun s hs => by rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hs0S) hu
        have hA0 := D.card_ann_singleton_le hK3 hs0
        have hSk : Nat.card S ≤ Nat.card k := by
          refine Nat.card_le_card_of_injective
            (fun x : S => (⟨x.1 * s0⁻¹, (D.hk _).2 (mem_k_of_rel hs0 (by
              have := hB1 x.1 x.2
              linear_combination this))⟩ : k)) ?_
          intro x y hxy
          have := congrArg Subtype.val hxy
          simp only at this
          exact Subtype.ext (mul_right_cancel₀ (inv_ne_zero hs0) this)
        calc Nat.card S * Nat.card W
            ≤ Nat.card k * (Nat.card k ^ 2 * Nat.card k) :=
              Nat.mul_le_mul hSk (hW.trans (Nat.mul_le_mul hA0 le_rfl))
          _ = Nat.card k ^ 4 := by ring
          _ ≤ 2 * Nat.card k ^ 4 := by omega
      · push Not at hB2a
        have hsub : (S : Set K) ⊆ {0, s0} := by
          intro s hs
          by_cases h0 : s = 0
          · exact Or.inl h0
          · exact Or.inr (hB2a s hs h0)
        have hS2 : Nat.card S ≤ 2 := by
          have h1 : Nat.card (S : Set K) ≤ Nat.card ({0, s0} : Set K) :=
            Nat.card_mono (Set.toFinite _) hsub
          have h2 : Nat.card ({0, s0} : Set K) ≤ 2 := by
            rw [Nat.card_coe_set_eq]
            calc ({0, s0} : Set K).ncard ≤ ({s0} : Set K).ncard + 1 := Set.ncard_insert_le _ _
              _ = 2 := by rw [Set.ncard_singleton]
          exact h1.trans h2
        have hW := D.card_W_le hK3 S W hfix hs0S hs0
        calc Nat.card S * Nat.card W ≤ 2 * Nat.card k ^ 4 := Nat.mul_le_mul hS2 hW

end D4Syl

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
