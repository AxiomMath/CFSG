module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.LocalAnalysis.StandardType.GGSignedCoordSwaps

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

variable {n p : ℕ}

structure SignedNbrDatum (n p : ℕ) (xh w : Fin n → Multiplicative (ZMod p))
    (Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) : Prop where
  isSignedBlockOn : ∃ I : Finset (Fin n), IsSignedBlockOn n p I Γ
  card_fix_le : Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ Γ, u f = f} ≤ p ^ 2
  fix : ∀ u ∈ Γ, u w = w
  not_fix : ¬ ∀ u ∈ Γ, u xh = xh

private theorem mem_zpowers_iff_toAdd {n p : ℕ} (v w : Fin n → Multiplicative (ZMod p)) :
    w ∈ Subgroup.zpowers v ↔ ∃ c : ZMod p, ∀ k, toAdd (w k) = c * toAdd (v k) := by
  constructor
  · intro h
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    refine ⟨(m : ZMod p), fun k => ?_⟩
    rw [Pi.pow_apply, toAdd_zpow, zsmul_eq_mul]
  · rintro ⟨c, hc⟩
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective c
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    refine eq_of_toAdd_eq fun k => ?_
    rw [Pi.pow_apply, toAdd_zpow, zsmul_eq_mul]
    exact (hc k).symm

private theorem mem_closure_pair_toAdd {n p : ℕ}
    {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    (h : w ∈ Subgroup.closure ({xh, w₀} : Set (Fin n → Multiplicative (ZMod p)))) :
    ∃ α β : ZMod p, ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k) := by
  obtain ⟨m, n, hmn⟩ := Subgroup.mem_closure_pair.mp h
  refine ⟨(m : ZMod p), (n : ZMod p), fun k => ?_⟩
  rw [← hmn, Pi.mul_apply, Pi.pow_apply, Pi.pow_apply, toAdd_mul, toAdd_zpow, toAdd_zpow,
    zsmul_eq_mul, zsmul_eq_mul]

private theorem sign_eq_one_or_neg_one {p : ℕ} (hp : p.Prime) {x : ZMod p} (h : x * x = 1) :
    x = 1 ∨ x = -1 := by
  have := Fact.mk hp
  exact mul_self_eq_one_iff.mp h

private theorem eq_neg_of_sign_ne {x y : ZMod p} (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) (h : x ≠ y) : x = -y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

private theorem eq_of_sign_ne_neg {x δ : ZMod p} (hx : x = 1 ∨ x = -1)
    (hδ : δ = 1 ∨ δ = -1) (h : x ≠ -δ) : x = δ := by
  rcases hx with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp_all

private theorem diagAut_self_inv {n p : ℕ} {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1) :
    (diagAut d hd)⁻¹ = diagAut d hd := by
  refine inv_eq_of_mul_eq_one_right ?_
  refine MulEquiv.ext fun f => funext fun i => ?_
  show ofAdd (d i * toAdd (diagAut d hd f i)) = f i
  rw [diagAut_apply, toAdd_ofAdd, ← mul_assoc, hd i, one_mul, ofAdd_toAdd]

private theorem fix_map_conj_diagAut_iff {n p : ℕ} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ (aPermutationOn n p I).map (MulAut.conj (diagAut d hd)).toMonoidHom, u f = f) ↔
      ∀ i ∈ I, ∀ j ∈ I, d i * toAdd (f i) = d j * toAdd (f j) := by
  rw [forall_map_conj_fix_iff, forall_aPermutationOn_fix_iff]
  constructor
  · intro h i hi j hj
    have h' := h i hi j hj
    have h'' : ofAdd (d i * toAdd (f i)) = ofAdd (d j * toAdd (f j)) := by
      simpa only [diagAut_self_inv hd, diagAut_apply] using h'
    exact Multiplicative.ofAdd.injective h''
  · intro h i hi j hj
    show (diagAut d hd)⁻¹ f i = (diagAut d hd)⁻¹ f j
    rw [diagAut_self_inv hd]
    show ofAdd (d i * toAdd (f i)) = ofAdd (d j * toAdd (f j))
    rw [h i hi j hj]

private def BDFix {n p : ℕ} (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) : Prop :=
  ∀ i ∈ I, toAdd (f i) = 0

private def SigmaFix {n p : ℕ} (d : Fin n → ZMod p) (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, d i * toAdd (f i) = d j * toAdd (f j)

private inductive BlockProfile (n p : ℕ)
    (Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) : Prop
  | bd (I : Finset (Fin n)) (hcard : n ≤ I.card + 2)
      (hfix : ∀ f, (∀ u ∈ Γ, u f = f) ↔ BDFix I f)
  | sigma (I : Finset (Fin n)) (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1)
      (hcard : n ≤ I.card + 1)
      (hfix : ∀ f, (∀ u ∈ Γ, u f = f) ↔ SigmaFix d I f)

private theorem block_profile (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {xh w : Fin n → Multiplicative (ZMod p)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (h : SignedNbrDatum n p xh w Γ) : BlockProfile n p Γ := by
  obtain ⟨I, hI⟩ := h.isSignedBlockOn
  have hcard2 := IsSignedBlockOn.le_card_add_two hp hp2 hI h.card_fix_le
  rcases hI with hB | ⟨hI2, hD⟩ | ⟨d, hd, hS⟩
  · refine BlockProfile.bd I hcard2 (fun f => ?_)
    rw [hB, forall_bBlockOn_fix_iff hp hp2 I f]
    constructor
    · intro hf i hi
      rw [hf i hi, toAdd_one]
    · intro hf i hi
      exact toAdd.injective (by simpa using hf i hi)
  · refine BlockProfile.bd I hcard2 (fun f => ?_)
    rw [hD, forall_dBlockOn_fix_iff hp hp2 hI2 f]
    constructor
    · intro hf i hi
      rw [hf i hi, toAdd_one]
    · intro hf i hi
      exact toAdd.injective (by simpa using hf i hi)
  · have hcard1 : n ≤ I.card + 1 := by
      have hc := h.card_fix_le
      rw [hS] at hc
      exact le_card_add_one_of_map_conj_aPermutationOn hp hn hc
    refine BlockProfile.sigma I d hd hcard1 ?_
    rw [hS]
    exact fix_map_conj_diagAut_iff hd

private theorem mem_of_bdFix_not {n p : ℕ} {I : Finset (Fin n)} {i0 : Fin n}
    {xh : Fin n → Multiplicative (ZMod p)} (hxh : ∀ k, k ≠ i0 → xh k = 1)
    (h : ¬ BDFix I xh) : i0 ∈ I := by
  by_contra hi0
  apply h
  intro i hi
  rw [hxh i (fun h' => hi0 (h' ▸ hi)), toAdd_one]

private theorem mem_of_sigmaFix_not {n p : ℕ} {I : Finset (Fin n)} {i0 : Fin n}
    {d : Fin n → ZMod p} {xh : Fin n → Multiplicative (ZMod p)}
    (hxh : ∀ k, k ≠ i0 → xh k = 1) (h : ¬ SigmaFix d I xh) : i0 ∈ I := by
  by_contra hi0
  apply h
  intro i hi j hj
  rw [hxh i (fun h' => hi0 (h' ▸ hi)), hxh j (fun h' => hi0 (h' ▸ hj))]
  simp

private theorem eq_one_of_bdFix {n p : ℕ} {I : Finset (Fin n)}
    {w : Fin n → Multiplicative (ZMod p)} (h : BDFix I w) : ∀ k ∈ I, w k = 1 := by
  intro k hk
  exact toAdd.injective (by simpa using h k hk)

private theorem exists_coord_of_sigmaFix {n p : ℕ} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) (hI : I.Nonempty) {w : Fin n → Multiplicative (ZMod p)}
    (h : SigmaFix d I w) : ∃ lam, ∀ k ∈ I, toAdd (w k) = d k * lam := by
  obtain ⟨z, hz⟩ := hI
  refine ⟨d z * toAdd (w z), fun k hk => ?_⟩
  have h' := h k hk z hz
  calc toAdd (w k) = d k * (d k * toAdd (w k)) := by rw [← mul_assoc, hd k, one_mul]
    _ = d k * (d z * toAdd (w z)) := by rw [h']

private inductive AxisData (n p : ℕ) (xh w : Fin n → Multiplicative (ZMod p)) (i0 : Fin n) : Prop
  | bd (I : Finset (Fin n)) (hi0 : i0 ∈ I) (hcard : n ≤ I.card + 2)
      (hw : ∀ k ∈ I, w k = 1)
  | sigma (I : Finset (Fin n)) (d : Fin n → ZMod p) (hsign : ∀ i, d i = 1 ∨ d i = -1)
      (lam : ZMod p) (hi0 : i0 ∈ I) (hcard : n ≤ I.card + 1)
      (hw : ∀ k ∈ I, toAdd (w k) = d k * lam)

private theorem axis_data (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {xh w : Fin n → Multiplicative (ZMod p)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {i0 : Fin n}
    (h : SignedNbrDatum n p xh w Γ) (hxh : ∀ k, k ≠ i0 → xh k = 1) :
    AxisData n p xh w i0 := by
  rcases block_profile hp hp2 (by omega) h with ⟨I, hcard, hfix⟩ | ⟨I, d, hd, hcard, hfix⟩
  · have hnot : ¬ BDFix I xh := fun hx => h.not_fix ((hfix xh).mpr hx)
    exact AxisData.bd I (mem_of_bdFix_not hxh hnot) hcard
      (eq_one_of_bdFix ((hfix w).mp h.fix))
  · have hnot : ¬ SigmaFix d I xh := fun hx => h.not_fix ((hfix xh).mpr hx)
    have hi0 : i0 ∈ I := mem_of_sigmaFix_not hxh hnot
    obtain ⟨lam, hw⟩ := exists_coord_of_sigmaFix hd ⟨i0, hi0⟩ ((hfix w).mp h.fix)
    exact AxisData.sigma I d (fun i => sign_eq_one_or_neg_one hp (hd i)) lam hi0 hcard hw

private theorem exists_coeff_of_mem_closure {n p : ℕ}
    {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    (hpl : w ∈ Subgroup.closure ({xh, w₀} : Set (Fin n → Multiplicative (ZMod p))))
    (hwx : w ∉ Subgroup.zpowers xh) :
    ∃ α β : ZMod p, β ≠ 0 ∧
      ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k) := by
  obtain ⟨α, β, hαβ⟩ := mem_closure_pair_toAdd hpl
  have hβ : β ≠ 0 := by
    intro h0
    apply hwx
    exact (mem_zpowers_iff_toAdd _ _).mpr ⟨α, fun k => by rw [hαβ k, h0, zero_mul, add_zero]⟩
  exact ⟨α, β, hβ, hαβ⟩

private theorem exists_mem_ne_of_one_lt_card {α : Type*} [DecidableEq α] {I : Finset α}
    {m : α} (h : 1 < I.card) : ∃ k ∈ I, k ≠ m := by
  obtain ⟨k, hkI, hkm⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := {m}) (t := I) (by simpa using h)
  exact ⟨k, hkI, by simpa using hkm⟩

private theorem exists_mem_ne_ne_of_two_lt_card {α : Type*} [DecidableEq α] {I : Finset α}
    {i j : α} (hij : i ≠ j) (h : 2 < I.card) : ∃ k ∈ I, k ≠ i ∧ k ≠ j := by
  obtain ⟨k, hkI, hk⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := {i, j}) (t := I) (by
      rw [Finset.card_pair hij]; exact h)
  exact ⟨k, hkI, by simpa using hk⟩

private theorem exists_common_ne {n : ℕ} {I I₀ : Finset (Fin n)} {i0 : Fin n}
    (hi0' : i0 ∈ I₀) (hI : n ≤ I.card + 2) (hI₀ : n ≤ I₀.card + 2)
    (hSig : n ≤ I.card + 1 ∨ n ≤ I₀.card + 1) (hn : 5 ≤ n) :
    ∃ k, k ∈ I ∧ k ∈ I₀ ∧ k ≠ i0 := by
  classical
  by_contra h
  have hsub : I₀.erase i0 ⊆ Iᶜ := by
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [Finset.mem_compl]
    intro hkI
    exact h ⟨k, hkI, hk.2, hk.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi0', Finset.card_compl, Fintype.card_fin] at hcard
  rcases hSig with hSig | hSig <;> omega

private theorem axis_case_bd_bd {n p : ℕ} {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    {i0 : Fin n} {I I₀ : Finset (Fin n)} {α β : ZMod p}
    (hxh : ∀ k, k ≠ i0 → xh k = 1)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hi0 : i0 ∈ I) (hi0' : i0 ∈ I₀) (hw : ∀ k ∈ I, w k = 1)
    (hw₀ : ∀ k ∈ I₀, w₀ k = 1) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun k => ?_⟩)
  by_cases hk : k = i0
  · subst hk
    rw [hw k hi0, hw₀ k hi0', toAdd_one, mul_zero]
  · rw [hcoord k, hxh k hk, toAdd_one, mul_zero, zero_add]

private theorem axis_case_bd_sigma {n p : ℕ} (hp : p.Prime)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {i0 : Fin n} {I I₀ : Finset (Fin n)}
    {d : Fin n → ZMod p} {α β lam : ZMod p}
    (hxh : ∀ k, k ≠ i0 → xh k = 1) (hβ : β ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hi0 : i0 ∈ I) (hi0' : i0 ∈ I₀) (hw : ∀ k ∈ I, w k = 1)
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (hw₀ : ∀ k ∈ I₀, toAdd (w₀ k) = d k * lam)
    (hex : ∃ k, k ∈ I ∧ k ∈ I₀ ∧ k ≠ i0) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  obtain ⟨k, hkI, hkI₀, hkne⟩ := hex
  have hxk : toAdd (xh k) = 0 := by rw [hxh k hkne, toAdd_one]
  have hwk : toAdd (w k) = 0 := by rw [hw k hkI, toAdd_one]
  have hwk₀ : toAdd (w₀ k) = 0 := by
    have h := hcoord k
    rw [hxk, hwk, mul_zero, zero_add] at h
    exact (coord_mul_eq_zero hp h.symm).resolve_left hβ
  have hlam : lam = 0 := by
    have hk0 : d k * lam = 0 := by rw [← hw₀ k hkI₀, hwk₀]
    exact (coord_mul_eq_zero hp hk0).resolve_left (coord_sign_ne_zero hp (hsign k))
  refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun l => ?_⟩)
  by_cases hl : l = i0
  · subst hl
    rw [hw l hi0, toAdd_one, hw₀ l hi0', hlam, mul_zero, mul_zero]
  · rw [hcoord l, hxh l hl, toAdd_one, mul_zero, zero_add]

private theorem axis_case_sigma_bd {n p : ℕ} (hp : p.Prime)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {i0 : Fin n} {I I₀ : Finset (Fin n)}
    {d : Fin n → ZMod p} {α β lam : ZMod p}
    (hxh : ∀ k, k ≠ i0 → xh k = 1)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hi0 : i0 ∈ I) (hi0' : i0 ∈ I₀)
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (hw : ∀ k ∈ I, toAdd (w k) = d k * lam)
    (hw₀ : ∀ k ∈ I₀, w₀ k = 1) (hex : ∃ k, k ∈ I ∧ k ∈ I₀ ∧ k ≠ i0) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  obtain ⟨k, hkI, hkI₀, hkne⟩ := hex
  have hxk : toAdd (xh k) = 0 := by rw [hxh k hkne, toAdd_one]
  have hwk : toAdd (w k) = 0 := by
    have h := hcoord k
    rw [hxk, mul_zero, zero_add, hw₀ k hkI₀, toAdd_one, mul_zero] at h
    exact h
  have hlam : lam = 0 := by
    have hk0 : d k * lam = 0 := by rw [← hw k hkI, hwk]
    exact (coord_mul_eq_zero hp hk0).resolve_left (coord_sign_ne_zero hp (hsign k))
  refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun l => ?_⟩)
  by_cases hl : l = i0
  · subst hl
    rw [hw l hi0, hlam, mul_zero, hw₀ l hi0', toAdd_one, mul_zero]
  · rw [hcoord l, hxh l hl, toAdd_one, mul_zero, zero_add]

private theorem axis_case_sigma_sigma_final {n p : ℕ} {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    {i0 : Fin n} {I₀ : Finset (Fin n)} {d₀ : Fin n → ZMod p} {α β lam₀ δ : ZMod p}
    (hxh : ∀ k, k ≠ i0 → xh k = 1)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hδsign : δ = 1 ∨ δ = -1) (hsign₀ : ∀ i, d₀ i = 1 ∨ d₀ i = -1)
    (hi0' : i0 ∈ I₀) (hw₀ : ∀ k ∈ I₀, toAdd (w₀ k) = d₀ k * lam₀)
    (hdi0 : toAdd (w i0) = β * lam₀ * δ) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  by_cases hδ : δ = d₀ i0
  · refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun l => ?_⟩)
    by_cases hl : l = i0
    · subst hl
      rw [hdi0, hw₀ l hi0', hδ]
      ring
    · rw [hcoord l, hxh l hl, toAdd_one, mul_zero, zero_add]
  · have hδneg : δ = -d₀ i0 := eq_neg_of_sign_ne hδsign (hsign₀ i0) hδ
    refine Or.inr ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun l => ?_⟩)
    by_cases hl : l = i0
    · subst hl
      rw [sgnAut_apply, Function.update_self, toAdd_inv, hw₀ l hi0', hdi0, hδneg]
      ring
    · rw [sgnAut_apply, Function.update_of_ne hl, hcoord l, hxh l hl,
        toAdd_one, mul_zero, zero_add]

private theorem axis_case_sigma_sigma_ne {n p : ℕ} (hp : p.Prime)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {i0 : Fin n} {I I₀ : Finset (Fin n)}
    {d d₀ : Fin n → ZMod p} {α β lam lam₀ : ZMod p}
    (hxh : ∀ k, k ≠ i0 → xh k = 1)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hi0 : i0 ∈ I) (hi0' : i0 ∈ I₀)
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (hsign₀ : ∀ i, d₀ i = 1 ∨ d₀ i = -1)
    (hw : ∀ k ∈ I, toAdd (w k) = d k * lam) (hw₀ : ∀ k ∈ I₀, toAdd (w₀ k) = d₀ k * lam₀)
    (hex : ∃ k, k ∈ I ∧ k ∈ I₀ ∧ k ≠ i0) (hlam : lam ≠ 0) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  obtain ⟨k, hkI, hkI₀, hkne⟩ := hex
  have hxk : toAdd (xh k) = 0 := by rw [hxh k hkne, toAdd_one]
  have hrel : d k * lam = β * (d₀ k * lam₀) := by
    calc d k * lam = toAdd (w k) := (hw k hkI).symm
      _ = α * toAdd (xh k) + β * toAdd (w₀ k) := hcoord k
      _ = β * (d₀ k * lam₀) := by rw [hxk, hw₀ k hkI₀, mul_zero, zero_add]
  have hlam₀ : lam₀ ≠ 0 := by
    intro h0
    apply hlam
    have hr := hrel
    rw [h0, mul_zero, mul_zero] at hr
    exact (coord_mul_eq_zero hp hr).resolve_left (coord_sign_ne_zero hp (hsign k))
  have hrel' : lam = β * lam₀ * (d k * d₀ k) := by
    have hdk2 : d k * d k = 1 := coord_sign_mul_self (hsign k)
    calc lam = d k * (d k * lam) := by rw [← mul_assoc, hdk2, one_mul]
      _ = d k * (β * (d₀ k * lam₀)) := by rw [hrel]
      _ = β * lam₀ * (d k * d₀ k) := by ring
  set δ : ZMod p := d i0 * d k * d₀ k with hδdef
  have hδsign : δ = 1 ∨ δ = -1 := by
    rcases hsign i0 with h1 | h1 <;> rcases hsign k with h2 | h2 <;>
      rcases hsign₀ k with h3 | h3 <;> simp [hδdef, h1, h2, h3]
  have hdi0 : toAdd (w i0) = β * lam₀ * δ := by
    rw [hw i0 hi0, hrel', hδdef]
    ring
  exact axis_case_sigma_sigma_final hxh hcoord hδsign hsign₀ hi0' hw₀ hdi0

private theorem axis_case_sigma_sigma {n p : ℕ} (hp : p.Prime)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {i0 : Fin n} {I I₀ : Finset (Fin n)}
    {d d₀ : Fin n → ZMod p} {α β lam lam₀ : ZMod p}
    (hxh : ∀ k, k ≠ i0 → xh k = 1) (hβ : β ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hi0 : i0 ∈ I) (hi0' : i0 ∈ I₀)
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (hsign₀ : ∀ i, d₀ i = 1 ∨ d₀ i = -1)
    (hw : ∀ k ∈ I, toAdd (w k) = d k * lam) (hw₀ : ∀ k ∈ I₀, toAdd (w₀ k) = d₀ k * lam₀)
    (hex : ∃ k, k ∈ I ∧ k ∈ I₀ ∧ k ≠ i0) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  obtain ⟨k, hkI, hkI₀, hkne⟩ := hex
  have hxk : toAdd (xh k) = 0 := by rw [hxh k hkne, toAdd_one]
  have hrel : d k * lam = β * (d₀ k * lam₀) := by
    calc d k * lam = toAdd (w k) := (hw k hkI).symm
      _ = α * toAdd (xh k) + β * toAdd (w₀ k) := hcoord k
      _ = β * (d₀ k * lam₀) := by rw [hxk, hw₀ k hkI₀, mul_zero, zero_add]
  by_cases hlam : lam = 0
  · have hb : β * (d₀ k * lam₀) = 0 := by rw [← hrel, hlam, mul_zero]
    have hlam₀ : lam₀ = 0 := by
      exact (coord_mul_eq_zero hp ((coord_mul_eq_zero hp hb).resolve_left hβ)).resolve_left
        (coord_sign_ne_zero hp (hsign₀ k))
    refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun l => ?_⟩)
    by_cases hl : l = i0
    · subst hl
      rw [hw l hi0, hlam, hw₀ l hi0', hlam₀]
      simp
    · rw [hcoord l, hxh l hl, toAdd_one, mul_zero, zero_add]
  · exact axis_case_sigma_sigma_ne hp hxh hcoord hi0 hi0' hsign hsign₀ hw hw₀
      ⟨k, hkI, hkI₀, hkne⟩ hlam

private theorem toAdd_sgnAut_apply {n p : ℕ} (m k : Fin n)
    (xh : Fin n → Multiplicative (ZMod p)) :
    toAdd ((sgnAut m xh) k) = if k = m then -toAdd (xh k) else toAdd (xh k) := by
  rw [sgnAut_apply]
  by_cases hk : k = m
  · subst hk
    rw [Function.update_self, toAdd_inv, if_pos rfl]
  · rw [Function.update_of_ne hk, if_neg hk]

private theorem toAdd_sgnAut_sgnAut_apply {n p : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (xh : Fin n → Multiplicative (ZMod p)) :
    toAdd ((sgnAut i (sgnAut j xh)) k) =
      if k = i ∨ k = j then -toAdd (xh k) else toAdd (xh k) := by
  rw [toAdd_sgnAut_apply]
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl, toAdd_sgnAut_apply, if_neg hij, if_pos (Or.inl rfl)]
  · rw [if_neg hki, toAdd_sgnAut_apply]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl, if_pos (Or.inr rfl)]
    · rw [if_neg hkj, if_neg (fun h => h.elim hki hkj)]

private theorem sigmaFix_of_const {n p : ℕ} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    {xh : Fin n → Multiplicative (ZMod p)} (hxh : ∀ a b, xh a = xh b) {δ : ZMod p}
    (h : ∀ a ∈ I, d a = δ) : SigmaFix d I xh := by
  intro a ha b hb
  rw [h a ha, h b hb, hxh a b]

private theorem exists_pair_eq_neg {n p : ℕ} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    {i j : Fin n} {δ : ZMod p} (hsign : ∀ a, d a = 1 ∨ d a = -1)
    (hδsign : δ = 1 ∨ δ = -1) (hnot : ¬ ∀ a ∈ I, d a = δ)
    (hδ : ∀ k ∈ I, k ≠ i → k ≠ j → d k = δ) :
    ∃ a, (a = i ∨ a = j) ∧ a ∈ I ∧ d a = -δ := by
  by_contra h
  have h' : ∀ a, (a = i ∨ a = j) → a ∈ I → d a ≠ -δ :=
    fun a ha haI had => h ⟨a, ha, haI, had⟩
  apply hnot
  intro a ha
  by_cases hai : a = i
  · subst hai
    exact eq_of_sign_ne_neg (hsign a) hδsign (h' a (Or.inl rfl) ha)
  · by_cases haj : a = j
    · subst haj
      exact eq_of_sign_ne_neg (hsign a) hδsign (h' a (Or.inr rfl) ha)
    · exact hδ a ha hai haj

private theorem const_axis_bd_case {n p : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {m : Fin n}
    {α β : ZMod p} (hw₀ : ∀ k, k ≠ m → w₀ k = 1)
    (hc : ∀ i, toAdd (xh i) ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hcard : n ≤ I.card + 2) (hw : ∀ k ∈ I, w k = 1) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut m xh) := by
  have hcard3 : 1 < I.card := by omega
  obtain ⟨k, hkI, hkm⟩ := exists_mem_ne_of_one_lt_card hcard3
  have hα : α = 0 := by
    have h := hcoord k
    rw [hw k hkI, toAdd_one, hw₀ k hkm, toAdd_one, mul_zero,
      add_zero] at h
    exact (coord_mul_eq_zero hp (by rw [← h])).resolve_right (hc k)
  refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun k => ?_⟩)
  rw [hcoord k, hα, zero_mul, zero_add]

private theorem eq_of_mul_eq_mul_right {p : ℕ} (hp : p.Prime) {a b c : ZMod p} (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have h' : (a - b) * c = 0 := by rw [sub_mul, h, sub_self]
  exact sub_eq_zero.mp ((coord_mul_eq_zero hp h').resolve_right hc)

private theorem const_axis_sigma_ne {n p : ℕ} (hp : p.Prime)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    {m : Fin n} {α β lam : ZMod p} (hxh : ∀ a b, xh a = xh b)
    (hw₀ : ∀ k, k ≠ m → w₀ k = 1) (hc : ∀ i, toAdd (xh i) ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hα : α ≠ 0) (hsign : ∀ i, d i = 1 ∨ d i = -1)
    (hw : ∀ k ∈ I, toAdd (w k) = d k * lam) (hnot : ¬ SigmaFix d I xh)
    {k₀ : Fin n} (hk₀m : k₀ ≠ m)
    (hrel : d k₀ * lam = α * toAdd (xh m)) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut m xh) := by
  have hc0 : α * toAdd (xh m) ≠ 0 := coord_mul_ne_zero hp hα (hc m)
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrel
    exact hc0 hrel.symm
  set δ : ZMod p := d k₀ with hδdef
  have hδsign : δ = 1 ∨ δ = -1 := hsign k₀
  have hδrel : δ * lam = α * toAdd (xh m) := by rw [hδdef]; exact hrel
  have hδ : ∀ k ∈ I, k ≠ m → d k = δ := by
    intro k hk hkm
    have hkrel : d k * lam = α * toAdd (xh m) := by
      calc d k * lam = toAdd (w k) := (hw k hk).symm
        _ = α * toAdd (xh k) + β * toAdd (w₀ k) := hcoord k
        _ = α * toAdd (xh m) := by
          rw [hxh k m, hw₀ k hkm, toAdd_one, mul_zero, add_zero]
    rw [hδdef]
    exact eq_of_mul_eq_mul_right hp hlam (by rw [hkrel, hrel])
  have hm : m ∈ I := by
    by_contra hm
    exact hnot (sigmaFix_of_const hxh (fun k hk => hδ k hk (fun h => hm (h ▸ hk))))
  have hdm : d m = -δ := by
    have hne : d m ≠ δ := by
      intro hdmδ
      apply hnot
      exact sigmaFix_of_const hxh (fun k hk => by
        by_cases hkm : k = m
        · rw [hkm, hdmδ]
        · exact hδ k hk hkm)
    exact eq_neg_of_sign_ne (hsign m) hδsign hne
  refine Or.inr ((mem_zpowers_iff_toAdd _ _).mpr ⟨α, fun k => ?_⟩)
  rw [toAdd_sgnAut_apply]
  by_cases hkm : k = m
  · subst hkm
    rw [if_pos rfl, hw k hm, hdm]
    calc -δ * lam = -(δ * lam) := neg_mul ..
      _ = -(α * toAdd (xh k)) := by rw [hδrel]
      _ = α * -toAdd (xh k) := by ring
  · rw [if_neg hkm, hcoord k, hxh k m, hw₀ k hkm, toAdd_one, mul_zero, add_zero]

private theorem const_axis_sigma_case {n p : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    {m : Fin n} {α β lam : ZMod p} (hxh : ∀ a b, xh a = xh b)
    (hw₀ : ∀ k, k ≠ m → w₀ k = 1) (hc : ∀ i, toAdd (xh i) ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (hcard : n ≤ I.card + 1)
    (hw : ∀ k ∈ I, toAdd (w k) = d k * lam) (hnot : ¬ SigmaFix d I xh) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut m xh) := by
  have hcard3 : 1 < I.card := by omega
  obtain ⟨k₀, hk₀I, hk₀m⟩ := exists_mem_ne_of_one_lt_card hcard3
  have hrel : d k₀ * lam = α * toAdd (xh m) := by
    calc d k₀ * lam = toAdd (w k₀) := (hw k₀ hk₀I).symm
      _ = α * toAdd (xh k₀) + β * toAdd (w₀ k₀) := hcoord k₀
      _ = α * toAdd (xh m) := by
        rw [hxh k₀ m, hw₀ k₀ hk₀m, toAdd_one, mul_zero, add_zero]
  by_cases hα : α = 0
  · refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun k => ?_⟩)
    rw [hcoord k, hα, zero_mul, zero_add]
  · exact const_axis_sigma_ne hp hxh hw₀ hc hcoord hα hsign hw hnot hk₀m hrel

private theorem const_pair_bd_case {n p : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {i j : Fin n}
    {α β : ZMod p} (hij : i ≠ j) (hw₀ : ∀ k, k ≠ i → k ≠ j → w₀ k = 1)
    (hc : ∀ k, toAdd (xh k) ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hcard : n ≤ I.card + 2) (hw : ∀ k ∈ I, w k = 1) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i (sgnAut j xh)) := by
  have hcard3 : 2 < I.card := by omega
  obtain ⟨k, hkI, hki, hkj⟩ := exists_mem_ne_ne_of_two_lt_card hij hcard3
  have hα : α = 0 := by
    have h := hcoord k
    rw [hw k hkI, toAdd_one, hw₀ k hki hkj, toAdd_one,
      mul_zero, add_zero] at h
    exact (coord_mul_eq_zero hp (by rw [← h])).resolve_right (hc k)
  refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun k => ?_⟩)
  rw [hcoord k, hα, zero_mul, zero_add]

private theorem const_pair_sigma_final {n p : ℕ} {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    {i j : Fin n} {α β : ZMod p} (hxh : ∀ a b, xh a = xh b) (hij : i ≠ j)
    (hw₀ : ∀ k, k ≠ i → k ≠ j → w₀ k = 1)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hwi : toAdd (w i) = -α * toAdd (xh i)) (hwj : toAdd (w j) = -α * toAdd (xh i)) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i (sgnAut j xh)) := by
  refine Or.inr ((mem_zpowers_iff_toAdd _ _).mpr ⟨α, fun k => ?_⟩)
  rw [toAdd_sgnAut_sgnAut_apply hij]
  by_cases hki : k = i
  · subst hki
    rw [if_pos (Or.inl rfl), hwi]
    ring
  · by_cases hkj : k = j
    · subst hkj
      rw [if_pos (Or.inr rfl), hwj, hxh i k]
      ring
    · rw [if_neg (fun h => h.elim hki hkj), hcoord k, hxh k i, hw₀ k hki hkj,
        toAdd_one, mul_zero, add_zero]

private theorem const_pair_sigma_ne {n p : ℕ} (hp : p.Prime)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    {i j : Fin n} {α β lam : ZMod p} (hxh : ∀ a b, xh a = xh b) (hij : i ≠ j)
    (hw₀ij : w₀ i = w₀ j) (hw₀ : ∀ k, k ≠ i → k ≠ j → w₀ k = 1)
    (hc : ∀ k, toAdd (xh k) ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hα : α ≠ 0) (hsign : ∀ i, d i = 1 ∨ d i = -1)
    (hw : ∀ k ∈ I, toAdd (w k) = d k * lam) (hnot : ¬ SigmaFix d I xh)
    {k₀ : Fin n} (hk₀i : k₀ ≠ i) (hk₀j : k₀ ≠ j)
    (hrel : d k₀ * lam = α * toAdd (xh i)) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i (sgnAut j xh)) := by
  have hc0 : α * toAdd (xh i) ≠ 0 := coord_mul_ne_zero hp hα (hc i)
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrel
    exact hc0 hrel.symm
  set δ : ZMod p := d k₀ with hδdef
  have hδsign : δ = 1 ∨ δ = -1 := hsign k₀
  have hδrel : δ * lam = α * toAdd (xh i) := by rw [hδdef]; exact hrel
  have hδ : ∀ k ∈ I, k ≠ i → k ≠ j → d k = δ := by
    intro k hk hki hkj
    have hkrel : d k * lam = α * toAdd (xh i) := by
      calc d k * lam = toAdd (w k) := (hw k hk).symm
        _ = α * toAdd (xh k) + β * toAdd (w₀ k) := hcoord k
        _ = α * toAdd (xh i) := by
          rw [hxh k i, hw₀ k hki hkj, toAdd_one, mul_zero, add_zero]
    rw [hδdef]
    exact eq_of_mul_eq_mul_right hp hlam (by rw [hkrel, hrel])
  have hnotconst : ¬ ∀ a ∈ I, d a = δ := fun hc => hnot (sigmaFix_of_const hxh hc)
  obtain ⟨a, hai, haI, had⟩ := exists_pair_eq_neg hsign hδsign hnotconst hδ
  have hwa : toAdd (w a) = -α * toAdd (xh i) := by
    rw [hw a haI, had, neg_mul, hδrel]
    ring
  have hji : toAdd (w i) = toAdd (w j) := by
    rw [hcoord i, hcoord j, hxh i j, hw₀ij]
  have hwi : toAdd (w i) = -α * toAdd (xh i) := by
    rcases hai with rfl | rfl
    · simpa using hwa
    · rw [hji, hwa]
  have hwj : toAdd (w j) = -α * toAdd (xh i) := by rw [← hji, hwi]
  exact const_pair_sigma_final hxh hij hw₀ hcoord hwi hwj

private theorem const_pair_sigma_case {n p : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {d : Fin n → ZMod p}
    {i j : Fin n} {α β lam : ZMod p} (hxh : ∀ a b, xh a = xh b) (hij : i ≠ j)
    (hw₀ij : w₀ i = w₀ j) (hw₀ : ∀ k, k ≠ i → k ≠ j → w₀ k = 1)
    (hc : ∀ k, toAdd (xh k) ≠ 0)
    (hcoord : ∀ k, toAdd (w k) = α * toAdd (xh k) + β * toAdd (w₀ k))
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (hcard : n ≤ I.card + 1)
    (hw : ∀ k ∈ I, toAdd (w k) = d k * lam) (hnot : ¬ SigmaFix d I xh) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i (sgnAut j xh)) := by
  have hcard3 : 2 < I.card := by omega
  obtain ⟨k₀, hk₀I, hk₀i, hk₀j⟩ := exists_mem_ne_ne_of_two_lt_card hij hcard3
  have hrel : d k₀ * lam = α * toAdd (xh i) := by
    calc d k₀ * lam = toAdd (w k₀) := (hw k₀ hk₀I).symm
      _ = α * toAdd (xh k₀) + β * toAdd (w₀ k₀) := hcoord k₀
      _ = α * toAdd (xh i) := by
        rw [hxh k₀ i, hw₀ k₀ hk₀i hk₀j, toAdd_one, mul_zero, add_zero]
  by_cases hα : α = 0
  · refine Or.inl ((mem_zpowers_iff_toAdd _ _).mpr ⟨β, fun k => ?_⟩)
    rw [hcoord k, hα, zero_mul, zero_add]
  · exact const_pair_sigma_ne hp hxh hij hw₀ij hw₀ hc hcoord hα hsign hw hnot hk₀i
      hk₀j hrel

theorem SignedNbrDatum.mem_zpowers_or_of_axis (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    {Γ₀ Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {i0 : Fin n}
    (hxh : ∀ k, k ≠ i0 → xh k = 1) (h₀ : SignedNbrDatum n p xh w₀ Γ₀)
    (h : SignedNbrDatum n p xh w Γ)
    (hpl : w ∈ Subgroup.closure ({xh, w₀} : Set (Fin n → Multiplicative (ZMod p))))
    (hwx : w ∉ Subgroup.zpowers xh) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i0 w₀) := by
  obtain ⟨α, β, hβ, hcoord⟩ := exists_coeff_of_mem_closure hpl hwx
  have hA := axis_data hp hp2 hn h hxh
  have hA₀ := axis_data hp hp2 hn h₀ hxh
  rcases hA with ⟨I, hi0, hcard, hw⟩ | ⟨I, d, hsign, lam, hi0, hcard, hw⟩
  · rcases hA₀ with ⟨I₀, hi0', hcard₀, hw₀⟩ | ⟨I₀, d₀, hsign₀, lam₀, hi0', hcard₀, hw₀⟩
    · exact axis_case_bd_bd hxh hcoord hi0 hi0' hw hw₀
    · obtain ⟨k, hkI, hkI₀, hkne⟩ :=
        exists_common_ne hi0' hcard (by omega) (Or.inr hcard₀) hn
      exact axis_case_bd_sigma hp hxh hβ hcoord hi0 hi0' hw hsign₀ hw₀
        ⟨k, hkI, hkI₀, hkne⟩
  · rcases hA₀ with ⟨I₀, hi0', hcard₀, hw₀⟩ | ⟨I₀, d₀, hsign₀, lam₀, hi0', hcard₀, hw₀⟩
    · obtain ⟨k, hkI, hkI₀, hkne⟩ :=
        exists_common_ne hi0' (by omega) hcard₀ (Or.inl hcard) hn
      exact axis_case_sigma_bd hp hxh hcoord hi0 hi0' hsign hw hw₀ ⟨k, hkI, hkI₀, hkne⟩
    · obtain ⟨k, hkI, hkI₀, hkne⟩ :=
        exists_common_ne hi0' (by omega) (by omega) (Or.inl hcard) hn
      exact axis_case_sigma_sigma hp hxh hβ hcoord hi0 hi0' hsign hsign₀ hw hw₀
        ⟨k, hkI, hkI₀, hkne⟩

theorem SignedNbrDatum.sgnAut_axis_eq_of_bBlockOn (hp : p.Prime) (hp2 : p ≠ 2)
    {xh w : Fin n → Multiplicative (ZMod p)} {I : Finset (Fin n)} {i0 : Fin n}
    (hxh : ∀ k, k ≠ i0 → xh k = 1) (h : SignedNbrDatum n p xh w (bBlockOn n p I)) :
    sgnAut i0 w = w := by
  have hw : ∀ k ∈ I, w k = 1 := (forall_bBlockOn_fix_iff hp hp2 I w).mp h.fix
  have hi0 : i0 ∈ I := by
    by_contra hi0
    apply h.not_fix
    exact (forall_bBlockOn_fix_iff hp hp2 I xh).mpr
      (fun k hk => hxh k (fun h' => hi0 (h' ▸ hk)))
  rw [sgnAut_apply]
  funext k
  by_cases hk : k = i0
  · subst hk
    rw [Function.update_self, hw k hi0, inv_one]
  · rw [Function.update_of_ne hk]

theorem SignedNbrDatum.mem_zpowers_or_of_const_axis (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {m : Fin n}
    (hxh : ∀ i j, xh i = xh j) (hw₀ : ∀ k, k ≠ m → w₀ k = 1) (h : SignedNbrDatum n p xh w Γ)
    (hpl : w ∈ Subgroup.closure ({xh, w₀} : Set (Fin n → Multiplicative (ZMod p))))
    (hwx : w ∉ Subgroup.zpowers xh) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut m xh) := by
  obtain ⟨α, β, hβ, hcoord⟩ := exists_coeff_of_mem_closure hpl hwx
  have hxh1 : xh ≠ 1 := by
    intro h1
    apply h.not_fix
    intro u _
    rw [h1]
    exact map_one u
  have hc : ∀ i, toAdd (xh i) ≠ 0 := by
    intro i hi
    apply hxh1
    refine eq_of_toAdd_eq fun k => ?_
    rw [hxh k i, hi, Pi.one_apply, toAdd_one]
  rcases block_profile hp hp2 (by omega) h with ⟨I, hcard, hfix⟩ | ⟨I, d, hd, hcard, hfix⟩
  · have hw : ∀ k ∈ I, w k = 1 := eq_one_of_bdFix ((hfix w).mp h.fix)
    exact const_axis_bd_case hp hn hw₀ hc hcoord hcard hw
  · have hnot : ¬ SigmaFix d I xh := fun hx => h.not_fix ((hfix xh).mpr hx)
    obtain ⟨k, hkI, _⟩ := exists_mem_ne_of_one_lt_card (m := m) (by omega : 1 < I.card)
    obtain ⟨lam, hw⟩ := exists_coord_of_sigmaFix hd ⟨k, hkI⟩ ((hfix w).mp h.fix)
    exact const_axis_sigma_case hp hn hxh hw₀ hc hcoord
      (fun i => sign_eq_one_or_neg_one hp (hd i)) hcard hw hnot

theorem SignedNbrDatum.mem_zpowers_or_of_const_pair (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {xh w₀ w : Fin n → Multiplicative (ZMod p)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {i j : Fin n}
    (hxh : ∀ a b, xh a = xh b) (hij : i ≠ j) (hw₀ij : w₀ i = w₀ j)
    (hw₀ : ∀ k, k ≠ i → k ≠ j → w₀ k = 1) (h : SignedNbrDatum n p xh w Γ)
    (hpl : w ∈ Subgroup.closure ({xh, w₀} : Set (Fin n → Multiplicative (ZMod p))))
    (hwx : w ∉ Subgroup.zpowers xh) :
    w ∈ Subgroup.zpowers w₀ ∨ w ∈ Subgroup.zpowers (sgnAut i (sgnAut j xh)) := by
  obtain ⟨α, β, hβ, hcoord⟩ := exists_coeff_of_mem_closure hpl hwx
  have hxh1 : xh ≠ 1 := by
    intro h1
    apply h.not_fix
    intro u _
    rw [h1]
    exact map_one u
  have hc : ∀ k, toAdd (xh k) ≠ 0 := by
    intro k hk
    apply hxh1
    refine eq_of_toAdd_eq fun l => ?_
    rw [hxh l k, hk, Pi.one_apply, toAdd_one]
  rcases block_profile hp hp2 (by omega) h with ⟨I, hcard, hfix⟩ | ⟨I, d, hd, hcard, hfix⟩
  · have hw : ∀ k ∈ I, w k = 1 := eq_one_of_bdFix ((hfix w).mp h.fix)
    exact const_pair_bd_case hp hn hij hw₀ hc hcoord hcard hw
  · have hnot : ¬ SigmaFix d I xh := fun hx => h.not_fix ((hfix xh).mpr hx)
    obtain ⟨k, hkI, _, _⟩ := exists_mem_ne_ne_of_two_lt_card hij (by omega : 2 < I.card)
    obtain ⟨lam, hw⟩ := exists_coord_of_sigmaFix hd ⟨k, hkI⟩ ((hfix w).mp h.fix)
    exact const_pair_sigma_case hp hn hxh hij hw₀ij hw₀ hc hcoord
      (fun a => sign_eq_one_or_neg_one hp (hd a)) hcard hw hnot

theorem profile_of_forall_mem_zpowers (hp : p.Prime) {I₀ : Finset (Fin n)} {i j : Fin n}
    {w₀ : Fin n → Multiplicative (ZMod p)} (hw₀ : ∀ k ∈ I₀, w₀ k = 1)
    (hline : ∀ f : Fin n → Multiplicative (ZMod p), (∀ k ∈ I₀, f k = 1) → f i = f j →
      f ∈ Subgroup.zpowers w₀) :
    (∃ m, m ≠ i ∧ m ≠ j ∧ ∀ k, k ≠ m → w₀ k = 1) ∨ ∀ k, k ≠ i → k ≠ j → w₀ k = 1 := by
  by_cases hex : ∃ m, m ∉ I₀ ∧ m ≠ i ∧ m ≠ j
  · obtain ⟨m, hmI, hmi, hmj⟩ := hex
    left
    refine ⟨m, hmi, hmj, ?_⟩
    set e : Fin n → Multiplicative (ZMod p) := Pi.mulSingle m (ofAdd 1) with he
    have heI : ∀ k ∈ I₀, e k = 1 := by
      intro k hk
      rw [he, Pi.mulSingle_apply, if_neg]
      intro hkm
      exact hmI (hkm ▸ hk)
    have hei : e i = e j := by
      rw [he, Pi.mulSingle_apply, Pi.mulSingle_apply, if_neg (Ne.symm hmi),
        if_neg (Ne.symm hmj)]
    have hmem : e ∈ Subgroup.zpowers w₀ := hline e heI hei
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hkm : (k : ZMod p) ≠ 0 := by
      intro hk0
      have h1 : (k : ZMod p) * toAdd (w₀ m) = 1 := by
        have := congrArg (fun f => toAdd (f m)) hk
        rw [Pi.pow_apply, toAdd_zpow, zsmul_eq_mul, he, Pi.mulSingle_apply, if_pos rfl] at this
        simpa using this
      rw [hk0, zero_mul] at h1
      exact (coord_zero_ne_one hp) h1
    intro l hl
    have h0 : (k : ZMod p) * toAdd (w₀ l) = 0 := by
      have := congrArg (fun f => toAdd (f l)) hk
      rw [Pi.pow_apply, toAdd_zpow, zsmul_eq_mul, he, Pi.mulSingle_apply, if_neg hl] at this
      exact this
    exact toAdd.injective (by simpa using (coord_mul_eq_zero hp h0).resolve_left hkm)
  · right
    intro k hki hkj
    apply hw₀ k
    by_contra hkI
    exact hex ⟨k, hkI, hki, hkj⟩

end CFSG.StandardType

end
