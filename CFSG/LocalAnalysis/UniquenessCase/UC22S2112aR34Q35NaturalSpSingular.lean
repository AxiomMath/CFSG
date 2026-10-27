module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open scoped commutatorElement

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma z_mul_self {Z : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) : z * z = 1 := by
  by_cases hz : z = 1
  · rw [hz, one_mul]
  · have hzZ : z ∈ Z := (hZ z).mpr (Or.inr rfl)
    have hzz : z * z ∈ Z := Z.mul_mem hzZ hzZ
    rcases (hZ (z * z)).mp hzz with h | h
    · exact h
    · exfalso
      apply hz
      have h' : z * z = z * 1 := by simpa using h
      exact mul_left_cancel h'

omit [Finite Γ] in
omit [Finite Γ] in
private lemma z_inv {z : Γ} (hz2 : z * z = 1) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right hz2

omit [Finite Γ] in
omit [Finite Γ] in
private lemma Z_central {Z : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    {u : Γ} (hu : u ∈ Z) : ∀ w : Γ, u * w = w * u := by
  rcases (hZ u).mp hu with rfl | rfl
  · intro w; simp
  · intro w; exact (hzc w).symm

omit [Finite Γ] in
omit [Finite Γ] in
private lemma card_Z {Z : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hz : z ≠ 1) : Nat.card Z = 2 := by
  have hset : (Z : Set Γ) = {1, z} := Set.ext fun w => by simpa using hZ w
  have h : Nat.card ↥(Z : Set Γ) = 2 := by
    rw [Nat.card_coe_set_eq, hset]
    exact Set.ncard_pair (Ne.symm hz)
  exact h

omit [Finite Γ] in
omit [Finite Γ] in
private lemma commutator_mem_Z {Z N : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    {x y : Γ} (hx : x ∈ N) (hy : y ∈ N) : x * y * x⁻¹ * y⁻¹ ∈ Z := by
  rcases hcomm x hx y hy with h | h
  · have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [h]; group
    rw [h1]
    exact (hZ 1).mpr (Or.inl rfl)
  · have h1 : x * y * x⁻¹ * y⁻¹ = z := by rw [h]; group
    rw [h1]
    exact (hZ z).mpr (Or.inr rfl)

private lemma exists_involution {Z N : Subgroup Γ} [N.Normal] {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hz : z ≠ 1) (hzc : ∀ g : Γ, g * z = z * g)
    (hcard : Nat.card N = 32) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hcen : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x ∈ Z) :
    ∃ s : Γ, s ∈ N ∧ s ∉ Z ∧ s * s = 1 := by
  classical
  have hz2 : z * z = 1 := z_mul_self hZ
  have hZcard : Nat.card Z = 2 := card_Z hZ hz
  obtain ⟨x, hxN, hxZ⟩ : ∃ x : Γ, x ∈ N ∧ x ∉ Z := by
    by_contra h
    push Not at h
    have hc := Subgroup.card_le_of_le (show N ≤ Z from h)
    rw [hcard, hZcard] at hc
    exact absurd hc (by decide)
  let f : ↥N →* Γ :=
    { toFun := fun y => x * (y : Γ) * x⁻¹ * (y : Γ)⁻¹
      map_one' := by simp
      map_mul' := by
        intro y y'
        have hy : (y : Γ) ∈ N := y.2
        have hy' : (y' : Γ) ∈ N := y'.2
        have hc' : x * (y' : Γ) * x⁻¹ * (y' : Γ)⁻¹ ∈ Z := commutator_mem_Z hZ hcomm hxN hy'
        have hcc' : ∀ w : Γ,
            (x * (y' : Γ) * x⁻¹ * (y' : Γ)⁻¹) * w = w * (x * (y' : Γ) * x⁻¹ * (y' : Γ)⁻¹) :=
          Z_central hZ hzc hc'
        show x * ((y : Γ) * (y' : Γ)) * x⁻¹ * ((y : Γ) * (y' : Γ))⁻¹ =
          (x * (y : Γ) * x⁻¹ * (y : Γ)⁻¹) * (x * (y' : Γ) * x⁻¹ * (y' : Γ)⁻¹)
        rw [← commutatorElement_def (g₁ := x) (g₂ := (y : Γ) * (y' : Γ))]
        rw [← commutatorElement_def (g₁ := x) (g₂ := (y : Γ))]
        rw [← commutatorElement_def (g₁ := x) (g₂ := (y' : Γ))]
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hconj : (y : Γ) * ⁅x, (y' : Γ)⁆ * (y : Γ)⁻¹ = ⁅x, (y' : Γ)⁆ := by
          rw [show (y : Γ) * ⁅x, (y' : Γ)⁆ = ⁅x, (y' : Γ)⁆ * (y : Γ) from
            (hcc' (y : Γ)).symm]
          group
        calc ⁅x, (y : Γ)⁆ * (y : Γ) * ⁅x, (y' : Γ)⁆ * (y : Γ)⁻¹
            = ⁅x, (y : Γ)⁆ * ((y : Γ) * ⁅x, (y' : Γ)⁆ * (y : Γ)⁻¹) := by group
          _ = ⁅x, (y : Γ)⁆ * ⁅x, (y' : Γ)⁆ := by rw [hconj] }
  have hrange : f.range = Z := by
    apply le_antisymm
    · rintro u ⟨y, rfl⟩
      exact commutator_mem_Z hZ hcomm hxN y.2
    · intro u hu
      rcases (hZ u).mp hu with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        have hne : ¬ (∀ y : ↥N, x * (y : Γ) = (y : Γ) * x) := by
          intro hall
          exact hxZ (hcen x hxN fun y hy => hall ⟨y, hy⟩)
        push Not at hne
        obtain ⟨y, hy⟩ := hne
        rcases hcomm x hxN (y : Γ) y.2 with h | h
        · exact absurd h hy
        · refine ⟨y, ?_⟩
          show x * (y : Γ) * x⁻¹ * (y : Γ)⁻¹ = z
          rw [h]
          group
  have hker : Nat.card ↥f.ker = 16 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hrange, hZcard, show Nat.card ↥N = 32 from hcard] at h
    nlinarith
  have hz1 : z ≠ 1 := hz
  have h1Z : (1 : Γ) ∈ Z := (hZ 1).mpr (Or.inl rfl)
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ h1Z)
  have hxz : x ≠ z := fun h => hxZ ((hZ x).mpr (Or.inr h))
  have hinv : (x * x)⁻¹ ∈ Z := Z.inv_mem (hsq x hxN)
  have hxz1 : x * z ≠ 1 := by
    intro h
    apply hxZ
    have hxeq : x = z⁻¹ := by
      have h' := congrArg (· * z⁻¹) h
      simpa [mul_assoc] using h'
    rw [hxeq, z_inv hz2]
    exact (hZ z).mpr (Or.inr rfl)
  have hxzz : x * z ≠ z := by
    intro h
    have h' : x = 1 := by
      have h'' := congrArg (· * z⁻¹) h
      simpa [mul_assoc] using h''
    exact hx1 h'
  have hxzx : x * z ≠ x := by
    intro h
    have h' : z = 1 := mul_left_cancel (a := x) (by simpa using h)
    exact hz1 h'
  have hVcard : ({1, z, x, x * z} : Finset Γ).card = 4 := by
    have h₁ : (1 : Γ) ∉ ({z, x, x * z} : Finset Γ) := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hz1 h.symm
      rcases Finset.mem_insert.mp h with h | h
      · exact hx1 h.symm
      exact hxz1 (Finset.mem_singleton.mp h).symm
    have h₂ : z ∉ ({x, x * z} : Finset Γ) := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hxz h.symm
      exact hxzz (Finset.mem_singleton.mp h).symm
    have h₃ : x ∉ ({x * z} : Finset Γ) := by
      intro hmem
      have h' : x = x * z := by simpa using hmem
      exact hxzx h'.symm
    rw [Finset.card_insert_of_notMem h₁, Finset.card_insert_of_notMem h₂,
      Finset.card_insert_of_notMem h₃, Finset.card_singleton]
  have : Fintype ↥f.ker := Fintype.ofFinite _
  let S : Finset Γ := Finset.univ.image (fun y : ↥f.ker => ((y : ↥N) : Γ))
  have hScard : S.card = 16 := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hker]
    · intro a b hab
      exact Subtype.ext (Subtype.ext hab)
  have hnotsub : ¬ S ⊆ ({1, z, x, x * z} : Finset Γ) := by
    intro hsub
    have hle : S.card ≤ 4 := by
      calc S.card ≤ _ := Finset.card_le_card hsub
        _ = 4 := hVcard
    rw [hScard] at hle
    exact absurd hle (by decide)
  rw [Finset.not_subset] at hnotsub
  obtain ⟨y, hyS, hyV⟩ := hnotsub
  obtain ⟨y0, -, rfl⟩ := Finset.mem_image.mp hyS
  have hyN : ((y0 : ↥N) : Γ) ∈ N := (y0 : ↥N).2
  have hfy : x * ((y0 : ↥N) : Γ) * x⁻¹ * ((y0 : ↥N) : Γ)⁻¹ = 1 :=
    MonoidHom.mem_ker.mp y0.2
  have hcommxy : x * ((y0 : ↥N) : Γ) = ((y0 : ↥N) : Γ) * x := by
    have h2 : x * ((y0 : ↥N) : Γ) * x⁻¹ = ((y0 : ↥N) : Γ) := by
      have h1 := congrArg (· * ((y0 : ↥N) : Γ)) hfy
      simpa [mul_assoc] using h1
    have h3 := congrArg (· * x) h2
    simpa [mul_assoc] using h3
  have hxx : x * x ∈ Z := hsq x hxN
  have hyy : ((y0 : ↥N) : Γ) * ((y0 : ↥N) : Γ) ∈ Z := hsq _ hyN
  have hyZ : ((y0 : ↥N) : Γ) ∈ Z ∨ ((y0 : ↥N) : Γ) ∉ Z := em _
  rcases (hZ (x * x)).mp hxx with hx1' | hxz'
  · exact ⟨x, hxN, hxZ, hx1'⟩
  rcases (hZ (((y0 : ↥N) : Γ) * ((y0 : ↥N) : Γ))).mp hyy with hy1 | hyz
  · have hyZ' : ((y0 : ↥N) : Γ) ≠ 1 := by
      intro h
      exact hyV (by rw [h]; simp)
    exact ⟨((y0 : ↥N) : Γ), hyN, fun h => by
      rcases (hZ _).mp h with h' | h'
      · exact hyZ' h'
      · exact hyV (by rw [h']; simp), hy1⟩
  · refine ⟨x * ((y0 : ↥N) : Γ), N.mul_mem hxN hyN, ?_, ?_⟩
    · intro hxyZ
      apply hyV
      have hzmem : (x * x)⁻¹ * (x * ((y0 : ↥N) : Γ)) ∈ Z := Z.mul_mem hinv hxyZ
      have hy_eq : ((y0 : ↥N) : Γ) = x * ((x * x)⁻¹ * (x * ((y0 : ↥N) : Γ))) := by group
      rw [hy_eq]
      rcases (hZ _).mp hzmem with h' | h'
      · rw [h']; simp
      · rw [h']; simp
    · have hsq2 : (x * ((y0 : ↥N) : Γ)) * (x * ((y0 : ↥N) : Γ)) = 1 := by
        calc (x * ((y0 : ↥N) : Γ)) * (x * ((y0 : ↥N) : Γ))
            = x * (((y0 : ↥N) : Γ) * x) * ((y0 : ↥N) : Γ) := by group
          _ = x * (x * ((y0 : ↥N) : Γ)) * ((y0 : ↥N) : Γ) := by rw [hcommxy]
          _ = (x * x) * (((y0 : ↥N) : Γ) * ((y0 : ↥N) : Γ)) := by group
          _ = z * z := by rw [hxz', hyz]
          _ = 1 := hz2
      exact hsq2

private def orbit (c s₀ : Γ) (k : ℕ) : Γ := c ^ k * s₀ * (c ^ k)⁻¹

omit [Finite Γ] in
omit [Finite Γ] in
private lemma conj_pow_mem {N : Subgroup Γ} [N.Normal] {c : Γ} (n : ℕ) (x : Γ) (hx : x ∈ N) :
    c ^ n * x * (c ^ n)⁻¹ ∈ N := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
      have h1 : c ^ (n + 1) = c ^ n * c := pow_succ c n
      rw [h1, mul_inv_rev]
      rw [show c ^ n * c * x * (c⁻¹ * (c ^ n)⁻¹) = c ^ n * (c * x * c⁻¹) * (c ^ n)⁻¹ by group]
      exact ih (c * x * c⁻¹) (Subgroup.Normal.conj_mem (inferInstance : N.Normal) x hx c)

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_mem {N : Subgroup Γ} [N.Normal] {c s₀ : Γ} (hs₀ : s₀ ∈ N) (k : ℕ) :
    orbit c s₀ k ∈ N :=
  conj_pow_mem k s₀ hs₀

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_sq {c s₀ : Γ} (hs₀ : s₀ * s₀ = 1) (k : ℕ) :
    orbit c s₀ k * orbit c s₀ k = 1 := by
  have h : orbit c s₀ k * orbit c s₀ k = c ^ k * (s₀ * s₀) * (c ^ k)⁻¹ := by
    rw [orbit]; group
  rw [h, hs₀, mul_one, mul_inv_cancel]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_period {c : Γ} (hc5 : c ^ 5 = 1) (s₀ : Γ) (k : ℕ) :
    orbit c s₀ (k + 5) = orbit c s₀ k := by
  have h1 : c ^ (k + 5) = c ^ k := by rw [pow_add, hc5, mul_one]
  rw [orbit]
  simp only [h1]
  rfl

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_add_five_mul {c : Γ} (hc5 : c ^ 5 = 1) (s₀ : Γ) (r : ℕ) :
    ∀ q : ℕ, orbit c s₀ (5 * q + r) = orbit c s₀ r := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      have h : 5 * (q + 1) + r = (5 * q + r) + 5 := by ring
      rw [h, orbit_period hc5, ih]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_eq_of_mod {c : Γ} (hc5 : c ^ 5 = 1) (s₀ : Γ) (k : ℕ) :
    orbit c s₀ (k % 5) = orbit c s₀ k := by
  conv_rhs => rw [← Nat.div_add_mod k 5]
  exact (orbit_add_five_mul hc5 s₀ (k % 5) (k / 5)).symm

omit [Finite Γ] in
omit [Finite Γ] in
private lemma Z_conj {Z : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    {w : Γ} (hw : w ∈ Z) (γ : Γ) : γ * w * γ⁻¹ ∈ Z := by
  rcases (hZ w).mp hw with h | h
  · rw [h]; simp
  · rw [h, hzc γ, mul_assoc, mul_inv_cancel, mul_one]
    exact (hZ z).mpr (Or.inr rfl)

omit [Finite Γ] in
omit [Finite Γ] in
private lemma z_pow_central {z : Γ} (hzc : ∀ g : Γ, g * z = z * g) (k : ℕ) (x : Γ) :
    z ^ k * x = x * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, ← hzc x, mul_assoc, ← pow_succ']

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_notMem_Z {Z : Subgroup Γ} {z : Γ} {c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    (hs₀Z : s₀ ∉ Z) (k : ℕ) : orbit c s₀ k ∉ Z := by
  intro h
  apply hs₀Z
  have h' : (c ^ k)⁻¹ * orbit c s₀ k * (c ^ k) ∈ Z := by
    have := Z_conj hZ hzc h ((c ^ k)⁻¹)
    simpa using this
  have heq : s₀ = (c ^ k)⁻¹ * orbit c s₀ k * (c ^ k) := by rw [orbit]; group
  rw [heq]; exact h'

omit [Finite Γ] in
omit [Finite Γ] in
private lemma class_fixing_pow {Z : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    {γ s : Γ} (h : γ * s * γ⁻¹ * s⁻¹ ∈ Z) (n : ℕ) :
    γ ^ n * s * (γ ^ n)⁻¹ * s⁻¹ ∈ Z := by
  induction n with
  | zero => simp
  | succ n ih =>
      set w : Γ := γ ^ n * s * (γ ^ n)⁻¹ * s⁻¹ with hwdef
      have hw : γ ^ n * s * (γ ^ n)⁻¹ = w * s := by rw [hwdef]; group
      have hmain : γ ^ (n + 1) * s * (γ ^ (n + 1))⁻¹ * s⁻¹
          = γ * (γ ^ n * s * (γ ^ n)⁻¹) * γ⁻¹ * s⁻¹ := by group
      rw [hmain, hw]
      have hsplit : γ * (w * s) * γ⁻¹ * s⁻¹
          = (γ * w * γ⁻¹) * (γ * s * γ⁻¹ * s⁻¹) := by group
      rw [hsplit]
      exact Z.mul_mem (Z_conj hZ hzc ih γ) h
omit [Finite Γ] in
private lemma exists_mul_mod_five (m : ℕ) (hm : m < 5) (hm0 : m ≠ 0) :
    ∃ m' : ℕ, (m * m') % 5 = 1 % 5 := by
  interval_cases m
  · exact absurd rfl hm0
  · exact ⟨1, by norm_num⟩
  · exact ⟨3, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨4, by norm_num⟩

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_mul_eq (c s : Γ) {k l : ℕ} (hkl : k ≤ l) :
    orbit c s k * orbit c s l
      = c ^ k * (s * c ^ (l - k) * s * (c ^ (l - k))⁻¹) * (c ^ k)⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, l = k + m := ⟨l - k, (Nat.add_sub_cancel' hkl).symm⟩
  have hm : k + m - k = m := by omega
  rw [hm]
  rw [orbit, orbit, pow_add, mul_inv_rev]
  group

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_class_aux {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z)
    {k l : ℕ} (hk : k < 5) (hl : l < 5) (hkl : k < l)
    (h : orbit c s₀ k * (orbit c s₀ l)⁻¹ ∈ Z) : False := by
  have hc5 : c ^ 5 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hm : l - k < 5 := by omega
  have hm0 : l - k ≠ 0 := by omega
  have hkl' : k ≤ l := le_of_lt hkl
  have hinv : (orbit c s₀ l)⁻¹ = orbit c s₀ l :=
    inv_eq_of_mul_eq_one_right (orbit_sq hs₀ l)
  rw [hinv, orbit_mul_eq c s₀ hkl'] at h
  have hu : s₀ * c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹ ∈ Z := by
    have h2 := Z_conj hZ hzc h ((c ^ k)⁻¹)
    simp only [inv_inv] at h2
    rwa [show (c ^ k)⁻¹ * (c ^ k * (s₀ * c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹) * (c ^ k)⁻¹)
        * c ^ k = s₀ * c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹ by group] at h2
  have h3 : c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹ * s₀⁻¹ ∈ Z := by
    have h4 := Z_conj hZ hzc hu s₀
    have heq : s₀ * (s₀ * c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹) * s₀⁻¹
        = c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹ * s₀⁻¹ := by
      rw [show s₀⁻¹ = s₀ from inv_eq_of_mul_eq_one_right hs₀]
      rw [show s₀ * (s₀ * c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹) * s₀
          = (s₀ * s₀) * (c ^ (l - k) * s₀ * (c ^ (l - k))⁻¹ * s₀) by group]
      rw [hs₀, one_mul]
    rw [heq] at h4
    simpa [hs₀] using h4
  obtain ⟨m', hm'⟩ := exists_mul_mod_five (l - k) hm hm0
  have hc_eq : (c ^ (l - k)) ^ m' = c := by
    rw [← pow_mul]
    have h1 : c ^ ((l - k) * m') = c ^ 1 := by
      rw [pow_eq_pow_iff_modEq, hc]
      exact hm'
    rw [h1, pow_one]
  have hfix := class_fixing_pow hZ hzc h3 m'
  rw [hc_eq] at hfix
  exact hs₀Z (hfree s₀ hs₀N hfix)

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_class_eq_of_mem {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z) {k l : ℕ}
    (h : orbit c s₀ k * (orbit c s₀ l)⁻¹ ∈ Z) : k % 5 = l % 5 := by
  have hc5 : c ^ 5 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  set k' := k % 5 with hk'
  set l' := l % 5 with hl'
  have hklt : k' < 5 := by rw [hk']; exact Nat.mod_lt k (by norm_num)
  have hllt : l' < 5 := by rw [hl']; exact Nat.mod_lt l (by norm_num)
  have hkE : orbit c s₀ k' = orbit c s₀ k := by
    rw [hk']; exact orbit_eq_of_mod hc5 s₀ k
  have hlE : orbit c s₀ l' = orbit c s₀ l := by
    rw [hl']; exact orbit_eq_of_mod hc5 s₀ l
  have h' : orbit c s₀ k' * (orbit c s₀ l')⁻¹ ∈ Z := by
    rw [hkE, hlE]; exact h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact orbit_class_aux hZ hzc hc hfree hs₀ hs₀N hs₀Z hklt hllt hlt h'
  · have hswap : orbit c s₀ l' * (orbit c s₀ k')⁻¹ ∈ Z := by
      have hinv := Z.inv_mem h'
      rwa [show (orbit c s₀ k' * (orbit c s₀ l')⁻¹)⁻¹
          = orbit c s₀ l' * (orbit c s₀ k')⁻¹ by rw [mul_inv_rev, inv_inv]] at hinv
    exact orbit_class_aux hZ hzc hc hfree hs₀ hs₀N hs₀Z hllt hklt hgt hswap

omit [Finite Γ] in
omit [Finite Γ] in
private lemma orbit_anticommute {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hts : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x * y = y * x →
      x ∈ Z ∨ y ∈ Z ∨ x * y ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z) {k l : ℕ}
    (hkl : k % 5 ≠ l % 5) :
    orbit c s₀ k * orbit c s₀ l = z * (orbit c s₀ l * orbit c s₀ k) := by
  have hkN : orbit c s₀ k ∈ N := orbit_mem hs₀N k
  have hlN : orbit c s₀ l ∈ N := orbit_mem hs₀N l
  have hksq : orbit c s₀ k * orbit c s₀ k = 1 := orbit_sq hs₀ k
  have hlsq : orbit c s₀ l * orbit c s₀ l = 1 := orbit_sq hs₀ l
  rcases hcomm _ hkN _ hlN with h | h
  · exfalso
    rcases hts _ hkN _ hlN hksq hlsq h with h' | h' | h'
    · exact orbit_notMem_Z hZ hzc hs₀Z k h'
    · exact orbit_notMem_Z hZ hzc hs₀Z l h'
    · have h'' : orbit c s₀ k * (orbit c s₀ l)⁻¹ ∈ Z := by
        rwa [show (orbit c s₀ l)⁻¹ = orbit c s₀ l from inv_eq_of_mul_eq_one_right hlsq]
      exact hkl (orbit_class_eq_of_mem hZ hzc hc hfree hs₀ hs₀N hs₀Z h'')
  · exact h

omit [Finite Γ] in
omit [Finite Γ] in
private lemma conj_mul (γ x y : Γ) :
    γ * (x * y) * γ⁻¹ = (γ * x * γ⁻¹) * (γ * y * γ⁻¹) := by group

omit [Finite Γ] in
omit [Finite Γ] in
private lemma z_pow_mul_eq {z : Γ} (hzc : ∀ g : Γ, g * z = z * g) (k l : ℕ) (a b : Γ) :
    (z ^ k * a) * (z ^ l * b) = z ^ (k + l) * (a * b) := by
  have h1 : (z ^ k * a) * (z ^ l * b) = z ^ k * (a * z ^ l) * b := by group
  rw [h1, ← z_pow_central hzc l a, ← mul_assoc, ← pow_add]
  group

omit [Finite Γ] in
omit [Finite Γ] in
private lemma conj_pow_self (s : Γ) (n : ℕ) : s * s ^ n * s⁻¹ = s ^ n := by
  rw [← pow_succ', pow_succ, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma zpow_mul_move {z : Γ} (hzc : ∀ g : Γ, g * z = z * g) (n : ℕ) (s : Γ) :
    (z ^ n * s ^ n) * (z * s) = z ^ (n + 1) * (s ^ n * s) := by
  rw [show (z ^ n * s ^ n) * (z * s) = z ^ n * (s ^ n * z) * s by group]
  rw [show s ^ n * z = z * s ^ n from hzc (s ^ n)]
  rw [show z ^ n * (z * s ^ n) * s = (z ^ n * z) * (s ^ n * s) by group]
  rw [← pow_succ]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma conj_pow_anti {z c s : Γ} (hanti : c * s = z * (s * c))
    (hzc : ∀ g : Γ, g * z = z * g) (n : ℕ) : c * s ^ n * c⁻¹ = z ^ n * s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs1 : c * s * c⁻¹ = z * s := by rw [hanti]; group
      rw [pow_succ s]
      calc c * (s ^ n * s) * c⁻¹
          = (c * s ^ n * c⁻¹) * (c * s * c⁻¹) := by rw [conj_mul]
        _ = (z ^ n * s ^ n) * (z * s) := by rw [ih, hs1]
        _ = z ^ (n + 1) * (s ^ n * s) := zpow_mul_move hzc n s

omit [Finite Γ] in
omit [Finite Γ] in
private lemma z_prod4_collect {z : Γ} (hzc : ∀ g : Γ, g * z = z * g)
    (a0 a1 a2 a3 : Γ) (k0 k1 k2 k3 : ℕ) :
    (z ^ k0 * a0) * (z ^ k1 * a1) * (z ^ k2 * a2) * (z ^ k3 * a3)
      = z ^ (k0 + k1 + k2 + k3) * (a0 * a1 * a2 * a3) := by
  rw [show (z ^ k0 * a0) * (z ^ k1 * a1) * (z ^ k2 * a2) * (z ^ k3 * a3)
      = ((z ^ k0 * a0) * (z ^ k1 * a1)) * ((z ^ k2 * a2) * (z ^ k3 * a3)) by group]
  rw [z_pow_mul_eq hzc, z_pow_mul_eq hzc, z_pow_mul_eq hzc]
  have he : (k0 + k1) + (k2 + k3) = k0 + k1 + k2 + k3 := by ring
  rw [he]
  group

private def prod4 (c s₀ : Γ) (e : Fin 4 → Fin 2) : Γ :=
  orbit c s₀ ((0 : Fin 4) : ℕ) ^ (e 0 : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ) ^ (e 1 : ℕ)
    * orbit c s₀ ((2 : Fin 4) : ℕ) ^ (e 2 : ℕ) * orbit c s₀ ((3 : Fin 4) : ℕ) ^ (e 3 : ℕ)

private def sgn (j : Fin 4) (e : Fin 4 → Fin 2) : ℕ :=
  (if (0 : Fin 4) = j then 0 else (e 0 : ℕ)) + (if (1 : Fin 4) = j then 0 else (e 1 : ℕ)) +
  (if (2 : Fin 4) = j then 0 else (e 2 : ℕ)) + (if (3 : Fin 4) = j then 0 else (e 3 : ℕ))

omit [Finite Γ] in
omit [Finite Γ] in
private lemma prod4_conj {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hts : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x * y = y * x →
      x ∈ Z ∨ y ∈ Z ∨ x * y ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z)
    (j : Fin 4) (e : Fin 4 → Fin 2) :
    orbit c s₀ (j : ℕ) * prod4 c s₀ e * (orbit c s₀ (j : ℕ))⁻¹
      = z ^ sgn j e * prod4 c s₀ e := by
  have hz2 : z * z = 1 := z_mul_self hZ
  have hanti : ∀ i j : Fin 4, i ≠ j →
      orbit c s₀ (i : ℕ) * orbit c s₀ (j : ℕ)
        = z * (orbit c s₀ (j : ℕ) * orbit c s₀ (i : ℕ)) := by
    intro i j hij
    have hi : (i : ℕ) % 5 = (i : ℕ) :=
      Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num))
    have hj : (j : ℕ) % 5 = (j : ℕ) :=
      Nat.mod_eq_of_lt (lt_trans j.isLt (by norm_num))
    have hkl : (i : ℕ) % 5 ≠ (j : ℕ) % 5 := by
      rw [hi, hj]
      intro h
      exact hij (Fin.ext h)
    exact orbit_anticommute hZ hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z hkl
  have hfactor : ∀ i : Fin 4,
      orbit c s₀ (j : ℕ) * orbit c s₀ (i : ℕ) ^ (e i : ℕ) * (orbit c s₀ (j : ℕ))⁻¹
        = z ^ (if i = j then 0 else (e i : ℕ)) * orbit c s₀ (i : ℕ) ^ (e i : ℕ) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, pow_zero, one_mul]
      exact conj_pow_self (orbit c s₀ (i : ℕ)) (e i : ℕ)
    · rw [if_neg hij]
      have hA : orbit c s₀ (j : ℕ) * orbit c s₀ (i : ℕ)
          = z * (orbit c s₀ (i : ℕ) * orbit c s₀ (j : ℕ)) := by
        rw [hanti i j hij, ← mul_assoc, hz2, one_mul]
      exact conj_pow_anti hA hzc (e i : ℕ)
  rw [prod4]
  rw [show orbit c s₀ (j : ℕ)
        * (orbit c s₀ ((0 : Fin 4) : ℕ) ^ (e 0 : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ) ^ (e 1 : ℕ)
          * orbit c s₀ ((2 : Fin 4) : ℕ) ^ (e 2 : ℕ) * orbit c s₀ ((3 : Fin 4) : ℕ) ^ (e 3 : ℕ))
        * (orbit c s₀ (j : ℕ))⁻¹
      = (orbit c s₀ (j : ℕ) * orbit c s₀ ((0 : Fin 4) : ℕ) ^ (e 0 : ℕ) * (orbit c s₀ (j : ℕ))⁻¹)
        * (orbit c s₀ (j : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ) ^ (e 1 : ℕ) * (orbit c s₀ (j : ℕ))⁻¹)
        * (orbit c s₀ (j : ℕ) * orbit c s₀ ((2 : Fin 4) : ℕ) ^ (e 2 : ℕ) * (orbit c s₀ (j : ℕ))⁻¹)
        * (orbit c s₀ (j : ℕ) * orbit c s₀ ((3 : Fin 4) : ℕ) ^ (e 3 : ℕ) * (orbit c s₀ (j : ℕ))⁻¹) by
    simp only [conj_mul]]
  rw [hfactor 0, hfactor 1, hfactor 2, hfactor 3]
  rw [z_prod4_collect hzc]
  rfl

omit [Finite Γ] in
omit [Finite Γ] in
private lemma conj_zpow_mul {z : Γ} (hzc : ∀ g : Γ, g * z = z * g) (γ x : Γ) (n : ℕ) :
    γ * (z ^ n * x) * γ⁻¹ = z ^ n * (γ * x * γ⁻¹) := by
  rw [show γ * (z ^ n * x) * γ⁻¹ = (γ * z ^ n * γ⁻¹) * (γ * x * γ⁻¹) by group]
  rw [show γ * z ^ n * γ⁻¹ = z ^ n from by
    rw [show γ * z ^ n = z ^ n * γ from (z_pow_central hzc n γ).symm, mul_assoc,
      mul_inv_cancel, mul_one]]

omit [Finite Γ] in
private lemma sgn_inj : ∀ e e' : Fin 4 → Fin 2,
    (∀ j : Fin 4, sgn j e % 2 = sgn j e' % 2) → e = e' := by
  decide

omit [Finite Γ] in
private lemma prod4_inj {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hz : z ≠ 1)
    (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hts : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x * y = y * x →
      x ∈ Z ∨ y ∈ Z ∨ x * y ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z)
    {e e' : Fin 4 → Fin 2} {ε δ : Fin 2}
    (h : z ^ (ε : ℕ) * prod4 c s₀ e = z ^ (δ : ℕ) * prod4 c s₀ e') :
    e = e' ∧ ε = δ := by
  have hz2 : z * z = 1 := z_mul_self hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz
  have hconj : ∀ j : Fin 4, z ^ (sgn j e) = z ^ (sgn j e') := by
    intro j
    have h2 : z ^ (sgn j e) * (z ^ (ε : ℕ) * prod4 c s₀ e)
        = z ^ (sgn j e') * (z ^ (δ : ℕ) * prod4 c s₀ e') := by
      calc z ^ (sgn j e) * (z ^ (ε : ℕ) * prod4 c s₀ e)
          = z ^ (ε : ℕ) * (z ^ (sgn j e) * prod4 c s₀ e) := by
              rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.add_comm, pow_add, mul_assoc]
        _ = z ^ (ε : ℕ) * (orbit c s₀ (j : ℕ) * prod4 c s₀ e * (orbit c s₀ (j : ℕ))⁻¹) := by
              rw [prod4_conj hZ hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z]
        _ = orbit c s₀ (j : ℕ) * (z ^ (ε : ℕ) * prod4 c s₀ e) * (orbit c s₀ (j : ℕ))⁻¹ := by
              rw [conj_zpow_mul hzc]
        _ = orbit c s₀ (j : ℕ) * (z ^ (δ : ℕ) * prod4 c s₀ e') * (orbit c s₀ (j : ℕ))⁻¹ := by
              rw [h]
        _ = z ^ (δ : ℕ) * (orbit c s₀ (j : ℕ) * prod4 c s₀ e' * (orbit c s₀ (j : ℕ))⁻¹) := by
              rw [conj_zpow_mul hzc]
        _ = z ^ (δ : ℕ) * (z ^ (sgn j e') * prod4 c s₀ e') := by
              rw [prod4_conj hZ hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z]
        _ = z ^ (sgn j e') * (z ^ (δ : ℕ) * prod4 c s₀ e') := by
              rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.add_comm, pow_add, mul_assoc]
    rw [h] at h2
    exact mul_right_cancel h2
  have he : e = e' := by
    apply sgn_inj
    intro j
    have h3 := (pow_eq_pow_iff_modEq (x := z)).mp (hconj j)
    rwa [hzord] at h3
  have hε : ε = δ := by
    have hp : z ^ (ε : ℕ) = z ^ (δ : ℕ) := by
      rw [he] at h
      exact mul_right_cancel h
    have h3 := (pow_eq_pow_iff_modEq (x := z)).mp hp
    rw [hzord] at h3
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h3 ε.isLt δ.isLt)
  exact ⟨he, hε⟩

private lemma span_four {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hz : z ≠ 1)
    (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hts : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x * y = y * x →
      x ∈ Z ∨ y ∈ Z ∨ x * y ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z) (hcard : Nat.card N = 32) :
    N ≤ Subgroup.closure (Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ))) := by
  classical
  set K := Subgroup.closure (Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ))) with hK
  have hgen : ∀ i : Fin 4, orbit c s₀ (i : ℕ) ∈ K := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  have hKN : K ≤ N := by
    rw [hK]
    exact (Subgroup.closure_le N).mpr (by rintro x ⟨i, rfl⟩; exact orbit_mem hs₀N (i : ℕ))
  have hanti01 : orbit c s₀ ((0 : Fin 4) : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ)
      = z * (orbit c s₀ ((1 : Fin 4) : ℕ) * orbit c s₀ ((0 : Fin 4) : ℕ)) := by
    exact orbit_anticommute hZ hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z (by decide)
  have hzK : z ∈ K := by
    have hT0 : orbit c s₀ ((0 : Fin 4) : ℕ) ∈ K := hgen 0
    have hT1 : orbit c s₀ ((1 : Fin 4) : ℕ) ∈ K := hgen 1
    have hsq0 : orbit c s₀ ((0 : Fin 4) : ℕ) * orbit c s₀ ((0 : Fin 4) : ℕ) = 1 :=
      orbit_sq hs₀ 0
    have hsq1 : orbit c s₀ ((1 : Fin 4) : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ) = 1 :=
      orbit_sq hs₀ 1
    have heq : (orbit c s₀ ((0 : Fin 4) : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ))
        * (orbit c s₀ ((0 : Fin 4) : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ)) = z := by
      nth_rewrite 1 [hanti01]
      rw [show z * (orbit c s₀ ((1 : Fin 4) : ℕ) * orbit c s₀ ((0 : Fin 4) : ℕ))
            * (orbit c s₀ ((0 : Fin 4) : ℕ) * orbit c s₀ ((1 : Fin 4) : ℕ))
          = z * (orbit c s₀ ((1 : Fin 4) : ℕ)
            * (orbit c s₀ ((0 : Fin 4) : ℕ) * orbit c s₀ ((0 : Fin 4) : ℕ))
            * orbit c s₀ ((1 : Fin 4) : ℕ)) by group]
      rw [hsq0, mul_one, hsq1, mul_one]
    rw [← heq]
    exact K.mul_mem (K.mul_mem hT0 hT1) (K.mul_mem hT0 hT1)
  have hprodK : ∀ e : Fin 4 → Fin 2, prod4 c s₀ e ∈ K := by
    intro e
    rw [prod4]
    exact K.mul_mem (K.mul_mem (K.mul_mem
      (K.pow_mem (hgen 0) _) (K.pow_mem (hgen 1) _)) (K.pow_mem (hgen 2) _))
      (K.pow_mem (hgen 3) _)
  let F : Fin 2 × (Fin 4 → Fin 2) → ↥K := fun p =>
    ⟨z ^ (p.1 : ℕ) * prod4 c s₀ p.2, K.mul_mem (K.pow_mem hzK _) (hprodK p.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨ε, e⟩ ⟨δ, e'⟩ hEq
    have hEq' : z ^ (ε : ℕ) * prod4 c s₀ e = z ^ (δ : ℕ) * prod4 c s₀ e' :=
      congrArg (fun x : ↥K => (x : Γ)) hEq
    obtain ⟨hee, hεδ⟩ := prod4_inj hZ hz hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z hEq'
    exact Prod.ext hεδ hee
  have hcardDom : Nat.card (Fin 2 × (Fin 4 → Fin 2)) = 32 := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_fun, Nat.card_fin]
    norm_num
  have hle : 32 ≤ Nat.card ↥K := by
    rw [← hcardDom]
    exact Nat.card_le_card_of_injective F hF
  have hKeq : K = N :=
    Subgroup.eq_of_le_of_card_ge hKN (by rw [hcard]; exact hle)
  rw [← hKeq]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma commute_of_commute_four {N : Subgroup Γ} {c s₀ : Γ}
    (hspan : N ≤ Subgroup.closure (Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ))))
    {n : Γ} (hcomm4 : ∀ i : Fin 4, n * orbit c s₀ (i : ℕ) = orbit c s₀ (i : ℕ) * n) :
    ∀ y ∈ N, n * y = y * n := by
  intro y hy
  have hle : Subgroup.closure (Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ)))
      ≤ Subgroup.centralizer ({n} : Set Γ) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact (Subgroup.mem_centralizer_iff).mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm4 i)
  have hmem := hle (hspan hy)
  rw [Subgroup.mem_centralizer_iff] at hmem
  exact hmem n (Set.mem_singleton n)

omit [Finite Γ] in
omit [Finite Γ] in
private lemma involution_class {Z N : Subgroup Γ} [N.Normal] {z c s₀ : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z)
    (hzc : ∀ g : Γ, g * z = z * g)
    (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hcen : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x ∈ Z)
    (hts : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x * y = y * x →
      x ∈ Z ∨ y ∈ Z ∨ x * y ∈ Z)
    (hs₀ : s₀ * s₀ = 1) (hs₀N : s₀ ∈ N) (hs₀Z : s₀ ∉ Z)
    (hspan : N ≤ Subgroup.closure (Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ))))
    {u : Γ} (huN : u ∈ N) (huZ : u ∉ Z) (hu2 : u * u = 1) :
    ∃ k : ℕ, k < 5 ∧ u * (orbit c s₀ k)⁻¹ ∈ Z := by
  have hz2 : z * z = 1 := z_mul_self hZ
  have hkZ : ∀ k : ℕ, orbit c s₀ k ∉ Z := fun k => orbit_notMem_Z hZ hzc hs₀Z k
  have hkN : ∀ k : ℕ, orbit c s₀ k ∈ N := fun k => orbit_mem hs₀N k
  have hksq : ∀ k : ℕ, orbit c s₀ k * orbit c s₀ k = 1 := fun k => orbit_sq hs₀ k
  by_cases h : ∃ k : Fin 4, u * (orbit c s₀ (k : ℕ))⁻¹ ∈ Z
  · obtain ⟨k, hk⟩ := h
    exact ⟨(k : ℕ), lt_trans k.isLt (by norm_num), hk⟩
  push Not at h
  have hanti : ∀ k : Fin 4,
      u * orbit c s₀ (k : ℕ) = z * (orbit c s₀ (k : ℕ) * u) := by
    intro k
    have hks : (orbit c s₀ (k : ℕ))⁻¹ = orbit c s₀ (k : ℕ) :=
      inv_eq_of_mul_eq_one_right (hksq (k : ℕ))
    rcases hcomm u huN _ (hkN (k : ℕ)) with h1 | h1
    · exfalso
      rcases hts u huN _ (hkN (k : ℕ)) hu2 (hksq (k : ℕ)) h1 with h2 | h2 | h2
      · exact huZ h2
      · exact hkZ (k : ℕ) h2
      · exact h k (by rwa [hks])
    · exact h1
  have hanti4 : ∀ k : Fin 4,
      orbit c s₀ 4 * orbit c s₀ (k : ℕ) = z * (orbit c s₀ (k : ℕ) * orbit c s₀ 4) := by
    intro k
    apply orbit_anticommute hZ hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z
    have hk5 : (k : ℕ) % 5 = (k : ℕ) := Nat.mod_eq_of_lt (lt_trans k.isLt (by norm_num))
    rw [show (4 : ℕ) % 5 = 4 by norm_num, hk5]
    intro h4
    omega
  have hcomm4 : ∀ k : Fin 4, (u * orbit c s₀ 4) * orbit c s₀ (k : ℕ)
      = orbit c s₀ (k : ℕ) * (u * orbit c s₀ 4) := by
    intro k
    calc (u * orbit c s₀ 4) * orbit c s₀ (k : ℕ)
        = u * (orbit c s₀ 4 * orbit c s₀ (k : ℕ)) := by group
      _ = u * (z * (orbit c s₀ (k : ℕ) * orbit c s₀ 4)) := by rw [hanti4 k]
      _ = z * (u * (orbit c s₀ (k : ℕ) * orbit c s₀ 4)) := by
            rw [show u * (z * (orbit c s₀ (k : ℕ) * orbit c s₀ 4))
                = z * (u * (orbit c s₀ (k : ℕ) * orbit c s₀ 4)) from by
              rw [← mul_assoc, hzc u, mul_assoc]]
      _ = z * ((u * orbit c s₀ (k : ℕ)) * orbit c s₀ 4) := by group
      _ = z * ((z * (orbit c s₀ (k : ℕ) * u)) * orbit c s₀ 4) := by rw [hanti k]
      _ = orbit c s₀ (k : ℕ) * (u * orbit c s₀ 4) := by
            rw [show z * ((z * (orbit c s₀ (k : ℕ) * u)) * orbit c s₀ 4)
                = (z * z) * (orbit c s₀ (k : ℕ) * (u * orbit c s₀ 4)) by group,
              hz2, one_mul]
  have hmulN : u * orbit c s₀ 4 ∈ N := N.mul_mem huN (hkN 4)
  have hmulZ : u * orbit c s₀ 4 ∈ Z := hcen _ hmulN (commute_of_commute_four hspan hcomm4)
  refine ⟨4, by norm_num, ?_⟩
  rwa [show (orbit c s₀ 4)⁻¹ = orbit c s₀ 4 from inv_eq_of_mul_eq_one_right (hksq 4)]

omit [Finite Γ] in
omit [Finite Γ] in
private lemma class_trans {Z : Subgroup Γ} {x y w : Γ} (h1 : x * y⁻¹ ∈ Z) (h2 : y * w⁻¹ ∈ Z) :
    x * w⁻¹ ∈ Z := by
  rw [show x * w⁻¹ = (x * y⁻¹) * (y * w⁻¹) by group]
  exact Z.mul_mem h1 h2

omit [Finite Γ] in
omit [Finite Γ] in
private lemma class_conj {Z : Subgroup Γ} {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    {x y : Γ} (h : x * y⁻¹ ∈ Z) (γ : Γ) :
    (γ * x * γ⁻¹) * (γ * y * γ⁻¹)⁻¹ ∈ Z := by
  rw [show (γ * x * γ⁻¹) * (γ * y * γ⁻¹)⁻¹ = γ * (x * y⁻¹) * γ⁻¹ by group]
  exact Z_conj hZ hzc h γ

omit [Finite Γ] in
omit [Finite Γ] in
private lemma class_conj_N {Z N : Subgroup Γ} [N.Normal] {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    {m x : Γ} (hm : m ∈ N) (hx : x ∈ N) : (m * x * m⁻¹) * x⁻¹ ∈ Z :=
  commutator_mem_Z hZ hcomm hm hx

omit [Finite Γ] in
omit [Finite Γ] in
private lemma g_action {Z N : Subgroup Γ} [N.Normal] {z c s₀ g : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hzc : ∀ g : Γ, g * z = z * g)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hs₀N : s₀ ∈ N)
    (hg : g * c * g⁻¹ * (c ^ 2)⁻¹ ∈ N)
    {b : ℕ} (hb : g * s₀ * g⁻¹ * (orbit c s₀ b)⁻¹ ∈ Z) :
    ∀ k : ℕ, g * orbit c s₀ k * g⁻¹ * (orbit c s₀ (2 * k + b))⁻¹ ∈ Z := by
  intro k
  induction k with
  | zero =>
      simpa [orbit] using hb
  | succ k ih =>
      set X : Γ := g * orbit c s₀ k * g⁻¹ with hXdef
      have hX : X ∈ N := by
        rw [hXdef]
        exact Subgroup.Normal.conj_mem (inferInstance : N.Normal) _ (orbit_mem hs₀N k) g
      have hc2X : c ^ 2 * X * (c ^ 2)⁻¹ ∈ N := by
        rw [hXdef]
        exact conj_pow_mem 2 X hX
      have hmN : g * c * g⁻¹ * (c ^ 2)⁻¹ ∈ N := hg
      have hm : g * c * g⁻¹ = (g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2 := by group
      have horbit_succ : orbit c s₀ (k + 1) = c * orbit c s₀ k * c⁻¹ := by
        rw [orbit, orbit, pow_succ c k, mul_inv_rev]
        group
      have h1 : ((g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2) * X
            * ((g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2)⁻¹
            * (c ^ 2 * X * (c ^ 2)⁻¹)⁻¹ ∈ Z := by
        rw [show ((g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2) * X
              * ((g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2)⁻¹
              = (g * c * g⁻¹ * (c ^ 2)⁻¹) * (c ^ 2 * X * (c ^ 2)⁻¹)
                * (g * c * g⁻¹ * (c ^ 2)⁻¹)⁻¹ by group]
        exact class_conj_N hZ hcomm hmN hc2X
      have h2 : (c ^ 2 * X * (c ^ 2)⁻¹) * (orbit c s₀ (2 * k + b + 2))⁻¹ ∈ Z := by
        have h := class_conj hZ hzc ih (c ^ 2)
        rwa [show c ^ 2 * orbit c s₀ (2 * k + b) * (c ^ 2)⁻¹
            = orbit c s₀ (2 * k + b + 2) by
          rw [orbit, orbit, show 2 * k + b + 2 = 2 + (2 * k + b) by ring,
            pow_add, pow_add, mul_inv_rev]
          group] at h
      have h3 := class_trans h1 h2
      rw [horbit_succ,
        show g * (c * orbit c s₀ k * c⁻¹) * g⁻¹
            = ((g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2) * X
              * ((g * c * g⁻¹ * (c ^ 2)⁻¹) * c ^ 2)⁻¹ by
          rw [hXdef, hm]; group,
        show 2 * (k + 1) + b = 2 * k + b + 2 by ring]
      exact h3

theorem exists_five_singular {Z N : Subgroup Γ} [N.Normal] {z : Γ}
    (hZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z) (hz : z ≠ 1) (hzc : ∀ g : Γ, g * z = z * g)
    (hZN : Z ≤ N) (hcard : Nat.card N = 32) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x ∨ x * y = z * (y * x))
    (hcen : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x ∈ Z)
    (hts : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x * y = y * x →
      x ∈ Z ∨ y ∈ Z ∨ x * y ∈ Z)
    {c g : Γ} (hc : orderOf c = 5) (hfree : ∀ x ∈ N, c * x * c⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hg : g * c * g⁻¹ * (c ^ 2)⁻¹ ∈ N) :
    ∃ s : ZMod 5 → Γ, (∀ i, s i ∈ N) ∧ (∀ i, s i * s i = 1) ∧
      (∀ i j, i ≠ j → s i * s j = z * (s j * s i)) ∧
      (∀ i, g * s i * g⁻¹ * (s (2 * i))⁻¹ ∈ Z) ∧ N ≤ Subgroup.closure (Set.range s) := by
  classical
  have _ : Z ≤ N := hZN
  obtain ⟨s₀, hs₀N, hs₀Z, hs₀⟩ := exists_involution hZ hz hzc hcard hsq hcomm hcen
  have hc5 : c ^ 5 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hspan : N ≤ Subgroup.closure (Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ))) :=
    span_four hZ hz hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z hcard
  have huN : g * s₀ * g⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem (inferInstance : N.Normal) s₀ hs₀N g
  have hu2 : (g * s₀ * g⁻¹) * (g * s₀ * g⁻¹) = 1 := by
    rw [show (g * s₀ * g⁻¹) * (g * s₀ * g⁻¹) = g * (s₀ * s₀) * g⁻¹ by group,
      hs₀, mul_one, mul_inv_cancel]
  have huZ : g * s₀ * g⁻¹ ∉ Z := by
    intro h
    apply hs₀Z
    have h' := Z_conj hZ hzc h g⁻¹
    rw [show g⁻¹ * (g * s₀ * g⁻¹) * g⁻¹⁻¹ = s₀ by group] at h'
    exact h'
  obtain ⟨b, hb5, hb⟩ :=
    involution_class hZ hzc hc hfree hcomm hcen hts hs₀ hs₀N hs₀Z hspan huN huZ hu2
  have hgact := g_action (z := z) hZ hzc hcomm hs₀N hg hb
  refine ⟨fun i : ZMod 5 => orbit c s₀ ((i - (b : ZMod 5)).val), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact orbit_mem hs₀N _
  · intro i
    exact orbit_sq hs₀ _
  · intro i j hij
    apply orbit_anticommute hZ hzc hc hfree hcomm hts hs₀ hs₀N hs₀Z
    intro hmod
    apply hij
    have h1 : (((i - (b : ZMod 5)).val : ℕ) : ZMod 5) = i - (b : ZMod 5) :=
      ZMod.natCast_zmod_val _
    have h2 : (((j - (b : ZMod 5)).val : ℕ) : ZMod 5) = j - (b : ZMod 5) :=
      ZMod.natCast_zmod_val _
    have hcast : (((i - (b : ZMod 5)).val : ℕ) : ZMod 5)
        = (((j - (b : ZMod 5)).val : ℕ) : ZMod 5) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hmod
    rw [h1, h2] at hcast
    have hbadd := congrArg (· + (b : ZMod 5)) hcast
    simpa [sub_add_cancel] using hbadd
  · intro i
    have h := hgact ((i - (b : ZMod 5)).val)
    have hcong : ((2 * ((i - (b : ZMod 5)).val) + b : ℕ) : ZMod 5)
        = ((((2 * i) - (b : ZMod 5)).val : ℕ) : ZMod 5) := by
      rw [ZMod.natCast_zmod_val]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    have hmod : (2 * ((i - (b : ZMod 5)).val) + b) % 5
        = (((2 * i) - (b : ZMod 5)).val) % 5 :=
      (ZMod.natCast_eq_natCast_iff _ _ 5).mp hcong
    have horbit : orbit c s₀ (2 * ((i - (b : ZMod 5)).val) + b)
        = orbit c s₀ (((2 * i) - (b : ZMod 5)).val) := by
      rw [← orbit_eq_of_mod hc5 s₀ (2 * ((i - (b : ZMod 5)).val) + b),
        ← orbit_eq_of_mod hc5 s₀ (((2 * i) - (b : ZMod 5)).val), hmod]
    rwa [horbit] at h
  · intro x hx
    have hsub : Set.range (fun i : Fin 4 => orbit c s₀ (i : ℕ))
        ⊆ (Subgroup.closure (Set.range fun i : ZMod 5 => orbit c s₀ ((i - (b : ZMod 5)).val)) : Set Γ) := by
      rintro y ⟨i, rfl⟩
      refine Subgroup.subset_closure ⟨((i : ℕ) : ZMod 5) + (b : ZMod 5), ?_⟩
      show orbit c s₀ ((((↑i : ZMod 5) + (b : ZMod 5)) - (b : ZMod 5)).val)
        = orbit c s₀ (i : ℕ)
      have h1 : (((i : ℕ) : ZMod 5) + (b : ZMod 5) - (b : ZMod 5)) = ((i : ℕ) : ZMod 5) := by ring
      rw [h1]
      have h2 : (((((i : ℕ) : ZMod 5)).val)) = (i : ℕ) := by
        rw [show (((i : ℕ) : ZMod 5)).val = (i : ℕ) % 5 from ZMod.val_natCast 5 (i : ℕ)]
        exact Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num))
      rw [h2]
    exact (Subgroup.closure_le _).mpr hsub (hspan hx)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
