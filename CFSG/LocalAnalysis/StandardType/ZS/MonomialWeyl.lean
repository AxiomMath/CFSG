module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD
import CFSG.LocalAnalysis.StandardType.GGResIWStar
import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvLinAlg

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private lemma mw_one_ne_neg_one (hp : p ≠ 2) : (1 : ZMod p) ≠ -1 := by
  intro h
  have h' : (-1 : ZMod p) = 1 := h.symm
  rcases (ZMod.neg_one_eq_one_iff (n := p)).mp h' with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h2

private lemma mw_neg_one_mul_neg_one : ((-1 : ZMod p) * (-1) : ZMod p) = 1 := by
  have h := neg_mul_neg (1 : ZMod p) (1 : ZMod p)
  rw [mul_one] at h
  exact h

private lemma mw_one_ne_zero : (1 : ZMod p) ≠ 0 := by
  have hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact one_ne_zero

private lemma mw_two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hd
  have h2 := (Fact.out : p.Prime).two_le
  omega

private def mw_sgn (i : Fin n) : Fin n → (ZMod p)ˣ := fun j => if j = i then -1 else 1

private lemma mw_sgn_val (i j : Fin n) :
    ((mw_sgn (p := p) i j : (ZMod p)ˣ) : ZMod p) = 1 ∨
      ((mw_sgn (p := p) i j : (ZMod p)ˣ) : ZMod p) = -1 := by
  by_cases h : j = i
  · right; rw [mw_sgn, if_pos h]; exact Units.val_neg 1
  · left; rw [mw_sgn, if_neg h]; exact Units.val_one

private lemma mw_sgn_apply_mul_self (i j : Fin n) :
    mw_sgn (p := p) i j * mw_sgn (p := p) i j = 1 := by
  by_cases h : j = i <;> simp [mw_sgn, h]

private lemma mw_mul_sign_zmod {x y : ZMod p} (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) : x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [hx, hy, one_mul]
  · right; rw [hx, hy]; simp only [one_mul]
  · right; rw [hx, hy]; simp only [mul_one]
  · left; rw [hx, hy]; exact mw_neg_one_mul_neg_one

private lemma mw_mul_sign {x y : (ZMod p)ˣ} (hx : (x : ZMod p) = 1 ∨ (x : ZMod p) = -1)
    (hy : (y : ZMod p) = 1 ∨ (y : ZMod p) = -1) :
    ((x * y : (ZMod p)ˣ) : ZMod p) = 1 ∨ ((x * y : (ZMod p)ˣ) : ZMod p) = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [Units.val_mul, hx, hy, one_mul]
  · right; rw [Units.val_mul, hx, hy]; simp only [one_mul]
  · right; rw [Units.val_mul, hx, hy]; simp only [mul_one]
  · left; rw [Units.val_mul, hx, hy]; exact mw_neg_one_mul_neg_one

private lemma mw_pairUnit_val (i j k : Fin n) :
    ((pairUnit p i j (-1) k : (ZMod p)ˣ) : ZMod p) = 1 ∨
      ((pairUnit p i j (-1) k : (ZMod p)ˣ) : ZMod p) = -1 := by
  by_cases h0 : k = i
  · right; rw [pairUnit, if_pos h0]; exact Units.val_neg 1
  · by_cases h1 : k = j
    · right; rw [pairUnit, if_neg h0, if_pos h1, inv_neg_one]; exact Units.val_neg 1
    · left; rw [pairUnit, if_neg h0, if_neg h1]; exact Units.val_one

omit [Fact p.Prime] in
private lemma mw_pairUnit_apply_left (a b : Fin n) : pairUnit p a b (-1) a = -1 := by
  simp [pairUnit]

omit [Fact p.Prime] in
private lemma mw_pairUnit_apply_right (a b : Fin n) : pairUnit p a b (-1) b = -1 := by
  by_cases hab : a = b
  · subst hab; simp [pairUnit]
  · simp [pairUnit]

omit [Fact p.Prime] in
private lemma mw_pairUnit_apply_of_ne (a b : Fin n) {i : Fin n} (hia : i ≠ a) (hib : i ≠ b) :
    pairUnit p a b (-1) i = 1 := by
  simp [pairUnit, hia, hib]

omit [Fact p.Prime] in
private lemma mw_pairUnit_apply_mul_self (a b i : Fin n) :
    pairUnit p a b (-1) i * pairUnit p a b (-1) i = 1 := by
  by_cases h0 : i = a
  · subst h0; simp [pairUnit]
  · by_cases h1 : i = b
    · subst h1; simp [pairUnit, h0]
    · simp [pairUnit, h0, h1]

private lemma mw_pairUnit_neg_one_eq (a b : Fin n) (hab : a ≠ b) :
    pairUnit p a b (-1) = mw_sgn (p := p) a * mw_sgn (p := p) b := by
  funext j
  by_cases hja : j = a
  · subst hja; rw [mw_pairUnit_apply_left]; simp [mw_sgn, hab]
  · by_cases hjb : j = b
    · subst hjb; rw [mw_pairUnit_apply_right]; simp [mw_sgn, hja]
    · rw [mw_pairUnit_apply_of_ne a b hja hjb]; simp [mw_sgn, hja, hjb]

private lemma mw_prod_sgn (i : Fin n) : ∏ j, (mw_sgn (p := p) i j : ZMod p) = -1 := by
  have h0 : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ i →
      ((mw_sgn (p := p) i b : (ZMod p)ˣ) : ZMod p) = 1 := by
    intro b _ hb; rw [mw_sgn, if_neg hb]; exact Units.val_one
  have h1 : i ∉ (Finset.univ : Finset (Fin n)) →
      ((mw_sgn (p := p) i i : (ZMod p)ˣ) : ZMod p) = 1 := by
    intro h; exact absurd (Finset.mem_univ i) h
  have h := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n))) i h0 h1
  rw [h, mw_sgn, if_pos rfl]
  exact Units.val_neg 1

private lemma mw_prod_pairUnit_neg_one (a b : Fin n) (hab : a ≠ b) :
    ∏ i, (pairUnit p a b (-1) i : ZMod p) = 1 := by
  rw [mw_pairUnit_neg_one_eq (p := p) a b hab]
  simp only [Pi.mul_apply, Units.val_mul]
  rw [Finset.prod_mul_distrib, mw_prod_sgn, mw_prod_sgn]
  exact mw_neg_one_mul_neg_one

private noncomputable def mwPermMapHom (b : Module.Basis (Fin n) (ZMod p) U) :
    Equiv.Perm (Fin n) →* (U ≃ₗ[ZMod p] U) :=
  MonoidHom.mk' (permMap p b) (fun σ τ => (permMap_mul b σ τ).symm)

private def mwSigned (b : Module.Basis (Fin n) (ZMod p) U) (g : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, g (b i) = c i • b (σ i)

private def mwEvenSigned (b : Module.Basis (Fin n) (ZMod p) U) (g : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, g (b i) = c i • b (σ i)

private lemma mw_diagMap_sgn_mem_g2mmn (_hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (a : Fin n) :
    diagMap p b (mw_sgn (p := p) a) ∈ g2mmn p b i₀ i₁ (-1) := by
  have hG : diagMap p b (mw_sgn (p := p) i₀) ∈ g2mmn p b i₀ i₁ (-1) :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hσ : permMap p b (Equiv.swap i₀ a) ∈ g2mmn p b i₀ i₁ (-1) :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  have hconj : permMap p b (Equiv.swap i₀ a) * diagMap p b (mw_sgn (p := p) i₀) *
      (permMap p b (Equiv.swap i₀ a))⁻¹ ∈ g2mmn p b i₀ i₁ (-1) :=
    mul_mem (mul_mem hσ hG) (inv_mem hσ)
  rw [permMap_mul_diagMap_mul_inv] at hconj
  have heq : mw_sgn (p := p) i₀ ∘ (Equiv.swap i₀ a).symm = mw_sgn (p := p) a := by
    funext j
    rw [Function.comp_apply, Equiv.symm_swap]
    simp only [mw_sgn]
    by_cases h : j = a
    · simp [h, Equiv.swap_apply_right]
    · have hne : Equiv.swap i₀ a j ≠ i₀ := by
        intro hc
        exact h (by simpa [Equiv.swap_apply_left] using (Equiv.swap_apply_eq_iff.mp hc))
      simp [h, hne]
  rwa [heq] at hconj

private lemma mw_eq_one_of_support_empty {e : Fin n → (ZMod p)ˣ}
    (hsupp : ∀ i, i ∈ (∅ : Finset (Fin n)) ↔ (e i : ZMod p) = -1)
    (he : ∀ i, (e i : ZMod p) = 1 ∨ (e i : ZMod p) = -1) : e = 1 := by
  funext i
  rcases he i with h | h
  · exact Units.ext h
  · exfalso
    have : i ∈ (∅ : Finset (Fin n)) := (hsupp i).mpr h
    simp at this

private lemma mw_support_erase (hp : p ≠ 2) {e : Fin n → (ZMod p)ˣ} {T : Finset (Fin n)}
    (a : Fin n) (ha : a ∈ T) (hsupp : ∀ i, i ∈ T ↔ (e i : ZMod p) = -1) :
    ∀ i, i ∈ T.erase a ↔ ((e * mw_sgn (p := p) a) i : ZMod p) = -1 := by
  intro i
  by_cases hia : i = a
  · rw [Finset.mem_erase]
    constructor
    · rintro ⟨h, -⟩; exact (h hia).elim
    · intro hcon
      have hTi : i ∈ T := by rw [hia]; exact ha
      have hea : (e i : ZMod p) = -1 := (hsupp i).mp hTi
      have h1 : ((e * mw_sgn (p := p) a) i : ZMod p) = 1 := by
        simp only [Pi.mul_apply]
        rw [show mw_sgn (p := p) a i = -1 by rw [mw_sgn, if_pos hia]]
        rw [Units.val_mul, hea, Units.val_neg, Units.val_one]
        exact mw_neg_one_mul_neg_one
      rw [h1] at hcon
      exact (mw_one_ne_neg_one hp hcon).elim
  · rw [Finset.mem_erase, hsupp i]
    have h1 : ((e * mw_sgn (p := p) a) i : ZMod p) = (e i : ZMod p) := by
      simp only [Pi.mul_apply, mw_sgn, if_neg hia, mul_one]
    rw [h1]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hia, h⟩

private lemma mw_diagMap_succ_g2mmn (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} {e : Fin n → (ZMod p)ˣ} (a : Fin n)
    (hIH : diagMap p b (e * mw_sgn (p := p) a) ∈ g2mmn p b i₀ i₁ (-1)) :
    diagMap p b e ∈ g2mmn p b i₀ i₁ (-1) := by
  let e' : Fin n → (ZMod p)ˣ := e * mw_sgn (p := p) a
  have he_eq : e = e' * mw_sgn (p := p) a := by
    funext i
    simp only [Pi.mul_apply, e']
    rw [mul_assoc, mw_sgn_apply_mul_self, mul_one]
  rw [he_eq, ← diagMap_mul]
  exact mul_mem hIH (mw_diagMap_sgn_mem_g2mmn hp b a)

private lemma mw_diagMap_g2mmn_key (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} :
    ∀ k (T : Finset (Fin n)) (e : Fin n → (ZMod p)ˣ),
      T.card = k → (∀ i, i ∈ T ↔ (e i : ZMod p) = -1) →
      (∀ i, (e i : ZMod p) = 1 ∨ (e i : ZMod p) = -1) →
      diagMap p b e ∈ g2mmn p b i₀ i₁ (-1) := by
  intro k
  induction k with
  | zero =>
    intro T e hcard hsupp he
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    subst hT
    rw [mw_eq_one_of_support_empty hsupp he, diagMap_one]
    exact Subgroup.one_mem _
  | succ k ih =>
    intro T e hcard hsupp he
    have hpos : 0 < T.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have hcard' : (T.erase a).card = k := by rw [Finset.card_erase_of_mem ha]; omega
    have hsupp' := mw_support_erase hp a ha hsupp
    have he' : ∀ i, ((e * mw_sgn (p := p) a) i : ZMod p) = 1 ∨
        ((e * mw_sgn (p := p) a) i : ZMod p) = -1 := by
      intro i
      have := mw_mul_sign (he i) (mw_sgn_val (p := p) a i)
      simpa only [Pi.mul_apply] using this
    exact mw_diagMap_succ_g2mmn hp b a
      (ih (T.erase a) (e * mw_sgn (p := p) a) hcard' hsupp' he')

private lemma mw_diagMap_mem_g2mmn_of_signs (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (d : Fin n → (ZMod p)ˣ)
    (hd : ∀ i, (d i : ZMod p) = 1 ∨ (d i : ZMod p) = -1) :
    diagMap p b d ∈ g2mmn p b i₀ i₁ (-1) :=
  mw_diagMap_g2mmn_key hp b (Finset.univ.filter (fun i => (d i : ZMod p) = -1)).card
    (Finset.univ.filter (fun i => (d i : ZMod p) = -1)) d rfl (fun i => by simp) hd

private lemma mw_signedB_mem_g2mmn (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} {g : U ≃ₗ[ZMod p] U} (h : mwSigned b g) :
    g ∈ g2mmn p b i₀ i₁ (-1) := by
  obtain ⟨σ, c, hc, hg⟩ := h
  let u : Fin n → (ZMod p)ˣ := fun i => Units.mk0 (c i) (by
    rcases hc i with h | h
    · rw [h]; exact mw_one_ne_zero
    · rw [h]; intro h0; exact mw_one_ne_zero (neg_eq_zero.mp h0))
  have hu : ∀ i, (u i : ZMod p) = c i := fun i => Units.val_mk0 _
  have heq : g = diagMap p b (u ∘ σ.symm) * permMap p b σ :=
    eq_diagMap_mul_permMap b σ u (fun i => by rw [hu i]; exact hg i)
  rw [heq]
  refine mul_mem (mw_diagMap_mem_g2mmn_of_signs hp b (u ∘ σ.symm) ?_) ?_
  · intro i
    rw [Function.comp_apply, hu]
    exact hc (σ.symm i)
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))

private lemma mw_mem_g2mmn_iff_signed (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (g : U ≃ₗ[ZMod p] U) :
    g ∈ g2mmn p b i₀ i₁ (-1) ↔ mwSigned b g := by
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun g _ => mwSigned b g) ?_ ?_ ?_ ?_ hg
    · rintro x (hx | hx)
      · obtain ⟨σ, rfl⟩ := hx
        exact ⟨σ, fun _ => 1, fun _ => Or.inl rfl, fun i => by
          rw [permMap_apply_basis, one_smul]⟩
      · rw [Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact ⟨1, fun i => (mw_sgn (p := p) i₀ i : ZMod p), fun i => mw_sgn_val i₀ i,
            fun i => by rw [diagMap_apply_basis]; rfl⟩
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨1, fun i => (pairUnit p i₀ i₁ (-1) i : ZMod p),
            fun i => mw_pairUnit_val i₀ i₁ i, fun i => by rw [diagMap_apply_basis]; rfl⟩
    · exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun i => by simp⟩
    · rintro x y _ _ ⟨σ, c, hc, hx⟩ ⟨τ, c', hc', hy⟩
      refine ⟨σ * τ, fun i => c' i * c (τ i), fun i => mw_mul_sign_zmod (hc' i) (hc (τ i)),
        fun i => ?_⟩
      rw [LinearEquiv.mul_apply, hy i, map_smul, hx (τ i), ← mul_smul, Equiv.Perm.mul_apply]
    · rintro x _ ⟨σ, c, hc, hx⟩
      refine ⟨σ.symm, fun i => c (σ.symm i), fun i => hc (σ.symm i), fun i => ?_⟩
      have h1 : x (b (σ.symm i)) = c (σ.symm i) • b i := by
        rw [hx (σ.symm i), Equiv.apply_symm_apply]
      have hcc : c (σ.symm i) * c (σ.symm i) = 1 := by
        rcases hc (σ.symm i) with h | h
        · rw [h, one_mul]
        · rw [h]; exact mw_neg_one_mul_neg_one
      have h2 : c (σ.symm i) • x (b (σ.symm i)) = b i := by
        rw [h1, smul_smul, hcc, one_smul]
      rw [← h2]
      change x.symm (c (σ.symm i) • x (b (σ.symm i))) = c (σ.symm i) • b (σ.symm i)
      rw [map_smul, LinearEquiv.symm_apply_apply]
  · exact mw_signedB_mem_g2mmn hp b

private lemma mw_diagMap_pairUnit_mem_gmmn (_hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {x y : Fin n} (hxy : x ≠ y) :
    diagMap p b (pairUnit p x y (-1)) ∈ gmmn p b i₀ i₁ (-1) := by
  obtain ⟨σ, hσ0, hσ1⟩ := UnitTv.exists_perm_apply_apply (d := n) hi hxy
  have hG : diagMap p b (pairUnit p i₀ i₁ (-1)) ∈ gmmn p b i₀ i₁ (-1) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hσ : permMap p b σ ∈ gmmn p b i₀ i₁ (-1) :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  have hconj : permMap p b σ * diagMap p b (pairUnit p i₀ i₁ (-1)) * (permMap p b σ)⁻¹ ∈
      gmmn p b i₀ i₁ (-1) := mul_mem (mul_mem hσ hG) (inv_mem hσ)
  rw [permMap_mul_diagMap_mul_inv] at hconj
  have heq : pairUnit p i₀ i₁ (-1) ∘ σ.symm = pairUnit p x y (-1) := by
    funext j
    simp only [Function.comp_apply, pairUnit]
    have h1 : (σ.symm j = i₀) ↔ j = x := by rw [Equiv.symm_apply_eq, hσ0]
    have h2 : (σ.symm j = i₁) ↔ j = y := by rw [Equiv.symm_apply_eq, hσ1]
    by_cases hjx : j = x
    · rw [if_pos (h1.mpr hjx), if_pos hjx]
    · rw [if_neg (fun hc => hjx (h1.mp hc)), if_neg hjx]
      by_cases hjy : j = y
      · rw [if_pos (h2.mpr hjy), if_pos hjy, inv_neg_one]
      · rw [if_neg (fun hc => hjy (h2.mp hc)), if_neg hjy]
  rwa [heq] at hconj

private lemma mw_card_ne_one_of_prod_one (hp : p ≠ 2) {e : Fin n → (ZMod p)ˣ}
    {T : Finset (Fin n)} (hsupp : ∀ i, i ∈ T ↔ (e i : ZMod p) = -1)
    (he : ∀ i, (e i : ZMod p) = 1 ∨ (e i : ZMod p) = -1)
    (hprod : ∏ i, (e i : ZMod p) = 1) : T.card ≠ 1 := by
  intro h1
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
  have ha : (e a : ZMod p) = -1 := (hsupp a).mp (Finset.mem_singleton_self a)
  have hprod1 : (∏ i, (e i : ZMod p)) = -1 := by
    have h0 : ∀ c ∈ (Finset.univ : Finset (Fin n)), c ≠ a → (e c : ZMod p) = 1 := by
      intro c _ hc
      rcases he c with h | h
      · exact h
      · exfalso
        have : c ∈ ({a} : Finset (Fin n)) := (hsupp c).mpr h
        exact hc (by simpa [Finset.mem_singleton] using this)
    have h1' : a ∉ (Finset.univ : Finset (Fin n)) → (e a : ZMod p) = 1 := by
      intro h; exact absurd (Finset.mem_univ a) h
    have := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n))) a h0 h1'
    rw [this]
    exact ha
  rw [hprod1] at hprod
  exact mw_one_ne_neg_one hp hprod.symm

private lemma mw_support_erase_erase (hp : p ≠ 2) {e : Fin n → (ZMod p)ˣ} {T : Finset (Fin n)}
    {x y : Fin n} (hx : x ∈ T) (hyT : y ∈ T)
    (hsupp : ∀ i, i ∈ T ↔ (e i : ZMod p) = -1) :
    ∀ i, i ∈ (T.erase x).erase y ↔ ((e * pairUnit p x y (-1)) i : ZMod p) = -1 := by
  intro i
  rw [Finset.mem_erase, Finset.mem_erase]
  by_cases hix : i = x
  · constructor
    · rintro ⟨-, h, -⟩; exact (h hix).elim
    · intro hcon
      have hTi : i ∈ T := by rw [hix]; exact hx
      have hex : (e i : ZMod p) = -1 := (hsupp i).mp hTi
      have h1 : ((e * pairUnit p x y (-1)) i : ZMod p) = 1 := by
        rw [hix]
        rw [hix] at hex
        simp only [Pi.mul_apply, mw_pairUnit_apply_left, Units.val_mul, Units.val_neg,
          Units.val_one]
        rw [hex]
        exact mw_neg_one_mul_neg_one
      rw [h1] at hcon
      exact (mw_one_ne_neg_one hp hcon).elim
  · by_cases hiy : i = y
    · constructor
      · rintro ⟨h, -, -⟩; exact (h hiy).elim
      · intro hcon
        have hTi : i ∈ T := by rw [hiy]; exact hyT
        have hey : (e i : ZMod p) = -1 := (hsupp i).mp hTi
        have h1 : ((e * pairUnit p x y (-1)) i : ZMod p) = 1 := by
          rw [hiy]
          rw [hiy] at hey
          simp only [Pi.mul_apply, mw_pairUnit_apply_right, Units.val_mul, Units.val_neg,
            Units.val_one]
          rw [hey]
          exact mw_neg_one_mul_neg_one
        rw [h1] at hcon
        exact (mw_one_ne_neg_one hp hcon).elim
    · have h1 : ((e * pairUnit p x y (-1)) i : ZMod p) = (e i : ZMod p) := by
        simp only [Pi.mul_apply, mw_pairUnit_apply_of_ne x y hix hiy, mul_one]
      rw [h1]
      exact ⟨fun h => (hsupp i).mp h.2.2,
        fun h => ⟨hiy, hix, (hsupp i).mpr h⟩⟩

private lemma mw_diagMap_succ_gmmn (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {m : ℕ} {T : Finset (Fin n)} {e : Fin n → (ZMod p)ˣ}
    (hT : T ≠ ∅) (hcard : T.card = m)
    (hsupp : ∀ i, i ∈ T ↔ (e i : ZMod p) = -1)
    (he : ∀ i, (e i : ZMod p) = 1 ∨ (e i : ZMod p) = -1)
    (hprod : (∏ i, (e i : ZMod p)) = 1)
    (ih : ∀ m' < m, ∀ (T' : Finset (Fin n)) (e' : Fin n → (ZMod p)ˣ),
      T'.card = m' → (∀ i, i ∈ T' ↔ (e' i : ZMod p) = -1) →
      (∀ i, (e' i : ZMod p) = 1 ∨ (e' i : ZMod p) = -1) →
      (∏ i, (e' i : ZMod p)) = 1 → diagMap p b e' ∈ gmmn p b i₀ i₁ (-1)) :
    diagMap p b e ∈ gmmn p b i₀ i₁ (-1) := by
  have hne1 : T.card ≠ 1 := mw_card_ne_one_of_prod_one hp hsupp he hprod
  have hpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
  have hcard2 : 2 ≤ T.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hx_erase_pos : 0 < (T.erase x).card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hx_erase_pos
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyT : y ∈ T := (Finset.mem_erase.mp hy).2
  let e' : Fin n → (ZMod p)ˣ := e * pairUnit p x y (-1)
  have hcard' : ((T.erase x).erase y).card < m := by
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx, hcard]; omega
  have hsupp' := mw_support_erase_erase hp hx hyT hsupp
  have he' : ∀ i, (e' i : ZMod p) = 1 ∨ (e' i : ZMod p) = -1 := by
    intro i
    have := mw_mul_sign (he i) (mw_pairUnit_val x y i)
    simpa only [e', Pi.mul_apply] using this
  have hprod' : (∏ i, (e' i : ZMod p)) = 1 := by
    simp only [e', Pi.mul_apply, Units.val_mul]
    rw [Finset.prod_mul_distrib, hprod,
      mw_prod_pairUnit_neg_one (p := p) x y (Ne.symm hyx), one_mul]
  have hIH := ih _ hcard' ((T.erase x).erase y) e' rfl hsupp' he' hprod'
  have he_eq : e = e' * pairUnit p x y (-1) := by
    funext i
    simp only [Pi.mul_apply, e']
    rw [mul_assoc, mw_pairUnit_apply_mul_self, mul_one]
  rw [he_eq, ← diagMap_mul]
  exact mul_mem hIH (mw_diagMap_pairUnit_mem_gmmn hp b hi (Ne.symm hyx))

private lemma mw_diagMap_gmmn_key (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) :
    ∀ m (T : Finset (Fin n)) (e : Fin n → (ZMod p)ˣ),
      T.card = m → (∀ i, i ∈ T ↔ (e i : ZMod p) = -1) →
      (∀ i, (e i : ZMod p) = 1 ∨ (e i : ZMod p) = -1) →
      (∏ i, (e i : ZMod p)) = 1 → diagMap p b e ∈ gmmn p b i₀ i₁ (-1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro T e hcard hsupp he hprod
    by_cases hT : T = ∅
    · subst hT
      rw [mw_eq_one_of_support_empty hsupp he, diagMap_one]
      exact Subgroup.one_mem _
    · exact mw_diagMap_succ_gmmn hp b hi hT hcard hsupp he hprod ih

private lemma mw_diagMap_mem_gmmn_of_even_signs (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁)
    (d : Fin n → (ZMod p)ˣ) (hd : ∀ i, (d i : ZMod p) = 1 ∨ (d i : ZMod p) = -1)
    (hprod : ∏ i, (d i : ZMod p) = 1) :
    diagMap p b d ∈ gmmn p b i₀ i₁ (-1) :=
  mw_diagMap_gmmn_key hp b hi (Finset.univ.filter (fun i => (d i : ZMod p) = -1)).card
    (Finset.univ.filter (fun i => (d i : ZMod p) = -1)) d rfl (fun i => by simp) hd hprod

private lemma mw_signedD_mem_gmmn (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {g : U ≃ₗ[ZMod p] U} (h : mwEvenSigned b g) :
    g ∈ gmmn p b i₀ i₁ (-1) := by
  obtain ⟨σ, c, hc, hprod, hg⟩ := h
  let u : Fin n → (ZMod p)ˣ := fun i => Units.mk0 (c i) (by
    rcases hc i with h | h
    · rw [h]; exact mw_one_ne_zero
    · rw [h]; intro h0; exact mw_one_ne_zero (neg_eq_zero.mp h0))
  have hu : ∀ i, (u i : ZMod p) = c i := fun i => Units.val_mk0 _
  have hprod_u : (∏ i, (u i : ZMod p)) = 1 := by
    rw [show (∏ i, (u i : ZMod p)) = ∏ i, c i from
      Finset.prod_congr rfl (fun i _ => hu i)]
    exact hprod
  have heq : g = diagMap p b (u ∘ σ.symm) * permMap p b σ :=
    eq_diagMap_mul_permMap b σ u (fun i => by rw [hu i]; exact hg i)
  rw [heq]
  refine mul_mem (mw_diagMap_mem_gmmn_of_even_signs hp b hi (u ∘ σ.symm) ?_ ?_) ?_
  · intro i
    rw [Function.comp_apply, hu]
    exact hc (σ.symm i)
  · simp only [Function.comp_apply]
    rw [Equiv.prod_comp σ.symm (fun i => (u i : ZMod p))]
    exact hprod_u
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))

private lemma mw_mem_gmmn_iff_even_signed (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (g : U ≃ₗ[ZMod p] U) :
    g ∈ gmmn p b i₀ i₁ (-1) ↔ mwEvenSigned b g := by
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun g _ => mwEvenSigned b g) ?_ ?_ ?_ ?_ hg
    · rintro x (hx | hx)
      · obtain ⟨σ, rfl⟩ := hx
        exact ⟨σ, fun _ => 1, fun _ => Or.inl rfl, by simp, fun i => by
          rw [permMap_apply_basis, one_smul]⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨1, fun i => (pairUnit p i₀ i₁ (-1) i : ZMod p),
          fun i => mw_pairUnit_val i₀ i₁ i, mw_prod_pairUnit_neg_one i₀ i₁ hi,
          fun i => by rw [diagMap_apply_basis]; rfl⟩
    · exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, by simp, fun i => by simp⟩
    · rintro x y _ _ ⟨σ, c, hc, hprod, hx⟩ ⟨τ, c', hc', hprod', hy⟩
      refine ⟨σ * τ, fun i => c' i * c (τ i), fun i => mw_mul_sign_zmod (hc' i) (hc (τ i)),
        ?_, fun i => ?_⟩
      · rw [Finset.prod_mul_distrib, Equiv.prod_comp τ c, hprod', hprod, mul_one]
      · rw [LinearEquiv.mul_apply, hy i, map_smul, hx (τ i), ← mul_smul, Equiv.Perm.mul_apply]
    · rintro x _ ⟨σ, c, hc, hprod, hx⟩
      refine ⟨σ.symm, fun i => c (σ.symm i), fun i => hc (σ.symm i), ?_, fun i => ?_⟩
      · rw [Equiv.prod_comp σ.symm c, hprod]
      · have h1 : x (b (σ.symm i)) = c (σ.symm i) • b i := by
          rw [hx (σ.symm i), Equiv.apply_symm_apply]
        have hcc : c (σ.symm i) * c (σ.symm i) = 1 := by
          rcases hc (σ.symm i) with h | h
          · rw [h, one_mul]
          · rw [h]; exact mw_neg_one_mul_neg_one
        have h2 : c (σ.symm i) • x (b (σ.symm i)) = b i := by
          rw [h1, smul_smul, hcc, one_smul]
        rw [← h2]
        change x.symm (c (σ.symm i) • x (b (σ.symm i))) = c (σ.symm i) • b (σ.symm i)
        rw [map_smul, LinearEquiv.symm_apply_apply]
  · exact mw_signedD_mem_gmmn hp b hi

private lemma mw_ggIsWeylMatrix_A3 : GGIsWeylMatrix (CoxeterMatrix.A 3) :=
  Or.inl ⟨3, Equiv.refl _, by norm_num, Or.inl (by
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl)⟩

private noncomputable def mwA3H {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) : Fin 3 → U :=
  fun i => if i = 0 then b 1 - b 2 else if i = 1 then b 0 - b 1 else b 1 + b 2

private noncomputable def mwA3A {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) :
    Fin 3 → Module.Dual (ZMod p) U :=
  fun i =>
    let A0 : Module.Dual (ZMod p) U :=
      { toFun := fun w => b.coord 1 w - b.coord 2 w
        map_add' := fun x y => by simp only [map_add]; ring
        map_smul' := fun c x => by
          simp only [map_smul, smul_eq_mul, mul_sub, RingHom.id_apply] }
    let A1 : Module.Dual (ZMod p) U :=
      { toFun := fun w => b.coord 0 w - b.coord 1 w
        map_add' := fun x y => by simp only [map_add]; ring
        map_smul' := fun c x => by
          simp only [map_smul, smul_eq_mul, mul_sub, RingHom.id_apply] }
    let A2 : Module.Dual (ZMod p) U :=
      { toFun := fun w => b.coord 1 w + b.coord 2 w
        map_add' := fun x y => by simp only [map_add]; ring
        map_smul' := fun c x => by
          simp only [map_smul, smul_eq_mul, mul_add, RingHom.id_apply] }
    if i = 0 then A0 else if i = 1 then A1 else A2

private lemma mw_finsupp_sub_apply {p : ℕ} {j : Fin 3} (f g : Fin 3 →₀ ZMod p) :
    (f - g) j = f j - g j := rfl

private lemma mwA3_pairing {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) (i j : Fin 3) :
    mwA3A b j (mwA3H b i) = (CartanMatrix.A 3 i j : ZMod p) := by
  fin_cases i <;> fin_cases j <;>
    simp [mwA3A, mwA3H, mw_finsupp_sub_apply, CartanMatrix.A] <;>
    ring_nf

private lemma mwA3_double_g0 {p : ℕ} {g : Fin 3 → ZMod p}
    (h0 : g 1 = 0) (h1 : g 0 + -g 1 + g 2 = 0) (h2 : -g 0 + g 2 = 0) :
    (2 : ZMod p) * g 0 = 0 := by linear_combination h1 - h2 + h0

private lemma mwA3_linearIndependent {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [NoZeroDivisors (ZMod p)] (h2z : (2 : ZMod p) ≠ 0)
    (b : Module.Basis (Fin 3) (ZMod p) U) :
    LinearIndependent (ZMod p) (mwA3H b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrArg (b.coord 0) hg
  have h1 := congrArg (b.coord 1) hg
  have h2 := congrArg (b.coord 2) hg
  simp only [map_zero, map_sum, map_smul, smul_eq_mul] at h0 h1 h2
  rw [Fin.sum_univ_three] at h0 h1 h2
  simp [mwA3H, mw_finsupp_sub_apply] at h0 h1 h2
  have hg0 : g 0 = 0 := by
    have h : (2 : ZMod p) * g 0 = 0 := mwA3_double_g0 h0 h1 h2
    exact (mul_eq_zero.mp h).resolve_left h2z
  fin_cases i
  · exact hg0
  · exact h0
  · rw [hg0, neg_zero, zero_add] at h2
    exact h2

private lemma mwA3_refl_swap12 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) (h2 : ∀ i, mwA3A b i (mwA3H b i) = 2) :
    Module.reflection (h2 0) = permMap p b (Equiv.swap 1 2) := by
  refine b.ext' fun k => ?_
  rw [Module.reflection_apply, permMap_apply_basis]
  fin_cases k <;>
    simp [mwA3A, mwA3H] ; abel

private lemma mwA3_refl_swap01 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) (h2 : ∀ i, mwA3A b i (mwA3H b i) = 2) :
    Module.reflection (h2 1) = permMap p b (Equiv.swap 0 1) := by
  refine b.ext' fun k => ?_
  rw [Module.reflection_apply, permMap_apply_basis]
  fin_cases k <;>
    simp [mwA3A, mwA3H] ; abel

private lemma mwA3_refl_diag {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) (h2 : ∀ i, mwA3A b i (mwA3H b i) = 2) :
    Module.reflection (h2 2) =
      diagMap p b (pairUnit p 1 2 (-1)) * permMap p b (Equiv.swap 1 2) := by
  refine b.ext' fun k => ?_
  rw [Module.reflection_apply, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  fin_cases k <;>
    simp [mwA3A, mwA3H, pairUnit, Equiv.swap_apply_def]

private lemma mwA3_h2 {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) (i : Fin 3) : mwA3A b i (mwA3H b i) = 2 := by
  rw [mwA3_pairing b i i]
  fin_cases i <;> simp [CartanMatrix.A]

private noncomputable def mwA3t {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) : Fin 3 → (U ≃ₗ[ZMod p] U) :=
  fun i => Module.reflection (mwA3_h2 b i)

private lemma mwA3t_apply {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (b : Module.Basis (Fin 3) (ZMod p) U) (i : Fin 3) (w : U) :
    mwA3t b i w = w - mwA3A b i w • mwA3H b i := by
  change Module.reflection (mwA3_h2 b i) w = w - mwA3A b i w • mwA3H b i
  rw [Module.reflection_apply]

private lemma mw_pairUnit_conj {p : ℕ} {π : Equiv.Perm (Fin 3)} (hπ1 : π 1 = 0) (hπ2 : π 2 = 1) :
    pairUnit p 1 2 (-1) ∘ π.symm = pairUnit p 0 1 (-1) := by
  funext j
  simp only [Function.comp_apply, pairUnit]
  have h1 : (π.symm j = 1) ↔ j = 0 := by rw [Equiv.symm_apply_eq, hπ1]
  have h2 : (π.symm j = 2) ↔ j = 1 := by rw [Equiv.symm_apply_eq, hπ2]
  by_cases hj0 : j = 0
  · rw [if_pos (h1.mpr hj0), if_pos hj0]
  · rw [if_neg (fun hc => hj0 (h1.mp hc)), if_neg hj0]
    by_cases hj1 : j = 1
    · rw [if_pos (h2.mpr hj1), if_pos hj1, inv_neg_one]
    · rw [if_neg (fun hc => hj1 (h2.mp hc)), if_neg hj1]

private lemma mwA3_perm_mem (_hp : p ≠ 2) (b : Module.Basis (Fin 3) (ZMod p) U)
    (σ : Equiv.Perm (Fin 3)) :
    permMap p b σ ∈ Subgroup.closure (Set.range (mwA3t b)) := by
  have hmem : ∀ i, mwA3t b i ∈ Subgroup.closure (Set.range (mwA3t b)) := fun i =>
    Subgroup.subset_closure (Set.mem_range_self i)
  have ht0 : mwA3t b 0 = permMap p b (Equiv.swap 1 2) := mwA3_refl_swap12 b (mwA3_h2 b)
  have ht1 : mwA3t b 1 = permMap p b (Equiv.swap 0 1) := mwA3_refl_swap01 b (mwA3_h2 b)
  have h01 : permMap p b (Equiv.swap 0 1) ∈ Subgroup.closure (Set.range (mwA3t b)) := by
    rw [← ht1]; exact hmem 1
  have h12 : permMap p b (Equiv.swap 1 2) ∈ Subgroup.closure (Set.range (mwA3t b)) := by
    rw [← ht0]; exact hmem 0
  have h02 : permMap p b (Equiv.swap 0 2) ∈ Subgroup.closure (Set.range (mwA3t b)) := by
    have hswap : Equiv.swap (0 : Fin 3) 2 = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext k; fin_cases k <;> decide
    rw [hswap, ← permMap_mul, ← permMap_mul]
    exact mul_mem (mul_mem h01 h12) h01
  have hswap_mem : ∀ f : Equiv.Perm (Fin 3), f.IsSwap →
      f ∈ (Subgroup.closure (Set.range (mwA3t b))).comap (mwPermMapHom (p := p) b) := by
    rintro f ⟨x, y, hxy, rfl⟩
    fin_cases x <;> fin_cases y
    · exact absurd rfl hxy
    · exact h01
    · exact h02
    · rw [Equiv.swap_comm]; exact h01
    · exact absurd rfl hxy
    · exact h12
    · rw [Equiv.swap_comm]; exact h02
    · rw [Equiv.swap_comm]; exact h12
    · exact absurd rfl hxy
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin 3))) ≤
      (Subgroup.closure (Set.range (mwA3t b))).comap (mwPermMapHom (p := p) b) := by
    rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    exact hswap_mem
  exact htop (Subgroup.mem_top σ)

private lemma mwA3_diag01_mem (hp : p ≠ 2) (b : Module.Basis (Fin 3) (ZMod p) U) :
    diagMap p b (pairUnit p 0 1 (-1)) ∈ Subgroup.closure (Set.range (mwA3t b)) := by
  have hmem2 : mwA3t b 2 ∈ Subgroup.closure (Set.range (mwA3t b)) :=
    Subgroup.subset_closure (Set.mem_range_self 2)
  have h12 : permMap p b (Equiv.swap 1 2) ∈ Subgroup.closure (Set.range (mwA3t b)) := by
    rw [← mwA3_refl_swap12 b (mwA3_h2 b)]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  have hdiag12 : diagMap p b (pairUnit p 1 2 (-1)) ∈ Subgroup.closure (Set.range (mwA3t b)) := by
    have h : diagMap p b (pairUnit p 1 2 (-1)) =
        mwA3t b 2 * (permMap p b (Equiv.swap 1 2))⁻¹ := by
      rw [show mwA3t b 2 = diagMap p b (pairUnit p 1 2 (-1)) *
          permMap p b (Equiv.swap 1 2) from mwA3_refl_diag b (mwA3_h2 b),
        mul_assoc, mul_inv_cancel, mul_one]
    rw [h]
    exact mul_mem hmem2 (inv_mem h12)
  obtain ⟨π, hπ1, hπ2⟩ := UnitTv.exists_perm_apply_apply (by decide : (1 : Fin 3) ≠ 2)
    (by decide : (0 : Fin 3) ≠ 1)
  have hπmem := mwA3_perm_mem hp b π
  have hconj : permMap p b π * diagMap p b (pairUnit p 1 2 (-1)) * (permMap p b π)⁻¹ ∈
      Subgroup.closure (Set.range (mwA3t b)) := mul_mem (mul_mem hπmem hdiag12) (inv_mem hπmem)
  rw [permMap_mul_diagMap_mul_inv] at hconj
  rwa [mw_pairUnit_conj (p := p) (π := π) hπ1 hπ2] at hconj

private lemma mwA3_closure_le (hp : p ≠ 2) (b : Module.Basis (Fin 3) (ZMod p) U) :
    Subgroup.closure (Set.range (mwA3t b)) ≤ gmmn p b 0 1 (-1) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change mwA3t b 0 ∈ gmmn p b 0 1 (-1)
    rw [show mwA3t b 0 = permMap p b (Equiv.swap 1 2)
        from mwA3_refl_swap12 b (mwA3_h2 b)]
    exact Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap 1 2)))
  · change mwA3t b 1 ∈ gmmn p b 0 1 (-1)
    rw [show mwA3t b 1 = permMap p b (Equiv.swap 0 1)
        from mwA3_refl_swap01 b (mwA3_h2 b)]
    exact Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap 0 1)))
  · change mwA3t b 2 ∈ gmmn p b 0 1 (-1)
    rw [show mwA3t b 2 = diagMap p b (pairUnit p 1 2 (-1)) *
        permMap p b (Equiv.swap 1 2) from mwA3_refl_diag b (mwA3_h2 b)]
    exact mul_mem (mw_diagMap_pairUnit_mem_gmmn hp b (by decide : (0 : Fin 3) ≠ 1)
        (by decide : (1 : Fin 3) ≠ 2))
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap 1 2))))

private lemma mwA3_closure_ge (hp : p ≠ 2) (b : Module.Basis (Fin 3) (ZMod p) U) :
    gmmn p b 0 1 (-1) ≤ Subgroup.closure (Set.range (mwA3t b)) := by
  rw [gmmn, Subgroup.closure_le]
  rintro x (hx | hx)
  · obtain ⟨σ, rfl⟩ := hx
    exact mwA3_perm_mem hp b σ
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mwA3_diag01_mem hp b

private lemma mw_linWeyl_gmmn_A3 (hp : p ≠ 2) (b : Module.Basis (Fin 3) (ZMod p) U) :
    LinWeyl p (gmmn p b 0 1 (-1)) := by
  classical
  have hlin : LinWeyl p (Subgroup.closure (Set.range (mwA3t b))) :=
    ggResI_linWeyl_T hp mw_ggIsWeylMatrix_A3 (ggIntCartan_A 3) (mwA3t b) (mwA3H b) (mwA3A b)
      (mwA3t_apply b) (mwA3_pairing b) (mwA3_linearIndependent (mw_two_ne_zero hp) b)
  have heq : Subgroup.closure (Set.range (mwA3t b)) = gmmn p b 0 1 (-1) :=
    le_antisymm (mwA3_closure_le hp b) (mwA3_closure_ge hp b)
  rwa [heq] at hlin

theorem linWeyl_gmmn_neg_one (hp : p ≠ 2) (hn : 3 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) : LinWeyl p (gmmn p b i₀ i₁ (-1)) := by
  by_cases h3 : n = 3
  · subst h3
    have h01 : LinWeyl p (gmmn p b 0 1 (-1)) := mw_linWeyl_gmmn_A3 hp b
    have heq : gmmn p b i₀ i₁ (-1) = gmmn p b 0 1 (-1) := by
      apply le_antisymm
      · intro g hg
        exact (mw_mem_gmmn_iff_even_signed hp b (by decide : (0 : Fin 3) ≠ 1) g).mpr
          ((mw_mem_gmmn_iff_even_signed hp b hi g).mp hg)
      · intro g hg
        exact (mw_mem_gmmn_iff_even_signed hp b hi g).mpr
          ((mw_mem_gmmn_iff_even_signed hp b (by decide : (0 : Fin 3) ≠ 1) g).mp hg)
    rwa [heq]
  · have h4 : 4 ≤ n := by omega
    exact ggRC_linWeyl_of_even_signed hp h4 b _
      (fun a => mw_mem_gmmn_iff_even_signed hp b hi a)

theorem linWeyl_g2mmn_neg_one (hp : p ≠ 2) (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} : LinWeyl p (g2mmn p b i₀ i₁ (-1)) :=
  ggRC_linWeyl_of_signed hp hn b _ (fun a => mw_mem_g2mmn_iff_signed hp b a)

end CFSG.StandardType.ZS
