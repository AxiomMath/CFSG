module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.NQCat.G2Rad

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

section Field

variable {K : Type} [Field K] [CharP K 2]

@[expose] def tr (s : K) (t : K × K × K × K) : K × K × K × K :=
  (t.1, t.2.1 + s * t.1, t.2.2.1 + s ^ 2 * t.1,
    t.2.2.2 + s ^ 3 * t.1 + s ^ 2 * t.2.1 + s * t.2.2.1)

omit [CharP K 2] in
theorem tr_sub (s : K) (t : K × K × K × K) :
    tr s t - t = (0, s * t.1, s ^ 2 * t.1, s ^ 3 * t.1 + s ^ 2 * t.2.1 + s * t.2.2.1) := by
  obtain ⟨t₁, t₂, t₃, t₄⟩ := t
  simp only [tr, Prod.mk_sub_mk, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

omit [CharP K 2] in
theorem tr_sub_mem {D : AddSubgroup (K × K × K × K)} (hD : ∀ s, ∀ t ∈ D, tr s t ∈ D) (s : K)
    {t : K × K × K × K} (ht : t ∈ D) :
    ((0 : K), s * t.1, s ^ 2 * t.1, s ^ 3 * t.1 + s ^ 2 * t.2.1 + s * t.2.2.1) ∈ D := by
  rw [← tr_sub]
  exact D.sub_mem (hD s t ht) ht

theorem exists_b_mem {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {D : AddSubgroup (K × K × K × K)}
    (hD : ∀ s, ∀ t ∈ D, tr s t ∈ D) {t : K × K × K × K} (ht : t ∈ D) (ht0 : t ≠ 0) :
    ∃ β : K, β ≠ 0 ∧ ((0 : K), (0 : K), (0 : K), β) ∈ D := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω1' : ω + 1 ≠ 0 := fun h => hω1 (by linear_combination h - h2)
  obtain ⟨t₁, t₂, t₃, t₄⟩ := t
  by_cases h1 : t₁ = 0
  · subst h1
    by_cases h2' : t₂ = 0
    · subst h2'
      by_cases h3 : t₃ = 0
      · subst h3
        exact ⟨t₄, fun h => ht0 (by rw [h]; rfl), ht⟩
      · refine ⟨t₃, h3, ?_⟩
        simpa using tr_sub_mem hD 1 ht
    · by_cases h : t₂ + t₃ = 0
      · refine ⟨ω ^ 2 * t₂ + ω * t₃, ?_, by simpa using tr_sub_mem hD ω ht⟩
        intro h'
        have ht3 : t₃ = t₂ := by linear_combination h - t₂ * h2
        rw [ht3] at h'
        have e : ω * (ω + 1) * t₂ = 0 := by linear_combination h'
        exact mul_ne_zero (mul_ne_zero hω0 hω1') h2' e
      · exact ⟨t₂ + t₃, h, by simpa using tr_sub_mem hD 1 ht⟩
  · refine ⟨ω * (ω + 1) * t₁, mul_ne_zero (mul_ne_zero hω0 hω1') h1, ?_⟩
    have h := tr_sub_mem hD ω (tr_sub_mem hD 1 ht)
    have e : ((0 : K), ω * (0 : K), ω ^ 2 * (0 : K),
        ω ^ 3 * 0 + ω ^ 2 * (1 * t₁) + ω * (1 ^ 2 * t₁)) =
        ((0 : K), (0 : K), (0 : K), ω * (ω + 1) * t₁) := by
      simp only [mul_zero, Prod.mk.injEq, true_and]
      ring
    simpa only [e] using h

omit [CharP K 2] in
theorem inv_eq_pow [Finite K] {u : K} (hu : u ≠ 0) : u⁻¹ = u ^ (Nat.card K - 2) := by
  have h1 : u ^ (Nat.card K - 1) = 1 := by
    have h := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 u hu)
    rw [Nat.card_units] at h
    simpa using congrArg Units.val h
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [show Nat.card K - 1 = (Nat.card K - 2) + 1 by omega, pow_succ] at h1
  exact (eq_inv_of_mul_eq_one_left h1).symm

theorem subring_eq_top [Finite K] (h8 : 8 ≤ Nat.card K) (R : Subring K)
    (hR : ∀ s : K, s ^ 2 + s ∈ R) : R = ⊤ := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra hne
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  by_cases hr : ∃ r ∈ R, r ≠ 0 ∧ r ≠ 1
  · obtain ⟨r, hr, hr0, hr1⟩ := hr
    apply hx
    have hm : x * (r ^ 2 + r) ∈ R := by
      have e : x * (r ^ 2 + r) = ((x * r) ^ 2 + x * r) - (x ^ 2 + x) * r ^ 2 := by
        linear_combination (x * r ^ 2) * h2
      rw [e]
      exact R.sub_mem (hR _) (R.mul_mem (hR x) (R.pow_mem hr 2))
    have hr' : r ^ 2 + r ≠ 0 := by
      have hr1' : r + 1 ≠ 0 := fun h => hr1 (by linear_combination h - h2)
      have e : r ^ 2 + r = r * (r + 1) := by ring
      rw [e]
      exact mul_ne_zero hr0 hr1'
    have e : x = x * (r ^ 2 + r) * (r ^ 2 + r)⁻¹ := (mul_inv_cancel_right₀ hr' x).symm
    rw [e, inv_eq_pow hr']
    exact R.mul_mem hm (R.pow_mem (R.add_mem (R.pow_mem hr 2) hr) _)
  · simp only [not_exists, not_and, not_not] at hr
    have h01 : ∀ s : K, s ^ 2 + s = 0 ∨ s ^ 2 + s = 1 := fun s => by
      by_cases h : s ^ 2 + s = 0
      · exact Or.inl h
      · exact Or.inr (hr _ (hR s) h)
    have hx01 : x ≠ 0 ∧ x ≠ 1 := ⟨fun h => hx (h ▸ R.zero_mem), fun h => hx (h ▸ R.one_mem)⟩
    have hroot : ∀ s : K, s ^ 2 + s = 0 → s = 0 ∨ s = 1 := fun s h => by
      have e : s * (s + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 e with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linear_combination h' - h2)
    have hx1 : x ^ 2 + x = 1 := by
      rcases h01 x with h | h
      · rcases hroot x h with h' | h'
        · exact absurd h' hx01.1
        · exact absurd h' hx01.2
      · exact h
    have hs : ∀ s : K, s = 0 ∨ s = 1 ∨ s = x ∨ s = x + 1 := by
      intro s
      rcases h01 s with h | h
      · rcases hroot s h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · have e : (s - x) * (s - x - 1) = 0 := by
          linear_combination h - hx1 + (x ^ 2 - x * s - s + x) * h2
        rcases mul_eq_zero.1 e with h' | h'
        · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h')))
        · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))
    have : Fintype K := Fintype.ofFinite K
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1, x, x + 1} := fun s _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hs s
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ] at hc
    have h4 : ({0, 1, x, x + 1} : Finset K).card ≤ 4 := Finset.card_le_four
    rw [Nat.card_eq_fintype_card] at h8
    omega

theorem eq_top_of_b [Finite K] (h8 : 8 ≤ Nat.card K) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {D : AddSubgroup (K × K × K × K)} (hD : ∀ s, ∀ t ∈ D, tr s t ∈ D)
    (hW : ∀ β : K, ((0 : K), (0 : K), (0 : K), β) ∈ D → (β, (0 : K), (0 : K), (0 : K)) ∈ D)
    {β₀ : K} (hβ₀ : β₀ ≠ 0) (h0 : ((0 : K), (0 : K), (0 : K), β₀) ∈ D) : D = ⊤ := by
  let R : Subring K :=
    { carrier := {m | ∀ β : K, ((0 : K), (0 : K), (0 : K), β) ∈ D →
        ((0 : K), (0 : K), (0 : K), m * β) ∈ D}
      mul_mem' := fun {a b} ha hb β hβ => by
        rw [mul_assoc]
        exact ha _ (hb β hβ)
      one_mem' := fun β hβ => by rwa [one_mul]
      add_mem' := fun {a b} ha hb β hβ => by
        have := D.add_mem (ha β hβ) (hb β hβ)
        simpa [add_mul] using this
      zero_mem' := fun β _ => by rw [zero_mul]; exact D.zero_mem
      neg_mem' := fun {a} ha β hβ => by
        have := D.neg_mem (ha β hβ)
        simpa [neg_mul] using this }
  have hR : ∀ s : K, s ^ 2 + s ∈ R := by
    intro s β hβ
    have h := tr_sub_mem hD 1 (tr_sub_mem hD s (hW β hβ))
    have e : ((0 : K), 1 * (0 : K), 1 ^ 2 * (0 : K),
        1 ^ 3 * 0 + 1 ^ 2 * (s * β) + 1 * (s ^ 2 * β)) =
        ((0 : K), (0 : K), (0 : K), (s ^ 2 + s) * β) := by
      simp only [mul_zero, Prod.mk.injEq, true_and]
      ring
    simpa only [e] using h
  have htop := subring_eq_top h8 R hR
  have hb : ∀ β : K, ((0 : K), (0 : K), (0 : K), β) ∈ D := fun β => by
    have hm : β * β₀⁻¹ ∈ R := htop ▸ Subring.mem_top _
    have := hm β₀ h0
    rwa [mul_assoc, inv_mul_cancel₀ hβ₀, mul_one] at this
  have ha : ∀ β : K, (β, (0 : K), (0 : K), (0 : K)) ∈ D := fun β => hW β (hb β)
  have huv : ∀ s β : K, ((0 : K), s * β, s ^ 2 * β, (0 : K)) ∈ D := by
    intro s β
    have := D.sub_mem (tr_sub_mem hD s (ha β)) (hb (s ^ 3 * β))
    simpa using this
  have hv : ∀ γ : K, ((0 : K), (0 : K), γ, (0 : K)) ∈ D := by
    intro γ
    have hω1' : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
    have := D.sub_mem (huv ω (γ * (ω - 1)⁻¹ * ω⁻¹)) (huv 1 (γ * (ω - 1)⁻¹))
    have e1 : ω * (γ * (ω - 1)⁻¹ * ω⁻¹) - 1 * (γ * (ω - 1)⁻¹) = 0 := by
      field_simp
      ring
    have e2 : ω ^ 2 * (γ * (ω - 1)⁻¹ * ω⁻¹) - 1 ^ 2 * (γ * (ω - 1)⁻¹) = γ := by
      field_simp
    simp only [Prod.mk_sub_mk, sub_self, e1, e2] at this
    exact this
  have hu : ∀ γ : K, ((0 : K), γ, (0 : K), (0 : K)) ∈ D := by
    intro γ
    have := D.sub_mem (huv 1 γ) (hv γ)
    simp only [Prod.mk_sub_mk, sub_self, one_mul, one_pow, sub_zero] at this
    exact this
  rw [eq_top_iff]
  rintro ⟨t₁, t₂, t₃, t₄⟩ -
  have := D.add_mem (D.add_mem (D.add_mem (ha t₁) (hu t₂)) (hv t₃)) (hb t₄)
  simpa using this

end Field

section Group

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def nf
    (t : K × K × K × K) : ModGL Tag.G2 K :=
  gX rA t.1 * (gX rU t.2.1 * (gX rV t.2.2.1 * gX rB t.2.2.2))

omit [CharP K 2] in
theorem nf_zero :
    nf (0 : K × K × K × K) = 1 := by
  simp [nf, gX_zero]

theorem b_mul_a
    (x y : K) : gX rB y * gX rA x = gX rA x * (gX rB y * gX rC (x * y)) := by
  have e : gX rB y * gX rA x = ⁅gX rA x, gX rB y⁆⁻¹ * (gX rA x * gX rB y) := by
    rw [commutatorElement_def]
    group
  rw [e, rel_ab, gX_inv, ← mul_assoc, ← (comm_ac x (x * y)).eq, mul_assoc,
    ← (comm_bc y (x * y)).eq]

theorem v_mul_u
    (x y : K) : gX rV y * gX rU x = gX rU x * (gX rV y * gX rC (x * y)) := by
  have e : gX rV y * gX rU x = ⁅gX rU x, gX rV y⁆⁻¹ * (gX rU x * gX rV y) := by
    rw [commutatorElement_def]
    group
  rw [e, rel_uv, gX_inv, ← mul_assoc, ← (comm_uc x (x * y)).eq, mul_assoc,
    ← (comm_vc y (x * y)).eq]

theorem nf_mul
    (t s : K × K × K × K) :
    nf t * nf s = nf (t + s) * gX rC (s.1 * t.2.2.2 + s.2.1 * t.2.2.1) := by
  obtain ⟨t₁, t₂, t₃, t₄⟩ := t
  obtain ⟨s₁, s₂, s₃, s₄⟩ := s
  have hBA : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rB y * (gX rA x * w) = gX rA x * (gX rB y * (gX rC (x * y) * w)) := fun x y w => by
    rw [← mul_assoc, b_mul_a]
    simp only [mul_assoc]
  have hVU : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rV y * (gX rU x * w) = gX rU x * (gX rV y * (gX rC (x * y) * w)) := fun x y w => by
    rw [← mul_assoc, v_mul_u]
    simp only [mul_assoc]
  have hVA : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rV y * (gX rA x * w) = gX rA x * (gX rV y * w) := fun x y w =>
    (comm_av x y).symm.left_comm w
  have hUA : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rU y * (gX rA x * w) = gX rA x * (gX rU y * w) := fun x y w =>
    (comm_au x y).symm.left_comm w
  have hBU : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rB y * (gX rU x * w) = gX rU x * (gX rB y * w) := fun x y w =>
    (comm_ub x y).symm.left_comm w
  have hBV : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rB y * (gX rV x * w) = gX rV x * (gX rB y * w) := fun x y w =>
    (comm_vb x y).symm.left_comm w
  have hCU : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rC y * (gX rU x * w) = gX rU x * (gX rC y * w) := fun x y w =>
    (comm_uc x y).symm.left_comm w
  have hCV : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rC y * (gX rV x * w) = gX rV x * (gX rC y * w) := fun x y w =>
    (comm_vc x y).symm.left_comm w
  have hCB : ∀ (x y : K) (w : ModGL Tag.G2 K),
      gX rC y * (gX rB x * w) = gX rB x * (gX rC y * w) := fun x y w =>
    (comm_bc x y).symm.left_comm w
  have hCB' : ∀ (x y : K), gX rC y * gX rB x = gX rB x * gX rC y := fun x y =>
    (comm_bc x y).symm.eq
  have hM : ∀ (d : Fin Tag.G2.rank → ℤ) (x y : K) (w : ModGL Tag.G2 K),
      gX d x * (gX d y * w) = gX d (x + y) * w := fun d x y w => by
    rw [← mul_assoc, ← gX_add]
  have hM' : ∀ (d : Fin Tag.G2.rank → ℤ) (x y : K), gX d x * gX d y = gX d (x + y) :=
    fun d x y => (gX_add d x y).symm
  simp only [nf, Prod.mk_add_mk, mul_assoc, hBA, hVU, hVA, hUA, hBU, hBV, hCU, hCV, hCB,
    hCB', hM, hM']
  rw [add_comm (s₂ * t₃)]

theorem nf_mul_C
    (t s : K × K × K × K) (c d : K) :
    nf t * gX rC c * (nf s * gX rC d) =
      nf (t + s) * gX rC (c + d + (s.1 * t.2.2.2 + s.2.1 * t.2.2.1)) := by
  have hC : Commute (gX rC c) (nf s) := by
    obtain ⟨s₁, s₂, s₃, s₄⟩ := s
    simp only [nf]
    exact ((comm_ac s₁ c).symm.mul_right ((comm_uc s₂ c).symm.mul_right
      ((comm_vc s₃ c).symm.mul_right (comm_bc s₄ c).symm)))
  calc nf t * gX rC c * (nf s * gX rC d) = nf t * nf s * (gX rC c * gX rC d) := by
        rw [mul_assoc, ← mul_assoc (gX rC c), hC.eq]
        group
    _ = _ := by
        rw [nf_mul, mul_assoc, ← gX_add, ← gX_add]
        congr 2
        ring

omit [CharP K 2] in
theorem nf_mul_inj
    {t s : K × K × K × K} {c d : K} (h : nf t * gX rC c = nf s * gX rC d) : t = s ∧ c = d := by
  classical
  obtain ⟨t₁, t₂, t₃, t₄⟩ := t
  obtain ⟨s₁, s₂, s₃, s₄⟩ := s
  have hAU : rA ≠ rU := by decide
  have hAV : rA ≠ rV := by decide
  have hAB : rA ≠ rB := by decide
  have hAC : rA ≠ rC := by decide
  have hUV : rU ≠ rV := by decide
  have hUB : rU ≠ rB := by decide
  have hUC : rU ≠ rC := by decide
  have hVB : rV ≠ rB := by decide
  have hVC : rV ≠ rC := by decide
  have hBC : rB ≠ rC := by decide
  have hnd : [rA, rU, rV, rB, rC].Nodup := by
    simp [hAU, hAV, hAB, hAC, hUV, hUB, hUC, hVB, hVC, hBC]
  have hL : ∀ α ∈ [rA, rU, rV, rB, rC], IsRoot Tag.G2 α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl <;> exact isRoot_pos_iff.2 (by simp)
  let f : K × K × K × K → K → (Fin Tag.G2.rank → ℤ) → K := fun t c α =>
    if α = rA then t.1 else if α = rU then t.2.1 else if α = rV then t.2.2.1 else
      if α = rB then t.2.2.2 else c
  have key := pinnedX_list_prod_injective (τ := Tag.G2) (R := K) [rA, rU, rV, rB, rC] hnd hL
    (f (t₁, t₂, t₃, t₄) c) (f (s₁, s₂, s₃, s₄) d) (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, f,
        hAU.symm, hAV.symm, hAB.symm, hAC.symm, hUV.symm, hUB.symm, hUC.symm, hVB.symm,
        hVC.symm, hBC.symm, ↓reduceIte]
      simpa [nf, mul_assoc] using h)
  have k1 := key rA (by simp)
  have k2 := key rU (by simp)
  have k3 := key rV (by simp)
  have k4 := key rB (by simp)
  have k5 := key rC (by simp)
  simp only [f, hAU.symm, hAV.symm, hAB.symm, hAC.symm, hUV.symm, hUB.symm, hUC.symm, hVB.symm,
    hVC.symm, hBC.symm, ↓reduceIte] at k1 k2 k3 k4 k5
  exact ⟨by rw [k1, k2, k3, k4], k5⟩

@[expose] noncomputable def coord
    (g : ModGL Tag.G2 K) : K × K × K × K :=
  Classical.epsilon fun t => ∃ c : K, g = nf t * gX rC c

omit [CharP K 2] in
theorem exists_nf
    {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1}) :
    ∃ t : K × K × K × K, ∃ c : K, g = nf t * gX rC c := by
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_one hg
  exact ⟨(t₁, t₂, t₃, t₄), t₅, by simp only [nf, mul_assoc]⟩

omit [CharP K 2] in
theorem coord_nf
    (t : K × K × K × K) (c : K) : coord (nf t * gX rC c) = t := by
  obtain ⟨c', hc'⟩ := Classical.epsilon_spec (p := fun t' => ∃ c' : K,
    nf t * gX rC c = nf t' * gX rC c') ⟨t, c, rfl⟩
  exact (nf_mul_inj hc').1.symm

omit [CharP K 2] in
theorem eq_nf_coord
    {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1}) :
    ∃ c : K, g = nf (coord g) * gX rC c := by
  obtain ⟨t, c, rfl⟩ := exists_nf hg
  exact ⟨c, by rw [coord_nf]⟩

theorem coord_mul
    {g h : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1})
    (hh : h ∈ parabolicRadical Tag.G2 K {i1}) : coord (g * h) = coord g + coord h := by
  obtain ⟨t, c, rfl⟩ := exists_nf hg
  obtain ⟨s, d, rfl⟩ := exists_nf hh
  rw [nf_mul_C, coord_nf, coord_nf, coord_nf]

omit [CharP K 2] in
theorem memA (x : K) :
    gX rA x ∈ parabolicRadical Tag.G2 K {i1} := mem_one (Or.inl rfl) x

omit [CharP K 2] in
theorem memU (x : K) :
    gX rU x ∈ parabolicRadical Tag.G2 K {i1} := mem_one (Or.inr (Or.inl rfl)) x

omit [CharP K 2] in
theorem memV (x : K) :
    gX rV x ∈ parabolicRadical Tag.G2 K {i1} := mem_one (Or.inr (Or.inr (Or.inl rfl))) x

omit [CharP K 2] in
theorem memB (x : K) :
    gX rB x ∈ parabolicRadical Tag.G2 K {i1} := mem_one (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) x

omit [CharP K 2] in
theorem memC (x : K) :
    gX rC x ∈ parabolicRadical Tag.G2 K {i1} := mem_one (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) x

omit [CharP K 2] in
theorem coord_A
    (x : K) : coord (gX rA x) = (x, 0, 0, 0) := by
  have e : gX rA x = nf (x, 0, 0, 0) * gX rC 0 := by simp [nf, gX_zero]
  rw [e, coord_nf]

omit [CharP K 2] in
theorem coord_U
    (x : K) : coord (gX rU x) = (0, x, 0, 0) := by
  have e : gX rU x = nf (0, x, 0, 0) * gX rC 0 := by simp [nf, gX_zero]
  rw [e, coord_nf]

omit [CharP K 2] in
theorem coord_V
    (x : K) : coord (gX rV x) = (0, 0, x, 0) := by
  have e : gX rV x = nf (0, 0, x, 0) * gX rC 0 := by simp [nf, gX_zero]
  rw [e, coord_nf]

omit [CharP K 2] in
theorem coord_B
    (x : K) : coord (gX rB x) = (0, 0, 0, x) := by
  have e : gX rB x = nf (0, 0, 0, x) * gX rC 0 := by simp [nf, gX_zero]
  rw [e, coord_nf]

omit [CharP K 2] in
theorem coord_C
    (x : K) : coord (gX rC x) = 0 := by
  have e : gX rC x = nf 0 * gX rC x := by rw [nf_zero, one_mul]
  rw [e, coord_nf]

theorem exists_of_mem_N1
    {g : ModGL Tag.G2 K} (hg : g ∈ (N1 : Subgroup (ModGL Tag.G2 K))) : ∃ c : K, g = gX rC c := by
  unfold N1 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩
  | one => exact ⟨0, (gX_zero rC).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (gX_add rC a b).symm⟩
  | inv x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, gX_inv rC a⟩

theorem mem_N1_iff
    {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1}) :
    g ∈ (N1 : Subgroup (ModGL Tag.G2 K)) ↔ coord g = 0 := by
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := exists_of_mem_N1 h
    exact coord_C c
  · intro h
    obtain ⟨c, hc⟩ := eq_nf_coord hg
    rw [hc, h, nf_zero, one_mul]
    exact gX_c_mem_N1 c

theorem coord_conj_xr
    {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1}) (s : K) :
    coord (gX rR s * g * (gX rR s)⁻¹) = tr s (coord g) := by
  obtain ⟨c, hgc⟩ := eq_nf_coord hg
  set t := coord g with ht
  have hRA : ∀ x : K, gX rR s * gX rA x * (gX rR s)⁻¹ = gX rC (x ^ 2 * s ^ 3) *
      (gX rB (x * s ^ 3) * (gX rV (x * s ^ 2) * (gX rU (x * s) * gX rA x))) := fun x => by
    have e : gX rR s * gX rA x * (gX rR s)⁻¹ = ⁅gX rA x, gX rR s⁆⁻¹ * gX rA x := by
      rw [commutatorElement_def]
      group
    rw [e, rel_ar]
    simp only [mul_inv_rev, gX_inv, mul_assoc]
  have hRU : ∀ y : K, gX rR s * gX rU y * (gX rR s)⁻¹ =
      gX rC (s * y ^ 2) * (gX rB (s ^ 2 * y) * gX rU y) := fun y => by
    have e : gX rR s * gX rU y * (gX rR s)⁻¹ = ⁅gX rR s, gX rU y⁆ * gX rU y := by
      rw [commutatorElement_def]
      group
    rw [e, rel_ru, mul_assoc]
  have hRV : ∀ y : K, gX rR s * gX rV y * (gX rR s)⁻¹ = gX rB (s * y) * gX rV y := fun y => by
    have e : gX rR s * gX rV y * (gX rR s)⁻¹ = ⁅gX rR s, gX rV y⁆ * gX rV y := by
      rw [commutatorElement_def]
      group
    rw [e, rel_rv]
  have hRB : ∀ y : K, gX rR s * gX rB y * (gX rR s)⁻¹ = gX rB y := fun y => by
    rw [(comm_rb s y).eq, mul_inv_cancel_right]
  have hRC : ∀ y : K, gX rR s * gX rC y * (gX rR s)⁻¹ = gX rC y := fun y => by
    rw [(comm_rc s y).eq, mul_inv_cancel_right]
  have e : gX rR s * g * (gX rR s)⁻¹ =
      (gX rR s * gX rA t.1 * (gX rR s)⁻¹) * ((gX rR s * gX rU t.2.1 * (gX rR s)⁻¹) *
        ((gX rR s * gX rV t.2.2.1 * (gX rR s)⁻¹) * (gX rR s * gX rB t.2.2.2 * (gX rR s)⁻¹))) *
        (gX rR s * gX rC c * (gX rR s)⁻¹) := by
    rw [hgc, nf]
    group
  have k1 : ∀ a b c d e : K,
      coord (gX rC a * (gX rB b * (gX rV c * (gX rU d * gX rA e)))) = (e, d, c, b) := by
    intro a b c d e
    rw [coord_mul (memC a) (mul_mem (memB b) (mul_mem (memV c) (mul_mem (memU d) (memA e)))),
      coord_mul (memB b) (mul_mem (memV c) (mul_mem (memU d) (memA e))),
      coord_mul (memV c) (mul_mem (memU d) (memA e)), coord_mul (memU d) (memA e),
      coord_C, coord_B, coord_V, coord_U, coord_A]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have k2 : ∀ a b d : K, coord (gX rC a * (gX rB b * gX rU d)) = (0, d, 0, b) := by
    intro a b d
    rw [coord_mul (memC a) (mul_mem (memB b) (memU d)), coord_mul (memB b) (memU d), coord_C,
      coord_B, coord_U]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have k3 : ∀ b c : K, coord (gX rB b * gX rV c) = (0, 0, c, b) := by
    intro b c
    rw [coord_mul (memB b) (memV c), coord_B, coord_V]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have m1 := mul_mem (memC (t.1 ^ 2 * s ^ 3)) (mul_mem (memB (t.1 * s ^ 3))
    (mul_mem (memV (t.1 * s ^ 2)) (mul_mem (memU (t.1 * s)) (memA t.1))))
  have m2 := mul_mem (memC (s * t.2.1 ^ 2)) (mul_mem (memB (s ^ 2 * t.2.1)) (memU t.2.1))
  have m3 := mul_mem (memB (s * t.2.2.1)) (memV t.2.2.1)
  have m4 := memB (K := K) t.2.2.2
  rw [e, hRA, hRU, hRV, hRB, hRC, coord_mul (mul_mem m1 (mul_mem m2 (mul_mem m3 m4))) (memC c),
    coord_mul m1 (mul_mem m2 (mul_mem m3 m4)), coord_mul m2 (mul_mem m3 m4), coord_mul m3 m4,
    k1, k2, k3, coord_B, coord_C]
  simp only [tr, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring, by ring⟩

theorem weyl_conj
    (i : Fin Tag.G2.rank) {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β) (c : K) :
    weylElt Tag.G2 K i 1 * gX β c * (weylElt Tag.G2 K i 1)⁻¹ = gX (reflect Tag.G2 i β) c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hβ
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
  rw [h, hε1, one_mul]

theorem conj_weyl_b_c
    (β c : K) : weylElt Tag.G2 K i1 1 * (gX rB β * gX rC c) * (weylElt Tag.G2 K i1 1)⁻¹ =
      gX rA β * gX rC c := by
  have hB : IsRoot Tag.G2 rB := (isRoot_pos_iff.2 (by simp)).1
  have hC : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1
  have eB : reflect Tag.G2 i1 rB = rA := by funext k; fin_cases k <;> decide
  have eC : reflect Tag.G2 i1 rC = rC := by funext k; fin_cases k <;> decide
  have e : weylElt Tag.G2 K i1 1 * (gX rB β * gX rC c) * (weylElt Tag.G2 K i1 1)⁻¹ =
      (weylElt Tag.G2 K i1 1 * gX rB β * (weylElt Tag.G2 K i1 1)⁻¹) *
        (weylElt Tag.G2 K i1 1 * gX rC c * (weylElt Tag.G2 K i1 1)⁻¹) := by group
  rw [e, weyl_conj i1 hB, weyl_conj i1 hC, eB, eC]

@[expose] noncomputable def coordSet
    (S : Subgroup (ModGL Tag.G2 K)) : AddSubgroup (K × K × K × K) where
  carrier := {t | ∃ c : K, nf t * gX rC c ∈ S}
  add_mem' := by
    rintro t t' ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c + c' + (t'.1 * t.2.2.2 + t'.2.1 * t.2.2.1), ?_⟩
    rw [← nf_mul_C]
    exact S.mul_mem hc hc'
  zero_mem' := ⟨0, by rw [nf_zero, gX_zero, one_mul]; exact S.one_mem⟩
  neg_mem' := by
    rintro t ⟨c, hc⟩
    have e : -t = t := by
      obtain ⟨t₁, t₂, t₃, t₄⟩ := t
      simp only [Prod.neg_mk, CharTwo.neg_eq]
    exact ⟨c, by rw [e]; exact hc⟩

theorem tr_mem_coordSet
    {S : Subgroup (ModGL Tag.G2 K)} (hSQ : S ≤ parabolicRadical Tag.G2 K {i1}) {s : K}
    (hs : gX rR s ∈ Subgroup.normalizer (S : Set (ModGL Tag.G2 K))) {t : K × K × K × K}
    (ht : t ∈ coordSet S) : tr s t ∈ coordSet S := by
  obtain ⟨c, hc⟩ := ht
  have hc' : gX rR s * (nf t * gX rC c) * (gX rR s)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 hs _).1 hc
  obtain ⟨d, hd⟩ := eq_nf_coord (hSQ hc')
  rw [coord_conj_xr (hSQ hc) s, coord_nf] at hd
  exact ⟨d, hd ▸ hc'⟩

theorem weyl_mem_coordSet
    {S : Subgroup (ModGL Tag.G2 K)}
    (hn : weylElt Tag.G2 K i1 1 ∈ Subgroup.normalizer (S : Set (ModGL Tag.G2 K))) {β : K}
    (hβ : ((0 : K), (0 : K), (0 : K), β) ∈ coordSet S) :
    (β, (0 : K), (0 : K), (0 : K)) ∈ coordSet S := by
  obtain ⟨c, hc⟩ := hβ
  have e0 : nf ((0 : K), (0 : K), (0 : K), β) = gX rB β := by simp [nf, gX_zero]
  have e1 : nf (β, (0 : K), (0 : K), (0 : K)) = gX rA β := by simp [nf, gX_zero]
  rw [e0] at hc
  refine ⟨c, ?_⟩
  rw [e1, ← conj_weyl_b_c]
  exact (Subgroup.mem_normalizer_iff.1 hn _).1 hc

end Group

end CFSG.Quasithin.H13.NQCat.G2Rad
