module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126F S126N S126L20

namespace S126L28

theorem pol_chk : ∀ z₁ z₂ : Fin 6 → ZMod 2,
    ((Finset.univ.filter fun i => emb z₁ i ≠ 0).card = 0 ∨
      (Finset.univ.filter fun i => emb z₁ i ≠ 0).card = 4) →
    ((Finset.univ.filter fun i => emb z₂ i ≠ 0).card = 0 ∨
      (Finset.univ.filter fun i => emb z₂ i ≠ 0).card = 4) →
    (((Finset.univ.filter fun i => (emb z₁ + emb z₂) i ≠ 0).card = 0 ∨
      (Finset.univ.filter fun i => (emb z₁ + emb z₂) i ≠ 0).card = 4) ↔
      ∑ i, emb z₁ i * emb z₂ i = 0) := by
  decide +kernel

theorem nondeg_chk : ∀ z : Fin 6 → ZMod 2,
    (∀ z' : Fin 6 → ZMod 2, ∑ i, emb z' i * emb z i = 0) → z = 0 := by
  decide +kernel

theorem emb_zero_eq : emb 0 = 0 := by
  decide

@[expose] noncomputable def ofZ (z : Fin 6 → ZMod 2) : D8 :=
  QuotientGroup.mk ⟨Multiplicative.ofAdd (emb z), (mem_coreMod).2 (sum_emb z)⟩

theorem toAdd_iota_ofZ (z : Fin 6 → ZMod 2) : Multiplicative.toAdd (iota (ofZ z)) = emb z := by
  funext i
  change Multiplicative.toAdd (nrm (Multiplicative.ofAdd (emb z))) i = emb z i
  rw [nrm_apply, toAdd_ofAdd, emb_zero, add_zero]

@[expose] noncomputable def wD (y : D8) : ℕ :=
  (Finset.univ.filter fun i => Multiplicative.toAdd (iota y) i ≠ 0).card

@[expose] noncomputable def bD (y y' : D8) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd (iota y) i * Multiplicative.toAdd (iota y') i

theorem bD_mul_left (y y' w : D8) : bD (y * y') w = bD y w + bD y' w := by
  unfold bD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toAdd_iota_mul, Pi.add_apply, add_mul]

theorem bD_comm (y y' : D8) : bD y y' = bD y' y :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem bD_mul_right (y w w' : D8) : bD y (w * w') = bD y w + bD y w' := by
  rw [bD_comm, bD_mul_left, bD_comm w, bD_comm w']

theorem bD_one_left (w : D8) : bD 1 w = 0 := by
  unfold bD
  simp

theorem hasWt4_iff (y : D8) : HasWt 4 y ↔ wD y = 4 := by
  refine ⟨wt_iota_of_wt4, fun h => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  have hmem : nrm (m : PermMod 8) ∈ coreMod 8 := by
    rcases nrm_eq m with e | e <;> rw [e]
    · exact m.2
    · exact (coreMod 8).mul_mem m.2 allOnes_mem
  exact ⟨⟨_, hmem⟩, (mk_eq_iff _ m).2 (nrm_eq m), h⟩

theorem eq_one_of_wD {y : D8} (h : wD y = 0) : y = 1 := by
  apply iota_inj
  rw [map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact eq_zero_of_wt0 _ h

theorem wD_one : wD 1 = 0 := by
  unfold wD
  simp

theorem sing_iff (y : D8) : (y = 1 ∨ HasWt 4 y) ↔ (wD y = 0 ∨ wD y = 4) := by
  rw [hasWt4_iff]
  constructor
  · rintro (rfl | h)
    · exact Or.inl wD_one
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (eq_one_of_wD h)
    · exact Or.inr h

theorem sing_mul_iff {y y' : D8} (hy : y = 1 ∨ HasWt 4 y) (hy' : y' = 1 ∨ HasWt 4 y') :
    (y * y' = 1 ∨ HasWt 4 (y * y')) ↔ bD y y' = 0 := by
  rw [sing_iff] at hy hy' ⊢
  have h := pol_chk (cmp (Multiplicative.toAdd (iota y))) (cmp (Multiplicative.toAdd (iota y')))
  rw [emb_iota, emb_iota] at h
  unfold wD at hy hy' ⊢
  rw [toAdd_iota_mul]
  exact h hy hy'

theorem eq_one_of_bD {y : D8} (h : ∀ x : D8, bD x y = 0) : y = 1 := by
  have hz : cmp (Multiplicative.toAdd (iota y)) = 0 := nondeg_chk _ fun z' => by
    have := h (ofZ z')
    unfold bD at this
    rwa [toAdd_iota_ofZ, ← emb_iota y] at this
  apply iota_inj
  rw [map_one]
  apply Multiplicative.toAdd.injective
  rw [← emb_iota y, hz, emb_zero_eq, toAdd_one]

theorem exists_bD_eq_one {y : D8} (hy : y ≠ 1) : ∃ x, bD x y = 1 := by
  by_contra h
  push Not at h
  exact hy (eq_one_of_bD fun x => by
    have := h x
    revert this
    generalize bD x y = a
    revert a
    decide)

@[expose] noncomputable def phiD (d₁ d₂ : D8) : D8 →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun x := Multiplicative.ofAdd (bD x d₁, bD x d₂)
  map_one' := by
    rw [bD_one_left, bD_one_left]
    rfl
  map_mul' x y := by
    rw [bD_mul_left, bD_mul_left]
    rfl

theorem span_chk : ∀ a b c : ZMod 2, ∀ p : ZMod 2 × ZMod 2, ∃ i j k : Bool,
    p = (if i then ((1 : ZMod 2), a) else 0) + (if j then (b, (1 : ZMod 2)) else 0) +
      (if k then (c, c + 1) else 0) := by
  decide

theorem toAdd_phiD_ite (d₁ d₂ x : D8) (q : ZMod 2 × ZMod 2) (b : Bool)
    (hq : Multiplicative.toAdd (phiD d₁ d₂ x) = q) :
    Multiplicative.toAdd (phiD d₁ d₂ (if b then x else 1)) = if b then q else 0 := by
  cases b
  · simp
  · simpa using hq

theorem phiD_surj {d₁ d₂ : D8} (h₁ : d₁ ≠ 1) (h₂ : d₂ ≠ 1) (h₁₂ : d₁ ≠ d₂) :
    Function.Surjective (phiD d₁ d₂) := by
  obtain ⟨x₁, hx₁⟩ := exists_bD_eq_one h₁
  obtain ⟨x₂, hx₂⟩ := exists_bD_eq_one h₂
  have h12 : d₁ * d₂ ≠ 1 := fun h => h₁₂ (by
    calc d₁ = d₁ * (d₂ * d₂) := by rw [mul_self_eq_one, mul_one]
      _ = d₁ * d₂ * d₂ := (mul_assoc _ _ _).symm
      _ = d₂ := by rw [h, one_mul])
  obtain ⟨x₃, hx₃⟩ := exists_bD_eq_one h12
  rw [bD_mul_right] at hx₃
  have hc : bD x₃ d₂ = bD x₃ d₁ + 1 := by
    revert hx₃
    generalize bD x₃ d₁ = a
    generalize bD x₃ d₂ = b
    revert a b
    decide
  intro p
  obtain ⟨i, j, k, hp⟩ := span_chk (bD x₁ d₂) (bD x₂ d₁) (bD x₃ d₁) (Multiplicative.toAdd p)
  refine ⟨(if i then x₁ else 1) * (if j then x₂ else 1) * (if k then x₃ else 1), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hp, (phiD d₁ d₂).map_mul, (phiD d₁ d₂).map_mul, toAdd_mul, toAdd_mul,
    toAdd_phiD_ite d₁ d₂ x₁ (1, bD x₁ d₂) i (by
      show (bD x₁ d₁, bD x₁ d₂) = _
      rw [hx₁]),
    toAdd_phiD_ite d₁ d₂ x₂ (bD x₂ d₁, 1) j (by
      show (bD x₂ d₁, bD x₂ d₂) = _
      rw [hx₂]),
    toAdd_phiD_ite d₁ d₂ x₃ (bD x₃ d₁, bD x₃ d₁ + 1) k (by
      show (bD x₃ d₁, bD x₃ d₂) = _
      rw [hc])]

theorem card_ker_phiD {d₁ d₂ : D8} (h₁ : d₁ ≠ 1) (h₂ : d₂ ≠ 1) (h₁₂ : d₁ ≠ d₂) :
    Nat.card (phiD d₁ d₂).ker = 16 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (phiD d₁ d₂).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (phiD_surj h₁ h₂ h₁₂)).toEquiv, card_D8_eq] at h1
  have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [h4] at h1
  omega

@[expose] def IsTS (W : Subgroup D8) : Prop := ∀ y ∈ W, y ≠ 1 → HasWt 4 y

theorem IsTS.sing {W : Subgroup D8} (h : IsTS W) {y : D8} (hy : y ∈ W) :
    y = 1 ∨ HasWt 4 y := by
  by_cases h1 : y = 1
  · exact Or.inl h1
  · exact Or.inr (h y hy h1)

theorem IsTS.bD_eq_zero {W : Subgroup D8} (h : IsTS W) {x y : D8} (hx : x ∈ W) (hy : y ∈ W) :
    bD x y = 0 :=
  (sing_mul_iff (h.sing hx) (h.sing hy)).1 (h.sing (W.mul_mem hx hy))

theorem card_inf_eq_four {D W W' : Subgroup D8} (hD : Nat.card D = 4) (h : D ≤ W)
    (h' : D ≤ W') (hc : Nat.card W = 8) (hne : ¬ W ≤ W') : Nat.card ↥(W ⊓ W') = 4 := by
  have h4 := Subgroup.card_dvd_of_le (le_inf h h')
  have h8 := Subgroup.card_dvd_of_le (inf_le_left : W ⊓ W' ≤ W)
  rw [hD] at h4
  rw [hc] at h8
  have hne8 : Nat.card ↥(W ⊓ W') ≠ 8 := fun e => by
    have h1 := Subgroup.eq_of_le_of_card_ge (inf_le_left : W ⊓ W' ≤ W) (by rw [hc, e])
    apply hne
    rw [← h1]
    exact inf_le_right
  generalize Nat.card ↥(W ⊓ W') = n at h4 h8 hne8 ⊢
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  interval_cases n <;> omega

theorem inv_mul_mem_of_index_two {W W' : Subgroup D8} (hc : Nat.card W = 8)
    (hi : Nat.card ↥(W ⊓ W') = 4) {a a' : D8} (ha : a ∈ W) (ha2 : a ∉ W') (ha' : a' ∈ W)
    (ha'2 : a' ∉ W') : a⁻¹ * a' ∈ W' := by
  have hidx : (W'.subgroupOf W).index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := W') (K := W)
    rw [inf_comm, hi, hc] at h
    change W'.relIndex W = 2
    omega
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, W.inv_mem ha⟩) (b := ⟨a', ha'⟩)
  simp only [Subgroup.mem_subgroupOf] at key
  exact key.2 (iff_of_false (fun h => ha2 (by simpa using W'.inv_mem h)) ha'2)

theorem not_three_ts {D W₁ W₂ W₃ : Subgroup D8} (hD : Nat.card D = 4)
    (h₁ : D ≤ W₁) (h₂ : D ≤ W₂) (h₃ : D ≤ W₃)
    (c₁ : Nat.card W₁ = 8) (c₂ : Nat.card W₂ = 8) (c₃ : Nat.card W₃ = 8)
    (t₁ : IsTS W₁) (t₂ : IsTS W₂) (t₃ : IsTS W₃)
    (n₁₂ : W₁ ≠ W₂) (n₁₃ : W₁ ≠ W₃) (n₂₃ : W₂ ≠ W₃) : False := by
  have hnle : ∀ {W W' : Subgroup D8}, Nat.card W = 8 → Nat.card W' = 8 → W ≠ W' → ¬ W ≤ W' :=
    fun hc hc' hne hle => hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc']))
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD
    omega
  obtain ⟨d₁, hd₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
  obtain ⟨d₂, hd₂, hd₂₁⟩ : ∃ d₂ : ↥D, d₂ ≠ 1 ∧ d₂ ≠ d₁ := by
    by_contra hcon
    push Not at hcon
    have := card_le_two_of_forall (K := ↥D) fun a b ha hb => (hcon a ha).trans (hcon b hb).symm
    omega
  have e₁ : (d₁ : D8) ≠ 1 := fun h => hd₁ (Subtype.ext h)
  have e₂ : (d₂ : D8) ≠ 1 := fun h => hd₂ (Subtype.ext h)
  have e₁₂ : (d₁ : D8) ≠ d₂ := fun h => hd₂₁ (Subtype.ext h).symm
  have hK := card_ker_phiD e₁ e₂ e₁₂
  have hWK : ∀ W : Subgroup D8, D ≤ W → IsTS W → W ≤ (phiD d₁ d₂).ker := by
    intro W hDW hW x hx
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (bD x d₁, bD x d₂) = 1
    rw [hW.bD_eq_zero hx (hDW d₁.2), hW.bD_eq_zero hx (hDW d₂.2)]
    rfl
  have hY : W₁ ⊔ W₂ = (phiD d₁ d₂).ker := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (hWK _ h₁ t₁) (hWK _ h₂ t₂)) ?_
    rw [hK]
    have h8 := Subgroup.card_dvd_of_le (le_sup_left : W₁ ≤ W₁ ⊔ W₂)
    rw [c₁] at h8
    have hne : Nat.card ↥(W₁ ⊔ W₂) ≠ 8 := fun e => by
      have h1 := Subgroup.eq_of_le_of_card_ge (le_sup_left : W₁ ≤ W₁ ⊔ W₂) (by rw [e, c₁])
      apply hnle c₂ c₁ (Ne.symm n₁₂)
      rw [h1]
      exact le_sup_right
    have hpos : 0 < Nat.card ↥(W₁ ⊔ W₂) := Nat.card_pos
    generalize Nat.card ↥(W₁ ⊔ W₂) = n at h8 hne hpos ⊢
    omega
  obtain ⟨w₃, hw₃, hw₃1, hw₃2⟩ : ∃ w ∈ W₃, w ∉ W₁ ∧ w ∉ W₂ := by
    obtain ⟨x, hx3, hx1⟩ := Set.not_subset.1 (hnle c₃ c₁ (Ne.symm n₁₃))
    obtain ⟨y, hy3, hy2⟩ := Set.not_subset.1 (hnle c₃ c₂ (Ne.symm n₂₃))
    by_cases hx2 : x ∈ W₂
    · by_cases hy1 : y ∈ W₁
      · refine ⟨x * y, W₃.mul_mem hx3 hy3, fun h => hx1 ?_, fun h => hy2 ?_⟩
        · have := W₁.mul_mem h (W₁.inv_mem hy1)
          rwa [mul_inv_cancel_right] at this
        · have := W₂.mul_mem (W₂.inv_mem hx2) h
          rwa [inv_mul_cancel_left] at this
      · exact ⟨y, hy3, hy1, hy2⟩
    · exact ⟨x, hx3, hx1, hx2⟩
  have hw₃Y : w₃ ∈ W₁ ⊔ W₂ := by
    rw [hY]
    exact hWK _ h₃ t₃ hw₃
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hw₃Y
  subst hab
  have ha2 : a ∉ W₂ := fun h => hw₃2 (W₂.mul_mem h hb)
  have hb1 : b ∉ W₁ := fun h => hw₃1 (W₁.mul_mem ha h)
  have hbab : bD a b = 0 := (sing_mul_iff (t₁.sing ha) (t₂.sing hb)).1 (t₃.sing hw₃)
  have i₁ := card_inf_eq_four hD h₁ h₂ c₁ (hnle c₁ c₂ n₁₂)
  have i₂ := card_inf_eq_four hD h₂ h₁ c₂ (hnle c₂ c₁ (Ne.symm n₁₂))
  have hZ : IsTS (W₁ ⊔ W₂) := by
    intro x hx hx1
    obtain ⟨a', ha', b', hb', rfl⟩ := Subgroup.mem_sup.1 hx
    have hab' : bD a' b' = 0 := by
      by_cases ha'2 : a' ∈ W₂
      · exact t₂.bD_eq_zero ha'2 hb'
      by_cases hb'1 : b' ∈ W₁
      · exact t₁.bD_eq_zero ha' hb'1
      have f₁ : a⁻¹ * a' ∈ W₂ := inv_mul_mem_of_index_two c₁ i₁ ha ha2 ha' ha'2
      have f₂ : b⁻¹ * b' ∈ W₁ := inv_mul_mem_of_index_two c₂ i₂ hb hb1 hb' hb'1
      have f₁' : a⁻¹ * a' ∈ W₁ := W₁.mul_mem (W₁.inv_mem ha) ha'
      rw [show a' = a * (a⁻¹ * a') by group, show b' = b * (b⁻¹ * b') by group,
        bD_mul_left a, bD_mul_right a b, bD_mul_right (a⁻¹ * a') b, hbab, t₁.bD_eq_zero ha f₂,
        t₂.bD_eq_zero f₁ hb, t₁.bD_eq_zero f₁' f₂]
      simp
    exact ((sing_mul_iff (t₁.sing ha') (t₂.sing hb')).2 hab').resolve_left hx1
  have h16 := card_le_eight hZ
  rw [hY, hK] at h16
  omega

end S126L28

end CFSG.Quasithin.H13
