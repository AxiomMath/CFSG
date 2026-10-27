module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Subgroup

variable {H : Type*} [Group H]

abbrev R (a b : H) : Subgroup H := Subgroup.closure {a, b}

structure E9Data (a b : H) : Prop where
  a3 : a ^ 3 = 1
  b3 : b ^ 3 = 1
  comm : a * b = b * a
  dist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) → i = k ∧ j = l

structure NormData (a b r₁ r₂ w : H) : Prop extends E9Data a b where
  r₁a : r₁ * a = a ^ 2 * r₁
  r₁b : r₁ * b = b * r₁
  r₂a : r₂ * a = a * r₂
  r₂b : r₂ * b = b ^ 2 * r₂
  wa : w * a = b * w
  wb : w * b = a * w

variable {a b : H}

theorem E9Data.pow_mod (h : E9Data a b) (i : ℕ) : a ^ i = a ^ (i % 3) := by
  conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, h.a3, one_pow, mul_one]

theorem E9Data.pow_mod' (h : E9Data a b) (i : ℕ) : b ^ i = b ^ (i % 3) := by
  conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, h.b3, one_pow, mul_one]

theorem E9Data.mem_R_iff (h : E9Data a b) {x : H} :
    x ∈ R a b ↔ ∃ i j : Fin 3, x = a ^ (i : ℕ) * b ^ (j : ℕ) := by
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := Hering214.exists_pow_mul_pow_of_mem_closure h.a3 h.b3 h.comm hx
    refine ⟨⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only [h.pow_mod i, h.pow_mod' j, Nat.mod_mod]
  · rintro ⟨i, j, rfl⟩
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)

theorem E9Data.mul_eq (h : E9Data a b) (i j k l : ℕ) :
    a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  have hc : Commute a b := h.comm
  calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
    _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [(hc.pow_pow k j).eq]
    _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; group

theorem E9Data.comm_R (h : E9Data a b) {x y : H} (hx : x ∈ R a b) (hy : y ∈ R a b) :
    x * y = y * x := by
  obtain ⟨i, j, rfl⟩ := h.mem_R_iff.mp hx
  obtain ⟨k, l, rfl⟩ := h.mem_R_iff.mp hy
  rw [h.mul_eq, h.mul_eq, add_comm (i : ℕ) k, add_comm (j : ℕ) l]

theorem E9Data.cube_R (h : E9Data a b) {x : H} (hx : x ∈ R a b) : x ^ 3 = 1 := by
  obtain ⟨i, j, rfl⟩ := h.mem_R_iff.mp hx
  have hc : Commute a b := h.comm
  rw [(hc.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ), mul_comm (j : ℕ), pow_mul,
    pow_mul, h.a3, h.b3, one_pow, one_pow, one_mul]

theorem E9Data.card_R (h : E9Data a b) : Nat.card (R a b) = 9 := by
  have hb : Function.Bijective (fun p : Fin 3 × Fin 3 =>
      (⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), h.mem_R_iff.mpr ⟨p.1, p.2, rfl⟩⟩ : R a b)) := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ hp
      have := h.dist i j k l (congrArg Subtype.val hp)
      rw [this.1, this.2]
    · intro x
      obtain ⟨i, j, hx⟩ := h.mem_R_iff.mp x.2
      exact ⟨(i, j), Subtype.ext hx.symm⟩
  rw [← Nat.card_eq_of_bijective _ hb]
  simp

theorem E9Data.a_ne_b (h : E9Data a b) : a ≠ b := by
  intro hab
  have := h.dist 1 0 0 1 (by simpa using hab)
  exact absurd this.1 (by decide)

theorem E9Data.a_ne_a2 (h : E9Data a b) : a ≠ a ^ 2 := by
  intro hab
  have := h.dist 1 0 2 0 (by simpa using hab)
  exact absurd this.1 (by decide)

theorem E9Data.a_ne_b2 (h : E9Data a b) : a ≠ b ^ 2 := by
  intro hab
  have := h.dist 1 0 0 2 (by simpa using hab)
  exact absurd this.1 (by decide)

theorem E9Data.a2_ne_b (h : E9Data a b) : a ^ 2 ≠ b := by
  intro hab
  have := h.dist 2 0 0 1 (by simpa using hab)
  exact absurd this.1 (by decide)

theorem E9Data.a2_ne_b2 (h : E9Data a b) : a ^ 2 ≠ b ^ 2 := by
  intro hab
  have := h.dist 2 0 0 2 (by simpa using hab)
  exact absurd this.1 (by decide)

theorem E9Data.b_ne_b2 (h : E9Data a b) : b ≠ b ^ 2 := by
  intro hab
  have := h.dist 0 1 0 2 (by simpa using hab)
  exact absurd this.2 (by decide)

theorem mem_normalizer_of_forall_conj_mem [Finite H] {K : Subgroup H} {j : H}
    (h : ∀ x ∈ K, j * x * j⁻¹ ∈ K) : j ∈ Subgroup.normalizer (K : Set H) := by
  have hle : K.map (MulAut.conj j).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card (K.map (MulAut.conj j).toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj j).injective
  have heq : K.map (MulAut.conj j).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    have hx' : j * x * j⁻¹ ∈ K.map (MulAut.conj j).toMonoidHom := by rw [heq]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := (MulAut.conj j).injective hyx
    rw [← this]
    exact hy

theorem conj_eq_of {j y z : H} (h : j * y = z * j) : MulAut.conj j y = z := by
  rw [MulAut.conj_apply, h, mul_assoc, mul_inv_cancel, mul_one]

theorem E9Data.a_mem (h : E9Data a b) : a ∈ R a b := subset_closure (by simp)

theorem E9Data.b_mem (h : E9Data a b) : b ∈ R a b := subset_closure (by simp)

theorem E9Data.a2_mem (h : E9Data a b) : a ^ 2 ∈ R a b := pow_mem h.a_mem _

theorem E9Data.b2_mem (h : E9Data a b) : b ^ 2 ∈ R a b := pow_mem h.b_mem _

theorem conj_mem_of_gens {j : H} (ha : MulAut.conj j a ∈ R a b) (hb : MulAut.conj j b ∈ R a b) :
    ∀ x ∈ R a b, MulAut.conj j x ∈ R a b := by
  have hle : (R a b).map (MulAut.conj j).toMonoidHom ≤ R a b := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem conj_R_formula (h : E9Data a b) (j : H) (i k : ℕ) :
    MulAut.conj j (a ^ i * b ^ k) = MulAut.conj j a ^ i * MulAut.conj j b ^ k := by
  simp [map_mul, map_pow]

section Count

variable [Finite H] {r₁ r₂ w : H}

@[expose] def jk (r₁ r₂ w : H) : Fin 8 → H := ![1, r₁, r₂, r₁ * r₂, w, r₁ * w, r₂ * w, r₁ * r₂ * w]

@[expose] def qk (a b : H) : Fin 8 → H × H :=
  ![(a, b), (a ^ 2, b), (a, b ^ 2), (a ^ 2, b ^ 2), (b, a), (b, a ^ 2), (b ^ 2, a),
    (b ^ 2, a ^ 2)]

theorem NormData.conj_pair (D : NormData a b r₁ r₂ w) (k : Fin 8) :
    (MulAut.conj (jk r₁ r₂ w k) a, MulAut.conj (jk r₁ r₂ w k) b) = qk a b k := by
  have h1a := conj_eq_of D.r₁a
  have h1b := conj_eq_of D.r₁b
  have h2a := conj_eq_of D.r₂a
  have h2b := conj_eq_of D.r₂b
  have hwa := conj_eq_of D.wa
  have hwb := conj_eq_of D.wb
  fin_cases k <;>
    simp [jk, qk, map_mul, MulAut.mul_apply, h1a, h1b, h2a, h2b, hwa, hwb, map_pow]

theorem NormData.jk_mem (D : NormData a b r₁ r₂ w) (k : Fin 8) :
    jk r₁ r₂ w k ∈ Subgroup.normalizer (R a b : Set H) := by
  have hp := D.conj_pair k
  have hq : ∀ x ∈ R a b, jk r₁ r₂ w k * x * (jk r₁ r₂ w k)⁻¹ ∈ R a b := by
    have hA : MulAut.conj (jk r₁ r₂ w k) a ∈ R a b ∧ MulAut.conj (jk r₁ r₂ w k) b ∈ R a b := by
      have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      simp only at h1 h2
      rw [h1, h2]
      fin_cases k <;> simp [qk, D.toE9Data.a_mem, D.toE9Data.b_mem, D.toE9Data.a2_mem,
        D.toE9Data.b2_mem]
    intro x hx
    exact conj_mem_of_gens hA.1 hA.2 x hx
  exact mem_normalizer_of_forall_conj_mem hq

theorem pow_two_sq_of_pow_three {x : H} (hx3 : x ^ 3 = 1) : (x ^ 2) ^ 2 = x := by
  rw [← pow_mul]
  conv_rhs => rw [← mul_one x, ← hx3]
  group

theorem bad_pair {a b x : H} {c : H ≃* H} (hx3 : x ^ 3 = 1) (hab : b ≠ a) (hab2 : b ≠ a ^ 2)
    (hu : c a = x ∨ c a = x ^ 2) (hv : c b = x ∨ c b = x ^ 2) : False := by
  have hc2 : c (a ^ 2) = c a ^ 2 := map_pow c a 2
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hab (c.injective (hv.trans hu.symm))
  · exact hab2 (c.injective (by rw [hc2, hu, hv]))
  · exact hab2 (c.injective (by rw [hc2, hu, hv, pow_two_sq_of_pow_three hx3]))
  · exact hab (c.injective (hv.trans hu.symm))

theorem NormData.qk_injective (D : NormData a b r₁ r₂ w) : Function.Injective (qk a b) := by
  have h1 := D.toE9Data.a_ne_b
  have h2 := D.toE9Data.a_ne_a2
  have h3 := D.toE9Data.a_ne_b2
  have h4 := D.toE9Data.a2_ne_b
  have h5 := D.toE9Data.a2_ne_b2
  have h6 := D.toE9Data.b_ne_b2
  intro k l h
  fin_cases k <;> fin_cases l <;> simp [qk, Prod.ext_iff] at h ⊢ <;> grind

@[expose] def InBlocks (a b u : H) : Prop := u = a ∨ u = a ^ 2 ∨ u = b ∨ u = b ^ 2

theorem NormData.pair_mem_range (D : NormData a b r₁ r₂ w) {s : H}
    (hu : InBlocks a b (MulAut.conj s a)) (hv : InBlocks a b (MulAut.conj s b)) :
    (MulAut.conj s a, MulAut.conj s b) ∈ Set.range (qk a b) := by
  have hbA : b ≠ a := D.toE9Data.a_ne_b.symm
  have hbA2 : b ≠ a ^ 2 := D.toE9Data.a2_ne_b.symm
  have hbad_a : ¬ ((MulAut.conj s a = a ∨ MulAut.conj s a = a ^ 2) ∧
      (MulAut.conj s b = a ∨ MulAut.conj s b = a ^ 2)) := fun h =>
    bad_pair (c := MulAut.conj s) D.toE9Data.a3 hbA hbA2 h.1 h.2
  have hbad_b : ¬ ((MulAut.conj s a = b ∨ MulAut.conj s a = b ^ 2) ∧
      (MulAut.conj s b = b ∨ MulAut.conj s b = b ^ 2)) := fun h =>
    bad_pair (c := MulAut.conj s) D.toE9Data.b3 hbA hbA2 h.1 h.2
  unfold InBlocks at hu hv
  rcases hu with hu | hu | hu | hu
  · rcases hv with hv | hv | hv | hv
    · exact absurd ⟨Or.inl hu, Or.inl hv⟩ hbad_a
    · exact absurd ⟨Or.inl hu, Or.inr hv⟩ hbad_a
    · exact ⟨0, by simp [qk, hu, hv]⟩
    · exact ⟨2, by simp [qk, hu, hv]⟩
  · rcases hv with hv | hv | hv | hv
    · exact absurd ⟨Or.inr hu, Or.inl hv⟩ hbad_a
    · exact absurd ⟨Or.inr hu, Or.inr hv⟩ hbad_a
    · exact ⟨1, by simp [qk, hu, hv]⟩
    · exact ⟨3, by simp [qk, hu, hv]⟩
  · rcases hv with hv | hv | hv | hv
    · exact ⟨4, by simp [qk, hu, hv]⟩
    · exact ⟨5, by simp [qk, hu, hv]⟩
    · exact absurd ⟨Or.inl hu, Or.inl hv⟩ hbad_b
    · exact absurd ⟨Or.inl hu, Or.inr hv⟩ hbad_b
  · rcases hv with hv | hv | hv | hv
    · exact ⟨6, by simp [qk, hu, hv]⟩
    · exact ⟨7, by simp [qk, hu, hv]⟩
    · exact absurd ⟨Or.inr hu, Or.inl hv⟩ hbad_b
    · exact absurd ⟨Or.inr hu, Or.inr hv⟩ hbad_b

theorem NormData.ncard_conj (D : NormData a b r₁ r₂ w)
    (hconj : ∀ s ∈ Subgroup.normalizer (R a b : Set H),
      InBlocks a b (MulAut.conj s a) ∧ InBlocks a b (MulAut.conj s b)) :
    {f : R a b → H | ∃ j ∈ Subgroup.normalizer (R a b : Set H),
      ∀ x : R a b, f x = j * x * j⁻¹}.ncard = 8 := by
  set F := {f : R a b → H | ∃ j ∈ Subgroup.normalizer (R a b : Set H),
      ∀ x : R a b, f x = j * x * j⁻¹} with hF
  let Φ : (R a b → H) → H × H := fun f => (f ⟨a, D.toE9Data.a_mem⟩, f ⟨b, D.toE9Data.b_mem⟩)
  have himg : Φ '' F = Set.range (qk a b) := by
    ext ⟨u, v⟩
    constructor
    · rintro ⟨f, ⟨s, hs, hf⟩, hΦ⟩
      have hu : u = MulAut.conj s a := by
        have := congrArg Prod.fst hΦ
        simp only [Φ] at this
        rw [← this, hf]
        rfl
      have hv : v = MulAut.conj s b := by
        have := congrArg Prod.snd hΦ
        simp only [Φ] at this
        rw [← this, hf]
        rfl
      subst hu hv
      exact D.pair_mem_range (hconj s hs).1 (hconj s hs).2
    · rintro ⟨k, hk⟩
      refine ⟨fun x => jk r₁ r₂ w k * x * (jk r₁ r₂ w k)⁻¹, ⟨_, D.jk_mem k, fun x => rfl⟩, ?_⟩
      rw [← hk, ← D.conj_pair k]
      rfl
  have hinj : Set.InjOn Φ F := by
    rintro f ⟨s, hs, hf⟩ f' ⟨s', hs', hf'⟩ hΦ
    have h1 : MulAut.conj s a = MulAut.conj s' a := by
      have := congrArg Prod.fst hΦ
      simp only [Φ, hf, hf'] at this
      exact this
    have h2 : MulAut.conj s b = MulAut.conj s' b := by
      have := congrArg Prod.snd hΦ
      simp only [Φ, hf, hf'] at this
      exact this
    funext ⟨x, hx⟩
    obtain ⟨i, j, rfl⟩ := D.toE9Data.mem_R_iff.mp hx
    rw [hf, hf']
    have := conj_R_formula D.toE9Data s i j
    have := conj_R_formula D.toE9Data s' i j
    show MulAut.conj s _ = MulAut.conj s' _
    simp only [conj_R_formula D.toE9Data, h1, h2]
  rw [← hinj.ncard_image, himg, Set.ncard_range_of_injective D.qk_injective]
  simp

theorem NormData.tau_inv (D : NormData a b r₁ r₂ w) {x : H} (hx : x ∈ R a b) :
    (r₁ * r₂) * x * (r₁ * r₂)⁻¹ = x⁻¹ := by
  obtain ⟨i, j, rfl⟩ := D.toE9Data.mem_R_iff.mp hx
  have h1a := conj_eq_of D.r₁a
  have h1b := conj_eq_of D.r₁b
  have h2a := conj_eq_of D.r₂a
  have h2b := conj_eq_of D.r₂b
  have hca : MulAut.conj (r₁ * r₂) a = a ^ 2 := by
    rw [map_mul, MulAut.mul_apply, h2a, h1a]
  have hcb : MulAut.conj (r₁ * r₂) b = b ^ 2 := by
    rw [map_mul, MulAut.mul_apply, h2b, map_pow, h1b]
  have hc := conj_R_formula D.toE9Data (r₁ * r₂) i j
  rw [hca, hcb] at hc
  have ha2 : a ^ 2 = a⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, D.toE9Data.a3]
  have hb2 : b ^ 2 = b⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, D.toE9Data.b3]
  have hcm : Commute (a ^ (i : ℕ)) (b ^ (j : ℕ)) := Commute.pow_pow D.toE9Data.comm _ _
  show MulAut.conj (r₁ * r₂) _ = _
  rw [hc, ha2, hb2, inv_pow, inv_pow, mul_inv_rev, hcm.inv_inv.eq]
  
theorem NormData.tau_mem (D : NormData a b r₁ r₂ w) :
    r₁ * r₂ ∈ Subgroup.normalizer (R a b : Set H) := by
  simpa [jk] using D.jk_mem 3

theorem NormData.noncomm (D : NormData a b r₁ r₂ w) :
    ∃ x ∈ R a b, r₁ * (w * x * w⁻¹) * r₁⁻¹ ≠ w * (r₁ * x * r₁⁻¹) * w⁻¹ := by
  refine ⟨a, D.toE9Data.a_mem, ?_⟩
  have h1a := conj_eq_of D.r₁a
  have h1b := conj_eq_of D.r₁b
  have hwa := conj_eq_of D.wa
  have h : MulAut.conj r₁ (MulAut.conj w a) ≠ MulAut.conj w (MulAut.conj r₁ a) := by
    rw [hwa, h1b, h1a, map_pow, hwa]
    exact D.toE9Data.b_ne_b2
  exact h

end Count

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
