module

public import CFSG.Quasithin.H13.GoldschmidtU43Swap

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def S (z : G) : Set G := {t | t ∈ Uz z ∧ t * t = 1 ∧ t ≠ 1 ∧ t ≠ z}

theorem conj_mem_S {z x t : G} (hx : x ∈ Hz z) (ht : t ∈ S z) : x * t * x⁻¹ ∈ S z := by
  obtain ⟨htU, ht2, ht1, htz⟩ := ht
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hx) t).mp htU, ?_, ?_, ?_⟩
  · calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  · intro h1
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply htz
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = x⁻¹ * z * x := by rw [h1]
      _ = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group

instance (z : G) : SMul ↥(Hz z) ↥(S z) :=
  ⟨fun x t => ⟨(x : G) * t * (x : G)⁻¹, conj_mem_S x.2 t.2⟩⟩

theorem smul_S_def {z : G} (x : ↥(Hz z)) (t : ↥(S z)) :
    ((x • t : ↥(S z)) : G) = (x : G) * t * (x : G)⁻¹ := rfl

instance (z : G) : MulAction ↥(Hz z) ↥(S z) where
  one_smul t := Subtype.ext (by rw [smul_S_def]; simp)
  mul_smul x y t := Subtype.ext (by
    rw [smul_S_def, smul_S_def, smul_S_def]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem isPretransitive_S [Finite G] : MulAction.IsPretransitive ↥(Hz z) ↥(S z) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx, hxab⟩ := h.exists_conj a.2.1 a.2.2.2.1 a.2.2.2.2 a.2.2.1 b.2.1 b.2.2.2.1
    b.2.2.2.2 b.2.2.1
  exact ⟨⟨x, hx⟩, Subtype.ext hxab⟩

theorem mul_z_mem_S {t : G} (ht : t ∈ S z) : z * t ∈ S z := by
  obtain ⟨htU, ht2, ht1, htz⟩ := ht
  have hzt : z * t = t * z := h.z_comm htU
  refine ⟨mul_mem h.z_mem htU, ?_, ?_, ?_⟩
  · calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [h.sq_z, ht2, one_mul]
  · intro h1
    apply htz
    calc t = z * (z * t) := by rw [← mul_assoc, h.sq_z, one_mul]
      _ = z := by rw [h1, mul_one]
  · intro h1
    apply ht1
    calc t = z * (z * t) := by rw [← mul_assoc, h.sq_z, one_mul]
      _ = 1 := by rw [h1, h.sq_z]

theorem card_S [Finite G] : Nat.card ↥(S z) = 18 := by
  classical
  let sec : V4 → ↥(Uz z) := fun v => Classical.choose (h.θ_surj (Multiplicative.ofAdd v))
  have hsec : ∀ v, h.θ (sec v) = Multiplicative.ofAdd v := fun v =>
    Classical.choose_spec (h.θ_surj (Multiplicative.ofAdd v))
  have hsecS : ∀ v : V4, q v = 0 → v ≠ 0 → ((sec v : ↥(Uz z)) : G) ∈ S z := by
    intro v hv hv0
    refine ⟨(sec v).2, ?_, ?_, ?_⟩
    · rcases h.sq_cases (sec v) with ⟨-, h1⟩ | ⟨h1, -⟩
      · rw [← pow_two]; exact h1
      · rw [hsec, toAdd_ofAdd, hv] at h1; exact absurd h1 (by decide)
    · intro h1
      have := (h.θ_eq_one_iff (sec v)).2 (Or.inl h1)
      rw [hsec] at this
      exact hv0 (Multiplicative.ofAdd.injective this)
    · intro h1
      have := (h.θ_eq_one_iff (sec v)).2 (Or.inr h1)
      rw [hsec] at this
      exact hv0 (Multiplicative.ofAdd.injective this)
  have hθz : h.θ ⟨z, h.z_mem⟩ = 1 := (h.θ_eq_one_iff _).2 (Or.inr rfl)
  have hzs : ∀ v : V4, (z * ((sec v : ↥(Uz z)) : G) = (sec v : G)) → False := by
    intro v h1
    apply h.z_ne_one
    calc z = (z * (sec v : G)) * (sec v : G)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  let vt : ↥(S z) → V4 := fun t => Multiplicative.toAdd (h.θ ⟨t, t.2.1⟩)
  have hvt : ∀ t : ↥(S z), q (vt t) = 0 ∧ vt t ≠ 0 := by
    intro t
    refine ⟨h.q_θ_eq_zero t.2.1 t.2.2.1, fun h0 => ?_⟩
    have := h.θ_ne_one t.2.1 t.2.2.2.1 t.2.2.2.2
    exact this (Multiplicative.toAdd.injective (by simpa [vt] using h0))
  have hvt_eq : ∀ (t : ↥(S z)) (v : V4),
      ((t : G) = (sec v : G) ∨ (t : G) = z * (sec v : G)) → vt t = v := by
    intro t v ht
    show Multiplicative.toAdd (h.θ ⟨t, t.2.1⟩) = v
    have : h.θ ⟨t, t.2.1⟩ = Multiplicative.ofAdd v := by
      rcases ht with h1 | h1
      · have : (⟨t, t.2.1⟩ : ↥(Uz z)) = sec v := Subtype.ext h1
        rw [this, hsec]
      · have : (⟨t, t.2.1⟩ : ↥(Uz z)) = ⟨z, h.z_mem⟩ * sec v := Subtype.ext h1
        rw [this, map_mul, hθz, one_mul, hsec]
    rw [this, toAdd_ofAdd]
  let e : ↥(S z) ≃ {v : V4 // q v = 0 ∧ v ≠ 0} × Bool :=
    { toFun := fun t => (⟨vt t, hvt t⟩, decide ((t : G) = z * (sec (vt t) : G)))
      invFun := fun p => ⟨cond p.2 (z * (sec p.1.1 : G)) (sec p.1.1 : G), by
          cases hb : p.2
          · exact hsecS p.1.1 p.1.2.1 p.1.2.2
          · exact h.mul_z_mem_S (hsecS p.1.1 p.1.2.1 p.1.2.2)⟩
      left_inv := fun t => by
        apply Subtype.ext
        show cond (decide ((t : G) = z * (sec (vt t) : G))) (z * (sec (vt t) : G))
          (sec (vt t) : G) = t
        have hθt : h.θ ⟨t, t.2.1⟩ = h.θ (sec (vt t)) := by
          rw [hsec]
          exact (ofAdd_toAdd _).symm
        rcases h.eq_of_θ_eq t.2.1 (sec (vt t)).2 hθt with h1 | h1
        · by_cases hb : (t : G) = z * (sec (vt t) : G)
          · exact absurd (hb.symm.trans h1) (hzs (vt t))
          · rw [decide_eq_false hb]
            exact h1.symm
        · rw [decide_eq_true h1]
          exact h1.symm
      right_inv := fun p => by
        obtain ⟨⟨v, hv⟩, b⟩ := p
        cases b
        · have hvv : vt ⟨(sec v : G), hsecS v hv.1 hv.2⟩ = v := hvt_eq _ v (Or.inl rfl)
          refine Prod.ext (Subtype.ext hvv) ?_
          show decide ((sec v : G) = z * (sec (vt ⟨(sec v : G), hsecS v hv.1 hv.2⟩) : G)) = false
          rw [hvv]
          exact decide_eq_false (fun h1 => hzs v h1.symm)
        · have hvv : vt ⟨z * (sec v : G), h.mul_z_mem_S (hsecS v hv.1 hv.2)⟩ = v :=
            hvt_eq _ v (Or.inr rfl)
          refine Prod.ext (Subtype.ext hvv) ?_
          show decide (z * (sec v : G) = z *
            (sec (vt ⟨z * (sec v : G), h.mul_z_mem_S (hsecS v hv.1 hv.2)⟩) : G)) = true
          rw [hvv]
          exact decide_eq_true rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_sing]
  simp

theorem card_centralizer_S [Finite G] {t : G} (ht : t ∈ S z) :
    Nat.card ↥(Hz z ⊓ Subgroup.centralizer ({t} : Set G)) = 64 := by
  have := h.isPretransitive_S
  let t' : ↥(S z) := ⟨t, ht⟩
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(Hz z) t')
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, h.card_S,
    h.card_H] at h1
  have h2 : Nat.card ↥(MulAction.stabilizer ↥(Hz z) t') =
      Nat.card ↥(Hz z ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x : ↥(Hz z)), Subgroup.mem_inf.mpr ⟨x.1.2, by
          have hx : ((x : ↥(Hz z)) • t' : ↥(S z)) = t' := x.2
          have e := congrArg Subtype.val hx
          rw [smul_S_def] at e
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc ((x : ↥(Hz z)) : G) * t
              = (((x : ↥(Hz z)) : G) * t * ((x : ↥(Hz z)) : G)⁻¹) * ((x : ↥(Hz z)) : G) := by
                group
            _ = t * ((x : ↥(Hz z)) : G) := by rw [show (((x : ↥(Hz z)) : G) * t *
                  ((x : ↥(Hz z)) : G)⁻¹) = t from e]⟩⟩
        invFun := fun g => ⟨⟨g, (Subgroup.mem_inf.mp g.2).1⟩, by
          have hg := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2
          show (⟨(g : G) * t * (g : G)⁻¹, conj_mem_S (Subgroup.mem_inf.mp g.2).1 ht⟩ : ↥(S z)) = t'
          apply Subtype.ext
          show (g : G) * t * (g : G)⁻¹ = t
          calc (g : G) * t * (g : G)⁻¹ = (t * (g : G)) * (g : G)⁻¹ := by rw [hg]
            _ = t := by group⟩
        left_inv := fun x => rfl
        right_inv := fun g => rfl }
  omega

end Hyp

end CFSG.Quasithin.H13.U43
