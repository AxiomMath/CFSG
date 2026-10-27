module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.F126

variable {W : Type*} [CommGroup W]

@[expose] def cmHom (f : MulAut W) : W →* W where
  toFun w := f w * w⁻¹
  map_one' := by simp
  map_mul' v w := by
    show f (v * w) * (v * w)⁻¹ = f v * v⁻¹ * (f w * w⁻¹)
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem cmHom_apply (f : MulAut W) (w : W) : cmHom f w = f w * w⁻¹ := rfl

@[expose] def cmOn (f : MulAut W) (S : Subgroup W) : Subgroup W := S.map (cmHom f)

abbrev cm (f : MulAut W) : Subgroup W := cmOn f ⊤

theorem mem_cmOn (f : MulAut W) {S : Subgroup W} {s : W} (hs : s ∈ S) : f s * s⁻¹ ∈ cmOn f S :=
  ⟨s, hs, rfl⟩

theorem mem_cm (f : MulAut W) (w : W) : f w * w⁻¹ ∈ cm f := mem_cmOn f (Subgroup.mem_top w)

theorem cmOn_le {f : MulAut W} {S : Subgroup W} (hS : ∀ s ∈ S, f s ∈ S) : cmOn f S ≤ S := by
  rintro _ ⟨s, hs, rfl⟩
  exact S.mul_mem (hS s hs) (S.inv_mem hs)

theorem eq_of_cmOn_eq_bot {f : MulAut W} {S : Subgroup W} (h : cmOn f S = ⊥) {s : W}
    (hs : s ∈ S) : f s = s := by
  have : f s * s⁻¹ ∈ cmOn f S := mem_cmOn f hs
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

theorem eq_one_of_cm_eq_bot {f : MulAut W} (h : cm f = ⊥) : f = 1 := by
  ext w
  exact eq_of_cmOn_eq_bot h (Subgroup.mem_top w)

theorem cmOn_conj (f g : MulAut W) (S : Subgroup W) :
    cmOn (g * f * g⁻¹) (S.map g.toMonoidHom) = (cmOn f S).map g.toMonoidHom := by
  ext w
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨f s * s⁻¹, mem_cmOn f hs, ?_⟩
    simp [cmHom_apply]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨g s, ⟨s, hs, rfl⟩, ?_⟩
    simp [cmHom_apply]

theorem card_cmOn_conj (f g : MulAut W) (S : Subgroup W) :
    Nat.card (cmOn (g * f * g⁻¹) (S.map g.toMonoidHom)) = Nat.card (cmOn f S) := by
  rw [cmOn_conj, Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]

theorem map_top_mulAut (g : MulAut W) : (⊤ : Subgroup W).map g.toMonoidHom = ⊤ :=
  Subgroup.map_top_of_surjective _ g.surjective

theorem card_cm_conj (f g : MulAut W) : Nat.card (cm (g * f * g⁻¹)) = Nat.card (cm f) := by
  have := card_cmOn_conj f g ⊤
  rwa [map_top_mulAut] at this

@[expose] def fx (f : MulAut W) : Subgroup W := (cmHom f).ker

theorem mem_fx {f : MulAut W} {w : W} : w ∈ fx f ↔ f w = w := by
  rw [fx, MonoidHom.mem_ker, cmHom_apply, mul_inv_eq_one]

variable [Finite W]

theorem card_sup_le (A B : Subgroup W) : Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun p : ↥A × ↥B => (⟨p.1 * p.2,
    Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

theorem factorial_dvd_24 {k : ℕ} (hk : k ≤ 4) : k.factorial ∣ 24 := by
  interval_cases k <;> decide

theorem pow_apply_eq_of_card_le (hW : ∀ w : W, w ^ 2 = 1) {f g : MulAut W} {S : Subgroup W}
    (hfS : ∀ s ∈ S, f s ∈ S) (hgS : ∀ s ∈ S, g s ∈ S) (hf : Nat.card (cmOn f S) ≤ 2)
    (hg : Nat.card (cmOn g S) ≤ 2) : ∀ s ∈ S, ((f * g) ^ 48) s = s := by
  classical
  set A := cmOn f S ⊔ cmOn g S with hA
  set u := f * g with hu
  have hAS : A ≤ S := sup_le (cmOn_le hfS) (cmOn_le hgS)
  have hcardA : Nat.card A ≤ 4 := (card_sup_le _ _).trans (Nat.mul_le_mul hf hg)
  have hgA : ∀ a ∈ A, g a ∈ A := fun a ha => by
    have : g a = (g a * a⁻¹) * a := by group
    rw [this]
    exact A.mul_mem (Subgroup.mem_sup_right (mem_cmOn g (hAS ha))) ha
  have hfA : ∀ a ∈ A, f a ∈ A := fun a ha => by
    have : f a = (f a * a⁻¹) * a := by group
    rw [this]
    exact A.mul_mem (Subgroup.mem_sup_left (mem_cmOn f (hAS ha))) ha
  have huA : ∀ a ∈ A, u a ∈ A := fun a ha => hfA _ (hgA a ha)
  have huS : ∀ s ∈ S, u s ∈ S := fun s hs => hfS _ (hgS s hs)
  have huW : ∀ s ∈ S, u s * s⁻¹ ∈ A := fun s hs => by
    have : u s * s⁻¹ = (f (g s) * (g s)⁻¹) * (g s * s⁻¹) := by
      rw [hu, MulAut.mul_apply]
      group
    rw [this]
    exact A.mul_mem (Subgroup.mem_sup_left (mem_cmOn f (hgS s hs)))
      (Subgroup.mem_sup_right (mem_cmOn g hs))
  let τ₀ : ↥A → ↥A := fun a => ⟨u a, huA a a.2⟩
  have hτinj : Function.Injective τ₀ := fun a b h =>
    Subtype.ext (u.injective (congrArg Subtype.val h))
  let τ : Equiv.Perm ↥A := Equiv.ofBijective τ₀ hτinj.bijective_of_finite
  have hτpow : ∀ (n : ℕ) (a : ↥A), ((τ ^ n) a : W) = (u ^ n) a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, MulAut.mul_apply, ← ih]
      rfl
  have hτ24 : τ ^ 24 = 1 := by
    have := Fintype.ofFinite ↥A
    refine orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_card).trans ?_)
    rw [Fintype.card_perm]
    exact factorial_dvd_24 (by rw [← Nat.card_eq_fintype_card]; exact hcardA)
  have hvA : ∀ a ∈ A, (u ^ 24) a = a := fun a ha => by
    have h1 := hτpow 24 ⟨a, ha⟩
    rw [hτ24, Equiv.Perm.one_apply] at h1
    simpa using h1.symm
  have hvW : ∀ (n : ℕ), ∀ s ∈ S, (u ^ n) s ∈ S ∧ (u ^ n) s * s⁻¹ ∈ A := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      obtain ⟨h1, h2⟩ := ih s hs
      refine ⟨by rw [pow_succ', MulAut.mul_apply]; exact huS _ h1, ?_⟩
      have : (u ^ (n + 1)) s * s⁻¹ = (u ((u ^ n) s) * ((u ^ n) s)⁻¹) * ((u ^ n) s * s⁻¹) := by
        rw [pow_succ', MulAut.mul_apply]
        group
      rw [this]
      exact A.mul_mem (huW _ h1) h2
  intro s hs
  have hc := (hvW 24 s hs).2
  have h48 : (u ^ 48) s = (u ^ 24) ((u ^ 24) s) := by
    rw [show (48 : ℕ) = 24 + 24 from rfl, pow_add, MulAut.mul_apply]
  have hdec : (u ^ 24) s = ((u ^ 24) s * s⁻¹) * s := by group
  rw [h48, hdec, map_mul, hvA _ hc]
  have hsq := hW ((u ^ 24) s * s⁻¹)
  set X := (u ^ 24) s with hX
  calc X * s⁻¹ * X = (X * s⁻¹) ^ 2 * s := by rw [pow_two]; group
    _ = s := by rw [hsq, one_mul]

theorem a5_exists_conj : ∀ b : ↥(alternatingGroup (Fin 5)), b ^ 2 = 1 → b ≠ 1 →
    ∃ g : ↥(alternatingGroup (Fin 5)), (b * (g * b * g⁻¹)) ^ 5 = 1 ∧ b * (g * b * g⁻¹) ≠ 1 := by
  decide +kernel

theorem card_eq_two_pow (hW : ∀ w : W, w ^ 2 = 1) (S : Subgroup W) :
    ∃ k, Nat.card S = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hW w⟩
  exact (hP.to_subgroup S).exists_card_eq

theorem le_two_of_lt_four (hW : ∀ w : W, w ^ 2 = 1) (S : Subgroup W) (h : Nat.card S < 4) :
    Nat.card S ≤ 2 := by
  obtain ⟨k, hk⟩ := card_eq_two_pow hW S
  rw [hk] at h ⊢
  have : k ≤ 1 := by
    by_contra hk1
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> norm_num

theorem four_le_card_cmOn_of_a5 (hW : ∀ w : W, w ^ 2 = 1)
    (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W) {S : Subgroup W}
    (hρS : ∀ a, ∀ s ∈ S, ρ a s ∈ S) (hρ : ∀ a, (∀ s ∈ S, ρ a s = s) → a = 1)
    {b : ↥(alternatingGroup (Fin 5))} (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    4 ≤ Nat.card (cmOn (ρ b) S) := by
  by_contra hlt
  have hle := le_two_of_lt_four hW (cmOn (ρ b) S) (by omega)
  obtain ⟨g, hg5, hg1⟩ := a5_exists_conj b hb2 hb1
  have hgS : (S.map (ρ g).toMonoidHom) = S := by
    refine le_antisymm ?_ fun s hs => ⟨ρ g⁻¹ s, hρS _ s hs, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hρS g s hs
    · show (ρ g) ((ρ g⁻¹) s) = s
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hle' : Nat.card (cmOn (ρ (g * b * g⁻¹)) S) ≤ 2 := by
    rw [map_mul, map_mul, map_inv]
    have := card_cmOn_conj (ρ b) (ρ g) S
    rw [hgS] at this
    rw [this]
    exact hle
  have h48 := pow_apply_eq_of_card_le hW (hρS b) (hρS _) hle hle'
  rw [← map_mul, ← map_pow] at h48
  have h48' := hρ _ h48
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : orderOf (b * (g * b * g⁻¹)) = 5 := orderOf_eq_prime hg5 hg1
  have := orderOf_dvd_of_pow_eq_one h48'
  rw [h5] at this
  norm_num at this

omit [Finite W] in
theorem card_cm_mul_card_fx (f : MulAut W) :
    Nat.card (cm f) * Nat.card (fx f) = Nat.card W := by
  have e : cm f = (cmHom f).range := by
    rw [cm, cmOn, ← MonoidHom.range_eq_map]
  rw [e, fx, ← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index]

theorem card_cm_ne_two {x f : MulAut W} (hx3 : x ^ 3 = 1) (hxfix : ∀ w, x w = w → w = 1)
    (hcard : 8 ≤ Nat.card W) (hn : f * x * f⁻¹ = x ∨ f * x * f⁻¹ = x ^ 2) :
    Nat.card (cm f) ≠ 2 := by
  intro h2
  rcases hn with hc | hc
  ·
    obtain ⟨c, hc1, hcuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(cm f))).1 h2
    have hfx : x * f = f * x := by
      calc x * f = (f * x * f⁻¹) * f := by rw [hc]
        _ = f * x := by group
    have hxc : ∀ v ∈ cm f, x v ∈ cm f := by
      rintro _ ⟨w, -, rfl⟩
      refine ⟨x w, Subgroup.mem_top _, ?_⟩
      simp only [cmHom_apply, map_mul, map_inv]
      rw [← MulAut.mul_apply, ← hfx, MulAut.mul_apply]
    have hxc' : x (c : W) ∈ cm f := hxc _ c.2
    have hne : (⟨x c, hxc'⟩ : ↥(cm f)) ≠ 1 := fun h => by
      have h' : x (c : W) = 1 := congrArg Subtype.val h
      rw [← map_one x] at h'
      exact hc1 (Subtype.ext (x.injective h'))
    have := hcuniq _ hne
    have hfix : x (c : W) = c := congrArg Subtype.val this
    exact hc1 (Subtype.ext (hxfix _ hfix))
  ·
    set f' := x * f * x⁻¹ with hf'
    have h2' : Nat.card (cm f') = 2 := by rw [hf', card_cm_conj, h2]
    have hx2 : x ^ 2 = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
    have hff : f * f'⁻¹ = x := by
      have e1 : f * f'⁻¹ = (f * x * f⁻¹) * x⁻¹ := by rw [hf']; group
      rw [e1, hc, hx2, ← mul_inv_rev, ← pow_two, hx2, inv_inv]
    have hint : fx f ⊓ fx f' = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hw, hw'⟩ := Subgroup.mem_inf.1 hw
      rw [mem_fx] at hw hw'
      rw [Subgroup.mem_bot]
      refine hxfix w ?_
      rw [← hff, MulAut.mul_apply]
      have : f'⁻¹ w = w := by
        conv_lhs => rw [← hw']
        simp
      rw [this, hw]
    have hidx := Subgroup.index_inf_le (H := fx f) (K := fx f')
    rw [hint, Subgroup.index_bot] at hidx
    have h1 := card_cm_mul_card_fx f
    have h1' := card_cm_mul_card_fx f'
    have hi1 := (fx f).card_mul_index
    have hi2 := (fx f').card_mul_index
    rw [h2] at h1
    rw [h2'] at h1'
    have hpos := (Nat.card_pos : 0 < Nat.card (fx f))
    have hi1' : (fx f).index = 2 := by
      have : Nat.card (fx f) * (fx f).index = Nat.card (fx f) * 2 := by rw [hi1, ← h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hpos' := (Nat.card_pos : 0 < Nat.card (fx f'))
    have hi2' : (fx f').index = 2 := by
      have : Nat.card (fx f') * (fx f').index = Nat.card (fx f') * 2 := by
        rw [hi2, ← h1']; ring
      exact Nat.eq_of_mul_eq_mul_left hpos' this
    rw [hi1', hi2'] at hidx
    omega

end CFSG.Quasithin.H13.F126
