module

public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126a

public section

namespace CFSG.Quasithin.H13.F126

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem inv_eq_self (hW : ∀ w : W, w ^ 2 = 1) (w : W) : w⁻¹ = w := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, hW]

omit [Finite W] in
theorem card_sup_eq_mul {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : ↥A × ↥B => (⟨p.1 * p.2,
    Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ he
    have e : a * b = a' * b' := congrArg Subtype.val he
    have hm : a'⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
      have : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [e]
          _ = b' * b⁻¹ := by group
      rw [this]
      exact B.mul_mem hb' (B.inv_mem hb)
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hm
    subst hm
    have hbb : b = b' := mul_left_cancel e
    subst hbb
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

section Doubling

variable {x t : MulAut W}

omit [Finite W] in
theorem apply_of_mem_cm (hW : ∀ w : W, w ^ 2 = 1) {f : MulAut W} (hf2 : f ^ 2 = 1) {w : W}
    (hw : w ∈ cm f) : f w = w := by
  obtain ⟨v, -, rfl⟩ := hw
  have hff : f (f v) = v := by rw [← MulAut.mul_apply, ← pow_two, hf2, MulAut.one_apply]
  rw [cmHom_apply, map_mul, map_inv, hff, inv_eq_self hW (f v), inv_eq_self hW v, mul_comm]

theorem cmHom_surjective (hxfix : ∀ w, x w = w → w = 1) : Function.Surjective (cmHom x) := by
  refine Finite.surjective_of_injective ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  rw [MonoidHom.mem_ker, cmHom_apply, mul_inv_eq_one] at hw
  exact (Subgroup.mem_bot).2 (hxfix w hw)

omit [Finite W] in
theorem cm_invariant {f b : MulAut W} (hbf : b * f = f * b) : ∀ s ∈ cm f, b s ∈ cm f := by
  rintro _ ⟨w, -, rfl⟩
  refine ⟨b w, Subgroup.mem_top _, ?_⟩
  simp only [cmHom_apply, map_mul, map_inv]
  rw [← MulAut.mul_apply, ← hbf, MulAut.mul_apply]

variable (hW : ∀ w : W, w ^ 2 = 1) (hx3 : x ^ 3 = 1) (hxfix : ∀ w, x w = w → w = 1)
  (ht2 : t ^ 2 = 1) (htx : t * x * t⁻¹ = x ^ 2)

include ht2 in
omit [Finite W] in
theorem inv_t : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]

include ht2 htx in
omit [Finite W] in
theorem x_mul_t : x * t = t * x ^ 2 := by
  have h1 : t * x * t = x ^ 2 := by rw [← htx, inv_t ht2]
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  calc x * t = (t * t) * x * t := by rw [htt, one_mul]
    _ = t * (t * x * t) := by simp only [mul_assoc]
    _ = t * x ^ 2 := by rw [h1]

include hx3 ht2 htx in
omit [Finite W] in
theorem tx_sq : (t * x) ^ 2 = 1 := by
  have h1 : t * x * t = x ^ 2 := by rw [← htx, inv_t ht2]
  calc (t * x) ^ 2 = (t * x * t) * x := by rw [pow_two]; simp only [mul_assoc]
    _ = x ^ 3 := by rw [h1, pow_succ x 2]
    _ = 1 := hx3

include hx3 ht2 htx in
omit [Finite W] in
theorem conj_t3 : (t * x ^ 2) * t * (t * x ^ 2)⁻¹ = t * x := by
  have hxt := x_mul_t ht2 htx
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have h1 : t * x ^ 2 * t = x := by
    calc t * x ^ 2 * t = x * t * t := by rw [← hxt]
      _ = x := by rw [mul_assoc, htt, mul_one]
  have h2 : x⁻¹ * t = t * x := by
    calc x⁻¹ * t = x⁻¹ * t * x ^ 3 := by rw [hx3, mul_one]
      _ = x⁻¹ * (t * x ^ 2) * x := by group
      _ = x⁻¹ * (x * t) * x := by rw [hxt]
      _ = t * x := by group
  calc (t * x ^ 2) * t * (t * x ^ 2)⁻¹ = (t * x ^ 2 * t) * (x ^ 2)⁻¹ * t⁻¹ := by group
    _ = x * (x ^ 2)⁻¹ * t := by rw [h1, inv_t ht2]
    _ = x⁻¹ * t := by group
    _ = t * x := h2

include hW hx3 hxfix ht2 htx in
omit [Finite W] in
theorem inf_cm : cm t ⊓ cm (t * x) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hw
  have e1 := apply_of_mem_cm hW ht2 h1
  have e2 := apply_of_mem_cm hW (tx_sq hx3 ht2 htx) h2
  rw [Subgroup.mem_bot]
  refine hxfix w ?_
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  calc x w = (t * (t * x)) w := by rw [← mul_assoc, htt, one_mul]
    _ = w := by rw [MulAut.mul_apply, e2, e1]

include hW hxfix in
theorem sup_cm : cm t ⊔ cm (t * x) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨v, rfl⟩ := cmHom_surjective hxfix w
  have e : cmHom x v = cmHom t (x v) * cmHom (t * x) v := by
    simp only [cmHom_apply, MulAut.mul_apply]
    have ha := hW (t (x v))
    rw [pow_two] at ha
    calc x v * v⁻¹ = (t (x v) * t (x v)) * (x v)⁻¹ * v⁻¹ := by
          rw [ha, one_mul, inv_eq_self hW (x v)]
      _ = t (x v) * (x v)⁻¹ * (t (x v) * v⁻¹) := by
          simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_cm t (x v)))
    (Subgroup.mem_sup_right (mem_cm (t * x) v))

include hx3 ht2 htx in
omit [Finite W] in
theorem map_cm : (cm t).map (t * x ^ 2).toMonoidHom = cm (t * x) := by
  have := cmOn_conj t (t * x ^ 2) ⊤
  rw [map_top_mulAut, conj_t3 hx3 ht2 htx] at this
  exact this.symm

include hW hx3 hxfix ht2 htx in
theorem eq_one_of_fix {f : MulAut W} (hfx : f * x = x * f) (hft : f * t = t * f)
    (h : ∀ s ∈ cm t, f s = s) : f = 1 := by
  have hf3 : f * (t * x ^ 2) = (t * x ^ 2) * f := by
    rw [← mul_assoc, hft, mul_assoc, pow_two, ← mul_assoc f x x, hfx, mul_assoc x f x, hfx]
    group
  have hfix2 : ∀ s ∈ cm (t * x), f s = s := by
    rw [← map_cm hx3 ht2 htx]
    rintro _ ⟨u, hu, rfl⟩
    show f ((t * x ^ 2) u) = (t * x ^ 2) u
    rw [← MulAut.mul_apply, hf3, MulAut.mul_apply, h u hu]
  have hle : cm t ⊔ cm (t * x) ≤ fx f :=
    sup_le (fun s hs => mem_fx.2 (h s hs)) (fun s hs => mem_fx.2 (hfix2 s hs))
  rw [sup_cm hW hxfix, top_le_iff] at hle
  ext w
  exact mem_fx.1 (hle ▸ Subgroup.mem_top w)

include hW hx3 hxfix ht2 htx in
theorem card_cm_eq_sq {b : MulAut W} (hbx : b * x = x * b) (hbt : b * t = t * b) :
    Nat.card (cm b) = Nat.card (cmOn b (cm t)) ^ 2 := by
  have hbtx : b * (t * x) = (t * x) * b := by
    rw [← mul_assoc, hbt, mul_assoc, hbx, mul_assoc]
  have hsup : cm b = cmOn b (cm t) ⊔ cmOn b (cm (t * x)) := by
    rw [cm, ← sup_cm hW hxfix (t := t), cmOn, cmOn, cmOn, Subgroup.map_sup]
  have hinf : cmOn b (cm t) ⊓ cmOn b (cm (t * x)) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf (cmOn_le (cm_invariant hbt)) (cmOn_le (cm_invariant hbtx))).trans
      (inf_cm hW hx3 hxfix ht2 htx).le)
  have hb3 : (t * x ^ 2) * b * (t * x ^ 2)⁻¹ = b := by
    have hc : b * (t * x ^ 2) = (t * x ^ 2) * b := by
      rw [← mul_assoc, hbt, mul_assoc, pow_two, ← mul_assoc b x x, hbx, mul_assoc x b x, hbx]
      group
    rw [← hc]
    group
  have h2 : Nat.card (cmOn b (cm (t * x))) = Nat.card (cmOn b (cm t)) := by
    have := card_cmOn_conj b (t * x ^ 2) (cm t)
    rwa [hb3, map_cm hx3 ht2 htx] at this
  rw [hsup, card_sup_eq_mul hinf, h2, pow_two]

include hW hx3 hxfix ht2 htx in
theorem sixteen_le_card_cm_of_a5 (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W)
    (hρ : Function.Injective ρ) (hρx : ∀ a, ρ a * x = x * ρ a) (hρt : ∀ a, ρ a * t = t * ρ a)
    {b : ↥(alternatingGroup (Fin 5))} (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    16 ≤ Nat.card (cm (ρ b)) := by
  have h4 := four_le_card_cmOn_of_a5 hW ρ (S := cm t) (fun a => cm_invariant (hρt a))
    (fun a ha => hρ (by rw [map_one]; exact eq_one_of_fix hW hx3 hxfix ht2 htx (hρx a) (hρt a) ha))
    hb2 hb1
  rw [card_cm_eq_sq hW hx3 hxfix ht2 htx (hρx b) (hρt b)]
  calc 16 = 4 ^ 2 := by norm_num
    _ ≤ Nat.card (cmOn (ρ b) (cm t)) ^ 2 := Nat.pow_le_pow_left h4 2

end Doubling

end CFSG.Quasithin.H13.F126
