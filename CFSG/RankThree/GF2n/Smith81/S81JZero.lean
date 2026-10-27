module

public import CFSG.RankThree.GF2n.Smith81.S81JRankOne

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem hasEnoughRootsOfUnity_units_exponent [Finite K] :
    HasEnoughRootsOfUnity K (Monoid.exponent Kˣ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨⟨(g : K), ?_⟩, inferInstance⟩
  rw [IsCyclic.exponent_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
  exact IsPrimitiveRoot.orderOf _

theorem const_or_weight [CharP K 2] [Finite K] {D : Type*} (u : Kˣ → V) (r : D → Kˣ)
    (hr : Function.Surjective r) (ρ : D → V →ₗ[K] V)
    (hρ : ∀ d s, ρ d (u s) = u (s * r d)) :
    (∀ s, u s = u 1) ∨
      ∃ (μ : Kˣ →* Kˣ) (w : V), (∃ c, μ c ≠ 1) ∧ w ≠ 0 ∧
        ∀ d, ρ d w = ((μ (r d) : Kˣ) : K) • w := by
  haveI : HasEnoughRootsOfUnity K (Monoid.exponent Kˣ) := hasEnoughRootsOfUnity_units_exponent
  haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
  haveI : Fintype (MulChar K K) := Fintype.ofFinite _
  obtain ⟨W, hW⟩ : ∃ W : MulChar K K → V,
      ∀ χ, W χ = ∑ s : Kˣ, χ ((s⁻¹ : Kˣ) : K) • u s :=
    ⟨fun χ => ∑ s : Kˣ, χ ((s⁻¹ : Kˣ) : K) • u s, fun _ => rfl⟩
  have ha : ∀ (χ : MulChar K K) (d : D), ρ d (W χ) = χ ((r d : Kˣ) : K) • W χ := by
    intro χ d
    have hc : ∀ s : Kˣ, χ ((s⁻¹ : Kˣ) : K) =
        χ ((r d : Kˣ) : K) * χ (((s * r d)⁻¹ : Kˣ) : K) := by
      intro s
      have hs : (s⁻¹ : Kˣ) = r d * (s * r d)⁻¹ := by group
      rw [hs, Units.val_mul, map_mul]
    rw [hW, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (r d)) _ _ (fun s => ?_)
    show ρ d (χ ((s⁻¹ : Kˣ) : K) • u s) =
      χ ((r d : Kˣ) : K) • (χ (((s * r d)⁻¹ : Kˣ) : K) • u (s * r d))
    rw [map_smul, hρ, hc s, smul_smul]
  have hcard : ((Nat.card Kˣ : ℕ) : K) = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have h1 : Nat.card K = Nat.card Kˣ + 1 := Nat.card_eq_card_units_add_one K
    have h2 : ((Nat.card K : ℕ) : K) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero K
    rw [h1, Nat.cast_add, Nat.cast_one] at h2
    have h3 : ((Nat.card Kˣ : ℕ) : K) = -1 := eq_neg_of_add_eq_zero_left h2
    rw [h3, CharTwo.neg_eq]
  have hsum1 : ∑ χ : MulChar K K, χ ((1 : Kˣ) : K) = 1 := by
    rw [Units.val_one]
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity K K]
    exact hcard
  have hcancel : ∀ s : Kˣ, s ≠ 1 → ∑ χ : MulChar K K, χ ((s⁻¹ : Kˣ) : K) = 0 := by
    intro s hs
    have ha1 : ((s⁻¹ : Kˣ) : K) ≠ 1 := fun h => hs (inv_eq_one.mp (Units.ext h))
    obtain ⟨χ₀, hχ₀⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity K K ha1
    have hS : (∑ χ : MulChar K K, χ ((s⁻¹ : Kˣ) : K)) =
        χ₀ ((s⁻¹ : Kˣ) : K) * ∑ χ : MulChar K K, χ ((s⁻¹ : Kˣ) : K) := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft χ₀) (fun χ => (χ₀ * χ) ((s⁻¹ : Kˣ) : K))
        (fun χ => χ ((s⁻¹ : Kˣ) : K)) (fun _ => rfl)).symm.trans
        (Finset.sum_congr rfl fun χ _ => MulChar.mul_apply χ₀ χ _)
    have hmul : (χ₀ ((s⁻¹ : Kˣ) : K) - 1) * ∑ χ : MulChar K K, χ ((s⁻¹ : Kˣ) : K) = 0 := by
      linear_combination -hS
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h) hχ₀
    · exact h
  have hb : ∑ χ : MulChar K K, W χ = u 1 := by
    simp only [hW]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (1 : Kˣ)]
    · simp only [inv_one, hsum1, one_smul]
    · intro s _ hs
      rw [hcancel s hs, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  by_cases hex : ∃ χ : MulChar K K, (∃ c : Kˣ, χ.toUnitHom c ≠ 1) ∧ W χ ≠ 0
  · obtain ⟨χ, ⟨c, hc⟩, hw⟩ := hex
    exact Or.inr ⟨χ.toUnitHom, W χ, ⟨c, hc⟩, hw, fun d => ha χ d⟩
  · left
    have hex' : ∀ χ : MulChar K K, (∃ c : Kˣ, χ.toUnitHom c ≠ 1) → W χ = 0 :=
      fun χ hc => by
        by_contra hw
        exact hex ⟨χ, hc, hw⟩
    have hfix : ∀ d, ρ d (u 1) = u 1 := by
      intro d
      rw [← hb, map_sum]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [ha χ d]
      by_cases hc : ∃ c : Kˣ, χ.toUnitHom c ≠ 1
      · rw [hex' χ hc, smul_zero]
      · have hc' : ∀ c : Kˣ, χ.toUnitHom c = 1 := fun c => by
          by_contra h
          exact hc ⟨c, h⟩
        have h1 : χ ((r d : Kˣ) : K) = 1 := by
          rw [← MulChar.coe_toUnitHom, hc' (r d), Units.val_one]
        rw [h1, one_smul]
    intro s
    obtain ⟨d, rfl⟩ := hr s
    have h2 := hρ d 1
    rw [hfix d, one_mul] at h2
    exact h2.symm

private theorem zB_finite : ∀ a b a' b' : Fin 6, a ≠ b → a' ≠ b' → (a ≠ a' ∨ b ≠ b') →
    ∃ p r : Fin 6, p ≠ r ∧
      ((if a = p then (1 : ℤ) else if a = r then -1 else 0) -
          (if b = p then (1 : ℤ) else if b = r then -1 else 0)) -
        ((if a' = p then (1 : ℤ) else if a' = r then -1 else 0) -
          (if b' = p then (1 : ℤ) else if b' = r then -1 else 0)) ∈
        ({1, -1, 2, -2} : Finset ℤ) := by
  decide

private theorem zB_cOn_eq_zpow (p r i : Fin 6) (c : Kˣ) :
    cOn p r c i = c ^ (if i = p then (1 : ℤ) else if i = r then -1 else 0) := by
  by_cases hip : i = p
  · simp [cOn, hip]
  · by_cases hir : i = r
    · subst hir
      simp [cOn, hip]
    · simp [cOn, hip, hir]

private theorem zB_prod_cOn {p r : Fin 6} (hpr : p ≠ r) (c : Kˣ) :
    ∏ i, cOn p r c i = 1 := by
  have hd_p : cOn p r c p = c := by simp [cOn]
  have hd_r : cOn p r c r = c⁻¹ := by simp [cOn, hpr.symm]
  have hd_other : ∀ b, b ≠ p → b ≠ r → cOn p r c b = 1 := fun b hbp hbr => by
    simp [cOn, hbp, hbr]
  rw [Finset.prod_eq_mul (s := Finset.univ) p r hpr
      (fun x _ hx => hd_other x hx.1 hx.2)
      (fun h => absurd (Finset.mem_univ p) h) (fun h => absurd (Finset.mem_univ r) h),
    hd_p, hd_r, mul_inv_cancel]

private theorem zB_val {μ : Kˣ →* Kˣ} (p r : Fin 6) (c : Kˣ) (i j : Fin 6) :
    μ (cOn p r c i * (cOn p r c j)⁻¹) =
      μ c ^ ((if i = p then (1 : ℤ) else if i = r then -1 else 0) -
        (if j = p then (1 : ℤ) else if j = r then -1 else 0)) := by
  rw [zB_cOn_eq_zpow, zB_cOn_eq_zpow, ← _root_.zpow_sub, map_zpow]

private theorem zB_eq_one_of_zpow [CharP K 2] {x : Kˣ} {m : ℤ}
    (hm : m ∈ ({1, -1, 2, -2} : Finset ℤ)) (h : x ^ m = 1) : x = 1 := by
  have hsq : ∀ y : Kˣ, y * y = 1 → y = 1 := by
    intro y hy
    have hyK : (y : K) * (y : K) = 1 := by
      simpa using congrArg Units.val hy
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : ((y : K) - 1) * ((y : K) - 1) = 0 := by
      linear_combination hyK + (1 - (y : K)) * h2K
    exact Units.ext (sub_eq_zero.mp (mul_self_eq_zero.mp h3))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rw [zpow_one] at h
    exact h
  · rw [_root_.zpow_neg_one, inv_eq_one] at h
    exact h
  · exact hsq x (by rw [← zpow_two]; exact h)
  · exact hsq x (by rw [← zpow_two]; rw [_root_.zpow_neg] at h; exact inv_eq_one.mp h)

theorem pairs_sep [CharP K 2] {μ : Kˣ →* Kˣ} (hμ : ∃ c, μ c ≠ 1) {a b a' b' : Fin 6}
    (hab : a ≠ b) (hab' : a' ≠ b') (h : a ≠ a' ∨ b ≠ b') :
    ∃ d : Fin 6 → Kˣ, ∏ i, d i = 1 ∧ μ (d a * (d b)⁻¹) ≠ μ (d a' * (d b')⁻¹) := by
  obtain ⟨p, r, hpr, hm⟩ := zB_finite a b a' b' hab hab' h
  obtain ⟨c, hc⟩ := hμ
  refine ⟨cOn p r c, zB_prod_cOn hpr c, ?_⟩
  intro heq
  rw [zB_val, zB_val] at heq
  apply hc
  refine zB_eq_one_of_zpow hm ?_
  rw [_root_.zpow_sub, heq, mul_inv_cancel]

theorem pair_ne_one [CharP K 2] {μ : Kˣ →* Kˣ} (hμ : ∃ c, μ c ≠ 1) {a b : Fin 6} (hab : a ≠ b) :
    ∃ d : Fin 6 → Kˣ, ∏ i, d i = 1 ∧ μ (d a * (d b)⁻¹) ≠ 1 := by
  obtain ⟨c, hc⟩ := hμ
  refine ⟨cOn a b c, zB_prod_cOn hab c, ?_⟩
  rw [zB_val]
  intro h
  apply hc
  have h2 : (if a = a then (1 : ℤ) else if a = b then -1 else 0) -
      (if b = a then (1 : ℤ) else if b = b then -1 else 0) = 2 := by
    norm_num [Ne.symm hab]
  rw [h2] at h
  exact zB_eq_one_of_zpow (by decide) h

theorem exists_perm_ab {a b : Fin 6} (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 6), σ 0 = a ∧ σ 3 = b := by
  have hb' : Equiv.swap 0 a b ≠ 0 := by
    intro h
    apply hab
    have h2 := congrArg (Equiv.swap 0 a) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact h2.symm
  refine ⟨Equiv.swap 0 a * Equiv.swap 3 (Equiv.swap 0 a b), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 6) ≠ 3 by decide) hb'.symm,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

structure Setup0 [CharP K 2] (A : SLAct K V) (v₀ : V) : Prop where
  hq : 4 ≤ Nat.card K
  hV : finrank K V = 20
  h0 : finrank K (A.Fix (Wc K I0)) = 1
  hv₀ : v₀ ∈ A.Fix (Wc K I0)
  hv0 : v₀ ≠ 0
  hid : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = v
  hspan : ⨆ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
    (A.Fix (Wc K I0)).map (A.act g.1) = ⊤

namespace SLAct

variable [CharP K 2] (A : SLAct K V)

theorem weights_trivial {v₀ : V} (S : Setup0 A v₀) {I : Finset (Fin 6)} (hI : I.card = 3)
    (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) : ∀ v ∈ A.Fix (Wc K I), A.act (dg d) v = v := by
  have hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0),
      A.act (dg (cOn 0 3 c)) v = (((1 : Kˣ →* Kˣ) c : Kˣ) : K) • v := by
    intro c v hv
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact S.hid c v hv
  intro v hv
  rw [A.weight_I S.h0 hξ hI d hd v hv]
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]

private theorem zC_unip_sq [CharP K 2] {W : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K W) : g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  obtain ⟨-, h1, h2⟩ := mem_UnipGL_iff.1 hg
  have hn : (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ W := h1 v
  have hfix := h2 _ hn
  rw [Matrix.mulVec_sub] at hfix
  have hz : ∀ x : Fin 6 → K, x + x = 0 := fun x => by
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  have h3 : (g : Matrix (Fin 6) (Fin 6) K).mulVec ((g : Matrix (Fin 6) (Fin 6) K).mulVec v) - v =
      0 := by
    have e : (g : Matrix (Fin 6) (Fin 6) K).mulVec ((g : Matrix (Fin 6) (Fin 6) K).mulVec v) - v =
        ((g : Matrix (Fin 6) (Fin 6) K).mulVec ((g : Matrix (Fin 6) (Fin 6) K).mulVec v) -
          (g : Matrix (Fin 6) (Fin 6) K).mulVec v) +
          ((g : Matrix (Fin 6) (Fin 6) K).mulVec v - v) := by
      abel
    rw [e, hfix, hz]
  exact sub_eq_zero.1 h3

theorem fix_I0_of_X_fix {v₀ : V} (S : Setup0 A v₀)
    (h : ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) = A.act (pm K (Equiv.swap 0 3)) v₀) :
    A.act (pm K (Equiv.swap 0 3)) v₀ ∈ A.Fix (Wc K I0) := by
  have hI1card : I1.card = 3 := by decide
  have himg : I0.image (Equiv.swap (0 : Fin 6) 3) = I1 := by decide
  have hv1I1 : A.act (pm K (Equiv.swap 0 3)) v₀ ∈ A.Fix (Wc K I1) := by
    have e := A.vI_eq S.h0 S.hv₀ (Equiv.swap 0 3)
    rw [himg] at e
    rw [e]
    exact A.vI_mem S.h0 S.hv₀ hI1card
  refine A.mem_Fix.2 fun u hu => ?_
  obtain ⟨hu', hstab⟩ := UnipGL_I0_decomp hu
  obtain ⟨u', hu'def⟩ : ∃ u' : GL (Fin 6) K,
      u' = u * transvGL K 0 3 (by decide) ((u : Matrix (Fin 6) (Fin 6) K) 0 3) := ⟨_, rfl⟩
  rw [← hu'def] at hu' hstab
  have hstab' : ∀ w ∈ Wc K I1, (u' : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ Wc K I1 := hstab
  have hdet' : (u' : Matrix (Fin 6) (Fin 6) K).det = 1 := (mem_UnipGL_iff.1 hu').1
  have hinv' : ∀ v ∈ A.Fix (Wc K I1), A.act u' v = v :=
    A.act_invol_fix hdet' (zC_unip_sq hu') hstab' (A.finrank_Fix_Wc S.h0 hI1card)
  obtain ⟨T', hT'def⟩ : ∃ T' : GL (Fin 6) K,
      T' = transvGL K 0 3 (by decide) (-((u : Matrix (Fin 6) (Fin 6) K) 0 3)) := ⟨_, rfl⟩
  have hu_eq : u = u' * T' := by
    rw [hu'def, hT'def, ← tr_inv, mul_inv_cancel_right]
  have hdetT' : (T' : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [hT'def]
    exact det_tr _ _
  have hT'v1 : A.act T' (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.act (pm K (Equiv.swap 0 3)) v₀ := by
    have hX := h (-((u : Matrix (Fin 6) (Fin 6) K) 0 3))
    rw [SLAct.X] at hX
    rw [hT'def]
    exact hX
  rw [hu_eq, A.act_mul u' T' hdet' hdetT', Module.End.mul_apply, hT'v1, hinv' _ hv1I1]

private theorem zE_exists_s (hq : 4 ≤ Nat.card K) : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
  classical
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  by_contra hcon
  have hcon' : ∀ s : K, s ≠ 0 → s = 1 := fun s hs => by
    by_contra h1
    exact hcon ⟨s, hs, h1⟩
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro s _
    by_cases hs : s = 0
    · simp [hs]
    · simp [hcon' s hs]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

private theorem zE_add_one_ne_zero [CharP K 2] {s : K} (hs : s ≠ 1) : s + 1 ≠ 0 := by
  intro h
  apply hs
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h - h2

private theorem zE_X_fix [CharP K 2] (v : V) (hq : 4 ≤ Nat.card K)
    (hc : ∀ t : K, t ≠ 0 → A.X t v = A.X 1 v) : ∀ t : K, A.X t v = v := by
  obtain ⟨s, hs0, hs1⟩ := zE_exists_s hq
  have e1 : A.X (s + 1) v = A.X 1 v := hc _ (zE_add_one_ne_zero hs1)
  have e2 : A.X s v = A.X 1 v := hc s hs0
  have e3 : A.X (s + 1) v = A.X s (A.X 1 v) := by
    rw [A.X_add, Module.End.mul_apply]
  have h1 : A.X 1 v = v :=
    calc A.X 1 v = A.X (s + 1) v := e1.symm
      _ = A.X s (A.X 1 v) := e3
      _ = A.X s (A.X s v) := by rw [e2]
      _ = v := A.X_X_self s v
  intro t
  by_cases ht : t = 0
  · subst ht
    rw [A.X_zero, Module.End.one_apply]
  · rw [hc t ht, h1]

private theorem zE_line_eq [FiniteDimensional K V] {W₁ W₂ : Submodule K V}
    (h₁ : finrank K W₁ = 1) (h₂ : finrank K W₂ = 1) {v : V} (hv : v ≠ 0)
    (hv₁ : v ∈ W₁) (hv₂ : v ∈ W₂) : W₁ = W₂ := by
  have e₁ : Submodule.span K {v} = W₁ :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v W₁).2 hv₁)
      (by rw [finrank_span_singleton hv, h₁])
  have e₂ : Submodule.span K {v} = W₂ :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v W₂).2 hv₂)
      (by rw [finrank_span_singleton hv, h₂])
  exact e₁.symm.trans e₂

private theorem zE_map_eq_of_stable {g : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) {I : Finset (Fin 6)}
    (hI : A.Fix (Wc K I) = A.Fix (Wc K I0))
    (hstab : ∀ w ∈ Wc K I, (g : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ Wc K I) :
    (A.Fix (Wc K I0)).map (A.act g) = A.Fix (Wc K I0) := by
  rw [← hI, A.Fix_map hg (Wc K I), actA_map_eq hstab]

private theorem zE_stab_mul {W : Submodule K V} {g h : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (hh : (h : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hgW : W.map (A.act g) = W) (hhW : W.map (A.act h) = W) :
    W.map (A.act (g * h)) = W := by
  rw [A.act_mul g h hg hh, Module.End.mul_eq_comp, Submodule.map_comp, hhW, hgW]

private theorem zE_stab_one {W : Submodule K V} : W.map (A.act 1) = W := by
  rw [A.act_one, Module.End.one_eq_id, Submodule.map_id]

private theorem zE_stab_inv {W : Submodule K V} {g : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (hgW : W.map (A.act g) = W) :
    W.map (A.act g⁻¹) = W := by
  calc W.map (A.act g⁻¹) = (W.map (A.act g)).map (A.act g⁻¹) := by rw [hgW]
    _ = W.map ((A.act g⁻¹).comp (A.act g)) := (Submodule.map_comp _ _ _).symm
    _ = W.map (A.act (g⁻¹ * g)) := by
        rw [A.act_mul g⁻¹ g (det_inv_eq_one hg) hg, Module.End.mul_eq_comp]
    _ = W := by rw [inv_mul_cancel, A.act_one, Module.End.one_eq_id, Submodule.map_id]

private theorem zE_tr_map [CharP K 2] (hI1 : A.Fix (Wc K I1) = A.Fix (Wc K I0))
    {a b : Fin 6} (hab : a ≠ b) (t : K) :
    (A.Fix (Wc K I0)).map (A.act (transvGL K a b hab t)) = A.Fix (Wc K I0) := by
  by_cases h : b ∈ I0 → a ∈ I0
  · exact zE_map_eq_of_stable A (I := I0) (det_tr hab t) rfl
      (fun w hw => tr_Wc_stable hab t h hw)
  · have hb : b ∈ I0 := by
      by_contra hb
      exact h (fun h' => absurd h' hb)
    have ha : a ∉ I0 := fun ha => h (fun _ => ha)
    obtain ⟨σ, hσI0, hσ0, hσ3⟩ := exists_perm_pair I0 (by decide) hb ha
    have hI : A.Fix (Wc K (I1.image σ)) = A.Fix (Wc K I0) := by
      rw [← A.act_pm_Fix σ I1, hI1, A.act_pm_Fix σ I0, hσI0]
    have hbI : b ∉ I1.image σ := by
      intro hb'
      obtain ⟨k, hk, hkb⟩ := Finset.mem_image.1 hb'
      have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by simpa [I1] using hk
      rcases hk' with rfl | rfl | rfl
      · exact absurd (σ.injective (hkb.trans hσ0.symm)) (by decide)
      · exact absurd (σ.injective (hkb.trans hσ0.symm)) (by decide)
      · exact hab (hσ3.symm.trans hkb)
    exact zE_map_eq_of_stable A (det_tr hab t) hI
      (fun w hw => tr_Wc_stable hab t (fun h' => absurd h' hbI) hw)

theorem caseA_false {v₀ : V} (S : Setup0 A v₀)
    (hconst : ∀ s : Kˣ, A.X (s : K) (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.X 1 (A.act (pm K (Equiv.swap 0 3)) v₀)) : False := by
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by rw [S.hV]; norm_num)
  have hv1ne : A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ ≠ 0 := by
    intro h
    apply S.hv0
    apply A.actA_inj (det_pm (K := K) (Equiv.swap (0 : Fin 6) 3))
    rw [map_zero]
    exact h
  have hv1I1 : A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ ∈ A.Fix (Wc K I1) := by
    have h := A.act_pm_Fix (Equiv.swap (0 : Fin 6) 3) I0
    have himg : I0.image (Equiv.swap (0 : Fin 6) 3) = I1 := by decide
    rw [himg] at h
    rw [← h]
    exact Submodule.mem_map_of_mem S.hv₀
  have hc : ∀ t : K, t ≠ 0 → A.X t (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀) =
      A.X 1 (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀) := fun t ht => by
    have h := hconst (Units.mk0 t ht)
    rwa [Units.val_mk0] at h
  have hv1I0 : A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ ∈ A.Fix (Wc K I0) :=
    A.fix_I0_of_X_fix S (zE_X_fix A _ S.hq hc)
  have hI1 : A.Fix (Wc K I1) = A.Fix (Wc K I0) :=
    zE_line_eq (A.finrank_Fix_Wc (I := I1) S.h0 (by decide)) S.h0 hv1ne hv1I1 hv1I0
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (GL (Fin 6) K), ∀ g : GL (Fin 6) K,
      g ∈ H ↔ ((g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
        (A.Fix (Wc K I0)).map (A.act g) = A.Fix (Wc K I0)) :=
    ⟨{ carrier := {g | (g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
          (A.Fix (Wc K I0)).map (A.act g) = A.Fix (Wc K I0)}
       mul_mem' := fun {g h} hg hh =>
         ⟨by rw [Units.val_mul, Matrix.det_mul, hg.1, hh.1, one_mul],
          zE_stab_mul A hg.1 hh.1 hg.2 hh.2⟩
       one_mem' := ⟨by simp, zE_stab_one A⟩
       inv_mem' := fun {g} hg => ⟨det_inv_eq_one hg.1, zE_stab_inv A hg.1 hg.2⟩ },
      fun g => Iff.rfl⟩
  have hHt : ∀ (a b : Fin 6) (hne : a ≠ b), (a.val + 1 = b.val ∨ b.val + 1 = a.val) →
      ∀ t : K, transvGL K a b hne t ∈ H := fun a b hne _ t =>
    (hH (transvGL K a b hne t)).2 ⟨det_tr hne t, zE_tr_map A hI1 hne t⟩
  have hall : ∀ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
      (A.Fix (Wc K I0)).map (A.act g.1) = A.Fix (Wc K I0) := fun g =>
    ((hH g.1).1 (sl_le_of_adjacent_transvections H hHt g.1 g.2)).2
  haveI : Nonempty {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1} :=
    ⟨⟨1, by simp⟩⟩
  have hsup : (⨆ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
      (A.Fix (Wc K I0)).map (A.act g.1)) = A.Fix (Wc K I0) := by
    simp only [hall, iSup_const]
  have htop : A.Fix (Wc K I0) = ⊤ := hsup.symm.trans S.hspan
  have hfr : finrank K (A.Fix (Wc K I0)) = finrank K V := by
    rw [htop, finrank_top]
  rw [S.h0, S.hV] at hfr
  omega

private theorem zD_weight_pm {μ : Kˣ →* Kˣ} {w : V}
    (hw' : ∀ d : {d : Fin 6 → Kˣ // ∏ i, d i = 1},
      A.act (dg d.1) w = ((μ (d.1 0 * (d.1 3)⁻¹) : Kˣ) : K) • w)
    (τ : Equiv.Perm (Fin 6)) (d : {d : Fin 6 → Kˣ // ∏ i, d i = 1}) :
    A.act (dg d.1) (A.act (pm K τ) w) =
      ((μ (d.1 (τ 0) * (d.1 (τ 3))⁻¹) : Kˣ) : K) • A.act (pm K τ) w := by
  obtain ⟨F, hF⟩ : ∃ F : Fin 6 → Kˣ, ∀ i, F i = d.1 (τ i) :=
    ⟨fun i => d.1 (τ i), fun _ => rfl⟩
  have hd1 : ∏ i, d.1 i = 1 := d.2
  have hFprod : ∏ i, F i = 1 := by
    simp only [hF]
    rw [Equiv.prod_comp τ d.1, hd1]
  have hFconj : pm K τ * dg F * (pm K τ)⁻¹ = dg d.1 := by
    rw [pm_conj_dg]
    congr 1
    funext i
    rw [hF, Equiv.apply_symm_apply]
  have key2 : dg d.1 * pm K τ = pm K τ * dg F := by
    rw [← hFconj, inv_mul_cancel_right]
  have hdetd : ((dg d.1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [det_dg, ← Units.coe_prod, hd1, Units.val_one]
  have hdetF : ((dg F : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [det_dg, ← Units.coe_prod, hFprod, Units.val_one]
  have hdetp : ((pm K τ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := det_pm τ
  have e1 : A.act (dg d.1) (A.act (pm K τ) w) = A.act (dg d.1 * pm K τ) w := by
    rw [A.act_mul _ _ hdetd hdetp, Module.End.mul_apply]
  have hF' : A.act (dg F) w = ((μ (F 0 * (F 3)⁻¹) : Kˣ) : K) • w := hw' ⟨F, hFprod⟩
  rw [e1, key2, A.act_mul _ _ hdetp hdetF, Module.End.mul_apply, hF', map_smul, hF 0, hF 3]

theorem caseB_false {v₀ : V} (S : Setup0 A v₀) {μ : Kˣ →* Kˣ} {w : V} (hμ : ∃ c, μ c ≠ 1)
    (hw : w ≠ 0)
    (hw' : ∀ d : {d : Fin 6 → Kˣ // ∏ i, d i = 1},
      A.act (dg d.1) w = ((μ (d.1 0 * (d.1 3)⁻¹) : Kˣ) : K) • w) : False := by
  have hσ : ∀ p : {p : Fin 6 × Fin 6 // p.1 ≠ p.2},
      ∃ τ : Equiv.Perm (Fin 6), τ 0 = p.1.1 ∧ τ 3 = p.1.2 := fun p => exists_perm_ab p.2
  choose σ hσ0 hσ3 using hσ
  obtain ⟨W, hWl, hWr⟩ : ∃ W : ({p : Fin 6 × Fin 6 // p.1 ≠ p.2} ⊕ Unit) → V,
      (∀ p, W (Sum.inl p) = A.act (pm K (σ p)) w) ∧ (∀ u, W (Sum.inr u) = v₀) :=
    ⟨Sum.elim (fun p => A.act (pm K (σ p)) w) (fun _ => v₀), fun _ => rfl, fun _ => rfl⟩
  obtain ⟨χ, hχl, hχr⟩ : ∃ χ : ({p : Fin 6 × Fin 6 // p.1 ≠ p.2} ⊕ Unit) →
      {d : Fin 6 → Kˣ // ∏ i, d i = 1} → K,
      (∀ p d, χ (Sum.inl p) d = ((μ (d.1 p.1.1 * (d.1 p.1.2)⁻¹) : Kˣ) : K)) ∧
        (∀ u d, χ (Sum.inr u) d = 1) :=
    ⟨Sum.elim (fun p d => ((μ (d.1 p.1.1 * (d.1 p.1.2)⁻¹) : Kˣ) : K)) (fun _ _ => 1),
      fun _ _ => rfl, fun _ _ => rfl⟩
  have hW0 : ∀ τ : Equiv.Perm (Fin 6), A.act (pm K τ) w ≠ 0 := by
    intro τ h
    apply hw
    apply A.actA_inj (det_pm τ)
    rw [h, map_zero]
  have hW : ∀ i, W i ≠ 0 := by
    rintro (p | u)
    · rw [hWl]
      exact hW0 (σ p)
    · rw [hWr]
      exact S.hv0
  have hr : ∀ (i : {p : Fin 6 × Fin 6 // p.1 ≠ p.2} ⊕ Unit)
      (d : {d : Fin 6 → Kˣ // ∏ i, d i = 1}),
      A.act (dg d.1) (W i) = χ i d • W i := by
    rintro (p | u) d
    · rw [hWl, hχl, zD_weight_pm A hw' (σ p) d, hσ0 p, hσ3 p]
    · rw [hWr, hχr, one_smul]
      exact weights_trivial A S (I := I0) (by decide) d.1 d.2 v₀ S.hv₀
  have hsep : ∀ i j : {p : Fin 6 × Fin 6 // p.1 ≠ p.2} ⊕ Unit, i ≠ j →
      ∃ d : {d : Fin 6 → Kˣ // ∏ i, d i = 1}, χ i d ≠ χ j d := by
    rintro (p | u) (q | v) hij
    · have hpq : p.1.1 ≠ q.1.1 ∨ p.1.2 ≠ q.1.2 := by
        by_cases h1 : p.1.1 = q.1.1
        · by_cases h2 : p.1.2 = q.1.2
          · exact absurd (congrArg Sum.inl (Subtype.ext (Prod.ext h1 h2))) hij
          · exact Or.inr h2
        · exact Or.inl h1
      obtain ⟨d, hd, hne⟩ := pairs_sep hμ p.2 q.2 hpq
      refine ⟨⟨d, hd⟩, ?_⟩
      rw [hχl, hχl]
      exact fun h => hne (Units.ext h)
    · obtain ⟨d, hd, hne⟩ := pair_ne_one hμ p.2
      refine ⟨⟨d, hd⟩, ?_⟩
      rw [hχl, hχr]
      exact fun h => hne (Units.val_eq_one.mp h)
    · obtain ⟨d, hd, hne⟩ := pair_ne_one hμ q.2
      refine ⟨⟨d, hd⟩, ?_⟩
      rw [hχr, hχl]
      exact fun h => hne (Units.val_eq_one.mp h.symm)
    · exact absurd (congrArg Sum.inr (Subsingleton.elim u v)) hij
  have hli : LinearIndependent K W :=
    linearIndependent_of_eigen (fun d : {d : Fin 6 → Kˣ // ∏ i, d i = 1} => A.act (dg d.1))
      W χ hW hr hsep
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by rw [S.hV]; norm_num)
  have hle := hli.fintype_card_le_finrank
  rw [S.hV, Fintype.card_sum, Fintype.card_unit] at hle
  have h30 : Fintype.card {p : Fin 6 × Fin 6 // p.1 ≠ p.2} = 30 := by decide
  rw [h30] at hle
  omega

theorem xi_trivial_false [Finite K] {v₀ : V} (S : Setup0 A v₀) : False := by
  have hv₁ : A.act (pm K (Equiv.swap 0 3)) v₀ ∈ A.Fix (Wc K I1) := by
    have e := vI_eq A S.h0 S.hv₀ (Equiv.swap 0 3)
    have hI : I0.image (Equiv.swap 0 3) = I1 := by decide
    rw [hI] at e
    rw [e]
    exact vI_mem A S.h0 S.hv₀ (by decide)
  have hfix : ∀ d : {d : Fin 6 → Kˣ // ∏ i, d i = 1},
      A.act (dg d.1) (A.act (pm K (Equiv.swap 0 3)) v₀) = A.act (pm K (Equiv.swap 0 3)) v₀ :=
    fun d => weights_trivial A S (I := I1) (by decide) d.1 d.2 _ hv₁
  have hr : Function.Surjective
      (fun d : {d : Fin 6 → Kˣ // ∏ i, d i = 1} => d.1 0 * (d.1 3)⁻¹) := by
    intro s
    refine ⟨⟨cOn 0 5 s, ?_⟩, ?_⟩
    · rw [Fin.prod_univ_six]
      simp [cOn]
    · simp [cOn]
  have hρ : ∀ (d : {d : Fin 6 → Kˣ // ∏ i, d i = 1}) (s : Kˣ),
      A.act (dg d.1) (A.X (s : K) (A.act (pm K (Equiv.swap 0 3)) v₀)) =
        A.X ((s * (d.1 0 * (d.1 3)⁻¹) : Kˣ) : K) (A.act (pm K (Equiv.swap 0 3)) v₀) := by
    intro d s
    have e : ((d.1 0 : K) * ((d.1 3 : K))⁻¹ * (s : K)) =
        ((s * (d.1 0 * (d.1 3)⁻¹) : Kˣ) : K) := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      ring
    rw [dg_X A d.1 d.2, hfix d, e]
  rcases const_or_weight (fun s : Kˣ => A.X (s : K) (A.act (pm K (Equiv.swap 0 3)) v₀))
      (fun d : {d : Fin 6 → Kˣ // ∏ i, d i = 1} => d.1 0 * (d.1 3)⁻¹) hr
      (fun d => A.act (dg d.1)) hρ with hconst | ⟨μ, w, hμ, hw, hw'⟩
  · exact caseA_false A S (fun s => by
      have h := hconst s
      simp only [Units.val_one] at h
      exact h)
  · exact caseB_false A S hμ hw hw'

end SLAct

end CFSG.RankThree.GF2n.Smith81.S81J
