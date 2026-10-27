module

public import CFSG.Quasithin.Background.SmithB45MatM22

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1
open scoped Matrix

@[expose] def pair22 (w u : W10) : ZMod 2 :=
  lift22 (Multiplicative.toAdd w) ⬝ᵥ lift10 (Multiplicative.toAdd u)

theorem pair22_mul_left (w₁ w₂ u : W10) : pair22 (w₁ * w₂) u = pair22 w₁ u + pair22 w₂ u := by
  simp only [pair22, toAdd_mul, map_add, add_dotProduct]

theorem pair22_mul_right (w u₁ u₂ : W10) : pair22 w (u₁ * u₂) = pair22 w u₁ + pair22 w u₂ := by
  simp only [pair22, toAdd_mul, map_add, dotProduct_add]

theorem pair22_one_left (u : W10) : pair22 1 u = 0 := by
  simp only [pair22, toAdd_one, map_zero, zero_dotProduct]

theorem pair22_one_right (w : W10) : pair22 w 1 = 0 := by
  simp only [pair22, toAdd_one, map_zero, dotProduct_zero]

theorem toAdd_rhoC10 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) (σ : ↥Γ)
    (w : W10) : Multiplicative.toAdd (rhoC10 Γ hΓ σ w) =
      κC22 (permWord σ (lift22 (Multiplicative.toAdd w))) := rfl

theorem toAdd_rho10 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) (σ : ↥Γ)
    (u : W10) : Multiplicative.toAdd (rho10 Γ hΓ σ u) =
      cc10 (permWord σ (lift10 (Multiplicative.toAdd u))) := rfl

theorem lift22_κC22 {x : Fin 24 → ZMod 2} (hx : x ∈ C) (hx01 : x 0 + x 1 = 0) :
    lift22 (κC22 x) = x ∨ lift22 (κC22 x) = x + Ω := by
  have hd : lift22 (κC22 x) - x ∈ C := C.sub_mem (lift22_mem _) hx
  have hd01 : (lift22 (κC22 x) - x) 0 + (lift22 (κC22 x) - x) 1 = 0 := by
    simp only [Pi.sub_apply]
    linear_combination lift22_pair (κC22 x) - hx01
  have hk : κC22 (lift22 (κC22 x) - x) = 0 := by
    rw [map_sub, κC22_lift22]
    exact sub_self _
  rcases (κC22_eq_zero_iff hd hd01).1 hk with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_iff_eq_add'.1 h)

theorem lift10_cc10 {y : Fin 24 → ZMod 2} (hy : ∑ k, y k = 0) :
    lift10 (cc10 y) - y ∈ C ∨
      lift10 (cc10 y) - y + Multiplicative.toAdd (pairVec 0 1) ∈ C := by
  have hs : ∑ k, (lift10 (cc10 y) - y) k = 0 :=
    (G6.coreMod 24).div_mem (x := Multiplicative.ofAdd (lift10 (cc10 y)))
      (y := Multiplicative.ofAdd y) (sum_lift10 _) hy
  refine (cc10_eq_zero_iff hs).1 ?_
  rw [map_sub, cc10_lift10]
  exact sub_self _

theorem dotProduct_pairVec (c : Fin 24 → ZMod 2) :
    c ⬝ᵥ Multiplicative.toAdd (pairVec 0 1) = c 0 + c 1 := by
  simp only [pairVec, toAdd_mul, toAdd_unitVec, dotProduct_add, dotProduct_single, mul_one]

theorem Ω_dotProduct (y : Fin 24 → ZMod 2) : Ω ⬝ᵥ y = ∑ k, y k := one_dotProduct y

theorem permWord_dotProduct (σ : Equiv.Perm (Fin 24)) (x y : Fin 24 → ZMod 2) :
    permWord σ x ⬝ᵥ permWord σ y = x ⬝ᵥ y :=
  Equiv.sum_comp σ⁻¹ fun i => x i * y i

theorem pair22_rho (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) (σ : ↥Γ)
    (w u : W10) : pair22 (rhoC10 Γ hΓ σ w) (rho10 Γ hΓ σ u) = pair22 w u := by
  have hσ : (σ : Equiv.Perm (Fin 24)) ∈ mog22plus := hΓ σ.2
  set c := lift22 (Multiplicative.toAdd w) with hc
  set e := lift10 (Multiplicative.toAdd u) with he
  have hσc : permWord σ c ∈ C ∧ permWord σ c 0 + permWord σ c 1 = 0 :=
    (preserves_code22 hσ).1 (Multiplicative.ofAdd c)
      ((mem_code22 _).2 ⟨lift22_mem _, lift22_pair _⟩)
  have hσe : ∑ k, permWord σ e k = 0 := by rw [sum_permWord]; exact sum_lift10 _
  unfold pair22
  rw [toAdd_rhoC10, toAdd_rho10, ← hc, ← he]
  set a := lift22 (κC22 (permWord σ c)) with ha
  have haC : a ∈ C := lift22_mem _
  have ha01 : a 0 + a 1 = 0 := lift22_pair _
  have h1 : a ⬝ᵥ lift10 (cc10 (permWord σ e)) = a ⬝ᵥ permWord σ e := by
    have hsplit : lift10 (cc10 (permWord σ e)) =
        permWord σ e + (lift10 (cc10 (permWord σ e)) - permWord σ e) := by abel
    rw [hsplit, dotProduct_add]
    rcases lift10_cc10 hσe with hd | hd
    · rw [dotProduct_eq_zero haC hd, add_zero]
    · have h0 := dotProduct_eq_zero haC hd
      rw [dotProduct_add, dotProduct_pairVec, ha01, add_zero] at h0
      rw [h0, add_zero]
  have h2 : a ⬝ᵥ permWord σ e = permWord σ c ⬝ᵥ permWord σ e := by
    rcases lift22_κC22 hσc.1 hσc.2 with h | h
    · rw [ha, h]
    · rw [ha, h, add_dotProduct, Ω_dotProduct, hσe, add_zero]
  rw [h1, h2, permWord_dotProduct]

theorem pair22_check : (List.range 1024).all (fun m => m == 0 ||
    (List.range 10).any fun i => popc 24 (lift22Cols.getD i 0 &&& actM lift10Cols m) % 2 == 1) =
      true := by
  decide +kernel

theorem exists_pair22_ne_zero {u : W10} (hu : u ≠ 1) : ∃ w, pair22 w u ≠ 0 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 u
  have hm0 : m ≠ 0 := fun h => hu (by rw [h, toW_zero])
  have := List.all_eq_true.1 pair22_check m (List.mem_range.2 hm)
  simp only [Bool.or_eq_true, beq_iff_eq, hm0, false_or, List.any_eq_true,
    List.mem_range] at this
  obtain ⟨i, hi, hodd⟩ := this
  refine ⟨toW 10 (2 ^ i), ?_⟩
  unfold pair22
  rw [toAdd_toW, toAdd_toW, lift22_cols i hi, lift10_bvec, bvec_dotProduct,
    ← ZMod.natCast_mod, hodd]
  exact one_ne_zero

@[expose] def pairHom22 (u : W10) : DualGrp W10 where
  toFun w := Multiplicative.ofAdd (pair22 w u)
  map_one' := by
    change Multiplicative.ofAdd (pair22 1 u) = 1
    rw [pair22_one_left]
    rfl
  map_mul' w₁ w₂ := by
    change Multiplicative.ofAdd (pair22 (w₁ * w₂) u) =
      Multiplicative.ofAdd (pair22 w₁ u) * Multiplicative.ofAdd (pair22 w₂ u)
    rw [pair22_mul_left]
    rfl

@[expose] def dual22Hom : W10 →* DualGrp W10 where
  toFun := pairHom22
  map_one' := DualGrp.ext fun w => by
    change Multiplicative.ofAdd (pair22 w 1) = 1
    rw [pair22_one_right]
    rfl
  map_mul' u₁ u₂ := DualGrp.ext fun w => by
    change Multiplicative.ofAdd (pair22 w (u₁ * u₂)) =
      Multiplicative.ofAdd (pair22 w u₁) * Multiplicative.ofAdd (pair22 w u₂)
    rw [pair22_mul_right]
    rfl

theorem dual22Hom_apply (u w : W10) : dual22Hom u w = Multiplicative.ofAdd (pair22 w u) := rfl

theorem dual22Hom_injective : Function.Injective dual22Hom := by
  rw [injective_iff_map_eq_one]
  intro u hu
  by_contra hne
  obtain ⟨w, hw⟩ := exists_pair22_ne_zero hne
  apply hw
  have h1 := DFunLike.congr_fun hu w
  rw [dual22Hom_apply] at h1
  exact h1

theorem sq_eq_one_W10 (v : W10) : v ^ 2 = 1 := (MaskCoords.std 10).sq_eq_one v

@[expose] noncomputable def dual22Equiv : W10 ≃* DualGrp W10 :=
  MulEquiv.ofBijective dual22Hom (dual22Hom_injective.bijective_of_nat_card_le
    (card_dualGrp sq_eq_one_W10).le)

theorem dual22Equiv_rho (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) (σ : ↥Γ)
    (u : W10) : dual22Equiv (rho10 Γ hΓ σ u) = dualAct W10 (rhoC10 Γ hΓ σ) (dual22Equiv u) := by
  refine DualGrp.ext fun w => ?_
  change Multiplicative.ofAdd (pair22 w (rho10 Γ hΓ σ u)) =
    Multiplicative.ofAdd (pair22 ((rhoC10 Γ hΓ σ)⁻¹ w) u)
  have h := pair22_rho Γ hΓ σ ((rhoC10 Γ hΓ σ)⁻¹ w) u
  rw [MulAut.apply_inv_self] at h
  rw [h]

@[expose] def dualCongr {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W) :
    DualGrp V ≃* DualGrp W where
  toFun f := f.comp e.symm.toMonoidHom
  invFun g := g.comp e.toMonoidHom
  left_inv f := DualGrp.ext fun v => by simp
  right_inv g := DualGrp.ext fun w => by simp
  map_mul' _ _ := rfl

theorem cocode22_dual {V : Type*} [CommGroup V]
    {L : Subgroup (MulAut V)} (h : MathieuCode22 L ⊤ ⊥) :
    MathieuCocode22 (L.map (dualAct V)) ⊤ ⊥ := by
  obtain ⟨e, he⟩ := code22_std h
  set ψ : DualGrp V ≃* W10 := (dualCongr e).trans dual22Equiv.symm with hψ
  have key : ∀ (σ : ↥mog22) (x : MulAut V),
      congrHom e x = rhoC10 mog22 mog22_le_mog22plus σ →
        congrHom ψ (dualAct V x) = rho10 mog22 mog22_le_mog22plus σ := by
    intro σ x hx
    refine MulEquiv.ext fun g => ?_
    change dual22Equiv.symm (dualCongr e (dualAct V x ((dualCongr e).symm
      (dual22Equiv g)))) = rho10 mog22 mog22_le_mog22plus σ g
    rw [MulEquiv.symm_apply_eq, dual22Equiv_rho]
    refine DualGrp.ext fun w => ?_
    change dual22Equiv g (e (x⁻¹ (e.symm w))) =
      dual22Equiv g ((rhoC10 mog22 mog22_le_mog22plus σ)⁻¹ w)
    rw [← hx]
    rfl
  have hrange : (L.map (dualAct V)).map (congrHom ψ) =
      (rho10 mog22 mog22_le_mog22plus).range := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have h1 : congrHom e x ∈ L.map (congrHom e) := ⟨x, hx, rfl⟩
      erw [he] at h1
      obtain ⟨σ, hσ⟩ := h1
      exact ⟨σ, (key σ x hσ.symm).symm⟩
    · rintro _ ⟨σ, rfl⟩
      have h1 : rhoC10 mog22 mog22_le_mog22plus σ ∈ (rhoC10 mog22 mog22_le_mog22plus).range :=
        ⟨σ, rfl⟩
      erw [← he] at h1
      obtain ⟨x, hx, hxσ⟩ := h1
      exact ⟨dualAct V x, ⟨x, hx, rfl⟩, key σ x hxσ⟩
  obtain ⟨a, b, hab, hR⟩ := B45Mat.M22.cocode22_rho10
  exact ⟨a, b, hab, B45Mat.M22.realizes_of_map_congrHom ψ hrange hR⟩

end CFSG.Quasithin.H.Mathieu

namespace CFSG.Quasithin.B45Mat

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.Code

variable {V : Type*} [CommGroup V] [Finite V] {L X : Subgroup (MulAut V)}

theorem not_isFFModule_dual_code22
    (hLX : IsOver L X) (h : MathieuCode22 L ⊤ ⊥) : ¬ IsFFModule (X.map (dualAct V)) := by
  have hW2 : ∀ f : DualGrp V, f ^ 2 = 1 := by
    intro f
    refine DFunLike.ext _ _ fun v => ?_
    show (f v) ^ 2 = 1
    generalize f v = x
    revert x
    decide
  have hLX' : IsOver (L.map (dualAct V)) (X.map (dualAct V)) :=
    ⟨Subgroup.map_mono hLX.1, (Subgroup.map_mono hLX.2).trans (Subgroup.le_normalizer_map _)⟩
  have hq := two_lt_qOf_cocode22 hLX' (cocode22_dual h)
  intro hFF
  have h1 : qOf (X.map (dualAct V)) ≤ 1 := ((B1_4_5 hW2 _).out 1 3).1 hFF
  have h2 : ((2 : ℚ) : WithTop ℚ) < ((1 : ℚ) : WithTop ℚ) := lt_of_lt_of_le hq h1
  have h3 : (2 : ℚ) < 1 := WithTop.coe_lt_coe.1 h2
  norm_num at h3

omit [Finite V] in
theorem not_isDualFFInt_code22
    {G : Type*} [Group G] [Finite G] {L₀ M₀ W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hLX : IsOver (autI hW L₀) (autI hW M₀)) (h : MathieuCode22 (autI hW L₀) ⊤ ⊥) :
    ¬ IsDualFFInt M₀ W hW :=
  not_isFFModule_dual_code22 (V := IntMod W hW) hLX h

end CFSG.Quasithin.B45Mat
