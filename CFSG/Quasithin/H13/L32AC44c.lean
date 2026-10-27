module

public import CFSG.Quasithin.H13.L32AC44b
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB42SL3Base

public section

namespace CFSG.Quasithin.H13.L32A.C.SL3N

open Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin CFSG.Quasithin.B42SL3
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups

section Explicit

variable {F : Type} [Field F] [CharP F 2]

theorem exists_natRep_equiv' {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) (j : ℕ) :
    ∃ ψ : SL(3, F) →* SL(3, F), (ψ = MonoidHom.id _ ∨ ψ = tauSL F) ∧ (∀ g, ψ (ψ g) = g) ∧
      Nonempty ((matRep (locRep (F := F) F ℓ.1 ℓ.2 j)).Equiv
        (matRep ((natRep (F := F) F j).comp ψ))) := by
  rcases hℓ with rfl | rfl
  · exact ⟨MonoidHom.id _, Or.inl rfl, fun g => rfl, ⟨Representation.Equiv.refl _⟩⟩
  · refine ⟨tauSL F, Or.inr rfl, tauSL_tauSL, ⟨?_⟩⟩
    have h : (natRep F j).comp (tauSL F) = locRep F false true j :=
      MonoidHom.ext fun g => natRep_tauSL (F := F) F j g
    rw [h]
    exact Representation.Equiv.refl _

variable [Fintype F] {f : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem exists_natural_of_single' (hF : Fintype.card F = 2 ^ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible) {a b : Fin f → Bool} (hS : cntS a b = 1) (hH : cntH a b = 0)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :
    ∃ ψ : SL(3, F) →* SL(3, F), (ψ = MonoidHom.id _ ∨ ψ = tauSL F) ∧
      ∃ E : U ≃+ (Fin 3 → F), ∀ g u,
        E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u := by
  obtain ⟨i₀, hsingle, hrest⟩ := exists_single_pos hS hH
  obtain ⟨e₁⟩ := nonempty_equiv_locRep (F := F) (fun i : Fin f => (a i, b i))
    (fun i => (i : ℕ)) (i₀ := i₀) hrest
  obtain ⟨ψ, hψ1, hψ, ⟨e₂⟩⟩ := exists_natRep_equiv' (F := F) hsingle (i₀ : ℕ)
  obtain ⟨E, hE⟩ := exists_addEquiv_of_sub hF ρ bas hirr W₀ hψ ((e₀.trans e₁).trans e₂)
  exact ⟨ψ, hψ1, exists_untwist ρ (i₀ : ℕ) E hE⟩

theorem natural_of_offender' [Finite U] (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F) (A : Subgroup (U ≃ₗ[ZMod 2] U))
    (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) [CFSG.IsElementaryAbelian 2 A]
    (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f) (hirr : ρ.IsIrreducible) (hA1 : A ≠ ⊥)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card U ≤ Nat.card ↥A * Nat.card {u : U // ∀ a ∈ A, a u = u}) :
    ∃ ψ : SL(3, F) →* SL(3, F), (ψ = MonoidHom.id _ ∨ ψ = tauSL F) ∧
      ∃ E : U ≃+ (Fin 3 → F), ∀ g u,
        E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  by_cases hsd : Nonempty (ρ.Equiv ρ.dual)
  · exfalso
    have := self_dual_full_normalizer_no_offender selfDualInvolutionRank hf hF ρ hker hirr hsd
      A hA1 hA
    omega
  have hnt : ∃ x, ρ x ≠ 1 := ⟨up3 0 0 1, fun h => by
    obtain ⟨c, -, hc⟩ := hker _ h
    exact not_scalar_up3 (F := F) ⟨(c : F), hc⟩⟩
  let bas := Module.finBasis (ZMod 2) U
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ := exists_label hF (by omega) ρ bas hirr hnt
  have hdim : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  rcases label_cases (by omega) a b hne _ hdim hsum with ⟨hS, hH⟩ | ⟨hS, hH, hR⟩ | hR
  · exact exists_natural_of_single' hF ρ bas hirr hS hH W₀ e₀
  · exfalso
    have hk := card_innerPart_le_of_two ρ hker A hA hF (by omega) hirr hquad bas hS hH W₀ e₀
    have := card_mul_card_fix_lt ρ hker A hA hf hF hirr hsd hA1 hk (by omega) (by omega)
    omega
  · exfalso
    have hk := card_innerPart_le ρ hker A hA hf hNat hirr
    have := card_mul_card_fix_lt ρ hker A hA hf hF hirr hsd hA1 hk (by omega) (by omega)
    omega

end Explicit

section Twist

variable {F : Type} [Field F] [CharP F 2]

@[expose] def rootE0 (F : Type) [Field F] [CharP F 2] : Subgroup SL(3, F) where
  carrier := Set.range fun p : F × F => up3 0 p.1 p.2
  one_mem' := ⟨(0, 0), up3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨y, z⟩, rfl⟩ ⟨⟨Y, Z⟩, rfl⟩
    refine ⟨(y + Y, z + Z), ?_⟩
    rw [up3_mul]
    simp
  inv_mem' := by
    rintro _ ⟨⟨y, z⟩, rfl⟩
    refine ⟨(y, z), ?_⟩
    rw [up3_inv]
    simp

theorem mem_rootE0 {g : SL(3, F)} : g ∈ rootE0 F ↔ ∃ y z : F, g = up3 0 y z :=
  ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp.symm⟩, fun ⟨y, z, h⟩ => ⟨(y, z), h.symm⟩⟩

theorem rootE0_mul_comm {g h : SL(3, F)} (hg : g ∈ rootE0 F) (hh : h ∈ rootE0 F) :
    g * h = h * g := by
  obtain ⟨y, z, rfl⟩ := mem_rootE0.mp hg
  obtain ⟨Y, Z, rfl⟩ := mem_rootE0.mp hh
  rw [up3_mul, up3_mul]
  congr 1 <;> ring

theorem rootE0_mul_self {g : SL(3, F)} (hg : g ∈ rootE0 F) : g * g = 1 := by
  obtain ⟨y, z, rfl⟩ := mem_rootE0.mp hg
  rw [up3_mul]
  simp [CharTwo.add_self_eq_zero, up3_zero]

omit [CharP F 2] in
theorem rootE0_mulVec (y z : F) (w : Fin 3 → F) :
    (up3 (0 : F) y z : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w + Pi.single 0 (z * w 1 + y * w 2) := by
  rw [up3_coe, upMat_mulVec]
  funext k
  fin_cases k
  · simp
    ring
  · simp
  · simp

omit [CharP F 2] in
theorem coe_mul_coe (g h : SL(3, F)) :
    (g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) =
      ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := rfl

omit [CharP F 2] in
theorem coe_inv_mul_coe (g : SL(3, F)) :
    ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
  congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (inv_mul_cancel g)

omit [CharP F 2] in
theorem coe_mul_coe_inv (g : SL(3, F)) :
    (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (mul_inv_cancel g)

omit [CharP F 2] in
theorem ext_of_mulVec {g h : SL(3, F)}
    (H : ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = (h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) :
    g = h := by
  apply Subtype.ext
  ext i j
  have := congrFun (H (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

omit [CharP F 2] in
theorem eq_one_of_mulVec {g : SL(3, F)} (h : ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    g = 1 := by
  apply Subtype.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end Twist

section Semi

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem exists_semilinear_of_aut {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (α : SL(3, F) ≃* SL(3, F)) :
    ∃ ψ : SL(3, F) →* SL(3, F), (ψ = MonoidHom.id _ ∨ ψ = tauSL F) ∧
      ∃ (E : (Fin 3 → F) ≃+ (Fin 3 → F)) (μ : F → F),
        (∀ g v, E (((α g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
          ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E v) ∧
        ∀ (c : F) v, E (c • v) = μ c • E v := by
  classical
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let lin : Matrix (Fin 3) (Fin 3) F → (Fin 3 → F) →ₗ[ZMod 2] (Fin 3 → F) := fun M =>
    { toFun := fun v => M *ᵥ v
      map_add' := fun v w => mulVec_add M v w
      map_smul' := fun c v => by
        rcases (show c = 0 ∨ c = 1 by fin_cases c; exacts [Or.inl rfl, Or.inr rfl]) with
          rfl | rfl <;> simp }
  have hlin : ∀ M v, lin M v = M *ᵥ v := fun _ _ => rfl
  let ρ : Representation (ZMod 2) SL(3, F) (Fin 3 → F) :=
    { toFun := fun g => lin ((α g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
      map_one' := by
        refine LinearMap.ext fun v => ?_
        rw [hlin, map_one]
        exact one_mulVec v
      map_mul' := fun g h => by
        refine LinearMap.ext fun v => ?_
        rw [Module.End.mul_apply, hlin, hlin, hlin, map_mul, mulVec_mulVec, coe_mul_coe] }
  have hρ : ∀ g v, ρ g v = ((α g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v :=
    fun _ _ => rfl
  let τ : SL(3, F) →* ((Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F)) :=
    { toFun := fun g =>
        { lin (g : Matrix (Fin 3) (Fin 3) F) with
          invFun := fun v => ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
          left_inv := fun v => by
            show ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v
            rw [mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
          right_inv := fun v => by
            show (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v
            rw [mulVec_mulVec, coe_mul_coe_inv, one_mulVec] }
      map_one' := LinearEquiv.ext fun v => one_mulVec v
      map_mul' := fun g h => LinearEquiv.ext fun v => by
        show ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
          (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
        rw [mulVec_mulVec, coe_mul_coe] }
  have hτ : ∀ g v, τ g v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := fun _ _ => rfl
  have hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F := by
    intro x hx
    have h2 : α x = 1 := eq_one_of_mulVec fun v => LinearMap.congr_fun hx v
    rw [show x = 1 from α.injective (h2.trans (map_one α).symm)]
    exact (scalars 3 F).one_mem
  set A : Subgroup ((Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F)) := (rootE0 F).map τ with hAdef
  have hAv : ∀ a ∈ A, ∃ y z : F, ∀ v, a v = v + Pi.single 0 (z * v 1 + y * v 2) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨y, z, rfl⟩ := mem_rootE0.mp hg
    exact ⟨y, z, fun v => rootE0_mulVec y z v⟩
  have hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y := by
    rintro _ ⟨r, -, rfl⟩ x
    refine ⟨α.symm (r * α x * r⁻¹), fun u => ?_⟩
    rw [hτ, hρ, hρ, hτ, MulEquiv.apply_symm_apply, mulVec_mulVec, mulVec_mulVec, coe_mul_coe,
      coe_mul_coe, inv_mul_cancel_right]
  have : CFSG.IsElementaryAbelian 2 ↥A :=
    { is_comm := ⟨fun a b => by
        obtain ⟨r₁, h₁, e₁⟩ := a.2
        obtain ⟨r₂, h₂, e₂⟩ := b.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← e₁, ← e₂, ← map_mul, ← map_mul,
          rootE0_mul_comm h₁ h₂]⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨r, hr, e⟩ := a.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← e, ← map_pow, pow_two, rootE0_mul_self hr,
          map_one] }
  have hirr : ρ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨inferInstance, fun M hM => ?_⟩
    rcases eq_bot_or_eq_top M.toAddSubgroup (fun g v hv => by
      obtain ⟨g', rfl⟩ := α.surjective g
      exact hM g' v hv) with h | h
    · exact Or.inl (Submodule.toAddSubgroup_injective (h.trans Submodule.bot_toAddSubgroup.symm))
    · exact Or.inr (Submodule.toAddSubgroup_injective (h.trans Submodule.top_toAddSubgroup.symm))
  have hA1 : A ≠ ⊥ := by
    intro h
    have hmem : τ (up3 0 0 1) ∈ A := ⟨_, mem_rootE0.mpr ⟨0, 1, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 := congrFun (LinearEquiv.congr_fun hmem (Pi.single 1 1)) 0
    rw [hτ, rootE0_mulVec] at h1
    simp at h1
  have hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w := by
    intro a ha b hb w
    obtain ⟨y, z, hy⟩ := hAv a ha
    obtain ⟨Y, Z, hY⟩ := hAv b hb
    rw [hy, add_sub_cancel_left, hY]
    simp
  have hτinj : Function.Injective τ := fun g h hgh =>
    ext_of_mulVec fun v => LinearEquiv.congr_fun hgh v
  have hcardR : Nat.card (rootE0 F) = Nat.card F ^ 2 := by
    have e : (F × F) ≃ rootE0 F := Equiv.ofBijective (fun p => ⟨up3 0 p.1 p.2, ⟨p, rfl⟩⟩)
      ⟨fun p q h => by
        have := up3_inj (congrArg Subtype.val h)
        exact Prod.ext this.2.1 this.2.2,
       fun ⟨g, ⟨p, hp⟩⟩ => ⟨p, Subtype.ext hp⟩⟩
    rw [← Nat.card_congr e, Nat.card_prod, pow_two]
  have hcardA : Nat.card A = Nat.card F ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective hτinj, hcardR]
  have hcardC : Nat.card F ≤ Nat.card {u : Fin 3 → F // ∀ a ∈ A, a u = u} := by
    refine Nat.card_le_card_of_injective (fun c : F => ⟨Pi.single 0 c, fun a ha => ?_⟩) ?_
    · obtain ⟨y, z, hy⟩ := hAv a ha
      rw [hy]
      simp
    · intro c d h
      have := congrFun (congrArg Subtype.val h) 0
      simpa using this
  have hoff : Nat.card (Fin 3 → F) ≤
      Nat.card ↥A * Nat.card {u : Fin 3 → F // ∀ a ∈ A, a u = u} := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hcardA]
    calc Nat.card F ^ 3 = Nat.card F ^ 2 * Nat.card F := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hcardC
  obtain ⟨ψ, hψ, E, hE⟩ := natural_of_offender' ρ hker A hA hf hF hirr hA1 hquad hoff
  have hEα : ∀ g v, E (((α g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E v := fun g v => hE g v
  have hψs : Function.Surjective ψ := by
    rcases hψ with rfl | rfl
    · exact fun g => ⟨g, rfl⟩
    · exact fun g => ⟨tauSL F g, tauSL_tauSL g⟩
  have hμ : ∀ c : F, ∃ m : F, ∀ v, E (c • v) = m • E v := by
    intro c
    let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun w => E (c • E.symm w)
        map_zero' := by simp
        map_add' := fun w w' => by simp [smul_add] }
    obtain ⟨m, hm⟩ := eq_smul_of_comm φ fun h w => by
      obtain ⟨g, rfl⟩ := hψs h
      have h1 : E.symm (((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
          ((α g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E.symm w := by
        apply E.injective
        rw [AddEquiv.apply_symm_apply, hEα, AddEquiv.apply_symm_apply]
      show E (c • E.symm (((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w)) =
        ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E (c • E.symm w)
      rw [h1, ← mulVec_smul, hEα]
    refine ⟨m, fun v => ?_⟩
    have := hm (E v)
    simpa [φ] using this
  choose μ hμ using hμ
  exact ⟨ψ, hψ, E, μ, hEα, hμ⟩

end Semi

end CFSG.Quasithin.H13.L32A.C.SL3N
