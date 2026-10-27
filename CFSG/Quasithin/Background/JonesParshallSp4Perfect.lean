module

public import CFSG.Quasithin.Background.JonesParshallSp4H1

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

theorem commutatorElement_eq_of {G : Type*} [Group G] {h x t : G} (e : h * x = t * x * h) :
    ⁅h, x⁆ = t := by
  rw [commutatorElement_def, e]
  group

theorem spX_mul (a b d a' b' d' : F) : spX a b d * spX a' b' d' = spX (a + a') (b + b') (d + d') :=
  sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, mul_smul, spX_smul, spX_smul, spX_smul]
    congr 1 <;> ring

theorem spY_mul (a b d a' b' d' : F) : spY a b d * spY a' b' d' = spY (a + a') (b + b') (d + d') :=
  sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, mul_smul, spY_smul, spY_smul, spY_smul]
    congr 1 <;> ring

theorem rootGens_subset_commutator {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    rootGens F ⊆ ((⁅sp4 F, sp4 F⁆ : Subgroup (GL Ix F)) : Set (GL Ix F)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc1' : c + 1 ≠ 0 := fun h => hc1 (by
    have : c = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq])
  have hc2 : c ^ 2 + 1 ≠ 0 := by
    have : c ^ 2 + 1 = (c + 1) ^ 2 := by rw [add_sq_F, one_pow]
    rw [this]
    exact pow_ne_zero 2 hc1'
  have hmem : ∀ {g x t : ↥(sp4 F)}, (g : GL Ix F) * x = t * x * g →
      (t : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun {g x t} e => by
    rw [← commutatorElement_eq_of e]
    exact Subgroup.commutator_mem_commutator g.2 x.2
  have hxa : ∀ s : F, (spX s 0 0 : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH c 1 hc0 one_ne_zero) (x := spX (s / (c ^ 2 + 1)) 0 0) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spX_smul, spH_smul, spH_smul, spX_smul, spX_smul]
    congr 1 <;> field_simp <;> ring_nf
    reduce_mod_char!
  have hxb : ∀ s : F, (spX 0 s 0 : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH c 1 hc0 one_ne_zero) (x := spX 0 (s / (c + 1)) 0) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spX_smul, spH_smul, spH_smul, spX_smul, spX_smul]
    congr 1 <;> field_simp <;> ring_nf <;> reduce_mod_char!
  have hxd : ∀ s : F, (spX 0 0 s : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH 1 c one_ne_zero hc0) (x := spX 0 0 (s / (c ^ 2 + 1))) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spX_smul, spH_smul, spH_smul, spX_smul, spX_smul]
    congr 1 <;> field_simp <;> ring_nf
    reduce_mod_char!
  have hya : ∀ s : F, (spY s 0 0 : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH c⁻¹ 1 (inv_ne_zero hc0) one_ne_zero)
      (x := spY (s / (c ^ 2 + 1)) 0 0) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spY_smul, spH_smul, spH_smul, spY_smul, spY_smul]
    congr 1 <;> field_simp <;> ring_nf
    reduce_mod_char!
  have hyb : ∀ s : F, (spY 0 s 0 : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH c⁻¹ 1 (inv_ne_zero hc0) one_ne_zero)
      (x := spY 0 (s / (c + 1)) 0) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spY_smul, spH_smul, spH_smul, spY_smul, spY_smul]
    congr 1 <;> field_simp <;> ring_nf <;> reduce_mod_char!
  have hyd : ∀ s : F, (spY 0 0 s : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH 1 c⁻¹ one_ne_zero (inv_ne_zero hc0))
      (x := spY 0 0 (s / (c ^ 2 + 1))) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spY_smul, spH_smul, spH_smul, spY_smul, spY_smul]
    congr 1 <;> field_simp <;> ring_nf
    reduce_mod_char!
  have hz : ∀ s : F, (spZ s : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH c 1 hc0 one_ne_zero) (x := spZ (s / (c + 1))) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spZ_smul, spH_smul, spH_smul, spZ_smul, spZ_smul]
    congr 1 <;> field_simp <;> ring_nf <;> reduce_mod_char!
  have hz' : ∀ s : F, (spZ' s : GL Ix F) ∈ ⁅sp4 F, sp4 F⁆ := fun s => by
    refine hmem (g := spH 1 c one_ne_zero hc0) (x := spZ' (s / (c + 1))) ?_
    refine gl_ext_vec4 fun x y z w => ?_
    rw [mul_smul, mul_smul, mul_smul, spZ'_smul, spH_smul, spH_smul, spZ'_smul, spZ'_smul]
    congr 1 <;> field_simp <;> ring_nf <;> reduce_mod_char!
  rintro g (⟨a, b, d, rfl⟩ | ⟨a, b, d, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩)
  · have e : spX a b d = spX a 0 0 * spX 0 b 0 * spX (0 : F) 0 d := by
      rw [spX_mul, spX_mul]
      congr 1 <;> ring
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hxa a) (hxb b)) (hxd d)
  · have e : spY a b d = spY a 0 0 * spY 0 b 0 * spY (0 : F) 0 d := by
      rw [spY_mul, spY_mul]
      congr 1 <;> ring
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hya a) (hyb b)) (hyd d)
  · exact hz t
  · exact hz' t

theorem sp4_commutator_eq {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) : ⁅sp4 F, sp4 F⁆ = sp4 F := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun g hg h hh => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
  · conv_lhs => rw [sp4_eq_closure]
    exact (Subgroup.closure_le _).mpr (rootGens_subset_commutator hc0 hc1)

section Theorem

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def additiveIx (F : Type) [Field F] : Additive (Multiplicative (Ix → F)) ≃+ (Ix → F) where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [CharP F 2] in
theorem BinaryNaturalSp4Derived.intertwiner {ρ : Representation (ZMod 2) Γ W}
    (h : BinaryNaturalSp4Derived ρ F) :
    ∃ (θ : Γ ≃* ↥⁅sp4 F, sp4 F⁆) (β : W ≃+ (Ix → F)),
      ∀ γ w, β (ρ γ w) = ((θ γ : ↥⁅sp4 F, sp4 F⁆) : GL Ix F) • β w := by
  obtain ⟨θ₀, β₀, hw⟩ := h
  let θ₁ : Γ ≃* ↥⁅sp4 F, sp4 F⁆ := θ₀
  have ha := Witness.ambient (D := FFModel.nat ⁅sp4 F, sp4 F⁆) (θ := θ₁) rfl rfl hw
  refine ⟨θ₁, (β₀.trans (secEquivAmb _ rfl rfl).toAdditive).trans (additiveIx F),
    fun γ w => ?_⟩
  exact congrArg (additiveIx F) (ha γ w)

variable [Fintype F]

theorem finrank_H1_sp4Derived_of_one_lt {ρ : Representation (ZMod 2) Γ W} {a : ℕ}
    (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) (h : BinaryNaturalSp4Derived ρ F) :
    Module.finrank (ZMod 2) (H1 ρ) = a := by
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSp4Derived.intertwiner h
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hF ha
  let θ' : Γ ≃* ↥(sp4 F) := θ.trans (MulEquiv.subgroupCongr (sp4_commutator_eq hc0 hc1))
  have : Finite Γ := Finite.of_equiv _ θ'.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = muSp (θ' γ) (β w) := hβ
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (card_Z1A_muSp hF ha), hF]

end Theorem

end CFSG.Quasithin.JonesParshall
