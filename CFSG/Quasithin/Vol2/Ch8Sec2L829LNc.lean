module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice

public section

namespace CFSG.Quasithin.H13.L829N

structure SectionModule {G : Type} [Group G] (Λ W₀ W₁ : Subgroup G) (W : Type)
    [AddCommGroup W] [Module (ZMod 2) W] where
  π : ↥W₁ →* Multiplicative W
  ρ : ↥Λ →* (W ≃ₗ[ZMod 2] W)
  surj : Function.Surjective π
  ker : ∀ x : ↥W₁, π x = 1 ↔ (x : G) ∈ W₀
  norm₁ : Λ ≤ Subgroup.normalizer (W₁ : Set G)
  le : W₀ ≤ W₁
  act : ∀ (y : ↥Λ) (x : ↥W₁) (hx : (y : G) * (x : G) * (y : G)⁻¹ ∈ W₁),
    ρ y (Additive.ofMul (π x)) = Additive.ofMul (π ⟨(y : G) * x * (y : G)⁻¹, hx⟩)

private abbrev toW_LNc {W : Type} (a : Multiplicative W) : W := Additive.ofMul a

private lemma toW_one_LNc {W : Type} [AddCommGroup W] : toW_LNc (1 : Multiplicative W) = 0 := rfl

private lemma toW_mul_inv_LNc {W : Type} [AddCommGroup W] (u v : Multiplicative W) :
    toW_LNc (u * v⁻¹) = toW_LNc u - toW_LNc v :=
  (rfl : toW_LNc (u * v⁻¹) = toW_LNc u + -toW_LNc v).trans (sub_eq_add_neg _ _).symm

private lemma conj_mem_W1_LNc {G : Type} [Group G] {Λ W₀ W₁ : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (S : SectionModule Λ W₀ W₁ W) (y : ↥Λ) (x : ↥W₁) :
    (y : G) * x * (y : G)⁻¹ ∈ W₁ :=
  (Subgroup.mem_normalizer_iff.mp (S.norm₁ y.2) x).mp x.2

private lemma zmod_two_cases_LNc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private class ElemAbelianSectionLNc {G : Type} [Group G] (W₀ W₁ : Subgroup G) : Prop where
  comm_mem : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₀
  sq_mem : ∀ x ∈ W₁, x * x ∈ W₀

section Construction

variable {G : Type} [Group G]

private lemma conj_mem_of_norm_LNc {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

private instance normal_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁] :
    (W₀.subgroupOf W₁).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa [mul_assoc] using
      mul_mem (ElemAbelianSectionLNc.comm_mem (g : G) g.2 (n : G) n.2) hn⟩

private lemma quot_mul_comm_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁]
    (a b : ↥W₁ ⧸ W₀.subgroupOf W₁) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa [mul_assoc] using
    ElemAbelianSectionLNc.comm_mem (y : G)⁻¹ (W₁.inv_mem y.2) (x : G)⁻¹ (W₁.inv_mem x.2)

private instance commGroup_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁] :
    CommGroup (↥W₁ ⧸ W₀.subgroupOf W₁) :=
  { (inferInstance : Group (↥W₁ ⧸ W₀.subgroupOf W₁)) with mul_comm := quot_mul_comm_LNc }

private lemma two_nsmul_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁]
    (a : Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) : (2 : ℕ) • a = 0 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have ha : a = Additive.ofMul (x : ↥W₁ ⧸ W₀.subgroupOf W₁) := by
    rw [hx, ofMul_toMul]
  rw [ha, ← ofMul_pow, ← QuotientGroup.mk_pow, ofMul_eq_zero, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, SubgroupClass.coe_pow, sq]
  exact ElemAbelianSectionLNc.sq_mem (x : G) x.2

private instance module_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁] :
    Module (ZMod 2) (Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) :=
  AddCommGroup.zmodModule (fun a => two_nsmul_LNc a)

private def conjW1_LNc {Λ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (y : ↥Λ) : ↥W₁ →* ↥W₁ where
  toFun x := ⟨(y : G) * x * (y : G)⁻¹, conj_mem_of_norm_LNc (h1 y.2) x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x z := Subtype.ext (by simp [mul_assoc])

private lemma conjW1_le_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) (y : ↥Λ) :
    W₀.subgroupOf W₁ ≤ (W₀.subgroupOf W₁).comap (conjW1_LNc h1 y) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact conj_mem_of_norm_LNc (h0 y.2) hx

private def ρQ_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ) :
    (↥W₁ ⧸ W₀.subgroupOf W₁) →* (↥W₁ ⧸ W₀.subgroupOf W₁) :=
  QuotientGroup.map (W₀.subgroupOf W₁) (W₀.subgroupOf W₁) (conjW1_LNc h1 y)
    (conjW1_le_LNc h1 h0 y)

private lemma ρQ_mul_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y z : ↥Λ) :
    ρQ_LNc h1 h0 (y * z) = (ρQ_LNc h1 h0 y).comp (ρQ_LNc h1 h0 z) := by
  apply QuotientGroup.monoidHom_ext
  ext x
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, ρQ_LNc, QuotientGroup.map_mk]
  congr 1
  exact Subtype.ext (by simp [conjW1_LNc, mul_assoc])

private lemma ρQ_one_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] :
    ρQ_LNc h1 h0 1 = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  ext x
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, ρQ_LNc, QuotientGroup.map_mk,
    MonoidHom.id_apply]
  congr 1
  exact Subtype.ext (by simp [conjW1_LNc])

private lemma ρQ_comp_inv_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ) :
    (ρQ_LNc h1 h0 y).comp (ρQ_LNc h1 h0 y⁻¹) = MonoidHom.id _ := by
  rw [← ρQ_mul_LNc h1 h0 y y⁻¹, mul_inv_cancel, ρQ_one_LNc h1 h0]

private lemma ρQ_inv_comp_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ) :
    (ρQ_LNc h1 h0 y⁻¹).comp (ρQ_LNc h1 h0 y) = MonoidHom.id _ := by
  rw [← ρQ_mul_LNc h1 h0 y⁻¹ y, inv_mul_cancel, ρQ_one_LNc h1 h0]

private def ρA_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ) :
    Additive (↥W₁ ⧸ W₀.subgroupOf W₁) →+ Additive (↥W₁ ⧸ W₀.subgroupOf W₁) :=
  MonoidHom.toAdditive (ρQ_LNc h1 h0 y)

private lemma ρA_mul_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y z : ↥Λ)
    (w : Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) :
    ρA_LNc h1 h0 (y * z) w = ρA_LNc h1 h0 y (ρA_LNc h1 h0 z w) :=
  congrArg (fun q => Additive.ofMul q)
    (DFunLike.congr_fun (ρQ_mul_LNc h1 h0 y z) (Additive.toMul w))

private lemma ρA_left_inv_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ)
    (w : Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) :
    ρA_LNc h1 h0 y (ρA_LNc h1 h0 y⁻¹ w) = w :=
  congrArg (fun q => Additive.ofMul q)
    (DFunLike.congr_fun (ρQ_comp_inv_LNc h1 h0 y) (Additive.toMul w))

private lemma ρA_right_inv_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ)
    (w : Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) :
    ρA_LNc h1 h0 y⁻¹ (ρA_LNc h1 h0 y w) = w :=
  congrArg (fun q => Additive.ofMul q)
    (DFunLike.congr_fun (ρQ_inv_comp_LNc h1 h0 y) (Additive.toMul w))

private def ρLin_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y : ↥Λ) :
    Additive (↥W₁ ⧸ W₀.subgroupOf W₁) ≃ₗ[ZMod 2] Additive (↥W₁ ⧸ W₀.subgroupOf W₁) :=
  LinearEquiv.ofLinearMap ((ρA_LNc h1 h0 y).toZModLinearMap 2)
    ((ρA_LNc h1 h0 y⁻¹).toZModLinearMap 2)
    (LinearMap.ext fun w => ρA_left_inv_LNc h1 h0 y w)
    (LinearMap.ext fun w => ρA_right_inv_LNc h1 h0 y w)

private lemma ρLin_mul_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] (y z : ↥Λ) :
    ρLin_LNc h1 h0 (y * z) = ρLin_LNc h1 h0 y * ρLin_LNc h1 h0 z := by
  refine LinearEquiv.ext fun w => ?_
  exact ρA_mul_LNc h1 h0 y z w

private def ρHom_LNc {Λ W₀ W₁ : Subgroup G} (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G)) [ElemAbelianSectionLNc W₀ W₁] :
    ↥Λ →* (Additive (↥W₁ ⧸ W₀.subgroupOf W₁) ≃ₗ[ZMod 2] Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) :=
  MonoidHom.mk' (fun y => ρLin_LNc h1 h0 y) (fun y z => ρLin_mul_LNc h1 h0 y z)

private def piQ_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁] :
    ↥W₁ →* Multiplicative (Additive (↥W₁ ⧸ W₀.subgroupOf W₁)) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul (x : ↥W₁ ⧸ W₀.subgroupOf W₁))
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma piQ_surj_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁] :
    Function.Surjective (piQ_LNc (W₀ := W₀) (W₁ := W₁)) := by
  intro b
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd b))
  refine ⟨x, ?_⟩
  show Multiplicative.ofAdd (Additive.ofMul (x : ↥W₁ ⧸ W₀.subgroupOf W₁)) = b
  rw [hx, ofMul_toMul, ofAdd_toAdd]

private lemma piQ_ker_LNc {W₀ W₁ : Subgroup G} [ElemAbelianSectionLNc W₀ W₁] (x : ↥W₁) :
    piQ_LNc (W₀ := W₀) (W₁ := W₁) x = 1 ↔ (x : G) ∈ W₀ := by
  show (x : ↥W₁ ⧸ W₀.subgroupOf W₁) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff (N := W₀.subgroupOf W₁) x).trans Subgroup.mem_subgroupOf

end Construction

theorem exists_sectionModule {G : Type} [Group G] [Finite G] {Λ W₀ W₁ : Subgroup G}
    (hle : W₀ ≤ W₁) (h0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (h1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hab : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₀) (hsq : ∀ x ∈ W₁, x * x ∈ W₀) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W),
      Nonempty (SectionModule Λ W₀ W₁ W) := by
  haveI : ElemAbelianSectionLNc W₀ W₁ := ⟨hab, hsq⟩
  refine ⟨Additive (↥W₁ ⧸ W₀.subgroupOf W₁), inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
    { π := piQ_LNc
      ρ := ρHom_LNc h1 h0
      surj := piQ_surj_LNc
      ker := piQ_ker_LNc
      norm₁ := h1
      le := hle
      act := fun _ _ _ => rfl }

namespace SectionModule

variable {G : Type} [Group G] {Λ W₀ W₁ : Subgroup G} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] (S : SectionModule Λ W₀ W₁ W)

noncomputable def sub (C : Subgroup G) : Submodule (ZMod 2) W where
  carrier := {w | ∃ x : ↥W₁, (x : G) ∈ C ∧ toW_LNc (S.π x) = w}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, C.mul_mem hx hy, (congrArg toW_LNc (map_mul S.π x y)).trans rfl⟩
  zero_mem' := ⟨1, C.one_mem, (congrArg toW_LNc (map_one S.π)).trans toW_one_LNc⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    rcases zmod_two_cases_LNc c with rfl | rfl
    · exact ⟨1, C.one_mem, (congrArg toW_LNc (map_one S.π)).trans
        (toW_one_LNc.trans (zero_smul (ZMod 2) _).symm)⟩
    · exact ⟨x, hx, by rw [one_smul]⟩

theorem mem_sub {C : Subgroup G} {w : W} :
    w ∈ S.sub C ↔ ∃ x : ↥W₁, (x : G) ∈ C ∧ Additive.ofMul (S.π x) = w := Iff.rfl

private lemma mem_sub_LNc {C : Subgroup G} {w : W} :
    w ∈ S.sub C ↔ ∃ x : ↥W₁, (x : G) ∈ C ∧ toW_LNc (S.π x) = w := Iff.rfl

private lemma mem_sub_of_mem_LNc {C : Subgroup G} {x : ↥W₁} (hx : (x : G) ∈ C) :
    toW_LNc (S.π x) ∈ S.sub C :=
  S.mem_sub_LNc.mpr ⟨x, hx, rfl⟩

private lemma act_LNc (y : ↥Λ) (x : ↥W₁) (hx : (y : G) * (x : G) * (y : G)⁻¹ ∈ W₁) :
    S.ρ y (toW_LNc (S.π x)) = toW_LNc (S.π ⟨(y : G) * x * (y : G)⁻¹, hx⟩) :=
  S.act y x hx

theorem mem_sub_of_mem {C : Subgroup G} {x : ↥W₁} (hx : (x : G) ∈ C) :
    Additive.ofMul (S.π x) ∈ S.sub C :=
  S.mem_sub_of_mem_LNc hx

theorem sub_mono {C D : Subgroup G} (h : C ≤ D) : S.sub C ≤ S.sub D := by
  rintro w hw
  obtain ⟨x, hx, rfl⟩ := S.mem_sub_LNc.mp hw
  exact S.mem_sub_of_mem_LNc (h hx)

theorem π_injective_of_bot (h : W₀ = ⊥) : Function.Injective S.π := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxW₀ : (x : G) ∈ W₀ := (S.ker x).mp hx
  rw [h, Subgroup.mem_bot] at hxW₀
  exact Subtype.ext hxW₀

theorem sub_inv (C : Subgroup G) (y : ↥Λ) (hC : ∀ c ∈ C, (y : G) * c * (y : G)⁻¹ ∈ C) :
    ∀ w ∈ S.sub C, S.ρ y w ∈ S.sub C := by
  rintro w hw
  obtain ⟨x, hx, rfl⟩ := S.mem_sub_LNc.mp hw
  rw [S.act_LNc y x (conj_mem_W1_LNc S y x)]
  exact S.mem_sub_of_mem_LNc (x := ⟨(y : G) * x * (y : G)⁻¹, conj_mem_W1_LNc S y x⟩) (hC _ hx)

theorem irreducible_of_chief (hlt : W₀ < W₁)
    (hchief : ∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ → Λ ≤ Subgroup.normalizer (B : Set G) →
      B = W₀ ∨ B = W₁) :
    Nontrivial W ∧
      ∀ P : Submodule (ZMod 2) W, (∀ y : ↥Λ, ∀ w ∈ P, S.ρ y w ∈ P) → P = ⊥ ∨ P = ⊤ := by
  obtain ⟨g, hgW₁, hgW₀⟩ := SetLike.exists_of_lt hlt
  have hne : toW_LNc (S.π ⟨g, hgW₁⟩) ≠ 0 := by
    intro h
    exact hgW₀ ((S.ker _).mp (ofMul_eq_zero.mp h))
  refine ⟨⟨⟨_, 0, hne⟩⟩, fun P hP => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G,
      ∀ g : G, g ∈ B ↔ ∃ x : ↥W₁, (x : G) = g ∧ toW_LNc (S.π x) ∈ P :=
    ⟨{ carrier := {g | ∃ x : ↥W₁, (x : G) = g ∧ toW_LNc (S.π x) ∈ P}
       one_mem' := ⟨1, rfl, by rw [map_one]; exact P.zero_mem⟩
       mul_mem' := by
         rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
         exact ⟨x * y, by simp, by
           rw [map_mul]
           exact P.add_mem hx hy⟩
       inv_mem' := by
         rintro _ ⟨x, rfl, hx⟩
         exact ⟨x⁻¹, by simp, by
           rw [map_inv]
           exact P.neg_mem hx⟩ }, fun g => Iff.rfl⟩
  have hWB : W₀ ≤ B := by
    intro g hg
    have h1 : S.π ⟨g, hlt.le hg⟩ = 1 := (S.ker ⟨g, hlt.le hg⟩).mpr hg
    refine (hB g).mpr ⟨⟨g, hlt.le hg⟩, rfl, ?_⟩
    rw [h1]
    exact P.zero_mem
  have hBW : B ≤ W₁ := by
    intro g hg
    obtain ⟨x, rfl, -⟩ := (hB g).mp hg
    exact x.2
  have fwd : ∀ (y : ↥Λ) (g : G), g ∈ B → (y : G) * g * (y : G)⁻¹ ∈ B := by
    intro y g hg
    obtain ⟨x, rfl, hx⟩ := (hB _).mp hg
    refine (hB _).mpr ⟨⟨_, conj_mem_W1_LNc S y x⟩, rfl, ?_⟩
    have h := hP y _ hx
    rwa [S.act_LNc y x (conj_mem_W1_LNc S y x)] at h
  have hnorm : Λ ≤ Subgroup.normalizer (B : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fwd ⟨y, hy⟩ h
    · intro hyh
      have h' := fwd ⟨y⁻¹, Λ.inv_mem hy⟩ _ hyh
      simpa [mul_assoc] using h'
  rcases hchief B hWB hBW hnorm with hB0 | hB1
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨x, hx⟩ := S.surj (Multiplicative.ofAdd w)
    have hwx : toW_LNc (S.π x) = w := congrArg toW_LNc hx
    subst hwx
    have hxB : (x : G) ∈ B := (hB _).mpr ⟨x, rfl, hw⟩
    rw [hB0] at hxB
    have h1 : S.π x = 1 := (S.ker x).mpr hxB
    rw [Submodule.mem_bot]
    exact (congrArg toW_LNc h1).trans toW_one_LNc
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, hx⟩ := S.surj (Multiplicative.ofAdd w)
    have hwx : toW_LNc (S.π x) = w := congrArg toW_LNc hx
    have hxB : (x : G) ∈ B := by
      rw [hB1]
      exact x.2
    obtain ⟨x', hx'eq, hx'P⟩ := (hB _).mp hxB
    have hxx' : x' = x := Subtype.ext hx'eq
    rw [hxx'] at hx'P
    rw [← hwx]
    exact hx'P

theorem ρ_sub_self (y : ↥Λ) (x : ↥W₁) (hx : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ W₁) :
    S.ρ y (Additive.ofMul (S.π x)) - (show W from Additive.ofMul (S.π x)) =
      Additive.ofMul (S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hx⟩) := by
  have hy := conj_mem_W1_LNc S y x
  have hsplit : (⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hx⟩ : ↥W₁) =
      ⟨(y : G) * x * (y : G)⁻¹, hy⟩ * x⁻¹ :=
    Subtype.ext (by simp [mul_assoc])
  show S.ρ y (toW_LNc (S.π x)) - toW_LNc (S.π x) =
    toW_LNc (S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hx⟩)
  rw [S.act_LNc y x hy, hsplit, map_mul, map_inv, toW_mul_inv_LNc]

theorem ρ_eq_one (y : ↥Λ) (h : ∀ x : ↥W₁, (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ W₀) :
    S.ρ y = 1 := by
  refine LinearEquiv.ext fun w => ?_
  obtain ⟨x, hx⟩ := S.surj (Multiplicative.ofAdd w)
  have hw : toW_LNc (S.π x) = w := congrArg toW_LNc hx
  subst hw
  have hxW₁ : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ W₁ :=
    W₁.mul_mem (conj_mem_W1_LNc S y x) (W₁.inv_mem x.2)
  have key : S.ρ y (toW_LNc (S.π x)) - toW_LNc (S.π x) =
      toW_LNc (S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hxW₁⟩) :=
    S.ρ_sub_self y x hxW₁
  have hz : S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hxW₁⟩ = 1 := (S.ker _).mpr (h x)
  rw [hz] at key
  exact sub_eq_zero.mp key

def img (X : Subgroup G) : Subgroup (W ≃ₗ[ZMod 2] W) := (X.subgroupOf Λ).map S.ρ

theorem mem_img {X : Subgroup G} {g : W ≃ₗ[ZMod 2] W} :
    g ∈ S.img X ↔ ∃ y : ↥Λ, (y : G) ∈ X ∧ S.ρ y = g := by
  unfold img
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)

theorem img_mono {X Y : Subgroup G} (h : X ≤ Y) : S.img X ≤ S.img Y := by
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (S.mem_img).mp hg
  exact (S.mem_img).mpr ⟨y, h hy, rfl⟩

theorem img_sup {X Y : Subgroup G} (hX : X ≤ Λ) (hY : Y ≤ Λ) :
    S.img (X ⊔ Y) = S.img X ⊔ S.img Y := by
  unfold img
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

end SectionModule

end CFSG.Quasithin.H13.L829N
