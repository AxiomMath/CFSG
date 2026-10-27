module

public import CFSG.Quasithin.MS93.M15Statement
public import CFSG.Quasithin.Background.JonesParshallSp4
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit
open scoped Matrix

variable {F : Type} [Field F]

theorem sp4Quad_add (x y : Ix → F) :
    sp4Quad F (x + y) = sp4Quad F x + sp4Quad F y + bil x y := by
  simp only [sp4Quad, bil, Pi.add_apply]
  ring

abbrev spMat (g : ↥(StatedSp 2 F)) : Matrix Ix Ix F :=
  ((g : Matrix.GeneralLinearGroup Ix F) : Matrix Ix Ix F)

theorem omega5Act_toAdd (g : ↥(StatedSp 2 F)) (y : Multiplicative ((Ix → F) × F)) :
    Multiplicative.toAdd (omega5Act F g y) =
      (spMat g *ᵥ (Multiplicative.toAdd y).1, (Multiplicative.toAdd y).2 +
        sp4Quad F (Multiplicative.toAdd y).1 + sp4Quad F (spMat g *ᵥ (Multiplicative.toAdd y).1)) :=
  rfl

variable [CharP F 2]

theorem statedSp_eq_sp4' : StatedSp 2 F = sp4 F := by
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    ext i j
    rw [Matrix.neg_apply]
    exact CharTwo.neg_eq _
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      spJ F := by
    rw [hneg]
    rfl
  unfold StatedSp
  rw [hJ]
  exact Subgroup.closure_eq (sp4 F)

theorem bil_statedSp (g : ↥(StatedSp 2 F)) (x y : Ix → F) :
    bil (spMat g *ᵥ x) (spMat g *ᵥ y) = bil x y := by
  have hg : (g : Matrix.GeneralLinearGroup Ix F) ∈ sp4 F := by
    rw [← statedSp_eq_sp4']
    exact g.2
  exact bil_smul hg x y

theorem quadDiff_add (g : ↥(StatedSp 2 F)) (x y : Ix → F) :
    sp4Quad F (x + y) + sp4Quad F (spMat g *ᵥ (x + y)) =
      (sp4Quad F x + sp4Quad F (spMat g *ᵥ x)) + (sp4Quad F y + sp4Quad F (spMat g *ᵥ y)) := by
  rw [Matrix.mulVec_add, sp4Quad_add, sp4Quad_add, bil_statedSp]
  have h2 : bil x y + bil x y = 0 := CharTwo.add_self_eq_zero _
  linear_combination h2

theorem omega5Act_mul (g : ↥(StatedSp 2 F)) (y z : Multiplicative ((Ix → F) × F)) :
    omega5Act F g (y * z) = omega5Act F g y * omega5Act F g z := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, omega5Act_toAdd, omega5Act_toAdd, omega5Act_toAdd, toAdd_mul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    exact Matrix.mulVec_add _ _ _
  simp only [Prod.fst_add, Prod.snd_add]
  have := quadDiff_add g (Multiplicative.toAdd y).1 (Multiplicative.toAdd z).1
  linear_combination this

theorem omega5Act_one (y : Multiplicative ((Ix → F) × F)) : omega5Act F 1 y = y := by
  apply Multiplicative.toAdd.injective
  rw [omega5Act_toAdd]
  have h1 : spMat (1 : ↥(StatedSp 2 F)) = 1 := rfl
  rw [h1, Matrix.one_mulVec]
  refine Prod.ext rfl ?_
  show (Multiplicative.toAdd y).2 + sp4Quad F (Multiplicative.toAdd y).1 +
    sp4Quad F (Multiplicative.toAdd y).1 = (Multiplicative.toAdd y).2
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem omega5Act_mul_act (g h : ↥(StatedSp 2 F)) (y : Multiplicative ((Ix → F) × F)) :
    omega5Act F (g * h) y = omega5Act F g (omega5Act F h y) := by
  apply Multiplicative.toAdd.injective
  rw [omega5Act_toAdd, omega5Act_toAdd, omega5Act_toAdd]
  have h1 : spMat (g * h) = spMat g * spMat h := rfl
  rw [h1, ← Matrix.mulVec_mulVec]
  refine Prod.ext rfl ?_
  simp only
  have h2 : sp4Quad F (spMat h *ᵥ (Multiplicative.toAdd y).1) +
      sp4Quad F (spMat h *ᵥ (Multiplicative.toAdd y).1) = 0 := CharTwo.add_self_eq_zero _
  linear_combination -h2

omit [CharP F 2] in
theorem omega5Act_rad (g : ↥(StatedSp 2 F)) {y : Multiplicative ((Ix → F) × F)}
    (hy : y ∈ omega5Rad F) : omega5Act F g y = y := by
  have hy' : (Multiplicative.toAdd y).1 = 0 := hy
  apply Multiplicative.toAdd.injective
  rw [omega5Act_toAdd, hy', Matrix.mulVec_zero]
  refine Prod.ext hy'.symm ?_
  simp [sp4Quad]

theorem omega5_isActionModel {Z : Subgroup (Multiplicative ((Ix → F) × F))}
    (hZ : Z ≤ omega5Rad F) : (FFModel.omega5 F Z).IsActionModel where
  act_mul := omega5Act_mul
  act_one := omega5Act_one
  act_mul_act := omega5Act_mul_act
  sec_inv := fun _ _ _ => Subgroup.mem_top _
  ker_inv := fun γ m hm => by
    show omega5Act F γ m ∈ Z
    rw [omega5Act_rad γ (hZ hm)]
    exact hm
  ker_le := le_top

@[expose] def omega5Proj :
    ↥(⊤ : Subgroup (Multiplicative ((Ix → F) × F))) →* ↥(⊤ : Subgroup (Multiplicative (Ix → F))) where
  toFun m := ⟨Multiplicative.ofAdd (Multiplicative.toAdd (m : Multiplicative ((Ix → F) × F))).1,
    Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [CharP F 2] in
theorem omega5Proj_surjective : Function.Surjective (omega5Proj (F := F)) := by
  intro x
  refine ⟨⟨Multiplicative.ofAdd (Multiplicative.toAdd (x : Multiplicative (Ix → F)), 0),
    Subgroup.mem_top _⟩, ?_⟩
  rfl

theorem omega5_realizesVia_of_nat {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : ↥(StatedSp 2 F) →* ↥H}
    (h : (FFModel.nat (StatedSp 2 F)).RealizesVia H U Z π) :
    (FFModel.omega5 F (omega5Rad F)).RealizesVia H U Z (π.comp (MonoidHom.id _)) :=
  FFModel.RealizesVia.of_surjHom (omega5_isActionModel le_rfl) h (MonoidHom.id _)
    Function.surjective_id omega5Proj omega5Proj_surjective (fun _ _ _ => rfl)
    (fun _ => ⟨fun h1 => congrArg Multiplicative.toAdd (Subgroup.mem_bot.1 h1),
      fun h1 => Subgroup.mem_bot.2 (congrArg Multiplicative.ofAdd h1)⟩)

@[expose] def toStated (g : ↥(sp4 F)) : ↥(StatedSp 2 F) :=
  ⟨g, by rw [statedSp_eq_sp4']; exact g.2⟩

theorem spMat_toStated (g : ↥(sp4 F)) (x : Ix → F) :
    spMat (toStated g) *ᵥ x = (g : GL Ix F) • x := rfl

omit [CharP F 2] in
theorem omega5_comm (g : ↥(StatedSp 2 F)) (x : Ix → F) (s : F) :
    omega5Act F g (Multiplicative.ofAdd (x, s)) * (Multiplicative.ofAdd (x, s))⁻¹ =
      Multiplicative.ofAdd (spMat g *ᵥ x - x, sp4Quad F x + sp4Quad F (spMat g *ᵥ x)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd, toAdd_ofAdd]
  refine Prod.ext (by simp [sub_eq_add_neg]) ?_
  simp only [Prod.snd_add, Prod.snd_neg]
  ring

omit [CharP F 2] in
theorem sp4Quad_vec4 (a b c d : F) : sp4Quad F (vec4 a b c d) = a * c + b * d := rfl

theorem omega5_gen {β : F} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (y : Multiplicative ((Ix → F) × F)) :
    y ∈ Subgroup.closure {x | ∃ (g : ↥(StatedSp 2 F)) (z : Multiplicative ((Ix → F) × F)),
      x = omega5Act F g z * z⁻¹} := by
  set G := Subgroup.closure {x | ∃ (g : ↥(StatedSp 2 F)) (z : Multiplicative ((Ix → F) × F)),
      x = omega5Act F g z * z⁻¹} with hG
  have hc : ∀ (g : ↥(StatedSp 2 F)) (x : Ix → F),
      Multiplicative.ofAdd (spMat g *ᵥ x - x, sp4Quad F x + sp4Quad F (spMat g *ᵥ x)) ∈ G :=
    fun g x => by
      rw [← omega5_comm g x 0]
      exact Subgroup.subset_closure ⟨g, _, rfl⟩
  have h1 : ∀ t c : F, Multiplicative.ofAdd ((vec4 (t * c) 0 0 0 : Ix → F), t * c * c) ∈ G := by
    intro t c
    have := hc (toStated (spX t 0 0)) (vec4 0 0 c 0)
    rw [spMat_toStated, spX_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h2 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 t 0 0 : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spX 0 0 t)) (vec4 0 0 0 1)
    rw [spMat_toStated, spX_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h3 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 0 t 0 : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spY t 0 0)) (vec4 1 0 0 0)
    rw [spMat_toStated, spY_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h4 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 0 0 t : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spY 0 0 t)) (vec4 0 1 0 0)
    rw [spMat_toStated, spY_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have hβ1' : (1 : F) - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ1)
  have hR : ∀ r : F, Multiplicative.ofAdd ((0 : Ix → F), r) ∈ G := by
    intro r
    set t := r / (1 - β) with ht
    have ha := h1 t 1
    have hb := h1 (t / β) β
    have e : Multiplicative.ofAdd ((0 : Ix → F), r) =
        Multiplicative.ofAdd ((vec4 (t * 1) 0 0 0 : Ix → F), t * 1 * 1) *
          (Multiplicative.ofAdd ((vec4 (t / β * β) 0 0 0 : Ix → F), t / β * β * β))⁻¹ := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.fst_neg]
        rw [div_mul_cancel₀ t hβ0, mul_one, ← sub_eq_add_neg, sub_self]
      · simp only [Prod.snd_add, Prod.snd_neg]
        rw [ht]
        field_simp
        ring
    rw [e]
    exact G.mul_mem ha (G.inv_mem hb)
  obtain ⟨⟨v, s⟩, rfl⟩ := Multiplicative.ofAdd.surjective y
  rw [vec4_eta v]
  set a := v (Sum.inl 0)
  set b := v (Sum.inl 1)
  set c := v (Sum.inr 0)
  set d := v (Sum.inr 1)
  have e : Multiplicative.ofAdd ((vec4 a b c d : Ix → F), s) =
      Multiplicative.ofAdd ((vec4 (a * 1) 0 0 0 : Ix → F), a * 1 * 1) *
        Multiplicative.ofAdd ((vec4 0 b 0 0 : Ix → F), b) *
        Multiplicative.ofAdd ((vec4 0 0 c 0 : Ix → F), c) *
        Multiplicative.ofAdd ((vec4 0 0 0 d : Ix → F), d) *
        Multiplicative.ofAdd ((0 : Ix → F), s - a - b - c - d) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, vec4_add, mul_one, add_zero, zero_add]
    · simp only [Prod.snd_add]
      ring
  rw [e]
  exact G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem (h1 a 1) (h2 b)) (h3 c)) (h4 d)) (hR _)

end CFSG.Quasithin.MS93
