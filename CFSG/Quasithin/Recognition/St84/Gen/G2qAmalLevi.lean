module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalRoots
public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs
public import CFSG.LocalAnalysis.EvenBN.G2.Radicals
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.ParabolicGradedAction
import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.Quasithin.F112R.St84.G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.EvenBN.G2
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i0 i1 coords_zero coords_one mem_zero mem_one)
open CFSG.QuasithinUnique.Setup.X6 (g2Index)
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem g2N_mem_parabolicRadical_zero_iff {A B C D E F : K} :
    g2N A B C D E F ∈ parabolicRadical Tag.G2 K {i0} ↔ B = 0 := by
  constructor
  · intro h
    obtain ⟨t₁, t₂, t₃, t₄, t₅, ht⟩ := coords_zero h
    have e : g2N A B C D E F = g2N t₁ 0 t₂ t₃ t₄ t₅ := by
      rw [ht]
      simp only [g2N, pinnedX_zero, mul_one, mul_assoc]
      rfl
    exact (g2N_injective e).2.1
  · rintro rfl
    have h : g2N A (0 : K) C D E F = X g2r A * (X g2u C * (X g2v D * (X g2b E * X g2c F))) := by
      simp only [g2N, pinnedX_zero, mul_one, mul_assoc]
    rw [h]
    exact mul_mem (mem_zero (Or.inl rfl) A) (mul_mem (mem_zero (Or.inr (Or.inl rfl)) C)
      (mul_mem (mem_zero (Or.inr (Or.inr (Or.inl rfl))) D)
        (mul_mem (mem_zero (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) E)
          (mem_zero (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) F))))

theorem M_eq_parabolicRadical_zero : Model.M K = parabolicRadical Tag.G2 K {i0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨A, C, D, E, F, rfl⟩ := Model.mem_M.1 hx
    exact g2N_mem_parabolicRadical_zero_iff.2 rfl
  · intro hx
    obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_zero hx
    refine Model.mem_M.2 ⟨t₁, t₂, t₃, t₄, t₅, ?_⟩
    simp only [g2N, pinnedX_zero, mul_one, mul_assoc]
    rfl

theorem D_eq_parabolicRadical_one : Model.D K = parabolicRadical Tag.G2 K {i1} := by
  ext x
  constructor
  · intro hx
    obtain ⟨B, C, D, E, F, rfl⟩ := Model.mem_D.1 hx
    exact g2N_mem_parabolicRadical_one_iff.2 rfl
  · intro hx
    obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_one hx
    refine Model.mem_D.2 ⟨t₁, t₂, t₃, t₄, t₅, ?_⟩
    simp only [g2N, pinnedX_zero, one_mul, mul_assoc]
    rfl

theorem g2N_mul_radB (A C D E F a c d e f : K) :
    g2N A 0 C D E F * g2N a 0 c d e f =
      g2N (A + a) 0 (C + c) (D + d) (E + e + C * a ^ 2 + D * a) (F + f + C ^ 2 * a + c * D) := by
  rw [g2N_mul_coords]
  refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> ring

theorem exists_coords_M (x : ↥(Model.M K)) :
    ∃ v : Fin 5 → K, (x : ModGL Tag.G2 K) = g2N (v 0) 0 (v 1) (v 2) (v 3) (v 4) := by
  obtain ⟨A, C, D, E, F, h⟩ := Model.mem_M.1 x.2
  exact ⟨![A, C, D, E, F], h⟩

@[expose] def coordsM (x : ↥(Model.M K)) : Fin 5 → K := (exists_coords_M x).choose

theorem coordsM_spec (x : ↥(Model.M K)) :
    (x : ModGL Tag.G2 K) =
      g2N (coordsM x 0) 0 (coordsM x 1) (coordsM x 2) (coordsM x 3) (coordsM x 4) :=
  (exists_coords_M x).choose_spec

theorem coordsM_eq {x : ↥(Model.M K)} {A C D E F : K}
    (h : (x : ModGL Tag.G2 K) = g2N A 0 C D E F) :
    coordsM x 0 = A ∧ coordsM x 1 = C ∧ coordsM x 2 = D ∧ coordsM x 3 = E ∧
      coordsM x 4 = F := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := g2N_injective ((coordsM_spec x).symm.trans h)
  exact ⟨h1, h3, h4, h5, h6⟩

@[expose] def radBCoord : ↥(Model.M K) →* Multiplicative (Fin 3 → K) where
  toFun x := Multiplicative.ofAdd ![coordsM x 2, coordsM x 1 ^ 2, coordsM x 0 ^ 2]
  map_one' := by
    obtain ⟨h1, h2, h3, -, -⟩ := coordsM_eq (x := 1) (A := (0 : K)) (C := 0) (D := 0) (E := 0)
      (F := 0) (by rw [OneMemClass.coe_one, g2N_zero])
    rw [h1, h2, h3, ← ofAdd_zero]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' x y := by
    obtain ⟨E', F', hxy⟩ : ∃ E' F' : K, ((x * y : ↥(Model.M K)) : ModGL Tag.G2 K) =
        g2N (coordsM x 0 + coordsM y 0) 0 (coordsM x 1 + coordsM y 1)
          (coordsM x 2 + coordsM y 2) E' F' :=
      ⟨_, _, by rw [Subgroup.coe_mul, coordsM_spec x, coordsM_spec y, g2N_mul_radB]⟩
    obtain ⟨h1, h2, h3, -, -⟩ := coordsM_eq hxy
    rw [h1, h2, h3, ← ofAdd_add]
    congr 1
    ext i
    fin_cases i <;> simp [CharTwo.add_sq]

theorem radBCoord_apply {x : ↥(Model.M K)} {A C D E F : K}
    (h : (x : ModGL Tag.G2 K) = g2N A 0 C D E F) :
    Multiplicative.toAdd (radBCoord x) = ![D, C ^ 2, A ^ 2] := by
  obtain ⟨h1, h2, h3, -, -⟩ := coordsM_eq h
  change ![coordsM x 2, coordsM x 1 ^ 2, coordsM x 0 ^ 2] = _
  rw [h1, h2, h3]

theorem radBCoord_mk (A C D E F : K) (h : g2N A 0 C D E F ∈ Model.M K) :
    Multiplicative.toAdd (radBCoord ⟨g2N A 0 C D E F, h⟩) = ![D, C ^ 2, A ^ 2] :=
  radBCoord_apply (x := ⟨g2N A 0 C D E F, h⟩) (A := A) (C := C) (D := D) (E := E) (F := F) rfl

theorem ker_radBCoord : (radBCoord (K := K)).ker = (Model.Y K).subgroupOf (Model.M K) := by
  ext x
  have hx := coordsM_spec x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hx, Model.g2N_mem_Y_iff,
    ← toAdd_eq_zero, radBCoord_apply hx]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.zero_apply,
      Matrix.head_cons, Matrix.tail_cons, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff] at h0 h1 h2
    exact ⟨h2, rfl, h1, h0⟩
  · rintro ⟨h0, -, h1, h2⟩
    rw [h0, h1, h2]
    ext i
    fin_cases i <;> simp

theorem radBCoord_surjective [Finite K] : Function.Surjective (radBCoord (K := K)) := by
  intro w
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' ((Multiplicative.toAdd w) 1)
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' ((Multiplicative.toAdd w) 2)
  refine ⟨⟨g2N a 0 c (Multiplicative.toAdd w 0) 0 0, Model.mem_M.2 ⟨_, _, _, _, _, rfl⟩⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [radBCoord_mk]
  ext i
  fin_cases i <;> simp [hc, ha, sq]

instance normal_Y_subgroupOf_M : ((Model.Y K).subgroupOf (Model.M K)).Normal := by
  rw [← ker_radBCoord]
  exact MonoidHom.normal_ker _

@[expose] def radBQuot [Finite K] :
    ↥(Model.M K) ⧸ (Model.Y K).subgroupOf (Model.M K) ≃* Multiplicative (Fin 3 → K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_radBCoord.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ radBCoord_surjective)

theorem radBQuot_mk [Finite K] (x : ↥(Model.M K)) :
    radBQuot (QuotientGroup.mk x) = radBCoord x :=
  rfl

theorem exists_coords_Y (z : ↥(Model.Y K)) :
    ∃ v : Fin 2 → K, (z : ModGL Tag.G2 K) = g2N 0 0 0 0 (v 1) (v 0) := by
  obtain ⟨E, F, h⟩ := Model.mem_Y.1 z.2
  exact ⟨![F, E], h⟩

@[expose] def coordsY (z : ↥(Model.Y K)) : Fin 2 → K := (exists_coords_Y z).choose

theorem coordsY_spec (z : ↥(Model.Y K)) :
    (z : ModGL Tag.G2 K) = g2N 0 0 0 0 (coordsY z 1) (coordsY z 0) :=
  (exists_coords_Y z).choose_spec

theorem coordsY_eq {z : ↥(Model.Y K)} {E F : K} (h : (z : ModGL Tag.G2 K) = g2N 0 0 0 0 E F) :
    coordsY z = ![F, E] := by
  obtain ⟨-, -, -, -, h5, h6⟩ := g2N_injective ((coordsY_spec z).symm.trans h)
  ext i
  fin_cases i
  · exact h6
  · exact h5

theorem coordsY_mk (E F : K) (h : g2N 0 0 0 0 E F ∈ Model.Y K) :
    coordsY ⟨g2N 0 0 0 0 E F, h⟩ = ![F, E] :=
  coordsY_eq (z := ⟨g2N 0 0 0 0 E F, h⟩) (E := E) (F := F) rfl

@[expose] def zBCoord : ↥(Model.Y K) ≃* Multiplicative (Fin 2 → K) where
  toFun z := Multiplicative.ofAdd (coordsY z)
  invFun v := ⟨g2N 0 0 0 0 (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 0),
    Model.mem_Y.2 ⟨Multiplicative.toAdd v 1, Multiplicative.toAdd v 0, rfl⟩⟩
  left_inv z := Subtype.ext (coordsY_spec z).symm
  right_inv v := by
    apply Multiplicative.toAdd.injective
    change coordsY ⟨g2N 0 0 0 0 (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 0),
      Model.mem_Y.2 ⟨Multiplicative.toAdd v 1, Multiplicative.toAdd v 0, rfl⟩⟩ =
        Multiplicative.toAdd v
    rw [coordsY_mk]
    ext i
    fin_cases i <;> rfl
  map_mul' z w := by
    have hzw : ((z * w : ↥(Model.Y K)) : ModGL Tag.G2 K) =
        g2N 0 0 0 0 (coordsY z 1 + coordsY w 1) (coordsY z 0 + coordsY w 0) := by
      rw [Subgroup.coe_mul, coordsY_spec z, coordsY_spec w, g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    change Multiplicative.ofAdd (coordsY (z * w)) =
      Multiplicative.ofAdd (coordsY z) * Multiplicative.ofAdd (coordsY w)
    rw [coordsY_eq hzw, ← ofAdd_add]
    congr 1
    ext i
    fin_cases i <;> simp

theorem zBCoord_apply {z : ↥(Model.Y K)} {E F : K}
    (h : (z : ModGL Tag.G2 K) = g2N 0 0 0 0 E F) :
    Multiplicative.toAdd (zBCoord z) = ![F, E] :=
  coordsY_eq h

@[expose] def torusJ4Hom : Kˣ →* ModGL Tag.G2 K := dTHom.comp (MonoidHom.inr Kˣ Kˣ)

theorem torusJ4Hom_apply (t : Kˣ) : torusJ4Hom t = dT (K := K) 1 t :=
  rfl

theorem range_torusJ4Hom : (torusJ4Hom (K := K)).range = Model.J₄ K := by
  ext h
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨dT_mem_torusGroup 1 t, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    have e := dT_conj_a (1 : Kˣ) t c
    rw [Units.val_one, one_mul] at e
    exact (mul_inv_eq_iff_eq_mul.1 e).symm
  · rintro ⟨hT, hc⟩
    obtain ⟨s, t, rfl⟩ := mem_torusGroup_iff.1 hT
    have h1 := Subgroup.mem_centralizer_iff.1 hc (X g2a 1) (mem_rootSubgroup.2 ⟨1, rfl⟩)
    have h2 : dT s t * X g2a 1 * (dT s t)⁻¹ = X g2a 1 := by
      rw [← h1, mul_inv_cancel_right]
    rw [dT_conj_a, pinnedX_a_eq_g2N, pinnedX_a_eq_g2N] at h2
    have hs : (s : K) = 1 := by
      have e := (g2N_injective h2).2.1
      rwa [mul_one] at e
    obtain rfl : s = 1 := Units.ext (by rw [hs, Units.val_one])
    exact ⟨t, rfl⟩

abbrev rhoLeviB : SL2 K →* ModGL Tag.G2 K := simpleRootSL2 Tag.G2 K g2ia

theorem rhoLeviB_uSL (s : K) : rhoLeviB (uSL s) = X g2a s := by
  rw [simpleRootSL2_uSL, xUnit_g2ia]

theorem rhoLeviB_vSL (s : K) : rhoLeviB (vSL s) = X g2na s := by
  rw [simpleRootSL2_vSL, yUnit_g2ia]

theorem range_rhoLeviB : (rhoLeviB (K := K)).range = Model.leviB K :=
  range_simpleRootSL2 g2ia

theorem commute_rhoLeviB_torusJ4Hom (g : SL2 K) (t : Kˣ) :
    Commute (rhoLeviB g) (torusJ4Hom t) := by
  have ht : torusJ4Hom t ∈ Model.J₄ K := by
    rw [← range_torusJ4Hom]
    exact ⟨t, rfl⟩
  have hg : rhoLeviB g ∈ Model.leviB K := by
    rw [← range_rhoLeviB]
    exact ⟨g, rfl⟩
  exact Subgroup.mem_centralizer_iff.1 (Model.J₄_le_centralizer_leviB ht) _ hg

@[expose] def leviBHom : SL2 K × Kˣ →* ModGL Tag.G2 K :=
  MonoidHom.noncommCoprod rhoLeviB torusJ4Hom commute_rhoLeviB_torusJ4Hom

theorem leviBHom_apply (p : SL2 K × Kˣ) : leviBHom p = rhoLeviB p.1 * torusJ4Hom p.2 :=
  rfl

theorem leviBHom_uSL (s : K) : leviBHom (uSL s, 1) = X g2a s := by
  rw [leviBHom_apply, rhoLeviB_uSL, map_one, mul_one]

theorem range_leviBHom : (leviBHom (K := K)).range = Model.leviB K ⊔ Model.J₄ K := by
  rw [leviBHom, MonoidHom.noncommCoprod_range, range_rhoLeviB, range_torusJ4Hom]

theorem leviBHom_injective : Function.Injective (leviBHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, t⟩ h
  rw [leviBHom_apply] at h
  have hmem : rhoLeviB g ∈ Model.leviB K ⊓ Model.J₄ K := by
    refine ⟨by rw [← range_rhoLeviB]; exact ⟨g, rfl⟩, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h]
    exact (Model.J₄ K).inv_mem (by rw [← range_torusJ4Hom]; exact ⟨t, rfl⟩)
  rw [Model.leviB_inf_J₄, Subgroup.mem_bot] at hmem
  have hg : g = 1 :=
    CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo g2ia
      (hmem.trans (map_one _).symm)
  rw [hmem, one_mul, torusJ4Hom_apply] at h
  have ht : t = 1 := (dT_eq_one_iff.1 h).2
  rw [hg, ht]
  rfl

@[expose] def leviBEquiv : SL2 K × Kˣ ≃* ↥(Model.leviB K ⊔ Model.J₄ K) :=
  (MonoidHom.ofInjective leviBHom_injective).trans (MulEquiv.subgroupCongr range_leviBHom)

theorem conj_a_radB (s A C D E F : K) : ∃ E' F' : K,
    X g2a s * g2N A 0 C D E F * (X g2a s)⁻¹ = g2N A 0 (C + s * A) (D + s * A ^ 2) E' F' := by
  rw [pinnedX_inv_eq, conj_a]
  exact ⟨_, _, g2N_eq_g2N rfl rfl (by ring) (by ring) rfl rfl⟩

theorem conj_na_radB (s A C D E F : K) : ∃ E' F' : K,
    X g2na s * g2N A 0 C D E F * (X g2na s)⁻¹ = g2N (A + s * C) 0 C (D + s * C ^ 2) E' F' := by
  rw [Model.conj_na_eq, Model.wb_conj_M, conj_a, Model.wb_conj_M]
  exact ⟨_, _, g2N_eq_g2N (by ring) rfl rfl (by ring) rfl rfl⟩

theorem rhoLeviB_conj_radB (g : SL2 K) (A C D E F : K) : ∃ A' C' D' E' F' : K,
    rhoLeviB g * g2N A 0 C D E F * (rhoLeviB g)⁻¹ = g2N A' 0 C' D' E' F' ∧
      ![D', C' ^ 2, A' ^ 2] = (sp4RadMat g).mulVec ![D, C ^ 2, A ^ 2] := by
  revert A C D E F
  induction g using Model.SL2_induction_uv with
  | h1 =>
    intro A C D E F
    exact ⟨A, C, D, E, F, by simp, by rw [sp4RadMat_one, Matrix.one_mulVec]⟩
  | hu s g ih =>
    intro A C D E F
    obtain ⟨A₁, C₁, D₁, E₁, F₁, h₁, e₁⟩ := ih A C D E F
    obtain ⟨E₂, F₂, h₂⟩ := conj_a_radB s A₁ C₁ D₁ E₁ F₁
    refine ⟨A₁, C₁ + s * A₁, D₁ + s * A₁ ^ 2, E₂, F₂, ?_, ?_⟩
    · rw [map_mul, show rhoLeviB (uSL s) * rhoLeviB g * g2N A 0 C D E F *
          (rhoLeviB (uSL s) * rhoLeviB g)⁻¹ = rhoLeviB (uSL s) *
          (rhoLeviB g * g2N A 0 C D E F * (rhoLeviB g)⁻¹) * (rhoLeviB (uSL s))⁻¹ by group,
        h₁, rhoLeviB_uSL, h₂]
    · rw [sp4RadMat_mul, ← Matrix.mulVec_mulVec, ← e₁, sp4RadMat_mulVec]
      ext i
      fin_cases i <;> simp [coe_uSL, CharTwo.add_sq, mul_pow] <;> ring
  | hv s g ih =>
    intro A C D E F
    obtain ⟨A₁, C₁, D₁, E₁, F₁, h₁, e₁⟩ := ih A C D E F
    obtain ⟨E₂, F₂, h₂⟩ := conj_na_radB s A₁ C₁ D₁ E₁ F₁
    refine ⟨A₁ + s * C₁, C₁, D₁ + s * C₁ ^ 2, E₂, F₂, ?_, ?_⟩
    · rw [map_mul, show rhoLeviB (vSL s) * rhoLeviB g * g2N A 0 C D E F *
          (rhoLeviB (vSL s) * rhoLeviB g)⁻¹ = rhoLeviB (vSL s) *
          (rhoLeviB g * g2N A 0 C D E F * (rhoLeviB g)⁻¹) * (rhoLeviB (vSL s))⁻¹ by group,
        h₁, rhoLeviB_vSL, h₂]
    · rw [sp4RadMat_mul, ← Matrix.mulVec_mulVec, ← e₁, sp4RadMat_mulVec]
      ext i
      fin_cases i <;> simp [coe_vSL, CharTwo.add_sq, mul_pow] <;> ring

theorem torusJ4Hom_conj_g2N (t : Kˣ) (A C D E F : K) :
    torusJ4Hom t * g2N A 0 C D E F * (torusJ4Hom t)⁻¹ =
      g2N (t * A) 0 (t * C) (t ^ 2 * D) (t ^ 3 * E) (t ^ 3 * F) := by
  rw [torusJ4Hom_apply, dT_conj_g2N, Units.val_one]
  refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> ring

theorem radBCoord_conj_leviBHom (p : SL2 K × Kˣ) (x y : ↥(Model.M K))
    (h : (y : ModGL Tag.G2 K) = leviBHom p * x * (leviBHom p)⁻¹) :
    Multiplicative.toAdd (radBCoord y) =
      ((p.2 : K) ^ 2) • (sp4RadMat p.1).mulVec (Multiplicative.toAdd (radBCoord x)) := by
  obtain ⟨A, C, D, E, F, hx⟩ := Model.mem_M.1 x.2
  obtain ⟨A', C', D', E', F', h₁, e₁⟩ := rhoLeviB_conj_radB p.1 (p.2 * A) (p.2 * C)
    (p.2 ^ 2 * D) (p.2 ^ 3 * E) (p.2 ^ 3 * F)
  have hy : (y : ModGL Tag.G2 K) = g2N A' 0 C' D' E' F' := by
    rw [h, leviBHom_apply, hx, ← h₁, ← torusJ4Hom_conj_g2N]
    group
  rw [radBCoord_apply hy, radBCoord_apply hx, e₁, ← Matrix.mulVec_smul]
  congr 1
  ext i
  fin_cases i <;> simp [mul_pow]

theorem torusJ4Hom_conj_Y (t : Kˣ) (E F : K) :
    torusJ4Hom t * g2N 0 0 0 0 E F * (torusJ4Hom t)⁻¹ = g2N 0 0 0 0 (t ^ 3 * E) (t ^ 3 * F) := by
  rw [torusJ4Hom_conj_g2N]
  simp only [mul_zero]

theorem zBCoord_conj_leviBHom (p : SL2 K × Kˣ) (z w : ↥(Model.Y K))
    (h : (w : ModGL Tag.G2 K) = leviBHom p * z * (leviBHom p)⁻¹) :
    Multiplicative.toAdd (zBCoord w) =
      ((p.2 : K) ^ 3) • (p.1 : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (zBCoord z)) := by
  obtain ⟨E, F, hz⟩ := Model.mem_Y.1 z.2
  have hw : (w : ModGL Tag.G2 K) = g2N 0 0 0 0
      ((Matrix.mulVec (p.1 : Matrix (Fin 2) (Fin 2) K) ![(p.2 : K) ^ 3 * F, (p.2 : K) ^ 3 * E]) 1)
      ((Matrix.mulVec (p.1 : Matrix (Fin 2) (Fin 2) K)
        ![(p.2 : K) ^ 3 * F, (p.2 : K) ^ 3 * E]) 0) := by
    rw [← Model.conj_Y_of_uv rhoLeviB_uSL rhoLeviB_vSL p.1, h, leviBHom_apply, hz]
    have e : g2N 0 0 0 0 (![(p.2 : K) ^ 3 * F, (p.2 : K) ^ 3 * E] 1)
        (![(p.2 : K) ^ 3 * F, (p.2 : K) ^ 3 * E] 0) =
        torusJ4Hom p.2 * g2N 0 0 0 0 E F * (torusJ4Hom p.2)⁻¹ := by
      rw [torusJ4Hom_conj_Y]
      rfl
    rw [e]
    group
  rw [zBCoord_apply hw, zBCoord_apply hz]
  have hv : ![(p.2 : K) ^ 3 * F, (p.2 : K) ^ 3 * E] = ((p.2 : K) ^ 3) • ![F, E] := by
    ext i
    fin_cases i <;> simp
  rw [hv, Matrix.mulVec_smul]
  ext i
  fin_cases i <;> rfl

theorem leviBHom_conj_mem_Y (p : SL2 K × Kˣ) {z : ModGL Tag.G2 K} (hz : z ∈ Model.Y K) :
    leviBHom p * z * (leviBHom p)⁻¹ ∈ Model.Y K := by
  obtain ⟨E, F, rfl⟩ := Model.mem_Y.1 hz
  rw [leviBHom_apply, show rhoLeviB p.1 * torusJ4Hom p.2 * g2N 0 0 0 0 E F *
      (rhoLeviB p.1 * torusJ4Hom p.2)⁻¹ = rhoLeviB p.1 *
      (torusJ4Hom p.2 * g2N 0 0 0 0 E F * (torusJ4Hom p.2)⁻¹) * (rhoLeviB p.1)⁻¹ by group,
    torusJ4Hom_conj_Y]
  exact Model.mem_Y.2 ⟨_, _, Model.conj_Y_of_uv rhoLeviB_uSL rhoLeviB_vSL p.1
    ![(p.2 : K) ^ 3 * F, (p.2 : K) ^ 3 * E]⟩

theorem zBCoord_sq (x : ↥(Model.M K)) (hx : (x : ModGL Tag.G2 K) ^ 2 ∈ Model.Y K) {x₀ b₀ b₁ : K}
    (h : Multiplicative.toAdd (radBCoord x) = ![x₀, b₀ ^ 2, b₁ ^ 2]) :
    Multiplicative.toAdd (zBCoord ⟨(x : ModGL Tag.G2 K) ^ 2, hx⟩) =
      (x₀ + b₀ * b₁) • ![b₀, b₁] := by
  obtain ⟨A, C, D, E, F, hxe⟩ := Model.mem_M.1 x.2
  rw [radBCoord_apply hxe] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  rw [CharTwo.sq_inj] at h1 h2
  subst h0 h1 h2
  have hsq : (x : ModGL Tag.G2 K) ^ 2 =
      g2N 0 0 0 0 (C * A ^ 2 + D * A) (C ^ 2 * A + C * D) := by
    rw [sq, hxe, g2N_mul_radB]
    refine g2N_eq_g2N ?_ rfl ?_ ?_ ?_ ?_ <;> char2_ring
  rw [zBCoord_apply (z := ⟨_, hx⟩) hsq]
  ext i
  fin_cases i <;> simp <;> ring

theorem leviB_sup_J₄_le_parabolicLevi :
    Model.leviB K ⊔ Model.J₄ K ≤ parabolicLevi Tag.G2 K {i0} := by
  refine sup_le ((Subgroup.closure_le _).2 ?_) (inf_le_left.trans (torusGroup_le_parabolicLevi _))
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_parabolicLevi (show g2ia ∈ ({i0} : Set (Fin Tag.G2.rank)) from rfl) c
  · exact yUnit_mem_parabolicLevi (show g2ia ∈ ({i0} : Set (Fin Tag.G2.rank)) from rfl) c

theorem parabolicLevi_zero_eq [Finite K] :
    parabolicLevi Tag.G2 K {i0} = Model.leviB K ⊔ Model.J₄ K := by
  refine le_antisymm (sup_le Model.J_le_leviB_sup_J₄ ((Subgroup.closure_le _).2 ?_))
    leviB_sup_J₄_le_parabolicLevi
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · obtain rfl := Set.mem_singleton_iff.1 hj
    exact Subgroup.mem_sup_left (xUnit_mem_g2RankOne g2ia c)
  · obtain rfl := Set.mem_singleton_iff.1 hj
    exact Subgroup.mem_sup_left (yUnit_mem_g2RankOne g2ia c)

theorem disjoint_M_leviB_sup_J₄ : Disjoint (Model.M K) (Model.leviB K ⊔ Model.J₄ K) := by
  rw [disjoint_iff, M_eq_parabolicRadical_zero, ← le_bot_iff,
    ← parabolicRadical_inf_parabolicLevi {i0}]
  exact inf_le_inf_left _ leviB_sup_J₄_le_parabolicLevi

theorem M_sup_leviB_sup_J₄ [Finite K] :
    Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K) = parabolicSubgroup Tag.G2 K {i0} := by
  rw [M_eq_parabolicRadical_zero, ← parabolicLevi_zero_eq, parabolicRadical_sup_parabolicLevi]

theorem leviB_sup_J₄_le_normalizer_M :
    Model.leviB K ⊔ Model.J₄ K ≤ Subgroup.normalizer (Model.M K : Set (ModGL Tag.G2 K)) :=
  sup_le Model.leviB_le_normalizer_M fun _ hh =>
    Model.borelGroup_le_normalizer_M (Subgroup.mem_sup_left hh.1)

theorem mem_M_sup_leviB_sup_J₄_iff [Finite K] {g : ModGL Tag.G2 K} :
    g ∈ Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K) ↔
      g ∈ parabolicSubgroup Tag.G2 K {g2Index 0} := by
  rw [M_sup_leviB_sup_J₄, g2Index_zero]

@[expose] def parBEquiv [Finite K] :
    ↥(Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K)) ≃* ↥(g2ParB K) where
  toFun x := ⟨⟨x, parabolicSubgroup_le_adjointGroup Tag.G2 K _
      (mem_M_sup_leviB_sup_J₄_iff.1 x.2)⟩,
    Subgroup.mem_subgroupOf.2 (mem_M_sup_leviB_sup_J₄_iff.1 x.2)⟩
  invFun y := ⟨y, mem_M_sup_leviB_sup_J₄_iff.2 (Subgroup.mem_subgroupOf.1 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem mul_comm_of_mem_Y_of_mem_M {z x : ModGL Tag.G2 K} (hz : z ∈ Model.Y K)
    (hx : x ∈ Model.M K) : z * x = x * z := by
  rw [← Model.M_inf_centralizer_M] at hz
  exact (Subgroup.mem_centralizer_iff.1 hz.2 x hx).symm

theorem sq_eq_one_of_mem_Y {z : ModGL Tag.G2 K} (hz : z ∈ Model.Y K) : z ^ 2 = 1 := by
  obtain ⟨E, F, rfl⟩ := Model.mem_Y.1 hz
  rw [sq, g2N_mul_coords, ← g2N_zero]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem sq_mem_Y_of_mem_M {x : ModGL Tag.G2 K} (hx : x ∈ Model.M K) : x ^ 2 ∈ Model.Y K := by
  rw [← Model.closure_sq_M]
  exact Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem mem_D_iff_forall_commutator [Finite K] (hK : 3 ≤ Nat.card K) {x : ModGL Tag.G2 K}
    (hx : x ∈ Model.S K) :
    x ∈ Model.D K ↔ ∀ y₁ ∈ Model.S K, ∀ y₂ ∈ Model.S K, ∀ s ∈ Model.S K,
      ⁅x, ⁅y₁, y₂⁆⁆ * s = s * ⁅x, ⁅y₁, y₂⁆⁆ := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := Model.mem_S.1 hx
  constructor
  · intro hD y₁ hy₁ y₂ hy₂ s hs
    obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, rfl⟩ := Model.mem_S.1 hy₁
    obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, rfl⟩ := Model.mem_S.1 hy₂
    obtain rfl : A = 0 := Model.g2N_mem_D_iff.1 hD
    rw [g2N_commutator_coords a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂, g2N_commutator_coords]
    refine (Model.commute_of_mem_U (Model.g2N_mem_U_iff.2 ⟨?_, ?_, ?_, ?_, ?_⟩) hs).symm <;> ring
  · intro h
    rw [Model.g2N_mem_D_iff]
    by_contra hA
    obtain ⟨t, ht0, htA⟩ := exists_ne_ne hK 0 A
    have hy₁ : g2N (0 : K) 1 0 0 0 0 ∈ Model.S K := Model.mem_S.2 ⟨_, _, _, _, _, _, rfl⟩
    have hy₂ : g2N t (0 : K) 0 0 0 0 ∈ Model.S K := Model.mem_S.2 ⟨_, _, _, _, _, _, rfl⟩
    have hU : ⁅g2N A B C D E F, ⁅g2N (0 : K) 1 0 0 0 0, g2N t 0 0 0 0 0⁆⁆ ∈ Model.U K := by
      rw [← Model.S_inf_centralizer_S]
      refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun s hs => (h _ hy₁ _ hy₂ s hs).symm⟩
      rw [g2N_commutator_coords, g2N_commutator_coords]
      exact Model.mem_S.2 ⟨_, _, _, _, _, _, rfl⟩
    rw [g2N_commutator_coords 0 1 0 0 0 0 t 0 0 0 0 0, g2N_commutator_coords] at hU
    obtain ⟨-, -, -, -, h5⟩ := Model.g2N_mem_U_iff.1 hU
    have h5' : A * t * (A + t) = 0 := by linear_combination h5
    rcases mul_eq_zero.1 h5' with h6 | h6
    · rcases mul_eq_zero.1 h6 with h7 | h7
      · exact hA h7
      · exact ht0 h7
    · apply htA
      rw [← sub_eq_zero, CharTwo.sub_eq_add, add_comm]
      exact h6

end CFSG.Quasithin.F112R.St84.G2q

end
