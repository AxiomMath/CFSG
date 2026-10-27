module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.AppendixH.H14.H142Conj
public import CFSG.Quasithin.AppendixH.H14.H142Group
public import CFSG.Quasithin.AppendixH.Common.OctadTwoCore
public import CFSG.Quasithin.AppendixH.Common.OctadCentralizer
public import CFSG.Quasithin.AppendixH.Common.OctadOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.H16TwoM22

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.ASVolI.AppH CFSG.Monster.Code CFSG.Open

theorem natHom_surjective (n : ℕ) : Function.Surjective (natHom n (ZMod 2)) := by
  intro γ
  let g : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
  { toFun := fun v => Multiplicative.toAdd (γ (Multiplicative.ofAdd v))
    map_zero' := by simp
    map_add' := fun v w => by rw [ofAdd_add, map_mul, toAdd_mul] }
  let f : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    @AddMonoidHom.toZModLinearMap 2 (Fin n → ZMod 2) (Fin n → ZMod 2) _ _
      (Pi.Function.module (Fin n) (ZMod 2) (ZMod 2))
      (Pi.Function.module (Fin n) (ZMod 2) (ZMod 2)) g
  let g' : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
  { toFun := fun v => Multiplicative.toAdd (γ.symm (Multiplicative.ofAdd v))
    map_zero' := by simp
    map_add' := fun v w => by rw [ofAdd_add, map_mul, toAdd_mul] }
  let f' : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    @AddMonoidHom.toZModLinearMap 2 (Fin n → ZMod 2) (Fin n → ZMod 2) _ _
      (Pi.Function.module (Fin n) (ZMod 2) (ZMod 2))
      (Pi.Function.module (Fin n) (ZMod 2) (ZMod 2)) g'
  have hf : ∀ v, f v = Multiplicative.toAdd (γ (Multiplicative.ofAdd v)) := fun v => rfl
  have hf' : ∀ v, f' v = Multiplicative.toAdd (γ.symm (Multiplicative.ofAdd v)) := fun v => rfl
  have hcomp : f ∘ₗ f' = 1 := by
    refine LinearMap.ext fun v => ?_
    change f (f' v) = v
    rw [hf, hf']
    simp
  have hcomp' : f' ∘ₗ f = 1 := by
    refine LinearMap.ext fun v => ?_
    change f' (f v) = v
    rw [hf, hf']
    simp
  have h1 : LinearMap.toMatrix' f * LinearMap.toMatrix' f' = 1 := by
    rw [← LinearMap.toMatrix'_comp, hcomp]
    change LinearMap.toMatrix' (LinearMap.id : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) = 1
    rw [LinearMap.toMatrix'_id]
  have h2 : LinearMap.toMatrix' f' * LinearMap.toMatrix' f = 1 := by
    rw [← LinearMap.toMatrix'_comp, hcomp']
    change LinearMap.toMatrix' (LinearMap.id : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) = 1
    rw [LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' f, LinearMap.toMatrix' f', h1, h2⟩, ?_⟩
  apply MulEquiv.ext
  intro v
  show Multiplicative.ofAdd ((LinearMap.toMatrix' f).mulVec (Multiplicative.toAdd v)) = γ v
  rw [LinearMap.toMatrix'_mulVec, hf]
  simp

theorem natHom_injective (n : ℕ) : Function.Injective (natHom n (ZMod 2)) := by
  rw [injective_iff_map_eq_one]
  intro a h
  apply Units.ext
  ext i j
  have h1 := congrArg (fun φ : MulAut (Multiplicative (Fin n → ZMod 2)) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1))) i) h
  simp only [natHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    toAdd_ofAdd, MulAut.one_apply, Matrix.mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1

theorem card_GL_four : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field]
  rw [Fin.prod_univ_four]
  norm_num [ZMod.card]

theorem exists_mulEquiv_elemAbelian_two {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hE : IsElemAbelian 2 E) (n : ℕ) (hcard : Nat.card ↥E = 2 ^ n) :
    Nonempty (↥E ≃* Multiplicative (Fin n → ZMod 2)) := by
  classical
  letI : CommGroup ↥E := @IsMulCommutative.instCommGroup _ _ hE.1
  have hsq : ∀ y : ↥E, y ^ 2 = 1 := fun y => Subtype.ext (hE.2 (y : G) y.2)
  haveI : Module (ZMod 2) (Additive ↥E) :=
    AddCommGroup.zmodModule fun x => by
      apply Additive.toMul.injective
      simpa [toMul_nsmul] using hsq (Additive.toMul x)
  have hcardAdd : Nat.card (Additive ↥E) = 2 ^ n := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  have hfin : Module.finrank (ZMod 2) (Additive ↥E) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥E)
    rw [Nat.card_zmod, hcardAdd] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b : Module.Basis (Fin n) (ZMod 2) (Additive ↥E) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥E) hfin
  exact ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv⟩

theorem octad_conjIsoModel {O : Finset (Fin 24)}
    (hO : IsOctad O) :
    ConjIsoModel (MY M24g O) (KY M24g O) (Multiplicative (Fin 4 → ZMod 2))
      ((natSub 4 (ZMod 2) ⊤ : Subgroup (MulAut (Multiplicative (Fin 4 → ZMod 2)))) :
        Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) := by
  have hK_eq : KY M24g O = octFix O := by
    unfold KY MY
    exact pCoreOf_octStab hO
  unfold ConjIsoModel
  rw [hK_eq]
  obtain ⟨φ⟩ := exists_mulEquiv_elemAbelian_two (G := S24) (octFix O) (isElemAbelian_octFix hO) 4
    (by rw [card_octFix hO]; norm_num)
  have hKG : octFix O ≤ MY M24g O := octFix_le_octStab O
  have hGK : ∀ g ∈ MY M24g O, ∀ k ∈ octFix O, g * k * g⁻¹ ∈ octFix O := by
    intro g hg k hk
    have hk' : k ∈ pCoreOf 2 (MY M24g O) := by
      have : k ∈ KY M24g O := by rwa [hK_eq]
      exact this
    have hmem : g * k * g⁻¹ ∈ pCoreOf 2 (MY M24g O) :=
      (Subgroup.normal_subgroupOf_iff (pCoreOf_le 2 (MY M24g O))).mp
        (normal_subgroupOf_pCoreOf 2 (MY M24g O)) k g hk' hg
    have hmem' : g * k * g⁻¹ ∈ KY M24g O := hmem
    rwa [hK_eq] at hmem'
  have h3 : ∀ g ∈ MY M24g O, (∀ k ∈ octFix O, g * k = k * g) → g ∈ octFix O := by
    intro g hg hcomm
    have hcent : g ∈ Subgroup.centralizer (octFix O : Set S24) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm k hk).symm
    have hmem : g ∈ octStab O ⊓ Subgroup.centralizer (octFix O : Set S24) := ⟨hg, hcent⟩
    rw [octStab_inf_centralizer_octFix hO] at hmem
    exact hmem
  let π : ↥(MY M24g O) →* MulAut (Multiplicative (Fin 4 → ZMod 2)) := actHom hGK φ
  have h1 : ∀ g : ↥(MY M24g O), π g ∈ natSub 4 (ZMod 2) ⊤ := by
    intro g
    obtain ⟨a, ha⟩ := natHom_surjective 4 (π g)
    rw [natSub, Subgroup.mem_map]
    exact ⟨a, Subgroup.mem_top a, ha⟩
  have hconj_range : ConjIso (MY M24g O) (octFix O) (Multiplicative (Fin 4 → ZMod 2))
      (π.range : Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) φ π :=
    conjIso_of_actHom hKG hGK φ (π.range : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))
      (fun g => MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      (fun γ hγ => MonoidHom.mem_range.mp hγ) h3
  have hker : π.ker = (octFix O).subgroupOf (MY M24g O) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hconj_range.2.2.2.1 g
  have hcardKer : Nat.card π.ker = 16 := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv).trans (card_octFix hO)
  have hcardM : Nat.card ↥(MY M24g O) = 322560 := card_octStab hO
  have hcardRange : Nat.card π.range = 20160 := by
    have h := Subgroup.card_ker_mul_card_range π
    rw [hcardKer, hcardM] at h
    omega
  have hNatSub : Nat.card (natSub 4 (ZMod 2) ⊤) = 20160 := by
    rw [natSub, Subgroup.card_map_of_injective (natHom_injective 4), Subgroup.card_top]
    exact card_GL_four
  have hrange_le : π.range ≤ natSub 4 (ZMod 2) ⊤ := by
    rintro γ ⟨g, rfl⟩
    exact h1 g
  have heq : π.range = natSub 4 (ZMod 2) ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge hrange_le ?_
    rw [hcardRange, hNatSub]
  have h2 : ∀ γ ∈ natSub 4 (ZMod 2) ⊤, ∃ g : ↥(MY M24g O), π g = γ := by
    intro γ hγ
    rw [← heq] at hγ
    exact MonoidHom.mem_range.mp hγ
  exact ⟨φ, π, conjIso_of_actHom hKG hGK φ
    ((natSub 4 (ZMod 2) ⊤ : Subgroup (MulAut (Multiplicative (Fin 4 → ZMod 2)))) :
      Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) h1 h2 h3⟩

end CFSG.Quasithin.AppendixH.H14
