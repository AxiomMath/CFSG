module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMap
public import CFSG.Quasithin.H13.U4ParRecog
public import CFSG.Quasithin.H13.U4ParOuter
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.H13.U4ParTorus
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.BA CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

local notation "Y₄" => hypSU h 2 0
local notation "U₄" => hypUnitriangular h 2 0
local notation "H₄" => hypTorus h 2 0
local notation "𝔽" => MonoidHom.range (fieldAutHom h 2 0)

theorem u4_center : ∀ y : ↥Y₄, (∀ x, y * x = x * y) → y = 1 := by
  have := isSimpleGroup_hypSU h
  obtain ⟨a, -, b, -, hab⟩ := exists_radQ_ne_comm h
  intro y hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Y₄) with h0 | h0
  · have hyc : y ∈ Subgroup.center ↥Y₄ := Subgroup.mem_center_iff.mpr fun g => (hy g).symm
    rw [h0, Subgroup.mem_bot] at hyc
    exact hyc
  · exact absurd (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a) b).symm hab

theorem u4_sylow : IsSylowTwoOf U₄ ⊤ := by
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num)
    (by norm_num)).2.1
  have h2 := isSylowTwoOf_top_of_sylow (show Sylow 2 ↥Y₄ from P)
  rwa [show ((show Sylow 2 ↥Y₄ from P) : Subgroup ↥Y₄) = U₄ from hP] at h2

theorem scalar_mul_comm {ι : Type} [Fintype ι] [DecidableEq ι] (c : Kˣ) (z : GL ι K) :
    GeneralLinearGroup.scalar ι c * z = z * GeneralLinearGroup.scalar ι c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r) _).eq

theorem u4_normal_form (α : MulAut ↥Y₄) (hα : ∀ x, α x ∈ U₄ ↔ x ∈ U₄) :
    ∃ g ∈ Subgroup.normalizer (U₄ : Set ↥Y₄), ∃ φ ∈ 𝔽, α = MulAut.conj g * φ := by
  let e := hypSUEquivPSU h
  let θ : MulAut (hypPSU h 2 0) := (e.symm.trans α).trans e
  have hθ : ∀ g, θ (hypProj h 2 0 g) = hypProj h 2 0 (α g) := fun g => by
    change e (α (e.symm (e g))) = e (α g)
    rw [e.symm_apply_apply]
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective_of_admissible h (r := 2) (ε := 0)
    (by norm_num) (by norm_num) (by norm_num) (fun h' => by omega) θ
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep h (r := 2) (ε := 0) (by norm_num)
    (by norm_num) (by norm_num) x₀
  obtain ⟨g, c, hA⟩ := exists_su_rep h hxU
  set σ : K ≃+* K := (x : SemiGL (HypIndex 2 0) K).right with hσ
  have hc : ∀ w : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) c * w *
      (GeneralLinearGroup.scalar (HypIndex 2 0) c)⁻¹ = w := fun w => by
    rw [scalar_mul_comm c w, mul_assoc, mul_inv_cancel, mul_one]
  have hform : ∀ g' : hypSU h 2 0, α g' = g * fieldAut h σ g' * g⁻¹ := by
    intro g'
    have h1 := semilinearAutHom_apply h (r := 2) (ε := 0) (by norm_num) (by norm_num) x g'
    rw [hxΦ, hx₀, hθ] at h1
    have h2 := hypProj_injective h h1
    refine Subtype.ext ?_
    rw [h2]
    change (x : SemiGL (HypIndex 2 0) K).left * glAut σ (g' : GL (HypIndex 2 0) K) *
      (x : SemiGL (HypIndex 2 0) K).left⁻¹ = ((g * fieldAut h σ g' * g⁻¹ : hypSU h 2 0) :
        GL (HypIndex 2 0) K)
    rw [hA]
    have : (GeneralLinearGroup.scalar (HypIndex 2 0) c * (g : GL (HypIndex 2 0) K)) *
        glAut σ (g' : GL (HypIndex 2 0) K) *
        (GeneralLinearGroup.scalar (HypIndex 2 0) c * (g : GL (HypIndex 2 0) K))⁻¹ =
        GeneralLinearGroup.scalar (HypIndex 2 0) c * ((g : GL (HypIndex 2 0) K) *
          glAut σ (g' : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K)⁻¹) *
          (GeneralLinearGroup.scalar (HypIndex 2 0) c)⁻¹ := by group
    rw [this, hc]
    rfl
  have hα' : α = MulAut.conj g * fieldAut h σ := MulEquiv.ext fun g' => by
    rw [hform g', MulAut.mul_apply, MulAut.conj_apply]
  refine ⟨g, ?_, fieldAut h σ, ⟨σ, rfl⟩, hα'⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e1 : (MulAut.conj g) y = α ((fieldAut h σ)⁻¹ y) := by
    rw [hα', MulAut.mul_apply, MulAut.apply_inv_self]
  have h1 := hα ((fieldAut h σ)⁻¹ y)
  have h2 := fieldAut_mem_unitriangular h σ ((fieldAut h σ)⁻¹ y)
  rw [MulAut.apply_inv_self] at h2
  rw [← MulAut.conj_apply, e1, h1]
  exact h2

theorem borelAutData_u4 : BorelAutData U₄ H₄ 𝔽 := by
  have := h.finite
  exact
    { center := u4_center h
      sylow := u4_sylow h
      H_comm := fun a ha b hb => hypTorus_comm h ha hb
      H_le := hypTorus_le_normalizer h (by norm_num) (by norm_num)
      U_inf_H := fun x hx hxH => hypUnitriangular_inf_hypTorus h hx hxH
      B_eq := fun g hg => normalizer_eq_mul h (by norm_num) (by norm_num) hg
      F_U := by
        rintro _ ⟨τ, rfl⟩ x
        exact fieldAut_mem_unitriangular h τ x
      F_H := by
        rintro _ ⟨τ, rfl⟩ x hx
        exact fieldAut_mem_torus h τ hx
      F_comm := by
        rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
        exact fieldAutHom_comm h σ τ
      F_faithful := by
        rintro _ ⟨σ, rfl⟩ hfix
        rw [eq_one_of_fixes_torus h (by norm_num) σ hfix, map_one]
      normal_form := fun α hα => u4_normal_form h α hα }

end CFSG.Quasithin.H13.Sec53F.Unit

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint

theorem lieBorelFacts_u4 : LieBorelFacts .PSU 4 := by
  intro Y _ _ f hpar hY U hU
  obtain ⟨K, _, h, ⟨e⟩⟩ := U4Par.exists_hypSU_equiv_of_lieModel hY
  have := U4Par.finite_hypSU h
  exact (Unit.borelAutData_u4 h).exists_of_equiv e.symm hU

theorem lieAutFacts_u4 : LieAutFacts .PSU 4 :=
  lieAutFacts_of_lieBorelFacts lieBorelFacts_u4

end CFSG.Quasithin.H13.Sec53F
