module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Mathlib

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups
open Matrix
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.X7
open CFSG.GorensteinWalter
open CFSG.Timmesfeld.ARS.NaturalModule

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def IsNatSumModule (ρ : Representation (ZMod 2) SL(2, F) W) : Prop :=
  ∃ (k : ℕ) (φ : W ≃+ (Fin k → Fin 2 → F)), ∀ g w i,
    φ (ρ g w) i = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ φ w i

namespace NatSumModel

noncomputable scoped instance instModuleZMod2Pi (k : ℕ) :
    Module (ZMod 2) (Fin k → Fin 2 → F) :=
  AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    ext i j
    exact CharTwo.add_self_eq_zero (x i j))

scoped instance instSMulCommClassPi (k : ℕ) :
    SMulCommClass SL(2, F) (ZMod 2) (Fin k → Fin 2 → F) where
  smul_comm g c x :=
    ZMod.map_smul (DistribMulAction.toAddMonoidEnd SL(2, F) (Fin k → Fin 2 → F) g) c x

@[expose] noncomputable def natSumRep (F : Type) [Field F] [CharP F 2] (k : ℕ) :
    Representation (ZMod 2) SL(2, F) (Fin k → Fin 2 → F) :=
  Representation.ofDistribMulAction (ZMod 2) SL(2, F) (Fin k → Fin 2 → F)

theorem natSumRep_apply (k : ℕ) (g : SL(2, F)) (v : Fin k → Fin 2 → F) :
    natSumRep F k g v = g • v := rfl

@[simp] theorem natSumRep_mul_apply (k : ℕ) (a b : SL(2, F)) (u : Fin k → Fin 2 → F) :
    natSumRep F k a (natSumRep F k b u) = natSumRep F k (a * b) u := by
  change ((natSumRep F k a) * (natSumRep F k b)) u = natSumRep F k (a * b) u
  rw [← map_mul]

private theorem sl2_smul_smul (g : SL(2, F)) (c : F) (x : Fin 2 → F) :
    g • (c • x) = c • (g • x) := by
  rw [smul_eq_mulVec', smul_eq_mulVec', Matrix.mulVec_smul]

theorem natSumRep_smul (k : ℕ) (a : F) (g : SL(2, F)) (w : Fin k → Fin 2 → F) :
    a • (natSumRep F k g w) = natSumRep F k g (a • w) := by
  ext i j
  rw [natSumRep_apply, Pi.smul_apply, natSumRep_apply, Pi.smul_apply]
  exact congrFun (sl2_smul_smul g a (w i)).symm j

theorem second_eq_zero_of_fixed_rootGroup (k : ℕ)
    {U : Submodule (ZMod 2) (Fin k → Fin 2 → F)}
    (hU : U ≤ fixedSub (natSumRep F k) (upperRootGroup F))
    {u : Fin k → Fin 2 → F} (hu : u ∈ U) (i : Fin k) : u i 1 = 0 := by
  have h1 : uElt (1 : F) ∈ upperRootGroup F :=
    (mem_upperRootGroup_iff _).mpr ⟨1, rfl⟩
  have hfix : natSumRep F k (uElt 1) u = u := mem_fixedSub.mp (hU hu) _ h1
  have h2 := congrFun (congrFun hfix i) 0
  rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec', coe_uElt] at h2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
  have h2' : u i 0 + u i 1 = u i 0 + 0 := by simpa using h2
  exact add_left_cancel h2'

theorem exists_coeff_e1 {v : Fin 2 → F} (hv : v 1 ≠ 0) (x : Fin 2 → F) :
    ∃ a b : F, x = a • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)) + b • v := by
  refine ⟨x 0 + (x 1 * (v 1)⁻¹) * v 0, x 1 * (v 1)⁻¹, ?_⟩
  ext i
  fin_cases i
  · simp [add_assoc, CharTwo.add_self_eq_zero]
  · simp [mul_assoc, inv_mul_cancel₀ hv]

theorem natSumRep_action_eq (k : ℕ) {g h : SL(2, F)} {a b : F}
    (hcoeff : g • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)) =
      a • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)) +
        b • (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))))
    {u : Fin k → Fin 2 → F} (hu : ∀ i, u i 1 = 0) :
    natSumRep F k g u = a • u + b • natSumRep F k h u := by
  ext i j
  have hui : u i = (u i 0) • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)) := by
    ext l
    fin_cases l <;> simp [hu i]
  rw [natSumRep_apply, Pi.smul_apply, hui]
  simp only [natSumRep_apply, Pi.add_apply, Pi.smul_apply]
  rw [hui, sl2_smul_smul, hcoeff, sl2_smul_smul]
  simp only [smul_add, smul_smul, Pi.add_apply, Pi.smul_apply]
  fin_cases j <;>
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, Pi.add_apply, Pi.smul_apply, hu i, mul_comm]

theorem natSumRep_action_h_eq (k : ℕ) {g h : SL(2, F)} {a b : F}
    (hcoeff : g • (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))) =
      a • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)) +
        b • (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))))
    {u : Fin k → Fin 2 → F} (hu : ∀ i, u i 1 = 0) :
    natSumRep F k g (natSumRep F k h u) = a • u + b • natSumRep F k h u := by
  ext i j
  have hui0 : u i = (u i 0) • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)) := by
    ext l
    fin_cases l <;> simp [hu i]
  have hui : natSumRep F k h u i =
      (u i 0) • (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))) := by
    rw [natSumRep_apply, Pi.smul_apply]
    calc
      h • (u i) = h • ((u i 0) • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))) := by
        conv_lhs => rw [hui0]
      _ = (u i 0) • (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))) :=
            smul_comm h (u i 0) ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))
  rw [natSumRep_apply, Pi.smul_apply, hui]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [sl2_smul_smul, hcoeff, hui]
  simp only [smul_add, smul_smul, Pi.add_apply, Pi.smul_apply]
  fin_cases j <;>
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, Pi.add_apply, Pi.smul_apply, hu i, mul_comm]

theorem smul_mem_of_mem_rootGroup (k : ℕ)
    {U : Submodule (ZMod 2) (Fin k → Fin 2 → F)}
    (hU : U ≤ fixedSub (natSumRep F k) (upperRootGroup F))
    (hUN : ∀ g ∈ Subgroup.normalizer (upperRootGroup F : Set (SL(2, F))),
      ∀ u ∈ U, natSumRep F k g u ∈ U)
    {a : F} {u : Fin k → Fin 2 → F} (hu : u ∈ U) : a • u ∈ U := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · let c : Fˣ := Units.mk0 a ha
    have hdiag : diagElt c ∈ Subgroup.normalizer (upperRootGroup F : Set (SL(2, F))) := by
      rw [normalizer_upperRootGroup, mem_borelSubgroup_iff]
      exact ⟨c, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [diagElt]⟩
    have hmem := hUN (diagElt c) hdiag u hu
    rw [natSumRep_apply] at hmem
    have hu1 : ∀ i, u i 1 = 0 := second_eq_zero_of_fixed_rootGroup k hU hu
    have hc : (c : F) = a := Units.val_mk0 ha
    have hdiag_eq : diagElt c • u = a • u := by
      ext i j
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mulVec', diagElt_mulVec]
      fin_cases j <;> simp [hu1 i, hc]
    rwa [hdiag_eq] at hmem

theorem upperRootGroup_sup_map_invariant (k : ℕ)
    {U : Submodule (ZMod 2) (Fin k → Fin 2 → F)}
    (hU : U ≤ fixedSub (natSumRep F k) (upperRootGroup F))
    (hUN : ∀ g ∈ Subgroup.normalizer (upperRootGroup F : Set (SL(2, F))),
      ∀ u ∈ U, natSumRep F k g u ∈ U)
    {h : SL(2, F)} (hh : h ∉ Subgroup.normalizer (upperRootGroup F : Set (SL(2, F)))) :
    ∀ g, ∀ w ∈ U ⊔ U.map (natSumRep F k h),
      natSumRep F k g w ∈ U ⊔ U.map (natSumRep F k h) := by
  intro g w hw
  rw [Submodule.mem_sup] at hw
  obtain ⟨u, hu, v, hv, hw⟩ := hw
  rw [Submodule.mem_map] at hv
  obtain ⟨u', hu', rfl⟩ := hv
  have hu1 : ∀ i, u i 1 = 0 := second_eq_zero_of_fixed_rootGroup k hU hu
  have hu'1 : ∀ i, u' i 1 = 0 := second_eq_zero_of_fixed_rootGroup k hU hu'
  have hh10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro h0
    exact hh (by
      rw [normalizer_upperRootGroup]
      exact (sl2_mem_stabilizer_infinity_iff h).mpr h0)
  have hv1 : (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))) 1 ≠ 0 := by
    rw [smul_eq_mulVec']
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using hh10
  obtain ⟨a, b, hab⟩ := exists_coeff_e1 hv1 (g • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F)))
  obtain ⟨c, d, hcd⟩ :=
    exists_coeff_e1 hv1 (g • (h • ((Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F))))
  have hgu : natSumRep F k g u = a • u + b • natSumRep F k h u :=
    natSumRep_action_eq k hab hu1
  have hghu' : natSumRep F k g (natSumRep F k h u') =
      c • u' + d • natSumRep F k h u' :=
    natSumRep_action_h_eq k hcd hu'1
  have hdecomp : (a • u + b • natSumRep F k h u) +
      (c • u' + d • natSumRep F k h u') =
      (a • u + c • u') + natSumRep F k h (b • u + d • u') := by
    rw [map_add, ← natSumRep_smul, ← natSumRep_smul]
    abel
  rw [← hw, map_add, hgu, hghu', hdecomp]
  refine Submodule.add_mem (U ⊔ U.map (natSumRep F k h)) ?_ ?_
  · exact Submodule.mem_sup_left (U.add_mem (smul_mem_of_mem_rootGroup k hU hUN hu)
      (smul_mem_of_mem_rootGroup k hU hUN hu'))
  · exact Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨b • u + d • u',
      U.add_mem (smul_mem_of_mem_rootGroup k hU hUN hu)
        (smul_mem_of_mem_rootGroup k hU hUN hu'), rfl⟩)

private theorem sup_map_invariant_of_conj (k : ℕ)
    {U U₁ : Submodule (ZMod 2) (Fin k → Fin 2 → F)} {x h h₁ : SL(2, F)}
    (hUmap : U₁ = U.map (natSumRep F k x⁻¹)) (hhmap : h₁ = x⁻¹ * h * x)
    (hmain : ∀ g, ∀ w ∈ U₁ ⊔ U₁.map (natSumRep F k h₁),
      natSumRep F k g w ∈ U₁ ⊔ U₁.map (natSumRep F k h₁)) :
    ∀ g, ∀ w ∈ U ⊔ U.map (natSumRep F k h),
      natSumRep F k g w ∈ U ⊔ U.map (natSumRep F k h) := by
  have hcomp₁ : (natSumRep F k x).comp (natSumRep F k x⁻¹) = LinearMap.id := by
    ext u i j
    change natSumRep F k x (natSumRep F k x⁻¹ u) i j = u i j
    rw [natSumRep_mul_apply]
    simp
  have hcomp₂ : ((natSumRep F k x).comp (natSumRep F k h₁)).comp
      (natSumRep F k x⁻¹) = natSumRep F k h := by
    ext u i j
    change natSumRep F k x (natSumRep F k h₁ (natSumRep F k x⁻¹ u)) i j =
      natSumRep F k h u i j
    rw [natSumRep_mul_apply, natSumRep_mul_apply]
    congr 1
    rw [hhmap]
    group
  have hUx : U₁.map (natSumRep F k x) = U := by
    rw [hUmap, ← Submodule.map_comp, hcomp₁, Submodule.map_id]
  have hUh : U.map (natSumRep F k h) =
      (U₁.map (natSumRep F k h₁)).map (natSumRep F k x) := by
    rw [hUmap, ← Submodule.map_comp, ← Submodule.map_comp, hcomp₂]
  have hM : U ⊔ U.map (natSumRep F k h) =
      (U₁ ⊔ U₁.map (natSumRep F k h₁)).map (natSumRep F k x) := by
    rw [Submodule.map_sup, hUx, ← hUh]
  intro g w hw
  rw [hM] at hw ⊢
  rw [Submodule.mem_map] at hw
  obtain ⟨w₁, hw₁, rfl⟩ := hw
  rw [Submodule.mem_map]
  refine ⟨natSumRep F k (x⁻¹ * g * x) w₁, hmain _ _ hw₁, ?_⟩
  simp only [natSumRep_mul_apply]
  congr 1
  group

theorem natSumRep_sup_map_invariant (k : ℕ) {A : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    {U : Submodule (ZMod 2) (Fin k → Fin 2 → F)}
    (hU : U ≤ fixedSub (natSumRep F k) A)
    (hUN : ∀ g ∈ Subgroup.normalizer (A : Set (SL(2, F))), ∀ u ∈ U, natSumRep F k g u ∈ U)
    {h : SL(2, F)} (hh : h ∉ Subgroup.normalizer (A : Set (SL(2, F)))) :
    ∀ g, ∀ w ∈ U ⊔ U.map (natSumRep F k h),
      natSumRep F k g w ∈ U ⊔ U.map (natSumRep F k h) := by
  have hcard : Nat.card A = Nat.card F := by simpa using hA
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hcard
  have hx' : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ upperRootGroup F :=
    fun g => by simpa [upperRootGroup] using hx g
  let U₁ : Submodule (ZMod 2) (Fin k → Fin 2 → F) := U.map (natSumRep F k x⁻¹)
  let h₁ : SL(2, F) := x⁻¹ * h * x
  have hAeq : A = (upperRootGroup F).map (MulAut.conj x).toMonoidHom := by
    ext g
    rw [Subgroup.mem_map]
    refine ⟨fun hg => ⟨x⁻¹ * g * x, (hx' g).mp hg,
      by simp [MulAut.conj_apply, mul_assoc]⟩, ?_⟩
    rintro ⟨r, hr, rfl⟩
    exact (hx' _).mpr (by simpa [MulAut.conj_apply, mul_assoc] using hr)
  have hNA : Subgroup.normalizer (A : Set (SL(2, F))) =
      (Subgroup.normalizer (upperRootGroup F : Set (SL(2, F)))).map
        (MulAut.conj x).toMonoidHom := by
    rw [hAeq]
    exact (Subgroup.map_normalizer_eq_of_bijective (upperRootGroup F)
      (MulAut.conj x).bijective).symm
  have hmap : A.map (MulAut.conj x⁻¹).toMonoidHom = upperRootGroup F := by
    have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (SL(2, F)) := by
      refine MonoidHom.ext fun g => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [hAeq, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hU₁ : U₁ ≤ fixedSub (natSumRep F k) (upperRootGroup F) := by
    calc U₁ = U.map (natSumRep F k x⁻¹) := rfl
      _ ≤ (fixedSub (natSumRep F k) A).map (natSumRep F k x⁻¹) := Submodule.map_mono hU
      _ = fixedSub (natSumRep F k) (A.map (MulAut.conj x⁻¹).toMonoidHom) :=
            (fixedSub_map_conj (natSumRep F k) x⁻¹ A).symm
      _ = fixedSub (natSumRep F k) (upperRootGroup F) := by rw [hmap]
  have hUN₁ : ∀ g ∈ Subgroup.normalizer (upperRootGroup F : Set (SL(2, F))),
      ∀ u ∈ U₁, natSumRep F k g u ∈ U₁ := by
    intro g hg u hu
    rw [Submodule.mem_map] at hu ⊢
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    refine ⟨natSumRep F k (x * g * x⁻¹) u₀, ?_, ?_⟩
    · apply hUN (x * g * x⁻¹)
      · rw [hNA, Subgroup.mem_map]
        exact ⟨g, hg, by simp [MulAut.conj_apply]⟩
      · exact hu₀
    · simp only [natSumRep_mul_apply]; congr 1; group
  have hh₁ : h₁ ∉ Subgroup.normalizer (upperRootGroup F : Set (SL(2, F))) := by
    intro hh1
    apply hh
    rw [hNA, Subgroup.mem_map]
    exact ⟨h₁, hh1, by simp [h₁, MulAut.conj_apply, mul_assoc]⟩
  exact sup_map_invariant_of_conj (k := k) (U := U) (U₁ := U₁) (x := x) (h := h) (h₁ := h₁)
    rfl rfl (upperRootGroup_sup_map_invariant k hU₁ hUN₁ hh₁)

end NatSumModel

open NatSumModel in
theorem sup_map_invariant_of_isNatSumModule
    (ρ : Representation (ZMod 2) SL(2, F) W) (hρ : IsNatSumModule ρ)
    {A : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = Fintype.card F)
    {U : Submodule (ZMod 2) W} (hUA : U ≤ fixedSub ρ A)
    (hUN : ∀ g ∈ Subgroup.normalizer (A : Set (SL(2, F))), ∀ u ∈ U, ρ g u ∈ U)
    {h : SL(2, F)} (hh : h ∉ Subgroup.normalizer (A : Set (SL(2, F)))) :
    ∀ g, ∀ w ∈ U ⊔ U.map (ρ h), ρ g w ∈ U ⊔ U.map (ρ h) := by
  obtain ⟨k, φ, hφ⟩ := hρ
  let φl : W →ₗ[ZMod 2] (Fin k → Fin 2 → F) :=
    AddMonoidHom.toZModLinearMap 2 (φ : W →+ (Fin k → Fin 2 → F))
  let e := natSumRep F k
  have hφe : ∀ g w, φ (ρ g w) = e g (φ w) := by
    intro g w
    ext i
    rw [hφ g w i, natSumRep_apply, Pi.smul_apply, smul_eq_mulVec']
  have hU₀ : U.map φl ≤ fixedSub e A := by
    intro u hu
    rw [Submodule.mem_map] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    rw [mem_fixedSub]
    intro a ha
    change e a (φ u₀) = φ u₀
    rw [← hφe a u₀]
    exact congrArg φ (mem_fixedSub.mp (hUA hu₀) a ha)
  have hUN₀ : ∀ g ∈ Subgroup.normalizer (A : Set (SL(2, F))),
      ∀ u ∈ U.map φl, e g u ∈ U.map φl := by
    intro g hg u hu
    rw [Submodule.mem_map] at hu ⊢
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    exact ⟨ρ g u₀, hUN g hg u₀ hu₀, hφe g u₀⟩
  have hmain := natSumRep_sup_map_invariant k hA2 hA hU₀ hUN₀ hh
  have hMφ : (U ⊔ U.map (ρ h)).map φl = U.map φl ⊔ (U.map φl).map (e h) := by
    rw [Submodule.map_sup]
    congr 1
    calc
      (U.map (ρ h)).map φl = U.map (φl.comp (ρ h)) :=
        (Submodule.map_comp (ρ h) φl U).symm
      _ = U.map ((e h).comp φl) := by
        congr 1
        ext u i j
        simpa [φl] using congrFun (congrFun (hφe h u) i) j
      _ = (U.map φl).map (e h) := Submodule.map_comp φl (e h) U
  intro g w hw
  have hwφ : φl w ∈ U.map φl ⊔ (U.map φl).map (e h) := by
    rw [← hMφ]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hmainw := hmain g (φl w) hwφ
  have hφg : φl (ρ g w) = e g (φl w) := hφe g w
  have hmem : φl (ρ g w) ∈ (U ⊔ U.map (ρ h)).map φl := by
    rw [hMφ, hφg]
    exact hmainw
  rw [Submodule.mem_map] at hmem
  obtain ⟨v, hv, hveq⟩ := hmem
  have hvw : v = ρ g w := φ.injective (by simpa [φl] using hveq)
  simpa [hvw] using hv

end CFSG.RankThree.GF2n.Tim81.Sec2
