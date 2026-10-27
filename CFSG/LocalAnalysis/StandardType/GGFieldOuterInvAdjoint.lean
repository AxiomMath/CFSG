module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterNormalForm
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangDatum
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangSetup
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvSolvable
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.ExcMaxToral
open CFSG.Open (IsElemAbelian)

private theorem ggPA5_frobeniusEquiv_pow_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (n : ℕ) (c : K) : (frobeniusEquiv K 2 ^ n) c = c ^ 2 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, frobeniusEquiv_def, ← pow_mul, ← pow_succ]

private theorem ggPA5_normalForm
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hF4 : τ = .F4 → Even f)
    (α : MulAut (adjointGroup τ K)) (hα2 : α * α = 1)
    (hout : ∀ c : adjointGroup τ K, α ≠ MulAut.conj c) :
    ∃ (e : ℕ) (σ : K ≃+* K) (g : adjointGroup τ K), f = 2 * e ∧
      (∀ c, σ c = c ^ 2 ^ e) ∧ α = MulAut.conj g * entrywiseAdjointAut τ σ := by
  rcases hτ with rfl | rfl | rfl
  · exact ggFieldOuterNormalForm_E78 hf hK (Or.inl rfl) α hα2 hout
  · exact ggFieldOuterNormalForm_E78 hf hK (Or.inr rfl) α hα2 hout
  · obtain ⟨e, g, hfe, hαeq⟩ := ggFieldOuterNormalForm_F4 hf (hF4 rfl) hK α hα2 hout
    refine ⟨e, frobeniusEquiv K 2 ^ e, g, hfe,
      fun c => ggPA5_frobeniusEquiv_pow_apply e c, ?_⟩
    rw [hαeq]
    congr 1
    exact (CFSG.LieType.Chevalley.entrywiseAdjointAut_eq_finiteFrobeniusAut_pow
      (fun c => ggPA5_frobeniusEquiv_pow_apply e c)).symm

private theorem ggPA5_baseChange_normalForm
    {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L] [ExpChar L 2]
    {e : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {g : adjointGroup τ K} {α : MulAut (adjointGroup τ K)}
    (hαeq : α = MulAut.conj g * entrywiseAdjointAut τ σ) :
    ∀ c : adjointGroup τ K,
      baseChangeGL (algebraMap K L) ((α c : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K L) (g : ModGL τ K) *
        Units.map (entrywiseHom (iterateFrobenius L 2 e))
          (baseChangeGL (algebraMap K L) (c : ModGL τ K)) *
        (baseChangeGL (algebraMap K L) (g : ModGL τ K))⁻¹ := by
  intro c
  have hcomp : (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L 2 e).comp (algebraMap K L) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change (algebraMap K L) (σ x) = (iterateFrobenius L 2 e) ((algebraMap K L) x)
    rw [hσ, map_pow, iterateFrobenius_def]
  have key : baseChangeGL (algebraMap K L)
        (Units.map (entrywiseHom σ.toRingHom) (c : ModGL τ K)) =
      Units.map (entrywiseHom (iterateFrobenius L 2 e))
        (baseChangeGL (algebraMap K L) (c : ModGL τ K)) := by
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have h1 : ((α c : adjointGroup τ K) : ModGL τ K) =
      (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (c : ModGL τ K) *
        (g : ModGL τ K)⁻¹ := by
    rw [hαeq]
    simp only [MulAut.mul_apply, MulAut.conj_apply, coe_entrywiseAdjointAut, Subgroup.coe_mul,
      Subgroup.coe_inv]
  rw [h1, map_mul, map_mul, map_inv, key]

private theorem ggPA5_false_of_isComponentOf_of_solvable {G : Type} [Group G] {X L : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hL : CFSG.Assembly.IsComponentOf L X) : False := by
  haveI : Group.IsSolvable ↥X := hX
  have hLsol : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hL.1)
      (Subgroup.inclusion_injective hL.1)
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  haveI := hL.2.2.2
  haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  exact Group.IsPerfect.not_isSolvable ↥L hLsol

theorem ggFieldOuterInvModel_adjointGroup
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hF4 : τ = .F4 → Even f ∧ Nat.card K ≠ 4) :
    GGFieldOuterInvModel (adjointGroup τ K) := by
  intro p b α hp hp2 hb1 hbp ⟨E, hE, hbE, h4, hmax⟩ hα2 hout hαb ⟨L₁, hL₁⟩ hfix
  obtain ⟨e, σ, g, hfe, hσ, hαeq⟩ :=
    ggPA5_normalForm hτ hf K hK (fun h => (hF4 h).1) α hα2 hout
  have he1 : 1 ≤ e := by omega
  have hq : ∃ e', Nat.card K = 4 ^ e' := by
    refine ⟨e, ?_⟩
    rw [hK, hfe, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  obtain ⟨Fr, hFr, w, g0, hg0C, hg0, htor⟩ :=
    exists_langDatum_of_maxElem (τ := τ) hτ K hq hp hp2 E hE h4 hmax
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, hfe]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨S, a, ι, hSD, hrootE, ha, hinj, hirange, hιc, hιconj⟩ :=
    exists_langSetup_conj (τ := τ) hτ K hK4 hp hp2 hFr hg0C hg0 b hbp (htor b hbE)
  have hdT : rootDiagUnit τ a ∈ S.D.torus := (S.E_le hrootE).1
  have hBC := ggPA5_baseChange_normalForm (K := K) (L := AlgebraicClosure K) hσ hαeq
  by_cases hKerEmpty : familyKernel (fun _ : Unit => a) = ∅
  · have hsol : Group.IsSolvable
        ↥(adjointGroup τ (AlgebraicClosure K) ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
      isSolvable_centralizer_of_familyKernel_empty hp a ha hKerEmpty
    have hΓadj : S.Γ ≤ adjointGroup τ (AlgebraicClosure K) := by
      change ⁅S.D.model, S.D.model⁆ ≤ adjointGroup τ (AlgebraicClosure K)
      exact (commutator_le_self_of_subgroup S.D.model).trans inf_le_left
    have hι_mem : ∀ c : ↥(Subgroup.centralizer {b}),
        ι (c : adjointGroup τ K) ∈
          adjointGroup τ (AlgebraicClosure K) ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
      intro c
      have hcc : (c : adjointGroup τ K) ∈ Subgroup.centralizer {b} := c.2
      have hcb : (c : adjointGroup τ K) * b = b * (c : adjointGroup τ K) :=
        Subgroup.mem_centralizer_singleton_iff.mp hcc
      have hbcb : b * (c : adjointGroup τ K) * b⁻¹ = c := by
        rw [← hcb]; group
      have hconj_c : rootDiagUnit τ a * ι (c : adjointGroup τ K) *
          (rootDiagUnit τ a)⁻¹ = ι (c : adjointGroup τ K) := by
        rw [← hιconj (c : adjointGroup τ K), hbcb]
      have hcent : ι (c : adjointGroup τ K) ∈ Subgroup.centralizer {rootDiagUnit τ a} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc ι (c : adjointGroup τ K) * rootDiagUnit τ a =
              (rootDiagUnit τ a * ι (c : adjointGroup τ K) *
                (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by rw [hconj_c]
            _ = rootDiagUnit τ a * ι (c : adjointGroup τ K) := by group
      have hιΓ : ι (c : adjointGroup τ K) ∈ S.Γ := by
        rw [← hirange]
        exact ⟨c, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨hΓadj hιΓ, hcent⟩
    let f' : ↥(Subgroup.centralizer {b}) →*
        ↥(adjointGroup τ (AlgebraicClosure K) ⊓
          Subgroup.centralizer {rootDiagUnit τ a}) :=
      { toFun := fun c => ⟨ι (c : adjointGroup τ K), hι_mem c⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro x y
          apply Subtype.ext
          simp }
    have hf'inj : Function.Injective f' := by
      intro x y hxy
      refine Subtype.ext ?_
      exact hinj (congrArg (fun z : ↥(adjointGroup τ (AlgebraicClosure K) ⊓
        Subgroup.centralizer {rootDiagUnit τ a}) => (z : ModGL τ (AlgebraicClosure K))) hxy)
    haveI : Group.IsSolvable
        ↥(adjointGroup τ (AlgebraicClosure K) ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := hsol
    have hCXsol : Group.IsSolvable ↥(Subgroup.centralizer {b}) :=
      Group.isSolvable_of_isSolvable_injective hf'inj
    exact ggPA5_false_of_isComponentOf_of_solvable hCXsol hL₁
  · obtain ⟨a0, ha0mem⟩ := Set.nonempty_iff_ne_empty.mpr hKerEmpty
    have hker : a0 ∈ kernelRoots (rootCharHom a) := by
      refine ⟨ha0mem.1, ?_⟩
      show rootChar a a0 = 1
      exact ha0mem.2 ()
    let i : KernelComponent (rootCharHom a) := (⟦⟨a0, hker⟩⟧ : KernelComponent (rootCharHom a))
    let z' : ModGL τ (AlgebraicClosure K) :=
      ι g * (g0⁻¹ * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) g0)
    have hz' : z' = ι g * (g0⁻¹ *
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) g0) := rfl
    have hconj : ∀ c : adjointGroup τ K,
        z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) (ι c) *
          z'⁻¹ = ι (α c) := by
      intro c
      set FrL : ModGL τ (AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K) :=
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) with hFrL
      have hz : z' = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g : ModGL τ K) *
          FrL g0 := by
        rw [hz', hιc g]
        group
      have hιc' : ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (c : ModGL τ K) * g0 := hιc c
      rw [hz, hιc', hFrL]
      rw [map_mul, map_mul, map_inv]
      rw [hιc (α c), hBC c, hFrL]
      group
    have hfix' : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) x *
          z'⁻¹ = x := by
      intro x hx
      have hsub := langSubnormal_of_mem_torus S hdT i
      have hxΓ : x ∈ S.Γ := (hsub.1 hx).1
      have hxd : x ∈ Subgroup.centralizer {rootDiagUnit τ a} := (hsub.1 hx).2
      obtain ⟨c, hcx⟩ : x ∈ ι.range := by
        rw [hirange]
        exact hxΓ
      have hxd' : rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹ = x := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hxd]
        group
      have hιbc : ι (b * c * b⁻¹) = ι c := by
        rw [hιconj c, hcx, hxd']
      have hbcb : b * c * b⁻¹ = c := hinj hιbc
      have hccent : c ∈ Subgroup.centralizer {b} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcb : b * c = c * b := by
          calc b * c = b * c * b⁻¹ * b := by group
            _ = c * b := by rw [hbcb]
        exact hcb.symm
      have hαc : α c = c := hfix c hccent
      calc z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) x *
            z'⁻¹ =
            z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) (ι c) *
              z'⁻¹ := by rw [hcx]
          _ = ι (α c) := hconj c
          _ = ι c := by rw [hαc]
          _ = x := hcx
    have hτne : τ ≠ .G2 := by
      intro h
      rcases hτ with h1 | h1 | h1 <;> rw [h] at h1 <;> cases h1
    have hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ := by
      by_cases hF4' : τ = .F4
      · left
        rw [hSD]
        exact (hF4 hF4').2
      · right
        rcases hτ with h1 | h1 | h1
        · rw [h1]; exact Or.inr (Or.inr (Or.inl rfl))
        · rw [h1]; exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd h1 hF4'
    have hqouter : S.D.q = 2 ^ f := by
      rw [hSD]
      exact hK
    exact outer_false_of_component_fixed_by_twist_of_E (S := S)
      (a := a) (i := i) (r := 2) (f := f) (j := e)
      hτne hrootE Nat.prime_two hqouter hq4 he1 (by omega) z' hfix'

end CFSG.StandardType
