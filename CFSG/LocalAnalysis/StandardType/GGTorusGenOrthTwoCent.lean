module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaSplit
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCentFrame
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOFix
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks

public section

namespace CFSG.StandardType

open Module QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup mem_sesqUnitaryGroup)
open LayerCores LayerCores.OrthSplit

@[expose] noncomputable def orthRestrict {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]
    (C : Subgroup (V ≃ₗ[K] V)) (hCO : C ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hCS : C ≤ stab A) :
    C →* ↥(sesqUnitaryGroup (LinearMap.BilinForm.restrict (polarBilin Q) (freeSp A))) :=
  MonoidHom.codRestrict (((LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (freeSp A)).symm.toMonoidHom).comp ((restrFree A).comp (Subgroup.inclusion hCS))) _
    fun g => mem_sesqUnitaryGroup.mpr fun x y =>
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (hCO g.2) (x : V) (y : V)

theorem orthRestrict_apply {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]
    (C : Subgroup (V ≃ₗ[K] V)) (hCO : C ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hCS : C ≤ stab A) (g : C) (w : freeSp A) :
    (((orthRestrict A C hCO hCS g : ↥(sesqUnitaryGroup
        (LinearMap.BilinForm.restrict (polarBilin Q) (freeSp A)))) :
        LinearMap.GeneralLinearGroup K (freeSp A)) : Module.End K (freeSp A)) w =
      restrFree A ⟨g, hCS g.2⟩ w :=
  rfl

private theorem quad_map_of_polar {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} [Fintype A]
    (hodd : Odd (Fintype.card A)) (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (g : freeSp A ≃ₗ[K] freeSp A)
    (hgB : ∀ u v : freeSp A, polar Q (g u : V) (g v : V) = polar Q (u : V) (v : V))
    (hgA : ∀ (a : V ≃ₗ[K] V) (ha : a ∈ A) (w : freeSp A),
      (g (restrFree A ⟨a, le_stab ha⟩ w) : V) = a (g w : V))
    (w : freeSp A) : Q (g w : V) = Q (w : V) := by
  have hA : (Fintype.card A : K) ≠ 0 := natCast_card_ne_zero_of_odd hodd
  let D : freeSp A →+ K :=
    { toFun := fun u => Q (g u : V) - Q (u : V)
      map_zero' := by simp
      map_add' := fun u v => by
        simp only [map_add, Submodule.coe_add]
        rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q (u : V), hgB u v]
        ring }
  have hDinv : ∀ a : A, D (restrFree A ⟨a, le_stab a.2⟩ w) = D w := by
    intro a
    show Q (g (restrFree A ⟨a, le_stab a.2⟩ w) : V) - Q (restrFree A ⟨a, le_stab a.2⟩ w : V) =
      Q (g w : V) - Q (w : V)
    rw [hgA a a.2 w, coe_restrFree_apply,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hAO a.2),
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hAO a.2)]
  have hsum : w = ∑ a : A, (restrFree A ⟨a, le_stab a.2⟩ w - w) := by
    refine Subtype.ext ?_
    have h0 : ∑ a : A, (a : V ≃ₗ[K] V) (w : V) = 0 := by
      have h := LinearMap.mem_ker.mp w.2
      rw [avg_apply] at h
      exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hA)
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_sub, coe_restrFree_apply]
    rw [Finset.sum_sub_distrib, h0, Finset.sum_const, Finset.card_univ, zero_sub,
      ← Nat.cast_smul_eq_nsmul K,
      natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero, one_smul,
      ← neg_one_smul K (w : V), CharTwo.neg_eq, one_smul]
  have hzero : D w = 0 := by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun a _ => by rw [map_sub, hDinv a, sub_self]
  exact sub_eq_zero.mp hzero

private theorem restrict_hsc {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (A : Subgroup (V ≃ₗ[K] V)) [Fintype A] (hodd : Odd (Fintype.card A))
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hscA : ∀ g : ↥(orthDerived Q),
      (∀ a ∈ A, (g : V ≃ₗ[K] V) * a = a * (g : V ≃ₗ[K] V)) → g ^ 3 = 1 → (g : V ≃ₗ[K] V) ∈ A) :
    ∀ g : ↥(sesqUnitaryGroup (LinearMap.BilinForm.restrict (polarBilin Q) (freeSp A))),
      (∀ e ∈ (orthRestrict A A hAO le_stab).range, g * e = e * g) → g ^ 3 = 1 →
      g ∈ (orthRestrict A A hAO le_stab).range := by
  intro g hgcomm hg3
  have hA : (Fintype.card A : K) ≠ 0 := natCast_card_ne_zero_of_odd hodd
  let gL : freeSp A ≃ₗ[K] freeSp A :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K (freeSp A) g.val
  have gL_apply : ∀ w, gL w = (g.val : Module.End K (freeSp A)) w := fun w => by
    rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  have hgL3 : gL ^ 3 = 1 := by
    have hv : g.val ^ 3 = 1 := by simpa using congrArg Subtype.val hg3
    rw [show gL = LinearMap.GeneralLinearGroup.generalLinearEquiv K (freeSp A) g.val from rfl,
      ← map_pow, hv, map_one]
  have hgB : ∀ u v : freeSp A, polar Q (gL u : V) (gL v : V) = polar Q (u : V) (v : V) := by
    intro u v
    rw [gL_apply u, gL_apply v]
    exact mem_sesqUnitaryGroup.mp g.2 u v
  have hgA : ∀ (a : V ≃ₗ[K] V) (ha : a ∈ A) (w : freeSp A),
      (gL (restrFree A ⟨a, le_stab ha⟩ w) : V) = a (gL w : V) := by
    intro a ha w
    have h := congrArg (fun x : ↥(sesqUnitaryGroup
        (LinearMap.BilinForm.restrict (polarBilin Q) (freeSp A))) =>
      ((((x : LinearMap.GeneralLinearGroup K (freeSp A)) : Module.End K (freeSp A)) w :
        freeSp A) : V)) (hgcomm _ ⟨⟨a, ha⟩, rfl⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, orthRestrict_apply,
      coe_restrFree_apply] at h
    rw [gL_apply, gL_apply]
    exact h
  have hmem : split hA (1, gL) ∈
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [centralizer_eq_map_split hA hAO]
    refine ⟨(1, gL), Subgroup.mem_prod.mpr ⟨one_mem _, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨⟨a, haS⟩, ha, rfl⟩
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, coe_restrFree_apply]
      exact (hgA a (Subgroup.mem_subgroupOf.mp ha) w).symm
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w =>
        quad_map_of_polar hodd hAO gL hgB hgA w
  obtain ⟨hgc, hgO⟩ := Subgroup.mem_inf.mp hmem
  have hg3' : split hA (1, gL) ^ 3 = 1 := by
    rw [← map_pow, Prod.pow_mk, one_pow, hgL3, Prod.mk_one_one, map_one]
  have hgD : split hA (1, gL) ∈ orthDerived Q :=
    CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ hT (by norm_num) hgO hg3'
  have hgA' : split hA (1, gL) ∈ A :=
    hscA ⟨_, hgD⟩ (fun a ha => (Subgroup.mem_centralizer_iff.mp hgc a ha).symm)
      (Subtype.ext hg3')
  refine MonoidHom.mem_range.mpr ⟨⟨_, hgA'⟩, ?_⟩
  refine Subtype.ext (Units.ext (LinearMap.ext fun w => Subtype.ext ?_))
  rw [orthRestrict_apply, coe_restrFree_apply]
  exact (split_apply_free hA (1, gL) w).trans (congrArg Subtype.val (gL_apply w))

theorem ggTorusCentSC_orthDerivedTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) :
    GGTorusCentSC 3 ↥(orthDerived Q) := by
  intro E hE h3 hsc c hc hcp
  classical
  have : Finite (V ≃ₗ[K] V) := LayerCores.finite_linearEquiv
  have : Fintype E := Fintype.ofFinite E
  let A : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype
  have : Fintype A := Fintype.ofFinite A
  have hA : CFSG.Open.IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hE _
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h
  have hAodd : Odd (Fintype.card A) := by
    rw [← Nat.card_eq_fintype_card,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
    rw [hn]
    exact (by norm_num : Odd 3).pow
  have hA0 : (Fintype.card A : K) ≠ 0 := natCast_card_ne_zero_of_odd hAodd
  have hDO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Q)
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.map_subtype_le _).trans hDO
  have hscA : ∀ g : ↥(orthDerived Q),
      (∀ a ∈ A, (g : V ≃ₗ[K] V) * a = a * (g : V ≃ₗ[K] V)) → g ^ 3 = 1 →
      (g : V ≃ₗ[K] V) ∈ A := by
    intro g hg hg3
    refine Subgroup.mem_map.mpr ⟨g, hsc g (fun e he => ?_) hg3, rfl⟩
    have hAe : (e : V ≃ₗ[K] V) ∈ A := Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    refine Subtype.ext ?_
    show (g : V ≃ₗ[K] V) * (orthDerived Q).subtype e = (orthDerived Q).subtype e * (g : V ≃ₗ[K] V)
    simp only [Subgroup.coe_subtype]
    exact hg _ hAe
  have hcA : ∀ a ∈ A, (c : V ≃ₗ[K] V) * a = a * (c : V ≃ₗ[K] V) := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    have h := congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[K] V)) (hc e he)
    show (c : V ≃ₗ[K] V) * (orthDerived Q).subtype e = (orthDerived Q).subtype e * (c : V ≃ₗ[K] V)
    simp only [Subgroup.coe_subtype]
    simpa only [Subgroup.coe_mul] using h
  let B : LinearMap.BilinForm K (freeSp A) :=
    LinearMap.BilinForm.restrict (polarBilin Q) (freeSp A)
  have hnd : B.Nondegenerate := by
    have h := CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
      (polarNondegOn_freeSp hQ hA0 hAO)
    exact ⟨fun x hx => h.1 x hx, fun y hy => h.2 y hy⟩
  have hcO : Subgroup.zpowers (c : V ≃ₗ[K] V) ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr (hDO c.2)
  have hcS : Subgroup.zpowers (c : V ≃ₗ[K] V) ≤ stab A :=
    Subgroup.zpowers_le.mpr (centralizer_le_stab (Subgroup.mem_centralizer_iff.mpr
      fun a ha => (hcA a ha).symm))
  let cW : ↥(sesqUnitaryGroup B) := orthRestrict A _ hcO hcS ⟨c, Subgroup.mem_zpowers _⟩
  have hcWcomm : ∀ e ∈ (orthRestrict A A hAO le_stab).range, cW * e = e * cW := by
    rintro _ ⟨a, rfl⟩
    refine Subtype.ext (Units.ext (LinearMap.ext fun w => Subtype.ext ?_))
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, cW, orthRestrict_apply,
      coe_restrFree_apply]
    simpa only [LinearEquiv.mul_apply] using
      congrArg (fun x : V ≃ₗ[K] V => x (w : V)) (hcA a a.2)
  have hEWel : CFSG.Open.IsElemAbelian 3 (orthRestrict A A hAO le_stab).range := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
      rw [show a * b = b * a from Subtype.ext (by
        simpa only [Subgroup.coe_mul] using hAab a a.2 b b.2)]
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
      rw [← ha, ← MonoidHom.map_pow, show a ^ 3 = 1 from Subtype.ext (by
        rw [Subgroup.coe_pow, hA.2 (a : V ≃ₗ[K] V) a.2, Subgroup.coe_one]), map_one]
  have hcent := SpNS.centralizer_le_of_selfCent_spForm (B := B) hK
    (fun w => CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q w) hnd
    (orthRestrict A A hAO le_stab).range hEWel (restrict_hsc hQ hT A hAodd hAO hscA)
  have hcWmem : cW ∈ (orthRestrict A A hAO le_stab).range :=
    hcent (Subgroup.mem_centralizer_iff.mpr (fun e he => (hcWcomm e he).symm))
  obtain ⟨a, ha⟩ := hcWmem
  obtain ⟨e, heE, hea⟩ := Subgroup.mem_map.mp a.2
  have hcWact : ∀ w : freeSp A, (a : V ≃ₗ[K] V) (w : V) = (c : V ≃ₗ[K] V) (w : V) := by
    intro w
    have h := congrArg (fun x : ↥(sesqUnitaryGroup B) =>
      ((((x : LinearMap.GeneralLinearGroup K (freeSp A)) : Module.End K (freeSp A)) w :
        freeSp A) : V)) ha
    simpa only [cW, orthRestrict_apply, coe_restrFree_apply] using h
  let d : ↥(orthDerived Q) := c * e⁻¹
  have hdW : ∀ w ∈ freeSp A, (d : V ≃ₗ[K] V) w = w := by
    intro w hw
    have hea' : ((e : ↥(orthDerived Q)) : V ≃ₗ[K] V) = (a : V ≃ₗ[K] V) := by
      simpa only [Subgroup.coe_subtype] using hea
    have hmem : ((a : V ≃ₗ[K] V))⁻¹ w ∈ freeSp A := by
      rw [LinearMap.mem_ker, le_stab (A.inv_mem a.2) w, LinearMap.mem_ker.mp hw, map_zero]
    have hd : (d : V ≃ₗ[K] V) w = (c : V ≃ₗ[K] V) (((a : V ≃ₗ[K] V))⁻¹ w) := by
      show (((c * e⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V)) w = _
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hea', LinearEquiv.mul_apply]
    rw [hd, ← hcWact ⟨((a : V ≃ₗ[K] V))⁻¹ w, hmem⟩]
    exact LinearEquiv.apply_symm_apply (a : V ≃ₗ[K] V) w
  have hdWpow : ∀ n, ∀ w ∈ freeSp A, ((d : V ≃ₗ[K] V) ^ n) w = w := by
    intro n
    induction n with
    | zero => intro w hw; rfl
    | succ n ih => intro w hw; rw [pow_succ', LinearEquiv.mul_apply, ih w hw, hdW w hw]
  have hd3 : ∃ k, d ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    refine ⟨k + 1, ?_⟩
    have he3 : e ^ 3 = 1 := hE.2 e heE; have hcomm : Commute c e := hc e heE
    have hc1 : c ^ 3 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
    have he1 : (e⁻¹) ^ 3 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, show (e⁻¹) ^ 3 = 1 from by
        rw [show (e⁻¹) ^ 3 = (e ^ 3)⁻¹ from (inv_pow e 3).symm, he3, inv_one], one_pow]
    calc d ^ 3 ^ (k + 1) = (c * e⁻¹) ^ 3 ^ (k + 1) := rfl
      _ = c ^ 3 ^ (k + 1) * (e⁻¹) ^ 3 ^ (k + 1) := (hcomm.inv_right).mul_pow _
      _ = 1 := by rw [hc1, he1, mul_one]
  have hdcomm : ∀ e' ∈ E, d * e' = e' * d := by
    intro e' he'
    have hee : Commute e e' := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨e', he'⟩)
    exact (show Commute c e' from hc e' he').mul_left hee.inv_left
  have hd_eq_one : d = 1 := by
    obtain ⟨k, hk⟩ := hd3
    have key : ∀ k, d ^ 3 ^ k = 1 → d = 1 := by
      intro k
      induction k with
      | zero => intro h; simpa using h
      | succ k ih =>
          intro h
          have hd'pow : (d ^ 3 ^ k) ^ 3 = 1 := by rw [← pow_mul, ← pow_succ, h]
          have hd'comm : ∀ e' ∈ E, (d ^ 3 ^ k) * e' = e' * (d ^ 3 ^ k) :=
            fun e' he' => (show Commute d e' from hdcomm e' he').pow_left (3 ^ k)
          have hd'E : d ^ 3 ^ k ∈ E := hsc _ hd'comm hd'pow
          have hP : ∀ p ∈ fixSp A, ((d ^ 3 ^ k : ↥(orthDerived Q)) : V ≃ₗ[K] V) p = p := by
            intro p hp
            exact (mem_fixSp_iff hA0).mp hp _ (Subgroup.mem_map.mpr ⟨_, hd'E, rfl⟩)
          have hW : ∀ w ∈ freeSp A, ((d ^ 3 ^ k : ↥(orthDerived Q)) : V ≃ₗ[K] V) w = w := by
            intro w hw
            rw [show ((d ^ 3 ^ k : ↥(orthDerived Q)) : V ≃ₗ[K] V) = (d : V ≃ₗ[K] V) ^ (3 ^ k)
              from by simp only [Subgroup.coe_pow]]
            exact hdWpow _ w hw
          have hd'eq : d ^ 3 ^ k = 1 := Subtype.ext <| LinearEquiv.ext fun v => by
            have hv : v ∈ fixSp A ⊔ freeSp A := by
              rw [(isCompl_fixSp_freeSp hA0).sup_eq_top]; exact Submodule.mem_top
            obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
            show ((d ^ 3 ^ k : ↥(orthDerived Q)) : V ≃ₗ[K] V) (p + w) = p + w
            rw [map_add, hP p hp, hW w hw]
          exact ih hd'eq
    exact key k hk
  rw [mul_inv_eq_one.mp hd_eq_one]
  exact heE

end CFSG.StandardType
