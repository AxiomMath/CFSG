module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrame
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridge
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecHolds
public import CFSG.LocalAnalysis.StandardType.GGL45NtSimp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc

theorem kgLang_torusGroup_lang
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {e : ℕ}
    (he : 1 ≤ e) {Q : ModGL τ L}
    (hQ : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L))) :
    ∀ c ∈ torusGroup τ L, ∃ z ∈ torusGroup τ L, z⁻¹ * frobTwistGL τ L ℓ e Q z = c := by
  have hker : kernelRoots (MonoidHom.id (Multiplicative (Fin τ.rank → ℤ))) = ∅ := by
    ext α
    simp only [kernelRoots, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      MonoidHom.id_apply]
    exact fun hα => hα.ne_zero
  have hconn := by
    letI : Group (WithConv (GLCoord L (Label τ) →ₐ[L] L)) := AlgHom.convGroup
    have h :=
      CFSG.HardMathSupport.Timmesfeld.Torality.isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots
        (τ := τ) (k := L) (MonoidHom.id (Multiplicative (Fin τ.rank → ℤ)))
    simpa [hker, rootSpan] using h
  have hmap : (torusGroup τ L).map (frobTwistGL τ L ℓ e Q) = torusGroup τ L :=
    map_frobTwistGL_torusGroup ℓ e hQ
  have hst : ∀ g ∈ torusGroup τ L, frobTwistGL τ L ℓ e Q g ∈ torusGroup τ L := by
    intro g hg
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hconn he Q hst
  intro c hc
  exact hlang c hc

theorem kgLang_frame_mem_normalizer
    {τ : Tag} {L : Type} [Field L] {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q)
    (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) L w * Q ∈
      Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  rcases hQ with rfl | ⟨t, j, h, rfl⟩
  · rw [mul_one]
    exact canonicalRep_mem_normalizer w
  · cases h
    exact mul_mem (canonicalRep_mem_normalizer w)
      (zpow_mem (diagramMap_mem_normalizer t) j)

theorem kgLang_twFw_lang
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e)
    {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) :
    ∀ c ∈ torusGroup τ L, ∃ z ∈ torusGroup τ L, z⁻¹ * twFw τ L e Q w z = c := by
  rw [twFw_eq_frobTwistGL]
  exact kgLang_torusGroup_lang 2 he (kgLang_frame_mem_normalizer hQ w)

private theorem kgLangExcTorusAux_torusGroup_comm
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {x y : ModGL τ L}
    (hx : x ∈ torusGroup τ L) (hy : y ∈ torusGroup τ L) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

private theorem kgLangExcTorusAux_prod_range_mul_succ {M : Type*} [Monoid M] (k : ℕ)
    (f : ℕ → M) :
    ((List.range k).map f).prod * f k = f 0 * ((List.range k).map (fun i => f (i + 1))).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    rw [ih, mul_assoc]

private theorem kgLangExcTorusAux_endPow_mul_prod {Γ : Type*} [Group Γ] (F : Γ →* Γ)
    (x z : Γ) (hFz : F z = z * x) (k : ℕ) :
    endPow F k z = z * ((List.range k).map fun i => endPow F i x).prod := by
  have hFstep : ∀ i, F (endPow F i x) = endPow F (i + 1) x := by
    intro i
    rw [endPow_apply, endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
  induction k with
  | zero => simp [endPow_apply]
  | succ k ih =>
    have hstep : endPow F (k + 1) z = F (endPow F k z) := by
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
    rw [hstep, ih, map_mul, hFz]
    have hFP : F (((List.range k).map (fun i => endPow F i x)).prod) =
        ((List.range k).map (fun i => endPow F (i + 1) x)).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hFstep i
    rw [hFP]
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    rw [kgLangExcTorusAux_prod_range_mul_succ k (fun i => endPow F i x)]
    simp only [endPow_apply, Function.iterate_zero, id_eq]
    rw [mul_assoc]

theorem kgLangExcTorusInput_of_toral_conj
    (hM2 : CFSG.StandardType.LieCore.GGLieLangPosition)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q)
    (hfin : Finite ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)))
    (E : Subgroup (ModGL τ L)) (hEab : IsElemAbelian p E)
    (hEG : ∀ x ∈ E, x ∈ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) ∧
      frobTwistGL τ L 2 e Q x = x)
    (htoral : ExcFramesHalf.IsToralSubgroup τ L E) :
    ∃ N : Subgroup (ModGL τ L), N ≤ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ x ∈ N, frobTwistGL τ L 2 e Q x ∈ N) ∧
      (∀ c ∈ N, ((List.range p).map fun i => endPow (frobTwistGL τ L 2 e Q) i c).prod = 1 →
        ∃ s ∈ N, c = s⁻¹ * frobTwistGL τ L 2 e Q s) ∧ E ≤ N ∧
      ∃ g ∈ adjointGroup τ L, N.map (MulAut.conj g).toMonoidHom ≤ torusGroup τ L := by
  classical
  let F₀ : ModGL τ L →* ModGL τ L := frobTwistGL τ L 2 e Q
  have hEF : E ≤ ratPts τ L F₀ := by
    intro x hx
    obtain ⟨hxG, hxF⟩ := hEG x hx
    rw [ratPts, Subgroup.mem_inf] at hxG ⊢
    exact ⟨hxG.1, hxF⟩
  have hSt : CFSG.StandardType.LieCore.IsSteinbergEndZ τ L (2 ^ e) F₀ :=
    CFSG.StandardType.LieCore.isSteinbergEndZ_frobTwistGL 2 e hQ
  have hleF0 : ratPts τ L F₀ ≤ ratPts τ L (endPow F₀ p) := ratPts_le_endPow hp.one_le
  haveI hfinG : Finite ↥(ratPts τ L (endPow F₀ p)) := hfin
  haveI hfinF0 : Finite ↥(CFSG.StandardType.LieCore.ratPoints F₀) :=
    Finite.of_injective (Subgroup.inclusion hleF0) (Subgroup.inclusion_injective hleF0)
  obtain ⟨w, h, a, hh, hEa, hF⟩ :=
    exc_lang_frame_of_toral hM2 hp hp2 he hQ hfin hEab hEF htoral
  let Fw : ModGL τ L →* ModGL τ L := twFw τ L e Q w
  have hF' : ∀ y, h * F₀ (h⁻¹ * y * h) * h⁻¹ = Fw y := hF
  have hint : ∀ n y, endPow Fw n (h * y * h⁻¹) = h * endPow F₀ n y * h⁻¹ :=
    fun n y => endPow_conj F₀ Fw h hF' n y
  have hFwmap : (torusGroup τ L).map Fw = torusGroup τ L := by
    change (torusGroup τ L).map (twFw τ L e Q w) = torusGroup τ L
    rw [twFw_eq_frobTwistGL]
    exact map_frobTwistGL_torusGroup 2 e (kgLang_frame_mem_normalizer hQ w)
  have hHstab : ∀ y ∈ torusGroup τ L, Fw y ∈ torusGroup τ L := by
    intro y hy
    rw [← hFwmap]
    exact Subgroup.mem_map_of_mem Fw hy
  let Hp : Subgroup (ModGL τ L) :=
    torusGroup τ L ⊓ (endPow Fw p).eqLocus (MonoidHom.id (ModGL τ L))
  let N : Subgroup (ModGL τ L) := Hp.map (MulAut.conj h⁻¹).toMonoidHom
  have mem_Hp : ∀ x : ModGL τ L, x ∈ Hp ↔ x ∈ torusGroup τ L ∧ endPow Fw p x = x := by
    intro x
    show x ∈ torusGroup τ L ⊓ (endPow Fw p).eqLocus (MonoidHom.id (ModGL τ L)) ↔ _
    rw [Subgroup.mem_inf]
    exact and_congr_right fun _ => Iff.rfl
  refine ⟨N, ?_, ?_, ?_, ?_, ?_, h, hh, ?_⟩
  · intro u hu
    change u ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom at hu
    obtain ⟨x, hxHp, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨hxH, hxfix⟩ := (mem_Hp x).mp hxHp
    have hconj : (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [hconj, ratPts, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh)
        (torusGroup_le_adjointGroup hxH)) hh
    · have hx2 := hint p (h⁻¹ * x * h)
      rw [show h * (h⁻¹ * x * h) * h⁻¹ = x from by group, hxfix] at hx2
      have h1 : h⁻¹ * x * h = endPow F₀ p (h⁻¹ * x * h) := by
        nth_rewrite 1 [hx2]; group
      exact h1.symm
  · intro u hu v hv
    change u ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom at hu
    change v ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom at hv
    obtain ⟨x, hxHp, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨y, hyHp, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨hxH, -⟩ := (mem_Hp x).mp hxHp
    obtain ⟨hyH, -⟩ := (mem_Hp y).mp hyHp
    have hconjx : (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    have hconjy : (MulAut.conj h⁻¹).toMonoidHom y = h⁻¹ * y * h := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [hconjx, hconjy]
    have hc := kgLangExcTorusAux_torusGroup_comm hxH hyH
    calc h⁻¹ * x * h * (h⁻¹ * y * h)
        = h⁻¹ * (x * y) * h := by group
      _ = h⁻¹ * (y * x) * h := by rw [hc]
      _ = h⁻¹ * y * h * (h⁻¹ * x * h) := by group
  · intro u hu
    change u ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom at hu
    obtain ⟨x, hxHp, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨hxH, hxfix⟩ := (mem_Hp x).mp hxHp
    have hconj : (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [hconj]
    have hFxHp : Fw x ∈ Hp := by
      refine (mem_Hp (Fw x)).mpr ⟨hHstab x hxH, ?_⟩
      rw [endPow_comm_apply Fw p x, hxfix]
    refine Subgroup.mem_map.mpr ⟨Fw x, hFxHp, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hFz : F₀ (h⁻¹ * x * h) = h⁻¹ * Fw x * h := by
      rw [← hF x]; group; rfl
    rw [hFz]; group
  · intro c hc hnorm1
    change c ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom at hc
    obtain ⟨x, hxHp, rfl⟩ := Subgroup.mem_map.mp hc
    obtain ⟨hxH, hxfix⟩ := (mem_Hp x).mp hxHp
    have hconjx : (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [hconjx]
    have hcfix : ∀ i, endPow F₀ i (h⁻¹ * x * h) = (MulAut.conj h⁻¹) (endPow Fw i x) := by
      intro i
      have hx2 := hint i (h⁻¹ * x * h)
      rw [show h * (h⁻¹ * x * h) * h⁻¹ = x from by group] at hx2
      rw [MulAut.conj_apply, hx2]
      group
    have h2 : (MulAut.conj h⁻¹) ((List.range p).map (fun i => endPow Fw i x)).prod =
        ((List.range p).map (fun i => (MulAut.conj h⁻¹) (endPow Fw i x))).prod := by
      rw [map_list_prod, List.map_map]
      rfl
    have hP : ((List.range p).map fun i => endPow Fw i x).prod = 1 := by
      have hY : (MulAut.conj h⁻¹) ((List.range p).map (fun i => endPow Fw i x)).prod = 1 := by
        rw [h2, ← List.map_congr_left (fun i _ => (hcfix i))]
        exact hnorm1
      exact (MulAut.conj h⁻¹).injective (by rw [hY, map_one])
    obtain ⟨z, hzH, hz⟩ := kgLang_twFw_lang he hQ w x hxH
    have hFz : Fw z = z * x := by
      change twFw τ L e Q w z = z * x
      rw [← hz, ← mul_assoc, mul_inv_cancel, one_mul]
    have hzfix : endPow Fw p z = z := by
      rw [kgLangExcTorusAux_endPow_mul_prod Fw x z hFz p, hP, mul_one]
    have hzHp : z ∈ Hp := (mem_Hp z).mpr ⟨hzH, hzfix⟩
    refine ⟨(MulAut.conj h⁻¹).toMonoidHom z, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨z, hzHp, rfl⟩
    · change h⁻¹ * x * h = (h⁻¹ * z * h)⁻¹ * F₀ (h⁻¹ * z * h)
      have hFz' : F₀ (h⁻¹ * z * h) = h⁻¹ * Fw z * h := by
        rw [← hF z]; group; rfl
      rw [hFz', ← hz]
      group; rfl
  · intro x hxE
    change x ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom
    let d : ModGL τ L :=
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ (a ⟨x, hxE⟩)
    have hxconj : h * x * h⁻¹ = d := hEa ⟨x, hxE⟩
    have hFxd : Fw d = d := by
      rw [← hxconj, ← hF (h * x * h⁻¹)]
      rw [show h⁻¹ * (h * x * h⁻¹) * h = x from by group]
      rw [show F₀ x = x from (hEG x hxE).2]
    refine Subgroup.mem_map.mpr ⟨d, ?_, ?_⟩
    · refine (mem_Hp d).mpr ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      rw [endPow_apply]
      exact Function.iterate_fixed hFxd p
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hxconj]
      group
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    change u ∈ Hp.map (MulAut.conj h⁻¹).toMonoidHom at hu
    obtain ⟨x, hxHp, rfl⟩ := Subgroup.mem_map.mp hu
    have hx : (MulAut.conj h).toMonoidHom ((MulAut.conj h⁻¹).toMonoidHom x) = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hx]
    exact ((mem_Hp x).mp hxHp).1

theorem kgLangExcTorusInput_of_toral
    (hM2 : CFSG.StandardType.LieCore.GGLieLangPosition)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q)
    (hfin : Finite ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)))
    (E : Subgroup (ModGL τ L)) (hEab : IsElemAbelian p E)
    (hEG : ∀ x ∈ E, x ∈ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) ∧
      frobTwistGL τ L 2 e Q x = x)
    (htoral : ExcFramesHalf.IsToralSubgroup τ L E) :
    ∃ N : Subgroup (ModGL τ L), N ≤ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ x ∈ N, frobTwistGL τ L 2 e Q x ∈ N) ∧
      (∀ c ∈ N, ((List.range p).map fun i => endPow (frobTwistGL τ L 2 e Q) i c).prod = 1 →
        ∃ s ∈ N, c = s⁻¹ * frobTwistGL τ L 2 e Q s) ∧ E ≤ N := by
  obtain ⟨N, hN, hab, hst, h90, hEN, -⟩ :=
    kgLangExcTorusInput_of_toral_conj hM2 hp hp2 he hQ hfin E hEab hEG htoral
  exact ⟨N, hN, hab, hst, h90, hEN⟩

theorem kgLangExcTorusInput
    (hM1 : CFSG.StandardType.LieCore.GGLieToralPosition)
    (hM2 : CFSG.StandardType.LieCore.GGLieLangPosition)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q)
    (hfin : Finite ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p))) :
    KGLangTorusInput p (ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)) (frobTwistGL τ L 2 e Q) := by
  classical
  intro E hEab hEG
  let F₀ : ModGL τ L →* ModGL τ L := frobTwistGL τ L 2 e Q
  have hEF : E ≤ ratPts τ L F₀ := by
    intro x hx
    obtain ⟨hxG, hxF⟩ := hEG x hx
    rw [ratPts, Subgroup.mem_inf] at hxG ⊢
    exact ⟨hxG.1, hxF⟩
  have hSt : CFSG.StandardType.LieCore.IsSteinbergEndZ τ L (2 ^ e) F₀ :=
    CFSG.StandardType.LieCore.isSteinbergEndZ_frobTwistGL 2 e hQ
  have hleF0 : ratPts τ L F₀ ≤ ratPts τ L (endPow F₀ p) := ratPts_le_endPow hp.one_le
  haveI hfinG : Finite ↥(ratPts τ L (endPow F₀ p)) := hfin
  haveI hfinF0 : Finite ↥(CFSG.StandardType.LieCore.ratPoints F₀) :=
    Finite.of_injective (Subgroup.inclusion hleF0) (Subgroup.inclusion_injective hleF0)
  haveI hfinE : Finite E :=
    Finite.of_injective (Subgroup.inclusion (hEF.trans hleF0))
      (Subgroup.inclusion_injective (hEF.trans hleF0))
  have hcard : Nat.card E < p ^ CFSG.StandardType.LieCore.nontoralMinRank τ p :=
    card_elemAbelian_lt (N := CFSG.StandardType.LieCore.nontoralMinRank τ p)
      (le_of_eq (nontoralMinRank_eq_of_nonTorsion h3 h5).symm) hp hp2 hEab
  have htotal := hM1 τ (CFSG.StandardType.LieCore.isExcTag τ) L hL e he F₀ hSt hfinF0 p
    hp hp2 E hEF hEab hcard
  exact kgLangExcTorusInput_of_toral hM2 hp hp2 he hQ hfin E hEab hEG htotal

end CFSG.StandardType
