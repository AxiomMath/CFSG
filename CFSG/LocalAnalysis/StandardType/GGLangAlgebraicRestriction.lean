module

public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraic
public import CFSG.LocalAnalysis.StandardType.GGLangRootSpanReflect
public import CFSG.LocalAnalysis.StandardType.GGLangDescentEntries
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6OuterDescent

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.StandardType.TableCRes
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [local instance] ZMod.algebra algebraicClosure.isAlgClosure IsAlgClosure.isAlgClosed

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem langRestrict_diagram_lift
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (ι : algebraicClosure (ZMod 2) L →+* L) (P : ModGL τ L)
    (hP : P = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ), P = diagramAt τ L t h) :
    ∃ P0 : ModGL τ (algebraicClosure (ZMod 2) L),
      (P0 = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ),
        P0 = diagramAt τ (algebraicClosure (ZMod 2) L) t h) ∧
      baseChangeGL ι P0 = P := by
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · exact ⟨1, Or.inl rfl, map_one _⟩
  · refine ⟨diagramAt τ (algebraicClosure (ZMod 2) L) t ht, Or.inr ⟨t, ht, rfl⟩, ?_⟩
    cases ht
    exact baseChangeGL_diagramMap ι t

theorem LangSetup.exists_algebraicRestriction
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) :
    ∃ S0 : LangSetup τ (algebraicClosure (ZMod 2) L) p₀,
      S0.D.q = S.D.q ∧ S0.ρ = S.ρ ∧ S0.IsAlgebraic ∧
      baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L) S0.D.n = S.D.n ∧
      baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L) S0.D.g0 = S.D.g0 ∧
      (∀ g, baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L) (S0.D.Φ g) =
        S.D.Φ (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L) g)) ∧
      S0.D.model.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) = S.D.model ∧
      S0.Γ.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) = S.Γ ∧
      S0.D.torus.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) = S.D.torus ∧
      S0.E.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) = S.E := by
  classical
  let L0 := algebraicClosure (ZMod 2) L
  let ι : L0 →+* L := algebraMap L0 L
  have h2q : 2 ∣ S.D.q := (CharP.cast_eq_zero_iff L 2 S.D.q).1 S.hqpow.2
  obtain ⟨f, -, hfpos, hqf⟩ := (isPrimePow_nat_iff_bounded_log_minFac S.D.q).1 S.hqpow.1
  have hmin : S.D.q.minFac = 2 := (Nat.minFac_eq_two_iff S.D.q).2 h2q
  have hq2f : S.D.q = 2 ^ f := by rw [hqf, hmin]
  let Fr0 : L0 →+* L0 := iterateFrobenius L0 2 f
  have hFr0 : ∀ c : L0, Fr0 c = c ^ S.D.q := by
    intro c
    rw [iterateFrobenius_def, hq2f]
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨P0, hP0, hbcP0⟩ := langRestrict_diagram_lift ι P hP
  have hcomm : ι.comp Fr0 = Fr.comp ι := by
    ext c
    simp only [RingHom.comp_apply]
    rw [hFr0 c, map_pow, hFr]
  let Φ0 : ModGL τ L0 →* ModGL τ L0 :=
    (MulAut.conj P0).toMonoidHom.comp (Units.map (entrywiseHom Fr0))
  have hΦcompat : ∀ g : ModGL τ L0,
      baseChangeGL ι (Φ0 g) = S.D.Φ (baseChangeGL ι g) := by
    intro g
    rw [hΦ (baseChangeGL ι g)]
    change baseChangeGL ι ((MulAut.conj P0) (Units.map (entrywiseHom Fr0) g)) =
      P * Units.map (entrywiseHom Fr) (baseChangeGL ι g) * P⁻¹
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hbcP0]
    congr 1
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hcomm]
  obtain ⟨w, hw⟩ := S.D.n_weyl
  let n0 : ModGL τ L0 := canonicalRep (coxeterSystem τ) L0 w
  have hbcn0 : baseChangeGL ι n0 = S.D.n := by
    rw [baseChangeGL_canonicalRep, hw]
  obtain ⟨g00, hg00⟩ := (LangSetup.model_g0_mem_range_algebraicClosure S).2
  have hg00mem : g00 ∈ adjointGroup τ L0 :=
    CFSG.LocalAnalysis.GLTheoremA.T158.mem_adjointGroup_of_baseChangeGL_mem L0 L (hg00 ▸ S.D.g0_mem)
  have hlang : Φ0 g00 = g00 * n0 := by
    apply baseChangeGL_injective ι
    rw [map_mul, hΦcompat g00, hg00, hbcn0]
    exact S.D.lang
  let D0 : LangDatum τ L0 :=
    { Φ := Φ0
      q := S.D.q
      n := n0
      g0 := g00
      steinberg := ⟨Fr0, hFr0, P0, hP0, fun g => by
        change (MulAut.conj P0) (Units.map (entrywiseHom Fr0) g) =
          P0 * Units.map (entrywiseHom Fr0) g * P0⁻¹
        rw [MulAut.conj_apply]⟩
      n_weyl := ⟨w, rfl⟩
      g0_mem := hg00mem
      lang := hlang }
  have hD0step : ∀ x : ModGL τ L0,
      baseChangeGL ι (D0.step x) = S.D.step (baseChangeGL ι x) := by
    intro x
    change baseChangeGL ι ((MulAut.conj D0.n) (D0.Φ x)) =
      (MulAut.conj S.D.n) (S.D.Φ (baseChangeGL ι x))
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hbcn0, hΦcompat x]
  have hmodel : D0.model.map (baseChangeGL ι) = S.D.model := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxadj, hxfix⟩ := (LangDatum.mem_model D0).1 hx
      refine (LangDatum.mem_model S.D).2
        ⟨CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (f := ι) hxadj, ?_⟩
      have h1 : baseChangeGL ι (D0.n * D0.Φ x * D0.n⁻¹) = baseChangeGL ι x := by rw [hxfix]
      rw [map_mul, map_mul, map_inv, hbcn0, hΦcompat x] at h1
      exact h1
    · intro y hy
      obtain ⟨x, hx⟩ := (LangSetup.model_g0_mem_range_algebraicClosure S).1 hy
      rw [← hx]
      refine Subgroup.mem_map_of_mem (f := baseChangeGL ι) ?_
      refine (LangDatum.mem_model D0).2
        ⟨CFSG.LocalAnalysis.GLTheoremA.T158.mem_adjointGroup_of_baseChangeGL_mem L0 L
          (hx ▸ ((LangDatum.mem_model S.D).1 hy).1), ?_⟩
      apply baseChangeGL_injective ι
      rw [map_mul, map_mul, map_inv, hbcn0, hΦcompat x, hx]
      exact ((LangDatum.mem_model S.D).1 hy).2
  have hΓ : D0.Γ.map (baseChangeGL ι) = S.D.Γ := by
    rw [LangDatum.Γ, LangDatum.Γ, Subgroup.map_commutator, hmodel]
  have htor : D0.torus.map (baseChangeGL ι) = S.D.torus := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf D0.n D0.Φ := hx
      obtain ⟨hxtor, hxfix⟩ := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf).1 hx'
      refine (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf).2
        ⟨CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup ι hxtor, ?_⟩
      have h1 : baseChangeGL ι (D0.n * D0.Φ x * D0.n⁻¹) = baseChangeGL ι x := by rw [hxfix]
      rw [map_mul, map_mul, map_inv, hbcn0, hΦcompat x] at h1
      exact h1
    · intro y hy
      have hyM : y ∈ S.D.model := LangDatum.torus_le_model S.D hy
      obtain ⟨x, hx⟩ := (LangSetup.model_g0_mem_range_algebraicClosure S).1 hyM
      have hxadj : x ∈ adjointGroup τ L0 :=
        CFSG.LocalAnalysis.GLTheoremA.T158.mem_adjointGroup_of_baseChangeGL_mem L0 L
          (hx ▸ ((LangDatum.mem_model S.D).1 hyM).1)
      have hytor : baseChangeGL ι x ∈ torusGroup τ L := by
        rw [hx]
        exact (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf).1
          (show y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf S.D.n S.D.Φ from hy) |>.1
      rw [← hx]
      refine Subgroup.mem_map_of_mem (f := baseChangeGL ι) ?_
      refine (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf).2
        ⟨CFSG.RankThree.Classical2.mem_torusGroup_of_baseChangeGL_mem ι hxadj hytor, ?_⟩
      apply baseChangeGL_injective ι
      rw [map_mul, map_mul, map_inv, hbcn0, hΦcompat x, hx]
      exact (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf).1
        (show y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf S.D.n S.D.Φ from hy) |>.2
  have hfin : Finite D0.model := by
    haveI : Finite S.D.model := S.finite
    refine Finite.of_injective
      (fun x : D0.model =>
        (⟨baseChangeGL ι x.1, hmodel ▸ Subgroup.mem_map_of_mem _ x.2⟩ : S.D.model))
      (fun a b h => Subtype.ext (baseChangeGL_injective ι (Subtype.ext_iff.mp h)))
  have hfrob : FrobRootMap D0 S.ρ := by
    refine ⟨S.frob.isRoot_iff, S.frob.neg_eq, S.frob.iform_eq, ?_, ?_⟩
    · intro γ hγ
      have hle : (rootSubgroup τ L0 γ).map D0.step ≤ rootSubgroup τ L0 (S.ρ γ) := by
        rw [Subgroup.map_le_iff_le_comap, rootSubgroup, Subgroup.closure_le]
        rintro _ ⟨c, rfl⟩
        have hbc : baseChangeGL ι (D0.step (pinnedX τ L0 γ c)) ∈ rootSpan τ L {S.ρ γ} := by
          rw [rootSpan_singleton, hD0step]
          have hmem : baseChangeGL ι (pinnedX τ L0 γ c) ∈ rootSubgroup τ L γ := by
            rw [← rootSpan_singleton]
            exact CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan (S := {γ}) ι
              (by rw [rootSpan_singleton]; exact Subgroup.subset_closure ⟨c, rfl⟩)
          have hmem2 : S.D.step (baseChangeGL ι (pinnedX τ L0 γ c)) ∈
              (rootSubgroup τ L γ).map S.D.step :=
            Subgroup.mem_map_of_mem _ hmem
          rwa [S.frob.map_rootSubgroup γ hγ] at hmem2
        have hthis :=
          CFSG.LieType.AlgebraicGroups.mem_rootSpan_of_baseChangeGL_mem_algClosed ι {S.ρ γ} hbc
        rwa [rootSpan_singleton] at hthis
      obtain ⟨ρ0, hroot0, hneg0, hform0, hstep0⟩ := exists_step_pinnedX D0
      obtain ⟨μ, hμ0, hμ⟩ := hstep0 γ hγ
      have hρ0 : ρ0 γ = S.ρ γ := by
        obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (μ⁻¹) S.q_pos
        have hc' : μ * c ^ S.D.q = 1 := by rw [hc, mul_inv_cancel₀ hμ0]
        refine eq_of_pinnedX_one_mem_rootSubgroup (L := L0) ((hroot0 γ).2 hγ)
          ((S.frob.isRoot_iff γ).2 hγ) ?_
        rw [← hc', ← hμ]
        exact hle (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨c, rfl⟩))
      refine le_antisymm hle ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨d, rfl⟩
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (μ⁻¹ * d) S.q_pos
      have harg : μ * c ^ S.D.q = d := by
        rw [hc, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
      have heq : D0.step (pinnedX τ L0 γ c) = pinnedX τ L0 (S.ρ γ) d := by
        rw [hμ c, hρ0, harg]
      rw [← heq]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨c, rfl⟩)
    · intro a ha γ hγ
      have hbcT : rootDiagUnit τ (fun i => Units.map ι.toMonoidHom (a i)) ∈ S.D.torus := by
        rw [← baseChangeGL_rootDiagUnit ι a]
        exact htor ▸ Subgroup.mem_map_of_mem _ ha
      have h1 := S.frob.rootChar_eq (fun i => Units.map ι.toMonoidHom (a i)) hbcT γ hγ
      apply Units.map_injective (f := ι.toMonoidHom) ι.injective
      simpa only [← CFSG.RankThree.PartOne.KE.rootChar_map_tuple, map_pow] using h1
  have hT : (D0.torus ⊓ D0.Γ).map (baseChangeGL ι) = S.D.torus ⊓ S.D.Γ := by
    rw [Subgroup.map_inf D0.torus D0.Γ (baseChangeGL ι) (baseChangeGL_injective ι), htor, hΓ]
  have hE : (D0.torsion p₀).map (baseChangeGL ι) = S.E := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [LangDatum.mem_torsion D0] at hx
      refine S.E_all (baseChangeGL ι x) ?_ ?_
      · rw [← hT]
        exact Subgroup.mem_map_of_mem _ hx.1
      · rw [← map_pow, hx.2, map_one]
    · intro hy
      have hyp : y ^ p₀ = 1 := S.E_exp y hy
      have hy' : y ∈ (D0.torus ⊓ D0.Γ).map (baseChangeGL ι) := by
        rw [hT]
        exact S.E_le hy
      obtain ⟨x, hxT, rfl⟩ := hy'
      rw [Subgroup.mem_map]
      refine ⟨x, ?_, rfl⟩
      rw [LangDatum.mem_torsion D0]
      exact ⟨hxT, by
        apply baseChangeGL_injective ι
        rw [map_pow, hyp, map_one]⟩
  have hcast : ((D0.q : ℕ) : L0) = 0 := by
    apply ι.injective
    rw [map_natCast, S.hqpow.2, map_zero]
  let S0 : LangSetup τ L0 p₀ :=
    D0.toSetup p₀ S.ρ hfrob S.hp S.hq ⟨S.hqpow.1, hcast⟩ S.hpq hfin
  haveI : Algebra.IsAlgebraic (ZMod 2) L0 := algebraicClosure.isAlgebraic (ZMod 2) L
  have hS0alg : S0.IsAlgebraic :=
    CFSG.StandardType.langSetup_isAlgebraic_of_zmod_two S0 (by rw [LangDatum.toSetup_D]; exact hq2f)
  refine ⟨S0, rfl, rfl, hS0alg, hbcn0, hg00, hΦcompat, hmodel, hΓ, htor, hE⟩

end CFSG.HardMathSupport.Timmesfeld.LangTorus
