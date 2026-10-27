module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1On
public import CFSG.LocalAnalysis.StandardType.GGXInLCommTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Tor
import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin
import CFSG.LocalAnalysis.StandardType.GGResXDatumSurj
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2TableBI1FailOn_twE6
    (hX : GGQ2XInLCommTwE6) : GGQ2TableBI1FailOn (fun lab => lab.tag = .twE6) := by
  classical
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨hq, hSl⟩, hBsN, h3I⟩ := hP
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := by simpa using hlab.1
    have h2 : lab.n < 2 := by simpa only [GGLabQTwo] using hq
    omega
  have hTw : GGInnerDiagOnLabel GGTwE6BadLabel 3 Bs L :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ', ⟨⟨_, hS'⟩, hrest⟩⟩ =>
      ⟨hs, hna, θ', ⟨⟨hS', rfl, by rw [hn1]; norm_num⟩, hrest⟩⟩) hraw⟩
  have hE6 : GGInnerDiagOnLabel (fun _ lab => lab.tag = LargeEvenLieTag.twE6) 3 Bs L :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ', ⟨⟨_, hS'⟩, hrest⟩⟩ =>
      ⟨hs, hna, θ', ⟨hS', hrest⟩⟩) hraw⟩
  have hWlab : GGQ2LabelWeyl lab CoxeterMatrix.E₆ := by
    rw [GGQ2LabelWeyl, hSl]
    exact ⟨Equiv.refl _, rfl⟩
  have hcfg : GGConfig 3 B Bs x L D J := hset.1.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hSstar.2.2.2.2
  have hNoTr : GGNoTransvection 3 Bs := hset.1.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hBsN
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hx1 hLx hcyc
  obtain ⟨e, he⟩ := ggTwE6Bad_weylOfType hset.1 hTw
  obtain ⟨Φ, T, w, hm⟩ := ggTwE6Bad_model hset.1 hTw hN
  obtain ⟨V, iadd, imod, ⟨ιV⟩⟩ := exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := iadd
  letI : Module (ZMod 3) V := imod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨cor, α, hα, hrefl, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso (p := 3) (by norm_num) hNoTr ggIntCartan_E₆
      (SecFiveRootRefl.entries_E 6) (SecFiveRootRefl.cartanTree_E 6 (by norm_num)) e he
      (fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ) ιV
  let simple : Fin 6 → MulAut ↥Bs :=
    fun i => ((e (CoxeterMatrix.E₆.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hsimple_apply : ∀ i v, ggLin (p := 3) ιV (simple i) v = v - α i v • cor i :=
    fun i v => by rw [hrefl i]; exact Module.reflection_apply v (hα i)
  have hAL : ggAutomizer L Bs = Subgroup.closure (Set.range simple) :=
    ggAutomizer_eq_closure_of_surj e.toMonoidHom e.surjective fun _ => rfl
  have hsimple_mem : ∀ i, simple i ∈ ggAutomizer L Bs := fun i => (e _).2
  have hci : ∀ i, cor i ≠ 0 := by
    intro i h0
    apply zmod_two_ne_zero (p := 3) (by norm_num)
    rw [← hα i, h0, map_zero]
  let xV : V := ιV (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hxV0 : xV ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
      apply ιV.injective
      simpa [xV] using h0
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      simpa using Additive.ofMul.injective h1
    exact congrArg (fun b : ↥Bs => (b : G)) h2
  have hxVfix : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := 3) ιV φ xV = xV := by
    intro φ hφ
    obtain ⟨a, haL, -, ha⟩ := mem_ggAutomizer_iff.mp hφ
    have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp (hLx haL)
    have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      apply Subtype.ext
      rw [ha]
      change a * x * a⁻¹ = x
      calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [hax]
        _ = x := by group
    change ggLin (p := 3) ιV φ (ιV (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = xV
    rw [ggLin_apply_ofMul, hφx]
  have hunder : ∀ i : Fin 6, ∃ c ∈ ggAutomizer L Bs, GGOverGamma hN c (hm.conjAut i) := by
    intro i
    obtain ⟨g, hgL, hg, -, hover⟩ :=
      exists_isReflection_overGamma_of_weylElt hp (by norm_num) hBs hSC hN
        (hm.torusWeylElt_w i) (hm.conj_w_mem_normalizer i) (hm.conjAut_isReflection i)
    exact ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgL hg, hover⟩
  have hfixγ : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → ggGamma L hN b = 1 := by
    intro b hb
    have hcoord : ∀ i : Fin 6,
        Multiplicative.toAdd (Φ ((ggGamma L hN).rangeRestrict b)) i = 0 := by
      intro i
      obtain ⟨c, hc, hover⟩ := hunder i
      have h1 := hover b
      rw [hb c hc] at h1
      have h2 := hm.conjAut_apply_toAdd i ((ggGamma L hN).rangeRestrict b)
      rw [← h1] at h2
      exact (adRefl_eq_self_iff i _).mp h2.symm
    have hzero : Φ ((ggGamma L hN).rangeRestrict b) = 1 := by
      have h0 : Multiplicative.toAdd (Φ ((ggGamma L hN).rangeRestrict b)) = 0 := funext hcoord
      simpa using congrArg Multiplicative.ofAdd h0
    have hrr : (ggGamma L hN).rangeRestrict b = 1 :=
      hm.injective (hzero.trans (map_one Φ).symm)
    simpa using congrArg Subtype.val hrr
  have hfixed_x : ggFixedSubmodule (p := 3) ιV (ggAutomizer L Bs) =
      Submodule.span (ZMod 3) {xV} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ιV (Additive.ofMul b) = v :=
        ⟨Additive.toMul (ιV.symm v), by simp⟩
      have hbfix : ∀ φ ∈ ggAutomizer L Bs, φ b = b := fun φ hφ =>
        (ggLin_apply_ofMul_eq_iff ιV φ b b).mp (mem_ggFixedSubmodule_iff.mp hv φ hφ)
      rw [span_singleton_eq_ggLinImage ιV hxBs, ofMul_mem_ggLinImage, ← hBL]
      exact ⟨b.2, (ggGamma_eq_one_iff L hN b).mp (hfixγ b hbfix)⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_ggFixedSubmodule_iff.mpr hxVfix
  have hroot_xV : ∀ i, α i xV = 0 := by
    intro i
    have heq := hsimple_apply i xV
    rw [hxVfix (simple i) (hsimple_mem i)] at heq
    have hzero : α i xV • cor i = 0 := sub_eq_self.mp heq.symm
    exact (smul_eq_zero.mp hzero).resolve_right (hci i)
  have hker : (LinearMap.pi α).ker = Submodule.span (ZMod 3) {xV} := by
    apply le_antisymm
    · intro v hv
      have hv' : ∀ i, α i v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hv) i
      rw [← hfixed_x, hAL, ← Set.image_univ]
      exact (mem_ggFixedSubmodule_closure_iff (p := 3) (by norm_num) ιV simple cor α
        hsimple_apply hα Set.univ v).mpr fun i _ => hv' i
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine LinearMap.mem_ker.mpr ?_
      funext i
      exact hroot_xV i
  have hrank : 6 ≤ ((CartanMatrix.E 6).map (Int.castRingHom (ZMod 3))).rank + 1 := by
    simpa using ggIntCartan_card_le_rank_add_one (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))
      ggIntCartan_E₆ 3 (by norm_num)
  have hshape := ggQ2_shape_linear (p := 3) hrank cor α hpair hxV0 hker
  have hmove : ∀ φ ∈ ggAutomizer L Bs, ∀ v : V,
      v - ggLin (p := 3) ιV φ v ∈ Submodule.span (ZMod 3) (Set.range cor) := by
    intro φ hφ
    rw [hAL] at hφ
    induction hφ using Subgroup.closure_induction with
    | mem φ hφ =>
      obtain ⟨i, rfl⟩ := hφ
      intro v
      rw [hsimple_apply, sub_sub_cancel]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | one =>
      intro v
      rw [map_one, LinearEquiv.coe_one, id, sub_self]
      exact Submodule.zero_mem _
    | mul φ ψ _ _ hφ hψ =>
      intro v
      have hsplit : v - ggLin (p := 3) ιV (φ * ψ) v = (v - ggLin (p := 3) ιV ψ v) +
          (ggLin (p := 3) ιV ψ v - ggLin (p := 3) ιV φ (ggLin (p := 3) ιV ψ v)) := by
        rw [map_mul, LinearEquiv.mul_apply]
        abel
      rw [hsplit]
      exact Submodule.add_mem _ (hψ v) (hφ _)
    | inv φ _ hφ =>
      intro v
      have h1 := hφ (ggLin (p := 3) ιV φ⁻¹ v)
      have h2 : ggLin (p := 3) ιV φ (ggLin (p := 3) ιV φ⁻¹ v) = v := by
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one,
          id]
      rw [h2] at h1
      have hneg : v - ggLin (p := 3) ιV φ⁻¹ v = -(ggLin (p := 3) ιV φ⁻¹ v - v) := by abel
      rw [hneg]
      exact Submodule.neg_mem _ h1
  have hmoveL : ∀ φ ∈ ggAutomizer L Bs, ∀ v : V,
      v - ggLin (p := 3) ιV φ v ∈ ggLinImage (p := 3) ιV L := by
    intro φ hφ v
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ιV (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ιV.symm v), by simp⟩
    rw [← neg_sub, ggLin_apply_ofMul_sub]
    refine Submodule.neg_mem _ ((ofMul_mem_ggLinImage ιV L _).mpr ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hg b]
    have hbg : (b : G) * g⁻¹ * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hN b.2) g⁻¹).mp (L.inv_mem hgL)
    have hcomm : g * (b : G) * g⁻¹ * (b : G)⁻¹ = g * ((b : G) * g⁻¹ * (b : G)⁻¹) := by group
    rw [hcomm]
    exact L.mul_mem hgL hbg
  have hmem : x ∈ L ↔ xV ∈ Submodule.span (ZMod 3) (Set.range cor) := by
    constructor
    · intro hxL
      have hcomm := hX G 3 B Bs x L D J hset hxL hE6
      let Hs : Subgroup G := (AddSubgroup.toSubgroup'
        ((Submodule.span (ZMod 3) (Set.range cor)).toAddSubgroup.comap
          ιV.toAddMonoidHom)).map Bs.subtype
      have hle : ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ ≤ Hs := by
        rw [Subgroup.commutator_le]
        intro b hb g hg
        have hc : ggConjAut Bs hg.2 ∈ ggAutomizer L Bs := ggConjAut_mem_ggAutomizer hg.1 hg.2
        refine Subgroup.mem_map.mpr ⟨⟨b, hb⟩ * (ggConjAut Bs hg.2 ⟨b, hb⟩)⁻¹, ?_, ?_⟩
        · rw [AddSubgroup.mem_toSubgroup', AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
            AddEquiv.coe_toAddMonoidHom, ofMul_mul, ofMul_inv, map_add, map_neg,
            ← sub_eq_add_neg, ← ggLin_apply_ofMul (p := 3)]
          exact hmove _ hc _
        · rw [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply,
            commutatorElement_def]
          group
      obtain ⟨b, hbS, hbx⟩ := Subgroup.mem_map.mp (hle hcomm)
      have hb : b = ⟨x, hxBs⟩ := Subtype.ext hbx
      subst hb
      rw [AddSubgroup.mem_toSubgroup', AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
        AddEquiv.coe_toAddMonoidHom] at hbS
      exact hbS
    · intro hxH
      have hle : Submodule.span (ZMod 3) (Set.range cor) ≤ ggLinImage (p := 3) ιV L := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have hci2 : cor i = (2 : ZMod 3) • (cor i - ggLin (p := 3) ιV (simple i) (cor i)) := by
          rw [hsimple_apply, hα i, sub_sub_cancel, smul_smul]
          have h4 : (2 : ZMod 3) * 2 = 1 := rfl
          rw [h4, one_smul]
        rw [hci2]
        exact Submodule.smul_mem _ _ (hmoveL _ (hsimple_mem i) _)
      exact (ofMul_mem_ggLinImage ιV L ⟨x, hxBs⟩).mp (hle hxH)
  let Dm : GGQ2LDatum 3 Bs L x :=
    { Λ := Fin 6
      coxeter := CoxeterMatrix.E₆
      cartan := CartanMatrix.E 6
      V := V
      model := ιV
      hx := hxBs
      simple := simple
      coroot := cor
      root := α
      isWeyl := Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)
      isCartan := ggIntCartan_E₆
      pairing := hpair
      simple_apply := hsimple_apply
      automizer_L := hAL
      fixed_x := hfixed_x }
  have hDshape : Dm.Shape := by
    change Dm.ShapeFull ∨ Dm.ShapeA ∨ Dm.ShapeB ∨ Dm.ShapeC ∨ Dm.ShapeD
    rcases hshape with ⟨hLI, hxVH, hsup⟩ | ⟨hLI, hxVH, hdim, hsurj⟩ |
      ⟨hfin, hxVH, hsup⟩ | ⟨hfin, hxVH, hdim, hsurj⟩ | ⟨hLI, htop⟩
    · refine Or.inl ⟨fun hxL => hxVH (hmem.mp hxL), hLI, ?_, ?_⟩
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hsup
    · refine Or.inr (Or.inl ⟨hmem.mpr hxVH, hLI, ?_, ?_, ?_⟩)
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · dsimp only [Dm]
        simpa using hdim
      · simpa [GGQ2LDatum.rootMap] using hsurj
    · refine Or.inr (Or.inr (Or.inl ⟨fun hxL => hxVH (hmem.mp hxL), ?_, ?_, ?_⟩))
      · exact hfin.trans (Fintype.card_fin 6).symm
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hsup
    · refine Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fun hxL => hxVH (hmem.mp hxL), ?_, ?_, ?_, ?_⟩)))
      · exact hfin.trans (Fintype.card_fin 6).symm
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · dsimp only [Dm]
        simpa using hdim
      · simpa [GGQ2LDatum.rootMap] using hsurj
    · have hxVH : xV ∈ Submodule.span (ZMod 3) (Set.range cor) := by
        rw [htop]
        exact Submodule.mem_top
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hmem.mpr hxVH, hLI, ?_⟩)))
      simpa [GGQ2LDatum.coSpan] using htop
  exact ⟨lab, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSl))))),
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩,
    Dm, hWlab, hDshape, fun _ => Or.inr hSl⟩

end CFSG.StandardType

end
