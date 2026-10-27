module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCGraphDefs
import Mathlib.Algebra.Group.TypeTags.Basic
import CFSG.LocalAnalysis.StandardType.GGQTwoLDatumWeyl
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
import CFSG.LocalAnalysis.StandardType.GGQTwoCor123
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2gl_layer_le {G : Type} [Group G] (H : Subgroup G) : LargeEvenLayer H ≤ H := by
  change sSup {K : Subgroup G | IsComponentOf K H} ≤ H
  exact sSup_le fun K hK => hK.1

private lemma ggQ2gl_kernel_eq_bot (D : GGQ2WDatum 3)
    (hdet : ((D.cartan.det : ℤ) : ZMod 3) ≠ 0) :
    ∀ v ∈ D.corootSpan, (∀ i, D.root i v = 0) → v = 0 := by
  intro v hv hroot
  rw [GGQ2WDatum.corootSpan, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  have hmat : ((Int.castRingHom (ZMod 3)).mapMatrix D.cartan).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdet
  have h0 : ((Int.castRingHom (ZMod 3)).mapMatrix D.cartan).mulVec c = 0 := by
    funext j
    have h := hroot j
    rw [← hc] at h
    simp only [map_sum, map_smul, smul_eq_mul, D.pairing] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hmat h0
  rw [hc0] at hc
  simpa using hc.symm

private lemma ggQ2gl_det_ne_zero {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hLW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (htag : labL.tag = .D ∨ labL.tag = .F4) :
    ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
  rcases htag with htag | htag
  ·
    have h4' : Even labL.rank ∧ 4 ≤ labL.rank := by simpa [GGQ2TBLabel, htag] using hlab
    have hLW' : ∃ e : Fin labL.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD labL.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hC : GGIntCartan ((ggCoxeterMatrixD labL.rank).reindex e) M.cartan := by
      rw [← he]; exact M.isCartan
    have hC0 : GGIntCartan ((ggCoxeterMatrixD labL.rank).reindex e)
        (Matrix.reindex e e (CartanMatrix.D labL.rank)) := (ggIntCartan_D labL.rank).reindex e
    have hone : GGAtMostOneMultipleEdge ((ggCoxeterMatrixD labL.rank).reindex e) :=
      (ggAtMostOneMultipleEdge_D labL.rank).reindex e
    have hdet : M.cartan.det = (CartanMatrix.D labL.rank).det := by
      rcases hC.eq_or_eq_transpose hC0 hone with h | h
      · rw [h, Matrix.det_reindex_self e (CartanMatrix.D labL.rank)]
      · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e (CartanMatrix.D labL.rank)]
    rw [hdet, CartanMatrix.D_det (show 2 ≤ labL.rank by omega)]
    intro hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    norm_num at hz
  ·
    have hLW' : ∃ e : Fin 4 ≃ M.Λ, M.coxeter = CoxeterMatrix.F₄.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hC : GGIntCartan (CoxeterMatrix.F₄.reindex e) M.cartan := by
      rw [← he]; exact M.isCartan
    have hC0 : GGIntCartan (CoxeterMatrix.F₄.reindex e)
        (Matrix.reindex e e CartanMatrix.F₄) := (ggIntCartan_F₄).reindex e
    have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.F₄.reindex e) :=
      (ggAtMostOneMultipleEdge_F₄).reindex e
    have hdet : M.cartan.det = CartanMatrix.F₄.det := by
      rcases hC.eq_or_eq_transpose hC0 hone with h | h
      · rw [h, Matrix.det_reindex_self e CartanMatrix.F₄]
      · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e CartanMatrix.F₄]
    rw [hdet, CartanMatrix.F₄_det]
    norm_num

private lemma ggQ2gl_fix {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) :
    ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := by
  intro v
  have hfixed : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) ↔
      ∀ g ∈ M.toWDatum.weyl, g v = v := by
    rw [M.weyl_eq_map, mem_ggFixedSubmodule_iff]
    constructor
    · rintro h g hg
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      exact h φ hφ
    · intro h φ hφ
      exact h (ggLin (p := 3) M.model φ) (Subgroup.mem_map_of_mem _ hφ)
  rw [← hfixed, M.fixed_x]
  rfl

noncomputable def ggQ2gl_E {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (D : Subgroup G) : Submodule (ZMod 3) M.V where
  carrier := {v | ∃ b : ↥Bs, (b : G) ∈ D ∧ M.model (Additive.ofMul b) = v}
  add_mem' := by
    rintro v w ⟨b, hbD, rfl⟩ ⟨c, hcD, rfl⟩
    exact ⟨b * c, by rw [Subgroup.coe_mul]; exact D.mul_mem hbD hcD, by
      rw [ofMul_mul, map_add]⟩
  zero_mem' := ⟨1, D.one_mem, by simp⟩
  smul_mem' := by
    rintro n v ⟨b, hbD, rfl⟩
    refine ⟨b ^ n.val, by rw [Subgroup.coe_pow]; exact pow_mem hbD n.val, ?_⟩
    rw [ofMul_pow]
    rw [show M.model (n.val • Additive.ofMul b) = n.val • M.model (Additive.ofMul b) from
      (M.model.toAddMonoidHom).map_nsmul n.val (Additive.ofMul b)]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) n.val, ZMod.natCast_zmod_val]

theorem ggQ2gl_mem_E {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (D : Subgroup G) {v : M.V} :
    v ∈ ggQ2gl_E M D ↔ ∃ b : ↥Bs, (b : G) ∈ D ∧ M.model (Additive.ofMul b) = v :=
  Iff.rfl

noncomputable def ggQ2gl_E_equiv {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {D : Subgroup G} (hDBs : D ≤ Bs) :
    ↥(ggQ2gl_E M D) ≃ ↥D :=
  (Equiv.ofBijective
    (fun d : ↥D => (⟨M.model (Additive.ofMul ⟨(d : G), hDBs d.2⟩),
      (ggQ2gl_mem_E M D).mpr ⟨⟨(d : G), hDBs d.2⟩, d.2, rfl⟩⟩ : ↥(ggQ2gl_E M D)))
    ⟨fun d₁ d₂ h => by
      have h' : M.model (Additive.ofMul ⟨(d₁ : G), hDBs d₁.2⟩) =
          M.model (Additive.ofMul ⟨(d₂ : G), hDBs d₂.2⟩) := congrArg Subtype.val h
      have h2 : (⟨(d₁ : G), hDBs d₁.2⟩ : ↥Bs) = ⟨(d₂ : G), hDBs d₂.2⟩ :=
        Additive.ofMul.injective (M.model.injective h')
      apply Subtype.ext
      exact congrArg (fun y : ↥Bs => (y : G)) h2,
    fun v => by
      obtain ⟨b, hbD, hbEq⟩ := (ggQ2gl_mem_E M D).mp v.2
      refine ⟨⟨(b : G), hbD⟩, ?_⟩
      apply Subtype.ext
      show M.model (Additive.ofMul ⟨(b : G), hDBs hbD⟩) = (v : M.V)
      have hbk : (⟨(b : G), hDBs hbD⟩ : ↥Bs) = b := Subtype.ext rfl
      rw [hbk]
      exact hbEq⟩).symm

private lemma ggQ2gl_transvectionFree {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {J : Subgroup G} (hNT : GGNoTransvection 3 Bs) :
    TransvectionFree ((ggAutomizer J Bs).map (ggLin (p := 3) M.model)) := by
  rintro g hg ⟨u, f, hu, hf, hfu, hgv⟩
  rw [Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  obtain ⟨k, -, hkN, hkφ⟩ := mem_ggAutomizer_iff.mp hφ
  exact hNT φ ⟨k, Subgroup.mem_top k, hkN, hkφ⟩
    (ggIsTransvection_of_apply M.model hu hf hfu hgv)

private lemma ggQ2gl_finrank_E {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {D : Subgroup G} (hDBs : D ≤ Bs)
    (hcard : Nat.card ↥D = 9) : Module.finrank (ZMod 3) ↥(ggQ2gl_E M D) = 2 := by
  have hfinV : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hfinE : Finite ↥(ggQ2gl_E M D) :=
    Finite.of_injective (fun v : ↥(ggQ2gl_E M D) => (v : M.V)) (fun _ _ h => Subtype.ext h)
  have hcardE : Nat.card ↥(ggQ2gl_E M D) = 9 := by
    rw [Nat.card_congr (ggQ2gl_E_equiv M hDBs)]
    exact hcard
  have hpow : 3 ^ Module.finrank (ZMod 3) ↥(ggQ2gl_E M D) = 3 ^ 2 := by
    rw [FiniteField.pow_finrank_eq_natCard 3 ↥(ggQ2gl_E M D), hcardE]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow

private lemma ggQ2gl_shapeFull {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hxV0 : M.xV ≠ 0)
    (hdetW : ((M.toWDatum.cartan.det : ℤ) : ZMod 3) ≠ 0)
    (hfix : ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV})
    (hind : LinearIndependent (ZMod 3) M.coroot) (hshape : M.Shape) : M.ShapeFull := by
  have hfin : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
    rw [GGQ2LDatum.coSpan]
    exact finrank_span_eq_card hind
  have hxH : M.xV ∉ M.coSpan := by
    intro hxspan
    have hroot0 : ∀ i : M.Λ, M.root i M.xV = 0 := by
      intro i
      have hfixi := (hfix M.xV).mpr (Submodule.mem_span_singleton_self M.xV)
        (M.toWDatum.simpleRefl i) (M.toWDatum.simpleRefl_mem_weyl i)
      have h2 := GGQ2WDatum.simpleRefl_apply M.toWDatum i M.xV
      rw [h2] at hfixi
      have h0 : M.root i M.xV • M.coroot i = 0 := sub_eq_self.mp hfixi
      have h1 := congrArg (M.root i) h0
      rw [map_smul, smul_eq_mul, show M.root i (M.coroot i) = 2 from
        M.toWDatum.root_coroot_self i, map_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_right (by decide : (2 : ZMod 3) ≠ 0)
    exact hxV0 (ggQ2gl_kernel_eq_bot M.toWDatum hdetW M.xV hxspan hroot0)
  rcases hshape with hF | hA | hB | hC | hD
  · exact hF
  · exact absurd hA.2.2.1 hxH
  · exact absurd (hfin ▸ hB.2.1) (by omega)
  · exact absurd (hfin ▸ hC.2.1) (by omega)
  · exact absurd (hD.2.2 ▸ Submodule.mem_top) hxH

theorem ggQ2_shapeFull_of_graph {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hLW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (htag : labL.tag = .D ∨ labL.tag = .F4) (hx1 : x ≠ 1)
    (hshape : M.Shape) : M.ShapeFull := by
  have hxV0 : M.xV ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h0)
    have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hx1 (Subtype.ext_iff.mp h2)
  have hdet : ((M.toWDatum.cartan.det : ℤ) : ZMod 3) ≠ 0 := ggQ2gl_det_ne_zero M hLW hlab htag
  exact ggQ2gl_shapeFull M hxV0 hdet (ggQ2gl_fix M)
    (GGQ2WDatum.coroot_linearIndependent_of_det M.toWDatum hdet) hshape

theorem ggQ2_gammaXOffI1Graph_of_core (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hcore : GGQ2GraphCoreAll) (hTBC : GGQ2TBCGraphInput) : GGQ2GammaXOffI1GraphInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hCav _ labL hmark htag M hLW hshape
  subst hp
  classical
  let D' : GGQ2WDatum 3 :=
    { Λ := M.Λ
      coxeter := M.coxeter
      cartan := M.cartan
      V := M.V
      coroot := M.coroot
      root := M.root
      isWeyl := M.isWeyl
      isCartan := M.isCartan
      pairing := M.pairing }
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hSstar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hx_D : x ∈ D := hStdSub.1.2.2.2.1
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hDcard : Nat.card ↥D = 9 := by simpa using hStdSub.1.2.2.1
  have hJeq : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hStdSub.1.2.2.2.2.1
  have hJcentD : J ≤ Subgroup.centralizer (D : Set G) := by
    rw [hJeq]
    exact (ggQ2gl_layer_le _).trans inf_le_right
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hCav
    norm_num at hCav
  have hweyl : D'.weyl = (ggAutomizer L Bs).map (ggLin (p := 3) M.model) :=
    GGQ2LDatum.weyl_eq_map M
  have hfix2 : ∀ v : D'.V, (∀ g ∈ D'.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := ggQ2gl_fix M
  have hxV0 : M.xV ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h0)
    have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hx1 (Subtype.ext_iff.mp h2)
  have hdet : ((D'.cartan.det : ℤ) : ZMod 3) ≠ 0 := ggQ2gl_det_ne_zero M hLW hmark.2.1 htag
  have hind : LinearIndependent (ZMod 3) D'.coroot :=
    GGQ2WDatum.coroot_linearIndependent_of_det D' hdet
  have hshapeFull : M.ShapeFull := ggQ2gl_shapeFull M hxV0 hdet hfix2 hind hshape
  obtain ⟨-, -, hxH, hsup⟩ := hshapeFull
  have hxE : M.xV ∈ ggQ2gl_E M D := (ggQ2gl_mem_E M D).mpr ⟨⟨x, M.hx⟩, hx_D, rfl⟩
  have hE2 : Module.finrank (ZMod 3) ↥(ggQ2gl_E M D) = 2 := ggQ2gl_finrank_E M hDBs hDcard
  let A : Subgroup (D'.V ≃ₗ[ZMod 3] D'.V) := (ggAutomizer J Bs).map (ggLin (p := 3) M.model)
  have hAE : ∀ a ∈ A, ∀ v ∈ ggQ2gl_E M D, a v = v := by
    rintro a ha v hv
    obtain ⟨b, hbD, rfl⟩ := (ggQ2gl_mem_E M D).mp hv
    obtain ⟨ψ, hψJ, rfl⟩ := Subgroup.mem_map.mp ha
    rw [ggLin_apply_ofMul]
    have hcen : J ≤ Subgroup.centralizer ({(b : G)} : Set G) :=
      hJcentD.trans (Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hbD))
    rw [ggAutomizer_apply_eq_of_le_centralizer hcen hψJ]
  have hTF : TransvectionFree A := ggQ2gl_transvectionFree M hS.1.2.2.2.1
  have hCavA : 4 ∣ Nat.card A := by
    rw [Subgroup.card_map_of_injective (ggLin_injective (p := 3) M.model)]
    exact hCav
  have hfixA : ∃ v : D'.V, (∀ a ∈ A, a v = v) ∧ v ∉ ggQ2gl_E M D := by
    have hI1' : ∃ b : G, b ∈ Bs ∧ (∀ j ∈ J, b * j = j * b) ∧ b ∉ D := by
      by_contra hcon
      refine hI1 (fun b hb hc => ?_)
      by_contra hbD
      exact hcon ⟨b, hb, hc, hbD⟩
    obtain ⟨b, hbBs, hbcent, hbD⟩ := hI1'
    refine ⟨M.model (Additive.ofMul ⟨b, hbBs⟩), ?_, ?_⟩
    · rintro a ha
      obtain ⟨ψ, hψJ, rfl⟩ := Subgroup.mem_map.mp ha
      rw [ggLin_apply_ofMul]
      have hcen : J ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
        intro j hj
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hbcent j hj
      rw [ggAutomizer_apply_eq_of_le_centralizer hcen hψJ]
    · intro hmem
      obtain ⟨c, hcD, hcEq⟩ := (ggQ2gl_mem_E M D).mp hmem
      have hcb : c = (⟨b, hbBs⟩ : ↥Bs) :=
        Additive.ofMul.injective (M.model.injective hcEq)
      exact hbD (by simpa [hcb] using hcD)
  have hTBCmodel : ∀ t ∈ D'.weyl, IsReflLin t →
      (∀ v ∈ ggQ2gl_E M D, t v = v) → t ∈ A ∨ ∀ a ∈ A, t * a = a * t := by
    intro t ht hrefl hEfix
    rw [hweyl] at ht
    obtain ⟨ψ, hψL, hψt⟩ := Subgroup.mem_map.mp ht
    obtain ⟨c, f, hfc, htc⟩ := hrefl
    have hψrefl : GGIsReflection 3 ψ :=
      ggIsReflection_of_eq_reflection (p := 3) (by decide) M.model hfc (by rw [hψt]; exact htc)
    have hψD : ∀ b : ↥Bs, (b : G) ∈ D → ψ b = b := by
      intro b hbD
      have h1 : t (M.model (Additive.ofMul b)) = M.model (Additive.ofMul b) :=
        hEfix _ ((ggQ2gl_mem_E M D).mpr ⟨b, hbD, rfl⟩)
      rw [← hψt, ggLin_apply_ofMul] at h1
      exact Additive.ofMul.injective (M.model.injective h1)
    rcases hTBC hS rfl hI1 hCav hmark htag M hLW hshape ψ hψL hψrefl hψD with hψJ | hψcomm
    · left
      rw [← hψt]
      exact Subgroup.mem_map.mpr ⟨ψ, hψJ, rfl⟩
    · right
      intro a ha
      obtain ⟨χ, hχJ, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← hψt, ← map_mul, ← map_mul, hψcomm χ hχJ]
  intro g hg hgx
  let φ : MulAut ↥Bs := ggConjAut Bs hg
  have hφ : φ ∈ ggAutomizer ⊤ Bs := ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  have hφg : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := fun b => ggConjAut_apply Bs hg b
  have hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow, ggConjAut_apply]
    exact hk
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hS.1 hAJ M.hx hφ hφx
  let T : D'.V ≃ₗ[ZMod 3] D'.V := ggLin (p := 3) M.model φ
  have hTnorm : T ∈ Subgroup.normalizer (D'.weyl : Set (D'.V ≃ₗ[ZMod 3] D'.V)) := by
    rw [hweyl]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  obtain ⟨w, hw, hwE⟩ := hcore D' hmark.2.1 htag hLW M.xV hxV0 hfix2 hind hxH hsup
    (ggQ2gl_E M D) hxE hE2 A hAE hTF hCavA hfixA hTBCmodel T hTnorm
  have hwT : T * w * T⁻¹ ∈ D'.weyl :=
    (Subgroup.mem_normalizer_iff.mp hTnorm w).mp hw
  rw [hweyl] at hwT
  obtain ⟨ψ, hψL, hψw⟩ := Subgroup.mem_map.mp hwT
  have hD' : ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D := by
    intro b hbD
    have hmem : M.model (Additive.ofMul ((ψ * φ) b)) ∈ ggQ2gl_E M D := by
      have h1 : M.model (Additive.ofMul ((ψ * φ) b)) = T (w (M.model (Additive.ofMul b))) := by
        rw [← ggLin_apply_ofMul (p := 3) M.model (ψ * φ) b, map_mul,
          LinearEquiv.mul_apply, hψw]
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        congr 2
        exact T.symm_apply_apply _
      rw [h1]
      exact hwE _ ((ggQ2gl_mem_E M D).mpr ⟨b, hbD, rfl⟩)
    obtain ⟨c, hcD, hcEq⟩ := (ggQ2gl_mem_E M D).mp hmem
    have hcb : c = (ψ * φ) b := Additive.ofMul.injective (M.model.injective hcEq)
    simpa [hcb] using hcD
  obtain ⟨k, hkL, hkN, hψk⟩ := mem_ggAutomizer_iff.mp hψL
  have hψφg : ∀ b : ↥Bs, (((ψ * φ) b : ↥Bs) : G) = (k * g) * b * (k * g)⁻¹ := by
    intro b
    rw [MulAut.mul_apply, hψk (φ b), hφg b]
    group
  have hmBs : k * g ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hkN hg
  have hmD : k * g ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_fintype (S := (D : Set G)) (fun n hn => by
      have hb := hD' ⟨n, hDBs hn⟩ hn
      rwa [hψφg ⟨n, hDBs hn⟩] at hb)
  have hmG0 : k * g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    ggQ2n_normalizer_inf_le hLB hP hS.1 rfl hCav (Subgroup.mem_inf.mpr ⟨hmBs, hmD⟩)
  have hkG0 : k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    Subgroup.le_normalizer (le_ggG0_left 3 B x L D J hkL)
  have hgG0 : g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    have h : k⁻¹ * (k * g) ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hkG0) hmG0
    simpa using h
  exact hgG0

end CFSG.StandardType

end
