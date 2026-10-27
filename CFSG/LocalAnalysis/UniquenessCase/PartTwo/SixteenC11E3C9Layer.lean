module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFramePSL
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s1611e3_frame_commutator_prod {Z S : Type*} [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) :
    commutator (Z × S × S) =
      (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) := by
  rw [_root_.commutator_def]
  simp only [← Subgroup.top_prod_top]
  rw [Subgroup.commutator_prod_prod, Subgroup.commutator_prod_prod]
  simp only [show ⁅(⊤ : Subgroup Z), ⊤⁆ = ⊥ from commutator_eq_bot Z,
    show ⁅(⊤ : Subgroup S), ⊤⁆ = ⊤ from hperf.commutator_eq_top]

private noncomputable def s1611e3_prod_commutator_equiv (Z S : Type*) [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) :
    ↥(commutator (Z × S × S)) ≃* S × S := by
  rw [s1611e3_frame_commutator_prod hperf]
  exact (Subgroup.prodEquiv (⊥ : Subgroup Z) ((⊤ : Subgroup S).prod (⊤ : Subgroup S))).trans
    ((MulEquiv.uniqueProd (M := ↥((⊤ : Subgroup S).prod (⊤ : Subgroup S)))
        (N := ↥(⊥ : Subgroup Z))).trans
      ((Subgroup.prodEquiv (⊤ : Subgroup S) (⊤ : Subgroup S)).trans
        (MulEquiv.prodCongr Subgroup.topEquiv Subgroup.topEquiv)))

private lemma s1611e3_commutator_iso {F Z S : Type*} [Group F] [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) (e : F ≃* Z × S × S) :
    Nonempty (↥(commutator F) ≃* S × S) := by
  have hmap : (commutator F).map (e : F →* Z × S × S) = commutator (Z × S × S) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  refine ⟨(Subgroup.equivMapOfInjective (commutator F) (e : F →* Z × S × S)
    e.injective).trans ?_⟩
  rw [hmap]
  exact s1611e3_prod_commutator_equiv Z S hperf

theorem s1611e3_case9_layer {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h9 : Case168_9 D V₀ V hV L) :
    ∃ (E : Subgroup ↥(Mbar D.M V₀ V hV)) (hE : E.Normal),
      Nonempty (↥E ≃* ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) ∧
      haveI := hE
      Group.IsSolvable (↥(Mbar D.M V₀ V hV) ⧸ E) := by
  classical
  obtain ⟨⟨e⟩, hL3, -, -, -⟩ := h9
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let Fs : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar Mb
  let Fb : Subgroup ↥Mb := Fs.subgroupOf Mb
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts Mb
  haveI hFbN : Fb.Normal := ⟨fun a ha b => hFn b.1 b.2 a.1 ha⟩
  have hL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hSC : CFSG.ComponentClassification.AutL2Facts.SimpleCentreless ↥(lBar V₀ V hV L) :=
    s16c167_isPSL_simpleCentreless hL
  have hperf : Group.IsPerfect ↥(lBar V₀ V hV L) := s16c167_isPSL_isPerfect hL
  have hout : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(lBar V₀ V hV L)) :=
    s16c167_isPSL_outer_solvable hL
  have eFb : ↥Fb ≃* Multiplicative (ZMod 7) ×
      (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) :=
    (Subgroup.subgroupOfEquivOfLe hFX).trans e
  have hcommIso : Nonempty (↥(commutator ↥Fb) ≃*
      (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L))) :=
    s1611e3_commutator_iso hperf eFb
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsCyclic (Multiplicative (ZMod 7)) :=
    isCyclic_of_prime_card (p := 7) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  have hOutFb : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Fb) :=
    s16c167_frame_outer_cyclic_square_solvable hSC hperf hout eFb
  let ψ : ↥Mb →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Fb :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Fb)).comp
      (MulAut.conjNormal (H := Fb))
  have hkerψ : ψ.ker = Fb := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      change QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Fb)
        (MulAut.conjNormal (H := Fb) x) = 1 at hx
      have hx' : MulAut.conjNormal (H := Fb) x ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Fb :=
        (QuotientGroup.eq_one_iff (MulAut.conjNormal (H := Fb) x)).mp hx
      obtain ⟨h, hh⟩ := hx'
      have hcent : (h : ↥Mb)⁻¹ * x ∈ Fb := by
        change (h : ↥Mb)⁻¹ * x ∈ Fs.subgroupOf Mb
        rw [Subgroup.mem_subgroupOf]
        refine hself ((h : ↥Mb)⁻¹ * x).1 ((h : ↥Mb)⁻¹ * x).2 ?_
        intro f hf
        let yf : ↥Fb := ⟨⟨f, hFX hf⟩, hf⟩
        have h1 : MulAut.conj h yf = MulAut.conjNormal (H := Fb) x yf :=
          congrArg (fun φ : MulAut ↥Fb => φ yf) hh
        have h2 : (h : ↥Mb) * (yf : ↥Mb) * (h : ↥Mb)⁻¹ =
            x * (yf : ↥Mb) * x⁻¹ := by
          have h1' := congrArg (fun z : ↥Fb => (z : ↥Mb)) h1
          simpa only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
            Subgroup.coe_inv] using h1'
        have h3 : ((h : ↥Mb)⁻¹ * x) * (yf : ↥Mb) =
            (yf : ↥Mb) * ((h : ↥Mb)⁻¹ * x) := by
          calc ((h : ↥Mb)⁻¹ * x) * (yf : ↥Mb)
              = (h : ↥Mb)⁻¹ * (x * (yf : ↥Mb) * x⁻¹) * x := by group
            _ = (h : ↥Mb)⁻¹ * ((h : ↥Mb) * (yf : ↥Mb) * (h : ↥Mb)⁻¹) * x := by rw [← h2]
            _ = (yf : ↥Mb) * ((h : ↥Mb)⁻¹ * x) := by group
        simpa using congrArg Subtype.val h3
      rw [show x = (h : ↥Mb) * ((h : ↥Mb)⁻¹ * x) by group]
      exact Fb.mul_mem h.2 hcent
    · intro hx
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Fb)
        (MulAut.conjNormal (H := Fb) x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Fb) := hOutFb
  have hAF : Group.IsSolvable (↥Mb ⧸ Fb) := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := QuotientGroup.lift Fb ψ hkerψ.symm.le) ?_
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hkerψ,
      QuotientGroup.map_mk'_self]
  haveI : Group.IsSolvable (↥Mb ⧸ Fb) := hAF
  let E : Subgroup ↥Mb := (commutator ↥Fb).map Fb.subtype
  have hE : E.Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := Fb) (K := commutator ↥Fb)
  haveI : E.Normal := hE
  have hEFb : E ≤ Fb := Subgroup.map_subtype_le (commutator ↥Fb)
  have hEcomm : E = ⁅Fb, Fb⁆ := by
    change (commutator ↥Fb).map Fb.subtype = ⁅Fb, Fb⁆
    rw [_root_.commutator_def, Subgroup.map_commutator]
    congr 1 <;> rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hab : IsMulCommutative ↥(Fb.map (QuotientGroup.mk' E)) :=
    (Subgroup.commutator_self_eq_bot_iff (H := Fb.map (QuotientGroup.mk' E))).mp (by
      rw [← Subgroup.map_commutator, ← hEcomm, QuotientGroup.map_mk'_self])
  haveI : IsMulCommutative ↥(Fb.map (QuotientGroup.mk' E)) := hab
  have hQuot : Group.IsSolvable ((↥Mb ⧸ E) ⧸ Fb.map (QuotientGroup.mk' E)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientQuotientEquivQuotient E Fb hEFb).toMonoidHom)
      (QuotientGroup.quotientQuotientEquivQuotient E Fb hEFb).injective
  haveI : Group.IsSolvable ((↥Mb ⧸ E) ⧸ Fb.map (QuotientGroup.mk' E)) := hQuot
  have hSol : Group.IsSolvable (↥Mb ⧸ E) :=
    Group.isSolvable_of_subgroup_quotient (Fb.map (QuotientGroup.mk' E))
  refine ⟨E, hE, ⟨?_, ?_⟩⟩
  · exact ⟨(Subgroup.equivMapOfInjective (commutator ↥Fb) Fb.subtype
      Fb.subtype_injective).symm.trans hcommIso.some⟩
  · exact hSol

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
