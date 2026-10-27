module

public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly


@[expose] def GGStructSOneComp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (G₀ A : Subgroup X),
    p.Prime → p ≠ 2 → IsSimpleGroup ↥G₀ → IsElemAbelian p A →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    ∀ C : Subgroup X, IsComponentOf C (Subgroup.centralizer (A : Set X) ⊓ G₀) →
      LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True)

@[expose] def GGStructSOnePerf : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (G₀ A : Subgroup X),
    p.Prime → p ≠ 2 → IsSimpleGroup ↥G₀ → IsElemAbelian p A →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    ∀ P : Subgroup X, P ≤ Subgroup.centralizer (A : Set X) ⊓ G₀ → ⁅P, P⁆ = P →
      P ≤ LargeEvenLayer (Subgroup.centralizer (A : Set X) ⊓ G₀)

theorem s1Setup {X : Type} [Group X] [Finite X] {p : ℕ} {G₀ A : Subgroup X} (hp : p.Prime)
    (hp2 : p ≠ 2) (hG₀ : IsSimpleGroup ↥G₀) (hA : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hM : LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ)) :
    (∃ a b : ↥G₀, a * b ≠ b * a) ∧ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 ↥G₀ ∧
      ∃ E : Subgroup (MulAut ↥G₀), IsElemAbelian p E ∧
        (CFSG.LocalAnalysis.GLTheoremA.I142.centFix E).map G₀.subtype =
          Subgroup.centralizer (A : Set X) ⊓ G₀ := by
  haveI := hG₀
  have hnc : ∃ a b : ↥G₀, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hbot : commutator ↥G₀ = ⊥ := by
      rw [eq_bot_iff, commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h a b
    rw [hM.1] at hbot
    exact top_ne_bot hbot
  have hcenter : Subgroup.center ↥G₀ = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥G₀) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center ↥G₀ := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  have hchevG₀ : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 ↥G₀ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
      (isChevTwo_of_largeEvenMarking_of_center_eq_bot hM hcenter)
  let ψ : ↥A →* MulAut ↥G₀ :=
    (Subgroup.normalizerMonoidHom (H := G₀)).comp (Subgroup.inclusion hAN)
  let E : Subgroup (MulAut ↥G₀) := ψ.range
  have hψ : ∀ (a : ↥A) (g : ↥G₀), ((ψ a) g : X) = (a : X) * (g : X) * (a : X)⁻¹ :=
    fun a g => Subgroup.normalizerMonoidHom_apply_apply_coe G₀ (Subgroup.inclusion hAN a) g
  have hEel : IsElemAbelian p E :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isElemAbelian_range p ψ
      (fun a b => hA.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hA.2 a.1 a.2))
  refine ⟨hnc, hchevG₀, E, hEel, ?_⟩
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨?_, h.2⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro a ha
    have hfix : (ψ ⟨a, ha⟩) h = h :=
      (CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix.1 hh) _
        (MonoidHom.mem_range.2 ⟨⟨a, ha⟩, rfl⟩)
    have h1 : (a : X) * (h : X) * (a : X)⁻¹ = (h : X) := by
      simpa [hψ] using congrArg (Subtype.val) hfix
    calc (a : X) * (h : X) = ((a : X) * (h : X) * (a : X)⁻¹) * (a : X) := by group
      _ = (h : X) * (a : X) := by rw [h1]
  · rintro ⟨hgC, hgG⟩
    refine ⟨⟨g, hgG⟩, ?_, rfl⟩
    refine (CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix).2 ?_
    rintro e he
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 he
    apply Subtype.ext
    rw [hψ]
    have hcomm : (a : X) * g = g * (a : X) := Subgroup.mem_centralizer_iff.1 hgC a a.2
    rw [hcomm]
    group

theorem ggStructSOnePerf_holds : GGStructSOnePerf := by
  intro X _ _ p G₀ A hp hp2 hG₀ hA hAN hM P hPY hPperf
  obtain ⟨hnc, hchevG₀, E, hEel, hYeq⟩ := s1Setup hp hp2 hG₀ hA hAN hM
  haveI := hG₀
  have hPG0 : P ≤ G₀ := hPY.trans inf_le_right
  have hP₀perf : ⁅P.subgroupOf G₀, P.subgroupOf G₀⁆ = P.subgroupOf G₀ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPG0, hPperf]
  have hP₀le : P.subgroupOf G₀ ≤ CFSG.LocalAnalysis.GLTheoremA.I142.centFix E := by
    intro x hx
    have hxY : (x : X) ∈ Subgroup.centralizer (A : Set X) ⊓ G₀ := hPY (Subgroup.mem_subgroupOf.1 hx)
    rw [← hYeq] at hxY
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxY
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  have hLie : P.subgroupOf G₀ ≤ CFSG.Open.GLALayer
      (CFSG.LocalAnalysis.GLTheoremA.I142.centFix E) :=
    (CFSG.LocalAnalysis.GLTheoremA.I142.lieSemisimpleCentE_of_residuals
        CFSG.LocalAnalysis.GLTheoremA.I142.residualCyc_holds
        CFSG.LocalAnalysis.GLTheoremA.I142M.residualNonCyc_holds)
      ↥G₀ hG₀ hnc hchevG₀ p hp hp2 E hEel (P.subgroupOf G₀) hP₀le hP₀perf
  rw [CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer, ← hYeq]
  calc P = (P.subgroupOf G₀).map G₀.subtype := (Subgroup.map_subgroupOf_eq_of_le hPG0).symm
    _ ≤ (CFSG.Open.GLALayer (CFSG.LocalAnalysis.GLTheoremA.I142.centFix E)).map G₀.subtype :=
        Subgroup.map_mono hLie
    _ ≤ CFSG.Open.GLALayer ((CFSG.LocalAnalysis.GLTheoremA.I142.centFix E).map G₀.subtype) :=
        CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_map_le G₀.subtype
          (fun g hg => by
            have hg1 : g = 1 := G₀.subtype_injective (by simpa using hg)
            rw [hg1]
            exact Subgroup.one_mem _) _

theorem ggStructSOneComp_holds : GGStructSOneComp := by
  intro X _ _ p G₀ A hp hp2 hG₀ hA hAN hM C hC
  obtain ⟨hnc, hchevG₀, E, hEel, hYeq⟩ := s1Setup hp hp2 hG₀ hA hAN hM
  haveI := hG₀
  have hCG0 : C ≤ G₀ := hC.1.trans inf_le_right
  have hcompC₀ : CFSG.Open.IsComponentOf (C.subgroupOf G₀)
      (CFSG.LocalAnalysis.GLTheoremA.I142.centFix E) := by
    have h2 : CFSG.Assembly.IsComponentOf ((C.subgroupOf G₀).map G₀.subtype)
        ((CFSG.LocalAnalysis.GLTheoremA.I142.centFix E).map G₀.subtype) := by
      rwa [Subgroup.map_subgroupOf_eq_of_le hCG0, hYeq]
    exact CFSG.Assembly.isComponentOf_iff_open.1
      ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := G₀.subtype)
        G₀.subtype_injective).1 h2)
  have hchevC₀ : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (↥(C.subgroupOf G₀) ⧸ Subgroup.center ↥(C.subgroupOf G₀)) :=
    CFSG.LocalAnalysis.GLTheoremA.I142T.compTypesElem_holds ↥G₀ hG₀ hnc hchevG₀ p hp hp2 E hEel
      (C.subgroupOf G₀) hcompC₀
  have hchevC : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (↥C ⧸ Subgroup.center ↥C) := by
    have e : ↥C ⧸ Subgroup.center ↥C ≃*
        ↥(C.subgroupOf G₀) ⧸ Subgroup.center ↥(C.subgroupOf G₀) :=
      (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.subgroupOfEquivOfLe hCG0)).symm
    rcases hchevC₀ with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
    · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
    · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩
  exact CFSG.StandardType.ChevTwo.ys08_holds_legacy ↥C hC.2.2 hchevC

end CFSG.StandardType
