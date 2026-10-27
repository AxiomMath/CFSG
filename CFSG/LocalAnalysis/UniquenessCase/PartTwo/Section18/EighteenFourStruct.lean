module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ACandidateA5
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vg
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PM
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127MAbs
public import CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndQuot
public import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GroupTheory.CoprimeActionSupport
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure A5Data18 (D : Data G) (V₀ V L : Subgroup G) : Prop where
  hyp : Hyp18 D V₀ V 5 L
  alt : IsAlt (Bar2 L) 5
  eM : S17.eM D.M = 3
  shape : S17.IsA5A5Cyclic5
    ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)))
  hinf : Hinf (oTwoEOf D.M) ≤ Opp 5 D.M

theorem A5Data18.of_hyp18 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1768 : S17.R17_68At D V₀ V) (hA5 : IsAlt (Bar2 L) 5) :
    p = 5 ∧ A5Data18 D V₀ V L := by
  obtain ⟨hp, heM, hshape, hinf⟩ := h1768 p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX hA5
  exact ⟨hp, { hyp := hp ▸ h, alt := hA5, eM := heM, shape := hshape, hinf := hinf }⟩


private theorem components_of_Q {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L) :
    ∃ F₁ F₂ : Subgroup (CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (Bar2 D.M))),
      CFSG.Open.IsComponentOf F₁ ⊤ ∧ CFSG.Open.IsComponentOf F₂ ⊤ ∧
      Nonempty (↥F₁ ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (↥F₂ ≃* alternatingGroup (Fin 5)) ∧ F₁ ≠ F₂ ∧
      (∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a) ∧
      (∀ P : Subgroup (CFSG.RankThree.PartOne.pElementSubgroup 5
          (⊤ : Subgroup (Bar2 D.M))), CFSG.Open.IsComponentOf P ⊤ → P = F₁ ∨ P = F₂) := by
  classical
  let Q := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  obtain ⟨z, hz, ⟨e⟩⟩ := c.shape
  let A5 := alternatingGroup (Fin 5)
  let Z := Multiplicative (ZMod (5 ^ z))
  let π₁ : A5 × (A5 × Z) →* A5 := MonoidHom.fst A5 (A5 × Z)
  let π₂ : A5 × (A5 × Z) →* A5 :=
    (MonoidHom.fst A5 Z).comp (MonoidHom.snd A5 (A5 × Z))
  let πZ : A5 × (A5 × Z) →* Z :=
    (MonoidHom.snd A5 Z).comp (MonoidHom.snd A5 (A5 × Z))
  let F₁bar : Subgroup (A5 × (A5 × Z)) := π₂.ker ⊓ πZ.ker
  let F₂bar : Subgroup (A5 × (A5 × Z)) := π₁.ker ⊓ πZ.ker
  let F₁ : Subgroup Q := F₁bar.comap e.toMonoidHom
  let F₂ : Subgroup Q := F₂bar.comap e.toMonoidHom
  have hF₁map : F₁.map e.toMonoidHom = F₁bar :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective F₁bar
  have hF₂map : F₂.map e.toMonoidHom = F₂bar :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective F₂bar
  have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by norm_num)
  have eF₁ : ↥F₁bar ≃* A5 := by
    let f : ↥F₁bar →* A5 := π₁.comp F₁bar.subtype
    have hf_inj : Function.Injective f := by
      intro x y hxy
      obtain ⟨⟨x1, x2, xz⟩, hx⟩ := x
      obtain ⟨⟨y1, y2, yz⟩, hy⟩ := y
      simp only [F₁bar, Subgroup.mem_inf, MonoidHom.mem_ker, π₂, πZ,
        MonoidHom.comp_apply] at hx hy
      obtain ⟨hx2, hxz⟩ := hx
      obtain ⟨hy2, hyz⟩ := hy
      have h1 : x1 = y1 := hxy
      apply Subtype.ext
      exact Prod.ext h1 (Prod.ext (hx2.trans hy2.symm) (hxz.trans hyz.symm))
    have hf_surj : Function.Surjective f := by
      intro a
      exact ⟨⟨(a, 1, 1), by simp [F₁bar, π₂, πZ]⟩, rfl⟩
    exact MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have eF₂ : ↥F₂bar ≃* A5 := by
    let f : ↥F₂bar →* A5 := π₂.comp F₂bar.subtype
    have hf_inj : Function.Injective f := by
      intro x y hxy
      obtain ⟨⟨x1, x2, xz⟩, hx⟩ := x
      obtain ⟨⟨y1, y2, yz⟩, hy⟩ := y
      simp only [F₂bar, Subgroup.mem_inf, MonoidHom.mem_ker, π₁, πZ,
        MonoidHom.comp_apply] at hx hy
      obtain ⟨hx1, hxz⟩ := hx
      obtain ⟨hy1, hyz⟩ := hy
      have h2 : x2 = y2 := hxy
      apply Subtype.ext
      exact Prod.ext (hx1.trans hy1.symm) (Prod.ext h2 (hxz.trans hyz.symm))
    have hf_surj : Function.Surjective f := by
      intro a
      exact ⟨⟨(1, a, 1), by simp [F₂bar, π₁, πZ]⟩, rfl⟩
    exact MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hF₁q : CFSG.Open.IsQuasisimple ↥F₁ := by
    have eF : ↥F₁ ≃* ↥F₁bar :=
      (Subgroup.equivMapOfInjective F₁ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hF₁map)
    exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt
      (by norm_num) (eF.trans eF₁)
  have hF₂q : CFSG.Open.IsQuasisimple ↥F₂ := by
    have eF : ↥F₂ ≃* ↥F₂bar :=
      (Subgroup.equivMapOfInjective F₂ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hF₂map)
    exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt
      (by norm_num) (eF.trans eF₂)
  have hne : F₁ ≠ F₂ := by
    intro hEq
    have hbar : F₁bar = F₂bar := by rw [← hF₁map, ← hF₂map, hEq]
    obtain ⟨x, hx⟩ := exists_ne (1 : A5)
    have hmem : (x, 1, 1) ∈ F₁bar := by simp [F₁bar, π₂, πZ]
    rw [hbar] at hmem
    simp [F₂bar, π₁, πZ] at hmem
    exact hx hmem
  have hcomm : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := by
    intro a ha b hb
    apply e.injective
    have ha' : e a ∈ F₁bar := by rw [← hF₁map]; exact Subgroup.mem_map_of_mem _ ha
    have hb' : e b ∈ F₂bar := by rw [← hF₂map]; exact Subgroup.mem_map_of_mem _ hb
    have ha2 : (e a).2.1 = 1 := by
      have h := ha'
      simp only [F₁bar, Subgroup.mem_inf, MonoidHom.mem_ker, π₂, πZ,
        MonoidHom.comp_apply] at h
      exact h.1
    have haz : (e a).2.2 = 1 := by
      have h := ha'
      simp only [F₁bar, Subgroup.mem_inf, MonoidHom.mem_ker, π₂, πZ,
        MonoidHom.comp_apply] at h
      exact h.2
    have hb1 : (e b).1 = 1 := by
      have h := hb'
      simp only [F₂bar, Subgroup.mem_inf, MonoidHom.mem_ker, π₁, πZ,
        MonoidHom.comp_apply] at h
      exact h.1
    have hbz : (e b).2.2 = 1 := by
      have h := hb'
      simp only [F₂bar, Subgroup.mem_inf, MonoidHom.mem_ker, π₁, πZ,
        MonoidHom.comp_apply] at h
      exact h.2
    ext <;> simp [ha2, haz, hb1, hbz]
  have hsolvZ : Group.IsSolvable ((A5 × (A5 × Z)) ⧸ πZ.ker) := by
    have hRange : Group.IsSolvable ↥πZ.range :=
      Group.isSolvable_of_comm fun x y => Subtype.ext (mul_comm (x : Z) (y : Z))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange πZ).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange πZ).injective
  have hcomp : ∀ P : Subgroup Q, CFSG.Open.IsComponentOf P ⊤ → P = F₁ ∨ P = F₂ := by
    intro P hP
    let C : Subgroup (A5 × (A5 × Z)) := P.map e.toMonoidHom
    have hCcomp : CFSG.Open.IsComponentOf C ⊤ :=
      (CFSG.isComponent_iff_open C).mp
        (CFSG.LocalCores.isComponent_map_mulEquiv e
          ((CFSG.isComponent_iff_open P).mpr hP))
    have hCperf : ⁅C, C⁆ = C := by
      have hPperf : ⁅P, P⁆ = P :=
        CFSG.QuasithinUnique.L246C127.MAbs.comm_eq_self hP.2.2
      calc ⁅C, C⁆ = (⁅P, P⁆).map e.toMonoidHom := by
              rw [Subgroup.map_commutator]
        _ = C := by rw [hPperf]
    have hCker : C ≤ πZ.ker :=
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_le_perfectResidual C hCperf).trans
        (TwoModuloExtension.perfectResidual_le_of_isSolvable_quotient
          hsolvZ)
    have hCsub : CFSG.Open.IsSubnormal C πZ.ker := by
      have h := hCcomp.2.1.inf_of_le (le_top : πZ.ker ≤ ⊤)
      rwa [inf_eq_left.2 hCker] at h
    have hC'comp : CFSG.Open.IsComponentOf (C.subgroupOf πZ.ker) ⊤ :=
      ⟨le_top, (CFSG.Open.IsSubnormal.top_iff (L := C.subgroupOf πZ.ker)).2 hCsub.subgroupOf,
        CFSG.Open.IsQuasisimple.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hCker) hCcomp.2.2⟩
    have hF₁le : F₁bar ≤ πZ.ker := inf_le_right
    have hF₂le : F₂bar ≤ πZ.ker := inf_le_right
    have hF₁barq : CFSG.Open.IsQuasisimple ↥F₁bar :=
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt
        (by norm_num) eF₁
    have hF₂barq : CFSG.Open.IsQuasisimple ↥F₂bar :=
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt
        (by norm_num) eF₂
    have hF₁'q : CFSG.Open.IsQuasisimple ↥(F₁bar.subgroupOf πZ.ker) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hF₁le) hF₁barq
    have hF₂'q : CFSG.Open.IsQuasisimple ↥(F₂bar.subgroupOf πZ.ker) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hF₂le) hF₂barq
    have hF₁'simp : IsSimpleGroup ↥(F₁bar.subgroupOf πZ.ker) := by
      have e' : ↥(F₁bar.subgroupOf πZ.ker) ≃* A5 :=
        (Subgroup.subgroupOfEquivOfLe hF₁le).trans eF₁
      exact MulEquiv.isSimpleGroup e'
    have hF₂'simp : IsSimpleGroup ↥(F₂bar.subgroupOf πZ.ker) := by
      have e' : ↥(F₂bar.subgroupOf πZ.ker) ≃* A5 :=
        (Subgroup.subgroupOfEquivOfLe hF₂le).trans eF₂
      exact MulEquiv.isSimpleGroup e'
    have hgen : sSup {F₁bar.subgroupOf πZ.ker, F₂bar.subgroupOf πZ.ker} = ⊤ := by
      rw [sSup_pair]
      have hsup : F₁bar ⊔ F₂bar = πZ.ker := by
        apply le_antisymm
        · exact sup_le hF₁le hF₂le
        · intro x hx
          obtain ⟨a, b, hz⟩ := x
          simp only [πZ, MonoidHom.comp_apply,
            MonoidHom.mem_ker] at hx
          subst hx
          have h1 : (a, 1, 1) ∈ F₁bar := by simp [F₁bar, π₂, πZ]
          have h2 : (1, b, 1) ∈ F₂bar := by simp [F₂bar, π₁, πZ]
          have hmem : (a, 1, 1) * (1, b, 1) ∈ F₁bar ⊔ F₂bar :=
            Subgroup.mul_mem_sup h1 h2
          simpa using hmem
      rw [← Subgroup.subgroupOf_sup hF₁le hF₂le, hsup, Subgroup.subgroupOf_self]
    obtain ⟨N, hN, hCN⟩ :=
      CFSG.LocalAnalysis.RankThreeUC.S15.normal_big_of_not_L3_aux_gen hC'comp
        {F₁bar.subgroupOf πZ.ker, F₂bar.subgroupOf πZ.ker}
        (by
          intro N hN
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
          rcases hN with rfl | rfl
          · exact Subgroup.normal_subgroupOf
          · exact Subgroup.normal_subgroupOf)
        hgen
    have hNcases : N = F₁bar.subgroupOf πZ.ker ∨ N = F₂bar.subgroupOf πZ.ker := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hN
    have hCeq : C.subgroupOf πZ.ker = F₁bar.subgroupOf πZ.ker ∨
        C.subgroupOf πZ.ker = F₂bar.subgroupOf πZ.ker := by
      rcases hNcases with rfl | rfl
      · left
        exact CFSG.LocalAnalysis.RankThreeUC.S15.normal_big_of_not_L3_aux_eq
          hC'comp hCN hF₁'simp
      · right
        exact CFSG.LocalAnalysis.RankThreeUC.S15.normal_big_of_not_L3_aux_eq
          hC'comp hCN hF₂'simp
    have hCbar : C = F₁bar ∨ C = F₂bar := by
      rcases hCeq with h | h
      · left
        have := congrArg (Subgroup.map (πZ.ker).subtype) h
        rwa [Subgroup.map_subgroupOf_eq_of_le hCker,
          Subgroup.map_subgroupOf_eq_of_le hF₁le] at this
      · right
        have := congrArg (Subgroup.map (πZ.ker).subtype) h
        rwa [Subgroup.map_subgroupOf_eq_of_le hCker,
          Subgroup.map_subgroupOf_eq_of_le hF₂le] at this
    rcases hCbar with h | h
    · left
      have h1 : P.map e.toMonoidHom = F₁.map e.toMonoidHom := by
        rw [hF₁map]; exact h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1
    · right
      have h2 : P.map e.toMonoidHom = F₂.map e.toMonoidHom := by
        rw [hF₂map]; exact h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h2
  have hF₁bar_norm : F₁bar.Normal := by
    show (π₂.ker ⊓ πZ.ker).Normal
    exact Subgroup.normal_inf_normal _ _
  have hF₂bar_norm : F₂bar.Normal := by
    show (π₁.ker ⊓ πZ.ker).Normal
    exact Subgroup.normal_inf_normal _ _
  have hF₁norm : F₁.Normal := hF₁bar_norm.comap e.toMonoidHom
  have hF₂norm : F₂.Normal := hF₂bar_norm.comap e.toMonoidHom
  have hF₁comp : CFSG.Open.IsComponentOf F₁ ⊤ :=
    ⟨le_top, (CFSG.Open.IsSubnormal.top_iff).2 hF₁norm.isSubnormal, hF₁q⟩
  have hF₂comp : CFSG.Open.IsComponentOf F₂ ⊤ :=
    ⟨le_top, (CFSG.Open.IsSubnormal.top_iff).2 hF₂norm.isSubnormal, hF₂q⟩
  have hF₁iso : Nonempty (↥F₁ ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.equivMapOfInjective F₁ e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hF₁map).trans eF₁)⟩
  have hF₂iso : Nonempty (↥F₂ ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.equivMapOfInjective F₂ e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hF₂map).trans eF₂)⟩
  exact ⟨F₁, F₂, hF₁comp, hF₂comp, hF₁iso, hF₂iso, hne, hcomm, hcomp⟩


private theorem layer_le_Q {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L) :
    CFSG.layer (Bar2 D.M) ≤ CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (Bar2 D.M)) := by
  classical
  let Q := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  have hcomp_le : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → C ≤ Q := by
    intro C hC
    obtain ⟨J, hJ, hJC⟩ := s13_exists_calC_of_component D.M hC
    have hJM : J ≤ D.M := s13_le_of_mem_calC hJ
    have hJperf : ⁅J, J⁆ = J := hJ.2.1
    have hJleO : J ≤ oTwoEOf D.M := by
      intro x hx
      have hxM : x ∈ D.M := hJM hx
      have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ ∈ C := by
        rw [← hJC]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_map.2
        ⟨⟨x, hxM⟩, Subgroup.mem_comap.2 (CFSG.LocalCores.component_le_layer hC hxbar), rfl⟩
    have hJleH : J ≤ Hinf (oTwoEOf D.M) := uc22p21c_le_Hinf hJleO hJperf
    have hJleOpp : J ≤ Opp 5 D.M := hJleH.trans c.hinf
    calc C = barImage D.M J := hJC.symm
      _ ≤ barImage D.M (Opp 5 D.M) := Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hJleOpp)
      _ = Q := by
          rw [s13_barImage_opp Nat.prime_five (le_refl D.M), s13_barImage_self]
  rw [CFSG.layer.eq_sSup]
  exact sSup_le fun C hC => hcomp_le C hC


private theorem component_Q {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L) {C : Subgroup (Bar2 D.M)}
    (hC : CFSG.IsComponent C)
    (hCQ : C ≤ CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (Bar2 D.M))) :
    CFSG.Open.IsComponentOf (C.subgroupOf (CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (Bar2 D.M)))) ⊤ := by
  have hcomp := CFSG.LocalCores.component_overgroup hC hCQ
  refine ⟨le_top, (CFSG.Open.IsSubnormal.top_iff).2 hcomp.2, ?_⟩
  exact (CFSG.CGT.PushingUpLit.CGT6.EndQuot.isQuasisimple_iff_open _).1 hcomp.1


private theorem isComponent_map_Q {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L)
    {F : Subgroup (CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (Bar2 D.M)))}
    (hF : CFSG.Open.IsComponentOf F ⊤) :
    CFSG.IsComponent (F.map (CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (Bar2 D.M))).subtype) := by
  let Q := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  have hQnorm : Q.Normal := uc22p22r_pElementSubgroup_normal
  have hsub : CFSG.Open.IsSubnormal (F.map Q.subtype) ⊤ := by
    have h1 : CFSG.Open.IsSubnormal (F.map Q.subtype) ((⊤ : Subgroup Q).map Q.subtype) :=
      CFSG.Open.IsSubnormal.map (G := Q) Q.subtype hF.2.1
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1.trans ((CFSG.Open.IsSubnormal.top_iff).2 hQnorm.isSubnormal)
  have hq : CFSG.Open.IsQuasisimple ↥(F.map Q.subtype) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective F Q.subtype Q.subtype_injective).symm hF.2.2
  exact ⟨(CFSG.CGT.PushingUpLit.CGT6.EndQuot.isQuasisimple_iff_open _).2 hq,
    (CFSG.Open.IsSubnormal.top_iff).1 hsub⟩


theorem A5Data18.exists_second_component {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L) :
    ∃ K ∈ calC D.M, K ≠ L ∧ UC22.IsAlt (Bar2 K) 5 := by
  classical
  let Q := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  obtain ⟨F₁, F₂, hF₁comp, hF₂comp, hF₁iso, hF₂iso, hne, hcomm, hcomp⟩ :=
    components_of_Q c
  have hLcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent c.hyp.hL.1
  have hLle : barImage D.M L ≤ Q :=
    (CFSG.LocalCores.component_le_layer hLcomp).trans (layer_le_Q c)
  let LQ : Subgroup Q := (barImage D.M L).subgroupOf Q
  have hLQcomp : CFSG.Open.IsComponentOf LQ ⊤ := component_Q c hLcomp hLle
  have hLQ : LQ = F₁ ∨ LQ = F₂ := hcomp LQ hLQcomp
  let KQ : Subgroup Q := if LQ = F₁ then F₂ else F₁
  have hKQcomp : CFSG.Open.IsComponentOf KQ ⊤ := by
    by_cases h : LQ = F₁
    · change CFSG.Open.IsComponentOf (if LQ = F₁ then F₂ else F₁) ⊤
      rw [if_pos h]; exact hF₂comp
    · change CFSG.Open.IsComponentOf (if LQ = F₁ then F₂ else F₁) ⊤
      rw [if_neg h]; exact hF₁comp
  have hKQne : KQ ≠ LQ := by
    by_cases h : LQ = F₁
    · change (if LQ = F₁ then F₂ else F₁) ≠ LQ
      rw [if_pos h]
      exact fun hEq => hne (hEq.trans h).symm
    · change (if LQ = F₁ then F₂ else F₁) ≠ LQ
      rw [if_neg h]
      exact fun hEq => h hEq.symm
  have hKQiso : Nonempty (↥KQ ≃* alternatingGroup (Fin 5)) := by
    by_cases h : LQ = F₁
    · change Nonempty (↥(if LQ = F₁ then F₂ else F₁) ≃* alternatingGroup (Fin 5))
      rw [if_pos h]; exact hF₂iso
    · change Nonempty (↥(if LQ = F₁ then F₂ else F₁) ≃* alternatingGroup (Fin 5))
      rw [if_neg h]; exact hF₁iso
  have hKcomp : CFSG.IsComponent (KQ.map Q.subtype) := isComponent_map_Q c hKQcomp
  obtain ⟨K, hK, hKbar⟩ := s13_exists_calC_of_component D.M hKcomp
  have hKne : K ≠ L := by
    intro hEq
    have hbar : barImage D.M K = barImage D.M L := by rw [hEq]
    have h1 : KQ.map Q.subtype = LQ.map Q.subtype := by
      rw [← hKbar, hbar]
      exact (Subgroup.map_subgroupOf_eq_of_le hLle).symm
    have h2 : KQ = LQ :=
      Subgroup.map_injective (f := Q.subtype) Q.subtype_injective h1
    exact hKQne h2
  have hAlt : UC22.IsAlt (Bar2 K) 5 := by
    obtain ⟨eBar⟩ := s13_bar_equiv hK
    obtain ⟨eKQ⟩ := hKQiso
    have eMap : ↥(KQ.map Q.subtype) ≃* ↥KQ :=
      (Subgroup.equivMapOfInjective KQ Q.subtype Q.subtype_injective).symm
    exact ⟨eBar.trans ((MulEquiv.subgroupCongr hKbar).trans (eMap.trans eKQ))⟩
  exact ⟨K, hK, hKne, hAlt⟩


theorem A5Data18.calC_eq {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hK : K ∈ calC D.M) (hKne : K ≠ L) :
    ∀ J ∈ calC D.M, J = L ∨ J = K := by
  classical
  let Q := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  obtain ⟨F₁, F₂, -, -, -, -, hne, -, hcomp⟩ := components_of_Q c
  have hle : ∀ A ∈ calC D.M, barImage D.M A ≤ Q := by
    intro A hA
    exact (CFSG.LocalCores.component_le_layer (s13_barImage_isComponent hA)).trans
      (layer_le_Q c)
  let LQ : Subgroup Q := (barImage D.M L).subgroupOf Q
  let KQ : Subgroup Q := (barImage D.M K).subgroupOf Q
  have hLQcomp : CFSG.Open.IsComponentOf LQ ⊤ :=
    component_Q c (s13_barImage_isComponent c.hyp.hL.1) (hle L c.hyp.hL.1)
  have hKQcomp : CFSG.Open.IsComponentOf KQ ⊤ :=
    component_Q c (s13_barImage_isComponent hK) (hle K hK)
  have hLQ : LQ = F₁ ∨ LQ = F₂ := hcomp LQ hLQcomp
  have hKQ : KQ = F₁ ∨ KQ = F₂ := hcomp KQ hKQcomp
  have hKQne : KQ ≠ LQ := by
    intro hEq
    have h1 : barImage D.M K = barImage D.M L := by
      have h2 := congrArg (Subgroup.map Q.subtype) hEq
      rwa [Subgroup.map_subgroupOf_eq_of_le (hle K hK),
        Subgroup.map_subgroupOf_eq_of_le (hle L c.hyp.hL.1)] at h2
    exact hKne (uc22p22u_calC_ext hK c.hyp.hL.1 h1)
  intro J hJ
  let JQ : Subgroup Q := (barImage D.M J).subgroupOf Q
  have hJQcomp : CFSG.Open.IsComponentOf JQ ⊤ :=
    component_Q c (s13_barImage_isComponent hJ) (hle J hJ)
  have hJQ : JQ = F₁ ∨ JQ = F₂ := hcomp JQ hJQcomp
  have hJK : JQ = LQ ∨ JQ = KQ := by
    by_cases hJL : JQ = LQ
    · exact Or.inl hJL
    · right
      rcases hJQ with hJ1 | hJ2
      · rcases hLQ with hL1 | hL2
        · exact absurd (hJ1.trans hL1.symm) hJL
        · rcases hKQ with hK1 | hK2
          · exact hJ1.trans hK1.symm
          · exact absurd (hK2.trans hL2.symm) hKQne
      · rcases hLQ with hL1 | hL2
        · rcases hKQ with hK1 | hK2
          · exact absurd (hK1.trans hL1.symm) hKQne
          · exact hJ2.trans hK2.symm
        · exact absurd (hJ2.trans hL2.symm) hJL
  rcases hJK with hJL | hJK
  · left
    apply uc22p22u_calC_ext hJ c.hyp.hL.1
    have h2 := congrArg (Subgroup.map Q.subtype) hJL
    rwa [Subgroup.map_subgroupOf_eq_of_le (hle J hJ),
      Subgroup.map_subgroupOf_eq_of_le (hle L c.hyp.hL.1)] at h2
  · right
    apply uc22p22u_calC_ext hJ hK
    have h2 := congrArg (Subgroup.map Q.subtype) hJK
    rwa [Subgroup.map_subgroupOf_eq_of_le (hle J hJ),
      Subgroup.map_subgroupOf_eq_of_le (hle K hK)] at h2


theorem A5Data18.commutator_le {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hK : K ∈ calC D.M) (hKne : K ≠ L) :
    ⁅L, K⁆ ≤ pCoreOf 2 D.M := by
  have hLsub : CFSG.Open.IsSubnormal L D.M := c.hyp.hL.1.1
  have hKsub : CFSG.Open.IsSubnormal K D.M := hK.1
  have hLp : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
    CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hLsub
  have hKp : pCoreOf 2 K ≤ pCoreOf 2 D.M :=
    CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hKsub
  exact (calC_commutator_le_of_ne c.hyp.hL.1 hK hKne.symm).trans (inf_le_left.trans hLp)


private theorem uc22ConjClosure_le_of_forall {M L X : Subgroup G}
    (h : ∀ g ∈ M, conjSubgroup L g ≤ X) : UC22.conjClosure M L ≤ X := by
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨g, hg, rfl⟩ := hJ
  simpa only [conjSubgroup, inv_inv] using h g⁻¹ (M.inv_mem hg)

private theorem le_uc22ConjClosure_of_mem {M L : Subgroup G} {g : G} (hg : g ∈ M) :
    conjSubgroup L g ≤ UC22.conjClosure M L :=
  le_iSup₂ (f := fun J (_ : J ∈ UC22.conjSetOf M L) => J) (conjSubgroup L g)
    ⟨g⁻¹, M.inv_mem hg, rfl⟩

theorem A5Data18.dichotomy {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hcal : ∀ J ∈ calC D.M, J = L ∨ J = K) :
    (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
      (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧
        (K.subgroupOf D.M).Normal) := by
  classical
  have hconj_mem : ∀ g ∈ D.M, conjSubgroup L g ∈ calC D.M := by
    intro g hg
    have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (Subgroup.le_normalizer)
      c.hyp.hL.1 hg
    rwa [show uniqueFourConj g L = conjSubgroup L g from rfl] at h
  by_cases hex : ∃ g ∈ D.M, conjSubgroup L g = K
  · left
    obtain ⟨g, hg, hgK⟩ := hex
    have hle : UC22.conjClosure D.M L ≤ L ⊔ K := by
      refine uc22ConjClosure_le_of_forall fun x hx => ?_
      rcases hcal (conjSubgroup L x) (hconj_mem x hx) with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    have hge : L ⊔ K ≤ UC22.conjClosure D.M L := by
      refine sup_le (TwelveTwentyThree.le_conjClosure D.M L) ?_
      rw [← hgK]
      exact le_uc22ConjClosure_of_mem hg
    exact ⟨le_antisymm hle hge, ⟨g, hg, hgK.symm⟩⟩
  · right
    push Not at hex
    have hclosure : UC22.conjClosure D.M L = L := by
      apply le_antisymm
      · refine uc22ConjClosure_le_of_forall fun x hx => ?_
        rcases hcal (conjSubgroup L x) (hconj_mem x hx) with h | h
        · exact le_of_eq h
        · exact absurd h (hex x hx)
      · exact TwelveTwentyThree.le_conjClosure D.M L
    have hLnorm : (L.subgroupOf D.M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s13_le_of_mem_calC c.hyp.hL.1)]
      intro g hg
      have hconj := hcal (conjSubgroup L g⁻¹) (hconj_mem g⁻¹ (D.M.inv_mem hg))
      have hL : conjSubgroup L g⁻¹ = L := by
        rcases hconj with h | h
        · exact h
        · exact absurd h (hex g⁻¹ (D.M.inv_mem hg))
      have h : g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        (Quasithin.conjSubgroup_eq_iff_mem_normalizer).1 hL
      simpa using Subgroup.inv_mem (Subgroup.normalizer (L : Set G)) h
    have hKnorm : (K.subgroupOf D.M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s13_le_of_mem_calC hK)]
      intro g hg
      have hKconj : conjSubgroup K g ∈ calC D.M := by
        have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (Subgroup.le_normalizer) hK hg
        rwa [show uniqueFourConj g K = conjSubgroup K g from rfl] at h
      rcases hcal (conjSubgroup K g) hKconj with h | h
      · exfalso
        have h1 : K = conjSubgroup L g⁻¹ := by
          have h2 := congrArg (fun A => conjSubgroup A g⁻¹) h
          rwa [Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
            Quasithin.conjSubgroup_one] at h2
        exact (hex g⁻¹ (D.M.inv_mem hg)) h1.symm
      · exact (Quasithin.conjSubgroup_eq_iff_mem_normalizer).1 h
    exact ⟨hclosure, hLnorm, hKnorm⟩

private theorem uc22ConjClosure_conjSubgroup {M L : Subgroup G} {x : G} (hx : x ∈ M) :
    UC22.conjClosure M (conjSubgroup L x) = UC22.conjClosure M L := by
  have hset : UC22.conjSetOf M (conjSubgroup L x) = UC22.conjSetOf M L := by
    ext K
    constructor
    · rintro ⟨g, hg, hgK⟩
      refine ⟨g * x⁻¹, M.mul_mem hg (M.inv_mem hx), ?_⟩
      rw [hgK]
      simp only [conjSubgroup, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply]
    · rintro ⟨h, hh, hhK⟩
      refine ⟨h * x, M.mul_mem hh hx, ?_⟩
      rw [hhK]
      simp only [conjSubgroup, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply]
      group
  unfold UC22.conjClosure
  rw [hset]

theorem A5Data18.conjClosure_K_mem_calL0Star {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hK : K ∈ calC D.M) (hK5 : K ∈ S17.calLp D 5)
    (hAltK : UC22.IsAlt (Bar2 K) 5)
    (hdich : (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
      (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal)) :
    UC22.conjClosure D.M K ∈ S17.calL0Star D 5 := by
  rcases hdich with ⟨hclosureL, x, hx, hKconj⟩ | ⟨hclosureL, hLnorm, hKnorm⟩
  · rw [hKconj, uc22ConjClosure_conjSubgroup hx]
    exact c.hyp.hX
  · have hKcl : UC22.conjClosure D.M K = K := by
      apply le_antisymm
      · refine uc22ConjClosure_le_of_forall fun g hg => ?_
        have h : conjSubgroup K g = K := by
          rw [Quasithin.conjSubgroup_eq_iff_mem_normalizer]
          exact (Subgroup.normal_subgroupOf_iff_le_normalizer (s13_le_of_mem_calC hK)).1 hKnorm hg
        exact le_of_eq h
      · exact TwelveTwentyThree.le_conjClosure D.M K
    rw [hKcl]
    have hL0 : L ∈ S17.calL0Star D 5 := by
      rw [← hclosureL]
      exact c.hyp.hX
    have hL5star : L ∈ S17.calLpStar D 5 := ⟨L, c.hyp.hL, hclosureL.symm⟩
    have hL5 : L ∈ S17.calL5Star D 5 := ⟨hL5star, c.alt⟩
    have hj : S17.jM D 5 = 5 :=
      S17.jM_eq_five_of_mem_calL5Star c.hyp.hL hL0 hL5
    have hK5star : K ∈ S17.calL5Star D 5 :=
      ⟨⟨K, hK5, hKcl.symm⟩, hAltK⟩
    have h0 : S17.calL0Star D 5 = S17.calL5Star D 5 := by
      simp [S17.calL0Star, S17.calLjStar, hj]
    rwa [h0]


private theorem three_not_mem_sig_aux
    {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hK : K ∈ calC D.M) (hK5 : K ∈ S17.calLp D 5)
    (hAltK : UC22.IsAlt (Bar2 K) 5)
    (hcal : ∀ J ∈ calC D.M, J = L ∨ J = K)
    (h1768 : S17.R17_68At D V₀ V) : 3 ∉ D.sig := by
  intro h3sig
  have h3L : 3 ∈ piSet L :=
    ⟨Nat.prime_three,
      S17.three_dvd_card_of_bar_isL2Even
        (S17.isL2_PSL2_two_of_isAlt_five c.alt)⟩
  have h3K : 3 ∈ piSet K :=
    ⟨Nat.prime_three,
      S17.three_dvd_card_of_bar_isL2Even
        (S17.isL2_PSL2_two_of_isAlt_five hAltK)⟩
  have hLp : S17.calLp D 3 = S17.calLp D 5 := by
    ext J
    simp only [S17.mem_calLp]
    constructor
    · rintro ⟨hJ, -⟩
      rcases hcal J hJ with rfl | rfl
      · exact ⟨c.hyp.hL.1, c.hyp.hL.2⟩
      · exact ⟨hK5.1, hK5.2⟩
    · rintro ⟨hJ, -⟩
      rcases hcal J hJ with rfl | rfl
      · exact ⟨c.hyp.hL.1, h3L⟩
      · exact ⟨hK5.1, h3K⟩
  have hLpStar : S17.calLpStar D 3 = S17.calLpStar D 5 := by
    ext X
    simp only [S17.mem_calLpStar]
    rw [hLp]
  have hLjStar : ∀ j, S17.calLjStar D 3 j = S17.calLjStar D 5 j := by
    intro j
    simp only [S17.calLjStar]
    split_ifs <;>
      simp [S17.calL1Star, S17.calL2Star, S17.calL3Star, S17.calL4Star,
        S17.calL5Star, hLpStar, hLp]
  have hJM : S17.jM D 3 = S17.jM D 5 := by
    unfold S17.jM
    congr 1
    ext j
    simp only [hLjStar]
  have hL0 : S17.calL0Star D 3 = S17.calL0Star D 5 := by
    simp only [S17.calL0Star, hJM, hLjStar]
  have hHyp3 : Hyp18 D V₀ V 3 L :=
    { hyp125 := c.hyp.hyp125
      hp := h3sig
      hL := by rw [hLp]; exact c.hyp.hL
      hX := by rw [hL0]; exact c.hyp.hX
      small := c.hyp.small }
  have hL3 : L ∈ S17.calLp D 3 := by rw [hLp]; exact c.hyp.hL
  have hX3 : UC22.conjClosure D.M L ∈ S17.calL0Star D 3 := by
    rw [hL0]; exact c.hyp.hX
  have h := h1768 3 h3sig L hL3 (UC22.conjClosure D.M L) rfl hX3 c.alt
  exact absurd h.1 (by norm_num)

theorem A5Data18.exists_second {D : Data G} {V₀ V L : Subgroup G}
    (c : A5Data18 D V₀ V L)
    :
    ∃ K ∈ calC D.M, K ≠ L ∧ UC22.IsAlt (Bar2 K) 5 ∧ K ∈ S17.calLp D 5 ∧
      UC22.conjClosure D.M K ∈ S17.calL0Star D 5 ∧
      (∀ J ∈ calC D.M, J = L ∨ J = K) ∧
      ⁅L, K⁆ ≤ pCoreOf 2 D.M ∧
      ((UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
        (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧
          (K.subgroupOf D.M).Normal)) := by
  obtain ⟨K, hK, hKne, hAltK⟩ := c.exists_second_component
  have hK5 : K ∈ S17.calLp D 5 :=
    ⟨hK, Nat.prime_five,
      CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49.five_dvd_card_of_isAlt hAltK⟩
  have hcal : ∀ J ∈ calC D.M, J = L ∨ J = K := c.calC_eq hK hKne
  have hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M := c.commutator_le hK hKne
  have hdich := c.dichotomy hK hKne hcal
  have hKX := c.conjClosure_K_mem_calL0Star hK hK5 hAltK hdich
  exact ⟨K, hK, hKne, hAltK, hK5, hKX, hcal, hcomm, hdich⟩

theorem A5Data18.three_not_mem_sig
    {D : Data G} {V₀ V L : Subgroup G} (c : A5Data18 D V₀ V L)
    (h1768 : S17.R17_68At D V₀ V) : 3 ∉ D.sig := by
  obtain ⟨K, hK, hKne, hAltK⟩ := c.exists_second_component
  have hK5 : K ∈ S17.calLp D 5 :=
    ⟨hK, Nat.prime_five,
      CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49.five_dvd_card_of_isAlt hAltK⟩
  have hcal : ∀ J ∈ calC D.M, J = L ∨ J = K := c.calC_eq hK hKne
  exact three_not_mem_sig_aux c hK hK5 hAltK hcal h1768

theorem map_mbarImage_barSub {M V X : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal]
    (hXM : X ≤ M) :
    (mbarImage M V X).map
        ((mbarEquiv M V).trans (mbarEquivBarSub hMV hV)).toMonoidHom =
      (barSub ⊥ V hV X).subgroupOf (barSub ⊥ V hV M) := by
  classical
  rw [show ((mbarEquiv M V).trans (mbarEquivBarSub hMV hV)).toMonoidHom =
      (mbarEquivBarSub hMV hV).toMonoidHom.comp (mbarEquiv M V).toMonoidHom from rfl]
  rw [← Subgroup.map_map]
  rw [map_mbarImage]
  apply Subgroup.map_injective (f := (barSub ⊥ V hV M).subtype)
    (barSub ⊥ V hV M).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (barSub_mono ⊥ V hV hXM)]
  exact map_barImage11_mbarEquivBarSub hMV hV hXM

theorem A5Data18.compBar_subset {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hV₀ : V₀ = ⊥)
    (hV : IsElemAbelian 2 V) (hMV : D.M ≤ normalizer (V : Set G))
    (hH : F11.Hyp11 D ⊥ V) (h119 : R119W D)
    (hK : K ∈ calC D.M) (hKne : K ≠ L) :
    ∀ J, CFSG.Open.IsComponentOf J (Mbar D.M ⊥ V hV) →
      J = barSub ⊥ V hV L ∨ J = barSub ⊥ V hV K := by
  subst hV₀
  classical
  have hN : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.cTilde_bot_normal D.M V hMV
  let e : MBar D.M V ≃* ↥(barSub ⊥ V hV D.M) :=
    (mbarEquiv D.M V).trans (mbarEquivBarSub hMV hV)
  intro J hJ
  have hJle : J ≤ Mbar D.M ⊥ V hV := hJ.1
  let J' : Subgroup ↥(barSub ⊥ V hV D.M) := J.subgroupOf (barSub ⊥ V hV D.M)
  have hJ'comp : CFSG.IsComponent J' :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJle).1
      ((CFSG.Assembly.isComponentOf_iff_open).2 hJ)
  let Lb : Subgroup (MBar D.M V) := J'.map e.symm.toMonoidHom
  have hLbcomp : CFSG.IsComponent Lb :=
    CFSG.LocalCores.isComponent_map_mulEquiv e.symm hJ'comp
  have hLb : CFSG.Open.IsComponentOf Lb ⊤ := (CFSG.isComponent_iff_open Lb).mp hLbcomp
  obtain ⟨X, hX, hXL⟩ := uc22p22vg_exists_calC_image D hMV hH h119 hLb
  have hJmap : Lb.map e.toMonoidHom = J' := by
    rw [Subgroup.map_map]
    rw [show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ from by
      ext x; simp]
    exact Subgroup.map_id J'
  have hcal : ∀ Y ∈ calC D.M, Y = L ∨ Y = K := c.calC_eq hK hKne
  rcases hcal X hX with hLX | hKX
  · left
    have hmap : (mbarImage D.M V L).map e.toMonoidHom =
        (barSub ⊥ V hV L).subgroupOf (barSub ⊥ V hV D.M) :=
      map_mbarImage_barSub hMV hV (s13_le_of_mem_calC c.hyp.hL.1)
    have hEq : J' = (barSub ⊥ V hV L).subgroupOf (barSub ⊥ V hV D.M) := by
      rw [← hJmap, ← hXL, hLX, hmap]
    calc J = J'.map (barSub ⊥ V hV D.M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hJle).symm
      _ = ((barSub ⊥ V hV L).subgroupOf (barSub ⊥ V hV D.M)).map
            (barSub ⊥ V hV D.M).subtype := by rw [hEq]
      _ = barSub ⊥ V hV L := Subgroup.map_subgroupOf_eq_of_le
            (barSub_mono ⊥ V hV (s13_le_of_mem_calC c.hyp.hL.1))
  · right
    have hmap : (mbarImage D.M V K).map e.toMonoidHom =
        (barSub ⊥ V hV K).subgroupOf (barSub ⊥ V hV D.M) :=
      map_mbarImage_barSub hMV hV (s13_le_of_mem_calC hK)
    have hEq : J' = (barSub ⊥ V hV K).subgroupOf (barSub ⊥ V hV D.M) := by
      rw [← hJmap, ← hXL, hKX, hmap]
    calc J = J'.map (barSub ⊥ V hV D.M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hJle).symm
      _ = ((barSub ⊥ V hV K).subgroupOf (barSub ⊥ V hV D.M)).map
            (barSub ⊥ V hV D.M).subtype := by rw [hEq]
      _ = barSub ⊥ V hV K := Subgroup.map_subgroupOf_eq_of_le
            (barSub_mono ⊥ V hV (s13_le_of_mem_calC hK))

theorem barImage_inf_eq_bot_of_calC {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hLalt : IsAlt (Bar2 L) 5)
    (hcomm : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M K, a * b = b * a) :
    barImage D.M L ⊓ barImage D.M K = ⊥ := by
  let eL := (s13_bar_equiv hL).some
  have hcenter : Subgroup.center ↥(barImage D.M L) = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv
      (eL.symm.trans hLalt.some) (alternatingGroup.center_eq_bot (by norm_num))
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxcenter : (⟨x, hx.1⟩ : ↥(barImage D.M L)) ∈
      Subgroup.center ↥(barImage D.M L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcomm y y.2 x hx.2
  rw [hcenter, Subgroup.mem_bot] at hxcenter
  exact Subtype.ext_iff.mp hxcenter

theorem isA5xA5_barImage_sup_of_calC {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hLalt : IsAlt (Bar2 L) 5) (hKalt : IsAlt (Bar2 K) 5)
    (hcomm : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M K, a * b = b * a) :
    S17.IsA5xA5 ↥(barImage D.M (L ⊔ K)) := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hsup : barImage D.M (L ⊔ K) = barImage D.M L ⊔ barImage D.M K :=
    s13_barImage_sup hLM hKM
  have hdisj : barImage D.M L ⊓ barImage D.M K = ⊥ :=
    barImage_inf_eq_bot_of_calC hL hK hKne hLalt hcomm
  let eL := (s13_bar_equiv hL).some
  let eK := (s13_bar_equiv hK).some
  have eL5 : ↥(barImage D.M L) ≃* alternatingGroup (Fin 5) := eL.symm.trans hLalt.some
  have eK5 : ↥(barImage D.M K) ≃* alternatingGroup (Fin 5) := eK.symm.trans hKalt.some
  have hprod : ↥(barImage D.M L) × ↥(barImage D.M K) ≃*
      ↥(barImage D.M L ⊔ barImage D.M K) :=
    CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcomm hdisj
  have hcast : ↥(barImage D.M (L ⊔ K)) ≃*
      ↥(barImage D.M L ⊔ barImage D.M K) := MulEquiv.subgroupCongr hsup
  exact ⟨hcast.trans (hprod.symm.trans (eL5.prodCongr eK5))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
