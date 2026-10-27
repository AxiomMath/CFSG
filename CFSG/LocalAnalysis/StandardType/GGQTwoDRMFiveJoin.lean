module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveLin
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFormB
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSat
import CFSG.LocalAnalysis.StandardType.GGQTwoGlobSelected
import CFSG.LocalAnalysis.StandardType.GGFLWReflForm
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveOrbit

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem qtwoD_ainf_isometry {m : ℕ} (hm : 4 ≤ m) (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hAL : GGWeylReflectionGroup 3 (ggAutomizer L Bs)) (β : Additive ↥Bs ≃+ DVec m)
    (hβ : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) = dEven m)
    {g : DVec m ≃ₗ[ZMod 3] DVec m} (hg : g ∈ (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β))
    (v w : DVec m) : dDot m (g v) (g w) = dDot m v w := by
  have hW : dEven m ≤ (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β) := by
    rw [← hβ]
    exact Subgroup.map_mono (qTwoGlobSel_join_le_ggAInf hcfg)
  have hTF : ∀ g ∈ (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β), g ≠ 1 →
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg
    change g ∈ qTwoBarA B Bs L D J x β at hg
    exact qTwo_bar_notr B Bs L D J x β hcfg.1.2.2.2.1 hg
  have hgen : (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β) =
      Subgroup.closure {t | t ∈ (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β) ∧
        GGLinRefl t} := by
    have h1 := qtwoD_ainf_reflGen hcfg hAL
    apply le_antisymm
    · calc (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β)
          = (Subgroup.closure {φ | φ ∈ ggAInf 3 B Bs x L D J ∧
              GGIsReflection 3 φ}).map (ggLin (p := 3) β) := by rw [← h1]
        _ = Subgroup.closure (ggLin (p := 3) β ''
              {φ | φ ∈ ggAInf 3 B Bs x L D J ∧ GGIsReflection 3 φ}) :=
            MonoidHom.map_closure _ _
        _ ≤ _ := by
            refine Subgroup.closure_mono ?_
            rintro t ⟨φ, ⟨hφA, hφr⟩, rfl⟩
            exact ⟨Subgroup.mem_map_of_mem _ hφA,
              (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) β φ).mp hφr⟩
    · exact (Subgroup.closure_le _).mpr fun t ht => ht.1
  exact qtwoD_isometry_of_reflGen hm hW hTF hgen hg v w

private theorem dichotomy_of_weyl (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hAL : GGWeylReflectionGroup 3 (ggAutomizer L Bs)) (β : Additive ↥Bs ≃+ DVec 5)
    (hβ : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) = dEven 5)
    {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K) {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (htype : GGWeylOfType 3 M (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 ∨
      (ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β) = dNormTwo 5 := by
  have hW_le : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J :=
    sup_le (le_trans (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦)
        (qTwoGlobSel_join_le_ggAInf hcfg)) (ggAutomizer_le_ggAInf_of_nbr hK)
  have hiso : ∀ g ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β),
      ∀ v w : DVec 5, dDot 5 (g v) (g w) = dDot 5 v w := by
    intro g hg v w
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    exact qtwoD_ainf_isometry (m := 5) (by norm_num) hcfg hAL β hβ
      (Subgroup.mem_map_of_mem _ (hW_le hφ)) v w
  obtain ⟨e, he⟩ := htype
  let f : M.Group ≃* ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β)) :=
    e.trans (Subgroup.equivMapOfInjective (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
      (ggLin (p := 3) β) (ggLin_injective (p := 3) β))
  have hfcoe : ∀ i : ι,
      ((f (M.simple i) : ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β))) :
          DVec 5 ≃ₗ[ZMod 3] DVec 5) =
        ggLin (p := 3) β
          ((e (M.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) :=
    fun i => Subgroup.coe_equivMapOfInjective_apply (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
      (ggLin (p := 3) β) (ggLin_injective (p := 3) β) (e (M.simple i))
  have hf : ∀ i : ι, GGLinRefl
      (f (M.simple i) : DVec 5 ≃ₗ[ZMod 3] DVec 5) := by
    intro i
    rw [hfcoe i]
    exact (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) β _).mp (he i)
  obtain ⟨ιL, ML, hML, fL, hfL⟩ := hAL
  have hneL : Nonempty ιL := by
    rcases hML with ⟨n, eL, hn, -⟩ | ⟨eL, -⟩ | ⟨eL, -⟩ | ⟨eL, -⟩ | ⟨eL, -⟩ | ⟨eL, -⟩
    · exact ⟨eL ⟨0, by omega⟩⟩
    · exact ⟨eL 0⟩
    · exact ⟨eL 0⟩
    · exact ⟨eL 0⟩
    · exact ⟨eL 0⟩
    · exact ⟨eL 0⟩
  let r : MulAut ↥Bs := ((fL (ML.simple hneL.some) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hrA : r ∈ ggAutomizer L Bs := (fL (ML.simple hneL.some)).2
  have hrr : GGIsReflection 3 r := hfL hneL.some
  let t : DVec 5 ≃ₗ[ZMod 3] DVec 5 := ggLin (p := 3) β r
  have ht : t ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hrA)
  have htdEven : t ∈ dEven 5 := by
    rw [← hβ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hrA)
  have htr : GGLinRefl t :=
    (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) β r).mp hrr
  obtain ⟨c, φ, -, hφc, hform⟩ := ggFLW_isRefl_form (p := 3) (by norm_num) htr
  have hc : t c = -c := by
    rw [hform c, hφc]
    module
  have hcn : dDot 5 c c = 2 := dEven_reflection_norm htdEven hφc hform
  have hNorm := le_dNormTwo_of_weylOfType (n := 5)
    (ggSimplyLacedConnected_of_weyl hM h3) hiso f hf ht htr hc hcn
  have hWnorm : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β) ≤
      dNormTwo 5 := hNorm.2
  by_cases hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦
  · exact Or.inl hle
  refine Or.inr ?_
  have hex : ∃ i : ι,
      ((e (M.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∉
        ggAutomizerJoin L Bs 𝒦 := by
    by_contra hcon
    have hall : ∀ i : ι,
        ((e (M.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
          ggAutomizerJoin L Bs 𝒦 := by
      intro i
      by_contra hi
      exact hcon ⟨i, hi⟩
    apply hle
    intro a ha
    obtain ⟨w, hw⟩ := e.surjective ⟨a, Subgroup.mem_sup_right ha⟩
    have htop : Subgroup.closure (Set.range M.simple) = (⊤ : Subgroup M.Group) :=
      PresentedGroup.closure_range_of M.relationsSet
    have hw' : w ∈ Subgroup.closure (Set.range M.simple) := by
      rw [htop]
      trivial
    have hmem : ((e w : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
        ggAutomizerJoin L Bs 𝒦 := by
      refine Subgroup.closure_induction (p := fun w _ =>
        ((e w : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
          ggAutomizerJoin L Bs 𝒦) ?_ ?_ ?_ ?_ hw'
      · rintro _ ⟨i, rfl⟩
        exact hall i
      · simp
      · intro u v _ _ hu hv
        simpa using mul_mem hu hv
      · intro u _ hu
        simpa using inv_mem hu
    have hcoe : ((e w : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) = a := by
      have h := congrArg (fun x : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) =>
        ((x : MulAut ↥Bs))) hw
      simpa using h
    simpa [hcoe] using hmem
  obtain ⟨i, hi⟩ := hex
  have ht'not : (f (M.simple i) : DVec 5 ≃ₗ[ZMod 3] DVec 5) ∉ dEven 5 := by
    intro hmem
    rw [hfcoe i, ← hβ] at hmem
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hmem
    have ha' : a = ((e (M.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) :=
      ggLin_injective (p := 3) β haeq
    exact hi (ha' ▸ ha)
  have ht'class : (f (M.simple i) : DVec 5 ≃ₗ[ZMod 3] DVec 5) ∈
      ZS.ClassRefl 3 (dQuadTwo 5) 1 := hNorm.1 i
  have ht'le : Subgroup.zpowers (f (M.simple i) : DVec 5 ≃ₗ[ZMod 3] DVec 5) ≤
      (ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [hfcoe i]
    refine Subgroup.mem_map_of_mem _ ?_
    exact sup_le (le_trans (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦)
      (le_sup_left : ggAutomizerJoin L Bs 𝒦 ≤
        ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K Bs)) le_sup_right
      ((e (M.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))).2
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [hβ]
      exact dEven_le_dNormTwo (by norm_num)
    · exact le_trans (Subgroup.map_mono le_sup_right) hWnorm
  · calc dNormTwo 5 ≤ dEven 5 ⊔
        Subgroup.zpowers (f (M.simple i) : DVec 5 ≃ₗ[ZMod 3] DVec 5) :=
        dNormTwo_five_le_sup ht'class ht'not
      _ ≤ (ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β) := by
        refine sup_le ?_ ht'le
        rw [← hβ]
        exact Subgroup.map_mono le_sup_left

theorem qtwoD5_join_dichotomy (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hAL : GGWeylReflectionGroup 3 (ggAutomizer L Bs)) (β : Additive ↥Bs ≃+ DVec 5)
    (hβ : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) = dEven 5) {y : G} {K : Subgroup G}
    (hK : GGNbr 3 B x D J y K)
    (htype : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
      GGWeylOfType 3 (ggCoxeterMatrixD 5) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 ∨
      (ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K Bs).map (ggLin (p := 3) β) = dNormTwo 5 := by
  rcases htype with htype | htype
  · refine dichotomy_of_weyl (M := CoxeterMatrix.A 5) hcfg hAL β hβ hK
      (Or.inl ⟨5, Equiv.refl _, by norm_num, Or.inl rfl⟩) ?_ htype
    intro i j hij
    simp only [CoxeterMatrix.A, Matrix.of_apply, hij, ite_false]
    split_ifs <;> norm_num
  · refine dichotomy_of_weyl (M := ggCoxeterMatrixD 5) hcfg hAL β hβ hK
      (Or.inl ⟨5, Equiv.refl _, by norm_num, Or.inr (Or.inr ⟨by norm_num, rfl⟩)⟩) ?_ htype
    intro i j hij
    rw [ggCoxeterMatrixD_apply, if_neg hij]
    split_ifs <;> norm_num

end

end CFSG.StandardType.QTwo

end
