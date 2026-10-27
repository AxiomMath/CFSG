module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSL3Sub
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSL3Par
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapCoverF4
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapCoverA2
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapMap
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private theorem wcgapsf_map_centralizer_eq {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (S : Subgroup M) :
    (Subgroup.centralizer (S : Set M)).map e.toMonoidHom =
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup M') : Set M') := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (S : Set M) e.toMonoidHom
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (e.toMonoidHom s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)

private lemma wcgapsf_injOn_of_isPGroup {G₀ G : Type} [Group G₀] [Finite G₀] [Group G]
    (α : G₀ →* G) (hodd : Odd (Nat.card ↥α.ker)) {P : Subgroup G₀}
    (hP : IsPGroup 2 P) : ∀ x ∈ P, ∀ y ∈ P, α x = α y → x = y := by
  obtain ⟨n, hn⟩ := hP.exists_card_dvd_pow
  have hcop : Nat.Coprime (Nat.card ↥α.ker) (Nat.card ↥P) :=
    Nat.Coprime.of_dvd (dvd_refl _) hn (hodd.coprime_two_right.pow_right n)
  have hinf : α.ker ⊓ P = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ α.ker ⊓ P :=
    Subgroup.mem_inf.mpr
      ⟨by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel],
        P.mul_mem (P.inv_mem hx) hy⟩
  rw [hinf] at hmem
  exact inv_mul_eq_one.mp (by simpa using hmem)

private lemma wcgapsf_map_inf_centralizer_of_injOn {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) (P : Subgroup G₀)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, α x = α y → x = y) :
    (P ⊓ Subgroup.centralizer (P : Set G₀)).map α =
      P.map α ⊓ Subgroup.centralizer ((P.map α : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨z, hzP, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s' hs'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs'
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hzc t ht]
  · intro s hs
    obtain ⟨hsS, hsc⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨z, hzP, rfl⟩ := Subgroup.mem_map.mp hsS
    refine Subgroup.mem_map.mpr ⟨z, Subgroup.mem_inf.mpr ⟨hzP, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hcomm := Subgroup.mem_centralizer_iff.mp hsc (α t)
      (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    have hker : α (z * t * z⁻¹ * t⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hmem : z * t * z⁻¹ * t⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hzP ht) (P.inv_mem hzP)) (P.inv_mem ht)
    have h1 : z * t * z⁻¹ * t⁻¹ = 1 :=
      hinj _ hmem 1 P.one_mem (by simpa using hker)
    have ht1 : z * t * z⁻¹ = t := by
      have := congrArg (· * t) h1
      simpa [mul_assoc] using this
    have hzt : z * t = t * z := by
      have := congrArg (· * z) ht1
      simpa [mul_assoc] using this
    exact hzt.symm

private theorem wcgapsf_exists_sylow_eq_of_isSylowIn_top {M : Type} [Group M] [Finite M]
    {S : Subgroup M} (hS : IsSylowIn 2 S (⊤ : Subgroup M)) :
    ∃ P : Sylow 2 M, (P : Subgroup M) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hS.isPGroup.toSylow ?_, IsPGroup.toSylow_coe _ _⟩
  have := hS.not_dvd_relIndex
  rwa [Subgroup.relIndex_top_right] at this

theorem centralKData_slThree {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F)) :
    CentralKData (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
      ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ⊓ centralizer
        ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))) := by
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  obtain ⟨U, hU⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) F) U S
  let e : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    MulAut.conj g
  have hSmap : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) =
      (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map e.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] <;> rfl
  have hUdata : CentralKData (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
      ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ⊓
        Subgroup.centralizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))) := by
    rw [hU]
    exact centralKData_slThree_unitriangular (F := F) hF
  have hmap : ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ⊓
        Subgroup.centralizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))).map e.toMonoidHom =
      (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map e.toMonoidHom ⊓
        Subgroup.centralizer (((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map
          e.toMonoidHom : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
            Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    rw [Subgroup.map_inf (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
        (Subgroup.centralizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))) e.toMonoidHom e.injective,
      wcgapsf_map_centralizer_eq e (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))]
  rw [hSmap, ← hmap]
  exact centralKData_map e hUdata

theorem rankTwoParabData_slThree {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F)) :
    RankTwoParabData (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  obtain ⟨U, hU⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) F) U S
  let e : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    MulAut.conj g
  have hSmap : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) =
      (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map e.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] <;> rfl
  have hUdata : RankTwoParabData (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    rw [hU]
    exact rankTwoParabData_slThree_unitriangular (F := F) hF
  rw [hSmap]
  exact rankTwoParabData_map e hUdata

theorem centralKData_of_hasSL3Cover {G : Type} [Group G] [Finite G]
    (h : HasSL3Cover G) (S : Sylow 2 G) :
    CentralKData (S : Subgroup G) ((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) := by
  obtain ⟨F, hF, hFin, hFcard, α, hα, hkerle⟩ := h
  letI : Field F := hF
  letI : Finite F := hFin
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin]
    exact CFSG.Open.StatedCenterThree.card_rootsOfUnity_three (by norm_num [hFcard])
  have hdvd : Nat.card ↥α.ker ∣ 3 := by
    have h3 := Subgroup.card_dvd_of_le hkerle
    convert h3 using 1
    exact hcenter.symm
  have hodd : Odd (Nat.card ↥α.ker) := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (Nat.card ↥α.ker) hdvd with h1 | h3
    · rw [h1]; exact odd_one
    · rw [h3]; exact ⟨1, by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀eq⟩ := Sylow.mapSurjective_surjective (p := 2) hα S
  have hSeq : (S : Subgroup G) =
      (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map α := by
    have h := hS₀eq ▸ Sylow.coe_mapSurjective hα S₀
    simpa using h
  have hinj : ∀ x ∈ (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)),
      ∀ y ∈ (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)), α x = α y → x = y :=
    wcgapsf_injOn_of_isPGroup α hodd S₀.isPGroup'
  have hZeq : ((S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ⊓
        Subgroup.centralizer ((S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))).map α =
      (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map α ⊓
        Subgroup.centralizer (((S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map α :
          Subgroup G) : Set G) :=
    wcgapsf_map_inf_centralizer_of_injOn α
      (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) hinj
  rw [hSeq, ← hZeq]
  exact centralKData_of_cover α hα hkerle hodd S₀.isPGroup' inf_le_left
    (centralKData_slThree hFcard S₀)

theorem rankTwoParabData_of_hasSL3Cover {G : Type} [Group G]
    [Finite G] (h : HasSL3Cover G) (S : Sylow 2 G) : RankTwoParabData (S : Subgroup G) := by
  obtain ⟨F, hF, hFin, hFcard, α, hα, hkerle⟩ := h
  letI : Field F := hF
  letI : Finite F := hFin
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin]
    exact CFSG.Open.StatedCenterThree.card_rootsOfUnity_three (by norm_num [hFcard])
  have hdvd : Nat.card ↥α.ker ∣ 3 := by
    have h3 := Subgroup.card_dvd_of_le hkerle
    convert h3 using 1
    exact hcenter.symm
  have hodd : Odd (Nat.card ↥α.ker) := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (Nat.card ↥α.ker) hdvd with h1 | h3
    · rw [h1]; exact odd_one
    · rw [h3]; exact ⟨1, by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀eq⟩ := Sylow.mapSurjective_surjective (p := 2) hα S
  have hSeq : (S : Subgroup G) =
      (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map α := by
    have h := hS₀eq ▸ Sylow.coe_mapSurjective hα S₀
    simpa using h
  have hSyl : IsSylowIn 2 (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    refine ⟨le_top, S₀.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S₀.not_dvd_index
  rw [hSeq]
  exact rankTwoParabData_of_cover α hα hkerle hodd hSyl
    (rankTwoParabData_slThree hFcard S₀)

theorem choiceOfKTop_of_hasSL3Cover {G : Type} [Group G] [Finite G]
    (h : HasSL3Cover G) (rk : Prop) : ChoiceOfKTop G rk := by
  refine choiceOfKTop_of_central_data rk fun S hS => ?_
  obtain ⟨P, rfl⟩ := wcgapsf_exists_sylow_eq_of_isSylowIn_top hS
  refine ⟨?_, Or.inr (rankTwoParabData_of_hasSL3Cover h P)⟩
  intro A hAS hAc _hAe hA4 _hTIS
  exact centralKData_of_card_center_four (a2KleinData_of_hasSL3Cover h P).2.1
    (centralKData_of_hasSL3Cover h P) A hAS hAc hA4

theorem choiceOfKOn_shapeSL3 :
    ChoiceOfKOn ShapeSL3 :=
  choiceOfKOn_of_top ShapeSL3 fun Y _ _ L hL =>
    ⟨↥L, inferInstance, MulEquiv.refl _,
      choiceOfKTop_of_hasSL3Cover (hasSL3Cover_of_shapeSL3 hL) _⟩

theorem choiceOfKOn_shapeL3 : ChoiceOfKOn ShapeL3 :=
  choiceOfKOn_of_top ShapeL3 fun Y _ _ L hL =>
    ⟨↥L, inferInstance, MulEquiv.refl _,
      choiceOfKTop_of_hasSL3Cover (hasSL3Cover_of_shapeL3 hL) _⟩

end CFSG.LocalAnalysis.WeakClosure81

end
