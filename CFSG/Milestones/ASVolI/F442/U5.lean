module

public import CFSG.Milestones.ASVolI.F442.Amal
public import CFSG.Milestones.ASVolI.F431.RU5Out
public import CFSG.Milestones.ASVolI.F431.AU5Syl

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section U5Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {K : Type} [Field K]

theorem burnsideF42g_u5_omega (h : UnitaryFieldData 2 1 K) : ∃ ω : K, ω * ω + ω + 1 = 0 := by
  classical
  haveI := h.finite
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, h.card]; norm_num
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    have hall : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (by_contra fun hx1 => hcon ⟨x, hx, hx1⟩)
    have hle : Fintype.card K ≤ 2 := by
      calc Fintype.card K = (Finset.univ : Finset K).card := rfl
        _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card (fun x _ => by
            rcases hall x with rfl | rfl <;> simp)
        _ ≤ 2 := Finset.card_le_two
    omega
  refine ⟨ω, ?_⟩
  have h4 : ω ^ 4 = ω := by rw [← hcard]; exact FiniteField.pow_card ω
  have hprod : ω * (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp hprod with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hω0
    · exact absurd (sub_eq_zero.mp h'') hω1
  · exact h'

theorem burnsideF42g_u5_herm_cases {h : UnitaryFieldData 2 1 K} {ω : K} (hω : ω * ω + ω + 1 = 0)
    {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hd : Y.det = 0)
    (hdJ : (Y + !![0, 1; 1, 0]).det = 0) :
    Y = !![1, ω + 1; ω, 1] ∨ Y = !![1, ω; ω + 1, 1] := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h00, h11, h10⟩ := isHerm_iff.mp hY
  rw [h.bar_apply, pow_one, pow_two] at h00 h11 h10
  rw [Matrix.det_fin_two] at hd hdJ
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, add_zero] at hdJ
  have hlin : Y 1 0 = Y 0 1 + 1 := by
    linear_combination hd - hdJ - (Y 0 1 + 1) * h2
  have hq : Y 0 1 * Y 0 1 + Y 0 1 + 1 = 0 := by
    linear_combination hlin - h10 + (Y 0 1 + 1) * h2
  have hp : Y 0 0 * Y 1 1 = 1 := by
    linear_combination hd + Y 0 1 * hlin + hq - h2
  have h00' : Y 0 0 = 1 := by
    rcases mul_eq_zero.mp (show Y 0 0 * (Y 0 0 - 1) = 0 by linear_combination h00) with e | e
    · rw [e, zero_mul] at hp; exact absurd hp zero_ne_one
    · exact sub_eq_zero.mp e
  have h11' : Y 1 1 = 1 := by rw [h00', one_mul] at hp; exact hp
  have hroot : (Y 0 1 - ω) * (Y 0 1 + ω + 1) = 0 := by linear_combination hq - hω
  rcases mul_eq_zero.mp hroot with e | e
  · right
    have e1 : Y 0 1 = ω := sub_eq_zero.mp e
    have e2 : Y 1 0 = ω + 1 := by rw [hlin, e1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00', h11', e1, e2]
  · left
    have e1 : Y 0 1 = ω + 1 := by linear_combination e - (ω + 1) * h2
    have e2 : Y 1 0 = ω := by rw [hlin, e1]; linear_combination h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00', h11', e1, e2]

variable {h : UnitaryFieldData 2 1 K}

theorem burnsideF42g_u5_isHerm_add {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hY' : IsHerm h Y') : IsHerm h (Y + Y') := by
  unfold IsHerm at hY hY' ⊢
  rw [Matrix.map_add _ (map_add h.bar), Matrix.transpose_add, add_add_add_comm, hY, hY', add_zero]

theorem burnsideF42g_u5_vSU_mul {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hY' : IsHerm h Y') :
    vSU h Y hY * vSU h Y' hY' = vSU h (Y + Y') (burnsideF42g_u5_isHerm_add hY hY') := by
  apply mat_injective
  rw [mat_mul, mat_vSU, mat_vSU, mat_vSU, oddUni_mul]
  congr 1
  · simp
  · ext i j
    simp [vecMulVec]

theorem burnsideF42g_u5_conj_z {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hY0 : Y ≠ 0)
    (hd : Y.det = 0) : IsConj (Un.z5Y h) (hypProj h 2 1 (vSU h Y hY)) := by
  have hz1 : z₁SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_e₁₁ h)
  have hv : vSU h Y hY ∈ Vsub h := vSU_mem_Vsub hY
  have hYv : Yof (vSU h Y hY) = Y := Yof_eq (mat_vSU hY)
  obtain ⟨A, hA, hAv⟩ := Un.exists_lev_conj_of_det_eq_zero hz1 hv
    (by
      rw [Un.Yof_z₁SU]
      intro e
      have := congrFun (congrFun e 0) 0
      simp at this)
    (by rw [Un.Yof_z₁SU]; simp [Matrix.det_fin_two])
    (by rw [hYv]; exact hY0) (by rw [hYv]; exact hd)
  refine isConj_iff.mpr ⟨hypProj h 2 1 (lev (hK := h) A hA), ?_⟩
  rw [Un.z5Y, ← map_inv, ← map_mul, ← map_mul, hAv]

theorem burnsideF42g_u5_det_of_conj {v : hypSU h 2 1} (hv : v ∈ Vsub h)
    (hc : IsConj (Un.z5Y h) (hypProj h 2 1 v)) : (Yof v).det = 0 := by
  by_contra hd
  have hz2 : z₂SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_swap h)
  obtain ⟨A, hA, hAv⟩ := Un.exists_lev_conj_of_det_ne_zero hv hz2 hd
    (by rw [Un.Yof_z₂SU]; simp [Matrix.det_fin_two])
  have h1 : IsConj (hypProj h 2 1 v) (Un.t5Y h) := by
    refine isConj_iff.mpr ⟨hypProj h 2 1 (lev (hK := h) A hA), ?_⟩
    rw [Un.t5Y, ← map_inv, ← map_mul, ← map_mul, hAv]
  obtain ⟨c, hcz⟩ := isConj_iff.mp (hc.trans h1)
  exact Un.noconj_Y (MulAut.conj c) (by rw [MulAut.conj_apply]; exact hcz)

theorem burnsideF42g_conj_mem_centerOf {G : Type*} [Group G] {Q : Subgroup G} {x c : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) (hc : c ∈ centerOf Q) :
    x * c * x⁻¹ ∈ centerOf Q := by
  obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx c).mp hcQ, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : x⁻¹ * q * x ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) q).mp hq
    rwa [inv_inv] at this
  have hcomm := Subgroup.mem_centralizer_iff.mp hcC _ hq'
  calc q * (x * c * x⁻¹) = x * ((x⁻¹ * q * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * q * x)) * x⁻¹ := by rw [hcomm]
    _ = x * c * x⁻¹ * q := by group

theorem burnsideF42g_u5_u_inv {ω : K} (hω : ω * ω + ω + 1 = 0)
    (hU : IsHerm h !![1, ω + 1; ω, 1]) {x : hypPSU h 2 1}
    (hx : x ∈ Subgroup.centralizer ({Un.t5Y h} : Set (hypPSU h 2 1))) :
    x * hypProj h 2 1 (vSU h _ hU) * x⁻¹ = hypProj h 2 1 (vSU h _ hU) ∨
      x * hypProj h 2 1 (vSU h _ hU) * x⁻¹ = hypProj h 2 1 (vSU h _ hU) * Un.t5Y h := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ : IsHerm h (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := isHerm_swap h
  have hUJ := burnsideF42g_u5_isHerm_add hU hJ
  have hω0 : ω ≠ 0 := fun e => by rw [e] at hω; simp at hω
  have hUne : (!![1, ω + 1; ω, 1] : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro e
    have := congrFun (congrFun e 0) 0
    simp at this
  have hUd : (!![1, ω + 1; ω, 1] : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    rw [Matrix.det_fin_two_of]
    linear_combination -hω + h2
  have hUJne : (!![1, ω + 1; ω, 1] + !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro e
    have := congrFun (congrFun e 0) 0
    simp at this
  have hUJd : (!![1, ω + 1; ω, 1] + !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    rw [Matrix.det_fin_two]
    simp
    linear_combination -hω - ω * h2
  have hxP : x ∈ u5LnP h := Un.cent_t_Y hx
  have hnorm : x ∈ Subgroup.normalizer ((pCoreOf 2 (u5LnP h) : Subgroup (hypPSU h 2 1)) :
      Set (hypPSU h 2 1)) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hxP
  have hV : ∀ c ∈ Un.v5Y h, x * c * x⁻¹ ∈ Un.v5Y h := by
    intro c hc
    rw [Un.v5Y_eq_centerOf_pCoreOf] at hc ⊢
    exact burnsideF42g_conj_mem_centerOf hnorm hc
  set u := hypProj h 2 1 (vSU h _ hU) with hudef
  have huV : u ∈ Un.v5Y h := ⟨_, vSU_mem_Vsub hU, rfl⟩
  obtain ⟨v, hv, hvy⟩ := hV u huV
  have hzu : IsConj (Un.z5Y h) u := burnsideF42g_u5_conj_z hU hUne hUd
  have hut : u * Un.t5Y h = hypProj h 2 1 (vSU h _ hUJ) := by
    rw [hudef, Un.t5Y, ← map_mul]
    congr 1
    exact burnsideF42g_u5_vSU_mul hU hJ
  have hzut : IsConj (Un.z5Y h) (u * Un.t5Y h) := by
    rw [hut]
    exact burnsideF42g_u5_conj_z hUJ hUJne hUJd
  have hxt : x * Un.t5Y h * x⁻¹ = Un.t5Y h := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  have hzy : IsConj (Un.z5Y h) (hypProj h 2 1 v) := by
    rw [hvy]
    exact hzu.trans (isConj_iff.mpr ⟨x, rfl⟩)
  have hvz : v * z₂SU h ∈ Vsub h := Subgroup.mul_mem _ hv (vSU_mem_Vsub hJ)
  have hzyt : IsConj (Un.z5Y h) (hypProj h 2 1 (v * z₂SU h)) := by
    rw [map_mul, hvy]
    have e : x * u * x⁻¹ * hypProj h 2 1 (z₂SU h) = x * (u * Un.t5Y h) * x⁻¹ := by
      rw [Un.t5Y]
      conv_rhs => rw [show x * (u * hypProj h 2 1 (z₂SU h)) * x⁻¹ =
        x * u * x⁻¹ * (x * hypProj h 2 1 (z₂SU h) * x⁻¹) by group]
      rw [← Un.t5Y, hxt, Un.t5Y]
    rw [e]
    exact hzut.trans (isConj_iff.mpr ⟨x, rfl⟩)
  have hd1 := burnsideF42g_u5_det_of_conj hv hzy
  have hd2 := burnsideF42g_u5_det_of_conj hvz hzyt
  have hYvz : Yof (v * z₂SU h) = Yof v + !![0, 1; 1, 0] := by
    obtain ⟨-, Y, hY⟩ := hv
    apply Yof_eq
    rw [mat_mul, hY, z₂SU, mat_vSU, oddUni_mul, Yof_eq hY]
    congr 1
    · simp
    · ext i j
      simp [vecMulVec]
  rw [hYvz] at hd2
  rcases burnsideF42g_u5_herm_cases hω (herm_Yof hv) hd1 hd2 with e | e
  · left
    rw [← hvy]
    congr 1
    exact Yof_injOn h hv (vSU_mem_Vsub hU) (by rw [e, Yof_eq (mat_vSU hU)])
  · right
    rw [← hvy, hut]
    congr 1
    refine Yof_injOn h hv (vSU_mem_Vsub hUJ) ?_
    rw [e, Yof_eq (mat_vSU hUJ)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination -h2

end U5Model

section U5Main

set_option linter.unusedSectionVars false



open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF42g_A42_U5two (hyp : HypF_4_31 .U5 1 Gp M₁ M₂ β ε z) (_hL43 : ¬ IsL43 M)
    (hGp : Gp = ⊤) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .U5 Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  obtain ⟨K, fK, h, Ψ, h1, h2⟩ := burnsideF4m_U5_chart hyp.amalgam.toHypF_4_4g
  haveI : CharP K 2 := h.charP
  have hch2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hle : ∀ X : Subgroup E, Gp ⊓ X = X := fun X => inf_eq_right.2 (hGp ▸ le_top)
  set ψ : hypPSU h 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Gp.subtype_injective.comp Ψ.injective
  have hψs : Function.Surjective ψ := by
    intro e
    have he : e ∈ Gp := hGp ▸ Subgroup.mem_top e
    obtain ⟨y, hy⟩ := Ψ.surjective ⟨e, he⟩
    exact ⟨y, by rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hy]; rfl⟩
  set θ : hypPSU h 2 1 ≃* E := MulEquiv.ofBijective ψ ⟨hψ, hψs⟩ with hθdef
  have hθ : θ.toMonoidHom = ψ := rfl
  have hθinj : Function.Injective θ := θ.injective
  have hθ2 : M₂ = (u5LnP h).map θ.toMonoidHom := by rw [hθ, ← h2, hle]
  set U := hypProjUnitriangular h 2 1 with hUdef
  have hUP1 : U ≤ u5PtP h := Un.OL5.U_le_u5PtP h
  have hUP2 : U ≤ u5LnP h := Un.U_le_u5LnP
  have hUsyl : IsSylowTwoOf U (u5PtP h ⊓ u5LnP h) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right Un.isSylowTwoOf_U_u5LnP (le_inf hUP1 hUP2)
      inf_le_right
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtP h ⊓ u5LnP h).map ψ := by
    rw [Subgroup.map_inf _ _ _ hψ, ← h1, ← h2, inf_inf_distrib_left]
  have hUsylB : IsSylowTwoOf (U.map ψ) (Gp ⊓ (M₁ ⊓ M₂)) := by
    rw [hB]
    exact burnsideF4m_isSylowTwoOf_map_inj ψ hψ hUsyl
  obtain ⟨hSyl, -⟩ := burnsideF4j_sylow_data hyp.amalgam
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSsylB : IsSylowTwoOf (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (Gp ⊓ (M₁ ⊓ M₂)) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right hSyl hSB inf_le_left
  have hSU : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ U.map ψ :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hUsylB
  have hSeq : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = U.map θ.toMonoidHom :=
    (burnsideF4j_eq_of_sylow_le hSsylB hUsylB.2.1 hSU hUsylB.1).symm
  have hSeq' : pCoreOf 2 (M₁ ⊓ M₂) = U.map θ.toMonoidHom := by rw [← hSeq, hle]
  obtain ⟨ω, hω⟩ := burnsideF42g_u5_omega h
  have hω0 : ω ≠ 0 := fun e => by rw [e] at hω; simp at hω
  have hω1 : ω + 1 ≠ 0 := fun e => by
    have e' : ω = 1 := by linear_combination e - hch2
    rw [e'] at hω
    have : (1 : K) = 0 := by linear_combination hω - hch2
    exact one_ne_zero this
  have hbarω : h.bar ω = ω + 1 := by
    rw [h.bar_apply, pow_one, pow_two]
    linear_combination hω - (ω + 1) * hch2
  have hU : IsHerm h (!![1, ω + 1; ω, 1] : Matrix (Fin 2) (Fin 2) K) := by
    refine isHerm_iff.mpr ⟨by simp, by simp, ?_⟩
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [map_add, hbarω, map_one]
    linear_combination -hch2
  have hJ : IsHerm h (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := isHerm_swap h
  have hUJ := burnsideF42g_u5_isHerm_add hU hJ
  have hE₂ : IsHerm h (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) :=
    isHerm_iff.mpr ⟨by simp, by simp, by simp⟩
  have hE₁ : IsHerm h (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) := isHerm_e₁₁ h
  have hE₁₂ := burnsideF42g_u5_isHerm_add hE₁ hE₂
  have hE₁₂J := burnsideF42g_u5_isHerm_add hE₁₂ hJ
  have hπne : ∀ {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hY' : IsHerm h Y'), Y ≠ Y' →
      hypProj h 2 1 (vSU h Y hY) ≠ hypProj h 2 1 (vSU h Y' hY') := by
    intro Y Y' hY hY' hne e
    have e1 := Un.hypProj_eq_of_mem_U (vSU_mem_Vsub hY).1 (vSU_mem_Vsub hY').1 e
    apply hne
    rw [← Yof_eq (mat_vSU hY), e1, Yof_eq (mat_vSU hY')]
  have hθmul : ∀ {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hY' : IsHerm h Y'),
      θ (hypProj h 2 1 (vSU h Y hY)) * θ (hypProj h 2 1 (vSU h Y' hY')) =
        θ (hypProj h 2 1 (vSU h (Y + Y') (burnsideF42g_u5_isHerm_add hY hY'))) := by
    intro Y Y' hY hY'
    rw [← map_mul, ← map_mul, burnsideF42g_u5_vSU_mul]
  have hz5 : Un.z5Y h = hypProj h 2 1 (vSU h _ hE₁) := rfl
  have ht5 : Un.t5Y h = hypProj h 2 1 (vSU h _ hJ) := rfl
  have hCθ : Subgroup.centralizer ({θ (Un.t5Y h)} : Set E) =
      (Subgroup.centralizer ({Un.t5Y h} : Set (hypPSU h 2 1))).map θ.toMonoidHom :=
    burnsideF4gG2TwoInv_centralizer_map θ (Un.t5Y h)
  have hCθmem : ∀ c : hypPSU h 2 1, θ c ∈ Subgroup.centralizer ({θ (Un.t5Y h)} : Set E) ↔
      c * Un.t5Y h = Un.t5Y h * c := by
    intro c
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact ⟨fun e => hθinj e, fun e => by rw [e]⟩
  have hVC : ∀ {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y),
      θ (hypProj h 2 1 (vSU h Y hY)) ∈ Subgroup.centralizer ({θ (Un.t5Y h)} : Set E) :=
    fun hY => (hCθmem _).mpr (Un.v5Y_comm ⟨_, vSU_mem_Vsub hY, rfl⟩ Un.t5Y_mem_v5Y)
  have hVsq : ∀ {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y),
      θ (hypProj h 2 1 (vSU h Y hY)) * θ (hypProj h 2 1 (vSU h Y hY)) = 1 := fun hY => by
    rw [← map_mul, ← map_mul, Vsub_sq (vSU_mem_Vsub hY), map_one, map_one]
  have hne0 : ∀ {Y : Matrix (Fin 2) (Fin 2) K} (i j : Fin 2), Y i j ≠ 0 → Y ≠ 0 :=
    fun i j hij e => hij (by rw [e]; rfl)
  have hθconj : ∀ {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y), Y ≠ 0 → Y.det = 0 →
      IsConj (θ (Un.z5Y h)) (θ (hypProj h 2 1 (vSU h Y hY))) := fun hY hY0 hd =>
    (burnsideF4gG2TwoInv_isConj_map θ).mpr (burnsideF42g_u5_conj_z hY hY0 hd)
  refine burnsideF42g_A42_of_lemmaU (z₀ := θ (Un.z5Y h)) (tb := θ (Un.t5Y h))
    (u := θ (hypProj h 2 1 (vSU h _ hU))) (v₁ := θ (Un.z5Y h))
    (v₂ := θ (hypProj h 2 1 (vSU h _ hE₂))) hyp hGp (by decide)
    (fun i j hi hj hi1 hj1 hi2 hj2 =>
      burnsideF4r_A35_U5 hyp (by norm_num) i j hi hj hi1 hj1 hi2 hj2) ?_
    (fun e => Un.z5Y_ne_one (hθinj (by rw [e, map_one])))
    (by rw [← map_mul, Un.z5Y_sq, map_one]) ?_ ?_
    (fun e => Un.t5Y_ne_one (hθinj (by rw [e, map_one])))
    (by rw [← map_mul, Un.t5Y_sq, map_one]) ?_ ?_ ?_ (hVC hU) (hVsq hU)
    (hθconj hU (hne0 0 0 (by simp)) ?_) ?_
    ((hCθmem _).mpr Un.L5.comm_zt) (by rw [← map_mul, Un.z5Y_sq, map_one]) (IsConj.refl _) ?_
    (hVC hE₂) (hVsq hE₂) (hθconj hE₂ (hne0 1 1 (by simp)) (by simp [Matrix.det_fin_two])) ?_ ?_
  ·
    rw [hSeq', burnsideF4gG2TwoInv_ctr_map θ]
    exact ⟨_, burnsideF4gG2TwoInv_mem_ctr.2 ⟨Un.z5Y_mem_U, fun k hk => Un.L5.z5Y_cent hk⟩, rfl⟩
  ·
    rw [hle, hθ2, burnsideF4gG2TwoInv_pCoreOf_map θ]
    refine ⟨_, ?_, rfl⟩
    have := Un.t5Y_mem_v5Y (h := h)
    rw [Un.v5Y_eq_centerOf_pCoreOf] at this
    exact this.1
  ·
    rw [hSeq]
    exact ⟨_, Un.t5Y_mem_U, rfl⟩
  ·
    rw [burnsideF4gG2TwoInv_isConj_map θ]
    intro hc
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    exact Un.noconj_Y (MulAut.conj c) (by rw [MulAut.conj_apply]; exact hc)
  ·
    rw [hCθ, hθ2]
    exact Subgroup.map_mono Un.cent_t_Y
  ·
    rw [hSeq, hle, hCθ, ← Subgroup.map_inf _ _ _ hθinj]
    exact burnsideF4m_isSylowTwoOf_map_inj θ.toMonoidHom hθinj Un.L5.burnsideF4m_u5_sylow_t
  ·
    rw [Matrix.det_fin_two_of]
    linear_combination -hω + hch2
  ·
    intro x hx
    obtain ⟨x', rfl⟩ := θ.surjective x
    have hx' : x' ∈ Subgroup.centralizer ({Un.t5Y h} : Set (hypPSU h 2 1)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr ((hCθmem x').mp hx)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rcases burnsideF42g_u5_u_inv hω hU hx' with e | e
    · exact Or.inl (by rw [e])
    · exact Or.inr (by rw [e])
  ·
    rw [hz5, ht5, hθmul]
    exact ⟨fun e => hπne hE₁ hU (fun e' => hω1 (by
        have := congrFun (congrFun e' 0) 1; simpa using this.symm)) (hθinj e),
      fun e => hπne hE₁ hUJ (fun e' => hω0 (by
        have := congrFun (congrFun e' 0) 1
        simp at this
        linear_combination -this - hch2)) (hθinj e)⟩
  ·
    rw [ht5, hθmul]
    exact ⟨fun e => hπne hE₂ hU (fun e' => by
        have := congrFun (congrFun e' 0) 0; simp at this) (hθinj e),
      fun e => hπne hE₂ hUJ (fun e' => by
        have := congrFun (congrFun e' 0) 0; simp at this) (hθinj e)⟩
  ·
    right
    rw [hz5, ht5, hθmul, hθmul]
    refine hθconj _ (hne0 0 0 (by simp)) ?_
    rw [Matrix.det_fin_two]
    simp

end U5Main


end CFSG.ASVolI
