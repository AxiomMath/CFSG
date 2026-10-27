module

public import CFSG.Milestones.ASVolI.F429.bC8
public import CFSG.Milestones.ASVolI.F429.bC7F4
public import Certificates.Certificate7660

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem burnsideF429b_mem_oTwoRes_of_pow {P : Subgroup G} {g : G} (hg : g ∈ P) {m : ℕ}
    (hm : Odd m) (h : g ^ m = 1) : g ∈ oTwoRes P :=
  Subgroup.subset_closure ⟨hg, m, hm, h⟩

theorem burnsideF429b_mem_oTwoRes_of_two {P : Subgroup G} {g s : G} (hg : g ∈ P) (hs : s ∈ P)
    {m : ℕ} (hm : Odd m) (h1 : g ^ m = 1) (h2 : (g⁻¹ * s) ^ m = 1) : s ∈ oTwoRes P := by
  have e : s = g * (g⁻¹ * s) := by group
  rw [e]
  exact (oTwoRes P).mul_mem (burnsideF429b_mem_oTwoRes_of_pow hg hm h1)
    (burnsideF429b_mem_oTwoRes_of_pow (P.mul_mem (P.inv_mem hg) hs) hm h2)

theorem burnsideF429b_map_equiv_comp {N N' : Type} [Group N] [Group N'] (ψ : N →* G)
    (Φ : N ≃* N') (X : Subgroup N) :
    (X.map Φ.toMonoidHom).map (ψ.comp Φ.symm.toMonoidHom) = X.map ψ := by
  have e : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id N := by
    ext x
    simp
  rw [Subgroup.map_map, MonoidHom.comp_assoc, e, MonoidHom.comp_id]

end Generic

section TitsD

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits


theorem burnsideF429b_mem_titsWordGroup {ws : List (List ℤ)} {w : List ℤ} (hw : w ∈ ws) :
    wordIn 13 titsT w ∈ titsWordGroup ws :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem burnsideF429b_tits_three {sW gW : List ℤ} (hs : lettersOK 13 sW = true)
    (hg : lettersOK 13 gW = true)
    (h : (let g := wordArr 1755 titsDerivedArrs gW
      let h := compA 1755 (invCand 1755 g) (wordArr 1755 titsDerivedArrs sW)
      isInvA 1755 g (invCand 1755 g) && eqA 1755 (compA 1755 g (compA 1755 g g)) (idA 1755) &&
        eqA 1755 (compA 1755 h (compA 1755 h h)) (idA 1755)) = true) :
    wordIn 13 titsT gW ^ 3 = 1 ∧ ((wordIn 13 titsT gW)⁻¹ * wordIn 13 titsT sW) ^ 3 = 1 := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hinv, hg3⟩, hh3⟩ := h
  have hA := rep_wordArr_titsT hg
  have hB := rep_compA (rep_inv_of_isInvA hA hinv) (rep_wordArr_titsT hs)
  refine ⟨?_, ?_⟩
  · rw [pow_three]
    exact eq_of_eqA (rep_compA hA (rep_compA hA hA)) rep_idA hg3
  · rw [pow_three]
    exact eq_of_eqA (rep_compA hB (rep_compA hB hB)) rep_idA hh3

theorem burnsideF429b_tits_five {sW gW : List ℤ} (hs : lettersOK 13 sW = true)
    (hg : lettersOK 13 gW = true)
    (h : (let g := wordArr 1755 titsDerivedArrs gW
      let h := compA 1755 (invCand 1755 g) (wordArr 1755 titsDerivedArrs sW)
      isInvA 1755 g (invCand 1755 g) &&
        eqA 1755 (compA 1755 g (compA 1755 g (compA 1755 g (compA 1755 g g)))) (idA 1755) &&
        eqA 1755 (compA 1755 h (compA 1755 h (compA 1755 h (compA 1755 h h)))) (idA 1755)) =
          true) :
    wordIn 13 titsT gW ^ 5 = 1 ∧ ((wordIn 13 titsT gW)⁻¹ * wordIn 13 titsT sW) ^ 5 = 1 := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hinv, hg5⟩, hh5⟩ := h
  have hA := rep_wordArr_titsT hg
  have hB := rep_compA (rep_inv_of_isInvA hA hinv) (rep_wordArr_titsT hs)
  have e : ∀ x : Equiv.Perm (Fin 1755), x ^ 5 = x * (x * (x * (x * x))) := fun x => by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact eq_of_eqA (rep_compA hA (rep_compA hA (rep_compA hA (rep_compA hA hA)))) rep_idA hg5
  · rw [e]
    exact eq_of_eqA (rep_compA hB (rep_compA hB (rep_compA hB (rep_compA hB hB)))) rep_idA hh5

theorem burnsideF429b_titsS_le :
    titsS ≤ (titsS ⊓ oTwoRes titsH) ⊔ (titsS ⊓ oTwoRes titsN) := by
  obtain ⟨h12, h3⟩ := (Certificates.certificate7660)
  have hall := List.all_eq_true.1 h12
  have hN : ∀ w ∈ titsNWords, wordIn 13 titsT w ∈ titsN := fun w hw =>
    burnsideF429b_mem_titsWordGroup hw
  have hH : ∀ w ∈ titsHWords, wordIn 13 titsT w ∈ titsH := fun w hw =>
    burnsideF429b_mem_titsWordGroup hw
  have hS : ∀ w ∈ titsSWords, wordIn 13 titsT w ∈ titsS := fun w hw =>
    burnsideF429b_mem_titsWordGroup hw
  show titsWordGroup titsSWords ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  have hwS := hS w hw
  have hw' : w = [13] ∨ w = [-4, -4] ∨ w = [-4, 3, 3] := by simpa [titsSWords] using hw
  rcases hw' with rfl | rfl | rfl
  · refine Subgroup.mem_sup_right ⟨hwS, ?_⟩
    obtain ⟨h1, h2⟩ := burnsideF429b_tits_three (sW := [13])
      (gW := [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4]) (by decide) (by decide)
      (hall ([13], [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4]) (by simp))
    have hg : wordIn 13 titsT [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4] ∈ titsN := by
      have e : ([2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4] : List ℤ) =
          [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] ++ [-4, 3, 3] ++ [-4, -4] := rfl
      rw [e, wordIn_append, wordIn_append]
      exact titsN.mul_mem (titsN.mul_mem (hN _ (by simp [titsNWords])) (hN _ (by simp [titsNWords])))
        (hN _ (by simp [titsNWords]))
    exact burnsideF429b_mem_oTwoRes_of_two hg (titsS_le_titsN hwS) ⟨1, by norm_num⟩ h1 h2
  · refine Subgroup.mem_sup_right ⟨hwS, ?_⟩
    obtain ⟨h1, h2⟩ := burnsideF429b_tits_three (sW := [-4, -4])
      (gW := [-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]) (by decide) (by decide)
      (hall ([-4, -4], [-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]) (by simp))
    have hg : wordIn 13 titsT [-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] ∈ titsN := by
      have e : ([-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] : List ℤ) =
          [-4, 3, 3] ++ [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] := rfl
      rw [e, wordIn_append]
      exact titsN.mul_mem (hN _ (by simp [titsNWords])) (hN _ (by simp [titsNWords]))
    exact burnsideF429b_mem_oTwoRes_of_two hg (titsS_le_titsN hwS) ⟨1, by norm_num⟩ h1 h2
  · refine Subgroup.mem_sup_left ⟨hwS, ?_⟩
    obtain ⟨h1, h2⟩ := burnsideF429b_tits_five (sW := [-4, 3, 3]) (gW := [13, 13, 4])
      (by decide) (by decide) h3
    have hg : wordIn 13 titsT [13, 13, 4] ∈ titsH := by
      have e : ([13, 13, 4] : List ℤ) = [13] ++ [13] ++ [4] := rfl
      rw [e, wordIn_append, wordIn_append]
      exact titsH.mul_mem (titsH.mul_mem (hH _ (by simp [titsHWords])) (hH _ (by simp [titsHWords])))
        (hH _ (by simp [titsHWords]))
    exact burnsideF429b_mem_oTwoRes_of_two hg (titsS_le_titsH hwS) ⟨2, by norm_num⟩ h1 h2

end TitsD

section TwoF4Model

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin.H13.F431.TwoF4


theorem burnsideF429b_twoF4_model :
    twoF4TT ⊓ oTwoRes ⊤ ≤ (twoF4TT ⊓ oTwoRes twoF4M1) ⊔ (twoF4TT ⊓ oTwoRes twoF4M2) ∧
      (twoF4TT ⊓ oTwoRes ⊤).relIndex twoF4TT ∣ 2 := by
  have hι : Function.Injective twoF4M.subtype := twoF4M.subtype_injective
  have hHM : twoF4H ≤ twoF4M := twoF4H_le_twoF4M
  have hNM : twoF4N ≤ twoF4M := extSub_mono titsN_le_titsD
  have hSM : twoF4S ≤ twoF4M := twoF4S_le_twoF4M
  have hmapX : (titsS ⊓ oTwoRes titsH) ⊔ (titsS ⊓ oTwoRes titsN) ≤
      ((twoF4TT ⊓ oTwoRes twoF4M1) ⊔ (twoF4TT ⊓ oTwoRes twoF4M2)).map twoF4M.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ hι, Subgroup.map_inf _ _ _ hι,
      ← burnsideF429b_oTwoRes_map _ hι, ← burnsideF429b_oTwoRes_map _ hι]
    unfold twoF4TT twoF4M1 twoF4M2
    rw [Subgroup.map_subgroupOf_eq_of_le hSM, Subgroup.map_subgroupOf_eq_of_le hHM,
      Subgroup.map_subgroupOf_eq_of_le hNM]
    exact sup_le_sup (inf_le_inf le_extSub (burnsideF429b_oTwoRes_mono le_extSub))
      (inf_le_inf le_extSub (burnsideF429b_oTwoRes_mono le_extSub))
  have hSX : titsS.subgroupOf twoF4M ≤
      (twoF4TT ⊓ oTwoRes twoF4M1) ⊔ (twoF4TT ⊓ oTwoRes twoF4M2) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hmapX (burnsideF429b_titsS_le (Subgroup.mem_subgroupOf.1 hx))
    rwa [← hι hyx]
  have hO : oTwoRes (⊤ : Subgroup ↥twoF4M) ≤ titsD.subgroupOf twoF4M :=
    burnsideF429b_oTwoRes_le_of_index_two index_titsD_twoF4M ⊤
  have hSD : twoF4TT ⊓ titsD.subgroupOf twoF4M ≤ titsS.subgroupOf twoF4M := by
    rintro x ⟨hxS, hxD⟩
    exact Subgroup.mem_subgroupOf.2 (mem_of_mem_extSub_of_mem_D titsS_le_titsD
      (Subgroup.mem_subgroupOf.1 hxS) (Subgroup.mem_subgroupOf.1 hxD))
  refine ⟨(inf_le_inf_left _ hO).trans (hSD.trans hSX), ?_⟩
  have hXT : (twoF4TT ⊓ oTwoRes twoF4M1) ⊔ (twoF4TT ⊓ oTwoRes twoF4M2) ≤
      twoF4TT ⊓ oTwoRes ⊤ :=
    sup_le (inf_le_inf_left _ (burnsideF429b_oTwoRes_mono le_top))
      (inf_le_inf_left _ (burnsideF429b_oTwoRes_mono le_top))
  refine (Subgroup.relIndex_dvd_of_le_left _ (hSX.trans hXT)).trans ?_
  have h2 : titsS.relIndex twoF4S = 2 :=
    relIndex_extSub (fun h => tπ_not_mem_D (titsS_le_titsD h))
  unfold twoF4TT
  rw [Subgroup.relIndex_subgroupOf hSM, h2]

end TwoF4Model

section F4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Sporadic.Schreier.Tits


theorem burnsideF429b_F4_chart_two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .F4tw 2 1 Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime),
      Nat.card K = 2 ^ (2 * 0 + 1) ∧
      ∃ Ψ : Gm K 0 ≃* ↥Gp,
        M₁.subgroupOf Gp = (Pg K 0 ⟨1, by decide⟩).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (Pg K 0 ⟨0, by decide⟩).map Ψ.toMonoidHom := by
  obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, h1, h2⟩ := burnsideF4g_chart_F4tw h
  have ha : a = 0 := by omega
  subst ha
  letI := fK
  haveI := finK
  have hK : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨Φ, hΦ⟩ := burnsideF429b_F4_exists_iso hK marking
  refine ⟨K, fK, finK, inferInstance, hK, Φ, h1.trans (hΦ _ _ fun y => ?_),
    h2.trans (hΦ _ _ fun y => ?_)⟩
  · rw [burnsideF4gF4Inv_reeParabolic_one_eq]
    exact Subgroup.mem_subgroupOf
  · rw [burnsideF4gF4Inv_reeParabolic_zero_eq]
    exact Subgroup.mem_subgroupOf

theorem burnsideF429b_c8sbar_F4two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 1 Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp ≤
        ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) ∧
      (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).relIndex (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∣ 2 := by
  obtain ⟨K, fK, finK, cK, hKa, Ψ, h1, h2⟩ := burnsideF429b_F4_chart_two hyp.toHypF_4_4g
  have hK : Nat.card K = 2 := by simpa using hKa
  obtain ⟨Φ, -, hP1, hP2⟩ := burnsideF4gF4TwoInv_gamma hK hKa
  have e1 : Pg K 0 ⟨1, by decide⟩ = (burnsideF4gF4Two_system hK).P₁ := by
    ext y
    rw [burnsideF4gF4Two_mem_P₁_iff hK y, burnsideF4gF4Inv_reeParabolic_one_eq]
    exact Subgroup.mem_subgroupOf
  have e0 : Pg K 0 ⟨0, by decide⟩ = (burnsideF4gF4Two_system hK).P₂ := by
    ext y
    rw [burnsideF4gF4Two_mem_P₂_iff hK y, burnsideF4gF4Inv_reeParabolic_zero_eq]
    exact Subgroup.mem_subgroupOf
  have hL := twoF4_F431LieI
  have hMT : twoF4M1 ⊓ twoF4M2 = twoF4TT :=
    le_antisymm burnsideF4gF4TwoInv_twoF4_inf (le_inf hL.T_le₁ hL.T_le₂)
  have hφ : Function.Injective
      ((Gp.subtype.comp Ψ.toMonoidHom).comp Φ.symm.toMonoidHom) :=
    (Gp.subtype_injective.comp Ψ.injective).comp Φ.symm.injective
  have hG : Gp = (⊤ : Subgroup ↥twoF4M).map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp Φ.symm.toMonoidHom) := by
    rw [← Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective,
      burnsideF429b_map_equiv_comp, ← Subgroup.map_map,
      Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hM1 : Gp ⊓ M₁ = twoF4M1.map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp Φ.symm.toMonoidHom) := by
    rw [burnsideF429_inf_eq_map Ψ h1, ← hP1, ← e1, burnsideF429b_map_equiv_comp]
  have hM2 : Gp ⊓ M₂ = twoF4M2.map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp Φ.symm.toMonoidHom) := by
    rw [burnsideF429_inf_eq_map Ψ h2, ← hP2, ← e0, burnsideF429b_map_equiv_comp]
  have hM12 : Gp ⊓ (M₁ ⊓ M₂) = twoF4TT.map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp Φ.symm.toMonoidHom) := by
    rw [burnsideF429_inf_eq_map Ψ (burnsideF429b_inf_subgroupOf Ψ h1 h2), ← hMT, ← hP1, ← hP2,
      ← Subgroup.map_inf _ _ _ Φ.injective, ← e1, ← e0, burnsideF429b_map_equiv_comp]
  obtain ⟨ha, hb⟩ := burnsideF429b_twoF4_model
  exact burnsideF429b_c8sbar_of_inj _ hφ hG hM1 hM2 hM12 hL.sylow.2.1 ha hb

end F4Two

end CFSG.ASVolI
