module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch12Sec5Cfg

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125Ir Matrix

namespace S125Beta

theorem fix2 : ∀ x : Fin 10 → ZMod 2,
    (∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat ((1 + Matrix.single 0 1 (1 : ZMod 2))) *ᵥ x) k = x k) →
    (∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat ((1 + Matrix.single 1 2 (1 : ZMod 2))) *ᵥ x) k = x k) →
    (∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat ((1 + Matrix.single 2 3 (1 : ZMod 2))) *ᵥ x) k = x k) →
    (∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat ((1 + Matrix.single 3 4 (1 : ZMod 2))) *ᵥ x) k = x k) →
    ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → x k = 0 := by
  decide +kernel

theorem wedge_t32 : JonesParshall.wedgeMat ((1 + Matrix.single 3 2 (1 : ZMod 2))) *ᵥ
    (Pi.single 1 1 : Fin 10 → ZMod 2) = Pi.single 1 1 + Pi.single 2 1 := by
  decide +kernel

theorem wedge_t42 : JonesParshall.wedgeMat ((1 + Matrix.single 4 2 (1 : ZMod 2))) *ᵥ
    (Pi.single 1 1 : Fin 10 → ZMod 2) = Pi.single 1 1 + Pi.single 3 1 := by
  decide +kernel

theorem wedge_t10_1 : JonesParshall.wedgeMat ((1 + Matrix.single 1 0 (1 : ZMod 2))) *ᵥ
    (Pi.single 1 1 : Fin 10 → ZMod 2) = Pi.single 1 1 + Pi.single 4 1 := by
  decide +kernel

theorem wedge_t10_2 : JonesParshall.wedgeMat ((1 + Matrix.single 1 0 (1 : ZMod 2))) *ᵥ
    (Pi.single 2 1 : Fin 10 → ZMod 2) = Pi.single 2 1 + Pi.single 5 1 := by
  decide +kernel

theorem wedge_t10_3 : JonesParshall.wedgeMat ((1 + Matrix.single 1 0 (1 : ZMod 2))) *ᵥ
    (Pi.single 3 1 : Fin 10 → ZMod 2) = Pi.single 3 1 + Pi.single 6 1 := by
  decide +kernel

theorem card_V7_filter : (Finset.univ.filter fun x : Fin 10 → ZMod 2 =>
    ∀ k ∉ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 10)), x k = 0).card = 128 := by
  decide +kernel

theorem wedge_t12 : ∀ a b : ZMod 2,
    JonesParshall.wedgeMat ((1 + Matrix.single 1 2 (1 : ZMod 2))) *ᵥ
      (Pi.single 0 a + Pi.single 1 b : Fin 10 → ZMod 2) =
        Pi.single 0 a + Pi.single 1 b + Pi.single 0 b := by
  decide +kernel

theorem stabGam_t32 : StabGam 2 (Matrix.SpecialLinearGroup.transvection
    (show (3 : Fin 5) ≠ 2 by decide) (1 : ZMod 2)) := by
  intro i j hj hi
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  fin_cases i <;> fin_cases j <;> simp_all

theorem stabGam_t42 : StabGam 2 (Matrix.SpecialLinearGroup.transvection
    (show (4 : Fin 5) ≠ 2 by decide) (1 : ZMod 2)) := by
  intro i j hj hi
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  fin_cases i <;> fin_cases j <;> simp_all

theorem stabGam_t10 : StabGam 2 (Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 5) ≠ 0 by decide) (1 : ZMod 2)) := by
  intro i j hj hi
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  fin_cases i <;> fin_cases j <;> simp_all

variable {G : Type} [Group G] [Finite G]

theorem exists_fix_mod {T V₁ Y : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (V₁ : Set G)) (hYT : Y ≤ T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hne : ¬ Y ≤ V₁) :
    ∃ z ∈ Y, z ∉ V₁ ∧ ∀ t ∈ T, z * t * z⁻¹ * t⁻¹ ∈ V₁ := by
  set N := Subgroup.normalizer (V₁ : Set G) with hN
  have hT2' : IsPGroup 2 (secImg N V₁ T) := isPGroup_secImg hTN hT2
  have : Group.IsNilpotent (secImg N V₁ T) := hT2'.isNilpotent
  have hYT' : secImg N V₁ Y ≤ secImg N V₁ T := secImg_mono hYT
  have hnorm : secImg N V₁ T ≤ Subgroup.normalizer (secImg N V₁ Y : Set _) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_secImg.1 hy
    exact secMk_mem_normalizer_secImg (hTY ht)
  have : ((secImg N V₁ Y).subgroupOf (secImg N V₁ T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  obtain ⟨v, hvY, hvV₁⟩ : ∃ v ∈ Y, v ∉ V₁ := by
    by_contra hcon
    push Not at hcon
    exact hne hcon
  have hvN : v ∈ N := hTN (hYT hvY)
  have hv_ne : secMk N V₁ ⟨v, hvN⟩ ≠ 1 := fun h1 => hvV₁ (secMk_eq_one_iff.1 h1)
  have hne' : (secImg N V₁ Y).subgroupOf (secImg N V₁ T) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨secMk N V₁ ⟨v, hvN⟩, hYT' (secMk_mem_secImg hvY)⟩ : ↥(secImg N V₁ T)) ∈
        (secImg N V₁ Y).subgroupOf (secImg N V₁ T) :=
      Subgroup.mem_subgroupOf.2 (secMk_mem_secImg hvY)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hv_ne (congrArg Subtype.val hmem)
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  obtain ⟨z, hzY, hz⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 w.2.1)
  refine ⟨z, hzY, ?_, fun t ht => ?_⟩
  · intro hzV₁
    apply hw
    have h1 : (w.1 : SecQuot N V₁) = 1 := by rw [← hz]; exact secMk_eq_one_iff.2 hzV₁
    exact Subtype.ext (Subtype.ext h1)
  · have hc := Subgroup.mem_center_iff.1 w.2.2 ⟨secMk N V₁ ⟨t, hTN ht⟩, secMk_mem_secImg ht⟩
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at this
    rw [← hz] at this
    exact commutator_mem_of_secMk_commute (x := z) (y := ⟨t, hTN ht⟩) this.symm

variable {T L V : Subgroup G}

omit [Finite G] in
theorem e_conj (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (x : ↥(L ⊔ T)) (v w : ↥V)
    (hw : (w : G) = x * v * (x : G)⁻¹) :
    Multiplicative.toAdd (F.e w) = JonesParshall.wedgeMat
      (S125Pm.phi F hLV hTV x : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (F.e v) := by
  have hw' : w = A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x v := Subtype.ext hw
  have h := F.wedge ⟨A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x, S125Pm.act_mem F hLV hTV x⟩ v
  rw [S125ZV.wedgeRep_apply] at h
  rw [hw']
  exact congrArg Multiplicative.toAdd h

@[expose] noncomputable def bvec (F : Frame125 T L V) (l : Fin 10) : ↥V :=
  F.e.symm (Multiplicative.ofAdd (Pi.single l 1))

omit [Finite G] in
theorem bvec_mem_of_step (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {Y : Subgroup G} {l l' : Fin 10}
    (hb : ((bvec F l : ↥V) : G) ∈ Y) (x : ↥(L ⊔ T))
    (hxY : (x : G) ∈ Subgroup.normalizer (Y : Set G))
    (hw : JonesParshall.wedgeMat (S125Pm.phi F hLV hTV x : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
      (Pi.single l 1 : Fin 10 → ZMod 2) = Pi.single l 1 + Pi.single l' 1) :
    ((bvec F l' : ↥V) : G) ∈ Y := by
  set b := bvec F l with hbdef
  have hxV : (x : G) ∈ Subgroup.normalizer (V : Set G) := sup_le hLV hTV x.2
  set w : ↥V := ⟨x * b * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hxV _).mp b.2⟩ with hwdef
  have hwY : (w : G) ∈ Y := (Subgroup.mem_normalizer_iff.mp hxY _).mp hb
  have hcw := e_conj F hLV hTV x b w rfl
  rw [hbdef, bvec, MulEquiv.apply_symm_apply, toAdd_ofAdd, hw] at hcw
  have he : bvec F l' = w * b⁻¹ := by
    apply F.e.injective
    rw [bvec, MulEquiv.apply_symm_apply, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_inv, hcw, hbdef, bvec, MulEquiv.apply_symm_apply,
      toAdd_ofAdd]
    abel
  rw [he]
  exact Y.mul_mem hwY (Y.inv_mem hb)

theorem le_V1_or_V7_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hMW : mi T L F.V1 ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ F.V1 ∨ F.V7 ≤ W := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hf.T_le
  by_cases hW : W ≤ F.V1
  · exact Or.inl hW
  right
  have hT2 : IsPGroup 2 T := hH.hyp.sylow.1
  have hTN : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right hTN
  have hVT : V ≤ T := S125.le_of_hyp1223 hH.hyp
  obtain ⟨z, hzW, hzV₁, hzT⟩ := exists_fix_mod hT2 hTN (hWV.trans hVT) (hTM.trans hMW) hW
  set v : ↥V := ⟨z, hWV hzW⟩ with hvdef
  set x := Multiplicative.toAdd (F.e v) with hxdef
  have hcond : ∀ τ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      τ ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 2) →
      ∀ k : Fin 10, k ≠ 0 →
        (JonesParshall.wedgeMat (τ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) k = x k := by
    intro τ hτ k hk
    obtain ⟨t, ht⟩ := S125Pm.phi_surjective F hLV hTV τ
    have htT : (t : G) ∈ T :=
      (S125Pm.mem_T_iff (hLV := hLV) (hTV := hTV) h1222 F hH t).2 (ht ▸ hτ)
    have h1 := hzT t htT
    have h2 : (t : G) * z * (t : G)⁻¹ * z⁻¹ ∈ F.V1 := by
      have := F.V1.inv_mem h1
      rwa [show (z * t * z⁻¹ * (t : G)⁻¹)⁻¹ = (t : G) * z * (t : G)⁻¹ * z⁻¹ by group] at this
    set w : ↥V := ⟨t * z * (t : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
      (sup_le hLV hTV t.2) z).mp v.2⟩ with hwdef
    have hcw := e_conj F hLV hTV t v w rfl
    rw [ht] at hcw
    have h3 : ((w * v⁻¹ : ↥V) : G) ∈ F.V1 := h2
    rw [show F.V1 = F.sub {0} from rfl, S125St.mem_sub_iff] at h3
    have h4 := h3 k (by simpa using hk)
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hcw] at h4
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact h4
  have hU : ∀ (i j : Fin 5) (h : i < j), Matrix.SpecialLinearGroup.transvection h.ne (1 : ZMod 2) ∈
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 2) := fun i j h =>
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transvection_mem_unitriangular h 1
  have hfix := fix2 x
    (by simpa [Matrix.SpecialLinearGroup.transvection_coe] using hcond _ (hU 0 1 (by decide)))
    (by simpa [Matrix.SpecialLinearGroup.transvection_coe] using hcond _ (hU 1 2 (by decide)))
    (by simpa [Matrix.SpecialLinearGroup.transvection_coe] using hcond _ (hU 2 3 (by decide)))
    (by simpa [Matrix.SpecialLinearGroup.transvection_coe] using hcond _ (hU 3 4 (by decide)))
  have hx : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
    funext k
    by_cases h0 : k = 0
    · subst h0
      simp
    by_cases h1 : k = 1
    · subst h1
      simp
    rw [hfix k h0 h1, Pi.add_apply, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, add_zero]
  have hx1 : x 1 = 1 := by
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (x 1) with h | h
    · exfalso
      apply hzV₁
      have : (v : G) ∈ F.sub {0} := by
        rw [S125St.mem_sub_iff]
        intro k hk
        by_cases h1 : k = 1
        · subst h1
          exact h
        · exact hfix k (by simpa using hk) h1
      exact this
    · exact h
  obtain ⟨a, ha⟩ : ∃ a, x 0 = a := ⟨_, rfl⟩
  have hxa : x = Pi.single 0 a + Pi.single 1 1 := by rw [← ha, ← hx1]; exact hx
  obtain ⟨t₁₂, ht₁₂⟩ := S125Pm.phi_surjective F hLV hTV
    (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 2 by decide) (1 : ZMod 2))
  have ht₁₂T : (t₁₂ : G) ∈ T :=
    (S125Pm.mem_T_iff (hLV := hLV) (hTV := hTV) h1222 F hH t₁₂).2
      (ht₁₂ ▸ hU 1 2 (by decide))
  have hb0 : ((bvec F 0 : ↥V) : G) ∈ W := by
    set w : ↥V := ⟨t₁₂ * z * (t₁₂ : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
      (sup_le hLV hTV t₁₂.2) z).mp v.2⟩ with hwdef
    have hwW : (w : G) ∈ W := (Subgroup.mem_normalizer_iff.mp (hMW (hTM ht₁₂T)) z).mp hzW
    have hcw := e_conj F hLV hTV t₁₂ v w rfl
    rw [ht₁₂, Matrix.SpecialLinearGroup.transvection_coe, ← hxdef, hxa, wedge_t12] at hcw
    have he : bvec F 0 = w * v⁻¹ := by
      apply F.e.injective
      rw [bvec, MulEquiv.apply_symm_apply, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, toAdd_mul, toAdd_inv, hcw, ← hxdef, hxa]
      abel
    rw [he]
    exact W.mul_mem hwW (W.inv_mem hzW)
  have hb1 : ((bvec F 1 : ↥V) : G) ∈ W := by
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) a with h | h
    · have he : bvec F 1 = v := by
        apply F.e.injective
        rw [bvec, MulEquiv.apply_symm_apply]
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, ← hxdef, hxa, h, Pi.single_zero, zero_add]
      rw [he]
      exact hzW
    · have he : bvec F 1 = v * bvec F 0 := by
        apply F.e.injective
        rw [bvec, bvec, MulEquiv.apply_symm_apply, map_mul, MulEquiv.apply_symm_apply]
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, ← hxdef, hxa, h]
        funext k
        simp only [Pi.add_apply]
        by_cases hk : k = 0
        · subst hk
          simp
          decide
        · simp [Pi.single_apply, hk]
      rw [he]
      exact W.mul_mem hzW hb0
  have hstep : ∀ {l l' : Fin 10} (τ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)),
      StabGam 2 τ → ((bvec F l : ↥V) : G) ∈ W →
      JonesParshall.wedgeMat (τ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        (Pi.single l 1 : Fin 10 → ZMod 2) = Pi.single l 1 + Pi.single l' 1 →
      ((bvec F l' : ↥V) : G) ∈ W := by
    intro l l' τ hτ hb hw
    obtain ⟨m, hm⟩ := S125Pm.phi_surjective F hLV hTV τ
    have hmM : (m : G) ∈ mi T L F.V1 :=
      (S125Pm.mem_mi_iff (hLV := hLV) (hTV := hTV) F m).2 (hm ▸ S125Tr.mem_stabK.2 hτ)
    refine bvec_mem_of_step F hLV hTV hb m (hMW hmM) ?_
    rw [hm]
    exact hw
  have hb2 := hstep _ stabGam_t32 hb1
    (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact wedge_t32)
  have hb3 := hstep _ stabGam_t42 hb1
    (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact wedge_t42)
  have hb4 := hstep _ stabGam_t10 hb1
    (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact wedge_t10_1)
  have hb5 := hstep _ stabGam_t10 hb2
    (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact wedge_t10_2)
  have hb6 := hstep _ stabGam_t10 hb3
    (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact wedge_t10_3)
  have hall : ∀ l ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 10)),
      ((bvec F l : ↥V) : G) ∈ W := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hb0
    · exact hb1
    · exact hb2
    · exact hb3
    · exact hb4
    · exact hb5
    · exact hb6
  have hle : coordOf F F.V7 ≤ coordOf F W := by
    rw [show F.V7 = F.sub {0, 1, 2, 3, 4, 5, 6} from rfl, coordOf_sub]
    exact coordSub_le fun l hl => mem_coordOf.2 (hall l hl)
  exact (coordOf_le_iff F (S125St.sub_le F _)).1 hle

omit [Finite G] in
theorem card_V7 (F : Frame125 T L V) : Nat.card F.V7 = 128 := by
  rw [← card_V7_filter, ← S125L9a.card_sub F {0, 1, 2, 3, 4, 5, 6}]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv.symm

theorem not_card_eq_sixteen (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hMW : mi T L F.V1 ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card W ≠ 16 := by
  intro h16
  rcases le_V1_or_V7_le h1222 F hH hWV hMW with h | h
  · have := Subgroup.card_le_of_le h
    rw [h16, S125L9a.card_V1 F] at this
    omega
  · have := Subgroup.card_le_of_le h
    rw [h16, card_V7 F] at this
    omega

omit [Finite G] in
theorem mem_pCoreOf_iff {K : Subgroup G} (x : ↥K) :
    (x : G) ∈ pCoreOf 2 K ↔ x ∈ CFSG.pCore 2 ↥K := CFSG.mem_openPCoreOf_iff x

theorem V_le_pCoreOf_of_beta {Q : Type} [Group Q]
    (hβ : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* Q) →
      ∀ S N D E : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → S125KG.Config63 S N D →
        E ≤ pCoreOf 2 N → N ≤ Subgroup.normalizer (E : Set X) → E = ⊥ ∨ Nat.card E = 64)
    (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (hPK : oTwoUpper F.P ≤ K₁)
    (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Q) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hc := S125Cfg.config63 h1222 F hH hK₁n hKG hLK hPK
  have hS := S125Cfg.isSylow_img h1222 F hH hK₁n hKG
  have hVK : V ≤ K₁ := (S125L8.V_le_l1 h1222 F hH).trans hLK
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 10) hf.card
  have hTN : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right hTN
  have hVM : V ≤ mi T L F.V1 := (S125.le_of_hyp1223 hH.hyp).trans hTM
  have hMV : mi T L F.V1 ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (sup_le hf.normalizes hf.T_le)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  set E := S125Cfg.img K₁ V with hE
  have hEN : E ≤ S125Cfg.img K₁ (mi T L F.V1) := S125Cfg.img_mono hVM
  have hNE : S125Cfg.img K₁ (mi T L F.V1) ≤ Subgroup.normalizer (E : Set _) := by
    rintro _ ⟨m, hm, rfl⟩
    apply S125St.mem_normalizer_of_conj_le
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨m * v * m⁻¹, ?_, by simp⟩
    show ((m : G) * v * (m : G)⁻¹) ∈ V
    exact (Subgroup.mem_normalizer_iff.mp (hMV hm) v).mp hv
  have hE2 : IsPGroup 2 ↥E :=
    (hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm).map π
  have hEO : E ≤ pCoreOf 2 (S125Cfg.img K₁ (mi T L F.V1)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEN hNE hE2
  set ρ : ↥V →* ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ := π.comp (Subgroup.inclusion hVK) with hρ
  have hrange : ρ.range = E := by
    rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range, hE, S125Cfg.img]
  have hkerc : Nat.card ρ.ker = Nat.card ↥(V ⊓ pCoreOf 2 K₁) := by
    refine Nat.card_congr
      ⟨fun x => ⟨(x : ↥V), ⟨(x : ↥V).2, ?_⟩⟩, fun y => ⟨⟨y, y.2.1⟩, ?_⟩, fun _ => rfl,
        fun _ => rfl⟩
    · have hx : π (Subgroup.inclusion hVK (x : ↥V)) = 1 := MonoidHom.mem_ker.1 x.2
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← mem_pCoreOf_iff] at hx
      exact hx
    · show π (Subgroup.inclusion hVK ⟨y, y.2.1⟩) = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← mem_pCoreOf_iff]
      exact y.2.2
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hrange, hkerc, hf.card] at hcard
  have hW : mi T L F.V1 ≤ Subgroup.normalizer ((V ⊓ pCoreOf 2 K₁ : Subgroup G) : Set G) :=
    fun m hm => Subgroup.inf_normalizer_le_normalizer_inf ⟨hMV hm,
      S125Fin.normalizer_le_normalizer_pCoreOf K₁
        (hK₁n ((inf_le_right : mi T L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G)) hm))⟩
  rcases hβ _ ⟨e⟩ _ _ _ E hS hc hEO hNE with hb | h64
  ·
    have hVO : V ≤ pCoreOf 2 K₁ := by
      intro v hv
      have h1 : π ⟨v, hVK hv⟩ ∈ E := ⟨⟨v, hVK hv⟩, hv, rfl⟩
      rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        ← mem_pCoreOf_iff] at h1
      exact h1
    exact hVO.trans (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hKG)
      (hK₁n.trans (S125Fin.normalizer_le_normalizer_pCoreOf K₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K₁))
  · exfalso
    rw [h64] at hcard
    exact not_card_eq_sixteen h1222 F hH inf_le_left hW (by omega)

end S125Beta

end CFSG.Quasithin.H13
