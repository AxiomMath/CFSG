module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Sylow
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private noncomputable def s16k_vecEquiv (M : S16kGL6) :
    Multiplicative (Fin 6 → ZMod 2) ≃* Multiplicative (Fin 6 → ZMod 2) :=
  (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.toAddEquiv.toMultiplicative

private theorem s16k_vecEquiv_toAdd (M : S16kGL6) (v : Multiplicative (Fin 6 → ZMod 2)) :
    Multiplicative.toAdd (s16k_vecEquiv M v) =
      (M : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd v) := by
  have h1 : Multiplicative.toAdd (s16k_vecEquiv M v) =
      (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv (Multiplicative.toAdd v) := rfl
  rw [h1, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

private theorem s16k_pRank_map_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (e : X ≃* Y) (H : Subgroup X) :
    CFSG.Open.pRank p H = CFSG.Open.pRank p (H.map e.toMonoidHom) := by
  refine le_antisymm (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective H) ?_
  have h := CFSG.SectionRank.pRank_le_map hp.one_lt e.symm.toMonoidHom e.symm.injective
    (H.map e.toMonoidHom)
  rw [Subgroup.map_map,
    show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X from by ext x; simp,
    Subgroup.map_id] at h
  exact h

private theorem s16k_card_le_pow_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {E K : Subgroup X} (hEK : E ≤ K) (hE : IsElemAbelian p E) :
    Nat.card ↥E ≤ p ^ CFSG.Open.pRank p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE.isPGroup
  have hk_le : k ≤ CFSG.Open.pRank p K := CFSG.SectionRank.le_pRank hp.one_lt hEK hE hk
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk_le

private theorem s16k_cTilde_mono {A M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAM : A ≤ M) (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    F11.CTilde A V₀ V ≤ F11.CTilde M V₀ V := by
  intro g hg
  rw [mem_cTilde_iff (M := M) hV hM]
  rw [mem_cTilde_iff (M := A) hV (hAM.trans hM)] at hg
  exact ⟨hAM hg.1, hg.2⟩

private theorem s16k_z3_model_data (h : S16kBase D V₀ V L hV)
    (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6) :
    ∃ (e : Vtil V₀ V hV ≃* Multiplicative (Fin 6 → ZMod 2))
      (φ : MulAut (Vtil V₀ V hV) ≃* S16kGL6),
      (∀ (g : MulAut (Vtil V₀ V hV)) (w : Vtil V₀ V hV), Multiplicative.toAdd (e (g w)) =
        ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (Multiplicative.toAdd (e w))) ∧
      (lBar V₀ V hV L).map φ.toMonoidHom = s16kScal ∧
      (Mbar D.M V₀ V hV).map φ.toMonoidHom ≤
        Subgroup.normalizer (s16kScal : Set S16kGL6) := by
  classical
  have hW : ∀ x : Vtil V₀ V hV, x ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top (T := Vtil V₀ V hV) hW, hrk]
  have hfpf : ∀ l ∈ lBar V₀ V hV L, ∀ x : Vtil V₀ V hV, l x = x → l = 1 ∨ x = 1 := by
    intro l hl x hlx
    by_cases hl1 : l = 1
    · exact Or.inl hl1
    · right
      have hfix : fixV (lBar V₀ V hV L) = ⊥ := by
        have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by rw [hZ.2]; norm_num
        have hb := CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hodd
          (Y := lBar V₀ V hV L)
        rw [h.comm_top, inf_top_eq] at hb
        exact hb
      have hzpl : Subgroup.zpowers l = lBar V₀ V hV L := by
        have hle : Subgroup.zpowers l ≤ lBar V₀ V hV L := Subgroup.zpowers_le.mpr hl
        have hne : Subgroup.zpowers l ≠ ⊥ := by
          intro hbot
          exact hl1 (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_zpowers l))
        have hdvd : Nat.card ↥(Subgroup.zpowers l) ∣ Nat.card ↥(lBar V₀ V hV L) :=
          Subgroup.card_dvd_of_le hle
        rw [hZ.2] at hdvd
        have hne1 : Nat.card ↥(Subgroup.zpowers l) ≠ 1 := fun h1 =>
          hne (Subgroup.eq_bot_of_card_eq (Subgroup.zpowers l) h1)
        have hcard3 : Nat.card ↥(Subgroup.zpowers l) = 3 := by
          rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three
            (Nat.card ↥(Subgroup.zpowers l)) hdvd with h1 | h3
          · exact absurd h1 hne1
          · exact h3
        exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ.2, hcard3])
      have hxmem : x ∈ fixV (Subgroup.zpowers l) := (mem_fixV_zpowers l x).2 hlx
      rw [hzpl, hfix] at hxmem
      exact Subgroup.mem_bot.1 hxmem
  obtain ⟨e, φ, hmul, hφL⟩ := s16k_z3_model (W := Vtil V₀ V hV) hW hcard hZ hfpf
  refine ⟨e, φ, hmul, hφL, ?_⟩
  calc (Mbar D.M V₀ V hV).map φ.toMonoidHom
      ≤ (Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).map
          φ.toMonoidHom := Subgroup.map_mono h.mBar_le_normalizer
    _ = Subgroup.normalizer ((lBar V₀ V hV L).map φ.toMonoidHom) :=
        Subgroup.map_equiv_normalizer_eq _ φ
    _ = Subgroup.normalizer (s16kScal : Set S16kGL6) := by rw [hφL]

theorem s16k_z3_three_mem_sig (h : S16kBase D V₀ V L hV)
    (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6) : 3 ∈ D.sig := by
  obtain ⟨e₀, φ₀, -, -, hN⟩ := s16k_z3_model_data h hZ hrk
  obtain ⟨p, hpσ⟩ := h.exists_sig
  have hpp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have h3p : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := h.three_le_pRank hpσ
  have heq : CFSG.Open.pRank p (Mbar D.M V₀ V hV) =
      CFSG.Open.pRank p ((Mbar D.M V₀ V hV).map φ₀.toMonoidHom) :=
    s16k_pRank_map_mulEquiv hpp φ₀ _
  have hle : CFSG.Open.pRank p ((Mbar D.M V₀ V hV).map φ₀.toMonoidHom) ≤
      if p = 3 then 3 else 1 := s16k_z3_pRank_le hN hpp hp2
  have hp3 : p = 3 := by
    by_contra hne
    rw [if_neg hne, ← heq] at hle
    omega
  rw [← hp3]
  exact hpσ

theorem s16k_z3_image_torus (h : S16kBase D V₀ V L hV)
    (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6) {A : Subgroup G} (hAM : A ≤ D.M)
    (hA : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4) :
    CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 3 ∧
      ∃ (e : Vtil V₀ V hV ≃* Multiplicative (Fin 6 → ZMod 2))
        (φ : MulAut (Vtil V₀ V hV) ≃* S16kGL6),
        (∀ (g : MulAut (Vtil V₀ V hV)) (w : Vtil V₀ V hV), Multiplicative.toAdd (e (g w)) =
          ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (Multiplicative.toAdd (e w))) ∧
        (lBar V₀ V hV L).map φ.toMonoidHom = s16kScal ∧
        (Mbar D.M V₀ V hV).map φ.toMonoidHom ≤ Subgroup.normalizer (s16kScal : Set S16kGL6) ∧
        (barSub V₀ V hV A).map φ.toMonoidHom = s16kDiag := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₀, φ₀, hmul, hφ₀L, hN⟩ := s16k_z3_model_data h hZ hrk
  have hMbar_le : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 3 := by
    rw [s16k_pRank_map_mulEquiv Nat.prime_three φ₀ (Mbar D.M V₀ V hV)]
    have hle := s16k_z3_pRank_le hN Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2)
    simpa using hle
  refine ⟨hMbar_le, ?_⟩
  have hAstab : A ≤ stabTil V₀ V := hAM.trans (s16g_le_stabTil h.setting)
  have hAnorm : A ≤ Subgroup.normalizer (V : Set G) := hAstab.trans (stabTil_le_normalizer V₀ V)
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) :=
    (s16g_le_stabTil h.setting).trans (stabTil_le_normalizer V₀ V)
  let φbar : ↥A →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hAstab
  have hker_eq : φbar.ker = (F11.CTilde A V₀ V).subgroupOf A :=
    ker_barHom V₀ V hV hAnorm hAstab
  have hrange_eq : φbar.range = barSub V₀ V hV A := range_barHom V₀ V hV hAstab
  have hAbar_el : IsElemAbelian 3 (barSub V₀ V hV A) := by
    have hel := (hA.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
    simpa only [barSub] using hel
  have hAbar_le : barSub V₀ V hV A ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hAM
  have h115 : CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h.std.h61
      (Hyp125.hyp11 h.std.h127 h.setting.hyp16.hyp125)
      (c23_card_v0_le_four D h.setting.hyp16) (s16k_z3_three_mem_sig h hZ hrk)
  have hCTle : F11.CTilde A V₀ V ≤ F11.CTilde D.M V₀ V := s16k_cTilde_mono hV hAM hMnorm
  have hCTel : IsElemAbelian 3 (F11.CTilde A V₀ V) :=
    hA.mono (WeakClosure81.cTilde_le_M A V₀ V)
  have hker_card : Nat.card ↥(φbar.ker) ≤ 3 := by
    rw [hker_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (WeakClosure81.cTilde_le_M A V₀ V)).toEquiv]
    calc Nat.card ↥(F11.CTilde A V₀ V)
        ≤ 3 ^ CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) :=
          s16k_card_le_pow_pRank Nat.prime_three hCTle hCTel
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h115
      _ = 3 := by norm_num
  have hAbar_ub : Nat.card ↥(barSub V₀ V hV A) ≤ 27 :=
    calc Nat.card ↥(barSub V₀ V hV A)
        ≤ 3 ^ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) :=
          s16k_card_le_pow_pRank Nat.prime_three hAbar_le hAbar_el
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hMbar_le
      _ = 27 := by norm_num
  have hprod : Nat.card ↥(φbar.ker) * Nat.card ↥(φbar.range) = 3 ^ 4 := by
    simpa only [hA4] using Subgroup.card_ker_mul_card_range φbar
  have hAbar_lb : 27 ≤ Nat.card ↥(barSub V₀ V hV A) := by
    rw [← hrange_eq]
    have h1 : 3 ^ 4 ≤ 3 * Nat.card ↥(φbar.range) := by
      calc 3 ^ 4 = Nat.card ↥(φbar.ker) * Nat.card ↥(φbar.range) := hprod.symm
        _ ≤ 3 * Nat.card ↥(φbar.range) := Nat.mul_le_mul_right _ hker_card
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num] at h1
    omega
  have hAbar_card : Nat.card ↥(barSub V₀ V hV A) = 27 := le_antisymm hAbar_ub hAbar_lb
  have hE_le : (barSub V₀ V hV A).map φ₀.toMonoidHom ≤
      Subgroup.normalizer (s16kScal : Set S16kGL6) := (Subgroup.map_mono hAbar_le).trans hN
  have hE_el : IsElemAbelian 3 ((barSub V₀ V hV A).map φ₀.toMonoidHom) :=
    hAbar_el.map φ₀.toMonoidHom
  have hE_card : Nat.card ↥((barSub V₀ V hV A).map φ₀.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (K := barSub V₀ V hV A) (f := φ₀.toMonoidHom) φ₀.injective,
      hAbar_card]
    norm_num
  obtain ⟨n, hnN, hnE⟩ := s16k_z3_e27_conj hE_le hE_el hE_card
  let m : S16kGL6 := n⁻¹
  let φ : MulAut (Vtil V₀ V hV) ≃* S16kGL6 := φ₀.trans (MulAut.conj m)
  let e : Vtil V₀ V hV ≃* Multiplicative (Fin 6 → ZMod 2) := e₀.trans (s16k_vecEquiv m)
  have hmN : m ∈ Subgroup.normalizer (s16kScal : Set S16kGL6) := by
    show n⁻¹ ∈ _
    exact Subgroup.inv_mem _ hnN
  have hcomp : φ.toMonoidHom = ((MulAut.conj m).toMonoidHom).comp φ₀.toMonoidHom := by
    ext g
    rfl
  have hφL : (lBar V₀ V hV L).map φ.toMonoidHom = s16kScal := by
    rw [hcomp, ← Subgroup.map_map, hφ₀L]
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := s16kScal) (g := m)).1 hmN
  refine ⟨e, φ, ?_, hφL, ?_, ?_⟩
  · intro g w
    have hgw : Multiplicative.toAdd (e (g w)) =
        (m : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (Multiplicative.toAdd (e₀ (g w))) := by
      rw [show e (g w) = s16k_vecEquiv m (e₀ (g w)) from rfl, s16k_vecEquiv_toAdd]
    have hw : Multiplicative.toAdd (e w) =
        (m : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (Multiplicative.toAdd (e₀ w)) := by
      rw [show e w = s16k_vecEquiv m (e₀ w) from rfl, s16k_vecEquiv_toAdd]
    rw [hgw, hw, hmul g w]
    have hmat : (↑(MulAut.conj m (φ₀ g)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        (m : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (m : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          (φ₀ g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      have hGL : MulAut.conj m (φ₀ g) * m = m * φ₀ g := by
        rw [MulAut.conj_apply]
        group
      simpa only [Matrix.GeneralLinearGroup.coe_mul] using
        congrArg (fun x : S16kGL6 => (x : Matrix (Fin 6) (Fin 6) (ZMod 2))) hGL
    calc (m : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            ((φ₀ g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
              (Multiplicative.toAdd (e₀ w)))
        = ((m : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
            (φ₀ g : Matrix (Fin 6) (Fin 6) (ZMod 2))).mulVec
              (Multiplicative.toAdd (e₀ w)) :=
          Matrix.mulVec_mulVec _ _ _
      _ = ((↑(MulAut.conj m (φ₀ g)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
            (m : Matrix (Fin 6) (Fin 6) (ZMod 2))).mulVec
              (Multiplicative.toAdd (e₀ w)) := by
          rw [← hmat]
      _ = (↑(MulAut.conj m (φ₀ g)) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            ((m : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
              (Multiplicative.toAdd (e₀ w))) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = (φ g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            ((m : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
              (Multiplicative.toAdd (e₀ w))) := rfl
  · calc (Mbar D.M V₀ V hV).map φ.toMonoidHom
        ≤ (Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).map
            φ.toMonoidHom := Subgroup.map_mono h.mBar_le_normalizer
      _ = Subgroup.normalizer ((lBar V₀ V hV L).map φ.toMonoidHom) :=
          Subgroup.map_equiv_normalizer_eq _ φ
      _ = Subgroup.normalizer (s16kScal : Set S16kGL6) := by rw [hφL]
  · rw [hcomp, ← Subgroup.map_map, hnE, Subgroup.map_map]
    rw [show ((MulAut.conj m).toMonoidHom).comp ((MulAut.conj n).toMonoidHom) =
        MonoidHom.id S16kGL6 from by
      apply MonoidHom.ext
      intro g
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulAut.conj_apply]
      show n⁻¹ * (n * g * n⁻¹) * n = g
      group,
      Subgroup.map_id]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
