module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V0Loc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_normalizer_le_of_local {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p ∈ D.sig)
    (Itil : Subgroup (Vtil V₀ V hV))
    (hIT : ∀ φ ∈ barSub V₀ V hV D.T, Itil.map φ.toMonoidHom = Itil)
    (hI3 : ∀ w ∈ Itil, w ≠ 1 → ∃ y ∈ Mbar D.M V₀ V hV, orderOf y = p ∧ y w = w)
    (hMod : ∀ E : Subgroup (MulAut (Vtil V₀ V hV)), E ≤ barSub V₀ V hV D.T → IsElemAbelian2 E →
      E ≠ ⊥ → ∃ B ≤ E, E3.mQuot E B = 1 ∧ ∃ u : Vtil V₀ V hV, (∀ b ∈ B, b u = u) ∧
        (∃ e ∈ E, e u ≠ u) ∧ ∀ e ∈ E, e u * u⁻¹ ∈ Itil) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  have h16 : Hyp16 D V₀ V := hc.setting.hyp16
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hP := h125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hk1 : 1 ≤ D.k := TwelveShort.one_le_k D
  have hm1 : 1 < mBar D.M V₀ V hV := s16t_one_lt_mBar_of_three D h.h1217 h.h153 hc
  have hm : MBarGT D.M V₀ V 1 := (h125.mBarGT_iff_lt_mBar 1).2 hm1
  have hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hk1 _)
      (s16n9b_k_add_lt_rMV D h.hSg (h.h1219 V₀ V h125) h.hx h.h61 h.h127 h16)
  have hγ : V₀ = ⊥ ∨ ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V := by
    by_cases h0 : V₀ = ⊥
    · exact Or.inl h0
    · exact Or.inr (s16c11_one_add_lt_gammaN_one hk1
        (s16n9b_main_gamma D h.hSg (h.h1219 V₀ V h125) h.h1217 hV hc h0))
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    h.hSg.sig1_sp p (h.h1219 V₀ V h125 ▸ hp)
  have hIV : preTil V₀ V hV Itil ≤ V := preTil_le V₀ V hV Itil
  have hcent : V₀ ≠ ⊥ → ∀ w ∈ preTil V₀ V hV Itil, w ∉ V₀ →
      p ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G)) := by
    intro _ w hwI hw0
    have hwV : w ∈ V := preTil_le V₀ V hV Itil hwI
    have hwt : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ Itil :=
      (mem_preTil_iff_of_mem V₀ V hV Itil hwV).1 hwI
    have hwne : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ≠ 1 := by
      intro h1
      apply hw0
      have h2 : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) = mkTil V₀ V hV (1 : IntMod V hV) := by
        rw [h1, map_one]
      have h3 := (mkTil_eq_iff V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) 1).1 h2
      change (IntMod.mk hV ⟨w, hwV⟩).val ∈ V₀
      simpa using h3
    obtain ⟨y, hyM, hyo, hyw⟩ := hI3 _ hwt hwne
    exact s16c11_dvd_card_cent_of_fixed_order D (Hyp125.hyp11 h.h127 h125)
      (c23_card_v0_le_four D h16) hV hpP hp2 hwV hw0 hyM hyo hyw
  have hTIloc : ∀ g : G, g ∉ D.M → preTil V₀ V hV Itil ⊓ conjSubgroup V₀ g = ⊥ :=
    s1611e3_ti_local D h125 hsp hIV hcent
  have hbot : ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = ⊥ := by
    intro A hA
    obtain ⟨hAT, g, hAg, hA0⟩ := hA
    have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
    have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg.isPGroup hAg).1 hA0
    by_cases hg : g ∈ D.M
    · have hgN : g ∈ normalizer (V : Set G) := by
        rw [h125.normalizer_eq]; exact hg
      have hVV : conjSubgroup V g = V := by
        ext x
        rw [mem_conjSubgroup_iff]
        exact (Subgroup.mem_normalizer_iff.1 hgN x).symm
      rw [hAeq, hVV]
      exact s16c11_barSub_self_eq_bot hV
    · by_contra hne
      have hAM : A ≤ D.M := hAT.trans D.sylowM.le
      have hAst : A ≤ stabTil V₀ V := hAM.trans hMst
      have hAel : IsElemAbelian 2 A := hAeq.symm ▸ hVg
      have hĒT : barSub V₀ V hV A ≤ barSub V₀ V hV D.T := barSub_mono V₀ V hV hAT
      have hĒel : IsElemAbelian2 (barSub V₀ V hV A) := isElemAbelian2_barSub hV hAel
      obtain ⟨B, hBle, hBq, ũ, hfixB, hmoved, hcomm⟩ :=
        hMod (barSub V₀ V hV A) hĒT hĒel hne
      obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV ũ
      have hD'A : preBarSub A V₀ V hV B ≤ A := inf_le_left
      have hD'st : preBarSub A V₀ V hV B ≤ stabTil V₀ V := hD'A.trans hAst
      have hbarD' : barSub V₀ V hV (preBarSub A V₀ V hV B) = B := by
        rw [barSub_preBarSub]
        exact inf_eq_left.2 hBle
      have huD : ∀ d ∈ preBarSub A V₀ V hV B, ⁅x.val, d⁆ ∈ V₀ := by
        intro d hd
        have hdst : d ∈ stabTil V₀ V := hD'st hd
        have hbar : actTil V₀ V hV ⟨d, hdst⟩ ∈ B := by
          rw [← hbarD']
          exact actTil_mem_barSub V₀ V hV hd hdst
        have hfix : actTil V₀ V hV ⟨d, hdst⟩ ũ = ũ := hfixB _ hbar
        have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨d, hdst⟩ x) = mkTil V₀ V hV x := by
          rw [← actTil_mk V₀ V hV ⟨d, hdst⟩ x, hx, hfix]
        rw [mkTil_eq_iff, actStab_apply_val] at h1
        have hconj : ⁅x.val, d⁆ = (d * x.val * d⁻¹ * (x.val)⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [hconj]
        exact V₀.inv_mem h1
      have hqA : E3.mQuot A (preBarSub A V₀ V hV B) = 1 :=
        (mQuot_barSub_preBarSub_gen hV hAst hBle).symm.trans hBq
      have hD'1 : E3.mQuot (conjSubgroup V g) (preBarSub A V₀ V hV B) = 1 := by
        rw [← hAeq]; exact hqA
      have hD'g : preBarSub A V₀ V hV B ≤ conjSubgroup V g := hAeq ▸ hD'A
      have hAMg : conjSubgroup V g ≤ D.M := hAeq ▸ hAM
      have hγ' : V₀ ⊓ conjSubgroup V g = ⊥ ∨
          ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V := by
        rcases hγ with h0 | h1
        · exact Or.inl (by rw [h0]; exact bot_inf_eq _)
        · exact Or.inr h1
      have hcommA : ∀ a ∈ conjSubgroup V g, ⁅x.val, a⁆ ∈ conjSubgroup V₀ g :=
        s1611e3_comm_mem_conj_of_hyperplane D h125 hAMg hm hr hγ' hD'g hD'1 x.val_mem huD
      have hfixA : ∀ a (ha : a ∈ A), actTil V₀ V hV ⟨a, hAst ha⟩ ũ = ũ := by
        intro a ha
        have hca : ⁅x.val, a⁆ ∈ conjSubgroup V₀ g := hcommA a (hAeq ▸ ha)
        have hcV : ⁅x.val, a⁆ ∈ V := by
          have haN : a ∈ normalizer (V : Set G) := by
            rw [h125.normalizer_eq]; exact hAM ha
          have hconj : a * (x.val)⁻¹ * a⁻¹ ∈ V :=
            (Subgroup.mem_normalizer_iff.1 haN (x.val)⁻¹).1 (V.inv_mem x.val_mem)
          rw [commutatorElement_def]
          simpa only [mul_assoc] using V.mul_mem x.val_mem hconj
        have hcommI : ⁅x.val, a⁆ ∈ preTil V₀ V hV Itil := by
          refine (mem_preTil_iff_of_mem V₀ V hV Itil hcV).2 ?_
          have himg : mkTil V₀ V hV (IntMod.mk hV ⟨⁅x.val, a⁆, hcV⟩) =
              (actTil V₀ V hV ⟨a, hAst ha⟩ ũ * ũ⁻¹)⁻¹ := by
            have hIntMod : IntMod.mk hV ⟨⁅x.val, a⁆, hcV⟩ =
                ((actStab V₀ V hV ⟨a, hAst ha⟩ x) * x⁻¹)⁻¹ := by
              apply IntMod.val_injective
              show ⁅x.val, a⁆ = (((actStab V₀ V hV ⟨a, hAst ha⟩ x) * x⁻¹)⁻¹).val
              simp only [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
              rw [commutatorElement_def]
              group
            rw [hIntMod]
            simp only [map_inv, map_mul]
            rw [← actTil_mk V₀ V hV ⟨a, hAst ha⟩ x, hx]
          rw [himg]
          exact Itil.inv_mem (hcomm _ (actTil_mem_barSub V₀ V hV ha (hAst ha)))
        have hcommInf : ⁅x.val, a⁆ ∈ preTil V₀ V hV Itil ⊓ conjSubgroup V₀ g :=
          Subgroup.mem_inf.2 ⟨hcommI, hca⟩
        rw [hTIloc g hg, Subgroup.mem_bot] at hcommInf
        have hau : a * x.val * a⁻¹ = x.val := by
          have hcomm' : x.val * a = a * x.val :=
            commutatorElement_eq_one_iff_mul_comm.1 hcommInf
          rw [← hcomm']; group
        rw [← hx, actTil_mk V₀ V hV ⟨a, hAst ha⟩ x]
        have hacts : actStab V₀ V hV ⟨a, hAst ha⟩ x = x := by
          apply IntMod.val_injective
          rw [actStab_apply_val]
          exact hau
        rw [hacts]
      obtain ⟨e, he, hene⟩ := hmoved
      obtain ⟨g', hg'A, hg'e⟩ := (mem_barSub V₀ V hV A e).1 he
      have hfixg' : e ũ = ũ := by
        have h1 : actTil V₀ V hV g' = actTil V₀ V hV ⟨(g' : G), hAst hg'A⟩ :=
          congrArg (actTil V₀ V hV) (Subtype.ext rfl)
        have h2 : actTil V₀ V hV g' ũ = ũ := by
          rw [h1]
          exact hfixA (g' : G) hg'A
        rw [hg'e] at h2
        exact h2
      exact hene hfixg'
  obtain ⟨P, hPM, hPp, hPc⟩ := s1611e3_exists_noncyclic_mbar h h16 hp
  exact s16c11_normalizer_le_of_forall_barSub_eq_bot D h.h61 hV h125 hbot hp hPM hPp hPc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
