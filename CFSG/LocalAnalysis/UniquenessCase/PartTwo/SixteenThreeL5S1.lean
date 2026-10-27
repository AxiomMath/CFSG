module

public import CFSG.Quasithin.Background.SLFiveQuotientFixedKernel
public import CFSG.LinearAlgebra.SLFiveRankTenCentralizer
public import CFSG.Quasithin.Background.JonesParshallWedgePointStabilizer
public import CFSG.Quasithin.Background.SmithD37Lin
public import CFSG.Quasithin.Vol2.Ch11SecOE2D
public import CFSG.GroupTheory.PRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.G11
open CFSG.Quasithin.SmithD37
open CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.JonesParshall.Curtis

variable {G : Type} [Group G] [Finite G]

theorem s168e3_l5_s1_false
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL : IsLn ↥(lBar V₀ V hV L) 5 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 10) :
    False := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcomm : commSub (⊤ : Subgroup W) H = ⊤ := by
    simpa [wTil, H, W, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hirrPair : commSub (commSub (⊤ : Subgroup W) H) H = commSub (⊤ : Subgroup W) H ∧
      IsIrrOn H (commSub (⊤ : Subgroup W) H)
        (commSub (⊤ : Subgroup W) H ⊓ fixV H) := by
    simpa only [irrSet, Set.mem_setOf_eq, H, W] using hirr
  have hirrOn : IsIrrOn H (⊤ : Subgroup W) (fixV H) := by
    simpa [hcomm, H, W, top_inf_eq] using hirrPair.2
  have hdim' : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10 := by
    simpa [hcomm, H, W, top_inf_eq] using hdim
  have hLie : CFSG.Blueprint.LieModel ↥H .PSL 5 2 1 := hL
  obtain ⟨eH⟩ := CFSG.Quasithin.Vol2.Ch11.OE2.nonempty_sl_of_lieModel (d := 5) hLie
  have hmodel : StatedClassicalModel ↥H .PSL 5 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide)
  have hfixbot : fixV H = ⊥ :=
    CFSG.Quasithin.fixV_eq_bot_of_sl5_rank_ten (W := W) hW H eH hcomm
      (fun J hJ hstable => hirrOn.2.2.2 J hstable hJ le_top) hdim'
  have hdimBot : E3.mQuot (⊤ : Subgroup W) (⊥ : Subgroup W) = 10 := by
    simpa [hfixbot] using hdim'
  have hcardW : Nat.card W = 2 ^ 10 := by
    have hrel := CFSG.Quasithin.E3.relIndex_eq_two_pow
      ((CFSG.Quasithin.isPGroup_two_of_sq_eq_one hW).to_subgroup (⊤ : Subgroup W))
      (⊥ : Subgroup W)
    rw [hdimBot] at hrel
    simpa [Subgroup.relIndex_bot_left, Subgroup.card_top] using hrel
  have hcardAdd : Nat.card (Additive W) = 2 ^ 10 := by
    rw [Nat.card_congr Additive.toMul]
    exact hcardW
  let : Module (ZMod 2) (Additive W) := SmithD37.zmodModule hW
  have hdim10 : Module.finrank (ZMod 2) (Additive W) = 10 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod, hcardAdd] at hpow
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) hpow).symm
  let f : MulAut W →* GLV (Additive W) := (SmithD37.autLin hW).toMonoidHom
  let Llin : Subgroup (GLV (Additive W)) := H.map f
  have hirrBot : IsIrrOn H (⊤ : Subgroup W) (⊥ : Subgroup W) := by
    simpa [hfixbot] using hirrOn
  have hdich : ∀ J : Subgroup W, (∀ g ∈ H, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJ => hirrBot.2.2.2 J hJ bot_le le_top
  have hIrrAct := SmithD37.isIrrAct_map (X := H) hW hdich
  have : Nontrivial (Additive W) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardAdd]; norm_num)
  have hIrr : IsIrr Llin (⊤ : Submodule (ZMod 2) (Additive W)) := by
    refine ⟨fun _ _ _ _ => Submodule.mem_top, bot_lt_top, ?_⟩
    intro J hJ _ _
    exact hIrrAct J hJ
  let eLlin : ↥Llin ≃* G5 := ((SmithD37.autLin hW).subgroupMap H).symm.trans eH
  have hHA : H ≤ A := by
    simpa [H, A, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAnorm : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs ha)
  let Alin : Subgroup (GLV (Additive W)) := A.map f
  have hLlin_le_Alin : Llin ≤ Alin := Subgroup.map_mono hHA
  have hAlin_norm : Alin ≤ Subgroup.normalizer (Llin : Set (GLV (Additive W))) := by
    have hmap := Subgroup.map_normalizer_eq_of_bijective (f := f) H
      (SmithD37.autLin hW).bijective
    calc Alin = A.map f := rfl
      _ ≤ (Subgroup.normalizer (H : Set (MulAut W))).map f := Subgroup.map_mono hAnorm
      _ = Subgroup.normalizer (Llin : Set (GLV (Additive W))) := by
          simpa [Llin] using hmap
  have hAlin_le_Llin : Alin ≤ Llin := by
    have hnorm := CFSG.LinearAlgebra.SLFiveRankTen.normalizer_eq_self_of_finrank_ten
      (L := Llin) eLlin hIrr hdim10
    exact hAlin_norm.trans (le_of_eq hnorm)
  have hAlin_eq : Alin = Llin := le_antisymm hAlin_le_Llin hLlin_le_Alin
  have hAeqH : A = H := by
    apply Subgroup.map_injective (f := f) (SmithD37.autLin hW).injective
    simpa [Alin, Llin] using hAlin_eq
  have hfixH : ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = 3 ∧ b x = x := by
    intro x _
    obtain ⟨θ, β, hact⟩ :=
      CFSG.LinearAlgebra.SLFiveRankTen.exists_actsAs_wedgeRep_of_finrank_ten
        (L := Llin) eLlin hIrr hdim10
    obtain ⟨g, hgord, hgfix⟩ :=
      CFSG.Quasithin.JonesParshall.wedgeRep_exists_order_three_fixing
        (β (Additive.ofMul x))
    let b : MulAut W := (SmithD37.autLin hW).symm (θ.symm g)
    have hbmap : (SmithD37.autLin hW) b = (θ.symm g : GLV (Additive W)) := by
      simp [b]
    have hbL : b ∈ H := by
      have hmem : (SmithD37.autLin hW) b ∈ Llin := by
        rw [hbmap]
        exact (θ.symm g).2
      obtain ⟨h, hh, hval⟩ := Subgroup.mem_map.mp (by simpa [Llin] using hmem)
      have hb_eq : h = b := (SmithD37.autLin hW).injective hval
      simpa [hb_eq] using hh
    have hord : orderOf b = 3 := by
      calc orderOf b = orderOf ((SmithD37.autLin hW) b) :=
            (MulEquiv.orderOf_eq (SmithD37.autLin hW) b).symm
        _ = orderOf (θ.symm g : GLV (Additive W)) := by rw [hbmap]
        _ = orderOf (θ.symm g : ↥Llin) := Subgroup.orderOf_coe _
        _ = orderOf g := MulEquiv.orderOf_eq θ.symm g
        _ = 3 := hgord
    have hβfix : β (((θ.symm g : ↥Llin) : GLV (Additive W)) (Additive.ofMul x)) =
        β (Additive.ofMul x) := by
      calc β (((θ.symm g : ↥Llin) : GLV (Additive W)) (Additive.ofMul x))
          = wedgeRep (θ (θ.symm g)) (β (Additive.ofMul x)) := hact (θ.symm g) _
        _ = wedgeRep g (β (Additive.ofMul x)) := by rw [MulEquiv.apply_symm_apply]
        _ = β (Additive.ofMul x) := hgfix
    have hlinfix : ((θ.symm g : ↥Llin) : GLV (Additive W)) (Additive.ofMul x) =
        Additive.ofMul x := β.injective hβfix
    have hactfix : b x = x := by
      have h := SmithD37.autLin_apply hW b x
      have h' : (SmithD37.autLin hW) b (Additive.ofMul x) = Additive.ofMul x := by
        rw [hbmap]
        exact hlinfix
      rw [h] at h'
      exact Additive.ofMul.injective h'
    exact ⟨b, hbL, hord, hactfix⟩
  have hAcard : Nat.card ↥A = 9999360 := by
    rw [hAeqH]
    exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hmodel
  have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥A := by
    rw [hAcard]
    norm_num
  have hqsq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 →
      ¬ q ^ 2 ∣ Nat.card ↥A := by
    intro q hq hq2 hq3 hdvd
    rw [hAcard] at hdvd
    have hq_dvd : q ∣ 9999360 := by
      have hq_dvd_q2 : q ∣ q ^ 2 := by
        rw [pow_two]
        exact dvd_mul_right q q
      exact hq_dvd_q2.trans hdvd
    have hfactor : q ∣ 2 ^ 10 * (3 ^ 2 * (5 * (7 * 31))) := by
      rwa [show 2 ^ 10 * (3 ^ 2 * (5 * (7 * 31))) = 9999360 by norm_num]
    have hcases : q ∣ 2 ^ 10 ∨ q ∣ 3 ^ 2 ∨ q ∣ 5 ∨ q ∣ 7 ∨ q ∣ 31 := by
      rcases (Nat.Prime.dvd_mul hq).1 hfactor with h | h
      · exact Or.inl h
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · exact Or.inr (Or.inl h)
        · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    rcases hcases with h | h | h | h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
    · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h))
    · have hq5 : q = 5 :=
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).1 h
      subst hq5
      exact (by decide : ¬ 5 ^ 2 ∣ 9999360) hdvd
    · have hq7 : q = 7 :=
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1 h
      subst hq7
      exact (by decide : ¬ 7 ^ 2 ∣ 9999360) hdvd
    · have hq31 : q = 31 :=
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31)).1 h
      subst hq31
      exact (by decide : ¬ 31 ^ 2 ∣ 9999360) hdvd
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have hpbound : CFSG.Open.pRank q (Mbar D.M V₀ V hV) ≤ 1 := by
      have h := CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := A) (k := 1) hq
        (by simpa using hqsq q hq hq2 hq3)
      simpa [A] using h
    omega
  have hfixA : ∀ x : W, x ≠ 1 → ∃ b ∈ A, orderOf b = 3 ∧ b x = x := by
    intro x hx
    obtain ⟨b, hbH, hord, hbx⟩ := hfixH x hx
    exact ⟨b, hAeqH.symm ▸ hbH, hord, hbx⟩
  have hk : S168e3Kernel A 3 :=
    s168e3_kernel_of_cube Nat.prime_three A hcube hfixA
  have h3sig : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact s168e3_false_of_kernel c Nat.prime_three h3sig hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
