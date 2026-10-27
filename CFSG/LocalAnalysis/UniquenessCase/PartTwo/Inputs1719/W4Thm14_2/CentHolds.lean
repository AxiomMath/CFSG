module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.GraphLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.CentCoprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.CentScalar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.CentHomog
public import CFSG.GroupTheory.GF4Scalar
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Norm
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.Statement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups Matrix

private lemma six_le_mQuot_of_lt {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsSL3 ↥L 2)
    {z : MulAut W} (hzL : z ∈ L) (hz3 : z ^ 3 = 1)
    (hfpf : fixV (Subgroup.zpowers z) = ⊥) {V U : Subgroup W}
    (hV : StableUnder L V) (hU : StableUnder L U) (hlt : V < U) :
    6 ≤ E3.mQuot U V := by
  classical
  have hfree : ∀ w : W, z w = w → w = 1 := by
    intro w hw
    have hmem : w ∈ fixV (Subgroup.zpowers z) := mem_fixV_zpowers_iff_apply.mpr hw
    rw [hfpf] at hmem
    simpa using hmem
  let S : Set (Subgroup W) := {M | StableUnder L M ∧ V < M ∧ M ≤ U}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨U, hU, hlt, le_rfl⟩
  obtain ⟨M, hMS, hMmin⟩ := Set.exists_min_image S (fun M => rk M) hSfin hSne
  obtain ⟨hMstab, hVM, hMU⟩ := hMS
  have hirr : IsIrrOn L M V := by
    refine ⟨hVM, hMstab, hV, ?_⟩
    intro J hJstab hVJ hJM
    by_cases hJV : J = V
    · exact Or.inl hJV
    · refine Or.inr ?_
      have hltJV : V < J := lt_of_le_of_ne hVJ (Ne.symm hJV)
      have hJS : J ∈ S := ⟨hJstab, hltJV, hJM.trans hMU⟩
      have h1 : rk M ≤ rk J := hMmin J hJS
      have h2 : rk J ≤ rk M := rk_mono hJM
      exact eq_of_le_of_rk_le hW hJM (by omega)
  have hMmap : M.map z.toMonoidHom = M :=
    (StabLat.mem_stabSub_iff_map).mp (B1.le_stabSub_of_invariant hMstab hzL)
  have hVmap : V.map z.toMonoidHom = V :=
    (StabLat.mem_stabSub_iff_map).mp (B1.le_stabSub_of_invariant hV hzL)
  have heven : Even (E3.mQuot M V) :=
    CFSG.GroupTheory.even_mQuot_of_gf4 hW hz3 hfree M V hVM.le hMmap hVmap
  have hrkM : rk ↥M = rk ↥V + E3.mQuot M V := (c8_rk_eq_mQuot_add hVM.le).trans (add_comm _ _)
  have hMp : IsPGroup 2 ↥M := (isPGroup_two_of_sq_eq_one hW).to_subgroup M
  have hfive : 5 ≤ E3.mQuot M V := by
    by_contra h5
    push Not at h5
    have hd : 5 ≤ dMinDeg ↥L := k_SL3MinDegree_holds ↥L (Or.inl hL)
    have hcomm : commSub M L ≤ V :=
      commSub_le_of_rk_lt_dMinDeg hW hVM.le hMstab hV (by omega)
    have hmq0 : E3.mQuot M V ≠ 0 := by
      intro h0
      have hzero := (E3.mQuot_eq_zero_iff hMp hVM.le).mp h0
      exact hVM.ne hzero
    have h2dvd : 2 ∣ E3.mQuot M V := even_iff_two_dvd.mp heven
    have hmq2 : 2 ≤ E3.mQuot M V := Nat.le_of_dvd (Nat.pos_of_ne_zero hmq0) h2dvd
    obtain ⟨x, hxM, hxV⟩ : ∃ x ∈ M, x ∉ V := by
      by_contra h
      push Not at h
      exact hVM.ne (le_antisymm hVM.le h)
    have hx1 : x ≠ 1 := fun hx => hxV (hx ▸ V.one_mem)
    have hx2 : x ^ 2 = 1 := hW x
    let J : Subgroup W := V ⊔ Subgroup.zpowers x
    have hJle : J ≤ M := sup_le hVM.le (Subgroup.zpowers_le.mpr hxM)
    have hVJ : V < J := by
      refine lt_of_le_of_ne le_sup_left (Ne.symm ?_)
      intro hEq
      have hxJ : x ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      exact hxV (hEq ▸ hxJ)
    have hJstab : StableUnder L J := by
      intro l hl j hj
      have hcommJ : commSub J L ≤ V := (commSub_mono hJle le_rfl).trans hcomm
      have hmem : l j * j⁻¹ ∈ commSub J L :=
        Subgroup.subset_closure ⟨l, hl, j, hj, rfl⟩
      have hmemV : l j * j⁻¹ ∈ V := hcommJ hmem
      have heq : l j = (l j * j⁻¹) * j := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [heq]
      exact J.mul_mem (Subgroup.mem_sup_left hmemV) hj
    have hzx : Nat.card ↥(Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (p := 2) hx2 hx1
    have hinf : V ⊓ Subgroup.zpowers x = ⊥ := by
      have hle : V ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x := inf_le_right
      have hdvd : Nat.card ↥(V ⊓ Subgroup.zpowers x) ∣
          Nat.card ↥(Subgroup.zpowers x) := Subgroup.card_dvd_of_le hle
      rw [hzx] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact Subgroup.card_eq_one.mp h
      · exfalso
        have heq : V ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h, hzx])
        exact hxV (Subgroup.mem_inf.mp (heq.symm ▸ Subgroup.mem_zpowers x)).1
    have hcardJ : Nat.card ↥J = 2 * Nat.card ↥V := by
      have h1 := card_sup_mul_card_inf (U := V) (W := Subgroup.zpowers x)
      rw [hinf, hzx, Subgroup.card_bot, mul_one, mul_comm] at h1
      exact h1
    have hJneM : J ≠ M := by
      intro hEq
      have hcard : Nat.card ↥J = Nat.card ↥M := by rw [hEq]
      have hMc : Nat.card ↥M = 2 ^ E3.mQuot M V * Nat.card ↥V :=
        E3.card_eq_two_pow_mul hMp hVM.le
      have h4 : 4 ≤ 2 ^ E3.mQuot M V := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ E3.mQuot M V := Nat.pow_le_pow_right (by norm_num) hmq2
      have hMge : 4 * Nat.card ↥V ≤ Nat.card ↥M := by
        rw [hMc]
        exact Nat.mul_le_mul_right _ h4
      have hVpos : 0 < Nat.card ↥V := Nat.card_pos
      omega
    rcases hirr.2.2.2 J hJstab le_sup_left hJle with h | h
    · exact hVJ.ne' h
    · exact hJneM h
  have h6M : 6 ≤ E3.mQuot M V := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hadd := E3.mQuot_add (V := U) (U := V) (U' := M) hVM.le hMU
  omega

theorem pow_six_eq_one_of_graphType {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsSL3 ↥L 2)
    (hrk : rk ↥(⊤ : Subgroup W) ≤ 12) (hfix : fixV L = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] (α : SL(3, K) →* ↥L)
    (hα : Function.Surjective α) (hK : Nat.card K = 4)
    (hcen : (LinearFlag.scalars 3 K).map α = Subgroup.center ↥L) (hZ : Subgroup.center ↥L ≠ ⊥)
    {x : MulAut W}
    (ν : MulAut SL(3, K)) (hν : ∀ s, ((α (ν s) : ↥L) : MulAut W) = x * (α s : MulAut W) * x⁻¹)
    (hgraph : L34Out.IsGraphType ν) (c : MulAut W) (hc : ∀ l ∈ L, c * l = l * c) :
    c ^ 6 = 1 := by
  classical
  haveI : Finite (MulAut W) := inferInstanceAs (Finite (W ≃* W))
  have hcommapply_aux : ∀ (f : MulAut W) (l : MulAut W) (x : W), l ∈ L →
      (∀ l ∈ L, f * l = l * f) → l (f x) = f (l x) := by
    intro f l x hl hf
    have h := congrArg (fun t : MulAut W => t x) (hf l hl)
    simpa [MulAut.mul_apply, MulEquiv.coe_toMonoidHom] using h.symm
  have hcenter_ne : ∃ c₀ : ↥L, c₀ ∈ Subgroup.center ↥L ∧ c₀ ≠ 1 := by
    by_contra h
    apply hZ
    rw [eq_bot_iff]
    intro c₀ hc₀
    rw [Subgroup.mem_bot]
    by_contra hne
    exact h ⟨c₀, hc₀, hne⟩
  obtain ⟨c₀, hc₀mem, hc₀ne⟩ := hcenter_ne
  have hc₀map : c₀ ∈ (LinearFlag.scalars 3 K).map α := hcen.symm ▸ hc₀mem
  obtain ⟨A, hA, hAc⟩ := Subgroup.mem_map.mp hc₀map
  have hc₀cube : c₀ ^ 3 = 1 := by
    rw [← hAc, ← map_pow,
      CFSG.HardMathSupport.Curtis.Coordinator.pow_three_of_mem_scalars hA, map_one]
  have hz3 : ((c₀ : MulAut W)) ^ 3 = 1 := by
    have h := congrArg (fun t : ↥L => (t : MulAut W)) hc₀cube
    simpa using h
  have hz1 : ((c₀ : MulAut W)) ≠ 1 := by
    intro h
    apply hc₀ne
    exact Subtype.ext (by simpa using h)
  have hzL : ((c₀ : MulAut W)) ∈ L := c₀.2
  have hzc : ∀ l ∈ L, ((c₀ : MulAut W)) * l = l * ((c₀ : MulAut W)) := by
    intro l hl
    have h1 : (⟨l, hl⟩ : ↥L) * c₀ = c₀ * ⟨l, hl⟩ := Subgroup.mem_center_iff.mp hc₀mem _
    have h := congrArg (fun t : ↥L => (t : MulAut W)) h1
    simpa using h.symm
  have hfpf : fixV (Subgroup.zpowers ((c₀ : MulAut W))) = ⊥ :=
    fixV_zpowers_eq_bot_of_center hW hL hrk hfix α hα hcen hzL hzc hz1 hz3
  by_cases hIrr : IsIrrOn L ⊤ ⊥
  · have h3 : ∀ u ∈ (⊤ : Subgroup W), (c ^ 3) u * u⁻¹ ∈ (⊥ : Subgroup W) :=
      pow_three_mem_of_isIrrOn hW hL hrk α hα hK hcen hzL hzc hz1 hz3 hfpf hIrr hc
        (fun u _ => Subgroup.mem_top u) (fun v hv => by
          rw [Subgroup.mem_bot] at hv ⊢
          rw [hv, map_one])
    have hc3 : c ^ 3 = 1 := by
      ext w
      have h := h3 w (Subgroup.mem_top w)
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h
      simpa using h
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
  · have hWnt : Nontrivial W := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      haveI hsub : Subsingleton W := h
      haveI : Subsingleton (MulAut W) :=
        ⟨fun a b => MulEquiv.ext fun w => Subsingleton.elim (a w) (b w)⟩
      exact hz1 (Subsingleton.elim ((c₀ : MulAut W)) 1)
    haveI := hWnt
    obtain ⟨W₁, -, hW₁irr⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Three_exists_irr_le
        (A := L) (X := ⊤) (by intro a ha u hu; exact Subgroup.mem_top u) (by simp)
    have hW₁stab : StableUnder L W₁ := hW₁irr.2.1
    have hW₁bot : ⊥ < W₁ := hW₁irr.1
    have hrkW₁ : 6 ≤ rk ↥W₁ := by
      have h6 := six_le_mQuot_of_lt hW hL hzL hz3 hfpf (V := ⊥) (U := W₁)
        (fun a ha u hu => by
          rw [Subgroup.mem_bot] at hu ⊢
          rw [hu, map_one]) hW₁stab hW₁bot
      have h2 : E3.mQuot W₁ (⊥ : Subgroup W) ≤ rk ↥W₁ := by
        rw [c8_rk_eq_mQuot_add (A := W₁) (B := ⊥) bot_le, rk_bot, Nat.add_zero]
      exact le_trans h6 h2
    have hW₁neTop : W₁ ≠ ⊤ := by
      intro h
      apply hIrr
      rw [← h]
      exact hW₁irr
    by_cases hcW₁ : W₁.map c.toMonoidHom = W₁
    · have hcW₁_le : ∀ u ∈ W₁, c u ∈ W₁ := by
        intro u hu
        have hmem : c u ∈ W₁.map c.toMonoidHom := Subgroup.mem_map_of_mem c.toMonoidHom hu
        rwa [hcW₁] at hmem
      have h3₁ : ∀ u ∈ W₁, (c ^ 3) u * u⁻¹ ∈ (⊥ : Subgroup W) :=
          pow_three_mem_of_isIrrOn hW hL hrk α hα hK hcen hzL hzc hz1 hz3 hfpf hW₁irr hc hcW₁_le
            (fun v hv => by
              rw [Subgroup.mem_bot] at hv ⊢
              rw [hv, map_one])
      have hc3W₁ : ∀ u ∈ W₁, (c ^ 3) u = u := by
        intro u hu
        have h := h3₁ u hu
        rw [Subgroup.mem_bot, mul_inv_eq_one] at h
        exact h
      have hIrrTop : IsIrrOn L ⊤ W₁ := by
        refine ⟨lt_top_iff_ne_top.mpr hW₁neTop, fun a ha u hu => Subgroup.mem_top u,
          hW₁stab, ?_⟩
        intro J hJstab hW₁J hJtop
        by_cases hJV : J = W₁
        · exact Or.inl hJV
        · refine Or.inr ?_
          by_contra hJne
          have hlt : W₁ < J := lt_of_le_of_ne hW₁J (Ne.symm hJV)
          have h6W : 6 ≤ E3.mQuot (⊤ : Subgroup W) W₁ :=
            six_le_mQuot_of_lt hW hL hzL hz3 hfpf hW₁stab
              (fun a ha u hu => Subgroup.mem_top u) (lt_top_iff_ne_top.mpr hW₁neTop)
          have h6J : 6 ≤ E3.mQuot J W₁ :=
            six_le_mQuot_of_lt hW hL hzL hz3 hfpf hW₁stab hJstab hlt
          have h6WJ : 6 ≤ E3.mQuot (⊤ : Subgroup W) J :=
            six_le_mQuot_of_lt hW hL hzL hz3 hfpf hJstab
              (fun a ha u hu => Subgroup.mem_top u) (lt_top_iff_ne_top.mpr hJne)
          have hadd := E3.mQuot_add (V := (⊤ : Subgroup W)) (U := W₁) (U' := J) hW₁J hJtop
          have hrkrel : rk ↥(⊤ : Subgroup W) = rk ↥W₁ + E3.mQuot (⊤ : Subgroup W) W₁ :=
            (c8_rk_eq_mQuot_add (le_trans hW₁J hJtop)).trans (add_comm _ _)
          omega
      have h3top : ∀ u ∈ (⊤ : Subgroup W), (c ^ 3) u * u⁻¹ ∈ W₁ :=
        pow_three_mem_of_isIrrOn hW hL hrk α hα hK hcen hzL hzc hz1 hz3 hfpf hIrrTop hc
          (fun u _ => Subgroup.mem_top u) hcW₁_le
      ext w
      have hmem : (c ^ 3) w * w⁻¹ ∈ W₁ := h3top w (Subgroup.mem_top w)
      have hfix2 : (c ^ 3) ((c ^ 3) w * w⁻¹) = (c ^ 3) w * w⁻¹ := hc3W₁ _ hmem
      have h2 : (c ^ 6) w * ((c ^ 3) w)⁻¹ = (c ^ 3) w * w⁻¹ := by
        have h6 : (c ^ 6) w = (c ^ 3) ((c ^ 3) w) := by
          rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, MulAut.mul_apply]
        have hinv : ((c ^ 3) w)⁻¹ = (c ^ 3) w⁻¹ := by rw [map_inv]
        rw [h6, hinv, ← map_mul]
        exact hfix2
      have hcw : (c ^ 3) w * (c ^ 3) w = 1 := by
        simpa [pow_two] using hW ((c ^ 3) w)
      have hw2 : w * w = 1 := by simpa [pow_two] using hW w
      have hB : ((c ^ 3) w)⁻¹ = (c ^ 3) w := inv_eq_of_mul_eq_one_right hcw
      have hD : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
      rw [hB, hD] at h2
      have hfin : (c ^ 6) w = w := by
        calc (c ^ 6) w = (c ^ 6) w * ((c ^ 3) w * (c ^ 3) w) := by rw [hcw, mul_one]
          _ = ((c ^ 6) w * (c ^ 3) w) * (c ^ 3) w := (mul_assoc _ _ _).symm
          _ = ((c ^ 3) w * w) * (c ^ 3) w := by rw [h2]
          _ = w * ((c ^ 3) w * (c ^ 3) w) := by
              rw [mul_comm ((c ^ 3) w) w, mul_assoc]
          _ = w := by rw [hcw, mul_one]
      simpa using hfin
    · have hcinv : ∀ l ∈ L, c⁻¹ * l = l * c⁻¹ := by
        intro l hl
        exact Commute.inv_left (hc l hl)
      set W₂ : Subgroup W := W₁.map c.toMonoidHom with hW₂
      have hW₂stab : StableUnder L W₂ := by
        intro l hl u hu
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
        have hcommapply : l (c.toMonoidHom v) = c.toMonoidHom (l v) :=
          hcommapply_aux c l v hl hc
        rw [hcommapply]
        exact Subgroup.mem_map_of_mem c.toMonoidHom (hW₁stab l hl v hv)
      have hW₂irr : IsIrrOn L W₂ ⊥ := by
        have hW₂ne : W₂ ≠ ⊥ := by
          intro h
          rw [hW₂] at h
          have h1 := (Subgroup.map_eq_bot_iff_of_injective W₁ c.injective).mp h
          exact hW₁bot.ne' h1
        refine ⟨bot_lt_iff_ne_bot.mpr hW₂ne, hW₂stab, ?_, ?_⟩
        · intro a ha u hu
          rw [Subgroup.mem_bot] at hu ⊢
          rw [hu, map_one]
        · intro J hJstab hbotJ hJW₂
          by_cases hJ : J = ⊥
          · exact Or.inl hJ
          · refine Or.inr ?_
            have hKle : J.map (c⁻¹).toMonoidHom ≤ W₁ := by
              rintro _ ⟨j, hj, rfl⟩
              obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (hJW₂ hj)
              simpa using hv
            have hKstab : StableUnder L (J.map (c⁻¹).toMonoidHom) := by
              intro l hl k hk
              obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hk
              have hcommapply : l ((c⁻¹).toMonoidHom j) = (c⁻¹).toMonoidHom (l j) :=
                hcommapply_aux c⁻¹ l j hl hcinv
              rw [hcommapply]
              exact Subgroup.mem_map_of_mem (c⁻¹).toMonoidHom (hJstab l hl j hj)
            have hKne : J.map (c⁻¹).toMonoidHom ≠ ⊥ := by
              intro h
              exact hJ ((Subgroup.map_eq_bot_iff_of_injective J (c⁻¹).injective).mp h)
            have hK : J.map (c⁻¹).toMonoidHom = W₁ := by
              rcases hW₁irr.2.2.2 (J.map (c⁻¹).toMonoidHom) hKstab bot_le hKle with h | h
              · exact absurd h hKne
              · exact h
            have hcard : Nat.card ↥J = Nat.card ↥W₂ := by
              have h1 : Nat.card ↥(J.map (c⁻¹).toMonoidHom) = Nat.card ↥J :=
                Subgroup.card_map_of_injective (K := J) (c⁻¹).injective
              rw [hK] at h1
              rw [hW₂]
              have h2 : Nat.card ↥(W₁.map c.toMonoidHom) = Nat.card ↥W₁ :=
                Subgroup.card_map_of_injective (K := W₁) c.injective
              omega
            exact Subgroup.eq_of_le_of_card_ge hJW₂ (le_of_eq hcard.symm)
      have hdisj : W₁ ⊓ W₂ = ⊥ := by
        have hstab : StableUnder L (W₁ ⊓ W₂) := fun l hl u hu =>
          ⟨hW₁stab l hl u hu.1, hW₂stab l hl u hu.2⟩
        rcases hW₁irr.2.2.2 (W₁ ⊓ W₂) hstab bot_le inf_le_left with h | h
        · exact h
        · exfalso
          have hcard : Nat.card ↥W₁ = Nat.card ↥W₂ := by
            rw [hW₂]
            exact (Subgroup.card_map_of_injective (K := W₁) c.injective).symm
          have hle : W₁ ≤ W₂ := le_of_inf_eq h
          have heq : W₁ = W₂ := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
          exact hcW₁ (hW₂.symm.trans heq.symm)
      have hsup : W₁ ⊔ W₂ = ⊤ := by
        have hcardW₂ : rk ↥W₂ = rk ↥W₁ := by
          rw [hW₂]
          show padicValNat 2 (Nat.card ↥(W₁.map c.toMonoidHom)) = padicValNat 2 (Nat.card ↥W₁)
          rw [Subgroup.card_map_of_injective (K := W₁) c.injective]
        have hsupadd : rk ↥(W₁ ⊔ W₂) = rk ↥W₁ + rk ↥W₂ := by
          have h1 := rk_sup_add_rk_inf W₁ W₂
          rw [hdisj, rk_bot] at h1
          omega
        have hle : rk ↥(W₁ ⊔ W₂) ≤ rk ↥(⊤ : Subgroup W) := rk_mono le_top
        have hb : rk ↥W₁ = 6 := by omega
        refine eq_of_le_of_rk_le hW le_top ?_
        rw [hsupadd, hcardW₂, hb]
        omega
      exact (false_of_isGraphType_of_homogeneous hW hL hrk α hα ν hν hgraph
        hW₁irr hW₂irr hdisj hsup hc (show W₁.map c.toMonoidHom = W₂ from hW₂.symm)).elim

theorem k14_2Cent_holds :
    K14_2Cent := by
  intro W _ _ hW L hL hZ hZodd hrk hfix hcomm hex c hc
  obtain ⟨x, hxL, S, hS, hxS, P, hP, hmove⟩ := hex
  obtain ⟨K, hKf, hKfin, hKchar, _e, α, hKcard, hα, hαc, hαcen⟩ :=
    LinearFlag.exists_cover_of_odd_center (Y := ↥L) hL.1 hL.2 hZodd
  have hodd : Odd (Nat.card α.ker) :=
    LinearFlag.odd_card_ker_of_le_scalars (n := 3) (by norm_num) hαc
  obtain ⟨ν, hν, hgraph⟩ :=
    exists_graphType_of_moves (G := MulAut W) (L := L) (S := S) (P := P) α hα hαc hodd hS
      hxL hxS hP hmove
  exact pow_six_eq_one_of_graphType hW hL hrk hfix α hα (hKcard.trans (by norm_num)) hαcen hZ ν hν hgraph c hc
