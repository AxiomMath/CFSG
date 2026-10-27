module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_commSub_sup_left (D M : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (D ⊔ M) X = commSub D X ⊔ commSub M X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨d, hd, m, hm, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (d * m) * (d * m)⁻¹ = (x d * d⁻¹) * (x m * m⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [h1]
    have hd1 : x d * d⁻¹ ∈ commSub D X := Subgroup.subset_closure ⟨x, hx, d, hd, rfl⟩
    have hm1 : x m * m⁻¹ ∈ commSub M X := Subgroup.subset_closure ⟨x, hx, m, hm, rfl⟩
    exact (commSub D X ⊔ commSub M X).mul_mem (Subgroup.mem_sup_left hd1)
      (Subgroup.mem_sup_right hm1)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w16g_commSub_stable_of_commute {M : Subgroup W} {X : Subgroup (MulAut W)}
    {c : MulAut W} (hc : ∀ x ∈ X, c * x = x * c) (hM : ∀ u ∈ M, c u ∈ M) :
    ∀ u ∈ commSub M X, c u ∈ commSub M X := by
  have hmapM : M.map c.toMonoidHom = M := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      exact hM v hv
    · rw [Subgroup.card_map_of_injective c.injective]
  have hmapX : X.map (MulAut.conj c).toMonoidHom = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : c * x * c⁻¹ = x := by rw [hc x hx, mul_inv_cancel_right]
      show c * x * c⁻¹ ∈ X
      rw [h1]; exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      show c * y * c⁻¹ = y
      rw [hc y hy, mul_inv_cancel_right]
  have h := CFSG.Quasithin.Z391.commSub_map_conj c M X
  rw [hmapM, hmapX] at h
  intro u hu
  rw [h]
  exact ⟨u, hu, rfl⟩

private theorem w16g_fixV_stable_of_commute {X : Subgroup (MulAut W)} {c : MulAut W}
    (hc : ∀ x ∈ X, c * x = x * c) : ∀ u ∈ fixV X, c u ∈ fixV X := by
  intro u hu
  rw [mem_fixV] at hu ⊢
  intro x hx
  calc x (c u) = (x * c) u := by rw [MulAut.mul_apply]
    _ = (c * x) u := by rw [(hc x hx).symm]
    _ = c (x u) := by rw [MulAut.mul_apply]
    _ = c u := by rw [hu x hx]

private theorem w16g_commSub_stable_of_normalizes {D : Subgroup W} {X : Subgroup (MulAut W)}
    {c : MulAut W} (hD : ∀ u ∈ D, c u ∈ D) (hX : ∀ x ∈ X, c * x * c⁻¹ ∈ X) :
    ∀ u ∈ commSub D X, c u ∈ commSub D X := by
  have hmapD : D.map c.toMonoidHom = D := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      exact hD v hv
    · rw [Subgroup.card_map_of_injective c.injective]
  have hmapX : X.map (MulAut.conj c).toMonoidHom = X := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      show c * x * c⁻¹ ∈ X
      exact hX x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have h := CFSG.Quasithin.Z391.commSub_map_conj c D X
  rw [hmapD, hmapX] at h
  intro u hu
  rw [h]
  exact ⟨u, hu, rfl⟩

theorem s13_2_three_rank8 (h : Cfg133 A t 3)
    (hP : IsPOnePlusTwo 3 ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆))
    (hr : rk ↥(commSub ⊤ (⁅pCoreOf 3 A, Subgroup.zpowers t⁆)) = 8) :
    ∃ (z : MulAut W) (N : Subgroup (MulAut W)), Data8 A t z N := by
  classical
  let O : Subgroup (MulAut W) := pCoreOf 3 A
  let P : Subgroup (MulAut W) := ⁅pCoreOf 3 A, Subgroup.zpowers t⁆
  have hO := s13_P_facts (W := W) (A := A) (t := t) (p := 3) h
  have hPg : IsPGroup 3 ↥P := hO.2.1
  have hPne : P ≠ ⊥ := hO.2.2.1
  have hPn : ∀ x ∈ P, t * x * t⁻¹ ∈ P := hO.2.2.2.1
  have hPc : ⁅P, Subgroup.zpowers t⁆ = P := hO.2.2.2.2.1
  have hPOn : ∀ y ∈ O, ∀ x ∈ P, y * x * y⁻¹ ∈ P := hO.2.2.2.2.2
  let h132 : Cfg132 t P :=
    { hW := fun w => by rw [pow_two]; exact h.hW w,
      ht := orderOf_eq_prime h.ht2 h.ht1,
      hrk := h.hrk,
      hP := hPg,
      hne := hPne,
      hn := hPn,
      hc := hPc }
  have hMin : W4Lem13_2MinLe 27 := w16h_minLe w4Lem13_1_holds 27
  obtain ⟨z, hzP, hz3, hzc, hzt, hZP⟩ := w16h_ext_center h132 hP
  obtain ⟨hMt2, hM6⟩ := w16h_ext_faithful_part hMin h132 hP hzP hz3 hzc hzt hZP
  let zs : Subgroup (MulAut W) := Subgroup.zpowers z
  let M : Subgroup W := commSub ⊤ zs
  let D : Subgroup W := fixV zs
  let D' : Subgroup W := commSub D P
  let N : Subgroup (MulAut W) := P ⊓ centSub D'
  have hM6' : rk ↥M = 6 := hM6
  have hcardP : Nat.card ↥P = 27 := by rw [hP.2.1]; norm_num
  have hPodd : Odd (Nat.card ↥P) := by rw [hcardP]; decide
  have hz3pow : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz3] at h1
    exact h1
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h132.ht, pow_two] at h1
    exact h1
  have htz : t * z = z * t := by
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hzt]
  have hodd : Odd (Nat.card zs) := by
    change Odd (Nat.card (Subgroup.zpowers z))
    rw [Nat.card_zpowers, hz3]
    decide
  have hcompl : IsCompl D M := by
    have hc := isCompl_fixV_commV_of_odd zs hodd h132.hW
    rw [commV_eq_commSub] at hc
    exact hc
  have hsup : D ⊔ M = ⊤ := hcompl.sup_eq_top
  have hinf : D ⊓ M = ⊥ := hcompl.inf_eq_bot
  have hPM : ∀ x ∈ P, ∀ u ∈ M, x u ∈ M := by
    intro x hx u hu
    change u ∈ commSub ⊤ zs at hu
    change x u ∈ commSub ⊤ zs
    exact w16g_commSub_stable_of_commute (M := ⊤) (X := zs) (c := x)
      (fun y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((show Commute x z from hzc x hx).zpow_right n).eq)
      (fun w _ => Subgroup.mem_top (x w)) u hu
  have hPD : ∀ x ∈ P, ∀ u ∈ D, x u ∈ D := by
    intro x hx u hu
    change u ∈ fixV zs at hu
    change x u ∈ fixV zs
    exact w16g_fixV_stable_of_commute (X := zs) (c := x)
      (fun y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((show Commute x z from hzc x hx).zpow_right n).eq) u hu
  have hMP : commSub M P = M := by
    refine le_antisymm (commSub_le_of_invariant hPM) ?_
    have h1 : commSub M zs = M := by
      change commSub (commSub ⊤ zs) zs = commSub ⊤ zs
      exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.commSub_commSub_eq h132.hW hodd
    calc M = commSub M zs := h1.symm
      _ ≤ commSub M P := commSub_mono le_rfl (Subgroup.zpowers_le.mpr hzP)
  have hD'Ple : commSub D P ≤ D := commSub_le_of_invariant hPD
  have hdisjP : commSub D P ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact Subgroup.mem_bot.mp (hinf ▸ ⟨hD'Ple hu.1, hu.2⟩)
  have hPdecomp : commSub ⊤ P = commSub D P ⊔ M := by
    rw [← hsup, w16g_commSub_sup_left, hMP]
  have hrankP : rk ↥(commSub ⊤ P) = rk ↥(commSub D P) + rk ↥M := by
    rw [hPdecomp]
    have hh := rk_sup_add_rk_inf (commSub D P) M
    rw [hdisjP, rk_bot, add_zero] at hh
    exact hh
  have hrkD' : rk ↥D' = 2 := by
    change rk ↥(commSub D P) = 2
    have hr' : rk ↥(commSub ⊤ P) = 8 := hr
    rw [hrankP, hM6'] at hr'
    omega
  have hD'ne : D' ≠ ⊥ := by
    intro hbot
    have h0 : rk ↥D' = 0 := by rw [hbot, rk_bot]
    omega
  have hD'D : D' ≤ D := hD'Ple
  have hPstab : P ≤ stabSub D' := by
    intro x hx
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
        have h1 := w16g_commSub_stable_of_normalizes (D := D) (X := P) (c := x⁻¹)
          (fun v hv => hPD x⁻¹ (P.inv_mem hx) v hv)
          (fun y hy => P.mul_mem (P.mul_mem (P.inv_mem hx) hy) (P.inv_mem (P.inv_mem hx)))
          (x u) hu
        simpa using h1,
      fun hu => w16g_commSub_stable_of_normalizes (D := D) (X := P) (c := x)
        (fun v hv => hPD x hx v hv)
        (fun y hy => P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) u hu⟩
  have hD'Pinv : ∀ x ∈ P, ∀ u ∈ D', x u ∈ D' := by
    intro x hx u hu
    exact w16g_commSub_stable_of_normalizes (D := D) (X := P) (c := x)
      (fun v hv => hPD x hx v hv)
      (fun y hy => P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) u hu
  have hDt : ∀ u ∈ D, t u ∈ D := by
    intro u hu
    change u ∈ fixV zs at hu
    change t u ∈ fixV zs
    exact w16g_fixV_stable_of_commute (X := zs) (c := t)
      (fun y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((show Commute t z from htz).zpow_right n).eq) u hu
  have hD'P : commSub D' P = D' := by
    have htopfix : commSub (⊤ : Subgroup W) P ⊓ fixV P = ⊥ := by
      have h2 := (CFSG.Quasithin.coprime_decomp hPodd h132.hW (W := (⊤ : Subgroup W))
        (fun g _ w _ => Subgroup.mem_top (g w))).2
      simpa using h2
    have hD'fixP : D' ⊓ fixV P = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      exact Subgroup.mem_bot.mp
        (htopfix ▸ ⟨commSub_mono le_top le_rfl hu.1, hu.2⟩)
    have h1 := (CFSG.Quasithin.coprime_decomp hPodd h132.hW (W := D') hD'Pinv).1
    rwa [hD'fixP, sup_bot_eq] at h1
  have hDdecomp : D' ⊔ (D ⊓ fixV P) = D := by
    have h1 := (CFSG.Quasithin.coprime_decomp hPodd h132.hW (W := D) hPD).1
    exact h1
  have hP'ne : autSub P D' ≠ ⊥ := by
    intro hbot
    have hPcent : P ≤ centSub D' := by
      intro x hx
      rw [mem_centSub]
      intro u hu
      have hmem : resHom D' ⟨x, hPstab hx⟩ ∈ autSub P D' :=
        mem_autSub.mpr ⟨⟨x, hPstab hx⟩, hx, rfl⟩
      rw [hbot] at hmem
      have h1 : resHom D' ⟨x, hPstab hx⟩ = 1 := Subgroup.mem_bot.mp hmem
      have h2 := congrArg (fun φ : MulAut ↥D' => ((φ ⟨u, hu⟩ : ↥D') : W)) h1
      simpa [resHom_apply] using h2
    have hbot2 : commSub D' P = ⊥ := by
      rw [commSub, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨x, hx, u, hu, rfl⟩
      rw [mem_centSub.mp (hPcent hx) u hu, mul_inv_cancel]
      rfl
    rw [hD'P] at hbot2
    exact hD'ne hbot2
  have hD'2 : Nat.card ↥D' = 4 := by
    have h1 := card_eq_two_pow h132.hW D'
    rw [h1, hrkD']; norm_num
  have hD'sq : ∀ v : ↥D', v ^ 2 = 1 := by
    intro v
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using h132.hW (v : W)
  have hMulAutCard : Nat.card (MulAut ↥D') = 6 := by
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
      (W := ↥D') (fun a b => mul_comm a b) hD'sq (n := 2) (by rw [hD'2]; norm_num)
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp [Fin.prod_univ_succ]
  have hP'grp : IsPGroup 3 ↥(autSub P D') := by
    have hPsub : IsPGroup 3 ↥(P.subgroupOf (stabSub D')) :=
      hPg.comap_of_injective (stabSub D').subtype (stabSub D').subtype_injective
    exact IsPGroup.map hPsub (resHom D')
  have hP'dvd : Nat.card ↥(autSub P D') ∣ 6 := by
    rw [← hMulAutCard]
    exact Subgroup.card_subgroup_dvd_card (autSub P D')
  have hP'card : Nat.card ↥(autSub P D') = 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := ↥(autSub P D'))).mp hP'grp
    have hdvd : 3 ^ n ∣ 6 := hn ▸ hP'dvd
    have hne1 : Nat.card ↥(autSub P D') ≠ 1 := by
      intro hc
      exact hP'ne (Subgroup.card_eq_one.mp hc)
    have hnle : n ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h2 : 2 ≤ n := by omega
      have h9 : 9 ≤ 3 ^ n := by
        calc (9 : ℕ) = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      have h6 : 3 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases n
    · rw [hn] at hne1; norm_num at hne1
    · rw [hn]; norm_num
  have hcardAut := card_autSub_mul (A := P) (U := D') hPstab
  have hNcard : Nat.card ↥N = 9 := by
    change Nat.card ↥(P ⊓ centSub D') = 9
    have h1 := hcardAut
    rw [hP'card, hcardP] at h1
    omega
  have hNcomm : ∀ a b : ↥N, a * b = b * a := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card ↥N = 3 ^ 2 := by rw [hNcard]; norm_num
    exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥N) hcard).is_comm.comm
  have hNpow : ∀ a : ↥N, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    change (a : MulAut W) ^ 3 = 1
    have h1 : (⟨(a : MulAut W), a.2.1⟩ : ↥P) ^ 3 = 1 := hP.2.2 _
    have h2 : (((⟨(a : MulAut W), a.2.1⟩ : ↥P) ^ 3 : ↥P) : MulAut W)
        = (a : MulAut W) ^ 3 := by rw [Subgroup.coe_pow]
    rw [h1] at h2
    simpa using h2.symm
  have hN9 : IsElemAbelianOfRank 3 2 ↥N := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact w16g_isElemAbelianOfRank_of_card (p := 3) (n := 2) hNcomm hNpow
      (by rw [hNcard]; norm_num)
  have hNP : N ≤ P := inf_le_left
  have hzN : z ∈ N := by
    refine ⟨hzP, ?_⟩
    change z ∈ centSub D'
    rw [mem_centSub]
    intro u hu
    exact mem_fixV.mp (hD'D hu) z (Subgroup.mem_zpowers z)
  have hDN : commSub D N = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV]
    intro x hx
    have hxP : x ∈ P := hNP hx
    have hxD' : x ∈ centSub D' := hx.2
    rw [← hDdecomp] at hu
    obtain ⟨v, hv, w, hw, hvw⟩ := Subgroup.mem_sup.mp hu
    calc x u = x (v * w) := by rw [← hvw]
      _ = x v * x w := map_mul x v w
      _ = v * w := by rw [mem_centSub.mp hxD' v hv, mem_fixV.mp hw.2 x hxP]
      _ = u := hvw
  have hNM : commSub ⊤ N ≤ M := by
    have h1 : commSub ⊤ N = commSub (D ⊔ M) N := by rw [hsup]
    rw [h1, w16g_commSub_sup_left, hDN, bot_sup_eq]
    exact (commSub_mono le_rfl hNP).trans (le_of_eq hMP)
  have hNV : commSub ⊤ N = commSub ⊤ (Subgroup.zpowers z) := by
    refine le_antisymm hNM ?_
    exact commSub_mono le_rfl (Subgroup.zpowers_le.mpr hzN)
  have hrkt : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
    have hmono := (w16h_rk_six_or_eight hMin w4Lem13_1_holds h132 hP).2
    have hr' : rk ↥(commSub ⊤ P) = 8 := hr
    have hge : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
      by_contra hlt
      push Not at hlt
      have hle2 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 2 := by omega
      have h6 := hmono hle2
      omega
    exact le_antisymm h.hrk hge
  have htD' : ∀ u ∈ D', t u ∈ D' :=
    w16g_commSub_stable_of_normalizes (D := D) (X := P) (c := t) hDt hPn
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have htD'inv : ∀ u ∈ D', t⁻¹ u ∈ D' := by
    intro u hu; rw [htinv]; exact htD' u hu
  have hNt : ∀ x ∈ N, t * x * t⁻¹ ∈ N := by
    intro x hx
    refine ⟨hPn x hx.1, ?_⟩
    change t * x * t⁻¹ ∈ centSub D'
    rw [mem_centSub]
    intro u hu
    show (t * x * t⁻¹) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, mem_centSub.mp hx.2 (t⁻¹ u) (htD'inv u hu)]
    simp
  have hNO : ∀ g ∈ pCoreOf 3 A, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    intro g hg x hx
    have hgO : g ∈ O := hg
    have hgP : ∀ y ∈ P, g * y * g⁻¹ ∈ P := hPOn g hgO
    have hgzP : g * z * g⁻¹ ∈ P := hgP z hzP
    have hgzC : ∀ y ∈ P, y * (g * z * g⁻¹) = (g * z * g⁻¹) * y := by
      intro y hy
      have hgyP : g⁻¹ * y * g ∈ P := hPOn g⁻¹ (O.inv_mem hgO) y hy
      have h1 : (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) := hzc _ hgyP
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = (g * z * g⁻¹) * y := by group
    have hgz_zp : g * z * g⁻¹ ∈ zs := hZP _ hgzP hgzC
    have hgs : zs.map (MulAut.conj g).toMonoidHom = zs := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · change (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers z
        rw [MonoidHom.map_zpowers]
        exact Subgroup.zpowers_le.mpr hgz_zp
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hgD : D.map g.toMonoidHom = D := by
      have h1 := CFSG.Quasithin.Asc81c.fixV_map_conj zs g
      rw [hgs] at h1
      exact h1.symm
    have hgPmap : P.map (MulAut.conj g).toMonoidHom = P := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro y ⟨v, hv, rfl⟩
        show g * v * g⁻¹ ∈ P
        exact hgP v hv
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hgD' : D'.map g.toMonoidHom = D' := by
      have h1 := CFSG.Quasithin.Z391.commSub_map_conj g D P
      rw [hgD, hgPmap] at h1
      exact h1.symm
    refine ⟨hgP x hx.1, ?_⟩
    change g * x * g⁻¹ ∈ centSub D'
    rw [mem_centSub]
    intro u hu
    have hgu : g⁻¹ u ∈ D' := by
      have hu' : u ∈ D'.map g.toMonoidHom := by rw [hgD']; exact hu
      obtain ⟨v, hv, hv_eq⟩ := Subgroup.mem_map.mp hu'
      rw [← hv_eq]
      simpa using hv
    show (g * x * g⁻¹) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, mem_centSub.mp hx.2 (g⁻¹ u) hgu]
    simp
  exact ⟨z, N, ⟨hP, hzN, hNP, hz3, hzc, hZP, hzt, hN9, hNO, hNt, hrkt, hNV, hM6'⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
