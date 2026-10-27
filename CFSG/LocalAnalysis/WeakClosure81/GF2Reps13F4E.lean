module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4D2
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4EAux1
import CFSG.RankThree.S4Free.Stellmacher25

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s134b_caseB_irr {Y K : Subgroup (MulAut W)} {t : MulAut W} (F : S134Frame Y K t)
    {x u : MulAut W} (hx : x ∈ K) (hu : u ∈ K) (hx7 : orderOf x = 7)
    (hux : u * x * u⁻¹ = x ^ 2) (hw : S134Weights x (t * x * t⁻¹) u) :
    commSub ⊤ (K ⊔ S134Conj t K) = commSub ⊤ (Subgroup.zpowers x) ∧
      IsIrrOn (K ⊔ S134Conj t K) (commSub ⊤ (K ⊔ S134Conj t K)) ⊥ ∧
      Nat.card ↥(commSub ⊤ (K ⊔ S134Conj t K)) = 2 ^ 9 ∧
      (¬ ∀ k ∈ K, ∀ r ∈ commSub ⊤ (K ⊔ S134Conj t K), (k : MulAut W) r = r) ∧
      (¬ ∀ k ∈ S134Conj t K, ∀ r ∈ commSub ⊤ (K ⊔ S134Conj t K), (k : MulAut W) r = r) := by
  classical
  obtain ⟨hx'mem, hx'7, hcomm, htx', hne⟩ := F.seven_data hx hx7
  set x' : MulAut W := t * x * t⁻¹ with hx'def
  set K' : Subgroup (MulAut W) := S134Conj t K with hK'def
  set E : Subgroup (MulAut W) := Subgroup.zpowers x ⊔ Subgroup.zpowers x' with hEdef
  set M : Subgroup W := commSub ⊤ E with hMdef
  set R : Subgroup W := commSub ⊤ (Subgroup.zpowers x) with hRdef
  set L : Subgroup (MulAut W) := K ⊔ K' with hLdef
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hx7
    simp at hx7
  have hx'1 : x' ≠ 1 := by
    intro h
    rw [h] at hx'7
    simp at hx'7
  have hux' : u * x' * u⁻¹ = x' := by
    rw [F.comm u hu x' hx'mem, mul_inv_cancel_right]
  have hRM : R = M := hw.eq_x
  have hR'M : commSub ⊤ (Subgroup.zpowers x') = R := hw.eq_x'.trans hRM.symm
  have hrkR : rk R = 9 := by rw [hRM]; exact hw.rk_nine
  have hEelem : CFSG.Open.IsElemAbelian 7 E := by
    rw [hEdef]
    exact w16g_isElemAbelian_sup_zpowers (by rw [← hx7]; exact pow_orderOf_eq_one x)
      (by rw [← hx'7]; exact pow_orderOf_eq_one x') (show Commute x x' from hcomm)
  have hEcard : Nat.card ↥E = 49 := by
    rw [hEdef]
    have h := w16g_card_sup_zpowers Nat.prime_seven hx7 hx'7 (show Commute x x' from hcomm) hne
    norm_num at h ⊢
    exact h
  have hEodd : Odd (Nat.card ↥E) := by
    rw [hEcard]
    exact ⟨24, by norm_num⟩
  have hKstabR : StableUnder K R := by
    rw [← hR'M]
    exact f4e_stable_commSub (A := K) (G := Subgroup.zpowers x') (U := ⊤)
      (fun a ha g hg => f4e_commute_zpowers_of (F.comm a ha x' hx'mem) hg)
      (fun a ha u hu => Subgroup.mem_top (a u))
  have hK'stabR : StableUnder K' R := by
    rw [hRdef]
    exact f4e_stable_commSub (A := K') (G := Subgroup.zpowers x) (U := ⊤)
      (fun a ha g hg => f4e_commute_zpowers_of (F.comm x hx a ha).symm hg)
      (fun a ha u hu => Subgroup.mem_top (a u))
  have hKmemstab : K ≤ stabSub R := by
    intro a ha
    rw [mem_stabSub]
    intro u
    refine ⟨fun h => ?_, fun h => hKstabR a ha u h⟩
    have h' := hKstabR a⁻¹ (K.inv_mem ha) (a u) h
    rwa [show a⁻¹ (a u) = u by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h'
  have hK'memstab : K' ≤ stabSub R := by
    intro a ha
    rw [mem_stabSub]
    intro u
    refine ⟨fun h => ?_, fun h => hK'stabR a ha u h⟩
    have h' := hK'stabR a⁻¹ (K'.inv_mem ha) (a u) h
    rwa [show a⁻¹ (a u) = u by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h'
  have hLRstab : StableUnder L R := by
    have hle : L ≤ stabSub R := by
      rw [hLdef]
      exact sup_le hKmemstab hK'memstab
    intro l hl r hr
    exact (mem_stabSub.mp (hle hl) r).2 hr
  have hR_le_L : R ≤ commSub ⊤ L := by
    rw [hRdef, hLdef]
    exact commSub_mono le_rfl (le_trans (Subgroup.zpowers_le.mpr hx) le_sup_left)
  have hKcomm_le_R : commSub ⊤ K ≤ R :=
    s134b_commSub_le_of_normalClosure (K := K) (s134b_isSimpleGroup_of_isL3 F.l3) hx hx1
      hKstabR le_rfl
  have hK'comm_le_R : commSub ⊤ K' ≤ R :=
    s134b_commSub_le_of_normalClosure (K := K') (s134b_isSimpleGroup_of_isL3 F.l3') hx'mem hx'1
      hK'stabR (le_of_eq hR'M)
  have hKcent : K ≤ centSec ⊤ R := by
    intro a ha
    refine mem_centSec.mpr ⟨mem_stabSub.mpr (fun u => by simp), fun w _ => ?_⟩
    exact hKcomm_le_R (Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩)
  have hK'cent : K' ≤ centSec ⊤ R := by
    intro a ha
    refine mem_centSec.mpr ⟨mem_stabSub.mpr (fun u => by simp), fun w _ => ?_⟩
    exact hK'comm_le_R (Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩)
  have hLcomm_le_R : commSub ⊤ L ≤ R := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨l, hl, w, _, rfl⟩
    exact (mem_centSec.mp ((sup_le hKcent hK'cent) hl)).2 w (Subgroup.mem_top w)
  have hcommL : commSub ⊤ L = R := le_antisymm hLcomm_le_R hR_le_L
  have hntK : ¬ ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r = r := by
    intro hall
    have hR_le_fix : R ≤ fixV (Subgroup.zpowers x) := by
      intro r hr
      rw [CFSG.RankThree.S4Free.Stell.mem_fixV_zpowers_iff_apply]
      exact hall x hx r hr
    have hRbot : R = ⊥ := by
      have hle : R ≤ R ⊓ fixV (Subgroup.zpowers x) := le_inf le_rfl hR_le_fix
      rw [hw.fix_x] at hle
      exact le_bot_iff.mp hle
    have h9 := hrkR
    rw [hRbot, rk_bot] at h9
    omega
  have hntK' : ¬ ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r = r := by
    intro hall
    have hR_eq : R = commSub ⊤ (Subgroup.zpowers x') := hRM.trans hw.eq_x'.symm
    have hR_le_fix : R ≤ fixV (Subgroup.zpowers x') := by
      intro r hr
      rw [CFSG.RankThree.S4Free.Stell.mem_fixV_zpowers_iff_apply]
      exact hall x' hx'mem r hr
    have hx'odd : Odd (Nat.card ↥(Subgroup.zpowers x')) := by
      rw [Nat.card_zpowers, hx'7]
      exact ⟨3, by norm_num⟩
    have hfixR' : R ⊓ fixV (Subgroup.zpowers x') = ⊥ := by
      rw [hR_eq, inf_comm]
      exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' F.exp hx'odd
    have hRbot : R = ⊥ := by
      have hle : R ≤ R ⊓ fixV (Subgroup.zpowers x') := le_inf le_rfl hR_le_fix
      rw [hfixR'] at hle
      exact le_bot_iff.mp hle
    have h9 := hrkR
    rw [hRbot, rk_bot] at h9
    omega
  have hbot_lt_R : ⊥ < R := by
    rw [bot_lt_iff_ne_bot]
    intro hbot
    have h9 := hrkR
    rw [hbot, rk_bot] at h9
    omega
  have hLbot : StableUnder L ⊥ := by
    intro l hl r hr
    rw [Subgroup.mem_bot] at hr ⊢
    rw [hr, map_one]
  have hirr : IsIrrOn L R ⊥ := by
    refine ⟨hbot_lt_R, hLRstab, hLbot, ?_⟩
    intro J hJstab hbotJ hJR
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    · right
      have hE_le_L : E ≤ L := by
        rw [hEdef, hLdef]
        exact sup_le (le_trans (Subgroup.zpowers_le.mpr hx) le_sup_left)
          (le_trans (Subgroup.zpowers_le.mpr hx'mem) le_sup_right)
      have hJstabE : StableUnder E J := fun e he j hj => hJstab e (hE_le_L he) j hj
      have hJfixE : J ⊓ fixV E = ⊥ := by
        have hJM : J ≤ M := hRM ▸ hJR
        have hle : J ⊓ fixV E ≤ ⊥ := by
          calc J ⊓ fixV E ≤ M ⊓ fixV E := inf_le_inf_right _ hJM
            _ = ⊥ := by
              rw [show M = commSub ⊤ E from hMdef, inf_comm]
              exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' F.exp hEodd
        exact le_bot_iff.mp hle
      have hJcommE : commSub J E = J := by
        have hdec := CFSG.Quasithin.B1.coprime_decomp F.exp hEodd hJstabE
        rw [hJfixE, bot_sup_eq] at hdec
        exact hdec.1
      have hdecomp := inf_fixV_hyperplane_decomposition (W := W) F.exp Nat.prime_seven
        (by norm_num) E hEelem hJstabE hJcommE
      have hex : ∃ D : hyperplanes 7 E, J ⊓ fixV (D : Subgroup (MulAut W)) ≠ ⊥ := by
        by_contra h
        have h0 : ∀ D : hyperplanes 7 E, J ⊓ fixV (D : Subgroup (MulAut W)) = ⊥ := by
          intro D
          by_contra hD
          exact h ⟨D, hD⟩
        have hsup0 : (⨆ D : hyperplanes 7 E,
            J ⊓ fixV (D : Subgroup (MulAut W))) = ⊥ := iSup_eq_bot.mpr h0
        rw [hdecomp.2] at hsup0
        exact hJbot hsup0
      obtain ⟨D, hDne⟩ := hex
      have hJle_hyp : J ⊓ fixV (D : Subgroup (MulAut W)) ≤
          hypPart E (D : Subgroup (MulAut W)) := by
        change J ⊓ fixV (D : Subgroup (MulAut W)) ≤
          M ⊓ fixV (D : Subgroup (MulAut W))
        exact inf_le_inf_right _ (hRM ▸ hJR)
      have hhyp_ne : hypPart E (D : Subgroup (MulAut W)) ≠ ⊥ := fun h0 =>
        hDne (le_bot_iff.mp (hJle_hyp.trans (le_of_eq h0)))
      have hDsupp : (D : Subgroup (MulAut W)) ∈ hypSupp 7 E := ⟨D.2, hhyp_ne⟩
      have hhyp_rk : rk ↥(hypPart E (D : Subgroup (MulAut W))) = 3 :=
        hw.supp_rk _ hDsupp
      have hJ_rk_dvd : 3 ∣ rk ↥(J ⊓ fixV (D : Subgroup (MulAut W))) :=
        f4e_three_dvd_component F.exp hEelem hEcard hJstabE hJfixE D.2
      have hJ_rk_pos : 0 < rk ↥(J ⊓ fixV (D : Subgroup (MulAut W))) := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        exact hDne ((rk_eq_zero_iff F.exp).mp h0)
      have hJ_rk_le : rk ↥(J ⊓ fixV (D : Subgroup (MulAut W))) ≤ 3 := by
        rw [← hhyp_rk]
        exact rk_mono hJle_hyp
      have hJ_rk : rk ↥(J ⊓ fixV (D : Subgroup (MulAut W))) = 3 := by
        rcases hJ_rk_dvd with ⟨k, hk⟩
        have hk1 : k ≤ 1 := by omega
        have hk0 : 0 < k := by omega
        omega
      have hJeq_hyp : J ⊓ fixV (D : Subgroup (MulAut W)) =
          hypPart E (D : Subgroup (MulAut W)) :=
        eq_of_le_of_rk_le F.exp hJle_hyp (by rw [hJ_rk, hhyp_rk])
      have hhyp_le_J : hypPart E (D : Subgroup (MulAut W)) ≤ J := hJeq_hyp ▸ inf_le_left
      have hall : ∀ D' ∈ hypSupp 7 E, hypPart E D' ≤ J := by
        intro D' hD'
        obtain ⟨m, hm⟩ := hw.supp_trans (D : Subgroup (MulAut W)) hDsupp D' hD'
        have hn : u ^ m ∈ normalizer (E : Set (MulAut W)) :=
          Subgroup.pow_mem (normalizer (E : Set (MulAut W)))
            (s134b_mem_normalizer_sup (x := x) (x' := x') (u := u) hux hux') m
        have hmap := f4e_map_hypPart_conj (E := E) (D := (D : Subgroup (MulAut W))) hn
        have hle : (hypPart E (D : Subgroup (MulAut W))).map (u ^ m).toMonoidHom ≤ J := by
          intro x0 hx0
          rcases Subgroup.mem_map.mp hx0 with ⟨y, hy, rfl⟩
          exact hJstab (u ^ m) (Subgroup.mem_sup_left (Subgroup.pow_mem K hu m))
            y (hhyp_le_J hy)
        rw [hm, ← hmap]
        exact hle
      have hMstabE : StableUnder E M := by
        rw [hMdef]
        intro e he m hm
        exact CFSG.Quasithin.Asc81c.commSub_stable' he hm
      have hMcommE : commSub M E = M := by
        rw [hMdef]
        exact CFSG.Quasithin.Asc81c.commSub_commSub_eq' F.exp hEodd
      have hMdecomp := inf_fixV_hyperplane_decomposition (W := W) F.exp Nat.prime_seven
        (by norm_num) E hEelem hMstabE hMcommE
      have hM_le_J : M ≤ J := by
        rw [← hMdecomp.2]
        refine iSup_le fun D'' => ?_
        change hypPart E (D'' : Subgroup (MulAut W)) ≤ J
        by_cases h : hypPart E (D'' : Subgroup (MulAut W)) = ⊥
        · rw [h]
          exact bot_le
        · exact hall _ ⟨D''.2, h⟩
      have hR_le_J : R ≤ J := by rw [hRM]; exact hM_le_J
      exact le_antisymm hJR hR_le_J
  have hcardR : Nat.card ↥R = 2 ^ 9 := by
    rw [card_eq_two_pow F.exp R, hrkR]
  refine ⟨hcommL, ?_, ?_, ?_, ?_⟩
  · rw [hcommL]
    exact hirr
  · rw [hcommL]
    exact hcardR
  · rw [hcommL]
    exact hntK
  · rw [hcommL]
    exact hntK'

end CFSG.LocalAnalysis.WeakClosure81
