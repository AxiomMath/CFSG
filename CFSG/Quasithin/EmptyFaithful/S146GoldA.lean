module

public import CFSG.Quasithin.EmptyFaithful.S146Three
public import CFSG.Quasithin.EmptyFaithful.S146Main
public import CFSG.Quasithin.Recognition.Gold2Central

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem six_main_central (hc : GoldschmidtCentralAbelianBound) (S : Setting146 G T M)
    {H : Subgroup G} (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2 ∧
      tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G) ∧
      tZero T u = pCoreOf 2 (mcOf T) ⊔ tU T u ∧ tZero T u = pCoreOf 2 H ⊔ tU T u)
    (h2 : Subgroup.normalizer (tZero T u : Set G) = T)
    (h3 : ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.centralizer (VZ T M : Set G)) ∧
      yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆ ∧
      yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G)⁆)
    (h4 : Subgroup.normalizer (tU T u : Set G) = tZero T u ∧
      IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u)
    {I : Subgroup G} (hI : IsIStar T M u I) (h211 : 2 ^ 11 < Nat.card T)
    (hL : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M))
    {H₂ : Subgroup G} (hT0 : tZero T u ≤ H₂)
    (hH₂C : H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u))
    (hS3 : Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3))) (hH₂M : ¬ H₂ ≤ M) :
    IsIStar T M u ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I))) ∧
      F6.IsGoldschmidtTripleIn ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)))
        (lI T M I ⊔ (T ⊓ I)) (oTwoUpper H₂ ⊔ (T ⊓ I)) := by
  obtain ⟨hidx4, hidx2, -, hQT, -⟩ := h1
  obtain ⟨hNu, -, -⟩ := h4
  obtain ⟨hSylTI, hTIcases⟩ := isIStar_sylow_cases S hu hidx2 h2 hNu hI
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hTu_I : tU T u ≤ I := hI.1.1.1
  have hTuTI : tU T u ≤ T ⊓ I := le_inf inf_le_left hTu_I
  have hTIT : T ⊓ I ≤ T := inf_le_left
  have hTIT0 : T ⊓ I ≤ tZero T u := by
    rcases hTIcases with h | h
    · rw [h]; exact tU_le_tZero T u
    · exact h.le
  have hTIH₂ : T ⊓ I ≤ H₂ := hTIT0.trans hT0
  have hH₂H : H₂ ≤ H := hH₂C.trans (centralizerMod_le_left _ _ _)
  have hTH : T ≤ H := hH.1.1
  have hQC : pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G) ≤ tU T u :=
    le_inf (inf_le_left.trans S.pCoreOf_mcOf_le) inf_le_right
  have hS1 := S.nonempty_oTwoQuot_I1 hL h3.2.1 (hQC.trans hTuTI) hTIT
  have hS2 := S.nonempty_oTwoQuot_I2 hH hu hQT hT0 hH₂C hS3 hTuTI hTIH₂
  have hT0S : IsSylowTwoOf (tZero T u) H₂ :=
    isSylowTwoOf_of_le_of_le' (S.isSylowTwoOf_tZero hH hu) hT0 hH₂C
  have hH₂eq : H₂ ≤ oTwoUpper H₂ ⊔ tZero T u :=
    F7.isSylowTwoOf_le_sup_of_two_power hT0S (le_normalizer_oTwoUpper H₂)
      (fun x hx => exists_pow_mem_oTwoUpper H₂ hx)
  have hOc : oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) :=
    S.oTwoUpper_le_centralizer hH hH₂C
  have hlIL : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  have hlII : lI T M I ≤ I := (oTwoUpper_le _).trans inf_le_right
  obtain ⟨I₁, hI₁⟩ : ∃ I₁, I₁ = lI T M I ⊔ (T ⊓ I) := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ I₂, I₂ = oTwoUpper H₂ ⊔ (T ⊓ I) := ⟨_, rfl⟩
  obtain ⟨I₀, hI₀⟩ : ∃ I₀, I₀ = I₁ ⊔ I₂ := ⟨_, rfl⟩
  rw [← hI₁, ← hI₂, ← hI₀]
  rw [← hI₁] at hS1
  rw [← hI₂] at hS2
  have hI₁I : I₁ ≤ I := by rw [hI₁]; exact sup_le hlII inf_le_right
  have hTI_I₁ : T ⊓ I ≤ I₁ := by rw [hI₁]; exact le_sup_right
  have hTI_I₂ : T ⊓ I ≤ I₂ := by rw [hI₂]; exact le_sup_right
  have hI₂H₂ : I₂ ≤ H₂ := by rw [hI₂]; exact sup_le (oTwoUpper_le H₂) hTIH₂
  have hI₁I₀ : I₁ ≤ I₀ := by rw [hI₀]; exact le_sup_left
  have hI₂I₀ : I₂ ≤ I₀ := by rw [hI₀]; exact le_sup_right
  have hSyl1 : IsSylowTwoOf (T ⊓ I) I₁ := isSylowTwoOf_of_le_of_le' hSylTI hTI_I₁ hI₁I
  have hSyl2 : IsSylowTwoOf (T ⊓ I) I₂ := by
    rcases hTIcases with h | h
    · have hI₂C : I₂ ≤ H ⊓ Subgroup.centralizer ({u} : Set G) := by
        rw [hI₂]
        refine sup_le (le_inf ((oTwoUpper_le H₂).trans hH₂H) hOc) (le_inf (hTIT.trans hTH) ?_)
        rw [h]; exact inf_le_right
      refine isSylowTwoOf_of_le_of_le' ?_ hTI_I₂ hI₂C
      rw [h]; exact hu.sylow
    · exact isSylowTwoOf_of_le_of_le' (h ▸ hT0S) hTI_I₂ hI₂H₂
  obtain ⟨e₁⟩ := hS1
  obtain ⟨e₂⟩ := hS2
  have hidx1 : (T ⊓ I).relIndex I₁ = 3 := relIndex_eq_three_of_isSylowTwoOf e₁ hSyl1
  have hidx2' : (T ⊓ I).relIndex I₂ = 3 := relIndex_eq_three_of_isSylowTwoOf e₂ hSyl2
  have hXN : yOfL22 T M ⊔ T ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
    sup_le Subgroup.le_normalizer (hTM.trans S.hyp1281.normal)
  have hO2L_le : pCoreOf 2 (yOfL22 T M) ≤ T :=
    (F7.pCoreOf_mono_of_le_normalizer (le_sup_left : yOfL22 T M ≤ yOfL22 T M ⊔ T) hXN).trans
      (pCoreOf_two_le_of_isSylowTwoOf
        (isSylowTwoOf_of_le_of_le' S.isSylowTwoOf_top le_sup_right le_top))
  have hnot1 : ¬ I₁ ≤ mcOf T := by
    intro h
    have hlIG : lI T M I ≤ mcOf T := (by rw [hI₁] at h; exact le_sup_left.trans h)
    exact S.not_yOfL22_le_mcOf (hL.le.trans (sup_le hlIG
      (hO2L_le.trans (le_centralizer_quasithinOmegaOneCenter T))))
  have hI₂G : I₂ ≤ mcOf T := hI₂H₂.trans (hH₂H.trans (S.le_mcOf hH))
  have hmeet : I₁ ⊓ I₂ = T ⊓ I := by
    rcases eq_or_eq_of_relIndex_prime Nat.prime_three (le_inf hTI_I₁ hTI_I₂) inf_le_left hidx1
      with h | h
    · exact h
    · exfalso
      exact hnot1 ((inf_eq_left.mp h).trans hI₂G)
  by_cases hO : pCoreOf 2 I₀ = ⊥
  ·
    exfalso
    obtain ⟨⟨z, hzZ⟩, hz1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hzZ).1
    have hz2 : z ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(quasithinOmegaOneCenter T)) (x := ⟨z, hzZ⟩)
      rw [S.card_Z] at this
      simpa using congrArg Subtype.val this
    have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu.mem
    have hzu : z ∈ Subgroup.centralizer ({u} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.mp huG) z hzZ).symm
    have hzTI : z ∈ T ⊓ I := ⟨hzT, hTu_I ⟨hzT, hzu⟩⟩
    have hz12 : z ∈ I₁ ⊓ I₂ := by rw [hmeet]; exact hzTI
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZz : quasithinOmegaOneCenter T = Subgroup.zpowers z := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
      rw [S.card_Z, Nat.card_zpowers, orderOf_eq_prime hz2 hz1']
    have hI₂z : I₂ ≤ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp (hI₂G hx)) h hzZ
    have hcentI : I₁ ⊓ Subgroup.centralizer ({z} : Set G) = I₁ ⊓ I₂ := by
      have hle : T ⊓ I ≤ I₁ ⊓ Subgroup.centralizer ({z} : Set G) := by
        refine le_inf hTI_I₁ (fun x hx => ?_)
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (Subgroup.mem_centralizer_iff.mp
          (le_centralizer_quasithinOmegaOneCenter T hx.1)) h hzZ
      rcases eq_or_eq_of_relIndex_prime Nat.prime_three hle inf_le_left hidx1 with h | h
      · rw [hmeet]; exact h
      · exfalso
        apply hnot1
        intro x hx
        have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := by
          have : x ∈ I₁ ⊓ Subgroup.centralizer ({z} : Set G) := by rw [h]; exact hx
          exact this.2
        have hcomm : Commute z x := (Subgroup.mem_centralizer_iff.mp hxz) z rfl
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro y hy
        rw [hZz] at hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hcomm.zpow_left k).eq
    have hIM : I₁ ≤ M := by
      rw [hI₁]; exact sup_le (hlIL.trans (yOfL22_le T M)) (hTIT.trans hTM)
    have hzV : conjClosure (Subgroup.zpowers z) I₁ ≤ VZ T M :=
      conjClosure_mono (Subgroup.zpowers_le.mpr hzZ) hIM
    have hcard4 : Nat.card ↥(conjClosure (Subgroup.zpowers z) I₁) ≤ 4 := by
      have := Subgroup.card_le_of_le hzV
      rw [S.hyp.rank_two] at this
      exact this
    have habel : IsMulCommutative ↥(conjClosure (conjClosure (Subgroup.zpowers z) I₁) I₂) := by
      have hle : conjClosure (conjClosure (Subgroup.zpowers z) I₁) I₂ ≤ uOfL22 T M :=
        conjClosure_mono hzV hI₂G
      have := S.abelian
      exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hle ha) (hle hb)
    have hbound : Nat.card ↥(T ⊓ I) ≤ 2 ^ 9 := by
      have h₁ : IsSylowTwoOf (I₁ ⊓ I₂) I₁ := by rw [hmeet]; exact hSyl1
      have h₂ : IsSylowTwoOf (I₁ ⊓ I₂) I₂ := by rw [hmeet]; exact hSyl2
      have hO' : pCoreOf 2 (I₁ ⊔ I₂) = ⊥ := by rw [← hI₀]; exact hO
      rw [← hmeet]
      by_cases hc2 : CharTwo I₂
      · by_cases hc1 : CharTwo I₁
        · exact hc G I₁ I₂ z ⟨e₁⟩ ⟨e₂⟩ h₁ h₂ hc1 hc2 hO' hz12 hz1' hz2 hI₂z hcentI hcard4 habel
        · exact (gold2_card_inf_le_sixteen_of_not_charTwo_left e₁ e₂ h₁ h₂ hO' hc1).trans
            (by norm_num)
      · exact (gold2_card_inf_le_sixteen_of_not_charTwo_right e₁ e₂ h₁ h₂ hO' hc2).trans
          (by norm_num)
    have hmul := Subgroup.relIndex_mul_card (T ⊓ I) T
    rw [inf_of_le_left hTIT] at hmul
    have hidx : (T ⊓ I).relIndex T ≤ 4 := by
      rcases hTIcases with h | h
      · rw [h, hidx4]
      · rw [h, hu.index_two]; norm_num
    have : Nat.card ↥T ≤ 4 * 2 ^ 9 := by
      rw [← hmul]
      exact Nat.mul_le_mul hidx hbound
    omega
  ·
    have hnotM : ¬ I₀ ≤ M := by
      intro hle
      apply hH₂M
      refine hH₂eq.trans (sup_le ?_ ?_)
      · have hOI₂ : oTwoUpper H₂ ≤ I₂ := by rw [hI₂]; exact le_sup_left
        exact hOI₂.trans (hI₂I₀.trans hle)
      · exact (centralizerMod_le_left _ _ _).trans hTM
    have hI₀I : IsI T M u I₀ :=
      ⟨⟨hTuTI.trans (hTI_I₁.trans hI₁I₀), hO⟩, fun hle => hnot1 (hI₁I₀.trans hle), hnotM⟩
    obtain ⟨hI₀star, hTI₀⟩ := hI.of_le_inf hI₀I (hTI_I₁.trans hI₁I₀)
    refine ⟨hI₀star, hI₀.symm, ⟨e₁⟩, ⟨e₂⟩, ?_⟩
    rw [hmeet, ← hTI₀]
    exact (isIStar_sylow_cases S hu hidx2 h2 hNu hI₀star).1

theorem stepBCore_central (hcab : GoldschmidtCentralAbelianBound) (h9 : Stage1469)
    (h105 : Stage14610Five) (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) {T M : Subgroup G} (S : Setting146 G T M)
    (hD : FinalData146Core T M) : False := by
  obtain ⟨H, u, H₂, hH, hu, hCu, h4', hm, hT0, hH₂C, hS3, hH₂M, hrk⟩ := hD
  obtain ⟨I, hI, hIc⟩ := exists_isIStar_choice hCu
  have hTH : T ≤ H := hH.1.1
  have hlIL : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  have hlII : lI T M I ≤ I := (oTwoUpper_le _).trans inf_le_right
  have ha := h1 G T M S H hH u hu
  have hb := h2 G T M S H hH u hu
  have hc := h3 G T M S H hH u hu
  have hd := h4 G T M S H hH u hu
  obtain ⟨h211, hLT⟩ := h9 G T M H u S hH hu I hI h4' hm
  have hL_eq : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) := by
    refine le_antisymm ?_ (sup_le hlIL (LieType.BorelTits.pCoreOf_le 2 _))
    refine le_sup_pCoreOf_of_S3 (X := yOfL22 T M ⊔ T) le_sup_left ?_ S.hyp1281.residual
      (oTwoUpper_oTwoUpper _) hlIL S.facts.sThree (S.hyp.sylow.1.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) hLT
    exact sup_le Subgroup.le_normalizer (S.hyp.m_max.1.2.trans S.hyp1281.normal)
  obtain ⟨hI₀, hGT⟩ := six_main_central hcab S hH hu ha hb hc hd hI h211 hL_eq hT0 hH₂C hS3 hH₂M
  have hTI_le : T ⊓ I ≤ (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) :=
    le_sup_right.trans le_sup_left
  obtain ⟨-, hTI₀⟩ := hI.of_le_inf hI₀.1 hTI_le
  have hTIH₂ : T ⊓ I ≤ H₂ := by
    refine le_trans ?_ hT0
    rcases (isIStar_sylow_cases S hu ha.2.1 hb hd.1 hI).2 with h | h
    · rw [h]; exact tU_le_tZero T u
    · exact h.le
  have hOc : oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) :=
    S.oTwoUpper_le_centralizer hH hH₂C
  have hH₂H : H₂ ≤ H := hH₂C.trans (centralizerMod_le_left _ _ _)
  have hI₂H : oTwoUpper H₂ ⊔ (T ⊓ I) ≤ H :=
    sup_le ((oTwoUpper_le H₂).trans hH₂H) (inf_le_left.trans hTH)
  have hI₀eq := eq_sup_lI_sup (T := T) (M := M) (A := lI T M I) (B := T ⊓ I)
    (C := oTwoUpper H₂) (oTwoUpper_oTwoUpper _) hlIL rfl hTI₀
  have hcent : T ⊓ ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I))) = tU T u →
      (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro h
    have hIT : T ⊓ I = tU T u := by rw [← hTI₀]; exact h
    have hIc' := hIc hIT
    exact sup_le (sup_le (hlII.trans hIc') (inf_le_right.trans hIc'))
      (sup_le hOc (inf_le_right.trans hIc'))
  have hrank := h105 G T M H u S hH hu _ hI₀ h4' hm (oTwoUpper H₂ ⊔ (T ⊓ I))
    (by rw [hTI₀]; exact le_sup_right) hI₂H hGT.2.2.1 hI₀eq hcent
  have hconj : conjClosure (VZ T M) (oTwoUpper H₂ ⊔ (T ⊓ I)) =
      conjClosure (VZ T M) (oTwoUpper H₂) :=
    conjClosure_sup_eq_of_normalizes (hTIH₂.trans (le_normalizer_oTwoUpper H₂))
      (inf_le_left.trans S.T_le_normalizer_V)
  rw [hconj, hrk] at hrank
  norm_num at hrank

theorem stageSection146_of_inputs_central (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hcab : GoldschmidtCentralAbelianBound) (hA : Stage146BranchACore)
    (hB : Stage146BranchBCore) (h9 : Stage1469) (h105 : Stage14610Five) (h631 : Stage1463One)
    (h632 : Stage1463Two) (h633 : Stage1463Three) (h634 : Stage1463Four) : StageSection146 := by
  intro G _ _ T M hyp hnot hab
  have S : Setting146 G T M := ⟨hyp, hyp.facts1422 h11 h113, hnot, hab⟩
  by_cases h : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H
  · exact stepBCore_central hcab h9 h105 h631 h632 h633 h634 S (hB G T M S h)
  · push Not at h
    exact stepBCore_central hcab h9 h105 h631 h632 h633 h634 S (hA G T M S h)

end CFSG.Quasithin
