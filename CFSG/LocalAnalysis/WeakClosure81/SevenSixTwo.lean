module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoHall
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoMod
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def commOthers (V H E J A Y : Subgroup G) (v : G) : Subgroup G :=
  ⨆ d' ∈ dSetIn V H E J A, ⨆ (_ : d' ∈ Subgroup.normalizer (Y : Set G)),
    ⨆ (_ : v⁻¹ * d' ∉ J), ⁅Y, Subgroup.zpowers d'⁆

private theorem s762_zpow_eq_one_or_self_of_mul_self_eq_one {x : G} (hx : x * x = 1)
    (n : ℤ) : x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hx]
    rw [h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hx]
    rw [h2, one_zpow, one_mul]

private theorem s762_mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

private theorem s762_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf, hA x, hB x]

private theorem s762_mem_normalizer_iSup {ι : Sort*} {F : ι → Subgroup G} {g : G}
    (h : ∀ i, g ∈ Subgroup.normalizer (F i : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ i, F i : Subgroup G) : Set G) := by
  simp_rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h ⊢
  rw [Subgroup.map_iSup]
  exact iSup_congr h

private theorem s762_le_normalizer_iSup {ι : Sort*} {F : ι → Subgroup G} {Y : Subgroup G}
    (h : ∀ i, Y ≤ Subgroup.normalizer (F i : Set G)) :
    Y ≤ Subgroup.normalizer ((⨆ i, F i : Subgroup G) : Set G) :=
  (le_iInf h).trans (Subgroup.iInf_normalizer_le_normalizer_iSup F)

variable {V H E J A X : Subgroup G} [(J.subgroupOf X).Normal]

theorem Hyp76.commOthers_sup_iSub_centralizes (h : Hyp76 V H E J A X) {Y : Subgroup G}
    (hYX : Y ≤ X) {U : Subgroup G} (hU : U ∈ omegaSet V H E) (hUA : U ≤ A ⊔ J) {v : G}
    (hv : v ∈ U) (hvJ : v ∉ J) :
    ∀ w ∈ commOthers V H E J A Y v ⊔ iSub V H E,
      ∀ z ∈ ⁅iSub V H E, Subgroup.zpowers v⁆, w * z = z * w := by
  have hIab : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.isElemAbelian h.isTI h.isMulCommutative h.omega_le_H
  have hv2 : v * v = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU) hv
  have hcomm_le : ⁅iSub V H E, Subgroup.zpowers v⁆ ≤ U ⊓ iSub V H E := by
    rw [Subgroup.commutator_le]
    intro a ha t ht
    rw [Subgroup.mem_zpowers_iff] at ht
    obtain ⟨n, rfl⟩ := ht
    rcases s762_zpow_eq_one_or_self_of_mul_self_eq_one hv2 n with h1 | hv'
    · rw [h1]
      simp [commutatorElement_def]
    · rw [hv']
      have hmem := commutator_mem_inf_iSub (V := U)
        (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU)
        (isTI_of_mem_omegaSet hU h.isTI) h.isMulCommutative h.le_H h.normal_E
        (by rw [omegaSet_eq_of_mem hU]; exact h.omega_le_H)
        (by rw [omegaSet_eq_of_mem hU]; exact hU)
        (a := a) (v := v) (by rw [iSub_eq_of_mem hU]; exact ha) hv
      rwa [iSub_eq_of_mem hU] at hmem
  have hB_le : commOthers V H E J A Y v ≤ Subgroup.centralizer (U : Set G) := by
    unfold commOthers
    refine iSup₂_le fun d' hd' => ?_
    refine iSup_le fun hd'Y => ?_
    refine iSup_le fun hne => ?_
    have hcent := h.centralizes_commutator hU hUA hv hvJ hd' hne
    have hUcX : U ≤ Subgroup.centralizer ((⁅X, Subgroup.zpowers d'⁆ : Subgroup G) : Set G) :=
      fun u hu => Subgroup.mem_centralizer_iff.mpr fun y hy => (hcent u hu y hy).symm
    have hYX' : ⁅Y, Subgroup.zpowers d'⁆ ≤ ⁅X, Subgroup.zpowers d'⁆ :=
      Subgroup.commutator_mono hYX le_rfl
    exact Subgroup.le_centralizer_iff.mp (hUcX.trans (Subgroup.centralizer_le hYX'))
  have hcomm_leI : ⁅iSub V H E, Subgroup.zpowers v⁆ ≤ iSub V H E := hcomm_le.trans inf_le_right
  have hK_le_U : ⁅iSub V H E, Subgroup.zpowers v⁆ ≤ U := hcomm_le.trans inf_le_left
  have hI_le_centI : iSub V H E ≤ Subgroup.centralizer (iSub V H E : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hIab.1
  have hB_le_centK : commOthers V H E J A Y v ≤
      Subgroup.centralizer ((⁅iSub V H E, Subgroup.zpowers v⁆ : Subgroup G) : Set G) :=
    hB_le.trans (Subgroup.centralizer_le hK_le_U)
  have hI_le_centK : iSub V H E ≤
      Subgroup.centralizer ((⁅iSub V H E, Subgroup.zpowers v⁆ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hcomm_leI.trans hI_le_centI)
  have hsup_le := sup_le hB_le_centK hI_le_centK
  intro w hw z hz
  exact (Subgroup.mem_centralizer_iff.mp (hsup_le hw) z hz).symm

theorem Hyp76.normalizes_inf_commutator (h : Hyp76 V H E J A X) {Y : Subgroup G}
    (hYX : Y ≤ X) {U : Subgroup G} (hU : U ∈ omegaSet V H E) (hUA : U ≤ A ⊔ J) {v : G}
    (hv : v ∈ U) (hvY : v ∈ Subgroup.normalizer (Y : Set G)) :
    Y ≤ Subgroup.normalizer
        (((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
          (commOthers V H E J A Y v ⊔ iSub V H E) : Subgroup G) : Set G) ∧
      v ∈ Subgroup.normalizer
        (((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
          (commOthers V H E J A Y v ⊔ iSub V H E) : Subgroup G) : Set G) := by
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun W => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hH_N_I : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le_H h.normal_E)
  have hYH : Y ≤ H := hYX.trans h.X_le_H
  have hY_N_I : Y ≤ Subgroup.normalizer (iSub V H E : Set G) := hYH.trans hH_N_I
  have hvH : v ∈ H := h.omega_le_H U hU hv
  have hv_N_I : v ∈ Subgroup.normalizer (iSub V H E : Set G) := hH_N_I hvH
  have hY_N_B : Y ≤ Subgroup.normalizer (commOthers V H E J A Y v : Set G) := by
    unfold commOthers
    refine s762_le_normalizer_iSup fun d' => ?_
    refine s762_le_normalizer_iSup fun hd' => ?_
    refine s762_le_normalizer_iSup fun hd'Y => ?_
    refine s762_le_normalizer_iSup fun hne => ?_
    exact Subgroup.normalizer_commutator_ge_left Y (Subgroup.zpowers d')
  have hv_N_B : v ∈ Subgroup.normalizer (commOthers V H E J A Y v : Set G) := by
    unfold commOthers
    refine s762_mem_normalizer_iSup fun d' => ?_
    refine s762_mem_normalizer_iSup fun hd' => ?_
    refine s762_mem_normalizer_iSup fun hd'Y => ?_
    refine s762_mem_normalizer_iSup fun hne => ?_
    obtain ⟨U', hU', hU'A, hd'U', -⟩ := hd'
    have hcomm := h.commute_of_le_sup hU hU' hUA hU'A v hv d' hd'U'
    have hv_N_z : v ∈ Subgroup.normalizer (Subgroup.zpowers d' : Set G) := by
      have hconj : (↑(MulAut.conj v) : G →* G) d' = d' := by
        change MulAut.conj v d' = d'
        rw [MulAut.conj_apply, hcomm, mul_inv_cancel_right]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers, hconj]
    exact s762_mem_normalizer_commutator hvY hv_N_z
  have hY_N_W1 : Y ≤ Subgroup.normalizer
      ((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E : Subgroup G) : Set G) :=
    (le_inf (Subgroup.normalizer_commutator_ge_left Y (Subgroup.zpowers v)) hY_N_I).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hv_N_W1 : v ∈ Subgroup.normalizer
      ((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E : Subgroup G) : Set G) :=
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)
      ⟨Subgroup.normalizer_commutator_ge_right Y (Subgroup.zpowers v)
        (Subgroup.mem_zpowers v), hv_N_I⟩
  have hY_N_W2 : Y ≤ Subgroup.normalizer
      ((commOthers V H E J A Y v ⊔ iSub V H E : Subgroup G) : Set G) :=
    (le_inf hY_N_B hY_N_I).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hv_N_W2 : v ∈ Subgroup.normalizer
      ((commOthers V H E J A Y v ⊔ iSub V H E : Subgroup G) : Set G) :=
    (Subgroup.inf_normalizer_le_normalizer_sup _ _) ⟨hv_N_B, hv_N_I⟩
  exact ⟨fun y hy => s762_mem_normalizer_inf (hY_N_W1 hy) (hY_N_W2 hy),
    s762_mem_normalizer_inf hv_N_W1 hv_N_W2⟩

theorem Hyp76.inf_commutator_le_iSub (h : Hyp76 V H E J A X)
    (hOK : CFSG.QuasithinUnique.oddCoreIn (kSub V H E) = ⊥) {Y : Subgroup G}
    (hY : IsHallCompl V H E J X Y) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hUA : U ≤ A ⊔ J) {v : G} (hv : v ∈ U) (hvJ : v ∉ J)
    (hvY : v ∈ Subgroup.normalizer (Y : Set G)) :
    (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
        (commOthers V H E J A Y v ⊔ iSub V H E) ≤ iSub V H E := by
  have hIE : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.isElemAbelian h.isTI h.isMulCommutative h.omega_le_H
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun W => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hH_N_I : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le_H h.normal_E)
  have hYI : Y ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    (hY.le_X.trans h.X_le_H).trans hH_N_I
  have hvI : v ∈ Subgroup.normalizer (iSub V H E : Set G) :=
    hH_N_I (h.omega_le_H U hU hv)
  have hYv_le_Y : ⁅Y, Subgroup.zpowers v⁆ ≤ Y := commutator_zpowers_le hvY
  have hWY : (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) ≤ Y :=
    inf_le_left.trans (sup_le hYv_le_Y hY.iSub_le)
  have hIW : iSub V H E ≤ (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) :=
    le_inf le_sup_right le_sup_right
  have hodd : Odd ((iSub V H E).relIndex ((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E))) :=
    h.relIndex_odd_of_isHallCompl hY hIW hWY
  obtain ⟨hYnormW, hvnormW⟩ := h.normalizes_inf_commutator hY.le_X hU hUA hv hvY
  have hcent : ∀ w ∈ (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E),
      ∀ z ∈ ⁅iSub V H E, Subgroup.zpowers v⁆, w * z = z * w := by
    intro w hw
    exact h.commOthers_sup_iSub_centralizes hY.le_X hU hUA hv hvJ w hw.2
  have hcommIW : (⁅iSub V H E, ((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E))⁆ : Subgroup G) = ⊥ :=
    commutator_eq_bot_of_centralizes_commutator hIE hIW hWY hYI hYnormW hodd hvI hvnormW
      inf_le_left hcent
  have hW_cent : (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) ≤
      Subgroup.centralizer (iSub V H E : Set G) := by
    rw [Subgroup.commutator_comm] at hcommIW
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommIW
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le_H
  have hH_N_K : H ≤ Subgroup.normalizer (kSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hKleH
      (kSub_subgroupOf_normal h.le_H h.normal_E h.omega_le_H)
  have hI_le_K : iSub V H E ≤ kSub V H E := iSup₂_mono fun U _ => inf_le_left
  have hYv_le_K : ⁅Y, Subgroup.zpowers v⁆ ≤ kSub V H E := by
    rw [Subgroup.commutator_le]
    intro y hy t ht
    have hyH : y ∈ H := (hY.le_X.trans h.X_le_H) hy
    have htK : t ∈ kSub V H E := (Subgroup.zpowers_le.mpr (le_kSub hU hv)) ht
    have hconj : y * t * y⁻¹ ∈ kSub V H E :=
      (Subgroup.mem_normalizer_iff.mp (hH_N_K hyH) t).mp htK
    rw [commutatorElement_def]
    exact (kSub V H E).mul_mem hconj ((kSub V H E).inv_mem htK)
  have hW_le_K : (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) ≤ kSub V H E :=
    inf_le_left.trans (sup_le hYv_le_K hI_le_K)
  have hW_le_K_cent : (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) ≤
      kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) :=
    le_inf hW_le_K hW_cent
  have hW_le_pCore : (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) ≤ pCoreOf 2 (kSub V H E) := by
    have hh := hW_le_K_cent.trans
      (seven_four h.isElemAbelian h.isTI h.isMulCommutative h.le_H h.normal_E h.omega_le_H)
    rwa [hOK, sup_bot_eq] at hh
  have hW2 : IsPGroup 2 ↥((⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)).to_le hW_le_pCore
  exact le_of_isPGroup_of_odd_relIndex hW2 hodd

theorem Hyp76.inf_iSup_commModJ_le (h : Hyp76 V H E J A X)
    (hOK : CFSG.QuasithinUnique.oddCoreIn (kSub V H E) = ⊥) {d : G}
    (hd : d ∈ dSetIn V H E J A) :
    commModJ X J d ⊓
        (⨆ d' ∈ dSetIn V H E J A, ⨆ (_ : d⁻¹ * d' ∉ J), commModJ X J d') ≤ J := by
  obtain ⟨Y, hY⟩ := h.exists_hallCompl
  have hdD : d ∈ dSetIn V H E J A := hd
  simp only [dSetIn, Set.mem_setOf_eq] at hd
  obtain ⟨Ud, hUd, hUdA, hdUd, hdJ⟩ := hd
  obtain ⟨U₀, hU₀, hU₀A, v, hvU₀, hvJ, hvY, hdvJ⟩ := h.exists_normalizing_rep hY hdD
  have hJH : J ≤ H := h.le_X.trans h.X_le_H
  have hJ_N : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.normal_J
  have hdN : d ∈ Subgroup.normalizer (J : Set G) := hJ_N (h.omega_le_H Ud hUd hdUd)
  have hvN : v ∈ Subgroup.normalizer (J : Set G) := hJ_N (h.omega_le_H U₀ hU₀ hvU₀)
  have hY_N : Y ≤ Subgroup.normalizer (J : Set G) := (hY.le_X.trans h.X_le_H).trans hJ_N
  have hcommD_eq : commModJ X J d = ⁅Y, Subgroup.zpowers v⁆ ⊔ J := by
    rw [commModJ_eq_of_mul_mem h.le_X hdN hdvJ, ← hY.sup_J, commModJ_sup_eq hY_N hvN]
  have hT_le : (⨆ d' ∈ dSetIn V H E J A, ⨆ (_ : d⁻¹ * d' ∉ J), commModJ X J d') ≤
      commOthers V H E J A Y v ⊔ J := by
    refine iSup₂_le fun d' hd' => ?_
    refine iSup_le fun hne => ?_
    obtain ⟨Ud', hUd', hUd'A, hd'Ud', hd'J'⟩ := hd'
    have hd'N : d' ∈ Subgroup.normalizer (J : Set G) :=
      hJ_N (h.omega_le_H Ud' hUd' hd'Ud')
    have hd'D : d' ∈ dSetIn V H E J A := ⟨Ud', hUd', hUd'A, hd'Ud', hd'J'⟩
    obtain ⟨U₁, hU₁, hU₁A, d'₁, hd'₁U₁, hd'₁J, hd'₁Y, hd'_inv_J⟩ :=
      h.exists_normalizing_rep hY hd'D
    have hd'₁D : d'₁ ∈ dSetIn V H E J A := ⟨U₁, hU₁, hU₁A, hd'₁U₁, hd'₁J⟩
    have hv'_ne : v⁻¹ * d'₁ ∉ J := by
      intro hmem
      apply hne
      have heq : d⁻¹ * d' = (d⁻¹ * v) * (v⁻¹ * d'₁) * (d'⁻¹ * d'₁)⁻¹ := by group
      rw [heq]
      exact J.mul_mem (J.mul_mem hdvJ hmem) (J.inv_mem hd'_inv_J)
    have hle_B : ⁅Y, Subgroup.zpowers d'₁⁆ ≤ commOthers V H E J A Y v := by
      unfold commOthers
      exact le_iSup₂_of_le d'₁ hd'₁D
        (le_iSup_of_le hd'₁Y (le_iSup_of_le hv'_ne le_rfl))
    have hd'₁N : d'₁ ∈ Subgroup.normalizer (J : Set G) :=
      hJ_N (h.omega_le_H U₁ hU₁ hd'₁U₁)
    have hcommD'₁ : commModJ X J d' = ⁅Y, Subgroup.zpowers d'₁⁆ ⊔ J := by
      rw [commModJ_eq_of_mul_mem h.le_X hd'N hd'_inv_J, ← hY.sup_J,
        commModJ_sup_eq hY_N hd'₁N]
    rw [hcommD'₁]
    exact sup_le (hle_B.trans le_sup_left) le_sup_right
  intro g hg
  have hgd : g ∈ ⁅Y, Subgroup.zpowers v⁆ ⊔ J := by
    rw [← hcommD_eq]; exact hg.1
  have hgT : g ∈ commOthers V H E J A Y v ⊔ J := hT_le hg.2
  have hYv_le_Y : ⁅Y, Subgroup.zpowers v⁆ ≤ Y := commutator_zpowers_le hvY
  have hB_le_Y : commOthers V H E J A Y v ≤ Y := by
    unfold commOthers
    refine iSup₂_le fun d' hd' => ?_
    refine iSup_le fun hd'Y => ?_
    refine iSup_le fun hne => ?_
    exact commutator_zpowers_le hd'Y
  have hP_N : ⁅Y, Subgroup.zpowers v⁆ ≤ Subgroup.normalizer (J : Set G) :=
    hYv_le_Y.trans hY_N
  have hB_N : commOthers V H E J A Y v ≤ Subgroup.normalizer (J : Set G) :=
    hB_le_Y.trans hY_N
  have hgPJ : g ∈ ((⁅Y, Subgroup.zpowers v⁆ : Subgroup G) : Set G) * (J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (⁅Y, Subgroup.zpowers v⁆) J hP_N]
    exact hgd
  have hgBJ : g ∈ (commOthers V H E J A Y v : Set G) * (J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (commOthers V H E J A Y v) J hB_N]
    exact hgT
  obtain ⟨p, hpP, j, hjJ, hpj⟩ := Set.mem_mul.mp hgPJ
  obtain ⟨b, hbB, j', hj'J, hbj'⟩ := Set.mem_mul.mp hgBJ
  have hb'p_Y : b⁻¹ * p ∈ Y := Y.mul_mem (Y.inv_mem (hB_le_Y hbB)) (hYv_le_Y hpP)
  have hb'p_eq : b⁻¹ * p = j' * j⁻¹ := by
    have h1 : (b⁻¹ * p) * j = j' := by
      rw [mul_assoc, show p * j = b * j' by rw [hpj, hbj'], inv_mul_cancel_left]
    rwa [eq_mul_inv_iff_mul_eq]
  have hb'p_J : b⁻¹ * p ∈ J := by
    rw [hb'p_eq]; exact J.mul_mem hj'J (J.inv_mem hjJ)
  have hb'p_I : b⁻¹ * p ∈ iSub V H E := by
    rw [← hY.inf_J]; exact ⟨hb'p_Y, hb'p_J⟩
  have hp_inf : p ∈ (⁅Y, Subgroup.zpowers v⁆ ⊔ iSub V H E) ⊓
      (commOthers V H E J A Y v ⊔ iSub V H E) := by
    refine ⟨Subgroup.mem_sup_left hpP, ?_⟩
    have hp_eq : p = b * (b⁻¹ * p) := by group
    rw [hp_eq]
    exact (commOthers V H E J A Y v ⊔ iSub V H E).mul_mem (Subgroup.mem_sup_left hbB)
      (Subgroup.mem_sup_right hb'p_I)
  have hp_I : p ∈ iSub V H E :=
    h.inf_commutator_le_iSub hOK hY hU₀ hU₀A hvU₀ hvJ hvY hp_inf
  rw [← hpj]
  exact J.mul_mem (h.iSub_le hp_I) hjJ

end CFSG.LocalAnalysis.WeakClosure81
