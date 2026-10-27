module

public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.WeakClosure81.W16POneMod
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem isPGroup_two_closure_of_inv_mul {X : Type*} [Group X]
    {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (ht : IsPGroup 2 (Subgroup.zpowers (a * b))) :
    IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hat : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    calc a * (a * b) * a⁻¹ = a * (a * b) * a := by rw [hai]
      _ = (a * a) * (b * a) := by group
      _ = b * a := by rw [ha, one_mul]
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, hbi, hai]
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := by
    have hdvd : orderOf a ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact ha)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).1 (by simpa using hdvd)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hnorm : Subgroup.zpowers a ≤
      Subgroup.normalizer (Subgroup.zpowers (a * b) : Set X) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * (a * b) * a⁻¹) = Subgroup.zpowers (a * b)
    rw [hat, Subgroup.zpowers_inv]
  have hsup := IsPGroup.to_sup_of_normal_right' ha2 ht hnorm
  have hsup_eq : Subgroup.zpowers a ⊔ Subgroup.zpowers (a * b) =
      Subgroup.closure ({a, b} : Set X) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      · refine Subgroup.zpowers_le.mpr ?_
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hxa | hxb
      · rw [hxa]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · rw [Set.mem_singleton_iff] at hxb
        rw [hxb]
        have hb_mem : a⁻¹ * (a * b) ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers (a * b) :=
          Subgroup.mul_mem _
            (Subgroup.mem_sup_left ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers (a * b)))
        rwa [show a⁻¹ * (a * b) = b by group] at hb_mem
  rwa [hsup_eq] at hsup

theorem Cex16.inf_pCore_iSub16 (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {v : G} (hv : v ∈ V)
    (hvO : D.ρ ⟨v, h.V_le_S.trans hF.1 hv⟩ ∈ pCoreOf 2 (D.img H)) :
    v ∈ Subgroup.centralizer (iSub16 V H : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV_le_H : V ≤ H := h.V_le_S.trans hF.1
  let aH : ↥H := ⟨v, hV_le_H hv⟩
  have ha2 : aH * aH = 1 := by
    apply Subtype.ext
    show v * v = 1
    rw [← pow_two]
    exact h.hyp.h6.elemAbelian.2 v hv
  have hV0_le_I : V₀ ≤ iSub16 V H :=
    (le_inf h.hyp.h6.le (Cex16.V₀_le_pCoreOf h5 hS h hF hV)).trans
      (CFSG.Quasithin.le_conjClosure _ _)
  have key : ∀ g : ↥H, IsPGroup 2 (Subgroup.zpowers (aH * (g * aH * g⁻¹))) := by
    intro g
    set bH : ↥H := g * aH * g⁻¹
    set tH : ↥H := aH * bH
    have hρa : D.ρ aH ∈ pCoreOf 2 (D.img H) := hvO
    have hρb : D.ρ bH ∈ pCoreOf 2 (D.img H) := by
      rw [show bH = g * aH * g⁻¹ from rfl, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (D.img H)
          (D.mem_img.2 ⟨g, g.2, rfl⟩)) (D.ρ aH)).1 hρa
    have hρt : D.ρ tH ∈ pCoreOf 2 (D.img H) := by
      rw [show tH = aH * bH from rfl, map_mul]
      exact (pCoreOf 2 (D.img H)).mul_mem hρa hρb
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (D.img H))) ⟨D.ρ tH, hρt⟩
    have he' : orderOf (D.ρ tH) = 2 ^ e := by
      rw [← he]
      exact Subgroup.orderOf_coe (⟨D.ρ tH, hρt⟩ : pCoreOf 2 (D.img H))
    obtain ⟨k, m, hm_odd, ht_eq⟩ :=
      Nat.exists_eq_two_pow_mul_odd (orderOf_pos tH).ne'
    have he_dvd : 2 ^ e ∣ 2 ^ k * m := by
      rw [← ht_eq, ← he']
      exact orderOf_map_dvd D.ρ tH
    have hek : e ≤ k := by
      have hcop : Nat.Coprime (2 ^ e) m := (Nat.coprime_two_left.mpr hm_odd).pow_left e
      have h2 : 2 ^ e ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right he_dvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
    have hρy : D.ρ (tH ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp (he' ▸ pow_dvd_pow 2 hek)
    let yG : G := ((tH ^ 2 ^ k : ↥H) : G)
    have hy_ker : yG ∈ Subgroup.centralizer (iSub16 V H : Set G) :=
      (D.ρ_eq_one_iff (tH ^ 2 ^ k)).1 hρy
    have hy_pow_m : (tH ^ 2 ^ k) ^ m = 1 := by
      rw [← pow_mul, ← ht_eq, pow_orderOf_eq_one]
    have hb2 : bH * bH = 1 := by
      rw [show bH = g * aH * g⁻¹ from rfl,
        show g * aH * g⁻¹ * (g * aH * g⁻¹) = g * (aH * aH) * g⁻¹ by group, ha2]
      group
    have hat : aH * tH * aH⁻¹ = tH⁻¹ := by
      have h1 : aH⁻¹ = aH := inv_eq_of_mul_eq_one_right ha2
      have h2 : bH⁻¹ = bH := inv_eq_of_mul_eq_one_right hb2
      calc aH * tH * aH⁻¹ = aH * (aH * bH) * aH := by rw [show tH = aH * bH from rfl, h1]
        _ = (aH * aH) * (bH * aH) := by group
        _ = bH * aH := by rw [ha2, one_mul]
        _ = (aH * bH)⁻¹ := by rw [mul_inv_rev, h2, h1]
        _ = tH⁻¹ := by rw [show tH = aH * bH from rfl]
    have hay : aH * (tH ^ 2 ^ k) * aH⁻¹ = (tH ^ 2 ^ k)⁻¹ := by
      rw [← conj_pow (a := aH) (b := tH) (i := 2 ^ k), hat, inv_pow]
    have hayG : (aH : G) * yG * (aH : G)⁻¹ = yG⁻¹ := by
      have := congrArg (fun z : ↥H => (z : G)) hay
      simpa [yG] using this
    have hy_normV : yG ∈ Subgroup.normalizer (V : Set G) := by
      have hy_cV0 : yG ∈ Subgroup.centralizer (V₀ : Set G) :=
        Subgroup.centralizer_le hV0_le_I hy_ker
      have hM : yG ∈ M := by
        rw [← h.hyp.normalizer₀]
        exact Subgroup.centralizer_le_normalizer (V₀ : Set G) hy_cV0
      rwa [← h.hyp.h6.normalizer_eq] at hM
    have hy_sq_V : yG ^ 2 ∈ V := by
      have hmem : (aH : G) * (yG * (aH : G)⁻¹ * yG⁻¹) ∈ V :=
        V.mul_mem hv ((Subgroup.mem_normalizer_iff.1 hy_normV (aH : G)⁻¹).1 (V.inv_mem hv))
      have heq : (aH : G) * (yG * (aH : G)⁻¹ * yG⁻¹) = (yG ^ 2)⁻¹ := by
        rw [show (aH : G) * (yG * (aH : G)⁻¹ * yG⁻¹) =
          (aH : G) * yG * (aH : G)⁻¹ * yG⁻¹ by group, hayG]
        group
      rw [heq] at hmem
      simpa using V.inv_mem hmem
    have hy_pow_m_G : yG ^ m = 1 := by
      have := congrArg (fun z : ↥H => (z : G)) hy_pow_m
      simpa [yG] using this
    have hodd_yG : Odd (orderOf yG) :=
      hm_odd.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hy_pow_m_G)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 h.hyp.isPGroup) ⟨yG ^ 2, hy_sq_V⟩
    have hj' : orderOf (yG ^ 2) = 2 ^ j := by
      rw [← hj]
      exact Subgroup.orderOf_coe (⟨yG ^ 2, hy_sq_V⟩ : V)
    have h2j_dvd_m' : 2 ^ j ∣ m := by
      rw [← hj']
      exact (orderOf_pow_dvd (x := yG) 2).trans (orderOf_dvd_iff_pow_eq_one.mpr hy_pow_m_G)
    have hj0 : j = 0 := by
      by_contra hjne
      exact (Nat.not_even_iff_odd.mpr hm_odd)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hjne).trans h2j_dvd_m'))
    have hy_sq_one : yG ^ 2 = 1 := by
      rw [← orderOf_eq_one_iff, hj', hj0, pow_zero]
    have hyG_one : yG = 1 := by
      have hdvd2 : orderOf yG ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr hy_sq_one
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        obtain ⟨t, ht⟩ := h2 ▸ hodd_yG
        omega
    have ht_pow_one : tH ^ 2 ^ k = 1 := by
      apply Subtype.ext
      exact hyG_one
    have ht_order_dvd : orderOf tH ∣ 2 ^ k :=
      orderOf_dvd_iff_pow_eq_one.mpr ht_pow_one
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := k)).1 ht_order_dvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hcore : aH ∈ pCore 2 ↥H := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    have hb2 : (g * aH * g⁻¹) * (g * aH * g⁻¹) = 1 := by
      rw [show g * aH * g⁻¹ * (g * aH * g⁻¹) = g * (aH * aH) * g⁻¹ by group, ha2]
      group
    exact isPGroup_two_closure_of_inv_mul ha2 hb2 (key g)
  have hv_pcore : v ∈ pCoreOf 2 H :=
    Subgroup.mem_map.mpr ⟨aH, hcore, rfl⟩
  have hvI : v ∈ iSub16 V H :=
    CFSG.Quasithin.le_conjClosure _ _ ⟨hv, hv_pcore⟩
  refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
  exact B2F.isElemAbelian_comm (Cex16.isElemAbelian_iSub16 h1 hS h hF) hi hvI

theorem Cex16.assumption131_iSub16 (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    Assumption131 (D.img H) (D.conjImgFam V) (D.conjImgSpace V₀ V) (mRank (D.img V)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Subgroup G := iSub16 V H
  have hE : IsElemAbelian 2 I := Cex16.isElemAbelian_iSub16 h1 hS h hF
  have hI_le : I ≤ pCoreOf 2 H := Cex16.iSub16_le_pCoreOf h hF
  have hI_le_S : I ≤ S := hI_le.trans (h.pCoreOf_le_S h1 hS hF)
  have hV_le_H : V ≤ H := h.V_le_S.trans hF.1
  have hV0_le_V : V₀ ≤ V := h.hyp.h6.le
  have hV0_le_O : V₀ ≤ pCoreOf 2 H := Cex16.V₀_le_pCoreOf h5 hS h hF hV
  have hV0_le_I : V₀ ≤ I :=
    (le_inf hV0_le_V hV0_le_O).trans (CFSG.Quasithin.le_conjClosure _ _)
  have hV0_ne : V₀ ≠ ⊥ := h.hyp.ne_bot
  have hU_le : U ≤ pCoreOf 2 H := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le.trans hV_le_H) ?_
      (B2F.isPGroup_of_isElemAbelian (h.hyp.h6.elemAbelian.mono h.le))
    exact hF.2.1.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hcommI_V : ⁅I, V⁆ ≤ V₀ :=
    (Subgroup.commutator_mono hI_le_S le_rfl).trans
      (Subgroup.commutator_le.mpr fun s hs v hv => h.comm_mem_V₀ hs hv)
  have hVnt : D.img V ≠ ⊥ := by
    intro hbot
    have hVcent : V ≤ Subgroup.centralizer (I : Set G) :=
      D.le_centralizer_of_img_eq_bot hV_le_H hbot
    have hVeq : V = U ⊔ V₀ := by
      rw [← Cex16.inf_centralizer_iSub16_eq h1 h5 hS h hF hV]
      exact le_antisymm (le_inf le_rfl hVcent) inf_le_left
    exact hV (hVeq ▸ sup_le hU_le hV0_le_O)
  have hcardV : 1 < Nat.card (D.img V) := by
    have hne1 : Nat.card (D.img V) ≠ 1 := fun hc => hVnt (Subgroup.card_eq_one.mp hc)
    have hpos : 0 < Nat.card (D.img V) := Nat.card_pos
    omega
  have hconj_le : ∀ x ∈ H, conjSubgroup V x ≤ H := by
    intro x hxH y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 : x * y * x⁻¹ ∈ H := hV_le_H hy
    rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group]
    exact H.mul_mem (H.mul_mem (H.inv_mem hxH) h1) hxH
  have hEab_conj : ∀ x ∈ H, IsElemAbelian 2 (conjSubgroup V x) := by
    intro x _
    simpa [conjSubgroup] using h.hyp.h6.elemAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hI_norm : ∀ x ∈ H, x ∈ Subgroup.normalizer (I : Set G) :=
    fun x hxH => CFSG.Quasithin.le_normalizer_conjClosure _ _ hxH
  have hcomm_conj : ∀ x ∈ H, ⁅I, conjSubgroup V x⁆ = conjSubgroup ⁅I, V⁆ x := by
    intro x hxH
    have hI_map : I.map (MulAut.conj x⁻¹).toMonoidHom = I :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hI_norm x hxH)
    calc ⁅I, conjSubgroup V x⁆
        = ⁅I.map (MulAut.conj x⁻¹).toMonoidHom,
            V.map (MulAut.conj x⁻¹).toMonoidHom⁆ := by
            rw [hI_map]; rfl
      _ = (⁅I, V⁆).map (MulAut.conj x⁻¹).toMonoidHom :=
            (Subgroup.map_commutator (H₁ := I) (H₂ := V)
              (MulAut.conj x⁻¹).toMonoidHom).symm
      _ = conjSubgroup ⁅I, V⁆ x := rfl
  have hsingle : ∀ {x y : G}, x ∈ H → y ∈ H →
      D.img (conjSubgroup V x) = D.img (conjSubgroup V y) →
      conjSubgroup V₀ x = conjSubgroup V₀ y := by
    intro x y hxH hyH hxy
    have hD0_ne : ⁅I, V⁆ ≠ ⊥ := by
      intro hbot
      apply hVnt
      have hVcent : V ≤ Subgroup.centralizer (I : Set G) := by
        have hVI : ⁅V, I⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hbot
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVI
      rw [eq_bot_iff]
      intro r hr
      obtain ⟨j, hj, rfl⟩ := D.mem_img.1 hr
      rw [Subgroup.mem_bot]
      exact (D.ρ_eq_one_iff j).2 (hVcent hj)
    have hcomm_eq : ⁅I, conjSubgroup V x⁆ = ⁅I, conjSubgroup V y⁆ := by
      apply le_antisymm <;> intro e he
      · have heI : e ∈ I := D.commutator_le_E (hconj_le x hxH) he
        have hmem : D.ι e ∈ commSub (D.img (conjSubgroup V y)) := by
          rw [← hxy]
          exact (D.mem_commSub_img_iff (hconj_le x hxH) heI).2 he
        exact (D.mem_commSub_img_iff (hconj_le y hyH) heI).1 hmem
      · have heI : e ∈ I := D.commutator_le_E (hconj_le y hyH) he
        have hmem : D.ι e ∈ commSub (D.img (conjSubgroup V x)) := by
          rw [hxy]
          exact (D.mem_commSub_img_iff (hconj_le y hyH) heI).2 he
        exact (D.mem_commSub_img_iff (hconj_le x hxH) heI).1 hmem
    have hDconj : conjSubgroup ⁅I, V⁆ x = conjSubgroup ⁅I, V⁆ y := by
      rw [← hcomm_conj x hxH, ← hcomm_conj y hyH, hcomm_eq]
    obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD0_ne
    have hd : (d : G) ∈ ⁅I, V⁆ := d.2
    have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hdx_mem : x⁻¹ * (d : G) * x ∈ conjSubgroup ⁅I, V⁆ x := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hd
    have hdx_mem_y : x⁻¹ * (d : G) * x ∈ conjSubgroup ⁅I, V⁆ y := hDconj ▸ hdx_mem
    have hdx_ne : x⁻¹ * (d : G) * x ≠ 1 := by
      intro h
      apply hd1'
      have := congrArg (fun z => x * z * x⁻¹) h
      simpa [mul_assoc] using this
    have hle_x : conjSubgroup ⁅I, V⁆ x ≤ conjSubgroup V₀ x := Subgroup.map_mono hcommI_V
    have hle_y : conjSubgroup ⁅I, V⁆ x ≤ conjSubgroup V₀ y := by
      rw [hDconj]; exact Subgroup.map_mono hcommI_V
    have hinf_ne : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y ≠ ⊥ := by
      intro hbot
      exact hdx_ne (Subgroup.mem_bot.1 (hbot ▸ (le_inf hle_x hle_y hdx_mem)))
    have hyxM : y * x⁻¹ ∈ M := by
      by_contra hg
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinf_ne
      have hw : (w : G) ∈ conjSubgroup V₀ x ⊓ conjSubgroup V₀ y := w.2
      have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
      have hwx : x * (w : G) * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw.1
      have hwy : y * (w : G) * y⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw.2
      have hwv : x * (w : G) * x⁻¹ ∈ conjSubgroup V₀ (y * x⁻¹) := by
        rw [mem_conjSubgroup_iff]
        rw [show (y * x⁻¹) * (x * (w : G) * x⁻¹) * (y * x⁻¹)⁻¹ = y * (w : G) * y⁻¹ by
          group]
        exact hwy
      have hwx_ne : x * (w : G) * x⁻¹ ≠ 1 := by
        intro h
        apply hw1'
        have := congrArg (fun z => x⁻¹ * z * x) h
        simpa [mul_assoc] using this
      have hne : V₀ ⊓ conjSubgroup V₀ (y * x⁻¹) ≠ ⊥ := by
        intro hbot
        exact hwx_ne (Subgroup.mem_bot.1 (hbot ▸ ⟨hwx, hwv⟩))
      exact hne (by rw [inf_comm]; exact h.hyp.conj_inf_eq_bot hg)
    have hV0_eq : conjSubgroup V₀ (y * x⁻¹) = V₀ :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp.normalizer₀ ▸ hyxM)
    have h := conjSubgroup_conjSubgroup V₀ (y * x⁻¹) x
    rw [show y * x⁻¹ * x = y by group] at h
    rw [hV0_eq] at h
    exact h
  have hVA_eq : ∀ (z : G), z ∈ H →
      D.conjImgSpace V₀ V (D.img (conjSubgroup V z)) = D.sp (conjSubgroup V₀ z) := by
    intro z hzH
    rw [ModDataE.conjImgSpace]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      rintro ⟨w, hwH, hwEq⟩
      rw [hsingle hwH hzH hwEq]
    · exact le_iSup (fun w : {w : G // w ∈ H ∧
        D.img (conjSubgroup V w) = D.img (conjSubgroup V z)} => D.sp (conjSubgroup V₀ w.1))
        ⟨z, hzH, rfl⟩
  have hVA_ne : ∀ A ∈ D.conjImgFam V, D.conjImgSpace V₀ V A ≠ ⊥ := by
    rintro A ⟨z, hzH, rfl⟩
    rw [hVA_eq z hzH]
    intro hbot
    have hinf : conjSubgroup V₀ z ⊓ I = ⊥ := D.sp_eq_bot_iff.mp hbot
    have hV0z_le : conjSubgroup V₀ z ≤ I := by
      calc conjSubgroup V₀ z ≤ conjSubgroup I z := Subgroup.map_mono hV0_le_I
        _ = I := conjSubgroup_eq_iff_mem_normalizer.mpr (hI_norm z hzH)
    have hV0z_eq : conjSubgroup V₀ z = ⊥ := by
      apply le_bot_iff.mp
      calc conjSubgroup V₀ z ≤ conjSubgroup V₀ z ⊓ I := le_inf le_rfl hV0z_le
        _ = ⊥ := hinf
    apply hV0_ne
    have h := conjSubgroup_conjSubgroup V₀ z z⁻¹
    rw [hV0z_eq, mul_inv_cancel, conjSubgroup_one] at h
    simpa [conjSubgroup] using h.symm
  have hinv : ∀ A ∈ D.conjImgFam V, ∀ g ∈ D.img H, cj g A ∈ D.conjImgFam V := by
    rintro A ⟨x, hxH, rfl⟩ g hg
    obtain ⟨y, hyH, rfl⟩ := D.mem_img.1 hg
    refine ⟨x * (y : G)⁻¹, H.mul_mem hxH (H.inv_mem y.2), ?_⟩
    rw [D.img_conj (hconj_le x hxH) y, conjSubgroup_conjSubgroup]
  have hequiv : ∀ A ∈ D.conjImgFam V, ∀ g ∈ D.img H,
      D.conjImgSpace V₀ V (cj g A) = conjSub g (D.conjImgSpace V₀ V A) := by
    rintro A ⟨x, hxH, rfl⟩ g hg
    obtain ⟨y, hyH, rfl⟩ := D.mem_img.1 hg
    rw [D.img_conj (hconj_le x hxH) y, conjSubgroup_conjSubgroup,
      hVA_eq (x * (y : G)⁻¹) (H.mul_mem hxH (H.inv_mem y.2)), hVA_eq x hxH,
      D.conjSub_sp (conjSubgroup V₀ x) y, conjSubgroup_conjSubgroup]
  have hdisj : ∀ A ∈ D.conjImgFam V, ∀ B ∈ D.conjImgFam V, A ≠ B →
      D.conjImgSpace V₀ V A ⊓ D.conjImgSpace V₀ V B = ⊥ := by
    rintro A ⟨x, hxH, rfl⟩ B ⟨y, hyH, rfl⟩ hne
    have hbot : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y = ⊥ := by
      by_contra hinf_ne
      have hyxM : y * x⁻¹ ∈ M := by
        by_contra hg
        obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinf_ne
        have hw : (w : G) ∈ conjSubgroup V₀ x ⊓ conjSubgroup V₀ y := w.2
        have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
        have hwx : x * (w : G) * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw.1
        have hwy : y * (w : G) * y⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw.2
        have hwv : x * (w : G) * x⁻¹ ∈ conjSubgroup V₀ (y * x⁻¹) := by
          rw [mem_conjSubgroup_iff]
          rw [show (y * x⁻¹) * (x * (w : G) * x⁻¹) * (y * x⁻¹)⁻¹ = y * (w : G) * y⁻¹ by
            group]
          exact hwy
        have hwx_ne : x * (w : G) * x⁻¹ ≠ 1 := by
          intro h
          apply hw1'
          have := congrArg (fun z => x⁻¹ * z * x) h
          simpa [mul_assoc] using this
        have hne : V₀ ⊓ conjSubgroup V₀ (y * x⁻¹) ≠ ⊥ := by
          intro hbot
          exact hwx_ne (Subgroup.mem_bot.1 (hbot ▸ ⟨hwx, hwv⟩))
        exact hne (by rw [inf_comm]; exact h.hyp.conj_inf_eq_bot hg)
      have hVeq : conjSubgroup V x = conjSubgroup V y := by
        have hc : conjSubgroup V (y * x⁻¹) = V :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp.h6.normalizer_eq ▸ hyxM)
        have h := conjSubgroup_conjSubgroup V (y * x⁻¹) x
        rw [show y * x⁻¹ * x = y by group] at h
        rw [hc] at h
        exact h
      exact hne (by rw [hVeq])
    rw [hVA_eq x hxH, hVA_eq y hyH, ← D.sp_inf, hbot]
    exact D.sp_eq_bot_iff.2 (by simp)
  refine
    { pos_i := ?_
      le_G := ?_
      isElemAb := ?_
      invariant := hinv
      ne_bot := ?_
      inf_pCore := ?_
      normalizer_eq := ?_
      disjoint := hdisj
      cond2 := ?_
      quadratic := ?_
      equivariant := hequiv }
  · show 0 < mRank (D.img V)
    rw [mRank]
    exact Nat.log_pos (by norm_num) (by omega)
  · rintro A ⟨x, hxH, rfl⟩
    exact D.img_mono (hconj_le x hxH)
  · rintro A ⟨x, hxH, rfl⟩
    exact D.isElemAbelian_img (hEab_conj x hxH)
  · rintro A ⟨x, hxH, rfl⟩ hbot
    have hcard : Nat.card (D.img (conjSubgroup V x)) = Nat.card (D.img V) := by
      have h1 := D.img_conj hV_le_H (⟨x⁻¹, H.inv_mem hxH⟩ : ↥H)
      rw [inv_inv] at h1
      rw [← h1]
      exact card_cj (A := D.img V) (D.ρ (⟨x⁻¹, H.inv_mem hxH⟩ : ↥H))
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  · rintro A ⟨x, hxH, rfl⟩
    rw [eq_bot_iff]
    rintro a ⟨haA, haO⟩
    rw [Subgroup.mem_bot]
    obtain ⟨j, hjVx, rfl⟩ := D.mem_img.1 haA
    set v : G := x * (j : G) * x⁻¹ with hv
    have hvV : v ∈ V := mem_conjSubgroup_iff.mp hjVx
    have hxjH : (⟨v, hV_le_H hvV⟩ : ↥H) = ⟨x, hxH⟩ * j * ⟨x, hxH⟩⁻¹ := by
      ext; simp [hv]
    have hv_eq : D.ρ ⟨v, hV_le_H hvV⟩ =
        D.ρ (⟨x, hxH⟩ : ↥H) * D.ρ j * (D.ρ (⟨x, hxH⟩ : ↥H))⁻¹ := by
      rw [hxjH, map_mul, map_mul, map_inv]
    have hx_img : D.ρ (⟨x, hxH⟩ : ↥H) ∈ D.img H :=
      D.mem_img.2 ⟨⟨x, hxH⟩, hxH, rfl⟩
    have hvO : D.ρ ⟨v, hV_le_H hvV⟩ ∈ pCoreOf 2 (D.img H) := by
      rw [hv_eq]
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (D.img H) hx_img) (D.ρ j)).1 haO
    have hvC : v ∈ Subgroup.centralizer (I : Set G) :=
      Cex16.inf_pCore_iSub16 h1 h5 hS h hF hV D hvV hvO
    have hvρ : D.ρ ⟨v, hV_le_H hvV⟩ = 1 :=
      (D.ρ_eq_one_iff ⟨v, hV_le_H hvV⟩).2 hvC
    have : D.ρ j = (D.ρ (⟨x, hxH⟩ : ↥H))⁻¹ * D.ρ ⟨v, hV_le_H hvV⟩ *
        D.ρ (⟨x, hxH⟩ : ↥H) := by
      rw [hv_eq]; group
    rw [this, hvρ]; group
  · rintro A ⟨x, hxH, rfl⟩
    ext g
    constructor
    · rintro ⟨hgG, hgN⟩
      refine ⟨hgG, ?_⟩
      have hcj : cj g (D.img (conjSubgroup V x)) = D.img (conjSubgroup V x) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
      have h := hequiv (D.img (conjSubgroup V x)) ⟨x, hxH, rfl⟩ g hgG
      rw [hcj] at h
      exact h.symm
    · rintro ⟨hgG, hgS⟩
      refine ⟨hgG, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
      by_contra hne
      have hmem : cj g (D.img (conjSubgroup V x)) ∈ D.conjImgFam V :=
        hinv (D.img (conjSubgroup V x)) ⟨x, hxH, rfl⟩ g hgG
      have hdis := hdisj (D.img (conjSubgroup V x)) ⟨x, hxH, rfl⟩
        (cj g (D.img (conjSubgroup V x))) hmem (Ne.symm hne)
      have hVAg : D.conjImgSpace V₀ V (cj g (D.img (conjSubgroup V x))) =
          D.conjImgSpace V₀ V (D.img (conjSubgroup V x)) := by
        rw [hequiv (D.img (conjSubgroup V x)) ⟨x, hxH, rfl⟩ g hgG, hgS]
      rw [hVAg, inf_idem] at hdis
      exact hVA_ne (D.img (conjSubgroup V x)) ⟨x, hxH, rfl⟩ hdis
  · rintro A ⟨x, hxH, rfl⟩ B hBA _
    obtain ⟨B₀, hB₀Vx, -, hB₀img⟩ :=
      D.exists_preimage (A := conjSubgroup V x) (hconj_le x hxH) (B' := B) hBA
    have hB₀_le_H : B₀ ≤ H := hB₀Vx.trans (hconj_le x hxH)
    have h1 : ⁅I, conjSubgroup V x⁆ ≤ conjSubgroup V₀ x := by
      rw [hcomm_conj x hxH]
      exact Subgroup.map_mono hcommI_V
    rw [hVA_eq x hxH, ← hB₀img, D.fixSub_img hB₀_le_H]
    refine D.commSpace_img_sp_le (hconj_le x hxH) ?_
    exact (Subgroup.commutator_mono inf_le_right le_rfl).trans h1
  · rintro A ⟨x, hxH, rfl⟩
    refine D.commSpace_commSub_img_eq_bot (hconj_le x hxH) ?_
    have hEabx : IsElemAbelian 2 (conjSubgroup V x) := hEab_conj x hxH
    have h2 : ⁅conjSubgroup V₀ x, conjSubgroup V x⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (B2F.isElemAbelian_comm hEabx (Subgroup.map_mono hV0_le_V ha) hb).symm
    exact le_bot_iff.mp ((Subgroup.commutator_mono
      (by rw [hcomm_conj x hxH]; exact Subgroup.map_mono hcommI_V)
      le_rfl).trans (le_of_eq h2))

theorem Cex16.mRank_le_iSub16 (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ B ∈ D.conjImgFam V, mRank B ≤ mRank (D.img V) := by
  rintro B ⟨x, hxH, rfl⟩
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hconj := D.img_conj hVH (⟨x⁻¹, H.inv_mem hxH⟩ : ↥H)
  rw [inv_inv] at hconj
  rw [← hconj]
  simp only [mRank, card_cj]
  exact le_refl _

theorem Cex16.conjImgSpace_le_fixSub_iSub16 (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ B ∈ D.conjImgFam V, D.conjImgSpace V₀ V B ≤ fixSub B := by
  rintro B ⟨x, hxH, rfl⟩
  rw [ModDataE.conjImgSpace]
  refine iSup_le ?_
  rintro ⟨y, hyH, hyEq⟩
  intro w hw b hb
  rw [ModDataE.mem_sp] at hw
  obtain ⟨e, ⟨heV₀y, heI⟩, rfl⟩ := hw
  have hb' : b ∈ D.img (conjSubgroup V y) := hyEq ▸ hb
  obtain ⟨j, hjVy, rfl⟩ := D.mem_img.1 hb'
  rw [D.ρ_ι j e heI]
  congr 1
  have heVy : e ∈ conjSubgroup V y := Subgroup.map_mono h.hyp.h6.le heV₀y
  have hEab : IsElemAbelian 2 (conjSubgroup V y) := by
    simpa [conjSubgroup] using h.hyp.h6.elemAbelian.map (MulAut.conj y⁻¹).toMonoidHom
  exact mul_inv_eq_iff_eq_mul.mpr (B2F.isElemAbelian_comm hEab hjVy heVy)


end CFSG.LocalAnalysis.WeakClosure81

end
