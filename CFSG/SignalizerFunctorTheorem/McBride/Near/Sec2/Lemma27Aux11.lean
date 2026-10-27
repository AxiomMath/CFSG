module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux10
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux6
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux9

public section

open CFSG.Open
open scoped Pointwise
open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type u} [Group Γ]

theorem qmap_commute_of_commutator_mem {V : Subgroup Γ} {c y : ↥(nrm V)}
    (h : ⁅(c : Γ), (y : Γ)⁆ ∈ V) : qmap V c * qmap V y = qmap V y * qmap V c := by
  have h1 : qmap V ⁅c, y⁆ = 1 := (qmap_eq_one_iff V _).mpr h
  have h2 : qmap V ⁅c, y⁆ = ⁅qmap V c, qmap V y⁆ := by
    simp [commutatorElement_def]
  rw [h2, commutatorElement_def] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

variable [Finite Γ]

theorem cyc_of_quotient {p : ℕ} {A X V V₁ : Subgroup Γ} (hA : IsElemAbelian p A)
    (hAX : Admits A X) (hV₁X : V₁ ≤ X) (hXA : X ⊔ A ≤ nrm V) (hV₁ : IsNormalIn V₁ (X ⊔ A))
    (hH : ChiefCyclic p X) (hVX : V ≤ X)
    {J : Subgroup (QG V)} (hJ : J ∈ lcal (qimg V V₁)) :
    ∃ n ∈ qimg V A, qimg V A ⊓ Subgroup.normalizer (J : Set (QG V)) ≤
      (qimg V A ⊓ Subgroup.centralizer (orbitClosure J (qimg V A) : Set (QG V))) ⊔
        Subgroup.zpowers n := by
  have hXV : X ≤ nrm V := le_sup_left.trans hXA
  have hAV : A ≤ nrm V := le_sup_right.trans hXA
  have hXV₁ : X ≤ Subgroup.normalizer (V₁ : Set Γ) := le_sup_left.trans hV₁.2
  have hR'X' : qimg V V₁ ≤ qimg V X := qimg_mono V hV₁X
  have hX'R' : qimg V X ≤ Subgroup.normalizer ((qimg V V₁ : Subgroup (QG V)) : Set (QG V)) :=
    qimg_le_normalizer hXV₁
  have hA'X' : qimg V A ≤ Subgroup.normalizer ((qimg V X : Subgroup (QG V)) : Set (QG V)) :=
    qimg_le_normalizer hAX
  set M' := orbitClosure J (qimg V X) with hM'
  have hCFM : IsChiefFactorOf (qimg V X) M' ⊥ :=
    isChiefFactorOf_orbitClosure hR'X' hX'R' hJ
  have hCF : IsChiefFactorOf X (qpre V M') V := by
    have := isChiefFactorOf_qpre hVX hXV hCFM
    rwa [qpre_bot] at this
  set M := qpre V M' with hM
  have hVM : V ≤ M := le_qpre V M'
  have hMX : M ≤ X := hCF.2.1.1
  have hnorm : (V.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr (hMX.trans hXV)
  set D' := qimg V A ⊓ Subgroup.normalizer (J : Set (QG V)) with hD'
  set D := A ⊓ qpre V D' with hD
  have hDA : D ≤ A := inf_le_left
  have hDM : D ≤ Subgroup.normalizer (M : Set Γ) := by
    intro a ha
    obtain ⟨haA, hap⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hn, hq⟩ := mem_qpre_iff.mp hap
    refine mem_nrm_of_qmap_normalizer (hAV haA) ?_
    exact mem_normalizer_orbitClosure_of_normalizer (Subgroup.mem_inf.mp hq).2
      (hA'X' (Subgroup.mem_inf.mp hq).1)
  obtain ⟨n, hnD, hn⟩ := exists_cyclic_acting hVM hA hDA hDM (fun a ha => hAV (hDA ha))
    (hH M V hCF)
  refine ⟨qmap V ⟨n, hAV (hDA hnD)⟩, mem_qimg_of_mem (hDA hnD) _, fun d' hd' => ?_⟩
  obtain ⟨hd'A, hd'J⟩ := Subgroup.mem_inf.mp hd'
  obtain ⟨y, hyA, rfl⟩ := (mem_qimg_iff V A d').mp hd'A
  have hyD : (y : Γ) ∈ D := ⟨hyA, mem_qpre_iff.mpr ⟨y.2, hd'⟩⟩
  have hcomm : ∀ x ∈ D ⊓ sectionCentralizer V M, ∀ z ∈ Subgroup.zpowers n, Commute x z :=
    fun x hx z hz => commute_of_mem hA.1 (hDA (Subgroup.mem_inf.mp hx).1)
      ((Subgroup.zpowers_le.mpr (hDA hnD)) hz)
  obtain ⟨c, hc, zz, hzz, hczz⟩ := (mem_sup_iff_of_commute hcomm).mp (hn hyD)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzz
  obtain ⟨hcD, hcS⟩ := Subgroup.mem_inf.mp hc
  have hcA : c ∈ A := hDA hcD
  have hy : y = ⟨c, hAV hcA⟩ * (⟨n, hAV (hDA hnD)⟩ : ↥(nrm V)) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hczz.symm
  rw [hy, map_mul, map_zpow]
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  refine Subgroup.mem_inf.mpr ⟨mem_qimg_of_mem hcA _, ?_⟩
  refine centralizer_orbitClosure (isElemAbelian_qimg hA).1 (mem_qimg_of_mem hcA _) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hjM' : j ∈ M' := le_orbitClosure J (qimg V X) hj
  have hjM : j ∈ qimg V M := by rw [hM, qimg_qpre]; exact hjM'
  obtain ⟨y₂, hy₂M, rfl⟩ := (mem_qimg_iff V M j).mp hjM
  exact (qmap_commute_of_commutator_mem (c := ⟨c, hAV hcA⟩) (y := y₂)
    (hcS.2.2 _ hy₂M)).symm

theorem sec_step {p : ℕ} (hp : p.Prime) {A B X V V₁ : Subgroup Γ} (hA : IsElemAbelian p A)
    (hAX : Admits A X) (hcop : Nat.Coprime p (Nat.card X)) (hB : B ≤ A) (hV₁X : V₁ ≤ X)
    (hchief : IsChiefFactorOf (X ⊔ A) V₁ V) (hH : ChiefCyclic p X) :
    (V₁ : Set Γ) ⊆ (wSub A B V₁ : Set Γ) * (cenIn V₁ (B : Set Γ) : Set Γ) * (V : Set Γ) ∧
      (V₁ : Set Γ) ⊆ (cenIn V₁ (B : Set Γ) : Set Γ) * (wSub A B V₁ : Set Γ) * (V : Set Γ) := by
  obtain ⟨hVn, hV₁n, hVV₁, hmin⟩ := hchief
  have hXA : X ⊔ A ≤ nrm V := hVn.2
  have hXV : X ≤ nrm V := le_sup_left.trans hXA
  have hAV : A ≤ nrm V := le_sup_right.trans hXA
  have hVX : V ≤ X := hVV₁.le.trans hV₁X
  have hAV₁ : A ≤ Subgroup.normalizer (V₁ : Set Γ) := le_sup_right.trans hV₁n.2
  have hXV₁ : X ≤ Subgroup.normalizer (V₁ : Set Γ) := le_sup_left.trans hV₁n.2
  have hV₁nrm : V₁ ≤ nrm V := hV₁X.trans hXV
  have hAbot : A ⊓ V = ⊥ := inf_eq_bot_of_coprime hA hVX hcop
  have hcopV₁ : Nat.Coprime p (Nat.card V₁) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hV₁X)
  have hA' : IsElemAbelian p (qimg V A) := isElemAbelian_qimg hA
  have hB' : qimg V B ≤ qimg V A := qimg_mono V hB
  have hA'R' : qimg V A ≤ Subgroup.normalizer ((qimg V V₁ : Subgroup (QG V)) : Set (QG V)) :=
    qimg_le_normalizer hAV₁
  have hcopR' : Nat.Coprime p (Nat.card (qimg V V₁)) := by
    have h := card_qimg_mul_card hVV₁.le hV₁nrm
    exact hcopV₁.coprime_dvd_right (Dvd.intro _ h)
  have hW : wSub (qimg V A) (qimg V B) (qimg V V₁) ≤ qimg V (wSub A B V₁) :=
    wSub_qimg_le hp hA hAV hAbot hAV₁ hV₁nrm hcopV₁ hB
  have hZ : cenIn (qimg V V₁) (qimg V B : Set (QG V)) = qimg V (cenIn V₁ (B : Set Γ)) :=
    cenIn_qimg hp hA hAV hAV₁ hV₁nrm hcopV₁ hB
  have lift1 : ((qimg V V₁ : Subgroup (QG V)) : Set (QG V)) ⊆
      (wSub (qimg V A) (qimg V B) (qimg V V₁) : Set (QG V)) *
        (cenIn (qimg V V₁) (qimg V B : Set (QG V)) : Set (QG V)) →
      (V₁ : Set Γ) ⊆ (wSub A B V₁ : Set Γ) * (cenIn V₁ (B : Set Γ) : Set Γ) * (V : Set Γ) := by
    intro hmul x hx
    have hxn : x ∈ nrm V := hV₁nrm hx
    obtain ⟨w', hw', z', hz', hwz⟩ := hmul (mem_qimg_of_mem hx hxn)
    obtain ⟨w, hw, z, hz, v, hv, rfl⟩ := exists_lift_mul hxn
      ⟨w', hW hw', z', hZ ▸ hz', hwz⟩
    exact ⟨w * z, ⟨w, hw, z, hz, rfl⟩, v, hv, rfl⟩
  have lift2 : ((qimg V V₁ : Subgroup (QG V)) : Set (QG V)) ⊆
      (cenIn (qimg V V₁) (qimg V B : Set (QG V)) : Set (QG V)) *
        (wSub (qimg V A) (qimg V B) (qimg V V₁) : Set (QG V)) →
      (V₁ : Set Γ) ⊆ (cenIn V₁ (B : Set Γ) : Set Γ) * (wSub A B V₁ : Set Γ) * (V : Set Γ) := by
    intro hmul x hx
    have hxn : x ∈ nrm V := hV₁nrm hx
    obtain ⟨z', hz', w', hw', hzw⟩ := hmul (mem_qimg_of_mem hx hxn)
    obtain ⟨z, hz, w, hw, v, hv, rfl⟩ := exists_lift_mul hxn
      ⟨z', hZ ▸ hz', w', hW hw', hzw⟩
    exact ⟨z * w, ⟨z, hz, w, hw, rfl⟩, v, hv, rfl⟩
  by_cases hab : ∀ x ∈ qimg V V₁, ∀ y ∈ qimg V V₁, x * y = y * x
  · obtain ⟨h1, h2⟩ := subset_mul_of_abelian hp hA' hA'R' hcopR' hB' hab
    exact ⟨lift1 h1, lift2 h2⟩
  · push Not at hab
    have hCF0 := isChiefFactorOf_qimg (V := V) (H := X ⊔ A) (M := V₁) (N := V) hXA le_rfl
      ⟨hVn, hV₁n, hVV₁, hmin⟩
    rw [qimg_self] at hCF0
    have hR'H' : qimg V V₁ ≤ qimg V (X ⊔ A) := hCF0.2.1.1
    have hASimple : IsASimple (qimg V (X ⊔ A)) (qimg V V₁) :=
      ⟨hCF0.2.1.2, hab, fun K hKR _ hHK =>
        hCF0.2.2.2 K ⟨hKR.trans hR'H', hHK⟩ bot_le hKR⟩
    have hss : IsSemisimple (qimg V V₁) := isDirectProduct_simpleComponents hASimple
    have hDirect : IsDirectProduct (lcal (qimg V V₁)) (qimg V V₁) := hss.isDirectProduct_lcal
    have hcyc : ∀ J ∈ lcal (qimg V V₁), ∃ n ∈ qimg V A, qimg V A ⊓
        Subgroup.normalizer (J : Set (QG V)) ≤
        (qimg V A ⊓ Subgroup.centralizer (orbitClosure J (qimg V A) : Set (QG V))) ⊔
          Subgroup.zpowers n := fun J hJ =>
      cyc_of_quotient hA hAX hV₁X hXA hV₁n hH hVX hJ
    obtain ⟨h1, h2⟩ := mul_of_semisimple hp hA' hB' hDirect hA'R' hcopR' hcyc _
      (lcal (qimg V V₁)) subset_rfl
      (fun J hJ a ha => map_conj_mem_lcal hJ (hA'R' ha)) rfl
    rw [hDirect.sSup_eq] at h1 h2
    exact ⟨lift1 h1, lift2 h2⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
