module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_two_fixEq
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {Lo Hi : Subgroup G} (hstep : IsChiefStep (L2 ⊔ S) (str86U L1 L2 S) Lo Hi)
    (hnc : ¬ IsCentralStep (L2 ⊔ S) Lo Hi) :
    ∃ A : Subgroup G, IsElemAbelian 2 A ∧ A ≤ S ∧
      (centralizerMod Lo Hi A).relIndex Hi = 2 ^ m ∧
      (A ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex A = 2 ^ m := by
  classical
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) := str86_isSzU3Quot_of_statedSU hk hFc hU3
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hm2 : 2 ≤ m := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hL2sup : IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) :=
    str86_isL2Quot_sup_of_caseII hF.toW hSB hm2 hm
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := str86_pCoreOf_sup_eq_q2 hF.toW hSB hm2 hm
  have hUe : IsElemAbelian 2 (str86U L1 L2 S) :=
    isElemAbelian_str86U_of_caseII hF hSB hq hm2 hm hII hZ
  have hU2 : IsPGroup 2 (str86U L1 L2 S) := hUe.isPGroup
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF.toW hSB hm2 hm
  have hUH : str86U L1 L2 S ≤ L2 ⊔ S := by
    refine conjClosure_le fun g hg z hz => ?_
    have hzS : z ∈ S := hQ2S (hZ hz)
    exact (L2 ⊔ S).mul_mem ((L2 ⊔ S).mul_mem hg ((le_sup_right : S ≤ L2 ⊔ S) hzS))
      ((L2 ⊔ S).inv_mem hg)
  have hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S := not_thompsonJ_le_Q2_of_caseII hF.toW hSB hB1 hII
  have hAexists : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q2 L1 L2 S := by
    by_contra h
    have hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → A ≤ Q2 L1 L2 S := by
      intro A hA
      by_contra hAQ
      exact h ⟨A, hA, hAQ⟩
    exact hJQ2 (by
      rw [thompsonJ]
      exact iSup₂_le hall)
  obtain ⟨A, hA, hAQ2⟩ := hAexists
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAS : A ≤ S := hA.1
  have hAH : A ≤ L2 ⊔ S := hAS.trans le_sup_right
  obtain ⟨-, hCAU, -, hArel⟩ :=
    str86_two_equality_chain hF hSB hq hm2 hm hII hZ hUe hc hA hAQ2
  have hArel' : (A ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex A = 2 ^ m := by
    rw [hpCore2]
    exact hArel
  have hAncQ : ¬ A ≤ pCoreOf 2 (L2 ⊔ S) := by
    rw [hpCore2]
    exact hAQ2
  obtain ⟨t, htA, htO⟩ := Set.not_subset.mp hAncQ
  have htS : t ∈ S := hAS htA
  have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) htS
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hAe.2 t htA
  have ht2' : t * t ∈ pCoreOf 2 (L2 ⊔ S) := by
    rw [ht2]
    exact (pCoreOf 2 (L2 ⊔ S)).one_mem
  have hk : ∀ L' N' : Subgroup G, IsChiefStep (L2 ⊔ S) (str86U L1 L2 S) L' N' →
      ¬ IsCentralStep (L2 ⊔ S) L' N' → 2 ^ m ≤ (centralizerMod L' N' A).relIndex N' := by
    intro L' N' hstep' hnc'
    have h1 : 2 ^ m ≤ (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' :=
      l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := m) hm2 hL2sup hU2 hUH hstep'
        hnc' htH ht2' htO
    have h2 : centralizerMod L' N' A ≤ centralizerMod L' N' (Subgroup.zpowers t) :=
      centralizerMod_anti_right (V₁ := L') (X := N')
        (U := Subgroup.zpowers t) (U' := A) (Subgroup.zpowers_le.mpr htA)
    exact h1.trans (Subgroup.relIndex_le_of_le_left h2 (D15Proof.relIndex_ne_zero _ _))
  have hsb := Ch3y.step_bound (H := L2 ⊔ S) (U := str86U L1 L2 S) (A := A)
    hUH hAH (k := 2 ^ m) hk hstep hnc (c := 2) hc
  rw [hCAU] at hsb
  have hxle : (centralizerMod Lo Hi A).relIndex Hi ≤ 2 ^ m := by
    have h := hsb
    simp only [Nat.reduceSub, pow_one, pow_two] at h
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hAnc : ¬ A ≤ centralizerMod Lo (L2 ⊔ S) Hi := by
    rw [centralizerMod_eq_pCoreOf_of_isL2Quot hm2 hL2sup hU2 hUH hstep hnc, hpCore2]
    exact hAQ2
  have hlower := l2_chiefStep_relIndex_ge (H := L2 ⊔ S) (V := str86U L1 L2 S)
    (m := m) hm2 hL2sup hU2 hUH hstep hnc hAH hAe hAnc
  have hxge : 2 ^ m ≤ (centralizerMod Lo Hi A).relIndex Hi := by
    rw [← hArel']
    exact hlower
  exact ⟨A, hAe, hAS, le_antisymm hxle hxge, hArel'⟩

theorem str86_caseIIa_two_equality
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2) :
    IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1 ∧
    (∃ t ∈ Q2 L1 L2 S, t ∉ Q1 L1 L2 S ∧ t * t = 1 ∧
      (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≤ (2 ^ k) ^ 2) ∧
    ∀ Lo Hi : Subgroup G, IsChiefStep (L2 ⊔ S) (str86U L1 L2 S) Lo Hi →
      ¬ IsCentralStep (L2 ⊔ S) Lo Hi →
      Lo.relIndex Hi = (2 ^ m) ^ 2 ∧
      ∀ X : Subgroup G, Lo ≤ X → X ≤ Hi → (∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Lo) →
        Lo.relIndex X ≤ 2 ^ m := by
  refine ⟨str86_caseIIa_two_z1_series hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc,
    str86_caseIIa_two_small_involution hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc, ?_⟩
  intro Lo Hi hstep hnc
  have hm2 : 2 ≤ m := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hL2sup : IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) :=
    str86_isL2Quot_sup_of_caseII hF.toW hSB hm2 hm
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := str86_pCoreOf_sup_eq_q2 hF.toW hSB hm2 hm
  have hUe : IsElemAbelian 2 (str86U L1 L2 S) :=
    isElemAbelian_str86U_of_caseII hF hSB (str86_isSzU3Quot_of_statedSU hk hFc hU3) hm2 hm hII hZ
  have hU2 : IsPGroup 2 (str86U L1 L2 S) := hUe.isPGroup
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF.toW hSB hm2 hm
  have hUH : str86U L1 L2 S ≤ L2 ⊔ S := by
    refine conjClosure_le fun g hg z hz => ?_
    have hzS : z ∈ S := hQ2S (hZ hz)
    exact (L2 ⊔ S).mul_mem ((L2 ⊔ S).mul_mem hg ((le_sup_right : S ≤ L2 ⊔ S) hzS))
      ((L2 ⊔ S).inv_mem hg)
  obtain ⟨A, hAe, hAS, hx, hAq⟩ :=
    str86_caseIIa_two_fixEq hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
  have hAncQ : ¬ A ≤ pCoreOf 2 (L2 ⊔ S) := by
    rw [hpCore2]
    intro hle
    have h1 : (A ⊓ Q2 L1 L2 S).relIndex A = 1 := by
      rw [inf_eq_left.mpr hle]
      exact Subgroup.relIndex_eq_one.mpr le_rfl
    rw [← hpCore2, hAq] at h1
    have h2 : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  obtain ⟨t, htA, htO⟩ := Set.not_subset.mp hAncQ
  have htS : t ∈ S := hAS htA
  have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) htS
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hAe.2 t htA
  have ht2' : t * t ∈ pCoreOf 2 (L2 ⊔ S) := by
    rw [ht2]
    exact (pCoreOf 2 (L2 ⊔ S)).one_mem
  have hlower : 2 ^ m ≤ (centralizerMod Lo Hi (Subgroup.zpowers t)).relIndex Hi :=
    l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := m) hm2 hL2sup hU2 hUH hstep hnc
      htH ht2' htO
  have hupper : (centralizerMod Lo Hi (Subgroup.zpowers t)).relIndex Hi ≤ 2 ^ m := by
    have hmono : centralizerMod Lo Hi A ≤ centralizerMod Lo Hi (Subgroup.zpowers t) :=
      centralizerMod_anti_right (V₁ := Lo) (X := Hi)
        (U := Subgroup.zpowers t) (U' := A) (Subgroup.zpowers_le.mpr htA)
    exact (Subgroup.relIndex_le_of_le_left hmono (D15Proof.relIndex_ne_zero _ _)).trans
      (le_of_eq hx)
  have hCeq : (centralizerMod Lo Hi (Subgroup.zpowers t)).relIndex Hi = 2 ^ m :=
    le_antisymm hupper hlower
  have hsq := str86_chiefSection_sq_relIndex (H := L2 ⊔ S) (U := str86U L1 L2 S)
    (L := Lo) (N := Hi) (m := m) hm2 hL2sup hU2 hUH hstep hnc htH ht2' htO
  have hLoHi : Lo.relIndex Hi = (2 ^ m) ^ 2 := by
    rw [← hsq, hCeq]
  refine ⟨hLoHi, ?_⟩
  intro X hLoX hXHi hcomm
  set C : Subgroup G := centralizerMod Lo Hi (Subgroup.zpowers t) with hCdef
  have hXC : X ≤ C := by
    intro x hx
    refine ⟨hXHi hx, ?_, ?_⟩
    · exact D14.le_normalizer_of_isNormalIn hstep.2.1 (hUH (hstep.1.1 (hXHi hx)))
    · intro u hu
      have h1 := hcomm u (Subgroup.zpowers_le.mpr htS hu) x hx
      have e : (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
      rw [← e]
      exact Lo.inv_mem h1
  have hLoC : Lo ≤ C := by
    intro l hl
    refine ⟨hstep.2.2.1.le hl, Subgroup.le_normalizer hl, ?_⟩
    intro u hu
    have huS : u ∈ S := Subgroup.zpowers_le.mpr htS hu
    have h1 : u * l⁻¹ * u⁻¹ ∈ Lo :=
      hstep.2.1.2 u ((le_sup_right : S ≤ L2 ⊔ S) huS) l⁻¹ (Lo.inv_mem hl)
    have e : l * u * l⁻¹ * u⁻¹ = l * (u * l⁻¹ * u⁻¹) := by group
    rw [e]
    exact Lo.mul_mem hl h1
  have hCHi : C ≤ Hi := centralizerMod_le_left Lo Hi (Subgroup.zpowers t)
  have hmul : Lo.relIndex C * C.relIndex Hi = Lo.relIndex Hi :=
    Subgroup.relIndex_mul_relIndex Lo C Hi hLoC hCHi
  have hLC : Lo.relIndex C = 2 ^ m := by
    have hpos : 0 < 2 ^ m := by positivity
    have h2 : Lo.relIndex C * 2 ^ m = 2 ^ m * 2 ^ m := by
      calc Lo.relIndex C * 2 ^ m = Lo.relIndex C * C.relIndex Hi := by rw [hCeq]
        _ = Lo.relIndex Hi := hmul
        _ = (2 ^ m) ^ 2 := hLoHi
        _ = 2 ^ m * 2 ^ m := pow_two _
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  calc Lo.relIndex X ≤ Lo.relIndex C :=
        Subgroup.relIndex_le_of_le_right hXC (D15Proof.relIndex_ne_zero _ _)
    _ = 2 ^ m := hLC

end CFSG.Quasithin.Stroth

end
