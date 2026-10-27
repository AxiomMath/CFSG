module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Extra
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Setup
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Setup
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Structure
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

section Frame

variable {p ℓ : ℕ} {X : Type*} [Group X] [Finite X] {f : MulAut X}

theorem Frame.sylow_le_conj_fixedNormalizer (hF : Frame p ℓ f) (R : Sylow ℓ X) :
    ∃ g : X, (R : Subgroup X) ≤ (fixedNormalizer f).map (MulAut.conj g).toMonoidHom := by
  have := Fact.mk hF.prime_ℓ
  obtain ⟨S, hS⟩ := hF.C0_pgroup.exists_le_sylow
  have hSeq : (S : Subgroup X) = fixedFitting f := hF.C0_sylow S S.isPGroup' hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S R
  refine ⟨g, ?_⟩
  have hR : (R : Subgroup X) = (S : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hR, hSeq]
  exact Subgroup.map_mono ((fixedFitting_le f).trans (fixed_le_fixedNormalizer f))

theorem Frame.exists_involution_fpf (hF : Frame p ℓ f) (hℓ : ℓ ≠ 2)
    (h2 : 2 ∣ Nat.card (signalizerFixedSubgroup f)) :
    ∃ t ∈ signalizerFixedSubgroup f, orderOf t = 2 ∧
      ∀ x ∈ fixedFitting f, x ≠ 1 → t * x * t⁻¹ ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := signalizerFixedSubgroup f) 2 h2
  have ht2 : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe, ht]
  refine ⟨t, t.2, ht2, fun x hx hx1 hcomm => ?_⟩
  have htF : (t : X) ∉ fixedFitting f := by
    intro htF
    have hp := hF.C0_pgroup
    have : Fact ℓ.Prime := ⟨hF.prime_ℓ⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) (⟨t, htF⟩ : fixedFitting f)
    rw [Subgroup.orderOf_mk, ht2] at hk
    have h2ℓ : 2 ∣ ℓ ^ k := hk ▸ dvd_refl 2
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hF.prime_ℓ).mp
      (Nat.prime_two.dvd_of_dvd_pow h2ℓ)
    exact hℓ this.symm
  have hxZ : x ∈ Subgroup.centralizer (fixedFitting f : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hF.C0_comm.is_comm.comm (⟨y, hy⟩ : fixedFitting f) ⟨x, hx⟩)
  have hcomm' : (t : X) * x = x * t := by
    have := congrArg (· * (t : X)) hcomm
    simpa [mul_assoc] using this
  exact hx1 (hF.fpf t t.2 htF x hxZ hcomm')

end Frame

section Models

variable {p : ℕ} {J : Type*} [Group J] [Finite J]

namespace ModelFacts

theorem card_fixed_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) :
    Nat.card (signalizerFixedSubgroup (MulAut.congr e f)) =
      Nat.card (signalizerFixedSubgroup f) := by
  rw [signalizerFixedSubgroup_congr, Subgroup.card_map_of_injective e.injective]

end ModelFacts

omit [Finite J] in
theorem NearSimple.fixedNormalizer_eq_of_psl3
    (h : NearSimple p J) {f : MulAut J}
    (hf : orderOf f = p)
    (hJ : Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    fixedNormalizer f = signalizerFixedSubgroup f ∧ Nat.card (signalizerFixedSubgroup f) = 12 ∧
      Nat.card (fixedFitting f) = 4 := by
  obtain ⟨e⟩ := hJ
  have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
    rw [← Nat.card_congr e.toEquiv]; exact h.coprime
  have hf' : orderOf (MulAut.congr e f) = p := by rw [orderOf_congr, hf]
  have hM := fixedNormalizer_psl2Three h.prime hcop _ hf'
  have hA4 := PSL2Three.isA4_fixed h.prime hcop _ hf'
  rw [fixedNormalizer_congr, signalizerFixedSubgroup_congr] at hM
  refine ⟨Subgroup.map_injective e.injective hM, ?_, ?_⟩
  · rw [← ModelFacts.card_fixed_congr e f]
    exact hA4.card
  · have h4 : Nat.card (fixedFitting (MulAut.congr e f)) = 4 := by
      rw [hA4.fixedFitting_eq]
      exact hA4.card_klein
    rw [fixedFitting_congr, Subgroup.card_map_of_injective e.injective] at h4
    exact h4

omit [Finite J] in
theorem NearSimple.fixedSubgroup_mulEquiv_a4 (h : NearSimple p J) {f : MulAut J}
    (hf : orderOf f = p)
    (hJ : Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    Nonempty (↥(signalizerFixedSubgroup f) ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨e⟩ := hJ
  have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
    rw [← Nat.card_congr e.toEquiv]; exact h.coprime
  have hf' : orderOf (MulAut.congr e f) = p := by rw [orderOf_congr, hf]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e'⟩ := CFSG.SignalizerFunctorTheorem.NearModels.psl2_fixedSubgroup_mulEquiv 3 h.prime
    hcop _ hf'
  exact ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (signalizerFixedSubgroup_congr e f).symm).trans
      (e'.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup))⟩

theorem NearSimple.exists_involution_fpf
    (h : NearSimple p J) {f : MulAut J}
    (hf : orderOf f = p)
    (hJ : ¬ Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    ∃ t ∈ signalizerFixedSubgroup f, orderOf t = 2 ∧
      ∀ x ∈ fixedFitting f, x ≠ 1 → t * x * t⁻¹ ≠ x := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hF : Frame p 3 f := Frame.of_model e (fun f' hf' => frame_psl2Even h.prime hcop f' hf') hf
    refine hF.exists_involution_fpf (by norm_num) ?_
    obtain ⟨c, t, hS⟩ := PSL2Even.exists_S3Data_of_coprime h.prime hcop (MulAut.congr e f)
      (by rw [orderOf_congr, hf])
    rw [← ModelFacts.card_fixed_congr e f, hS.card]
    norm_num
  · exact absurd ⟨e⟩ hJ
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    have hF : Frame (2 * n + 1) 5 f :=
      Frame.of_model e (fun f' hf' => frame_sz h.prime hcop hY f' hf') hf
    refine hF.exists_involution_fpf (by norm_num) ?_
    rw [← ModelFacts.card_fixed_congr e f,
      SzModel.card_fixed h.prime hcop _ (by rw [orderOf_congr, hf])]
    norm_num
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    have hF : Frame p 3 f := Frame.of_model e (fun f' hf' => frame_psu3 h.prime hcop hY f' hf') hf
    refine hF.exists_involution_fpf (by norm_num) ?_
    rw [← ModelFacts.card_fixed_congr e f, UnitaryFrame.card_fixedSubgroup h.prime hcop _
      (by rw [orderOf_congr, hf])]
    norm_num

omit [Finite J] in
theorem NearSimple.fixedCore1_eq
    (h : NearSimple p J) {f : MulAut J} (hf : orderOf f = p)
    (hJ : ¬ Nonempty (J ≃* PSU3 2 p)) : fixedCore1 f = signalizerFixedSubgroup f := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact Extra.fixedCore1_eq_of_congr e
      (fixedCore1_psl2Even h.prime hcop _ (by rw [orderOf_congr, hf]))
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact Extra.fixedCore1_eq_of_congr e
      (fixedCore1_psl2Three h.prime hcop _ (by rw [orderOf_congr, hf]))
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact Extra.fixedCore1_eq_of_congr e
      (fixedCore1_sz h.prime hcop _ (by rw [orderOf_congr, hf]))
  · exact absurd ⟨e⟩ hJ

theorem NearSimple.sylow_le_conj_fixedNormalizer
    (h : NearSimple p J) {f : MulAut J}
    (hf : orderOf f = p) {r : ℕ} (hr : r.Prime)
    (hcase : (r = 2 ∧ Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 p))) ∨ (r = 3 ∧ Nonempty (J ≃* PSU3 2 p))) (R : Sylow r J) :
    ∃ g : J, (R : Subgroup J) ≤ (fixedNormalizer f).map (MulAut.conj g).toMonoidHom := by
  rcases hcase with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hF : Frame p 2 f :=
      Frame.of_model e (fun f' hf' => frame_psl2Three h.prime hcop f' hf') hf
    exact hF.sylow_le_conj_fixedNormalizer R
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    have hF : Frame p 3 f := Frame.of_model e (fun f' hf' => frame_psu3 h.prime hcop hY f' hf') hf
    exact hF.sylow_le_conj_fixedNormalizer R

theorem NearSimple.p_eq_three
    (h : NearSimple p J) {f : MulAut J} (hf : orderOf f = p)
    (hp3 : p = 3) : Nonempty (J ≃* Sz 1) ∧ Nat.card (fixedFitting f) = 5 := by
  have hcopJ := h.coprime
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exfalso
    subst hp3
    rw [Nat.card_congr e.toEquiv, NearSolvable.card_psl2_even (by norm_num)] at hcopJ
    norm_num at hcopJ
  · exfalso
    subst hp3
    rw [Nat.card_congr e.toEquiv, NearSolvable.card_psl2_three (by norm_num)] at hcopJ
    norm_num at hcopJ
  · subst hn
    obtain rfl : n = 1 := by omega
    refine ⟨⟨e⟩, ?_⟩
    have hcop : Nat.Coprime (2 * 1 + 1) (Nat.card (Sz 1)) := by
      rw [← Nat.card_congr e.toEquiv]; exact hcopJ
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    have hF : Frame (2 * 1 + 1) 5 f :=
      Frame.of_model e (fun f' hf' => frame_sz h.prime hcop hY f' hf') hf
    have hC : Nat.card (signalizerFixedSubgroup f) = 20 := by
      rw [← ModelFacts.card_fixed_congr e f,
        SzModel.card_fixed h.prime hcop _ (by rw [orderOf_congr, hf])]
    have hdvd : Nat.card (fixedFitting f) ∣ 20 :=
      hC ▸ Subgroup.card_dvd_of_le (fixedFitting_le f)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨k, hk⟩ := hF.C0_pgroup.exists_card_eq
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have h25 : 25 ∣ 20 := (pow_dvd_pow 5 hk2 : 5 ^ 2 ∣ 5 ^ k).trans (hk ▸ hdvd)
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hF.C0_ne_bot (Subgroup.card_eq_one.mp (by simpa using hk))
    obtain rfl : k = 1 := by omega
    simpa using hk
  · exfalso
    subst hp3
    rw [Nat.card_congr e.toEquiv, NearSolvable.card_psu3 (by norm_num)] at hcopJ
    norm_num at hcopJ

end Models

end CFSG.SignalizerFunctorTheorem.McBride
