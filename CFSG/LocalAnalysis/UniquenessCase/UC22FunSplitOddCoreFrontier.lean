module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitNormalizerGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitDegreeThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOddCoreContainment

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped Pointwise commutatorElement


theorem oddCore_commutes_fundamental_involution_of_permuting
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) (B : Subgroup X)
    (hBab : IsMulCommutative B) (hBo : Odd (Nat.card B))
    (hB3 : ¬ 3 ∣ Nat.card B) (hBp : ¬ p ∣ Nat.card B)
    (hrank : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → pRank r B ≤ 2)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    {J : Subgroup X} (hJ : J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    {z : X} (hz : IsUniqueInvolution J z) :
    ∀ o ∈ (classicalInvolutionOddCore ↥(B ⊔ (P : Subgroup X))).map
      (B ⊔ (P : Subgroup X)).subtype, o * z = z * o := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, _hqs, hL2, hΩ⟩ :=
    fundamental_ambient_of_lieModel hp hp2 hadm hX hA1 hJ.1
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ LieModel (X ⧸ center X) t n p f :=
    ⟨t, n, e, hadm, rfl, hX.quotient_center hZ⟩
  let H : Subgroup X := B ⊔ (P : Subgroup X)
  let O : Subgroup X := (classicalInvolutionOddCore H).map H.subtype
  let E : Subgroup X := ⁅O, Subgroup.zpowers z⁆
  let Ω : Set (Subgroup X) := {K : Subgroup X | IsFundamentalOver (p ^ e) K}
  let Γ : Set X := {x : X | ∃ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
    K ≠ J ∧ x ∈ K}
  let A : Subgroup X := centralizingLayer Ω Γ
  have hPK : IsSylow2In ((P : Subgroup X) ⊓ J) J := IsSylow2In.of_isSylowOf hJ.2
  have hzP : z ∈ (P : Subgroup X) := (Sec6Gen.mem_of_isSylow2In hz hPK).1
  have hzH : z ∈ H := (le_sup_right : (P : Subgroup X) ≤ H) hzP
  obtain ⟨hEO, hinv, -⟩ := oddCore_commutator_involution
    (B := B) (P := P) (H := H) hBab hBo P.isPGroup' rfl hperm hzH hz.sq
  have hOB : O ≤ B := oddCore_map_le_of_permuting
    (B := B) (P := P) (H := H) hBo P.isPGroup' rfl hperm
  have hEB : E ≤ B := hEO.trans hOB
  have hEodd : Odd (Nat.card E) := Odd.of_dvd_nat hBo (Subgroup.card_dvd_of_le hEB)
  have hEab : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext (congrArg (fun b : B => (b : X))
      (hBab.is_comm.comm ⟨a, hEB a.2⟩ ⟨b, hEB b.2⟩))⟩⟩
  have hE3 : ¬ 3 ∣ Nat.card E := fun h =>
    hB3 (h.trans (Subgroup.card_dvd_of_le hEB))
  have hEp : ¬ p ∣ Nat.card E := fun h =>
    hBp (h.trans (Subgroup.card_dvd_of_le hEB))
  have hfinish : E = ⊥ → ∀ o ∈ O, o * z = z * o := by
    intro hEbot o ho
    have hmem : ⁅o, z⁆ ∈ E := by
      simpa [E] using Subgroup.commutator_mem_commutator
        (H₁ := O) (H₂ := Subgroup.zpowers z) ho (Subgroup.mem_zpowers z)
    rw [hEbot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  by_cases hEbot : E = ⊥
  · exact hfinish hEbot
  · have hEne : E ≠ ⊥ := hEbot
    have hrankOpen : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → CFSG.Open.pRank r B ≤ 2 := by
      intro r hr hdvd
      rw [← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank
        (p := r) (Q := B) hr]
      exact hrank r hr hdvd
    obtain ⟨hKAraw, hEAraw, -⟩ :=
      oddCore_commutator_le_centralizingLayer hp2 hdesc hL2 hΩ P B hBab hBo hrankOpen hperm hJ hz
    have hKA : J ≤ A := by simpa [A, Γ, Ω] using hKAraw
    have hEA : E ≤ A := by simpa [A, Γ, Ω] using hEAraw
    obtain ⟨Q, hQPK, ⟨eQ⟩, hzQ⟩ := exists_q8_of_mem_funSet hΩ P hJ hz
    have hQH : Q ≤ H := (hQPK.trans inf_le_left).trans le_sup_right
    have hQK : Q ≤ J := hQPK.trans inf_le_right
    have hQA : Q ≤ A := hQK.trans hKA
    have hQN : Q ≤ Subgroup.normalizer (E : Set X) := fun q hq =>
      mem_normalizer_oddCore_commutator_of_mem_of_centralizes (hQH hq)
        (hz.commute_of_mem (hQK hq)).symm
    have hzA : z ∈ A := hKA hz.mem
    have hAalt := centralizingLayer_funSet_rankOne_or_degree_three
      hp hp2 hadm hX hA1 hRee P hJ
    have hDegreeFalse : (LieModel (A ⧸ center A) .PSL 3 p e ∨
        LieModel (A ⧸ center A) .PSU 3 p e) → False := by
      intro hLie
      let EA : Subgroup A := E.subgroupOf A
      let QA : Subgroup A := Q.subgroupOf A
      have hcardEA : Nat.card EA = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv
      have hEoddA : Odd (Nat.card EA) := by rw [hcardEA]; exact hEodd
      have hEneA : EA ≠ ⊥ := by
        intro hbot
        apply hEne
        have hcard : Nat.card E = 1 := by rw [← hcardEA, hbot]; simp
        exact Subgroup.eq_bot_of_card_eq E hcard
      have hEabA : IsMulCommutative EA := by
        refine IsMulCommutative.of_comm fun x y => ?_
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : E => (z : X))
          (hEab.is_comm.comm
            ⟨((x : A) : X), Subgroup.mem_subgroupOf.mp x.2⟩
            ⟨((y : A) : X), Subgroup.mem_subgroupOf.mp y.2⟩)
      let eQA : QA ≃* QuaternionGroup 2 :=
        (Subgroup.subgroupOfEquivOfLe hQA).trans eQ
      let zA : A := ⟨z, hzA⟩
      let zQA : QA := ⟨zA, Subgroup.mem_subgroupOf.mpr hzQ.mem⟩
      have hzQa : eQ (⟨z, hzQ.mem⟩ : Q) = QuaternionGroup.a 2 := by
        have hsq : (eQ.symm (QuaternionGroup.a 2) : Q) *
            (eQ.symm (QuaternionGroup.a 2) : Q) = 1 := by
          refine eQ.injective ?_
          rw [map_mul, map_one, eQ.apply_symm_apply]
          decide
        have hsqX : ((eQ.symm (QuaternionGroup.a 2) : Q) : X) *
            ((eQ.symm (QuaternionGroup.a 2) : Q) : X) = 1 := by
          rw [← Subgroup.coe_mul, hsq, Subgroup.coe_one]
        have hneX : ((eQ.symm (QuaternionGroup.a 2) : Q) : X) ≠ 1 := by
          intro h
          have hQ : (eQ.symm (QuaternionGroup.a 2) : Q) = 1 := Subtype.ext h
          have h1 : QuaternionGroup.a 2 = (1 : QuaternionGroup 2) := by
            rw [← eQ.apply_symm_apply (QuaternionGroup.a 2), hQ, map_one]
          exact absurd h1 (by decide)
        rcases hzQ.unique _ (eQ.symm (QuaternionGroup.a 2)).2 hsqX with h1 | h1
        · exact absurd h1 hneX
        · have h1Q : (eQ.symm (QuaternionGroup.a 2) : Q) = ⟨z, hzQ.mem⟩ := Subtype.ext h1
          have := congrArg eQ h1Q
          simpa using this.symm
      have hzQA : eQA zQA = QuaternionGroup.a 2 := by
        change eQ ((Subgroup.subgroupOfEquivOfLe hQA) zQA) = QuaternionGroup.a 2
        rw [show (Subgroup.subgroupOfEquivOfLe hQA) zQA = ⟨z, hzQ.mem⟩ from rfl]
        exact hzQa
      have hinvA : ∀ x ∈ EA, (zQA : A) * x * (zQA : A)⁻¹ = x⁻¹ := by
        intro x hx
        have hxX : ((x : A) : X) ∈ E := Subgroup.mem_subgroupOf.mp hx
        have h := hinv ((x : A) : X) hxX
        apply Subtype.ext
        simpa using h
      obtain ⟨hInjE, hInjQ⟩ :=
        injective_center_quotient_of_q8_inverts (A := A) EA QA
          hEoddA hEneA eQA zQA hzQA hinvA
      let πA : A →* A ⧸ center A := QuotientGroup.mk' (center A)
      let fE : EA →* A ⧸ center A := πA.comp EA.subtype
      let fQ : QA →* A ⧸ center A := πA.comp QA.subtype
      have hInjE' : Function.Injective fE := by
        simpa [fE, πA, MonoidHom.domRestrict] using hInjE
      have hInjQ' : Function.Injective fQ := by
        simpa [fQ, πA, MonoidHom.domRestrict] using hInjQ
      let E' : Subgroup (A ⧸ center A) := fE.range
      let Q' : Subgroup (A ⧸ center A) := fQ.range
      let eE' : EA ≃* E' := MonoidHom.ofInjective hInjE'
      let eQ' : QA ≃* Q' := MonoidHom.ofInjective hInjQ'
      let eQ'' : Q' ≃* QuaternionGroup 2 := eQ'.symm.trans eQA
      let zQ' : Q' := eQ' zQA
      have hzQ' : eQ'' zQ' = QuaternionGroup.a 2 := by
        simp [eQ'', zQ', hzQA]
      have hcardE' : Nat.card E' = Nat.card E := by
        calc Nat.card E' = Nat.card EA := (Nat.card_congr eE'.toEquiv).symm
          _ = Nat.card E := hcardEA
      have hEne' : E' ≠ ⊥ := by
        intro hbot
        apply hEne
        have hcard : Nat.card E = 1 := by rw [← hcardE', hbot]; simp
        exact Subgroup.eq_bot_of_card_eq E hcard
      have hEodd' : Odd (Nat.card E') := by rw [hcardE']; exact hEodd
      have hE3' : ¬ 3 ∣ Nat.card E' := fun h => hE3 (hcardE' ▸ h)
      have hEp' : ¬ p ∣ Nat.card E' := fun h => hEp (hcardE' ▸ h)
      have hEab' : IsMulCommutative E' := by
        refine IsMulCommutative.of_comm fun x y => ?_
        refine eE'.symm.injective ?_
        rw [map_mul, map_mul]
        exact hEabA.is_comm.comm (eE'.symm x) (eE'.symm y)
      have hQE' : ∀ q' ∈ Q', ∀ x' ∈ E', q' * x' * q'⁻¹ ∈ E' := by
        intro q' hq' x' hx'
        obtain ⟨qA, rfl⟩ := hq'
        obtain ⟨xA, rfl⟩ := hx'
        have hqA : (qA : X) ∈ Q := Subgroup.mem_subgroupOf.mp qA.2
        have hxA : (xA : X) ∈ E := Subgroup.mem_subgroupOf.mp xA.2
        have hmemX : (qA : X) * (xA : X) * (qA : X)⁻¹ ∈ E :=
          (Subgroup.mem_normalizer_iff.mp (hQN (x := (qA : X)) hqA) (xA : X)).mp hxA
        have hmemA : (qA : A) * (xA : A) * (qA : A)⁻¹ ∈ EA := hmemX
        refine ⟨⟨(qA : A) * (xA : A) * (qA : A)⁻¹, hmemA⟩, ?_⟩
        simp [fQ, fE, map_mul, map_inv]
      have hinv' : ∀ x' ∈ E', (zQ' : A ⧸ center A) * x' * (zQ' : A ⧸ center A)⁻¹ =
          x'⁻¹ := by
        intro x' hx'
        obtain ⟨xA, rfl⟩ := hx'
        have hxE : ((xA : A) : X) ∈ E := Subgroup.mem_subgroupOf.mp xA.2
        have h := hinv ((xA : A) : X) hxE
        have hzQ'val : (zQ' : A ⧸ center A) = πA zA := by
          change fQ zQA = πA zA
          simp [fQ, zQA, zA, πA]
        have hA : zA * (xA : A) * zA⁻¹ = (xA : A)⁻¹ := Subtype.ext h
        rw [hzQ'val, show fE xA = πA (xA : A) from rfl,
          ← map_mul, ← map_inv, ← map_mul]
        rw [hA, map_inv]
      exact false_of_odd_abelian_q8_in_lieModel_PSL3_or_PSU3 hLie
        hEne' hEab' hEodd' hE3' hEp' eQ'' hQE' zQ' hzQ' hinv'
    rcases hAalt with hAK | hPSL | hPSU
    · have hAK' : A = J := by simpa [A, Γ, Ω] using hAK
      have hEJ : E ≤ J := hAK' ▸ hEA
      have hEbotJ : E = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxJ : x ∈ J := hEJ hx
        have hzx : z * x * z⁻¹ = x := by
          rw [hz.commute_of_mem hxJ]
          group
        have hxinv : x = x⁻¹ := by
          have h := hinv x hx
          rwa [hzx] at h
        exact Subgroup.mem_bot.mpr
          (CFSG.Wreathed.ComponentCoverConfinement.eq_one_of_eq_inv_of_odd
            (Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E hx)) hxinv)
      exact hfinish hEbotJ
    · exact False.elim (hDegreeFalse (Or.inl hPSL))
    · exact False.elim (hDegreeFalse (Or.inr hPSU))

end CFSG.LocalAnalysis.UniquenessCase.UC22
