module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Basic

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S31

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_mtil
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    thetaOf θ B ∈ mtil p A θ := by
  obtain ⟨hB1, hBA, -⟩ := h.mem_rSet_iff.mp hB
  exact thetaOf_mem_mtil h.hyp.nearFunctor hBA hB1

theorem nearAsolv
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    NearAsolvAction p A (thetaOf θ B) :=
  have hX := mem_mtil h hB
  { prime := h.hyp.prime
    odd := h.hyp.odd
    elemAbelian := h.hyp.elemAbelian
    admits := hX.1.1
    nearPSolvable := hX.1.2.2.2.1
    solvable_cen := hX.1.2.2.2.2 }

theorem not_isSolvable
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    ¬ Group.IsSolvable (thetaOf θ B) :=
  (h.mem_rSet_iff.mp hB).2.2

theorem sol_thetaOf_eq_bot
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    sol (thetaOf θ B) = ⊥ := by
  obtain ⟨hB1, hBA, hns⟩ := h.mem_rSet_iff.mp hB
  exact h.sol_thetaOf_eq_bot hB1 hBA hns

theorem exists_conj
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ)
    {J J' : Subgroup G} (hJ : J ∈ lcal (kOf (thetaOf θ B)))
    (hJ' : J' ∈ lcal (kOf (thetaOf θ B))) :
    ∃ g ∈ dsub A θ ⊔ A, J' = J.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hB1, hBA, hns⟩ := h.mem_rSet_iff.mp hB
  exact h.exists_conj_eq_of_mem_lcal_thetaOf hB1 hBA hns hJ hJ'

theorem nonempty_mulEquiv
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ)
    {J J' : Subgroup G} (hJ : J ∈ lcal (kOf (thetaOf θ B)))
    (hJ' : J' ∈ lcal (kOf (thetaOf θ B))) : Nonempty (↥J ≃* ↥J') := by
  obtain ⟨g, -, rfl⟩ := exists_conj h hB hJ hJ'
  exact ⟨Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulAut.conj g).injective⟩

theorem ne_bot_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    thetaOf θ B ≠ ⊥ := fun hbot =>
  not_isSolvable h hB (by rw [hbot]; infer_instance)

theorem hyp
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    Lemma216.Hyp p A (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) where
  near := nearAsolv h hB
  sol_eq := sol_thetaOf_eq_bot h hB
  ne_bot := ne_bot_thetaOf h hB
  greatest := h.isGreatest_ssol_inf (mem_mtil h hB)

omit [Finite G] in
theorem s0_eq (S H : Subgroup G) : s0 H (S ⊓ H) = S ⊓ kOf H := by
  unfold s0
  rw [inf_assoc, inf_eq_right.mpr (kOf_le _)]

omit [Finite G] in
theorem s1_eq (S H : Subgroup G) : s1 H (S ⊓ H) = CFSG.fittingSubgroupOf (S ⊓ kOf H) := by
  unfold s1
  rw [s0_eq]

section Ident

variable (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ)

include h hB

theorem dZero_eq :
    dZero p A θ = dsub A θ ⊓ kOf (thetaOf θ B) :=
  le_antisymm (iSup₂_le fun _ hB' => (h.lemma66 hB' hB).le)
    (le_iSup₂ (f := fun B' (_ : B' ∈ rSet p A θ) => dsub A θ ⊓ kOf (thetaOf θ B')) B hB)

theorem d0_eq
    : d0 A (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) = dZero p A θ := by
  have H := hyp h hB
  rw [lemma216_d0 H.near H.sol_eq H.ne_bot H.greatest, cenIn_eq_dsub h.hyp.nearFunctor
    (mem_mtil h hB), dZero_eq h hB]

theorem d1_eq :
    d1 A (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) = dOne p A θ := by
  unfold d1 dOne
  rw [d0_eq h hB]

theorem d2_eq :
    d2 A (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) = dTwo p A θ := by
  unfold d2 dTwo
  rw [d0_eq h hB, d1_eq h hB]

theorem cenIn_kOf_eq :
    cenIn (kOf (thetaOf θ B)) A = dZero p A θ := by
  have H := hyp h hB
  rw [← H.d0_eq, d0_eq h hB]

theorem mOf_eq :
    mOf A (kOf (thetaOf θ B)) = ssol p A θ ⊓ kOf (thetaOf θ B) := by
  have H := hyp h hB
  rw [← H.s0_eq_mOf, s0_eq]

theorem fitting_eq_cenIn_kOf :
    CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) =
        cenIn (kOf (thetaOf θ B)) (dOne p A θ) ∧
      IsMulCommutative (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) := by
  have H := hyp h hB
  have hc := thm210c H.semisimpleAction
  rw [mOf_eq h hB, cenIn_kOf_eq h hB] at hc
  exact ⟨hc.2, hc.1⟩

theorem admits_cenIn_dOne :
    Admits (cenIn (thetaOf θ B) A ⊔ A) (cenIn (thetaOf θ B) (dOne p A θ)) := by
  have hX := mem_mtil h hB
  have hQH : cenIn (thetaOf θ B) A ⊔ A ≤ Subgroup.normalizer (thetaOf θ B : Set G) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) hX.1.1
  have hQD : cenIn (thetaOf θ B) A ⊔ A ≤ Subgroup.normalizer (dOne p A θ : Set G) := by
    intro g hg
    have h1 := Lemma216.admits_cenIn_kOf (thetaOf θ B) A hg
    rw [cenIn_kOf_eq h hB] at h1
    exact Lemma216.mem_normalizer_fittingSubgroupOf h1
  exact fun g hg => Lemma216.mem_normalizer_cenIn (hQH hg) (hQD hg)

theorem cenIn_dOne_eq :
    cenIn (thetaOf θ B) (dOne p A θ) =
      CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
  have H := hyp h hB
  obtain ⟨hF, -⟩ := fitting_eq_cenIn_kOf h hB
  refine le_antisymm ?_ ?_
  · have hZH : cenIn (thetaOf θ B) (dOne p A θ) ≤ thetaOf θ B := inf_le_left
    have hZK : cenIn (thetaOf θ B) (dOne p A θ) ⊓ kOf (thetaOf θ B) ≤
        s1 (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) := by
      rw [s1_eq, hF]
      intro x hx
      obtain ⟨⟨-, hxc⟩, hxK⟩ := hx
      exact ⟨hxK, hxc⟩
    have hZ2 := lemma216c H.near H.sol_eq H.ne_bot H.greatest hZH (admits_cenIn_dOne h hB) hZK
    have hs2 : s2 (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) ≤ ssol p A θ ⊓ kOf (thetaOf θ B) :=
      (inf_le_left : s2 (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) ≤
        s0 (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B)).trans (s0_eq _ _).le
    intro z hz
    have hzK : z ∈ kOf (thetaOf θ B) := (inf_le_right : ssol p A θ ⊓ kOf (thetaOf θ B) ≤ _)
      (hs2 (hZ2 hz))
    rw [hF]
    exact ⟨hzK, (Subgroup.mem_inf.mp hz).2⟩
  · rw [hF]
    exact inf_le_inf_right _ (kOf_le _)

theorem sectionCentralizer_d2 :
    ssol p A θ ⊓ kOf (thetaOf θ B) ≤ thetaOf θ B ⊓ sectionCentralizer
        (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
        (dTwo p A θ ⊔ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) ∧
      thetaOf θ B ⊓ sectionCentralizer
        (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
        (dTwo p A θ ⊔ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) ≤
        khat (thetaOf θ B) := by
  have H := hyp h hB
  have h1 := lemma216a H.near H.sol_eq H.ne_bot H.greatest
  rw [s0_eq, s1_eq, d2_eq h hB] at h1
  exact h1

theorem sectionCentralizer_d0 :
    thetaOf θ B ⊓ sectionCentralizer
        (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
        (dZero p A θ ⊔ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) ≤
      ssol p A θ ⊓ kOf (thetaOf θ B) := by
  have H := hyp h hB
  have h2 := lemma216b H.near H.sol_eq H.ne_bot H.greatest
  rw [d0_eq h hB, s1_eq] at h2
  rw [← h2]
  exact (inf_le_left : s2 (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B) ≤
    s0 (thetaOf θ B) (ssol p A θ ⊓ thetaOf θ B)).trans (s0_eq _ _).le

theorem sOne_inf_eq :
    sOne p A θ ⊓ thetaOf θ B = cenIn (thetaOf θ B) (dOne p A θ) := by
  have hX := mem_mtil h hB
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxH⟩ := hx
    exact ⟨hxH, hxS.2⟩
  · set Z := cenIn (thetaOf θ B) (dOne p A θ) with hZ
    have hZH : Z ≤ thetaOf θ B := inf_le_left
    have hAZ : Admits A Z := (le_sup_right : A ≤ cenIn (thetaOf θ B) A ⊔ A).trans
      (admits_cenIn_dOne h hB)
    have hZ1 : Z ∈ assoc p A θ := mem_assoc_of_le h.hyp.prime hX.1 hZH hAZ
    have hZN : Z ≤ Subgroup.normalizer (dOne p A θ : Set G) := fun z hz =>
      Subgroup.centralizer_le_normalizer _ hz.2
    refine le_inf (le_inf ?_ inf_le_right) hZH
    exact le_iSup₂ (f := fun Y (_ : Y ∈ {Y : Subgroup G | Y ∈ assoc p A θ ∧
      Y ≤ Subgroup.normalizer (dOne p A θ : Set G)}) => Y) Z ⟨hZ1, hZN⟩

end Ident

end Sec6S31

end CFSG.SignalizerFunctorTheorem.McBride.Near
