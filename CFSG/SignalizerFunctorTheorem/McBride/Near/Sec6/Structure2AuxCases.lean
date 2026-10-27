module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Structure2Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Structure

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S32

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

section Cyclic

variable (h : Counterexample p A θ)

include h

theorem zpowers_mem_rSet
    {B : Subgroup G} (hB : B ∈ rSet p A θ) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : Subgroup.zpowers b ∈ rSet p A θ :=
  h.rSet_mono hB (Subgroup.zpowers_le.mpr hb) (fun hbot => hb1 (by
    simpa [Subgroup.zpowers_eq_bot] using hbot))

theorem zpowers_le_A
    {B : Subgroup G} (hB : B ∈ rSet p A θ) {b : G} (hb : b ∈ B) :
    Subgroup.zpowers b ≤ A :=
  Subgroup.zpowers_le.mpr ((h.mem_rSet_iff.mp hB).2.1 hb)

end Cyclic

section CaseI

variable (h : Counterexample p A θ)

include h

theorem fitting_le_of_inf_ne_bot
    {E Z : Subgroup G} (hE : E ∈ rSet p A θ)
    (hI : ∀ J ∈ lcal (thetaOf θ E), IsPSL3 p J) (hZS : Z ≤ ssol p A θ)
    (hZadm : Admits (ssol p A θ ⊔ A) Z)
    (hne : Z ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥) :
    CFSG.fittingSubgroupOf (kOf (thetaOf θ E) ⊓ ssol p A θ) ≤ Z := by
  obtain ⟨-, hEA, -⟩ := h.mem_rSet_iff.mp hE
  have hSA : A ≤ Subgroup.normalizer (ssol p A θ : Set G) := h.ssol_mem_assoc.1
  have hΓC : (thetaOf θ E ⊓ ssol p A θ) ⊔ A ≤ Subgroup.centralizer (E : Set G) := by
    refine sup_le (inf_le_left.trans (h.hyp.isFunctor.thetaOf_le_centralizer hEA)) ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (commute_of_mem h.hyp.elemAbelian.1 (hEA he) ha).eq
  have hΓZ : (thetaOf θ E ⊓ ssol p A θ) ⊔ A ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (inf_le_right.trans (le_sup_left.trans hZadm)) (le_sup_right.trans hZadm)
  have hΓE : (thetaOf θ E ⊓ ssol p A θ) ⊔ A ≤ Subgroup.normalizer (E : Set G) :=
    fun g hg => Subgroup.centralizer_le_normalizer (E : Set G) (hΓC hg)
  have hW : Admits ((thetaOf θ E ⊓ ssol p A θ) ⊔ A) (Z ⊓ Subgroup.centralizer (E : Set G)) :=
    fun g hg => Lemma216.mem_normalizer_inf (hΓZ hg)
      (Lemma216.mem_normalizer_centralizer (hΓE hg))
  obtain ⟨N', hN'W, hN'1, hN'adm, hN'min⟩ := HypAAux.exists_minimal_admits hne hW
  have hN'H : N' ≤ thetaOf θ E ⊓ ssol p A θ := fun x hx =>
    ⟨inf_centralizer_le_thetaOf h.ssol_mem_assoc hEA ⟨hZS (hN'W hx).1, (hN'W hx).2⟩,
      hZS (hN'W hx).1⟩
  have hN'M : N' ≤ ssol p A θ ⊓ kOf (thetaOf θ E) :=
    le_inf_kOf_of_minimal h hE hN'H hN'1 hN'adm hN'min
  obtain ⟨J, hJ⟩ := exists_mem_lcal h hE
  have h69 := h.lemma69 hE hJ (hI J hJ)
  have hch : IsChiefFactorOf ((thetaOf θ E ⊓ ssol p A θ) ⊔ A) N' ⊥ :=
    isChiefFactorOf_bot (hN'H.trans le_sup_left) hN'1 hN'adm hN'min
  have := h69.2 N' hch (hN'M.trans inf_le_right)
  rw [← this]
  exact hN'W.trans inf_le_left

theorem isMulCommutative_sOne_of_psl3
    (hI : ∀ E ∈ rSet p A θ, ∀ J ∈ lcal (thetaOf θ E), IsPSL3 p J) :
    IsMulCommutative (sOne p A θ) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨B, hB2⟩ := h.rSetN_two_nonempty
  have hB : B ∈ rSet p A θ := hB2.1
  have hBcard : Nat.card B = p ^ 2 := hB2.2
  obtain ⟨-, hBA, -⟩ := h.mem_rSet_iff.mp hB
  have hBel : IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.hyp.elemAbelian hBA
  have hSA : A ≤ Subgroup.normalizer (ssol p A θ : Set G) := h.ssol_mem_assoc.1
  have hSsol : Group.IsSolvable (ssol p A θ) := h.isSolvable_ssol
  have hD1S : dOne p A θ ≤ ssol p A θ := (dOne_le_dsub h).trans h.dsub_le_ssol
  have hSne : ssol p A θ ≠ ⊥ := fun hbot => dOne_ne_bot h (le_bot_iff.mp (hbot ▸ hD1S))
  have hSadm : Admits (ssol p A θ ⊔ A) (ssol p A θ) :=
    sup_le (Subgroup.le_normalizer) hSA
  obtain ⟨Z, hZS, hZ1, hZadm, hZmin⟩ := HypAAux.exists_minimal_admits hSne hSadm
  have hZsol : Group.IsSolvable Z :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hZS)
  have hZcomm := HypAAux.forall_mul_comm_of_solvable_minimal hZadm hZ1 hZmin hZsol
  have hZA : A ≤ Subgroup.normalizer (Z : Set G) := le_sup_right.trans hZadm
  have hZcop : Nat.Coprime p (Nat.card Z) :=
    h.ssol_mem_assoc.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hZS)
  have hZmem : Z ∈ assoc p A θ := mem_assoc_of_le h.hyp.prime h.ssol_mem_assoc hZS hZA
  have hgenZ := iSup_inf_centralizer h.hyp.prime hBel (by rw [hBcard]) (hBA.trans hZA) hZcop
  obtain ⟨b₀, hb₀B, hb₀1, hb₀ne⟩ : ∃ b ∈ B, b ≠ 1 ∧ Z ⊓ Subgroup.centralizer {b} ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hZ1
    rw [← hgenZ]
    exact le_bot_iff.mp (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
      (hcon b hb hb1).le)
  have key : ∀ b ∈ B, b ≠ 1 → Z ⊓ Subgroup.centralizer {b} ≠ ⊥ →
      CFSG.fittingSubgroupOf (kOf (thetaOf θ (Subgroup.zpowers b)) ⊓ ssol p A θ) ≤ Z := by
    intro b hb hb1 hne
    have hE := zpowers_mem_rSet h hB hb hb1
    refine fitting_le_of_inf_ne_bot h hE (hI _ hE) hZS hZadm ?_
    rwa [centralizer_zpowers_eq_singleton]
  have hD1Z : dOne p A θ ≤ Z := by
    have hE₀ := zpowers_mem_rSet h hB hb₀B hb₀1
    have := dOne_le_fitting h hE₀
    rw [inf_comm] at this
    exact this.trans (key b₀ hb₀B hb₀1 hb₀ne)
  have hD1C : ∀ b ∈ B, b ≠ 1 → Z ⊓ Subgroup.centralizer {b} ≠ ⊥ := by
    intro b hb hb1 hbot
    apply dOne_ne_bot h
    refine le_bot_iff.mp (hbot ▸ le_inf hD1Z ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have hxD : x ∈ dsub A θ := dOne_le_dsub h hx
    exact Subgroup.mem_centralizer_iff.mp (dsub_le_centralizer hθ hxD) c (hBA hb)
  have hZs : Z ≤ sOne p A θ := by
    have hZc : Z ≤ Subgroup.centralizer (dOne p A θ : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun d hd => hZcomm d (hD1Z hd) z hz
    exact le_inf (le_thetaN hZmem (hZc.trans (Subgroup.centralizer_le_normalizer _))) hZc
  have hsOneA : Admits A (sOne p A θ) := (sOne_mem_assoc h).1
  have hgenS := iSup_inf_centralizer h.hyp.prime hBel (by rw [hBcard]) (hBA.trans hsOneA)
    (sOne_mem_assoc h).2.1
  have hsZ : sOne p A θ ≤ Z := by
    rw [← hgenS]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    have hE := zpowers_mem_rSet h hB hb hb1
    have h1 : sOne p A θ ⊓ Subgroup.centralizer {b} ≤
        sOne p A θ ⊓ thetaOf θ (Subgroup.zpowers b) := by
      refine le_inf inf_le_left ?_
      have := inf_centralizer_le_thetaOf (sOne_mem_assoc h) (zpowers_le_A h hB hb)
      rw [centralizer_zpowers_eq_singleton] at this
      exact fun x hx => this hx
    rw [Counterexample.lemma611 h hE] at h1
    exact h1.trans (key b hb hb1 (hD1C b hb hb1))
  have hZeq : sOne p A θ = Z := le_antisymm hsZ hZs
  rw [hZeq]
  exact ⟨⟨fun a b => Subtype.ext (hZcomm a a.2 b b.2)⟩⟩

end CaseI

section CaseII

variable (h : Counterexample p A θ)

include h

theorem isMulCommutative_sOne_of_not_psl3
    (hII : ∀ E ∈ rSet p A θ, ∀ J ∈ lcal (thetaOf θ E), ¬ IsPSL3 p J) :
    IsMulCommutative (sOne p A θ) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨B, hB2⟩ := h.rSetN_two_nonempty
  have hB : B ∈ rSet p A θ := hB2.1
  have hBcard : Nat.card B = p ^ 2 := hB2.2
  obtain ⟨-, hBA, -⟩ := h.mem_rSet_iff.mp hB
  have hBel : IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.hyp.elemAbelian hBA
  obtain ⟨J, hJ⟩ := exists_mem_lcal h hB
  obtain ⟨t, htD0, ht2, htfpf⟩ := h.lemma68a hB hJ (hII B hB J hJ)
  have htD : t ∈ dsub A θ := ((Sec6S31.dZero_eq h hB).le.trans inf_le_left) htD0
  have htS : t ∈ Subgroup.normalizer (sOne p A θ : Set G) := dsub_le_normalizer_sOne h htD
  have ht2' : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2] at this
    simpa [sq] using this
  have hsOneA : Admits A (sOne p A θ) := (sOne_mem_assoc h).1
  have hU : sOne p A θ ⊓ Subgroup.centralizer {t} = ⊥ := by
    by_contra hne
    have hBt : B ≤ Subgroup.centralizer ({t} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (dsub_le_centralizer hθ htD) a (hBA ha)
    have hUA : Admits B (sOne p A θ ⊓ Subgroup.centralizer {t}) := fun a ha =>
      Lemma216.mem_normalizer_inf (hsOneA (hBA ha)) (admits_centralizer_singleton hBt ha)
    have hUcop : Nat.Coprime p
        (Nat.card (sOne p A θ ⊓ Subgroup.centralizer {t} : Subgroup G)) :=
      (sOne_mem_assoc h).2.1.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    have hgen := iSup_inf_centralizer h.hyp.prime hBel (by rw [hBcard]) hUA hUcop
    obtain ⟨b, hb, hb1, hbne⟩ : ∃ b ∈ B, b ≠ 1 ∧
        (sOne p A θ ⊓ Subgroup.centralizer {t}) ⊓ Subgroup.centralizer {b} ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [← hgen]
      exact le_bot_iff.mp (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
        (hcon b hb hb1).le)
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbne
    have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
    obtain ⟨⟨hxS, hxt⟩, hxb⟩ := hx
    have hE := zpowers_mem_rSet h hB hb hb1
    have hxH : x ∈ sOne p A θ ⊓ thetaOf θ (Subgroup.zpowers b) := by
      refine ⟨hxS, ?_⟩
      have := inf_centralizer_le_thetaOf (sOne_mem_assoc h) (zpowers_le_A h hB hb)
      rw [centralizer_zpowers_eq_singleton] at this
      exact this ⟨hxS, hxb⟩
    rw [Counterexample.lemma611 h hE, inf_comm] at hxH
    obtain ⟨J', hJ'⟩ := exists_mem_lcal h hE
    apply h.lemma68b hE hJ' (hII _ hE J' hJ') htD0 ht2 htfpf x hxH hx1'
    have := Subgroup.mem_centralizer_iff.mp hxt t (Set.mem_singleton t)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine isMulCommutative_of_fpf ht2' htS fun x hx hxt => ?_
  have : x ∈ sOne p A θ ⊓ Subgroup.centralizer {t} := by
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rwa [mul_inv_eq_iff_eq_mul] at hxt
  rw [hU, Subgroup.mem_bot] at this
  exact this

end CaseII

section Assembly

variable (h : Counterexample p A θ)

include h

theorem isMulCommutative_sOne :
    IsMulCommutative (sOne p A θ) := by
  by_cases hcase : ∃ E ∈ rSet p A θ, ∃ J ∈ lcal (thetaOf θ E), IsPSL3 p J
  · obtain ⟨E₀, hE₀, J₀, hJ₀, ⟨e'⟩⟩ := hcase
    refine isMulCommutative_sOne_of_psl3 h fun E hE J hJ => ?_
    obtain ⟨e⟩ := h.lemma610 hE₀ hE hJ₀ hJ
    exact ⟨e.symm.trans e'⟩
  · push Not at hcase
    exact isMulCommutative_sOne_of_not_psl3 h hcase

end Assembly

end Sec6S32

end CFSG.SignalizerFunctorTheorem.McBride.Near
