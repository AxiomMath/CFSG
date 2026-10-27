module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux

public section

open CFSG.Open
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Sec6S32

section Generic

variable {Γ : Type*} [Group Γ]

theorem isMulCommutative_of_fpf [Finite Γ] {S : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (htS : t ∈ Subgroup.normalizer (S : Set Γ))
    (hfpf : ∀ x ∈ S, t * x * t⁻¹ = x → x = 1) : IsMulCommutative S := by
  have hconj : ∀ x ∈ S, t * x * t⁻¹ ∈ S := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htS x).mp hx
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hc2 : ∀ x : Γ, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    rw [htinv]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; group
  let f : S → S := fun x => ⟨(x : Γ)⁻¹ * (t * x * t⁻¹), mul_mem (inv_mem x.2) (hconj x x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (x : Γ)⁻¹ * (t * x * t⁻¹) = (y : Γ)⁻¹ * (t * y * t⁻¹) := congrArg Subtype.val hxy
    have h3 : (y : Γ) * (x : Γ)⁻¹ * (t * x * t⁻¹) = t * y * t⁻¹ := by
      calc (y : Γ) * (x : Γ)⁻¹ * (t * x * t⁻¹) = y * ((x : Γ)⁻¹ * (t * x * t⁻¹)) := by group
        _ = y * ((y : Γ)⁻¹ * (t * y * t⁻¹)) := by rw [h1]
        _ = t * y * t⁻¹ := by group
    have h2 : t * ((y : Γ) * (x : Γ)⁻¹) * t⁻¹ = (y : Γ) * (x : Γ)⁻¹ := by
      calc t * ((y : Γ) * (x : Γ)⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
        _ = ((y : Γ) * (x : Γ)⁻¹ * (t * x * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by rw [h3]
        _ = (y : Γ) * (x : Γ)⁻¹ := by group
    have h4 : (y : Γ) * (x : Γ)⁻¹ = 1 :=
      hfpf _ (mul_mem y.2 (inv_mem x.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h4).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hinvert : ∀ g ∈ S, t * g * t⁻¹ = g⁻¹ := by
    intro g hg
    obtain ⟨x, hx⟩ := hsurj ⟨g, hg⟩
    have hgx : g = (x : Γ)⁻¹ * (t * x * t⁻¹) := (congrArg Subtype.val hx).symm
    rw [hgx]
    calc t * ((x : Γ)⁻¹ * (t * x * t⁻¹)) * t⁻¹
        = (t * (x : Γ)⁻¹ * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
      _ = (t * (x : Γ)⁻¹ * t⁻¹) * x := by rw [hc2]
      _ = ((x : Γ)⁻¹ * (t * x * t⁻¹))⁻¹ := by group
  refine ⟨⟨fun a b => ?_⟩⟩
  have hab : t * ((a : Γ) * b) * t⁻¹ = ((a : Γ) * b)⁻¹ := hinvert _ (mul_mem a.2 b.2)
  have hab' : t * ((a : Γ) * b) * t⁻¹ = (a : Γ)⁻¹ * (b : Γ)⁻¹ := by
    calc t * ((a : Γ) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = (a : Γ)⁻¹ * (b : Γ)⁻¹ := by rw [hinvert _ a.2, hinvert _ b.2]
  have hcomm : ((b : Γ) * a)⁻¹ = ((a : Γ) * b)⁻¹ := by
    rw [mul_inv_rev, ← hab', hab, mul_inv_rev]
  apply Subtype.ext
  exact inv_injective hcomm.symm

theorem mem_sectionCentralizer_sup {X V : Subgroup Γ} {g : Γ}
    (hgX : g ∈ Subgroup.normalizer (X : Set Γ)) (hV : V ≤ Subgroup.normalizer (X : Set Γ))
    (hgV : ∀ v ∈ V, ⁅g, v⁆ ∈ X) : g ∈ sectionCentralizer X (V ⊔ X) := by
  refine (Lemma216.mem_sectionCentralizer_iff_of_le le_sup_right).mpr ⟨hgX, fun y hy => ?_⟩
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right V X hV
  have hy' : y ∈ (V : Set Γ) * (X : Set Γ) := by
    rw [← hmul]
    exact hy
  obtain ⟨v, hv, x, hx, rfl⟩ := Set.mem_mul.mp hy'
  have e : ⁅g, v * x⁆ = ⁅g, v⁆ * (v * ⁅g, x⁆ * v⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine mul_mem (hgV v hv) ?_
  exact (Subgroup.mem_normalizer_iff.mp (hV hv) _).mp (Lemma216.commutator_mem_of_mem_normalizer
    hgX hx)

theorem isChiefFactorOf_bot {Γ' N' : Subgroup Γ} (hN'Γ : N' ≤ Γ') (hN'1 : N' ≠ ⊥)
    (hadm : Admits Γ' N') (hmin : ∀ M ≤ N', Admits Γ' M → M = ⊥ ∨ M = N') :
    IsChiefFactorOf Γ' N' ⊥ :=
  ⟨⟨bot_le, le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge⟩,
    ⟨hN'Γ, hadm⟩, bot_lt_iff_ne_bot.mpr hN'1, fun _ hK _ hKN => hmin _ hKN hK.2⟩

end Generic

section Setting

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem le_thetaN {X Y : Subgroup G} (hY : Y ∈ assoc p A θ)
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) : Y ≤ thetaN p A θ X :=
  le_iSup₂ (f := fun Y (_ : Y ∈ {Y : Subgroup G | Y ∈ assoc p A θ ∧
    Y ≤ Subgroup.normalizer (X : Set G)}) => Y) Y ⟨hY, hYX⟩

theorem thetaN_spec (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ assoc p A θ)
    (hX1 : X ≠ ⊥) :
    thetaN p A θ X ∈ assoc p A θ ∧ thetaN p A θ X ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨Y, hY, hYN, hYmax⟩ := h.isLocallyComplete X hX hX1
  have heq : thetaN p A θ X = Y :=
    le_antisymm (iSup₂_le fun Z hZ => hYmax Z hZ.1 hZ.2) (le_thetaN hY hYN)
  rw [heq]
  exact ⟨hY, hYN⟩

variable (h : Counterexample p A θ)

include h

theorem exists_mem_rSet :
    ∃ B, B ∈ rSet p A θ := by
  obtain ⟨B, hB⟩ := h.rSetN_two_nonempty
  exact ⟨B, hB.1⟩

theorem exists_mem_lcal
    {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    ∃ J, J ∈ lcal (thetaOf θ B) := by
  have H := Sec6S31.hyp h hB
  have hK := H.semisimpleAction
  obtain ⟨J, hJ⟩ : (lcal (kOf (thetaOf θ B))).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hK.ne_bot
    rw [← hK.isDirectProduct_lcal.sSup_eq, hcon, sSup_empty]
  exact ⟨J, H.lcal_kOf ▸ hJ⟩

theorem dOne_ne_bot :
    dOne p A θ ≠ ⊥ := by
  obtain ⟨B, hB⟩ := exists_mem_rSet h
  obtain ⟨J, hJ⟩ := exists_mem_lcal h hB
  have H := Sec6S31.hyp h hB
  have hK := H.semisimpleAction
  have hJ' : J ∈ lcal (kOf (thetaOf θ B)) := H.lcal_kOf ▸ hJ
  intro hbot
  apply hK.fittingSubgroupOf_smear_ne_bot hJ'
  have h1 := hK.fittingSubgroupOf_smear_le hJ'
  rw [Sec6S31.cenIn_kOf_eq h hB] at h1
  have h2 : dOne p A θ = CFSG.fittingSubgroupOf (dZero p A θ) := rfl
  rw [← h2, hbot] at h1
  exact le_bot_iff.mp h1

theorem admits_dOne
    {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    Admits (dsub A θ ⊔ A) (dOne p A θ) := by
  intro g hg
  have h1 := Lemma216.admits_cenIn_kOf (thetaOf θ B) A
  rw [cenIn_eq_dsub h.hyp.nearFunctor (Sec6S31.mem_mtil h hB)] at h1
  have h2 := h1 hg
  rw [Sec6S31.cenIn_kOf_eq h hB] at h2
  exact Lemma216.mem_normalizer_fittingSubgroupOf h2

theorem dOne_le_fitting
    {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    dOne p A θ ≤ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
  have hK := (Sec6S31.hyp h hB).semisimpleAction
  have hdK : dOne p A θ ≤ kOf (thetaOf θ B) :=
    (Subgroup.map_subtype_le _).trans ((Sec6S31.dZero_eq h hB).le.trans inf_le_right)
  have hdD : dZero p A θ ≤ dsub A θ := (Sec6S31.dZero_eq h hB).le.trans inf_le_left
  have hadm : Admits (cenIn (kOf (thetaOf θ B)) A ⊔ A) (dOne p A θ) := by
    rw [Sec6S31.cenIn_kOf_eq h hB]
    exact (sup_le_sup_right hdD A).trans (admits_dOne h hB)
  have := thm210f hK (X := dOne p A θ) hdK hadm (isNilpotent_fittingSubgroupOf _)
  rwa [Sec6S31.mOf_eq h hB] at this

theorem dOne_le_dsub :
    dOne p A θ ≤ dsub A θ := by
  obtain ⟨B, hB⟩ := exists_mem_rSet h
  exact (Subgroup.map_subtype_le _).trans ((Sec6S31.dZero_eq h hB).le.trans inf_le_left)

theorem dOne_mem_assoc :
    dOne p A θ ∈ assoc p A θ := by
  obtain ⟨B, hB⟩ := exists_mem_rSet h
  exact mem_assoc_of_le h.hyp.prime (dsub_mem_assoc h.hyp.nearFunctor) (dOne_le_dsub h)
    (le_sup_right.trans (admits_dOne h hB))

theorem sOne_mem_assoc :
    sOne p A θ ∈ assoc p A θ := by
  obtain ⟨B, hB⟩ := exists_mem_rSet h
  obtain ⟨hmem, -⟩ := thetaN_spec h (dOne_mem_assoc h) (dOne_ne_bot h)
  have hAD : A ≤ Subgroup.normalizer (dOne p A θ : Set G) :=
    le_sup_right.trans (admits_dOne h hB)
  have hadm : Admits A (sOne p A θ) := fun a ha =>
    Lemma216.mem_normalizer_inf (hmem.1 ha) (Lemma216.mem_normalizer_centralizer (hAD ha))
  exact mem_assoc_of_le h.hyp.prime hmem inf_le_left hadm

theorem dsub_le_normalizer_sOne :
    dsub A θ ≤ Subgroup.normalizer (sOne p A θ : Set G) := by
  obtain ⟨B, hB⟩ := exists_mem_rSet h
  intro d hd
  have hθ := h.hyp.nearFunctor
  have hdN : d ∈ Subgroup.normalizer (dOne p A θ : Set G) :=
    admits_dOne h hB (Subgroup.mem_sup_left hd)
  have hDle : dsub A θ ≤ thetaN p A θ (dOne p A θ) :=
    le_thetaN (dsub_mem_assoc hθ) fun x hx => admits_dOne h hB (Subgroup.mem_sup_left hx)
  exact Lemma216.mem_normalizer_inf (Subgroup.le_normalizer (hDle hd))
    (Lemma216.mem_normalizer_centralizer hdN)

theorem le_inf_kOf_of_minimal
    {B N : Subgroup G} (hB : B ∈ rSet p A θ)
    (hNH : N ≤ thetaOf θ B ⊓ ssol p A θ) (hN1 : N ≠ ⊥)
    (hNΓ : Admits ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) N)
    (hmin : ∀ N' ≤ N, Admits ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) N' → N' = ⊥ ∨ N' = N) :
    N ≤ ssol p A θ ⊓ kOf (thetaOf θ B) := by
  have Hhyp := Sec6S31.hyp h hB
  have hSA : A ≤ Subgroup.normalizer (ssol p A θ : Set G) := h.ssol_mem_assoc.1
  have hΓM : Admits ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
    refine sup_le (fun x hx => ?_) (fun a ha => ?_)
    · exact Lemma216.mem_normalizer_inf (Subgroup.le_normalizer hx.2)
        (Nonsolv.le_normalizer_kOf _ hx.1)
    · exact Lemma216.mem_normalizer_inf (hSA ha) (Hhyp.A_le_normalizer ha)
  have hMΓ : ssol p A θ ⊓ kOf (thetaOf θ B) ≤ (thetaOf θ B ⊓ ssol p A θ) ⊔ A :=
    (le_inf (inf_le_right.trans (kOf_le _)) inf_le_left).trans le_sup_left
  have hNMadm : Admits ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) (N ⊓ (ssol p A θ ⊓ kOf (thetaOf θ B))) :=
    fun g hg => Lemma216.mem_normalizer_inf (hNΓ hg) (hΓM hg)
  rcases hmin _ inf_le_left hNMadm with h0 | h0
  · exfalso
    have hD1M : dOne p A θ ≤ ssol p A θ ⊓ kOf (thetaOf θ B) :=
      (dOne_le_fitting h hB).trans (Subgroup.map_subtype_le _)
    have hNC : N ≤ cenIn (thetaOf θ B) (dOne p A θ : Set G) := by
      intro n hn
      refine ⟨(hNH hn).1, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hdM := hD1M hd
      have hdΓ := hMΓ hdM
      have hnΓ : n ∈ (thetaOf θ B ⊓ ssol p A θ) ⊔ A := Subgroup.mem_sup_left (hNH hn)
      have h1 : n * d * n⁻¹ * d⁻¹ ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hNΓ hdΓ) n⁻¹).mp (inv_mem hn)
        have h2 := mul_mem hn this
        simpa [mul_assoc] using h2
      have h2 : n * d * n⁻¹ * d⁻¹ ∈ ssol p A θ ⊓ kOf (thetaOf θ B) := by
        have := (Subgroup.mem_normalizer_iff.mp (hΓM hnΓ) d).mp hdM
        exact mul_mem this (inv_mem hdM)
      have h3 : n * d * n⁻¹ * d⁻¹ ∈ N ⊓ (ssol p A θ ⊓ kOf (thetaOf θ B)) :=
        Subgroup.mem_inf.mpr ⟨h1, h2⟩
      rw [h0, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    have hNM : N ≤ ssol p A θ ⊓ kOf (thetaOf θ B) := by
      have := hNC
      rw [Sec6S31.cenIn_dOne_eq h hB] at this
      exact this.trans (Subgroup.map_subtype_le _)
    exact hN1 (by rw [← inf_eq_left.mpr hNM, h0])
  · exact inf_eq_left.mp h0

end Setting

end Sec6S32

end CFSG.SignalizerFunctorTheorem.McBride.Near
