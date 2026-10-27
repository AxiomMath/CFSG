module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210 Thm210g

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G J : Subgroup Γ}

section Finite

variable [Finite Γ]

theorem SemisimpleAction.exists_noncomm_cenIn
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ x ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)), ∃ c ∈ cenIn J (norIn A J),
      c * x * c⁻¹ ≠ x := by
  obtain ⟨f, hf, hC, hC₀, -, -⟩ := h.exists_frame_data hJ
  have hfrob := (near_frobenius (h.nearSimple hJ) hf).2.1
  unfold IsFrobeniusWithKernel at hfrob
  obtain ⟨hKne, -, -, V, hV, hVH, -, -, hfpf⟩ := hfrob
  by_contra hcon
  push Not at hcon
  apply hKne
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV
  have hvC : ((v : ↥J) : Γ) ∈ cenIn J (norIn A J) := hC ▸ ⟨v, hVH v.2, rfl⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hkF : ((k : ↥J) : Γ) ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := hC₀ ▸ ⟨k, hk, rfl⟩
  have h1 := hcon _ hkF _ hvC
  have h2 : ((v : ↥J) : Γ) * (k : Γ) = (k : Γ) * ((v : ↥J) : Γ) := by
    rwa [mul_inv_eq_iff_eq_mul] at h1
  refine hfpf (v : ↥J) v.2 (fun h => hv1 (Subtype.ext h)) k hk (Subtype.ext h2)

theorem SemisimpleAction.exists_noncomm_smear
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ x ∈ CFSG.fittingSubgroupOf (smear J A), ∃ d ∈ smear J A, d * x * d⁻¹ ≠ x := by
  obtain ⟨x, hx, c, hc, hne⟩ := h.exists_noncomm_cenIn hJ
  have hG := h.isDirectProduct_lcal
  rw [← h.projIn_fittingSubgroupOf_smear hJ] at hx
  rw [← h.projIn_smear hJ] at hc
  obtain ⟨y, hy, rfl⟩ := (hG.mem_projIn_iff hJ).1 hx
  obtain ⟨d, hd, rfl⟩ := (hG.mem_projIn_iff hJ).1 hc
  refine ⟨y, hy, d, hd, fun hcon => hne ?_⟩
  have e : d * y * d⁻¹ = y := Subtype.ext hcon
  have := congrArg (fun z => ((hG.coord hJ z : J) : Γ)) e
  simpa [map_mul, map_inv] using this

theorem SemisimpleAction.fittingSubgroupOf_smear_le_of_inf_ne_bot
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {Y : Subgroup Γ} (hY : Admits (smear J A) Y) (hne : Y ⊓ smear J A ≠ ⊥) :
    CFSG.fittingSubgroupOf (smear J A) ≤ Y := by
  have hnorm : ((Y ⊓ smear J A).subgroupOf (smear J A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro x s hx hs
    obtain ⟨hxY, hxS⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hY hs) x).1 hxY,
      mul_mem (mul_mem hs hxS) (inv_mem hs)⟩
  exact (h.fittingSubgroupOf_smear_le_of_normal hJ inf_le_right hnorm hne).trans inf_le_left

theorem SemisimpleAction.le_kJ_or_le_normalizer
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {P Q : Subgroup Γ} (hQJ : Q ≤ J)
    (hCP : cenIn J (norIn A J) ≤ Subgroup.normalizer (P : Set Γ))
    (hQP : Q ≤ Subgroup.normalizer (P : Set Γ)) :
    Q ≤ kJ A J ∨ J ≤ Subgroup.normalizer (P : Set Γ) := by
  by_cases hH : norIn J (P : Set Γ) = J
  · exact Or.inr (hH ▸ inf_le_right)
  · left
    have hle : norIn J (P : Set Γ) ≤ kJ A J :=
      h.le_kJ_of_le_of_ne hJ inf_le_left (le_inf inf_le_left hCP) hH
    exact fun x hx => hle (Subgroup.mem_inf.2 ⟨hQJ hx, hQP hx⟩)

@[expose] def Thm210g.orbSet (A J : Subgroup Γ) : Set (Subgroup Γ) :=
  {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom}

@[expose] def Thm210g.outOrbit (G A J : Subgroup Γ) : Subgroup Γ :=
  sSup (lcal G \ orbSet A J)

omit [Finite Γ] in
theorem Thm210g.self_mem_orbSet (A J : Subgroup Γ) : J ∈ orbSet A J :=
  ⟨1, one_mem A, (map_conj_one J).symm⟩

omit [Finite Γ] in
theorem Thm210g.orbSet_subset_lcal (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    orbSet A J ⊆ lcal G := by
  rintro _ ⟨a, ha, rfl⟩
  exact h.permutes_lcal a ha J hJ

omit [Finite Γ] in
theorem Thm210g.sSup_orbSet (A J : Subgroup Γ) : sSup (orbSet A J) = orbitClosure J A := by
  refine le_antisymm (sSup_le ?_) (orbitClosure_le fun a ha => le_sSup ⟨a, ha, rfl⟩)
  rintro _ ⟨a, ha, rfl⟩
  exact map_conj_le_orbitClosure J ha

omit [Finite Γ] in
theorem Thm210g.orbitClosure_le_group (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    orbitClosure J A ≤ G := by
  rw [← sSup_orbSet]
  exact sSup_le fun K hK => lcal_le (orbSet_subset_lcal h hJ hK)

omit [Finite Γ] in
theorem Thm210g.outOrbit_le (G A J : Subgroup Γ) : outOrbit G A J ≤ G :=
  sSup_le fun _ hK => lcal_le hK.1

theorem Thm210g.commute_orbitClosure_outOrbit (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : ∀ x ∈ orbitClosure J A, ∀ y ∈ outOrbit G A J, Commute x y := by
  rw [← sSup_orbSet]
  exact commute_sSup_sSup h.isDirectProduct_lcal (orbSet_subset_lcal h hJ) Set.sdiff_subset
    Set.disjoint_sdiff_right

theorem Thm210g.orbitClosure_sup_outOrbit (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : orbitClosure J A ⊔ outOrbit G A J = G := by
  rw [← sSup_orbSet, outOrbit, ← sSup_union, Set.union_sdiff_cancel (orbSet_subset_lcal h hJ)]
  exact h.isDirectProduct_lcal.sSup_eq

theorem Thm210g.exists_mul_orbitClosure_outOrbit (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {x : Γ} (hx : x ∈ G) :
    ∃ y ∈ orbitClosure J A, ∃ l ∈ outOrbit G A J, y * l = x := by
  rw [← orbitClosure_sup_outOrbit h hJ] at hx
  exact (mem_sup_iff_of_commute (commute_orbitClosure_outOrbit h hJ)).1 hx

omit [Finite Γ] in
theorem Thm210g.outOrbit_le_sSup_diff (G A J : Subgroup Γ) :
    outOrbit G A J ≤ sSup (lcal G \ {J}) :=
  sSup_le_sSup fun _ hK =>
    ⟨hK.1, fun hKJ => hK.2 (Set.mem_singleton_iff.1 hKJ ▸ self_mem_orbSet A J)⟩

theorem Thm210g.le_normalizer_orbitClosure (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : G ≤ Subgroup.normalizer (orbitClosure J A : Set Γ) := by
  rw [← sSup_orbSet]
  exact le_normalizer_sSup h.isDirectProduct_lcal (orbSet_subset_lcal h hJ)

theorem Thm210g.le_normalizer_outOrbit (h : SemisimpleAction p A G) :
    G ≤ Subgroup.normalizer (outOrbit G A J : Set Γ) :=
  le_normalizer_sSup h.isDirectProduct_lcal Set.sdiff_subset

omit [Finite Γ] in
theorem Thm210g.admits_outOrbit (h : SemisimpleAction p A G) :
    A ≤ Subgroup.normalizer (outOrbit G A J : Set Γ) := by
  refine Thm210.le_normalizer_of_conj_mem fun a ha x hx => ?_
  have hle : outOrbit G A J ≤ (outOrbit G A J).comap (MulAut.conj a).toMonoidHom := by
    refine sSup_le fun K hK y hy => ?_
    have hK' : K.map (MulAut.conj a).toMonoidHom ∈ lcal G \ orbSet A J := by
      refine ⟨h.permutes_lcal a ha K hK.1, ?_⟩
      rintro ⟨b, hb, hKb⟩
      refine hK.2 ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb, ?_⟩
      rw [← map_conj_map_conj, ← hKb, map_conj_map_conj, inv_mul_cancel, map_conj_one]
    exact le_sSup hK' ⟨y, hy, rfl⟩
  simpa using hle hx

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near
