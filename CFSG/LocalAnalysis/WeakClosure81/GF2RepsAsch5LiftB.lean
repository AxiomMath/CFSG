module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5LiftA
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)
open CFSG.Blueprint (LieModel)

theorem exists_mulEquiv_map_of_hasQuotShape {Q : Type} [Group Q] {H L N : Subgroup Q}
    (hLH : L ≤ H) {Hb : Type} [Group Hb] (π : ↥H →* Hb)
    (hker : ∀ x : ↥H, π x = 1 ↔ (x : Q) ∈ N) {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape L (N : Set Q) P) :
    ∃ (X : Type) (_ : Group X), P X ∧ Nonempty (↥((L.subgroupOf H).map π) ≃* X) := by
  obtain ⟨X, hXg, φ, hφ, hkerφ, hP⟩ := h
  have hrange : (π.comp (Subgroup.inclusion hLH)).range = (L.subgroupOf H).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkerEq : (π.comp (Subgroup.inclusion hLH)).ker = φ.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hkerφ l]
    exact hker (Subgroup.inclusion hLH l)
  refine ⟨X, hXg, hP, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange (π.comp (Subgroup.inclusion hLH))).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)))

theorem false_of_psp4_overgroups {p : ℕ}
    (hOver : ∀ (X : Type) [Group X] [Finite X],
      LieModel X .PSp 2 p 1 → AlmostSimpleOvergroupPair X)
    {Q : Type} [Group Q] [Finite Q] {H T M L : Subgroup Q}
    (hT : IsSylowIn 2 T H) (hU : calNIn H T = {M})
    (hL : IsComponentModN (OInf H) H L) (hLT : L ⊔ T = H)
    (hX : HasQuotShape L (OInf H : Set Q)
      (fun X _ => LieModel X .PSp 2 p 1)) : False := by
  obtain ⟨hNn, hNL, hLH, hLsub, hq⟩ := hL
  haveI := hNn
  let N' : Subgroup ↥H := (OInf H).subgroupOf H
  let π : ↥H →* ↥H ⧸ N' := QuotientGroup.mk' N'
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N'
  have hker : ∀ x : ↥H, π x = 1 ↔ (x : Q) ∈ OInf H := by
    intro x
    rw [show π x = QuotientGroup.mk x from rfl, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hTH : T ≤ H := hT.le
  obtain ⟨X₁, _, hX₁, ⟨e₁⟩⟩ := exists_mulEquiv_map_of_hasQuotShape hLH π hker hq
  obtain ⟨X₂, _, hX₂, ⟨e₂⟩⟩ := exists_mulEquiv_map_of_hasQuotShape hLH π hker hX
  have hLie : LieModel ↥((L.subgroupOf H).map π) .PSp 2 p 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e₂.symm hX₂
  have hs : IsSimpleGroup ↥((L.subgroupOf H).map π) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie
  have hnab : ∃ a b : ↥((L.subgroupOf H).map π), a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hX₁
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨e₁.symm a, e₁.symm b, fun hh => hab ?_⟩
    have h2 := congrArg e₁ hh
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
  have hsub : ((L.subgroupOf H).map π).IsSubnormal :=
    Subgroup.IsSubnormal.map hπ (CFSG.Open.IsSubnormal.subgroupOf hLsub)
  have hLbTb : (L.subgroupOf H).map π ⊔ (T.subgroupOf H).map π = ⊤ := by
    have h1 : (L.subgroupOf H) ⊔ (T.subgroupOf H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLH hTH, hLT, Subgroup.subgroupOf_self]
    rw [← Subgroup.map_sup, h1, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπ]
  have hTb : IsPGroup 2 ↥((T.subgroupOf H).map π) := by
    have h1 : IsPGroup 2 ↥((π.comp (Subgroup.inclusion hTH)).range) :=
      IsPGroup.of_surjective hT.isPGroup (π.comp (Subgroup.inclusion hTH)).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.range_comp, Subgroup.inclusion_range] at h1
  obtain ⟨D₁, D₂, hTD₁, hTD₂, hD₁, hD₂, hD⟩ :=
    exists_proper_overgroups_of_almostSimple_overgroups (hOver _ hLie) hTb hLbTb hsub hs hnab
  have hMmem : M ∈ calNIn H T := by rw [hU]; exact Set.mem_singleton M
  have hMH : M < H := hMmem.2.1
  have key : ∀ D : Subgroup (↥H ⧸ N'), (T.subgroupOf H).map π ≤ D → D < ⊤ →
      (D.comap π).map H.subtype ≤ M := by
    intro D hTD hDtop
    have hTY : T ≤ (D.comap π).map H.subtype := by
      intro t ht
      refine ⟨⟨t, hTH ht⟩, ?_, rfl⟩
      exact hTD (Subgroup.mem_map_of_mem π (show (⟨t, hTH ht⟩ : ↥H) ∈ T.subgroupOf H from ht))
    have hYH : (D.comap π).map H.subtype < H := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun heq => ?_
      apply (ne_of_lt hDtop)
      rw [eq_top_iff]
      intro b _
      obtain ⟨x, rfl⟩ := hπ b
      have hx : (x : Q) ∈ (D.comap π).map H.subtype := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    obtain ⟨X, hXm, hYX⟩ := exists_mem_calNIn_of_lt hTY hYH
    rw [hU] at hXm
    rw [← Set.mem_singleton_iff.mp hXm]
    exact hYX
  have h1 := key D₁ hTD₁ hD₁
  have h2 := key D₂ hTD₂ hD₂
  have hrange₁ : D₁ ≤ π.range := by
    rw [MonoidHom.range_eq_top.mpr hπ]
    exact le_top
  have hrange₂ : D₂ ≤ π.range := by
    rw [MonoidHom.range_eq_top.mpr hπ]
    exact le_top
  have hsupcomap : D₁.comap π ⊔ D₂.comap π = ⊤ := by
    rw [Subgroup.comap_sup_eq_of_le_range (f := π) hrange₁ hrange₂, hD, Subgroup.comap_top]
  have hsupH : (D₁.comap π).map H.subtype ⊔ (D₂.comap π).map H.subtype = H := by
    rw [← Subgroup.map_sup, hsupcomap, Subgroup.map_top, Subgroup.range_subtype]
  have : H ≤ M := hsupH ▸ sup_le h1 h2
  exact absurd hMH (not_lt_of_ge this)

theorem false_of_psp4Three (h : Asch5_PSp4Three) {Q : Type} [Group Q] [Finite Q]
    {H T M L : Subgroup Q} (hT : IsSylowIn 2 T H) (hU : calNIn H T = {M})
    (hL : IsComponentModN (OInf H) H L) (hLT : L ⊔ T = H)
    (hX : HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSp 2 3 1)) : False := by
  refine false_of_psp4_overgroups (p := 3) ?_ hT hU hL hLT hX
  intro X _ _ hLie
  exact h X hLie

end CFSG.LocalAnalysis.WeakClosure81
