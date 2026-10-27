module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Wr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)

variable {G : Type} [Group G] {H : Subgroup G} {Y : Type} [Group Y]

@[expose] def preG (π : ↥H →* Y) (E : Subgroup Y) : Subgroup G := (E.comap π).map H.subtype

theorem preG_le (π : ↥H →* Y) (E : Subgroup Y) : preG π E ≤ H := Subgroup.map_subtype_le _

theorem mem_preG_iff {π : ↥H →* Y} {E : Subgroup Y} {x : G} :
    x ∈ preG π E ↔ ∃ hx : x ∈ H, π ⟨x, hx⟩ ∈ E := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

@[expose] noncomputable def toE (π : ↥H →* Y) (E : Subgroup Y) : ↥(preG π E) →* ↥E :=
  (π.subgroupComap E).comp
    (Subgroup.equivMapOfInjective (E.comap π) H.subtype H.subtype_injective).symm.toMonoidHom

theorem coe_toE (π : ↥H →* Y) (E : Subgroup Y) (l : ↥(preG π E)) :
    ((toE π E l : ↥E) : Y) = π ⟨(l : G), preG_le π E l.2⟩ := by
  have h1 : (((Subgroup.equivMapOfInjective (E.comap π) H.subtype H.subtype_injective).symm l :
      ↥(E.comap π)) : ↥H) = ⟨(l : G), preG_le π E l.2⟩ := by
    apply Subtype.ext
    have h3 := congrArg (fun z : ↥((E.comap π).map H.subtype) => (z : G))
      (MulEquiv.apply_symm_apply
        (Subgroup.equivMapOfInjective (E.comap π) H.subtype H.subtype_injective) l)
    simp only [Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_subtype] at h3
    exact h3
  change π (((Subgroup.equivMapOfInjective (E.comap π) H.subtype H.subtype_injective).symm l :
      ↥(E.comap π)) : ↥H) = _
  rw [h1]

theorem toE_surjective {π : ↥H →* Y} (hπ : Function.Surjective π) (E : Subgroup Y) :
    Function.Surjective (toE π E) :=
  (MonoidHom.subgroupComap_surjective π E hπ).comp (MulEquiv.surjective _)

theorem toE_eq_one_iff (π : ↥H →* Y) (E : Subgroup Y) (l : ↥(preG π E)) :
    toE π E l = 1 ↔ (l : G) ∈ π.ker.map H.subtype := by
  rw [← Subtype.coe_inj, coe_toE, OneMemClass.coe_one]
  constructor
  · intro h
    exact ⟨⟨(l : G), preG_le π E l.2⟩, h, rfl⟩
  · rintro ⟨k, hk, hkl⟩
    have : k = ⟨(l : G), preG_le π E l.2⟩ := Subtype.ext hkl
    rw [← this]
    exact hk

@[expose] noncomputable def innPsi (π : ↥H →* Y) (E : Subgroup Y) {A : Subgroup (MulAut ↥E)}
    (hA : innAutOf ↥E ≤ A) : ↥(preG π E) →* ↥((innAutOf ↥E).subgroupOf A) :=
  (((MulAut.conj : ↥E →* MulAut ↥E).comp (toE π E)).codRestrict A
    (fun l => hA ⟨toE π E l, rfl⟩)).codRestrict ((innAutOf ↥E).subgroupOf A)
    (fun l => Subgroup.mem_subgroupOf.mpr ⟨toE π E l, rfl⟩)

theorem coe_innPsi (π : ↥H →* Y) (E : Subgroup Y) {A : Subgroup (MulAut ↥E)}
    (hA : innAutOf ↥E ≤ A) (l : ↥(preG π E)) :
    (((innPsi π E hA l : ↥((innAutOf ↥E).subgroupOf A)) : ↥A) : MulAut ↥E) =
      MulAut.conj (toE π E l) := rfl

theorem innPsi_surjective {π : ↥H →* Y} (hπ : Function.Surjective π) (E : Subgroup Y)
    {A : Subgroup (MulAut ↥E)} (hA : innAutOf ↥E ≤ A) : Function.Surjective (innPsi π E hA) := by
  rintro ⟨⟨a, haA⟩, ha⟩
  obtain ⟨e, he⟩ := Subgroup.mem_subgroupOf.mp ha
  obtain ⟨l, rfl⟩ := toE_surjective hπ E e
  refine ⟨l, Subtype.ext (Subtype.ext ?_)⟩
  exact he

theorem innPsi_eq_one_iff (π : ↥H →* Y) {E : Subgroup Y} (hZ : center ↥E = ⊥)
    {A : Subgroup (MulAut ↥E)} (hA : innAutOf ↥E ≤ A) (l : ↥(preG π E)) :
    innPsi π E hA l = 1 ↔ (l : G) ∈ π.ker.map H.subtype := by
  rw [← toE_eq_one_iff]
  constructor
  · intro h
    have h1 : MulAut.conj (toE π E l) = 1 := by
      have := congrArg (fun x : ↥((innAutOf ↥E).subgroupOf A) => ((x : ↥A) : MulAut ↥E)) h
      simpa [coe_innPsi] using this
    have hc : toE π E l ∈ center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun f : MulAut ↥E => f y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * toE π E l = toE π E l * y * (toE π E l)⁻¹ * toE π E l := by rw [h2]
        _ = toE π E l * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_innPsi, h, map_one]
    rfl

theorem mem_normalizer_preG {π : ↥H →* Y} {E : Subgroup Y} {s : ↥H}
    (hs : π s ∈ normalizer (E : Set Y)) : (s : G) ∈ normalizer (preG π E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_preG_iff, mem_preG_iff]
  by_cases hx : x ∈ H
  · have hsx : (s : G) * x * (s : G)⁻¹ ∈ H := H.mul_mem (H.mul_mem s.2 hx) (H.inv_mem s.2)
    have hπ : π ⟨(s : G) * x * (s : G)⁻¹, hsx⟩ = π s * π ⟨x, hx⟩ * (π s)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    constructor
    · rintro ⟨hx', h⟩
      refine ⟨hsx, ?_⟩
      rw [hπ]
      exact (Subgroup.mem_normalizer_iff.mp hs _).mp h
    · rintro ⟨hx', h⟩
      refine ⟨hx, ?_⟩
      rw [hπ] at h
      exact (Subgroup.mem_normalizer_iff.mp hs _).mpr h
  · constructor
    · rintro ⟨hx', -⟩
      exact absurd hx' hx
    · rintro ⟨hx', -⟩
      apply absurd _ hx
      have := H.mul_mem (H.mul_mem (H.inv_mem s.2) hx') s.2
      simpa [mul_assoc] using this

theorem innPsi_conj (π : ↥H →* Y) (E : Subgroup Y) {A : Subgroup (MulAut ↥E)}
    (hA : innAutOf ↥E ≤ A) {s : ↥H} {n : ↥(normalizer (E : Set Y))} (hn : (n : Y) = π s)
    (l l₂ : ↥(preG π E)) (h : (l₂ : G) = (s : G) * l * (s : G)⁻¹) :
    (((innPsi π E hA l₂ : ↥((innAutOf ↥E).subgroupOf A)) : ↥A) : MulAut ↥E) =
      autJ E n * (((innPsi π E hA l : ↥((innAutOf ↥E).subgroupOf A)) : ↥A) : MulAut ↥E) *
        (autJ E n)⁻¹ := by
  rw [coe_innPsi, coe_innPsi]
  have he : toE π E l₂ = autJ E n (toE π E l) := by
    apply Subtype.ext
    rw [autJ_apply, coe_toE, coe_toE, hn, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, he, map_mul, map_inv,
    MulEquiv.apply_symm_apply, MulAut.inv_apply]

theorem exists_of_mem_autT {T : Subgroup G} (π : ↥H →* Y) {E : Subgroup Y} {t' : MulAut ↥E}
    (ht' : t' ∈ autT ((T.subgroupOf H).map π) E) :
    ∃ s : ↥H, (s : G) ∈ T ∧ ∃ n : ↥(normalizer (E : Set Y)), (n : Y) = π s ∧ autJ E n = t' := by
  obtain ⟨n, hn, rfl⟩ := ht'
  obtain ⟨s, hs, hsn⟩ := Subgroup.mem_subgroupOf.mp hn
  exact ⟨s, Subgroup.mem_subgroupOf.mp hs, n, hsn.symm, rfl⟩

theorem oInf_top_eq_bot {Q : Type} [Group Q] [Finite Q] (h : CFSG.solvableRadical Q = ⊥) :
    OInf (⊤ : Subgroup Q) = ⊥ := by
  set N : Subgroup Q := (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype
  have hsurj : Function.Surjective (⊤ : Subgroup Q).subtype := fun x => ⟨⟨x, trivial⟩, rfl⟩
  have hNn : N.Normal := Subgroup.Normal.map inferInstance _ hsurj
  haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥(⊤ : Subgroup Q)) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hNs : Group.IsSolvable ↥N :=
    Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical ↥(⊤ : Subgroup Q)).equivMapOfInjective _
        (⊤ : Subgroup Q).subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have := CFSG.Quasithin.A3.le_solvableRadical hNn hNs
  rw [h] at this
  exact le_bot_iff.mp this

end CFSG.LocalAnalysis.WeakClosure81

end
