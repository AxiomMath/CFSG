module

public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SzN15

open CFSG.QuasithinUnique

section Cover

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

theorem isSylowTwoOf_top_of {G : Type*} [Group G] {S : Subgroup G} (h2 : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.index) : IsSylowTwoOf S ⊤ := by
  refine ⟨le_top, h2, ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact hidx

theorem exists_sylow_cover {Γ X : Type*} [Group Γ] [Finite Γ] [Group X] (π : Γ →* X)
    (hπ : Function.Surjective π) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    ∃ T : Subgroup Γ, IsSylowTwoOf T ⊤ ∧ T.map π = S := by
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨P⟩ : Nonempty (Sylow 2 Γ) := inferInstance
  have hP2 : IsPGroup 2 (P : Subgroup Γ) := P.isPGroup'
  have hPidx : ¬ 2 ∣ (P : Subgroup Γ).index := P.not_dvd_index
  have hA2 : IsPGroup 2 ((P : Subgroup Γ).map π) := hP2.map π
  have hAidx : ¬ 2 ∣ ((P : Subgroup Γ).map π).index := fun h =>
    hPidx (h.trans (Subgroup.index_map_dvd (P : Subgroup Γ) hπ))
  have hA : IsSylowTwoOf ((P : Subgroup Γ).map π) ⊤ := isSylowTwoOf_top_of hA2 hAidx
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hA) (isSylowTwoOf_iff_isSylowOf.1 hS)
  obtain ⟨γ, rfl⟩ := hπ k
  refine ⟨(P : Subgroup Γ).map (MulAut.conj γ).toMonoidHom, ?_, ?_⟩
  · have h := isSylowOf_map_injective (p := 2) (MulAut.conj γ).toMonoidHom
      (MulAut.conj γ).injective (isSylowTwoOf_iff_isSylowOf.1 (isSylowTwoOf_top_of hP2 hPidx))
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj γ).surjective] at h
    exact isSylowTwoOf_iff_isSylowOf.2 h
  · ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ht
      rw [hk]
      refine Subgroup.mem_map.2 ⟨p, hp, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group
    · intro hx
      have h1 := (hk x).1 hx
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 h1
      refine ⟨γ * p * γ⁻¹, Subgroup.mem_map.2 ⟨p, hp, by simp⟩, ?_⟩
      simp only [map_mul, map_inv, hpx]
      group

end Cover

section Good

open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

@[expose] def GoodCoatom (X S : Subgroup (MulAut V)) : Prop :=
  ∃ Q : Subgroup ↥X, Q ⋖ ⊤ ∧
    (∀ x : ↥X, (x : MulAut V) ∈ Subgroup.normalizer (S : Set (MulAut V)) → x ∈ Q) ∧
    ∀ a : MulAut V, a ∈ Subgroup.normalizer (X : Set (MulAut V)) →
      a ∈ Subgroup.normalizer (S : Set (MulAut V)) →
      ∀ x y : ↥X, (y : MulAut V) = a * (x : MulAut V) * a⁻¹ → x ∈ Q → y ∈ Q

theorem isSylowTwoOf_subgroupOf_top {X S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.subgroupOf X) ⊤ := by
  refine isSylowTwoOf_top_of ?_ hS.2.2
  exact hS.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hS.1).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hS.1).injective

section NatGood

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {X : Subgroup (MulAut V)} {U Z : Subgroup V} {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
  {π : ↥Γ →* ↥X}

theorem NatReal.goodCoatom [Finite Γ] (R : NatReal X U Z Γ π)
    (hcov : ∀ T : Subgroup ↥Γ, IsSylowTwoOf T ⊤ → Qt Γ T ⋖ ⊤)
    (hUa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ U ↔ a u ∈ U)
    (hZa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ Z ↔ a u ∈ Z)
    {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X) : GoodCoatom X S := by
  obtain ⟨T, hTs, hTS⟩ := exists_sylow_cover π R.surj (isSylowTwoOf_subgroupOf_top hS)
  have hT : ∀ s : MulAut V, s ∈ S ↔ ∃ t ∈ T, ((π t : ↥X) : MulAut V) = s := by
    intro s
    constructor
    · intro hs
      have h1 : (⟨s, hS.1 hs⟩ : ↥X) ∈ T.map π := by
        rw [hTS]
        exact hs
      obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 h1
      exact ⟨t, ht, congrArg Subtype.val hts⟩
    · rintro ⟨t, ht, rfl⟩
      have h1 : π t ∈ T.map π := Subgroup.mem_map.2 ⟨t, ht, rfl⟩
      rw [hTS] at h1
      exact h1
  have hXn : ∀ x : ↥X, (x : MulAut V) ∈ Subgroup.normalizer (X : Set (MulAut V)) := fun x =>
    Subgroup.le_normalizer x.2
  refine ⟨(setStab (fixMod S U Z)).comap X.subtype,
    covBy_top_of_comap π R.surj _ ?_, fun x hx => ?_, fun a haX haS x y hy hx => ?_⟩
  · rw [R.comap_eq hT]
    exact hcov T hTs
  · exact fixMod_inv hx (hUa _ (hXn x)) (hZa _ (hXn x))
  · have h1 := conj_mem_setStab (fixMod_inv haS (hUa a haX) (hZa a haX)) hx
    show (y : MulAut V) ∈ setStab (fixMod S U Z)
    rw [hy]
    exact h1

end NatGood

theorem exists_cover_data {Γ : Type*} [Group Γ] [Finite Γ] {X S : Subgroup (MulAut V)}
    (π : Γ →* ↥X) (hπ : Function.Surjective π) (hS : IsSylowTwoOf S X) :
    ∃ T : Subgroup Γ, IsSylowTwoOf T ⊤ ∧
      ∀ s : MulAut V, s ∈ S ↔ ∃ t ∈ T, ((π t : ↥X) : MulAut V) = s := by
  obtain ⟨T, hTs, hTS⟩ := exists_sylow_cover π hπ (isSylowTwoOf_subgroupOf_top hS)
  refine ⟨T, hTs, fun s => ⟨fun hs => ?_, ?_⟩⟩
  · have h1 : (⟨s, hS.1 hs⟩ : ↥X) ∈ T.map π := by
      rw [hTS]
      exact hs
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 h1
    exact ⟨t, ht, congrArg Subtype.val hts⟩
  · rintro ⟨t, ht, rfl⟩
    have h1 : π t ∈ T.map π := Subgroup.mem_map.2 ⟨t, ht, rfl⟩
    rw [hTS] at h1
    exact h1

section TwoGood

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {X : Subgroup (MulAut V)} {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥X}

theorem goodCoatom_of_two [Finite Γ] {I : Fin 2 → Subgroup V} (hdis : Disjoint (I 0) (I 1))
    (hreal : ∀ i, NatReal X (I i) ⊥ Γ π)
    (hcov : ∀ T : Subgroup ↥Γ, IsSylowTwoOf T ⊤ → Qt Γ T ⋖ ⊤)
    (hUa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ I 0 ⊔ I 1 ↔ a u ∈ I 0 ⊔ I 1)
    {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X) : GoodCoatom X S := by
  have hsurj := (hreal 0).surj
  obtain ⟨T, hTs, hT⟩ := exists_cover_data π hsurj hS
  have hSX : S ≤ X := hS.1
  have hXn : ∀ x : ↥X, (x : MulAut V) ∈ Subgroup.normalizer (X : Set (MulAut V)) := fun x =>
    Subgroup.le_normalizer x.2
  have hIinv : ∀ i, ∀ x : ↥X, ∀ u, u ∈ I i ↔ (x : MulAut V) u ∈ I i := by
    intro i x u
    refine ⟨(hreal i).U_inv x u, fun h => ?_⟩
    have := (hreal i).U_inv x⁻¹ _ h
    simpa using this
  have hcomap : ∀ i, ((setStab (fixMod S (I i) ⊥)).comap X.subtype).comap π = Qt Γ T :=
    fun i => (hreal i).comap_eq hT
  have hQ01 : (setStab (fixMod S (I 0) ⊥)).comap X.subtype =
      (setStab (fixMod S (I 1) ⊥)).comap X.subtype :=
    Subgroup.comap_injective hsurj (by rw [hcomap 0, hcomap 1])
  have hQ : (setStab (fixMod S (I 0 ⊔ I 1) ⊥)).comap X.subtype =
      (setStab (fixMod S (I 0) ⊥)).comap X.subtype := by
    ext x
    constructor
    · intro hx w
      have hΛ : ∀ w, w ∈ fixMod S (I 0) ⊥ ↔ w ∈ I 0 ∧ w ∈ fixMod S (I 0 ⊔ I 1) ⊥ := by
        intro w
        rw [mem_fixMod_bot, mem_fixMod_bot]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Subgroup.mem_sup_left h1, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      show w ∈ fixMod S (I 0) ⊥ ↔ (x : MulAut V) w ∈ fixMod S (I 0) ⊥
      have hx' : ∀ u, u ∈ fixMod S (I 0 ⊔ I 1) ⊥ ↔ (x : MulAut V) u ∈ fixMod S (I 0 ⊔ I 1) ⊥ := hx
      rw [hΛ, hΛ, ← hx' w, ← hIinv 0 x w]
    · intro hx
      have hx1 : x ∈ (setStab (fixMod S (I 1) ⊥)).comap X.subtype := hQ01 ▸ hx
      exact setStab_two_iff x hSX hdis (hIinv 0) (hIinv 1) hx hx1 (inv_mem hx) (inv_mem hx1)
  refine ⟨(setStab (fixMod S (I 0 ⊔ I 1) ⊥)).comap X.subtype, ?_, fun x hx => ?_,
    fun a haX haS x y hy hx => ?_⟩
  · rw [hQ]
    exact covBy_top_of_comap π hsurj _ (by rw [hcomap 0]; exact hcov T hTs)
  · exact fixMod_inv hx (hUa _ (hXn x)) (bot_iff_apply _)
  · have h1 := conj_mem_setStab (fixMod_inv haS (hUa a haX) (bot_iff_apply a)) hx
    show (y : MulAut V) ∈ setStab (fixMod S (I 0 ⊔ I 1) ⊥)
    rw [hy]
    exact h1

end TwoGood

end Good

end CFSG.Quasithin.SzN15
