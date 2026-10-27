module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.RonanF13

universe u v

@[expose] def RankOneTwist (K : Type u) [Group K] : Prop :=
  ∀ (T D : Subgroup K) (α : MulAut K), IsPGroup 2 T → ¬ 2 ∣ T.index →
    T ⊔ D = Subgroup.normalizer (T : Set K) → Odd (Nat.card D) →
    (∀ x, α x ∈ T ↔ x ∈ T) → (∀ x, α x ∈ D ↔ x ∈ D) → Odd (orderOf α) →
    (∀ x ∈ D, α (x⁻¹ * α x) = x⁻¹ * α x) → ∀ x ∈ D, α x = x

@[expose] def SelfNormSylow (K : Type u) [Group K] : Prop :=
  ∀ T : Subgroup K, IsPGroup 2 T → ¬ 2 ∣ T.index → Subgroup.normalizer (T : Set K) = T

theorem rankOneTwist_of_selfNormSylow {K : Type u} [Group K] (h : SelfNormSylow K) :
    RankOneTwist K := by
  intro T D α hT hodd hTD hDodd _ _ _ _ x hx
  have hDT : D ≤ T := by
    have h1 : D ≤ T ⊔ D := le_sup_right
    rw [hTD, h T hT hodd] at h1
    exact h1
  have hxT : x ∈ T := hDT hx
  have h2 : IsPGroup 2 ↥D := hT.to_le hDT
  have hfin : Finite ↥D :=
    Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hDodd; exact absurd hDodd (by decide))
  have hD1 : Nat.card D = 1 := by
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [hm] at hDodd ⊢
    rcases m with _ | m
    · rfl
    · exfalso
      have : Even (2 ^ (m + 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact (Nat.not_even_iff_odd.mpr hDodd) this
  have hx1 : x = 1 := by
    have : Subsingleton ↥D := (Nat.card_eq_one_iff_unique.mp hD1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥D) 1)
  subst hx1
  simp

theorem RankOneTwist.of_mulEquiv {K : Type u} {K' : Type v} [Group K] [Group K'] (e : K ≃* K')
    (h : RankOneTwist K) : RankOneTwist K' := by
  intro T' D' α' hT' hodd' hTD' hDodd' hαT' hαD' hαodd' hcomm'
  have hsurj : Function.Surjective (e : K →* K') := e.surjective
  let T : Subgroup K := T'.comap (e : K →* K')
  let D : Subgroup K := D'.comap (e : K →* K')
  let α : MulAut K := (MulAut.congr e).symm α'
  have hα0 : (MulAut.congr e) α = α' := (MulAut.congr e).apply_symm_apply α'
  have hα : ∀ x, e (α x) = α' (e x) := by
    intro x
    rw [← hα0]
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hT : IsPGroup 2 T := hT'.comap_of_injective (e : K →* K') e.injective
  have hodd : ¬ 2 ∣ T.index := by
    show ¬ 2 ∣ (T'.comap (e : K →* K')).index
    rw [Subgroup.index_comap_of_surjective T' hsurj]
    exact hodd'
  have hTD : T ⊔ D = Subgroup.normalizer (T : Set K) := by
    have h1 : (T' ⊔ D').comap (e : K →* K') =
        T'.comap (e : K →* K') ⊔ D'.comap (e : K →* K') := by
      rw [Subgroup.comap_equiv_eq_map_symm, Subgroup.comap_equiv_eq_map_symm,
        Subgroup.comap_equiv_eq_map_symm, Subgroup.map_sup]
    change T'.comap (e : K →* K') ⊔ D'.comap (e : K →* K') = _
    rw [← h1, hTD']
    ext x
    have := Subgroup.comap_normalizer_eq_of_surjective T' hsurj
    change x ∈ Subgroup.comap (e : K →* K') (Subgroup.normalizer ((T' : Subgroup K') : Set K')) ↔
      x ∈ Subgroup.normalizer ((T'.comap (e : K →* K') : Subgroup K) : Set K)
    rw [this]
  have hDodd : Odd (Nat.card D) := by
    have : Nat.card D = Nat.card D' := by
      show Nat.card (D'.comap (e : K →* K')) = Nat.card D'
      rw [Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective e.symm.injective]
    rw [this]
    exact hDodd'
  have hαT : ∀ x, α x ∈ T ↔ x ∈ T := by
    intro x
    show e (α x) ∈ T' ↔ e x ∈ T'
    rw [hα, hαT']
  have hαD : ∀ x, α x ∈ D ↔ x ∈ D := by
    intro x
    show e (α x) ∈ D' ↔ e x ∈ D'
    rw [hα, hαD']
  have hαodd : Odd (orderOf α) := by
    have : orderOf α = orderOf α' := by
      have h2 := MulEquiv.orderOf_eq (MulAut.congr e) α
      rw [← h2, hα0]
    rw [this]
    exact hαodd'
  have hcomm : ∀ x ∈ D, α (x⁻¹ * α x) = x⁻¹ * α x := by
    intro x hx
    have hx' : e x ∈ D' := hx
    have h3 := hcomm' (e x) hx'
    apply e.injective
    rw [hα, map_mul, map_inv, hα]
    exact h3
  intro x' hx'
  obtain ⟨x, rfl⟩ := e.surjective x'
  have h4 := h T D α hT hodd hTD hDodd hαT hαD hαodd hcomm x hx'
  rw [← hα, h4]

theorem inf_eq_bot_of_odd {K : Type*} [Group K] {T D : Subgroup K} (hT : IsPGroup 2 T) (hDodd : Odd (Nat.card D)) :
    T ⊓ D = ⊥ := by
  have hfin : Finite ↥D :=
    Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hDodd; exact absurd hDodd (by decide))
  have h1 : IsPGroup 2 ↥(T ⊓ D) := hT.to_le inf_le_left
  have hfinI : Finite ↥(T ⊓ D) := Finite.of_injective (Subgroup.inclusion (inf_le_right : T ⊓ D ≤ D))
    (Subgroup.inclusion_injective _)
  obtain ⟨m, hm⟩ := h1.exists_card_eq
  have hdvd : Nat.card ↥(T ⊓ D) ∣ Nat.card D :=
    Subgroup.card_dvd_of_le (inf_le_right : T ⊓ D ≤ D)
  rw [hm] at hdvd
  rcases m with _ | m
  · exact (Subgroup.card_eq_one).mp (by simpa using hm)
  · exfalso
    have h2 : 2 ∣ Nat.card D := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h2)


end CFSG.Quasithin.RonanF13
