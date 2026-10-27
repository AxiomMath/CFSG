module

public import CFSG.Timmesfeld.RootSubgroupBasic
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Open
open scoped commutatorElement

variable {Y : Type*} [Group Y] {E : Set Y}

theorem commute_of_mem_odd_of_commute (hD : IsRootInvolutionSet E)
    (hconj : ∀ g : Y, ∀ x ∈ E, g * x * g⁻¹ ∈ E) {u₁ u₂ : Y} (hu₁ : u₁ ∈ E) (hu₂ : u₂ ∈ E)
    (hc : Commute u₁ u₂) (hu₃ : u₁ * u₂ ∈ E) {M : Subgroup Y} (hM : M.Normal)
    (hodd : Odd (Nat.card M)) {y : Y} (hy : y ∈ M) (hyc : Commute y u₂) : Commute y u₁ := by
  have h1 : u₁ * u₁ = 1 := hD.mul_self_eq_one hu₁
  have h1inv : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right h1
  set t := u₁ * (y⁻¹ * u₁ * y) with ht
  have htM : t ∈ M := by
    have : u₁ * y⁻¹ * u₁⁻¹ ∈ M := hM.conj_mem _ (M.inv_mem hy) u₁
    rw [h1inv] at this
    rw [ht, ← mul_assoc, ← mul_assoc]
    exact M.mul_mem this hy
  have hct : Commute t u₂ := hc.mul_left (((hyc.inv_left).mul_left hc).mul_left hyc)
  have hy2 : y⁻¹ * u₂ * y = u₂ := by
    rw [mul_assoc, ← hyc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hkey : u₁ * (y⁻¹ * (u₁ * u₂) * y) = t * u₂ := by
    rw [show y⁻¹ * (u₁ * u₂) * y = y⁻¹ * u₁ * y * (y⁻¹ * u₂ * y) by group, hy2, ht, ← mul_assoc]
  have hoddt : Odd (orderOf t) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard M htM)
  have hord : orderOf (t * u₂) = orderOf t * 2 := by
    rw [hct.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [hD.orderOf_eq_two hu₂]
      exact Nat.Coprime.symm ((Nat.coprime_two_left).2 hoddt)), hD.orderOf_eq_two hu₂]
  have hmem : y⁻¹ * (u₁ * u₂) * y ∈ E := by
    have := hconj y⁻¹ _ hu₃
    rwa [inv_inv] at this
  have hroot := hD.2.1 u₁ hu₁ _ hmem
  rw [hkey, hord] at hroot
  have ht1 : t = 1 := by
    rcases hroot with h | h | h
    · exact orderOf_eq_one_iff.1 (by omega)
    · exfalso
      have : orderOf t = 2 := by omega
      rw [this] at hoddt
      exact absurd hoddt (by decide)
    · exfalso
      exact (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 (dvd_mul_left 2 _))
  have hconj' : y⁻¹ * u₁ * y = u₁ := by
    have := eq_inv_of_mul_eq_one_right ht1
    rwa [h1inv] at this
  show y * u₁ = u₁ * y
  calc y * u₁ = y * (y⁻¹ * u₁ * y) := by rw [hconj']
    _ = u₁ * y := by group

theorem mem_four_of_mem_closure {u₁ u₂ : Y} (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1)
    (hc : Commute u₁ u₂) {x : Y} (hx : x ∈ Subgroup.closure {u₁, u₂}) :
    x = 1 ∨ x = u₁ ∨ x = u₂ ∨ x = u₁ * u₂ := by
  have h1inv : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right h1
  have h2inv : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right h2
  have step : ∀ s ∈ ({u₁, u₂} : Set Y), ∀ y : Y, (y = 1 ∨ y = u₁ ∨ y = u₂ ∨ y = u₁ * u₂) →
      (s * y = 1 ∨ s * y = u₁ ∨ s * y = u₂ ∨ s * y = u₁ * u₂) := by
    rintro s (rfl | rfl) y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, h1, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hc.eq.symm))
    · exact Or.inl h2
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hc.eq, mul_assoc, h2, mul_one]))
  induction hx using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left s hs y _ ih => exact step s hs y ih
  | inv_mul_cancel s hs y _ ih =>
    rcases hs with rfl | rfl
    · rw [h1inv]
      exact step _ (Or.inl rfl) y ih
    · rw [h2inv]
      exact step _ (Or.inr rfl) y ih

theorem commute_of_mem_odd_card [Finite Y] (hD : IsRootInvolutionSet E)
    (hconj : ∀ g : Y, ∀ x ∈ E, g * x * g⁻¹ ∈ E) {u₁ u₂ : Y} (hu₁ : u₁ ∈ E) (hu₂ : u₂ ∈ E)
    (hne : u₁ ≠ u₂) (hc : Commute u₁ u₂) (hu₃ : u₁ * u₂ ∈ E) {M : Subgroup Y} (hM : M.Normal)
    (hodd : Odd (Nat.card M)) {y : Y} (hy : y ∈ M) : Commute y u₁ := by
  classical
  have h1 : u₁ * u₁ = 1 := hD.mul_self_eq_one hu₁
  have h2 : u₂ * u₂ = 1 := hD.mul_self_eq_one hu₂
  set A := Subgroup.closure ({u₁, u₂} : Set Y) with hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, Commute a b := by
    intro a ha b hb
    refine commute_of_mem_closure ?_ ha hb
    rintro s (rfl | rfl) s' (rfl | rfl)
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := by
    intro a ha
    rcases mem_four_of_mem_closure h1 h2 hc ha with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two, h1]
    · rw [pow_two, h2]
    · rw [hc.mul_pow, pow_two, pow_two, h1, h2, one_mul]
  have hEl : IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2).eq⟩⟩, hsq⟩
  have h1ne : u₁ ≠ 1 := hD.ne_one hu₁
  have h2ne : u₂ ≠ 1 := hD.ne_one hu₂
  have h3ne1 : u₁ * u₂ ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rwa [inv_eq_of_mul_eq_one_right h2] at this)
  have h3ne2 : u₁ * u₂ ≠ u₁ := fun h => h2ne (by
    calc u₂ = u₁ * (u₁ * u₂) := by rw [← mul_assoc, h1, one_mul]
      _ = 1 := by rw [h, h1])
  have h3ne3 : u₁ * u₂ ≠ u₂ := fun h => h1ne (by
    calc u₁ = u₁ * u₂ * u₂ := by rw [mul_assoc, h2, mul_one]
      _ = 1 := by rw [h, h2])
  have hsub : ({1, u₁, u₂, u₁ * u₂} : Set Y) ⊆ (A : Set Y) := by
    rintro z (rfl | rfl | rfl | rfl)
    · exact A.one_mem
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact A.mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  have hcard4 : ({1, u₁, u₂, u₁ * u₂} : Set Y).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h3ne3.symm]
    · rintro (h | h)
      · exact hne h
      · exact h3ne2 h.symm
    · rintro (h | h | h)
      · exact h1ne h.symm
      · exact h2ne h.symm
      · exact h3ne1 h.symm
  have hcardA : 2 ^ (1 + 1) ≤ Nat.card A := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num, ← hcard4, ← Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hnorm : A ≤ Subgroup.normalizer (M : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hM]
    exact le_top
  have hcop : Nat.Coprime 2 (Nat.card M) := (Nat.coprime_two_left).2 hodd
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two A M hEl hcardA hnorm hcop
  have hle : M ≤ Subgroup.centralizer ({u₁} : Set Y) := by
    rw [← hgen]
    refine iSup₂_le fun S hS => ?_
    intro z hz
    obtain ⟨hzM, hzS⟩ := Subgroup.mem_inf.1 hz
    have hSne : S ≠ ⊥ := by
      intro hS0
      have h2' := hS.2
      rw [hS0, Subgroup.card_bot] at h2'
      norm_num at h2'
    obtain ⟨⟨s, hsS⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
    have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
    have hzs : Commute z s := ((Subgroup.mem_centralizer_iff.1 hzS) s hsS).symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have key : Commute z u₁ := by
      rcases mem_four_of_mem_closure h1 h2 hc (hS.1 hsS) with rfl | rfl | rfl | rfl
      · exact absurd rfl hs1
      · exact hzs
      · exact commute_of_mem_odd_of_commute hD hconj hu₁ hu₂ hc hu₃ hM hodd hzM hzs
      · have hu₃' : u₁ * (u₁ * u₂) ∈ E := by rw [← mul_assoc, h1, one_mul]; exact hu₂
        exact commute_of_mem_odd_of_commute hD hconj hu₁ hu₃ ((Commute.refl u₁).mul_right hc)
          hu₃' hM hodd hzM hzs
    exact key.eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem le_center_of_odd_card [Finite Y] (hclass : ∃ d₀ : Y, E = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet E) (hgen : Subgroup.closure E = ⊤) {u₁ u₂ : Y} (hu₁ : u₁ ∈ E)
    (hu₂ : u₂ ∈ E) (hne : u₁ ≠ u₂) (hc : Commute u₁ u₂) (hu₃ : u₁ * u₂ ∈ E) {M : Subgroup Y}
    (hM : M.Normal) (hodd : Odd (Nat.card M)) : M ≤ Subgroup.center Y := by
  have hconj : ∀ g : Y, ∀ x ∈ E, g * x * g⁻¹ ∈ E := fun g x hx => conj_mem_of_isClass hclass g hx
  have hE : ∀ e ∈ E, ∀ y ∈ M, Commute y e := by
    intro e he y hy
    obtain ⟨d₀, hd₀⟩ := hclass
    have hue : IsConj u₁ e := by
      rw [hd₀] at hu₁ he
      exact hu₁.symm.trans he
    obtain ⟨g, rfl⟩ := isConj_iff.1 hue
    have hy' : g⁻¹ * y * g ∈ M := by
      have := hM.conj_mem y hy g⁻¹
      rwa [inv_inv] at this
    have h := commute_of_mem_odd_card hD hconj hu₁ hu₂ hne hc hu₃ hM hodd hy'
    have h' := h.map (MulAut.conj g).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h'
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure E := hgen ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (hE x hx y hy).eq.symm
  | one => simp
  | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha => exact (Commute.inv_left (show Commute a y from ha)).eq

theorem le_center_of_isSolvable [Finite Y] (hclass : ∃ d₀ : Y, E = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet E) (hgen : Subgroup.closure E = ⊤) {u₁ u₂ : Y} (hu₁ : u₁ ∈ E)
    (hu₂ : u₂ ∈ E) (hne : u₁ ≠ u₂) (hc : Commute u₁ u₂) (hu₃ : u₁ * u₂ ∈ E)
    (h2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) {N : Subgroup Y} (hN : N.Normal)
    (hs : Group.IsSolvable N) : N ≤ Subgroup.center Y := by
  suffices key : ∀ n : ℕ, ∀ N : Subgroup Y, Nat.card N = n → N.Normal → Group.IsSolvable N →
      N ≤ Subgroup.center Y from key _ N rfl hN hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hn hN hs
    by_cases hbot : N = ⊥
    · rw [hbot]
      exact bot_le
    have hlt : ⁅N, N⁆ < N := by
      have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hbot
      rw [← N.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
        Subgroup.map_subtype_lt_map_subtype]
      exact Group.IsSolvable.commutator_lt_top_of_nontrivial N
    have hKs : Group.IsSolvable (⁅N, N⁆ : Subgroup Y) := by
      have := hs
      have e := (Subgroup.subgroupOfEquivOfLe hlt.le)
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have hK : ⁅N, N⁆ ≤ Subgroup.center Y :=
      ih _ (hn ▸ Subgroup.card_lt_of_lt hlt) _ rfl inferInstance hKs
    have hnil : Group.IsNilpotent N := by
      refine ⟨⟨2, eq_top_iff.2 fun x _ => ?_⟩⟩
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro y
      rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
      intro z
      have hxy : ((⁅x, y⁆ : N) : Y) ∈ ⁅N, N⁆ := by
        have : ((⁅x, y⁆ : N) : Y) = ⁅(x : Y), (y : Y)⁆ := by simp [commutatorElement_def]
        rw [this]
        exact Subgroup.commutator_mem_commutator x.2 y.2
      exact Subtype.ext ((Subgroup.mem_center_iff.1 (hK hxy)) z)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 N))
    have hPc : (P : Subgroup N).Characteristic := P.characteristic_of_normal inferInstance
    have hPY : ((P : Subgroup N).map N.subtype).Normal := inferInstance
    have hP2 : IsPGroup 2 ((P : Subgroup N).map N.subtype) := P.isPGroup'.map N.subtype
    have hPbot := h2 _ hPY hP2
    have hodd : Odd (Nat.card N) := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro hdvd
      apply P.ne_bot_of_dvd_card hdvd
      rw [← Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
      exact hPbot
    exact le_center_of_odd_card hclass hD hgen hu₁ hu₂ hne hc hu₃ hN hodd

end CFSG.Timmesfeld.Bridge
