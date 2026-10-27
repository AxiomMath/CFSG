module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.L3YC

namespace Row13

section Generic

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem conj_inner_of_equiv {N : Subgroup K} [N.Normal] {X : Type*} [Group X] (e : ↥N ≃* X)
    (hin : ∀ φ : X ≃* X, ∃ s : X, ∀ x, φ x = s * x * s⁻¹) (g : K) :
    ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹ := by
  obtain ⟨s, hs⟩ := hin (e.symm.trans ((MulAut.conjNormal g).trans e))
  refine ⟨(e.symm s).1, (e.symm s).2, fun a ha => ?_⟩
  have h1 := hs (e ⟨a, ha⟩)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  have h2 : (MulAut.conjNormal g) ⟨a, ha⟩ = e.symm s * ⟨a, ha⟩ * (e.symm s)⁻¹ := by
    apply e.injective
    rw [h1]
    simp
  have := congrArg Subtype.val h2
  simpa [MulAut.conjNormal_apply] using this

theorem le_of_isPGroup_normalizes_sylow {N S A : Subgroup K} (hS : IsSylowTwoOf S N)
    (hAN : A ≤ N) (hA : IsPGroup 2 A) (hnorm : A ≤ Subgroup.normalizer (S : Set K)) : A ≤ S := by
  have hW : S ⊔ A ≤ N := sup_le hS.1 hAN
  have hWn : S ⊔ A ≤ Subgroup.normalizer (S : Set K) :=
    sup_le Subgroup.le_normalizer hnorm
  have hodd : ¬ 2 ∣ S.relIndex (S ⊔ A) := by
    have h1 := Subgroup.relIndex_mul_relIndex S (S ⊔ A) N le_sup_left hW
    have h2 : ¬ 2 ∣ S.relIndex N := hS.2.2
    intro h
    exact h2 (h1 ▸ h.mul_right _)
  exact B6.le_of_isPGroup_of_odd_relIndex le_sup_right hA le_sup_left hWn hodd

theorem card_sup_eq_two_pow_mul {L S : Subgroup K} (hS2 : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set K)) :
    ∃ n : ℕ, Nat.card ↥(L ⊔ S) = 2 ^ n * Nat.card L := by
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hS2 L
  have h1 : L.relIndex (S ⊔ L) = L.relIndex S := B6.relIndex_sup_eq_of_le_normalizer hSL
  have e1 : L.relIndex (S ⊔ L) * Nat.card ↥(L ⊓ (S ⊔ L)) = Nat.card ↥(S ⊔ L) :=
    Subgroup.relIndex_mul_card L (S ⊔ L)
  rw [inf_eq_left.mpr le_sup_right, h1, hn] at e1
  exact ⟨n, by rw [sup_comm, ← e1]⟩

end Generic

section Bar

variable {G : Type} [Group G] [Finite G]

theorem card_eq_modO2Image_mul {H L : Subgroup G} (hLH : L ≤ H) :
    ∃ c : ℕ, Nat.card L = Nat.card (modO2Image H L) * 2 ^ c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mk : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  have hker : mk.ker = CFSG.pCore 2 ↥H := QuotientGroup.ker_mk' _
  have e1 := Subgroup.relIndex_mul_card mk.ker (L.subgroupOf H)
  have e2 : mk.ker.relIndex (L.subgroupOf H) = Nat.card (modO2Image H L) :=
    by rw [Subgroup.relIndex_ker]; rfl
  have hp : IsPGroup 2 ↥(mk.ker ⊓ L.subgroupOf H) := by
    rw [hker]
    exact (CFSG.pCore_isPGroup (G := ↥H) (p := 2)).to_inf_left
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hp
  refine ⟨c, ?_⟩
  rw [← hc, ← e2, e1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv).symm

omit [Finite G] in
theorem exists_bar_overgroup' {H L S : Subgroup G} {t' x : G} (hSH : S ≤ H) (hxL : x ∈ L)
    (hx₂H : t'⁻¹ * x * t' ∈ H) (hconj : ∀ s ∈ S, t' * s * t'⁻¹ ∈ S) :
    ∃ Y : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), Nat.card Y ∣ Nat.card ↥(L ⊔ S) ∧
      (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤ Y ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t'⁻¹ * x * t', hx₂H⟩ ∈ Y := by
  set X₂ : Subgroup G := Subgroup.closure ((S : Set G) ∪ {t'⁻¹ * x * t'}) with hX₂
  have hSX : S ≤ X₂ := fun s hs => Subgroup.subset_closure (Or.inl hs)
  have hxX : t'⁻¹ * x * t' ∈ X₂ := Subgroup.subset_closure (Or.inr rfl)
  have hX₂H : X₂ ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy)
    · exact hSH hy
    · rw [Set.mem_singleton_iff.mp hy]; exact hx₂H
  have hX₂c : X₂ ≤ B6.conjSub t'⁻¹ (L ⊔ S) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy)
    · refine B6.mem_conjSub.mpr ?_
      rw [inv_inv]
      exact (le_sup_right : S ≤ L ⊔ S) (hconj y hy)
    · rw [Set.mem_singleton_iff.mp hy]
      refine B6.mem_conjSub.mpr ?_
      rw [inv_inv]
      have : t' * (t'⁻¹ * x * t') * t'⁻¹ = x := by group
      rw [this]
      exact (le_sup_left : L ≤ L ⊔ S) hxL
  have hcardConj : Nat.card ↥(B6.conjSub t'⁻¹ (L ⊔ S)) = Nat.card ↥(L ⊔ S) :=
    Subgroup.card_map_of_injective (MulAut.conj t'⁻¹).injective
  have hX : Nat.card ↥X₂ ∣ Nat.card ↥(L ⊔ S) := by
    rw [← hcardConj]; exact Subgroup.card_dvd_of_le hX₂c
  refine ⟨(X₂.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)), ?_, ?_, ?_⟩
  · refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂H).toEquiv]
    exact hX
  · exact Subgroup.map_mono (fun y hy => hSX hy)
  · exact ⟨⟨t'⁻¹ * x * t', hx₂H⟩, hxX, rfl⟩

end Bar

section Data

theorem row13_data {Λ : Type} [Group Λ]
    (h : IsExt Λ (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
      IsExt Λ (fun V _ => IsE2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) :
    Nat.card Λ = 2688 ∨ Nat.card Λ = 1344 := by
  have key : ∀ (n : ℕ), IsExt Λ (fun V _ => IsE2 n V) (fun Y' _ => IsPSL 3 2 1 Y') →
      Nat.card Λ = 2 ^ n * 168 := by
    intro n ⟨V, hVn, hV, hQ⟩
    obtain ⟨e⟩ := hV
    obtain ⟨φ⟩ := row18_equiv_sl_of_isPSL hQ
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [Nat.card_congr φ.toEquiv, Row18.card_SL32, Nat.card_congr e.toEquiv] at h1
    rw [h1]
    simp [Nat.card_eq_fintype_card, mul_comm]
  rcases h with h | h
  · left; rw [key 4 h]; norm_num
  · right; rw [key 3 h]; norm_num

end Data

section Transport

variable {K : Type*} [Group K] {N : Subgroup K} {X : Type*} [Group X]

theorem mem_map_subgroupOf_iff {A : Subgroup K} (e : ↥N ≃* X) {a : K} (ha : a ∈ N) :
    e ⟨a, ha⟩ ∈ (A.subgroupOf N).map e.toMonoidHom ↔ a ∈ A := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rfl

theorem card_map_subgroupOf {A : Subgroup K} (e : ↥N ≃* X) (hAN : A ≤ N) :
    Nat.card ((A.subgroupOf N).map e.toMonoidHom) = Nat.card A := by
  rw [Subgroup.card_map_of_injective e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv

theorem orderOf_equiv_mk {e : ↥N ≃* X} {a : K} (ha : a ∈ N) :
    orderOf (e ⟨a, ha⟩) = orderOf a := by
  rw [MulEquiv.orderOf_eq]
  exact (Subgroup.orderOf_coe (⟨a, ha⟩ : N)).symm

end Transport

theorem nat_aux {m c : ℕ} (hc : c = 2 ^ m * 21) (h1 : 2 ^ 7 ∣ c) (h2 : c ∣ 2 ^ 7 * 79695) :
    c = 2 ^ 7 * 21 := by
  subst hc
  have h1' : 2 ^ 7 ∣ 2 ^ m :=
    Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime (2 ^ 7) 21) h1
  have h2' : 2 ^ m ∣ 2 ^ 7 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 79695))
      ((Dvd.intro _ rfl).trans h2)
  have h3 : m = 7 := le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2')
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1')
  rw [h3]

end Row13

end Stellmacher.L3YC

end CFSG.Quasithin
