module

public import CFSG.Quasithin.Background.G117Lt4

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace Canon

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem not_isNilpotent_of_simple_card_360 (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (h : Nat.card G = 360) : ¬ Group.IsNilpotent G := by
  intro hnil
  letI : CommGroup G := @instCommGroupOfIsSimpleGroupOfIsNilpotent G _ _ hnil
  have hp := IsSimpleGroup.prime_card (α := G)
  rw [h] at hp
  exact absurd hp (by norm_num)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem fitting_eq_centralizer {Γ H : Subgroup (GLV V)} (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hsimple : IsSimpleGroup ↥H)
    (hnn : ¬ Group.IsNilpotent ↥H)
    (hC : Group.IsNilpotent ↥(Γ ⊓ Subgroup.centralizer (H : Set (GLV V)))) :
    genFittingFitting ↥Γ = (Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ := by
  set P : Subgroup ↥Γ := (Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ with hP
  have hPn : P.Normal := G117.normal_centralizer_subgroupOf hN
  have hPnil : Group.IsNilpotent ↥P :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : Γ ⊓
      Subgroup.centralizer (H : Set (GLV V)) ≤ Γ)).symm
  rw [genFittingFitting.eq_sSup]
  apply le_antisymm
  · refine sSup_le fun K ⟨hKn, hKnil⟩ => ?_
    set H' : Subgroup ↥Γ := H.subgroupOf Γ with hH'
    have hH'n : H'.Normal := ⟨fun n hn g => by
      rw [hH', Subgroup.mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
    have : IsSimpleGroup ↥H' :=
      (Subgroup.subgroupOfEquivOfLe hHΓ : ↥H' ≃* ↥H).isSimpleGroup
    have hinf : K ⊓ H' = ⊥ := by
      have hnorm : ((K ⊓ H').subgroupOf H').Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
        refine ⟨?_, ?_⟩
        · have := hKn.conj_mem (n : ↥Γ) hn.1 (g : ↥Γ)
          simpa using this
        · exact H'.mul_mem (H'.mul_mem g.2 hn.2) (H'.inv_mem g.2)⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ H').subgroupOf H') with h0 | h1
      · rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hx.2⟩ : ↥H') ∈ (K ⊓ H').subgroupOf H' := hx
        rw [h0, Subgroup.mem_bot] at hx'
        have : x = 1 := congrArg Subtype.val hx'
        rw [this]
        exact Subgroup.one_mem _
      · exfalso
        apply hnn
        have hle : H' ≤ K := fun x hx => (show (⟨x, hx⟩ : ↥H') ∈ (K ⊓ H').subgroupOf H' by
          rw [h1]; exact Subgroup.mem_top _).1
        have hnilH'K : Group.IsNilpotent ↥(H'.subgroupOf K) := inferInstance
        have hnilH' : Group.IsNilpotent ↥H' :=
          Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
        exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHΓ)
    intro k hk
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨k.2, fun h hh => ?_⟩
    set h' : ↥Γ := ⟨h, hHΓ hh⟩ with hh'
    have hh'mem : h' ∈ H' := hh
    have hcomm : k * h' * k⁻¹ * h'⁻¹ ∈ K ⊓ H' := by
      refine ⟨?_, ?_⟩
      · have := hKn.conj_mem k⁻¹ (K.inv_mem hk) h'
        have h5 := K.mul_mem hk (by simpa using this)
        simpa [mul_assoc] using h5
      · exact H'.mul_mem (hH'n.conj_mem h' hh'mem k) (H'.inv_mem hh'mem)
    rw [hinf, Subgroup.mem_bot] at hcomm
    have h6 : k * h' * k⁻¹ = h' := mul_inv_eq_one.1 hcomm
    have h7 : k * h' = h' * k := by
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6
    exact (congrArg Subtype.val h7).symm
  · exact le_sSup ⟨hPn, hPnil⟩

theorem inf_eq_bot_of_centralizing {A : Type*} [Group A] {H P : Subgroup A} [Finite ↥H]
    (hsimple : IsSimpleGroup ↥H) (hcard : Nat.card ↥H = 360)
    (hP : ∀ p ∈ P, ∀ h ∈ H, p * h = h * p) : H ⊓ P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxc : (⟨x, hx.1⟩ : ↥H) ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hP x hx.2 g g.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥H) with h0 | h1
  · rw [h0, Subgroup.mem_bot] at hxc
    exact congrArg Subtype.val hxc
  · exfalso
    have hc : ∀ a b : ↥H, a * b = b * a := fun a b => by
      have : a ∈ Subgroup.center ↥H := h1 ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
    letI : CommGroup ↥H := { (inferInstance : Group ↥H) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥H)
    rw [hcard] at hp
    exact absurd hp (by norm_num)

theorem card_mul_le_card_sup {A : Type*} [Group A] (E P : Subgroup A) [Finite ↥(E ⊔ P)]
    (h : E ⊓ P = ⊥) : Nat.card ↥E * Nat.card ↥P ≤ Nat.card ↥(E ⊔ P) := by
  let f : ↥E × ↥P → ↥(E ⊔ P) := fun ep =>
    ⟨(ep.1 : A) * (ep.2 : A), Subgroup.mul_mem _ (Subgroup.mem_sup_left ep.1.2)
      (Subgroup.mem_sup_right ep.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨e, p⟩ ⟨e', p'⟩ hep
    have h1 : (e : A) * (p : A) = (e' : A) * (p' : A) := congrArg Subtype.val hep
    have h2 : (e' : A)⁻¹ * (e : A) = (p' : A) * (p : A)⁻¹ := by
      calc (e' : A)⁻¹ * (e : A) = (e' : A)⁻¹ * ((e : A) * (p : A)) * (p : A)⁻¹ := by group
        _ = (e' : A)⁻¹ * ((e' : A) * (p' : A)) * (p : A)⁻¹ := by rw [h1]
        _ = (p' : A) * (p : A)⁻¹ := by group
    have h3 : (e' : A)⁻¹ * (e : A) ∈ E ⊓ P :=
      ⟨E.mul_mem (E.inv_mem e'.2) e.2, h2 ▸ P.mul_mem p'.2 (P.inv_mem p.2)⟩
    rw [h, Subgroup.mem_bot] at h3
    have he : e = e' := Subtype.ext (inv_mul_eq_one.1 h3).symm
    have hp : p = p' := by
      have h4 : (p' : A) * (p : A)⁻¹ = 1 := h2 ▸ h3
      exact Subtype.ext (mul_inv_eq_one.1 h4).symm
    rw [he, hp]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem eq_sup_zpowers_of_card {A : Type*} [Group A] {Γ M : Subgroup A} {x : A} [Finite ↥Γ]
    (hMΓ : M ≤ Γ) (hx : x ∈ Γ) (hxM : x ∉ M) (hΓ : Nat.card ↥Γ = 2 * Nat.card ↥M) :
    Γ = M ⊔ Subgroup.zpowers x := by
  have hle : M ⊔ Subgroup.zpowers x ≤ Γ := sup_le hMΓ ((Subgroup.zpowers_le).2 hx)
  haveI : Finite ↥M :=
    Finite.of_injective (Subgroup.inclusion hMΓ) (Subgroup.inclusion_injective hMΓ)
  haveI : Finite ↥(M ⊔ Subgroup.zpowers x) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hlt : M < M ⊔ Subgroup.zpowers x := by
    refine lt_of_le_of_ne le_sup_left fun h => hxM ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have h1 : Nat.card ↥M ∣ Nat.card ↥(M ⊔ Subgroup.zpowers x) := Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(M ⊔ Subgroup.zpowers x) ∣ Nat.card ↥Γ := Subgroup.card_dvd_of_le hle
  have h3 : Nat.card ↥M < Nat.card ↥(M ⊔ Subgroup.zpowers x) := Subgroup.card_lt_of_lt hlt
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hMpos : 0 < Nat.card ↥M := Nat.card_pos
  have ha2 : 2 ≤ a := by
    by_contra hcon
    have : a ≤ 1 := by omega
    interval_cases a <;> omega
  have hb2 : a * b = 2 := by
    have : Nat.card ↥M * (a * b) = Nat.card ↥M * 2 := by
      rw [← mul_assoc, ← ha, ← hb, hΓ, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hMpos this
  have hb1 : b = 1 := by
    have : a ∣ 2 := ⟨b, hb2.symm⟩
    have ha2' : a = 2 := by
      have := Nat.le_of_dvd (by norm_num) this
      omega
    subst ha2'
    omega
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hb, hb1, mul_one]

end Canon

end G11

end CFSG.Quasithin
