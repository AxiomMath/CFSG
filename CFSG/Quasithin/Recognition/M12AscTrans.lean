module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open Subgroup

open scoped IsMulCommutative

variable {X : Type*} [Group X]

theorem thompson_transfer_index_two [Finite X] (P : Sylow 2 X) {Q : Subgroup X}
    (hindex : Q.relIndex (P : Subgroup X) = 2) {u : X} (hu : u * u = 1)
    (huP : u ∈ (P : Subgroup X)) (hQu : ∀ a : X, a⁻¹ * u * a ∉ Q) :
    ∃ X₀ : Subgroup X, X₀.Normal ∧ X₀.index = 2 ∧ u ∉ X₀ ∧
      ∀ g ∈ (P : Subgroup X), g * g = 1 →
        (∀ a : X, a⁻¹ * g * a ∈ (P : Subgroup X) → (a⁻¹ * g * a ∈ Q ↔ g ∈ Q)) →
          (g ∈ X₀ ↔ g ∈ Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup X := (P : Subgroup X) with hP'
  set Q' : Subgroup P' := Q.subgroupOf P' with hQ'
  have hQ'index : Q'.index = 2 := hindex
  have : Q'.Normal := Subgroup.normal_of_index_eq_two hQ'index
  have hcard : Nat.card (P' ⧸ Q') = 2 := by rw [← Subgroup.index_eq_card]; exact hQ'index
  have : IsCyclic (P' ⧸ Q') := isCyclic_of_prime_card hcard
  let ϕ : P' →* P' ⧸ Q' := QuotientGroup.mk' Q'
  have hsq : ∀ w : P' ⧸ Q', w ^ 2 = 1 := fun w => by
    simpa [hcard] using pow_card_eq_one' (G := P' ⧸ Q') (x := w)
  have hodd : Odd P'.index := by
    have := P.not_dvd_index
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 this)
  have heval : ∀ g (hg : g ∈ P'), g * g = 1 →
      (∀ a : X, a⁻¹ * g * a ∈ P' → (a⁻¹ * g * a ∈ Q ↔ g ∈ Q)) →
        MonoidHom.transfer ϕ g = ϕ ⟨g, hg⟩ := by
    intro g hg hg2 hcond
    have hg2' : g ^ 2 = 1 := by rw [pow_two]; exact hg2
    have hV := transfer_eq_pow_of_forall ϕ hg (by
      intro k a ha
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · have h1 : g ^ (2 * j) = 1 := by rw [pow_mul, hg2', one_pow]
        have h2 : (⟨a⁻¹ * g ^ (2 * j) * a, ha⟩ : P') = 1 := Subtype.ext (by simp [h1])
        have h3 : (⟨g ^ (2 * j), P'.pow_mem hg _⟩ : P') = 1 := Subtype.ext (by simp [h1])
        rw [h2, h3]
      · have h1 : g ^ (2 * j + 1) = g := by rw [pow_succ, pow_mul, hg2', one_pow, one_mul]
        have e1 : (⟨g ^ (2 * j + 1), P'.pow_mem hg _⟩ : P') = ⟨g, hg⟩ := Subtype.ext h1
        have ha' : a⁻¹ * g * a ∈ P' := by rwa [h1] at ha
        have e2 : (⟨a⁻¹ * g ^ (2 * j + 1) * a, ha⟩ : P') = ⟨a⁻¹ * g * a, ha'⟩ :=
          Subtype.ext (by show a⁻¹ * g ^ (2 * j + 1) * a = a⁻¹ * g * a; rw [h1])
        rw [e1, e2, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          Subgroup.mul_mem_iff_of_index_two hQ'index]
        simp only [inv_mem_iff]
        have := hcond a ha'
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact this.symm)
    rw [hV]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have huQ0 : u ∉ Q := fun h => hQu 1 (by simpa using h)
  have hu1 : MonoidHom.transfer ϕ u = ϕ ⟨u, huP⟩ := by
    refine heval u huP hu ?_
    intro a _
    exact iff_of_false (hQu a) huQ0
  have huQ : (⟨u, huP⟩ : P') ∉ Q' := fun h => huQ0 (Subgroup.mem_subgroupOf.1 h)
  have hz1 : ϕ ⟨u, huP⟩ ≠ 1 := fun h => huQ ((QuotientGroup.eq_one_iff _).1 h)
  refine ⟨(MonoidHom.transfer ϕ).ker, MonoidHom.normal_ker _, ?_, ?_, ?_⟩
  · rw [Subgroup.index_ker]
    have hdvd : Nat.card (MonoidHom.transfer ϕ).range ∣ 2 := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hne : Nat.card (MonoidHom.transfer ϕ).range ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      have : MonoidHom.transfer ϕ u ∈ (MonoidHom.transfer ϕ).range := ⟨u, rfl⟩
      rw [h1, Subgroup.mem_bot, hu1] at this
      exact hz1 this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  · rw [MonoidHom.mem_ker, hu1]
    exact hz1
  · intro g hgP hg2 hcond
    rw [MonoidHom.mem_ker, heval g hgP hg2 hcond]
    constructor
    · intro h
      have := (QuotientGroup.eq_one_iff _).1 h
      exact Subgroup.mem_subgroupOf.1 this
    · intro h
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)

theorem card_map_subtype {G : Type*} [Group G] (X : Subgroup G) (W : Subgroup X) :
    Nat.card (W.map X.subtype) = Nat.card W :=
  (Nat.card_congr (Subgroup.equivMapOfInjective W X.subtype X.subtype_injective)).symm

@[expose] def sylowOfMaximal {G : Type*} [Group G] [Finite G] (X S : Subgroup G) (hSX : S ≤ X)
    (hSp : IsPGroup 2 S) (hSmax : ∀ R : Subgroup G, R ≤ X → IsPGroup 2 R → S ≤ R → R = S) :
    Sylow 2 X where
  toSubgroup := S.subgroupOf X
  isPGroup' := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hSp
    refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  is_maximal' := by
    intro R hR hle
    have hRp : IsPGroup 2 (R.map X.subtype) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
      refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
      rw [card_map_subtype, hn]
    have hle' : S ≤ R.map X.subtype := fun s hs =>
      ⟨⟨s, hSX hs⟩, hle (Subgroup.mem_subgroupOf.2 hs), rfl⟩
    have heq := hSmax _ (Subgroup.map_subtype_le _) hRp hle'
    refine le_antisymm (fun x hx => ?_) hle
    have hx' : (x : G) ∈ R.map X.subtype := ⟨x, hx, rfl⟩
    rw [heq] at hx'
    exact Subgroup.mem_subgroupOf.2 hx'

theorem coe_sylowOfMaximal {G : Type*} [Group G] [Finite G] (X S : Subgroup G) (hSX : S ≤ X)
    (hSp : IsPGroup 2 S) (hSmax : ∀ R : Subgroup G, R ≤ X → IsPGroup 2 R → S ≤ R → R = S) :
    (sylowOfMaximal X S hSX hSp hSmax : Subgroup X) = S.subgroupOf X := rfl

theorem thompson_transfer_index_two_sub {G : Type*} [Group G] [Finite G] (X S Q : Subgroup G)
    (hSX : S ≤ X) (hSp : IsPGroup 2 S)
    (hSmax : ∀ R : Subgroup G, R ≤ X → IsPGroup 2 R → S ≤ R → R = S)
    (hindex : Q.relIndex S = 2) {u : G} (hu : u * u = 1) (huS : u ∈ S)
    (hQu : ∀ a ∈ X, a⁻¹ * u * a ∉ Q) :
    ∃ X₀ : Subgroup G, X₀ ≤ X ∧ (∀ x ∈ X, ∀ w ∈ X₀, x * w * x⁻¹ ∈ X₀) ∧
      Nat.card X = 2 * Nat.card X₀ ∧ u ∉ X₀ ∧ (∀ a ∈ X, a ∈ X₀ ∨ a * u ∈ X₀) ∧
      ∀ g ∈ S, g * g = 1 → (∀ a ∈ X, a⁻¹ * g * a ∈ S → (a⁻¹ * g * a ∈ Q ↔ g ∈ Q)) →
        (g ∈ X₀ ↔ g ∈ Q) := by
  classical
  have hmapcard : ∀ W : Subgroup X, Nat.card (W.map X.subtype) = Nat.card W :=
    fun W => card_map_subtype X W
  let P : Sylow 2 X := sylowOfMaximal X S hSX hSp hSmax
  obtain ⟨X₁, hX₁n, hX₁i, hu1, hcrit⟩ := thompson_transfer_index_two P (Q := Q.subgroupOf X)
    ((Subgroup.relIndex_subgroupOf hSX).trans hindex) (u := (⟨u, hSX huS⟩ : X))
    (Subtype.ext hu) (Subgroup.mem_subgroupOf.2 huS)
    (fun a h => hQu a.1 a.2 (Subgroup.mem_subgroupOf.1 h))
  refine ⟨X₁.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx w hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact ⟨⟨x, hx⟩ * w' * ⟨x, hx⟩⁻¹, hX₁n.conj_mem w' hw' ⟨x, hx⟩, rfl⟩
  · have h1 := Subgroup.card_mul_index X₁
    rw [hX₁i] at h1
    rw [hmapcard]
    omega
  · rintro ⟨w, hw, hwu⟩
    have hweq : w = ⟨u, hSX huS⟩ := Subtype.ext hwu
    rw [hweq] at hw
    exact hu1 hw
  · intro a ha
    by_cases hmem : (⟨a, ha⟩ : X) ∈ X₁
    · left; exact ⟨⟨a, ha⟩, hmem, rfl⟩
    · right
      have : (⟨a, ha⟩ * ⟨u, hSX huS⟩ : X) ∈ X₁ :=
        (Subgroup.mul_mem_iff_of_index_two hX₁i).2 (iff_of_false hmem hu1)
      exact ⟨_, this, rfl⟩
  · intro g hg hg2 hcond
    have hmem : (⟨g, hSX hg⟩ : X) ∈ X₁ ↔ (⟨g, hSX hg⟩ : X) ∈ Q.subgroupOf X :=
      hcrit ⟨g, hSX hg⟩ (Subgroup.mem_subgroupOf.2 hg) (Subtype.ext hg2) (fun a ha => by
        have := hcond a.1 a.2 (Subgroup.mem_subgroupOf.1 ha)
        simpa [Subgroup.mem_subgroupOf] using this)
    rw [Subgroup.mem_subgroupOf] at hmem
    constructor
    · rintro ⟨w, hw, hwg⟩
      have : w = ⟨g, hSX hg⟩ := Subtype.ext hwg
      rw [this] at hw
      exact hmem.1 hw
    · intro h
      exact ⟨⟨g, hSX hg⟩, hmem.2 h, rfl⟩

end CFSG.Quasithin
