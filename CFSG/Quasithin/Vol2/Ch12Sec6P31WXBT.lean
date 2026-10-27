module

public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.QuasithinUnique CFSG.ASVolI
open scoped Pointwise

section Counting

theorem bt_card_map_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (hK : f.ker ≤ K) : Nat.card (K.map f) * Nat.card f.ker = Nat.card K := by
  set g : ↥K →* H := f.comp K.subtype with hg
  have h1 : Nat.card (↥K ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h2 : g.range = K.map f := by
    ext x
    simp [hg, Subgroup.mem_map]
  have h3 : g.ker = f.ker.subgroupOf K := by
    ext x
    simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h4 : Nat.card (f.ker.subgroupOf K) = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  rw [← h4, ← h3, ← h2, ← h1]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker).symm

end Counting

section Transport

variable {Y : Type} [Group Y] {X U : Subgroup Y} {G : Type} [Group G]

theorem bt_sylow_iso [Finite G] (hU : IsSylowTwoOf U X) (e₀ : ↥X ≃* G) {R : Subgroup G}
    (hR : IsSylowTwoOf R ⊤) :
    ∃ e : ↥X ≃* G, (U.subgroupOf X).map e.toMonoidHom = R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf (U.subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm
    · have h1 : ((U.subgroupOf X).subgroupOf ⊤).index = (U.subgroupOf X).index := by
        change (U.subgroupOf X).relIndex ⊤ = _
        exact Subgroup.relIndex_top_right _
      rw [h1]
      exact hU.2.2
  exact burnsideAut_exists_equiv_sylow e₀ hS hR

variable (hU : IsSylowTwoOf U X) (e : ↥X ≃* G) {UG : Subgroup G}
  (he : (U.subgroupOf X).map e.toMonoidHom = UG)

include hU in
theorem bt_hsub :
    (X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X =
      Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx' : (x : Y) ∈ Subgroup.normalizer (U : Set Y) := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_normalizer_iff] at hx'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hx' (h : Y)
  · intro hx
    have hx' : (x : Y) ∈ Subgroup.normalizer (U : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      by_cases hh : h ∈ X
      · have key := (Subgroup.mem_normalizer_iff.mp hx) ⟨h, hh⟩
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
        simpa using key
      · have h1 : h ∉ U := fun h' => hh (hU.1 h')
        have h2 : (x : Y) * h * (x : Y)⁻¹ ∉ U := by
          intro h'
          apply hh
          have h'' : (x : Y) * h * (x : Y)⁻¹ ∈ X := hU.1 h'
          have hm := X.mul_mem (X.inv_mem x.2) (X.mul_mem h'' x.2)
          simpa [mul_assoc] using hm
        exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
    exact Subgroup.mem_inf.mpr ⟨x.2, hx'⟩

include hU e he in
theorem bt_mem_B (g : ↥X) :
    (g : Y) ∈ X ⊓ Subgroup.normalizer (U : Set Y) ↔
      e g ∈ Subgroup.normalizer (UG : Set G) := by
  have hNB : (Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)).map e.toMonoidHom =
      Subgroup.normalizer (UG : Set G) := by
    rw [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) _ e.bijective, he]
  rw [← hNB]
  have h1 : (g : Y) ∈ X ⊓ Subgroup.normalizer (U : Set Y) ↔
      g ∈ (X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X := Subgroup.mem_subgroupOf.symm
  rw [h1, bt_hsub hU]
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm

include e he in
theorem bt_mem_U (g : ↥X) : (g : Y) ∈ U ↔ e g ∈ UG := by
  rw [← he]
  have : (g : Y) ∈ U ↔ g ∈ U.subgroupOf X := Subgroup.mem_subgroupOf.symm
  rw [this]
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm

include hU e he in
theorem bt_card_B :
    Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) =
      Nat.card ↥(Subgroup.normalizer (UG : Set G)) := by
  have hNB : (Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)).map e.toMonoidHom =
      Subgroup.normalizer (UG : Set G) := by
    rw [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) _ e.bijective, he]
  have h1 : Nat.card ↥((X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X) =
      Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      X ⊓ Subgroup.normalizer (U : Set Y) ≤ X)).toEquiv
  have h2 := Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    (K := Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X))
  rw [← h1, bt_hsub hU, ← h2, hNB]

include hU e he in
theorem bt_card_U : Nat.card ↥U = Nat.card ↥UG := by
  have h1 : Nat.card ↥(U.subgroupOf X) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv
  have h2 : Nat.card ↥((U.subgroupOf X).map e.toMonoidHom) = Nat.card ↥(U.subgroupOf X) :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
  rw [← h1, ← h2, he]

include hU e he in
theorem bt_coatom (h : IsCoatom (Subgroup.normalizer (UG : Set G))) :
    IsCoatom ((X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X) := by
  have hNB : (Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)).map e.toMonoidHom =
      Subgroup.normalizer (UG : Set G) := by
    rw [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) _ e.bijective, he]
  rw [bt_hsub hU]
  have h' : IsCoatom ((Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)).map
      e.toMonoidHom) := by
    rw [hNB]
    exact h
  exact (OrderIso.isCoatom_iff e.mapSubgroup _).1 h'

include hU e he in
theorem bt_cyc (h : ∃ g ∈ Subgroup.normalizer (UG : Set G), ∀ b ∈ Subgroup.normalizer (UG : Set G),
    ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ UG) :
    ∃ g ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
      ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U := by
  obtain ⟨g₀, hg₀, hcyc⟩ := h
  obtain ⟨g', hg'⟩ : ∃ g' : ↥X, e g' = g₀ := ⟨e.symm g₀, MulEquiv.apply_symm_apply e g₀⟩
  have hg'B : (g' : Y) ∈ X ⊓ Subgroup.normalizer (U : Set Y) :=
    (bt_mem_B hU e he g').2 (by rw [hg']; exact hg₀)
  refine ⟨(g' : Y), hg'B, fun b hb => ?_⟩
  have hbX : b ∈ X := (Subgroup.mem_inf.mp hb).1
  have hbN : e ⟨b, hbX⟩ ∈ Subgroup.normalizer (UG : Set G) := (bt_mem_B hU e he ⟨b, hbX⟩).1 hb
  obtain ⟨k, hk⟩ := hcyc (e ⟨b, hbX⟩) hbN
  refine ⟨k, ?_⟩
  have hmem : e ((g' ^ k)⁻¹ * ⟨b, hbX⟩) ∈ UG := by
    rw [map_mul, map_inv, map_pow, hg']
    exact hk
  have := (bt_mem_U e he _).2 hmem
  simpa using this

include hU e he in
theorem bt_abel (h : ∀ a ∈ Subgroup.normalizer (UG : Set G), ∀ b ∈ Subgroup.normalizer (UG : Set G),
    a * b * a⁻¹ * b⁻¹ ∈ UG) :
    ∀ a ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
      a * b * a⁻¹ * b⁻¹ ∈ U := by
  intro a ha b hb
  have haX : a ∈ X := (Subgroup.mem_inf.mp ha).1
  have hbX : b ∈ X := (Subgroup.mem_inf.mp hb).1
  have hc := h (e ⟨a, haX⟩) ((bt_mem_B hU e he ⟨a, haX⟩).1 ha) (e ⟨b, hbX⟩)
    ((bt_mem_B hU e he ⟨b, hbX⟩).1 hb)
  have hmem : e (⟨a, haX⟩ * ⟨b, hbX⟩ * ⟨a, haX⟩⁻¹ * ⟨b, hbX⟩⁻¹) ∈ UG := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hc
  have := (bt_mem_U e he _).2 hmem
  simpa using this

include hU e he in
theorem bt_solv
    (h : ∀ A : Subgroup G, UG ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer (UG : Set G)) :
    ∀ A : Subgroup Y, A ≤ X → U ≤ A → Group.IsSolvable ↥A →
      A ≤ X ⊓ Subgroup.normalizer (U : Set Y) := by
  intro A hAX hUA hAs
  set A' : Subgroup G := (A.subgroupOf X).map e.toMonoidHom with hA'
  have hUA' : UG ≤ A' := by
    rw [← he]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hUA (Subgroup.mem_subgroupOf.mp hx)))
  have hA's : Group.IsSolvable ↥A' := by
    have e1 : ↥(A.subgroupOf X) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAX
    haveI : Group.IsSolvable ↥(A.subgroupOf X) :=
      Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective
    have e2 : ↥(A.subgroupOf X) ≃* ↥A' := (A.subgroupOf X).equivMapOfInjective _ e.injective
    exact Group.isSolvable_of_surjective (f := e2.toMonoidHom) e2.surjective
  have hle := h A' hUA' hA's
  intro a ha
  have haX : a ∈ X := hAX ha
  have haA' : e ⟨a, haX⟩ ∈ A' := ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  exact (bt_mem_B hU e he ⟨a, haX⟩).2 (hle haA') |> fun hb => by
    exact Subgroup.mem_inf.mpr ⟨haX, (Subgroup.mem_inf.mp hb).2⟩

include hU e he in
theorem bt_conj [Finite G] (r : Y)
    (hr : r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y)) :
    ∃ α : MulAut G, UG.map α.toMonoidHom = UG ∧
      ∀ (x : ↥X) (hx : r * (x : Y) * r⁻¹ ∈ X), e ⟨r * (x : Y) * r⁻¹, hx⟩ = α (e x) := by
  obtain ⟨hrX, hrU⟩ := hr
  have hrX' : X.map (MulAut.conj r).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hrX
  let θ : ↥X ≃* ↥X :=
    (MulEquiv.subgroupMap (MulAut.conj r) X).trans (MulEquiv.subgroupCongr hrX')
  have hθ : ∀ x : ↥X, ((θ x : ↥X) : Y) = r * (x : Y) * r⁻¹ := fun x => rfl
  let α : MulAut G := (e.symm.trans θ).trans e
  refine ⟨α, ?_, ?_⟩
  · apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨p, hp, rfl⟩
      have hs : e.symm p ∈ U.subgroupOf X := by
        rw [← he] at hp
        obtain ⟨s, hs, rfl⟩ := hp
        simpa using hs
      have hsU : ((e.symm p : ↥X) : Y) ∈ U := Subgroup.mem_subgroupOf.mp hs
      have hθU : ((θ (e.symm p) : ↥X) : Y) ∈ U := by
        rw [hθ]
        exact (Subgroup.mem_normalizer_iff.mp hrU _).1 hsU
      exact (bt_mem_U e he (θ (e.symm p))).1 hθU
    · exact le_of_eq (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).symm
  · intro x hx
    change e ⟨r * (x : Y) * r⁻¹, hx⟩ = e (θ (e.symm (e x)))
    rw [MulEquiv.symm_apply_apply]
    rfl

end Transport

end CFSG.Quasithin.H13.P31X
