module

public import CFSG.Quasithin.EmptyFaithful.S153Q1b
public import CFSG.Quasithin.EmptyFaithful.S153Q1a

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q1

open Equiv

theorem hatGrp_top {G : Type*} [Group G] (h : F6.IsHatSym 6 G) :
    ∃ (A : Subgroup G) (z : G), HatGrp (⊤ : Subgroup G) A z := by
  classical
  obtain ⟨φ, hs, hk, hA⟩ := h
  have h720 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hcard : Nat.card G = 2160 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hs).toEquiv, hk, h720] at h1
    exact h1
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨⟨hperf, -⟩, hZ3, -⟩ := hA
  generalize hAdef : (alternatingGroup (Fin 6)).comap φ = A at hperf hZ3
  have hmemA : ∀ g : G, g ∈ A ↔ φ g ∈ alternatingGroup (Fin 6) := by
    intro g
    rw [← hAdef]
    rfl
  have hsign : ∀ g : G, g ∈ A ↔ Perm.sign (φ g) = 1 := fun g => by
    rw [hmemA, Perm.mem_alternatingGroup]
  have hAn : A.Normal := by
    rw [← hAdef]
    infer_instance
  have : Group.IsPerfect ↥A := ⟨hperf⟩
  have hidx2 : ∀ g h : G, g ∉ A → h ∉ A → g * h ∈ A := by
    intro g h hg hh
    rw [hsign] at hg hh ⊢
    rw [map_mul, map_mul]
    rcases Int.units_eq_one_or (Perm.sign (φ g)) with h1 | h1
    · exact absurd h1 hg
    · rcases Int.units_eq_one_or (Perm.sign (φ h)) with h2 | h2
      · exact absurd h2 hh
      · rw [h1, h2]
        rfl
  have hAidx : A.index = 2 := by
    rw [← hAdef, Subgroup.index_comap_of_surjective _ hs]
    exact alternatingGroup.index_eq_two
  have hAcard : Nat.card ↥A = 1080 := by
    have h1 := A.card_mul_index
    rw [hAidx, hcard] at h1
    omega
  have hkA : φ.ker ≤ A := fun g hg => by
    rw [hsign, MonoidHom.mem_ker.mp hg, map_one]
  have : (φ.ker.subgroupOf A).Normal := Subgroup.Normal.subgroupOf inferInstance A
  have hKr3 : Nat.card ↥(φ.ker.subgroupOf A) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkA).toEquiv]
    exact hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥(φ.ker.subgroupOf A) := isCyclic_of_prime_card hKr3
  have hKc : φ.ker.subgroupOf A ≤ Subgroup.center ↥A := le_center_of_isCyclic hperf
  have hkerc : ∀ q : ↥A, φ q = 1 → q ∈ Subgroup.center ↥A := fun q hq =>
    hKc (Subgroup.mem_subgroupOf.mpr (MonoidHom.mem_ker.mpr hq))
  have hrange : (φ.comp A.subtype).range = alternatingGroup (Fin 6) := by
    ext σ
    constructor
    · rintro ⟨q, rfl⟩
      exact (hmemA q).1 q.2
    · intro hσ
      obtain ⟨g, rfl⟩ := hs σ
      exact ⟨⟨g, (hmemA g).2 hσ⟩, rfl⟩
  obtain ⟨z, hzK, hz1, hz3⟩ := exists_ne_one_of_card_three hk
  have hzk : φ.ker = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzK)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, hk])).symm
  have hzA : z ∈ A := hkA hzK
  have hzc : (⟨z, hzA⟩ : ↥A) ∈ Subgroup.center ↥A :=
    hkerc ⟨z, hzA⟩ (MonoidHom.mem_ker.mp hzK)
  have hz_central : ∀ g ∈ A, g * z = z * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨g, hg⟩)
  obtain ⟨t₀, ht₀⟩ := hs (swap 4 5)
  have ht₀A : t₀ ∉ A := by
    rw [hsign, ht₀, Perm.sign_swap (by decide)]
    decide
  have hinv : t₀ * z * t₀⁻¹ = z⁻¹ := by
    let α : ↥A →* ↥A := (MulAut.conjNormal t₀ : MulAut ↥A).toMonoidHom
    have hα : ∀ q : ↥A,
        (φ.comp A.subtype) (α q) = swap 4 5 * (φ.comp A.subtype) q * swap 4 5 := by
      intro q
      simp only [α, MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conjNormal_apply, map_mul, map_inv, ht₀, swap_inv]
    have h1 := inv_of_cover hZ3 (φ.comp A.subtype) hkerc hrange α hα hzc
    have h2 := congrArg Subtype.val h1
    simpa [α, MulAut.conjNormal_apply] using h2
  have houter : ∀ t ∈ (⊤ : Subgroup G), t ∉ A → t * z * t⁻¹ = z⁻¹ := by
    intro t _ htA
    have h1 : t * t₀⁻¹ ∈ A :=
      hidx2 t t₀⁻¹ htA (fun hh => ht₀A (by simpa using A.inv_mem hh))
    have hc : Commute (t * t₀⁻¹) z := hz_central _ h1
    calc t * z * t⁻¹ = (t * t₀⁻¹) * (t₀ * z * t₀⁻¹) * (t * t₀⁻¹)⁻¹ := by group
      _ = (t * t₀⁻¹) * z⁻¹ * (t * t₀⁻¹)⁻¹ := by rw [hinv]
      _ = z⁻¹ := by rw [hc.inv_right.eq]; group
  have hpsi : ∃ ψ : ↥A →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ ∧
      ∀ g : ↥A, ψ g = 1 ↔ (g : G) ∈ Subgroup.zpowers z := by
    refine ⟨(φ.comp A.subtype).codRestrict (alternatingGroup (Fin 6))
      (fun q => (hmemA q).1 q.2), ?_, ?_⟩
    · intro σ
      obtain ⟨g, hg⟩ := hs σ
      have hgA : g ∈ A := (hmemA g).2 (by rw [hg]; exact σ.2)
      exact ⟨⟨g, hgA⟩, Subtype.ext hg⟩
    · intro q
      constructor
      · intro h1
        have h2 : φ q = 1 := congrArg Subtype.val h1
        rw [← hzk]
        exact h2
      · intro h1
        rw [← hzk] at h1
        exact Subtype.ext (MonoidHom.mem_ker.mp h1)
  have hgen : ∀ X : Subgroup G, (∀ x ∈ (⊤ : Subgroup G), Odd (orderOf x) → x ∈ X) → A ≤ X := by
    intro X hX a ha
    have h1 : Subgroup.closure {x : ↥A | Odd (orderOf x)} ≤ X.subgroupOf A := by
      rw [Subgroup.closure_le]
      intro x hx
      exact hX x trivial (by rw [Subgroup.orderOf_coe]; exact hx)
    have h2 : (⟨a, ha⟩ : ↥A) ∈ X.subgroupOf A :=
      h1 (by rw [closure_odd_eq_top]; exact Subgroup.mem_top _)
    exact h2
  exact ⟨A, z,
    { Ah_le := le_top
      Ah_norm := fun g _ a ha => hAn.conj_mem a ha g
      index2 := fun g _ h' _ hg hh => hidx2 g h' hg hh
      z_mem := hzA
      z_ne := hz1
      z_cube := hz3
      z_central := hz_central
      outer := houter
      perfect := (Subgroup.isPerfect_iff.mp inferInstance).ge
      card := hAcard
      psi := hpsi
      gen_odd := hgen }⟩

end Q1

theorem hatGrp_of_isHatSym {K : Type*} [Group K] {Γ : Subgroup K} (h : F6.IsHatSym 6 ↥Γ) :
    ∃ (Ah : Subgroup K) (z : K), HatGrp Γ Ah z := by
  obtain ⟨A, z, hG⟩ := Q1.hatGrp_top h
  refine ⟨A.map Γ.subtype, Γ.subtype z, Q1.hatGrp_map hG Γ.subtype Γ.subtype_injective ?_⟩
  rw [Subgroup.map_top, Subgroup.range_subtype]

end S153Q

end CFSG.Quasithin
