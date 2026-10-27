module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.OddTranspositions.QZ

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem odd_relIndex_commutator_of_index_two {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, d * d = 1) (hgen : Subgroup.closure D = ⊤) {L : Subgroup G} (hLn : L.Normal)
    (hL2 : L.index = 2) (hDL : ∀ d ∈ D, d ∉ L) : Odd ((⁅L, L⁆).relIndex L) := by
  classical
  obtain ⟨d₀, rfl⟩ := hcls
  have hd₀ : d₀ ∈ {g | IsConj d₀ g} := IsConj.refl d₀
  set N : Subgroup G := ⁅L, L⁆ with hN
  haveI : N.Normal := Subgroup.commutator_normal L L
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set A : Subgroup (G ⧸ N) := L.map π with hA
  have hNL : N ≤ L := Subgroup.commutator_le_left L L
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul]
    change ((x * y * (y * x)⁻¹ : G) : G ⧸ N) = 1
    rw [QuotientGroup.eq_one_iff]
    have h := Subgroup.commutator_mem_commutator hx hy
    rw [commutatorElement_def] at h
    convert h using 1
    group
  set c : G ⧸ N := π d₀ with hcdef
  have hc2 : c * c = 1 := by rw [hcdef, ← map_mul, hinv d₀ hd₀, map_one]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hcc : ∀ y : G ⧸ N, c * (c * y) = y := fun y => by rw [← mul_assoc, hc2, one_mul]
  have hAn : A.Normal := Subgroup.Normal.map hLn π hπs
  have hcx : ∀ x ∈ A, c * x * c⁻¹ ∈ A := fun x hx => hAn.conj_mem x hx c
  let f : A →* A :=
    { toFun := fun x => ⟨c * x * c⁻¹ * (x : G ⧸ N)⁻¹, A.mul_mem (hcx x x.2) (A.inv_mem x.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        ext
        simp only [Subgroup.coe_mul]
        have h1 := hAab _ (hcx y hy) _ (A.inv_mem hx)
        have hxy := hAab x hx y hy
        calc c * (x * y) * c⁻¹ * (x * y)⁻¹
            = c * (x * y) * c⁻¹ * (y * x)⁻¹ := by rw [hxy]
          _ = (c * x * c⁻¹) * ((c * y * c⁻¹) * x⁻¹) * y⁻¹ := by group
          _ = (c * x * c⁻¹) * (x⁻¹ * (c * y * c⁻¹)) * y⁻¹ := by rw [h1]
          _ = c * x * c⁻¹ * x⁻¹ * (c * y * c⁻¹ * y⁻¹) := by group }
  have hf : ∀ x : A, (f x : G ⧸ N) = c * x * c⁻¹ * (x : G ⧸ N)⁻¹ := fun x => rfl
  set Bq : Subgroup (G ⧸ N) := f.range.map A.subtype with hBq
  have hBqA : Bq ≤ A := by rintro _ ⟨b, -, rfl⟩; exact b.2
  have hconjL : ∀ g ∈ L, π (g * d₀ * g⁻¹) ∈ (Bq : Set (G ⧸ N)) * ({c} : Set (G ⧸ N)) := by
    intro g hg
    have hgA : π g ∈ A := ⟨g, hg, rfl⟩
    refine ⟨f ⟨(π g)⁻¹, A.inv_mem hgA⟩, ⟨_, ⟨_, rfl⟩, rfl⟩, c, rfl, ?_⟩
    rw [hf]
    simp only [map_mul, map_inv, inv_inv]
    have h := hAab _ (hcx _ (A.inv_mem hgA)) _ hgA
    calc c * (π g)⁻¹ * c⁻¹ * π g * c = (c * (π g)⁻¹ * c⁻¹ * π g) * c := by group
      _ = (π g * (c * (π g)⁻¹ * c⁻¹)) * c := by rw [h]
      _ = π g * c * (π g)⁻¹ := by group
  have hconj : ∀ x ∈ {g | IsConj d₀ g}, π x ∈ (Bq : Set (G ⧸ N)) * ({c} : Set (G ⧸ N)) := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    by_cases hg : g ∈ L
    · exact hconjL g hg
    · have hgd : g * d₀ ∈ L := by
        rw [Subgroup.mul_mem_iff_of_index_two hL2]
        exact iff_of_false hg (hDL d₀ hd₀)
      have : g * d₀ * g⁻¹ = (g * d₀) * d₀ * (g * d₀)⁻¹ := by group
      rw [this]
      exact hconjL _ hgd
  have hcN : c ∈ Subgroup.normalizer (Bq : Set (G ⧸ N)) := by
    have key : ∀ b ∈ Bq, c * b * c⁻¹ ∈ Bq := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨f ⟨c * x * c⁻¹, hcx x x.2⟩, ⟨_, rfl⟩, ?_⟩
      simp only [Subgroup.coe_subtype, hf]
      simp only [mul_assoc, hcinv, mul_inv_rev, inv_inv, hcc]
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨key b, fun hb => ?_⟩
    have := key _ hb
    simpa only [mul_assoc, hcinv, hcc, hc2, mul_one] using this
  have hsup : ((Subgroup.zpowers c ⊔ Bq : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (Subgroup.zpowers c : Set (G ⧸ N)) * (Bq : Set (G ⧸ N)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hcN)
  have htop : Subgroup.zpowers c ⊔ Bq = ⊤ := by
    have hcl : Subgroup.closure (π '' {g | IsConj d₀ g}) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective π hπs]
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, _, rfl, hbc⟩ := hconj x hx
    rw [← hbc, sup_comm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hcardc : Nat.card (Subgroup.zpowers c) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, hc2])
  have hQle : Nat.card (G ⧸ N) ≤ 2 * Nat.card Bq := by
    have h1 : Nat.card (G ⧸ N) =
        Nat.card ((Subgroup.zpowers c : Set (G ⧸ N)) * (Bq : Set (G ⧸ N))) := by
      rw [← hsup, htop]; simp [Nat.card_univ]
    rw [h1]
    calc Nat.card ((Subgroup.zpowers c : Set (G ⧸ N)) * (Bq : Set (G ⧸ N)))
        ≤ Nat.card (Subgroup.zpowers c : Set (G ⧸ N)) * Nat.card (Bq : Set (G ⧸ N)) :=
          Set.natCard_mul_le
      _ ≤ 2 * Nat.card Bq := Nat.mul_le_mul_right _ hcardc
  have hAidx : A.index = 2 := by
    rw [hA, Subgroup.index_map_eq _ hπs (by rw [QuotientGroup.ker_mk']; exact hNL), hL2]
  have hQA : Nat.card (G ⧸ N) = 2 * Nat.card A := by
    rw [← A.index_mul_card, hAidx]
  have hBqcard : Nat.card Bq = Nat.card f.range :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ A.subtype_injective).symm.toEquiv
  have hrange : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    omega
  have hfsurj : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
  have hfinj : Function.Injective f := Finite.injective_iff_surjective.mpr hfsurj
  have hAcard : Nat.card A = N.relIndex L := by
    have h1 := Subgroup.relIndex_mul_index hNL
    rw [hL2, Subgroup.index] at h1
    omega
  rw [← hAcard]
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (even_iff_two_dvd.mp hodd)
  obtain ⟨y, rfl⟩ := hfsurj t
  have hinvt : (f y)⁻¹ = f y := by
    have : (f y) ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one _
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, this])
  have hfix : f (f y) = 1 := by
    ext
    rw [hf]
    set t : G ⧸ N := (f y : G ⧸ N) with ht'
    have h1 : c * t * c⁻¹ = t⁻¹ := by
      rw [ht', hf]
      simp only [mul_assoc, hcinv, mul_inv_rev, inv_inv, hcc]
    have h2 : t⁻¹ = t := by
      have := congrArg Subtype.val hinvt
      simpa [ht'] using this
    rw [h1]
    conv_lhs => arg 1; rw [h2]
    simp
  have : f y = 1 := hfinj (by rw [hfix, map_one])
  rw [this, orderOf_one] at ht
  exact absurd ht (by norm_num)

end CFSG.OddTranspositions.QZ
