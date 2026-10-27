module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def conjAut (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    MulAut ↥K where
  toFun k := ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg k).1 k.2⟩
  invFun k := ⟨g⁻¹ * k * g, (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * k * g)).2 (by
    rw [show g * (g⁻¹ * (k : G) * g) * g⁻¹ = k by group]
    exact k.2)⟩
  left_inv k := by
    apply Subtype.ext
    change g⁻¹ * (g * (k : G) * g⁻¹) * g = k
    group
  right_inv k := by
    apply Subtype.ext
    change g * (g⁻¹ * (k : G) * g) * g⁻¹ = k
    group
  map_mul' x y := by
    apply Subtype.ext
    change g * ((x : G) * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹)
    group

@[expose] def conjHom (K R : Subgroup G) (h : K ≤ Subgroup.normalizer (R : Set G)) :
    ↥K →* MulAut ↥R where
  toFun k := conjAut R k (h k.2)
  map_one' := by
    ext r
    change (1 : G) * r * (1 : G)⁻¹ = r
    group
  map_mul' x y := by
    ext r
    change ((x * y : K) : G) * r * ((x * y : K) : G)⁻¹ =
      (x : G) * ((y : G) * r * (y : G)⁻¹) * (x : G)⁻¹
    simp [mul_assoc]

theorem le_normalizer_of_characteristic {K R T : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (R : Set G)) (hTR : T ≤ R)
    (hT : (T.subgroupOf R).Characteristic) : K ≤ Subgroup.normalizer (T : Set G) := by
  have key : ∀ g ∈ K, ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg x hx
    have h1 := Subgroup.characteristic_iff_le_comap.1 hT (conjAut R g (hK hg))
    have hx' : (⟨x, hTR hx⟩ : ↥R) ∈ T.subgroupOf R := hx
    exact h1 hx'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (K.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem card_modEq_card_inf_centralizer [Finite G] (Y : Subgroup G) {a : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (ha5 : a ^ 5 = 1) :
    Nat.card Y ≡ Nat.card (Y ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype ↥Y := Fintype.ofFinite ↥Y
  have hK : Subgroup.zpowers a ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.2 ha
  set σ : Equiv.Perm ↥Y := MulAut.toPerm ↥Y (conjAut Y a ha) with hσ
  have hk5 : (⟨a, Subgroup.mem_zpowers a⟩ : ↥(Subgroup.zpowers a)) ^ 5 = 1 :=
    Subtype.ext (by simpa using ha5)
  have hconj5 : (conjAut Y a ha) ^ 5 = 1 := by
    have h : (conjHom (Subgroup.zpowers a) Y hK ⟨a, Subgroup.mem_zpowers a⟩) ^ 5 = 1 := by
      rw [← map_pow, hk5, map_one]
    exact h
  have hσ5 : σ ^ 5 ^ 1 = 1 := by
    rw [pow_one, hσ, ← map_pow, hconj5, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ5
  have hfix : ∀ y : ↥Y,
      y ∈ (Equiv.Perm.support σ)ᶜ ↔ (y : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    intro y
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not,
      Subgroup.mem_centralizer_singleton_iff]
    have hσy : ((σ y : ↥Y) : G) = a * (y : G) * a⁻¹ := rfl
    rw [Subtype.ext_iff, hσy]
    constructor
    · intro h
      calc (y : G) * a = a * y * a⁻¹ * a := by rw [h]
        _ = a * y := by group
    · intro h
      calc a * (y : G) * a⁻¹ = y * a * a⁻¹ := by rw [← h]
        _ = y := by group
  have hcard : ((Equiv.Perm.support σ)ᶜ).card =
      Nat.card (Y ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨(y.1 : G), y.1.2, (hfix y.1).1 y.2⟩) ⟨?_, ?_⟩)
    · intro y z hyz
      have h : ((y.1 : ↥Y) : G) = ((z.1 : ↥Y) : G) :=
        congrArg (fun w : ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) => (w : G)) hyz
      exact Subtype.ext (Subtype.ext h)
    · rintro ⟨g, hgY, hgc⟩
      exact ⟨⟨⟨g, hgY⟩, (hfix ⟨g, hgY⟩).2 hgc⟩, rfl⟩
  rw [← hcard, Nat.card_eq_fintype_card]
  exact hmod.symm

end CFSG.RankThree.PartOne.OddCore37
