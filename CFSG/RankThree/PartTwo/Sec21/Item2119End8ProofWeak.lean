module

import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools
public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofJ

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Item2119End8Proof

variable {G : Type} [Group G] [Finite G]

theorem facts_H {A L Le Fb Q : Subgroup G} {c d b : G} (hF : IsFOf2127 A Le Fb)
    (hL : IsLOf2125 L c d b Le) (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (h28 : Concl2128 Le Fb Q) :
    Nat.card (Fb ⊓ Le : Subgroup G) = 9 ∧
      ∀ v ∈ Fb ⊓ Le, ∀ w ∈ Fb ⊓ Le, v ≠ 1 → w ≠ 1 →
        ∃ m ∈ Le ⊓ Subgroup.normalizer (Fb : Set G), m * v * m⁻¹ = w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eL34⟩ := h26
  obtain ⟨hFe, hF27, -, -, ⟨eQ8⟩⟩ := hF
  obtain ⟨-, -, -, ⟨eLe⟩, -, -⟩ := hL
  obtain ⟨-, hYtriv, -⟩ := h28
  have hVc : ∀ x y : Fb, x * y = y * x := fun x y => hFe.1.is_comm.comm x y
  have hV3 : ∀ x : Fb, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hFe.2 x x.2)
  have hT : Le.subgroupOf Fb ≠ ⊤ := by
    intro h
    have hle : Fb ≤ Le := by
      intro x hx
      have hx' : (⟨x, hx⟩ : Fb) ∈ Le.subgroupOf Fb := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    apply Item2119End3Proof.not_dvd_card_of_lBar eLe eL34
    rw [← hF27]
    exact Subgroup.card_dvd_of_le hle
  have hQ8T : Sec4.autIn Le Fb ≤ Item2119End3Proof.fixQuot (Le.subgroupOf Fb) := by
    rw [← Item2119End3Proof.trivOnQuot_eq_fixQuot]
    refine le_trans (Item2119End3Proof.autIn_le_of_le ?_) hYtriv
    exact (le_sup_left : Le ⊓ Subgroup.normalizer (Fb : Set G) ≤
      (Le ⊓ Subgroup.normalizer (Fb : Set G)) ⊔ Q)
  have hT9 := Item2119End3Proof.card_eq_nine hV3 hF27 hT eQ8 hQ8T
  refine ⟨?_, ?_⟩
  · rw [← hT9, inf_comm, ← Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_map_of_injective Fb.subtype_injective
  · intro v hv w hw hv1 hw1
    have hv' : (⟨v, hv.1⟩ : Fb) ∈ Le.subgroupOf Fb := Subgroup.mem_subgroupOf.mpr hv.2
    have hw' : (⟨w, hw.1⟩ : Fb) ∈ Le.subgroupOf Fb := Subgroup.mem_subgroupOf.mpr hw.2
    obtain ⟨φ, hφ, hφv⟩ := Item2119End3Proof.exists_mem_quaternion_apply_eq hVc hV3 hT9 eQ8
      hQ8T hv' (fun h => hv1 (congrArg Subtype.val h)) hw'
      (fun h => hw1 (congrArg Subtype.val h))
    obtain ⟨m, hmN, hmL, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    refine ⟨m, ⟨hmL, hmN⟩, ?_⟩
    have h := congrArg Subtype.val hφv
    rwa [Sec4.normalizerMonoidHom_apply_coe] at h

theorem quadratic_of_normal {D H Y : Subgroup G} {b : G} (hDe : IsElemAbelian 3 D)
    (hD81 : Nat.card D = 81) (hb3 : b ^ 3 = 1) (hbY : b ∈ Y)
    (hYD : Y ≤ Subgroup.normalizer (D : Set G)) (hbD : b ∉ D)
    (hrank : ∀ X : Subgroup G, IsPGroup 3 X → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      X ≤ Subgroup.centralizer ({b} : Set G) → Nat.card X ≤ 27)
    (hHD : H ≤ D) (hHb : H ≤ Subgroup.centralizer ({b} : Set G)) (hH9 : Nat.card H = 9)
    (hconj : ∀ y ∈ Y, ∃ h ∈ H, y * b * y⁻¹ = b * h)
    (htrans : ∀ v ∈ H, ∀ w ∈ H, v ≠ 1 → w ≠ 1 → ∃ m ∈ Y, m * v * m⁻¹ = w) :
    ∀ x ∈ D, b * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbN : b ∈ Subgroup.normalizer (D : Set G) := hYD hbY
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD3 : IsPGroup 3 D := isPGroup_of_pow hDe.2
  set C := D ⊓ Subgroup.centralizer ({b} : Set G) with hCdef
  have hC9 : Nat.card C ≤ 9 := by
    have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy => hDc x hx.1 y hy.1
    have hbc : ∀ y ∈ C, b * y = y * b := fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
    have hC3 : IsPGroup 3 C := hD3.to_le inf_le_left
    have hb3' : IsPGroup 3 (Subgroup.zpowers b) := by
      refine isPGroup_of_pow fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hZ3 : IsPGroup 3 (Subgroup.zpowers b ⊔ C : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hb3' hC3
        (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun y hy => (hbc y hy).symm)))
    have hZc := comm_sup (comm_zpowers_self b) hCc (comm_zpowers hbc)
    have hZC := le_centralizer_of_mem hZc (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
    have h27 := hrank _ hZ3 hZc hZC
    have hlt : C < Subgroup.zpowers b ⊔ C := by
      refine lt_of_le_of_ne le_sup_right fun h => hbD ?_
      have : b ∈ C := by rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
      exact this.1
    have hClt := Subgroup.card_lt_of_lt hlt
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hC3
    rw [hm] at hClt ⊢
    have hm2 : m < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp
      (show 3 ^ m < 3 ^ 3 by omega)
    calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  have hHC : H = C := Subgroup.eq_of_le_of_card_ge (le_inf hHD hHb) (by rw [hH9]; exact hC9)
  let _ : CommGroup D :=
    { (inferInstance : Group D) with mul_comm := fun x y => hDe.1.is_comm.comm x y }
  have h3 : ∀ x : D, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hDe.2 x x.2)
  set φ : D →* D := (D.normalizerMonoidHom ⟨b, hbN⟩ : MulAut D).toMonoidHom with hφdef
  have hφ : ∀ x : D, (φ x : G) = b * x * b⁻¹ := fun x => rfl
  have hφ3 : ∀ x : D, φ (φ (φ x)) = x := by
    intro x
    apply Subtype.ext
    rw [hφ, hφ, hφ]
    have hb3' : b * b * b = 1 := by rw [← pow_three']; exact hb3
    calc b * (b * (b * (x : G) * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * x * (b * b * b)⁻¹ := by
          group
      _ = x := by rw [hb3']; group
  let τ : D →* D :=
    { toFun := fun y => y⁻¹ * φ y
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev]
        simp only [mul_assoc, mul_comm, mul_left_comm] }
  have hτ : ∀ y : D, τ y = y⁻¹ * φ y := fun y => rfl
  have hτ3 : ∀ x : D, τ (τ (τ x)) = 1 := by
    intro x
    simp only [hτ, map_mul, map_inv, hφ3]
    exact Item2119End7Proof.cube_comm h3 (φ x) (φ (φ x)) x
  have hτG : ∀ x : D, ((τ x : D) : G) = b * x * b⁻¹ * (x : G)⁻¹ := by
    intro x
    have h1 : ((x : G))⁻¹ * (φ x : G) = (φ x : G) * ((x : G))⁻¹ :=
      hDc _ (D.inv_mem x.2) _ (φ x).2
    rw [hφ] at h1
    show ((x : G))⁻¹ * (b * x * b⁻¹) = b * x * b⁻¹ * (x : G)⁻¹
    rw [h1]
  have hequiv : ∀ m ∈ Y, ∀ y ∈ D,
      m * (b * y * b⁻¹ * y⁻¹) * m⁻¹ = b * (m * y * m⁻¹) * b⁻¹ * (m * y * m⁻¹)⁻¹ := by
    intro m hm y hy
    obtain ⟨h, hh, hmb⟩ := hconj m hm
    have hy' : m * y * m⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hYD hm) y).mp hy
    have hhy : h * (m * y * m⁻¹) = (m * y * m⁻¹) * h := hDc h (hHD hh) _ hy'
    calc m * (b * y * b⁻¹ * y⁻¹) * m⁻¹
        = (m * b * m⁻¹) * (m * y * m⁻¹) * (m * b * m⁻¹)⁻¹ * (m * y * m⁻¹)⁻¹ := by group
      _ = (b * h) * (m * y * m⁻¹) * (b * h)⁻¹ * (m * y * m⁻¹)⁻¹ := by rw [hmb]
      _ = b * (h * (m * y * m⁻¹)) * h⁻¹ * b⁻¹ * (m * y * m⁻¹)⁻¹ := by group
      _ = b * ((m * y * m⁻¹) * h) * h⁻¹ * b⁻¹ * (m * y * m⁻¹)⁻¹ := by rw [hhy]
      _ = b * (m * y * m⁻¹) * b⁻¹ * (m * y * m⁻¹)⁻¹ := by group
  have hker : ∀ x : D, τ x = 1 ↔ (x : G) ∈ H := by
    intro x
    rw [hHC]
    constructor
    · intro h
      have h1 : b * x * b⁻¹ * (x : G)⁻¹ = 1 := by rw [← hτG, h]; rfl
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (x : G) * b = (b * x * b⁻¹ * (x : G)⁻¹)⁻¹ * b * x := by group
        _ = b * x := by rw [h1]; group
    · intro h
      apply Subtype.ext
      rw [hτG]
      have h1 : (x : G) * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp h.2
      calc b * x * b⁻¹ * (x : G)⁻¹ = (x * b) * b⁻¹ * (x : G)⁻¹ := by rw [h1]
        _ = 1 := by group
  have hkercard : Nat.card τ.ker = 9 := by
    rw [← hH9]
    refine Nat.card_congr (Equiv.ofBijective (fun k => (⟨(k : D), (hker k).mp k.2⟩ : H))
      ⟨?_, ?_⟩)
    · intro k₁ k₂ h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : G)) h))
    · intro h
      refine ⟨⟨⟨h, hHD h.2⟩, (hker _).mpr h.2⟩, rfl⟩
  have hrange : Nat.card τ.range = 9 := by
    have h := Item2119End6Proof.card_eq_card_ker_mul_card_range τ
    rw [hD81, hkercard] at h
    omega
  have hττ : ∀ x : D, τ (τ x) = 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x₀, hx₀⟩ := hall
    set R₂ := (τ.comp τ).range with hR₂
    have hR₂ker : R₂ ≤ τ.ker := by
      rintro _ ⟨y, rfl⟩
      exact hτ3 y
    have hR₂range : R₂ ≤ τ.range := by
      rintro _ ⟨y, rfl⟩
      exact ⟨τ y, rfl⟩
    have hne : R₂ ≠ τ.ker := by
      intro h
      have hle : τ.ker ≤ τ.range := h ▸ hR₂range
      have heq : τ.ker = τ.range :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hkercard, hrange])
      apply hx₀
      have : τ x₀ ∈ τ.ker := heq ▸ ⟨x₀, rfl⟩
      exact this
    obtain ⟨w, hwK, hwR⟩ : ∃ w ∈ τ.ker, w ∉ R₂ := by
      by_contra h
      push Not at h
      exact hne (le_antisymm hR₂ker h)
    have hvR : τ (τ x₀) ∈ R₂ := ⟨x₀, rfl⟩
    have hvH : ((τ (τ x₀) : D) : G) ∈ H := (hker _).mp (hR₂ker hvR)
    have hwH : ((w : D) : G) ∈ H := (hker _).mp hwK
    have hv1 : ((τ (τ x₀) : D) : G) ≠ 1 := fun h => hx₀ (Subtype.ext h)
    have hw1 : ((w : D) : G) ≠ 1 := fun h => hwR (by
      have : w = 1 := Subtype.ext h
      rw [this]
      exact R₂.one_mem)
    obtain ⟨m, hmY, hmvw⟩ := htrans _ hvH _ hwH hv1 hw1
    have hmx : m * x₀ * m⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hYD hmY) _).mp x₀.2
    set x₁ : D := ⟨m * x₀ * m⁻¹, hmx⟩ with hx₁
    have hτ1 : ((τ x₁ : D) : G) = m * (τ x₀ : G) * m⁻¹ := by
      rw [hτG, hτG, hequiv m hmY _ x₀.2]
    have hτ1D : m * (τ x₀ : G) * m⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hYD hmY) _).mp (τ x₀).2
    have hτ2 : ((τ (τ x₁) : D) : G) = m * (τ (τ x₀) : G) * m⁻¹ := by
      have e1 : τ x₁ = ⟨m * (τ x₀ : G) * m⁻¹, hτ1D⟩ := Subtype.ext hτ1
      rw [e1, hτG, hτG (τ x₀), hequiv m hmY _ (τ x₀).2]
    apply hwR
    have : w = τ (τ x₁) := by
      apply Subtype.ext
      rw [hτ2, hmvw]
    rw [this]
    exact ⟨x₁, rfl⟩
  intro x hx
  have h1 := hττ ⟨x, hx⟩
  have h2 : ((τ (τ ⟨x, hx⟩) : D) : G) = 1 := by rw [h1]; rfl
  rw [hτG (τ ⟨x, hx⟩), hτG ⟨x, hx⟩] at h2
  set u := b * x * b⁻¹ * x⁻¹ with hu
  calc b * u = (b * u * b⁻¹ * u⁻¹) * u * b := by group
    _ = u * b := by rw [h2, one_mul]

end Item2119End8Proof

end CFSG.RankThree.PartTwo.Sec21
