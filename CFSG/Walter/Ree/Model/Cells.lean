module

public import CFSG.LieType.Ree.SmallReeBorelCosetAction
public import CFSG.LieType.Ree.ReeGenericPerfect

public noncomputable section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open scoped Pointwise

abbrev smallReeU
    (a : ℕ) (K : Type) [Field K] (t b c : K) : ModGL ReeTag.G2.tag K :=
  smallReeCoord a K t b c

abbrev smallReeH
    (a : ℕ) (K : Type) [Field K] (s : Kˣ) : ModGL ReeTag.G2.tag K :=
  smallReeTorusElt a K s

@[expose] def smallReeMidX
    (a : ℕ) (K : Type) [Field K] : Set (ModGL ReeTag.G2.tag K) :=
  Set.range fun b : K => smallReeU a K 0 b 0

@[expose] def smallReeInvCentralizer
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] : Subgroup (ModGL ReeTag.G2.tag K) :=
  ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {smallReeH a K (-1)}

section Field

variable {K : Type} [Field K] {a : ℕ}

theorem smallReeH_mul
    (s s' : Kˣ) : smallReeH a K (s * s') = smallReeH a K s * smallReeH a K s' :=
  smallReeTorusElt_mul s s'

theorem smallReeH_one :
    smallReeH a K 1 = 1 :=
  smallReeTorusElt_one

theorem smallReeH_inv
    (s : Kˣ) : (smallReeH a K s)⁻¹ = smallReeH a K s⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← smallReeH_mul, mul_inv_cancel, smallReeH_one])

theorem smallReeH_neg_one_mul_self :
    smallReeH a K (-1) * smallReeH a K (-1) = 1 := by
  rw [← smallReeH_mul, neg_one_mul, neg_neg, smallReeH_one]

theorem smallReeH_neg_one_inv :
    (smallReeH a K (-1))⁻¹ = smallReeH a K (-1) :=
  inv_eq_of_mul_eq_one_right smallReeH_neg_one_mul_self

theorem smallReeH_mem_torusGroup
    (s : Kˣ) : smallReeH a K s ∈ torusGroup ReeTag.G2.tag K :=
  mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem smallReeH_injective :
    Function.Injective (smallReeH a K) :=
  smallReeTorusElt_injective

theorem smallReeU_inj
    {t b c t' b' c' : K} (h : smallReeU a K t b c = smallReeU a K t' b' c') :
    t = t' ∧ b = b' ∧ c = c' := by
  have h' : smallReeCoord a K t b c = smallReeCoord a K t' b' c' := h
  rw [smallReeCoord_eq_smallReeP, smallReeCoord_eq_smallReeP] at h'
  obtain ⟨h0, -, h2, h3, -⟩ := smallReeP_injective h'
  exact ⟨h0, h2, h3⟩

end Field

section Main

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

theorem smallReeH_mem
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (s : Kˣ) :
    smallReeH a K s ∈ G2.reeFixedTorus K a :=
  smallReeTorusElt_mem hK s

theorem exists_smallReeH_eq
    {g : ModGL G2.tag K} (hg : g ∈ G2.reeFixedTorus K a) :
    ∃ s : Kˣ, smallReeH a K s = g :=
  exists_smallReeTorusElt_eq hg

theorem smallReeU_mem
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (v b c : K) :
    smallReeU a K v b c ∈ G2.reeFixedPosUnipotent K a := by
  have h := (bijOn_smallReeCoord (a := a) hK).1 (Set.mem_univ (v, b, c))
  exact h

theorem exists_smallReeU_eq
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {u : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a) : ∃ v b c : K, smallReeU a K v b c = u := by
  obtain ⟨⟨v, b, c⟩, -, h⟩ := (bijOn_smallReeCoord (a := a) hK).2.2 (SetLike.mem_coe.2 hu)
  exact ⟨v, b, c, h⟩

theorem smallReeH_neg_one_conj
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (v b c : K) :
    smallReeH a K (-1) * smallReeU a K v b c * (smallReeH a K (-1))⁻¹ =
      smallReeU a K (-v) b (-c) := by
  have hθ : Odd (3 ^ a) := Odd.pow ⟨1, rfl⟩
  have h1 : ((-1 : Kˣ) ^ (2 * 3 ^ a - 1) : Kˣ) = -1 := Odd.neg_one_pow (by
    obtain ⟨k, hk⟩ := hθ
    exact ⟨2 * k, by omega⟩)
  have h2 : ((-1 : Kˣ) ^ (1 - (3 ^ a : ℤ)) : Kˣ) = 1 :=
    Even.neg_one_zpow (Odd.sub_odd odd_one (Odd.pow ⟨1, by norm_num⟩))
  have h3 : ((-1 : Kˣ) : K) ^ 3 ^ a = -1 := by
    rw [Units.val_neg, Units.val_one]
    exact hθ.neg_one_pow
  have h := smallReeTorusElt_conj_smallReeCoord hK (-1) v b c
  rw [h1, h2, h3] at h
  simp only [Units.val_neg, Units.val_one, neg_one_mul, one_mul] at h
  exact h

theorem smallReeU_commute_iff
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (v b c : K) :
    smallReeU a K v b c * smallReeH a K (-1) = smallReeH a K (-1) * smallReeU a K v b c ↔
      v = 0 ∧ c = 0 := by
  have h3 := smallRee_three_eq_zero (K := K)
  have e : smallReeU a K v b c * smallReeH a K (-1) = smallReeH a K (-1) * smallReeU a K v b c ↔
      smallReeH a K (-1) * smallReeU a K v b c * (smallReeH a K (-1))⁻¹ = smallReeU a K v b c :=
    ⟨fun h => by rw [← h, mul_inv_cancel_right], fun h => by
      calc smallReeU a K v b c * smallReeH a K (-1) =
            smallReeH a K (-1) * smallReeU a K v b c * (smallReeH a K (-1))⁻¹ *
              smallReeH a K (-1) := by rw [h]
        _ = _ := by group⟩
  rw [e, smallReeH_neg_one_conj hK]
  constructor
  · intro h
    obtain ⟨hv, -, hc⟩ := smallReeU_inj h
    exact ⟨by linear_combination hv + v * h3, by linear_combination hc + c * h3⟩
  · rintro ⟨rfl, rfl⟩
    rw [neg_zero]

theorem coe_reeFixedPosUnipotent_inf_centralizer
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ((G2.reeFixedPosUnipotent K a ⊓ Subgroup.centralizer {smallReeH a K (-1)} :
        Subgroup (ModGL G2.tag K)) : Set (ModGL G2.tag K)) = smallReeMidX a K := by
  ext g
  rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hgU, hg⟩
    obtain ⟨v, b, c, rfl⟩ := exists_smallReeU_eq hK hgU
    obtain ⟨rfl, rfl⟩ := (smallReeU_commute_iff hK v b c).1 hg
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨smallReeU_mem hK 0 b 0, (smallReeU_commute_iff hK 0 b 0).2 ⟨rfl, rfl⟩⟩

theorem smallReeMidX_subset
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    smallReeMidX a K ⊆ (G2.reeFixedPosUnipotent K a : Set (ModGL G2.tag K)) := by
  rw [← coe_reeFixedPosUnipotent_inf_centralizer hK]
  exact fun g hg => (Subgroup.mem_inf.1 hg).1

theorem smallReeH_commute_of_mem
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {h : ModGL G2.tag K}
    (hh : h ∈ G2.reeFixedTorus K a) : smallReeH a K (-1) * h = h * smallReeH a K (-1) :=
  reeFixedTorus_mul_comm (smallReeH_mem hK (-1)) hh

theorem smallReeH_conj_mem
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {u : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a) :
    smallReeH a K (-1) * u * (smallReeH a K (-1))⁻¹ ∈ G2.reeFixedPosUnipotent K a :=
  (Subgroup.mem_normalizer_iff.1
    (reeFixedTorus_le_normalizer_reeFixedPosUnipotent (smallReeH_mem hK (-1))) u).1 hu

theorem mem_smallReeMidX_of_conj_eq
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {u : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a)
    (h : smallReeH a K (-1) * u * (smallReeH a K (-1))⁻¹ = u) : u ∈ smallReeMidX a K := by
  rw [← coe_reeFixedPosUnipotent_inf_centralizer hK]
  refine Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc u * smallReeH a K (-1) =
        smallReeH a K (-1) * u * (smallReeH a K (-1))⁻¹ * smallReeH a K (-1) := by rw [h]
    _ = _ := by group

theorem smallReeH_conj_mul
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {u h : ModGL G2.tag K}
    (hh : h ∈ G2.reeFixedTorus K a) :
    smallReeH a K (-1) * (u * h) * (smallReeH a K (-1))⁻¹ =
      (smallReeH a K (-1) * u * (smallReeH a K (-1))⁻¹) * h := by
  have hth : smallReeH a K (-1) * h * (smallReeH a K (-1))⁻¹ = h := by
    rw [smallReeH_commute_of_mem hK hh, mul_inv_cancel_right]
  calc smallReeH a K (-1) * (u * h) * (smallReeH a K (-1))⁻¹ =
        (smallReeH a K (-1) * u * (smallReeH a K (-1))⁻¹) *
          (smallReeH a K (-1) * h * (smallReeH a K (-1))⁻¹) := by group
    _ = _ := by rw [hth]

theorem mem_smallReeInvCentralizer_of_mem_smallReeMidX
    (hK : Nat.card K = 3 ^ (2 * a + 1))
    {u : ModGL G2.tag K} (hu : u ∈ smallReeMidX a K) : u ∈ smallReeInvCentralizer a K := by
  rw [← coe_reeFixedPosUnipotent_inf_centralizer hK] at hu
  obtain ⟨hU, hC⟩ := Subgroup.mem_inf.1 hu
  exact Subgroup.mem_inf.2 ⟨reeFixedPosUnipotent_le_reeGamma hU, hC⟩

theorem smallReeH_mem_smallReeInvCentralizer
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (s : Kˣ) :
    smallReeH a K s ∈ smallReeInvCentralizer a K :=
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (smallReeH_mem hK s)).2,
    Subgroup.mem_centralizer_singleton_iff.2
      ((smallReeH_commute_of_mem hK (smallReeH_mem hK s)).symm)⟩

theorem mem_smallReeInvCentralizer_of_mem_reeFixedTorus
    (hK : Nat.card K = 3 ^ (2 * a + 1))
    {h : ModGL G2.tag K} (hh : h ∈ G2.reeFixedTorus K a) : h ∈ smallReeInvCentralizer a K := by
  obtain ⟨s, rfl⟩ := exists_smallReeH_eq hh
  exact smallReeH_mem_smallReeInvCentralizer hK s

variable {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
include hw₀

omit [CharP K G2.prime] in
theorem canonicalRep_conj_smallReeH
    (s : Kˣ) :
    canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeH a K s *
        (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ = smallReeH a K s⁻¹ := by
  rw [canonicalRep_longest_conj_torus hw₀ (smallReeH_mem_torusGroup s), smallReeH_inv]

omit [CharP K G2.prime] in
theorem canonicalRep_commute_smallReeH :
    canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeH a K (-1) =
      smallReeH a K (-1) * canonicalRep (coxeterSystem G2.tag) K w₀ := by
  have h := canonicalRep_conj_smallReeH (K := K) (a := a) hw₀ (-1)
  rw [inv_neg_one] at h
  calc canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeH a K (-1) =
        canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeH a K (-1) *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ * canonicalRep (coxeterSystem G2.tag) K w₀ :=
        by group
    _ = _ := by rw [h]

omit [CharP K G2.prime] in
theorem canonicalRep_inv_conj
    {x : ModGL G2.tag K} (hx : x ∈ torusGroup G2.tag K) :
    (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ * x * canonicalRep (coxeterSystem G2.tag) K w₀ =
      x⁻¹ := by
  have h := canonicalRep_longest_conj_torus hw₀ (inv_mem hx)
  rw [inv_inv] at h
  calc (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ * x * canonicalRep (coxeterSystem G2.tag) K w₀ =
        (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ * (canonicalRep (coxeterSystem G2.tag) K w₀ *
          x⁻¹ * (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) *
            canonicalRep (coxeterSystem G2.tag) K w₀ := by rw [h]
    _ = x⁻¹ := by group

theorem reeGamma_G2_cases
    {g : ModGL G2.tag K} (hg : g ∈ G2.reeGamma K a) :
    (∃ u ∈ G2.reeFixedPosUnipotent K a, ∃ h ∈ G2.reeFixedTorus K a, u * h = g) ∨
      (g ∉ G2.reeFixedBorel K a ∧ ∃ u ∈ G2.reeFixedPosUnipotent K a,
        ∃ h ∈ G2.reeFixedTorus K a, ∃ v ∈ G2.reeFixedPosUnipotent K a,
          u * h * canonicalRep (coxeterSystem G2.tag) K w₀ * v = g) := by
  by_cases hgB : g ∈ G2.reeFixedBorel K a
  · left
    have hg' : g ∈ (G2.reeFixedPosUnipotent K a : Set (ModGL G2.tag K)) *
        (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) := by
      rw [← reeFixedBorel_eq_mul']
      exact hgB
    obtain ⟨u, hu, h, hh, rfl⟩ := hg'
    exact ⟨u, hu, h, hh, rfl⟩
  · right
    refine ⟨hgB, ?_⟩
    set n := canonicalRep (coxeterSystem G2.tag) K w₀
    obtain ⟨u, hu, hub⟩ := exists_reeFixedPosUnipotent_mul_canonicalRep hw₀ hg hgB
    have hb : (u * n)⁻¹ * g ∈ (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) *
        (G2.reeFixedPosUnipotent K a : Set (ModGL G2.tag K)) := by
      rw [← reeFixedBorel_eq_mul]
      exact hub
    obtain ⟨h, hh, v, hv, hhv⟩ := hb
    refine ⟨u, hu, h⁻¹, inv_mem hh, v, hv, ?_⟩
    have hnh : n * h * n⁻¹ = h⁻¹ := canonicalRep_longest_conj_torus hw₀ (Subgroup.mem_inf.1 hh).1
    have hhv' : h * v = (u * n)⁻¹ * g := hhv
    calc u * h⁻¹ * n * v = u * (n * h * n⁻¹) * n * v := by rw [hnh]
      _ = (u * n) * (h * v) := by group
      _ = g := by rw [hhv', mul_inv_cancel_left]

theorem eq_of_mul_canonicalRep_mul_eq
    {u u' h h' v v' : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a) (hu' : u' ∈ G2.reeFixedPosUnipotent K a)
    (hh : h ∈ G2.reeFixedTorus K a) (hh' : h' ∈ G2.reeFixedTorus K a)
    (hv : v ∈ G2.reeFixedPosUnipotent K a) (hv' : v' ∈ G2.reeFixedPosUnipotent K a)
    (heq : u * h * canonicalRep (coxeterSystem G2.tag) K w₀ * v =
      u' * h' * canonicalRep (coxeterSystem G2.tag) K w₀ * v') : u = u' ∧ h = h' ∧ v = v' := by
  set n := canonicalRep (coxeterSystem G2.tag) K w₀ with hn
  have hUB := fun {x : ModGL G2.tag K} (hx : x ∈ G2.reeFixedPosUnipotent K a) =>
    reeFixedPosUnipotent_le_reeFixedBorel (t := G2) (K := K) (a := a) hx
  have hHB := fun {x : ModGL G2.tag K} (hx : x ∈ G2.reeFixedTorus K a) =>
    reeFixedTorus_le_reeFixedBorel (t := G2) (K := K) (a := a) hx
  have hx : n * (v * v'⁻¹) * n⁻¹ ∈ G2.reeFixedTorus K a := by
    rw [← reeFixedBorel_inf_map_conj (K := K) (a := a) hw₀]
    refine Subgroup.mem_inf.2 ⟨?_, ⟨v * v'⁻¹, mul_mem (hUB hv) (inv_mem (hUB hv')), rfl⟩⟩
    have e : n * (v * v'⁻¹) * n⁻¹ = (u * h)⁻¹ * (u' * h') := by
      calc n * (v * v'⁻¹) * n⁻¹ = (u * h)⁻¹ * (u * h * n * v) * v'⁻¹ * n⁻¹ := by group
        _ = (u * h)⁻¹ * (u' * h' * n * v') * v'⁻¹ * n⁻¹ := by rw [heq]
        _ = (u * h)⁻¹ * (u' * h') := by group
    rw [e]
    exact mul_mem (inv_mem (mul_mem (hUB hu) (hHB hh))) (mul_mem (hUB hu') (hHB hh'))
  have hy : v * v'⁻¹ = (n * (v * v'⁻¹) * n⁻¹)⁻¹ := by
    rw [← canonicalRep_inv_conj hw₀ (Subgroup.mem_inf.1 hx).1, ← hn]
    group
  have hy1 : v * v'⁻¹ = 1 := eq_one_of_mem_reeFixedPosUnipotent_of_mem_reeFixedTorus
    (mul_mem hv (inv_mem hv')) (by rw [hy]; exact inv_mem hx)
  have hvv : v = v' := mul_inv_eq_one.1 hy1
  subst hvv
  have huh : u * h = u' * h' := by
    have h1 := congrArg (fun x => x * v⁻¹ * n⁻¹) heq
    simpa only [mul_inv_cancel_right] using h1
  obtain ⟨e1, e2⟩ := reeFixed_mul_unique' hh hh' hu hu' huh
  exact ⟨e1, e2, rfl⟩

theorem smallReeH_conj_bigCell
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {u h v : ModGL G2.tag K}
    (hh : h ∈ G2.reeFixedTorus K a) :
    smallReeH a K (-1) * (u * h * canonicalRep (coxeterSystem G2.tag) K w₀ * v) *
        (smallReeH a K (-1))⁻¹ =
      (smallReeH a K (-1) * u * (smallReeH a K (-1))⁻¹) * h *
        canonicalRep (coxeterSystem G2.tag) K w₀ *
        (smallReeH a K (-1) * v * (smallReeH a K (-1))⁻¹) := by
  set t := smallReeH a K (-1)
  set n := canonicalRep (coxeterSystem G2.tag) K w₀
  have hth : t * h * t⁻¹ = h := by
    rw [smallReeH_commute_of_mem hK hh, mul_inv_cancel_right]
  have htn : t * n * t⁻¹ = n := by
    rw [← canonicalRep_commute_smallReeH hw₀, mul_inv_cancel_right]
  calc t * (u * h * n * v) * t⁻¹ =
        (t * u * t⁻¹) * (t * h * t⁻¹) * (t * n * t⁻¹) * (t * v * t⁻¹) := by group
    _ = _ := by rw [hth, htn]

theorem canonicalRep_mem_smallReeInvCentralizer :
    canonicalRep (coxeterSystem G2.tag) K w₀ ∈ smallReeInvCentralizer a K :=
  Subgroup.mem_inf.2 ⟨canonicalRep_longest_mem_reeGamma hw₀,
    Subgroup.mem_centralizer_singleton_iff.2 (canonicalRep_commute_smallReeH hw₀)⟩

theorem coe_smallReeInvCentralizer
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (smallReeInvCentralizer a K : Set (ModGL G2.tag K)) =
      smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) ∪
        smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) *
          {canonicalRep (coxeterSystem G2.tag) K w₀} * smallReeMidX a K := by
  set n := canonicalRep (coxeterSystem G2.tag) K w₀
  ext g
  constructor
  · intro hg
    obtain ⟨hgΓ, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgt := Subgroup.mem_centralizer_singleton_iff.1 hgC
    have hfix : smallReeH a K (-1) * g * (smallReeH a K (-1))⁻¹ = g := by
      rw [← hgt, mul_inv_cancel_right]
    rcases reeGamma_G2_cases hw₀ hgΓ with ⟨u, hu, h, hh, rfl⟩ | ⟨-, u, hu, h, hh, v, hv, rfl⟩
    · left
      rw [smallReeH_conj_mul hK hh] at hfix
      exact ⟨u, mem_smallReeMidX_of_conj_eq hK hu (mul_right_cancel hfix), h, hh, rfl⟩
    · right
      rw [smallReeH_conj_bigCell hw₀ hK hh] at hfix
      obtain ⟨e1, -, e3⟩ := eq_of_mul_canonicalRep_mul_eq hw₀ (smallReeH_conj_mem hK hu)
        hu hh hh (smallReeH_conj_mem hK hv) hv hfix
      exact ⟨u * h * n, ⟨u * h, ⟨u, mem_smallReeMidX_of_conj_eq hK hu e1, h, hh, rfl⟩, n, rfl,
        rfl⟩, v, mem_smallReeMidX_of_conj_eq hK hv e3, rfl⟩
  · rintro (⟨u, hu, h, hh, rfl⟩ | ⟨_, ⟨_, ⟨u, hu, h, hh, rfl⟩, _, rfl, rfl⟩, v, hv, rfl⟩)
    · exact mul_mem (mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hu)
        (mem_smallReeInvCentralizer_of_mem_reeFixedTorus hK hh)
    · exact mul_mem (mul_mem (mul_mem (mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hu)
        (mem_smallReeInvCentralizer_of_mem_reeFixedTorus hK hh))
        (canonicalRep_mem_smallReeInvCentralizer hw₀))
        (mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hv)

theorem disjoint_smallReeCells
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Disjoint (smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)))
      (smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) *
        {canonicalRep (coxeterSystem G2.tag) K w₀} * smallReeMidX a K) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu, h, hh, rfl⟩ ⟨_, ⟨_, ⟨u', hu', h', hh', rfl⟩, _, rfl, rfl⟩, v, hv, hx⟩
  dsimp only at hx
  have hUB := fun {x : ModGL G2.tag K} (hx : x ∈ G2.reeFixedPosUnipotent K a) =>
    reeFixedPosUnipotent_le_reeFixedBorel (t := G2) (K := K) (a := a) hx
  have hHB := fun {x : ModGL G2.tag K} (hx : x ∈ G2.reeFixedTorus K a) =>
    reeFixedTorus_le_reeFixedBorel (t := G2) (K := K) (a := a) hx
  apply canonicalRep_longest_not_mem_reeFixedBorel hK hw₀
  have e : canonicalRep (coxeterSystem G2.tag) K w₀ = (u' * h')⁻¹ * (u * h) * v⁻¹ := by
    rw [← hx]
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (mul_mem (hUB (smallReeMidX_subset hK hu'))
    (hHB hh'))) (mul_mem (hUB (smallReeMidX_subset hK hu)) (hHB hh)))
    (inv_mem (hUB (smallReeMidX_subset hK hv)))

omit hw₀ in
theorem bijOn_smallReeCell₁
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × Kˣ => smallReeU a K 0 p.1 0 * smallReeH a K p.2) Set.univ
      (smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K))) := by
  refine ⟨fun p _ => ⟨_, ⟨p.1, rfl⟩, _, smallReeH_mem hK p.2, rfl⟩,
    fun p _ p' _ h => ?_, ?_⟩
  · obtain ⟨e1, e2⟩ := reeFixed_mul_unique' (smallReeH_mem hK p.2) (smallReeH_mem hK p'.2)
      (smallReeU_mem hK 0 p.1 0) (smallReeU_mem hK 0 p'.1 0) h
    exact Prod.ext (smallReeU_inj e1).2.1 (smallReeH_injective e2)
  · rintro _ ⟨_, ⟨b, rfl⟩, h, hh, rfl⟩
    obtain ⟨s, rfl⟩ := exists_smallReeH_eq hh
    exact ⟨(b, s), Set.mem_univ _, rfl⟩

theorem bijOn_smallReeCell₂
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × Kˣ × K => smallReeU a K 0 p.1 0 * smallReeH a K p.2.1 *
        canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeU a K 0 p.2.2 0) Set.univ
      (smallReeMidX a K * (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) *
        {canonicalRep (coxeterSystem G2.tag) K w₀} * smallReeMidX a K) := by
  refine ⟨fun p _ => ⟨_, ⟨_, ⟨_, ⟨p.1, rfl⟩, _, smallReeH_mem hK p.2.1, rfl⟩, _, rfl,
    rfl⟩, _, ⟨p.2.2, rfl⟩, rfl⟩, fun p _ p' _ h => ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := eq_of_mul_canonicalRep_mul_eq hw₀ (smallReeU_mem hK 0 p.1 0)
      (smallReeU_mem hK 0 p'.1 0) (smallReeH_mem hK p.2.1) (smallReeH_mem hK p'.2.1)
      (smallReeU_mem hK 0 p.2.2 0) (smallReeU_mem hK 0 p'.2.2 0) h
    exact Prod.ext (smallReeU_inj e1).2.1
      (Prod.ext (smallReeH_injective e2) (smallReeU_inj e3).2.1)
  · rintro _ ⟨_, ⟨_, ⟨_, ⟨b, rfl⟩, h, hh, rfl⟩, _, rfl, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
    obtain ⟨s, rfl⟩ := exists_smallReeH_eq hh
    exact ⟨(b, s, c), Set.mem_univ _, rfl⟩

theorem card_smallReeInvCentralizer
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (smallReeInvCentralizer a K) = 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) := by
  have h1 := bijOn_smallReeCell₁ (a := a) hK
  have h2 := bijOn_smallReeCell₂ (a := a) hw₀ hK
  have hc1 := h1.injOn.ncard_image
  have hc2 := h2.injOn.ncard_image
  rw [h1.image_eq, Set.ncard_univ] at hc1
  rw [h2.image_eq, Set.ncard_univ] at hc2
  have hf1 := Set.finite_univ.image (fun p : K × Kˣ => smallReeU a K 0 p.1 0 * smallReeH a K p.2)
  have hf2 := Set.finite_univ.image (fun p : K × Kˣ × K => smallReeU a K 0 p.1 0 *
    smallReeH a K p.2.1 * canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeU a K 0 p.2.2 0)
  rw [h1.image_eq] at hf1
  rw [h2.image_eq] at hf2
  have hC : Nat.card (smallReeInvCentralizer a K) =
      (smallReeInvCentralizer a K : Set (ModGL G2.tag K)).ncard := Nat.card_coe_set_eq _
  rw [hC, coe_smallReeInvCentralizer hw₀ hK,
    Set.ncard_union_eq (disjoint_smallReeCells hw₀ hK) hf1 hf2, hc1, hc2]
  simp only [Nat.card_prod, Nat.card_units, hK]
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ (2 * a + 1) = m + 1 :=
    ⟨3 ^ (2 * a + 1) - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm⟩
  rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 by ring, Nat.add_sub_cancel]
  ring

theorem smallReeInvCentralizer_eq_closure
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    smallReeInvCentralizer a K = Subgroup.closure (smallReeMidX a K ∪
      (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) ∪
        {canonicalRep (coxeterSystem G2.tag) K w₀}) := by
  set S := smallReeMidX a K ∪ (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) ∪
    {canonicalRep (coxeterSystem G2.tag) K w₀}
  refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hg' : g ∈ (smallReeInvCentralizer a K : Set (ModGL G2.tag K)) := hg
    rw [coe_smallReeInvCentralizer hw₀ hK] at hg'
    have hX : ∀ x ∈ smallReeMidX a K, x ∈ Subgroup.closure S :=
      fun x hx => Subgroup.subset_closure (Or.inl (Or.inl hx))
    have hH : ∀ x ∈ G2.reeFixedTorus K a, x ∈ Subgroup.closure S :=
      fun x hx => Subgroup.subset_closure (Or.inl (Or.inr hx))
    have hn : canonicalRep (coxeterSystem G2.tag) K w₀ ∈ Subgroup.closure S :=
      Subgroup.subset_closure (Or.inr rfl)
    rcases hg' with ⟨u, hu, h, hh, rfl⟩ | ⟨_, ⟨_, ⟨u, hu, h, hh, rfl⟩, _, rfl, rfl⟩, v, hv, rfl⟩
    · exact mul_mem (hX u hu) (hH h hh)
    · exact mul_mem (mul_mem (mul_mem (hX u hu) (hH h hh)) hn) (hX v hv)
  · rintro x ((hx | hx) | hx)
    · exact mem_smallReeInvCentralizer_of_mem_smallReeMidX hK hx
    · exact mem_smallReeInvCentralizer_of_mem_reeFixedTorus hK hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact canonicalRep_mem_smallReeInvCentralizer hw₀

end Main

theorem small_Ree_torus_involution_centralizer_cells
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (w₀ : WeylGroup ReeTag.G2.tag)
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    ((ReeTag.G2.reeFixedPosUnipotent K a ⊓ Subgroup.centralizer {smallReeH a K (-1)} :
        Subgroup (ModGL ReeTag.G2.tag K)) : Set (ModGL ReeTag.G2.tag K)) = smallReeMidX a K ∧
    (∀ s : Kˣ, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * smallReeH a K s *
        (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹ = smallReeH a K s⁻¹) ∧
    canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ smallReeInvCentralizer a K ∧
    (smallReeInvCentralizer a K : Set (ModGL ReeTag.G2.tag K)) =
      smallReeMidX a K * (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) ∪
        smallReeMidX a K * (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) *
          {canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} * smallReeMidX a K ∧
    Disjoint (smallReeMidX a K * (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)))
      (smallReeMidX a K * (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) *
        {canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} * smallReeMidX a K) ∧
    Set.BijOn (fun p : K × Kˣ => smallReeU a K 0 p.1 0 * smallReeH a K p.2) Set.univ
      (smallReeMidX a K * (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K))) ∧
    Set.BijOn (fun p : K × Kˣ × K => smallReeU a K 0 p.1 0 * smallReeH a K p.2.1 *
        canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * smallReeU a K 0 p.2.2 0) Set.univ
      (smallReeMidX a K * (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) *
        {canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} * smallReeMidX a K) ∧
    Nat.card (smallReeInvCentralizer a K) = 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) ∧
    smallReeInvCentralizer a K = Subgroup.closure (smallReeMidX a K ∪
      (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) ∪
        {canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}) :=
  ⟨coe_reeFixedPosUnipotent_inf_centralizer hK, canonicalRep_conj_smallReeH hw₀,
    canonicalRep_mem_smallReeInvCentralizer hw₀, coe_smallReeInvCentralizer hw₀ hK,
    disjoint_smallReeCells hw₀ hK, bijOn_smallReeCell₁ hK, bijOn_smallReeCell₂ hw₀ hK,
    card_smallReeInvCentralizer hw₀ hK, smallReeInvCentralizer_eq_closure hw₀ hK⟩

end CFSG.Walter.Ree.Model
