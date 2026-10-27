module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ExtraspecialCriterion
public import CFSG.Quasithin.H13.AS91Sec8Prod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1G43_isElemAbelianOfRank_of_card {V : Type*} [Group V] [Finite V]
    (hc : ∀ x y : V, x * y = y * x) (hsq : ∀ x : V, x * x = 1) {n : ℕ}
    (hcard : Nat.card V = 2 ^ n) : CFSG.Quasithin.IsElemAbelianOfRank 2 n V := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) = Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive V)
  have hd : Module.finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hcard' : Nat.card (Additive V) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

theorem s16c1G43_extraspecial {K U B N : Subgroup G} (hUK : U ≤ K) (hBK : B ≤ K)
    (hKUB : ∀ k ∈ K, ∃ u ∈ U, ∃ b ∈ B, k = u * b)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUsq : ∀ x ∈ U, x * x = 1)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBsq : ∀ x ∈ B, x * x = 1)
    (hN : N = U ⊓ B) (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hNcent : ∀ n ∈ N, ∀ k ∈ K, k * n = n * k)
    (hUZ : ∀ u ∈ U, (∀ b ∈ B, b * u = u * b) → u ∈ B)
    (hBZ : ∀ b ∈ B, (∀ u ∈ U, u * b = b * u) → b ∈ U)
    (hU : Nat.card ↥U = 32) (hB : Nat.card ↥B = 32) (hNc : Nat.card ↥N = 2) :
    IsExtraspecialPlus2 ↥K 4 := by
  have hNU : N ≤ U := by rw [hN]; exact inf_le_left
  have hNB : N ≤ B := by rw [hN]; exact inf_le_right
  have hNK : N ≤ K := hNU.trans hUK
  have hUB : (U : Set G) * (B : Set G) = (K : Set G) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨u, hu, b, hb, rfl⟩ := hx
      exact K.mul_mem (hUK hu) (hBK hb)
    · intro hx
      rw [Set.mem_mul]
      obtain ⟨u, hu, b, hb, hxub⟩ := hKUB x (by simpa using hx)
      exact ⟨u, hu, b, hb, hxub.symm⟩
  have hcardK : Nat.card ↥K = 512 := by
    have h := CFSG.Quasithin.H13.AS91.card_mul_set_mul_card_inf U B
    rw [hUB, ← hN, hNc, hU, hB] at h
    have h' : Nat.card ↥K * 2 = 1024 := by simpa using h
    omega
  have hcardKpow : Nat.card ↥K = 2 ^ (2 * 4 + 1) := by
    rw [hcardK]; norm_num
  have hcenter_eq : center ↥K = N.subgroupOf K := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨u, hu, b, hb, hzub⟩ := hKUB (z : G) z.2
      have hzu : (z : G) * b⁻¹ = u := by rw [hzub]; group
      have hbu : u⁻¹ * (z : G) = b := by rw [hzub]; group
      have huB : u ∈ B := by
        apply hUZ u hu
        intro b' hb'
        have hb'z : b' * (z : G) = (z : G) * b' := by
          have hmem := (Subgroup.mem_center_iff.mp hz) ⟨b', hBK hb'⟩
          simpa using congrArg Subtype.val hmem
        have hb'b : b' * b⁻¹ = b⁻¹ * b' := hBab b' hb' b⁻¹ (B.inv_mem hb)
        calc b' * u = b' * ((z : G) * b⁻¹) := by rw [hzu]
          _ = (b' * (z : G)) * b⁻¹ := by group
          _ = ((z : G) * b') * b⁻¹ := by rw [hb'z]
          _ = (z : G) * (b' * b⁻¹) := by group
          _ = (z : G) * (b⁻¹ * b') := by rw [hb'b]
          _ = ((z : G) * b⁻¹) * b' := by group
          _ = u * b' := by rw [hzu]
      have hbU : b ∈ U := by
        apply hBZ b hb
        intro u' hu'
        have hu'z : u' * (z : G) = (z : G) * u' := by
          have hmem := (Subgroup.mem_center_iff.mp hz) ⟨u', hUK hu'⟩
          simpa using congrArg Subtype.val hmem
        have hu'u : u' * u⁻¹ = u⁻¹ * u' := hUab u' hu' u⁻¹ (U.inv_mem hu)
        calc u' * b = u' * (u⁻¹ * (z : G)) := by rw [hbu]
          _ = (u' * u⁻¹) * (z : G) := by group
          _ = (u⁻¹ * u') * (z : G) := by rw [hu'u]
          _ = u⁻¹ * (u' * (z : G)) := by group
          _ = u⁻¹ * ((z : G) * u') := by rw [hu'z]
          _ = (u⁻¹ * (z : G)) * u' := by group
          _ = b * u' := by rw [hbu]
      have huN : u ∈ N := by rw [hN]; exact Subgroup.mem_inf.mpr ⟨hu, huB⟩
      have hbN : b ∈ N := by rw [hN]; exact Subgroup.mem_inf.mpr ⟨hbU, hb⟩
      rw [hzub]
      exact N.mul_mem huN hbN
    · intro n hn
      rw [Subgroup.mem_subgroupOf] at hn
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hNcent (n : G) hn (g : G) g.2
  have hZ : Nat.card (center ↥K) = 2 := by
    rw [hcenter_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv, hNc]
  have hcomm : ∀ x y : ↥K, x * y * x⁻¹ * y⁻¹ ∈ center ↥K := by
    intro x y
    rw [hcenter_eq, Subgroup.mem_subgroupOf]
    have h := hKcomm (x : G) x.2 (y : G) y.2
    rwa [commutatorElement_def] at h
  have hsq : ∀ x : ↥K, x ^ 2 ∈ center ↥K := by
    intro x
    obtain ⟨u, hu, b, hb, hxub⟩ := hKUB (x : G) x.2
    have hcN : ⁅b⁻¹, u⁻¹⁆ ∈ N :=
      hKcomm b⁻¹ (K.inv_mem (hBK hb)) u⁻¹ (K.inv_mem (hUK hu))
    have hc_eq : ⁅b⁻¹, u⁻¹⁆ = b⁻¹ * u⁻¹ * b * u := by
      rw [commutatorElement_def]; group
    have hbu_c : b * u = u * b * ⁅b⁻¹, u⁻¹⁆ := by
      rw [hc_eq]; group
    have hbc : b * ⁅b⁻¹, u⁻¹⁆ = ⁅b⁻¹, u⁻¹⁆ * b :=
      hNcent (⁅b⁻¹, u⁻¹⁆) hcN b (hBK hb)
    have hx2 : (x : G) ^ 2 = ⁅b⁻¹, u⁻¹⁆ := by
      rw [hxub, pow_two]
      calc u * b * (u * b) = u * (b * u) * b := by group
        _ = u * (u * b * ⁅b⁻¹, u⁻¹⁆) * b := by rw [hbu_c]
        _ = (u * u) * b * ⁅b⁻¹, u⁻¹⁆ * b := by group
        _ = b * ⁅b⁻¹, u⁻¹⁆ * b := by rw [hUsq u hu, one_mul]
        _ = ⁅b⁻¹, u⁻¹⁆ * (b * b) := by rw [hbc]; group
        _ = ⁅b⁻¹, u⁻¹⁆ := by rw [hBsq b hb, mul_one]
    rw [hcenter_eq, Subgroup.mem_subgroupOf]
    have hco : ((x ^ 2 : ↥K) : G) = (x : G) ^ 2 := rfl
    rw [hco, hx2]
    exact hcN
  have hnt : ∃ x : ↥K, x ∉ center ↥K := by
    by_contra h
    rw [not_exists] at h
    have htop : center ↥K = ⊤ := by
      ext x
      exact ⟨fun _ => trivial, fun _ => by simpa using h x⟩
    have hcardeq : Nat.card ↥(center ↥K) = Nat.card ↥K := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    omega
  have hisExt : CFSG.IsExtraspecial 2 ↥K :=
    CFSG.EvenSporadicStandard.HNRecog.Harada.isExtraspecial_two_of_sq_comm_mem_center
      (P := ↥K) hZ hsq hcomm hnt
  refine ⟨hisExt, hcardKpow, ?_⟩
  refine ⟨U.subgroupOf K, ?_⟩
  have hUab' : ∀ x y : ↥U, x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact hUab (x : G) x.2 (y : G) y.2
  have hUsq' : ∀ x : ↥U, x * x = 1 := by
    intro x
    apply Subtype.ext
    exact hUsq (x : G) x.2
  have hUcard : Nat.card ↥U = 2 ^ (4 + 1) := by rw [hU]; norm_num
  obtain ⟨e⟩ := s16c1G43_isElemAbelianOfRank_of_card hUab' hUsq' (n := 4 + 1) hUcard
  exact ⟨(Subgroup.subgroupOfEquivOfLe hUK).trans e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
