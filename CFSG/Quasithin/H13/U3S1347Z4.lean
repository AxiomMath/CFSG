module

public import CFSG.Quasithin.H13.U3S1347Z3
public import CFSG.Quasithin.H13.U3S1347Z

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_chain_two {Q T' : Subgroup G} (hQT : Q ≤ T') (hQ2 : IsPGroup 2 Q)
    (hT4 : Nat.card T' = 4 * Nat.card Q) :
    ∃ T₁ : Subgroup G, Q ≤ T₁ ∧ T₁ ≤ T' ∧ Q.relIndex T₁ = 2 ∧ T₁.relIndex T' = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hQ2.exists_card_eq
  obtain ⟨T₁, h1, hQT₁, hT₁T⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := m + 1) (by rw [hm]; exact pow_dvd_pow 2 (Nat.le_succ m))
    (by rw [hT4, hm]; exact ⟨2, by ring⟩) hQT
  refine ⟨T₁, hQT₁, hT₁T, ?_, ?_⟩
  · have h := relIndex_mul_card Q T₁
    rw [inf_eq_left.2 hQT₁, hm, h1, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos m) (h.trans (mul_comm _ _))
  · have h := relIndex_mul_card T₁ T'
    rw [inf_eq_left.2 hT₁T, h1, hT4, hm, show 4 * 2 ^ m = 2 * 2 ^ (m + 1) by ring] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos (m + 1)) h

theorem s1347_card_V0 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hH₀ : InH T (H₁ ⊔ H₂)) (hc₁ : Nat.card ↥(cZ T H₁) = 2)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)))
    [IsMulCommutative ↥(v0Of T H₁ H₂)] {z : MulAut ↥(v0Of T H₁ H₂)}
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzn : ∀ β ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂), β * z * β⁻¹ = z ∨ β * z * β⁻¹ = z⁻¹)
    (h6k : ∃ k : ℕ, Nat.card ↥(commAutU3 z).range = 2 ^ (6 * k)) :
    Nat.card ↥(v0Of T H₁ H₂) = 2 ^ 6 ∧ fixAutU3 z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hP : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  have hVc : ∀ a ∈ v0Of T H₁ H₂, ∀ b ∈ v0Of T H₁ H₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ a ∈ v0Of T H₁ H₂, a * a = 1 := fun a ha => by
    rw [← sq]
    exact hred.2.2.1.2 a ha
  have hW2 : ∀ w : ↥(v0Of T H₁ H₂), w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have hmemX : ∀ g : ↥(H₁ ⊔ H₂), Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g ∈
      autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := fun g => (Setup.mem_autOn_self_iff hP).2 ⟨g, rfl⟩
  have hinv : ∀ w : ↥(v0Of T H₁ H₂), w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← sq, hW2])
  have hXU : ∀ β ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂), ∀ u ∈ (commAutU3 z).range,
      β u ∈ (commAutU3 z).range := by
    intro β hβ u hu
    obtain ⟨v, rfl⟩ := hu
    rcases hzn β hβ with e | e
    · have e' : β * z = z * β := by
        calc β * z = (β * z * β⁻¹) * β := by group
          _ = z * β := by rw [e]
      refine ⟨β v, ?_⟩
      rw [commAutU3_apply, commAutU3_apply, map_mul, map_inv, ← MulAut.mul_apply _ β z, e',
        MulAut.mul_apply]
    · have e' : β * z = z⁻¹ * β := by
        calc β * z = (β * z * β⁻¹) * β := by group
          _ = z⁻¹ * β := by rw [e]
      have hzz : z (z⁻¹ (β v)) = β v := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      refine ⟨z⁻¹ (β v), ?_⟩
      rw [commAutU3_apply, commAutU3_apply, hzz, map_mul, map_inv, ← MulAut.mul_apply _ β z, e',
        MulAut.mul_apply, hinv, hinv, mul_comm]
  set U := (commAutU3 z).range.map (v0Of T H₁ H₂).subtype with hUdef
  have hUV : U ≤ v0Of T H₁ H₂ := map_subtype_le _
  have hNU : H₁ ⊔ H₂ ≤ normalizer (U : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨g, hg⟩ u, hXU _ (hmemX _) u hu, ?_⟩
      exact Setup.rho_apply_coe hP ⟨g, hg⟩ u
    · rintro ⟨u, hu, hux⟩
      refine ⟨Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨g⁻¹, inv_mem hg⟩ u,
        hXU _ (hmemX _) u hu, ?_⟩
      show g⁻¹ * (u : G) * g⁻¹⁻¹ = x
      have hux' : (u : G) = g * x * g⁻¹ := hux
      rw [hux']
      group
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hVc a (hUV ha) b (hUV hb)
  have hU2 : ∀ a ∈ U, a * a = 1 := fun a ha => hV2 a (hUV ha)
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hO₀T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  obtain ⟨T₁, hQT₁, hT₁T, h21, h22⟩ := exists_chain_two hO₀T (pCoreOf_isPGroup 2 _) hT4
  have hc1 := card_inf_centralizer_le_sq hUc hU2 hQT₁ h21
    ((hT₁T.trans hH₀.1).trans hNU)
  have hc2 := card_inf_centralizer_le_sq hUc hU2 hT₁T h22 (hH₀.1.trans hNU)
  rw [inf_eq_left.2 (hUV.trans (le_centralizer_iff.1 (pCoreOf_le_centralizer_of_reduced' hred)))]
    at hc1
  have hU4 : Nat.card ↥U ≤ Nat.card ↥(U ⊓ centralizer (T : Set G)) ^ 4 := by
    calc Nat.card ↥U ≤ _ := hc1
      _ ≤ (Nat.card ↥(U ⊓ centralizer (T : Set G)) ^ 2) ^ 2 := Nat.pow_le_pow_left hc2 2
      _ = _ := by rw [← pow_mul]
  have hVT : v0Of T H₁ H₂ ≤ T := s1347_V0_le_T S hH₀
  have hCZ : U ⊓ centralizer (T : Set G) ≤ quasithinOmegaOneCenter T :=
    fun x hx => subset_closure ⟨⟨hVT (hUV (mem_inf.1 hx).1), (mem_inf.1 hx).2⟩,
      hred.2.2.1.2 x (hUV (mem_inf.1 hx).1)⟩
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by rw [h.index₁, hc₁]
  obtain ⟨k, hk⟩ := h6k
  have hUk : Nat.card ↥U = 2 ^ (6 * k) := by
    rw [hUdef, card_map_of_injective (v0Of T H₁ H₂).subtype_injective, hk]
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this, mul_zero, pow_zero] at hk
    apply hz1
    refine MulEquiv.ext fun v => ?_
    have h1 : commAutU3 z v = 1 := by
      have := (card_eq_one.1 hk)
      rw [eq_bot_iff] at this
      exact this ⟨v, rfl⟩
    rw [commAutU3_apply, mul_inv_eq_one] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.card ↥(U ⊓ centralizer (T : Set G)) := ⟨_, rfl⟩
  have hc4 : c ∣ 4 := by
    rw [hc, ← hZ4]
    exact card_dvd_of_le hCZ
  have hc64 : 2 ^ 6 ≤ c ^ 4 := by
    have h1 : 2 ^ 6 ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hc]
    exact h1.trans (hUk.symm.le.trans hU4)
  have hc4' : c = 4 := by
    have hcle : c ≤ 4 := Nat.le_of_dvd (by norm_num) hc4
    interval_cases c
    · norm_num at hc64
    · norm_num at hc64
    · norm_num at hc64
    · norm_num at hc4
    · rfl
  have hZU : quasithinOmegaOneCenter T ≤ U := by
    have he : U ⊓ centralizer (T : Set G) = quasithinOmegaOneCenter T :=
      eq_of_le_of_card_ge hCZ (by rw [hZ4, ← hc, hc4'])
    rw [← he]
    exact inf_le_left
  have hVU : v0Of T H₁ H₂ ≤ U := conjClosure_le fun g hg s hs =>
    (mem_normalizer_iff.1 (hNU hg) s).1 (hZU hs)
  have hUtop : (commAutU3 z).range = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, hu, huw⟩ := hVU w.2
    have : u = w := Subtype.ext huw
    rw [← this]
    exact hu
  refine ⟨?_, ?_⟩
  ·
    have hVeq : Nat.card ↥(v0Of T H₁ H₂) = 2 ^ (6 * k) := by
      rw [← hUk, le_antisymm hUV hVU]
    have h8 : 2 ^ (6 * k) ≤ 2 ^ 8 := by
      have := hU4
      rw [hUk, ← hc, hc4'] at this
      calc 2 ^ (6 * k) ≤ 4 ^ 4 := this
        _ = 2 ^ 8 := by norm_num
    have hk' : 6 * k ≤ 8 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h8
    have : k = 1 := by omega
    rw [hVeq, this]
  ·
    rw [eq_bot_iff]
    intro w hw
    rw [mem_bot]
    exact eq_one_of_mem_range_commAutU3 hW2 hz3 (hUtop ▸ mem_top w) hw

end CFSG.Quasithin.H13.U3
