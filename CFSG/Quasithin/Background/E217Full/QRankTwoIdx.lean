module

public import CFSG.Quasithin.Background.E217Full.QRankTwoA
import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin.E217Full.LemmaQ

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem relIndex_inf_centSub_le_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hV16 : Nat.card V = 16)
    {X : Subgroup (MulAut V)} (hX : IsPGroup 2 X) {z : MulAut V} (hzc : ∀ x ∈ X, x * z = z * x)
    (hidx : (fixV (Subgroup.zpowers z)).index = 4) :
    (X ⊓ centSub (fixV (Subgroup.zpowers z))).relIndex X ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXst : X ≤ stabSub (fixV (Subgroup.zpowers z)) := by
    intro x hx u
    constructor
    · intro hu
      have h := fixV_zpowers_invariant (hzc x⁻¹ (X.inv_mem hx)) hu
      simpa using h
    · intro hu
      exact fixV_zpowers_invariant (hzc x hx) hu
  let ρ : X →* MulAut (fixV (Subgroup.zpowers z)) :=
    (resHom (fixV (Subgroup.zpowers z))).comp (Subgroup.inclusion hXst)
  have hker : ρ.ker = (X ⊓ centSub (fixV (Subgroup.zpowers z))).subgroupOf X := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have e : x ∈ ρ.ker ↔ Subgroup.inclusion hXst x ∈ (resHom (fixV (Subgroup.zpowers z))).ker :=
      Iff.rfl
    rw [e, ker_resHom, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hidx' : (X ⊓ centSub (fixV (Subgroup.zpowers z))).relIndex X = Nat.card ρ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hW2 : ∀ w : fixV (Subgroup.zpowers z), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hV (w : V))
  have hcardW : Nat.card (fixV (Subgroup.zpowers z)) = 4 := by
    have h := Subgroup.card_mul_index (fixV (Subgroup.zpowers z))
    rw [hidx, hV16] at h
    omega
  have hrkW : rk (fixV (Subgroup.zpowers z)) = 2 := by
    unfold rk
    rw [hcardW, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h6 : Nat.card (MulAut (fixV (Subgroup.zpowers z))) = 6 := card_mulAut_of_rk_two hW2 hrkW
  have : Finite (MulAut (fixV (Subgroup.zpowers z))) :=
    Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  have hp : IsPGroup 2 ρ.range := hX.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card ρ.range ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card _
  rw [hidx', hk]
  rw [hk] at hdvd
  have hle : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hk3 : k < 3 := by
    by_contra hk3
    push Not at hk3
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk3
    omega
  interval_cases k <;> simp_all

end CFSG.Quasithin.E217Full.LemmaQ
