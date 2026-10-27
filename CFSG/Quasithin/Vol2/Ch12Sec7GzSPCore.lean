module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open

theorem pcore_normal {G : Type} [Group G] (H : Subgroup G) :
    ∀ h ∈ H, ∀ x ∈ pCoreOf 2 H, h * x * h⁻¹ ∈ pCoreOf 2 H := by
  intro h hh x hx
  unfold pCoreOf at hx ⊢
  have hN : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : H) * y * (⟨h, hh⟩ : H)⁻¹, ?_, ?_⟩
  · exact hN.conj_mem y hy ⟨h, hh⟩
  · simp

theorem pcore_isPGroup {G : Type} [Group G] (H : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 H) := by
  unfold pCoreOf
  have hN : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  exact hN.map H.subtype

theorem pcore_max {G : Type} [Group G] (H : Subgroup G) {X : Subgroup G} (hXH : X ≤ H)
    (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hX2 : IsPGroup 2 ↥X) : X ≤ pCoreOf 2 H := by
  have hnorm : (X.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hXn (g : G) g.2 (n : G) hn⟩
  have hP2 : IsPGroup 2 ↥(X.subgroupOf H) :=
    hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  have hmem : X.subgroupOf H ∈ {K : Subgroup ↥H | K.Normal ∧ IsPGroup 2 ↥K} := ⟨hnorm, hP2⟩
  have hle : X.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup hmem
  intro x hx
  have hxH : x ∈ H := hXH hx
  have hmem' : (⟨x, hxH⟩ : H) ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  unfold pCoreOf
  exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hle hmem', rfl⟩

theorem pcore_le_of_odd {G : Type} [Group G] [Finite G] {H P : Subgroup G} (hPH : P ≤ H)
    (hP2 : IsPGroup 2 ↥P) (hodd : ¬ 2 ∣ P.relIndex H) : pCoreOf 2 H ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 ↥(P.subgroupOf H) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hidx : ¬ 2 ∣ (P.subgroupOf H).index := hodd
  have hN : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hle : CFSG.pCore 2 ↥H ≤ (hP'.toSylow hidx : Subgroup ↥H) :=
    hN.le_sylow_of_normal (hP'.toSylow hidx)
  intro x hx
  unfold pCoreOf at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyP : y ∈ P.subgroupOf H := hle hy
  exact Subgroup.mem_subgroupOf.mp hyP

theorem mem_pcore_of_central {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G} (hzH : z ∈ H)
    (hzc : ∀ h ∈ H, h * z = z * h) (hz2 : z * z = 1) : z ∈ pCoreOf 2 H := by
  have hXH : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.mpr hzH
  have hXn : ∀ h ∈ H, ∀ x ∈ Subgroup.zpowers z, h * x * h⁻¹ ∈ Subgroup.zpowers z := by
    intro h hh x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute h (z ^ k) := (show Commute h z from hzc h hh).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact (Subgroup.zpowers z).zpow_mem (Subgroup.mem_zpowers z) k
  have h2 : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hX2 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by simp [Nat.card_zpowers, h1])
    · exact IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, h1])
  exact pcore_max H hXH hXn hX2 (Subgroup.mem_zpowers z)

end CFSG.Quasithin.H13.I1277

end
