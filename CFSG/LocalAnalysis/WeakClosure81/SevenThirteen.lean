module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_le_pCoreOf_kSub {V H E : Subgroup G} (h : Hyp711 V H E) :
    ¬ V ≤ pCoreOf 2 (kSub V H E) := by
  intro hle
  obtain ⟨g, -, -, hnot⟩ := mem_omegaSet.mp h.mem
  exact hnot (hle.trans (pCoreOf_kSub_le_pCoreOf h.le h.normal h.omega_le))

theorem inf_pCoreOf_kSub_eq_inf_iSub {V H E : Subgroup G} (h : Hyp711 V H E) :
    V ⊓ pCoreOf 2 (kSub V H E) = V ⊓ iSub V H E := by
  exact (inf_iSub_eq_inf_J h.mem h.iSub_le h.pcore_le).symm

theorem rk_add_one_le_of_lt {V A : Subgroup G} (hV : IsElemAbelian 2 V) (hA : A < V) :
    rk ↥A + 1 ≤ rk ↥V := by
  have hVp : IsPGroup 2 V := isPGroup_two_of_isElemAbelian hV
  have hAp : IsPGroup 2 A := hVp.to_le hA.le
  have h1 : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hAp
  have h2 : Nat.card V = 2 ^ rk V := card_eq_two_pow_of_isPGroup hVp
  have hlt : Nat.card A < Nat.card V := Subgroup.card_lt_of_lt (by simpa using hA)
  rw [h1, h2] at hlt
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  omega

private theorem zpow_eq_one_or_self_of_mul_self_eq_one {x : G} (hx : x * x = 1) (n : ℤ) :
    x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast, pow_two, hx]
    rw [h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast, pow_two, hx]
    rw [h2, one_zpow, one_mul]


theorem kSub_inf_centralizer_iSub_le_pCoreOf {V H E : Subgroup G} (h : Hyp711 V H E) :
    kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤ pCoreOf 2 (kSub V H E) := by
  have h4 := seven_four h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
  have hodd : CFSG.QuasithinUnique.oddCoreIn (kSub V H E) = ⊥ := h.oddCore
  rwa [hodd, sup_bot_eq] at h4

theorem commutator_iSub_zpowers_le_inf_iSub {V H E : Subgroup G} (h : Hyp711 V H E) {v : G}
    (hv : v ∈ V) : ⁅iSub V H E, Subgroup.zpowers v⁆ ≤ V ⊓ iSub V H E := by
  rw [Subgroup.commutator_le]
  intro a ha w hw
  rw [Subgroup.mem_zpowers_iff] at hw
  obtain ⟨n, rfl⟩ := hw
  rcases zpow_eq_one_or_self_of_mul_self_eq_one (elemAbelian_mul_self h.elemAbelian hv) n
    with h1 | hv'
  · rw [h1]
    simp [commutatorElement_def]
  · rw [hv']
    exact commutator_mem_inf_iSub h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
      h.mem ha hv

theorem seven_thirteen_at {m n : ℕ} (hRank : UnitaryRootCommutatorRankAt m)
    {V H E : Subgroup G} (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hX : IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hroot : ∀ k : ↥(kSub V H E), (k : G) ∈ V → (k : G) ∉ pCoreOf 2 (kSub V H E) →
      IsUnitaryTransvection X m n (φ k)) :
    2 * n + 1 ≤ rk ↥V ∧ 2 * n ≤ rk ↥(V ⊓ iSub V H E) := by
  have hnle : ¬ V ≤ pCoreOf 2 (kSub V H E) := not_le_pCoreOf_kSub h
  obtain ⟨v, hvV, hvJ⟩ := Set.not_subset.1 hnle
  have hVK : V ≤ kSub V H E := le_kSub h.mem
  have hvK : v ∈ kSub V H E := hVK hvV
  have hIab : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHN : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal)
  have hKN : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) := hKH.trans hHN
  have hcent := kSub_inf_centralizer_iSub_le_pCoreOf h
  have hvv : v * v = 1 := elemAbelian_mul_self h.elemAbelian hvV
  have hrank := hRank G (kSub V H E) (iSub V H E) n hIab hKN hcent X φ hφ hX
    ⟨v, hvK⟩ hvv (hroot ⟨v, hvK⟩ hvV hvJ)
  have hle := commutator_iSub_zpowers_le_inf_iSub h hvV
  have h2 : 2 * n ≤ rk ↥(V ⊓ iSub V H E) := hrank.trans (rk_mono hle)
  have h3 : V ⊓ iSub V H E < V := by
    rw [← inf_pCoreOf_kSub_eq_inf_iSub h]
    exact inf_lt_left.2 hnle
  exact ⟨by have := rk_add_one_le_of_lt h.elemAbelian h3; omega, h2⟩

theorem seven_thirteen (hRank : UnitaryRootCommutatorRank) {V H E : Subgroup G}
    (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {m n : ℕ} (hm : 3 ≤ m)
    (hX : IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hroot : ∀ k : ↥(kSub V H E), (k : G) ∈ V → (k : G) ∉ pCoreOf 2 (kSub V H E) →
      IsUnitaryTransvection X m n (φ k)) :
    2 * n + 1 ≤ rk ↥V ∧ 2 * n ≤ rk ↥(V ⊓ iSub V H E) :=
  seven_thirteen_at (unitaryRootCommutatorRank_iff_at.1 hRank m hm) h hφ hX hroot

end CFSG.LocalAnalysis.WeakClosure81

