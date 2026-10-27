module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma qTwoLMDivCoordInner_tker_two_group_eq_one {L : Type} [Group L] {H : Subgroup L}
    (hH : IsPGroup 2 H) {z : L} (hz : z ∈ H) (hz3 : z ^ 3 = 1) : z = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hH.exists_orderOf_eq_pow ⟨z, hz⟩
  have hkz : orderOf z = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hdvd : 2 ^ k ∣ 3 := by
    rw [← hkz]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz3
  have hk0 : 2 ^ k = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact h
    · exfalso
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at h
        norm_num at h
      · have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)
        rw [h] at h2
        norm_num at h2
  have h1 : orderOf z = 1 := by rw [hkz, hk0]
  exact orderOf_eq_one_iff.mp h1

private lemma qTwoLMDivCoordInner_tker_commutator_hom {H : Type} [Group H]
    (x : H) (hcen : ∀ y : H, ⁅x, y⁆ ∈ Subgroup.center H) :
    ∃ φ : H →* Subgroup.center H, ∀ y : H, (φ y : H) = ⁅x, y⁆ := by
  refine ⟨MonoidHom.mk' (fun y => ⟨⁅x, y⁆, hcen y⟩) (fun y z => Subtype.ext ?_), fun y => rfl⟩
  show ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  have hc : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [Subgroup.mem_center_iff.1 (hcen z) y, mul_inv_cancel_right]
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hc]

theorem qTwoLMDivCoordInner_tker {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m) (h3 : 3 ∣ m) {F0 : Type}
    [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0] {c : ↥L →* L0}
    {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ) :
    (3 ∣ Nat.card (Subgroup.center ↥L) → Function.Injective τ) ∧
      (¬ 3 ∣ Nat.card (Subgroup.center ↥L) →
        ∀ f, τ f = 1 ↔ f ∈ Subgroup.zpowers (qTwoOneVec m h3)) ∧
      ∀ l : ↥L, τ (qTwoOneVec m h3) * l = l * τ (qTwoOneVec m h3) := by
  have hperf : commutator ↥L = ⊤ := qTwoLMFrameC_perfect hG
  have hkerpi := qTwoLMDivCoordInner_kerpi hperf hN (by omega : 4 ≤ m) hU
  refine ⟨?_, ?_, ?_⟩
  · intro h3dvd
    rw [injective_iff_map_eq_one]
    intro f hf
    have hpid : π (δ f) = 1 := by
      calc π (δ f) = c (τ f) := (hτ.comm f).symm
        _ = c 1 := by rw [hf]
        _ = 1 := map_one c
    have hker : δ f ∈ π.ker := MonoidHom.mem_ker.mpr hpid
    rw [hkerpi.1 h3dvd, Subgroup.mem_bot] at hker
    exact hδ.inj (by rw [hker, map_one])
  · intro h3ndvd f
    constructor
    · intro hf
      have hpid : π (δ f) = 1 := by
        calc π (δ f) = c (τ f) := (hτ.comm f).symm
          _ = c 1 := by rw [hf]
          _ = 1 := map_one c
      have hker : δ f ∈ Subgroup.center (Su F0 2 1 m) :=
        hU.π_ker (MonoidHom.mem_ker.mpr hpid)
      obtain ⟨c0, hc0⟩ := qTwoLMDivCoordInner_center_scalar hU.card (by omega : 4 ≤ m) hker
      exact (hδ.scalar f).mp ⟨c0, hc0⟩
    · intro hf
      obtain ⟨c0, hc0⟩ := (hδ.scalar f).mpr hf
      have hker : δ f ∈ π.ker :=
        hkerpi.2 h3ndvd (δ f) (qTwoLMDivCoordInner_scalar_central hc0)
      have hc : c (τ f) = 1 := by
        rw [hτ.comm f, MonoidHom.mem_ker.mp hker]
      exact qTwoLMDivCoordInner_tker_two_group_eq_one hU.c_two (MonoidHom.mem_ker.mpr hc)
        (hτ.cube f)
  · intro l
    set v1 : ↥(sumZero m 3) := qTwoOneVec m h3
    obtain ⟨c0, hc0⟩ := (hδ.scalar v1).mpr (Subgroup.mem_zpowers v1)
    have hcen : δ v1 ∈ Subgroup.center (Su F0 2 1 m) :=
      qTwoLMDivCoordInner_scalar_central hc0
    have hpi_center : π (δ v1) ∈ Subgroup.center L0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨s, rfl⟩ := hU.π_surj y
      calc π s * π (δ v1) = π (s * δ v1) := (map_mul π s (δ v1)).symm
        _ = π (δ v1 * s) := by rw [Subgroup.mem_center_iff.mp hcen s]
        _ = π (δ v1) * π s := map_mul π (δ v1) s
    have hc_center : c (τ v1) ∈ Subgroup.center L0 := by
      rw [hτ.comm v1]
      exact hpi_center
    have hmem_comm : ∀ l' : ↥L, ⁅τ v1, l'⁆ ∈ Subgroup.center ↥L := by
      intro l'
      apply hU.c_ker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hc_center (c l')).symm
    obtain ⟨φ, hφ⟩ := qTwoLMDivCoordInner_tker_commutator_hom (τ v1) hmem_comm
    have htriv : φ l = 1 := by
      have hle : commutator ↥L ≤ φ.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        apply Subtype.ext
        show (⁅(φ a : ↥L), (φ b : ↥L)⁆ : ↥L) = 1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp (φ a).2 (φ b)).symm
      have htop : ⊤ ≤ φ.ker := hperf ▸ hle
      exact MonoidHom.mem_ker.mp (htop trivial)
    have h2 : ⁅τ v1, l⁆ = 1 := by
      rw [← hφ l, htriv, Subgroup.coe_one]
    exact commutatorElement_eq_one_iff_mul_comm.mp h2

end CFSG.StandardType.QTwo

end
