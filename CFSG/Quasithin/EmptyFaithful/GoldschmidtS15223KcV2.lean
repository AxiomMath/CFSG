module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Quot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem quasithinV2_ne_bot_of_commutator_ne_bot {H' L Z : Subgroup G} (hchar : CharTwo H')
    (hLH : L ≤ H') (hsub : IsSubnormal L H') (hperf : ⁅L, L⁆ = L) (hZH : Z ≤ H')
    (hZe : IsElemAbelian 2 Z) (hQZ : pCoreOf 2 H' ≤ Subgroup.centralizer (Z : Set G))
    (hQL : pCoreOf 2 H' ≤ Subgroup.normalizer (L : Set G)) (hne : ⁅Z, L⁆ ≠ ⊥) :
    quasithinV2 L ≠ ⊥ := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := pCoreOf 2 H' with hQdef
  have hQn : H' ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H'
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 H'
  have hZc : ∀ z ∈ Z, ∀ q ∈ Q, q * z = z * q := fun z hz q hq =>
    ((Subgroup.mem_centralizer_iff.mp (hQZ hq)) z hz).symm
  have hZQ : Z ≤ Q := fun z hz =>
    hchar ⟨hZH hz, Subgroup.mem_centralizer_iff.mpr fun q hq => hZc z hz q hq⟩
  have hOQ : pCoreOf 2 L ≤ Q := A4.pCoreOf_le_of_subnormal 2 hsub
  have hLQ : L ⊓ Q ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf_of_both Subgroup.le_normalizer (hLH.trans hQn)) (hQ2.to_inf_right)
  have hcomm : ∀ z ∈ Z, ∀ l ∈ L, ⁅z, l⁆ ∈ {y | y ∈ pCoreOf 2 L ⊓ Subgroup.centralizer
      (pCoreOf 2 L : Set G) ∧ y ^ 2 = 1} := by
    intro z hz l hl
    have hlq : ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := fun q hq =>
      (Subgroup.mem_normalizer_iff.mp (hQn (hLH hl)) q).mp hq
    have hlq' : ∀ q ∈ Q, l⁻¹ * q * l ∈ Q := fun q hq => by
      have := (Subgroup.mem_normalizer_iff.mp (hQn (hLH (L.inv_mem hl))) q).mp hq
      simpa using this
    have hw : l * z⁻¹ * l⁻¹ ∈ Q := hlq _ (Q.inv_mem (hZQ hz))
    have hzl : z * l * z⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hQL (hZQ hz)) l).mp hl
    have hxL : ⁅z, l⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem hzl (L.inv_mem hl)
    have hxQ : ⁅z, l⁆ ∈ Q := by
      have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Q.mul_mem (hZQ hz) hw
    have hwc : ∀ q ∈ Q, q * (l * z⁻¹ * l⁻¹) = (l * z⁻¹ * l⁻¹) * q := by
      intro q hq
      have h1 := hZc z⁻¹ (Z.inv_mem hz) (l⁻¹ * q * l) (hlq' q hq)
      have e1 : q * (l * z⁻¹ * l⁻¹) = l * ((l⁻¹ * q * l) * z⁻¹) * l⁻¹ := by group
      have e2 : (l * z⁻¹ * l⁻¹) * q = l * (z⁻¹ * (l⁻¹ * q * l)) * l⁻¹ := by group
      rw [e1, e2, h1]
    have hxc : ∀ q ∈ Q, q * ⁅z, l⁆ = ⁅z, l⁆ * q := by
      intro q hq
      have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      calc q * ⁅z, l⁆ = q * (z * (l * z⁻¹ * l⁻¹)) := by rw [e]
        _ = (q * z) * (l * z⁻¹ * l⁻¹) := (mul_assoc _ _ _).symm
        _ = (z * q) * (l * z⁻¹ * l⁻¹) := by rw [hZc z hz q hq]
        _ = z * (q * (l * z⁻¹ * l⁻¹)) := mul_assoc _ _ _
        _ = z * ((l * z⁻¹ * l⁻¹) * q) := by rw [hwc q hq]
        _ = (z * (l * z⁻¹ * l⁻¹)) * q := (mul_assoc _ _ _).symm
        _ = ⁅z, l⁆ * q := by rw [e]
    have hsq : ⁅z, l⁆ ^ 2 = 1 := by
      have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      have hzz : z ^ 2 = 1 := hZe.2 z hz
      have hww : (l * z⁻¹ * l⁻¹) ^ 2 = 1 := by
        rw [conj_pow]
        have : (z⁻¹) ^ 2 = 1 := by rw [inv_pow, hzz, inv_one]
        rw [this]
        group
      have hcom : Commute z (l * z⁻¹ * l⁻¹) := hwc z (hZQ hz)
      rw [e, hcom.mul_pow, hzz, hww, one_mul]
    exact ⟨⟨hLQ ⟨hxL, hxQ⟩,
      Subgroup.mem_centralizer_iff.mpr fun q hq => hxc q (hOQ hq)⟩, hsq⟩
  have hU : ⁅Z, L⁆ ≤ Subgroup.closure {y | y ∈ pCoreOf 2 L ⊓ Subgroup.centralizer
      (pCoreOf 2 L : Set G) ∧ y ^ 2 = 1} := by
    rw [Subgroup.commutator_le]
    exact fun z hz l hl => Subgroup.subset_closure (hcomm z hz l hl)
  intro hV
  have h1 : ⁅⁅Z, L⁆, L⁆ = ⊥ := by
    rw [eq_bot_iff, ← hV]
    exact Subgroup.commutator_mono hU le_rfl
  have h2 : ⁅⁅L, Z⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L Z]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hperf] at h3
  exact hne (by rw [Subgroup.commutator_comm]; exact h3)

end S15223

end CFSG.Quasithin
