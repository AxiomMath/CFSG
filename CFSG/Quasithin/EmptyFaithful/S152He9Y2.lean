module

public import CFSG.Quasithin.EmptyFaithful.S143Five
public import CFSG.Quasithin.Recognition.CertSzZero
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oTwoQuot_sup_iso {Y R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hYO : (pCoreOf 2 Y).relIndex Y = 5) (hOR : pCoreOf 2 Y ≤ R)
    (hnt : ∃ r ∈ R, ∃ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∉ pCoreOf 2 Y) :
    IsSylowTwoOf R (Y ⊔ R) ∧ R.relIndex (Y ⊔ R) = 5 ∧
      (Nonempty (OTwoQuot (Y ⊔ R) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (Y ⊔ R) ≃* ↥(CFSG.Open.Sz 0))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 Y with hP
  set Q := Y ⊔ R with hQ
  have hPY : P ≤ Y := pCoreOf_le 2 Y
  have hYQ : Y ≤ Q := le_sup_left
  have hRQ : R ≤ Q := le_sup_right
  set I := Y ⊓ R with hI
  have hIY : I ≤ Y := inf_le_left
  have hIR : I ≤ R := inf_le_right
  have hPI : P ≤ I := le_inf hPY hOR
  have h1 : Y.relIndex (R ⊔ Y) = Y.relIndex R := F1.relIndex_sup_eq_of_le_normalizer hRY
  rw [sup_comm] at h1
  have h2 : I.relIndex R = Y.relIndex R := Subgroup.inf_relIndex_right Y R
  have hm1 := Subgroup.relIndex_mul_relIndex I R Q hIR hRQ
  have hm2 := Subgroup.relIndex_mul_relIndex I Y Q hIY hYQ
  have hne : Y.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : R.relIndex Q = I.relIndex Y := by
    rw [h2, ← h1] at hm1
    have : Y.relIndex Q * R.relIndex Q = Y.relIndex Q * I.relIndex Y := by
      rw [hm1, mul_comm (Y.relIndex Q) (I.relIndex Y)]
      exact hm2.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this
  have h4 : I.relIndex Y ∣ 5 := by
    have := Subgroup.relIndex_mul_relIndex P I Y hPI hIY
    rw [hYO] at this
    exact Dvd.intro_left _ this
  have h5 : R.relIndex Q = 5 := by
    rw [h3]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h4 with h6 | h6
    · exfalso
      have hYI : Y ≤ I := Subgroup.relIndex_eq_one.mp h6
      have hYR : Y ≤ R := hYI.trans hIR
      have hYp : IsPGroup 2 Y := hR2.to_le hYR
      have hY2 : Y ≤ P := le_pCoreOf_of_le_normalizer le_rfl Subgroup.le_normalizer hYp
      have : P = Y := le_antisymm hPY hY2
      rw [this, Subgroup.relIndex_self] at hYO
      omega
    · exact h6
  have hsyl : IsSylowTwoOf R Q := ⟨hRQ, hR2, by rw [show (R.subgroupOf Q).index = R.relIndex Q from rfl, h5]; norm_num⟩
  have hnn : ¬ Q ≤ Subgroup.normalizer (R : Set G) := by
    intro hQR
    obtain ⟨r, hr, y, hy, hnot⟩ := hnt
    apply hnot
    have hyQ : y ∈ Q := hYQ hy
    have hrQ : r ∈ Q := hRQ hr
    have hc1 : r * y * r⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRY hr) y).mp hy) (Y.inv_mem hy)
    have hc2 : r * y * r⁻¹ * y⁻¹ ∈ R := by
      have e : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
      rw [e]
      exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hQR hyQ) r⁻¹).mp (R.inv_mem hr))
    have hIN : Y ≤ Subgroup.normalizer (I : Set G) := by
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hQR (hYQ hg)⟩
    exact le_pCoreOf_of_le_normalizer hIY hIN (hR2.to_le hIR) ⟨hc1, hc2⟩
  obtain ⟨S, hS, hSi, hS1⟩ :=
    exists_isPGroup_index_quot_of_relIndex hRQ hR2 h5 (by norm_num) hnn
  have hX2 := OTwoQuot.eq_bot_of_normal_of_isPGroup Q
  refine ⟨hsyl, h5, ?_⟩
  rcases nonempty_mulEquiv_dihedralGroup_five_or_card_twenty hX2 hS hS1 hSi with hD | hc
  · exact Or.inl hD
  · have : Finite ↥(CFSG.Open.Sz 0) := Nat.finite_of_card_ne_zero (by rw [card_sz_zero_eq_twenty]; norm_num)
    obtain ⟨e⟩ := nonempty_mulEquiv_of_card_twenty hX2
      (fun N hN hp => le_bot_iff.mp (pCore_two_sz_zero_eq_bot ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp))
      hc card_sz_zero_eq_twenty
    exact Or.inr ⟨e⟩

end CFSG.Quasithin.He9
