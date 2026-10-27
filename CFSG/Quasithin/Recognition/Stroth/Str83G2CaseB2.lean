module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CoprimeChain
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Vol2.Ch11SecDGroup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem inf_conjugate_centralized_of_le {H0 S Q1 Q2 V : Subgroup G} {w : G}
    (hSw : S ⊔ conjugate S w = H0) (hwH : w ∈ H0)
    (hQ1Q2 : Q1 ⊔ Q2 = S)
    (hQ1S : Q1 ≤ S) (hQ2S : Q2 ≤ S)
    (hQ1n : S ≤ Subgroup.normalizer (Q1 : Set G))
    (hQ2n : S ≤ Subgroup.normalizer (Q2 : Set G))
    (hQ2p : IsPGroup 2 Q2)
    (hQ2H : H0 ≤ Subgroup.normalizer (Q2 : Set G))
    (hV1 : Q1 ≤ Subgroup.centralizer (V : Set G))
    (hV2 : Q2 ≤ Subgroup.normalizer (V : Set G)) :
    oTwoUpper H0 ≤ Subgroup.centralizer (V ⊓ conjugate V w : Set G) := by
  classical
  set Qs : Subgroup G := Q1 ⊔ conjugate Q1 w with hQs
  have hQ2_le_H0 : Q2 ≤ H0 := hQ2S.trans (hSw ▸ le_sup_left)
  have hQ1_le_H0 : Q1 ≤ H0 := hQ1S.trans (hSw ▸ le_sup_left)
  have hQ1w_le_H0 : conjugate Q1 w ≤ H0 := by
    exact (Subgroup.map_mono hQ1S).trans (hSw ▸ le_sup_right)
  have hQ2w : conjugate Q2 w = Q2 :=
    conjugate_eq_self_of_mem_normalizer (hQ2H hwH)
  have hQ1w_le_Qs : conjugate Q1 w ≤ Qs := by
    rw [hQs]; exact le_sup_right
  have hQ1_le_Qs : Q1 ≤ Qs := by
    rw [hQs]; exact le_sup_left
  have hQ2_le_NQ1 : Q2 ≤ Subgroup.normalizer (Q1 : Set G) := hQ2S.trans hQ1n
  have hQ2_le_NQ1w : Q2 ≤ Subgroup.normalizer (conjugate Q1 w : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [mem_conjugate_iff] at hx ⊢
      have hq' : w * q * w⁻¹ ∈ Q2 := by
        have : q ∈ conjugate Q2 w := by rw [hQ2w]; exact hq
        exact (mem_conjugate_iff Q2 w q).mp this
      have hxq : (w * q * w⁻¹) * (w * x * w⁻¹) * (w * q * w⁻¹)⁻¹ ∈ Q1 :=
        (Subgroup.mem_normalizer_iff.mp (hQ2_le_NQ1 hq') _).mp hx
      convert hxq using 1
      group
    · intro hx
      rw [mem_conjugate_iff] at hx ⊢
      have hq' : w * q * w⁻¹ ∈ Q2 := by
        have : q ∈ conjugate Q2 w := by rw [hQ2w]; exact hq
        exact (mem_conjugate_iff Q2 w q).mp this
      have hxq : (w * q * w⁻¹) * (w * x * w⁻¹) * (w * q * w⁻¹)⁻¹ ∈ Q1 := by
        convert hx using 1
        group
      exact (Subgroup.mem_normalizer_iff.mp (hQ2_le_NQ1 hq') _).mpr hxq
  have hQ2_le_NQs : Q2 ≤ Subgroup.normalizer (Qs : Set G) := by
    rw [hQs]
    exact F1.le_normalizer_sup hQ2_le_NQ1 hQ2_le_NQ1w
  have hQsQ2 : Qs ⊔ Q2 = H0 := by
    apply le_antisymm
    · rw [hQs]
      exact sup_le (sup_le hQ1_le_H0 hQ1w_le_H0) hQ2_le_H0
    · rw [← hSw]
      refine sup_le ?_ ?_
      · rw [← hQ1Q2]
        exact sup_le (hQ1_le_Qs.trans le_sup_left) le_sup_right
      · rw [← hQ1Q2, conjugate, Subgroup.map_sup]
        change conjugate Q1 w ⊔ conjugate Q2 w ≤ Qs ⊔ Q2
        rw [hQ2w]
        exact sup_le (hQ1w_le_Qs.trans le_sup_left) le_sup_right
  have hQ2_le_NVw : Q2 ≤ Subgroup.normalizer (conjugate V w : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [mem_conjugate_iff] at hx ⊢
      have hq' : w * q * w⁻¹ ∈ Q2 := by
        have : q ∈ conjugate Q2 w := by rw [hQ2w]; exact hq
        exact (mem_conjugate_iff Q2 w q).mp this
      have hxq : (w * q * w⁻¹) * (w * x * w⁻¹) * (w * q * w⁻¹)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hV2 hq') _).mp hx
      convert hxq using 1
      group
    · intro hx
      rw [mem_conjugate_iff] at hx ⊢
      have hq' : w * q * w⁻¹ ∈ Q2 := by
        have : q ∈ conjugate Q2 w := by rw [hQ2w]; exact hq
        exact (mem_conjugate_iff Q2 w q).mp this
      have hxq : (w * q * w⁻¹) * (w * x * w⁻¹) * (w * q * w⁻¹)⁻¹ ∈ V := by
        convert hx using 1
        group
      exact (Subgroup.mem_normalizer_iff.mp (hV2 hq') _).mpr hxq
  have hQs_le_C : Qs ≤ Subgroup.centralizer (V ⊓ conjugate V w : Set G) := by
    rw [hQs]
    refine sup_le ?_ ?_
    · exact hV1.trans (Subgroup.centralizer_le Set.inter_subset_left)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [mem_conjugate_iff] at hx
      have hyw : y ∈ conjugate V w := hy.2
      rw [mem_conjugate_iff] at hyw
      have hq : w * x * w⁻¹ ∈ Q1 := hx
      have hv : w * y * w⁻¹ ∈ V := hyw
      have hcomm : (w * y * w⁻¹) * (w * x * w⁻¹) =
          (w * x * w⁻¹) * (w * y * w⁻¹) :=
        Subgroup.mem_centralizer_iff.mp (hV1 hq) _ hv
      calc y * x = w⁻¹ * ((w * y * w⁻¹) * (w * x * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * x * w⁻¹) * (w * y * w⁻¹)) * w := by rw [hcomm]
        _ = x * y := by group
  exact (CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup' (X := H0) (Y := Qs) (T := Q2)
    (by rw [hQsQ2]) hQ2p hQ2_le_NQs).trans hQs_le_C


theorem card_commutator_le_of_two_steps {H X D : Subgroup G} {q : ℕ}
    (hXH : X ≤ H) (hXnormal : IsNormalIn H X X) (hXe : IsElemAbelian 2 X)
    (hDH : D ≤ H) (hDodd : Odd (Nat.card D))
    (hCount : ∀ c : ℕ, IsChiefSeriesFrom H X X c → c = 2)
    (hb : ∀ L N : Subgroup G, IsChiefStep H X L N → ¬ IsCentralStep H L N →
      Nat.card (N ⧸ L.subgroupOf N) ≤ q ^ 2) :
    Nat.card ↥⁅X, D⁆ ≤ q ^ 4 := by
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := X) X hXnormal
  have hc : c = 2 := hCount c hser
  have h := card_commutator_le_pow_of_chiefSeries (H := H) (X := X) (D := D) (b := q ^ 2)
    hXH hXe hDH hDodd hb hser
  rw [hc] at h
  calc Nat.card ↥⁅X, D⁆ ≤ (q ^ 2) ^ 2 := h
    _ = q ^ 4 := by ring

end CFSG.Quasithin.Stroth

end
