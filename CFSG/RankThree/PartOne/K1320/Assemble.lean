module

public import CFSG.RankThree.PartOne.K1320.Pair
public import CFSG.RankThree.PartOne.K1320.Comm
public import CFSG.RankThree.PartOne.PAIR22.Dich
public import CFSG.RankThree.PartOne.K1320.Chain

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem chain_comm_clause (hS : SchreierFor InCatalog)
    (h133 : S13K.KF133Two) (hDist : S13K.KFCommDistinct) (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hn8 : ¬ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f)
    {z : MulAut E} (hz : Inverter p E z) {t₁ t₂ t₃ : MulAut E} (hch : Chain3 p E L t₁ t₂ t₃)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hs₁ : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ reflectionSet p E)
    (hs₁L : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ torusImage E L) {g₁ g₃ : ℕ}
    (hK₁ : KFAt p E g₁ (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹)) (hK₃ : KFAt p E g₃ t₃)
    (hsp : p ∣ 2 ^ g₁ - 1) :
    kZero p E t₁ ≤ Subgroup.centralizer (kZero p E t₃ : Set G) ∧
      kZero p E t₁ ⊓ kZero p E t₃ = ⊥ := by
  have hp := h.prime
  have hs₃ : conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ ∈ reflectionSet p E :=
    conj_mem_reflectionSet hp hch.mem₃ hw
  have hKs₃ : KFAt p E g₃ (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹) := hK₃.conj hw
  have hne : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ≠
      conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ := by
    intro h1
    have h2 : t₁ = t₃ := mul_left_cancel (mul_right_cancel h1)
    have h3 := hch.ord₁₂
    rw [h2, Sec1320.orderOf_mul_comm_reflections hch.mem₂.1 hch.mem₃.1, hch.ord₂₃] at h3
    omega
  have hcomm : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ *
      (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹) =
      conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ *
      (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) := by
    calc conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ * (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹)
        = conjAut E w hw * (t₁ * t₃) * (conjAut E w hw)⁻¹ := by group
      _ = conjAut E w hw * (t₃ * t₁) * (conjAut E w hw)⁻¹ := by rw [hch.comm₁₃]
      _ = _ := by group
  have hnc : ∀ y ∈ reflectionGroup p E, y * (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) * y⁻¹ ≠
      conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ := by
    intro y hy hyst
    have hgW : conjAut E w hw ∈ torusWeyl E := ⟨⟨w, hw⟩, rfl⟩
    have hy' : (conjAut E w hw)⁻¹ * y * conjAut E w hw ∈ reflectionGroup p E := by
      have := Sec1322.conj_mem_reflectionGroup hp ((torusWeyl E).inv_mem hgW) hy
      simpa [mul_assoc] using this
    refine chain_not_conj_one_three hch hz.noconj hy' ?_
    calc (conjAut E w hw)⁻¹ * y * conjAut E w hw * t₁ *
          ((conjAut E w hw)⁻¹ * y * conjAut E w hw)⁻¹
        = (conjAut E w hw)⁻¹ * (y * (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) * y⁻¹) *
          conjAut E w hw := by group
      _ = (conjAut E w hw)⁻¹ * (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹) *
          conjAut E w hw := by rw [hyst]
      _ = t₃ := by group
  exact commClause_of_conj hw (comm_clause hS h133 hDist h hF hF13 hT hEA hn8 hz hs₁ hs₁L hs₃
    hK₁ hKs₃ hsp hne hcomm hnc)

theorem chain_pair_data
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two) (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A) (hn8 : ¬ RowModel p L 8)
    {z : MulAut E} (hz : Inverter p E z) {t₁ t₂ t₃ : MulAut E} (hch : Chain3 p E L t₁ t₂ t₃)
    (hL₂ : PAIR22.PairLift p E t₂) (hL₃ : PAIR22.PairLift p E t₃) :
    ∃ f' : ℕ, KFAt p E f' t₂ ∧ KFAt p E f' t₃ ∧
      CentrallyLThree f' ↥(kZero p E t₂ ⊔ kZero p E t₃) := by
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hst : t₂ * t₃ ≠ t₃ * t₂ := by
    intro hc
    have h2 : (t₂ * t₃) ^ 2 = 1 := by
      have h22 : t₂ * t₂ = 1 := RefFacts.mul_self_eq_one hch.mem₂.1
      have h33 : t₃ * t₃ = 1 := RefFacts.mul_self_eq_one hch.mem₃.1
      calc (t₂ * t₃) ^ 2 = t₂ * (t₃ * t₂) * t₃ := by rw [pow_two]; group
        _ = t₂ * (t₂ * t₃) * t₃ := by rw [← hc]
        _ = (t₂ * t₂) * (t₃ * t₃) := by group
        _ = 1 := by rw [h22, h33, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hch.ord₂₃] at this
    omega
  obtain ⟨w, hw, -, hs₂L⟩ := hch.inL
  obtain ⟨J, hJ, h2J, h3J⟩ := PAIR22.pair_member hS h133 h hF hF13 hT hn8 hch.mem₂ hch.mem₃ hst hw
    hs₂L hL₂ hL₃
  exact centrallyLThree_of_pair hGA hF13 hcard hz hJ hch.mem₂ h2J hch.mem₃ h3J hch.ord₂₃

theorem chain_pair_L3
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two) (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A) (hn8 : ¬ RowModel p L 8)
    {z : MulAut E} (hz : Inverter p E z) {t₁ t₂ t₃ : MulAut E} (hch : Chain3 p E L t₁ t₂ t₃) {g : ℕ}
    (hK₂ : KFAt p E g t₂) (hL₃ : PAIR22.PairLift p E t₃) :
    CentrallyLThree g ↥(kZero p E t₃ ⊔ kZero p E t₂) := by
  obtain ⟨f', hK2, -, hcl⟩ := chain_pair_data hGA hS h133 h hF hF13 hT hEA hn8 hz hch
    (PAIR22.pairLift_of_kfAt hK₂) hL₃
  have hf'g : f' = g := psl_two_degree_eq hK2.2.1 hK₂.2.1
  subst hf'g
  rw [sup_comm]
  exact hcl

omit [Finite G] in
theorem chain_sup_model {t₁ t₂ : MulAut E} {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hgen : kZero p E (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) ⊔
      kZero p E (conjAut E w hw * t₂ * (conjAut E w hw)⁻¹) = L)
    {tag : StatedLieTag} {n f : ℕ} (hL : StatedClassicalModel ↥L tag n 2 f) :
    StatedClassicalModel ↥(kZero p E t₂ ⊔ kZero p E t₁) tag n 2 f := by
  have h1 : conjBy w (kZero p E t₂ ⊔ kZero p E t₁) = L := by
    rw [conjBy_sup, ← kZero_conj p t₂ hw, ← kZero_conj p t₁ hw, sup_comm]
    exact hgen
  have h2 : kZero p E t₂ ⊔ kZero p E t₁ = conjBy w⁻¹ L := by
    rw [← h1, Equivariance.conjBy_inv_conjBy]
  rw [h2]
  exact (Equivariance.statedClassicalModel_conjBy_iff w⁻¹ L).mpr hL

end CFSG.RankThree.PartOne.K1320
