module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeA2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeB2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeM2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem ggQTwoDUnit_B_shape {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {m : ℕ} (hm : 5 ≤ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {ψ : Su F0 2 1 m →* G} {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}
    (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    B = Bs ∨ ∃ a b : Fin m, a ≠ b ∧ ∀ s : ↥Bs, ((s : G) ∈ B ↔
      ∀ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (s : G) c → c a = c b) := by
  obtain ⟨hBs, hxB, hL, hcyc, hBmax, hT⟩ := qtwoDB3_unpack hcfg
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    fun b hb => qtwoDB3_bs_le_normalizer hbase (hBs.1 hb)
  by_cases hBeq : B = Bs
  · exact Or.inl hBeq
  right
  have hLn := qtwoDB3_L_normal hbase hm hL hcyc
  obtain ⟨T, hTx, hT2, hBT, t, ht, b, hb, hnt⟩ :=
    qtwoDB3_exists_t hbase hm hBs hxB hBL hLn hBmax hT (Or.inl hBeq)
  have hBL' : B ≤ Subgroup.normalizer (ψ.range : Set G) := by rw [hbase.range]; exact hBL
  have hTL : T ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hbase.range]; exact fun g hg => hLn g (hTx hg)
  have hind : ∀ b ∈ B, ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ b c :=
    fun b hb => qtwoDB3_ind_exists hbase (hBs.1 hb)
  have hnt' : ∃ t ∈ T, ∃ b ∈ B, ⁅t, b⁆ ∉ Subgroup.centralizer (ψ.range : Set G) := by
    rw [hbase.range]; exact ⟨t, ht, b, hb, hnt⟩
  obtain ⟨a, a', haa', hall⟩ :=
    qtwoDB3_core hbase.card_field hm hbase.hyp.ker hT2 hBL' hTL hBT hind hnt'
  obtain ⟨H, hHBs, hxH, hcardH, hHiff⟩ := qtwoDB3_exists_Hab hbase hm haa'
  have hBH : B ≤ H := fun s hs => (hHiff ⟨s, hBs.1 hs⟩).2 (hall s hs)
  have hp3 : p = 3 := hbase.p_eq
  have hcard : Nat.card ↥H ≤ Nat.card ↥B := by
    have h1 := hBs.2.2.1
    rw [hp3] at h1
    omega
  have hBHeq : B = H := Subgroup.eq_of_le_of_card_ge hBH hcard
  refine ⟨a, a', haa', fun s => ?_⟩
  rw [hBHeq]
  exact hHiff s

theorem ggQTwoDUnit_B_lt_Bs {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {m : ℕ} (hm : 5 ≤ m)
    (hm3 : ¬ 3 ∣ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {ψ : Su F0 2 1 m →* G} {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}
    (hbase : QTwoUnitBase p B Bs x L ψ ε) : B < Bs := by
  classical
  obtain ⟨hBs, hxB, hL, hcyc, hBmax, hT⟩ := qtwoDB3_unpack hcfg
  refine lt_of_le_of_ne hBs.1 fun hBeq => ?_
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    fun b hb => qtwoDB3_bs_le_normalizer hbase (hBs.1 hb)
  have hLn := qtwoDB3_L_normal hbase hm hL hcyc
  obtain ⟨T, hTx, hT2, hBT, t, ht, b, hb, hnt⟩ :=
    qtwoDB3_exists_t hbase hm hBs hxB hBL hLn hBmax hT (Or.inr hm3)
  have hBL' : B ≤ Subgroup.normalizer (ψ.range : Set G) := by rw [hbase.range]; exact hBL
  have hTL : T ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hbase.range]; exact fun g hg => hLn g (hTx hg)
  have hind : ∀ b ∈ B, ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ b c :=
    fun b hb => qtwoDB3_ind_exists hbase (hBs.1 hb)
  have hnt' : ∃ t ∈ T, ∃ b ∈ B, ⁅t, b⁆ ∉ Subgroup.centralizer (ψ.range : Set G) := by
    rw [hbase.range]; exact ⟨t, ht, b, hb, hnt⟩
  obtain ⟨a, a', haa', hall⟩ :=
    qtwoDB3_core hbase.card_field hm hbase.hyp.ker hT2 hBL' hTL hBT hind hnt'
  have hnt1 : Nontrivial F0ˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units, hbase.card_field]
    norm_num
  obtain ⟨ω, hω⟩ := exists_ne (1 : F0ˣ)
  obtain ⟨s, hs, hsc⟩ := hbase.full (Pi.mulSingle a ω)
  have h := hall s (hBeq ▸ hs) _ hsc
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm haa')] at h
  exact hω h

end CFSG.StandardType.QTwo

end
