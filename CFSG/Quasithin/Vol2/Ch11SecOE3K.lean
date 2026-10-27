module

public import CFSG.Quasithin.Vol2.Ch11SecOE3J
public import CFSG.Quasithin.H13.NQBlockRadicalR2Inputs
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Vol2.Ch11SecOE3E

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped IsMulCommutative

theorem false_of_r2Shape
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hFSU : Ch10.StmtFSUChoice) (h701 : Stmt7_0_1) {G : Type} [Group G] [Finite G]
    {T K : Subgroup G} (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hmax : quasithinIsMaximalLocal T K) (hf : quasithinIsFaithfulLocal T K) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hX : R2Shape r (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  have hTN := le_normalizer_of_r2Shape h37 h38 hs hnab hK hmax.1 hr hr5 hX
  obtain ⟨I, hI⟩ := hFSU G T K hs hnab hK hT hmax hf hX.1
  have hset : Setting G T K I r := ⟨hI, hTN, hr, hr5, hX⟩
  obtain ⟨_, -, -, hcases⟩ := h701 G T K I hI
  rcases hcases with hFF | hJ4 | hOrth | hFour
  · obtain ⟨A, hA⟩ := hFF
    obtain ⟨A₀, -, hA₀⟩ := B1.exists_isFFStarMin_le hA
    have hbest := B15P4.isFFStarMin_iff_isBestOffender.1 hA₀
    rw [hset.fsuL0_eq] at hbest
    by_cases hc : ⁅autOn K (fsuV T I), A₀⁆ = ⊥
    · exact hset.false_of_comm_eq_bot hbest hc
    · exact hset.false_of_comm_ne_bot hbest hc
  · exact hset.not_concl701J4 hJ4
  · exact hset.not_concl701Orth hOrth
  · exact hset.not_concl701Four hFour

theorem noOddLinear_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hFSU : Ch10.StmtFSUChoice) (h701 : Stmt7_0_1) : NQBlock.NoOddLinearThreeLStarF := by
  intro G _ _ T K hs hnab hK hT hmax hf r hr hr3
  have hr5 : 5 ≤ r := by
    have h4 : r ≠ 4 := by
      rintro rfl
      norm_num at hr
    omega
  exact ⟨fun hX => false_of_r2Shape h37 h38 hFSU h701 hs hnab hK hT hmax hf hr hr5
      (r2Shape_of_isPSL hr hr5 hX),
    fun hX => false_of_r2Shape h37 h38 hFSU h701 hs hnab hK hT hmax hf hr hr5
      (r2Shape_of_isSL3 hr hr5 hX)⟩

end CFSG.Quasithin.Vol2.Ch11.OE3
