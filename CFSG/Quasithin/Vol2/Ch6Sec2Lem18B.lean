module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem15C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem four_lt_ch618 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    4 < (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) := by
  obtain ⟨U₀, hU₀U, -, hU₀es, hU₀32, -⟩ :=
    h.exists_extraspecial_ch615 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h h331 h432 h512 h614 h615
  have hZc : ∀ z ∈ zCh611 T, ∀ u ∈ uCh611 T L V, u * z = z * u := fun z hz u hu =>
    (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm
  have hcomm : ∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
    fun a ha b hb => h.comm_mem_ch615 h331 h432 h512 h614 h615 ha hb
  obtain ⟨-, -, hcen⟩ := extraspecial_facts_ch615 hZ2 hU₀U hZc hcomm hU₀es
  have hle : centerOf (uCh611 T L V) ⊓ U₀ ≤ zCh611 T := fun x hx => hcen x hx.2 hx.1
  have hcard : Nat.card ↥(centerOf (uCh611 T L V) ⊓ U₀) ≤ 2 :=
    hZ2 ▸ Subgroup.card_le_of_le hle
  have h1 := Subgroup.relIndex_mul_card (centerOf (uCh611 T L V)) U₀
  have hne : (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_le_of_le_right hU₀U hne
  have h3 : 2 ^ 5 ≤ (centerOf (uCh611 T L V)).relIndex U₀ * 2 :=
    hU₀32.trans (h1 ▸ Nat.mul_le_mul_left _ hcard)
  omega

end Hyp6Sec2

end CFSG.Quasithin.H13
