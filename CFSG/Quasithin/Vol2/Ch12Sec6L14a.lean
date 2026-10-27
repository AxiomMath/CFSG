module

public import CFSG.Quasithin.Vol2.Ch12Sec6L615
public import CFSG.Quasithin.Vol2.Ch12Sec6L13b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_le_Q_of_not_ff (hD3 : Lemma12_6_6_9) (hD5 : Lemma12_6_11)
    (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hJ : thompsonJ (Tv T v) ≤ Qv T V)
    (hnff : ¬ IsFFModule (autI (isElemAbelian_Usec Kv S) (Kv ⊔ S))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hNJ⟩ := (hD3 G T L V F v Kv S hC).2.2.2.1 hJ
  have hKM := (hD5 G T L V F v Kv S hC).2
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  set X := Kv ⊔ S with hX
  have hU := isElemAbelian_Usec Kv S
  have hKS : X ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S X :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  have hPS : pCoreOf 2 X ≤ S := pCoreOf_KvS_le hC
  have hUX : Usec Kv S ≤ X := (Usec_le Kv S).trans (pCoreOf_le 2 _)
  have hXU : X ≤ Subgroup.normalizer (Usec Kv S : Set G) :=
    (le_normalizer_pCoreOf 2 X).trans (normalizer_le_normalizer_Usec Kv S)
  have hJX : thompsonJ X ≤ Subgroup.centralizer (Usec Kv S : Set G) := by
    rcases B2_7 hU hUX hXU hSX with ⟨h, -⟩ | ⟨-, hFF, -⟩
    · exact h
    · exact absurd hFF hnff
  have hJSP : thompsonJ S ≤ pCoreOf 2 X := by
    rw [hO]
    exact le_inf ((thompsonJ_le_self S).trans le_sup_right)
      ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hSX).trans hJX)
  have hJeq := thompsonJ_eq_of_le hJSP hPS
  apply hKM
  intro k hk
  apply hNJ
  rw [hJeq]
  exact normalizer_le_normalizer_thompsonJ _
    (le_normalizer_pCoreOf 2 X ((le_sup_left : Kv ≤ X) hk))

end S126T2

end CFSG.Quasithin.H13
