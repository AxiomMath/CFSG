module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Syl
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

section PGroup

variable {G : Type} [Group G] [Finite G]

theorem eq_of_inf_normalizer_le {R Q : Subgroup G} (hR : IsPGroup 2 ↥R) (hQR : Q ≤ R)
    (hN : R ⊓ Subgroup.normalizer (Q : Set G) ≤ Q) : Q = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne (le_antisymm hQR ?_)
    exact Subgroup.subgroupOf_eq_top.1 h
  have : Group.IsNilpotent ↥R := hR.isNilpotent
  have hU := Group.normalizerCondition_of_isNilpotent (Q.subgroupOf R) hlt
  obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.exists_of_lt hU
  apply hxQ
  have hxN : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : (⟨y, hQR hy⟩ : ↥R) ∈ Q.subgroupOf R := hy
      have h2 := (Subgroup.mem_normalizer_iff.1 hx _).1 h1
      exact h2
    · intro hy
      have hyR : y ∈ R := by
        have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ R :=
          R.mul_mem (R.mul_mem (R.inv_mem x.2) (hQR hy)) x.2
        simpa [mul_assoc] using h1
      have h1 : x * (⟨y, hyR⟩ : ↥R) * x⁻¹ ∈ Q.subgroupOf R := hy
      exact (Subgroup.mem_normalizer_iff.1 hx _).2 h1
  exact hN ⟨x.2, hxN⟩

end PGroup

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem Mv_le_normalizer_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) :
    Subgroup.normalizer (L : Set G) ⊓ Gv v ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨-, -, hTI, -⟩ := S126L20.facts h1222 hH
  rintro c ⟨hcM, hcv⟩
  exact S126N.mem_normalizer_of_TI hTI hv hv1 hcM (Subgroup.mem_centralizer_singleton_iff.1 hcv)

omit [Finite G] in
theorem v_ne_one (F : Frame126 T L V) {v : G} (hv : v ∈ V)
    (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) : v ≠ 1 := by
  have hnv : IsNonsing (F.β ⟨v, hv⟩) := hβ ▸ ⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩
  exact fun h => ne_one_of_nonsing hnv (by
    rw [show (⟨v, hv⟩ : ↥V) = 1 from Subtype.ext h, map_one])

theorem isSylowTwoOf_Tv_Mv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Tv T v) (Subgroup.normalizer (L : Set G) ⊓ Gv v) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have h := isSylowTwoOf_Tv_of_le h1222 F hH hv hβ (W := Subgroup.normalizer (L : Set G) ⊓
    Subgroup.normalizer (V : Set G))
    (le_inf (sup_le Subgroup.le_normalizer hH.hyp.normalizes) (sup_le hLV hTV)) le_rfl
  have hMv := Mv_le_normalizer_V h1222 hH hv (v_ne_one F hv hβ)
  have e : Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) ⊓ Gv v =
      Subgroup.normalizer (L : Set G) ⊓ Gv v :=
    le_antisymm (inf_le_inf_right _ inf_le_left)
      (fun x hx => ⟨⟨hx.1, hMv hx⟩, hx.2⟩)
  rwa [e] at h

theorem Rsec_eq_Rv (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hN : Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Rsec L Kv S v = Rv T L v := by
  obtain ⟨-, hRvR, -, -, -, -, -, -, -⟩ := hD2 G T L V F v Kv S hC
  have hRS : Rsec L Kv S v ≤ S := centralizerSection_le_left _ _ _
  have hS2 : IsPGroup 2 ↥S := hC.sylow.2.1
  have hSG : S ≤ Gv v := hC.sylow.1
  have hTvM := isSylowTwoOf_Tv_Mv h1222 F hC.hyp hC.mem hC.coord
  have hSM : S ⊓ (Subgroup.normalizer (L : Set G) ⊓ Gv v) = Tv T v :=
    CFSG.QuasithinUnique.IsSylowTwoOf.eq_of_le hTvM (le_inf hC.tv_le hTvM.1) inf_le_right
      (hS2.to_le inf_le_left)
  have hRvR' : Rv T L v ≤ Rsec L Kv S v := hRvR ▸ inf_le_left
  refine (eq_of_inf_normalizer_le (R := Rsec L Kv S v) (Q := Rv T L v) (hS2.to_le hRS) hRvR'
    ?_).symm
  rintro r ⟨hrR, hrN⟩
  have hrT : r ∈ Tv T v := hSM ▸ ⟨hRS hrR, hN hrN, hSG (hRS hrR)⟩
  rw [hRvR]
  exact ⟨hrR, hrT⟩

theorem not_Rsec_le_centralizer (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5)
    (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S)
    (hN : Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ¬ Rsec L Kv S v ≤ Subgroup.centralizer (Usec Kv S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM := (hD5 G T L V F v Kv S hC).2
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, -, -, -, -, hOR, -, -, -⟩ := hD2 G T L V F v Kv S hC
  have hRR := Rsec_eq_Rv h1222 hD2 hC hN
  have hRS : Rsec L Kv S v ≤ S := centralizerSection_le_left _ _ _
  intro hRC
  have hRP : Rsec L Kv S v = pCoreOf 2 (Kv ⊔ S) := by
    refine le_antisymm ?_ hOR
    rw [hO]
    exact le_inf (hRS.trans le_sup_right) hRC
  apply hKM
  intro k hk
  apply hN
  rw [← hRR, hRP]
  exact le_normalizer_pCoreOf 2 _ ((le_sup_left : Kv ≤ Kv ⊔ S) hk)

theorem normalizer_Rsec_le (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) {F : Frame126 T L V}
    {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hN : Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Kv ⊓ Subgroup.normalizer (Rsec L Kv S v : Set G) ≤ Subgroup.normalizer (Lv L v : Set G) := by
  have hRR := Rsec_eq_Rv h1222 hD2 hC hN
  rintro k ⟨hk, hkN⟩
  rw [hRR] at hkN
  have hkM : k ∈ Subgroup.normalizer (L : Set G) := hN hkN
  have hkG : k ∈ Gv v := le_of_mem_cComp hC.cComp hk
  exact normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hkM, Subgroup.le_normalizer hkG⟩)

end S126T2

end CFSG.Quasithin.H13
