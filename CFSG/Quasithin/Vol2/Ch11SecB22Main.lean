module

public import CFSG.Quasithin.Vol2.Ch11SecB22Six
public import CFSG.Quasithin.Vol2.Ch11SecBDerived22
public import CFSG.Quasithin.Vol2.Ch11SecB22Four

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem wClos_zero_le_of_G2 (hDG2 : DerivedG2WeakClosure) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) (hG2 : KindG2 L (fsuV T I) n) :
    E3.wClos (fsuV T I) 0 T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ∧
      Subgroup.normalizer (E3.wClos (fsuV T I) 0 T : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      0 < E3.wParam T (fsuV T I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 := isPGroup_fsuV hyp
  have hW : E3.wClos (fsuV T I) 0 T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hA0⟩ := hA
    have hAeq : A = conjSubgroup (fsuV T I) g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).mp hA0
    subst hAeq
    exact le_inf hAT (hDG2 G T L I n hyp hG2 g hAT)
  have hVW : fsuV T I ≤ E3.wClos (fsuV T I) 0 T := by
    have hV1 : conjSubgroup (fsuV T I) 1 = fsuV T I := by
      ext x
      rw [mem_conjSubgroup_iff]
      simp
    refine le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet (fsuV T I) 0 T) => A) (fsuV T I)
      ⟨fsuV_le_T hyp, 1, hV1.symm ▸ le_rfl, by rw [hV1, E3.mQuot_self]⟩ le_rfl
  have hW1 : E3.wClos (fsuV T I) 0 T ≠ ⊥ := fun h =>
    fsuV_ne_bot hyp (le_bot_iff.mp (h ▸ hVW))
  have hLT : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le (L_le_normalizer_fsuV hyp) (T_le_normalizer_fsuV T I)
  have huniq := isUniqueM_normalizer_inf_centralizer h331 h1102 hyp le_rfl hLT
    (fsuV_le_T hyp) (isElemAbelian_fsuV hyp).1 (fsuV_ne_bot hyp)
  have hN := (E3.e3_16_one (S := T) (H := ⊤)
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_top) le_top
    (hyp.fsu.sylow.1.to_le inf_le_left) hW hW1 huniq).2
  refine ⟨hW, hN, ?_⟩
  unfold E3.wParam
  refine lt_of_lt_of_le (zero_lt_one) (le_iInf₂ fun j hj => ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · exact absurd hW hj
  · exact_mod_cast hjp

theorem stmt11_2_2_of (hNF : NatFacts) (hFM : FactMParam) (hFO : FactOddCodim)
    (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt) (hN : FactNot4213) (hFR : FactRootInv)
    (hA2 : FactA2InL) (hFC1 : FactFlagOneCentral) (hG12 : FactG2Twelve)
    (hDG2 : DerivedG2WeakClosure) (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) (h664 : ASInputs.AS_E_6_6_four)
    (h614 : ASInputs.AS_E_6_14) (h3228 : Ch10.TmpL6_3_2_2_eight) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4) (h1114 : Stmt11_1_4) :
    Stmt11_2_2 := by
  intro G _ _ T L I n m V₁ V₂ hyp hV₁ hV₂ hm
  obtain ⟨-, hn, hLV, hVL, hnat, hLM, hMN⟩ := natSetting h1102 hyp
  refine ⟨fun hV => (hFM G L (fsuV T I) _ n m hV hn hLV hVL hnat hm hLM hMN).1,
    fun U hUV hres hk => centralizer_le_of_lt hFM hFO hFH hS44 hN h4213 h311 h63 h612 h664 h614
      h331 h1102 h1103 h1104 hyp hm hUV hres hk,
    rParam_cases hNF hFM hFO hFH hS44 hN hFR h4213 h311 h63 h612 h664 h614 h331 h1102 h1103
      h1104 h1114 hyp hm hV₂,
    fun hV => sParam_eq hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331 h1102 h1103 hyp hm hV,
    fun j hj => wClos_le_TL hFM hFH hS44 hN hA2 hFC1 h4213 h311 h63 h664 h614 h3228 h331 h1102
      h1103 hyp hm hV₁ j hj,
    fun hG2 => wClos_zero_le_of_G2 hDG2 h331 h1102 hyp hG2,
    fun hG2 => centralizer_cClos_le hNF hFM hFH hS44 hN hG12 h4213 h311 h63 h664 h614 h331
      h1102 h1103 h1114 hyp hV₁ hG2⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
