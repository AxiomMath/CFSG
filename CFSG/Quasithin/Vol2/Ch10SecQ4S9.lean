module

public import CFSG.Quasithin.Vol2.Ch10SecQ4S8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.Quasithin.Vol2.Ch10SecQ4S5
public import CFSG.Quasithin.Vol2.Ch10SecQ4S7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem vz_facts (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) :
    IsElemAbelian 2 (VZ T H) ∧ VZ T H ≤ pCoreOf 2 H ∧
      pCoreOf 2 H ≤ Subgroup.centralizer (VZ T H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := SecB.minParabolic_of_isHStar h331 hyp hH
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hchar : CharTwo H := charTwo_of_inH hyp.fsu.qtke.2.1 S (hS ▸ hH.1)
  obtain ⟨-, hel, hW⟩ := conjClosure_isTwoReducedIn_of_charTwo hmp.isSylow hchar
    (le_refl (quasithinOmegaOneCenter T))
  have hV2 : IsPGroup 2 ↥(VZ T H) := fun g => ⟨1, Subtype.ext (by simpa using hel.2 g g.2)⟩
  refine ⟨hel, CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hW.1 hW.2.1 hV2, ?_⟩
  refine hW.2.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) fun d hd => ?_
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [hk']
  exact Subgroup.one_mem _

theorem exists_A5Block_H (he23 : E2.E23Statement) (he234 : E2.E23FourStatement)
    (h1021 : Ch10.Stmt10_2_1) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hn3 : ¬ Ch10.Case10_1_1Three T L I)
    (hsyl : ¬ IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T))
    (hbot : pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) = ⊥) :
    ∃ K ∈ cComp H, IsShort2 K ∧ IsAltType K 5 ∧ H = K ⊔ T := by
  obtain ⟨K, hKc, hKs, hty, hKT⟩ :=
    exists_block_H he23 he234 h1021 h331 hyp hH hZH hn3 hsyl hbot
  refine ⟨K, hKc, hKs, ?_, hKT⟩
  rcases hty with ⟨n, hn, hlin⟩ | h5
  · exfalso
    obtain ⟨hel, hc⟩ := C10E4.e23Concl_H he23 h1021 h331 hyp hH hZH hn3
    obtain ⟨I', hcard, hJ, hcomm, -, hA5⟩ := C10E4.isA5Module_of_not_isSylowTwoOf hc hsyl
    obtain ⟨K₀, hK₀⟩ := Finset.card_pos.mp (by omega : 0 < I'.card)
    have h2J : oTwoUpper H ≤ thompsonJ H := SecE.twoResidual_eq_oTwoUpper H ▸ hc.1
    have hHN : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
    obtain ⟨t, ht, hle⟩ := exists_le_autI_map hel hHN hyp.fsu.sylow.1 hKc hKT h2J hJ hcomm hK₀
      (hA5 K₀ hK₀)
    obtain ⟨-, hVO, hO⟩ := vz_facts h331 hyp hH
    have hTH : T ≤ H := hKT ▸ le_sup_right
    have hKtc : K.map (MulAut.conj t).toMonoidHom ∈ cComp H :=
      H13.LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer (hTH ht))
    exact false_of_isLin2Type hel hHN hVO hO hKtc (hA5 K₀ hK₀) hle (by omega : 1 ≤ n)
      ((Lin2.isLin2Type_map_equiv_iff (MulAut.conj t) K n).mpr hlin)
  · exact h5

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
