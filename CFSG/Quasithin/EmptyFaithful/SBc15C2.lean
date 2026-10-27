module

public import CFSG.Quasithin.EmptyFaithful.SBc15Weak
public import CFSG.Quasithin.EmptyFaithful.SBc15C2Aut
public import CFSG.Quasithin.EmptyFaithful.SBc15C2Dec
public import CFSG.Quasithin.Vol2.Ch10SecKHLk2C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc15

theorem input14616ParabolicTwo_proved : Input14616ParabolicTwo := by
  intro G _ _ T M S H PQ p hred hp hC H₀ H₁ H₂ t hdec
  obtain ⟨-, hKc, n, hn, ⟨ι⟩⟩ := hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTG
  have hKG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := SBc13.kz_le_mcOf S hred
  have hKn : mcOf T ≤ Subgroup.normalizer (conjClosure (oTwoUpper H) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hXK : oTwoUpper H ≤ conjClosure (oTwoUpper H) (mcOf T) := le_conjClosure _ _
  have hUX : T ⊓ conjClosure (oTwoUpper H) (mcOf T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    inf_le_left.trans (hTH.trans (le_normalizer_oTwoUpper H))
  have hU : IsSylowTwoOf (T ⊓ conjClosure (oTwoUpper H) (mcOf T))
      (conjClosure (oTwoUpper H) (mcOf T)) := B6.isSylowTwoOf_inf_normal hTsyl hKG hKn
  let ψ : ↥(mcOf T) →* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(mcOf T)))
  have hψ : Function.Surjective ψ := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 ψ.ker := by
    refine (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 (CFSG.Open.pCore 2 ↥(mcOf T))).to_le fun x hx => ?_
    have hx' : ι (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(mcOf T)) x) = 1 := hx
    rw [map_eq_one_iff _ ι.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  let j : ↥(conjClosure (oTwoUpper H) (mcOf T)) →* ↥(mcOf T) := Subgroup.inclusion hKG
  have hj : Function.Injective j := Subgroup.inclusion_injective hKG
  have hjn : j.range.Normal := by
    rw [Subgroup.inclusion_range]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hKn
  have : Group.IsPerfect ↥(conjClosure (oTwoUpper H) (mcOf T)) :=
    Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKc)
  have : Nontrivial ↥(conjClosure (oTwoUpper H) (mcOf T)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (ne_bot_of_mem_cComp hKc)
  obtain ⟨θ, hθ, hθker⟩ := exists_theta_sl hn ψ hψ hker j hj hjn
  refine ⟨fun g hg => ?_, fun k hk hw => ?_⟩
  ·
    have hP2 : IsPGroup 2 ↥(T.subgroupOf (mcOf T)) :=
      hTsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTG).symm
    obtain ⟨k, y, hy, hgky⟩ := exists_mul_eq_sl hn ψ hψ hker j hj hjn hP2 hTsyl.2.2 ⟨g, hg⟩
    exact ⟨(k : G), k.2, (y : G), hy, congrArg Subtype.val hgky⟩
  · exact CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.mem_sup_of_conj_le_of_le hn hθ hθker hU hXK hUX
      (relIndex_pCoreOf_oTwoUpper_eq_nine S hred hp hdec) hk hw

end SBc15

end CFSG.Quasithin
