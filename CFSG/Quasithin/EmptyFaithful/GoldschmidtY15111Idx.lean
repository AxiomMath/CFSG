module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

theorem nonempty_perm_equiv_of_index_three {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsPGroup 2 T) (hidx : T.index = 3) (hn : ¬ T.Normal) :
    Nonempty (K ⧸ CFSG.Open.pCore 2 K ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardα : Nat.card (K ⧸ T) = 3 := by rw [← hidx]; rfl
  let e3 : (K ⧸ T) ≃ Fin 3 := (Finite.equivFin (K ⧸ T)).trans (finCongr hcardα)
  let ρ0 : K →* Equiv.Perm (K ⧸ T) := MulAction.toPermHom K (K ⧸ T)
  let ρ : K →* Equiv.Perm (Fin 3) := e3.permCongrHom.toMonoidHom.comp ρ0
  have hker : ρ.ker = T.normalCore := by
    have hk : ρ.ker = ρ0.ker := by
      ext y
      simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact e3.permCongrHom.map_eq_one_iff
    rw [hk, Subgroup.normalCore_eq_ker]
  have hcoreT : T.normalCore ≤ T := Subgroup.normalCore_le T
  have hidxcore : T.normalCore.index = T.normalCore.relIndex T * 3 := by
    rw [← hidx]
    exact (Subgroup.relIndex_mul_index hcoreT).symm
  have hrange : Nat.card ρ.range = T.normalCore.index := by
    rw [← hker, Subgroup.index_ker]
  have hdvd : Nat.card ρ.range ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card ρ.range
    rwa [gold_card_perm_fin_three] at this
  have hrel1 : T.normalCore.relIndex T ≠ 1 := fun h1 => hn (by
    have h2 : T ≤ T.normalCore := Subgroup.relIndex_eq_one.mp h1
    have heq : T.normalCore = T := le_antisymm hcoreT h2
    rw [← heq]
    infer_instance)
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  have hle6 : Nat.card ρ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hrel2 : T.normalCore.relIndex T = 2 := by
    rw [hrange, hidxcore] at hle6 hpos
    omega
  have hcard6 : Nat.card ρ.range = 6 := by rw [hrange, hidxcore, hrel2]
  have hρ : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcard6, gold_card_perm_fin_three])
  have hker' : ρ.ker = CFSG.Open.pCore 2 K := by
    rw [hker]
    apply le_antisymm
    · have : T.normalCore.Normal := inferInstance
      exact CFSG.LieType.BorelTits.le_pCore 2 this (hT.to_le hcoreT)
    · have hN : (CFSG.Open.pCore 2 K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
      have hodd : ¬ 2 ∣ T.index := by rw [hidx]; decide
      have hle : CFSG.Open.pCore 2 K ≤ T :=
        (CFSG.LieType.BorelTits.pCore_isPGroup (G := K) 2).le_sylow_of_normal (hT.toSylow hodd)
      exact Subgroup.normal_le_normalCore.mpr hle
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker').symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

theorem isSolvable_of_index_three {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsPGroup 2 T) (hidx : T.index = 3) (hn : ¬ T.Normal) : Group.IsSolvable K := by
  obtain ⟨e⟩ := nonempty_perm_equiv_of_index_three hT hidx hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (CFSG.Open.pCore 2 K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : Group.IsNilpotent ↥(CFSG.Open.pCore 2 K) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := K) 2).isNilpotent
  have h2 : Group.IsSolvable ↥(CFSG.Open.pCore 2 K) := inferInstance
  have h3 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have h4 : Group.IsSolvable (K ⧸ CFSG.Open.pCore 2 K) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_subgroup_quotient (CFSG.Open.pCore 2 K)

end Y15111

end CFSG.Quasithin
