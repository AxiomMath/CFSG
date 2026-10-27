module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9G8
public import CFSG.Quasithin.Vol2.Ch10SecQ9H6
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix CFSG.QuasithinUnique

theorem card_eq_64_of_sylow {S : Subgroup SL4} (hS : IsSylowTwoOf S ⊤) : Nat.card S = 64 := by
  obtain ⟨-, hp, hi⟩ := hS
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hidx : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [hidx] at hi
  have h := S.card_mul_index
  rw [hm, card_SL_four_two] at h
  have hm14 : m ≤ 14 := by
    by_contra hc
    have : 2 ^ 15 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < S.index := Nat.pos_of_ne_zero fun h0 => by rw [h0] at h; omega
    nlinarith
  rw [hm]
  interval_cases m <;> omega

theorem card_mulAut_SL3_le :
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ≤ 336 := by
  let F : GL (Fin 3) (ZMod 2) × Bool → MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    fun p => if p.2 then
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) p.1 *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 (ZMod 2)
      else CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) p.1
  have hF : Function.Surjective F := fun α => by
    rcases CFSG.QuasithinUnique.Setup.Family.aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
    · exact ⟨(A, false), hA.symm⟩
    · exact ⟨(A, true), hA.symm⟩
  have hGL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
    rw [← Nat.card_congr (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).toEquiv,
      card_SL_three_two]
  calc Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
      ≤ Nat.card (GL (Fin 3) (ZMod 2) × Bool) := Nat.card_le_card_of_surjective F hF
    _ = 336 := by rw [Nat.card_prod, hGL, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

theorem inf_centralizer_ne_bot {X S : Subgroup SL4} (hS64 : Nat.card S = 64)
    (hSX : S ≤ Subgroup.normalizer (X : Set SL4))
    (e : ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    S ⊓ Subgroup.centralizer (X : Set SL4) ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card (MulAut ↥X) ≤ 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact card_mulAut_SL3_le
  set S' := S.subgroupOf (Subgroup.normalizer (X : Set SL4))
  set φ := X.normalizerMonoidHom.comp S'.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h2 : (s : ↥(Subgroup.normalizer (X : Set SL4))) ∈ X.normalizerMonoidHom.ker := hs
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    have h3 : ((s : ↥(Subgroup.normalizer (X : Set SL4))) : SL4) ∈
        S ⊓ Subgroup.centralizer (X : Set SL4) := ⟨Subgroup.mem_subgroupOf.mp s.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subtype.ext (Subtype.ext h3)
  have hS' : Nat.card S' = 64 := by
    rw [← hS64]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have h64 : 64 ∣ Nat.card (MulAut ↥X) := by
    have h := Subgroup.card_subgroup_dvd_card (φ.range)
    rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hS'] at h
  have hc : Subgroup.center ↥X = ⊥ := by
    have h := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [center_SL_eq_bot 3, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have hinj : Function.Injective (MulAut.conj : ↥X →* MulAut ↥X) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.mpr fun y => by
      have := congrArg (fun α : MulAut ↥X => α y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [hc, Subgroup.mem_bot] at hxc
    exact hxc
  have hX : Nat.card ↥X = 168 := by
    rw [Nat.card_congr e.toEquiv, card_SL_three_two]
  have h168 : 168 ∣ Nat.card (MulAut ↥X) := by
    have h := Subgroup.card_subgroup_dvd_card ((MulAut.conj : ↥X →* MulAut ↥X).range)
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hX] at h
  have hlcm : 1344 ∣ Nat.card (MulAut ↥X) := by
    have := Nat.lcm_dvd h64 h168
    rwa [show Nat.lcm 64 168 = 1344 by norm_num] at this
  have hpos : 0 < Nat.card (MulAut ↥X) := Nat.card_pos
  have := Nat.le_of_dvd hpos hlcm
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
