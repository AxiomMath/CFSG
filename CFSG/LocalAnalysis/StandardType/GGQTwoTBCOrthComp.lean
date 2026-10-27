module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerFixed
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.S11d.OrthLayer
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.StandardType

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne (piOrth piOrth_injective centralizerImage_eq
  map_centralizer_eq_centralizerImage)
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix (inner_comp_cases dims dims'
  orthDerived_not_quasisimple_small orthDerived_not_quasisimple_le_two
  orthDerived_quasisimple_normal_eq_top_of_minus_four)

theorem ggTBC_orth_comp_cases {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n)
    {d : V ≃ₗ[F] V} (hdΩ : d ∈ orthDerived Q) (hd3 : orderOf d = 3)
    {J : Subgroup (V ≃ₗ[F] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {d})) :
    J = specialBlock Q d (X ^ 2 + X + 1) ∨
      (J = supportedFixedDerived Q d ∧
        (6 ≤ Module.finrank F (fixedSpace d) ∨
          (Module.finrank F (fixedSpace d) = 4 ∧
            ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace d).subtype)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := h
    have h1 : d = 1 := LinearEquiv.ext fun v => Subsingleton.elim (d v) v
    rw [h1, orderOf_one] at hd3
    omega
  have := hnt
  have hx3 : orderOf (⟨d, hdΩ⟩ : ↥(orthDerived Q)) = 3 :=
    (Subgroup.orderOf_coe ⟨d, hdΩ⟩).symm.trans hd3
  have hcen : (orthDerived Q ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V))).subgroupOf
      (orthDerived Q) = Subgroup.centralizer ({⟨d, hdΩ⟩} : Set ↥(orthDerived Q)) := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun hz => Subtype.ext hz.2, fun hz => ⟨z.2, Subtype.ext_iff.mp hz⟩⟩
  have hJH : J ≤ orthDerived Q := hJ.1.trans inf_le_left
  have hJsub : CFSG.Assembly.IsComponentOf (J.subgroupOf (orthDerived Q))
      (Subgroup.centralizer ({⟨d, hdΩ⟩} : Set ↥(orthDerived Q))) := by
    have h1 := ggIsComponentOf_subgroupOf_of_le (orthDerived Q) hJH hJ
    rwa [hcen] at h1
  have hL : CFSG.Open.IsComponentOf ((J.subgroupOf (orthDerived Q)).map (piOrth Q))
      (Subgroup.centralizer ({piOrth Q ⟨d, hdΩ⟩} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJsub
      (piOrth Q) (piOrth_injective hQ)
    rw [map_centralizer_eq_centralizerImage, centralizerImage_eq hQ] at h1
    exact CFSG.Assembly.isComponentOf_iff_open.mp h1
  rcases inner_comp_cases (K := F) (Or.inl hF) hQ ⟨d, hdΩ⟩ hx3 hL with
    ⟨-, hq, hLJ⟩ | ⟨P, hPq, hPle, hPn, hPdim, hLP⟩
  ·
    left
    have hsp : specialBlock Q d (X ^ 2 + X + 1) ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer (X ^ 2 + X + 1)).trans
          fun _ hg => (Subgroup.mem_inf.mp hg).1)
    have hEq : (J.subgroupOf (orthDerived Q)).map (piOrth Q) =
        ((specialBlock Q d (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)).map (piOrth Q) := by
      rw [hLJ]
      rfl
    have hEq' : J.subgroupOf (orthDerived Q) =
        (specialBlock Q d (X ^ 2 + X + 1)).subgroupOf (orthDerived Q) := by
      rw [← Subgroup.comap_map_eq_self_of_injective (f := piOrth Q) (piOrth_injective hQ)
        (J.subgroupOf (orthDerived Q)), hEq]
      exact Subgroup.comap_map_eq_self_of_injective (piOrth_injective hQ) _
    have h := Subgroup.subgroupOf_inj.1 hEq'
    rwa [inf_eq_left.2 hJH, inf_eq_left.2 hsp] at h
  ·
    have hx1 : d ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hd3
      omega
    have hpl : (3 : ℕ) ≠ ringChar F := by
      rw [ringChar.eq F 2]
      norm_num
    have hx : OddOrderIsometry Q 3 d :=
      oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ ⟨d, hdΩ⟩ hx3
    have hpq : 3 ∣ Nat.card F + 1 := by
      rw [hF]
    obtain ⟨-, s, hs, -, htype⟩ := dims' hx hpq hx1 hdim
    have hPΩ : P ≤ orthDerived Q := hPle.trans hx.supportedFixedDerived_le_orthDerived
    have hEq' : J.subgroupOf (orthDerived Q) = P.subgroupOf (orthDerived Q) := by
      rw [← Subgroup.comap_map_eq_self_of_injective (f := piOrth Q) (piOrth_injective hQ)
        (J.subgroupOf (orthDerived Q)), hLP]
      exact Subgroup.comap_map_eq_self_of_injective (piOrth_injective hQ) _
    have hJeq : J = P := by
      have h := Subgroup.subgroupOf_inj.1 hEq'
      rwa [inf_eq_left.2 hJH, inf_eq_left.2 hPΩ] at h
    let e := supportedFixedDerivedEquiv hx
    let N : Subgroup ↥(orthDerived (Q.comp (fixedSpace d).subtype)) :=
      (P.subgroupOf (supportedFixedDerived Q d)).map
        (e : ↥(supportedFixedDerived Q d) →* ↥(orthDerived (Q.comp (fixedSpace d).subtype)))
    have hNn : N.Normal := hPn.map
      (e : ↥(supportedFixedDerived Q d) →* ↥(orthDerived (Q.comp (fixedSpace d).subtype)))
      e.surjective
    have hNq : CFSG.IsQuasisimple ↥N :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe hPle).symm.trans (e.subgroupMap _)) hPq
    rcases Nat.lt_or_ge s 3 with hlt | hs3
    · rcases Nat.lt_or_ge s 2 with h1 | h2
      ·
        exact (orthDerived_not_quasisimple_le_two hx.polarBilin_fixed_nondegenerate hs
          (by omega) N hNn hNq).elim
      ·
        have hs2 : s = 2 := by omega
        by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
            (Q.comp (fixedSpace d).subtype)
        · exact (orthDerived_not_quasisimple_small (W := fixedSpace d)
            (R := Q.comp (fixedSpace d).subtype) hx.polarBilin_fixed_nondegenerate hs
            (fun _ => ⟨fun _ => hs2.symm ▸ even_two, fun _ => hplus⟩)
            (Or.inr ⟨hs2, hF⟩) N hNn hNq).elim
        ·
          have htop : N = ⊤ :=
            orthDerived_quasisimple_normal_eq_top_of_minus_four
              hx.polarBilin_fixed_nondegenerate (by rw [hs, hs2]) hplus N hNn hNq
          have htop' : P.subgroupOf (supportedFixedDerived Q d) = ⊤ := by
            refine le_antisymm le_top ?_
            intro x _
            have hxN : e x ∈ N := by rw [htop]; exact Subgroup.mem_top _
            obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxN
            rwa [e.injective hyx] at hy
          exact Or.inr ⟨hJeq.trans
            (le_antisymm hPle (Subgroup.subgroupOf_eq_top.mp htop')),
            Or.inr ⟨by rw [hs, hs2], hplus⟩⟩
    ·
      have hPs : P = supportedFixedDerived Q d := by
        rcases hPdim with h4 | h
        · change Module.finrank F (fixedSpace d) ≤ 4 at h4
          rw [hs] at h4
          omega
        · exact h
      exact Or.inr ⟨hJeq.trans hPs, Or.inl (by rw [hs]; omega)⟩

end CFSG.StandardType

end
