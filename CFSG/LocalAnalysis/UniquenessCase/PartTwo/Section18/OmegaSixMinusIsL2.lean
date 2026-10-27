module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusResidual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusStdResidual

import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreOmegaMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus)
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

private theorem hinf_eq_derInf_T2J7 {G : Type} [Group G] (H : Subgroup G) :
    Hinf H = F07.DerInf H := rfl

private theorem conj_Eom_T2J7 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (g : Gom Q) (u w : V) :
    g * Eom Q u w * g⁻¹ = Eom Q (g.app u) (g.app w) := by
  apply Subtype.ext
  exact eichler_conj (elementaryGroup_le_orthogonalGroup Q g.2) u w

private theorem leviSub_commutator_eq_T2J7
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ⁅leviSub (stdP0 F b c), leviSub (stdP0 F b c)⁆ = leviSub (stdP0 F b c) := by
  obtain ⟨eL⟩ := nonempty_leviSub_equiv_statedOmega (F := F) (b := b) (c := c) hirr
    (perpIsMinusTwo_stdP0 F b c)
  have hperfT : Group.IsPerfect ↥(StatedOmega (StatedQuadMinus 2 F b c)) :=
    Subgroup.isPerfect_iff.mpr
      (CFSG.SeitzReduction.F4Pilot.commutator_statedOmega_quadMinus_two (K := F) hirr)
  have hperfL : Group.IsPerfect ↥(leviSub (stdP0 F b c)) :=
    hperfT.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  exact Subgroup.isPerfect_iff.mp hperfL

private theorem pCore_leviSub_eq_bot_T2J7
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    CFSG.pCore 2 ↥(leviSub (stdP0 F b c)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := nonempty_leviSub_equiv_statedOmega (F := F) (b := b) (c := c) hirr
    (perpIsMinusTwo_stdP0 F b c)
  have hT : CFSG.pCore 2 ↥(StatedOmega (StatedQuadMinus 2 F b c)) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedOmega_minus_eq_bot 2
      (m := 2) le_rfl hirr
  have hmap := CFSG.pCore_map_iso 2 eL
  rw [hT] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := CFSG.pCore 2 ↥(leviSub (stdP0 F b c))) (f := eL.toMonoidHom)
    eL.injective).1 hmap

private theorem eom_mul_conj_ne_one_T2J7 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {l : Gom Q} (hl : l ∈ leviSub P) {a : V} (ha : a ∈ P.perp) (hne : l.app a ≠ a) :
    Eom Q P.e a * l * (Eom Q P.e a)⁻¹ * l⁻¹ ≠ 1 := by
  intro hx1
  have h1 : Eom Q P.e a * l * (Eom Q P.e a)⁻¹ = l := by
    have := congrArg (· * l) hx1
    simpa [mul_assoc] using this
  have h2 : Eom Q P.e a * l = l * Eom Q P.e a := by
    calc Eom Q P.e a * l = (Eom Q P.e a * l * (Eom Q P.e a)⁻¹) * Eom Q P.e a := by group
      _ = l * Eom Q P.e a := by rw [h1]
  have hconj : l * Eom Q P.e a * l⁻¹ = Eom Q P.e a := by
    calc l * Eom Q P.e a * l⁻¹ = (Eom Q P.e a * l) * l⁻¹ := by rw [h2]
      _ = Eom Q P.e a := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hconjE : l * Eom Q P.e a * l⁻¹ = Eom Q P.e (l.app a) := by
    have h := conj_Eom_T2J7 l P.e a
    rwa [show l.app P.e = P.e from (app_eq_of_mem_leviSub P hl).1] at h
  have hEom : Eom Q P.e a = Eom Q P.e (l.app a) := hconj.symm.trans hconjE
  have hEich : eichler Q P.e a = eichler Q P.e (l.app a) := congrArg Subtype.val hEom
  have hlapp : l.app a ∈ P.perp := by
    obtain ⟨g', rfl⟩ := hl
    have happ := leviEmb_app P g' (p := 0) (w := a) (Submodule.zero_mem _) ha
    simp only [zero_add] at happ
    rw [happ]
    exact (g'.app ⟨a, ha⟩).2
  have hpol : polar Q P.e a = 0 := (HypPair.mem_perp.1 ha).1
  have hpol' : polar Q P.e (l.app a) = 0 := (HypPair.mem_perp.1 hlapp).1
  obtain ⟨c, hc⟩ := (eichler_eq_eichler_iff hQ P.Q_e P.e_ne_zero hpol hpol').1 hEich
  have hcperp : c • P.e ∈ P.perp := by
    have hmem : l.app a - a ∈ P.perp := P.perp.sub_mem hlapp ha
    have heq : c • P.e = l.app a - a := by rw [hc]; abel
    rwa [heq]
  have hc0 : c = 0 := by
    have h := (HypPair.mem_perp.1 hcperp).2
    rw [polar_smul_right_eq, P.polar_fe, mul_one] at h
    exact h
  rw [hc0, zero_smul, add_zero] at hc
  exact hne hc

theorem isL2_bar2_derInf_std {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Subgroup (Gom (quadMinus 3 F b c))}
    (hLX : leviSub (stdP0 F b c) ≤ X)
    (hXS : X ≤ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e) :
    IsL2 (Bar2 (F07.DerInf X)) (2 * n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := nonempty_leviSub_equiv_statedOmega (F := F) (b := b) (c := c) hirr
    (perpIsMinusTwo_stdP0 F b c)
  have hLperf : ⁅leviSub (stdP0 F b c), leviSub (stdP0 F b c)⁆ = leviSub (stdP0 F b c) :=
    leviSub_commutator_eq_T2J7 hirr
  have hLcore : CFSG.pCore 2 ↥(leviSub (stdP0 F b c)) = ⊥ := pCore_leviSub_eq_bot_T2J7 hirr
  have hT : CFSG.pCore 2 ↥(StatedOmega (StatedQuadMinus 2 F b c)) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedOmega_minus_eq_bot 2
      (m := 2) le_rfl hirr
  have hcardLT : Nat.card (leviSub (stdP0 F b c)) =
      Nat.card ↥(StatedOmega (StatedQuadMinus 2 F b c)) := Nat.card_congr eL.toEquiv
  obtain ⟨eS⟩ := nonempty_bar2_derInf_pointStabilizer_std (F := F) (b := b) (c := c) hirr
  obtain ⟨eX⟩ := nonempty_bar2_derInf_equiv_of_levi
    (T := ↥(StatedOmega (StatedQuadMinus 2 F b c)))
    (P := pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e)
    (L := leviSub (stdP0 F b c)) (X := X) hLX hXS hLperf hLcore hT hcardLT eS
  have hn : 1 ≤ n := by
    have hlt : 1 < Nat.card F := Finite.one_lt_card
    rw [hcard] at hlt
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    simp at hlt
  exact uc22p22d_isL2_of_omegaMinus4 hn hcard b c hirr eX

private theorem exists_ne_one_inf_derInf_Lom_T2J7
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ x ∈ F07.DerInf (pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e) ⊓
      Lom (quadMinus 3 F b c) (stdP0 F b c).e, x ≠ 1 := by
  let Q6 : QuadraticForm F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := quadMinus 3 F b c
  let P : HypPair Q6 := stdP0 F b c
  let S : Subgroup (Gom Q6) := pointStabilizer Q6 P.e
  let U : Subgroup (Gom Q6) := Lom Q6 P.e
  let D : Subgroup (Gom Q6) := F07.DerInf S
  have hP : PerpIsMinusTwo P b c := perpIsMinusTwo_stdP0 F b c
  have hLperf : ⁅leviSub P, leviSub P⁆ = leviSub P := leviSub_commutator_eq_T2J7 hirr
  have hLD : leviSub P ≤ D := by
    have h := uc22p21c_le_Hinf (leviSub_le_pointStabilizer P) hLperf
    rwa [hinf_eq_derInf_T2J7 S] at h
  have hSD : S ≤ Subgroup.normalizer (D : Set (Gom Q6)) := by
    have h := uc22p22m_le_normalizer_Hinf S
    rwa [hinf_eq_derInf_T2J7 S] at h
  haveI : Nontrivial (Gom (Q6.restrict P.perp)) := nontrivial_gom_restrict_perp hirr hP
  obtain ⟨l, hl, a, ha, hla⟩ := exists_mem_leviSub_app_ne P
  have hQ : (polarBilin Q6).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hx_ne : Eom Q6 P.e a * l * (Eom Q6 P.e a)⁻¹ * l⁻¹ ≠ 1 :=
    eom_mul_conj_ne_one_T2J7 hQ P hl ha hla
  have hpol : polar Q6 P.e a = 0 := (HypPair.mem_perp.1 ha).1
  have hrU : Eom Q6 P.e a ∈ U := Eom_mem_Lom hpol
  have hrS : Eom Q6 P.e a ∈ S := Lom_le_pointStabilizer (Q := Q6) P.e hrU
  have hl_enorm : l * (Eom Q6 P.e a)⁻¹ * l⁻¹ ∈ U :=
    conj_mem_Lom_of_mem_pointStabilizer (leviSub_le_pointStabilizer P hl) (U.inv_mem hrU)
  have hxU : Eom Q6 P.e a * l * (Eom Q6 P.e a)⁻¹ * l⁻¹ ∈ U := by
    simpa only [mul_assoc] using U.mul_mem hrU hl_enorm
  have hrlrD : Eom Q6 P.e a * l * (Eom Q6 P.e a)⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.1 (hSD hrS) l).1 (hLD hl)
  have hx_D : Eom Q6 P.e a * l * (Eom Q6 P.e a)⁻¹ * l⁻¹ ∈ D :=
    D.mul_mem hrlrD (D.inv_mem (hLD hl))
  exact ⟨_, ⟨hx_D, hxU⟩, hx_ne⟩

theorem pCoreOf_derInf_pointStabilizer_std_ne_bot (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    pCoreOf 2 (F07.DerInf (pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e)) ≠ ⊥ := by
  let Q6 : QuadraticForm F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := quadMinus 3 F b c
  let P : HypPair Q6 := stdP0 F b c
  let S : Subgroup (Gom Q6) := pointStabilizer Q6 P.e
  let U : Subgroup (Gom Q6) := Lom Q6 P.e
  let D : Subgroup (Gom Q6) := F07.DerInf S
  obtain ⟨x, hx_inf, hx_ne⟩ := exists_ne_one_inf_derInf_Lom_T2J7 hirr
  have hDS : D ≤ S := Subgroup.map_subtype_le (⨅ n : ℕ, derivedSeries ↥S n)
  have hnormU : ∀ x ∈ S, ∀ y ∈ U, x * y * x⁻¹ ∈ U :=
    fun x hx y hy => conj_mem_Lom_of_mem_pointStabilizer hx hy
  have hUp : IsPGroup 2 U := isPGroup_Lom P.e
  have hSD : S ≤ Subgroup.normalizer (D : Set (Gom Q6)) := by
    have h := uc22p22m_le_normalizer_Hinf S
    rwa [hinf_eq_derInf_T2J7 S] at h
  have hle : D ⊓ U ≤ pCoreOf 2 D :=
    CFSG.ClassicalGroups.PCoreSection.le_pCoreOf inf_le_left
      (fun x hx y hy => ⟨D.mul_mem (D.mul_mem hx hy.1) (D.inv_mem hx),
        hnormU x (hDS hx) y hy.2⟩)
      (hUp.to_le inf_le_right)
  intro hbot
  have : x ∈ (⊥ : Subgroup (Gom Q6)) := by
    rw [← hbot]
    exact hle hx_inf
  exact hx_ne (Subgroup.mem_bot.mp this)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
