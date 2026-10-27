module

public import CFSG.LargeExtraspecial.A2ModFrBKlein
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputsBlock
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType

open Matrix CFSG.RankThree.PartOne.K159 CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.SpecialLinear CFSG.RankThree.CALinearPlane
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

noncomputable def tv03 (t : K) : SpecialLinearGroup (Fin 4) K :=
  SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) t

omit [CharP K 2] in
theorem coe_tv03 (t : K) :
    (tv03 t : Matrix (Fin 4) (Fin 4) K) = 1 + Matrix.single 0 3 t := by
  rw [tv03, SpecialLinearGroup.transvection_coe]

abbrev rootR (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 4) K) :=
  rootGroup K (by decide : (0 : Fin 4) ≠ 3)

omit [CharP K 2] in
theorem tv03_mem_rootR (t : K) : tv03 t ∈ rootR K := by
  rw [rootR]
  exact CFSG.ClassicalGroups.SpecialLinear.transvection_mem_rootGroup (by decide : (0 : Fin 4) ≠ 3) t

theorem slRootGroup_isElemAbelian {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) : CFSG.Open.IsElemAbelian 2 (rootGroup K hij) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    obtain ⟨x, hx⟩ := (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup (K := K) (hij := hij)).mp a.2
    obtain ⟨y, hy⟩ := (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup (K := K) (hij := hij)).mp b.2
    rw [← hx, ← hy]
    rw [← SpecialLinearGroup.transvection_add, ← SpecialLinearGroup.transvection_add]
    congr 1
    exact add_comm x y
  · intro x hx
    obtain ⟨c, hc⟩ := (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup (K := K) (hij := hij)).mp hx
    rw [← hc, pow_two, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero]

omit [CharP K 2] in
theorem slRootGroup_card {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) : Nat.card (rootGroup K hij) = Nat.card K := by
  change Nat.card (CFSG.ClassicalGroups.SpecialLinear.rootHom K hij).range = Nat.card K
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (CFSG.ClassicalGroups.SpecialLinear.rootHom_injective hij)]
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd]

theorem rootR_isElemAbelian : CFSG.Open.IsElemAbelian 2 (rootR K) :=
  slRootGroup_isElemAbelian (K := K) (by decide : (0 : Fin 4) ≠ 3)

omit [CharP K 2] in
theorem rootR_card (hK : Nat.card K = 4) : Nat.card (rootR K) = 4 := by
  rw [rootR, slRootGroup_card (by decide : (0 : Fin 4) ≠ 3), hK]

theorem rootR_not_le_center :
    ¬ rootR K ≤ Subgroup.center (SpecialLinearGroup (Fin 4) K) := by
  intro hle
  have hmem : tv03 (1 : K) ∈ Subgroup.center (SpecialLinearGroup (Fin 4) K) :=
    hle (tv03_mem_rootR (1 : K))
  rw [CFSG.RankThree.PartOne.K159.Klein.center_sl4_eq_bot] at hmem
  have hbot : tv03 (1 : K) = 1 := Subgroup.mem_bot.mp hmem
  have hne : tv03 (1 : K) ≠ 1 := by
    intro h
    have h0 : (1 : SpecialLinearGroup (Fin 4) K) =
        SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) (0 : K) :=
      (SpecialLinearGroup.transvection_coeff_zero (by decide : (0 : Fin 4) ≠ 3)).symm
    rw [h0] at h
    exact one_ne_zero (SpecialLinearGroup.transvection_injective
      (by decide : (0 : Fin 4) ≠ 3) h)
  exact hne hbot

section OrderFiveCentralizers

private lemma eq_one_of_conj_eq_mul_center_of_orderFive
    {X : Type*} [Group X] {a z g : X} (ha : orderOf a = 5)
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z ∣ 3)
    (h : g * a * g⁻¹ = a * z) : z = 1 := by
  have hcomm : Commute a z := Subgroup.mem_center_iff.mp hz a
  have hleft : (g * a * g⁻¹) ^ 5 = 1 := by
    rw [conj_pow, show a ^ 5 = 1 by rw [← ha, pow_orderOf_eq_one], mul_one, mul_inv_cancel]
  have hright : (a * z) ^ 5 = z ^ 5 := by
    rw [hcomm.mul_pow, show a ^ 5 = 1 by rw [← ha, pow_orderOf_eq_one], one_mul]
  have hp : (g * a * g⁻¹) ^ 5 = (a * z) ^ 5 := congrArg (fun x => x ^ 5) h
  have hzpow : z ^ 5 = 1 := by
    rw [← hright, ← hp]
    exact hleft
  have hdvd5 : orderOf z ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hzpow
  have hdvd1 : orderOf z ∣ 1 := by
    have hg : Nat.gcd 5 3 = 1 := by norm_num
    simpa [hg] using Nat.dvd_gcd hdvd5 hz3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

theorem sl6_centralizer_eq_map_of_orderFive
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {Q : Type} [Group Q] [Finite Q]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    (hrange : ψ.range = ⊤)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    :
    Subgroup.centralizer ({ψ a} : Set Q) =
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))).map ψ := by
  classical
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  have hcenterCard : Nat.card (Subgroup.center X) = 3 := by
    dsimp [X]
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
    norm_num
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ ψ.range := by rw [hrange]; exact Subgroup.mem_top y
    rwa [MonoidHom.mem_range] at hy
  apply le_antisymm
  · intro q hq
    obtain ⟨g, rfl⟩ := hsurj q
    rw [Subgroup.mem_centralizer_singleton_iff] at hq
    let z : X := a⁻¹ * (g * a * g⁻¹)
    have hzker : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [z]
      simp only [map_mul, MonoidHom.map_inv]
      rw [hq]
      group
    have hzcenter : z ∈ Subgroup.center X := hker hzker
    have hzle : Subgroup.zpowers z ≤ Subgroup.center X := by
      intro w hw
      rw [Subgroup.mem_zpowers_iff] at hw
      obtain ⟨k, rfl⟩ := hw
      exact Subgroup.zpow_mem (K := Subgroup.center X) hzcenter k
    have hz3 : orderOf z ∣ 3 := by
      have hcard : Nat.card (Subgroup.zpowers z) ∣ Nat.card (Subgroup.center X) :=
        Subgroup.card_dvd_of_le hzle
      rwa [Nat.card_zpowers, hcenterCard] at hcard
    have hconj : g * a * g⁻¹ = a * z := by
      dsimp [z]
      group
    have hz1 : z = 1 :=
      eq_one_of_conj_eq_mul_center_of_orderFive ha hzcenter hz3 hconj
    have hga : g * a * g⁻¹ = a := by simpa [hz1] using hconj
    refine ⟨g, ?_, rfl⟩
    change g ∈ Subgroup.centralizer ({a} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      g * a = (g * a * g⁻¹) * g := by group
      _ = a * g := by rw [hga]
  · rintro _ ⟨g, hg, rfl⟩
    change g ∈ Subgroup.centralizer ({a} : Set X) at hg
    change ψ g ∈ Subgroup.centralizer ({ψ a} : Set Q)
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    simpa only [map_mul] using congrArg ψ hg

end OrderFiveCentralizers

end CFSG.StandardType

end
