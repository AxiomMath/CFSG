module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4BorelQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.GroupTheory
open CFSG.QuasithinUnique (IsSylowTwoOf isSylowTwoOf_top_of_sylow)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F11 (Omega1p)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin.H13.Sec53F
open CFSG.Quasithin.H13.Sec53F.Unit
open CFSG.RankThree.CentralLiftU
open CFSG.LocalAnalysis.ComponentInitial

private theorem kt7_u4_case (hU : K_U4CartanRank) {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hn : 2 ≤ n) (heven : Even n) (hY : IsU4 Y n) (S : Sylow 2 Y) :
    IsMulCommutative (normalizerQuotient (S : Subgroup Y)) ∧
      ∃ E : Subgroup (normalizerQuotient (S : Subgroup Y)),
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hq : 2 < 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hS : IsSylowTwoOf (S : Subgroup Y) ⊤ := isSylowTwoOf_top_of_sylow S
  have hcomm : IsMulCommutative (normalizerQuotient (S : Subgroup Y)) :=
    isMulCommutative_normalizerQuotient_u4 hq hY (S : Subgroup Y) hS
  have hdvd : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨m, hm⟩ := heven
    have h4 : 2 ^ n = 4 ^ m := by
      rw [hm, pow_add, ← mul_pow]
      norm_num
    have hd : 3 ∣ 4 ^ m - 1 := by
      simpa using Nat.sub_one_dvd_pow_sub_one 4 m
    simpa [h4] using hd
  obtain ⟨-, hcard, -⟩ :=
    hU Y n hY hq (S : Subgroup Y) hS 3 (by norm_num) (by norm_num) hdvd
  have hEea : IsElemAbelian 3 (Omega1p 3 (⊤ : Subgroup (normalizerQuotient (S : Subgroup Y)))) := by
    refine IsElemAbelian.closure_of_commute
      (s := {x : normalizerQuotient (S : Subgroup Y) | x ∈ ⊤ ∧ x ^ 3 = 1}) ?_ ?_
    · intro a _ b _
      exact hcomm.is_comm.comm a b
    · intro a ha
      exact ha.2
  refine ⟨hcomm, ⟨Omega1p 3 (⊤ : Subgroup (normalizerQuotient (S : Subgroup Y))), hEea, ?_⟩⟩
  simpa using hcard

private noncomputable def u5TorusElt {K : Type} [Field K] (h : UnitaryFieldData 2 2 K)
    (a : Fin 2 → Kˣ) (d : Fin 1 → Kˣ)
    (hd : ∀ k, h.norm ((d k : Kˣ) : K) = 1) (hp : torusRatio h a d = 1) :
    hypTorus h 2 1 :=
  ⟨(torusMat_mem_hypSU h a (d := d) hd hp).choose,
    (torusMat_mem_hypSU h a (d := d) hd hp).choose_spec.1⟩

private theorem u5TorusElt_coe {K : Type} [Field K] (h : UnitaryFieldData 2 2 K)
    (a : Fin 2 → Kˣ) (d : Fin 1 → Kˣ)
    (hd : ∀ k, h.norm ((d k : Kˣ) : K) = 1) (hp : torusRatio h a d = 1) :
    (((u5TorusElt h a d hd hp : hypTorus h 2 1) : hypSU h 2 1) :
        GL (HypIndex 2 1) K) =
      Matrix.diagonal (torusEntries h a d) :=
  (torusMat_mem_hypSU h a (d := d) hd hp).choose_spec.2

private theorem u5TorusElt_pow_three_eq_one {K : Type} [Field K]
    (h : UnitaryFieldData 2 2 K) (a : Fin 2 → Kˣ) (d : Fin 1 → Kˣ)
    (hd : ∀ k, h.norm ((d k : Kˣ) : K) = 1) (hp : torusRatio h a d = 1)
    (h3 : ∀ i, torusEntries h a d i ^ 3 = 1) :
    (u5TorusElt h a d hd hp) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, u5TorusElt_coe h a d hd hp,
    Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact h3 i

private theorem torusEntries_cube_one {K : Type} [Field K] (h : UnitaryFieldData 2 2 K)
    {a : Fin 2 → Kˣ} (ha : ∀ i, ((a i : K)) ^ 3 = 1)
    (hba : ∀ i, h.bar ((a i : K)) = ((a i : K))) :
    ∀ i, torusEntries h a (fun _ : Fin 1 => 1) i ^ 3 = 1 := by
  intro i
  rcases i with i | k | i
  · simpa [torusEntries] using ha i
  · simp [torusEntries]
  · rw [torusEntries]
    rw [hba i, inv_pow, ha i, inv_one]

private theorem exists_elemAbelian_nine_hypTorus {K : Type} [Field K]
    (h : UnitaryFieldData 2 2 K) :
    ∃ E : Subgroup (hypTorus h 2 1), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x ∈ E, (x : hypSU h 2 1) ∈ hypScalars h 2 1 → x = 1 := by
  classical
  have hfin : Finite K := h.finite
  have hfintype : Fintype K := Fintype.ofFinite K
  have hdvdK : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    norm_num
  have hdvdUnits : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hdvdK
  obtain ⟨ζ, hζord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvdUnits
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζord]
    exact pow_orderOf_eq_one ζ
  have hζ3K : ((ζ : K)) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hζ3
  have hζne : ζ ≠ 1 := by
    intro hζ1
    rw [hζ1, orderOf_one] at hζord
    norm_num at hζord
  have hbarζ : h.bar ((ζ : K)) = (ζ : K) := by
    rw [h.bar_apply, show 2 ^ 2 = 4 by norm_num]
    calc (ζ : K) ^ 4 = (ζ : K) ^ 3 * (ζ : K) := by
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
      _ = 1 * (ζ : K) := by rw [hζ3K]
      _ = (ζ : K) := one_mul _
  let d1 : Fin 1 → Kˣ := fun _ => 1
  have hd1 : ∀ k : Fin 1, h.norm ((d1 k : Kˣ) : K) = 1 := fun _ => by
    simp [d1, UnitaryFieldData.norm]
  let aX : Fin 2 → Kˣ := fun i => if i = 0 then ζ else 1
  let aY : Fin 2 → Kˣ := fun i => if i = 0 then 1 else ζ
  have hpX : torusRatio h aX d1 = 1 := by
    rw [torusRatio]
    simp [aX, d1, hbarζ, Fin.prod_univ_two]
  have hpY : torusRatio h aY d1 = 1 := by
    rw [torusRatio]
    simp [aY, d1, hbarζ, Fin.prod_univ_two]
  let xT : hypTorus h 2 1 := u5TorusElt h aX d1 hd1 hpX
  let yT : hypTorus h 2 1 := u5TorusElt h aY d1 hd1 hpY
  have htx0 : tcoord h (0 : Fin 2) xT = ζ := by
    apply Units.ext
    rw [coe_tcoord_of_diag h 0 (u5TorusElt_coe h aX d1 hd1 hpX)]
    simp [torusEntries, aX]
  have htx1 : tcoord h (1 : Fin 2) xT = 1 := by
    apply Units.ext
    rw [coe_tcoord_of_diag h 1 (u5TorusElt_coe h aX d1 hd1 hpX)]
    simp [torusEntries, aX]
  have hty0 : tcoord h (0 : Fin 2) yT = 1 := by
    apply Units.ext
    rw [coe_tcoord_of_diag h 0 (u5TorusElt_coe h aY d1 hd1 hpY)]
    simp [torusEntries, aY]
  have hty1 : tcoord h (1 : Fin 2) yT = ζ := by
    apply Units.ext
    rw [coe_tcoord_of_diag h 1 (u5TorusElt_coe h aY d1 hd1 hpY)]
    simp [torusEntries, aY]
  have haX : ∀ i, ((aX i : K)) ^ 3 = 1 := by
    intro i
    fin_cases i <;> simp [aX, hζ3K]
  have hbaX : ∀ i, h.bar ((aX i : K)) = ((aX i : K)) := by
    intro i
    fin_cases i <;> simp [aX, hbarζ]
  have haY : ∀ i, ((aY i : K)) ^ 3 = 1 := by
    intro i
    fin_cases i <;> simp [aY, hζ3K]
  have hbaY : ∀ i, h.bar ((aY i : K)) = ((aY i : K)) := by
    intro i
    fin_cases i <;> simp [aY, hbarζ]
  have hx3 : xT ^ 3 = 1 :=
    u5TorusElt_pow_three_eq_one h aX d1 hd1 hpX (torusEntries_cube_one h haX hbaX)
  have hy3 : yT ^ 3 = 1 :=
    u5TorusElt_pow_three_eq_one h aY d1 hd1 hpY (torusEntries_cube_one h haY hbaY)
  have hxne : xT ≠ 1 := by
    intro hx1
    rw [hx1, map_one] at htx0
    exact hζne htx0.symm
  have hyne : yT ≠ 1 := by
    intro hy1
    rw [hy1, map_one] at hty1
    exact hζne hty1.symm
  have hxord : orderOf xT = 3 := orderOf_eq_prime hx3 hxne
  have hyord : orderOf yT = 3 := orderOf_eq_prime hy3 hyne
  have hXcard : Nat.card (Subgroup.zpowers xT) = 3 := by
    rw [Nat.card_zpowers, hxord]
  have hyNot : yT ∉ Subgroup.zpowers xT := by
    rintro ⟨k, hk⟩
    have h1 := congrArg (tcoord h (1 : Fin 2)) hk
    rw [map_zpow, hty1, htx1, one_zpow] at h1
    exact hζne h1.symm
  have hcomm : ∀ a ∈ Subgroup.zpowers xT, a * yT = yT * a := by
    intro a ha
    exact Subtype.ext (hypTorus_comm h a.2 yT.2)
  obtain ⟨hEea, hEcard⟩ :=
    isElemAbelian_sup_zpowers_of_commute (r := 3) hXcard hyord hyNot hcomm
  let E3 : Subgroup (hypTorus h 2 1) := Subgroup.zpowers xT ⊔ Subgroup.zpowers yT
  refine ⟨E3, hEea, hEcard, ?_⟩
  intro z hzE hzscal
  obtain ⟨c, -, hc5, hcmat⟩ := mem_normOneScalars.mp hzscal
  have hc5' : c ^ 5 = 1 := by simpa using hc5
  have hcmat' : (((z : hypSU h 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      Matrix.diagonal (fun _ => (c : K)) := by
    have hmat := congrArg (fun g : GL (HypIndex 2 1) K =>
      (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K)) hcmat
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hmat
  have htc0z : tcoord h (0 : Fin 2) z = c := by
    apply Units.ext
    simpa using coe_tcoord_of_diag h 0 hcmat'
  have hmapE3 : E3.map (tcoord h (0 : Fin 2)) ≤ Subgroup.zpowers ζ := by
    change (Subgroup.zpowers xT ⊔ Subgroup.zpowers yT).map (tcoord h (0 : Fin 2)) ≤
      Subgroup.zpowers ζ
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_zpowers, htx0]
    · rw [MonoidHom.map_zpowers, hty0]
      simp
  have hmem : tcoord h (0 : Fin 2) z ∈ Subgroup.zpowers ζ :=
    hmapE3 (Subgroup.mem_map_of_mem _ hzE)
  have hc3 : c ^ 3 = 1 := by
    rw [← htc0z]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hi]
    calc (ζ ^ i) ^ 3 = ζ ^ (i * 3) := (zpow_mul ζ i 3).symm
      _ = ζ ^ ((3 : ℤ) * i) := by rw [mul_comm]
      _ = (ζ ^ (3 : ℤ)) ^ i := zpow_mul ζ 3 i
      _ = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hζ3, one_zpow]
  have hc1 : c = 1 := by
    have h6 : c ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
    have h6' : c ^ 6 = c := by
      rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, hc5', one_mul, pow_one]
    exact h6'.symm.trans h6
  have hz1 : (z : hypSU h 2 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hcmat', hc1]
    simp
  exact Subtype.ext hz1

private theorem u5_case {Y : Type} [Group Y] [Finite Y] (hY : IsU5 Y 2) (S : Sylow 2 Y) :
    IsMulCommutative (normalizerQuotient (S : Subgroup Y)) ∧
      ∃ E : Subgroup (normalizerQuotient (S : Subgroup Y)),
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hY' : LieModel Y .PSU 5 2 2 := hY
  rcases hY' with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hc
    have h : UnitaryFieldData 2 2 K :=
      ⟨Nat.prime_two, by norm_num, by rw [hK, ← pow_mul]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    let e' : hypPSU h 2 1 ≃* Y :=
      (hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm
    have hfinPSU : Finite (hypPSU h 2 1) := Unit.finite_hypPSU_five h
    let D := Unit.borelAutDiag_u5 h
    obtain ⟨eC⟩ := normalizerQuotient_equiv_of_complement D.H_le D.U_inf_H D.B_eq
    obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e'
      (Unit.u5_sylow h) (isSylowTwoOf_top_of_sylow S)
    let e : normalizerQuotient (S : Subgroup Y) ≃* (hypTorus h 2 1).map (hypProj h 2 1) :=
      eN.symm.trans eC
    have hcomm : IsMulCommutative (normalizerQuotient (S : Subgroup Y)) := by
      refine IsMulCommutative.mk (Std.Commutative.mk fun a b => ?_)
      apply e.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (D.H_comm (e a).1 (e a).2 (e b).1 (e b).2)
    obtain ⟨E3, hE3ea, hE3card, hE3inj⟩ := exists_elemAbelian_nine_hypTorus h
    let π : hypTorus h 2 1 →* hypPSU h 2 1 :=
      (hypProj h 2 1).comp (hypTorus h 2 1).subtype
    let F : Subgroup (hypPSU h 2 1) := E3.map π
    have hFea : IsElemAbelian 3 F := hE3ea.map π
    have hFcard : Nat.card F = 9 := by
      have hinj : Function.Injective (π.comp E3.subtype) := by
        rw [injective_iff_map_eq_one]
        intro z hz
        have hscal : (z.1 : hypSU h 2 1) ∈ hypScalars h 2 1 := by
          rw [← ker_hypProj]
          exact hz
        exact Subtype.ext (hE3inj z.1 z.2 hscal)
      have hrange : (π.comp E3.subtype).range = F := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      calc Nat.card F = Nat.card (π.comp E3.subtype).range := by rw [hrange]
        _ = Nat.card E3 := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
        _ = 9 := hE3card
    have hFle : F ≤ (hypTorus h 2 1).map (hypProj h 2 1) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, t.2, rfl⟩
    let Fh : Subgroup ((hypTorus h 2 1).map (hypProj h 2 1)) :=
      F.subgroupOf ((hypTorus h 2 1).map (hypProj h 2 1))
    have hFh_ea : IsElemAbelian 3 Fh := hFea.subgroupOf _
    have hFh_card : Nat.card Fh = 9 := by
      rw [← hFcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFle).toEquiv
    refine ⟨hcomm, ⟨Fh.map e.symm.toMonoidHom, hFh_ea.map e.symm.toMonoidHom, ?_⟩⟩
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hFh_card]
  all_goals exact absurd hn (by norm_num)

theorem kU4U5CartanQuotient_of_U4 (hU : K_U4CartanRank) : KU4U5CartanQuotient := by
  intro Y _ _ n hn heven hY S
  rcases hY with ⟨n', hY4, hn'⟩ | hY5
  · subst n'
    exact kt7_u4_case hU hn heven hY4 S
  · exact u5_case hY5 S

theorem kU4U5CartanQuotient_holds : KU4U5CartanQuotient :=
  kU4U5CartanQuotient_of_U4 k_U4CartanRank_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
