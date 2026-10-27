module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.OddLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.Diag
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.QuotMap
import CFSG.Quasithin.Background.B4L3Coord
import CFSG.Quasithin.Background.Asc81cTenFourA
import CFSG.Quasithin.EmptyFaithful.E22SUGenNeTwo
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module
import CFSG.Quasithin.H13.L32AL2o
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1

open CFSG.Quasithin CFSG.Quasithin.E22S CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

private theorem exists_lift_data {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {Z : Subgroup W} {n : ℕ} {Kf : Type} [Field Kf] [Finite Kf]
    (hn : 2 ≤ n) (hKcard : Nat.card Kf = (2 ^ n) ^ 2) (hZK : StableUnder K Z) (hZ : Z ≤ fixV K)
    (hq : CFSG.Open.IsQuasisimple ↥K) {c : Kfˣ} (hc : c ^ (2 ^ n + 1) = 1) (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) {π : ↥(CFSG.Open.StatedSU 3 (2 ^ n) Kf) →* ↥(autQuot K Z)}
    (hπ : (FFModel.nat (CFSG.Open.StatedSU 3 (2 ^ n) Kf)).RealizesVia (autQuot K Z) ⊤ ⊥ π) :
    ∃ x : Fin 3 → ↥K,
      (∀ k, ((x k : ↥K) : MulAut W) ^ (2 ^ n + 1) = 1) ∧
      (∀ k, fixV (Subgroup.zpowers ((x k : ↥K) : MulAut W)) = Z) ∧
      (∀ j k, Commute ((x j : ↥K) : MulAut W) ((x k : ↥K) : MulAut W)) ∧
      (∀ k, toAutQuot hZK (x k) = π ⟨reflDiag c k, reflDiag_mem hKcard hc k⟩) := by
  classical
  obtain ⟨β, -, hβker, hβeq⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (CFSG.Open.StatedSU 3 (2 ^ n) Kf)) rfl rfl hπ
  let z : Fin 3 → ↥(CFSG.Open.StatedSU 3 (2 ^ n) Kf) :=
    fun k => ⟨reflDiag c k, reflDiag_mem hKcard hc k⟩
  have hzpow : ∀ k, z k ^ (2 ^ n + 1) = 1 := fun k => Subtype.ext (reflDiag_pow_eq_one hc k)
  have hzcomm : ∀ j k, Commute (z j) (z k) := fun j k => Subtype.ext (commute_reflDiag c j k)
  have hm : Odd (2 ^ n + 1) := ((Nat.even_pow' (by omega)).2 even_two).add_one
  have hsq : ∀ a ∈ (toAutQuot hZK).ker, a * a = 1 :=
    fun a ha => mul_self_eq_one_of_mem_ker_toAutQuot hW hZK hZ ha
  have hker : (toAutQuot hZK).ker ≤ Subgroup.center ↥K := ker_toAutQuot_le_center hW hZK hZ hq
  have hex : ∀ k, ∃ y : ↥K, toAutQuot hZK y = π (z k) ∧ y ^ (2 ^ n + 1) = 1 := fun k =>
    exists_pow_odd_lift _ (toAutQuot_surjective hZK) hsq hm (by rw [← map_pow, hzpow k, map_one])
  choose x hxφ hxpow using hex
  have hxpow' : ∀ k, ((x k : ↥K) : MulAut W) ^ (2 ^ n + 1) = 1 := fun k => by
    simpa using congrArg (fun y : ↥K => (y : MulAut W)) (hxpow k)
  have hfp : ∀ k, ∀ u : W ⧸ Z,
      ((toAutQuot hZK (x k) : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u = u → u = 1 := by
    intro k u hu
    let v : Fin 3 → Kf := Multiplicative.toAdd (β ⟨u, Subgroup.mem_top u⟩)
    have harg : ((π (z k) : ↥(autQuot K Z)) : MulAut (W ⧸ Z))
        ((⟨u, Subgroup.mem_top u⟩ : ↥(⊤ : Subgroup (W ⧸ Z))) : W ⧸ Z) =
        ((toAutQuot hZK (x k) : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u :=
      congrArg (fun g : MulAut (W ⧸ Z) =>
        g ((⟨u, Subgroup.mem_top u⟩ : ↥(⊤ : Subgroup (W ⧸ Z))) : W ⧸ Z))
        (congrArg (fun g : ↥(autQuot K Z) => (g : MulAut (W ⧸ Z))) (hxφ k).symm)
    have h1 : β ⟨u, Subgroup.mem_top u⟩ =
        β ⟨((toAutQuot hZK (x k) : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u,
          Subgroup.mem_top _⟩ := by rw [hu]
    have h4 : β ⟨((toAutQuot hZK (x k) : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u,
        Subgroup.mem_top _⟩ =
        (FFModel.nat (CFSG.Open.StatedSU 3 (2 ^ n) Kf)).act (z k)
          (β ⟨u, Subgroup.mem_top u⟩) :=
      harg ▸ hβeq (z k) ⟨u, Subgroup.mem_top u⟩ (Subgroup.mem_top _)
    rw [h4] at h1
    let w : Fin 3 → Kf := Multiplicative.toAdd
      ((FFModel.nat (CFSG.Open.StatedSU 3 (2 ^ n) Kf)).act (z k) (β ⟨u, Subgroup.mem_top u⟩))
    have hvw : v = w :=
      congrArg (fun m : (FFModel.nat (CFSG.Open.StatedSU 3 (2 ^ n) Kf)).Amb =>
        (Multiplicative.toAdd m : Fin 3 → Kf)) h1
    have hw : w = (reflDiag c k : Matrix (Fin 3) (Fin 3) Kf) *ᵥ v := by
      have hwr : w = Multiplicative.toAdd (Multiplicative.ofAdd
          ((reflDiag c k : Matrix (Fin 3) (Fin 3) Kf) *ᵥ v)) := rfl
      rw [hwr, toAdd_ofAdd]
    have h5 : (reflDiag c k : Matrix (Fin 3) (Fin 3) Kf) *ᵥ v = v := (hvw.trans hw).symm
    have hzero : v = 0 := eq_zero_of_reflDiag_mulVec_eq hc1 hc2 k h5
    have hva : β ⟨u, Subgroup.mem_top u⟩ = Multiplicative.ofAdd v :=
      (ofAdd_toAdd (β ⟨u, Subgroup.mem_top u⟩)).symm
    have hβ1 : β ⟨u, Subgroup.mem_top u⟩ = 1 := by rw [hva, hzero]; exact ofAdd_zero
    have hmem : u ∈ (⊥ : Subgroup (W ⧸ Z)) := (hβker _).mp hβ1
    simpa using hmem
  refine ⟨x, hxpow', fun k => fixV_zpowers_eq hZK hZ (hfp k), fun j k => ?_, hxφ⟩
  have hcommK : Commute (x j) (x k) :=
    commute_of_map_commute_of_pow_odd (g := x j) (g₂ := x k) (m := 2 ^ n + 1)
      (toAutQuot hZK) hker hsq hm (hxpow k)
      (by rw [hxφ j, hxφ k]; exact (hzcomm j k).map π)
  exact hcommK.map K.subtype

private theorem mem_stabSub_commSub_of_commute {W : Type} [CommGroup W] {t y : MulAut W}
    (hc : Commute y t) :
    y ∈ stabSub (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  have hconj : (MulAut.conj y) t = t := by
    rw [MulAut.conj_apply, hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hYmap : (Subgroup.zpowers t).map (MulAut.conj y).toMonoidHom = Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hconj
  have hEq : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) =
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)).map y.toMonoidHom := by
    rw [← CFSG.Quasithin.Asc81c.commSub_map_conj (Subgroup.zpowers t) y, hYmap]
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    rw [hEq] at hu
    obtain ⟨p, hp, hpu⟩ := hu
    have hpe : p = u := y.injective hpu
    rwa [hpe] at hp
  · intro hu
    rw [hEq]
    exact Subgroup.mem_map_of_mem y.toMonoidHom hu

private theorem stableUnder_commSub {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {Z : Subgroup W} {n : ℕ} {Kf : Type} [Field Kf] [Finite Kf]
    (hn : 2 ≤ n) (hKcard : Nat.card Kf = (2 ^ n) ^ 2) (hZK : StableUnder K Z) (hZ : Z ≤ fixV K)
    (hq : CFSG.Open.IsQuasisimple ↥K) {c : Kfˣ} (hc : c ^ (2 ^ n + 1) = 1)
    {π : ↥(CFSG.Open.StatedSU 3 (2 ^ n) Kf) →* ↥(autQuot K Z)}
    (hπsurj : Function.Surjective π) {x : Fin 3 → ↥K} {P : Subgroup W}
    (hP : P = commSub (⊤ : Subgroup W) (Subgroup.zpowers ((x 0 : ↥K) : MulAut W)))
    (hxpow : ∀ k, ((x k : ↥K) : MulAut W) ^ (2 ^ n + 1) = 1)
    (hxfix : ∀ k, fixV (Subgroup.zpowers ((x k : ↥K) : MulAut W)) = Z)
    (hxcomm : ∀ j k, Commute ((x j : ↥K) : MulAut W) ((x k : ↥K) : MulAut W))
    (hxφ : ∀ k, toAutQuot hZK (x k) = π ⟨reflDiag c k, reflDiag_mem hKcard hc k⟩) :
    StableUnder K P := by
  classical
  have hm : Odd (2 ^ n + 1) := ((Nat.even_pow' (by omega)).2 even_two).add_one
  have hxpowK : ∀ k, x k ^ (2 ^ n + 1) = 1 := fun k => Subtype.ext (by simpa using hxpow k)
  have hq2 : 2 ^ n ≠ 2 := by
    intro h
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [h] at h4
    norm_num at h4
  have hsq : ∀ a ∈ (toAutQuot hZK).ker, a * a = 1 :=
    fun a ha => mul_self_eq_one_of_mem_ker_toAutQuot hW hZK hZ ha
  have hker : (toAutQuot hZK).ker ≤ Subgroup.center ↥K := ker_toAutQuot_le_center hW hZK hZ hq
  have hPX : ∀ k, commSub (⊤ : Subgroup W) (Subgroup.zpowers ((x k : ↥K) : MulAut W)) = P := by
    intro k
    rw [hP]
    exact CFSG.Quasithin.H13.L32A.L2.commSub_eq_of_fixV_eq (a₁ := ((x k : ↥K) : MulAut W))
      (a₂ := ((x 0 : ↥K) : MulAut W)) (m₁ := 2 ^ n + 1) (m₂ := 2 ^ n + 1) hW hm hm
      (hxpow k) (hxpow 0) (hxcomm k 0) (by rw [hxfix k, hxfix 0])
  let S : Subgroup ↥K := (stabSub P).comap K.subtype
  have hSgen : ∀ k, (suStab Kf (2 ^ n) k).map π ≤ S.map (toAutQuot hZK) := by
    intro k h hh
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨y, hy⟩ := toAutQuot_surjective hZK (π g)
    have hyS : y ∈ S := by
      refine Subgroup.mem_comap.mpr ?_
      rw [← hPX k]
      refine mem_stabSub_commSub_of_commute ?_
      have hgz : Commute g ⟨reflDiag c k, reflDiag_mem hKcard hc k⟩ := by
        show g * ⟨reflDiag c k, reflDiag_mem hKcard hc k⟩ =
          ⟨reflDiag c k, reflDiag_mem hKcard hc k⟩ * g
        exact Subtype.ext (commute_reflDiag_of_mem_suStab hKcard c hg)
      have hcommK : Commute y (x k) :=
        commute_of_map_commute_of_pow_odd (g := y) (g₂ := x k) (m := 2 ^ n + 1)
          (toAutQuot hZK) hker hsq hm (hxpowK k)
          (by rw [hy, hxφ k]; exact hgz.map π)
      exact hcommK.map K.subtype
    rw [← hy]
    exact Subgroup.mem_map_of_mem _ hyS
  have htop : (⨆ k : Fin 3, (suStab Kf (2 ^ n) k).map π) = ⊤ := by
    rw [← Subgroup.map_iSup, E22S.iSup_suStab_eq_top_of_ne_two hq2 hKcard,
      Subgroup.map_top_of_surjective _ hπsurj]
  have htop' : S.map (toAutQuot hZK) = ⊤ := top_le_iff.mp (htop ▸ iSup_le hSgen)
  have hkerS : (toAutQuot hZK).ker ≤ S := by
    intro y hy
    refine Subgroup.mem_comap.mpr ?_
    rw [← hPX 0]
    refine mem_stabSub_commSub_of_commute ?_
    have hcent : y ∈ Subgroup.center ↥K := hker hy
    have hcommK : y * x 0 = x 0 * y := (Subgroup.mem_center_iff.mp hcent (x 0)).symm
    exact congrArg (fun z : ↥K => (z : MulAut W)) hcommK
  have hS : S = ⊤ := by
    calc S = S ⊔ (toAutQuot hZK).ker := (sup_eq_left.mpr hkerS).symm
      _ = (S.map (toAutQuot hZK)).comap (toAutQuot hZK) := (Subgroup.comap_map_eq _ _).symm
      _ = ⊤ := by rw [htop', Subgroup.comap_top]
  intro a ha u hu
  have hmem : (⟨a, ha⟩ : ↥K) ∈ S := by rw [hS]; exact Subgroup.mem_top _
  exact ((mem_stabSub.mp hmem) u).2 hu

private theorem exists_compl_of_realizes {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {n : ℕ} (hK : IsSU3 ↥K n) (hn : 2 ≤ n) {Z : Subgroup W}
    (hZK : StableUnder K Z) (hZ : Z ≤ fixV K) {Kf : Type} [hF : Field Kf] [hFin : Finite Kf]
    (hKcard : Nat.card Kf = (2 ^ n) ^ 2)
    {π : ↥(CFSG.Open.StatedSU 3 (2 ^ n) Kf) →* ↥(autQuot K Z)}
    (hπ : (FFModel.nat (CFSG.Open.StatedSU 3 (2 ^ n) Kf)).RealizesVia (autQuot K Z) ⊤ ⊥ π) :
    ∃ P : Subgroup W, StableUnder K P ∧ P ⊓ Z = ⊥ ∧ P ⊔ Z = ⊤ ∧
      P ≤ commSub (⊤ : Subgroup W) K := by
  obtain ⟨c, hc, hc1, hc2⟩ := exists_pow_two_pow_add_one_eq_one (n := n) (by omega) hKcard
  obtain ⟨x, hxpow, hxfix, hxcomm, hxφ⟩ :=
    exists_lift_data hW hn hKcard hZK hZ hK.1 hc hc1 hc2 hπ
  let P : Subgroup W := commSub (⊤ : Subgroup W) (Subgroup.zpowers ((x 0 : ↥K) : MulAut W))
  have hoddP : Odd (Nat.card (Subgroup.zpowers ((x 0 : ↥K) : MulAut W))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat ((Nat.even_pow' (by omega)).2 even_two).add_one
      (orderOf_dvd_of_pow_eq_one (hxpow 0))
  have hPinf : P ⊓ Z = ⊥ := by
    change commSub (⊤ : Subgroup W) (Subgroup.zpowers ((x 0 : ↥K) : MulAut W)) ⊓ Z = ⊥
    rw [inf_comm, ← hxfix 0]
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_inf_commSub_eq_bot hW hoddP
  have hPsup : P ⊔ Z = ⊤ := by
    change commSub (⊤ : Subgroup W) (Subgroup.zpowers ((x 0 : ↥K) : MulAut W)) ⊔ Z = ⊤
    rw [sup_comm, ← hxfix 0]
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_sup_commSub_eq_top hW hoddP
  have hPK : P ≤ commSub (⊤ : Subgroup W) K :=
    commSub_mono le_rfl (Subgroup.zpowers_le.mpr (x 0).2)
  exact ⟨P, stableUnder_commSub hW hn hKcard hZK hZ hK.1 hc hπ.1 rfl hxpow hxfix hxcomm hxφ,
    hPinf, hPsup, hPK⟩

theorem exists_stableUnder_compl {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {n : ℕ} (hK : IsSU3 ↥K n) (hn : 2 ≤ n) {Z : Subgroup W}
    (hZK : StableUnder K Z) (hZ : Z ≤ fixV K) (hNat : NatSUn (autQuot K Z) ⊤ ⊥ 3 n) :
    ∃ P : Subgroup W, StableUnder K P ∧ P ⊓ Z = ⊥ ∧ P ⊔ Z = ⊤ ∧
      P ≤ commSub (⊤ : Subgroup W) K := by
  obtain ⟨Kf, hKfield, hKfin, hKcard, hReal⟩ := hNat
  obtain ⟨π, hπ⟩ := hReal
  exact exists_compl_of_realizes (K := K) (n := n) (Z := Z) (Kf := Kf) (hF := hKfield)
    (hFin := hKfin) hW hK hn hZK hZ hKcard hπ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1
