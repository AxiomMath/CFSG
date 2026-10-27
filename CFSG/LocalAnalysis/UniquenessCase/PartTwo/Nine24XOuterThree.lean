module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GH74.KGroups.PSL2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Basic
import CFSG.Walter.PSL2Facts.FieldGenerator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.SeitzReduction.LinearPilot
open CFSG.GorensteinWalter

private theorem n924x_conj_eq_one_psl2 {K : Type*} [Field K] [Finite K] {c : PSL2 K}
    (h : MulAut.conj c = 1) : c = 1 := by
  have hc : c ∈ Subgroup.center (PSL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut (PSL2 K) => f x) h
    simp only [MulAut.one_apply, MulAut.conj_apply] at hx
    have hx' : c * x = x * c := by
      calc c * x = (c * x * c⁻¹) * c := by group
        _ = x * c := by rw [hx]
    exact hx'.symm
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot K, Subgroup.mem_bot] at hc
  exact hc

private theorem n924x_hasE9_psl2_of_outer_three {S₀ : Type} [Group S₀] [Finite S₀] {m : ℕ}
    (hS : IsL2 S₀ m) (e : S₀ ≃* PSL2 (GaloisField 2 m))
    {A : Subgroup (MulAut (PSL2 (GaloisField 2 m)))}
    (hA : (MulAut.conj : PSL2 (GaloisField 2 m) →*
      MulAut (PSL2 (GaloisField 2 m))).range ≤ A)
    {g : MulAut (PSL2 (GaloisField 2 m))} (hgA : g ∈ A)
    (hg3 : IsPGroup 3 (Subgroup.zpowers g))
    (hg : g ∉ (MulAut.conj : PSL2 (GaloisField 2 m) →*
      MulAut (PSL2 (GaloisField 2 m))).range) : HasE9 ↥A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set τ : GaloisField 2 m ≃+* GaloisField 2 m :=
    psl2FieldPart (GaloisField 2 m) g with hτdef
  obtain ⟨k, hk⟩ := hg3.exists_orderOf_eq_pow (⟨g, Subgroup.mem_zpowers g⟩)
  rw [Subgroup.orderOf_mk] at hk
  have hτdvd : orderOf τ ∣ 3 ^ k := by
    rw [hτdef, ← hk]
    exact orderOf_map_dvd (psl2FieldPart (GaloisField 2 m)) g
  have hτ3 : IsPGroup 3 (Subgroup.zpowers τ) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rwa [Nat.card_zpowers]
  have hτne : τ ≠ 1 := by
    intro h1
    apply hg
    have h1' : psl2FieldPart (GaloisField 2 m) g = 1 := by rw [← hτdef]; exact h1
    rw [CFSG.Walter.psl2FieldPart_eq_autFieldPart] at h1'
    obtain ⟨x, hx⟩ := CFSG.Quasithin.exists_conj_of_autFieldPart_eq_one
      (K := GaloisField 2 m) h1'
    exact ⟨x, hx.symm⟩
  obtain ⟨b, hb⟩ := hτ3.exists_orderOf_eq_pow (⟨τ, Subgroup.mem_zpowers τ⟩)
  rw [Subgroup.orderOf_mk] at hb
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h0 | h
    · rw [h0, pow_zero] at hb
      exact absurd (orderOf_eq_one_iff.mp hb) hτne
    · exact h
  have hσ'ord : orderOf (τ ^ (3 ^ (b - 1))) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hb1, ← hb, pow_orderOf_eq_one]
    · exact pow_ne_one_of_lt_orderOf (Nat.pow_pos (show (0 : ℕ) < 3 by norm_num)).ne'
        (by rw [hb]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hσ'mem : τ ^ (3 ^ (b - 1)) ∈ Subgroup.zpowers τ :=
    Subgroup.mem_zpowers_iff.mpr ⟨(3 ^ (b - 1) : ℤ), zpow_natCast τ (3 ^ (b - 1))⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hσ'mem
  let hh : MulAut (PSL2 (GaloisField 2 m)) := g ^ j
  have hhA : hh ∈ A := A.zpow_mem hgA j
  have hhfield : psl2FieldPart (GaloisField 2 m) hh = τ ^ (3 ^ (b - 1)) := by
    change psl2FieldPart (GaloisField 2 m) (g ^ j) = τ ^ (3 ^ (b - 1))
    rw [map_zpow, ← hτdef]
    exact hj
  let ψ : MulAut (PSL2 (GaloisField 2 m)) :=
    psl2FieldAut (GaloisField 2 m) (τ ^ (3 ^ (b - 1)))
  have hψfield : psl2FieldPart (GaloisField 2 m) ψ = τ ^ (3 ^ (b - 1)) :=
    psl2FieldPart_psl2FieldAut (GaloisField 2 m) _
  have hψord : orderOf ψ = 3 := by
    change orderOf (psl2FieldAut (GaloisField 2 m) (τ ^ (3 ^ (b - 1)))) = 3
    rw [orderOf_injective (psl2FieldAut (GaloisField 2 m))
      (psl2FieldAut_injective (GaloisField 2 m)) _, hσ'ord]
  have hψout : ψ ∉ (MulAut.conj : PSL2 (GaloisField 2 m) →*
      MulAut (PSL2 (GaloisField 2 m))).range := by
    rintro ⟨x, hx⟩
    have h1 : τ ^ (3 ^ (b - 1)) = 1 := by
      calc τ ^ (3 ^ (b - 1)) = psl2FieldPart (GaloisField 2 m) ψ := hψfield.symm
        _ = psl2FieldPart (GaloisField 2 m) (MulAut.conj x) := by rw [hx]
        _ = 1 := psl2FieldPart_conj (K := GaloisField 2 m) x
    have h2 : orderOf (τ ^ (3 ^ (b - 1))) = 1 := by rw [h1, orderOf_one]
    omega
  have hwfield : psl2FieldPart (GaloisField 2 m) (hh * ψ⁻¹) = 1 := by
    rw [map_mul, map_inv, hhfield, hψfield, mul_inv_cancel]
  have hwInn : hh * ψ⁻¹ ∈ (MulAut.conj : PSL2 (GaloisField 2 m) →*
      MulAut (PSL2 (GaloisField 2 m))).range := by
    rw [CFSG.Walter.psl2FieldPart_eq_autFieldPart] at hwfield
    obtain ⟨x, hx⟩ := CFSG.Quasithin.exists_conj_of_autFieldPart_eq_one
      (K := GaloisField 2 m) hwfield
    exact ⟨x, hx.symm⟩
  have hψA : ψ ∈ A := by
    have hwA : hh * ψ⁻¹ ∈ A := hA hwInn
    have hψeq : ψ = (hh * ψ⁻¹)⁻¹ * hh := by group
    rw [hψeq]
    exact A.mul_mem (A.inv_mem hwA) hhA
  let θ : MulAut S₀ := MulAut.congr e.symm ψ
  have hθord : orderOf θ = 3 := by
    change orderOf (MulAut.congr e.symm ψ) = 3
    rw [MulEquiv.orderOf_eq]
    exact hψord
  have hθout : θ ∉ (MulAut.conj : S₀ →* MulAut S₀).range := by
    intro h
    exact hψout ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e.symm ψ).mp h)
  obtain ⟨-, ⟨e_fix⟩⟩ :=
    uc22s2112r2_fixed_psl2 (p := 2) (f := m) (r := 3) hS Nat.prime_three (by decide)
      hθord hθout
  obtain ⟨d₁, hd₁ord⟩ := CFSG.RankThree.PartTwo.KFacts.exists_orderOf_eq_three_psl2
    (GaloisField 2 (m / 3))
  set d₀ : ↥(CFSG.Open.signalizerFixedSubgroup θ) := e_fix.symm d₁ with hd₀def
  have hθd₀ : θ (d₀ : S₀) = (d₀ : S₀) := d₀.2
  have hd₀ord : orderOf (d₀ : S₀) = 3 := by
    rw [Subgroup.orderOf_coe, hd₀def, MulEquiv.orderOf_eq, hd₁ord]
  let d : PSL2 (GaloisField 2 m) := e (d₀ : S₀)
  have hdord : orderOf d = 3 := by
    change orderOf (e (d₀ : S₀)) = 3
    rw [MulEquiv.orderOf_eq, hd₀ord]
  have hψd : ψ d = d := by
    have h : (MulAut.congr e.symm ψ) (d₀ : S₀) = (d₀ : S₀) := hθd₀
    have h' := congrArg e h
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply] at h'
    change ψ (e (d₀ : S₀)) = e (d₀ : S₀)
    exact h'
  have hcA : MulAut.conj d ∈ A := hA ⟨d, rfl⟩
  have hcord : orderOf (MulAut.conj d) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have hd3 : d ^ 3 = 1 := by rw [← hdord]; exact pow_orderOf_eq_one d
      rw [← map_pow (MulAut.conj : PSL2 (GaloisField 2 m) →*
        MulAut (PSL2 (GaloisField 2 m))) d 3, hd3, map_one]
    · intro h
      have hd1 : d = 1 := n924x_conj_eq_one_psl2 h
      have h13 : (1 : ℕ) = 3 := by simpa [hd1] using hdord
      omega
  have hψcd : ψ * MulAut.conj d * ψ⁻¹ = MulAut.conj d := by
    rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hψd]
  have hcomm : Commute ψ (MulAut.conj d) := by
    rw [commute_iff_eq]
    calc ψ * MulAut.conj d = ψ * MulAut.conj d * ψ⁻¹ * ψ := by group
      _ = MulAut.conj d * ψ := by rw [hψcd]
  have hcnot : MulAut.conj d ∉ Subgroup.zpowers ψ := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hfield1 : (τ ^ (3 ^ (b - 1))) ^ j = 1 := by
      have h := congrArg (psl2FieldPart (GaloisField 2 m)) hj
      rw [map_zpow, hψfield, psl2FieldPart_conj] at h
      exact h
    have h3dvd : (3 : ℤ) ∣ j := by
      have hdvd := (orderOf_dvd_iff_zpow_eq_one (x := τ ^ (3 ^ (b - 1))) (i := j)).mpr
        hfield1
      rwa [hσ'ord] at hdvd
    have hψj : ψ ^ j = 1 := by
      have hd : (orderOf ψ : ℤ) ∣ j := by rw [hψord]; exact h3dvd
      exact (orderOf_dvd_iff_zpow_eq_one (x := ψ) (i := j)).mp hd
    have hconj1 : MulAut.conj d = 1 := by rw [← hj, hψj]
    have hd1 : d = 1 := n924x_conj_eq_one_psl2 hconj1
    have h13 : (1 : ℕ) = 3 := by simpa [hd1] using hdord
    omega
  refine ⟨⟨ψ, hψA⟩, ⟨MulAut.conj d, hcA⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk, hψord]
  · rw [Subgroup.orderOf_mk, hcord]
  · rw [commute_iff_eq]
    exact Subtype.ext_iff.mpr hcomm.eq
  · intro hmem
    apply hcnot
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨j, ?_⟩
    have h := congrArg Subtype.val hj
    simpa using h

theorem hasE9_of_outer_three {S₀ : Type} [Group S₀] [Finite S₀] {m : ℕ} (hS : IsL2 S₀ m)
    {A : Subgroup (MulAut S₀)} (hA : (MulAut.conj : S₀ →* MulAut S₀).range ≤ A)
    {g : MulAut S₀} (hgA : g ∈ A) (hg3 : IsPGroup 3 (Subgroup.zpowers g))
    (hg : g ∉ (MulAut.conj : S₀ →* MulAut S₀).range) : HasE9 ↥A := by
  have hm1 : 1 ≤ m := hS.admissible.2.1
  have hm0 : m ≠ 0 := by omega
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (K := S₀)
    (F := GaloisField 2 m) 2 m (by omega) (GaloisField.card 2 m hm0) hS
  set A' : Subgroup (MulAut (PSL2 (GaloisField 2 m))) :=
    A.map (MulAut.congr e).toMonoidHom with hA'def
  set g' : MulAut (PSL2 (GaloisField 2 m)) := MulAut.congr e g with hg'def
  have hA' : (MulAut.conj : PSL2 (GaloisField 2 m) →*
      MulAut (PSL2 (GaloisField 2 m))).range ≤ A' := by
    rw [hA'def, ← CFSG.RankThree.PartTwo.KFacts.map_innAut_congr e]
    exact Subgroup.map_mono hA
  have hg'A : g' ∈ A' := by
    rw [hg'def, hA'def]
    exact Subgroup.mem_map_of_mem _ hgA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hg3.exists_orderOf_eq_pow (⟨g, Subgroup.mem_zpowers g⟩)
  rw [Subgroup.orderOf_mk] at hk
  have hg'ord : orderOf g' = 3 ^ k := by
    rw [hg'def, MulEquiv.orderOf_eq, hk]
  have hg'3 : IsPGroup 3 (Subgroup.zpowers g') := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers, hg'ord]
  have hg' : g' ∉ (MulAut.conj : PSL2 (GaloisField 2 m) →*
      MulAut (PSL2 (GaloisField 2 m))).range := by
    rw [hg'def]
    exact fun h => hg ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e g).mp h)
  have hE9' := n924x_hasE9_psl2_of_outer_three hS e hA' hg'A hg'3 hg'
  let eA := Subgroup.equivMapOfInjective A (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective
  exact HasE9.map_injective eA.symm.toMonoidHom eA.symm.injective hE9'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
