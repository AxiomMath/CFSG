module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c1614_invariant_of_realizes {W : Type*} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hR : D.Realizes H U Z) :
    ∀ a ∈ H, ∀ u ∈ U, a u ∈ U := by
  obtain ⟨π, -, -, -, hUinv, -⟩ := hR
  intro a ha u hu
  exact hUinv ⟨a, ha⟩ u hu

theorem s16c1614_exists_moved_of_realizes {W : Type*} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hR : D.Realizes H U Z)
    (hfaith : ∀ γ : D.Gam, γ ≠ 1 → ∃ m ∈ D.sec, m⁻¹ * D.act γ m ∉ D.ker)
    {x : MulAut W} (hx : x ∈ H) (hx1 : x ≠ 1) : ∃ u ∈ U, x u ≠ u := by
  obtain ⟨π, hπ, -, -, hUinv, -, hsec, -, β, hβs, -, hβeq⟩ := hR
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hx⟩
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [map_one] at hγ
    exact hx1 (congrArg Subtype.val hγ).symm
  obtain ⟨m, hm, hmk⟩ := hfaith γ hγ1
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  by_contra hcon
  push Not at hcon
  have hxu : ((π γ : ↥H) : MulAut W) (u : W) = u := by
    rw [hγ]
    exact hcon u u.2
  have hmem : ((π γ : ↥H) : MulAut W) (u : W) ∈ U := hUinv (π γ) u u.2
  have hm' : D.act γ m ∈ D.sec := hsec γ m hm
  have h1 := hβeq γ u ⟨m, hm⟩ hmem hm' hu
  have h2 : (⟨((π γ : ↥H) : MulAut W) (u : W), hmem⟩ : ↥U) = u := Subtype.ext hxu
  rw [h2, hu] at h1
  exact hmk (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1))

theorem s16c1614_invariant_of_alternatingNatural {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ} (h : AlternatingNatural H U Z n) :
    ∀ a ∈ H, ∀ u ∈ U, a u ∈ U :=
  s16c1614_invariant_of_realizes h

theorem s16c1614_invariant_of_binaryNaturalSL {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {d a : ℕ} (h : BinaryNaturalSL H U Z d a) :
    ∀ x ∈ H, ∀ u ∈ U, x u ∈ U := by
  obtain ⟨K, _, _, -, hR⟩ := h
  exact s16c1614_invariant_of_realizes hR

theorem s16c1614_altDn_seven_faithful (γ : ↥(alternatingGroup (Fin 7))) (hγ : γ ≠ 1) :
    ∃ m ∈ (FFModel.altDn 7).sec,
      m⁻¹ * (FFModel.altDn 7).act γ m ∉ (FFModel.altDn 7).ker := by
  classical
  set σ : Equiv.Perm (Fin 7) := (γ : Equiv.Perm (Fin 7)) with hσ
  have hσ1 : σ⁻¹ ≠ 1 := by
    intro h
    apply hγ
    apply Subtype.ext
    exact inv_eq_one.1 h
  obtain ⟨a, ha⟩ : ∃ a : Fin 7, σ⁻¹ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  obtain ⟨b, hb⟩ : ∃ b : Fin 7, σ⁻¹ a = b := ⟨_, rfl⟩
  have key : ∀ a b : Fin 7, ∃ c : Fin 7, c ≠ a ∧ c ≠ b := by decide
  obtain ⟨c, hca, hcb⟩ := key a b
  rw [hb] at ha
  let v : Fin 7 → ZMod 2 := Pi.single a 1 + Pi.single c 1
  refine ⟨Multiplicative.ofAdd v, ?_, ?_⟩
  · show Multiplicative.ofAdd v ∈ G6.coreMod 7
    rw [G6.mem_coreMod]
    simp only [toAdd_ofAdd, v, Pi.add_apply, Finset.sum_add_distrib]
    simp
    decide
  · intro hker
    have hy := Subgroup.mem_inf.1 hker
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy.1
    have hcoord : ∀ i, Multiplicative.toAdd ((G6.allOnes 7) ^ k) i = k • (1 : ZMod 2) := by
      intro i
      rw [toAdd_zpow]
      simp [G6.allOnes]
    have hya : Multiplicative.toAdd
        ((Multiplicative.ofAdd v)⁻¹ * G6.permAct 7 σ (Multiplicative.ofAdd v)) a = 1 := by
      rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply, hb]
      simp only [toAdd_ofAdd, v, Pi.add_apply, Pi.single_apply, hca.symm, ha, hcb.symm, if_true,
        if_false]
      decide
    have hk1 : k • (1 : ZMod 2) = 1 := by
      have h : Multiplicative.toAdd ((G6.allOnes 7) ^ k) a = 1 :=
        (congrArg (fun y : Multiplicative (Fin 7 → ZMod 2) => Multiplicative.toAdd y a) hk).trans
          hya
      rw [← hcoord a]
      exact h
    have hsum : ∑ i, Multiplicative.toAdd ((G6.allOnes 7) ^ k) i = 0 :=
      (Finset.sum_congr rfl (fun i _ =>
        congrArg (fun y : Multiplicative (Fin 7 → ZMod 2) => Multiplicative.toAdd y i) hk)).trans
        ((G6.mem_coreMod).1 hy.2)
    simp only [hcoord, hk1] at hsum
    revert hsum
    decide

theorem s16c1614_natSL_faithful {d : ℕ} {K : Type} [Field K] (γ : ↥(StatedSL d K))
    (hγ : γ ≠ 1) :
    ∃ m ∈ (FFModel.nat (StatedSL d K)).sec,
      m⁻¹ * (FFModel.nat (StatedSL d K)).act γ m ∉ (FFModel.nat (StatedSL d K)).ker := by
  by_contra hcon
  push Not at hcon
  apply hγ
  have hmv : ∀ j : Fin d,
      ((γ : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec
        (Pi.single j (1 : K)) = Pi.single j 1 := by
    intro j
    have h := hcon (Multiplicative.ofAdd (Pi.single j (1 : K))) (Subgroup.mem_top _)
    have h1 : (Multiplicative.ofAdd (Pi.single j (1 : K)) : Multiplicative (Fin d → K))⁻¹ *
        natAct (StatedSL d K) γ (Multiplicative.ofAdd (Pi.single j 1)) = 1 :=
      Subgroup.mem_bot.1 h
    have h2 := inv_mul_eq_one.1 h1
    exact (congrArg Multiplicative.toAdd h2).symm
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h3 := congrFun (hmv j) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h3

theorem s16c1614_moved_of_alternatingNatural_seven {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (h : AlternatingNatural H U Z 7)
    {x : MulAut W} (hx : x ∈ H) (hx1 : x ≠ 1) : ∃ u ∈ U, x u ≠ u :=
  s16c1614_exists_moved_of_realizes h s16c1614_altDn_seven_faithful hx hx1

theorem s16c1614_moved_of_binaryNaturalSL {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {d a : ℕ} (h : BinaryNaturalSL H U Z d a)
    {x : MulAut W} (hx : x ∈ H) (hx1 : x ≠ 1) : ∃ u ∈ U, x u ≠ u := by
  obtain ⟨K, _, _, -, hR⟩ := h
  exact s16c1614_exists_moved_of_realizes hR s16c1614_natSL_faithful hx hx1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
