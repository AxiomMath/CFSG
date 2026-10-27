module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.W16LBDesc
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoD
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsF
import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open

theorem w16l_false_of_linear {X : Type} [Group X] [Finite X] {B : Subgroup X} {m n : ℕ}
    (hm : 3 ≤ m) (hlin : IsTransvectionCenterGroup X m n B)
    (hcore : CFSG.pCore 2 X = ⊥) (hel : IsElemAbelian 2 B)
    (hgen : Subgroup.normalClosure (B : Set X) = ⊤)
    (hP : ∀ x : X, (∃ a ∈ B, ∃ b ∈ CFSG.Quasithin.conjSubgroup B x, a * b ≠ b * a) →
      ∀ a ∈ B, a ∈ Subgroup.normalizer ((CFSG.Quasithin.conjSubgroup B x : Subgroup X) : Set X) →
        a = 1) :
    False := by
  classical
  obtain ⟨F, hF, hFin, _hFcard, e, a, ha, hVb⟩ := hlin
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : Nontrivial F := ⟨0, 1, zero_ne_one⟩
  have hm2 : 2 ≤ m := by omega
  have hcard : 1 < (transvectionCenterSet m F a).ncard := by
    rw [ncard_transvectionCenterSet m F hm2 a ha]
    exact Nat.one_lt_pow (by omega) (Finite.one_lt_card (α := F))
  obtain ⟨x₁, hx₁, hx₁ne⟩ :=
    Set.exists_ne_of_one_lt_ncard hcard (1 : StatedProj (StatedSL m F))
  have hx0 : ∃ x : X, ∃ a ∈ B, ∃ b ∈ CFSG.Quasithin.conjSubgroup B x, a * b ≠ b * a := by
    by_contra hcon
    have hcomm : ∀ x : X, ∀ a ∈ B, ∀ b ∈ CFSG.Quasithin.conjSubgroup B x,
        a * b = b * a := by
      intro x a ha b hb
      by_contra hne
      exact hcon ⟨x, a, ha, b, hb, hne⟩
    have hconj_sub : Group.conjugatesOfSet (B : Set X) ⊆
        (Subgroup.centralizer (B : Set X) : Set X) := by
      intro y hy
      rw [Group.mem_conjugatesOfSet_iff] at hy
      obtain ⟨c, hc, hcy⟩ := hy
      obtain ⟨d, hd⟩ := isConj_iff.mp hcy
      rw [← hd]
      change d * c * d⁻¹ ∈ Subgroup.centralizer (B : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      refine hcomm d⁻¹ b hb (d * c * d⁻¹) ?_
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      have h1 : d⁻¹ * (d * c * d⁻¹) * (d⁻¹)⁻¹ = c := by group
      rw [h1]
      exact hc
    have hclosure :
        Subgroup.normalClosure (B : Set X) ≤ Subgroup.centralizer (B : Set X) :=
      (Subgroup.closure_le (Subgroup.centralizer (B : Set X))).mpr hconj_sub
    have htop : (⊤ : Subgroup X) ≤ Subgroup.centralizer (B : Set X) := by
      rw [← hgen]
      exact hclosure
    have hBcenter : B ≤ Subgroup.center X := by
      intro b hb
      rw [Subgroup.mem_center_iff]
      intro y
      exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top y)) b hb).symm
    haveI hBnorm : B.Normal := Subgroup.normal_of_le_center hBcenter
    have hnc : Subgroup.normalClosure (B : Set X) = B := Subgroup.normalClosure_eq_self B
    have hBtop : B = ⊤ := hnc.symm.trans hgen
    have hel_top : IsElemAbelian 2 (⊤ : Subgroup X) := by
      rw [← hBtop]
      exact hel
    have hX2 : IsPGroup 2 (⊤ : Subgroup X) := CFSG.Open.IsElemAbelian.isPGroup hel_top
    have hXle : (⊤ : Subgroup X) ≤ CFSG.pCore 2 X :=
      le_sSup (s := {K : Subgroup X | K.Normal ∧ IsPGroup 2 K}) ⟨inferInstance, hX2⟩
    have htopbot : (⊤ : Subgroup X) = ⊥ := by
      rw [hcore] at hXle
      exact le_bot_iff.mp hXle
    have hsub : Subsingleton X := by
      refine ⟨fun p q => ?_⟩
      have hp : p ∈ (⊥ : Subgroup X) := by rw [← htopbot]; trivial
      have hq : q ∈ (⊥ : Subgroup X) := by rw [← htopbot]; trivial
      rw [Subgroup.mem_bot] at hp hq
      rw [hp, hq]
    have hcenter_top : Subgroup.center X = ⊤ := by
      refine le_antisymm le_top ?_
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hsub.elim (y * x) (x * y)
    have hsubq : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [hcenter_top]
      exact QuotientGroup.subsingleton_quotient_top
    have hsubt : Subsingleton (StatedProj (StatedSL m F)) :=
      ⟨fun p q => e.symm.injective (hsubq.elim (e.symm p) (e.symm q))⟩
    exact hx₁ne (hsubt.elim x₁ 1)
  obtain ⟨x₀, a₀, ha₀, b₀, hb₀, hne₀⟩ := hx0
  have hfree : ∀ b ∈ B,
      b ∈ Subgroup.normalizer ((CFSG.Quasithin.conjSubgroup B x₀ : Subgroup X) : Set X) →
        b = 1 :=
    hP x₀ ⟨a₀, ha₀, b₀, hb₀, hne₀⟩
  have hZo : Odd (Nat.card (Subgroup.center X)) := odd_card_center_of_pCore_eq_bot hcore
  have hB2 : IsPGroup 2 B := CFSG.Open.IsElemAbelian.isPGroup hel
  have hdescent := w16l_descent_free hZo hB2 x₀ hfree
  have hVb' : ∀ y : X ⧸ Subgroup.center X,
      y ∈ B.map (QuotientGroup.mk' (Subgroup.center X)) ↔
        e y ∈ transvectionCenterSet m F a := by
    intro y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hby⟩
      rw [QuotientGroup.mk'_apply] at hby
      exact (hVb y).mp ⟨b, hb, hby⟩
    · rintro hy
      obtain ⟨b, hb, hby⟩ := (hVb y).mpr hy
      refine ⟨b, hb, ?_⟩
      rw [QuotientGroup.mk'_apply]
      exact hby
  have hnt : B.map (QuotientGroup.mk' (Subgroup.center X)) ≠ ⊥ := by
    intro hbot
    have hmem : e.symm x₁ ∈ B.map (QuotientGroup.mk' (Subgroup.center X)) :=
      (hVb' (e.symm x₁)).mpr (by simpa using hx₁)
    rw [hbot] at hmem
    have hne : e.symm x₁ ≠ 1 := by
      intro h1
      apply hx₁ne
      have := congrArg e h1
      simpa using this
    exact hne (Subgroup.mem_bot.mp hmem)
  exact false_of_transvection_config kFacts1234_holds hm e ha
    (B.map (QuotientGroup.mk' (Subgroup.center X)))
    (CFSG.Quasithin.conjSubgroup (B.map (QuotientGroup.mk' (Subgroup.center X)))
      (QuotientGroup.mk' (Subgroup.center X) x₀))
    hVb' hnt (QuotientGroup.mk' (Subgroup.center X) x₀) rfl hdescent

end CFSG.LocalAnalysis.WeakClosure81

end
