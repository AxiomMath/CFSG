module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

section Module

private lemma ggLinMove_le_ggLinCom
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Set (V ≃ₗ[ZMod p] V)) {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A) :
    ggLinMove a ≤ ggLinCom A :=
  le_iSup₂ (f := fun a (_ : a ∈ A) => ggLinMove a) a ha

theorem ggLin_eq_com_of_neg_one
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hprop : ∀ W : Submodule (ZMod p) V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      W ≤ ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) ∨ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) ≤ W)
    (hfix : ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) = ⊥) (ε : V ≃ₗ[ZMod p] V) (hε : ε ∈ A)
    (hεsq : ε * ε = 1) (hεc : ∀ a ∈ A, a * ε = ε * a)
    (hεneg : ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), ε u = -u) :
    ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) = ⊤ := by
  have hpodd : Odd p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨m, hm⟩ := hpodd
  let k : ZMod p := ((m + 1 : ℕ) : ZMod p)
  have h2k : (2 : ZMod p) * k = 1 := by
    change (2 : ZMod p) * ((m + 1 : ℕ) : ZMod p) = 1
    have h2m : 2 * (m + 1) = p + 1 := by omega
    have hcast : (2 : ZMod p) * ((m + 1 : ℕ) : ZMod p) = ((2 * (m + 1) : ℕ) : ZMod p) := by
      push_cast
      ring
    rw [hcast, h2m, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  have hk2 : k * 2 = 1 := by rw [mul_comm, h2k]
  have hεε : ∀ v : V, ε (ε v) = v := by
    intro v
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hεsq
    simpa [LinearEquiv.mul_apply] using h
  let Z : Submodule (ZMod p) V := ggLinFix ({ε} : Set (V ≃ₗ[ZMod p] V))
  have hZmem : ∀ w : V, w ∈ Z ↔ ε w = w := by
    intro w
    simp [Z, ggLinFix]
  have hZstab : ∀ a ∈ A, ∀ w ∈ Z, a w ∈ Z := by
    intro a ha w hw
    have hw' : ε w = w := (hZmem w).mp hw
    rw [hZmem (a w), ← LinearEquiv.mul_apply, ← hεc a ha, LinearEquiv.mul_apply, hw']
  rcases hprop Z hZstab with hZle | hcomZ
  ·
    have hZbot : Z = ⊥ := le_bot_iff.mp (hZle.trans (le_of_eq hfix))
    have hv_mem : ∀ v : V, v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
      intro v
      have hmemZ : v + ε v ∈ Z := by
        rw [hZmem, map_add, hεε v]
        exact add_comm _ _
      have hzero : v + ε v = 0 := by
        have h := hmemZ
        rw [hZbot] at h
        exact (Submodule.mem_bot (ZMod p)).mp h
      have hεv : ε v = -v := eq_neg_of_add_eq_zero_right hzero
      have hmemC : (-2 : ZMod p) • v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
        apply ggLinMove_le_ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) hε
        rw [ggLinMove, LinearMap.mem_range]
        refine ⟨v, ?_⟩
        change ε v - v = (-2 : ZMod p) • v
        rw [hεv]
        calc -v - v = -(v + v) := by rw [sub_eq_add_neg, neg_add]
          _ = -((2 : ZMod p) • v) := by rw [two_smul]
          _ = (-2 : ZMod p) • v := by rw [neg_smul]
      have h2v : (2 : ZMod p) • v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
        have hneg_eq : -((-2 : ZMod p) • v) = (2 : ZMod p) • v := by rw [← neg_smul, neg_neg]
        exact hneg_eq ▸ (ggLinCom (A : Set (V ≃ₗ[ZMod p] V))).neg_mem hmemC
      have hv_eq : v = k • ((2 : ZMod p) • v) := by
        rw [← smul_assoc, smul_eq_mul, hk2, one_smul]
      rw [hv_eq]
      exact (ggLinCom (A : Set (V ≃ₗ[ZMod p] V))).smul_mem k h2v
    rw [Submodule.eq_top_iff']
    exact hv_mem
  ·
    have hcom_bot : ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
      rw [← le_bot_iff]
      intro u hu
      have huZ : ε u = u := (hZmem u).mp (hcomZ hu)
      have hεu : ε u = -u := hεneg u hu
      have huu : u = -u := huZ.symm.trans hεu
      have h2u : (2 : ZMod p) • u = 0 := by
        rw [two_smul]
        exact (eq_neg_iff_add_eq_zero).mp huu
      calc u = k • ((2 : ZMod p) • u) := by rw [← smul_assoc, smul_eq_mul, hk2, one_smul]
        _ = 0 := by rw [h2u, smul_zero]
    have hfixTop : ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro v
      change ∀ a ∈ A, a v = v
      intro a ha
      have hmem : a v - v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
        apply ggLinMove_le_ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) ha
        rw [ggLinMove, LinearMap.mem_range]
        exact ⟨v, rfl⟩
      rw [hcom_bot] at hmem
      exact sub_eq_zero.mp ((Submodule.mem_bot (ZMod p)).mp hmem)
    have htopbot : (⊤ : Submodule (ZMod p) V) = ⊥ := by
      rw [← hfixTop]
      exact hfix
    rw [hcom_bot]
    exact htopbot.symm

end Module

end CFSG.StandardType

end
