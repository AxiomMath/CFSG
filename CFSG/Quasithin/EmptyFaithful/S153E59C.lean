module

public import CFSG.Quasithin.Background.F6CatRecogOut
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153E59

section L32

theorem card_statedSL_three_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem card_mulAut_statedSL_three_two : Nat.card (MulAut ↥(StatedSL 3 (ZMod 2))) = 336 := by
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  let e₁ : ↥(StatedSL 3 (ZMod 2)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  let e₅ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃*
      StatedProj (StatedSL 2 (ZMod 7)) := projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 7)
  let ε : ↥(StatedSL 3 (ZMod 2)) ≃* StatedProj (StatedSL 2 (ZMod 7)) :=
    e₁.trans (e₃.trans (e₄.trans e₅))
  have hcard : Nat.card (StatedProj (StatedSL 2 (ZMod 7))) = 168 := by
    rw [← Nat.card_congr ε.toEquiv, card_statedSL_three_two]
  have := CFSG.Quasithin.F6.card_mulAut_psl_two_prime (K := ZMod 7) (p := 7) (by norm_num)
    (by simp)
  rw [Nat.card_congr (MulAut.congr ε).toEquiv, this, hcard]

theorem isSimpleGroup_statedSL_three_two : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := by
  have := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 (by norm_num)
  exact (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.isSimpleGroup

theorem statedSL_center {s : ↥(StatedSL 3 (ZMod 2))} (hs : ∀ t, s * t = t * s) : s = 1 := by
  let e := specialLinearGroupEquivStatedSL 3 (ZMod 2)
  have hc : e.symm s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hs (e g)
    have h2 := congrArg e.symm this
    simpa using h2.symm
  rw [CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot, Subgroup.mem_bot] at hc
  exact e.symm.injective (by simpa using hc)

end L32

section CenterAut

theorem eq_one_of_central_mulAut {S : Type*} [Group S] (hS : ∀ s : S, (∀ t, s * t = t * s) → s = 1)
    {a : MulAut S} (ha : ∀ b : MulAut S, a * b = b * a) : a = 1 := by
  refine MulEquiv.ext fun s => ?_
  have h1 : ∀ t : S, a s * a t * (a s)⁻¹ = s * a t * s⁻¹ := by
    intro t
    have := congrArg (fun φ : MulAut S => φ t) (ha (MulAut.conj s))
    simpa [MulAut.conj_apply] using this
  have h2 : (s⁻¹ * a s) = 1 := by
    apply hS
    intro t'
    obtain ⟨t, rfl⟩ := a.surjective t'
    have := h1 t
    calc s⁻¹ * a s * a t = s⁻¹ * (a s * a t * (a s)⁻¹) * a s := by group
      _ = s⁻¹ * (s * a t * s⁻¹) * a s := by rw [this]
      _ = a t * (s⁻¹ * a s) := by group
  simpa using (mul_eq_one_iff_eq_inv.mp h2).symm

end CenterAut

section AutData

theorem autL32Data {W : Type} [Group W] [Finite W] (A : Subgroup (MulAut W))
    (hA : Nonempty (↥A ≃* MulAut ↥(StatedSL 3 (ZMod 2))))
    (π : ↥(StatedSL 3 (ZMod 2)) →* ↥(oTwoUpper A)) (hπ : Function.Surjective π) :
    Nat.card ↥A = 336 ∧ Nat.card ↥(oTwoUpper A) = 168 ∧ (oTwoUpper A).relIndex A = 2 ∧
      IsSimpleGroup ↥(oTwoUpper A) ∧ ∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1 := by
  have hfin : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨e⟩ := hA
  have hAcard : Nat.card ↥A = 336 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_mulAut_statedSL_three_two
  have hA0ne : oTwoUpper A ≠ ⊥ := by
    intro hbot
    have h2 : IsPGroup 2 ↥A := by
      intro a
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper A a.2
      refine ⟨k, Subtype.ext ?_⟩
      rw [hbot, Subgroup.mem_bot] at hk
      simpa using hk
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h2
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn, hAcard]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := isSimpleGroup_statedSL_three_two
  have : Nontrivial ↥(oTwoUpper A) := (Subgroup.nontrivial_iff_ne_bot _).mpr hA0ne
  have hinj : Function.Injective π :=
    CFSG.QuasithinUnique.Bridge.injective_of_surjective_of_simple π hπ
  let eπ : ↥(StatedSL 3 (ZMod 2)) ≃* ↥(oTwoUpper A) := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  have hA0card : Nat.card ↥(oTwoUpper A) = 168 := by
    rw [← Nat.card_congr eπ.toEquiv, card_statedSL_three_two]
  refine ⟨hAcard, hA0card, ?_, eπ.symm.isSimpleGroup, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (oTwoUpper A) A
    rw [inf_eq_left.mpr (oTwoUpper_le A), hA0card, hAcard] at h1
    omega
  · intro a ha hc
    have hcen : ∀ b : MulAut ↥(StatedSL 3 (ZMod 2)), e ⟨a, ha⟩ * b = b * e ⟨a, ha⟩ := by
      intro b
      obtain ⟨b', rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc b' b'.2)
    have h1 := eq_one_of_central_mulAut (fun s hs => statedSL_center hs) hcen
    have : (⟨a, ha⟩ : ↥A) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this

end AutData

end S153E59

end CFSG.Quasithin
