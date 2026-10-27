module

public import CFSG.Quasithin.Vol2.Ch6SL2Fix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem fixedSub_iff_rootLine {ρ : Representation (ZMod 2) SL(2, F) W}
    {φ : W ≃+ (Fin 2 → F)}
    (hφ : ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w))
    {A : Subgroup SL(2, F)} {x : SL(2, F)}
    (hx : ∀ g, g ∈ A ↔
      x⁻¹ * g * x ∈ (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent
        (F := F)).range)
    (w : W) : w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x := by
  rw [mem_fixedSub]
  constructor
  · intro hw
    refine mem_rootLine_of_fixed x (φ w) (fun g hg => ?_)
    have hgA : g ∈ A := (hx g).mpr hg
    have h1 : ρ g w = w := hw g hgA
    rw [smul_eq_mulVec', ← hφ, h1]
  · intro hw g hg
    have hgU : x⁻¹ * g * x ∈
        (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent (F := F)).range :=
      (hx g).mp hg
    have h1 := fixed_of_conj_mem x g hgU (φ w) hw
    apply φ.injective
    rw [hφ]
    exact h1

theorem IsNaturalModule.fixedSub_zpowers_eq {ρ : Representation (ZMod 2) SL(2, F) W}
    (hρ : IsNaturalModule ρ) {A : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Nat.card F)
    {a : SL(2, F)} (ha : a ∈ A) (ha1 : a ≠ 1) :
    fixedSub ρ (Subgroup.zpowers a) = fixedSub ρ A := by
  classical
  obtain ⟨φ, hφ⟩ := hρ
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hA
  have hxU : x⁻¹ * a * x ∈ (upperUnipotent (F := F)).range := (hx a).mp ha
  have hxa1 : x⁻¹ * a * x ≠ 1 := by
    intro h
    apply ha1
    have := congrArg (fun g => x * g * x⁻¹) h
    simpa [mul_assoc] using this
  have hAiff : ∀ w : W, w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x :=
    fun w => fixedSub_iff_rootLine hφ hx w
  have haiff : ∀ w : W, w ∈ fixedSub ρ (Subgroup.zpowers a) ↔ φ w ∈ rootLine x := by
    intro w
    rw [mem_fixedSub]
    constructor
    · intro hw
      have h1 : ρ a w = w := hw a (Subgroup.mem_zpowers a)
      have hfix : a • φ w = φ w := by
        rw [smul_eq_mulVec', ← hφ, h1]
      have hpow : (x⁻¹ * a * x) • (x⁻¹ • φ w) = x⁻¹ • φ w := by
        have := congrArg (fun v => x⁻¹ • v) hfix
        simpa [mul_smul] using this
      have h2 : (x⁻¹ * a * x) ^ 2 = 1 := by
        rw [pow_two]
        have haa := hA2 a ha
        calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
          _ = 1 := by rw [haa]; group
      have hzp : Subgroup.zpowers (x⁻¹ * a * x) ≠ ⊥ := by
        intro hbot
        apply hxa1
        have hmem : x⁻¹ * a * x ∈ (⊥ : Subgroup SL(2, F)) := by
          rw [← hbot]
          exact Subgroup.mem_zpowers _
        exact Subgroup.mem_bot.mp hmem
      have hPv : ∀ g ∈ Subgroup.zpowers (x⁻¹ * a * x),
          (g : SL(2, F)) • (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
        intro g hg
        have hgU : g ∈ (upperUnipotent (F := F)).range :=
          Subgroup.zpowers_le.mpr hxU hg
        exact (sl2_fixes_first_iff g).mpr hgU
      have hPw : ∀ g ∈ Subgroup.zpowers (x⁻¹ * a * x),
          (g : SL(2, F)) • (x⁻¹ • φ w) = x⁻¹ • φ w := by
        intro g hg
        rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime h2 hxa1] at hg
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
        have hj2 : j = 0 ∨ j = 1 := by
          have := Finset.mem_range.mp hj
          omega
        rcases hj2 with rfl | rfl
        · simp
        · simpa using hpow
      obtain ⟨c, hc⟩ := CFSG.Quasithin.H13.fixed_eq_line
        (Subgroup.zpowers (x⁻¹ * a * x)) hzp (by simp) hPv hPw
      have hφw : φ w = c • (x • (Pi.single 0 1 : Fin 2 → F)) := by
        calc φ w = x • (x⁻¹ • φ w) := by rw [smul_inv_smul]
          _ = x • (c • (Pi.single 0 1 : Fin 2 → F)) := by rw [hc]
          _ = c • (x • (Pi.single 0 1 : Fin 2 → F)) := by
              rw [smul_eq_mulVec' x (c • (Pi.single 0 1 : Fin 2 → F)), Matrix.mulVec_smul,
                ← smul_eq_mulVec']
      rw [hφw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · intro hw g hg
      have hgA : g ∈ A := Subgroup.zpowers_le.mpr ha hg
      have hgU : x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range := (hx g).mp hgA
      have h1 := fixed_of_conj_mem x g hgU (φ w) hw
      apply φ.injective
      rw [hφ]
      exact h1
  ext w
  rw [hAiff w, haiff w]

theorem IsNaturalModule.natCard_fixedSub {ρ : Representation (ZMod 2) SL(2, F) W}
    (hρ : IsNaturalModule ρ) {A : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Nat.card F) :
    Nat.card (fixedSub ρ A) = Nat.card F := by
  obtain ⟨φ, hφ⟩ := hρ
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hA
  have hAiff : ∀ w : W, w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x :=
    fun w => fixedSub_iff_rootLine hφ hx w
  have e : ↥(fixedSub ρ A) ≃ ↥(rootLine x) :=
    Equiv.subtypeEquiv φ.toEquiv (fun w => hAiff w)
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F), finrank_rootLine, pow_one]

end CFSG.RankThree.GF2n.Tim81.Sec2

end
