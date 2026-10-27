module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.SignalizerFunctorTheorem Subgroup
open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem six_thirteen_A_normalizes {X B : Subgroup (LGL 2 V)}
    (hB : IsElemAbelian 2 B) (hB2 : 2 ^ 2 ≤ Nat.card B)
    (hXB : B ≤ Subgroup.normalizer (X : Set (LGL 2 V)))
    (hodd : Odd (Nat.card X))
    (hfix : ∀ D ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 B,
      fixSub D = fixSub B) :
    ∀ x ∈ X, ∀ f ∈ fixSub B, x f ∈ fixSub B := by
  intro x hx f hf
  have hcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.2 hodd
  have hgen := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.generation_hyperplanes
    Nat.prime_two hB hB2 hXB hcop
  have hxN : x ∈ stabilizerOf ⊤ (fixSub B) := by
    have hxsup : x ∈ ⨆ D ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 B,
        X ⊓ Subgroup.centralizer (D : Set (LGL 2 V)) := by
      rw [hgen]; exact hx
    have hle : (⨆ D ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 B,
        X ⊓ Subgroup.centralizer (D : Set (LGL 2 V))) ≤ stabilizerOf ⊤ (fixSub B) :=
      iSup₂_le fun D hD => by
        intro g hg
        have hgD : g ∈ Subgroup.centralizer (D : Set (LGL 2 V)) := hg.2
        have hfixD : fixSub D = fixSub B := hfix D hD
        have hpres : ∀ u ∈ fixSub B, g u ∈ fixSub B := by
          intro u hu
          rw [← hfixD] at hu ⊢
          intro d hd
          have hgd : d * g = g * d := Subgroup.mem_centralizer_iff.1 hgD d hd
          calc d (g u) = (d * g) u := (LinearEquiv.mul_apply d g u).symm
            _ = (g * d) u := by rw [hgd]
            _ = g (d u) := LinearEquiv.mul_apply g d u
            _ = g u := by rw [hu d hd]
        have hpresi : ∀ u ∈ fixSub B, g⁻¹ u ∈ fixSub B := by
          intro u hu
          rw [← hfixD] at hu ⊢
          intro d hd
          have hgd : d * g⁻¹ = g⁻¹ * d := by
            have := Subgroup.mem_centralizer_iff.1
              ((Subgroup.centralizer (D : Set (LGL 2 V))).inv_mem hgD) d hd
            simpa using this
          calc d (g⁻¹ u) = (d * g⁻¹) u := (LinearEquiv.mul_apply d g⁻¹ u).symm
            _ = (g⁻¹ * d) u := by rw [hgd]
            _ = g⁻¹ (d u) := LinearEquiv.mul_apply g⁻¹ d u
            _ = g⁻¹ u := by rw [hu d hd]
        refine ⟨Subgroup.mem_top _, ?_⟩
        apply le_antisymm
        · rintro v ⟨u, hu, rfl⟩
          exact hpres u hu
        · intro v hv
          exact ⟨g⁻¹ v, hpresi v hv, g.apply_symm_apply v⟩
    exact hle hxsup
  have hconj : conjSub x (fixSub B) = fixSub B := hxN.2
  exact hconj ▸ apply_mem_conjSub hf

theorem six_thirteen_A_commutator_centralizes {X B : Subgroup (LGL 2 V)}
    (hB : IsElemAbelian 2 B) (hB2 : 2 ^ 2 ≤ Nat.card B)
    (hXB : B ≤ Subgroup.normalizer (X : Set (LGL 2 V)))
    (hodd : Odd (Nat.card X))
    (hfix : ∀ D ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 B,
      fixSub D = fixSub B) :
    ⁅X, B⁆ ≤ centralizerOn ⊤ (fixSub B) := by
  have hnorm := six_thirteen_A_normalizes hB hB2 hXB hodd hfix
  rw [Subgroup.commutator_le]
  intro x hx b hb
  rw [mem_centralizerOn]
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro f hf
  have hbf : b f = f := hf b hb
  have hbinvf : b⁻¹ f = f := by
    have h := congrArg (fun w => b⁻¹ w) hbf
    simp at h
    exact h.symm
  have hxif : x⁻¹ f ∈ fixSub B := hnorm x⁻¹ (X.inv_mem hx) f hf
  have hbxif : b (x⁻¹ f) = x⁻¹ f := hxif b hb
  rw [commutatorElement_def]
  simp only [LinearEquiv.mul_apply]
  rw [hbinvf, hbxif]
  exact x.apply_symm_apply f

open CFSG.SignalizerFunctorTheorem.Quadratic in
theorem eq_bot_of_fixSub_le_fixSub_of_odd {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {Q B : Subgroup (LGL 2 V)} (hQ : Odd (Nat.card Q))
    (hB : IsPGroup 2 B) (hBnorm : B ≤ Subgroup.normalizer (Q : Set (LGL 2 V)))
    (hfix : fixSub B ≤ fixSub Q) : Q = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card Q) := Nat.coprime_two_left.2 hQ
  have hdisj : fixSub Q ⊓ commSub Q = ⊥ := (isCompl_fixSub_commSub hcop).inf_eq_bot
  have hWinv : ∀ g ∈ B, ∀ w ∈ commSub Q, g w ∈ commSub Q :=
    fun g hg w hw => map_mem_commSub_of_mem_normalizer (A := Q) (hBnorm hg) hw
  by_contra hQne
  have hWne : commSub Q ≠ ⊥ := fun h => hQne ((commSub_eq_bot_iff (A := Q)).mp h)
  obtain ⟨u, huW, hu0, hufix⟩ := exists_fixed_of_isPGroup (U := commSub Q) hB hWne hWinv
  have huB : u ∈ fixSub B := hufix
  have huQ : u ∈ fixSub Q := hfix huB
  have huBot : u ∈ (⊥ : Submodule (ZMod 2) V) := by
    rw [← hdisj]
    exact ⟨huQ, huW⟩
  exact hu0 (by simpa using huBot)

open CFSG.SignalizerFunctorTheorem.Quadratic in
theorem six_thirteen_A {X B : Subgroup (LGL 2 V)}
    (hB : IsElemAbelian 2 B) (hB2 : 2 ^ 2 ≤ Nat.card B)
    (hXB : B ≤ Subgroup.normalizer (X : Set (LGL 2 V)))
    (hodd : Odd (Nat.card X))
    (hfix : ∀ D ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 B,
      fixSub D = fixSub B) :
    ⁅X, B⁆ = ⊥ := by
  have hcomm := six_thirteen_A_commutator_centralizes hB hB2 hXB hodd hfix
  have hQleX : ⁅X, B⁆ ≤ X :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := B) (K := X)).mp hXB
  have hQcop : Nat.Coprime 2 (Nat.card ↥(⁅X, B⁆)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hQleX) (Nat.coprime_two_left.2 hodd)
  have hQnorm : B ≤ Subgroup.normalizer (⁅X, B⁆ : Subgroup (LGL 2 V)) :=
    Subgroup.normalizer_commutator_ge_right X B
  have hfixQ : fixSub B ≤ fixSub (⁅X, B⁆) := by
    intro v hv
    rw [mem_fixSub]
    intro q hq
    exact (mem_centralizerOn.mp (hcomm hq)).2 v hv
  exact eq_bot_of_fixSub_le_fixSub_of_odd (Nat.coprime_two_left.1 hQcop) hB.isPGroup hQnorm hfixQ

end CFSG.LocalAnalysis.WeakClosure81
