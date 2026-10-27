module

public import CFSG.RankThree.PartOne.KLR.Frame
public import CFSG.RankThree.PartOne.RF4.Descent
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section FExt

variable {τ : Tag} {L : Type} [Field L]

@[expose] noncomputable def Fext (F : MulAut (adjointGroup τ L)) (u : ModGL τ L) : ModGL τ L := by
  classical
  exact if hu : u ∈ adjointGroup τ L then ((F ⟨u, hu⟩ : adjointGroup τ L) : ModGL τ L) else 1

theorem Fext_of_mem (F : MulAut (adjointGroup τ L)) {u : ModGL τ L} (hu : u ∈ adjointGroup τ L) :
    Fext F u = ((F ⟨u, hu⟩ : adjointGroup τ L) : ModGL τ L) := by
  simp [Fext, hu]

theorem Fext_mul (F : MulAut (adjointGroup τ L)) {u v : ModGL τ L} (hu : u ∈ adjointGroup τ L)
    (hv : v ∈ adjointGroup τ L) : Fext F (u * v) = Fext F u * Fext F v := by
  rw [Fext_of_mem F hu, Fext_of_mem F hv, Fext_of_mem F (mul_mem hu hv)]
  have : (⟨u * v, mul_mem hu hv⟩ : adjointGroup τ L) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
  rw [this, map_mul]
  rfl

theorem Fext_one (F : MulAut (adjointGroup τ L)) : Fext F 1 = 1 := by
  rw [Fext_of_mem F (one_mem _)]
  have : (⟨1, one_mem _⟩ : adjointGroup τ L) = 1 := rfl
  rw [this, map_one]
  rfl

theorem Fext_inv (F : MulAut (adjointGroup τ L)) {u : ModGL τ L} (hu : u ∈ adjointGroup τ L) :
    Fext F u⁻¹ = (Fext F u)⁻¹ := by
  rw [Fext_of_mem F (inv_mem hu), Fext_of_mem F hu]
  have : (⟨u⁻¹, inv_mem hu⟩ : adjointGroup τ L) = ⟨u, hu⟩⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem Fext_mem (F : MulAut (adjointGroup τ L)) {u : ModGL τ L} (hu : u ∈ adjointGroup τ L) :
    Fext F u ∈ adjointGroup τ L := by
  rw [Fext_of_mem F hu]
  exact (F ⟨u, hu⟩).2

@[expose] def twistedFixed (F : MulAut (adjointGroup τ L)) (n : ModGL τ L) :
    Subgroup (ModGL τ L) where
  carrier := {u | u ∈ adjointGroup τ L ∧ n * Fext F u * n⁻¹ = u}
  mul_mem' := fun {u v} hu hv => by
    refine ⟨mul_mem hu.1 hv.1, ?_⟩
    rw [Fext_mul F hu.1 hv.1]
    calc n * (Fext F u * Fext F v) * n⁻¹ = (n * Fext F u * n⁻¹) * (n * Fext F v * n⁻¹) := by group
      _ = u * v := by rw [hu.2, hv.2]
  one_mem' := ⟨one_mem _, by rw [Fext_one]; group⟩
  inv_mem' := fun {u} hu => by
    refine ⟨inv_mem hu.1, ?_⟩
    rw [Fext_inv F hu.1]
    calc n * (Fext F u)⁻¹ * n⁻¹ = (n * Fext F u * n⁻¹)⁻¹ := by group
      _ = u⁻¹ := by rw [hu.2]

theorem mem_twistedFixed {F : MulAut (adjointGroup τ L)} {n u : ModGL τ L} :
    u ∈ twistedFixed F n ↔ u ∈ adjointGroup τ L ∧ n * Fext F u * n⁻¹ = u := Iff.rfl

end FExt

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  (L : Type) [Field L] [Algebra K L]

@[expose] noncomputable def thetaGamma (a : ℕ) :
    ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
  (baseChangeGL (algebraMap K L)).comp (ReeTag.F4.reeGamma K a).subtype

theorem thetaGamma_apply (γ : ReeTag.F4.reeGamma K a) :
    thetaGamma L a γ = baseChangeGL (algebraMap K L) (γ : ModGL ReeTag.F4.tag K) := rfl

theorem thetaGamma_eq_adjoint (γ : ReeTag.F4.reeGamma K a) :
    thetaGamma L a γ =
      ((adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L)
        (RF4.reeGammaToAdjoint (K := K) a γ : adjointGroup ReeTag.F4.tag K) :
        adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) := rfl

theorem thetaGamma_mem_adjointGroup (γ : ReeTag.F4.reeGamma K a) :
    thetaGamma L a γ ∈ adjointGroup ReeTag.F4.tag L := by
  rw [thetaGamma_eq_adjoint]
  exact (adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L)
    (RF4.reeGammaToAdjoint (K := K) a γ : adjointGroup ReeTag.F4.tag K)).2

theorem thetaGamma_injective : Function.Injective (thetaGamma (K := K) L a) := by
  intro γ₁ γ₂ h
  rw [thetaGamma_eq_adjoint, thetaGamma_eq_adjoint] at h
  exact RF4.reeGammaToAdjoint_injective a
    (adjointBaseChangeHom_injective ReeTag.F4.tag (algebraMap K L) (Subtype.ext h))

structure ReeFrameData (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (L : Type) [Field L] [Algebra K L] (a : ℕ) where
  F : MulAut (adjointGroup ReeTag.F4.tag L)
  isFrob : IsReeFrob a F
  lang : ∀ m, ∃ h, m = h⁻¹ * F h
  base : ∀ u, F (adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L) u) =
    adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L)
      ((ReeTag.F4.finiteExceptionalAut K ^ (2 * a + 1)) u)
  Frq : L →+* L
  Frq_pow : ∀ c, Frq c = c ^ Nat.card K
  sq : ∀ y, ((F (F y) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
    Units.map (entrywiseHom Frq) (y : ModGL ReeTag.F4.tag L)

variable {L}

theorem reeFrameData_nonempty [IsAlgClosure K L] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (ReeFrameData K L a) := by
  obtain ⟨F, h1, h2, h3, Frq, h4, h5⟩ := reeFrame_exists L hK
  exact ⟨⟨F, h1, h2, h3, Frq, h4, h5⟩⟩

variable (D : ReeFrameData K L a)

theorem ReeFrameData.fext_theta (γ : ReeTag.F4.reeGamma K a) :
    Fext D.F (thetaGamma L a γ) = thetaGamma L a γ := by
  rw [Fext_of_mem D.F (thetaGamma_mem_adjointGroup L γ)]
  have h1 : (⟨thetaGamma L a γ, thetaGamma_mem_adjointGroup L γ⟩ : adjointGroup ReeTag.F4.tag L) =
      adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L)
        (RF4.reeGammaToAdjoint (K := K) a γ : adjointGroup ReeTag.F4.tag K) := rfl
  rw [h1, D.base, ← RF4.finiteReeAut_eq_pow, RF4.finiteReeAut_reeGammaToAdjoint]
  rfl

theorem ReeFrameData.exists_theta_of_fixed [IsAlgClosure K L] {v : ModGL ReeTag.F4.tag L}
    (hv : v ∈ adjointGroup ReeTag.F4.tag L) (hfix : Fext D.F v = v) :
    ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = v := by
  have hF : D.F ⟨v, hv⟩ = ⟨v, hv⟩ := by
    refine Subtype.ext ?_
    rw [← Fext_of_mem D.F hv]
    exact hfix
  have hFr : Units.map (entrywiseHom D.Frq) v = v := by
    have := D.sq ⟨v, hv⟩
    rw [hF, hF] at this
    exact this.symm
  obtain ⟨u, hu, huy⟩ := mem_range_baseChange_of_frobenius_fixed L D.Frq D.Frq_pow ⟨v, hv⟩ hFr
  have hι : adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L) ⟨u, hu⟩ = ⟨v, hv⟩ := Subtype.ext huy
  have hfixu : ReeTag.F4.finiteReeAut K a ⟨u, hu⟩ = ⟨u, hu⟩ := by
    have h1 := D.base ⟨u, hu⟩
    rw [hι, hF, ← hι] at h1
    have h2 := adjointBaseChangeHom_injective ReeTag.F4.tag (algebraMap K L) h1.symm
    rw [RF4.finiteReeAut_eq_pow]
    exact h2
  refine ⟨⟨u, ReeTag.mem_reeGamma.2 ⟨hu, hfixu⟩⟩, ?_⟩
  rw [thetaGamma_apply]
  exact huy

end Frame

section Master

variable {τ : Tag} {L : Type} [Field L]

theorem Fext_conj (F : MulAut (adjointGroup τ L)) {g u : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hu : u ∈ adjointGroup τ L) :
    Fext F (g * u * g⁻¹) = Fext F g * Fext F u * (Fext F g)⁻¹ := by
  rw [Fext_mul F (mul_mem hg hu) (inv_mem hg), Fext_mul F hg hu, Fext_inv F hg]

theorem conj_mem_twistedFixed (F : MulAut (adjointGroup τ L)) {g₀ n : ModGL τ L}
    (hg₀ : g₀ ∈ adjointGroup τ L) (hFg : Fext F g₀ = g₀ * n) {v : ModGL τ L}
    (hv : v ∈ adjointGroup τ L) (hfix : Fext F v = v) : g₀⁻¹ * v * g₀ ∈ twistedFixed F n := by
  refine ⟨mul_mem (mul_mem (inv_mem hg₀) hv) hg₀, ?_⟩
  have h1 : g₀⁻¹ * v * g₀ = g₀⁻¹ * v * g₀⁻¹⁻¹ := by rw [inv_inv]
  rw [h1, Fext_conj F (inv_mem hg₀) hv, Fext_inv F hg₀, hfix, hFg]
  group

theorem fixed_of_mem_twistedFixed (F : MulAut (adjointGroup τ L)) {g₀ n : ModGL τ L}
    (hg₀ : g₀ ∈ adjointGroup τ L) (hFg : Fext F g₀ = g₀ * n) {u : ModGL τ L}
    (hu : u ∈ twistedFixed F n) : g₀ * u * g₀⁻¹ ∈ adjointGroup τ L ∧
      Fext F (g₀ * u * g₀⁻¹) = g₀ * u * g₀⁻¹ := by
  refine ⟨mul_mem (mul_mem hg₀ hu.1) (inv_mem hg₀), ?_⟩
  rw [Fext_conj F hg₀ hu.1, hFg]
  have h2 : Fext F u = n⁻¹ * u * n := by
    have := hu.2
    calc Fext F u = n⁻¹ * (n * Fext F u * n⁻¹) * n := by group
      _ = n⁻¹ * u * n := by rw [this]
  rw [h2]
  group

end Master

end CFSG.RankThree.PartOne.KLR
