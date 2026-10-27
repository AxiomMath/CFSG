module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.F112Crit

open CFSG.OrderReductions.FrattiniAutomorphisms CFSG.Semidihedral.ElementaryActionTransport

theorem exists_frattini_action {H : Type} [Group H] [Finite H]
    (hH : Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H) ≤ CFSG.pCore 2 H) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V)
      (_ : FiniteDimensional (ZMod 2) V) (π : Additive ↥(CFSG.pCore 2 H) →+ V)
      (ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) V),
      Function.Surjective π ∧
      (∀ (h : H) (n : ↥(CFSG.pCore 2 H)),
        (ρ h : V →ₗ[ZMod 2] V) (π (Additive.ofMul n)) =
          π (Additive.ofMul (MulAut.conjNormal h n))) ∧
      (∀ h : H, ρ h = 1 ↔ h ∈ CFSG.pCore 2 H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  obtain ⟨-, -, -, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hP
  haveI : IsElementaryAbelian 2 (↥(CFSG.pCore 2 H) ⧸ frattini ↥(CFSG.pCore 2 H)) := helem
  let ρ₀ : H →* MulAut (↥(CFSG.pCore 2 H) ⧸ frattini ↥(CFSG.pCore 2 H)) :=
    (quotientAutomorphism (frattini ↥(CFSG.pCore 2 H))).comp
      (MulAut.conjNormal : H →* MulAut ↥(CFSG.pCore 2 H))
  have hρ₀ : ∀ (h : H) (n : ↥(CFSG.pCore 2 H)),
      ρ₀ h (QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) n) =
        QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) (MulAut.conjNormal h n) :=
    fun h n => quotientAutomorphism_apply _ _ n
  refine ⟨Additive (↥(CFSG.pCore 2 H) ⧸ frattini ↥(CFSG.pCore 2 H)), inferInstance, inferInstance,
    inferInstance, (QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H))).toAdditive,
    primeFieldAction (p := 2) ρ₀, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (frattini ↥(CFSG.pCore 2 H)) (Additive.toMul v)
    exact ⟨Additive.ofMul n, congrArg Additive.ofMul hn⟩
  · intro h n
    exact congrArg Additive.ofMul (hρ₀ h n)
  · intro h
    constructor
    · intro hρ
      have hle : (MulAut.conjNormal : H →* MulAut ↥(CFSG.pCore 2 H)).ker ≤ CFSG.pCore 2 H := by
        intro x hx
        apply hH
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := congrArg (fun φ : MulAut ↥(CFSG.pCore 2 H) => (φ ⟨y, hy⟩ : H))
          (MonoidHom.mem_ker.mp hx)
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
        calc y * x = (x * y * x⁻¹) * x := by rw [this]
          _ = x * y := by group
      have hkerconj : IsPGroup 2 ↥(MulAut.conjNormal : H →* MulAut ↥(CFSG.pCore 2 H)).ker :=
        CFSG.pCore_isPGroup.to_le hle
      have hker : IsPGroup 2 ↥(primeFieldAction (p := 2) ρ₀).ker := by
        rw [primeFieldAction_kernel]
        exact IsPGroup.comap_of_ker_isPGroup
          (CFSG.GroupTheory.frattini_automorphism_kernel hP).2 _ hkerconj
      have hnormal : (primeFieldAction (p := 2) ρ₀).ker.Normal := MonoidHom.normal_ker _
      have hsub : (primeFieldAction (p := 2) ρ₀).ker ≤ CFSG.pCore 2 H :=
        le_sSup ⟨hnormal, hker⟩
      exact hsub (MonoidHom.mem_ker.mpr hρ)
    · intro hh
      refine Units.ext (LinearMap.ext fun v => ?_)
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥(CFSG.pCore 2 H)) (Additive.toMul v)
      show (primeFieldAction (p := 2) ρ₀ h : Module.End (ZMod 2)
          (Additive (↥(CFSG.pCore 2 H) ⧸ frattini ↥(CFSG.pCore 2 H))))
        (Additive.ofMul (QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) n)) =
          Additive.ofMul (QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) n)
      rw [primeFieldAction_apply, hρ₀]
      congr 1
      have e : MulAut.conjNormal h n = (⟨h, hh⟩ : ↥(CFSG.pCore 2 H)) * n * (⟨h, hh⟩ : ↥(CFSG.pCore 2 H))⁻¹ :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
      rw [e, map_mul, map_mul, map_inv]
      have hc : QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) (⟨h, hh⟩ : ↥(CFSG.pCore 2 H)) *
          QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) n =
          QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) n *
            QuotientGroup.mk' (frattini ↥(CFSG.pCore 2 H)) (⟨h, hh⟩ : ↥(CFSG.pCore 2 H)) :=
        mul_comm _ _
      rw [hc]
      group

end CFSG.Quasithin.F112Crit
