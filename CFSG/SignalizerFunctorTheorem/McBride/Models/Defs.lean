module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

structure NearSimple (p : ℕ) (X : Type*) [Group X] : Prop where
  prime : p.Prime
  simple : IsSimpleGroup X
  nonabelian : ∃ a b : X, a * b ≠ b * a
  nearPSolvable : signalizerNearPSolvable p X

variable {X : Type*} [Group X]

theorem NearSimple.model {p : ℕ} (h : NearSimple p X) : signalizerNearSimpleModel p X := by
  have := h.simple
  let e : (⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤ ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (⊤ : Subgroup X))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hsimple : IsSimpleGroup ((⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤) :=
    e.isSimpleGroup
  have hnonab : ∃ a b : (⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  exact TransportA.nearSimpleModel_of_mulEquiv e (h.nearPSolvable.2 ⊤ ⊥ bot_le hsimple hnonab)

theorem NearSimple.coprime {p : ℕ} (h : NearSimple p X) : Nat.Coprime p (Nat.card X) :=
  h.nearPSolvable.1

@[expose] def IsFrobeniusWithKernel (H K : Subgroup X) : Prop :=
  K ≠ ⊥ ∧ K ≤ H ∧ (K.subgroupOf H).Normal ∧
    ∃ V : Subgroup X, V ≠ ⊥ ∧ V ≤ H ∧ Disjoint K V ∧ K ⊔ V = H ∧
      ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, v * k = k * v → k = 1

@[expose] def fixedFitting (f : MulAut X) : Subgroup X :=
  CFSG.fittingSubgroupOf (signalizerFixedSubgroup f)

@[expose] def fixedNormalizer (f : MulAut X) : Subgroup X :=
  Subgroup.normalizer (fixedFitting f : Set X)

theorem fixedFitting_le (f : MulAut X) : fixedFitting f ≤ signalizerFixedSubgroup f :=
  Subgroup.map_subtype_le _

theorem fixedFitting_conj_mem {f : MulAut X} {c y : X} (hc : c ∈ signalizerFixedSubgroup f)
    (hy : y ∈ fixedFitting f) : c * y * c⁻¹ ∈ fixedFitting f := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, ?_, rfl⟩
  exact (CFSG.fittingSubgroup_normal (G := signalizerFixedSubgroup f)).conj_mem y' hy' ⟨c, hc⟩

theorem fixed_le_fixedNormalizer (f : MulAut X) : signalizerFixedSubgroup f ≤ fixedNormalizer f :=
  fun c hc => Subgroup.mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => by
        have := fixedFitting_conj_mem hc hy
        simpa [mul_assoc] using this,
      fun hy => by
        have := fixedFitting_conj_mem (Subgroup.inv_mem _ hc) hy
        simpa [mul_assoc] using this⟩

open scoped commutatorElement

@[expose] def fixedCore1 (f : MulAut X) : Subgroup X where
  carrier := {c | c ∈ signalizerFixedSubgroup f ∧
    ∀ x ∈ signalizerFixedSubgroup f, ⁅c, x⁆ ∈ fixedFitting f}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haC, ha⟩ ⟨hbC, hb⟩
    refine ⟨Subgroup.mul_mem _ haC hbC, fun x hx => ?_⟩
    have h1 : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.mul_mem _ (fixedFitting_conj_mem haC (hb x hx)) (ha x hx)
  inv_mem' := by
    rintro a ⟨haC, ha⟩
    refine ⟨Subgroup.inv_mem _ haC, fun x hx => ?_⟩
    have h1 : ⁅a⁻¹, x⁆ = a⁻¹ * (⁅a, x⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact fixedFitting_conj_mem (Subgroup.inv_mem _ haC) (Subgroup.inv_mem _ (ha x hx))

@[expose] def autCommutator (f : MulAut X) (S : Subgroup X) : Subgroup X :=
  Subgroup.closure {y | ∃ x ∈ S, y = x⁻¹ * f x}

end CFSG.SignalizerFunctorTheorem.McBride
