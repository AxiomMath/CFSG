module

public import CFSG.Walter.W67.RCyc
public import CFSG.Walter.Ree.Cyclic

public section

namespace CFSG.Walter.W67

open CFSG.LieType.Ree

@[expose] def ReeIdentNative :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (h : Ward.ReeTypeHyp G),
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime),
      1 ≤ a ∧ Nat.card K = 3 ^ (2 * a + 1) ∧ h.q = Nat.card K ∧
      Nonempty (G ≃* ReeTag.G2.reeGamma K a)

theorem isCyclic_sylow_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] (e : G ≃* H) (h : ∀ Q : Sylow p H, IsCyclic (Q : Subgroup H))
    (P : Sylow p G) : IsCyclic (P : Subgroup G) := by
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  have hQ := h (P.mapSurjective hs)
  have hmap : ((P.mapSurjective hs : Sylow p H) : Subgroup H) =
      (P : Subgroup G).map e.toMonoidHom := rfl
  rw [hmap] at hQ
  let iso := Subgroup.equivMapOfInjective (P : Subgroup G) e.toMonoidHom e.injective
  exact isCyclic_of_surjective iso.symm.toMonoidHom iso.symm.surjective

theorem hall_of_reeIdentNative
    (hR : ReeIdentNative) :
    ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 → 3 < hL.q →
      ∀ (p : ℕ) [Fact p.Prime], p ∣ hL.q ^ 2 - hL.q + 1 →
        ∀ P : Sylow p L, IsCyclic (P : Subgroup L) := by
  intro L _ _ hL hq5 hq3 p _ hp P
  have hq : 5 < hL.q := hL.five_lt_q hq5 hq3
  obtain ⟨a, K, _, _, _, ha, hK, hqK, ⟨e⟩⟩ := hR L (hL.toReeTypeHyp CFSG.Walter.jtThreeHyp hq)
  rw [JRGroup.toReeTypeHyp_q] at hqK
  refine isCyclic_sylow_of_mulEquiv e (fun Q => ?_) P
  exact CFSG.Walter.Ree.reeGamma_isCyclic_sylow a ha K hK p (hqK ▸ hp) Q

theorem rCyclicSylow_of_reeIdentNative
    (hR : ReeIdentNative) : RCyclicSylow :=
  rCyclicSylow_of_hall (hall_of_reeIdentNative hR)

theorem theorem_of_reeIdentNative
    (h66 : S_prop_6_6) (hR : ReeIdentNative) : Theorem :=
  theorem_of_rCyclicSylow h66 (rCyclicSylow_of_reeIdentNative hR)

end CFSG.Walter.W67
