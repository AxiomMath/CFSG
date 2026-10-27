module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporSylow
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.Bar
  CFSG.Quasithin.E6.Inn CFSG.Blueprint

theorem center_eq_pCore_of_simple_quotient {X : Type*} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hs : IsSimpleGroup (X ⧸ CFSG.pCore 2 X)) :
    center X = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpc_le : CFSG.pCore 2 X ≤ center X := by
    have hTop : CFSG.IsComponent (⊤ : Subgroup X) :=
      ⟨isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
        Subgroup.Normal.isSubnormal inferInstance⟩
    have hle := CFSG.LocalAnalysis.ComponentInitial.isComponent_le_centralizer_of_isPGroup
      (p := 2) hTop CFSG.pCore_normal CFSG.pCore_isPGroup
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) x hx).symm
  refine le_antisymm ?_ hpc_le
  have hnorm : ((center X).map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal ((center X).map (QuotientGroup.mk' (CFSG.pCore 2 X))) with
    h | h
  · intro x hx
    have hx' : (QuotientGroup.mk' (CFSG.pCore 2 X)) x ∈
        (center X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 hx'
  · exfalso
    have hall : ∀ x : X, x ∈ center X := by
      intro x
      have hx : (QuotientGroup.mk' (CFSG.pCore 2 X)) x ∈
          (center X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := h ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := hx
      have h1 : c⁻¹ * x ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hcx
      have h2 : c⁻¹ * x ∈ center X := hpc_le h1
      have h3 : x = c * (c⁻¹ * x) := by group
      rw [h3]
      exact mul_mem hc h2
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hall a₀) b₀).symm

theorem e68CentCompSpor_of
    (hsimp : ∀ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hfix : ∀ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s →
      InvolFixInner (NativeSporadic.Carrier s))
    (hc : ∀ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s →
      Cent2NoComp (NativeSporadic.Carrier s)) : E68CentCompSpor := by
  intro Y _ _ L R K z u hF h hK
  exfalso
  obtain ⟨⟨s, hs, ⟨e⟩⟩, -⟩ := hF
  have hsim : IsSimpleGroup (NativeSporadic.Carrier s) := hsimp s hs
  have hsimL : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
  have hZ : center ↥L = CFSG.pCore 2 ↥L := center_eq_pCore_of_simple_quotient h.quasisimple hsimL
  let e' : Qbar L ≃* NativeSporadic.Carrier s := (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  exact not_isComponentIn_of_cent2 h (InvolFixInner.of_mulEquiv e' (hfix s hs))
    (Cent2NoComp.of_mulEquiv e' (hc s hs)) K hK

end CFSG.Quasithin.E6.Spor
