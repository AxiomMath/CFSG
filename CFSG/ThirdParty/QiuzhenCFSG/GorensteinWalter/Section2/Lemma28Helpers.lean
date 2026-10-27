module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection

namespace CFSG
end CFSG
open CFSG

/-!
# Elementary endpoints for Lemma 2.8

This lower-layer module records two steps used in Bender's proof of Lemma 2.8.
First, if `S₀` centralizes `U`, then it normalizes every subgroup of `U`.
Second, the hypothesis that `I_U(s)` is a subgroup gives the standard
Fact 1.5(iii) conclusion: that subgroup is abelian, normal in `U`, and lies
in `F(U)`.  The structural contradiction in Lemma 2.8 (and the choice of a
nontrivial subgroup of an inverted set) is intentionally left to the owning
Section 2 theorem.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `S₀` centralizes `U`, then it normalizes every subgroup of `U`. -/
public theorem centralizerSetup_S0_le_normalizer_of_commutator_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {X : Subgroup G}
    (hcomm : ⁅c.S0, c.U⁆ = ⊥) (hX : X ≤ c.U) :
    c.S0 ≤ Subgroup.normalizer (X : Set G) := by
  have hcentU : c.S0 ≤ Subgroup.centralizer (c.U : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hcentX : c.S0 ≤ Subgroup.centralizer (X : Set G) :=
    hcentU.trans (Subgroup.centralizer_le (by
      intro x hx
      exact hX hx))
  exact hcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))

/-- A reflection-inverted subgroup is abelian, normal in `U`, and contained in
`F(U)`.  This is Fact 1.5(iii) specialized to the fixed centralizer setup. -/
public theorem centralizerSetup_reflection_invertedSubgroup_abelian_normal
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {I : Subgroup G} (hI : IsInvertedSubgroup I c.U s) :
    IsMulCommutative I ∧ IsNormalIn I c.U ∧ I ≤ c.FU := by
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c hs
  have hsH : s ∈ c.H := by
    exact centralizerSetup_S_le_H c hs.1
  have hcop : Nat.Coprime 2 (Nat.card (↥c.U)) := by
    change Nat.Coprime 2
      (Nat.card (↥((pPrimeCore 2 c.H).map c.H.subtype)))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hsU : ∀ x : G, x ∈ c.U → s * x * s⁻¹ ∈ c.U := by
    intro x hx
    have hxU : x ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
      simpa [CentralizerSetup.U, oddCoreOf] using hx
    have hxH : x ∈ c.H :=
      SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H)
        (pPrimeCore 2 c.H)) hxU
    have hchar : (pPrimeCore 2 c.H).Characteristic :=
      pPrimeCore_characteristic (p := 2) (G := c.H)
    have hcomap : (pPrimeCore 2 c.H) ≤
        (pPrimeCore 2 c.H).comap
          (MulAut.conj ⟨s, hsH⟩).toMonoidHom :=
      (Subgroup.characteristic_iff_le_comap.mp hchar)
        (MulAut.conj ⟨s, hsH⟩)
    have hxK : (⟨x, hxH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
      rcases (Subgroup.mem_map.mp hxU) with ⟨y, hy, hyeq⟩
      have hyeq' : (⟨x, hxH⟩ : ↥c.H) = y := by
        ext
        simpa using hyeq.symm
      simpa [hyeq'] using hy
    have hconj : (MulAut.conj ⟨s, hsH⟩) ⟨x, hxH⟩ ∈
        pPrimeCore 2 c.H :=
      Subgroup.mem_comap.mp (hcomap hxK)
    refine Subgroup.mem_map.mpr ?_
    refine ⟨⟨s * x * s⁻¹,
      c.H.mul_mem (c.H.mul_mem hsH hxH) (c.H.inv_mem hsH)⟩, ?_, rfl⟩
    have hcx : (MulAut.conj ⟨s, hsH⟩) ⟨x, hxH⟩ =
        (⟨s * x * s⁻¹,
          c.H.mul_mem (c.H.mul_mem hsH hxH) (c.H.inv_mem hsH)⟩ : ↥c.H) := by
      ext
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hcx]
    exact hconj
  exact fact_1_5_iii_inverted_subgroup_abelian_normal hsInv hcop hsU hI

end CFSG.GorensteinWalter
