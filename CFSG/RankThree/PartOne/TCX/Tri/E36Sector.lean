module

public import CFSG.RankThree.PartOne.TCX.Tri.RegularBound

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped Matrix

section Sector

variable
  {C : Type} [Group C] [Finite C] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {p f₀ : ℕ}
  {ι : C →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem tri_sector_e36 (h : IsShintani p ι (triF0 L f₀) (triPhi L p f₀) α₀) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hodd : ∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosure K L] (σ : K ≃+* K)
    (hKc : Nat.card K = (2 ^ (p * f₀)) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀))
    {k : Type} [Field k] [Finite k] [Algebra k L] [IsAlgClosure k L] (σk : k ≃+* k)
    (hkc : Nat.card k = (2 ^ f₀) ^ 3) (hσk : ∀ c, σk c = c ^ 2 ^ f₀)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hpd : (p : ℤ) ∣ ((2 ^ f₀ : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f₀ : ℕ) : ℤ) + 1)
    {x : C} (hx : orderOf x = p) (hxα : α₀ x = x) :
    RegularShape (2 ^ (p * f₀)) x ∨
      SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  have hp3 : 3 < p := by omega
  obtain ⟨w, hw, g₀, hg₀C, hg₀, hfr₁, hfr₂⟩ := tri_frame_e36 hf₀ k hkc σk hσk hε hp hp3 hpd L
  have hF₀ : triF0 L f₀ = twistHom TwistTag.D4 L (iterateFrobenius L 2 f₀) := rfl
  obtain ⟨c, hcα, hcmem⟩ := h.frame_transfer hp hF₀ σk hσk hfr₁ hfr₂ hx hxα
  obtain ⟨hmemT, -⟩ := mem_twistedTorusOf.1 hcmem
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmemT
  have hb' : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ := hb.symm
  have hbo : orderOf (rootDiagUnit TwistTag.D4.tag b) = p := by
    rw [hb']
    have e1 : orderOf (g₀⁻¹ * ι (c * x * c⁻¹) * g₀) = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective
        (ι (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι h.inj _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbT : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) (triF0 L f₀) := by
    rw [hb']
    exact hcmem
  rcases tri_kernel_e36 (f := f₀) hε hp L hw hbT hbo with hE | ⟨i, hi⟩
  · left
    obtain ⟨ψ, hψinj, -, hψt, hψT⟩ := tri_regular_of_frame h hp hp3 hg₀C hg₀ hx hb' hbT hE
    refine regularShape_of_torus_embedding ψ hψinj hψt fun y hy => ?_
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hψt y)
    have hT := hψT y
    rw [ha] at hT hy ⊢
    exact tri_regular_exponent_e36 hp hp5 hε hw hT hy
  · right
    exact tri_a2_layer h hp hp5 hf₀ hodd σ hKc hσ hε hw hg₀C hg₀ i hx hcα hb' hbT hi

end Sector

end CFSG.RankThree.PartOne.TCX.Tri
