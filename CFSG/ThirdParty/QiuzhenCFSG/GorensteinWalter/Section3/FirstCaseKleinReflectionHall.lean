module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Nontrivial inverted Hall subgroups in the Klein-four branch

The source uses `C_S(U) = O₂(Ĥ)` to show that the inverted Hall subgroup
attached to an involution outside `O₂(Ĥ)` cannot be trivial.  This module
proves that local step for reflections; the subsequent uniformity argument
will transport the result through the `D₆` quotient.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem oddCore_normal_local
    {G : Type u} [Group G] (H : Subgroup G) : IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem y hy
      (⟨h, hh⟩ : ↥H)

private theorem oddCore_card_eq_pPrimeCore_local
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (oddCoreOf H) = Nat.card (pPrimeCore 2 H) := by
  simpa [oddCoreOf] using
    (Subgroup.card_map_of_injective (K := pPrimeCore 2 H) H.subtype_injective)

private theorem mem_centralizerIn_iff_local
    {G : Type u} [Group G] (X : Subgroup G) (s x : G) :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ s * x * s⁻¹ = x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hcomm : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
    rw [hcomm]
    simp
  · rintro ⟨hx, hfix⟩
    refine ⟨hx, ?_⟩
    change x ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = s := by simpa using hy
    rw [hy']
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hfix)

public theorem firstCase_klein_reflection_hall_nontrivial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (s : G) (hs : c.IsReflection s)
    (hsV : s ∉ twoCoreOf c.Hhat) :
    ∃ I : Subgroup G,
      IsInvertedSubgroup I c.U s ∧ IsHallIn I c.FU ∧ I ≠ ⊥ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I, hI, hHall⟩ := hfirst.1 s hs
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c hs
  have hsH : s ∈ c.H := centralizerSetup_S_le_H c hs.1
  have hUnorm : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    exact oddCore_normal_local c.H
  have hsNormU : ∀ x : G, x ∈ c.U → s * x * s⁻¹ ∈ c.U := by
    intro x hx
    exact hUnorm.2 s hsH x hx
  have hUodd : Nat.Coprime 2 (Nat.card (↥c.U)) := by
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
    rw [oddCore_card_eq_pPrimeCore_local]
    simpa using pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hIne : I ≠ ⊥ := by
    intro hIbot
    have hdecomp := fact_1_5_ii_decomposition
      (G := G) (X := c.U) (s := s) hsInv hUodd hsNormU
    have hsCentU : ∀ x : G, x ∈ c.U → s * x * s⁻¹ = x := by
      intro x hx
      obtain ⟨z, hzC, i, hiI, hxi⟩ := hdecomp x hx
      have hiBot : i = 1 := by
        apply (Subgroup.eq_bot_iff_forall (H := I)).1 hIbot
        change i ∈ (I : Set G)
        change (I : Set G) = invertedElements c.U s at hI
        rw [hI]
        exact hiI
      rw [hiBot] at hxi
      calc
        s * x * s⁻¹ = s * (z * 1) * s⁻¹ := by rw [hxi]
        _ = s * z * s⁻¹ := by simp
        _ = z := ((mem_centralizerIn_iff_local c.U s z).1 hzC).2
        _ = x := by simpa using hxi.symm
    have hsVmem : s ∈ twoCoreOf c.Hhat := by
      have hsS : s ∈ (c.S : Subgroup G) := hs.1
      have hsC : s ∈ Subgroup.centralizer (c.U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        calc
          x * s = (s * x * s⁻¹) * s := by rw [hsCentU x hx]
          _ = s * x := by group
      have h26 := theorem_2_6 hmin c
      rw [← h26.2.1]
      exact ⟨hsS, hsC⟩
    exact hsV hsVmem
  exact ⟨I, hI, hHall, hIne⟩

end CFSG.GorensteinWalter
