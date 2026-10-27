module

public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable
  {τ : Tag} {K : Type} [Field K]

theorem exists_weyl_of_conj_torus {s s' g : ModGL τ K} (hs : s ∈ torusGroup τ K)
    (hs' : s' ∈ torusGroup τ K) (hg : g ∈ adjointGroup τ K) (hsg : s * g = g * s') :
    ∃ w : WeylGroup τ, s * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K w * s' := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
  rw [LieType.Chevalley.adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hbij := LieType.Chevalley.bijOn_bruhatCell (τ := τ) (K := K) w
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := hbij.surjOn hw
  simp only at hbu hb hu
  have hsB : s ∈ borelGroup τ K :=
    (le_sup_left : torusGroup τ K ≤ torusGroup τ K ⊔ posUnipotent τ K) hs
  have hnT : n ∈ normalizer (torusGroup τ K : Set (ModGL τ K)) :=
    (LieType.Chevalley.canonical_weyl_root_transport τ K).2.2 w
  have hk : s * n * s'⁻¹ * n⁻¹ ∈ torusGroup τ K := by
    have h1 : n * s'⁻¹ * n⁻¹ ∈ torusGroup τ K := (mem_normalizer_iff.1 hnT _).1 (inv_mem hs')
    rw [show s * n * s'⁻¹ * n⁻¹ = s * (n * s'⁻¹ * n⁻¹) by group]
    exact mul_mem hs h1
  have hu' : s' * u * s'⁻¹ ∈ rootSpan τ K (LieType.Chevalley.inversionSet w) :=
    (mem_normalizer_iff.1 (LieType.Chevalley.torusGroup_le_normalizer_rootSpan
      (fun α h => h.1) hs') u).1 hu
  have hb' : s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) ∈ borelGroup τ K :=
    mul_mem (mul_mem (mul_mem hsB hb) (inv_mem hsB))
      ((le_sup_left : torusGroup τ K ≤ torusGroup τ K ⊔ posUnipotent τ K) hk)
  have heq : s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) * n * (s' * u * s'⁻¹) = b * n * u := by
    calc s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) * n * (s' * u * s'⁻¹) =
        s * (b * n * u) * s'⁻¹ := by group
      _ = b * n * u := by rw [hbu, hsg, mul_inv_cancel_right]
  have hinj := hbij.injOn (x₁ := (s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹), s' * u * s'⁻¹))
    (x₂ := (b, u)) ⟨hb', hu'⟩ ⟨hb, hu⟩ heq
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨h1, -⟩ := hinj
  have hb'' : b ∈ (borelGroup τ K : Set (ModGL τ K)) := hb
  rw [hTB.2.2.2.2.1] at hb''
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := Set.mem_mul.1 hb''
  have hsu₀ : s * u₀ * s⁻¹ ∈ posUnipotent τ K :=
    (Subgroup.mem_normalizer_iff.1 (hTB.2.2.1 hs) u₀).1 hu₀
  have hc : s * h₀ = h₀ * s := hTB.1 s hs h₀ hh₀
  have e2 : s * u₀ * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) = u₀ := by
    calc s * u₀ * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) =
        h₀⁻¹ * (s * (h₀ * u₀) * s⁻¹ * (s * n * s'⁻¹ * n⁻¹)) := by
          rw [← mul_assoc s h₀, hc]
          group
      _ = u₀ := by rw [h1, inv_mul_cancel_left]
  have hk1 : s * n * s'⁻¹ * n⁻¹ = 1 := by
    have hkU : s * n * s'⁻¹ * n⁻¹ ∈ posUnipotent τ K := by
      rw [eq_inv_mul_of_mul_eq e2]
      exact mul_mem (inv_mem hsu₀) hu₀
    have h := LieType.Chevalley.torusGroup_inf_posUnipotent (τ := τ) (R := K)
    rw [eq_bot_iff] at h
    exact mem_bot.1 (h (mem_inf.2 ⟨hk, hkU⟩))
  refine ⟨w, ?_⟩
  calc s * n = s * n * s'⁻¹ * n⁻¹ * (n * s') := by group
    _ = n * s' := by rw [hk1, one_mul]

theorem rootDiagUnit_injective' :
    Function.Injective (rootDiagUnit τ : (Fin τ.rank → Kˣ) → ModGL τ K) := by
  intro b b' h
  funext i
  have hv := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))
    (rootVec τ K (Pi.single i 1))) h
  change rootDiag b (rootVec τ K _) = rootDiag b' (rootVec τ K _) at hv
  rw [rootDiag_rootVec _ (isRoot_single τ i), rootDiag_rootVec _ (isRoot_single τ i)] at hv
  have hne : rootVec τ K (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := by
    rw [LieType.Chevalley.rootVec_eq_single (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h1 := smul_left_injective K hne hv
  have e : ∀ c : Fin τ.rank → Kˣ, rootChar c (Pi.single i 1) = c i := fun c => by
    have := rootChar_nsmul_single c i 1
    rwa [one_nsmul, pow_one] at this
  rw [e, e] at h1
  exact Units.ext h1

theorem exists_weyl_of_conj_rootDiagUnit {a b : Fin τ.rank → Kˣ} {g : ModGL τ K}
    (ha : rootDiagUnit τ a ∈ torusGroup τ K) (hb : rootDiagUnit τ b ∈ torusGroup τ K)
    (hg : g ∈ adjointGroup τ K) (hconj : g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ a) :
    ∃ w : WeylGroup τ, weylTuple w b = a := by
  have hsg : rootDiagUnit τ a * g = g * rootDiagUnit τ b := by
    rw [← hconj]
    group
  obtain ⟨w, hw⟩ := exists_weyl_of_conj_torus ha hb hg hsg
  refine ⟨w, rootDiagUnit_injective' ?_⟩
  rw [← canonicalRep_conj_rootDiagUnit, ← hw]
  group

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
