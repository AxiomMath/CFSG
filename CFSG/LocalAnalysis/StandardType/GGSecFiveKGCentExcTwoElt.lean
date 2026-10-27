module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotToral
import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcCoroot

public section

namespace CFSG.StandardType.KGCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F
  CFSG.StandardType.LayerExc

theorem eq_one_of_commute_famKernel_rootSpan
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1) {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K) (h2 : ∃ k : ℕ, g ^ 2 ^ k = 1)
    (hcomm : ∀ a ∈ F, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g)
    (hc : g ∈ Subgroup.centralizer (rootSpan τ K (famKernel F) : Set (ModGL τ K))) :
    g = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => hp2' (hζ ▸ orderOf_dvd_of_pow_eq_one h)
  choose! A hA using fun β (hβ : IsRoot τ β) => exists_rootDiagUnit_mem_rootSpan_pair hτ hβ ζ
  set F' : Set (Fin τ.rank → Kˣ) := F ∪ A '' famKernel F
  have hF'p : ∀ a ∈ F', ∀ i, a i ^ p = 1 := by
    rintro a (ha | ⟨β, hβ, rfl⟩) i
    · exact hF a ha i
    · obtain ⟨m, hm⟩ := (hA β hβ.1).2.2 i
      rw [hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have hker : famKernel F' = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun α hα => ?_
    have hαF : α ∈ famKernel F := ⟨hα.1, fun a ha => hα.2 a (Or.inl ha)⟩
    have h1 := hα.2 (A α) (Or.inr ⟨α, hαF, rfl⟩)
    rw [(hA α hα.1).2.1] at h1
    exact hζ2 h1
  have hcomm' : ∀ a ∈ F', rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g := by
    rintro a (ha | ⟨β, hβ, rfl⟩)
    · exact hcomm a ha
    · have hmem : rootDiagUnit τ (A β) ∈ rootSpan τ K (famKernel F) :=
        rootSpan_mono (Set.insert_subset hβ (Set.singleton_subset_iff.2 (neg_mem_famKernel hβ)))
          (hA β hβ.1).1
      rw [Subgroup.mem_centralizer_iff.1 hc _ hmem, mul_inv_cancel_right]
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hgeq⟩ := fam_factor F' hg hcomm'
  have hbot : rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [hker, Set.empty_inter, hbot, Subgroup.mem_bot] at hu hv
  rw [hu, hv, mul_one, mul_one] at hgeq
  obtain ⟨k, hk⟩ := h2
  have hM : MapsRootLines g w := by
    rw [hgeq]
    simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep (R := K) w)
  have hMpow : ∀ m : ℕ, MapsRootLines (g ^ m) (w ^ m) := by
    intro m
    induction m with
    | zero => simpa using (mapsRootLines_one : MapsRootLines (1 : ModGL τ K) 1)
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul hM
  have hw2 : w ^ 2 ^ k = 1 := by
    have h' := hMpow (2 ^ k)
    rw [hk] at h'
    exact (mapsRootLines_one.unique h').symm
  have hpU : ¬ p ∣ Nat.card (Subgroup.zpowers w) := by
    rw [Nat.card_zpowers]
    exact fun hdvd => hp2' (hp.dvd_of_dvd_pow (hdvd.trans (orderOf_dvd_of_pow_eq_one hw2)))
  have hle := LayerExc.le_famReflectionGroup_of_coprime hp F'
    (fun a ha => ⟨1, funext fun i => by simpa using hF'p a ha i⟩) _
    ((Subgroup.zpowers_le (G := WeylGroup τ)).2 hw) hpU
  have hrefl : famReflectionGroup F' = ⊥ := by
    rw [famReflectionGroup, hker]
    simp
  have hw1 : w = 1 := by
    have hmem := hle (Subgroup.mem_zpowers w)
    rwa [hrefl, Subgroup.mem_bot] at hmem
  rw [hw1, canonicalRep_one, mul_one] at hgeq
  rw [hgeq] at hk ⊢
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Kˣ) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 odd_card_units)
  have h1 := pow_gcd_eq_one.2 ⟨hk, pow_eq_one_of_mem_torusGroup hh⟩
  rwa [hcop.gcd_eq_one, pow_one] at h1

end CFSG.StandardType.KGCentExc

end
