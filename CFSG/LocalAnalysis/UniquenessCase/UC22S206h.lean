module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Quasithin.H13.A7Blk (ptPre mem_ptPre ptCore ptCore_le coe_ptHom ptHom)

variable {G : Type} [Group G]

theorem uc22s206h_commute (i : Fin 9) {σ : alternatingGroup (Fin 8)}
    (h0 : (σ : Equiv.Perm (Fin 8)) 0 = 0) (h1 : (σ : Equiv.Perm (Fin 8)) 1 = 1) :
    Commute (uc22s206gC i) (uc22s206gEmb i σ : alternatingGroup (Fin 9)) := by
  have key : ∀ (f : Equiv.Perm (Fin 9)) (u v : Fin 9), f u = u → f v = v →
      f * Equiv.swap u v = Equiv.swap u v * f := by
    intro f u v hu hv
    rw [Equiv.mul_swap_eq_swap_mul, hu, hv]
  have hE1 := key (uc22s206gExt i σ) i (i.succAbove 1) (uc22s206gExt_self i σ)
    (by rw [uc22s206gExt_succAbove, h1])
  have hE0 := key (uc22s206gExt i σ) i (i.succAbove 0) (uc22s206gExt_self i σ)
    (by rw [uc22s206gExt_succAbove, h0])
  apply Subtype.ext
  show Equiv.swap i (i.succAbove 1) * Equiv.swap i (i.succAbove 0) * uc22s206gExt i σ =
    uc22s206gExt i σ * (Equiv.swap i (i.succAbove 1) * Equiv.swap i (i.succAbove 0))
  rw [mul_assoc, ← hE0, ← mul_assoc, ← hE1, mul_assoc]

theorem uc22s206h_not_le_of_commute [Finite G] {L M : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hLM : L ⊓ M = ptPre α i) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {x : ↥L} (hxq : orderOf x = q) {c : alternatingGroup (Fin 9)}
    (hc : Commute c (α x)) (hci : (c : Equiv.Perm (Fin 9)) i ≠ i) :
    ¬ normalizer (zpowers (x : G) : Set G) ≤ M := by
  intro hle
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup q (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxq, pow_one])
  have h2 : IsPGroup 2 α.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hcop : Nat.Coprime q (Nat.card α.ker) := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hcN : c ∈ normalizer ((zpowers (α x) : Subgroup (alternatingGroup (Fin 9))) :
      Set (alternatingGroup (Fin 9))) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact (hc.zpow_right k).eq.symm
  have himg := CFSG.SignalizerFunctor.Helpers.coprime_surjective_normalizer_image q hq α hα
    (zpowers x) hcop hpg
  rw [MonoidHom.map_zpowers] at himg
  rw [← himg] at hcN
  obtain ⟨n, hn, hnc⟩ := hcN
  have hnG : (n : G) ∈ normalizer (zpowers (x : G) : Set G) := by
    have h := le_normalizer_map L.subtype (mem_map_of_mem L.subtype hn)
    rw [MonoidHom.map_zpowers, Subgroup.coe_subtype] at h
    exact h
  have hnLM : (n : G) ∈ L ⊓ M := ⟨n.2, hle hnG⟩
  rw [hLM, mem_ptPre] at hnLM
  obtain ⟨_, hni⟩ := hnLM
  apply hci
  rw [← hnc]
  exact hni

theorem uc22s206h_normalizer_not_le [Finite G] {L M : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hLM : L ⊓ M = ptPre α i)
    {x : ↥(ptCore α i)} (hx : ptHom α i x = uc22s206gEmb i uc22s206dX0) (hx3 : orderOf x = 3) :
    ¬ normalizer (zpowers (x : G) : Set G) ≤ M := by
  have hαx : α (Subgroup.inclusion (ptCore_le α i) x) =
      (uc22s206gEmb i uc22s206dX0 : alternatingGroup (Fin 9)) := by
    rw [← hx, coe_ptHom]
    rfl
  have hx3' : orderOf (Subgroup.inclusion (ptCore_le α i) x) = 3 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective (ptCore_le α i)), hx3]
  refine uc22s206h_not_le_of_commute α hα hker hLM Nat.prime_three (by decide) hx3'
    (c := uc22s206gC i) ?_ ?_
  · rw [hαx]
    exact uc22s206h_commute i (by decide) (by decide)
  · rw [uc22s206gC_apply]
    exact Fin.succAbove_ne i 0

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
