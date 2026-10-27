module

public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.Background.E1Amb
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Quasithin CFSG.Open

universe u v

theorem eOne_of_surjective_of_isPGroup_ker
    {K : Type u} {Γ : Type v}
    [Group K] [Group Γ] [Finite K] [Finite Γ]
    (π : K →* Γ) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker) (A : Subgroup K)
    (hOne : CFSG.Quasithin.E1.EOne Γ (A.map π)) :
    CFSG.Quasithin.E1.EOne K A := by
  obtain ⟨p, hp, hp2, hoTwo, hne, hcomm, hcard⟩ := hOne
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (CFSG.pCore 2 K).map π = CFSG.pCore 2 Γ :=
    CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker π hπ hker
  have hker_le : π.ker ≤ CFSG.pCore 2 K :=
    CFSG.LieType.BorelTits.le_pCore 2 π.normal_ker hker
  have hcomap : (CFSG.pCore 2 Γ).comap π = CFSG.pCore 2 K := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self hker_le
  let f : K →* Γ ⧸ CFSG.pCore 2 Γ :=
    (QuotientGroup.mk' (CFSG.pCore 2 Γ)).comp π
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hπ
  have hkerf : CFSG.pCore 2 K = f.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let e : (K ⧸ CFSG.pCore 2 K) ≃* (Γ ⧸ CFSG.pCore 2 Γ) :=
    (QuotientGroup.quotientMulEquivOfEq hkerf).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : ∀ k : K, e (QuotientGroup.mk' (CFSG.pCore 2 K) k) =
      QuotientGroup.mk' (CFSG.pCore 2 Γ) (π k) := fun _ => rfl
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 K)) =
      (QuotientGroup.mk' (CFSG.pCore 2 Γ)).comp π :=
    MonoidHom.ext he
  have hbar : (E1.barO2 K A).map e.toMonoidHom = E1.barO2 Γ (A.map π) := by
    unfold E1.barO2
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  have h2 : IsPGroup 2 ((CFSG.pCore 2 Γ).comap π) :=
    IsPGroup.comap_of_ker_isPGroup
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := Γ) (r := 2)) π hker
  have hpPow : ∀ x ∈ (E1.oTwoP Γ p).comap π,
      ∃ k : ℕ, x ^ p ^ k ∈ (CFSG.pCore 2 Γ).comap π := by
    intro x hx
    obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_oTwoP (p := p) ((Subgroup.mem_comap).mp hx)
    exact ⟨k, by rwa [Subgroup.mem_comap, map_pow]⟩
  have hqPow : ∀ q : K, ∃ k : ℕ, q ^ 2 ^ k ∈ (E1.oTwoP Γ p).comap π := by
    intro q
    obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_pCore (Q := Γ) (M := E1.oTwoP Γ p)
      (fun y => by
        have hy : y ∈ E1.oTwoPTwo Γ p := by
          rw [hoTwo]
          exact Subgroup.mem_top _
        simpa [E1.oTwoPTwo] using hy) (π q)
    exact ⟨k, by rwa [Subgroup.mem_comap, map_pow]⟩
  have hoTwoK : E1.oTwoPTwo K p = ⊤ :=
    E1.oTwoPTwo_eq_top_of_series
      (N₂ := (CFSG.pCore 2 Γ).comap π) (N₂p := (E1.oTwoP Γ p).comap π)
      h2 hpPow hqPow
  have hmapP : (CFSG.pCore p (K ⧸ CFSG.pCore 2 K)).map e.toMonoidHom =
      CFSG.pCore p (Γ ⧸ CFSG.pCore 2 Γ) :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  have hneK : CFSG.pCore p (K ⧸ CFSG.pCore 2 K) ≠ ⊥ := by
    intro hbot
    apply hne
    simpa [hbot] using hmapP.symm
  have hcommK : CFSG.pCore p (K ⧸ CFSG.pCore 2 K) =
      ⁅CFSG.pCore p (K ⧸ CFSG.pCore 2 K), E1.barO2 K A⁆ := by
    apply (E1.map_inj_mulEquiv e).mp
    rw [Subgroup.map_commutator, hmapP, hbar]
    exact hcomm
  have hcardK : Nat.card (E1.barO2 K A) = 2 := by
    have h := Subgroup.card_map_of_injective (K := E1.barO2 K A)
      (f := e.toMonoidHom) e.injective
    rw [hbar, hcard] at h
    exact h.symm
  exact ⟨p, hp, hp2, hoTwoK, hneK, hcommK, hcardK⟩

end E1

end CFSG.Quasithin
