module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumM

import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint Equiv

namespace Insp7

theorem card_centralizer_perm8_le (σ : Perm (Fin 8)) (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : Perm.sign σ = 1) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) ≤ 384 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rwa [sq]) h1
  have hct : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1' : n ∣ 2 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h2' : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have h3 : n ≤ 2 := Nat.le_of_dvd (by norm_num) h1'
    omega
  set k := Multiset.card σ.cycleType with hk
  have hrep : σ.cycleType = Multiset.replicate k 2 := Multiset.eq_replicate.mpr ⟨rfl, hct⟩
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate]
    simp [mul_comm]
  have hle : 2 * k ≤ 8 := by
    have := Equiv.Perm.sum_cycleType_le σ
    simpa [hsum] using this
  have hk0 : k ≠ 0 := by
    intro h0
    exact h1 (Equiv.Perm.card_cycleType_eq_zero.mp h0)
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hs, hsum, ← hk] at hsign
  have heven : Even k := by
    have h3 : (-1 : ℤˣ) ^ (2 * k + k) = 1 := hsign.symm
    obtain ⟨m, hm⟩ := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp h3
    exact ⟨m - k, by omega⟩
  have hk24 : k = 2 ∨ k = 4 := by
    obtain ⟨j, hj⟩ := heven
    omega
  rw [Equiv.Perm.nat_card_centralizer σ, hrep]
  rcases hk24 with h | h
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel

theorem numFactAt_a8 : NumFactAt (fun L _ => StatedClassicalModel L .PSL 4 2 1) := by
  intro L _ _ _ hF z hz2 hzc Gc _ _ ρ hρ _ ž hž Ŝ _ _ _ hcard hC9
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff L).mp
    (Or.inl ⟨by decide, hF⟩)
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  let c : Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 8))
  let cE : Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) := MulEquiv.ofBijective c hbij
  let ψ : Gc →* Perm (Fin 8) :=
    (cE.symm : MulAut (alternatingGroup (Fin 8)) →* Perm (Fin 8)).comp
      ((MulAut.congr e).toMonoidHom.comp ρ)
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply hρ
    apply (MulAut.congr e).injective
    exact cE.symm.injective hab
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  set σ : Perm (Fin 8) := ((e z : alternatingGroup (Fin 8)) : Perm (Fin 8)) with hσ
  have hψž : ψ ž = σ := by
    show cE.symm (MulAut.congr e (ρ ž)) = σ
    rw [hž, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.symm_apply_eq]
    ext x
    simp [cE, c, hσ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hσ2 : σ * σ = 1 := by
    have h : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
    have := congrArg (fun a : alternatingGroup (Fin 8) => (a : Perm (Fin 8))) h
    simpa [hσ] using this
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hz1
    apply e.injective
    apply Subtype.ext
    simpa [hσ] using h
  have hσs : Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp (e z).2
  have h384 := card_centralizer_perm8_le σ hσ2 hσ1 hσs
  have hmap : (Subgroup.centralizer ({ž} : Set Gc)).map ψ ≤
      Subgroup.centralizer ({σ} : Set (Perm (Fin 8))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x * ž = ž * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hψž, ← map_mul, ← map_mul, hx']
  have hle : Nat.card (Subgroup.centralizer ({ž} : Set Gc)) ≤
      Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) := by
    have h1 := Subgroup.card_le_of_le hmap
    rwa [← Nat.card_congr (Subgroup.equivMapOfInjective _ ψ hψ).toEquiv] at h1
  have h128 : 2 ^ 7 ≤ Nat.card Ŝ := by
    rcases hcard with h | h
    · rw [h]
    · rw [h]
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

@[expose] def M11Fam (L : Type) [Group L] : Prop :=
  Nonempty (L ≃* NativeSporadic.Carrier .M11)

end Insp7

end CFSG.Quasithin
