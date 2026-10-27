module


import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open Equiv

namespace S143

namespace InspW2

theorem a8_embedding {L Gc : Type} [Group L] [Group Gc] (e : L ≃* alternatingGroup (Fin 8))
    (ρ : Gc →* MulAut L) (hρ : Function.Injective ρ) :
    ∃ ψ : Gc →* Perm (Fin 8), Function.Injective ψ ∧ ∀ (l : L) (g : Gc),
      ρ g = MulAut.conj l → ψ g = ((e l : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  let c : Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 8))
  let cE : Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) := MulEquiv.ofBijective c hbij
  refine ⟨(cE.symm : MulAut (alternatingGroup (Fin 8)) →* Perm (Fin 8)).comp
    ((MulAut.congr e).toMonoidHom.comp ρ), ?_, ?_⟩
  · intro a b hab
    apply hρ
    apply (MulAut.congr e).injective
    exact cE.symm.injective hab
  · intro l g hg
    show cE.symm (MulAut.congr e (ρ g)) = _
    rw [hg, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.symm_apply_eq]
    ext x
    simp [cE, c, MulAut.conjNormal_apply, MulAut.conj_apply]

theorem involution_cycleType8 (σ : Perm (Fin 8)) (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : Perm.sign σ = 1) :
    σ.cycleType = Multiset.replicate 2 2 ∨ σ.cycleType = Multiset.replicate 4 2 := by
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
  rcases hk24 with h | h
  · exact Or.inl (by rw [hrep, h])
  · exact Or.inr (by rw [hrep, h])

theorem card_centralizer8_two (σ : Perm (Fin 8)) (h : σ.cycleType = Multiset.replicate 2 2) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) = 192 := by
  rw [Equiv.Perm.nat_card_centralizer σ, h]
  decide +kernel

theorem exists_odd_centralizer8 (σ : Perm (Fin 8)) (h : σ.cycleType = Multiset.replicate 2 2) :
    ∃ τ : Perm (Fin 8), τ * σ = σ * τ ∧ Perm.sign τ = -1 := by
  have hsupp : σ.support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, h]
    simp
  have hfix : 1 < (Finset.univ \ σ.support).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hsupp]
    simp
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hfix
  have ha' : σ a = a := by
    by_contra hne
    exact (Finset.mem_sdiff.mp ha).2 (Equiv.Perm.mem_support.mpr hne)
  have hb' : σ b = b := by
    by_contra hne
    exact (Finset.mem_sdiff.mp hb).2 (Equiv.Perm.mem_support.mpr hne)
  refine ⟨swap a b, ?_, Equiv.Perm.sign_swap hab⟩
  have h1 := swap_apply_apply σ a b
  rw [ha', hb'] at h1
  calc swap a b * σ = (σ * swap a b * σ⁻¹) * σ := by rw [← h1]
    _ = σ * swap a b := by group

end InspW2

end S143

end CFSG.Quasithin
