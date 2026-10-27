module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.Monster.Schur.Defs
public import Mathlib.RepresentationTheory.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

section CharTwo

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

private theorem add_self_eq_zero_of_zmod_two (x : M) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

private theorem nsmul_eq_self_of_odd {k : ℕ} (hk : Odd k) (x : M) : k • x = x := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul, mul_nsmul', one_nsmul, two_nsmul, add_self_eq_zero_of_zmod_two]
  simp

private theorem neg_eq_self_of_zmod_two (x : M) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod_two x)

private theorem sub_comm_of_zmod_two (x y : M) : x - y = y - x := by
  rw [← neg_sub y x, neg_eq_self_of_zmod_two]

end CharTwo

section Odd

variable {Γ M : Type*} [Group Γ] [AddCommGroup M] [Module (ZMod 2) M]

private theorem principal_of_vanishing {ρ : Representation (ZMod 2) Γ M} {P : Subgroup Γ}
    (hP : Odd P.index) (δ : Γ → M) (hδ : ∀ g h, δ (g * h) = δ g + ρ g (δ h))
    (hP0 : ∀ p ∈ P, δ p = 0) : ∃ u : M, ∀ g, δ g = ρ g u - u := by
  classical
  have hfin : Finite (Γ ⧸ P) := Nat.finite_of_card_ne_zero hP.pos.ne'
  let _ : Fintype (Γ ⧸ P) := Fintype.ofFinite _
  refine ⟨∑ q : Γ ⧸ P, δ q.out, fun g => ?_⟩
  have key : ∀ q : Γ ⧸ P, δ g = δ (g • q).out - ρ g (δ q.out) := by
    intro q
    have e : g * q.out = (g • q).out * ((g • q).out⁻¹ * g * q.out) := by group
    have h1 := hδ g q.out
    rw [e, hδ, hP0 _ (CFSG.GroupTheory.ComplementLifting.out_inv_mul_mem g q), map_zero,
      add_zero] at h1
    exact eq_sub_of_add_eq h1.symm
  have hsum : ∑ _q : Γ ⧸ P, δ g = ∑ q : Γ ⧸ P, (δ (g • q).out - ρ g (δ q.out)) :=
    Finset.sum_congr rfl fun q _ => key q
  have hperm : ∑ q : Γ ⧸ P, δ (g • q).out = ∑ q : Γ ⧸ P, δ q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : Γ ⧸ P => δ q.out)
  rw [Finset.sum_const, Finset.card_univ, Finset.sum_sub_distrib, ← map_sum, hperm] at hsum
  have hcard : Fintype.card (Γ ⧸ P) = P.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcard, nsmul_eq_self_of_odd hP] at hsum
  rw [hsum, sub_comm_of_zmod_two]

theorem principal_of_odd_index (ρ : Representation (ZMod 2) Γ M) {P : Subgroup Γ}
    (hP : Odd P.index) (δ : Γ → M) (hδ : ∀ g h, δ (g * h) = δ g + ρ g (δ h))
    (hPδ : ∃ v : M, ∀ p ∈ P, δ p = ρ p v - v) :
    ∃ v : M, ∀ g, δ g = ρ g v - v := by
  obtain ⟨v₀, hv₀⟩ := hPδ
  let δ' : Γ → M := fun g => δ g - (ρ g v₀ - v₀)
  have hδ' : ∀ g h, δ' (g * h) = δ' g + ρ g (δ' h) := by
    intro g h
    simp only [δ', hδ, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hP0 : ∀ p ∈ P, δ' p = 0 := fun p hp => by
    simp only [δ', hv₀ p hp, sub_self]
  obtain ⟨u, hu⟩ := principal_of_vanishing hP δ' hδ' hP0
  refine ⟨u + v₀, fun g => ?_⟩
  have h1 : δ g = ρ g u - u + (ρ g v₀ - v₀) := by
    rw [← hu g]
    simp only [δ']
    abel
  rw [h1, map_add]
  abel

theorem principal_of_odd_index_dual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Γ V) {P : Subgroup Γ} (hP : Odd P.index)
    (f : Γ → Module.Dual (ZMod 2) V)
    (hf : ∀ g h v, f (g * h) v = f g (ρ h v) + f h v)
    (hPf : ∃ φ : Module.Dual (ZMod 2) V, ∀ p ∈ P, ∀ v, f p v = φ (ρ p v) - φ v) :
    ∃ φ : Module.Dual (ZMod 2) V, ∀ g v, f g v = φ (ρ g v) - φ v := by
  obtain ⟨φ, hφ⟩ := hPf
  obtain ⟨ψ, hψ⟩ := principal_of_odd_index (M := Module.Dual (ZMod 2) V) ρ.dual hP
    (fun g => f g⁻¹)
    (fun g h => by
      ext v
      simp only [mul_inv_rev, hf, LinearMap.add_apply, Representation.dual_apply,
        Module.Dual.transpose_apply, LinearMap.comp_apply]
      exact add_comm _ _)
    ⟨φ, fun p hp => by
      ext v
      simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.sub_apply,
        LinearMap.comp_apply]
      exact hφ p⁻¹ (P.inv_mem hp) v⟩
  refine ⟨ψ, fun g v => ?_⟩
  have h := congrArg (fun m => m v) (hψ g⁻¹)
  simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h

end Odd

section Assembly

variable {E : Type*} [Group E]

theorem exists_central_involution_of_card_ker_eq_two {G : Type*} [Group G] (π : E →* G)
    (h : Nat.card π.ker = 2) :
    ∃ n : E, n ≠ 1 ∧ n ∈ Subgroup.center E ∧ n * n = 1 ∧ π.ker = Subgroup.zpowers n := by
  obtain ⟨n, hn1, hn⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).1 h
  have hne : (n : E) ≠ 1 := fun e => hn1 (Subtype.ext e)
  have hall : ∀ x ∈ π.ker, x = 1 ∨ x = (n : E) := fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (congrArg Subtype.val (hn ⟨x, hx⟩ (fun e => h1 (congrArg Subtype.val e))))
  have hsq : (n : E) * n = 1 := by
    rcases hall _ (π.ker.mul_mem n.2 n.2) with h1 | h1
    · exact h1
    · exact absurd (mul_eq_left.1 h1) hne
  refine ⟨n, hne, ?_, hsq, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    have hmem : g * n * g⁻¹ ∈ π.ker := π.normal_ker.conj_mem n n.2 g
    rcases hall _ hmem with h1 | h1
    · exact absurd (by simpa using h1) hne
    · exact mul_inv_eq_iff_eq_mul.1 h1
  · ext x
    constructor
    · intro hx
      rcases hall x hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact π.ker.zpow_mem n.2 k

theorem finite_of_card_ker_ne_zero {G : Type*} [Group G] [Finite G] (π : E →* G)
    (h : Nat.card π.ker ≠ 0) : Finite E := by
  have hker : Finite π.ker := Nat.finite_of_card_ne_zero h
  have hq : Finite (E ⧸ π.ker) :=
    Finite.of_injective (QuotientGroup.kerLift π) (QuotientGroup.kerLift_injective π)
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := π.ker)).symm

theorem index_ne_two_of_isPerfect [Group.IsPerfect E] (D : Subgroup E) : D.index ≠ 2 := by
  intro h2
  have : D.Normal := Subgroup.normal_of_index_eq_two h2
  have hcard : Nat.card (E ⧸ D) = 2 := h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (E ⧸ D) := isCyclic_of_prime_card hcard
  have : IsMulCommutative (E ⧸ D) := inferInstance
  have : Subsingleton (E ⧸ D) := Group.IsPerfect.subsingleton_of_isMulCommutative
  have h1 : Nat.card (E ⧸ D) = 1 := Nat.card_unique
  omega

theorem eq_one_of_odd_index_complement [Finite E] [Group.IsPerfect E] {n : E}
    (hn : n ∈ Subgroup.center E) (hn2 : n * n = 1) {H D : Subgroup E} (hodd : Odd H.index)
    (hDn : D ⊓ Subgroup.zpowers n = ⊥) (hDsup : D ⊔ Subgroup.zpowers n = H) : n = 1 := by
  by_contra hn1
  have hcomm : ∀ g : E, Commute g n := fun g => Subgroup.mem_center_iff.1 hn g
  have hN : (Subgroup.zpowers n).Normal := ⟨fun x hx g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [((hcomm g).zpow_right k).mul_inv_cancel]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers n) k⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (Subgroup.zpowers n) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hn2) hn1
  have hcop : Nat.Coprime H.index (Nat.card (Subgroup.zpowers n)) := by
    rw [hcard]
    exact hodd.coprime_two_right
  obtain ⟨D', hcompl, -, -⟩ := CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting
    (Subgroup.zpowers n) H D hcop (by rwa [inf_comm]) (by rwa [sup_comm])
  exact index_ne_two_of_isPerfect D' (hcompl.index_eq_card.trans hcard)

theorem false_of_odd_index_complement {G : Type*} [Group G] [Finite G] [Group.IsPerfect E]
    (π : E →* G) (h2 : Nat.card π.ker = 2) {H D : Subgroup E} (hodd : Odd H.index)
    (hD : D ⊓ π.ker = ⊥) (hsup : D ⊔ π.ker = H) : False := by
  obtain ⟨n, hn1, hn, hn2, hker⟩ := exists_central_involution_of_card_ker_eq_two π h2
  have := finite_of_card_ker_ne_zero π (by rw [h2]; norm_num)
  rw [hker] at hD hsup
  exact hn1 (eq_one_of_odd_index_complement hn hn2 hodd hD hsup)

theorem noPerfectDoubleCover_of_odd_index_complement {G : Type*} [Group G] [Finite G]
    (h : ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → Group.IsPerfect E →
      Nat.card π.ker = 2 → ∃ H D : Subgroup E, Odd H.index ∧ D ⊓ π.ker = ⊥ ∧ D ⊔ π.ker = H) :
    NoPerfectDoubleCover G := by
  intro E _ π hπ hE h2
  have := hE
  obtain ⟨H, D, hodd, hD, hsup⟩ := h E π hπ hE h2
  exact false_of_odd_index_complement π h2 hodd hD hsup

end Assembly

end CFSG.Monster.Schur
