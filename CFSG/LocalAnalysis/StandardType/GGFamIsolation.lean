module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LieType.Chevalley.NonClosedRootCensus

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Transfer

variable {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']

theorem exists_componentRoots_superset
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'} (i : KernelComponent χ)
    (h : componentRoots χ i ⊆ kernelRoots χ') :
    ∃ j : KernelComponent χ', componentRoots χ i ⊆ componentRoots χ' j := by
  obtain ⟨x₀, rfl⟩ := Quotient.exists_rep i
  have hx₀ : (x₀ : Fin τ.rank → ℤ) ∈ componentRoots χ ⟦x₀⟧ := ⟨x₀.2, rfl⟩
  refine ⟨⟦⟨x₀, h hx₀⟩⟧, ?_⟩
  have horth : ∀ α ∈ componentRoots χ ⟦x₀⟧ ∩ componentRoots χ' ⟦⟨x₀, h hx₀⟩⟧,
      ∀ β ∈ componentRoots χ ⟦x₀⟧,
        β ∉ componentRoots χ ⟦x₀⟧ ∩ componentRoots χ' ⟦⟨x₀, h hx₀⟩⟧ → iform α β = 0 := by
    rintro α ⟨-, hαk, hαj⟩ β hβ hβS
    by_contra hne
    exact hβS ⟨hβ, h hβ, (mk_eq_of_iform_ne_zero (α := ⟨β, h hβ⟩) (β := ⟨α, hαk⟩)
      (by rwa [iform_comm])).trans hαj⟩
  rcases (isRootComponent_componentRoots ⟦x₀⟧).irreducible _ Set.inter_subset_left horth with
    h0 | h0
  · have hmem : (x₀ : Fin τ.rank → ℤ) ∈
        componentRoots χ ⟦x₀⟧ ∩ componentRoots χ' ⟦⟨x₀, h hx₀⟩⟧ := ⟨hx₀, h hx₀, rfl⟩
    rw [h0] at hmem
    exact absurd hmem (Set.notMem_empty _)
  · intro x hx
    rw [← h0] at hx
    exact hx.2

theorem mem_componentRoots_of_mem_ratClosure
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} {β : Fin τ.rank → ℤ} (hβ : β ∈ ratClosure (componentRoots χ i))
    (hβk : β ∈ kernelRoots χ) : β ∈ componentRoots χ i := by
  by_contra hβΨ
  have horth : ∀ ψ ∈ componentRoots χ i, iform β ψ = 0 := by
    rintro ψ ⟨hψk, hψi⟩
    exact iform_eq_zero_of_mk_ne (α := ⟨β, hβk⟩) (β := ⟨ψ, hψk⟩)
      fun h => hβΨ ⟨hβk, h.trans hψi⟩
  exact (iform_self_pos_of_isRoot hβ.1).ne' (iform_eq_zero_of_mem_ratClosure horth hβ)

end Transfer

section Pin

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_eq_one_of_mem_addClosure (a : Fin τ.rank → Lˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, rootChar a γ = 1) {x : Fin τ.rank → ℤ} (hx : x ∈ AddSubgroup.closure S) :
    rootChar a x = 1 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact rootChar_zero a
  | add x y _ _ hx hy => rw [rootChar_add, hx, hy, one_mul]
  | neg x _ hx => rw [← neg_one_smul ℤ x, rootChar_zsmul', hx, one_zpow]

theorem fam_component_nonclosed_pin
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : ∀ u j, a u j ^ p = 1) (i : KernelComponent (famCharHom a))
    (hncl : ¬ RootsRationallyClosed τ (componentRoots (famCharHom a) i)) :
    ∃ (u₀ : ι) (j : KernelComponent (rootCharHom (a u₀))),
      componentRoots (rootCharHom (a u₀)) j = componentRoots (famCharHom a) i := by
  have hC := nonClosedRootCensus_holds
  have hΨ := isRootComponent_componentRoots i
  have hker : ∀ u, ∀ γ ∈ componentRoots (famCharHom a) i, rootChar (a u) γ = 1 :=
    fun u γ hγ => ((mem_kernelRoots_famChar a).1 hγ.1).2 u
  have hmem : ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
      (fun k => (β k : ℚ)) ∈ Submodule.span ℚ
        ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' componentRoots (famCharHom a) i) →
      (∀ u, rootChar (a u) β = 1) → β ∈ componentRoots (famCharHom a) i :=
    fun β hβ hsp h => mem_componentRoots_of_mem_ratClosure ⟨hβ, hsp⟩
      ((mem_kernelRoots_famChar a).2 ⟨hβ, h⟩)
  rcases hC τ hτ _ hΨ hncl with h2 | ⟨-, -, -, hmax⟩
  ·
    refine absurd (fun β hβ hsp => hmem β hβ hsp fun u => ?_) hncl
    have hsq : rootChar (a u) β ^ 2 = 1 := by
      have h := rootChar_eq_one_of_mem_addClosure (a u) (hker u) (h2 β hβ hsp)
      rwa [rootChar_zsmul', zpow_two, ← sq] at h
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have hcp := rootChar_pow_eq_one_of_forall (hap u) β
    rwa [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at hcp
  ·
    by_contra hno
    refine hncl fun β hβ hsp => hmem β hβ hsp fun u => ?_
    obtain ⟨j, hj⟩ := exists_componentRoots_superset (χ' := rootCharHom (a u)) i
      fun γ hγ => ⟨hΨ.isRoot γ hγ, hker u γ hγ⟩
    have hC' := isRootComponent_componentRoots j
    rcases hmax _ hC'.isRoot hC'.neg_mem hC'.add_mem hj with h | h
    · exact absurd ⟨u, j, h⟩ hno
    · have hβj : β ∈ componentRoots (rootCharHom (a u)) j := by
        rw [h]
        exact hβ
      exact hβj.1.2

end Pin

section Closed

variable {τ : Tag}

private theorem exists_int_mul_eq {n : ℕ} (x : Fin n → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : Fin n → ℤ, ∀ k, (c k : ℚ) = D * x k := by
  classical
  refine ⟨∏ k, (x k).den, Finset.prod_pos fun k _ => Nat.pos_of_ne_zero (x k).den_nz,
    fun k => (x k).num * ∏ j ∈ Finset.univ.erase k, ((x j).den : ℤ), fun k => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (x j).den) (Finset.mem_univ k)]
  push_cast
  rw [← Rat.mul_den_eq_num (x k)]
  ring

theorem exists_generic_functional
    {Ψ : Set (Fin τ.rank → ℤ)} (hcl : RootsRationallyClosed τ Ψ) :
    ∃ c : Fin τ.rank → ℤ, (∀ ψ ∈ Ψ, ∑ k, c k * ψ k = 0) ∧
      ∀ β : Fin τ.rank → ℤ, IsRoot τ β → β ∉ Ψ → ∑ k, c k * β k ≠ 0 := by
  classical
  set V := Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) with hV
  have : Finite {β : Fin τ.rank → ℤ // IsRoot τ β ∧ β ∉ Ψ} :=
    ((finite_setOf_isRoot τ).subset fun β (hβ : IsRoot τ β ∧ β ∉ Ψ) => hβ.1).to_subtype
  have hnot : ∀ β : {β : Fin τ.rank → ℤ // IsRoot τ β ∧ β ∉ Ψ},
      (fun k => ((β : Fin τ.rank → ℤ) k : ℚ)) ∉ V :=
    fun β hβV => β.2.2 (hcl β β.2.1 hβV)
  obtain ⟨l, hl, hl'⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists V.dualAnnihilator
    (fun β : {β : Fin τ.rank → ℤ // IsRoot τ β ∧ β ∉ Ψ} =>
      Module.Dual.eval ℚ (Fin τ.rank → ℚ) (fun k => ((β : Fin τ.rank → ℤ) k : ℚ)))
    fun β => by
      obtain ⟨f, hf, hVf⟩ := Submodule.exists_le_ker_of_notMem (hnot β)
      exact ⟨f, (Submodule.mem_dualAnnihilator f).2 fun w hw => LinearMap.mem_ker.1 (hVf hw), hf⟩
  obtain ⟨D, hD, c, hc⟩ := exists_int_mul_eq fun k => l fun j => if k = j then 1 else 0
  have hlin : ∀ v : Fin τ.rank → ℤ, ((∑ k, c k * v k : ℤ) : ℚ) = D * l fun k => (v k : ℚ) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ l, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc k, smul_eq_mul]
    ring
  refine ⟨c, fun ψ hψ => ?_, fun β hβ hβΨ h0 => ?_⟩
  · have h0 : l (fun k => (ψ k : ℚ)) = 0 :=
      (Submodule.mem_dualAnnihilator l).1 hl _ (Submodule.subset_span ⟨ψ, hψ, rfl⟩)
    have h := hlin ψ
    rw [h0, mul_zero] at h
    exact_mod_cast h
  · have h := hlin β
    rw [h0, Int.cast_zero] at h
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    exact hl' ⟨β, hβ, hβΨ⟩ ((mul_eq_zero.1 h.symm).resolve_left hD')

theorem exists_isolating_element_of_closed
    {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (i : KernelComponent (famCharHom a))
    (hcl : RootsRationallyClosed τ (componentRoots (famCharHom a) i)) :
    ∃ (N : ℕ) (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b)),
      N.Prime ∧ N ≠ 2 ∧ rootDiagUnit τ b ^ N = 1 ∧
        componentRoots (rootCharHom b) j = componentRoots (famCharHom a) i := by
  classical
  obtain ⟨c, hc0, hc1⟩ := exists_generic_functional hcl
  set B : ℕ := (finite_setOf_isRoot τ).toFinset.sup fun β => (∑ k, c k * β k).natAbs with hBdef
  have hB : ∀ β, IsRoot τ β → (∑ k, c k * β k).natAbs ≤ B := fun β hβ =>
    Finset.le_sup (f := fun β => (∑ k, c k * β k).natAbs) ((Set.Finite.mem_toFinset _).2 hβ)
  obtain ⟨N, hNB, hN⟩ := Nat.exists_infinite_primes (B + 3)
  have hN2 : N ≠ 2 := by omega
  have hNL : (N : L) ≠ 0 := by
    intro h
    exact hN2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hN).1
      ((CharP.cast_eq_zero_iff L 2 N).1 h)).symm
  have : NeZero (N : L) := ⟨hNL⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N L) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 hN.pos).ne')
  have hζ' : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.1 hζ
  have hz := hζ'.isUnit_unit hN.ne_zero
  set z : Lˣ := (hζ'.isUnit hN.ne_zero).unit
  set b : Fin τ.rank → Lˣ := fun k => z ^ c k with hbdef
  have hb : ∀ v, rootChar b v = z ^ (∑ k, c k * v k) := fun v => by
    rw [rootChar, ← Finset.prod_zpow_eq_zpow_sum]
    exact Finset.prod_congr rfl fun k _ => (zpow_mul z (c k) (v k)).symm
  have hkerb : kernelRoots (rootCharHom b) = componentRoots (famCharHom a) i := by
    ext β
    rw [kernelRoots_rootCharHom, Set.mem_setOf_eq, hb, hz.zpow_eq_one_iff_dvd]
    constructor
    · rintro ⟨hβ, hdvd⟩
      by_contra hβΨ
      have hlt : (∑ k, c k * β k).natAbs < N := by have := hB β hβ; omega
      exact hc1 β hβ hβΨ (Int.natAbs_eq_zero.1
        (Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.1 hdvd) hlt))
    · intro hβ
      refine ⟨hβ.1.1, ?_⟩
      rw [hc0 β hβ]
      exact dvd_zero _
  obtain ⟨j, hj⟩ := exists_componentRoots_superset (χ' := rootCharHom b) i
    fun γ hγ => by rw [hkerb]; exact hγ
  refine ⟨N, b, j, hN, hN2, ?_, Set.Subset.antisymm (fun γ hγ => ?_) hj⟩
  ·
    have h := map_pow (rootDiagUnitHom τ L) b N
    change rootDiagUnit τ (b ^ N) = rootDiagUnit τ b ^ N at h
    have hbN : b ^ N = 1 := funext fun k => by
      rw [Pi.pow_apply, Pi.one_apply, hbdef, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hz.pow_eq_one, one_zpow]
    rw [← h, hbN, rootDiagUnit_one]
  · rw [← hkerb]
    exact hγ.1

theorem exists_isolating_element
    {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : ∀ u j, a u j ^ p = 1) (i : KernelComponent (famCharHom a)) :
    ∃ (N : ℕ) (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b)),
      N.Prime ∧ N ≠ 2 ∧ rootDiagUnit τ b ^ N = 1 ∧
        componentRoots (rootCharHom b) j = componentRoots (famCharHom a) i := by
  by_cases hcl : RootsRationallyClosed τ (componentRoots (famCharHom a) i)
  · exact exists_isolating_element_of_closed a i hcl
  · obtain ⟨u₀, j, hj⟩ :=
      fam_component_nonclosed_pin hτ a hp hp2 hap i hcl
    refine ⟨p, a u₀, j, hp, hp2, ?_, hj⟩
    have h := map_pow (rootDiagUnitHom τ L) (a u₀) p
    change rootDiagUnit τ (a u₀ ^ p) = rootDiagUnit τ (a u₀) ^ p at h
    have hp1 : a u₀ ^ p = 1 := funext fun k => by rw [Pi.pow_apply, Pi.one_apply, hap u₀ k]
    rw [← h, hp1, rootDiagUnit_one]

end Closed

end CFSG.StandardType.TableCRes
