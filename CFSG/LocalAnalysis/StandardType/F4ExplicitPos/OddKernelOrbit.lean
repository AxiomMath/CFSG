module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang

@[expose] public section

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes CFSG.StandardType.LieCore
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.F4ExplicitPos.OddKernelOrbit

theorem f4_orthogonal_sameLength_sum_or_double :
    ∀ α ∈ rootFinset Tag.F4, ∀ β ∈ rootFinset Tag.F4,
      iform α β = 0 → iform α α = iform β β →
      α + β ∈ rootFinset Tag.F4 ∨
        ¬ ∀ γ ∈ rootFinset Tag.F4, (2 : ℕ) • γ ≠ α + β := by
  decide +kernel

private theorem eq_one_of_sq_eq_one_of_odd_pow_eq_one {M : Type*} [CommGroup M] {x : M} {p : ℕ}
    (hp : Odd p) (h2 : x ^ 2 = 1) (hp' : x ^ p = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have hx : x ^ (2 * k + 1) = x := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← hx, hp']

theorem componentRoots_image_eq_of_odd_torsion
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {p : ℕ} (hp : Odd p)
    (hpow : ∀ γ, IsRoot Tag.F4 γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (_hρR : ∀ γ, IsRoot Tag.F4 (ρ γ) ↔ IsRoot Tag.F4 γ)
    (hρ : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' componentRoots χ i =
      componentRoots χ i := by
  classical
  obtain ⟨j, hj⟩ := exists_image_component_of_stable χ hker hρ i
  by_contra hne
  have hij : i ≠ j := by rintro rfl; exact hne hj
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  let α : Fin Tag.F4.rank → ℤ := a
  let β : Fin Tag.F4.rank → ℤ := ρ α
  have hαker : α ∈ kernelRoots χ := a.2
  have hαi : α ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hβker : β ∈ kernelRoots χ := hker α hαker
  have hβj : β ∈ componentRoots χ j := by
    rw [← hj]
    exact ⟨α, hαi, rfl⟩
  have horth : iform α β = 0 := iform_eq_zero_of_mem_componentRoots' hij hαi hβj
  have hnorm : iform α α = iform β β := (hρ α α).symm
  have hchk := f4_orthogonal_sameLength_sum_or_double α (mem_rootFinset.2 hαker.1) β
    (mem_rootFinset.2 hβker.1) horth hnorm
  obtain ⟨hβ', hβ'eq⟩ := hβj
  have e3 : (⟦(⟨β, hβker⟩ : kernelRoots χ)⟧ : KernelComponent χ) = j := by
    rw [show (⟨β, hβker⟩ : kernelRoots χ) = ⟨β, hβ'⟩ from Subtype.ext rfl]
    exact hβ'eq
  have e0 : (⟦a⟧ : KernelComponent χ) = ⟦(⟨α, hαker⟩ : kernelRoots χ)⟧ := rfl
  rcases hchk with hsum | hnot
  ·
    have hsumroot : IsRoot Tag.F4 (α + β) := mem_rootFinset.1 hsum
    have hsumker : α + β ∈ kernelRoots χ := ⟨hsumroot, by
      rw [ofAdd_add, map_mul, hαker.2, hβker.2, one_mul]⟩
    have h1 : iform (α + β) α ≠ 0 := by
      rw [iform_add_left, iform_comm β α, horth, add_zero]
      exact (iform_self_pos_of_isRoot hαker.1).ne'
    have h2 : iform (α + β) β ≠ 0 := by
      rw [iform_add_left, horth, zero_add]
      exact (iform_self_pos_of_isRoot hβker.1).ne'
    have e1 : (⟦(⟨α, hαker⟩ : kernelRoots χ)⟧ : KernelComponent χ) =
        ⟦(⟨α + β, hsumker⟩ : kernelRoots χ)⟧ :=
      (mk_eq_of_iform_ne_zero (α := ⟨α + β, hsumker⟩) (β := ⟨α, hαker⟩) h1).symm
    have e2 : (⟦(⟨β, hβker⟩ : kernelRoots χ)⟧ : KernelComponent χ) =
        ⟦(⟨α + β, hsumker⟩ : kernelRoots χ)⟧ :=
      (mk_eq_of_iform_ne_zero (α := ⟨α + β, hsumker⟩) (β := ⟨β, hβker⟩) h2).symm
    exact hij (ha.symm.trans (e0.trans (e1.trans (e2.symm.trans e3))))
  ·
    have hex : ∃ γ, γ ∈ rootFinset Tag.F4 ∧ (2 : ℕ) • γ = α + β := by
      by_contra hc
      exact hnot (fun γ hγ h2 => hc ⟨γ, hγ, h2⟩)
    obtain ⟨γ, hγmem, hγeq⟩ := hex
    have hγroot : IsRoot Tag.F4 γ := mem_rootFinset.1 hγmem
    have hαβχ : χ (Multiplicative.ofAdd (α + β)) = 1 := by
      rw [ofAdd_add, map_mul, hαker.2, hβker.2, one_mul]
    have hγ2 : χ (Multiplicative.ofAdd γ) ^ 2 = 1 := by
      rw [← hγeq, ofAdd_nsmul, map_pow] at hαβχ
      exact hαβχ
    have hγ1 : χ (Multiplicative.ofAdd γ) = 1 :=
      eq_one_of_sq_eq_one_of_odd_pow_eq_one hp hγ2 (hpow γ hγroot)
    have hγker : γ ∈ kernelRoots χ := ⟨hγroot, hγ1⟩
    have h1 : iform γ α ≠ 0 := by
      intro h0
      have heq : (2 : ℤ) * iform γ α = iform α α := by
        rw [two_mul, ← iform_add_left, ← two_nsmul, hγeq, iform_add_left, iform_comm β α,
          horth, add_zero]
      rw [h0, mul_zero] at heq
      exact (iform_self_pos_of_isRoot hαker.1).ne' heq.symm
    have h2 : iform γ β ≠ 0 := by
      intro h0
      have heq : (2 : ℤ) * iform γ β = iform β β := by
        rw [two_mul, ← iform_add_left, ← two_nsmul, hγeq, iform_add_left, horth, zero_add]
      rw [h0, mul_zero] at heq
      exact (iform_self_pos_of_isRoot hβker.1).ne' heq.symm
    have e1 : (⟦(⟨γ, hγker⟩ : kernelRoots χ)⟧ : KernelComponent χ) =
        ⟦(⟨α, hαker⟩ : kernelRoots χ)⟧ :=
      mk_eq_of_iform_ne_zero (α := ⟨γ, hγker⟩) (β := ⟨α, hαker⟩) h1
    have e2 : (⟦(⟨γ, hγker⟩ : kernelRoots χ)⟧ : KernelComponent χ) =
        ⟦(⟨β, hβker⟩ : kernelRoots χ)⟧ :=
      mk_eq_of_iform_ne_zero (α := ⟨γ, hγker⟩) (β := ⟨β, hβker⟩) h2
    exact hij (ha.symm.trans (e0.trans (e1.symm.trans (e2.trans e3))))

theorem componentOrbitLength_eq_one_of_image_eq
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (hρ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' Ψ = Ψ) :
    componentOrbitLength ρ Ψ = 1 := by
  have hmem : 1 ∈ {s : ℕ | 0 < s ∧
      (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))^[s] '' Ψ = Ψ} := by
    refine ⟨Nat.one_pos, ?_⟩
    rwa [Function.iterate_one]
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

theorem ratOrbit_eq_of_image_eq {ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)}
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} (h : ρ '' Ψ = Ψ) : ratOrbit ρ Ψ = Ψ := by
  have hpre : ∀ x, x ∈ Ψ → ρ x ∈ Ψ := by
    intro x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hiter : ∀ k : ℕ, ∀ x, x ∈ Ψ → (ρ^[k]) x ∈ Ψ := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hpre _ (ih x hx)
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    exact hiter k δ hδ
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem rationalRoots_eq_componentRoots_of_image_eq
    {L : Type} [Field L] (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (h : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' componentRoots χ i =
      componentRoots χ i) :
    rationalRoots ρ χ i = componentRoots χ i :=
  ratOrbit_eq_of_image_eq h

variable {L : Type} [Field L]

private theorem rootCharHom_ofAdd (a : Fin Tag.F4.rank → Lˣ)
    (γ : Fin Tag.F4.rank → ℤ) :
    rootCharHom a (Multiplicative.ofAdd γ) = rootChar a γ := rfl

private theorem jointChar_ofAdd (a d : Fin Tag.F4.rank → Lˣ)
    (γ : Fin Tag.F4.rank → ℤ) :
    jointChar a d (Multiplicative.ofAdd γ) = (rootChar a γ, rootChar d γ) := rfl

theorem f4_cyclic_componentRoots_image_eq_of_odd
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    {p : ℕ} (hp : Odd p)
    (hpow : ∀ γ, IsRoot Tag.F4 γ → rootChar a γ ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  refine componentRoots_image_eq_of_odd_torsion (χ := rootCharHom a) hp ?_ hρ.isRoot_iff
    hρ.iform_eq ?_ i
  · intro γ hγ
    rw [rootCharHom_ofAdd]
    exact hpow γ hγ
  · intro γ hγ
    have hγchar : rootChar a γ = 1 := hγ.2
    refine ⟨(hρ.isRoot_iff γ).2 hγ.1, ?_⟩
    rw [rootCharHom_ofAdd, hρ.rootChar_eq a ha γ hγ.1, hγchar, one_pow]

theorem f4_cyclic_componentOrbitLength_eq_one_of_odd
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    {p : ℕ} (hp : Odd p)
    (hpow : ∀ γ, IsRoot Tag.F4 γ → rootChar a γ ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i ∧
      componentOrbitLength ρ (componentRoots (rootCharHom a) i) = 1 :=
  ⟨f4_cyclic_componentRoots_image_eq_of_odd D ρ hρ a ha hp hpow i,
    componentOrbitLength_eq_one_of_image_eq
      (f4_cyclic_componentRoots_image_eq_of_odd D ρ hρ a ha hp hpow i)⟩

theorem f4_joint_componentRoots_image_eq_of_odd
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a d : Fin Tag.F4.rank → Lˣ)
    (ha : rootDiagUnit Tag.F4 a ∈ D.torus) (hd : rootDiagUnit Tag.F4 d ∈ D.torus)
    {p : ℕ} (hp : Odd p)
    (hpowa : ∀ γ, IsRoot Tag.F4 γ → rootChar a γ ^ p = 1)
    (hpowd : ∀ γ, IsRoot Tag.F4 γ → rootChar d γ ^ p = 1)
    (i : KernelComponent (jointChar a d)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (jointChar a d) i = componentRoots (jointChar a d) i := by
  refine componentRoots_image_eq_of_odd_torsion (χ := jointChar a d) hp ?_ hρ.isRoot_iff
    hρ.iform_eq ?_ i
  · intro γ hγ
    rw [jointChar_ofAdd, Prod.pow_mk, hpowa γ hγ, hpowd γ hγ]
    rfl
  · intro γ hγ
    have hγchar : (rootChar a γ, rootChar d γ) = 1 := hγ.2
    obtain ⟨h1, h2'⟩ := Prod.mk_eq_one.1 hγchar
    refine ⟨(hρ.isRoot_iff γ).2 hγ.1, ?_⟩
    rw [jointChar_ofAdd, Prod.mk_eq_one]
    exact ⟨by rw [hρ.rootChar_eq a ha γ hγ.1, h1, one_pow],
      by rw [hρ.rootChar_eq d hd γ hγ.1, h2', one_pow]⟩

theorem f4_joint_ratOrbit_eq_of_odd
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a d : Fin Tag.F4.rank → Lˣ)
    (ha : rootDiagUnit Tag.F4 a ∈ D.torus) (hd : rootDiagUnit Tag.F4 d ∈ D.torus)
    {p : ℕ} (hp : Odd p)
    (hpowa : ∀ γ, IsRoot Tag.F4 γ → rootChar a γ ^ p = 1)
    (hpowd : ∀ γ, IsRoot Tag.F4 γ → rootChar d γ ^ p = 1)
    (i : KernelComponent (jointChar a d)) :
    ratOrbit (fun u => ρ u) (componentRoots (jointChar a d) i) =
      componentRoots (jointChar a d) i :=
  ratOrbit_eq_of_image_eq
    (f4_joint_componentRoots_image_eq_of_odd D ρ hρ a d ha hd hp hpowa hpowd i)

theorem f4_cyclic_rationalRoots_eq_of_odd
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    {p : ℕ} (hp : Odd p)
    (hpow : ∀ γ, IsRoot Tag.F4 γ → rootChar a γ ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    rationalRoots ρ (rootCharHom a) i = componentRoots (rootCharHom a) i :=
  rationalRoots_eq_componentRoots_of_image_eq ρ (rootCharHom a) i
    (f4_cyclic_componentRoots_image_eq_of_odd D ρ hρ a ha hp hpow i)

end CFSG.StandardType.F4ExplicitPos.OddKernelOrbit

end

end
