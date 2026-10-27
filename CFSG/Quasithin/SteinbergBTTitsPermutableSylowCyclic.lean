module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCore

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat
open scoped Pointwise

theorem coe_sup_eq_mul_of_mul_comm {G : Type*} [Group G] {A U : Subgroup G}
    (hAU : (A : Set G) * (U : Set G) = (U : Set G) * (A : Set G)) :
    ((A ⊔ U : Subgroup G) : Set G) = (A : Set G) * (U : Set G) := by
  let M : Subgroup G :=
    { carrier := (A : Set G) * (U : Set G)
      mul_mem' := by
        rintro _ _ ⟨a, ha, u, hu, rfl⟩ ⟨a', ha', u', hu', rfl⟩
        have h : u * a' ∈ (A : Set G) * (U : Set G) := by
          rw [hAU]
          exact ⟨u, hu, a', ha', rfl⟩
        obtain ⟨a'', ha'', u'', hu'', he⟩ := h
        have he' : a'' * u'' = u * a' := he
        refine ⟨a * a'', mul_mem ha ha'', u'' * u', mul_mem hu'' hu', ?_⟩
        calc a * a'' * (u'' * u') = a * (a'' * u'') * u' := by group
          _ = a * u * (a' * u') := by
            rw [he']
            group
      one_mem' := ⟨1, one_mem A, 1, one_mem U, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, u, hu, rfl⟩
        have h : u⁻¹ * a⁻¹ ∈ (U : Set G) * (A : Set G) := ⟨u⁻¹, inv_mem hu, a⁻¹, inv_mem ha, rfl⟩
        rw [← hAU] at h
        rwa [mul_inv_rev] }
  have hle : A ⊔ U ≤ M := sup_le (fun a ha => ⟨a, ha, 1, one_mem U, mul_one a⟩)
    (fun u hu => ⟨1, one_mem A, u, hu, one_mul u⟩)
  refine Set.Subset.antisymm (SetLike.coe_subset_coe.2 hle) ?_
  rintro _ ⟨a, ha, u, hu, rfl⟩
  exact mul_mem (mem_sup_left ha) (mem_sup_right hu)

@[expose] def restrictMulAut {G : Type*} [Group G] (A : Subgroup G) (α : MulAut G)
    (h : A.map α.toMonoidHom = A) : MulAut A :=
  (α.subgroupMap A).trans (MulEquiv.subgroupCongr h)

theorem isCyclic_mulAut_of_card {A : Type*} [Group A] [Finite A] {p : ℕ}
    (h : Nat.card A = 1 ∨ (p.Prime ∧ Nat.card A = p)) : IsCyclic A ∧ IsCyclic (MulAut A) := by
  rcases h with h1 | ⟨hp, hpA⟩
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h1).1
    have : Subsingleton (MulAut A) := ⟨fun α β => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact ⟨inferInstance, inferInstance⟩
  · have : Fact (Nat.card A).Prime := ⟨hpA ▸ hp⟩
    have : NeZero (Nat.card A) := ⟨by rw [hpA]; exact hp.ne_zero⟩
    have : IsCyclic A := isCyclic_of_prime_card rfl
    exact ⟨inferInstance, isCyclic_of_surjective (IsCyclic.mulAutMulEquiv (G := A)).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv (G := A)).symm.surjective⟩

theorem tits_common_sylow_and_prime_subgroup_normalizer_action_is_cyclic
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (U : Sylow 2 titsD) (A : Subgroup titsD) (hA : IsPGroup p A)
    (hAU : (A : Set titsD) * (U : Set titsD) = (U : Set titsD) * (A : Set titsD)) :
    (Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5) ∧
    (A ≠ ⊥ → Nat.card A = p ∧ (p = 3 ∨ p = 5)) ∧ IsCyclic A ∧ IsCyclic (MulAut A) ∧
    IsCyclic (closure {β : MulAut A | ∃ (α : MulAut titsD) (h : A.map α.toMonoidHom = A),
      (U : Subgroup titsD).map α.toMonoidHom = U ∧ restrictMulAut A α h = β}) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 titsFlagStab :=
    IsPGroup.of_card (n := 11) (by rw [card_titsFlagStab]; norm_num)
  have hSi : ¬ 2 ∣ titsFlagStab.index := by
    rw [titsFlagStab_index]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsD (hS2.toSylow hSi) U
  have hUS : (U : Subgroup titsD) = titsFlagStab.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, IsPGroup.toSylow_coe]
    congr 1
  have hUcard : Nat.card U = 2048 := by
    rw [hUS, card_map_of_injective (MulAut.conj g).injective, card_titsFlagStab]
  set M : Subgroup titsD := A ⊔ (U : Subgroup titsD) with hM
  set M' : Subgroup titsD := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hSM : titsFlagStab ≤ M' := fun s hs => by
    refine ⟨g * s * g⁻¹, ?_, ?_⟩
    · have : g * s * g⁻¹ ∈ (U : Subgroup titsD) := by
        rw [hUS]
        exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
      exact mem_sup_right this
    · simp [mul_assoc]
  have hMM' : Nat.card M' = Nat.card M := card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  have hAM : Nat.card A ∣ Nat.card M := card_dvd_of_le le_sup_left
  have hcop : ∀ m, p ^ k ∣ 2 ^ 11 * m → p ^ k ∣ m := fun m h =>
    (Nat.Coprime.pow k 11 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)).dvd_of_dvd_mul_left h
  have hcases : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5 := by
    rw [hk] at hAM ⊢
    rcases tits_overgroups M' hSM with h | h | h | h
    · rw [← hMM', h, card_titsFlagStab, show 2048 = 2 ^ 11 * 1 by norm_num] at hAM
      exact Or.inl (Nat.dvd_one.1 (hcop 1 hAM))
    · rw [← hMM', h, card_titsPointStab, show 10240 = 2 ^ 11 * 5 by norm_num] at hAM
      rcases (Nat.dvd_prime Nat.prime_five).1 (hcop 5 hAM) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)
    · rw [← hMM', h, card_titsLineStab, show 6144 = 2 ^ 11 * 3 by norm_num] at hAM
      rcases (Nat.dvd_prime Nat.prime_three).1 (hcop 3 hAM) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · exfalso
      have hMtop : M = ⊤ := by
        refine eq_top_of_card_eq M ?_
        rw [← hMM', h, card_top]
      have h8775 : p ^ k ∣ 8775 := by
        rw [hMtop, card_top, card_titsD, show 17971200 = 2 ^ 11 * 8775 by norm_num] at hAM
        exact hcop 8775 hAM
      have hset := coe_sup_eq_mul_of_mul_comm hAU
      rw [← hM, hMtop, coe_top] at hset
      have hle : Nat.card titsD ≤ Nat.card A * Nat.card U := by
        rw [← Nat.card_prod]
        refine Nat.card_le_card_of_surjective (fun x : A × U => (x.1 : titsD) * x.2) ?_
        intro y
        have hy : y ∈ (Set.univ : Set titsD) := Set.mem_univ y
        rw [hset] at hy
        obtain ⟨a, ha, u, hu, rfl⟩ := hy
        exact ⟨(⟨a, ha⟩, ⟨u, hu⟩), rfl⟩
      rw [card_titsD, hk, hUcard] at hle
      have heq : p ^ k = 8775 := le_antisymm (Nat.le_of_dvd (by norm_num) h8775) (by omega)
      have h3 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow (heq ▸ (by norm_num : 3 ∣ 8775)))
      have h5 : 5 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1
        (Nat.prime_five.dvd_of_dvd_pow (heq ▸ (by norm_num : 5 ∣ 8775)))
      omega
  have hnontriv : A ≠ ⊥ → Nat.card A = p ∧ (p = 3 ∨ p = 5) := by
    intro hA1
    have h1 : Nat.card A ≠ 1 := fun h => hA1 (card_eq_one.1 h)
    have hpA : p ∣ Nat.card A := by
      rw [hk] at h1 ⊢
      exact dvd_pow_self p fun hk0 => h1 (by rw [hk0, pow_zero])
    rcases hcases with h | h | h
    · exact absurd h h1
    · rw [h] at hpA ⊢
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpA
      exact ⟨this.symm, Or.inl this⟩
    · rw [h] at hpA ⊢
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpA
      exact ⟨this.symm, Or.inr this⟩
  have hcyc : IsCyclic A ∧ IsCyclic (MulAut A) := by
    by_cases hA1 : A = ⊥
    · exact isCyclic_mulAut_of_card (p := p) (Or.inl (card_eq_one.2 hA1))
    · exact isCyclic_mulAut_of_card (Or.inr ⟨hp, (hnontriv hA1).1⟩)
  have : IsCyclic (MulAut A) := hcyc.2
  exact ⟨hcases, hnontriv, hcyc.1, hcyc.2, inferInstance⟩

end CFSG.Quasithin.SteinbergBT
