module

public import CFSG.Permutation.SylowTwoNormalizer.Blocks
public import CFSG.Permutation.SylowTwoNormalizer.Orbits
public import CFSG.Permutation.SylowTwoNormalizer.Restrict
public import TauCeti.GroupTheory.GroupAction.Transitive

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

private theorem eq_one_of_mem_normalizer_aux (n : ℕ) :
    ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω], Nat.card Ω = n →
      ∀ {R : Subgroup (Perm Ω)}, IsPGroup 2 R → ¬ 2 ∣ R.index →
        ∀ {σ : Perm Ω}, Odd (orderOf σ) →
          σ ∈ normalizer (R : Set (Perm Ω)) → σ = 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    classical
    intro Ω _ _ hn
    subst hn
    intro R hR hRi σ hσ hσR
    have restr_step : ∀ {s : Set Ω}, R ≤ stabilizer (Perm Ω) s →
        σ ∈ stabilizer (Perm Ω) s →
        ¬ 2 ∣ (restr R s).index → ¬ 2 ∣ (restr R sᶜ).index →
        Nat.card ↥s < Nat.card Ω → Nat.card ↥sᶜ < Nat.card Ω → σ = 1 := by
      intro s hRs hσs hsyl hsylc hlt hltc
      have hσs' : σ • s = s := mem_stabilizer_iff.mp hσs
      have hσsc : σ ∈ stabilizer (Perm Ω) sᶜ := by
        rw [mem_stabilizer_iff, Set.smul_set_compl, hσs']
      have hres_s : restrictHom s ⟨σ, hσs⟩ = 1 :=
        ih (Nat.card ↥s) hlt ↥s rfl (R := restr R s) (isPGroup_restr hR s) hsyl
          (σ := restrictHom s ⟨σ, hσs⟩) (odd_orderOf_restrictHom hσs hσ)
          (restrictHom_mem_normalizer hσs hσR)
      have hres_sc : restrictHom sᶜ ⟨σ, hσsc⟩ = 1 :=
        ih (Nat.card ↥sᶜ) hltc ↥sᶜ rfl (R := restr R sᶜ) (isPGroup_restr hR sᶜ) hsylc
          (σ := restrictHom sᶜ ⟨σ, hσsc⟩) (odd_orderOf_restrictHom hσsc hσ)
          (restrictHom_mem_normalizer hσsc hσR)
      exact eq_one_of_restrictHom_eq_one hσs hσsc hres_s hres_sc
    by_cases hn1 : Nat.card Ω ≤ 1
    ·
      haveI : Subsingleton Ω := Finite.card_le_one_iff_subsingleton.mp hn1
      ext x
      exact Subsingleton.elim _ _
    · push Not at hn1
      have h2 : 2 ≤ Nat.card Ω := by omega
      by_cases htr : MulAction.IsPretransitive R Ω
      ·
        haveI : Nonempty Ω := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card Ω)).1
        have hdvd : Nat.card Ω ∣ Nat.card R := TauCeti.natCard_dvd_natCard_of_isPretransitive R
        have hpow : ∃ a, Nat.card Ω = 2 ^ a ∧ 1 ≤ a := by
          have h : Nat.card Ω ∣ 2 ^ padicValNat 2 (Nat.card Ω).factorial := by
            rw [← card_eq_of_not_two_dvd_index hR hRi]
            exact hdvd
          obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
          refine ⟨a, ha, ?_⟩
          rcases Nat.eq_zero_or_pos a with ha0 | hapos
          · exfalso
            rw [ha0, pow_zero] at ha
            omega
          · exact hapos
        obtain ⟨a, ha, ha1⟩ := hpow
        obtain ⟨B, hBcard, hRB⟩ := exists_halving_block hR htr h2
        have hσB_card : 2 * Nat.card ↥(σ • B) = Nat.card Ω := by
          have hcard_smul : Nat.card ↥(σ • B) = Nat.card ↥B := by
            rw [Nat.card_coe_set_eq, Set.ncard_smul_set, Nat.card_coe_set_eq]
          rw [hcard_smul]
          exact hBcard
        have hBnonempty : B.Nonempty := by
          rw [← Set.ncard_pos, ← Nat.card_coe_set_eq]
          omega
        have hBne : B ≠ Bᶜ := ne_compl_self
        have hσB_fix : σ • B = B :=
          smul_set_eq_of_smul_set_eq_or_eq_compl hBnonempty hσ
            (eq_or_eq_compl_of_halving hR hRi ha hBcard hσB_card hRB
              (smul_set_halving_of_mem_normalizer hRB hσR))
        have hσB_stab : σ ∈ stabilizer (Perm Ω) B := mem_stabilizer_iff.mpr hσB_fix
        let R₀ : Subgroup (Perm Ω) := R ⊓ stabilizer (Perm Ω) B
        have hR₀ : IsPGroup 2 R₀ := hR.to_inf_left
        have hR₀B : R₀ ≤ stabilizer (Perm Ω) B := inf_le_right
        have hσR₀ : σ ∈ normalizer (R₀ : Set (Perm Ω)) := by
          have hσst : σ ∈ normalizer (stabilizer (Perm Ω) B : Set (Perm Ω)) :=
            Subgroup.le_normalizer hσB_stab
          exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hσR, hσst⟩
        have hg : ∃ g ∈ R, g • B = Bᶜ := exists_smul_eq_compl htr hBcard hBnonempty hRB
        have hcardR : Nat.card R = 2 ^ (2 ^ a - 1) := by
          rw [card_eq_of_not_two_dvd_index hR hRi, ha, padicValNat_two_factorial_two_pow]
        have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          rw [pow_succ']
          simp
        have hcardR0 : Nat.card R₀ = 2 ^ (2 ^ a - 2) := by
          have h2 := two_mul_card_inf_stabilizer hRB hg hBne
          have h2a1 : 2 ^ (2 ^ a - 1) = 2 * 2 ^ (2 ^ a - 2) := by
            rw [show 2 ^ a - 1 = (2 ^ a - 2) + 1 by omega, pow_succ']
          rw [hcardR, h2a1] at h2
          exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
        have hcard_split_B : Nat.card ↥B + Nat.card ↥Bᶜ = Nat.card Ω := by
          have h := Set.ncard_add_ncard_compl B
          rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
        have hcardB : Nat.card ↥B = 2 ^ (a - 1) := by
          have h := hBcard
          rw [ha, h2a] at h
          exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
        have hcardBc : Nat.card ↥Bᶜ = 2 ^ (a - 1) := by
          omega
        have hsumPadic : padicValNat 2 (Nat.card ↥B).factorial +
            padicValNat 2 (Nat.card ↥Bᶜ).factorial = 2 ^ a - 2 := by
          rw [hcardB, hcardBc, padicValNat_two_factorial_two_pow]
          have hle : 1 ≤ 2 ^ (a - 1) := Nat.one_le_pow (a - 1) 2 (by norm_num)
          rw [h2a]
          omega
        have hc : 2 ^ (padicValNat 2 (Nat.card ↥B).factorial +
            padicValNat 2 (Nat.card ↥Bᶜ).factorial) ∣ Nat.card R₀ := by
          rw [hsumPadic, hcardR0]
        have hSylow := not_two_dvd_index_restr hR₀ hR₀B hc
        have hcardB_lt : Nat.card ↥B < Nat.card Ω := by
          have hlt : 2 ^ (a - 1) < 2 ^ a :=
            Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        have hcardBc_lt : Nat.card ↥Bᶜ < Nat.card Ω := by
          have hlt : 2 ^ (a - 1) < 2 ^ a :=
            Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        have hresB : restrictHom B ⟨σ, hσB_stab⟩ = 1 :=
          ih (Nat.card ↥B) hcardB_lt ↥B rfl (R := restr R₀ B) (isPGroup_restr hR₀ B)
            hSylow.1 (σ := restrictHom B ⟨σ, hσB_stab⟩) (odd_orderOf_restrictHom hσB_stab hσ)
            (restrictHom_mem_normalizer hσB_stab hσR₀)
        have hσBc_stab : σ ∈ stabilizer (Perm Ω) Bᶜ := by
          rw [mem_stabilizer_iff, Set.smul_set_compl, mem_stabilizer_iff.mp hσB_stab]
        have hresBc : restrictHom Bᶜ ⟨σ, hσBc_stab⟩ = 1 :=
          ih (Nat.card ↥Bᶜ) hcardBc_lt ↥Bᶜ rfl (R := restr R₀ Bᶜ) (isPGroup_restr hR₀ Bᶜ)
            hSylow.2 (σ := restrictHom Bᶜ ⟨σ, hσBc_stab⟩)
            (odd_orderOf_restrictHom hσBc_stab hσ)
            (restrictHom_mem_normalizer hσBc_stab hσR₀)
        exact eq_one_of_restrictHom_eq_one hσB_stab hσBc_stab hresB hresBc
      ·
        rw [MulAction.isPretransitive_iff] at htr
        push Not at htr
        obtain ⟨x, y, hxy⟩ := htr
        have hx : MulAction.orbit R x ≠ Set.univ := by
          intro h
          have hy : y ∈ MulAction.orbit R x := by rw [h]; exact Set.mem_univ y
          rw [MulAction.mem_orbit_iff] at hy
          obtain ⟨g, hg⟩ := hy
          exact hxy g hg
        have hxmem : x ∈ MulAction.orbit R x := by
          simpa using MulAction.mem_orbit (R := R) x (1 : R)
        have hRs : R ≤ stabilizer (Perm Ω) (MulAction.orbit R x) := le_stabilizer_orbit R x
        have hσs : σ ∈ stabilizer (Perm Ω) (MulAction.orbit R x) :=
          mem_stabilizer_orbit hσR (apply_mem_orbit hR hRi hσR x)
        have hlt_s : Nat.card ↥(MulAction.orbit R x) < Nat.card Ω := by
          have hlt : (MulAction.orbit R x).ncard < (Set.univ : Set Ω).ncard :=
            Set.ncard_lt_ncard (by rwa [Set.ssubset_univ_iff])
          rw [Set.ncard_univ] at hlt
          rwa [Nat.card_coe_set_eq]
        have hlt_sc : Nat.card ↥(MulAction.orbit R x)ᶜ < Nat.card Ω := by
          have hpos : 0 < (MulAction.orbit R x).ncard := by
            rw [Set.ncard_pos]
            exact ⟨x, hxmem⟩
          have hsum : (MulAction.orbit R x).ncard + (MulAction.orbit R x)ᶜ.ncard = Nat.card Ω :=
            Set.ncard_add_ncard_compl _
          rw [Nat.card_coe_set_eq]
          omega
        have hcard_split : Nat.card ↥(MulAction.orbit R x) +
            Nat.card ↥(MulAction.orbit R x)ᶜ = Nat.card Ω := by
          have h := Set.ncard_add_ncard_compl (MulAction.orbit R x)
          rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
        have hle : padicValNat 2 (Nat.card ↥(MulAction.orbit R x)).factorial +
            padicValNat 2 (Nat.card ↥(MulAction.orbit R x)ᶜ).factorial ≤
            padicValNat 2 (Nat.card Ω).factorial := by
          have h := padicValNat_two_factorial_add_le
            (Nat.card ↥(MulAction.orbit R x)) (Nat.card ↥(MulAction.orbit R x)ᶜ)
          rwa [hcard_split] at h
        have hc : 2 ^ (padicValNat 2 (Nat.card ↥(MulAction.orbit R x)).factorial +
            padicValNat 2 (Nat.card ↥(MulAction.orbit R x)ᶜ).factorial) ∣ Nat.card R := by
          rw [card_eq_of_not_two_dvd_index hR hRi]
          exact pow_dvd_pow 2 hle
        have hSylow := not_two_dvd_index_restr hR hRs hc
        exact restr_step hRs hσs hSylow.1 hSylow.2 hlt_s hlt_sc

theorem eq_one_of_mem_normalizer {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index) {σ : Perm Ω}
    (hσ : Odd (orderOf σ)) (hσR : σ ∈ normalizer (R : Set (Perm Ω))) : σ = 1 :=
  eq_one_of_mem_normalizer_aux (Nat.card Ω) Ω rfl (R := R) hR hRi (σ := σ) hσ hσR

end CFSG.Permutation.SylowTwoNormalizer
