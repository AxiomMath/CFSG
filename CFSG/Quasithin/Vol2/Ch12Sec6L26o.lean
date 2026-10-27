module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

namespace S126Cop

variable {G : Type} [Group G]

theorem le_comm_sup_inf [Finite G] {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ Subgroup.centralizer (X : Set G)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ Subgroup.centralizer (X : Set G)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

theorem comm_comm_eq [Finite G] {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right P X)
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

theorem eq_one_of_fix {W : Type} [Group W] (h2 : ∀ w : W, w ^ 2 = 1) (f : W →* W)
    (hf3 : ∀ w, f (f (f w)) = w) {w : W} (hfix : f (w⁻¹ * f w) = w⁻¹ * f w) :
    w⁻¹ * f w = 1 := by
  have htel : (w⁻¹ * f w) * f (w⁻¹ * f w) * f (f (w⁻¹ * f w)) = 1 := by
    simp only [map_mul, map_inv, hf3]
    group
  rw [hfix, hfix] at htel
  have h3 : (w⁻¹ * f w) ^ 3 = 1 := by rw [pow_succ, sq]; exact htel
  calc w⁻¹ * f w = (w⁻¹ * f w) ^ 3 * ((w⁻¹ * f w) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem two_pow_ten_le {A : Type} [Group A] [Finite A] (hA : IsPGroup 2 A) (f : MulAut A)
    (hf : f ^ 11 = 1) (hf1 : f ≠ 1) : 2 ^ 10 ≤ Nat.card A := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Subgroup A := MonoidHom.eqLocus f.toMonoidHom (MonoidHom.id A)
  have hF : ∀ a, a ∈ F ↔ f a = a := fun a => Iff.rfl
  set σ : Equiv.Perm A := MulAut.toPerm (M := A) f with hσ
  have hσ11 : σ ^ 11 ^ 1 = 1 := by rw [hσ, pow_one, ← map_pow, hf, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ11
  have hFc : σ.supportᶜ.card = Nat.card F := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun a => by
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact (hF a).symm
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdvd : Nat.card F ∣ 2 ^ n := hn ▸ Subgroup.card_subgroup_dvd_card F
  obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hlt : m < n := by
    rcases lt_or_eq_of_le hmn with h | h
    · exact h
    · exfalso
      apply hf1
      have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hm, hn, h])
      ext a
      have : a ∈ F := hFtop ▸ Subgroup.mem_top a
      exact (hF a).mp this
  rw [hFc, hm, Fintype.card_eq_nat_card, hn] at hmod
  have h11 : 11 ∣ 2 ^ n - 2 ^ m := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num)
    hlt.le)).mp hmod
  have e : 2 ^ n - 2 ^ m = 2 ^ m * (2 ^ (n - m) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [e] at h11
  have hcop : Nat.Coprime 11 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
  have h11' := hcop.dvd_of_dvd_mul_left h11
  have hd : 10 ≤ n - m := by
    by_contra hd
    push Not at hd
    have h1 : 1 ≤ n - m := by omega
    interval_cases (n - m) <;> norm_num at h11'
  calc 2 ^ 10 ≤ 2 ^ (n - m) := Nat.pow_le_pow_right (by norm_num) hd
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n m)
    _ = Nat.card A := hn.symm

end S126Cop

end CFSG.Quasithin.H13
