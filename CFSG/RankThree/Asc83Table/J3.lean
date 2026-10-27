module

public import CFSG.RankThree.Asc83Table.J3Spec
public import CFSG.RankThree.Asc83Table.J3Check
public import Certificates.Certificate3169
public import Certificates.Certificate8004

public section

namespace CFSG.RankThree.Asc83Table.J3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.Sporadic.J3 Subgroup MulAction

local notation "hJ" => j3_check

theorem hrb : ∀ i, MFact.ord (rbF j3Cert i) 3 ∈ j3Cert.facts := by
  intro i
  fin_cases i
  · exact mem_facts (C := j3Cert.mcert) 0 rfl
  · exact mem_facts (C := j3Cert.mcert) 1 rfl
  · exact mem_facts (C := j3Cert.mcert) 2 rfl

theorem hrh : MFact.ord (rhF j3Cert 0) 9 ∈ j3Cert.facts ∧
    MFact.ord (rhF j3Cert 1) 9 ∈ j3Cert.facts ∧ MFact.ord (rhF j3Cert 2) 8 ∈ j3Cert.facts :=
  ⟨mem_facts (C := j3Cert.mcert) 6 rfl, mem_facts (C := j3Cert.mcert) 7 rfl,
    mem_facts (C := j3Cert.mcert) 8 rfl⟩

noncomputable abbrev x : Fin 3 → J D := xb hJ

noncomputable abbrev h : Fin 3 → J D := hb hJ

theorem x_pow (i : Fin 3) : x i ^ 3 = 1 := xb_pow hJ hrb i

theorem x_comm (i j : Fin 3) : Commute (x i) (x j) := by
  have h01 : Commute (x 0) (x 1) := X_comm hJ (hrb 0) (hrb 1) (mem_facts (C := j3Cert.mcert) 3 rfl)
  have h02 : Commute (x 0) (x 2) := X_comm hJ (hrb 0) (hrb 2) (mem_facts (C := j3Cert.mcert) 4 rfl)
  have h12 : Commute (x 1) (x 2) := X_comm hJ (hrb 1) (hrb 2) (mem_facts (C := j3Cert.mcert) 5 rfl)
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact h01
  · exact h02
  · exact h01.symm
  · exact Commute.refl _
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _

theorem x_inj : Function.Injective (basisProd x) := basisProd_injective hJ hrb x_comm

theorem h_conj (k j : Fin 3) :
    h k * x j * (h k)⁻¹ = basisProd x fun i => (t33 k : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j := by
  fin_cases k <;> fin_cases j
  · exact X_conj hJ hrb hrh.1 0 _ (mem_facts (C := j3Cert.mcert) 9 rfl)
  · exact X_conj hJ hrb hrh.1 1 _ (mem_facts (C := j3Cert.mcert) 10 rfl)
  · exact X_conj hJ hrb hrh.1 2 _ (mem_facts (C := j3Cert.mcert) 11 rfl)
  · exact X_conj hJ hrb hrh.2.1 0 _ (mem_facts (C := j3Cert.mcert) 12 rfl)
  · exact X_conj hJ hrb hrh.2.1 1 _ (mem_facts (C := j3Cert.mcert) 13 rfl)
  · exact X_conj hJ hrb hrh.2.1 2 _ (mem_facts (C := j3Cert.mcert) 14 rfl)
  · exact X_conj hJ hrb hrh.2.2 0 _ (mem_facts (C := j3Cert.mcert) 15 rfl)
  · exact X_conj hJ hrb hrh.2.2 1 _ (mem_facts (C := j3Cert.mcert) 16 rfl)
  · exact X_conj hJ hrb hrh.2.2 2 _ (mem_facts (C := j3Cert.mcert) 17 rfl)

theorem omega_basis (a : Fin 3 → ZMod 3) (i j : ℕ) (hi : i < 3) (hj : j < 3)
    (hij : i ≠ 0 ∨ j ≠ 0) : (basisProd x a * h 0 ^ i * h 1 ^ j) ^ 3 ≠ 1 :=
  omega_ne hJ hrb a i j hi hj hij ⟨hrh.1, hrh.2.1⟩

theorem len_ss : j3Cert.ss.length = 136 := by decide +kernel

theorem len_cs : j3Cert.ss.length = j3Cert.cs.length := (extra_parts hJ).2.2.2.2.2.2.2

theorem len_xs : j3Cert.xs.length = 108 := by decide +kernel

theorem base_size : D.base.size = 2 := rfl

theorem orbitFacts_D : OrbitFacts D := j3Facts.orbitFacts

noncomputable abbrev r : Vec := P D 0

theorem stabilizer_root_eq :
    stabilizer (J D) r = stabilizer (J D) (root D j3Facts.n_pos) := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  have hP : P D (g • root D j3Facts.n_pos).val = g • P D 0 :=
    P_smul orbitFacts_D g (root D j3Facts.n_pos)
  constructor
  · intro hg
    apply Fin.ext
    rw [hg] at hP
    exact P_injective orbitFacts_D.1 _ (g • root D j3Facts.n_pos).isLt 0 j3Facts.n_pos hP
  · intro hg
    rw [hg] at hP
    exact hP.symm

theorem card_stabilizer_r : Nat.card (stabilizer (J D) r) = 2448 := by
  rw [stabilizer_root_eq, card_stabilizer_root j3Facts, base_size, show (2 : ℕ) = 1 + 1 from rfl,
    Nat.Ico_succ_singleton, Finset.prod_singleton,
    trees_size_eq j3Facts (by rw [base_size]; norm_num)]
  rfl

theorem x0_ne_one : x 0 ≠ 1 := by
  have h := basisProd_ne_one hJ hrb (a := Pi.single 0 1) (by
    intro h0
    have := congrFun h0 0
    simp at this)
  have hb : basisProd x (Pi.single 0 1) = x 0 := by
    simp [basisProd, List.ofFn_succ, Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]
  rwa [hb] at h

theorem ncard_setOf_mem_le (l : List ℕ) : ({i | i ∈ l} : Set ℕ).ncard ≤ l.length := by
  rw [show ({i | i ∈ l} : Set ℕ) = (l.toFinset : Set ℕ) by ext; simp, Set.ncard_coe_finset]
  exact List.toFinset_card_le l

theorem card_normalizer :
    Nat.card (normalizer (Subgroup.closure (Set.range x) : Set (J D))) ≤ 1944 := by
  have hO := orbitFacts_D
  set Xs : Set Vec := P D '' {i | i ∈ j3Cert.xs}
  have hfin : ({i | i ∈ j3Cert.xs} : Set ℕ).Finite := j3Cert.xs.finite_toSet
  have hXf : Xs.Finite := hfin.image _
  have hXn : Xs.ncard ≤ 108 := by
    have h1 : Xs.ncard ≤ ({i | i ∈ j3Cert.xs} : Set ℕ).ncard := Set.ncard_image_le hfin
    have h2 := ncard_setOf_mem_le j3Cert.xs
    rw [len_xs] at h2
    omega
  have hX : ∀ g : J D, ∀ a, a ≠ 0 → basisProd x a • g • r = g • r → g • r ∈ Xs := by
    intro g a ha hfix
    obtain ⟨i, hi, hgi⟩ := smul_mem_ptSet D hO g r ⟨0, j3Facts.n_pos, rfl⟩
    rw [← hgi] at hfix ⊢
    by_cases hxs : i ∈ j3Cert.xs
    · exact ⟨i, hxs, rfl⟩
    · exact absurd hfix (basisProd_smul_ne hJ hrb ha hi hxs)
  have hroot : ∀ a, basisProd x a • r = r → basisProd x a ∈ zpowers (x 0) := by
    intro a ha
    obtain ⟨h1, h2⟩ := basisProd_smul_root hJ hrb ha
    have : basisProd x a = x 0 ^ (a 0).val := by
      simp [basisProd, List.ofFn_succ, h1, h2]
    rw [this]
    exact pow_mem (mem_zpowers _) _
  have h1 := card_normalizer_le_of_orbit x_pow x_comm 0 r hXf hX x0_ne_one (xb_smul_root hJ hrb)
    hroot
  have h2 := card_normalizer_zpowers_mul_le (stabilizer (J D) r) (x_pow 0) x0_ne_one
    (sE hJ) (cE hJ len_cs) (fun k => sE_smul_root hJ k len_cs) (sE_conj hJ hrb len_cs)
    (fun k l hkl => cE_ne hJ len_cs hkl)
  rw [len_ss, card_stabilizer_r] at h2
  set T : Subgroup (J D) := normalizer (zpowers (x 0) : Set (J D)) ⊓ stabilizer (J D) r
  have h18 : Nat.card T ≤ 18 := by omega
  calc Nat.card (normalizer (Subgroup.closure (Set.range x) : Set (J D)))
      ≤ Xs.ncard * Nat.card T := h1
    _ ≤ 108 * 18 := Nat.mul_le_mul hXn h18
    _ = 1944 := by norm_num

theorem factorization_card : (Nat.card (J D)).factorization 3 = 5 := by
  rw [← Nat.card_congr φ.toEquiv, CFSG.Sporadic.J3.card_J3]
  exact factorization_eq_of_eq Nat.prime_three (show 50232960 = 3 ^ 5 * 206720 by norm_num)
    (by norm_num)

theorem pRank_J : CFSG.pRank 3 (J D) = 3 :=
  e27_pRank x_pow x_comm x_inj h_conj card_normalizer omega_basis factorization_card

theorem automizer_J (A : Subgroup (J D)) (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    IsE9Z8 (Automizer A) :=
  e27_automizer x_pow x_comm x_inj h_conj card_normalizer omega_basis factorization_card hA h27

theorem native_J3 : CFSG.pRank 3 NativeSporadic.J3 = 3 ∧
    ∀ A : Subgroup NativeSporadic.J3, IsElementaryAbelian 3 A → Nat.card A = 27 →
      IsE9Z8 (Automizer A) :=
  e27_transport (G := J D) (L := NativeSporadic.J3) φ pRank_J automizer_J

theorem table {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .J3) :
    CFSG.pRank 3 L = 3 ∧
      ∀ B : Subgroup L, IsElementaryAbelian 3 B → Nat.card B = 27 →
        ActsNontriviallyOnTwoSubgroup B →
          Nat.card (Automizer B) = 72 ∧
            ∃ (E : Subgroup (Automizer B)) (_ : E.Normal), IsElementaryAbelian 3 E ∧
              Nat.card E = 9 ∧ IsCyclic (Automizer B ⧸ E) ∧ Nat.card (Automizer B ⧸ E) = 8 := by
  obtain ⟨e⟩ := hL
  obtain ⟨h₁, h₂⟩ := e27_transport (G := NativeSporadic.J3) (L := L) e native_J3.1 native_J3.2
  exact ⟨h₁, fun B hB h27 _ => h₂ B hB h27⟩

end CFSG.RankThree.Asc83Table.J3
