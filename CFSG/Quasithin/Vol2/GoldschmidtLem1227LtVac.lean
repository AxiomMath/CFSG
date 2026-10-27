module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtBasic
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAbs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

namespace Lem1227Lt

theorem isSolvable_of_card_pq {M : Type*} [Group M] [Finite M] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card M = p ^ a * q ^ b) : Group.IsSolvable M := by
  let _ : Fintype M := Fintype.ofFinite M
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem sylow_card_eq {Λ : Type*} [Group Λ] [Finite Λ] {S : Subgroup Λ} (hS : IsSylowTwoOf S ⊤)
    {a m : ℕ} (hΛ : Nat.card Λ = 2 ^ a * m) (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ a := by
  obtain ⟨hp, hidx⟩ := isSylowTwoOf_top_iff'.mp hS
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h1 : 2 ^ k * S.index = 2 ^ a * m := by
    rw [← hk, Subgroup.card_mul_index, hΛ]
  have hc1 : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.2 hm)
  have hc2 : Nat.Coprime (2 ^ a) S.index :=
    Nat.Coprime.pow_left a (Nat.prime_two.coprime_iff_not_dvd.2 hidx)
  have hka : 2 ^ k ∣ 2 ^ a := hc1.dvd_of_dvd_mul_right (h1 ▸ Dvd.intro _ rfl)
  have hak : 2 ^ a ∣ 2 ^ k := hc2.dvd_of_dvd_mul_right (h1.symm ▸ Dvd.intro _ rfl)
  have : k = a := by
    have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.1 hka
    have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.1 hak
    omega
  rw [hk, this]

theorem card_dvd_factorial_index {Λ : Type*} [Group Λ] [Finite Λ] [IsSimpleGroup Λ]
    {M : Subgroup Λ} (hM : M ≠ ⊤) : Nat.card Λ ∣ M.index.factorial := by
  have hfin : M.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have h1 := Subgroup.index_normalCore_dvd_factorial_index (H := M)
  have h2 : M.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exfalso
      exact hM (eq_top_iff.2 (h ▸ Subgroup.normalCore_le M))
  rwa [h2, Subgroup.index_bot] at h1

theorem false_of_overgroups_solvable {Λ : Type*} [Group Λ] [Finite Λ] [IsSimpleGroup Λ]
    {S B : Subgroup Λ} (hov : ∀ M : Subgroup Λ, S ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M)
    (hBS : S ≤ Subgroup.normalizer (B : Set Λ)) (hperf : ⁅B, B⁆ = B) (hbot : B ≠ ⊥)
    (htop : B ≠ ⊤) : False := by
  have hMN : B ⊔ S ≤ Subgroup.normalizer (B : Set Λ) :=
    sup_le Subgroup.le_normalizer hBS
  have hMtop : B ⊔ S ≠ ⊤ := by
    intro h
    have hN : B.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have := hMN (h ▸ Subgroup.mem_top g)
      exact (Subgroup.mem_normalizer_iff.1 this n).1 hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h0 | h1
    · exact hbot h0
    · exact htop h1
  have hsolv := hov _ le_sup_right hMtop
  have hBM : B ≤ B ⊔ S := le_sup_left
  have : Group.IsSolvable ↥B :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBM)
      (Subgroup.inclusion_injective hBM)
  have hperf' : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).2 hbot
  exact Group.IsPerfect.not_isSolvable ↥B ‹_›

section Orders

variable {Λ : Type*} [Group Λ] [Finite Λ] {S M : Subgroup Λ}

theorem solvOver_card_168 (h : Nat.card Λ = 168) (hS : IsSylowTwoOf S ⊤) (hSM : S ≤ M)
    (hM : M ≠ ⊤) : Group.IsSolvable ↥M := by
  have hS8 : Nat.card S = 2 ^ 3 :=
    sylow_card_eq hS (a := 3) (m := 21) (by rw [h]; norm_num) (by decide)
  have hd1 : Nat.card M ∣ 168 := h ▸ Subgroup.card_subgroup_dvd_card M
  have hd2 : 8 ∣ Nat.card M := by
    have := Subgroup.card_dvd_of_le hSM
    rwa [hS8] at this
  have hne : Nat.card M ≠ 168 := fun h' => hM (Subgroup.eq_top_of_card_eq M (h'.trans h.symm))
  have hcases : Nat.card M = 8 ∨ Nat.card M = 24 ∨ Nat.card M = 56 := by
    have hle : Nat.card M ≤ 168 := Nat.le_of_dvd (by norm_num) hd1
    obtain ⟨c, hc⟩ := hd2
    have hc' : c ≤ 21 := by omega
    interval_cases c <;> simp_all
  rcases hcases with h8 | h24 | h56
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 0)
      (by rw [h8]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 1)
      (by rw [h24]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two (by norm_num : Nat.Prime 7) (by norm_num) (a := 3)
      (b := 1) (by rw [h56]; norm_num)

theorem solvOver_card_60 (h : Nat.card Λ = 60) (hS : IsSylowTwoOf S ⊤) (hSM : S ≤ M)
    (hM : M ≠ ⊤) : Group.IsSolvable ↥M := by
  have hS4 : Nat.card S = 2 ^ 2 :=
    sylow_card_eq hS (a := 2) (m := 15) (by rw [h]; norm_num) (by decide)
  have hd1 : Nat.card M ∣ 60 := h ▸ Subgroup.card_subgroup_dvd_card M
  have hd2 : 4 ∣ Nat.card M := by
    have := Subgroup.card_dvd_of_le hSM
    rwa [hS4] at this
  have hne : Nat.card M ≠ 60 := fun h' => hM (Subgroup.eq_top_of_card_eq M (h'.trans h.symm))
  have hcases : Nat.card M = 4 ∨ Nat.card M = 12 ∨ Nat.card M = 20 := by
    have hle : Nat.card M ≤ 60 := Nat.le_of_dvd (by norm_num) hd1
    obtain ⟨c, hc⟩ := hd2
    have hc' : c ≤ 15 := by omega
    interval_cases c <;> simp_all
  rcases hcases with h4 | h12 | h20
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 0)
      (by rw [h4]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 1)
      (by rw [h12]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two (by norm_num : Nat.Prime 5) (by norm_num) (a := 2)
      (b := 1) (by rw [h20]; norm_num)

theorem solvOver_card_360 [IsSimpleGroup Λ] (h : Nat.card Λ = 360) (hS : IsSylowTwoOf S ⊤)
    (hSM : S ≤ M)
    (hM : M ≠ ⊤) : Group.IsSolvable ↥M := by
  have hS8 : Nat.card S = 2 ^ 3 :=
    sylow_card_eq hS (a := 3) (m := 45) (by rw [h]; norm_num) (by decide)
  have hd1 : Nat.card M ∣ 360 := h ▸ Subgroup.card_subgroup_dvd_card M
  have hd2 : 8 ∣ Nat.card M := by
    have := Subgroup.card_dvd_of_le hSM
    rwa [hS8] at this
  have hne : Nat.card M ≠ 360 := fun h' => hM (Subgroup.eq_top_of_card_eq M (h'.trans h.symm))
  have hidx : Nat.card Λ ∣ M.index.factorial := card_dvd_factorial_index hM
  have hmul : Nat.card M * M.index = 360 := by rw [Subgroup.card_mul_index, h]
  have h120 : Nat.card M ≠ 120 := by
    intro h'
    rw [h'] at hmul
    have hi : M.index = 3 := by omega
    rw [hi, h] at hidx
    norm_num [Nat.factorial] at hidx
  have hcases : Nat.card M = 8 ∨ Nat.card M = 24 ∨ Nat.card M = 40 ∨ Nat.card M = 72 := by
    have hle : Nat.card M ≤ 360 := Nat.le_of_dvd (by norm_num) hd1
    obtain ⟨c, hc⟩ := hd2
    have hc' : c ≤ 45 := by omega
    interval_cases c <;> simp_all
  rcases hcases with h8 | h24 | h40 | h72
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 0)
      (by rw [h8]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 1)
      (by rw [h24]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two (by norm_num : Nat.Prime 5) (by norm_num) (a := 3)
      (b := 1) (by rw [h40]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 2)
      (by rw [h72]; norm_num)

end Orders

section Families

variable {G : Type} [Group G] [Finite G] {T K Y : Subgroup G}

theorem false_of_nu_vac (h : LtHyp G T K Y) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X)
    (hν : Function.Surjective ν)
    (hov : ∀ S M : Subgroup X, IsSylowTwoOf S ⊤ → S ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) :
    False :=
  false_of_overgroups_solvable (S := imgS T Y (phiOf Y ν)) (B := imgK K Y (phiOf Y ν))
    (fun M hSM hM => hov _ M (isSylow_imgS h _ (phi_surj hν)) hSM hM)
    (imgS_le_normalizer h _) (imgK_perfect h _)
    (imgK_ne_bot h _ fun y hy => (phi_hkc h hX hν y).1 hy)
    (imgK_ne_top h _ fun y hy => (phi_hkc h hX hν y).1 hy)

theorem false_of_sl3 (h : LtHyp G T K Y)
    (e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : False := by
  have := isSimpleGroup_sl_zmodTwo (n := 3) le_rfl
  exact false_of_nu_vac h Seven.slThree_nonabelian e.toMonoidHom e.surjective
    fun S M hS hSM hM => solvOver_card_168 card_sl_three_zmod_two hS hSM hM

theorem false_of_alt5 (h : LtHyp G T K Y)
    (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* ↥(alternatingGroup (Fin 5))) (hν : Function.Surjective ν) :
    False := by
  have := Seven.alt5_simple
  have hc : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  exact false_of_nu_vac h Seven.alt5_nonabelian ν hν
    fun S M hS hSM hM => solvOver_card_60 hc hS hSM hM

theorem false_of_alt6 (h : LtHyp G T K Y)
    (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* ↥(alternatingGroup (Fin 6))) (hν : Function.Surjective ν) :
    False := by
  have := Seven.alt6_simple
  have hc : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  exact false_of_nu_vac h Seven.alt6_nonabelian ν hν
    fun S M hS hSM hM => solvOver_card_360 hc hS hSM hM

end Families

end Lem1227Lt

end CFSG.Quasithin.H13
