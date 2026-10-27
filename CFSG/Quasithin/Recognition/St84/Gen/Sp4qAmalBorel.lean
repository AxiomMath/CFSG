module

public import CFSG.Quasithin.Recognition.St84.Sp44DC

import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpDiag

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.F112R.St84.Sp44 (B0 dTor rootXa rootXb T0B A1B A2B HB XaB XbB
  mem_dTor dSp_mem_dTor dSp_inj dTor_comm dTor_le antiUnipotent_inf_dTor
  rootXa_le_antiUnipotent rootXb_le_antiUnipotent frobAut_pow_dSp frobAut_mem_B0_iff
  B0_le_normalizer_radA1 B0_le_normalizer_radA2 A1_le_B0 A2_le_B0 Xa_le_B0 Xb_le_B0
  A1B_le_T0B A2B_le_T0B T0B_normal)
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 uElt_mul_self uElt_zero_eq_one
  card_radicals radA1_inf_radA2 mem_antiUnipotentCenter_iff_central
  radA1_le_antiUnipotent radA2_le_antiUnipotent antiUnipotentCenter_le_radA1
  antiUnipotentCenter_le_radA2 mul_self_of_mem_radA1 mul_self_of_mem_radA2
  elementary_le_radA1_or_radA2 card_and_isSylowTwoOf_antiUnipotent)
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Fin257.Sp4
open CFSG.Quasithin.H13.F431.SpOut2
open Matrix CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem B0_eq_sup_dTor : B0 F = antiUnipotent F ⊔ dTor F := by
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨u, s, t, hu, rfl, -⟩ :=
      CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
    exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (dSp_mem_dTor s t))
  · refine sup_le ?_ (dTor_le (F := F))
    exact Subgroup.le_normalizer

theorem T0B_isComplement'_HB : (T0B F).IsComplement' (HB F) := by
  haveI : (T0B F).Normal := T0B_normal (F := F)
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxT hxH
    apply Subtype.ext
    have hx : (x : antiSp F) ∈ antiUnipotent F ⊓ dTor F := ⟨hxT, hxH⟩
    rw [antiUnipotent_inf_dTor] at hx
    simpa using hx
  · rw [← Subgroup.normal_mul]
    have hsup : T0B F ⊔ HB F = ⊤ := by
      change (antiUnipotent F).subgroupOf
          (Subgroup.normalizer (antiUnipotent F : Set (antiSp F))) ⊔
        (dTor F).subgroupOf
          (Subgroup.normalizer (antiUnipotent F : Set (antiSp F))) = ⊤
      rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer
          (show dTor F ≤ Subgroup.normalizer (antiUnipotent F : Set (antiSp F)) from dTor_le),
        ← B0_eq_sup_dTor]
      change (Subgroup.normalizer (antiUnipotent F : Set (antiSp F))).subgroupOf
        (Subgroup.normalizer (antiUnipotent F : Set (antiSp F))) = ⊤
      exact Subgroup.subgroupOf_self (G := antiSp F)
        (H := Subgroup.normalizer (antiUnipotent F : Set (antiSp F)))
    rw [hsup]
    simp

private theorem card_dTor_eq_units_mul :
    Nat.card (dTor F) = Nat.card Fˣ * Nat.card Fˣ := by
  have hcard : Nat.card (Fˣ × Fˣ) = Nat.card (dTor F) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun p : Fˣ × Fˣ => (⟨dSp p.1 p.2, dSp_mem_dTor p.1 p.2⟩ : dTor F)) ⟨?_, ?_⟩)
    · intro p q h
      have h' : dSp p.1 p.2 = (dSp q.1 q.2 : antiSp F) := by
        simpa using congrArg (fun x : dTor F => (x : antiSp F)) h
      obtain ⟨h1, h2⟩ := dSp_inj h'
      exact Prod.ext h1 h2
    · rintro ⟨x, hx⟩
      obtain ⟨s, t, rfl⟩ := mem_dTor.mp hx
      exact ⟨(s, t), rfl⟩
  rw [← hcard, Nat.card_prod]

theorem odd_card_dTor : Odd (Nat.card (dTor F)) := by
  rw [card_dTor_eq_units_mul]
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hq⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hq
  have hunits : Nat.card Fˣ = 2 ^ (n : ℕ) - 1 := by
    rw [Nat.card_units, hcard]
  rw [hunits]
  have heven : Even (2 ^ (n : ℕ)) :=
    (even_two (α := ℕ)).pow_of_ne_zero n.pos.ne'
  have hodd : Odd (2 ^ (n : ℕ) - 1) :=
    Nat.Even.sub_odd (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) heven odd_one
  exact hodd.mul hodd

theorem isSolvable_B0 : Group.IsSolvable ↥(B0 F) :=
  CFSG.Quasithin.H13.Sec53F.isSolvable_bor (F := F)
    (card_and_isSylowTwoOf_antiUnipotent (K := F)).2.2.1

theorem map_T0B_eq (σ : MulAut ↥(B0 F)) : (T0B F).map σ.toMonoidHom = T0B F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (T0B F).Normal := T0B_normal (F := F)
  have hTp : IsPGroup 2 ↥(T0B F) :=
    (card_and_isSylowTwoOf_antiUnipotent (K := F)).2.2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := antiUnipotent F))).symm
  have hidx : ¬ 2 ∣ (T0B F).index := by
    have hidxcard := (T0B_isComplement'_HB (F := F)).symm.index_eq_card
    rw [hidxcard]
    have hcardHB : Nat.card (HB F) = Nat.card (dTor F) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (dTor_le (F := F))).toEquiv
    rw [hcardHB]
    exact (odd_card_dTor (F := F)).not_two_dvd_nat
  have hTpc : T0B F = CFSG.pCore 2 ↥(B0 F) := by
    refine le_antisymm ?_ ?_
    · exact le_sSup ⟨inferInstance, hTp⟩
    · let S : Sylow 2 ↥(B0 F) := hTp.toSylow hidx
      have hS : (S : Subgroup ↥(B0 F)) = T0B F := rfl
      refine sSup_le ?_
      rintro K ⟨hKn, hKp⟩
      letI : K.Normal := hKn
      have hle := IsPGroup.le_sylow_of_normal (p := 2) hKp S
      rwa [hS] at hle
  rw [hTpc]
  exact CFSG.pCore_map_iso 2 σ

private theorem isHallSubgroup_of_complement_odd {W : Subgroup ↥(B0 F)}
    (hW : Odd (Nat.card W)) (hcW : (T0B F).IsComplement' W) :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥(T0B F) :=
    (card_and_isSylowTwoOf_antiUnipotent (K := F)).2.2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := antiUnipotent F))).symm
  refine CFSG.isHallSubgroup_of _ W ?_ ?_
  · intro p hp
    have hpodd : Odd p.val := hW.of_dvd_nat hp
    intro h2
    rw [h2] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  · intro p hp hpdvd
    rw [hcW.index_eq_card] at hpdvd
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    rw [hk] at hpdvd
    exact hp ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow p.property hpdvd))

theorem exists_conj_map_HB (σ : MulAut ↥(B0 F)) :
    ∃ e : ↥(B0 F), (e : antiSp F) ∈ antiUnipotent F ∧
      (HB F).map (MulAut.conj e * σ).toMonoidHom = HB F := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (T0B F).Normal := T0B_normal (F := F)
  let Y : Subgroup ↥(B0 F) := (HB F).map σ.toMonoidHom
  have hYc : (T0B F).IsComplement' Y := by
    have hdisj : Disjoint (T0B F) Y := by
      have h := Subgroup.disjoint_map (f := σ.toMonoidHom)
        (show Function.Injective σ.toMonoidHom from σ.injective)
        (T0B_isComplement'_HB (F := F)).disjoint
      rwa [map_T0B_eq σ] at h
    have hsup : T0B F ⊔ Y = ⊤ := by
      have h := congrArg (fun S : Subgroup ↥(B0 F) => S.map σ.toMonoidHom)
        (T0B_isComplement'_HB (F := F)).sup_eq_top
      rw [Subgroup.map_sup, map_T0B_eq σ, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr σ.surjective] at h
      exact h
    exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj (by
      rw [← Subgroup.normal_mul, hsup]
      simp)
  have hHBodd : Odd (Nat.card (HB F)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (dTor_le (F := F))).toEquiv]
    exact odd_card_dTor
  have hYodd : Odd (Nat.card Y) := by
    rw [Subgroup.card_map_of_injective σ.injective]
    exact hHBodd
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable
    (isSolvable_B0 (F := F))
    (isHallSubgroup_of_complement_odd hYodd hYc)
    (isHallSubgroup_of_complement_odd hHBodd (T0B_isComplement'_HB (F := F)))
  obtain ⟨⟨u, y⟩, huy⟩ := hYc.2 g
  have huy' : (u : ↥(B0 F)) * (y : ↥(B0 F)) = g := by simpa using huy
  have hYnorm : Y.map (MulAut.conj (y : ↥(B0 F))).toMonoidHom = Y :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer y.2)
  have hYu : Y.map (MulAut.conj (u : ↥(B0 F))).toMonoidHom = HB F := by
    have hconj : MulAut.conj g = MulAut.conj (u : ↥(B0 F)) * MulAut.conj (y : ↥(B0 F)) := by
      rw [← huy', map_mul]
    have hcomp : (MulAut.conj (u : ↥(B0 F)) * MulAut.conj (y : ↥(B0 F))).toMonoidHom =
        (MulAut.conj (u : ↥(B0 F))).toMonoidHom.comp
          (MulAut.conj (y : ↥(B0 F))).toMonoidHom := rfl
    rw [hconj, hcomp, ← Subgroup.map_map, hYnorm] at hg
    exact hg.symm
  refine ⟨(u : ↥(B0 F)), Subgroup.mem_subgroupOf.mp u.2, ?_⟩
  have hcomp : (MulAut.conj (u : ↥(B0 F)) * σ).toMonoidHom =
      (MulAut.conj (u : ↥(B0 F))).toMonoidHom.comp σ.toMonoidHom := rfl
  rw [hcomp, ← Subgroup.map_map]
  exact hYu

private theorem card_A1B_eq : Nat.card (A1B F) = Nat.card F ^ 3 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A1_le_B0 (F := F))).toEquiv).trans
    (card_radicals (K := F)).2.1

private theorem card_A2B_eq : Nat.card (A2B F) = Nat.card F ^ 3 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A2_le_B0 (F := F))).toEquiv).trans
    (card_radicals (K := F)).2.2.1

private theorem A1B_ne_A2B : A1B F ≠ A2B F := by
  intro heq
  apply radA1_ne_radA2 (K := F)
  have hmap := congrArg (fun H : Subgroup ↥(B0 F) => H.map (B0 F).subtype) heq
  rwa [Subgroup.map_subgroupOf_eq_of_le (A1_le_B0 (F := F)),
    Subgroup.map_subgroupOf_eq_of_le (A2_le_B0 (F := F))] at hmap

theorem map_A2B_of_map_A1B (σ : MulAut ↥(B0 F)) (h : (A1B F).map σ.toMonoidHom = A1B F) :
    (A2B F).map σ.toMonoidHom = A2B F := by
  classical
  have hT : (T0B F).map σ.toMonoidHom = T0B F := map_T0B_eq σ
  have hcardA2 : Nat.card ((A2B F).map σ.toMonoidHom) = Nat.card F ^ 3 := by
    rw [Subgroup.card_map_of_injective σ.injective, card_A2B_eq]
  let E : Subgroup (antiSp F) := ((A2B F).map σ.toMonoidHom).map (B0 F).subtype
  have hEU : E ≤ antiUnipotent F := by
    rintro y ⟨b, hb, rfl⟩
    have hbT : b ∈ T0B F := by
      rw [← hT]
      exact Subgroup.map_mono A2B_le_T0B hb
    exact hbT
  have hE2 : ∀ y ∈ E, y * y = 1 := by
    rintro y ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hb
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      simpa using mul_self_of_mem_radA2 (K := F) ha
    have h' : σ a * σ a = 1 := by simpa using congrArg σ ha2
    simpa using congrArg (fun z : ↥(B0 F) => (z : antiSp F)) h'
  rcases elementary_le_radA1_or_radA2 hEU hE2 with hE1 | hE2'
  · have hle1 : (A2B F).map σ.toMonoidHom ≤ A1B F := by
      have h' : E ≤ (A1B F).map (B0 F).subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le (A1_le_B0 (F := F))]
      exact Subgroup.map_subtype_le_map_subtype.mp h'
    have heq1 : (A2B F).map σ.toMonoidHom = A1B F :=
      Subgroup.eq_of_le_of_card_ge hle1 (by rw [card_A1B_eq, hcardA2])
    have hmap : (A2B F).map σ.toMonoidHom = (A1B F).map σ.toMonoidHom := by
      rw [heq1, h]
    exact absurd (Subgroup.map_injective σ.injective hmap.symm) A1B_ne_A2B
  · have hle2 : (A2B F).map σ.toMonoidHom ≤ A2B F := by
      have h' : E ≤ (A2B F).map (B0 F).subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le (A2_le_B0 (F := F))]
      exact Subgroup.map_subtype_le_map_subtype.mp h'
    exact Subgroup.eq_of_le_of_card_ge hle2 (by rw [card_A2B_eq, hcardA2])

theorem map_A1B_of_map_A2B (σ : MulAut ↥(B0 F)) (h : (A2B F).map σ.toMonoidHom = A2B F) :
    (A1B F).map σ.toMonoidHom = A1B F := by
  classical
  have hT : (T0B F).map σ.toMonoidHom = T0B F := map_T0B_eq σ
  have hcardA1 : Nat.card ((A1B F).map σ.toMonoidHom) = Nat.card F ^ 3 := by
    rw [Subgroup.card_map_of_injective σ.injective, card_A1B_eq]
  let E : Subgroup (antiSp F) := ((A1B F).map σ.toMonoidHom).map (B0 F).subtype
  have hEU : E ≤ antiUnipotent F := by
    rintro y ⟨b, hb, rfl⟩
    have hbT : b ∈ T0B F := by
      rw [← hT]
      exact Subgroup.map_mono A1B_le_T0B hb
    exact hbT
  have hE2 : ∀ y ∈ E, y * y = 1 := by
    rintro y ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hb
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      simpa using mul_self_of_mem_radA1 (K := F) ha
    have h' : σ a * σ a = 1 := by simpa using congrArg σ ha2
    simpa using congrArg (fun z : ↥(B0 F) => (z : antiSp F)) h'
  rcases elementary_le_radA1_or_radA2 hEU hE2 with hE1 | hE2'
  · have hle1 : (A1B F).map σ.toMonoidHom ≤ A1B F := by
      have h' : E ≤ (A1B F).map (B0 F).subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le (A1_le_B0 (F := F))]
      exact Subgroup.map_subtype_le_map_subtype.mp h'
    exact Subgroup.eq_of_le_of_card_ge hle1 (by rw [card_A1B_eq, hcardA1])
  · have hle2 : (A1B F).map σ.toMonoidHom ≤ A2B F := by
      have h' : E ≤ (A2B F).map (B0 F).subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le (A2_le_B0 (F := F))]
      exact Subgroup.map_subtype_le_map_subtype.mp h'
    have heq2 : (A1B F).map σ.toMonoidHom = A2B F :=
      Subgroup.eq_of_le_of_card_ge hle2 (by rw [card_A2B_eq, hcardA1])
    have hmap : (A1B F).map σ.toMonoidHom = (A2B F).map σ.toMonoidHom := by
      rw [heq2, h]
    exact absurd (Subgroup.map_injective σ.injective hmap) A1B_ne_A2B

private theorem exists_lambda_of_four (hF : 4 ≤ Nat.card F) :
    ∃ lam : F, lam ≠ 0 ∧ lam + 1 ≠ 0 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have h1lt : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    omega
  obtain ⟨ω, hω1⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Fˣ)
  refine ⟨(ω : F), ω.ne_zero, ?_⟩
  intro h
  apply hω1
  apply Units.ext
  have h1 : (ω : F) = -1 := add_eq_zero_iff_eq_neg.mp h
  rwa [CharTwo.neg_eq] at h1

private theorem commutator_mem_closure {V : Subgroup (antiSp F)}
    (hxa : ∀ a : F, uElt a 0 0 0 ∈ V) (hxb : ∀ d : F, uElt 0 0 0 d ∈ V) (α δ : F) :
    uElt 0 (α * δ) (α ^ 2 * δ) 0 ∈ V := by
  have hx := hxa α
  have hy := hxb δ
  have hxinv : (uElt α 0 0 0 : antiSp F)⁻¹ ∈ V := V.inv_mem hx
  have hyinv : (uElt 0 0 0 δ : antiSp F)⁻¹ ∈ V := V.inv_mem hy
  have heq : uElt α 0 0 0 * uElt 0 0 0 δ * (uElt α 0 0 0)⁻¹ * (uElt 0 0 0 δ)⁻¹ =
      uElt 0 (α * δ) (α ^ 2 * δ) 0 := by
    have hxinv' : (uElt α 0 0 0 : antiSp F)⁻¹ = uElt α 0 0 0 := by
      rw [uElt_inv]
      congr 1 <;> ring
    have hyinv' : (uElt 0 0 0 δ : antiSp F)⁻¹ = uElt 0 0 0 δ := by
      rw [uElt_inv]
      congr 1 <;> ring
    rw [hxinv', hyinv']
    have hxy : uElt α 0 0 0 * uElt 0 0 0 δ = uElt α (α * δ) 0 δ := by
      rw [uElt_mul]
      congr 1 <;> ring
    calc uElt α 0 0 0 * uElt 0 0 0 δ * uElt α 0 0 0 * uElt 0 0 0 δ
        = (uElt α 0 0 0 * uElt 0 0 0 δ) * (uElt α 0 0 0 * uElt 0 0 0 δ) := by group
      _ = (uElt α (α * δ) 0 δ) * (uElt α (α * δ) 0 δ) := by rw [hxy]
      _ = uElt 0 (α * δ) (α ^ 2 * δ) 0 := by rw [uElt_mul_self]
  rw [← heq]
  exact V.mul_mem (V.mul_mem (V.mul_mem hx hy) hxinv) hyinv

private theorem mem_rootU_closure_of_four (hF : 4 ≤ Nat.card F) {V : Subgroup (antiSp F)}
    (hcomm : ∀ α δ : F, uElt 0 (α * δ) (α ^ 2 * δ) 0 ∈ V) :
    (∀ b : F, uElt 0 b 0 0 ∈ V) ∧ (∀ c : F, uElt 0 0 c 0 ∈ V) := by
  obtain ⟨lam, hlam0, hlam1⟩ := exists_lambda_of_four (F := F) hF
  have hμ : lam * (lam + 1) ≠ 0 := mul_ne_zero hlam0 hlam1
  constructor
  · intro b
    let δ : F := b / (lam * (lam + 1))
    have hδ : b = lam * δ + lam ^ 2 * δ := by
      rw [show lam * δ + lam ^ 2 * δ = (lam * (lam + 1)) * δ by ring]
      exact (mul_div_cancel₀ b hμ).symm
    have h1 : uElt 0 (lam * δ) (lam ^ 2 * δ) 0 ∈ V := hcomm lam δ
    have h2 : uElt 0 (lam ^ 2 * δ) (lam ^ 2 * δ) 0 ∈ V := by
      simpa using hcomm 1 (lam ^ 2 * δ)
    have hprod : uElt 0 (lam ^ 2 * δ) (lam ^ 2 * δ) 0 *
        uElt 0 (lam * δ) (lam ^ 2 * δ) 0 = uElt 0 b 0 0 := by
      rw [uElt_mul]
      simp only [zero_mul, mul_zero, add_zero]
      rw [show lam ^ 2 * δ + lam * δ = b by rw [add_comm, ← hδ],
        CharTwo.add_self_eq_zero]
    rw [← hprod]
    exact V.mul_mem h2 h1
  · intro c
    let δ : F := c / (lam * (lam + 1))
    have hδ : c = lam * δ + lam ^ 2 * δ := by
      rw [show lam * δ + lam ^ 2 * δ = (lam * (lam + 1)) * δ by ring]
      exact (mul_div_cancel₀ c hμ).symm
    have h1 : uElt 0 (lam * δ) (lam ^ 2 * δ) 0 ∈ V := hcomm lam δ
    have h2 : uElt 0 (lam * δ) (lam * δ) 0 ∈ V := by
      simpa using hcomm 1 (lam * δ)
    have hprod : uElt 0 (lam * δ) (lam * δ) 0 * uElt 0 (lam * δ) (lam ^ 2 * δ) 0 =
        uElt 0 0 c 0 := by
      rw [uElt_mul]
      simp only [zero_mul, mul_zero, add_zero]
      rw [CharTwo.add_self_eq_zero, hδ.symm]
    rw [← hprod]
    exact V.mul_mem h2 h1

theorem B0_le_closure_roots (hF : 4 ≤ Nat.card F) :
    B0 F ≤ Subgroup.closure ((rootXa F : Set (antiSp F)) ∪ rootXb F ∪ dTor F) := by
  classical
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  let V : Subgroup (antiSp F) :=
    Subgroup.closure ((rootXa F : Set (antiSp F)) ∪ rootXb F ∪ dTor F)
  have hxa : ∀ a : F, uElt a 0 0 0 ∈ V := fun a =>
    Subgroup.subset_closure (Or.inl (Or.inl ⟨a, rfl⟩))
  have hxb : ∀ d : F, uElt 0 0 0 d ∈ V := fun d =>
    Subgroup.subset_closure (Or.inl (Or.inr ⟨d, rfl⟩))
  have hT : ∀ s t : Fˣ, dSp s t ∈ V := fun s t =>
    Subgroup.subset_closure (Or.inr (dSp_mem_dTor s t))
  have hcomm : ∀ α δ : F, uElt 0 (α * δ) (α ^ 2 * δ) 0 ∈ V :=
    commutator_mem_closure hxa hxb
  obtain ⟨hU1, hU2⟩ := mem_rootU_closure_of_four hF hcomm
  have hZ : antiUnipotentCenter F ≤ V := by
    rintro _ ⟨b, c, rfl⟩
    have hb := hU1 b
    have hc := hU2 c
    have hprod : uElt 0 b 0 0 * uElt 0 0 c 0 = uElt 0 b c 0 := by
      rw [uElt_mul]
      congr 1 <;> ring
    rw [← hprod]
    exact V.mul_mem hb hc
  intro g hg
  obtain ⟨u, s, t, hu, rfl, -⟩ :=
    CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
  obtain ⟨a, b, c, d, rfl⟩ := hu
  have hfac : uElt a b c d =
      uElt a 0 0 0 * uElt 0 0 0 d * uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := by
    have h1 : uElt a 0 0 0 * uElt 0 0 0 d = uElt a (a * d) 0 d := by
      rw [uElt_mul]
      congr 1 <;> ring
    have h2 : uElt a (a * d) 0 d * uElt 0 (b + a * d) (c + a * (b + a * d)) 0 =
        uElt a b c d := by
      rw [uElt_mul]
      congr 1 <;> (ring_nf; try simp [htwo])
    calc uElt a b c d
        = uElt a (a * d) 0 d * uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := h2.symm
      _ = (uElt a 0 0 0 * uElt 0 0 0 d) *
            uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := by rw [← h1]
      _ = uElt a 0 0 0 * uElt 0 0 0 d *
            uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := rfl
  rw [hfac]
  exact V.mul_mem (V.mul_mem (V.mul_mem (hxa a) (hxb d)) (hZ ⟨_, _, rfl⟩)) (hT s t)

private theorem closure_generators_B0 (hF : 4 ≤ Nat.card F) :
    Subgroup.closure ((XaB F : Set ↥(B0 F)) ∪ XbB F ∪ HB F) = ⊤ := by
  classical
  let T : Set (antiSp F) := (rootXa F : Set (antiSp F)) ∪ rootXb F ∪ dTor F
  have hsub : T ⊆ B0 F := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact Xa_le_B0 hx
    · exact Xb_le_B0 hx
    · exact dTor_le hx
  have hS : Subgroup.closure T = B0 F :=
    le_antisymm ((Subgroup.closure_le (K := B0 F)).mpr hsub) (B0_le_closure_roots hF)
  have hpre := Subgroup.closure_preimage_eq_top (G := antiSp F) T
  let e : ↥(Subgroup.closure T) ≃* ↥(B0 F) := MulEquiv.subgroupCongr hS
  have himage : e.toMonoidHom '' ((Subgroup.closure T).subtype ⁻¹' T) =
      (B0 F).subtype ⁻¹' T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ((y : ↥(Subgroup.closure T)) : antiSp F) ∈ T
      exact hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      show ((x : ↥(B0 F)) : antiSp F) ∈ T
      exact hx
  have hmap : (Subgroup.closure ((Subgroup.closure T).subtype ⁻¹' T)).map e.toMonoidHom =
      Subgroup.closure ((B0 F).subtype ⁻¹' T) := by
    rw [MonoidHom.map_closure, himage]
  have htop : Subgroup.closure ((B0 F).subtype ⁻¹' T) = ⊤ := by
    rw [← hmap, hpre, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]
  have hset : ((B0 F).subtype ⁻¹' T : Set ↥(B0 F)) =
      (XaB F : Set ↥(B0 F)) ∪ XbB F ∪ HB F := by
    ext x
    simp [T, XaB, XbB, HB, Subgroup.mem_subgroupOf]
  rwa [hset] at htop

theorem B0_monoidHom_ext {M : Type*} [Group M] (hF : 4 ≤ Nat.card F) {φ ψ : ↥(B0 F) →* M}
    (h : ∀ b : ↥(B0 F), ((b : antiSp F) ∈ rootXa F ∨ (b : antiSp F) ∈ rootXb F ∨
      (b : antiSp F) ∈ dTor F) → φ b = ψ b) : φ = ψ := by
  refine MonoidHom.eq_of_eqOn_dense (closure_generators_B0 (F := F) hF) ?_
  intro b hb
  exact h b (by
    simpa [XaB, XbB, HB, Subgroup.mem_subgroupOf, or_assoc] using hb)

theorem conj_frobAut_pow_uElt_a (s t : Fˣ) (k : ℕ) (a : F) :
    (MulAut.conj (dSp s t) * frobAut F ^ k) (uElt a 0 0 0) =
      uElt ((s : F) * ((t⁻¹ : Fˣ) : F) * a ^ 2 ^ k) 0 0 0 := by
  rw [MulAut.mul_apply, frobAut_pow_uElt, MulAut.conj_apply, dSp_conj_uElt]
  simp

theorem conj_frobAut_pow_uElt_d (s t : Fˣ) (k : ℕ) (d : F) :
    (MulAut.conj (dSp s t) * frobAut F ^ k) (uElt 0 0 0 d) =
      uElt 0 0 0 ((t : F) ^ 2 * d ^ 2 ^ k) := by
  rw [MulAut.mul_apply, frobAut_pow_uElt, MulAut.conj_apply, dSp_conj_uElt]
  simp

theorem conj_frobAut_pow_dSp (s t : Fˣ) (k : ℕ) (s' t' : Fˣ) :
    (MulAut.conj (dSp s t) * frobAut F ^ k) (dSp s' t') = dSp (s' ^ 2 ^ k) (t' ^ 2 ^ k) := by
  rw [MulAut.mul_apply, frobAut_pow_dSp, MulAut.conj_apply]
  have hcomm := dTor_comm (dSp_mem_dTor (F := F) s t)
    (dSp_mem_dTor (F := F) (s' ^ 2 ^ k) (t' ^ 2 ^ k))
  rw [hcomm]
  group

private theorem iff_of_map_eq {G : Type*} [Group G] (τ : MulAut G) {S : Subgroup G}
    (hS : S.map τ.toMonoidHom = S) (b : G) : b ∈ S ↔ τ b ∈ S := by
  constructor
  · intro hb
    rw [← hS]
    exact Subgroup.mem_map_of_mem τ.toMonoidHom hb
  · intro hb
    rw [← hS] at hb
    obtain ⟨b', hb', he⟩ := Subgroup.mem_map.mp hb
    rw [← τ.injective he]
    exact hb'

private theorem map_normalizer_of_map (τ : MulAut (antiSp F)) {H : Subgroup (antiSp F)}
    (hH : H.map τ.toMonoidHom = H) :
    (Subgroup.normalizer (H : Set (antiSp F))).map τ.toMonoidHom =
      Subgroup.normalizer (H : Set (antiSp F)) := by
  rw [Subgroup.map_normalizer_eq_of_bijective H
    (show Function.Bijective τ.toMonoidHom from τ.bijective), hH]

theorem conj_frobAut_pow_mem_normalizer_radA1_iff {g : antiSp F} (hg : g ∈ B0 F) (k : ℕ)
    (x : antiSp F) :
    x ∈ Subgroup.normalizer (radA1 F : Set (antiSp F)) ↔
      (MulAut.conj g * frobAut F ^ k) x ∈
        Subgroup.normalizer (radA1 F : Set (antiSp F)) := by
  have hconj : (radA1 F).map (MulAut.conj g).toMonoidHom = radA1 F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (B0_le_normalizer_radA1 hg)
  have hfrob : (radA1 F).map ((frobAut F ^ k)).toMonoidHom = radA1 F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (frobAut_pow_mem_iff frobAut_mem_radA1_iff k z).mpr hz
    · intro hy
      exact ⟨(frobAut F ^ k)⁻¹ y,
        (frobAut_pow_mem_iff frobAut_mem_radA1_iff k _).mp (by simpa using hy), by simp⟩
  have hmap : (radA1 F).map (MulAut.conj g * frobAut F ^ k).toMonoidHom = radA1 F := by
    have hcomp : (MulAut.conj g * frobAut F ^ k).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (frobAut F ^ k).toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map, hfrob, hconj]
  exact iff_of_map_eq _ (map_normalizer_of_map _ hmap) x

theorem conj_frobAut_pow_mem_normalizer_radA2_iff {g : antiSp F} (hg : g ∈ B0 F) (k : ℕ)
    (x : antiSp F) :
    x ∈ Subgroup.normalizer (radA2 F : Set (antiSp F)) ↔
      (MulAut.conj g * frobAut F ^ k) x ∈
        Subgroup.normalizer (radA2 F : Set (antiSp F)) := by
  have hconj : (radA2 F).map (MulAut.conj g).toMonoidHom = radA2 F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (B0_le_normalizer_radA2 hg)
  have hfrob : (radA2 F).map ((frobAut F ^ k)).toMonoidHom = radA2 F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (frobAut_pow_mem_iff frobAut_mem_radA2_iff k z).mpr hz
    · intro hy
      exact ⟨(frobAut F ^ k)⁻¹ y,
        (frobAut_pow_mem_iff frobAut_mem_radA2_iff k _).mp (by simpa using hy), by simp⟩
  have hmap : (radA2 F).map (MulAut.conj g * frobAut F ^ k).toMonoidHom = radA2 F := by
    have hcomp : (MulAut.conj g * frobAut F ^ k).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (frobAut F ^ k).toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map, hfrob, hconj]
  exact iff_of_map_eq _ (map_normalizer_of_map _ hmap) x

theorem conj_frobAut_pow_mem_B0_iff {g : antiSp F} (hg : g ∈ B0 F) (k : ℕ) (x : antiSp F) :
    x ∈ B0 F ↔ (MulAut.conj g * frobAut F ^ k) x ∈ B0 F := by
  have hconj : (antiUnipotent F).map (MulAut.conj g).toMonoidHom = antiUnipotent F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hfrob : (antiUnipotent F).map ((frobAut F ^ k)).toMonoidHom = antiUnipotent F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (frobAut_pow_mem_antiUnipotent_iff k z).mpr hz
    · intro hy
      exact ⟨(frobAut F ^ k)⁻¹ y,
        (frobAut_pow_mem_antiUnipotent_iff k _).mp (by simpa using hy), by simp⟩
  have hmap : (antiUnipotent F).map (MulAut.conj g * frobAut F ^ k).toMonoidHom =
      antiUnipotent F := by
    have hcomp : (MulAut.conj g * frobAut F ^ k).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (frobAut F ^ k).toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map, hfrob, hconj]
  exact iff_of_map_eq _ (map_normalizer_of_map _ hmap) x

theorem normalizer_radA1_inf_normalizer_radA2 {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
      Subgroup.normalizer (radA2 F : Set (antiSp F)) = B0 F :=
  (CFSG.Quasithin.H13.F431.SpModel.borel_antiSp (F := F) hn hF).inf_norm

theorem pCoreOf_normalizer_radA1 {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (Subgroup.normalizer (radA1 F : Set (antiSp F))) = radA1 F :=
  (CFSG.Quasithin.H13.F431.SpModel.borel_antiSp (F := F) hn hF).core₁

theorem pCoreOf_normalizer_radA2 {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (Subgroup.normalizer (radA2 F : Set (antiSp F))) = radA2 F :=
  (CFSG.Quasithin.H13.F431.SpModel.borel_antiSp (F := F) hn hF).core₂

end CFSG.Quasithin.F112R.St84
