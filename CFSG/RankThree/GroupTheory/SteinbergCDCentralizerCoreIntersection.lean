module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup CFSG.SolvableHall

theorem mem_iff_smul_mem_of_characteristic {B K : Type*} [Group B] [Group K]
    [MulDistribMulAction B K] (N : Subgroup K) [hN : N.Characteristic] (a : B) (x : K) :
    x ∈ N ↔ a • x ∈ N := by
  have h := Subgroup.characteristic_iff_comap_eq.mp hN (MulDistribMulAction.toMulAut B K a)
  have h2 : x ∈ N.comap (MulDistribMulAction.toMulAut B K a).toMonoidHom ↔ x ∈ N := by rw [h]
  exact h2.symm

theorem eq_one_of_mem_of_isPGroup_of_coprime {G : Type*} [Group G] {r : ℕ} {P L : Subgroup G}
    (hP : IsPGroup r P) (hL : Nat.Coprime r (Nat.card L)) {x : G} (hxP : x ∈ P) (hxL : x ∈ L) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ r ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  rw [← orderOf_eq_one_iff]
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (hL.pow_left k))
    (Subgroup.orderOf_dvd_natCard L hxL)

theorem exists_smul_eq_self_of_inv_mul_smul_mem {p : ℕ} [Fact p.Prime] {B K : Type*} [Group B]
    [Finite B] [Group K] [Finite K] [MulDistribMulAction B K] (hBp : IsPGroup p B)
    (D : Subgroup K) (hDinv : ∀ (a : B) (x : K), x ∈ D → a • x ∈ D) (hDp : ¬ p ∣ Nat.card D)
    (b : B) (g : K) (hg : g⁻¹ * (b • g) ∈ D) : ∃ c : K, b • c = c ∧ g⁻¹ * c ∈ D := by
  let S : Subgroup B :=
    { carrier := {a | g⁻¹ * (a • g) ∈ D}
      one_mem' := by
        change g⁻¹ * ((1 : B) • g) ∈ D
        rw [one_smul, inv_mul_cancel]
        exact one_mem D
      mul_mem' := by
        intro a a' ha ha'
        change g⁻¹ * ((a * a') • g) ∈ D
        have h : g⁻¹ * ((a * a') • g) = (g⁻¹ * (a • g)) * (a • (g⁻¹ * (a' • g))) := by
          rw [mul_smul, smul_mul', smul_inv']
          group
        rw [h]
        exact mul_mem ha (hDinv a _ ha')
      inv_mem' := by
        intro a ha
        change g⁻¹ * (a⁻¹ • g) ∈ D
        have h1 := hDinv a⁻¹ _ ha
        have h : a⁻¹ • (g⁻¹ * (a • g)) = (g⁻¹ * (a⁻¹ • g))⁻¹ := by
          rw [smul_mul', smul_inv', inv_smul_smul]
          group
        rw [h] at h1
        exact inv_mem_iff.mp h1 }
  have hbS : zpowers b ≤ S := zpowers_le.mpr hg
  let α : zpowers b →* MulAut K := (MulDistribMulAction.toMulAut B K).comp (zpowers b).subtype
  obtain ⟨c, hc, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p
    (hBp.to_subgroup _) α D hDp g).2 (by
      intro a x hx
      change g⁻¹ * ((a : B) • x) ∈ D
      have hag : g⁻¹ * ((a : B) • g) ∈ D := hbS a.2
      have h : g⁻¹ * ((a : B) • x) = (g⁻¹ * ((a : B) • g)) * ((a : B) • (g⁻¹ * x)) := by
        rw [smul_mul', smul_inv']
        group
      rw [h]
      exact mul_mem hag (hDinv _ _ hx))
  exact ⟨c, hcfix ⟨b, mem_zpowers b⟩, hc⟩

theorem iInf_pCore_fixedPoint_eq_bot_of_pCore_eq_bot {p r : ℕ} [Fact p.Prime] (hr : r.Prime)
    {B K : Type*} [Group B] [Finite B] [IsElementaryAbelian p B] [Group K] [Finite K]
    [MulDistribMulAction B K] (hB : p ^ 2 ≤ Nat.card B) (hK : Group.IsSolvable K)
    (hp : ¬ p ∣ Nat.card K) (hcore : pCore r K = ⊥) :
    ⨅ (b : B) (_ : b ≠ 1), (pCore r (fixedPointSubgroup (zpowers b) K)).map
      (fixedPointSubgroup (zpowers b) K).subtype = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  set X := ⨅ (b : B) (_ : b ≠ 1), (pCore r (fixedPointSubgroup (zpowers b) K)).map
      (fixedPointSubgroup (zpowers b) K).subtype with hX
  set L := pPrimeCore r K with hL
  have hLcop : Nat.Coprime r (Nat.card L) := pPrimeCore_coprime_card
  have hFL : fittingSubgroup K ≤ L := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    by_cases hqr : (q : ℕ) = r
    · rw [hqr, hcore]
      exact bot_le
    · have : Fact (q : ℕ).Prime := ⟨hq⟩
      refine le_sSup ⟨pCore_normal, ?_⟩
      obtain ⟨k, hk⟩ := (pCore_isPGroup (p := (q : ℕ)) (G := K)).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hr hq).mpr (Ne.symm hqr))
  have hCL : centralizer (L : Set K) ≤ L :=
    (centralizer_le hFL).trans
      ((CFSG.RankThree.PGroups.solvable_fitting_self_centralizing K).trans hFL)
  have hcomm : ∀ b : B, ∀ x ∈ (pCore r (fixedPointSubgroup (zpowers b) K)).map
      (fixedPointSubgroup (zpowers b) K).subtype, ∀ y ∈ L, b • y = y → x * y = y * x := by
    intro b x hx y hyL hby
    obtain ⟨x', hx', rfl⟩ := hx
    have hyC : y ∈ fixedPointSubgroup (zpowers b) K :=
      (mem_fixedPointSubgroup_zpowers_iff b y).mpr hby
    set y' : fixedPointSubgroup (zpowers b) K := ⟨y, hyC⟩
    have hc1 : y' * x' * y'⁻¹ * x'⁻¹ ∈ pCore r (fixedPointSubgroup (zpowers b) K) :=
      mul_mem (pCore_normal.conj_mem x' hx' y') (inv_mem hx')
    have hc2 : y * (x' : K) * y⁻¹ * (x' : K)⁻¹ ∈ L := by
      have h1 : (x' : K) * y⁻¹ * (x' : K)⁻¹ ∈ L :=
        (inferInstance : (pPrimeCore r K).Normal).conj_mem _ (inv_mem hyL) _
      have h := mul_mem hyL h1
      simpa only [mul_assoc] using h
    have hc1' : y * (x' : K) * y⁻¹ * (x' : K)⁻¹ ∈
        (pCore r (fixedPointSubgroup (zpowers b) K)).map
          (fixedPointSubgroup (zpowers b) K).subtype := ⟨_, hc1, rfl⟩
    have hc : y * (x' : K) * y⁻¹ * (x' : K)⁻¹ = 1 :=
      eq_one_of_mem_of_isPGroup_of_coprime (pCore_isPGroup.map _) hLcop hc1' hc2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc.symm
  have hLinv : ∀ (a : B) (x : K), x ∈ L ↔ a • x ∈ L :=
    mem_iff_smul_mem_of_characteristic L
  have : CFSG.IsInvariant B K L := ⟨hLinv⟩
  have hpL : ¬ p ∣ Nat.card L := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card L))
  have hgen := coprime_centralizer_generation (A := B) (H := L) hB hpL
  have hLX : L ≤ centralizer (X : Set K) := by
    intro y hy
    have hle : ⨆ (a : B) (_ : a ≠ 1), fixedPointSubgroup (zpowers a) L ≤
        (centralizer (X : Set K)).comap L.subtype := by
      refine iSup₂_le fun b hb => ?_
      intro y' hy'
      have hby : b • (y' : K) = y' :=
        congrArg Subtype.val ((mem_fixedPointSubgroup_zpowers_iff b y').mp hy')
      rw [mem_comap, mem_centralizer_iff]
      intro x hx
      exact hcomm b x (iInf₂_le (f := fun (b : B) (_ : b ≠ 1) =>
        (pCore r (fixedPointSubgroup (zpowers b) K)).map
          (fixedPointSubgroup (zpowers b) K).subtype) b hb hx) _ y'.2 hby
    have hmem : (⟨y, hy⟩ : L) ∈ ⨆ (a : B) (_ : a ≠ 1), fixedPointSubgroup (zpowers a) L := by
      rw [hgen]
      exact mem_top _
    exact hle hmem
  have hXL : X ≤ L := (le_centralizer_iff.mp hLX).trans hCL
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le hp1 hB)
  obtain ⟨b₀, hb₀⟩ := exists_ne (1 : B)
  rw [eq_bot_iff]
  intro x hx
  have hxO := iInf₂_le (f := fun (b : B) (_ : b ≠ 1) =>
    (pCore r (fixedPointSubgroup (zpowers b) K)).map
      (fixedPointSubgroup (zpowers b) K).subtype) b₀ hb₀ hx
  exact eq_one_of_mem_of_isPGroup_of_coprime (pCore_isPGroup.map _) hLcop hxO (hXL hx)

theorem coprime_solvable_centralizer_core_intersection {p r : ℕ} [Fact p.Prime] (hr : r.Prime)
    {B K : Type*} [Group B] [Finite B] [IsElementaryAbelian p B] [Group K] [Finite K]
    [MulDistribMulAction B K] (hB : p ^ 2 ≤ Nat.card B) (hK : Group.IsSolvable K)
    (hp : ¬ p ∣ Nat.card K) :
    ⨅ (b : B) (_ : b ≠ 1), (pCore r (fixedPointSubgroup (zpowers b) K)).map
        (fixedPointSubgroup (zpowers b) K).subtype =
      pCore r K ⊓ fixedPointSubgroup B K := by
  have : Fact r.Prime := ⟨hr⟩
  have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
  set π : Set Nat.Primes := {q | q.val = r} with hπ
  have hDeq : pCore r K = piCore π K := pCore_eq_piCore K r
  set D := piCore π K with hDdef
  have hDr : IsPGroup r D := hDeq ▸ pCore_isPGroup
  have hDinv : ∀ (a : B) (x : K), x ∈ D ↔ a • x ∈ D := mem_iff_smul_mem_of_characteristic D
  have hDp : ¬ p ∣ Nat.card D := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card D))
  let : MulDistribMulAction B (K ⧸ D) :=
    quotientMulDistribMulAction (A := B) (G := K) D ⟨hDinv⟩
  have hsmul : ∀ (a : B) (g : K), a • (g : K ⧸ D) = ((a • g : K) : K ⧸ D) := fun _ _ => rfl
  have hcoreQ : pCore r (K ⧸ D) = ⊥ := by
    rw [pCore_eq_piCore (K ⧸ D) r]
    exact CFSG.LocalCores.prime_set_core_quotient π
  have hpQ : ¬ p ∣ Nat.card (K ⧸ D) := fun h => hp (h.trans (Subgroup.card_quotient_dvd_card D))
  have := hK
  have hA := iInf_pCore_fixedPoint_eq_bot_of_pCore_eq_bot hr hB (inferInstance) hpQ hcoreQ
  have himage : ∀ (b : B) (x : K), x ∈ (pCore r (fixedPointSubgroup (zpowers b) K)).map
      (fixedPointSubgroup (zpowers b) K).subtype →
      (x : K ⧸ D) ∈ (pCore r (fixedPointSubgroup (zpowers b) (K ⧸ D))).map
        (fixedPointSubgroup (zpowers b) (K ⧸ D)).subtype := by
    intro b x hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hmapC : ∀ c : fixedPointSubgroup (zpowers b) K,
        ((c : K) : K ⧸ D) ∈ fixedPointSubgroup (zpowers b) (K ⧸ D) := fun c => by
      rw [mem_fixedPointSubgroup_zpowers_iff, hsmul,
        (mem_fixedPointSubgroup_zpowers_iff b (c : K)).mp c.2]
    let f : fixedPointSubgroup (zpowers b) K →* fixedPointSubgroup (zpowers b) (K ⧸ D) :=
      ((QuotientGroup.mk' D).comp (fixedPointSubgroup (zpowers b) K).subtype).codRestrict _ hmapC
    have hf : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g⁻¹ * (b • g) ∈ D := by
        have h := (mem_fixedPointSubgroup_zpowers_iff b _).mp hq
        rw [hsmul] at h
        exact QuotientGroup.eq.mp h.symm
      obtain ⟨c, hcfix, hcg⟩ := exists_smul_eq_self_of_inv_mul_smul_mem hBp D
        (fun a x hx => (hDinv a x).mp hx) hDp b g hg
      refine ⟨⟨c, (mem_fixedPointSubgroup_zpowers_iff b c).mpr hcfix⟩, Subtype.ext ?_⟩
      exact (QuotientGroup.eq.mpr hcg).symm
    have hle : (pCore r (fixedPointSubgroup (zpowers b) K)).map f ≤
        pCore r (fixedPointSubgroup (zpowers b) (K ⧸ D)) :=
      le_sSup ⟨pCore_normal.map f hf, pCore_isPGroup.map f⟩
    exact ⟨f x', hle ⟨x', hx', rfl⟩, rfl⟩
  rw [hDeq]
  apply le_antisymm
  · intro x hx
    have hx' : ∀ b : B, b ≠ 1 → x ∈ (pCore r (fixedPointSubgroup (zpowers b) K)).map
        (fixedPointSubgroup (zpowers b) K).subtype := fun b hb =>
      mem_iInf.mp (mem_iInf.mp hx b) hb
    refine ⟨?_, ?_⟩
    · change x ∈ D
      rw [← QuotientGroup.eq_one_iff]
      have hmem : (x : K ⧸ D) ∈ ⨅ (b : B) (_ : b ≠ 1),
          (pCore r (fixedPointSubgroup (zpowers b) (K ⧸ D))).map
            (fixedPointSubgroup (zpowers b) (K ⧸ D)).subtype :=
        mem_iInf.mpr fun b => mem_iInf.mpr fun hb => himage b x (hx' b hb)
      rw [hA] at hmem
      exact hmem
    · change x ∈ fixedPointSubgroup B K
      intro a
      by_cases ha : (a : B) = 1
      · rw [ha, one_smul]
      · obtain ⟨x', -, rfl⟩ := hx' a ha
        exact (mem_fixedPointSubgroup_zpowers_iff (a : B) _).mp x'.2
  · rintro x ⟨hxD, hxB⟩
    refine mem_iInf.mpr fun b => mem_iInf.mpr fun _ => ?_
    have hxC : x ∈ fixedPointSubgroup (zpowers b) K :=
      (mem_fixedPointSubgroup_zpowers_iff b x).mpr (hxB b)
    have hle : D.subgroupOf (fixedPointSubgroup (zpowers b) K) ≤
        pCore r (fixedPointSubgroup (zpowers b) K) :=
      le_sSup ⟨normal_subgroupOf, hDr.comap_of_injective _ (Subgroup.subtype_injective _)⟩
    exact ⟨⟨x, hxC⟩, hle hxD, rfl⟩

end CFSG.RankThree.GroupTheory
