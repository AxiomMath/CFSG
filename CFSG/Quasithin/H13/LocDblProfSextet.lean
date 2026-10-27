module

public import CFSG.Quasithin.H13.LocDblProfDefs
public import CFSG.Quasithin.H13.LocDblProfOrbit
public import CFSG.Quasithin.H13.LocDblProfAbel
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Prof

open scoped Pointwise

theorem card_filter_fix_modEq {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α)
    (s : Finset α) (hs : ∀ a, a ∈ s ↔ σ a ∈ s) (p : ℕ) [Fact p.Prime] (hσ : σ ^ p = 1) :
    s.card ≡ (s.filter fun a => σ a = a).card [MOD p] := by
  classical
  let τ : Equiv.Perm {a // a ∈ s} := σ.subtypePerm fun a => (hs a).symm
  have hτ : τ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext ⟨a, ha⟩
    simp [τ, Equiv.Perm.subtypePerm_pow, hσ]
  have h1 := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) hτ
  have h2 : τ.supportᶜ.card = (s.filter fun a => σ a = a).card := by
    refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hx
      simp only [Finset.mem_filter]
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      simpa [τ] using this
    · intro x _ y _ h
      exact Subtype.ext h
    · intro a ha
      simp only [Finset.mem_filter] at ha
      refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      apply Subtype.ext
      simpa [τ] using ha.2
  rw [h2, Fintype.card_coe] at h1
  exact h1.symm

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 24)]

theorem card_orbitSet_of_ptsOfSize {F : Subgroup Γ} (h : ptsOfSize F 4 = 24) :
    ∀ p : Fin 24, (orbitSet F p).card = 4 := by
  classical
  unfold ptsOfSize at h
  have := Finset.filter_card_eq (s := (Finset.univ : Finset (Fin 24)))
    (p := fun p => (orbitSet F p).card = 4) (by simpa using h)
  intro p
  exact this p (Finset.mem_univ p)

open Classical in
noncomputable def blocks (F : Subgroup Γ) : Finset (Finset (Fin 24)) :=
  Finset.univ.image (orbitSet F)

theorem card_blocks {F : Subgroup Γ} (h : ∀ p : Fin 24, (orbitSet F p).card = 4) :
    (blocks F).card = 6 := by
  classical
  have h1 := Finset.card_eq_sum_card_image (orbitSet F) (Finset.univ : Finset (Fin 24))
  have h2 : ∀ B ∈ blocks F, ((Finset.univ : Finset (Fin 24)).filter fun p => orbitSet F p = B).card
      = 4 := by
    intro B hB
    obtain ⟨p0, -, rfl⟩ := Finset.mem_image.1 hB
    have : ((Finset.univ : Finset (Fin 24)).filter fun p => orbitSet F p = orbitSet F p0) =
        orbitSet F p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        rw [← hx]
        exact self_mem_orbitSet F x
      · intro hx
        exact orbitSet_eq_of_mem hx
    rw [this, h p0]
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h3 : 24 = ∑ B ∈ blocks F, 4 := h1.trans (Finset.sum_congr rfl h2)
  rw [Finset.sum_const, smul_eq_mul] at h3
  omega

def blockKernel (F Y : Subgroup Γ) (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ)) : Subgroup ↥Y where
  carrier := {y | ∀ p : Fin 24, (y : Γ) • p ∈ orbitSet F p}
  mul_mem' := by
    intro a b ha hb p
    have hb' := hb p
    have ha' := ha ((b : Γ) • p)
    show ((a * b : ↥Y) : Γ) • p ∈ orbitSet F p
    rw [Subgroup.coe_mul, mul_smul]
    rw [orbitSet_eq_of_mem hb'] at ha'
    exact ha'
  one_mem' := fun p => by simpa using self_mem_orbitSet F p
  inv_mem' := by
    intro a ha p
    have h := ha (((a : Γ)⁻¹) • p)
    rw [smul_inv_smul] at h
    show (((a⁻¹ : ↥Y) : Γ)) • p ∈ orbitSet F p
    rw [Subgroup.coe_inv]
    exact mem_orbitSet_symm h

theorem blockKernel_normal (F Y : Subgroup Γ) (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ)) :
    (blockKernel F Y hnorm).Normal := by
  refine ⟨fun n hn g p => ?_⟩
  have hq := hn (((g : Γ)⁻¹) • p)
  have h1 := Finset.smul_mem_smul_finset (a := (g : Γ)) hq
  rw [smul_orbitSet (hnorm g.2), smul_inv_smul] at h1
  show (((g * n * g⁻¹ : ↥Y) : Γ)) • p ∈ orbitSet F p
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, mul_smul]
  exact h1

theorem blockKernel_ne_top [Finite Γ] {F Y : Subgroup Γ}
    (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ))
    (h9 : 9 ∣ Nat.card Y) (hnormal2 : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K)
    (hnofix : ∀ p : Fin 24, ∃ y ∈ Y, y • p ≠ p) (h4 : ∀ p : Fin 24, (orbitSet F p).card = 4) :
    blockKernel F Y hnorm ≠ ⊤ := by
  intro htop
  obtain ⟨y, hy, hne⟩ := hnofix 0
  have hall : ∀ y : ↥Y, ∀ p : Fin 24, (y : Γ) • p ∈ orbitSet F p := fun y p => by
    have : y ∈ blockKernel F Y hnorm := by rw [htop]; trivial
    exact this p
  have hsub : (MulAction.orbit ↥Y (0 : Fin 24)) ⊆ (orbitSet F 0 : Set (Fin 24)) := by
    rintro _ ⟨y, rfl⟩
    exact hall y 0
  have hle : Nat.card (MulAction.orbit ↥Y (0 : Fin 24)) ≤ 4 := by
    calc Nat.card (MulAction.orbit ↥Y (0 : Fin 24))
        = (MulAction.orbit ↥Y (0 : Fin 24)).ncard := Nat.card_coe_set_eq _
      _ ≤ (orbitSet F 0 : Set (Fin 24)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (orbitSet F 0).card := Set.ncard_coe_finset _
      _ = 4 := h4 0
  rcases orbit_card_eq_one_or_six_le (Y := ↥Y) h9 hnormal2 (0 : Fin 24) with h1 | h6
  · obtain ⟨a, ha⟩ := (Set.ncard_eq_one (s := MulAction.orbit ↥Y (0 : Fin 24))).1
      (by rw [← Nat.card_coe_set_eq]; exact h1)
    have h0 : (0 : Fin 24) ∈ MulAction.orbit ↥Y (0 : Fin 24) := MulAction.mem_orbit_self 0
    have hy0 : (⟨y, hy⟩ : ↥Y) • (0 : Fin 24) ∈ MulAction.orbit ↥Y (0 : Fin 24) :=
      MulAction.mem_orbit _ _
    rw [ha] at h0 hy0
    have e1 : (0 : Fin 24) = a := h0
    have e2 : (⟨y, hy⟩ : ↥Y) • (0 : Fin 24) = a := hy0
    exact hne (e2.trans e1.symm)
  · omega

theorem eq_one_of_isPGroup_three_two {G : Type*} [Group G] {A K : Subgroup G} (hA : IsPGroup 3 A)
    (hK : IsPGroup 2 K) {y : G} (hyA : y ∈ A) (hyK : y ∈ K) : y = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hA) ⟨y, hyA⟩
  obtain ⟨l, hl⟩ := (IsPGroup.iff_orderOf.1 hK) ⟨y, hyK⟩
  rw [Subgroup.orderOf_mk] at hk hl
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  · exfalso
    have h3 : 3 ∣ 2 ^ l := by
      rw [← hl, hk]
      exact dvd_pow_self 3 hkpos.ne'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega

theorem sextet_count {F : Subgroup Γ} (hb4 : ∀ p : Fin 24, (orbitSet F p).card = 4) {x : Γ}
    (hnx : x ∈ Subgroup.normalizer (F : Set Γ)) (hx3 : x ^ 3 = 1)
    (S : Finset (Finset (Fin 24))) (hSb : ∀ B ∈ S, ∃ p, B = orbitSet F p)
    (hSfix : ∀ p : Fin 24, orbitSet F p ∈ S ↔ x • orbitSet F p = orbitSet F p)
    (hS3 : S.card = 3)
    (htrans : ∀ B ∈ S, ∀ B' ∈ S, ∃ a : Γ, a * x = x * a ∧ a • B = B') :
    fixCount x = 3 ∨ fixCount x = 12 := by
  classical
  set t : Finset (Fin 24) → ℕ := fun B => (B.filter fun p => x • p = p).card with ht
  have hSinv : ∀ B ∈ S, x • B = B := by
    intro B hB
    obtain ⟨p, rfl⟩ := hSb B hB
    exact (hSfix p).1 hB
  have hdecomp : fixCount x = ∑ B ∈ S, t B := by
    unfold fixCount
    have : (Finset.univ.filter fun p : Fin 24 => x • p = p) =
        S.biUnion (fun B => B.filter fun p => x • p = p) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hp
        refine ⟨orbitSet F p, (hSfix p).2 ?_, self_mem_orbitSet F p, hp⟩
        rw [smul_orbitSet hnx, hp]
      · rintro ⟨B, hB, -, hp⟩
        exact hp
    rw [this, Finset.card_biUnion]
    intro B hB B' hB' hne
    obtain ⟨p, rfl⟩ := hSb B hB
    obtain ⟨q, rfl⟩ := hSb B' hB'
    exact Finset.disjoint_filter_filter (disjoint_orbitSet hne)
  have ht14 : ∀ B ∈ S, t B = 1 ∨ t B = 4 := by
    intro B hB
    obtain ⟨p, rfl⟩ := hSb B hB
    have hcard := hb4 p
    have hs : ∀ a : Fin 24, a ∈ orbitSet F p ↔
        (MulAction.toPerm x : Equiv.Perm (Fin 24)) a ∈ orbitSet F p := by
      intro a
      have h1 : x • a ∈ x • orbitSet F p ↔ a ∈ orbitSet F p := Finset.smul_mem_smul_finset_iff x
      rw [hSinv _ hB] at h1
      exact h1.symm
    have hσ : (MulAction.toPerm x : Equiv.Perm (Fin 24)) ^ 3 = 1 := by
      have : (MulAction.toPermHom Γ (Fin 24) x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
      exact this
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hmod := card_filter_fix_modEq (MulAction.toPerm x : Equiv.Perm (Fin 24))
      (orbitSet F p) hs 3 hσ
    have hle : t (orbitSet F p) ≤ 4 := hcard ▸ Finset.card_filter_le _ _
    rw [hcard] at hmod
    have hmod' : 4 ≡ t (orbitSet F p) [MOD 3] := hmod
    unfold Nat.ModEq at hmod'
    omega
  have hteq : ∀ B ∈ S, ∀ B' ∈ S, t B = t B' := by
    intro B hB B' hB'
    obtain ⟨a, hax, haB⟩ := htrans B hB B' hB'
    have hcx : x * a⁻¹ = a⁻¹ * x := Commute.inv_right (hax.symm : Commute x a)
    simp only [ht]
    refine Finset.card_bij (fun p _ => a • p) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨?_, ?_⟩
      · rw [← haB]
        exact Finset.smul_mem_smul_finset hp.1
      · calc x • a • p = (x * a) • p := (mul_smul _ _ _).symm
          _ = (a * x) • p := by rw [hax]
          _ = a • x • p := mul_smul _ _ _
          _ = a • p := by rw [hp.2]
    · intro p _ q _ h
      exact MulAction.injective a h
    · intro q hq
      simp only [Finset.mem_filter] at hq
      refine ⟨a⁻¹ • q, ?_, by simp⟩
      simp only [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.inv_smul_mem_iff, haB]
        exact hq.1
      · calc x • a⁻¹ • q = (x * a⁻¹) • q := (mul_smul _ _ _).symm
          _ = (a⁻¹ * x) • q := by rw [hcx]
          _ = a⁻¹ • x • q := mul_smul _ _ _
          _ = a⁻¹ • q := by rw [hq.2]
  obtain ⟨B0, hB0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hall : ∀ B ∈ S, t B = t B0 := fun B hB => hteq B hB B0 hB0
  rw [hdecomp, Finset.sum_congr rfl hall, Finset.sum_const, hS3, smul_eq_mul]
  rcases ht14 B0 hB0 with h | h <;> rw [h]
  · left; norm_num
  · right; norm_num

private theorem factorization_three_eq {j : ℕ} : (360 * 2 ^ j).factorization 3 = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 360 * 2 ^ j ≠ 0 := by positivity
  have h1 : 3 ^ 2 ∣ 360 * 2 ^ j := Dvd.dvd.mul_right (by norm_num) _
  have h2 : ¬ 3 ^ (2 + 1) ∣ 360 * 2 ^ j := by
    intro h
    have hcop : Nat.Coprime (3 ^ (2 + 1)) (2 ^ j) :=
      Nat.Coprime.pow _ _ (by norm_num)
    have := hcop.dvd_of_dvd_mul_right h
    norm_num at this
  have a := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).1 h1
  have b : ¬ (2 + 1 ≤ (360 * 2 ^ j).factorization 3) := fun h =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).2 h)
  omega

theorem false_of_sextet [Finite Γ] {Y F : Subgroup Γ} (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ))
    {j : ℕ} (hY : Nat.card Y = 360 * 2 ^ j)
    (hnormal2 : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K)
    (hnofix : ∀ p : Fin 24, ∃ y ∈ Y, y • p ≠ p)
    (hfix3 : ∀ x : Γ, x ≠ 1 → x ^ 3 = 1 → fixCount x = 0 ∨ fixCount x = 6)
    (h4 : ptsOfSize F 4 = 24) : False := by
  classical
  have hb4 := card_orbitSet_of_ptsOfSize h4
  have h9 : 9 ∣ Nat.card Y := by rw [hY]; exact Dvd.dvd.mul_right (by norm_num) _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hK0n := blockKernel_normal F Y hnorm
  have hK02 : IsPGroup 2 (blockKernel F Y hnorm) :=
    hnormal2 _ hK0n (blockKernel_ne_top hnorm h9 hnormal2 hnofix hb4)
  obtain ⟨A⟩ : Nonempty (Sylow 3 ↥Y) := inferInstance
  have hAcard : Nat.card (A : Subgroup ↥Y) = 3 ^ 2 := by
    rw [A.card_eq_multiplicity, hY, factorization_three_eq]
  have hAcomm : ∀ a b : ↥(A : Subgroup ↥Y), a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq hAcard
  let φA : ↥(A : Subgroup ↥Y) →* Γ := Y.subtype.comp (A : Subgroup ↥Y).subtype
  have hφinj : Function.Injective φA :=
    Y.subtype_injective.comp (A : Subgroup ↥Y).subtype_injective
  letI : MulAction ↥(A : Subgroup ↥Y) (Finset (Fin 24)) := MulAction.compHom _ φA
  have hφA : ∀ (a : ↥(A : Subgroup ↥Y)) (B : Finset (Fin 24)), a • B = (φA a) • B :=
    fun a B => rfl
  have hmemY : ∀ a : ↥(A : Subgroup ↥Y), φA a ∈ Y := fun a => (a : ↥Y).2
  have hcard6 := card_blocks hb4
  have hinv : ∀ a : ↥(A : Subgroup ↥Y), ∀ b ∈ blocks F, a • b ∈ blocks F := by
    intro a b hb
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hφA, smul_orbitSet (hnorm (hmemY a))]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hfaith : ∀ a : ↥(A : Subgroup ↥Y), (∀ b ∈ blocks F, a • b = b) → a = 1 := by
    intro a ha
    have hK : (a : ↥Y) ∈ blockKernel F Y hnorm := by
      intro p
      have h1 := ha (orbitSet F p) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      rw [hφA, smul_orbitSet (hnorm (hmemY a))] at h1
      have h2 := self_mem_orbitSet F (φA a • p)
      rw [h1] at h2
      exact h2
    have h1 : (a : ↥Y) = 1 := eq_one_of_isPGroup_three_two A.isPGroup' hK02 a.2 hK
    exact Subtype.ext h1
  obtain ⟨x, hx1, hx3, S, hSsub, hS3, hSfix, htrans⟩ :=
    exists_fixing_element_of_abelian_nine (A := ↥(A : Subgroup ↥Y)) (Ω := Finset (Fin 24))
      hAcard hAcomm (blocks F) hcard6 hinv hfaith
  have hxne : φA x ≠ 1 := fun h => hx1 (hφinj (h.trans (map_one φA).symm))
  have hx3' : φA x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hcount := sextet_count (F := F) hb4 (x := φA x) (hnorm (hmemY x)) hx3' S
    (fun B hB => by
      obtain ⟨p, -, hp⟩ := Finset.mem_image.1 (hSsub hB)
      exact ⟨p, hp.symm⟩)
    (fun p => (hSfix (orbitSet F p) (Finset.mem_image_of_mem _ (Finset.mem_univ _))).symm.trans
      Iff.rfl)
    hS3
    (fun B hB B' hB' => by
      obtain ⟨a, ha⟩ := htrans B hB B' hB'
      refine ⟨φA a, ?_, by rw [← hφA]; exact ha⟩
      rw [← map_mul, ← map_mul, hAcomm a x])
  rcases hfix3 (φA x) hxne hx3' with h | h <;> omega

end CFSG.Quasithin.H13.LocDbl.M24Prof
