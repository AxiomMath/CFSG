module

public import CFSG.Quasithin.H13.LocDblProfDefs
public import CFSG.Quasithin.H13.LocDblProfOrbit

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Prof

open scoped Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] [MulAction Γ (Fin 24)]

private theorem subgroup_smul_finset_eq {Y : Subgroup Γ} (z : ↥Y) (C : Finset (Fin 24)) :
    z • C = (z : Γ) • C :=
  rfl

private theorem card_filter_fix_modEq_five {y : Γ} (hy5 : y ^ 5 = 1) (B : Finset (Fin 24))
    (hB : y • B = B) :
    (B.filter fun p => y • p = p).card ≡ B.card [MOD 5] := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨f, hf⟩ : ∃ f : Equiv.Perm (Fin 24), f = MulAction.toPermHom Γ (Fin 24) y := ⟨_, rfl⟩
  have hfx : ∀ x : Fin 24, f x = y • x := fun x => by
    subst hf
    rfl
  have hf5 : f ^ 5 = 1 := by rw [hf, ← map_pow, hy5, map_one]
  have hinv : ∀ x : Fin 24, f x ∈ B ↔ x ∈ B := by
    intro x
    rw [hfx x]
    have key : y • x ∈ y • B ↔ x ∈ B := Finset.smul_mem_smul_finset_iff y
    rw [hB] at key
    exact key
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm {x : Fin 24 // x ∈ B},
      σ = f.subtypePerm (p := fun x => x ∈ B) hinv := ⟨_, rfl⟩
  have hσapp : ∀ a : {x : Fin 24 // x ∈ B}, (σ a).1 = f a.1 := fun a => by
    subst hσ
    rfl
  have hσ5 : σ ^ 5 = 1 := by
    have key : ∀ (τ : Equiv.Perm (Fin 24)) (hτ : τ = 1)
        (h : ∀ x : Fin 24, τ x ∈ B ↔ x ∈ B),
        τ.subtypePerm (p := fun x => x ∈ B) h = 1 := by
      intro τ hτ h
      subst hτ
      rfl
    rw [hσ, Equiv.Perm.subtypePerm_pow]
    exact key _ hf5 _
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ)
    (by simpa using hσ5)
  have hcardB : Fintype.card {x : Fin 24 // x ∈ B} = B.card := Fintype.card_coe B
  rw [hcardB] at hmod
  have hbij : σ.supportᶜ.card = (B.filter fun p => y • p = p).card := by
    apply Finset.card_bij (fun (a : {x : Fin 24 // x ∈ B}) _ => a.1)
    · intro a ha
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at ha
      have hval : f a.1 = a.1 := (hσapp a).symm.trans (congrArg Subtype.val ha)
      exact Finset.mem_filter.2 ⟨a.2, (hfx a.1).symm.trans hval⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro p hp
      obtain ⟨hpB, hpy⟩ := Finset.mem_filter.1 hp
      refine ⟨⟨p, hpB⟩, ?_, rfl⟩
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      apply Subtype.ext
      rw [hσapp]
      exact (hfx p).trans hpy
  rw [← hbij]
  exact hmod

private theorem smul_block_eq_of_le_five {Y F : Subgroup Γ}
    (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ)) (h9 : 9 ∣ Nat.card Y)
    (hnormal2 : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K)
    {s : ℕ} (q0 : Fin 24) (hq0 : (orbitSet F q0).card = s) (h5 : ptsOfSize F s ≤ 5 * s)
    {y : Γ} (hy : y ∈ Y) : y • orbitSet F q0 = orbitSet F q0 := by
  haveI : Fintype ↥Y := Fintype.ofFinite ↥Y
  obtain ⟨T, hT⟩ : ∃ T : Finset (Finset (Fin 24)),
      T = Finset.univ.image (fun z : ↥Y => z • orbitSet F q0) := ⟨_, rfl⟩
  have hmemT : ∀ C : Finset (Fin 24), C ∈ T ↔ ∃ z : ↥Y, z • orbitSet F q0 = C := by
    intro C
    simp only [hT, Finset.mem_image, Finset.mem_univ, true_and]
  have hTblock : ∀ C ∈ T, ∃ q : Fin 24, C = orbitSet F q := by
    intro C hC
    obtain ⟨z, rfl⟩ := (hmemT C).1 hC
    rw [subgroup_smul_finset_eq]
    exact ⟨(z : Γ) • q0, smul_orbitSet (hnorm z.2) q0⟩
  have hTcard : ∀ C ∈ T, C.card = s := by
    intro C hC
    obtain ⟨z, rfl⟩ := (hmemT C).1 hC
    rw [Finset.card_smul_finset, hq0]
  have hTdisj : ∀ C ∈ T, ∀ D ∈ T, C ≠ D → Disjoint C D := by
    intro C hC D hD hne
    obtain ⟨q, rfl⟩ := hTblock C hC
    obtain ⟨r, rfl⟩ := hTblock D hD
    exact disjoint_orbitSet hne
  have hsub : T.biUnion (fun C => C) ⊆
      Finset.univ.filter (fun p : Fin 24 => (orbitSet F p).card = s) := by
    intro p hp
    obtain ⟨C, hC, hpC⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨q, rfl⟩ := hTblock C hC
    have hpC' : p ∈ orbitSet F q := hpC
    rw [Finset.mem_filter, orbitSet_eq_of_mem hpC']
    exact ⟨Finset.mem_univ p, hTcard _ hC⟩
  have hbi : (T.biUnion (fun C => C)).card = ∑ C ∈ T, C.card :=
    Finset.card_biUnion (by
      intro C hC D hD hne
      exact hTdisj C hC D hD hne)
  have hle : (T.biUnion (fun C => C)).card ≤ ptsOfSize F s := Finset.card_le_card hsub
  have hsum : ∑ C ∈ T, C.card = T.card * s := by
    rw [Finset.sum_congr rfl hTcard, Finset.sum_const, smul_eq_mul]
  have hs0 : 0 < s := by
    rw [← hq0]
    exact Finset.card_pos.2 ⟨q0, self_mem_orbitSet F q0⟩
  have hT5 : T.card ≤ 5 := by
    have h1 : T.card * s ≤ 5 * s :=
      calc T.card * s = ∑ C ∈ T, C.card := hsum.symm
        _ = (T.biUnion (fun C => C)).card := hbi.symm
        _ ≤ ptsOfSize F s := hle
        _ ≤ 5 * s := h5
    exact Nat.le_of_mul_le_mul_right h1 hs0
  have hOT : (MulAction.orbit ↥Y (orbitSet F q0) : Set (Finset (Fin 24))) =
      (T : Set (Finset (Fin 24))) := by
    ext C
    rw [Finset.mem_coe, hmemT C, MulAction.mem_orbit_iff]
  have hcardorb : Nat.card (MulAction.orbit ↥Y (orbitSet F q0)) = T.card := by
    rw [Nat.card_coe_set_eq, hOT, Set.ncard_coe_finset]
  have hone : Nat.card (MulAction.orbit ↥Y (orbitSet F q0)) = 1 := by
    rcases orbit_card_eq_one_or_six_le h9 hnormal2 (orbitSet F q0) with h | h
    · exact h
    · omega
  haveI := (Nat.card_eq_one_iff_unique.1 hone).1
  have key := Subsingleton.elim (α := MulAction.orbit ↥Y (orbitSet F q0))
    ⟨(⟨y, hy⟩ : ↥Y) • orbitSet F q0, MulAction.mem_orbit _ _⟩
    ⟨orbitSet F q0, MulAction.mem_orbit_self _⟩
  exact congrArg Subtype.val key

theorem false_of_small {Y F : Subgroup Γ} (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ))
    (h9 : 9 ∣ Nat.card Y) (hnormal2 : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K)
    (hnofix : ∀ p : Fin 24, ∃ y ∈ Y, y • p ≠ p) {s : ℕ} (hs : s = 2 ∨ s = 4)
    (h0 : 0 < ptsOfSize F s) (h5 : ptsOfSize F s ≤ 5 * s) : False := by
  have hs4 : s ≤ 4 := by
    rcases hs with rfl | rfl <;> norm_num
  have h0' : 0 < (Finset.univ.filter fun p : Fin 24 => (orbitSet F p).card = s).card := h0
  obtain ⟨q0, hq0⟩ : ∃ q0 : Fin 24, (orbitSet F q0).card = s := by
    obtain ⟨p, hp⟩ := Finset.card_pos.1 h0'
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  have hB : ∀ y ∈ Y, y • orbitSet F q0 = orbitSet F q0 := fun y hy =>
    smul_block_eq_of_le_five hnorm h9 hnormal2 q0 hq0 h5 hy
  have hsub : (MulAction.orbit ↥Y q0 : Set (Fin 24)) ⊆ ↑(orbitSet F q0) := by
    intro x hx
    obtain ⟨z, rfl⟩ := MulAction.mem_orbit_iff.1 hx
    rw [Finset.mem_coe]
    have h1 : (z : Γ) • q0 ∈ (z : Γ) • orbitSet F q0 :=
      Finset.mem_smul_finset.2 ⟨q0, self_mem_orbitSet F q0, rfl⟩
    rw [hB (z : Γ) z.2] at h1
    exact h1
  have hcard : Nat.card (MulAction.orbit ↥Y q0) ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit ↥Y q0).ncard ≤ (↑(orbitSet F q0) : Set (Fin 24)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (orbitSet F q0).card := Set.ncard_coe_finset _
      _ ≤ 4 := by rw [hq0]; exact hs4
  have hone : Nat.card (MulAction.orbit ↥Y q0) = 1 := by
    rcases orbit_card_eq_one_or_six_le h9 hnormal2 q0 with h | h
    · exact h
    · omega
  haveI := (Nat.card_eq_one_iff_unique.1 hone).1
  obtain ⟨y, hy, hne⟩ := hnofix q0
  apply hne
  have key := Subsingleton.elim (α := MulAction.orbit ↥Y q0)
    ⟨(⟨y, hy⟩ : ↥Y) • q0, MulAction.mem_orbit _ _⟩ ⟨q0, MulAction.mem_orbit_self _⟩
  exact congrArg Subtype.val key

theorem false_of_eight {Y F : Subgroup Γ} (hnorm : Y ≤ Subgroup.normalizer (F : Set Γ))
    (h9 : 9 ∣ Nat.card Y) (hnormal2 : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K)
    (h5 : 5 ∣ Nat.card Y) (hfix5 : ∀ y : Γ, orderOf y = 5 → fixCount y ≤ 4)
    (h8 : ptsOfSize F 8 = 24) : False := by
  have hfull : Finset.univ.filter (fun q : Fin 24 => (orbitSet F q).card = 8) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    exact h8
  have hall : ∀ q : Fin 24, (orbitSet F q).card = 8 := by
    intro q
    have hq : q ∈ Finset.univ.filter (fun q : Fin 24 => (orbitSet F q).card = 8) := by
      rw [hfull]
      exact Finset.mem_univ q
    exact (Finset.mem_filter.1 hq).2
  have hB1 : (orbitSet F 0).card = 8 := hall 0
  obtain ⟨p2, hp2⟩ : ∃ p2 : Fin 24, p2 ∉ orbitSet F 0 := by
    by_contra hcon
    push Not at hcon
    have huniv : orbitSet F 0 = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hB1
    omega
  have hB2 : (orbitSet F p2).card = 8 := hall p2
  have hne12 : orbitSet F 0 ≠ orbitSet F p2 := by
    intro h
    apply hp2
    rw [h]
    exact self_mem_orbitSet F p2
  have hdisj : Disjoint (orbitSet F 0) (orbitSet F p2) := disjoint_orbitSet hne12
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x5, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 h5
  have hyorder : orderOf (x5 : Γ) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hx5
  have hy5 : (x5 : Γ) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one (x5 : Γ)
    rwa [hyorder] at h
  have hfix0 : (x5 : Γ) • orbitSet F 0 = orbitSet F 0 :=
    smul_block_eq_of_le_five hnorm h9 hnormal2 0 hB1 (by omega) x5.2
  have hfix2 : (x5 : Γ) • orbitSet F p2 = orbitSet F p2 :=
    smul_block_eq_of_le_five hnorm h9 hnormal2 p2 hB2 (by omega) x5.2
  have hm0 := card_filter_fix_modEq_five hy5 (orbitSet F 0) hfix0
  have hm2 := card_filter_fix_modEq_five hy5 (orbitSet F p2) hfix2
  unfold Nat.ModEq at hm0 hm2
  have hsubU : ((orbitSet F 0).filter fun p => (x5 : Γ) • p = p) ∪
      ((orbitSet F p2).filter fun p => (x5 : Γ) • p = p) ⊆
        Finset.univ.filter fun p : Fin 24 => (x5 : Γ) • p = p := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ p, (Finset.mem_filter.1 h).2⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ p, (Finset.mem_filter.1 h).2⟩
  have hdisjF : Disjoint ((orbitSet F 0).filter fun p => (x5 : Γ) • p = p)
      ((orbitSet F p2).filter fun p => (x5 : Γ) • p = p) :=
    Finset.disjoint_filter_filter hdisj
  have hcardU := Finset.card_union_of_disjoint hdisjF
  have hle := Finset.card_le_card hsubU
  have hfixC : fixCount (x5 : Γ) =
      (Finset.univ.filter fun p : Fin 24 => (x5 : Γ) • p = p).card := rfl
  have hfix4 := hfix5 (x5 : Γ) hyorder
  omega

end CFSG.Quasithin.H13.LocDbl.M24Prof
