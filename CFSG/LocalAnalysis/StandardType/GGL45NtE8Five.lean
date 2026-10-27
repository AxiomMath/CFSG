module

public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneCases

public noncomputable section

namespace CFSG.HardMathSupport.C14Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE8F

open scoped Matrix

theorem e8FiveG1_mem_fixReflectionGroup (p : ℕ) :
    e8FiveG1 ∈ fixReflectionGroup p e8FiveG1 := by
  let l : List (Fin Tag.E8.rank) := [0, 2, 3, 1]
  let y : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
    ![![0, 1, 1, 2, 2, 0, 0, 0], ![1, 1, 2, 3, 2, 0, 0, 0],
      ![1, 1, 1, 2, 2, 0, 0, 0], ![1, 1, 2, 2, 2, 0, 0, 0],
      0, 0, 0, 0]
  have hy : ∀ i ∈ l, (Pi.single i 1 : Fin Tag.E8.rank → ℤ) =
      l.foldr (reflect .E8) (y i) - y i := by
    decide +kernel
  have hi : ∀ i ∈ l, simple .E8 i ∈ fixReflectionGroup p e8FiveG1 := by
    intro i hil
    have h := conj_simple_mem_fixReflectionGroup (p := p)
      (w₀ := e8FiveG1) (u := 1) (i := i) (y i) 0 (by
        simp only [one_smul, smul_zero, add_zero]
        change Pi.single i 1 = (l.map (simple .E8)).prod • y i - y i
        rw [lattice_list_prod_simple_smul]
        exact hy i hil)
    simpa using h
  change (l.map (simple .E8)).prod ∈ fixReflectionGroup p e8FiveG1
  apply Subgroup.list_prod_mem
  intro s hs
  obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hs
  exact hi i hil

set_option maxRecDepth 16384 in
theorem e8FiveG2_mem_fixReflectionGroup (p : ℕ) :
    e8FiveG2 ∈ fixReflectionGroup p e8FiveG2 := by
  let l : List (Fin Tag.E8.rank) :=
    [4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6]
  let u : WeylGroup .E8 := (coxeterSystem .E8).wordProd l
  let β : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 3, 2, 1]
  have hu : u • (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = β := by
    change (l.map (simple .E8)).prod • Pi.single 7 1 = β
    rw [lattice_list_prod_simple_smul]
    funext k
    fin_cases k <;> decide +kernel
  have hprod : e8FiveG2 = simple .E8 7 * simple .E8 6 * simple .E8 5 *
      (u * simple .E8 7 * u⁻¹) := by
    change (coxeterSystem .E8).wordProd ([7, 6, 5] ++ (l ++ [7] ++ l.reverse)) = _
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_reverse]
    change simple .E8 7 * (simple .E8 6 * (simple .E8 5 * 1)) *
      ((u * (simple .E8 7 * 1)) * u⁻¹) = _
    simp only [mul_one, mul_assoc]
  let nodes : Fin 3 → Fin Tag.E8.rank := ![7, 6, 5]
  let y : Fin 3 → Fin Tag.E8.rank → ℤ :=
    ![![0, 0, 0, 0, -1, -1, -1, -1], ![0, 0, 0, 0, -1, -1, -1, 0],
      ![0, 0, 0, 0, -1, -1, 0, 0]]
  have hy : ∀ i, (Pi.single (nodes i) 1 : Fin Tag.E8.rank → ℤ) =
      e8FiveG2 • y i - y i := by
    change ∀ i, Pi.single (nodes i) 1 =
      (([7, 6, 5] ++ (l ++ [7] ++ l.reverse)).map (simple .E8)).prod • y i - y i
    simp_rw [lattice_list_prod_simple_smul]
    intro i
    funext k
    revert i k
    decide +kernel
  have hi : ∀ i, simple .E8 (nodes i) ∈ fixReflectionGroup p e8FiveG2 := by
    intro i
    have h := conj_simple_mem_fixReflectionGroup (p := p)
      (w₀ := e8FiveG2) (u := 1) (i := nodes i) (y i) 0 (by
        simpa only [one_smul, smul_zero, add_zero] using hy i)
    simpa using h
  have hβ : β = e8FiveG2 • (-Pi.single 4 1 : Fin Tag.E8.rank → ℤ) -
      (-Pi.single 4 1) := by
    change β = (([7, 6, 5] ++ (l ++ [7] ++ l.reverse)).map (simple .E8)).prod •
      (-Pi.single 4 1 : Fin Tag.E8.rank → ℤ) - (-Pi.single 4 1)
    rw [lattice_list_prod_simple_smul]
    funext k
    fin_cases k <;> decide +kernel
  have hroot := conj_simple_mem_fixReflectionGroup (p := p)
    (w₀ := e8FiveG2) (u := u) (i := 7) (-Pi.single 4 1) 0 (by
      rw [hu]
      simpa only [smul_zero, add_zero] using hβ)
  have hmem : simple .E8 7 * simple .E8 6 * simple .E8 5 *
      (u * simple .E8 7 * u⁻¹) ∈ fixReflectionGroup p e8FiveG2 :=
    mul_mem (mul_mem (mul_mem (hi 0) (hi 1)) (hi 2)) hroot
  simpa only [← hprod] using hmem



local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem ncard_fixSet_e8Five_pow_mul_le (i j : Fin 5)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    (fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ))).ncard ≤ 25 := by
  have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
  have hid : ¬ 5 ∣ (i : ℕ) := fun h =>
    hi0 (Nat.eq_zero_of_dvd_of_lt h i.isLt)
  have hex : ∀ i j : Fin 5, (i : ℕ) ≠ 0 →
      ∃ m : Fin 5, ((m : ℕ) * i) % 5 = j := by decide
  obtain ⟨m, hm⟩ := hex i j hi0
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    simp only [Fin.val_zero, zero_mul, Nat.zero_mod] at hm
    exact hj0 hm.symm
  have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) =
      (e8FiveH m) ^ (i : ℕ) := by
    have hc : Commute e8FiveG1 (e8FiveG2 ^ (m : ℕ)) :=
      Commute.pow_right e8Five_comm _
    rw [e8FiveH, hc.mul_pow, ← pow_mul,
      pow_eq_pow_mod ((m : ℕ) * (i : ℕ)) e8FiveG2_pow, hm]
  have hbound : (fixSet (e8FiveH m)).ncard ≤ 25 := by
    fin_cases m
    · exact (hm0 rfl).elim
    · exact ncard_fixSet_le_of_param (fun _ hz => fixSet_h1_param hz)
    · exact ncard_fixSet_le_of_param (fun _ hz => fixSet_h2_param hz)
    · exact ncard_fixSet_le_of_param (fun _ hz => fixSet_h3_param hz)
    · exact ncard_fixSet_le_of_param (fun _ hz => fixSet_h4_param hz)
  exact (Set.ncard_le_ncard
    (fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw) (Set.toFinite _)).trans hbound

open CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE.CTTorus CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ncard_range_le_fixSet_of_family {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {ι : Type} (a : ι → Fin Tag.E8.rank → Lˣ)
    (ha : ∀ i j, a i j ^ 5 = 1) {w : WeylGroup .E8}
    (hw : w ∈ familyStabilizerSubgroup a) :
    (Set.range a).ncard ≤ (fixSet w).ncard := by
  classical
  let M := weylMatrix w
  let Fr : L →+* L := RingHom.id L
  let Z := {z : Fin Tag.E8.rank → ZMod 5 // (modMat 5 M)ᵀ *ᵥ z = z}
  let T := {b : fixedCharTuples M Fr // ∀ j, (b : Fin Tag.E8.rank → Lˣ) j ^ 5 = 1}
  have hcount : Nat.card T = Nat.card Z := by
    simpa only [Nat.cast_one, one_smul] using
      (natCard_fixedTorsion (L := L) M Fr (q := 1) (ℓ := 2) Nat.prime_two
        (fun _ => by simp [Fr]) Nat.prime_five (by decide))
  have : Nonempty Z := ⟨⟨0, by simp⟩⟩
  have : Finite T := Nat.finite_of_card_ne_zero (by
    rw [hcount]
    exact (Nat.card_pos (α := Z)).ne')
  let f : Set.range a → T := fun b =>
    ⟨⟨b.1, by
      obtain ⟨i, hi⟩ := b.2
      rw [← hi]
      apply mem_fixedCharTuples_iff.mpr
      intro v
      have hwi : w ∈ rootCharStabilizerSubgroup (a i) :=
        (Subgroup.mem_iInf.mp hw) i
      simpa [M, Fr, weylMatrix_mulVec] using hwi v⟩, by
      obtain ⟨i, hi⟩ := b.2
      intro j
      simpa only [← hi] using ha i j⟩
  have hf : Function.Injective f := by
    intro b c h
    exact Subtype.ext (congrArg (fun t : T => (t.1 : Fin Tag.E8.rank → Lˣ)) h)
  have hZ : Nat.card Z = (fixSet w).ncard := by
    have hiff : ∀ z : Fin Tag.E8.rank → ZMod 5,
        (modMat 5 M)ᵀ *ᵥ z = z ↔ w ∈ dualWeylStabilizer z := by
      intro z
      have he : (modMat 5 M)ᵀ = dualMatrix (ZMod 5) w := rfl
      rw [he]
      have hi : w⁻¹ ∈ dualWeylStabilizer z ↔ w ∈ dualWeylStabilizer z := by
        constructor
        · intro h; simpa only [inv_inv] using (dualWeylStabilizer z).inv_mem h
        · exact fun h => (dualWeylStabilizer z).inv_mem h
      simpa only [inv_inv] using
        (mem_dualWeylStabilizer_iff_dualMatrix (w := w⁻¹) (z := z)).symm.trans hi
    change Nat.card Z = Nat.card (fixSet w)
    exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
  calc (Set.range a).ncard = Nat.card (Set.range a) := rfl
    _ ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = Nat.card Z := hcount
    _ = (fixSet w).ncard := hZ



open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five in
theorem pow_five_eq_one_of_isPGroup {R : Subgroup (WeylGroup .E8)}
    (hR : IsPGroup 5 R) {w : WeylGroup .E8} (hw : w ∈ R) : w ^ 5 = 1 := by
  obtain ⟨g, hg⟩ := One.exists_conj_le_sylowW hR
  obtain ⟨i, j, hij⟩ := One.exists_exp_of_mem_sylowW (hg w hw)
  have hpow : (g * w * g⁻¹) ^ 5 = 1 := by
    rw [← hij]
    exact One.exp_pow_five i j
  rw [conj_pow] at hpow
  have he := congrArg (fun z => g⁻¹ * z * g) hpow
  simpa [mul_assoc] using he

set_option maxRecDepth 2048 in
theorem familyStabilizer_le_reflection_E8_five {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} [Finite ι]
    (a : ι → Fin Tag.E8.rank → Lˣ) (ha : ∀ i j, a i j ^ 5 = 1)
    (hcard : 25 < (Set.range a).ncard) :
    familyStabilizerSubgroup a ≤ familyReflectionGroup a := by
  refine familyStabilizer_le_reflection_of_prime_power Nat.prime_five ha ?_
  intro w hw e hwe
  have hP : IsPGroup 5 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, hwe])
  have hw5 := pow_five_eq_one_of_isPGroup hP (Subgroup.mem_zpowers w)
  by_cases hw1 : w = 1
  · rw [hw1]; exact one_mem _
  have hwo : orderOf w = 5 := orderOf_eq_prime hw5 hw1
  obtain ⟨g, i, j, heq, hij⟩ := exists_conj_into_P hwo
  have hmem : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) ∈
      fixReflectionGroup 5 (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) := by
    by_cases hi : i = 0
    · subst i
      simp only [Fin.val_zero, pow_zero, one_mul]
      have hj0 : j ≠ 0 := by simpa using hij
      have hjd : ¬ 5 ∣ (j : ℕ) := fun h => hj0 (Fin.ext
        (Nat.eq_zero_of_dvd_of_lt h j.isLt))
      obtain ⟨n, hn⟩ := exists_pow_eq_of_not_dvd e8FiveG2_pow hjd
      have hle := fixReflectionGroup_mono (p := 5)
        (show e8FiveG2 ∈ Subgroup.zpowers (e8FiveG2 ^ (j : ℕ)) from
          Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), by
            simpa only [zpow_natCast] using hn⟩)
      exact (fixReflectionGroup 5 (e8FiveG2 ^ (j : ℕ))).pow_mem
        (hle (e8FiveG2_mem_fixReflectionGroup 5)) _
    · by_cases hj : j = 0
      · subst j
        simp only [Fin.val_zero, pow_zero, mul_one]
        have hid : ¬ 5 ∣ (i : ℕ) := fun h => hi (Fin.ext
          (Nat.eq_zero_of_dvd_of_lt h i.isLt))
        obtain ⟨n, hn⟩ := exists_pow_eq_of_not_dvd e8FiveG1_pow hid
        have hle := fixReflectionGroup_mono (p := 5)
          (show e8FiveG1 ∈ Subgroup.zpowers (e8FiveG1 ^ (i : ℕ)) from
            Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), by
              simpa only [zpow_natCast] using hn⟩)
        exact (fixReflectionGroup 5 (e8FiveG1 ^ (i : ℕ))).pow_mem
          (hle (e8FiveG1_mem_fixReflectionGroup 5)) _
      · have hsmall := ncard_fixSet_e8Five_pow_mul_le i j hi hj
        have hlarge := ncard_range_le_fixSet_of_family a ha hw
        rw [← ncard_fixSet_conj g w, heq] at hlarge
        omega
  have hconj := conj_mem_fixReflectionGroup g⁻¹ hmem
  rw [← heq] at hconj
  have he : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w := by group
  rw [he] at hconj
  exact fixReflectionGroup_le_family Nat.prime_five ha hw hconj

theorem familyCentralizer_eq_familyGroup_E8_five {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} [Finite ι]
    (a : ι → Fin Tag.E8.rank → Lˣ) (ha : ∀ i j, a i j ^ 5 = 1)
    (hcard : 25 < (Set.range a).ncard) :
    familyCentralizer .E8 L a = familyGroup (K := L) a :=
  familyCentralizer_eq_familyGroup a
    (familyStabilizer_le_reflection_E8_five a ha hcard)

end CFSG.HardMathSupport.C14Lattice
