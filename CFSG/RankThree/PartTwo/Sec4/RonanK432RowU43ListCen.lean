module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Class

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] def u43CenOK (t : ℕ) : Bool :=
  (uGens.any fun g => !commutes4 (uAt t) g) || uAt t == one4 || uAt t == uAt uZ ||
    uAt t == sq4 (uAt uZ)

@[expose] def u43WitOK : Bool :=
  commutes4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) (uAt uZ) &&
    !(conjStep (wordPair [1, 1, 1]) (uAt uZ) == one4) &&
    !(conjStep (wordPair [1, 1, 1]) (uAt uZ) == uAt uZ) &&
    !(conjStep (wordPair [1, 1, 1]) (uAt uZ) == sq4 (uAt uZ))

@[noinline, expose] def u43Check : Bool :=
  (cube4 (uAt uZ) == one4) && u43WitOK && (List.range 729).all u43CenOK

theorem u43Check_true : u43Check = true := by decide +kernel

theorem u43Check_parts : cube4 (uAt uZ) = one4 ∧ u43WitOK = true ∧
    (List.range 729).all u43CenOK = true := by
  have h := u43Check_true
  simp only [u43Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem uZ_lt : uZ < 729 := by decide

theorem u43WitOK_parts (h : u43WitOK = true) :
    commutes4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) (uAt uZ) = true ∧
      conjStep (wordPair [1, 1, 1]) (uAt uZ) ≠ one4 ∧
      conjStep (wordPair [1, 1, 1]) (uAt uZ) ≠ uAt uZ ∧
      conjStep (wordPair [1, 1, 1]) (uAt uZ) ≠ sq4 (uAt uZ) := by
  unfold u43WitOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := h
  refine ⟨hA, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e] at hB; simp at hB
  · rw [e] at hC; simp at hC
  · rw [e] at hD; simp at hD

theorem commutes_uGens_of_central (hsyl : uSylCheck = true) {t : ℕ} {s : SUg}
    (hst : dec4 (uAt t) = toMat s) (hc : ∀ g ∈ sylS, g * s = s * g) :
    ∀ g ∈ uGens, commutes4 (uAt t) g = true := by
  intro g hg
  unfold uGens at hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
  have hw4 : ∀ l ∈ w, l < 4 := (uSylCheck_parts hsyl).2.2.2.2 w hw
  have hmem : wordElem w ∈ sylS := Subgroup.subset_closure ⟨w, hw, rfl⟩
  have hm := congrArg toMat (hc (wordElem w) hmem)
  have hg' : toMat (wordElem w) = dec4 (wordCode w) := by
    rw [toMat_apply]
    exact coe_wordElem w hw4
  rw [map_mul, map_mul, hg', ← hst, ← dec4_mul4, ← dec4_mul4] at hm
  have h2 := dec4_injective (canon4_mul4 _ _) (canon4_mul4 _ _) hm
  unfold commutes4
  exact beq_iff_eq.mpr h2.symm

theorem sAt_uZ_pow_three (hsyl : uSylCheck = true) : sAt uZ ^ 3 = 1 :=
  pow_three_of_cube4 hsyl uZ_lt u43Check_parts.1

theorem inv_eq_mul_self_of_pow_three (x : SUg) (h : x ^ 3 = 1) : x⁻¹ = x * x :=
  inv_eq_of_mul_eq_one_right ((pow_three x).symm.trans h)

theorem inv_sAt_uZ (hsyl : uSylCheck = true) : (sAt uZ)⁻¹ = sAt uZ * sAt uZ :=
  inv_eq_mul_self_of_pow_three (sAt uZ) (sAt_uZ_pow_three hsyl)

theorem centre_sylS (hsyl : uSylCheck = true) {s : SUg} (hs : s ∈ sylS)
    (hc : ∀ g ∈ sylS, g * s = s * g) : s = 1 ∨ s = sAt uZ ∨ s = (sAt uZ)⁻¹ := by
  obtain ⟨hz3, -, hall⟩ := u43Check_parts
  obtain ⟨t, ht, hst⟩ := exists_code_sylS hsyl hs
  have hgen := commutes_uGens_of_central hsyl hst hc
  have hok : u43CenOK t = true := List.all_eq_true.mp hall t (List.mem_range.mpr ht)
  unfold u43CenOK at hok
  have hany : (uGens.any fun g => !commutes4 (uAt t) g) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨g, hg, hg'⟩ := List.any_eq_true.mp h
    rw [hgen g hg] at hg'
    exact absurd hg' (by decide)
  rw [hany, Bool.false_or] at hok
  simp only [Bool.or_eq_true, beq_iff_eq] at hok
  rcases hok with (h1 | h2) | h3
  · left
    apply toMat_injective
    rw [map_one, ← hst, h1, dec4_one4]
  · right; left
    apply toMat_injective
    rw [← hst, h2, toMat_sAt hsyl uZ_lt]
  · right; right
    have hsq : s = sAt uZ * sAt uZ := by
      apply toMat_injective
      rw [map_mul, toMat_sAt hsyl uZ_lt, ← hst, h3, dec4_sq4]
    rw [hsq]
    exact (inv_sAt_uZ hsyl).symm

@[expose] noncomputable def u43X : SUg := wordElem [1, 1, 1] * sAt uZ * (wordElem [1, 1, 1])⁻¹

theorem toMat_u43X (hsyl : uSylCheck = true) :
    toMat u43X = dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) := by
  unfold u43X
  rw [dec4_conjStep [1, 1, 1] (by decide) (uAt uZ), map_mul, map_mul, toMat_sAt hsyl uZ_lt]
  rfl

theorem u43X_comm (hsyl : uSylCheck = true) : u43X * sAt uZ = sAt uZ * u43X := by
  have hc := (u43WitOK_parts u43Check_parts.2.1).1
  unfold commutes4 at hc
  apply toMat_injective
  rw [map_mul, map_mul, toMat_u43X hsyl, toMat_sAt hsyl uZ_lt, ← dec4_mul4, ← dec4_mul4]
  exact congrArg dec4 (beq_iff_eq.mp hc)

theorem u43X_ne_one (hsyl : uSylCheck = true) : u43X ≠ 1 := by
  have hne := (u43WitOK_parts u43Check_parts.2.1).2.1
  intro h
  apply hne
  have h1 : dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = dec4 one4 := by
    rw [← toMat_u43X hsyl, h, map_one, dec4_one4]
  exact dec4_injective (by unfold conjStep; exact canon4_mul4 _ _) canon4_one4 h1

theorem u43X_ne_z (hsyl : uSylCheck = true) : u43X ≠ sAt uZ := by
  have hne := (u43WitOK_parts u43Check_parts.2.1).2.2.1
  intro h
  apply hne
  have h1 : dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = dec4 (uAt uZ) := by
    rw [← toMat_u43X hsyl, h, toMat_sAt hsyl uZ_lt]
  exact dec4_injective (by unfold conjStep; exact canon4_mul4 _ _) (canon4_uAt hsyl uZ_lt) h1

theorem u43X_ne_inv (hsyl : uSylCheck = true) : u43X ≠ (sAt uZ)⁻¹ := by
  have hne := (u43WitOK_parts u43Check_parts.2.1).2.2.2
  intro h
  apply hne
  have h1 : dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = dec4 (sq4 (uAt uZ)) := by
    rw [← toMat_u43X hsyl, h, inv_sAt_uZ hsyl, map_mul, toMat_sAt hsyl uZ_lt, dec4_sq4]
  exact dec4_injective (by unfold conjStep; exact canon4_mul4 _ _)
    (by unfold sq4; exact canon4_mul4 _ _) h1

end CFSG.RankThree.PartTwo.Sec4.RonanK432
