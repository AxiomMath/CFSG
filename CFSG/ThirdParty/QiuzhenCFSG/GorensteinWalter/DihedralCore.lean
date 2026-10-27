module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral-group core for `DihedralGroup (2 ^ m)`

The normal-subgroup classification and centralizer computation used by the
Klein-four (`V₄`) case of Proposition 9 (Gorenstein--Walter 1965).  The
reusable helper lemmas here were extracted from
`GorensteinWalter.Classification.lean` (where they are private) and are
public in this module so that both `Classification.lean` and `GW1965.lean`
can import them.

The main facts:

* `normal_subgroup_dihedral_two_pow` — the full normal-subgroup lattice of
  `DihedralGroup (2 ^ m)` (rotation subgroups, `⊤`, and the index-two
  families `dihedralIndexTwoSubgroup m j`);
* `normal_noncyclic_subgroup_dihedral_two_pow` — the non-cyclic corollary;
* `centralizer_dihedralIndexTwo_v4` / `centralizer_dihedralIndexTwo_large` —
  the centralizers of the index-two families;
* `centralizer_le_of_normal_dihedral` — the `C_S(D) ≤ D` fact for a normal
  non-cyclic subgroup `D` of the dihedral 2-group;
* `centralizer_kleinFour_le_of_dihedral_mulEquiv` — every Klein-four subgroup
  of an abstract finite dihedral `2`-group is self-centralizing.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

-- (1) element case split
public lemma dihedralGroup_cases {n : ℕ} (x : DihedralGroup n) :
    (∃ i : ZMod n, x = DihedralGroup.r i) ∨ ∃ i : ZMod n, x = DihedralGroup.sr i := by
  cases hx : DihedralGroup.equivSum x with
  | inl i =>
      left
      refine ⟨i, ?_⟩
      have h1 : x = (DihedralGroup.equivSum.symm) (DihedralGroup.equivSum x) :=
        (DihedralGroup.equivSum.symm_apply_apply x).symm
      rw [hx] at h1
      simpa [DihedralGroup.equivSum] using h1
  | inr i =>
      right
      refine ⟨i, ?_⟩
      have h1 : x = (DihedralGroup.equivSum.symm) (DihedralGroup.equivSum x) :=
        (DihedralGroup.equivSum.symm_apply_apply x).symm
      rw [hx] at h1
      simpa [DihedralGroup.equivSum] using h1

-- (2) rotations lie in the rotation subgroup
public lemma r_mem_zpowers_r_one {n : ℕ} [NeZero n] (i : ZMod n) :
    DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  refine ⟨i.val, ?_⟩
  change (DihedralGroup.r 1 : DihedralGroup n) ^ i.val = DihedralGroup.r i
  rw [DihedralGroup.r_one_pow]
  congr 1
  exact ZMod.natCast_zmod_val i

-- (3) reflections are not rotations
public lemma sr_not_mem_zpowers_r_one {n : ℕ} (i : ZMod n) :
    DihedralGroup.sr i ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  intro h
  rcases (Subgroup.mem_zpowers_iff).mp h with ⟨k, hk⟩
  have hsr : DihedralGroup.sr i = DihedralGroup.r (k : ZMod n) := by
    rw [← hk, DihedralGroup.r_one_zpow]
  have h1 : DihedralGroup.sr i * (DihedralGroup.r (k : ZMod n))⁻¹ = 1 := by
    rw [hsr, mul_inv_cancel]
  have h2 : DihedralGroup.sr i * (DihedralGroup.r (k : ZMod n))⁻¹ = DihedralGroup.sr (i - (k : ZMod n)) := by
    rw [DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
    congr 1
    rw [sub_eq_add_neg]
  have h3 : DihedralGroup.sr (i - (k : ZMod n)) = 1 := by rw [← h2, h1]
  have hord : orderOf (DihedralGroup.sr (i - (k : ZMod n))) = 2 := DihedralGroup.orderOf_sr (i - (k : ZMod n))
  have hone : orderOf (1 : DihedralGroup n) = 1 := orderOf_one
  have : 2 = 1 := by rw [← hord, h3, hone]
  norm_num at this

-- (4) decomposition: H = (H ⊓ R) ∪ sr i₀ · (H ⊓ R)
public lemma mem_decomp {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m)))
    (i₀ : ZMod (2 ^ m)) (hsi : DihedralGroup.sr i₀ ∈ H)
    (x : DihedralGroup (2 ^ m)) :
    x ∈ H ↔ x ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1) ∨
      ∃ y ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1), x = DihedralGroup.sr i₀ * y := by
  constructor
  · intro hx
    rcases (dihedralGroup_cases x) with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      rw [hi]
      rw [hi] at hx
      exact Subgroup.mem_inf.mpr ⟨hx, r_mem_zpowers_r_one i⟩
    · right
      rw [hi]
      rw [hi] at hx
      refine ⟨DihedralGroup.r (i - i₀), ?mem, ?eq⟩
      · have h1 : DihedralGroup.r (i - i₀) ∈ H :=
          (DihedralGroup.sr_mul_sr i₀ i).symm ▸ Subgroup.mul_mem H hsi hx
        exact Subgroup.mem_inf.mpr ⟨h1, r_mem_zpowers_r_one (i - i₀)⟩
      · rw [DihedralGroup.sr_mul_r]
        congr 1
        rw [sub_eq_add_neg]
        abel
  · intro hx
    rcases hx with hx | ⟨y, hy, hyx⟩
    · exact hx.1
    · rw [hyx]
      exact Subgroup.mul_mem H hsi hy.1

-- (5) generator of H ⊓ R
public lemma generator_of_inf {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m))) :
    ∃ a : DihedralGroup (2 ^ m), a ∈ H ∧
      Subgroup.zpowers a = H ⊓ Subgroup.zpowers (DihedralGroup.r 1) := by
  let R : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (DihedralGroup.r 1)
  have hcyc : IsCyclic (↥(H ⊓ R)) := Subgroup.isCyclic_of_le inf_le_right
  rcases hcyc.exists_generator with ⟨g, hg⟩
  have hgtop : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => hg x⟩
  let a : DihedralGroup (2 ^ m) := (g : DihedralGroup (2 ^ m))
  refine ⟨a, ?_, ?_⟩
  · change (g : DihedralGroup (2 ^ m)) ∈ H
    exact g.2.1
  · have hmap : (Subgroup.zpowers g).map (H ⊓ R).subtype = Subgroup.zpowers a := by
      simp [a]
    have htop : (⊤ : Subgroup (↥(H ⊓ R))).map (H ⊓ R).subtype = H ⊓ R := by
      ext x
      constructor
      · intro hx
        rcases (Subgroup.mem_map).mp hx with ⟨y, hy, hyx⟩
        exact hyx ▸ y.2
      · intro hx
        exact (Subgroup.mem_map).mpr ⟨⟨x, hx⟩, trivial, rfl⟩
    calc
      Subgroup.zpowers a = (Subgroup.zpowers g).map (H ⊓ R).subtype := hmap.symm
      _ = (⊤ : Subgroup (↥(H ⊓ R))).map (H ⊓ R).subtype := by rw [hgtop]
      _ = H ⊓ R := htop

-- (6) elements of a size-1 intersection are trivial
public lemma mem_eq_one_of_card_one {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m)))
    (hcard1 : Nat.card (↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = 1)
    {z : DihedralGroup (2 ^ m)} (hz : z ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1)) : z = 1 := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let : Fintype (↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) := Fintype.ofFinite _
  have hc1 : Fintype.card (↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = 1 := by
    rwa [Nat.card_eq_fintype_card] at hcard1
  rcases (Fintype.card_eq_one_iff).mp hc1 with ⟨z₀, hz₀⟩
  have hz' : (⟨z, hz⟩ : ↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = z₀ := hz₀ ⟨z, hz⟩
  have h1' : (⟨1, Subgroup.one_mem _⟩ : ↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = z₀ := hz₀ ⟨1, Subgroup.one_mem _⟩
  have heq : (⟨z, hz⟩ : ↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = ⟨1, Subgroup.one_mem _⟩ := by
    rw [hz', h1']
  exact congrArg Subtype.val heq

/-- The rotation subgroup `⟨r (2 ^ k)⟩` of `DihedralGroup (2 ^ m)`. -/
public def dihedralRotationSubgroup (m k : ℕ) : Subgroup (DihedralGroup (2 ^ m)) :=
  Subgroup.zpowers (DihedralGroup.r (2 ^ k : ZMod (2 ^ m)))

/-- Exposed defining equation for the rotation subgroup. -/
public theorem dihedralRotationSubgroup_def (m k : ℕ) :
    dihedralRotationSubgroup m k =
      Subgroup.zpowers (DihedralGroup.r (2 ^ k : ZMod (2 ^ m))) := by
  rfl

/-- The index-two family `⟨r 2, sr j⟩` of `DihedralGroup (2 ^ m)`. -/
public def dihedralIndexTwoSubgroup (m : ℕ) (j : ZMod (2 ^ m)) : Subgroup (DihedralGroup (2 ^ m)) :=
  Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) ⊔
    Subgroup.zpowers (DihedralGroup.sr j)

-- ⟨r 2⟩ is normal in the dihedral group
private lemma zpowers_r_two_normal {m : ℕ} :
    (Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))).Normal := by
  let R : Subgroup (DihedralGroup (2 ^ m)) :=
    Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
  exact ⟨fun n hn g => by
    rcases (Subgroup.mem_zpowers_iff.mp hn) with ⟨k, hk⟩
    rcases (dihedralGroup_cases g) with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [hi, ← hk, DihedralGroup.r_zpow, DihedralGroup.r_mul_r, DihedralGroup.inv_r,
        DihedralGroup.r_mul_r]
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [DihedralGroup.r_zpow]
      congr 1
      ring_nf
    · rw [hi, ← hk, DihedralGroup.r_zpow, DihedralGroup.sr_mul_r, DihedralGroup.inv_sr,
        DihedralGroup.sr_mul_sr]
      refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      rw [DihedralGroup.r_zpow]
      congr 1
      rw [Int.cast_neg]
      ring⟩

/-- The normal form of the index-two family: rotations with even exponent and
the reflection coset of `sr j`. -/
public theorem mem_dihedralIndexTwoSubgroup_iff
    {m : ℕ} (_hm : 1 ≤ m) (j : ZMod (2 ^ m))
    (x : DihedralGroup (2 ^ m)) :
    x ∈ dihedralIndexTwoSubgroup m j ↔
      (∃ k : ℤ, x = DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) ∨
      (∃ k : ℤ, x = DihedralGroup.sr (j + (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let : (Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))).Normal := zpowers_r_two_normal
  constructor
  · intro hx
    rcases (Subgroup.mem_sup_of_normal_left (s := Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))
        (t := Subgroup.zpowers (DihedralGroup.sr j)) (x := x)).mp hx with ⟨a, ha, b, hb, habx⟩
    rcases (Subgroup.mem_zpowers_iff.mp ha) with ⟨k₁, hk₁⟩
    rcases (Subgroup.mem_zpowers_iff.mp hb) with ⟨k₂, hk₂⟩
    have hk2 : (DihedralGroup.sr j) ^ k₂ = (DihedralGroup.sr j) ^ (k₂ % 2 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, DihedralGroup.orderOf_sr]
      exact (Int.mod_modEq k₂ 2).symm
    rcases Int.emod_two_eq_zero_or_one k₂ with hk₂₀ | hk₂₁
    · -- b = 1 — x = a = (r 2)^k₁ = r (2 k₁)
      left
      refine ⟨k₁, ?_⟩
      calc
        x = a * b := habx.symm
        _ = (DihedralGroup.r (2 : ZMod (2 ^ m))) ^ k₁ * (DihedralGroup.sr j) ^ k₂ := by rw [← hk₁, ← hk₂]
        _ = (DihedralGroup.r (2 : ZMod (2 ^ m))) ^ k₁ * 1 := by
              rw [hk2, hk₂₀, zpow_zero]
        _ = DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k₁ : ZMod (2 ^ m))) := by
              rw [mul_one, DihedralGroup.r_zpow]
    · -- b = sr j — x = a * sr j = r (2 k₁) * sr j = sr (j - 2 k₁) = sr (j + 2 (-k₁))
      right
      refine ⟨-k₁, ?_⟩
      calc
        x = a * b := habx.symm
        _ = (DihedralGroup.r (2 : ZMod (2 ^ m))) ^ k₁ * (DihedralGroup.sr j) ^ k₂ := by rw [← hk₁, ← hk₂]
        _ = (DihedralGroup.r (2 : ZMod (2 ^ m))) ^ k₁ * DihedralGroup.sr j := by
              rw [hk2, hk₂₁, zpow_one]
        _ = DihedralGroup.sr (j - (2 : ZMod (2 ^ m)) * (k₁ : ZMod (2 ^ m))) := by
              rw [DihedralGroup.r_zpow, DihedralGroup.r_mul_sr]
        _ = DihedralGroup.sr (j + (2 : ZMod (2 ^ m)) * ((-k₁ : ℤ) : ZMod (2 ^ m))) := by
              apply congrArg DihedralGroup.sr
              rw [Int.cast_neg]
              ring
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · rw [hk]
      exact (le_sup_left : Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) ≤
          dihedralIndexTwoSubgroup m j)
        (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [DihedralGroup.r_zpow]⟩)
    · rw [hk]
      exact (Subgroup.mem_sup_of_normal_left (s := Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))
        (t := Subgroup.zpowers (DihedralGroup.sr j))).mpr
        ⟨DihedralGroup.r ((2 : ZMod (2 ^ m)) * (-(k : ZMod (2 ^ m)))),
          Subgroup.mem_zpowers_iff.mpr ⟨-k, by rw [DihedralGroup.r_zpow]; simp⟩,
          DihedralGroup.sr j, Subgroup.mem_zpowers (DihedralGroup.sr j), by
            rw [DihedralGroup.r_mul_sr]
            congr 1
            ring⟩

-- the normal subgroups of the dihedral 2-group not contained in the rotation
-- subgroup are `⊤` or one of the index-two families `dihedralIndexTwoSubgroup m j`
private lemma normal_dihedral_of_not_le_rotation {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDnormal : D.Normal)
    (hDR : ¬ D ≤ Subgroup.zpowers (DihedralGroup.r 1)) :
    D = ⊤ ∨ ∃ j : ZMod (2 ^ m), D = dihedralIndexTwoSubgroup m j := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let R : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (DihedralGroup.r 1)
  have hx : ∃ x : DihedralGroup (2 ^ m), x ∈ D ∧ x ∉ R := by
    by_contra h
    apply hDR
    intro x hxH
    by_cases hxR : x ∈ R
    · exact hxR
    · exact False.elim (h ⟨x, hxH, hxR⟩)
  rcases hx with ⟨x, hxH, hxR⟩
  rcases (dihedralGroup_cases x) with ⟨i₀, hi₀⟩ | ⟨i₀, hi₀⟩
  · rw [hi₀] at hxR
    exact False.elim (hxR (r_mem_zpowers_r_one i₀))
  · rw [hi₀] at hxH
    -- sr i₀ ∈ D — normality under r 1 gives sr (i₀ - 2) ∈ D
    have hsr2 : DihedralGroup.sr (i₀ - 2) ∈ D := by
      have hconj : DihedralGroup.r 1 * DihedralGroup.sr i₀ * (DihedralGroup.r 1)⁻¹ ∈ D :=
        hDnormal.conj_mem (n := DihedralGroup.sr i₀) hxH (g := DihedralGroup.r 1)
      convert hconj using 1
      rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
      congr 1
      ring
    -- sr i₀ * sr (i₀ - 2) = r (-2), hence r 2 ∈ D
    have hr2 : DihedralGroup.r (2 : ZMod (2 ^ m)) ∈ D := by
      have hprod : DihedralGroup.sr i₀ * DihedralGroup.sr (i₀ - 2) ∈ D :=
        Subgroup.mul_mem D hxH hsr2
      have hval : DihedralGroup.sr i₀ * DihedralGroup.sr (i₀ - 2) =
          DihedralGroup.r (-(2 : ZMod (2 ^ m))) := by
        rw [DihedralGroup.sr_mul_sr]
        congr 1
        abel
      have hval2 : DihedralGroup.r (2 : ZMod (2 ^ m)) =
          (DihedralGroup.r (-(2 : ZMod (2 ^ m))))⁻¹ := by
        rw [DihedralGroup.inv_r]
        congr 1
        abel
      rw [hval2]
      exact Subgroup.inv_mem D (hval ▸ hprod)
    -- A := D ⊓ R contains ⟨r 2⟩, is contained in R, and has a 2-power order
    let A : Subgroup (DihedralGroup (2 ^ m)) := D ⊓ R
    have hr2A : DihedralGroup.r (2 : ZMod (2 ^ m)) ∈ A :=
      Subgroup.mem_inf.mpr ⟨hr2, r_mem_zpowers_r_one 2⟩
    have hRcard : Nat.card (↥R) = 2 ^ m := by
      calc
        Nat.card (↥R) = Fintype.card (↥R) := Nat.card_eq_fintype_card
        _ = orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) := Fintype.card_zpowers (x := DihedralGroup.r 1)
        _ = 2 ^ m := DihedralGroup.orderOf_r_one
    have hAdvd : Nat.card (↥A) ∣ 2 ^ m := by
      have hle : Nat.card (↥A) ∣ Nat.card (↥R) := Subgroup.card_dvd_of_le inf_le_right
      rwa [hRcard] at hle
    have hR2card : Nat.card (↥(Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))) = 2 ^ (m - 1) := by
      have hord : orderOf (DihedralGroup.r (2 : ZMod (2 ^ m))) = 2 ^ (m - 1) := by
        rw [DihedralGroup.orderOf_r]
        have hval : (2 : ZMod (2 ^ m)).val = 2 % 2 ^ m := ZMod.val_natCast (2 ^ m) 2
        rw [hval]
        by_cases hm1 : m = 1
        · subst m
          norm_num
        · have hlt : 2 < 2 ^ m := by
            exact lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2)
              (pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (m := 2) (n := m) (by omega : 2 ≤ m))
          have hmod : 2 % 2 ^ m = 2 := Nat.mod_eq_of_lt hlt
          rw [hmod]
          have hgcd : Nat.gcd (2 ^ m) 2 = 2 := by
            rw [Nat.gcd_eq_right]
            exact pow_dvd_pow 2 (by omega : 1 ≤ m)
          have hdiv : 2 ^ m = 2 * 2 ^ (m - 1) := by
            calc
              2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
              _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
              _ = 2 * 2 ^ (m - 1) := by rw [mul_comm]
          rw [hgcd, hdiv, Nat.mul_div_right _ (by norm_num : 0 < 2)]
      calc
        Nat.card (↥(Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))) =
            Fintype.card (↥(Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))) := Nat.card_eq_fintype_card
        _ = orderOf (DihedralGroup.r (2 : ZMod (2 ^ m))) :=
              Fintype.card_zpowers (x := DihedralGroup.r (2 : ZMod (2 ^ m)))
        _ = 2 ^ (m - 1) := hord
    have hR2le : Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) ≤ A := by
      intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.zpowers_le).mpr hr2 hx,
        (Subgroup.zpowers_le).mpr (r_mem_zpowers_r_one 2) hx⟩
    have hAlow : 2 ^ (m - 1) ≤ Nat.card (↥A) := by
      have hle : Nat.card (↥(Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))) ≤ Nat.card (↥A) :=
        Subgroup.card_le_of_le hR2le
      rwa [hR2card] at hle
    -- |A| = 2^(m-1) or |A| = 2^m
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hAdvd with ⟨a, ha_le_m, hapow⟩
    have ha_cases : a = m - 1 ∨ a = m := by
      have hlowpow : 2 ^ (m - 1) ≤ 2 ^ a := by rwa [hapow] at hAlow
      have hmla : m - 1 ≤ a :=
        (pow_le_pow_iff_right₀ (by norm_num : 1 < 2) (n := m - 1) (m := a)).mp hlowpow
      omega
    rcases ha_cases with ham1 | ham
    · -- |A| = 2^(m-1): A = ⟨r 2⟩ and D = dihedralIndexTwoSubgroup m i₀
      have hAeq : A = Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) := by
        symm
        apply Subgroup.eq_of_le_of_card_ge
        · exact hR2le
        · rw [hapow, hR2card, ham1]
      right
      refine ⟨i₀, ?_⟩
      apply le_antisymm
      · intro x hx
        rcases (mem_decomp D i₀ hxH x).mp hx with h1 | ⟨y, hy, hyx⟩
        · rw [mem_dihedralIndexTwoSubgroup_iff hm i₀ x]
          left
          change x ∈ A at h1
          rw [hAeq] at h1
          rcases (Subgroup.mem_zpowers_iff.mp h1) with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          rw [← hk, DihedralGroup.r_zpow]
        · rw [hyx]
          rw [mem_dihedralIndexTwoSubgroup_iff hm i₀ (DihedralGroup.sr i₀ * y)]
          right
          change y ∈ A at hy
          rw [hAeq] at hy
          rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          calc
            DihedralGroup.sr i₀ * y = DihedralGroup.sr i₀ *
                (DihedralGroup.r (2 : ZMod (2 ^ m))) ^ k := by rw [← hk]
            _ = DihedralGroup.sr (i₀ + (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) := by
                  rw [DihedralGroup.r_zpow, DihedralGroup.sr_mul_r]
      · intro x hx
        rw [mem_dihedralIndexTwoSubgroup_iff hm i₀ x] at hx
        rcases hx with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk]
          exact (Subgroup.zpowers_le).mpr hr2
            (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [DihedralGroup.r_zpow]⟩)
        · rw [hk]
          exact (mem_decomp D i₀ hxH
            (DihedralGroup.sr (i₀ + (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))))).mpr (Or.inr
              ⟨DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))),
                by
                  exact Subgroup.mem_inf.mpr
                    ⟨(Subgroup.zpowers_le).mpr hr2
                      (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [DihedralGroup.r_zpow]⟩),
                      r_mem_zpowers_r_one (2 * (k : ZMod (2 ^ m)))⟩,
                by
                  rw [DihedralGroup.sr_mul_r]⟩)
    · -- |A| = 2^m: A = R and D = ⊤
      have hAeq : A = R := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact inf_le_right
        · rw [hRcard, hapow, ham]
      left
      apply le_antisymm
      · intro x hx
        trivial
      · intro x hx
        rcases (dihedralGroup_cases x) with ⟨i, hi⟩ | ⟨i, hi⟩
        · rw [hi]
          exact (inf_le_left : A ≤ D) (le_of_eq hAeq.symm (r_mem_zpowers_r_one i))
        · rw [hi]
          exact (mem_decomp D i₀ hxH (DihedralGroup.sr i)).mpr (Or.inr
            ⟨DihedralGroup.r (i - i₀),
              by
                exact Subgroup.mem_inf.mpr
                  ⟨(inf_le_left : A ≤ D) (le_of_eq hAeq.symm (r_mem_zpowers_r_one (i - i₀))),
                    r_mem_zpowers_r_one (i - i₀)⟩,
              by
                rw [DihedralGroup.sr_mul_r]
                congr 1
                abel⟩)

/-- The non-cyclic normal subgroups of the dihedral 2-group: `⊤` or one of the
index-two families. -/
public theorem normal_noncyclic_subgroup_dihedral_two_pow
    {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDnormal : D.Normal)
    (hDnc : ¬ IsCyclic D) :
    D = ⊤ ∨ ∃ j : ZMod (2 ^ m), D = dihedralIndexTwoSubgroup m j := by
  by_cases hDR : D ≤ Subgroup.zpowers (DihedralGroup.r 1)
  · exact False.elim (hDnc (Subgroup.isCyclic_of_le hDR))
  · exact normal_dihedral_of_not_le_rotation hm D hDnormal hDR

-- the cyclic case: a subgroup of the rotation subgroup `⟨r 1⟩` is one of the
-- rotation subgroups `⟨r (2 ^ a)⟩` (a ≤ m), via
-- `gcd (2^m) n' = 2^a`, `n' = 2^a · u`, and the modular inverse
-- `u · b ≡ 1 [MOD 2^(m-a)]` lifted to `n' · b ≡ 2^a [MOD 2^m]`
public theorem le_zpowers_r_one_eq_dihedralRotationSubgroup {m : ℕ} (_hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDR : D ≤ Subgroup.zpowers (DihedralGroup.r 1)) :
    ∃ k : ℕ, k ≤ m ∧ D = dihedralRotationSubgroup m k := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  -- D ≤ ⟨r 1⟩ and ⟨r 1⟩ is cyclic, so D = ⟨(r 1)^n⟩ = ⟨r (n : ZMod (2^m))⟩
  rcases (Subgroup.le_zpowers_iff (DihedralGroup.r 1) D).mp hDR with ⟨n, hn⟩
  let n' : ℕ := (n : ZMod (2 ^ m)).val
  have hnZ : (n' : ZMod (2 ^ m)) = (n : ZMod (2 ^ m)) :=
    ZMod.natCast_zmod_val (n : ZMod (2 ^ m))
  have hDgen : D = Subgroup.zpowers (DihedralGroup.r (n' : ZMod (2 ^ m))) := by
    rw [hn]
    congr 1
    rw [DihedralGroup.r_one_pow]
    congr 1
    exact hnZ.symm
  -- the gcd is a power of two: gcd (2^m) n' = 2^a with a ≤ m
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ m) n') with ⟨a, ha_le_m, hapow⟩
  -- write n' = 2^a · u
  have hgd : Nat.gcd (2 ^ m) n' ∣ n' := Nat.gcd_dvd_right (2 ^ m) n'
  have hdivA : 2 ^ a ∣ n' := by
    rwa [hapow] at hgd
  let u : ℕ := n' / 2 ^ a
  have hn' : n' = 2 ^ a * u := by
    change n' = 2 ^ a * (n' / 2 ^ a)
    exact (Nat.mul_div_cancel' hdivA).symm
  -- u is coprime to 2^(m-a)
  have hgcd2 : Nat.gcd (2 ^ (m - a)) u = 1 := by
    have h1 : Nat.gcd (2 ^ m) (2 ^ a * u) = 2 ^ a := by
      rwa [← hn']
    have hpow : 2 ^ m = 2 ^ a * 2 ^ (m - a) := by
      calc
        2 ^ m = 2 ^ (a + (m - a)) := by congr 1; omega
        _ = 2 ^ a * 2 ^ (m - a) := by rw [pow_add]
    have h2 : 2 ^ a * Nat.gcd (2 ^ (m - a)) u = 2 ^ a := by
      rw [hpow] at h1
      rw [Nat.gcd_mul_left] at h1
      exact h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) a)
      (by simpa [mul_one] using h2)
  -- modular inverse b of u modulo 2^(m-a)
  have hc : Nat.Coprime u (2 ^ (m - a)) := by
    change Nat.gcd u (2 ^ (m - a)) = 1
    rwa [Nat.gcd_comm]
  let b : ℕ := (u⁻¹ : ZMod (2 ^ (m - a))).val
  have hb : (u * b : ZMod (2 ^ (m - a))) = 1 := by
    simpa [b] using (ZMod.mul_val_inv hc)
  have hmod : u * b ≡ 1 [MOD 2 ^ (m - a)] :=
    (ZMod.natCast_eq_natCast_iff (u * b) 1 (2 ^ (m - a))).mp
      (by simpa [Nat.cast_mul] using hb)
  -- lift the congruence to modulus 2^m
  have hmod2 : n' * b ≡ 2 ^ a [MOD 2 ^ m] := by
    have h1 : 2 ^ a * (u * b) ≡ 2 ^ a * 1 [MOD 2 ^ a * 2 ^ (m - a)] :=
      Nat.ModEq.mul_left' (2 ^ a) hmod
    have hpow : 2 ^ a * 2 ^ (m - a) = 2 ^ m := by
      calc
        2 ^ a * 2 ^ (m - a) = 2 ^ (a + (m - a)) := by rw [pow_add]
        _ = 2 ^ m := by congr 1; omega
    have hnm : 2 ^ a * (u * b) = n' * b := by
      rw [hn']
      ring
    rwa [hnm, mul_one, hpow] at h1
  have hcast : ((n' * b : ℕ) : ZMod (2 ^ m)) = ((2 ^ a : ℕ) : ZMod (2 ^ m)) :=
    (ZMod.natCast_eq_natCast_iff (n' * b) (2 ^ a) (2 ^ m)).mpr hmod2
  -- r (2^a) = (r n')^b, so ⟨r (2^a)⟩ ≤ ⟨r n'⟩
  have hr2a_mem : DihedralGroup.r ((2 ^ a : ℕ) : ZMod (2 ^ m)) ∈
      Subgroup.zpowers (DihedralGroup.r (n' : ZMod (2 ^ m))) := by
    rw [show DihedralGroup.r ((2 ^ a : ℕ) : ZMod (2 ^ m)) =
        (DihedralGroup.r (n' : ZMod (2 ^ m))) ^ b by
          rw [DihedralGroup.r_pow, ← Nat.cast_mul, hcast]]
    simpa using Subgroup.zpow_mem_zpowers (DihedralGroup.r (n' : ZMod (2 ^ m))) (b : ℤ)
  -- and the converse: r n' = (r (2^a))^u
  have hmem1 : DihedralGroup.r (n' : ZMod (2 ^ m)) ∈
      Subgroup.zpowers (DihedralGroup.r ((2 ^ a : ℕ) : ZMod (2 ^ m))) := by
    rw [show DihedralGroup.r (n' : ZMod (2 ^ m)) =
        (DihedralGroup.r ((2 ^ a : ℕ) : ZMod (2 ^ m))) ^ u by
          rw [DihedralGroup.r_pow, ← Nat.cast_mul, ← hn']]
    simpa using Subgroup.zpow_mem_zpowers (DihedralGroup.r ((2 ^ a : ℕ) : ZMod (2 ^ m))) (u : ℤ)
  have hD : D = Subgroup.zpowers (DihedralGroup.r (2 ^ a : ZMod (2 ^ m))) := by
    rw [hDgen]
    apply le_antisymm
    · simpa using (Subgroup.zpowers_le).mpr hmem1
    · simpa using (Subgroup.zpowers_le).mpr hr2a_mem
  refine ⟨a, ha_le_m, ?_⟩
  simpa [dihedralRotationSubgroup] using hD

/-- The normal subgroups of the dihedral 2-group `DihedralGroup (2 ^ m)`: one of
the rotation subgroups `⟨r (2 ^ k)⟩` (`k ≤ m`), the whole group, or one of the
index-two families `dihedralIndexTwoSubgroup m j`. -/
public theorem normal_subgroup_dihedral_two_pow
    {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDnormal : D.Normal) :
    (∃ k : ℕ, k ≤ m ∧ D = dihedralRotationSubgroup m k) ∨
      D = ⊤ ∨ ∃ j : ZMod (2 ^ m), D = dihedralIndexTwoSubgroup m j := by
  by_cases hDR : D ≤ Subgroup.zpowers (DihedralGroup.r 1)
  · left
    exact le_zpowers_r_one_eq_dihedralRotationSubgroup hm D hDR
  · right
    exact normal_dihedral_of_not_le_rotation hm D hDnormal hDR

/-- The solutions of `2 · i = 0` in `ZMod (2 ^ m)` (for `2 ≤ m`): `0` and the
central involution `2^(m-1)`. -/
public lemma zmod_two_mul_eq_zero_iff
    {m : ℕ} (hm : 2 ≤ m) (i : ZMod (2 ^ m)) :
    (2 : ZMod (2 ^ m)) * i = 0 ↔ i = 0 ∨ i = (2 ^ (m - 1) : ZMod (2 ^ m)) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  constructor
  · intro h
    let v : ℕ := i.val
    have hi : i = (v : ZMod (2 ^ m)) := by
      change i = (i.val : ZMod (2 ^ m))
      exact (ZMod.natCast_zmod_val i).symm
    have h2 : (2 : ZMod (2 ^ m)) * (v : ZMod (2 ^ m)) = 0 := by
      simpa [hi] using h
    have h4 : ((2 * v : ℕ) : ZMod (2 ^ m)) = 0 := by
      simpa [Nat.cast_mul] using h2
    have hdvd : 2 ^ m ∣ 2 * v := (ZMod.natCast_eq_zero_iff (2 * v) (2 ^ m)).mp h4
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      calc
        2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
        _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (m - 1) := by rw [mul_comm]
    have hdvd' : 2 ^ (m - 1) ∣ v := by
      rw [hpow] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
    rcases hdvd' with ⟨k, hk⟩
    have hvlt : v < 2 ^ m := ZMod.val_lt i
    have hklt : k < 2 := by
      rw [hk, hpow] at hvlt
      have hlt' : 2 ^ (m - 1) * k < 2 ^ (m - 1) * 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hvlt
      exact (Nat.mul_lt_mul_left (pow_pos (by norm_num : 0 < 2) (m - 1))).mp hlt'
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · left
      rw [hi, hk, hk0, mul_zero]
      simp
    · right
      rw [hi, hk, hk1, mul_one]
      simp
  · rintro (hi | hi)
    · rw [hi]
      simp
    · rw [hi]
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        calc
          2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
          _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (m - 1) := by rw [mul_comm]
      have hcast : (2 : ZMod (2 ^ m)) * (2 ^ (m - 1) : ZMod (2 ^ m)) =
          ((2 * 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [show (2 ^ (m - 1) : ZMod (2 ^ m)) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) by simp]
        rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num]
        rw [← Nat.cast_mul]
      rw [hcast, ← hpow]
      exact ZMod.natCast_self (2 ^ m)

/-- The centralizer of the index-two family in the ambient D₈ (`m = 2`) is the
subgroup itself (a Klein four group). -/
public theorem centralizer_dihedralIndexTwo_v4
    (j : ZMod 4) :
    Subgroup.centralizer (dihedralIndexTwoSubgroup 2 j : Set (DihedralGroup 4)) =
      dihedralIndexTwoSubgroup 2 j := by
  apply le_antisymm
  · intro x hx
    rcases (dihedralGroup_cases x) with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- x = r i: commutation with sr j gives 2i = 0
      have hc_srj : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
        (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.sr j)
          ((le_sup_right : Subgroup.zpowers (DihedralGroup.sr j) ≤
            dihedralIndexTwoSubgroup 2 j) (Subgroup.mem_zpowers (DihedralGroup.sr j)))
      have hieq : j - i = j + i := by
        simpa [hi, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] using hc_srj.symm
      have htwo : (2 : ZMod 4) * i = 0 := by
        have hz := congrArg (fun z : ZMod 4 => z - j) hieq
        have hneg : -i = i := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
        calc
          (2 : ZMod 4) * i = i + i := by rw [two_mul]
          _ = i + -i := congrArg (fun z : ZMod 4 => i + z) hneg.symm
          _ = 0 := by simp
      rcases (zmod_two_mul_eq_zero_iff (m := 2) (by norm_num : 2 ≤ 2) i).mp htwo with hi0 | hi2
      · rw [hi, hi0, DihedralGroup.r_zero]
        exact Subgroup.one_mem _
      · rw [hi, hi2]
        simpa [dihedralIndexTwoSubgroup] using ((le_sup_left : Subgroup.zpowers (DihedralGroup.r (2 : ZMod 4)) ≤
            dihedralIndexTwoSubgroup 2 j) (Subgroup.mem_zpowers (DihedralGroup.r (2 : ZMod 4))))
    · -- x = sr i: commutation with sr j gives i = j or i = j + 2
      have hc_srj : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
        (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.sr j)
          ((le_sup_right : Subgroup.zpowers (DihedralGroup.sr j) ≤
            dihedralIndexTwoSubgroup 2 j) (Subgroup.mem_zpowers (DihedralGroup.sr j)))
      have hieq : j - i = i - j := by
        simpa [hi, DihedralGroup.sr_mul_sr] using hc_srj.symm
      have htwo : (2 : ZMod 4) * (j - i) = 0 := by
        rw [two_mul]
        calc
          (j - i) + (j - i) = (j - i) + (i - j) := by rw [hieq]
          _ = 0 := by abel
      rcases (zmod_two_mul_eq_zero_iff (m := 2) (by norm_num : 2 ≤ 2) (j - i)).mp htwo with hji0 | hji2
      · -- i = j
        have hi' : i = j := (sub_eq_zero.mp hji0).symm
        rw [hi, hi']
        exact (le_sup_right : Subgroup.zpowers (DihedralGroup.sr j) ≤
            dihedralIndexTwoSubgroup 2 j) (Subgroup.mem_zpowers (DihedralGroup.sr j))
      · -- i = j + 2
        have hji2' : j = i + 2 := by
          have h1 : j = (2 : ZMod 4) + i := sub_eq_iff_eq_add.mp hji2
          rwa [add_comm] at h1
        have hsub : j - 2 = i := by
          have h2 := congrArg (fun z : ZMod 4 => z - 2) hji2'
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
        have hi' : i = j + 2 := by
          calc
            i = j - 2 := hsub.symm
            _ = j + 2 := by
              rw [sub_eq_add_neg, show -(2 : ZMod 4) = 2 by
                have h4 : (2 : ZMod 4) + 2 = 0 := by
                  norm_num
                  exact ZMod.natCast_self 4
                exact neg_eq_iff_add_eq_zero.mpr h4]
        rw [hi, hi']
        exact (mem_dihedralIndexTwoSubgroup_iff (by norm_num : 1 ≤ 2) j (DihedralGroup.sr (j + 2))).mpr
          (Or.inr ⟨1, by simp⟩)
  · -- D ≤ C(D): the two generators centralize the generating set
    have h_r2_srj : DihedralGroup.r (2 : ZMod 4) * DihedralGroup.sr j =
        DihedralGroup.sr j * DihedralGroup.r (2 : ZMod 4) := by
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      apply congrArg DihedralGroup.sr
      rw [sub_eq_add_neg, show -(2 : ZMod 4) = 2 by
        have h4 : (2 : ZMod 4) + 2 = 0 := by
          norm_num
          exact ZMod.natCast_self 4
        exact neg_eq_iff_add_eq_zero.mpr h4]
    have hDclosure : dihedralIndexTwoSubgroup 2 j =
        Subgroup.closure ({DihedralGroup.r (2 : ZMod 4), DihedralGroup.sr j} : Set (DihedralGroup 4)) := by
      rw [dihedralIndexTwoSubgroup]
      calc
        Subgroup.zpowers (DihedralGroup.r (2 : ZMod 4)) ⊔
            Subgroup.zpowers (DihedralGroup.sr j)
            = Subgroup.closure {DihedralGroup.r (2 : ZMod 4)} ⊔
                Subgroup.closure {DihedralGroup.sr j} := by
              rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
        _ = Subgroup.closure ({DihedralGroup.r (2 : ZMod 4)} ∪ {DihedralGroup.sr j}) := by
              rw [Subgroup.closure_union]
        _ = Subgroup.closure ({DihedralGroup.r (2 : ZMod 4), DihedralGroup.sr j} : Set (DihedralGroup 4)) := by
              congr 1
    rw [hDclosure, Subgroup.centralizer_closure]
    rw [Subgroup.closure_le]
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · exact Subgroup.mem_centralizer_iff.mpr (by
        intro y hy
        rcases (Set.mem_insert_iff.mp hy) with rfl | hy
        · rfl
        · rw [Set.mem_singleton_iff.mp hy]
          exact h_r2_srj.symm)
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_centralizer_iff.mpr (by
        intro y hy
        rcases (Set.mem_insert_iff.mp hy) with rfl | hy
        · exact h_r2_srj
        · simp [Set.mem_singleton_iff.mp hy])

/-- The centralizer of the index-two family in `DihedralGroup (2 ^ m)` for
`3 ≤ m` is the subgroup generated by the central involution `r (2^(m-1))`. -/
public theorem centralizer_dihedralIndexTwo_large
    {m : ℕ} (hm : 3 ≤ m) (j : ZMod (2 ^ m)) :
    Subgroup.centralizer (dihedralIndexTwoSubgroup m j : Set (DihedralGroup (2 ^ m))) =
      Subgroup.zpowers (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) := by
  apply le_antisymm
  · intro x hx
    have hc_r2 : DihedralGroup.r (2 : ZMod (2 ^ m)) * x = x * DihedralGroup.r (2 : ZMod (2 ^ m)) :=
      (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.r (2 : ZMod (2 ^ m)))
        ((le_sup_left : Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) ≤
          dihedralIndexTwoSubgroup m j) (Subgroup.mem_zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))))
    have hc_srj : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
      (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.sr j)
        ((le_sup_right : Subgroup.zpowers (DihedralGroup.sr j) ≤
          dihedralIndexTwoSubgroup m j) (Subgroup.mem_zpowers (DihedralGroup.sr j)))
    rcases (dihedralGroup_cases x) with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- x = r i: commutation with sr j gives 2i = 0
      have hieq : j - i = j + i := by
        simpa [hi, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] using hc_srj.symm
      have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
        have hz := congrArg (fun z : ZMod (2 ^ m) => z - j) hieq
        have hneg : -i = i := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
        calc
          (2 : ZMod (2 ^ m)) * i = i + i := by rw [two_mul]
          _ = i + -i := congrArg (fun z : ZMod (2 ^ m) => i + z) hneg.symm
          _ = 0 := by simp
      rcases (zmod_two_mul_eq_zero_iff (by omega : 2 ≤ m) i).mp htwo with hi0 | hi2
      · rw [hi, hi0, DihedralGroup.r_zero]
        exact Subgroup.one_mem _
      · rw [hi, hi2]
        exact Subgroup.mem_zpowers (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))
    · -- x = sr i: impossible, since commutation with r 2 gives 4 = 0
      have hieq : i + 2 = i - 2 := by
        simpa [hi, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] using hc_r2.symm
      have h2 : (2 : ZMod (2 ^ m)) = -(2 : ZMod (2 ^ m)) := by
        have hz := congrArg (fun z : ZMod (2 ^ m) => z - i) hieq
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
      have h4 : (4 : ZMod (2 ^ m)) = 0 := by
        calc
          (4 : ZMod (2 ^ m)) = (2 : ZMod (2 ^ m)) + 2 := by norm_num
          _ = (2 : ZMod (2 ^ m)) + -(2 : ZMod (2 ^ m)) :=
                congrArg (fun z : ZMod (2 ^ m) => (2 : ZMod (2 ^ m)) + z) h2
          _ = 0 := by simp
      have h4dvd : 2 ^ m ∣ 4 := (ZMod.natCast_eq_zero_iff 4 (2 ^ m)).mp h4
      have hle : 2 ^ m ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) h4dvd
      have hge : 8 ≤ 2 ^ m := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega : 3 ≤ m)
      omega
  · -- ⟨r (2^(m-1))⟩ ≤ C(D): the central involution commutes with both generators
    have hxsj : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) * DihedralGroup.sr j =
        DihedralGroup.sr j * DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := by
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      apply congrArg DihedralGroup.sr
      have hz : (2 : ZMod (2 ^ m)) * (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 :=
        (zmod_two_mul_eq_zero_iff (by omega : 2 ≤ m) (2 ^ (m - 1) : ZMod (2 ^ m))).mpr (Or.inr rfl)
      have hxadd : (2 ^ (m - 1) : ZMod (2 ^ m)) + (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
        simpa [two_mul] using hz
      have hxneg : -(2 ^ (m - 1) : ZMod (2 ^ m)) = (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        calc
          -(2 ^ (m - 1) : ZMod (2 ^ m))
              = -(2 ^ (m - 1) : ZMod (2 ^ m)) + 0 := by rw [add_zero]
          _ = -(2 ^ (m - 1) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ZMod (2 ^ m)) + (2 ^ (m - 1) : ZMod (2 ^ m))) := by rw [← hxadd]
          _ = (2 ^ (m - 1) : ZMod (2 ^ m)) := by abel
      calc
        j - (2 ^ (m - 1) : ZMod (2 ^ m)) = j + -(2 ^ (m - 1) : ZMod (2 ^ m)) := by rw [sub_eq_add_neg]
        _ = j + (2 ^ (m - 1) : ZMod (2 ^ m)) := by rw [hxneg]
    have hgen : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈
        Subgroup.centralizer ({DihedralGroup.r (2 : ZMod (2 ^ m)), DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases (Set.mem_insert_iff.mp hy) with rfl | hy
      · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
      · rw [Set.mem_singleton_iff.mp hy]
        exact hxsj.symm
    have hDclosure : dihedralIndexTwoSubgroup m j =
        Subgroup.closure ({DihedralGroup.r (2 : ZMod (2 ^ m)), DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))) := by
      rw [dihedralIndexTwoSubgroup]
      calc
        Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) ⊔
            Subgroup.zpowers (DihedralGroup.sr j)
            = Subgroup.closure {DihedralGroup.r (2 : ZMod (2 ^ m))} ⊔
                Subgroup.closure {DihedralGroup.sr j} := by
              rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
        _ = Subgroup.closure ({DihedralGroup.r (2 : ZMod (2 ^ m))} ∪ {DihedralGroup.sr j}) := by
              rw [Subgroup.closure_union]
        _ = Subgroup.closure ({DihedralGroup.r (2 : ZMod (2 ^ m)), DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))) := by
              congr 1
    rw [hDclosure, Subgroup.centralizer_closure]
    exact (Subgroup.zpowers_le).mpr hgen

/-- For a normal non-cyclic subgroup `D` of the dihedral 2-group, the centralizer
of `D` in the ambient group is contained in `D`. -/
public theorem centralizer_le_of_normal_dihedral
    {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDnormal : D.Normal)
    (hDnc : ¬ IsCyclic D) :
    Subgroup.centralizer (D : Set (DihedralGroup (2 ^ m))) ≤ D := by
  rcases (normal_noncyclic_subgroup_dihedral_two_pow hm D hDnormal hDnc) with hDtop | ⟨j, hDj⟩
  · rw [hDtop]
    intro x hx
    trivial
  · by_cases hm2 : m = 2
    · subst m
      rw [hDj]
      intro x hx
      rw [centralizer_dihedralIndexTwo_v4 j] at hx
      exact hx
    · by_cases hm1 : m = 1
      · -- m = 1: the index-two family is cyclic, contradicting hDnc
        exfalso
        subst m
        rw [hDj] at hDnc
        apply hDnc
        rw [show dihedralIndexTwoSubgroup 1 j = Subgroup.zpowers (DihedralGroup.sr j) by
          rw [dihedralIndexTwoSubgroup]
          have h2zero : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
          rw [h2zero, DihedralGroup.r_zero]
          simp]
        infer_instance
      · have hm3 : 3 ≤ m := by omega
        rw [hDj]
        rw [centralizer_dihedralIndexTwo_large hm3 j]
        have hr2m1_mem : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈
            dihedralIndexTwoSubgroup m j := by
          rw [mem_dihedralIndexTwoSubgroup_iff hm j (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))]
          left
          refine ⟨2 ^ (m - 2), ?_⟩
          apply congrArg DihedralGroup.r
          have h2 : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
            calc
              2 * 2 ^ (m - 2) = 2 ^ (1 + (m - 2)) := by rw [pow_add]; simp
              _ = 2 ^ (m - 1) := by congr 1; omega
          rw [show (2 ^ (m - 1) : ZMod (2 ^ m)) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) by simp]
          rw [show ((2 ^ (m - 2) : ℤ) : ZMod (2 ^ m)) = ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) by simp]
          rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num]
          rw [← Nat.cast_mul]
          congr 1
          exact h2.symm
        intro x hx
        exact (Subgroup.zpowers_le).mpr hr2m1_mem hx

/-- Every Klein-four subgroup of a finite dihedral `2`-group contains the
central rotation involution and is self-centralizing. -/
public theorem centralizer_kleinFour_le_dihedral
    {m : ℕ} (hm : 1 ≤ m)
    (V : Subgroup (DihedralGroup (2 ^ m))) (hV : IsKleinFour V) :
    Subgroup.centralizer (V : Set (DihedralGroup (2 ^ m))) ≤ V := by
  classical
  let : IsKleinFour V := hV
  by_cases hm1 : m = 1
  · subst m
    have hVtop : V = ⊤ := by
      apply Subgroup.eq_top_of_card_eq V
      rw [IsKleinFour.card_four, DihedralGroup.nat_card]
      norm_num
    rw [hVtop]
    intro x _hx
    trivial
  have hm2 : 2 ≤ m := by omega
  let R : Subgroup (DihedralGroup (2 ^ m)) :=
    Subgroup.zpowers (DihedralGroup.r 1)
  have hVnc : ¬ IsCyclic V := IsKleinFour.not_isCyclic
  have hVnotR : ¬ V ≤ R := by
    intro hle
    apply hVnc
    exact Subgroup.isCyclic_of_le hle
  obtain ⟨t, htV, htR⟩ := SetLike.not_le_iff_exists.mp hVnotR
  obtain ⟨j, hjV⟩ : ∃ j : ZMod (2 ^ m), DihedralGroup.sr j ∈ V := by
    rcases dihedralGroup_cases t with ⟨i, hi⟩ | ⟨i, hi⟩
    · exfalso
      apply htR
      rw [hi]
      exact r_mem_zpowers_r_one i
    · exact ⟨i, hi ▸ htV⟩
  let : Finite V := Nat.finite_of_card_ne_zero (by
    rw [IsKleinFour.card_four]
    norm_num)
  let : Fintype V := Fintype.ofFinite V
  let tV : V := ⟨DihedralGroup.sr j, hjV⟩
  have hthree : 3 ≤ ENat.card V := by
    rw [ENat.card_eq_coe_fintype_card, IsKleinFour.card_four']
    norm_num
  obtain ⟨w, hw1, hwt⟩ :=
    ENat.exists_ne_ne_of_three_le hthree (1 : V) tV
  have rotation_index_eq_half
      (i : ZMod (2 ^ m))
      (hsq : DihedralGroup.r i * DihedralGroup.r i = 1)
      (hne : DihedralGroup.r i ≠ 1) :
      i = (2 ^ (m - 1) : ZMod (2 ^ m)) := by
    have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
      have hri : DihedralGroup.r (i + i) = DihedralGroup.r 0 := by
        simpa only [DihedralGroup.r_mul_r, DihedralGroup.one_def] using hsq
      injection hri with hii
      simpa only [two_mul] using hii
    rcases (zmod_two_mul_eq_zero_iff hm2 i).mp htwo with hi0 | hihalf
    · exfalso
      apply hne
      rw [hi0, DihedralGroup.r_zero]
    · exact hihalf
  have hzV :
      DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈ V := by
    rcases dihedralGroup_cases (w : DihedralGroup (2 ^ m)) with
      ⟨i, hi⟩ | ⟨i, hi⟩
    · have hsq : DihedralGroup.r i * DihedralGroup.r i = 1 := by
        have hwself := congrArg Subtype.val (IsKleinFour.mul_self w)
        simpa [hi] using hwself
      have hne : DihedralGroup.r i ≠ 1 := by
        intro h
        apply hw1
        apply Subtype.ext
        simpa [hi] using h
      have hihalf := rotation_index_eq_half i hsq hne
      simpa [hi, hihalf] using w.property
    · let u : V := tV * w
      have hu1 : u ≠ 1 := by
        intro hu
        apply hwt
        have htw : tV = w⁻¹ := mul_eq_one_iff_eq_inv.mp hu
        rw [IsKleinFour.inv_eq_self] at htw
        exact htw.symm
      have husq :
          DihedralGroup.r (i - j) * DihedralGroup.r (i - j) = 1 := by
        have huself := congrArg Subtype.val (IsKleinFour.mul_self u)
        simpa [u, tV, hi] using huself
      have hune : DihedralGroup.r (i - j) ≠ 1 := by
        intro h
        apply hu1
        apply Subtype.ext
        simpa [u, tV, hi] using h
      have hhalf := rotation_index_eq_half (i - j) husq hune
      have huV : DihedralGroup.r (i - j) ∈ V := by
        simpa [u, tV, hi] using u.property
      simpa [hhalf] using huV
  have hhalfzero :
      (2 : ZMod (2 ^ m)) * (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 :=
    (zmod_two_mul_eq_zero_iff hm2
      (2 ^ (m - 1) : ZMod (2 ^ m))).mpr (Or.inr rfl)
  have hhalfneg :
      -(2 ^ (m - 1) : ZMod (2 ^ m)) =
        (2 ^ (m - 1) : ZMod (2 ^ m)) := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa [two_mul] using hhalfzero
  have hrefV :
      DihedralGroup.sr
        (j + (2 ^ (m - 1) : ZMod (2 ^ m))) ∈ V := by
    simpa using V.mul_mem hjV hzV
  intro x hx
  have hxcomm : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
    (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.sr j) hjV
  rcases dihedralGroup_cases x with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hieq : j + i = j - i := by
      simpa [hi, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] using hxcomm
    have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
      rw [two_mul]
      calc
        i + i = (j + i) - (j - i) := by abel
        _ = 0 := by rw [hieq]; simp
    rcases (zmod_two_mul_eq_zero_iff hm2 i).mp htwo with hi0 | hihalf
    · rw [hi, hi0, DihedralGroup.r_zero]
      exact V.one_mem
    · rw [hi, hihalf]
      exact hzV
  · have hieq : i - j = j - i := by
      simpa [hi, DihedralGroup.sr_mul_sr] using hxcomm
    have htwo : (2 : ZMod (2 ^ m)) * (j - i) = 0 := by
      rw [two_mul]
      calc
        (j - i) + (j - i) = (j - i) + (i - j) := by rw [hieq]
        _ = 0 := by abel
    rcases (zmod_two_mul_eq_zero_iff hm2 (j - i)).mp htwo with hji0 | hjihalf
    · have hi' : i = j := (sub_eq_zero.mp hji0).symm
      rw [hi, hi']
      exact hjV
    · have hi' : i = j + (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        calc
          i = j - (j - i) := by abel
          _ = j - (2 ^ (m - 1) : ZMod (2 ^ m)) := by rw [hjihalf]
          _ = j + (2 ^ (m - 1) : ZMod (2 ^ m)) := by
            rw [sub_eq_add_neg, hhalfneg]
      rw [hi, hi']
      exact hrefV

/-- Transport the self-centralizer theorem for Klein-four subgroups from the
concrete dihedral model to an abstract group. -/
public theorem centralizer_kleinFour_le_of_dihedral_mulEquiv
    {K : Type u} [Group K] {m : ℕ} (hm : 1 ≤ m)
    (e : K ≃* DihedralGroup (2 ^ m))
    (V : Subgroup K) (hV : IsKleinFour V) :
    Subgroup.centralizer (V : Set K) ≤ V := by
  let V' : Subgroup (DihedralGroup (2 ^ m)) := V.map e
  let eV : V ≃* V' := V.equivMapOfInjective e.toMonoidHom e.injective
  have hV' : IsKleinFour V' := {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two
  }
  have hle' :
      Subgroup.centralizer (V' : Set (DihedralGroup (2 ^ m))) ≤ V' :=
    centralizer_kleinFour_le_dihedral hm V' hV'
  intro x hx
  have hxmap : e x ∈ Subgroup.centralizer
      ((e : K → DihedralGroup (2 ^ m)) '' (V : Set K)) := by
    have hmem : e x ∈ Subgroup.map e.toMonoidHom
        (Subgroup.centralizer (V : Set K)) :=
      Subgroup.mem_map_of_mem e.toMonoidHom hx
    exact (Subgroup.map_centralizer_le_centralizer_image (V : Set K)
      e.toMonoidHom) hmem
  have hx' : e x ∈ V' := by
    apply hle'
    simpa [V', Subgroup.coe_map] using hxmap
  simpa using (Subgroup.mem_map_equiv.mp hx')

/-- Every central element of an abstract finite dihedral `2`-group belongs to
each of its Klein-four subgroups. -/
public theorem center_mem_kleinFour_of_dihedral_mulEquiv
    {K : Type u} [Group K] {m : ℕ} (hm : 1 ≤ m)
    (e : K ≃* DihedralGroup (2 ^ m))
    (V : Subgroup K) (hV : IsKleinFour V)
    {z : K} (hz : z ∈ Subgroup.center K) :
    z ∈ V := by
  apply centralizer_kleinFour_le_of_dihedral_mulEquiv hm e V hV
  rw [Subgroup.mem_centralizer_iff]
  intro v _hv
  exact Subgroup.mem_center_iff.mp hz v

/-- Every finite dihedral `2`-group contains a Klein-four subgroup.  Starting
from a reflection subgroup of order two, Sylow's first theorem supplies an
overgroup of order four.  Such an overgroup cannot be cyclic: a cyclic
order-four subgroup is generated by a rotation and therefore cannot contain
the original reflection. -/
public theorem exists_kleinFour_subgroup_dihedral
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ V : Subgroup (DihedralGroup (2 ^ m)), IsKleinFour V := by
  let H : Subgroup (DihedralGroup (2 ^ m)) :=
    Subgroup.zpowers (DihedralGroup.sr 0)
  have hHcard : Nat.card H = 2 ^ 1 := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_sr]
    norm_num
  have hdvd : 2 ^ (1 + 1) ∣ Nat.card (DihedralGroup (2 ^ m)) := by
    rw [DihedralGroup.nat_card]
    have hpow : 2 ^ (1 + 1) ∣ 2 ^ (m + 1) :=
      pow_dvd_pow 2 (by omega)
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hpow
  obtain ⟨V, hVcard, hHV⟩ :=
    Sylow.exists_subgroup_card_pow_succ (G := DihedralGroup (2 ^ m))
      hdvd hHcard
  have hVnc : ¬ IsCyclic V := by
    intro hVcyc
    obtain ⟨g, hgord⟩ :=
      isCyclic_iff_exists_orderOf_eq_natCard.mp hVcyc
    have hgord4 : orderOf (g : DihedralGroup (2 ^ m)) = 4 := by
      calc
        orderOf (g : DihedralGroup (2 ^ m)) = orderOf g :=
          orderOf_injective V.subtype Subtype.coe_injective g
        _ = 4 := by simpa using hgord.trans hVcard
    have hgen : Subgroup.zpowers g = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hgord]
    rcases dihedralGroup_cases (g : DihedralGroup (2 ^ m)) with
        ⟨i, hi⟩ | ⟨i, hi⟩
    · have hsrV : DihedralGroup.sr 0 ∈ V :=
        hHV (Subgroup.mem_zpowers (DihedralGroup.sr 0))
      have hsgen : (⟨DihedralGroup.sr 0, hsrV⟩ : V) ∈
          Subgroup.zpowers g := by
        rw [hgen]
        trivial
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsgen
      have hcoe := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow, hi, DihedralGroup.r_zpow] at hcoe
      change DihedralGroup.r (i * (k : ZMod (2 ^ m))) =
        DihedralGroup.sr 0 at hcoe
      cases hcoe
    · rw [hi, DihedralGroup.orderOf_sr] at hgord4
      norm_num at hgord4
  refine ⟨V, ?_⟩
  exact {
    card_four := by simpa using hVcard
    exponent_two :=
      (not_isCyclic_iff_exponent_eq_prime Nat.prime_two
        (by simpa using hVcard)).mp hVnc
  }

/-- An ambient subgroup abstractly isomorphic to a finite dihedral `2`-group
contains an ambient Klein-four subgroup. -/
public theorem exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    {G : Type u} [Group G]
    (P : Subgroup G) {m : ℕ} (hm : 1 ≤ m)
    (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ V : Subgroup G, V ≤ P ∧ IsKleinFour V := by
  obtain ⟨W, hW⟩ := exists_kleinFour_subgroup_dihedral hm
  let W' : Subgroup P := W.map e.symm.toMonoidHom
  let eWW' : W ≃* W' :=
    W.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hW' : IsKleinFour W' := {
    card_four := (Nat.card_congr eWW'.toEquiv).symm.trans hW.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eWW').symm.trans hW.exponent_two
  }
  let V : Subgroup G := W'.map P.subtype
  let eW'V : W' ≃* V :=
    W'.equivMapOfInjective P.subtype Subtype.coe_injective
  have hV : IsKleinFour V := {
    card_four := (Nat.card_congr eW'V.toEquiv).symm.trans hW'.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eW'V).symm.trans hW'.exponent_two
  }
  exact ⟨V, Subgroup.map_subtype_le W', hV⟩

/-! A transport wrapper for applications that work in an abstract group
isomorphic to the dihedral model.  Keeping this bridge next to the concrete
centralizer theorem avoids repeating the image-of-centralizer bookkeeping in
the Proposition-9 file. -/

public theorem centralizer_le_of_normal_dihedral_of_mulEquiv
    {K : Type u} [Group K] {m : ℕ} (hm : 1 ≤ m)
    (e : K ≃* DihedralGroup (2 ^ m))
    (D : Subgroup K) (hDnormal : D.Normal) (hDnc : ¬ IsCyclic D) :
    Subgroup.centralizer (D : Set K) ≤ D := by
  let D' : Subgroup (DihedralGroup (2 ^ m)) := D.map e
  have hD'normal : D'.Normal := by
    exact (e.normal_map_iff).2 hDnormal
  have eD : D ≃* D' := D.equivMapOfInjective e.toMonoidHom e.injective
  have hD'nc : ¬ IsCyclic D' := by
    intro hcyc
    apply hDnc
    exact (eD.isCyclic).2 hcyc
  have hle' :
      Subgroup.centralizer (D' : Set (DihedralGroup (2 ^ m))) ≤ D' :=
    centralizer_le_of_normal_dihedral hm D' hD'normal hD'nc
  intro x hx
  have hxmap : e x ∈ Subgroup.centralizer
      ((e : K → DihedralGroup (2 ^ m)) '' (D : Set K)) := by
    have hmem : e x ∈ Subgroup.map e.toMonoidHom
        (Subgroup.centralizer (D : Set K)) :=
      Subgroup.mem_map_of_mem e.toMonoidHom hx
    exact (Subgroup.map_centralizer_le_centralizer_image (D : Set K)
      e.toMonoidHom) hmem
  have hx' : e x ∈ D' := by
    apply hle'
    simpa [D', Subgroup.coe_map] using hxmap
  simpa using (Subgroup.mem_map_equiv.mp hx')

end CFSG.GorensteinWalter
