module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18

namespace CFSG
end CFSG
open CFSG

/-!
# The Gorenstein--Walter classification layer

This file records Bender's definition of D-groups and the minimal
counterexample statement used in the proof.
-/

noncomputable section

open Matrix

namespace CFSG.GorensteinWalter

universe u v

/-! ## The statement of the classification -/

/-- An involution is a nonidentity element whose square is one. -/
@[expose] public def IsInvolution {G : Type*} [Group G] (x : G) : Prop :=
  x ≠ 1 ∧ x ^ 2 = 1

/-- Every Sylow `2`-subgroup is a finite dihedral `2`-group.  Since
`DihedralGroup n` has order `2 * n`, the model `DihedralGroup (2 ^ m)` has
order `2 ^ (m + 1)`.  The lower bound includes the Klein four group. -/
@[expose] public def HasDihedralSylowTwo (G : Type u) [Group G] : Prop :=
  ∀ S : Sylow 2 G,
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))

/-- The class used in the induction: Sylow `2`-subgroups may be cyclic or
dihedral. -/
@[expose] public def HasCyclicOrDihedralSylowTwo (G : Type u) [Group G] : Prop :=
  ∀ S : Sylow 2 G,
    IsCyclic S ∨ ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))

/-- `PSL(2,K)`. -/
public abbrev PSL2 (K : Type u) [CommRing K] :=
  ProjectiveSpecialLinearGroup (Fin 2) K

/-- `PGL(2,K)`. -/
public abbrev PGL2 (K : Type u) [CommRing K] :=
  ProjGenLinGroup (Fin 2) K

/-- A positive power of an odd prime.  This is the `q` occurring in the
definition of a `D`-group. -/
@[expose] public def IsOddPrimePower (q : ℕ) : Prop :=
  ∃ p n : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ n ∧ q = p ^ n

/-- Bender's definition of a `D`-group.  It is a finite group with cyclic or
dihedral Sylow `2`-subgroups such that, after quotienting by the odd core, the
group is a `2`-group, is `A₇`, or has a normal subgroup of odd index isomorphic
to `PSL(2,q)` or `PGL(2,q)` for an odd prime power `q`.  A finite field is used
to package the prime-power condition. -/
public inductive IsDGroup (G : Type u) [Group G] [Finite G] : Prop
  | quotientIsTwoGroup
      (hSylow : HasCyclicOrDihedralSylowTwo G)
      (h : IsPGroup 2 (G ⧸ pPrimeCore 2 G))
  | quotientIsASeven
      (hSylow : HasCyclicOrDihedralSylowTwo G)
      (e : Nonempty ((G ⧸ pPrimeCore 2 G) ≃* alternatingGroup (Fin 7)))
  | quotientHasLinearNormalSubgroup
      (hSylow : HasCyclicOrDihedralSylowTwo G)
      (K : Type u) [Field K] [Finite K]
      (hKprimePower : IsOddPrimePower (Nat.card K))
      (L : Subgroup (G ⧸ pPrimeCore 2 G))
      (hLnormal : L.Normal)
      (hLindex : Odd L.index)
      (hLmodel : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))

/-- The Gorenstein--Walter classification, as a proposition. -/
@[expose] public def gorensteinWalterStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasDihedralSylowTwo G → IsDGroup G

/-- A minimal counterexample to the theorem.  The induction is over all
smaller finite groups with cyclic or dihedral Sylow `2`-subgroups, exactly as
in Bender's definition of `D`-groups. -/
@[expose] public def IsMinimalCounterexample
    (G : Type u) [Group G] [Finite G] : Prop :=
  HasDihedralSylowTwo G ∧
    ¬ IsDGroup G ∧
      ∀ (H : Type u) [Group H] [Finite H],
        Nat.card H < Nat.card G →
          HasCyclicOrDihedralSylowTwo H → IsDGroup H

/-! A cyclic Sylow `2`-subgroup gives the normal `2`-complement branch of
`IsDGroup`.  This is the Burnside transfer step used when selecting the
minimal counterexample. -/
private theorem isDGroup_of_cyclicSylowTwo
    {G : Type u} [Group G] [Finite G]
    (hSylow : ∀ S : Sylow 2 G, IsCyclic S) :
    IsDGroup G := by
  have hcomp : HasNormalPComplement 2 G := by
    by_cases h2 : 2 ∣ Nat.card G
    · let S : Sylow 2 G := Classical.choice Sylow.nonempty
      have hmin : (Nat.card G).minFac = 2 :=
        (Nat.minFac_eq_two_iff (Nat.card G)).2 h2
      have hNC : Subgroup.normalizer (S : Set G) ≤
          Subgroup.centralizer (S : Set G) :=
        (hSylow S).normalizer_le_centralizer hmin
      have hScenter : (S : Subgroup G) ≤
          centerIn (G := G) (Subgroup.normalizer (S : Subgroup G)) := by
        intro s hs
        refine ⟨Subgroup.le_normalizer hs, ?_⟩
        change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
      exact hasNormalPComplement_of_sylow_le_center_normalizer (G := G) 2 S hScenter
    · have hodd : Odd (Nat.card G) := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        exact h2
      refine ⟨⊤, inferInstance, ?_, ?_⟩
      · simpa using hodd.coprime_two_left
      · intro x
        refine ⟨0, ?_⟩
        have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
          QuotientGroup.subsingleton_quotient_top
        simpa using (@Subsingleton.elim _ hsub x 1)
  have hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) G hcomp
  have hSylow' : HasCyclicOrDihedralSylowTwo G := by
    intro S
    exact Or.inl (hSylow S)
  exact IsDGroup.quotientIsTwoGroup hSylow' hQ

private theorem hasDihedralSylowTwo_of_hasCyclicOrDihedralSylowTwo_of_not_cyclic
    {G : Type u} [Group G] [Finite G]
    (hSylow : HasCyclicOrDihedralSylowTwo G)
    (hnotcyc : ¬ ∀ S : Sylow 2 G, IsCyclic S) :
    HasDihedralSylowTwo G := by
  push Not at hnotcyc
  rcases hnotcyc with ⟨S, hSnot⟩
  have hSdihedral : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m)) :=
    (hSylow S).resolve_left hSnot
  rcases hSdihedral with ⟨m, hm, ⟨eS⟩⟩
  intro T
  refine ⟨m, hm, ⟨(Sylow.equiv S T).symm.trans eS⟩⟩

/-- If the classification fails, choose a counterexample of least order. -/
public theorem exists_minimalCounterexample
    (h : ¬ gorensteinWalterStatement.{u}) :
    ∃ (G : Type u) (hG : Group G) (hfin : Finite G),
      @IsMinimalCounterexample G hG hfin := by
  classical
  rw [gorensteinWalterStatement] at h
  push Not at h
  let bad : ℕ → Prop := fun n =>
    ∃ (G : Type u) (hG : Group G) (hfin : Finite G),
      Nat.card G = n ∧ HasCyclicOrDihedralSylowTwo G ∧
        ¬ @IsDGroup G hG hfin
  have hex : ∃ n, bad n := by
    rcases h with ⟨G, hG, hfin, hSyl, hD⟩
    have hSyl' : HasCyclicOrDihedralSylowTwo G := by
      intro S
      exact Or.inr (hSyl S)
    exact ⟨Nat.card G, G, hG, hfin, rfl, hSyl', hD⟩
  let n : ℕ := Nat.find hex
  have hn : bad n := Nat.find_spec hex
  rcases hn with ⟨G, hG, hfin, hcard, hSyl, hnot⟩
  have hnotcyc : ¬ ∀ S : Sylow 2 G, IsCyclic S := by
    intro hcyc
    exact hnot (isDGroup_of_cyclicSylowTwo hcyc)
  have hdihedral :=
    hasDihedralSylowTwo_of_hasCyclicOrDihedralSylowTwo_of_not_cyclic hSyl hnotcyc
  refine ⟨G, hG, hfin, hdihedral, hnot, ?_⟩
  intro H hH hHfin hlt hHsy
  by_cases hHcyc : ∀ S : Sylow 2 H, IsCyclic S
  · exact isDGroup_of_cyclicSylowTwo hHcyc
  · by_contra hHnot
    have hbadH : bad (Nat.card H) :=
      ⟨H, hH, hHfin, rfl, hHsy, hHnot⟩
    have hle : n ≤ Nat.card H := Nat.find_min' hex hbadH
    have hle' : Nat.card G ≤ Nat.card H := by simpa [hcard] using hle
    exact (Nat.not_le_of_lt hlt) hle'

-- (1) element case split
private lemma dihedralGroup_cases {n : ℕ} (x : DihedralGroup n) :
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
private lemma r_mem_zpowers_r_one {n : ℕ} [NeZero n] (i : ZMod n) :
    DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  refine ⟨i.val, ?_⟩
  change (DihedralGroup.r 1 : DihedralGroup n) ^ i.val = DihedralGroup.r i
  rw [DihedralGroup.r_one_pow]
  congr 1
  exact ZMod.natCast_zmod_val i

-- (3) reflections are not rotations
private lemma sr_not_mem_zpowers_r_one {n : ℕ} (i : ZMod n) :
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
private lemma mem_decomp {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m)))
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
private lemma generator_of_inf {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m))) :
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
      simpa [a] using MonoidHom.map_zpowers (H ⊓ R).subtype g
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
private lemma mem_eq_one_of_card_one {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m)))
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

-- (7) the classification
private lemma isCyclic_or_dihedral_of_subgroup_dihedral_two_group {m : ℕ} (hm : 1 ≤ m)
    (H : Subgroup (DihedralGroup (2 ^ m))) :
    IsCyclic H ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let R : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (DihedralGroup.r 1)
  by_cases hHR : H ≤ R
  · left
    exact Subgroup.isCyclic_of_le hHR
  · -- H ⊄ R
    have hx : ∃ x : DihedralGroup (2 ^ m), x ∈ H ∧ x ∉ R := by
      by_contra h
      apply hHR
      intro x hxH
      by_cases hxR : x ∈ R
      · exact hxR
      · exact False.elim (h ⟨x, hxH, hxR⟩)
    rcases hx with ⟨x, hxH, hxR⟩
    rcases (dihedralGroup_cases x) with ⟨i₀, hi₀⟩ | ⟨i₀, hi₀⟩
    · rw [hi₀] at hxR
      exact False.elim (hxR (r_mem_zpowers_r_one i₀))
    · rw [hi₀] at hxH
      rcases (generator_of_inf H) with ⟨a, ha, hgenR⟩
      have haR : a ∈ R := by
        have ha' : a ∈ H ⊓ R := by
          rw [← hgenR]
          exact Subgroup.mem_zpowers a
        exact ha'.2
      have hord : orderOf a = Nat.card (↥(H ⊓ R)) := by
        calc
          orderOf a = Fintype.card (↥(Subgroup.zpowers a)) := (Fintype.card_zpowers (x := a)).symm
          _ = Nat.card (↥(Subgroup.zpowers a)) := Nat.card_eq_fintype_card.symm
          _ = Nat.card (↥(H ⊓ R)) := by rw [hgenR]
      have hRcard : Nat.card (↥R) = 2 ^ m := by
        calc
          Nat.card (↥R) = Fintype.card (↥R) := Nat.card_eq_fintype_card
          _ = orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) := Fintype.card_zpowers (x := DihedralGroup.r 1)
          _ = 2 ^ m := DihedralGroup.orderOf_r_one
      have hdiv : Nat.card (↥(H ⊓ R)) ∣ 2 ^ m := by
        have hle : Nat.card (↥(H ⊓ R)) ∣ Nat.card (↥R) := Subgroup.card_dvd_of_le inf_le_right
        rwa [hRcard] at hle
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdiv with ⟨k, hkle, hkpow⟩
      by_cases hcard1 : Nat.card (↥(H ⊓ R)) = 1
      · left
        refine Subgroup.isCyclic_of_le (H := H) (H' := Subgroup.zpowers (DihedralGroup.sr i₀)) ?_
        intro x hx
        rcases (mem_decomp H i₀ hxH x).mp hx with h1 | ⟨y, hy, hyx⟩
        · -- x ∈ H ⊓ R of size 1: x = 1
          have hx1 : x = 1 := mem_eq_one_of_card_one H hcard1 h1
          exact hx1 ▸ Subgroup.one_mem (Subgroup.zpowers (DihedralGroup.sr i₀))
        · -- x = sr i₀ · y with y ∈ H ⊓ R of size 1: y = 1
          have hy1 : y = 1 := mem_eq_one_of_card_one H hcard1 hy
          rw [hyx, hy1, mul_one]
          exact Subgroup.mem_zpowers (DihedralGroup.sr i₀)
      · -- |H ⊓ R| ≥ 2: apply the core
        have hrelD : DihedralGroup.sr i₀ * a * (DihedralGroup.sr i₀)⁻¹ = a⁻¹ := by
          rcases (Subgroup.mem_zpowers_iff).mp haR with ⟨t, ht⟩
          have hat : a = DihedralGroup.r (t : ZMod (2 ^ m)) := by
            rw [← ht, DihedralGroup.r_one_zpow]
          calc
            DihedralGroup.sr i₀ * a * (DihedralGroup.sr i₀)⁻¹ =
                DihedralGroup.sr i₀ * DihedralGroup.r (t : ZMod (2 ^ m)) * (DihedralGroup.sr i₀)⁻¹ := by rw [hat]
            _ = DihedralGroup.sr (i₀ + (t : ZMod (2 ^ m))) * (DihedralGroup.sr i₀)⁻¹ := by rw [DihedralGroup.sr_mul_r]
            _ = DihedralGroup.sr (i₀ + (t : ZMod (2 ^ m))) * DihedralGroup.sr i₀ := by rw [DihedralGroup.inv_sr]
            _ = DihedralGroup.r (i₀ - (i₀ + (t : ZMod (2 ^ m)))) := by rw [DihedralGroup.sr_mul_sr]
            _ = DihedralGroup.r (-(t : ZMod (2 ^ m))) := by congr 1; abel
            _ = (DihedralGroup.r (t : ZMod (2 ^ m)))⁻¹ := by rw [DihedralGroup.inv_r]
            _ = a⁻¹ := by rw [hat]
        have hrel' : (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H) * ⟨a, ha⟩ * (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H)⁻¹ = (⟨a, ha⟩ : ↥H)⁻¹ := by
          apply Subtype.ext
          simpa [Subtype.ext_iff] using hrelD
        have hσ2' : (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subtype.ext_iff, pow_two] using (DihedralGroup.sr_mul_self i₀)
        have hgen : ⊤ = Subgroup.zpowers (⟨a, ha⟩ : ↥H) ⊔ Subgroup.zpowers (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H) := by
          have hHjoin : H = Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀) := by
            apply le_antisymm
            · intro x hx
              rcases (mem_decomp H i₀ hxH x).mp hx with h1 | ⟨y, hy, hyx⟩
              · exact (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀)) (by rwa [← hgenR] at h1)
              · rw [hyx]
                exact Subgroup.mul_mem (Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀))
                  ((le_sup_right : Subgroup.zpowers (DihedralGroup.sr i₀) ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀)) (Subgroup.mem_zpowers (DihedralGroup.sr i₀)))
                  ((le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀)) (by rwa [← hgenR] at hy))
            · exact sup_le ((Subgroup.zpowers_le).mpr ha) ((Subgroup.zpowers_le).mpr hxH)
          apply le_antisymm
          · intro x hx
            have hx1 : (x : DihedralGroup (2 ^ m)) ∈
                (Subgroup.zpowers (⟨a, ha⟩ : ↥H) ⊔ Subgroup.zpowers (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H)).map H.subtype := by
              simpa [Subgroup.map_sup, MonoidHom.map_zpowers, hHjoin] using x.2
            rcases (Subgroup.mem_map).mp hx1 with ⟨y, hy, hyx⟩
            have hyx' : y = x := Subtype.ext hyx
            exact hyx' ▸ hy
          · intro x hx
            trivial
        rcases (isCyclic_or_dihedral_of_generators (D := ↥H)
          (ρ := ⟨a, ha⟩) (σ := ⟨DihedralGroup.sr i₀, hxH⟩) hgen hσ2' hrel') with hcyc | hdih
        · left
          exact hcyc
        · right
          have hk1 : 1 ≤ k := by
            have hpos : 0 < Nat.card (↥(H ⊓ R)) := Nat.card_pos
            have h2 : 2 ≤ Nat.card (↥(H ⊓ R)) := by omega
            rw [hkpow] at h2
            have hk0 : k ≠ 0 := by
              intro hk0
              rw [hk0] at h2
              norm_num at h2
            omega
          refine ⟨k, hk1, ?_⟩
          have hord' : orderOf (⟨a, ha⟩ : ↥H) = orderOf a := by
            exact (orderOf_injective H.subtype (Subtype.coe_injective) ⟨a, ha⟩).symm
          rw [hord', hord, hkpow] at hdih
          exact hdih

/-! Public interface for the dihedral-subgroup classification used by the
    Gorenstein--Walter Proposition-9 translation. -/

public theorem subgroups_dihedral_twoGroup_cyclic_or_dihedral {m : ℕ} (hm : 1 ≤ m)
    (H : Subgroup (DihedralGroup (2 ^ m))) :
    IsCyclic H ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  exact isCyclic_or_dihedral_of_subgroup_dihedral_two_group hm H

-- IsCyclic transport under a MulEquiv
private lemma isCyclic_of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (h : IsCyclic H) : IsCyclic G := by
  rcases (isCyclic_iff_exists_zpowers_eq_top).mp h with ⟨g, hg⟩
  refine (isCyclic_iff_exists_zpowers_eq_top).mpr ⟨e.symm g, ?_⟩
  have hmap : (Subgroup.zpowers g).map (e.symm : H →* G) = Subgroup.zpowers (e.symm g) := MonoidHom.map_zpowers (e.symm : H →* G) g
  have htop : (⊤ : Subgroup H).map (e.symm : H →* G) = ⊤ := by
    ext x
    simp [Subgroup.mem_map]
  calc
    Subgroup.zpowers (e.symm g) = (Subgroup.zpowers g).map e.symm := hmap.symm
    _ = (⊤ : Subgroup H).map e.symm := by rw [hg]
    _ = ⊤ := htop

-- Sylow 2-subgroups of proper subgroups of a dihedral-Sylow group are cyclic or dihedral
private lemma sylow_cyclic_or_dihedral {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G) (M : Subgroup G)
    (S : Sylow 2 (↥M)) :
    IsCyclic S ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k)) := by
  rcases (Sylow.exists_comap_subtype_eq S) with ⟨Q, hQ⟩
  rcases (hdihedral Q) with ⟨m, hmge1, hQd⟩
  rcases hQd with ⟨eQ⟩
  have hSleQ : (S : Subgroup (↥M)).map M.subtype ≤ (Q : Subgroup G) := by
    rw [← hQ]
    exact Subgroup.map_comap_le M.subtype Q
  let S' : Subgroup G := (S : Subgroup (↥M)).map M.subtype
  let S'' : Subgroup (DihedralGroup (2 ^ m)) := (S'.subgroupOf Q).map eQ.toMonoidHom
  have eSM : S ≃* S' := by
    simpa [S'] using (Subgroup.equivMapOfInjective S M.subtype (Subtype.coe_injective))
  have eS' : S' ≃* S'.subgroupOf Q := (Subgroup.subgroupOfEquivOfLe hSleQ).symm
  have eS'' : S'.subgroupOf Q ≃* S'' := by
    simpa [S''] using (Subgroup.equivMapOfInjective (S'.subgroupOf Q) eQ.toMonoidHom eQ.injective)
  rcases (isCyclic_or_dihedral_of_subgroup_dihedral_two_group hmge1 (H := S'')) with hcyc'' | hdih''
  · left
    exact isCyclic_of_mulEquiv eSM (isCyclic_of_mulEquiv eS' (isCyclic_of_mulEquiv eS'' hcyc''))
  · right
    rcases hdih'' with ⟨k, hkge1, eS''k⟩
    refine ⟨k, hkge1, ?_⟩
    exact ⟨(eSM.trans eS').trans (eS''.trans eS''k.some)⟩

-- the proper-subgroups clause of the minimal counterexample
private theorem properSubgroups_areDGroups_test
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (M : Subgroup G) (hM : M ≠ ⊤) :
    IsDGroup M := by
  have hIH := hmin.2.2
  have hcardM : Nat.card (↥M) < Nat.card G := by
    have hcard : Nat.card (↥M) * M.index = Nat.card G := Subgroup.card_mul_index M
    have hind1 : M.index ≠ 1 := (Subgroup.index_eq_one.not.mpr hM)
    have hindpos : 1 ≤ M.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    have hind : 2 ≤ M.index := by omega
    have hposM : 1 ≤ Nat.card (↥M) := Nat.card_pos
    rw [← hcard]
    nlinarith
  have hSylowM : HasCyclicOrDihedralSylowTwo (↥M) := by
    intro S
    exact sylow_cyclic_or_dihedral hmin.1 M S
  exact hIH (↥M) hcardM hSylowM

public theorem properSubgroups_areDGroups
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (M : Subgroup G) (hM : M ≠ ⊤) :
    IsDGroup M := by
  have hIH := hmin.2.2
  have hcardM : Nat.card (↥M) < Nat.card G := by
    have hcard : Nat.card (↥M) * M.index = Nat.card G := Subgroup.card_mul_index M
    have hind1 : M.index ≠ 1 := (Subgroup.index_eq_one.not.mpr hM)
    have hindpos : 1 ≤ M.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    have hind : 2 ≤ M.index := by omega
    have hposM : 1 ≤ Nat.card (↥M) := Nat.card_pos
    rw [← hcard]
    nlinarith
  have hSylowM : HasCyclicOrDihedralSylowTwo (↥M) := by
    intro S
    exact sylow_cyclic_or_dihedral hmin.1 M S
  exact hIH (↥M) hcardM hSylowM

-- D_{2^m} is generated by r 1 and sr 1
private lemma dihedral_two_group_generated {m : ℕ} :
    Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ⊔
      Subgroup.zpowers (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) = ⊤ := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  apply le_antisymm
  · intro x hx
    trivial
  · intro x hx
    rcases (dihedralGroup_cases x) with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [hi]
      exact (le_sup_left : Subgroup.zpowers (DihedralGroup.r 1) ≤ Subgroup.zpowers (DihedralGroup.r 1) ⊔ Subgroup.zpowers (DihedralGroup.sr 1)) (r_mem_zpowers_r_one i)
    · rw [hi]
      have hsr : DihedralGroup.sr i = DihedralGroup.sr 1 * DihedralGroup.r (i - 1) := by
        rw [DihedralGroup.sr_mul_r]
        congr 1
        rw [sub_eq_add_neg]
        abel
      rw [hsr]
      exact Subgroup.mul_mem (Subgroup.zpowers (DihedralGroup.r 1) ⊔ Subgroup.zpowers (DihedralGroup.sr 1))
        ((le_sup_right : Subgroup.zpowers (DihedralGroup.sr 1) ≤ Subgroup.zpowers (DihedralGroup.r 1) ⊔ Subgroup.zpowers (DihedralGroup.sr 1)) (Subgroup.mem_zpowers (DihedralGroup.sr 1)))
        ((le_sup_left : Subgroup.zpowers (DihedralGroup.r 1) ≤ Subgroup.zpowers (DihedralGroup.r 1) ⊔ Subgroup.zpowers (DihedralGroup.sr 1)) (r_mem_zpowers_r_one (i - 1)))

-- the classification of the quotient Sylow: image of a dihedral Sylow under a hom
public theorem hasCyclicOrDihedralSylowTwo_quotient {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G) (N : Subgroup G) [N.Normal] :
    HasCyclicOrDihedralSylowTwo (G ⧸ N) := by
  intro S
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective N
  rcases (Sylow.mapSurjective_surjective (p := 2) (f := f) hf S) with ⟨Q, hQ⟩
  rcases (hdihedral Q) with ⟨m, hmge1, hQd⟩
  rcases hQd with ⟨eQ⟩
  let ρ : G ⧸ N := f (eQ.symm (DihedralGroup.r 1))
  let σ : G ⧸ N := f (eQ.symm (DihedralGroup.sr 1))
  have hsq : (eQ.symm (DihedralGroup.sr 1) : ↥(Q : Subgroup G)) ^ 2 = 1 := by
    calc
      (eQ.symm (DihedralGroup.sr 1) : ↥(Q : Subgroup G)) ^ 2 = eQ.symm ((DihedralGroup.sr 1) ^ 2) := by
        rw [map_pow]
      _ = 1 := by
        have hsr : (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
          rw [pow_two]
          exact DihedralGroup.sr_mul_self 1
        rw [hsr, map_one]
  have hσ2 : σ ^ 2 = 1 := by
    calc
      σ ^ 2 = f ((eQ.symm (DihedralGroup.sr 1) : ↥(Q : Subgroup G)) ^ 2) := by
        simp [σ, map_pow]
      _ = 1 := by
        simp [← Subgroup.coe_pow, hsq, map_one]
  have hrelD : (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) * DihedralGroup.r 1 * (DihedralGroup.sr 1)⁻¹ = (DihedralGroup.r 1)⁻¹ := by
    calc
      (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) * DihedralGroup.r 1 * (DihedralGroup.sr 1)⁻¹ =
          DihedralGroup.sr (1 + 1) * (DihedralGroup.sr 1)⁻¹ := by rw [DihedralGroup.sr_mul_r]
      _ = DihedralGroup.sr (1 + 1) * DihedralGroup.sr 1 := by rw [DihedralGroup.inv_sr]
      _ = DihedralGroup.r (1 - (1 + 1)) := by rw [DihedralGroup.sr_mul_sr]
      _ = DihedralGroup.r (-1) := by congr 1; abel
      _ = (DihedralGroup.r 1)⁻¹ := by rw [DihedralGroup.inv_r]
  have hrelQ : (eQ.symm (DihedralGroup.sr 1) : ↥(Q : Subgroup G)) * eQ.symm (DihedralGroup.r 1) *
      (eQ.symm (DihedralGroup.sr 1))⁻¹ = (eQ.symm (DihedralGroup.r 1))⁻¹ := by
    calc
      (eQ.symm (DihedralGroup.sr 1) : ↥(Q : Subgroup G)) * eQ.symm (DihedralGroup.r 1) *
          (eQ.symm (DihedralGroup.sr 1))⁻¹ =
          eQ.symm (DihedralGroup.sr 1 * DihedralGroup.r 1 * (DihedralGroup.sr 1)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      _ = eQ.symm ((DihedralGroup.r 1)⁻¹) := by
        exact congrArg eQ.symm hrelD
      _ = (eQ.symm (DihedralGroup.r 1))⁻¹ := by
        rw [map_inv]
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    calc
      σ * ρ * σ⁻¹ = f (eQ.symm (DihedralGroup.sr 1) * eQ.symm (DihedralGroup.r 1) * (eQ.symm (DihedralGroup.sr 1))⁻¹) := by
        simp [σ, ρ, map_mul, map_inv]
      _ = f ((eQ.symm (DihedralGroup.r 1))⁻¹) := by
        rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, hrelQ]
      _ = ρ⁻¹ := by
        simp [ρ, map_inv]
  have hSm : (Q : Subgroup G).map f = (S : Subgroup (G ⧸ N)) := by
    rw [← Sylow.coe_mapSurjective hf Q]
    exact congrArg (fun X : Sylow 2 (G ⧸ N) => (X : Subgroup (G ⧸ N))) hQ
  have hρS : f (eQ.symm (DihedralGroup.r 1)) ∈ (S : Subgroup (G ⧸ N)) := by
    rw [← hSm]
    exact (Subgroup.mem_map).mpr ⟨eQ.symm (DihedralGroup.r 1), (eQ.symm (DihedralGroup.r 1)).2, rfl⟩
  have hσS : f (eQ.symm (DihedralGroup.sr 1)) ∈ (S : Subgroup (G ⧸ N)) := by
    rw [← hSm]
    exact (Subgroup.mem_map).mpr ⟨eQ.symm (DihedralGroup.sr 1), (eQ.symm (DihedralGroup.sr 1)).2, rfl⟩
  let ρ' : ↥S := ⟨f (eQ.symm (DihedralGroup.r 1)), hρS⟩
  let σ' : ↥S := ⟨f (eQ.symm (DihedralGroup.sr 1)), hσS⟩
  have hgenamb : (S : Subgroup (G ⧸ N)) =
      Subgroup.zpowers (f (eQ.symm (DihedralGroup.r 1))) ⊔
        Subgroup.zpowers (f (eQ.symm (DihedralGroup.sr 1))) := by
    calc
      (S : Subgroup (G ⧸ N)) = (Q : Subgroup G).map f := hSm.symm
      _ = ((⊤ : Subgroup ↥(Q : Subgroup G)).map (Q : Subgroup G).subtype).map f := by
        congr 1
        symm
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (⊤ : Subgroup ↥(Q : Subgroup G)).map (f.comp (Q : Subgroup G).subtype) := by
        rw [Subgroup.map_map]
      _ = ((Subgroup.zpowers (DihedralGroup.r 1) ⊔ Subgroup.zpowers (DihedralGroup.sr 1)).map eQ.symm.toMonoidHom).map (f.comp (Q : Subgroup G).subtype) := by
        congr 1
        symm
        rw [dihedral_two_group_generated, ← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top.mpr eQ.symm.surjective
      _ = ((Subgroup.zpowers (eQ.symm (DihedralGroup.r 1)) ⊔ Subgroup.zpowers (eQ.symm (DihedralGroup.sr 1)))).map (f.comp (Q : Subgroup G).subtype) := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      _ = Subgroup.zpowers (f (eQ.symm (DihedralGroup.r 1))) ⊔ Subgroup.zpowers (f (eQ.symm (DihedralGroup.sr 1))) := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
  have hgen : ⊤ = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    apply le_antisymm
    · intro x hx
      have hx1 : (x : G ⧸ N) ∈
          (Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ').map (S : Subgroup (G ⧸ N)).subtype := by
        simpa [ρ', σ', Subgroup.map_sup, MonoidHom.map_zpowers, ← hgenamb] using x.2
      rcases (Subgroup.mem_map).mp hx1 with ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
    · intro x hx
      trivial
  have hσ2' : σ' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subtype.ext_iff, pow_two, map_mul] using hσ2
  have hrel' : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := by
    apply Subtype.ext
    simpa [Subtype.ext_iff, map_mul, map_inv] using hrel
  rcases (isCyclic_or_dihedral_of_generators ρ' σ' hgen hσ2' hrel') with hcyc | hdih
  · left
    exact hcyc
  · rcases (S.isPGroup' ρ') with ⟨k, hkpow1⟩
    have hdvd : orderOf ρ' ∣ 2 ^ k := (orderOf_dvd_iff_pow_eq_one).mpr hkpow1
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨j, hjle, hjpow⟩
    by_cases hρ1 : orderOf ρ' = 1
    · left
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcyc1 : IsCyclic (DihedralGroup 1) :=
        isCyclic_of_prime_card (p := 2) (by rw [DihedralGroup.nat_card])
      have e1 : ↥S ≃* DihedralGroup 1 := by
        rw [← hρ1]
        exact hdih.some
      exact isCyclic_of_mulEquiv e1 hcyc1
    · right
      have hj1 : 1 ≤ j := by
        have hj0 : j ≠ 0 := by
          intro hj0
          rw [hj0, pow_zero] at hjpow
          exact hρ1 hjpow
        omega
      refine ⟨j, hj1, ?_⟩
      rw [hjpow] at hdih
      exact hdih

/-- The preimage of a subgroup of the quotient has cardinality the product. -/
private lemma card_comap_quotient {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) :
    Nat.card (H.comap (QuotientGroup.mk' N)) = Nat.card H * Nat.card N := by
  let mk := QuotientGroup.mk' N
  let P : Subgroup G := H.comap mk
  have hNP : N ≤ P := by
    intro x hx
    apply (Subgroup.mem_comap).mpr
    have hx1 : mk x = 1 :=
      (MonoidHom.mem_ker (f := mk)).mp ((QuotientGroup.ker_mk' (N := N)).symm ▸ hx)
    simpa [mk, hx1] using H.one_mem
  have : (N.subgroupOf P).Normal := by
    -- N ⊴ G ⟹ N ≤ N_G(N) ⟹ N.subgroupOf P ⊴ P
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := P) (N := N)
      (Subgroup.le_normalizer_of_normal (H := N) (K := P))
  have h1 : Nat.card (↥P) = Nat.card (↥P ⧸ (N.subgroupOf P)) * Nat.card (N.subgroupOf P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N.subgroupOf P)
  have hker : MonoidHom.ker (mk.comp P.subtype) = N.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change mk (x : G) = 1 ↔ x.1 ∈ N
    rw [← MonoidHom.mem_ker (f := mk)]
    change x.1 ∈ MonoidHom.ker (QuotientGroup.mk' N) ↔ x.1 ∈ N
    rw [QuotientGroup.ker_mk']
  have hmap : P.map mk = H := by
    have h1' : (H.comap mk).map mk = mk.range ⊓ H := Subgroup.map_comap_eq mk H
    have htop : mk.range = ⊤ := MonoidHom.range_eq_top_of_surjective mk (QuotientGroup.mk'_surjective N)
    simpa [P, mk, htop] using h1'
  have h2 : Nat.card (↥P ⧸ (N.subgroupOf P)) = Nat.card (P.map mk) := by
    rw [← hker]
    simpa [MonoidHom.range_comp, Subgroup.subtype_range] using
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange (mk.comp P.subtype)).toEquiv)
  have h3 : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  calc
    Nat.card (H.comap mk) = Nat.card (↥P) := rfl
    _ = Nat.card (↥P ⧸ (N.subgroupOf P)) * Nat.card (N.subgroupOf P) := h1
    _ = Nat.card (P.map mk) * Nat.card N := by rw [h2, h3]
    _ = Nat.card H * Nat.card N := by rw [hmap]

/-- The odd core of the quotient by the odd core is trivial
(`O_{2'}(G/O(G)) = 1`).  General form: if `N ⊴ G` contains the odd core and
has odd order, then `O_{2'}(G/N) = 1`. -/
private lemma card_quotient_lt_card_of_ne_bot {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N)
  have hNcard : 2 ≤ Nat.card N := by
    have h1 : 1 < Nat.card (↥N) := (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN
    exact Nat.succ_le_of_lt h1
  have hqpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  rw [hcard]
  nlinarith

private lemma pPrimeCore_quotient_eq_bot_of_eq_core {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : pPrimeCore 2 G ≤ N) (hNodd : Nat.Coprime 2 (Nat.card N)) :
    pPrimeCore 2 (G ⧸ N) = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro H hHnorm hHcop
  let mk := QuotientGroup.mk' N
  let P : Subgroup G := H.comap mk
  have hPnorm : P.Normal := hHnorm.comap mk
  have hPodd : Nat.Coprime 2 (Nat.card P) := by
    rw [show Nat.card P = Nat.card H * Nat.card N by
      simpa [P, mk] using card_comap_quotient N H]
    exact Nat.Coprime.mul_right hHcop hNodd
  have hPcore : P ≤ pPrimeCore 2 G := le_sSup ⟨hPnorm, hPodd⟩
  have hPN : P ≤ N := hPcore.trans hN
  have hmap : H = P.map mk := by
    have h1' : (H.comap mk).map mk = mk.range ⊓ H := Subgroup.map_comap_eq mk H
    have htop : mk.range = ⊤ := MonoidHom.range_eq_top_of_surjective mk (QuotientGroup.mk'_surjective N)
    simpa [P, mk, htop] using h1'.symm
  rw [hmap]
  exact le_bot_iff.mp ((Subgroup.map_mono hPN).trans (le_of_eq (by
    rw [Subgroup.map_eq_bot_iff]
    simpa [mk] using le_of_eq (QuotientGroup.ker_mk' (N := N)).symm)))

-- the transfer: if the quotient by O₂'(G) is a D-group, so is G
private lemma isDGroup_of_isDGroup_quotient {G : Type u} [Group G] [Finite G]
    (hSylow : HasCyclicOrDihedralSylowTwo G)
    (h : IsDGroup (G ⧸ pPrimeCore 2 G)) :
    IsDGroup G := by
  have hNodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) :=
    pPrimeCore_coprime_card (p := 2) (G := G)
  have hcorebot : pPrimeCore 2 (G ⧸ pPrimeCore 2 G) = ⊥ :=
    pPrimeCore_quotient_eq_bot_of_eq_core (N := pPrimeCore 2 G) (by simp) hNodd
  have e : (G ⧸ pPrimeCore 2 G) ⧸ pPrimeCore 2 (G ⧸ pPrimeCore 2 G) ≃* G ⧸ pPrimeCore 2 G := by
    exact (QuotientGroup.quotientMulEquivOfEq (G := G ⧸ pPrimeCore 2 G) hcorebot).trans
      (QuotientGroup.quotientBot (G := G ⧸ pPrimeCore 2 G))
  rcases h with ⟨hSylow', htwo'⟩ | ⟨hSylow', e7'⟩ | ⟨hSylow', K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · refine IsDGroup.quotientIsTwoGroup hSylow ?_
    exact IsPGroup.of_equiv htwo' e
  · refine IsDGroup.quotientIsASeven hSylow ?_
    exact ⟨e.symm.trans e7'.some⟩
  · let L' : Subgroup (G ⧸ pPrimeCore 2 G) := L.map e.toMonoidHom
    have hL'normal : L'.Normal := by
      simpa [L'] using (hLnormal.map e.toMonoidHom e.surjective)
    have hL'index : Odd L'.index := by
      change Odd (L.map e.toMonoidHom).index
      rw [Subgroup.index_map]
      have hker : (e.toMonoidHom).ker = ⊥ := MonoidHom.ker_eq_bot e.toMonoidHom e.injective
      have hrange : (e.toMonoidHom).range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
      rw [hker, hrange, Subgroup.index_top, mul_one, sup_bot_eq]
      exact hLindex
    have eL : L ≃* L' := by
      simpa [L'] using (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective)
    rcases hLmodel with hLpsl | hLpgl
    · refine IsDGroup.quotientHasLinearNormalSubgroup hSylow K hKprime L' hL'normal hL'index ?_
      left
      exact ⟨eL.symm.trans hLpsl.some⟩
    · refine IsDGroup.quotientHasLinearNormalSubgroup hSylow K hKprime L' hL'normal hL'index ?_
      right
      exact ⟨eL.symm.trans hLpgl.some⟩

/-- The odd core of a minimal counterexample is trivial.  This is the
`O(G) = 1` step of Proposition 9 of Gorenstein--Walter (Part II, p. 219): if
`O(G) ≠ 1`, then `G/O(G)` has dihedral Sylow `2`-subgroups (the image of the
dihedral Sylow of `G`) and smaller order, so by the induction clause of
`IsMinimalCounterexample` it is a `D`-group, and the quotient transfer
`isDGroup_of_isDGroup_quotient` lifts that to `G`, contradicting minimality.
Axiom-free. -/
public lemma pPrimeCore_two_eq_bot_of_minimalCounterexample {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    pPrimeCore 2 G = ⊥ := by
  by_contra hne
  have hcard : Nat.card (G ⧸ pPrimeCore 2 G) < Nat.card G :=
    card_quotient_lt_card_of_ne_bot (pPrimeCore 2 G) hne
  have hSylowQ : HasCyclicOrDihedralSylowTwo (G ⧸ pPrimeCore 2 G) :=
    hasCyclicOrDihedralSylowTwo_quotient hmin.1 (pPrimeCore 2 G)
  have hDQ : IsDGroup (G ⧸ pPrimeCore 2 G) := hmin.2.2 (G ⧸ pPrimeCore 2 G) hcard hSylowQ
  have hSylowG : HasCyclicOrDihedralSylowTwo G := by
    intro S
    rcases hmin.1 S with ⟨m, hm, e⟩
    right
    exact ⟨m, hm, e⟩
  have hDG : IsDGroup G := isDGroup_of_isDGroup_quotient hSylowG hDQ
  exact hmin.2.1 hDG

/-- From a proper nontrivial normal subgroup of a finite group, extract a
minimal normal subgroup `H'` (a nontrivial normal subgroup of least order):
`H'` is normal, nontrivial, proper, and every normal subgroup of `G` contained
in `H'` is trivial or all of `H'`.  Used by the simplicity part of
Proposition 9 of Gorenstein--Walter (Part II, p. 219). -/
public lemma exists_minimalNormal_of_normal_ne_bot {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hHnormal : H.Normal) (hHne : H ≠ ⊥) (hHtop : H ≠ ⊤) :
    ∃ H' : Subgroup G, H'.Normal ∧ H' ≠ ⊥ ∧ H' ≠ ⊤ ∧
      ∀ M : Subgroup G, M.Normal → M ≤ H' → M = ⊥ ∨ M = H' := by
  classical
  let P : ℕ → Prop := fun n => ∃ K : Subgroup G, K.Normal ∧ K ≠ ⊥ ∧ Nat.card (↥K) = n
  have hP : ∃ n, P n := ⟨Nat.card (↥H), H, hHnormal, hHne, rfl⟩
  let n : ℕ := Nat.find hP
  rcases Nat.find_spec hP with ⟨H', hH'normal, hH'ne, hH'card⟩
  refine ⟨H', hH'normal, hH'ne, ?_, ?_⟩
  · have hle : n ≤ Nat.card (↥H) := by
      refine le_of_not_gt ?_
      intro hlt
      exact (Nat.find_min hP hlt) ⟨H, hHnormal, hHne, rfl⟩
    have hcardH : Nat.card (↥H) < Nat.card G := by
      have hcard : Nat.card (↥H) * H.index = Nat.card G := Subgroup.card_mul_index H
      have hind1 : H.index ≠ 1 := (Subgroup.index_eq_one.not.mpr hHtop)
      have hindpos : 1 ≤ H.index := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_pos
      have hind : 2 ≤ H.index := by omega
      have hposH : 1 ≤ Nat.card (↥H) := Nat.card_pos
      rw [← hcard]
      nlinarith
    have hcardH' : Nat.card (↥H') < Nat.card G := by
      calc
        Nat.card (↥H') = n := hH'card
        _ ≤ Nat.card (↥H) := hle
        _ < Nat.card G := hcardH
    intro htop
    rw [htop, Subgroup.card_top] at hcardH'
    exact (lt_irrefl _) hcardH'
  · intro M hMnormal hMH
    by_cases hMbot : M = ⊥
    · exact Or.inl hMbot
    · right
      have hPcard : P (Nat.card (↥M)) := ⟨M, hMnormal, hMbot, rfl⟩
      have hngt : ¬ Nat.card (↥M) < n := by
        intro hlt
        exact (Nat.find_min hP hlt) hPcard
      have hle0 : n ≤ Nat.card (↥M) := le_of_not_gt hngt
      have hle1 : Nat.card (↥H') ≤ Nat.card (↥M) := by
        dsimp [n] at hle0
        rwa [← hH'card] at hle0
      have hle2 : Nat.card (↥M) ≤ Nat.card (↥H') := Subgroup.card_le_of_le hMH
      have hcard : Nat.card (↥M) = Nat.card (↥H') := le_antisymm hle2 hle1
      have : Fintype ↑(M : Set G) := Fintype.ofFinite ↑(M : Set G)
      have : Fintype ↑(H' : Set G) := Fintype.ofFinite ↑(H' : Set G)
      have hset : (M : Set G) = (H' : Set G) := by
        apply Set.eq_of_subset_of_card_le (s := (M : Set G)) (t := (H' : Set G)) hMH
        simpa [Nat.card_eq_fintype_card] using (le_of_eq hcard.symm)
      have hmem : ∀ x : G, x ∈ (M : Set G) ↔ x ∈ (H' : Set G) := by
        intro x
        rw [hset]
      exact Subgroup.ext (fun x => hmem x)

/-- The image in `G` of a characteristic subgroup of a normal subgroup is
normal in `G`: conjugation by `g` restricts to an automorphism of the normal
subgroup `H`, which fixes the characteristic subgroup `K`. -/
private lemma characteristic_map_normal_of_normal {G : Type u} [Group G]
    (H : Subgroup G) (K : Subgroup (↥H)) (hKchar : K.Characteristic)
    (hHnormal : H.Normal) : (K.map H.subtype).Normal := by
  refine ⟨?conj_mem⟩
  intro x hx g
  rcases (Subgroup.mem_map).mp hx with ⟨y, hy, hyx⟩
  let α : ↥H ≃* ↥H := {
    toFun := fun y => ⟨g * y.1 * g⁻¹, hHnormal.conj_mem y.1 y.2 g⟩
    invFun := fun y => ⟨g⁻¹ * y.1 * g, by simpa using (hHnormal.conj_mem y.1 y.2 g⁻¹)⟩
    left_inv := by intro y; ext; group
    right_inv := by intro y; ext; group
    map_mul' := by
      intro a b
      ext
      change g * ↑(a * b) * g⁻¹ = (g * ↑a * g⁻¹) * (g * ↑b * g⁻¹)
      rw [Subgroup.coe_mul]
      group
  }
  have hmap : K.map α.toMonoidHom = K := (Subgroup.characteristic_iff_map_eq.mp hKchar) α
  have hαy : α y ∈ K := by
    rw [← hmap]
    exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
  refine (Subgroup.mem_map).mpr ⟨α y, hαy, ?_⟩
  change (α y).1 = g * x * g⁻¹
  rw [← hyx]
  rfl

/-- The odd core of a normal subgroup of the minimal counterexample is
trivial: `O₂'(H)` is characteristic in `H ⊴ G`, so its image in `G` is
normal of odd order, hence contained in `O₂'(G) = 1`.  The `O(H) = 1` step
of Proposition 9 of Gorenstein--Walter (Part II, p. 219). -/
public lemma pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (H : Subgroup G) (hHnormal : H.Normal) :
    pPrimeCore 2 (↥H) = ⊥ := by
  have hO : pPrimeCore 2 G = ⊥ := pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
  let K : Subgroup (↥H) := pPrimeCore 2 (↥H)
  let K' : Subgroup G := K.map H.subtype
  have hK'norm : K'.Normal := by
    simpa [K', K] using
      (characteristic_map_normal_of_normal H (pPrimeCore 2 (↥H))
        (pPrimeCore_characteristic (p := 2)) hHnormal)
  have hK'cop : Nat.Coprime 2 (Nat.card K') := by
    have hcard : Nat.card K' = Nat.card K := by
      exact (Nat.card_congr (Subgroup.equivMapOfInjective K H.subtype (Subtype.coe_injective))).symm
    rw [hcard]
    simpa [K] using (pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hK'le : K' ≤ pPrimeCore 2 G := le_sSup ⟨hK'norm, hK'cop⟩
  have hK'bot : K' = ⊥ := le_bot_iff.mp (by rwa [hO] at hK'le)
  have hKle : K ≤ H.subtype.ker := (Subgroup.map_eq_bot_iff K).mp hK'bot
  have hker : H.subtype.ker = ⊥ := MonoidHom.ker_eq_bot H.subtype (Subtype.coe_injective)
  rw [hker] at hKle
  exact le_bot_iff.mp hKle

/-- A group with a dihedral Sylow `2`-subgroup is nontrivial: the Sylow has
order `2^(m+1) ≥ 4`, so `2` divides the order of the group. -/
public lemma nontrivial_of_dihedralSylowTwo {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G) : Nontrivial G := by
  classical
  rcases (Sylow.nonempty (p := 2) (G := G)) with ⟨S⟩
  rcases hdihedral S with ⟨m, hm, hSd⟩
  rcases hSd with ⟨e⟩
  have hcardS : Nat.card (↥(S : Subgroup G)) = 2 * 2 ^ m := by
    calc
      Nat.card (↥(S : Subgroup G)) = Nat.card (DihedralGroup (2 ^ m)) := Nat.card_congr e
      _ = 2 * 2 ^ m := DihedralGroup.nat_card
  have h2dvdS : 2 ∣ Nat.card (↥(S : Subgroup G)) := by
    rw [hcardS]
    exact dvd_mul_right 2 (2 ^ m)
  have hdvd : Nat.card (↥(S : Subgroup G)) ∣ Nat.card G := by
    simpa [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (H := (S : Subgroup G)) (K := ⊤) le_top)
  have h2le : 2 ≤ Nat.card G := Nat.le_of_dvd (by exact Nat.card_pos) (dvd_trans h2dvdS hdvd)
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at h2le
  have h1 : 1 < Fintype.card G := by omega
  exact (Fintype.one_lt_card_iff_nontrivial (α := G)).mp h1

/-- Two noncommuting even permutations of `Fin 7`: the `3`-cycle `(0 1 2)`
and the double transposition `(0 1)(2 3)`. -/
private def a7a : Equiv.Perm (Fin 7) := Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2

/-- The second noncommuting element of `A₇`: `(0 1)(2 3)`. -/
private def a7b : Equiv.Perm (Fin 7) := Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3

private lemma a7a_mem : a7a ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign a7a = 1
  rw [a7a, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2)]
  norm_num

private lemma a7b_mem : a7b ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign a7b = 1
  rw [a7b, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 7) ≠ 3)]
  norm_num

/-- The alternating group on seven letters is not commutative. -/
private lemma a7_not_comm : ¬ IsMulCommutative (alternatingGroup (Fin 7)) := by
  intro h
  have h1 : (⟨a7a, a7a_mem⟩ : alternatingGroup (Fin 7)) * ⟨a7b, a7b_mem⟩ =
      ⟨a7b, a7b_mem⟩ * ⟨a7a, a7a_mem⟩ := h.is_comm.comm _ _
  have h2 : a7a * a7b ≠ a7b * a7a := by
    decide
  exact h2 (by
    apply_fun (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7))) at h1
    simpa [Subgroup.coe_mul] using h1)

/-- `A₇` has trivial center: the center is a normal subgroup of the simple
group `A₇`, so it is `⊥` or `⊤`; the latter would make `A₇` commutative. -/
private lemma center_eq_bot_alternatingGroupSeven :
    Subgroup.center (alternatingGroup (Fin 7)) = ⊥ := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  rcases ((hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7))))) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : IsMulCommutative (alternatingGroup (Fin 7)) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      have hx : (x : alternatingGroup (Fin 7)) ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
        rw [htop]
        trivial
      exact (Subgroup.mem_center_iff.mp hx y).symm
    exact a7_not_comm hcomm

/-- Proposition 9 of Gorenstein--Walter, used at the start of Bender's
Section 2: a minimal counterexample is simple. -/
-- the D₈ in A₇: ρ = (0 1 2 3)(4 5), σ = (1 3)(4 5)
public abbrev d8rho : Equiv.Perm (Fin 7) :=
  Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5
private def d8sigma : Equiv.Perm (Fin 7) := Equiv.swap (1 : Fin 7) 3 * Equiv.swap 4 5

public lemma d8rho_mem : d8rho ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign d8rho = 1
  rw [d8rho, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 7) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5)]
  norm_num

private lemma d8sigma_mem : d8sigma ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign d8sigma = 1
  rw [d8sigma, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5)]
  norm_num

private lemma d8_sigma_sq : d8sigma * d8sigma = 1 := by
  decide

private lemma d8_rel : d8sigma * d8rho * d8sigma⁻¹ = d8rho⁻¹ := by
  decide

-- D := ⟨ρ, σ⟩ in A₇
private def d8 : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)) ⊔
    Subgroup.zpowers (⟨d8sigma, d8sigma_mem⟩ : alternatingGroup (Fin 7))

-- the core application: D ≃* DihedralGroup 4
private lemma d8_is_dihedral4 : Nonempty (d8 ≃* DihedralGroup 4) := by
  let ρ' : d8 := ⟨⟨d8rho, d8rho_mem⟩, by
    exact (le_sup_left : Subgroup.zpowers (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)) ≤ d8)
      (Subgroup.mem_zpowers (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)))⟩
  let σ' : d8 := ⟨⟨d8sigma, d8sigma_mem⟩, by
    exact (le_sup_right : Subgroup.zpowers (⟨d8sigma, d8sigma_mem⟩ : alternatingGroup (Fin 7)) ≤ d8)
      (Subgroup.mem_zpowers (⟨d8sigma, d8sigma_mem⟩ : alternatingGroup (Fin 7)))⟩
  have hgen : ⊤ = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    have hmap : Subgroup.map d8.subtype ⊤ =
        Subgroup.map d8.subtype (Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ') := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      dsimp [ρ', σ']
      rfl
    exact (Subgroup.map_injective (f := d8.subtype) Subtype.coe_injective) hmap
  have hσ2 : σ' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σ', pow_two, Subgroup.coe_mul] using d8_sigma_sq
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := by
    apply Subtype.ext
    dsimp [σ', ρ']
    exact Subtype.coe_injective (by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using d8_rel)
  rcases (isCyclic_or_dihedral_of_generators ρ' σ' hgen hσ2 hrel) with hcyc | hdih
  · have : IsCyclic d8 := hcyc
    have hcomm : ρ' * σ' = σ' * ρ' := IsMulCommutative.is_comm.comm ρ' σ'
    have hc : (↑(ρ' * σ') : Equiv.Perm (Fin 7)) = (↑(σ' * ρ') : Equiv.Perm (Fin 7)) :=
      congrArg (fun x : d8 => (x : Equiv.Perm (Fin 7))) hcomm
    have hdiff : d8rho * d8sigma ≠ d8sigma * d8rho := by decide
    have hamb : d8rho * d8sigma = d8sigma * d8rho := by
      simpa [ρ', σ', Subgroup.coe_mul] using hc
    exact False.elim (hdiff hamb)
  · rcases hdih with ⟨e⟩
    have hord : orderOf ρ' = 4 := by
      rw [← Subgroup.orderOf_coe ρ']
      change orderOf (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)) = 4
      rw [← Subgroup.orderOf_coe (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7))]
      change orderOf d8rho = 4
      apply (orderOf_eq_iff (n := 4) (by norm_num)).mpr
      constructor
      · decide
      · intro m hm0 hm4
        interval_cases m <;> decide
    rw [hord] at e
    exact ⟨e⟩

private lemma card_alternatingGroupSeven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

private lemma card_d8 : Nat.card d8 = 8 := by
  rw [Nat.card_congr (d8_is_dihedral4.some.toEquiv), DihedralGroup.nat_card]

public def sylowD8 : Sylow 2 (alternatingGroup (Fin 7)) := by
  refine Sylow.ofCard d8 ?_
  rw [card_d8, card_alternatingGroupSeven]
  rw [show (2520 : ℕ).factorization 2 = 3 by
    rw [show 2520 = 2 ^ 3 * 315 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
  norm_num

/-- The concrete generator `d8rho` lies in the concrete Sylow `2`-subgroup
`sylowD8` of `A₇`. -/
public lemma d8rho_mem_sylowD8 :
    (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)) ∈
      (sylowD8 : Subgroup (alternatingGroup (Fin 7))) := by
  simpa [sylowD8, Sylow.coe_ofCard, d8] using
    (le_sup_left : Subgroup.zpowers
      (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)) ≤ d8)
      (Subgroup.mem_zpowers (⟨d8rho, d8rho_mem⟩ : alternatingGroup (Fin 7)))

-- center transport under a group iso
public lemma center_eq_bot_of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (hZ : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    rcases (e.surjective y) with ⟨z, hz⟩
    rw [← hz]
    simpa [map_mul] using congrArg e ((Subgroup.mem_center_iff.mp hx) z)
  have hx'' : e x = 1 := Subgroup.mem_bot.mp (by rwa [hZ] at hx')
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm 1 := by rw [hx'']
    _ = 1 := map_one e.symm

-- hZ for the A₇ branch: H ≅ A₇ (minimal normal with the A₇ quotient and
-- trivial odd core) has trivial center
public lemma center_eq_bot_of_A7_quotient
{G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (e7 : Nonempty (H ⧸ pPrimeCore 2 H ≃* alternatingGroup (Fin 7))) :
    Subgroup.center (↥H) = ⊥ := by
  have hOH : pPrimeCore 2 (↥H) = ⊥ :=
    pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample hmin H hHnormal
  have eHA : ↥H ≃* alternatingGroup (Fin 7) := by
    exact ((QuotientGroup.quotientMulEquivOfEq (G := ↥H) hOH).trans
      (QuotientGroup.quotientBot (G := ↥H))).symm.trans e7.some
  exact center_eq_bot_of_mulEquiv eHA center_eq_bot_alternatingGroupSeven

public lemma hasDihedralSylowTwo_of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) (hH : HasDihedralSylowTwo H) :
    HasDihedralSylowTwo G := by
  intro S
  let T : Subgroup H := S.map (e : G →* H)
  have eST : Nonempty (↥(S : Subgroup G) ≃* ↥T) :=
    ⟨Subgroup.equivMapOfInjective (S : Subgroup G) (e : G →* H) e.injective⟩
  have hcardT : Nat.card T = Nat.card (S : Subgroup G) := by
    exact (Nat.card_congr eST.some.toEquiv).symm
  let T' : Sylow 2 H := Sylow.ofCard T (by
    rw [hcardT, Sylow.card_eq_multiplicity S]
    rw [Nat.card_congr e.toEquiv])
  rcases (hH T') with ⟨m, hm, ⟨eTD⟩⟩
  refine ⟨m, hm, ⟨?_⟩⟩
  simpa [T, T', Sylow.coe_ofCard] using (eST.some).trans eTD

private lemma isPGroup_of_isDGroup_quotient_twoGroup
    {G : Type u} [Group G] [Finite G]
    (hOH : pPrimeCore 2 G = ⊥) (hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G)) :
    IsPGroup 2 G := by
  have e : G ≃* (G ⧸ pPrimeCore 2 G) := by
    exact ((QuotientGroup.quotientMulEquivOfEq (G := G) hOH).trans
      (QuotientGroup.quotientBot (G := G))).symm
  exact IsPGroup.of_equiv hQ e.symm

public lemma quotient_center_embed_aut
    {G : Type u} [Group G] (H : Subgroup G) [H.Normal] :
    Nonempty ((G ⧸ Subgroup.centralizer (H : Set G)) →* MulAut (↥H)) := by
  refine ⟨QuotientGroup.lift (Subgroup.centralizer (H : Set G)) (MulAut.conjNormal (H := H)) ?_⟩
  intro x hx
  rw [MonoidHom.mem_ker]
  ext h
  rw [MulAut.conjNormal_apply]
  have hx' : (h : G) * x = x * (h : G) :=
    (Subgroup.mem_centralizer_iff.mp hx) (h : G) h.2
  rw [← hx']
  group
  simpa

private lemma hasCyclicOrDihedral_of_hasDihedral {G : Type u} [Group G]
    (h : HasDihedralSylowTwo G) : HasCyclicOrDihedralSylowTwo G := by
  intro S
  rcases (h S) with ⟨m, hm1, hd⟩
  exact Or.inr ⟨m, hm1, hd⟩

private lemma isDGroup_of_isPGroup_two {G : Type u} [Group G] [Finite G]
    (hSylow : HasCyclicOrDihedralSylowTwo G) (hG2 : IsPGroup 2 G) :
    IsDGroup G := by
  refine IsDGroup.quotientIsTwoGroup hSylow ?_
  exact IsPGroup.to_quotient hG2 (pPrimeCore 2 G)

public lemma hasDihedralSylowTwo_alternatingGroupSeven :
    HasDihedralSylowTwo (alternatingGroup (Fin 7)) := by
  intro S
  refine ⟨2, by norm_num, ⟨?_⟩⟩
  simpa [sylowD8, Sylow.coe_ofCard] using (Sylow.equiv S sylowD8).trans d8_is_dihedral4.some

/-- A finite simple group of even order has trivial odd core.  This is the
standard one-line reduction used when transporting the `A₇` branch through a
group isomorphism: a normal odd-order subgroup is either trivial or all of
the simple group, and the latter is ruled out by evenness. -/
public lemma pPrimeCore_eq_bot_of_simple_of_even
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (heven : 2 ∣ Nat.card G) :
    pPrimeCore 2 G = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro K hKnormal hKcoprime
  rcases (haveI := hKnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal K) with hbot | htop
  · exact hbot
  · exfalso
    have hcard : Nat.card G = Nat.card (↥K) := by
      rw [htop]
      symm
      exact Subgroup.card_top
    have hcoprime : Nat.Coprime 2 (Nat.card G) := by
      rw [hcard]
      exact hKcoprime
    have hone : 2 = 1 := hcoprime.eq_one_of_dvd heven
    omega

/-- A group isomorphic to `A₇` is a `D`-group.  The proof is constructive:
the isomorphism transports the dihedral Sylow structure, while simplicity and
the even order of `A₇` give a trivial odd core, so the `A₇` quotient
constructor applies directly. -/
public lemma isDGroup_of_mulEquiv_aSeven
    {G : Type u} [Group G] [Finite G]
    (e : Nonempty (G ≃* alternatingGroup (Fin 7))) :
    IsDGroup G := by
  rcases e with ⟨e⟩
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup G := e.isSimpleGroup
  have hcoreA : pPrimeCore 2 (alternatingGroup (Fin 7)) = ⊥ := by
    apply pPrimeCore_eq_bot_of_simple_of_even
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcoreG : pPrimeCore 2 G = ⊥ := by
    have hmap := pPrimeCore_map_iso 2 e
    have hmap' : (pPrimeCore 2 G).map e.toMonoidHom = ⊥ := by
      simpa [hcoreA] using hmap
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    simpa using hmap'
  have hSylow : HasCyclicOrDihedralSylowTwo G := by
    intro S
    rcases (hasDihedralSylowTwo_of_mulEquiv e
      hasDihedralSylowTwo_alternatingGroupSeven S) with ⟨m, hm, he⟩
    exact Or.inr ⟨m, hm, he⟩
  refine IsDGroup.quotientIsASeven hSylow ?_
  refine ⟨?_⟩
  exact (QuotientGroup.quotientMulEquivOfEq (G := G) hcoreG).trans
    ((QuotientGroup.quotientBot (G := G)).trans e)

/-- The quotient by the odd core is functorial under a group isomorphism.
This local equivalence is kept private because callers should normally use
`isDGroup_of_mulEquiv`; it is nevertheless useful for transporting the three
constructors of `IsDGroup` without unfolding `pPrimeCore`. -/
private def quotientOddCoreMulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal]
    (hNM : N.map e.toMonoidHom = M) :
    G ⧸ N ≃* H ⧸ M := by
  have hcomap : M.comap e.toMonoidHom = N := by
    apply le_antisymm
    · intro x hx
      have hx' : e x ∈ N.map e.toMonoidHom := by
        rw [hNM]
        exact hx
      rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyeq⟩
      have hxy : x = y := e.injective (hyeq.symm)
      simpa [hxy] using hy
    · intro x hx
      have hx' : e x ∈ N.map e.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hNM] at hx'
      exact hx'
  let φ : G →* (H ⧸ M) := (QuotientGroup.mk' M).comp e.toMonoidHom
  have hker : φ.ker = N := by
    have hker' : φ.ker = M.comap e.toMonoidHom := by
      ext x
      change QuotientGroup.mk' M (e x) = 1 ↔ x ∈ M.comap e.toMonoidHom
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    exact hker'.trans hcomap
  have hsurj : Function.Surjective φ := by
    intro y
    rcases QuotientGroup.mk'_surjective M y with ⟨z, rfl⟩
    rcases e.surjective z with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  exact QuotientGroup.liftEquiv N hsurj hker.symm

/-- Transport the cyclic-or-dihedral Sylow condition across a group
isomorphism, including across universe levels. -/
public lemma hasCyclicOrDihedralSylowTwo_of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H)
    (hH : HasCyclicOrDihedralSylowTwo H) :
    HasCyclicOrDihedralSylowTwo G := by
  intro S
  let T : Subgroup H := S.map (e : G →* H)
  have eST : Nonempty (↥(S : Subgroup G) ≃* ↥T) :=
    ⟨Subgroup.equivMapOfInjective (S : Subgroup G) (e : G →* H) e.injective⟩
  have hcardT : Nat.card T = Nat.card (S : Subgroup G) :=
    (Nat.card_congr eST.some.toEquiv).symm
  let T' : Sylow 2 H := Sylow.ofCard T (by
    rw [hcardT, Sylow.card_eq_multiplicity S]
    rw [Nat.card_congr e.toEquiv])
  rcases hH T' with hcyc | ⟨m, hm, hd⟩
  · exact Or.inl (eST.some.isCyclic.mpr hcyc)
  · exact Or.inr ⟨m, hm, ⟨eST.some.trans hd.some⟩⟩

/-- `IsDGroup` is invariant under same-universe group isomorphism.  The
quotient-is-two-group, `A₇`, and linear-normal-subgroup constructors are all
transported explicitly; in particular, no quotient or core definitions are
left opaque to downstream modules. -/
public lemma isDGroup_of_mulEquiv
    {G H : Type u} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) (hH : IsDGroup H) :
    IsDGroup G := by
  have hSylowH : HasCyclicOrDihedralSylowTwo H := by
    rcases hH with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _, _, _, _, _⟩
    · exact h
    · exact h
    · exact h
  have hSylow : HasCyclicOrDihedralSylowTwo G :=
    hasCyclicOrDihedralSylowTwo_of_mulEquiv e hSylowH
  have hmap := pPrimeCore_map_iso 2 e
  let N : Subgroup G := pPrimeCore 2 G
  let M : Subgroup H := pPrimeCore 2 H
  have hNM : N.map e.toMonoidHom = M := by simpa [N, M] using hmap
  let : N.Normal := pPrimeCore_normal
  let : M.Normal := pPrimeCore_normal
  let qE : (G ⧸ N) ≃* (H ⧸ M) := quotientOddCoreMulEquiv e N M hNM
  rcases hH with ⟨_hSylowH, htwo⟩ | ⟨_hSylowH, e7⟩ |
      ⟨_hSylowH, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · refine IsDGroup.quotientIsTwoGroup hSylow ?_
    exact IsPGroup.of_equiv htwo qE.symm
  · refine IsDGroup.quotientIsASeven hSylow ?_
    exact ⟨qE.trans e7.some⟩
  · let L' : Subgroup (G ⧸ N) := L.map qE.symm.toMonoidHom
    have hL'normal : L'.Normal := by
      simpa [L'] using (hLnormal.map qE.symm.toMonoidHom qE.symm.surjective)
    have hL'index : Odd L'.index := by
      change Odd (L.map qE.symm.toMonoidHom).index
      rw [Subgroup.index_map]
      have hker : qE.symm.toMonoidHom.ker = ⊥ :=
        MonoidHom.ker_eq_bot qE.symm.toMonoidHom qE.symm.injective
      have hrange : qE.symm.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr qE.symm.surjective
      rw [hker, hrange, Subgroup.index_top, mul_one, sup_bot_eq]
      exact hLindex
    have eL : L ≃* L' := by
      simpa [L'] using
        (Subgroup.equivMapOfInjective L qE.symm.toMonoidHom qE.symm.injective)
    rcases hLmodel with hLpsl | hLpgl
    · refine IsDGroup.quotientHasLinearNormalSubgroup hSylow K hKprime L'
        hL'normal hL'index ?_
      left
      exact ⟨eL.symm.trans hLpsl.some⟩
    · refine IsDGroup.quotientHasLinearNormalSubgroup hSylow K hKprime L'
        hL'normal hL'index ?_
      right
      exact ⟨eL.symm.trans hLpgl.some⟩


-- NOTE: `minimalCounterexample_isSimple` moved to
-- `GorensteinWalter/MinimalCounterexample.lean` (above GW1965): its S3 body
-- needs the [10]-Prop-9 dGroup-quotient supplies that live in GW1965, and
-- this module sits below GW1965. Consumers import the new module.




end CFSG.GorensteinWalter
