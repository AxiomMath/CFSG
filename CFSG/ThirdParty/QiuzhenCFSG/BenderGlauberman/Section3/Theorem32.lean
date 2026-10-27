module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.GroupTheory.CosetCover

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — Theorem 3.2

Theorem 3.2: each `χ ∈ ±Irr(G)` satisfies `|B(χ)| ≤ 3`.  Includes the
`restrictU_scalarProduct` input from Remark 3.1.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section3

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- An `S0`-orbit is determined by any one of its members (re-proof of the
Remark 3.1 private lemma, using only the public `s0Orbit`/`conjIrrS` API). -/
private lemma s0Orbit_eq_of_mem (c : Hyp11 G) {α β : Irr (↥c.U)}
    (hβ : β ∈ s0Orbit c α) : s0Orbit c β = s0Orbit c α := by
  classical
  rcases Finset.mem_image.mp hβ with ⟨r, hr, rfl⟩
  apply Finset.ext
  intro γ
  constructor
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
    refine Finset.mem_image.mpr
      ⟨⟨(r : G) * (g : G), (c.S0 : Subgroup G).mul_mem r.2 g.2⟩,
        Finset.mem_univ _, ?_⟩
    have hEq : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 g.2)) α =
        conjIrrS c (c.S0_le_S g.2) (conjIrrS c (c.S0_le_S r.2) α) :=
      conjIrrS_mul c (c.S0_le_S r.2) (c.S0_le_S g.2) α
    exact hEq
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
    refine Finset.mem_image.mpr
      ⟨⟨(r : G)⁻¹ * (g : G),
          (c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2⟩,
        Finset.mem_univ _, ?_⟩
    have hEq : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2
        ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2))) α =
        conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2))
          (conjIrrS c (c.S0_le_S r.2) α) :=
      conjIrrS_mul c (c.S0_le_S r.2)
        (c.S0_le_S ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2)) α
    have hrg : (r : G) * ((r : G)⁻¹ * (g : G)) = (g : G) := by group
    have hg' : (⟨(r : G) * ((r : G)⁻¹ * (g : G)),
        (c.S0 : Subgroup G).mul_mem r.2
          ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2)⟩ :
        ↥(c.S0 : Subgroup G)) = ⟨g, g.2⟩ := by
      apply Subtype.ext
      exact hrg
    have hconj : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2
        ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2))) α =
        conjIrrS c (c.S0_le_S g.2) α := by
      exact congrArg (fun x : ↥(c.S0 : Subgroup G) => conjIrrS c (c.S0_le_S x.2) α) hg'
    calc
      conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2))
          (conjIrrS c (c.S0_le_S r.2) α)
          = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2
              ((c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2))) α := hEq.symm
      _ = conjIrrS c (c.S0_le_S g.2) α := hconj

/-- The scalar product is additive in the first argument over a finset. -/
private lemma scalarProduct_sum_left_finset {G : Type u} [Group G] [Fintype G]
    {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G) (ψ : ClassFunction G) :
    scalarProduct G (∑ i ∈ s, f i) ψ = ∑ i ∈ s, scalarProduct G (f i) ψ := by
  classical
  rw [← Finset.sum_coe_sort (s := s) (f := f)]
  rw [scalarProduct_sum_left (f := fun i : s => f i.1)]
  rw [Finset.sum_coe_sort (s := s) (f := fun i : ι => scalarProduct G (f i) ψ)]

/-- The scalar product is additive in the second argument over a finset. -/
private lemma scalarProduct_sum_right_finset {G : Type u} [Group G] [Fintype G]
    {ι : Type*} (s : Finset ι) (φ : ClassFunction G) (f : ι → ClassFunction G) :
    scalarProduct G φ (∑ i ∈ s, f i) = ∑ i ∈ s, scalarProduct G φ (f i) := by
  classical
  rw [← Finset.sum_coe_sort (s := s) (f := f)]
  rw [scalarProduct_sum_right φ (fun i : s => f i.1)]
  rw [Finset.sum_coe_sort (s := s) (f := fun i : ι => scalarProduct G φ (f i))]

/-- The scalar product of a sum of pairwise-distinct irreducibles with itself
is the number of summands. -/
private lemma scalarProduct_sum_self_distinct {G : Type u} [Group G] [Fintype G]
    {ι : Type*} (s : Finset ι) (χ : ι → Irr G)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → χ i ≠ χ j) :
    scalarProduct G (∑ i ∈ s, (χ i).1) (∑ i ∈ s, (χ i).1) = (s.card : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scalarProduct]
  | insert a s has ih =>
      have hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → χ i ≠ χ j := by
        intro i hi j hj hij
        exact hdist i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hIH : scalarProduct G (∑ i ∈ s, (χ i).1) (∑ i ∈ s, (χ i).1) = (s.card : ℂ) :=
        ih hd
      have hcross1 : scalarProduct G (χ a).1 (∑ i ∈ s, (χ i).1) = 0 := by
        rw [scalarProduct_sum_right_finset]
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hane : a ≠ i := by
          intro hEq
          exact has (hEq ▸ hi)
        have hne : χ a ≠ χ i := by
          intro hEq
          exact hdist a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) hane hEq
        rw [scalarProduct_irr_ite (χ a).2 (χ i).2]
        have hne' : (χ a).1 ≠ (χ i).1 := by
          intro hEq
          exact hne (Subtype.ext hEq)
        simp [hne']
      have hcross2 : scalarProduct G (∑ i ∈ s, (χ i).1) (χ a).1 = 0 := by
        rw [scalarProduct_sum_left_finset]
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hane : a ≠ i := by
          intro hEq
          exact has (hEq ▸ hi)
        have hne : χ a ≠ χ i := by
          intro hEq
          exact hdist a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) hane hEq
        rw [scalarProduct_irr_ite (χ i).2 (χ a).2]
        have hne' : (χ i).1 ≠ (χ a).1 := by
          intro hEq
          exact hne (Subtype.ext hEq.symm)
        simp [hne']
      rw [Finset.sum_insert has]
      rw [Finset.card_insert_of_notMem has]
      rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
      rw [scalarProduct_irreducible_self (χ a).2, hcross1, hcross2, hIH]
      rw [Nat.cast_add]
      ring

/-- The scalar product of two sums over disjoint sets of irreducibles is
zero. -/
private lemma scalarProduct_sum_disjoint {G : Type u} [Group G] [Fintype G]
    {ι : Type*} (s : Finset ι) {κ : Type*} (t : Finset κ)
    (χ : ι → Irr G) (ψ : κ → Irr G)
    (hdist : ∀ i ∈ s, ∀ j ∈ t, χ i ≠ ψ j) :
    scalarProduct G (∑ i ∈ s, (χ i).1) (∑ j ∈ t, (ψ j).1) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scalarProduct]
  | insert a s has ih =>
      have hd : ∀ i ∈ s, ∀ j ∈ t, χ i ≠ ψ j := by
        intro i hi j hj
        exact hdist i (Finset.mem_insert_of_mem hi) j hj
      have hIH : scalarProduct G (∑ i ∈ s, (χ i).1) (∑ j ∈ t, (ψ j).1) = 0 := ih hd
      have hcross : scalarProduct G (χ a).1 (∑ j ∈ t, (ψ j).1) = 0 := by
        rw [scalarProduct_sum_right_finset]
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hne : χ a ≠ ψ j := hdist a (Finset.mem_insert_self a s) j hj
        rw [scalarProduct_irr_ite (χ a).2 (ψ j).2]
        have hne' : (χ a).1 ≠ (ψ j).1 := by
          intro hEq
          exact hne (Subtype.ext hEq)
        simp [hne']
      rw [Finset.sum_insert has]
      rw [scalarProduct_add_left]
      rw [hcross, hIH]
      simp

/-- The scalar product of a signed sum of pairwise-distinct irreducibles
with itself is the number of summands when every sign is real and squares
to `1`. -/
private lemma scalarProduct_sum_smul_self_distinct {G : Type u} [Group G] [Fintype G]
    {ι : Type*} (s : Finset ι) (χ : ι → Irr G) (a : ι → ℂ)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → χ i ≠ χ j)
    (ha_real : ∀ i ∈ s, star (a i) = a i)
    (ha_sq : ∀ i ∈ s, a i * a i = 1) :
    scalarProduct G (∑ i ∈ s, a i • (χ i).1) (∑ i ∈ s, a i • (χ i).1) =
      (s.card : ℂ) := by
  classical
  calc
    scalarProduct G (∑ i ∈ s, a i • (χ i).1) (∑ i ∈ s, a i • (χ i).1)
        = ∑ μ ∈ s, ∑ ν ∈ s,
            a μ * star (a ν) * (if (χ μ).1 = (χ ν).1 then 1 else 0) := by
            rw [scalarProduct_sum_left_finset]
            refine Finset.sum_congr rfl ?_
            intro μ hμ
            rw [scalarProduct_sum_right_finset]
            refine Finset.sum_congr rfl ?_
            intro ν hν
            rw [scalarProduct_smul_left]
            rw [scalarProduct_smul_right]
            rw [scalarProduct_irr_ite (χ μ).2 (χ ν).2]
            by_cases hEq : (χ μ).1 = (χ ν).1
            · simp [hEq]
            · simp [hEq]
    _ = ∑ μ ∈ s, a μ * star (a μ) := by
            refine Finset.sum_congr rfl ?_
            intro μ hμ
            have hinner : (∑ ν ∈ s,
                a μ * star (a ν) * (if (χ μ).1 = (χ ν).1 then 1 else 0)) =
                a μ * star (a μ) := by
              have hsingle : (∑ ν ∈ s,
                  a μ * star (a ν) * (if (χ μ).1 = (χ ν).1 then 1 else 0)) =
                  a μ * star (a μ) * (if (χ μ).1 = (χ μ).1 then 1 else 0) := by
                refine Finset.sum_eq_single
                  (f := fun ν : ι => a μ * star (a ν) * (if (χ μ).1 = (χ ν).1 then 1 else 0))
                  μ ?_ ?_
                · intro ν hν hne
                  have hχne : χ μ ≠ χ ν := hdist μ hμ ν hν hne.symm
                  have hcoeff : (χ μ).1 ≠ (χ ν).1 := fun hEq => hχne (Subtype.ext hEq)
                  simp [hχne, hcoeff]
                · intro hnot
                  exact False.elim (hnot hμ)
              simpa using hsingle
            exact hinner
    _ = (s.card : ℂ) := by
            calc
              (∑ μ ∈ s, a μ * star (a μ)) = ∑ μ ∈ s, (1 : ℂ) := by
                refine Finset.sum_congr rfl ?_
                intro μ hμ
                rw [ha_real μ hμ, ha_sq μ hμ]
              _ = (s.card : ℂ) := by simp

/-- By Remark 3.1 (as used in the proof of Theorem 3.2): for `μ, ν ∈ Irr(H0)`,
`(μ|_U, ν|_U)_U` is `0` when `μ` and `ν` are not equivalent, and is equal to
`m/|Λν|` otherwise. -/
public theorem restrictU_scalarProduct (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (μ ν : Irr (↥c.H0)) :
    (¬ μ.1 ∈ orbit c.H0 c.U ν.1 →
      scalarProduct (↥c.U) (restrictU c h12 μ.1) (restrictU c h12 ν.1) = 0) ∧
    (μ.1 ∈ orbit c.H0 c.U ν.1 →
      scalarProduct (↥c.U) (restrictU c h12 μ.1) (restrictU c h12 ν.1) =
        ((c.U.subgroupOf c.H0).index : ℂ) /
          ((orbit c.H0 c.U ν.1).card : ℂ)) := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC μ with ⟨α, hαμ⟩
  rcases orbit_is_orbitOfAlpha c h12 hSC ν with ⟨β, hβν⟩
  have hselfμ : μ.1 ∈ orbit c.H0 c.U μ.1 := by
    refine Finset.mem_image.mpr
      ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
    ext x
    simp [LambdaChar]
  have hselfν : ν.1 ∈ orbit c.H0 c.U ν.1 := by
    refine Finset.mem_image.mpr
      ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
    ext x
    simp [LambdaChar]
  have hresμ : restrictU c h12 μ.1 = ∑ α' ∈ s0Orbit c α, α'.1 := by
    exact (orbitOfAlpha_spec c h12 hSC α).2 μ.1 (by simpa [hαμ] using hselfμ)
  have hresν : restrictU c h12 ν.1 = ∑ β' ∈ s0Orbit c β, β'.1 := by
    exact (orbitOfAlpha_spec c h12 hSC β).2 ν.1 (by simpa [hβν] using hselfν)
  constructor
  · intro hμνnot
    have hdisj : ∀ a ∈ s0Orbit c α, ∀ b ∈ s0Orbit c β,
        a ≠ b := by
      intro a ha b hb hab
      have hαa : s0Orbit c α = s0Orbit c a := (s0Orbit_eq_of_mem c ha).symm
      have hβb : s0Orbit c β = s0Orbit c b := (s0Orbit_eq_of_mem c hb).symm
      have hsum_eq : (∑ α' ∈ s0Orbit c α, α'.1) = ∑ β' ∈ s0Orbit c β, β'.1 := by
        rw [hαa, hβb, hab]
      have hOrbitEq : orbitOfAlpha c h12 hSC α = orbitOfAlpha c h12 hSC β := by
        refine orbitOfAlpha_unique c h12 hSC β (orbitOfAlpha c h12 hSC α) ?_
        constructor
        · exact (orbitOfAlpha_spec c h12 hSC α).1
        · intro ν₀ hν₀
          calc
            restrictU c h12 ν₀ = ∑ α' ∈ s0Orbit c α, α'.1 :=
              (orbitOfAlpha_spec c h12 hSC α).2 ν₀ hν₀
            _ = ∑ β' ∈ s0Orbit c β, β'.1 := hsum_eq
      have hμin : μ.1 ∈ orbit c.H0 c.U ν.1 := by
        rw [hβν, ← hOrbitEq, ← hαμ]
        exact hselfμ
      exact hμνnot hμin
    rw [hresμ, hresν]
    exact scalarProduct_sum_disjoint (s0Orbit c α) (s0Orbit c β)
      (fun a : Irr (↥c.U) => a) (fun b : Irr (↥c.U) => b) hdisj
  · intro hμν
    have hresμ' : restrictU c h12 μ.1 = ∑ β' ∈ s0Orbit c β, β'.1 := by
      calc
        restrictU c h12 μ.1 = restrictU c h12 ν.1 := restrictU_orbit_mem c h12 hμν
        _ = ∑ β' ∈ s0Orbit c β, β'.1 := hresν
    rw [hresμ', hresν]
    have hsp : scalarProduct (↥c.U) (∑ β' ∈ s0Orbit c β, β'.1)
        (∑ β' ∈ s0Orbit c β, β'.1) = (s0Orbit c β).card := by
      refine scalarProduct_sum_self_distinct (s0Orbit c β) (fun a : Irr (↥c.U) => a) ?_
      intro i hi j hj hij
      intro hEq
      exact hij hEq
    rw [hsp]
    have hindex_prod : (s0Orbit c β).card * (orbit c.H0 c.U ν.1).card =
        (c.U.subgroupOf c.H0).index := by
      by_cases hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) β = β
      · have hcard1 : (s0Orbit c β).card = 1 := by
          rw [s0Orbit_eq_singleton_of_fixed c hSC β hfix]
          simp
        have hcard_orbit : (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index := by
          have h1 := orbitOfAlpha_card c h12 hSC β
          rw [hcard1] at h1
          have h1' : (orbitOfAlpha c h12 hSC β).card = (c.U.subgroupOf c.H0).index := by
            simpa using h1
          rw [hβν]
          exact h1'
        rw [hcard1, hcard_orbit]
        simp
      · have hcard2 : (s0Orbit c β).card = 2 := by
          rw [s0Orbit_eq_pair_of_not_fixed c hSC β hfix]
          have hne : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem
              (S0_generator_mem_S0 c))) β ≠ β := by
            intro h'
            exact hfix ((conjIrrS_r0_fixed_iff_r0_inv c β).mpr h')
          rw [Finset.card_insert_of_notMem]
          · simp
          · intro hEq
            exact hne (Finset.mem_singleton.mp hEq).symm
        let γ : ClassFunction (↥c.H0) := extensionChar_ind c hSC β 1
        have hStab : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
            LambdaChar s.1 * γ = γ)).card = 2 := by
          simpa [γ] using stabilizer_ind_not_fixed_card c h12 hSC β hfix
        have hγirr : IsIrreducibleCharacter γ := by
          simpa [γ] using extensionChar_ind_isIrreducible_of_not_fixed c hSC h12 β 1 hfix
        have hresγ : restrictU c h12 γ = ∑ β' ∈ s0Orbit c β, β'.1 := by
          rw [extensionChar_ind_restrict]
          simpa [conjIrrS, conjChar, conjMonoidHom] using
            (s0Orbit_sum_eq_α_add_r0_of_not_fixed c hSC β hfix).symm
        have horbitγ : orbit c.H0 c.U γ = orbitOfAlpha c h12 hSC β := by
          refine orbitOfAlpha_unique c h12 hSC β (orbit c.H0 c.U γ) ?_
          constructor
          · refine ⟨⟨γ, hγirr⟩, rfl⟩
          · intro ν hν
            calc
              restrictU c h12 ν = restrictU c h12 γ := restrictU_orbit_mem c h12 hν
              _ = ∑ β' ∈ s0Orbit c β, β'.1 := hresγ
        have horbit_eq : orbit c.H0 c.U ν.1 = orbit c.H0 c.U γ := by
          rw [hβν, horbitγ]
        have hmain := orbit_card_mul_stab c.H0 c.U γ
        have hΛ : Fintype.card (LambdaHom c.H0 c.U) = (c.U.subgroupOf c.H0).index := by
          simpa using lambda_card_eq_index c h12
        have hmul : (orbit c.H0 c.U γ).card * 2 = (c.U.subgroupOf c.H0).index := by
          rw [← hStab, hmain, hΛ]
        have hmulν : (orbit c.H0 c.U ν.1).card * 2 = (c.U.subgroupOf c.H0).index := by
          rw [horbit_eq]
          exact hmul
        rw [hcard2]
        rw [mul_comm]
        exact hmulν
    have horbit_pos : 0 < (orbit c.H0 c.U ν.1).card :=
      Finset.card_pos.mpr ⟨ν.1, hselfν⟩
    have hindex_cast : ((c.U.subgroupOf c.H0).index : ℂ) =
        (s0Orbit c β).card * (orbit c.H0 c.U ν.1).card := by
      rw [← hindex_prod, Nat.cast_mul]
    rw [hindex_cast]
    have hk : ((orbit c.H0 c.U ν.1).card : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp horbit_pos)
    field_simp [hk]

/-- `|H0 : U|` is a power of `2`: `H0 = U·S0` with `S0` the cyclic
index-two subgroup of the dihedral Sylow `2`-subgroup `S`. -/
private lemma U_index_is_pow_two (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = 2 ^ c.m := by
  classical
  let f : ↥c.U × ↥c.S0 → ↥c.H0 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p q hEq
    have hEq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hEq
    have h₁ : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hU : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.U := (c.U).mul_mem ((c.U).inv_mem q.1.2) p.1.2
    have hS0 : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.S0 := (c.S0).mul_mem q.2.2 ((c.S0).inv_mem p.2.2)
    have honeU : (q.1 : G)⁻¹ * (p.1 : G) = 1 := U_inter_S0_eq_bot c hU (by
      rw [h₁]
      exact hS0)
    have hS0inU : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.U := by
      rw [← h₁]
      exact hU
    have honeS : (q.2 : G) * (p.2 : G)⁻¹ = 1 := U_inter_S0_eq_bot c hS0inU hS0
    apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel (a := (q.1 : G)⁻¹) (by
        calc
          (q.1 : G)⁻¹ * (p.1 : G) = 1 := honeU
          _ = (q.1 : G)⁻¹ * (q.1 : G) := by group)
    · apply Subtype.ext
      exact (calc
        (q.2 : G) = (q.2 : G) * (p.2 : G)⁻¹ * (p.2 : G) := by group
        _ = (p.2 : G) := by rw [honeS]; simp).symm
  have hsurj : ∀ x : ↥c.H0, ∃ p : ↥c.U × ↥c.S0, f p = x := by
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hEq⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hEq.symm
  have hcardcong : Nat.card (↥c.H0) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by
    let e : ↥c.U × ↥c.S0 ≃ ↥c.H0 := Equiv.ofBijective f ⟨hinj, hsurj⟩
    have hc : Nat.card (↥c.U × ↥c.S0) = Nat.card (↥c.H0) := Nat.card_congr e
    rw [← hc]
    simp
  have hUcard : Nat.card (↥(c.U.subgroupOf c.H0)) = Nat.card (↥c.U) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.U.subgroupOf c.H0) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have h1 : (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    rw [← hUcard]
    rw [mul_comm]
    exact hcm
  have h2 : Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    calc
      Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by rw [mul_comm]
      _ = Nat.card (↥c.H0) := hcardcong.symm
  have hindex : (c.U.subgroupOf c.H0).index = Nat.card (↥c.S0) := by
    exact mul_right_cancel₀ (b := Nat.card (↥c.U)) (Nat.card_pos (α := ↥c.U)).ne' (by
      calc
        (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := h1
        _ = Nat.card (↥c.S0) * Nat.card (↥c.U) := h2.symm)
  rw [hindex]
  exact S0_nat_card c

/-- Every `Λ`-orbit of an irreducible character of `H0` has 2-power
cardinality (orbit-stabilizer + `|Λ| = |H0 : U| = 2^m`). -/
private lemma orbit_card_is_pow_two (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : Irr (↥c.H0)) :
    ∃ k : ℕ, (orbit c.H0 c.U ν.1).card = 2 ^ k := by
  classical
  have hmain := orbit_card_mul_stab c.H0 c.U ν.1
  have hΛ : Fintype.card (LambdaHom c.H0 c.U) = (c.U.subgroupOf c.H0).index := by
    simpa using lambda_card_eq_index c h12
  have hdvd : (orbit c.H0 c.U ν.1).card ∣ (c.U.subgroupOf c.H0).index := by
    refine ⟨(Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * ν.1 = ν.1)).card, ?_⟩
    rw [← hΛ]
    rw [hmain]
  have hindex : (c.U.subgroupOf c.H0).index = 2 ^ c.m := U_index_is_pow_two c h12
  have hdvd' : (orbit c.H0 c.U ν.1).card ∣ 2 ^ c.m := by
    rwa [hindex] at hdvd
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd' with ⟨k, _hk, hk⟩
  exact ⟨k, hk⟩

/-- Every `Λ`-orbit of an irreducible character of `H0` has at least two
elements: a singleton orbit would force the character to vanish on `T`,
contradicting `ν(t) ≠ 0` for the central involution `t ∈ T`. -/
private lemma orbit_self_mem' (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    (ν : ClassFunction (↥c.H0)) : ν ∈ orbit c.H0 c.U ν := by
  classical
  refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
  ext x
  simp [LambdaChar]

private lemma orbit_card_ge_two (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : Irr (↥c.H0)) :
    2 ≤ (orbit c.H0 c.U ν.1).card := by
  classical
  by_contra hnot
  have hmem : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem' c ν.1
  have hpos : 0 < (orbit c.H0 c.U ν.1).card := Finset.card_pos.mpr ⟨ν.1, hmem⟩
  have hcard1 : (orbit c.H0 c.U ν.1).card = 1 := by omega
  have hsing : ∀ l : LambdaHom c.H0 c.U, LambdaChar l.1 * ν.1 = ν.1 := by
    intro l
    have h : LambdaChar l.1 * ν.1 ∈ orbit c.H0 c.U ν.1 :=
      Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
    rcases Finset.card_eq_one.mp hcard1 with ⟨a, ha⟩
    have hνa : ν.1 = a := Finset.mem_singleton.mp (by simpa [ha] using hmem)
    rw [ha] at h
    exact (Finset.mem_singleton.mp h).trans hνa.symm
  let tH0 : ↥c.H0 := ⟨c.t, S0_le_H0 c c.t_mem_S0⟩
  have ht_not_U : (tH0 : G) ∉ c.U := t_not_mem_U c
  rcases LambdaHom_separates c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12)
      tH0 ht_not_U with ⟨l, hl⟩
  have hνt : ν.1 tH0 ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0) (by simpa [tH0] using t_central_H0' c)
    (by simpa [tH0] using t_H0_sq c) ν.2
  have hpt : (l.1 tH0 : ℂ) * ν.1 tH0 = 1 * ν.1 tH0 := by
    have h := congrFun (hsing l) tH0
    simpa [LambdaChar] using h
  have hl1 : (l.1 tH0 : ℂ) = 1 := mul_right_cancel₀ hνt hpt
  exact hl (by simpa using hl1)

/-- The scalar product is additive in the first argument (difference form). -/
private lemma scalarProduct_sub_left {G : Type u} [Group G] [Fintype G]
    (φ₁ φ₂ ψ : ClassFunction G) :
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
  calc
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G (φ₁ + (-1 : ℂ) • φ₂) ψ := by
          congr 1
          funext x
          simp [sub_eq_add_neg]
    _ = scalarProduct G φ₁ ψ + scalarProduct G ((-1 : ℂ) • φ₂) ψ := scalarProduct_add_left _ _ _
    _ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
          rw [scalarProduct_smul_left]
          ring

/-- `s⁻¹` normalizes `H0` (from `s² = 1`). -/
private lemma s_inv_normalizes_H0' (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
  intro x
  have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hx : c.s * (x : G) * c.s⁻¹ ∈ c.H0 := s_normalizes_H0 c h12 x
  simpa [hs'] using hx

/-- Conjugation by the involution `s` is an involution on class functions. -/
private lemma conjChar_involution (c : Hyp11 G) (h12 : Hyp12 c)
    (φ : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12) (conjChar c.H0 (s_normalizes_H0 c h12) φ) = φ := by
  have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
  ext x
  simp only [conjChar, conjMonoidHom]
  apply congrArg φ
  apply Subtype.ext
  calc
    c.s * (c.s * (x : G) * c.s⁻¹) * c.s⁻¹ = c.s * (c.s * (x : G)) * c.s⁻¹ * c.s⁻¹ := by group
    _ = (c.s * c.s) * (x : G) * (c.s⁻¹ * c.s⁻¹) := by group
    _ = 1 * (x : G) * 1 := by
          rw [hss]
          rw [← mul_inv_rev c.s c.s]
          rw [hss]
          simp
    _ = (x : G) := by simp

/-- `(α, β^s) = (α^s, β)` for characters of `H0`. -/
private lemma scalarProduct_conjChar_eq (c : Hyp11 G) (h12 : Hyp12 c)
    (α β : Irr (↥c.H0)) :
    scalarProduct (↥c.H0) α.1 (conjChar c.H0 (s_normalizes_H0 c h12) β.1) =
      scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) α.1) β.1 := by
  classical
  unfold scalarProduct
  congr 1
  refine Finset.sum_bij
    (fun x : ↥c.H0 => fun _ : x ∈ (Finset.univ : Finset (↥c.H0)) =>
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp
  · intro a ha b hb hEq
    apply Subtype.ext
    have hEq' : c.s * (a : G) * c.s⁻¹ = c.s * (b : G) * c.s⁻¹ := congrArg Subtype.val hEq
    have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right hss
    calc
      (a : G) = 1 * (a : G) * 1 := by simp
      _ = (c.s * c.s) * (a : G) * (c.s * c.s) := by rw [hss]
      _ = c.s * (c.s * (a : G) * c.s⁻¹) * c.s := by
            rw [hs']
            group
      _ = c.s * (c.s * (b : G) * c.s⁻¹) * c.s := by rw [hEq']
      _ = (b : G) := by
            calc
              c.s * (c.s * (b : G) * c.s⁻¹) * c.s = c.s * (c.s * (b : G) * c.s) * c.s := by rw [hs']
              _ = (c.s * c.s) * (b : G) * (c.s * c.s) := by group
              _ = 1 * (b : G) * 1 := by rw [hss]
              _ = (b : G) := by simp
  · intro y hy
    refine ⟨⟨c.s⁻¹ * (y : G) * c.s, s_inv_normalizes_H0' c h12 y⟩, by simp, ?_⟩
    apply Subtype.ext
    have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right hss
    calc
      c.s * (c.s⁻¹ * (y : G) * c.s) * c.s⁻¹ = c.s * (c.s * (y : G) * c.s⁻¹) * c.s⁻¹ := by
            rw [hs']
      _ = (y : G) := by
            rw [hs']
            calc
              c.s * (c.s * (y : G) * c.s) * c.s = (c.s * c.s) * (y : G) * (c.s * c.s) := by group
              _ = 1 * (y : G) * 1 := by rw [hss]
              _ = (y : G) := by simp
  · intro x hx
    have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hs' : c.s⁻¹ = c.s := inv_eq_of_mul_eq_one_right hss
    simp only [conjChar]
    congr 1
    apply congrArg (α : ↥c.H0 → ℂ)
    apply Subtype.ext
    change (x : G) = c.s * (c.s * (x : G) * c.s⁻¹) * c.s⁻¹
    rw [hs']
    have hmain : c.s * (c.s * (x : G) * c.s) * c.s = (x : G) := by
      calc
        c.s * (c.s * (x : G) * c.s) * c.s = (c.s * c.s) * (x : G) * (c.s * c.s) := by group
        _ = 1 * (x : G) * 1 := by rw [hss]
        _ = (x : G) := by simp
    rw [hmain]

/-- The scalar product of a character with the `s`-conjugate of another is
`1` exactly when the `s`-conjugate of the first equals the second. -/
private lemma scalarProduct_conjChar_irr (c : Hyp11 G) (h12 : Hyp12 c)
    (α β : Irr (↥c.H0)) :
    scalarProduct (↥c.H0) α.1 (conjChar c.H0 (s_normalizes_H0 c h12) β.1) =
      if conjChar c.H0 (s_normalizes_H0 c h12) α.1 = β.1 then 1 else 0 := by
  classical
  rw [scalarProduct_conjChar_eq c h12 α β]
  rw [scalarProduct_irr_ite
    (isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) (s_inv_normalizes_H0' c h12) α.2) β.2]

/-- `±Irr(G)` are generalized characters. -/
private lemma isGeneralizedCharacter_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : IsGeneralizedCharacter χ := by
  rcases hχ with hχ | hχ
  · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero, by simp⟩
  · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχ, by simp⟩

/-- The difference of two generalized characters is a generalized character. -/
private lemma isGeneralizedCharacter_sub {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ) : IsGeneralizedCharacter (φ - ψ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hψ with ⟨ε₁, ε₂, hε₁, hε₂, hψeq⟩
  refine ⟨δ₁ + ε₂, δ₂ + ε₁, isCharacter_add hδ₁ hε₂, isCharacter_add hδ₂ hε₁, ?_⟩
  rw [hφeq, hψeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- `conjChar` is additive on differences. -/
private lemma conjChar_sub {G : Type u} [Group G] (H0 : Subgroup G) {s : G}
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0) (φ ψ : ClassFunction (↥H0)) :
    conjChar H0 hsH0 (φ - ψ) = conjChar H0 hsH0 φ - conjChar H0 hsH0 ψ := by
  ext x
  simp [conjChar, Pi.sub_apply, conjMonoidHom]

/-- Members of the same `Λ`-orbit agree on `U`, so `μ − ν` is supported on
`T = H0 ∖ U`. -/
private lemma supportedOn_T_of_orbit (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {μ ν : Irr (↥c.H0)}
    (hμν : μ.1 ∈ orbit c.H0 c.U ν.1) :
    supportedOn (μ.1 - ν.1) {x : ↥c.H0 | (x : G) ∈ c.T} := by
  intro x hxT
  have hxU : (x : G) ∈ c.U := by
    by_contra hnot
    exact hxT ⟨x.2, hnot⟩
  have hEq : μ.1 x = ν.1 x := by
    have h' := congrFun (restrictU_orbit_mem c h12 hμν) ⟨(x : G), hxU⟩
    simpa [restrictU] using h'
  simp [hEq]

/-- `(μ − ν, μ − ν) = 2` for distinct irreducibles `μ, ν`. -/
private lemma scalarProduct_sub_irr_self {G : Type u} [Group G] [Fintype G]
    {μ ν : Irr G} (hμν : μ ≠ ν) :
    scalarProduct G (μ.1 - ν.1) (μ.1 - ν.1) = 2 := by
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
  rw [scalarProduct_irreducible_self μ.2, scalarProduct_irr_ite μ.2 ν.2,
    scalarProduct_irr_ite ν.2 μ.2, scalarProduct_irreducible_self ν.2]
  have hμν' : μ.1 ≠ ν.1 := by
    intro h
    exact hμν (Subtype.ext h)
  have hνμ' : ν.1 ≠ μ.1 := by
    intro h
    exact hμν (Subtype.ext h.symm)
  simp [hμν', hνμ']
  norm_num

/-- `(μ − ν, (μ − ν)^s) = [μ^s=μ] − [μ^s=ν] − [ν^s=μ] + [ν^s=ν]`. -/
private lemma scalarProduct_sub_conj_irr (c : Hyp11 G) (h12 : Hyp12 c)
    (μ ν : Irr (↥c.H0)) :
    scalarProduct (↥c.H0) (μ.1 - ν.1)
        (conjChar c.H0 (s_normalizes_H0 c h12) (μ.1 - ν.1)) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = μ.1 then 1 else 0)
        + (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 1 else 0) := by
  rw [conjChar_sub]
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
  rw [scalarProduct_conjChar_irr c h12 μ μ, scalarProduct_conjChar_irr c h12 μ ν,
    scalarProduct_conjChar_irr c h12 ν μ, scalarProduct_conjChar_irr c h12 ν ν]
  ring

/-- Members of a `Λ`-orbit have the same degree. -/
private lemma orbit_mem_degree_eq' (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν) : μ 1 = ν 1 := by
  rcases Finset.mem_image.mp hμ with ⟨l, hl, hEq⟩
  rw [← hEq]
  simp [LambdaChar]

/-- `(χ, χ) = 1` for `χ ∈ ±Irr(G)`. -/
private lemma scalarProduct_self_eq_one_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : scalarProduct G χ χ = 1 := by
  rcases hχ with hχ | hχ
  · exact scalarProduct_irreducible_self hχ
  · have h' : scalarProduct G (-χ) (-χ) = 1 := scalarProduct_irreducible_self hχ
    rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
    simpa using h'

/-- The induced class function of a class function is a class function. -/
private lemma isClassFunction_inducedClassFunction {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (δ : ClassFunction (↥H)) (hδ : IsClassFunction δ) :
    IsClassFunction (inducedClassFunction H δ) := by
  intro x g
  unfold inducedClassFunction
  congr 1
  refine Finset.sum_bij
    (fun z : G => fun _ : z ∈ (Finset.univ : Finset G) => g⁻¹ * z) ?_ ?_ ?_ ?_
  · intro z hz
    simp
  · intro a ha b hb hEq
    exact mul_left_cancel hEq
  · intro y hy
    refine ⟨g * y, by simp, ?_⟩
    group
  · intro z hz
    by_cases hzmem : z⁻¹ * (g * x * g⁻¹) * z ∈ H
    · have hmem' : (g⁻¹ * z)⁻¹ * x * (g⁻¹ * z) ∈ H := by
        have hEq : (g⁻¹ * z)⁻¹ * x * (g⁻¹ * z) = z⁻¹ * (g * x * g⁻¹) * z := by
          group
        rwa [hEq]
      have hEq : (g⁻¹ * z)⁻¹ * x * (g⁻¹ * z) = z⁻¹ * (g * x * g⁻¹) * z := by
        group
      rw [dif_pos hzmem, dif_pos hmem']
      congr 1
      apply Subtype.ext
      exact hEq.symm
    · have hnot : ¬ (g⁻¹ * z)⁻¹ * x * (g⁻¹ * z) ∈ H := by
        intro hmem
        apply hzmem
        have hEq : (g⁻¹ * z)⁻¹ * x * (g⁻¹ * z) = z⁻¹ * (g * x * g⁻¹) * z := by
          group
        rwa [← hEq]
      rw [dif_neg hzmem, dif_neg hnot]

/-- `inducedFromSub` of a class function is a class function. -/
private lemma isClassFunction_inducedFromSub {G : Type u} [Group G] [Fintype G]
    {H0 H : Subgroup G} (hH0 : H0 ≤ H) (δ : ClassFunction (↥H0))
    (hδ : IsClassFunction δ) : IsClassFunction (inducedFromSub hH0 δ) := by
  let K : Subgroup (↥H) := H0.subgroupOf H
  let δ' : ClassFunction (↥K) := fun x => δ ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  have hδ' : IsClassFunction δ' := by
    intro x g
    have hx : (x : G) ∈ H0 := Subgroup.mem_subgroupOf.mp x.2
    have hg : (g : G) ∈ H0 := Subgroup.mem_subgroupOf.mp g.2
    change δ ⟨(g : G) * (x : G) * (g : G)⁻¹, by
      exact H0.mul_mem (H0.mul_mem hg hx) (H0.inv_mem hg)⟩ = δ ⟨(x : G), hx⟩
    exact hδ ⟨(x : G), hx⟩ ⟨(g : G), hg⟩
  have hmain : IsClassFunction (inducedClassFunction K δ') :=
    isClassFunction_inducedClassFunction K δ' hδ'
  simpa [inducedFromSub, K, δ'] using hmain

/-- `(I, I) = 2 + [μ^s=μ] − [μ^s=ν] − [ν^s=μ] + [ν^s=ν]` for
`I = Ind(μ − ν)`, with `μ, ν` distinct irreducibles in the same `Λ`-orbit. -/
private lemma induced_pair_norm (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {μ ν : Irr (↥c.H0)}
    (hμν : μ.1 ∈ orbit c.H0 c.U ν.1) (hμνne : μ ≠ ν) :
    scalarProduct G (inducedClassFunction c.H0 (μ.1 - ν.1))
        (inducedClassFunction c.H0 (μ.1 - ν.1)) =
      2 + (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = μ.1 then 1 else 0)
        + (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 1 else 0) := by
  classical
  let δ : ClassFunction (↥c.H0) := μ.1 - ν.1
  have hδgen : IsGeneralizedCharacter δ := by
    dsimp [δ]
    exact ⟨μ.1, ν.1, isCharacter_of_isIrreducibleCharacter μ.2,
      isCharacter_of_isIrreducibleCharacter ν.2, rfl⟩
  have hδc : IsClassFunction δ := isClassFunction_of_isGeneralizedCharacter hδgen
  have hδT : supportedOn δ {x : ↥c.H0 | (x : G) ∈ c.T} := by
    simpa [δ] using supportedOn_T_of_orbit c h12 hμν
  have h13 := lemma_1_3 c h12 hδc hδc hδT hδT
  have h13₁ : scalarProduct G (inducedClassFunction c.H0 δ) (inducedClassFunction c.H0 δ) =
      scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 δ)
        (inducedFromSub (h12.H0_normal_in_H).1 δ) := h13.1
  have hfrob : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 δ)
        (inducedFromSub (h12.H0_normal_in_H).1 δ) =
      scalarProduct (↥c.H0) δ
        (fun x : ↥c.H0 => (inducedFromSub (h12.H0_normal_in_H).1 δ)
          ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩) := by
    exact frobenius_reciprocity_inducedFromSub (h12.H0_normal_in_H).1 δ
      (χ := inducedFromSub (h12.H0_normal_in_H).1 δ)
      (hχ := isClassFunction_inducedFromSub (h12.H0_normal_in_H).1 δ hδc)
  have hrest : (fun x : ↥c.H0 => (inducedFromSub (h12.H0_normal_in_H).1 δ)
        ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩) =
      δ + conjChar c.H0 (s_normalizes_H0 c h12) δ := by
    ext x
    have hxsh : c.s * (x : G) * c.s⁻¹ ∈ c.H0 := s_normalizes_H0 c h12 x
    have hpt := inducedFromSub_eq_add_conj_index_two c.H0 c.H (h12.H0_normal_in_H).1
      (H0_index c h12) (s_mem_H c) (s_not_mem_H0' c h12) δ hδc
      (h := (x : G)) (hh := x.2) (hsh := hxsh)
    simp [conjChar, conjMonoidHom, Pi.add_apply, hpt]
  rw [h13₁, hfrob, hrest]
  rw [scalarProduct_add_right]
  dsimp [δ]
  rw [scalarProduct_sub_irr_self hμνne]
  rw [scalarProduct_sub_conj_irr c h12 μ ν]
  ring

/-- Two distinct members of `B(χ)` lying in one `Λ`-orbit are conjugate
under `s`.  This is the paper's "proper subset consisting of conjugate
characters" (the Cauchy--Schwarz + value-at-`1` argument). -/
private lemma BOf_orbit_pair_conj (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {μ ν : Irr (↥c.H0)}
    (hμB : μ ∈ BOf c h12 χ) (hνB : ν ∈ BOf c h12 χ)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) (hμν : μ ≠ ν) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 := by
  classical
  by_contra hμsν
  set eμ : ℂ := scalarProduct G χ (tildeNu c h12 μ) with hEμ
  set eν : ℂ := scalarProduct G χ (tildeNu c h12 ν) with hEν
  have heμ : eμ = 1 ∨ eμ = -1 := by
    simpa [eμ] using BOf_scalar_eq_pm_one c h12 hχ hμB
  have heν : eν = 1 ∨ eν = -1 := by
    simpa [eν] using BOf_scalar_eq_pm_one c h12 hχ hνB
  have heμreal : star eμ = eμ := by
    rcases heμ with h | h <;> simp [h]
  have heνreal : star eν = eν := by
    rcases heν with h | h <;> simp [h]
  have heμsq : eμ * star eμ = 1 := by
    rcases heμ with h | h <;> simp [h]
  have heνsq : eν * star eν = 1 := by
    rcases heν with h | h <;> simp [h]
  have hA : normSq G (tildeNu c h12 μ) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 2 else 1) :=
    tildeNu_norm c h12 μ
  have hB : normSq G (tildeNu c h12 ν) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1) :=
    tildeNu_norm c h12 ν
  let I : ClassFunction G := inducedClassFunction c.H0 (μ.1 - ν.1)
  have hI : scalarProduct G I I =
      2 + (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = μ.1 then 1 else 0)
        + (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 1 else 0) := by
    change scalarProduct G (inducedClassFunction c.H0 (μ.1 - ν.1))
        (inducedClassFunction c.H0 (μ.1 - ν.1)) =
      2 + (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 then 1 else 0)
        - (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = μ.1 then 1 else 0)
        + (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 1 else 0)
    exact induced_pair_norm c h12 hμL hμν
  have hind : I = tildeNu c h12 μ - tildeNu c h12 ν := by
    change inducedClassFunction c.H0 (μ.1 - ν.1) = tildeNu c h12 μ - tildeNu c h12 ν
    exact tildeNu_ind c h12 hμL
  have hW' : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) =
      normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) -
        scalarProduct G (tildeNu c h12 μ - tildeNu c h12 ν)
          (tildeNu c h12 μ - tildeNu c h12 ν) := by
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    simp only [normSq]
    ring_nf
  have hW : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) =
      normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) -
        scalarProduct G I I := by
    have hEq : scalarProduct G (tildeNu c h12 μ - tildeNu c h12 ν)
          (tildeNu c h12 μ - tildeNu c h12 ν) = scalarProduct G I I :=
      congrArg (fun φ : ClassFunction G => scalarProduct G φ φ) hind.symm
    rw [← hEq]
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    simp only [normSq]
    ring_nf
  have hW0 : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 0 := by
    rw [hW, hI]
    by_cases hνμ : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = μ.1
    · exfalso
      apply hμsν
      calc
        conjChar c.H0 (s_normalizes_H0 c h12) μ.1
            = conjChar c.H0 (s_normalizes_H0 c h12)
                (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) := by rw [hνμ]
        _ = ν.1 := conjChar_involution c h12 ν.1
    · by_cases hμμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1
      · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
        · rw [hA, hB]
          simp [hμsν, hνμ]
          simp [hμμ, hνν]
          try norm_num
        · rw [hA, hB]
          simp [hμsν, hνμ]
          simp [hμμ, hνν]
          try norm_num
      · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
        · rw [hA, hB]
          simp [hμsν, hνμ]
          simp [hμμ, hνν]
          try norm_num
        · rw [hA, hB]
          simp [hμsν, hνμ]
          simp [hμμ, hνν]
          try norm_num
  set ξ : ClassFunction G := eμ • tildeNu c h12 μ + eν • tildeNu c h12 ν with hξDef
  have hξξ : scalarProduct G ξ ξ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
    rw [hξDef]
    rcases heμ with hμ1 | hμm
    · rcases heν with hν1 | hνm
      · rw [hμ1, hν1]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
      · rw [hμ1, hνm]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        simp only [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              -scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (-scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) -
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
    · rcases heν with hν1 | hνm
      · rw [hμm, hν1]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        simp only [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              -scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (-scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) -
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
      · rw [hμm, hνm]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        simp only [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
  have hχξ : scalarProduct G χ ξ = 2 := by
    rw [hξDef]
    rw [scalarProduct_add_right]
    simp only [scalarProduct_smul_right]
    rw [← hEμ, ← hEν]
    rw [heμreal, heνreal]
    have heμsq2 : eμ * eμ = 1 := by rcases heμ with h | h <;> simp [h]
    have heνsq2 : eν * eν = 1 := by rcases heν with h | h <;> simp [h]
    rw [heμsq2, heνsq2]
    norm_num
  have hξχ : scalarProduct G ξ χ = 2 := by
    have h' := scalarProduct_conj χ ξ
    rw [hχξ] at h'
    norm_num at h'
    exact h'.symm
  have hdiff : scalarProduct G (ξ - (2 : ℂ) • χ) (ξ - (2 : ℂ) • χ) =
      scalarProduct G ξ ξ - 4 := by
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    rw [scalarProduct_smul_left, scalarProduct_smul_right, scalarProduct_smul_left,
      scalarProduct_smul_right]
    rw [hξχ, hχξ, scalarProduct_self_eq_one_of_isPMIrr hχ]
    norm_num
  have hcs : 0 ≤ (scalarProduct G (ξ - (2 : ℂ) • χ) (ξ - (2 : ℂ) • χ)).re := by
    simpa [normSq] using normSq_nonneg (ξ - (2 : ℂ) • χ)
  have hξξ4c : 0 ≤ (scalarProduct G ξ ξ - 4).re := by
    rw [hdiff] at hcs
    exact hcs
  have hξξ_vals : scalarProduct G ξ ξ = 2 ∨ scalarProduct G ξ ξ = 3 ∨
      scalarProduct G ξ ξ = 4 := by
    rw [hξξ, hA, hB]
    by_cases hμμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1
    · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
      · right; right; simp [hμμ, hνν]; norm_num
      · right; left; simp [hμμ, hνν]; norm_num
    · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
      · right; left; simp [hμμ, hνν]; norm_num
      · left; simp [hμμ, hνν]; norm_num
  have hξξ4 : scalarProduct G ξ ξ = 4 := by
    rcases hξξ_vals with h2 | h3 | h4
    · exfalso
      have h' : (scalarProduct G ξ ξ - 4).re = -2 := by rw [h2]; norm_num
      rw [h'] at hξξ4c
      norm_num at hξξ4c
    · exfalso
      have h' : (scalarProduct G ξ ξ - 4).re = -1 := by rw [h3]; norm_num
      rw [h'] at hξξ4c
      norm_num at hξξ4c
    · exact h4
  have hμμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
    by_contra hμμ
    have hA1 : normSq G (tildeNu c h12 μ) = 1 := by rw [hA]; simp [hμμ]
    rw [hξξ, hA1, hB] at hξξ4
    by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
    · simp [hνν] at hξξ4
      norm_num at hξξ4
    · simp [hνν] at hξξ4
      norm_num at hξξ4
  have hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
    by_contra hνν
    have hB1 : normSq G (tildeNu c h12 ν) = 1 := by rw [hB]; simp [hνν]
    rw [hξξ, hA, hB1] at hξξ4
    simp [hμμ] at hξξ4
    norm_num at hξξ4
  have hA2 : normSq G (tildeNu c h12 μ) = 2 := by rw [hA]; simp [hμμ]
  have hB2 : normSq G (tildeNu c h12 ν) = 2 := by rw [hB]; simp [hνν]
  have hξeq : ξ = (2 : ℂ) • χ := by
    have hd0 : scalarProduct G (ξ - (2 : ℂ) • χ) (ξ - (2 : ℂ) • χ) = 0 := by
      rw [hdiff, hξξ4]
      norm_num
    have hφ0 : ξ - (2 : ℂ) • χ = 0 := (normSq_eq_zero_iff (ξ - (2 : ℂ) • χ)).1 hd0
    exact sub_eq_zero.mp hφ0
  set η : ClassFunction G := tildeNu c h12 μ - eμ • χ with hηDef
  have hηgen : IsGeneralizedCharacter η := by
    rw [hηDef]
    have heμχgen : IsGeneralizedCharacter (eμ • χ) := by
      rcases heμ with h | h
      · rw [h]
        simpa using isGeneralizedCharacter_of_isPMIrr hχ
      · rw [h]
        have hχneg_gen : IsGeneralizedCharacter (-χ) := by
          exact isGeneralizedCharacter_of_isPMIrr (hχ.elim (fun hh => Or.inr (by simpa using hh))
            (fun hh => Or.inl hh))
        simpa using hχneg_gen
    exact isGeneralizedCharacter_sub (tildeNu_isGeneralized c h12 μ) heμχgen
  have hmuChi : scalarProduct G (tildeNu c h12 μ) χ = eμ := by
    have h' := scalarProduct_conj χ (tildeNu c h12 μ)
    change star eμ = scalarProduct G (tildeNu c h12 μ) χ at h'
    rw [heμreal] at h'
    exact h'.symm
  have hηη : scalarProduct G η η = 1 := by
    rw [hηDef]
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    rw [scalarProduct_smul_left, scalarProduct_smul_right]
    rw [show scalarProduct G (eμ • χ) (eμ • χ) =
        eμ * (star eμ * scalarProduct G χ χ) from by
          rw [scalarProduct_smul_left, scalarProduct_smul_right]
          ring]
    have hAA : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) = 2 := by
      rw [← normSq]
      exact hA2
    rw [hAA, ← hEμ, heμreal, hmuChi, scalarProduct_self_eq_one_of_isPMIrr hχ]
    have heμsq2 : eμ * eμ = 1 := by rcases heμ with h | h <;> simp [h]
    simp [heμsq2]
    norm_num
  rcases norm_one_signed_irreducible hηgen hηη with ⟨ψ, hψ, hψeq⟩
  have hη1 : η 1 ≠ 0 := by
    rcases hψeq with h | h
    · rw [h]
      exact irreducible_char_one_ne_zero hψ
    · rw [h]
      have hψ1 : ψ 1 ≠ 0 := irreducible_char_one_ne_zero hψ
      simpa using neg_ne_zero.mpr hψ1
  have hχ1 : χ 1 ≠ 0 := by
    rcases hχ with h | h
    · exact irreducible_char_one_ne_zero h
    · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero h
      simpa using h'
  have hmu1 : tildeNu c h12 μ 1 = η 1 + eμ * χ 1 := by
    have hmu : tildeNu c h12 μ = η + eμ • χ := by
      rw [hηDef]
      abel
    have h' := congrFun hmu 1
    simpa [Pi.add_apply, Pi.smul_apply] using h'
  have hξ2χ : eμ • tildeNu c h12 μ + eν • tildeNu c h12 ν = (2 : ℂ) • χ := by
    simpa [hξDef] using hξeq
  have hnu1 : tildeNu c h12 ν 1 = eν * (χ 1 - eμ * η 1) := by
    have hpt := congrFun hξ2χ 1
    simp only [Pi.add_apply, Pi.smul_apply] at hpt
    simp at hpt
    rw [hmu1] at hpt
    have heμsq2 : eμ * eμ = 1 := by rcases heμ with h | h <;> simp [h]
    have heνsq2 : eν * eν = 1 := by rcases heν with h | h <;> simp [h]
    rcases heμ with hμ1 | hμm
    · rcases heν with hν1 | hνm
      · rw [hμ1, hν1] at hpt ⊢
        simp at hpt ⊢
        linear_combination hpt
      · rw [hμ1, hνm] at hpt ⊢
        simp at hpt ⊢
        linear_combination -hpt
    · rcases heν with hν1 | hνm
      · rw [hμm, hν1] at hpt ⊢
        simp at hpt ⊢
        linear_combination hpt
      · rw [hμm, hνm] at hpt ⊢
        simp at hpt ⊢
        linear_combination -hpt
  have hI1 : inducedClassFunction c.H0 (μ.1 - ν.1) 1 = 0 := by
    unfold inducedClassFunction
    have hsum : (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then
          (μ.1 - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0) =
        (Nat.card G : ℂ) * (μ.1 1 - ν.1 1) := by
      calc
        (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ.1 - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0)
            = ∑ x : G, (μ.1 - ν.1) ⟨1, by simp⟩ := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hmem : x⁻¹ * 1 * x ∈ c.H0 := by simp
                rw [dif_pos hmem]
                apply congrArg (μ.1 - ν.1)
                apply Subtype.ext
                simp
        _ = (Nat.card G : ℂ) * (μ.1 1 - ν.1 1) := by
              change (∑ x : G, (μ.1 - ν.1) 1) = (Nat.card G : ℂ) * (μ.1 1 - ν.1 1)
              simp [Pi.sub_apply, Nat.card_eq_fintype_card]
              ring
    rw [hsum]
    have hdeg : μ.1 1 = ν.1 1 := orbit_mem_degree_eq' c hμL
    simp [hdeg]
  have hI1' : tildeNu c h12 μ 1 - tildeNu c h12 ν 1 = 0 := by
    have h' := congrFun (tildeNu_ind c h12 hμL) (1 : G)
    rw [hI1] at h'
    exact h'.symm
  have hmain : (eμ - eν) * χ 1 + (1 + eμ * eν) * η 1 = 0 := by
    rw [← hI1']
    rw [hmu1, hnu1]
    ring
  rcases heμ with hμ1 | hμm
  · rcases heν with hν1 | hνm
    · rw [hμ1, hν1] at hmain
      have h' : (2 : ℂ) * η 1 = 0 := by linear_combination hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hη1 ((mul_eq_zero.mp h').resolve_left h2ne)
    · rw [hμ1, hνm] at hmain
      have h' : (2 : ℂ) * χ 1 = 0 := by linear_combination hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hχ1 ((mul_eq_zero.mp h').resolve_left h2ne)
  · rcases heν with hν1 | hνm
    · rw [hμm, hν1] at hmain
      have h' : (2 : ℂ) * χ 1 = 0 := by linear_combination (-1) * hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hχ1 ((mul_eq_zero.mp h').resolve_left h2ne)
    · rw [hμm, hνm] at hmain
      have h' : (2 : ℂ) * η 1 = 0 := by linear_combination hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hη1 ((mul_eq_zero.mp h').resolve_left h2ne)

/-- `χ(1) ≠ 0` for `χ ∈ ±Irr(G)`. -/
private lemma chi_one_ne_zero_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G}
    (hχ : IsPMIrr G χ) : χ 1 ≠ 0 := by
  rcases hχ with h | h
  · exact irreducible_char_one_ne_zero h
  · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero h
    simpa using h'

/-- `Σ_G |χ|² = |G|` for `χ ∈ ±Irr(G)`. -/
private lemma sum_normSq_eq_card {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    (∑ x : G, Complex.normSq (χ x)) = (Nat.card G : ℝ) := by
  classical
  have hsp : scalarProduct G χ χ = 1 := scalarProduct_self_eq_one_of_isPMIrr hχ
  have hc : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hS : (∑ x : G, χ x * star (χ x)) = (Nat.card G : ℂ) := by
    have hmul := congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) hsp
    unfold scalarProduct at hmul
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at hmul
    simpa using hmul
  have hc' : (∑ x : G, (Complex.normSq (χ x) : ℂ)) = (Nat.card G : ℂ) := by
    calc
      (∑ x : G, (Complex.normSq (χ x) : ℂ)) = ∑ x : G, χ x * star (χ x) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact (Complex.mul_conj (χ x)).symm
      _ = (Nat.card G : ℂ) := hS
  have hc'' : (↑(∑ x : G, Complex.normSq (χ x)) : ℂ) = (Nat.card G : ℂ) := by
    simpa using hc'
  exact_mod_cast hc''

/-- Strict TI inequality: `Σ_{x∈T} |χ(x)|² < |H|` for `χ ∈ ±Irr(G)`.
Fiber counting with the TI-set `T = H0 ∖ U` (normalizer `H`), strict loss
at `1 ∉ T`. -/
private lemma TI_sum_lt_card (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    (∑ x ∈ (Finset.univ.filter (fun x : G => x ∈ c.T)), Complex.normSq (χ x)) <
      (Nat.card (↥c.H) : ℝ) := by
  classical
  let TF : Finset G := Finset.univ.filter (fun x : G => x ∈ c.T)
  let f : G → ℝ := fun x => Complex.normSq (χ x)
  have hχc : IsClassFunction χ :=
    isClassFunction_of_isGeneralizedCharacter (isGeneralizedCharacter_of_isPMIrr hχ)
  have hf : ∀ g x : G, f (g * x * g⁻¹) = f x := by
    intro g x
    simp [f, hχc x g]
  have hf_nonneg : ∀ x : G, 0 ≤ f x := fun x => Complex.normSq_nonneg (χ x)
  have hf1pos : 0 < f 1 := by
    have hχ1 : χ 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ
    exact Complex.normSq_pos.mpr hχ1
  have h1notT : (1 : G) ∉ c.T := by
    simp [Hyp11.T]
  have : c.H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rcases Subgroup.exists_leftTransversal_of_FiniteIndex (D := c.H) (H := ⊤)
      (by simp) with ⟨t, hcomp, hcover⟩
  have hcover' : ⋃ x ∈ t, (x : G) • (c.H : Set G) = Set.univ := by
    simpa using hcover
  have hcard_t : t.card = c.H.index := by
    have hc1 : Nat.card (↥(⊤ : Subgroup G)) = Nat.card G := Subgroup.card_top
    have hc2 := Subgroup.IsComplement.card_mul_card hcomp
    -- `hc2 : Nat.card ↑(t : Set ↥⊤) * Nat.card ↑(c.H.subgroupOf ⊤ : Set ↥⊤) = Nat.card ↥⊤`
    have hc2' : t.card * Nat.card (↥c.H) = Nat.card G := by
      -- convert the set-cardinalities
      have hS : Nat.card {x : ↥(⊤ : Subgroup G) // x ∈ (t : Set (↥(⊤ : Subgroup G)))} = t.card := by
        simp [Nat.card_eq_fintype_card]
      have hT : Nat.card {x : ↥(⊤ : Subgroup G) // x ∈ ((c.H).subgroupOf ⊤ : Set (↥(⊤ : Subgroup G)))} =
          Nat.card (↥c.H) := by
        exact Nat.card_congr {
          toFun := fun x => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
          invFun := fun y => ⟨⟨(y : G), by simp⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
          left_inv := by intro x; apply Subtype.ext; rfl
          right_inv := by intro y; apply Subtype.ext; rfl }
      change Nat.card {x : ↥(⊤ : Subgroup G) // x ∈ (t : Set (↥(⊤ : Subgroup G)))} *
          Nat.card {x : ↥(⊤ : Subgroup G) // x ∈ ((c.H).subgroupOf ⊤ : Set (↥(⊤ : Subgroup G)))} =
        Nat.card (↥(⊤ : Subgroup G)) at hc2
      rw [hS, hT, hc1] at hc2
      simpa [mul_comm] using hc2
    have hEq : t.card * Nat.card (↥c.H) = Nat.card (↥c.H) * c.H.index := by
      calc
        t.card * Nat.card (↥c.H) = Nat.card G := hc2'
        _ = Nat.card (↥c.H) * c.H.index := (Subgroup.card_mul_index c.H).symm
    have hm : Nat.card (↥c.H) ≠ 0 := (Nat.card_pos (α := ↥c.H)).ne'
    have hEq' : Nat.card (↥c.H) * t.card = Nat.card (↥c.H) * c.H.index := by
      simpa [mul_comm] using hEq
    exact Nat.mul_left_cancel (Nat.pos_iff_ne_zero.mpr hm) hEq'
  have hleft_distinct : ∀ x₁ : ↥(⊤ : Subgroup G), x₁ ∈ t → ∀ x₂ : ↥(⊤ : Subgroup G),
      x₂ ∈ t → x₁ ≠ x₂ → (x₁ : G)⁻¹ * (x₂ : G) ∉ c.H := by
    intro x₁ hx₁ x₂ hx₂ hne hmem
    apply hne
    let u₁ : (t : Set (↥(⊤ : Subgroup G))) := ⟨(x₁ : ↥(⊤ : Subgroup G)), hx₁⟩
    let u₂ : (t : Set (↥(⊤ : Subgroup G))) := ⟨(x₂ : ↥(⊤ : Subgroup G)), hx₂⟩
    let h2 : ↥((c.H).subgroupOf (⊤ : Subgroup G)) :=
      ⟨(x₂ : ↥(⊤ : Subgroup G))⁻¹ * (x₁ : ↥(⊤ : Subgroup G)),
        by
          rw [Subgroup.mem_subgroupOf]
          change (x₂ : G)⁻¹ * (x₁ : G) ∈ c.H
          simpa [mul_inv_rev] using (c.H.inv_mem hmem)⟩
    have hEq := hcomp.existsUnique x₁
    rcases hEq with ⟨p, hp, huniq⟩
    have hpair2 : (u₂ : ↥(⊤ : Subgroup G)) * (h2 : ↥(⊤ : Subgroup G)) = x₁ := by
      change (x₂ : ↥(⊤ : Subgroup G)) * (h2 : ↥(⊤ : Subgroup G)) = x₁
      dsimp [h2]
      apply Subtype.ext
      change (x₂ : G) * ((x₂ : G)⁻¹ * (x₁ : G)) = x₁
      simp
    have hpair1 : (u₁ : ↥(⊤ : Subgroup G)) * (1 : ↥((c.H).subgroupOf (⊤ : Subgroup G))) = x₁ := by
      simp [u₁]
    have hEqp : (u₁, (1 : ↥((c.H).subgroupOf (⊤ : Subgroup G)))) = p :=
      huniq (u₁, (1 : ↥((c.H).subgroupOf (⊤ : Subgroup G)))) hpair1
    have hEqp' : (u₂, h2) = p := huniq (u₂, h2) hpair2
    have hEqx : u₁ = u₂ := by
      exact congrArg Prod.fst (hEqp.trans hEqp'.symm)
    exact congrArg Subtype.val hEqx
  have hdisj_conj : ∀ x₁ : ↥(⊤ : Subgroup G), x₁ ∈ t → ∀ x₂ : ↥(⊤ : Subgroup G),
      x₂ ∈ t → x₁ ≠ x₂ →
      (fun y : G => (x₁ : G) * y * (x₁ : G)⁻¹) '' c.T ∩
        (fun y : G => (x₂ : G) * y * (x₂ : G)⁻¹) '' c.T = ∅ := by
    intro x₁ hx₁ x₂ hx₂ hne
    ext y
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false]
    apply iff_false_intro
    rintro ⟨⟨t₁, ht₁, hEq₁⟩, ⟨t₂, ht₂, hEq₂⟩⟩
    have hmemT : (x₁ : G)⁻¹ * (x₂ : G) ∈ c.H := by
      rw [← h12.T_normalizer]
      rw [Subgroup.mem_normalizer_iff_conj_image_eq]
      have hneq : (c.T ∩ (fun t : G => (x₁ : G)⁻¹ * (x₂ : G) * t *
          ((x₁ : G)⁻¹ * (x₂ : G))⁻¹) '' c.T).Nonempty := by
        refine ⟨t₁, ht₁, ?_⟩
        -- t₁ = (x₁⁻¹x₂) t₂ (x₁⁻¹x₂)⁻¹ from the two equalities
        refine ⟨t₂, ht₂, ?_⟩
        calc
          (x₁ : G)⁻¹ * (x₂ : G) * t₂ * ((x₁ : G)⁻¹ * (x₂ : G))⁻¹
              = (x₁ : G)⁻¹ * (x₂ * t₂ * (x₂ : G)⁻¹) * (x₁ : G) := by group
          _ = (x₁ : G)⁻¹ * y * (x₁ : G) := by rw [hEq₂]
          _ = t₁ := by
                calc
                  (x₁ : G)⁻¹ * y * (x₁ : G) = (x₁ : G)⁻¹ * (x₁ * t₁ * (x₁ : G)⁻¹) * (x₁ : G) := by rw [hEq₁]
                  _ = t₁ := by group
      rcases h12.T_is_TI ((x₁ : G)⁻¹ * (x₂ : G)) with hEqT | hDisjT
      · exact hEqT
      · rw [hDisjT] at hneq
        rcases hneq with ⟨w, hw⟩
        exact False.elim (by simpa using hw)
    exact hleft_distinct x₁ hx₁ x₂ hx₂ hne hmemT
  have h1not_conj : ∀ x : ↥(⊤ : Subgroup G),
      (1 : G) ∉ (fun y : G => (x : G) * y * (x : G)⁻¹) '' c.T := by
    intro x h
    rcases h with ⟨y, hyT, hEq⟩
    have hy1 : y = 1 := by
      calc
        y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
        _ = 1 := by simpa [hEq]
    exact h1notT (hy1 ▸ hyT)
  let Sx : ↥(⊤ : Subgroup G) → Finset G := fun x => Finset.univ.filter (fun y : G =>
    y ∈ (fun t : G => (x : G) * t * (x : G)⁻¹) '' c.T)
  have hSx_eq : ∀ x : ↥(⊤ : Subgroup G), (∑ y ∈ Sx x, f y) = ∑ y ∈ TF, f y := by
    intro x
    refine Finset.sum_bij (fun y : G => fun _ : y ∈ Sx x =>
        (x : G)⁻¹ * y * (x : G)) ?_ ?_ ?_ ?_
    · intro y hy
      rcases (by simpa [Sx, TF] using hy) with ⟨t, ht, hEq⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hEq' : (x : G)⁻¹ * y * (x : G) = t := by
        calc
          (x : G)⁻¹ * y * (x : G) = (x : G)⁻¹ * ((x : G) * t * (x : G)⁻¹) * (x : G) := by rw [hEq]
          _ = t := by group
      rwa [hEq']
    · intro a ha b hb hEq
      have h1 : (x : G) * ((x : G)⁻¹ * a * (x : G)) * (x : G)⁻¹ =
          (x : G) * ((x : G)⁻¹ * b * (x : G)) * (x : G)⁻¹ := by rw [hEq]
      group at h1
      exact h1
    · intro t ht
      refine ⟨(x : G) * t * (x : G)⁻¹, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · exact ⟨t, (Finset.mem_filter.mp ht).2, rfl⟩
      · group
    · intro y hy
      simpa using (hf (x : G)⁻¹ y).symm
  have hdisjSx : (↑t : Set (↥(⊤ : Subgroup G))).PairwiseDisjoint Sx := by
    intro x₁ hx₁ x₂ hx₂ hne
    change Disjoint (Sx x₁) (Sx x₂)
    rw [Finset.disjoint_left (s := Sx x₁) (t := Sx x₂)]
    intro y hy₁ hy₂
    have hmem₁ : y ∈ (fun t : G => (x₁ : G) * t * (x₁ : G)⁻¹) '' c.T :=
      (Finset.mem_filter.mp hy₁).2
    have hmem₂ : y ∈ (fun t : G => (x₂ : G) * t * (x₂ : G)⁻¹) '' c.T :=
      (Finset.mem_filter.mp hy₂).2
    have hz' : y ∈ (∅ : Set G) := by
      exact (hdisj_conj x₁ hx₁ x₂ hx₂ hne) ▸ (⟨hmem₁, hmem₂⟩ :
        y ∈ (fun y : G => (x₁ : G) * y * (x₁ : G)⁻¹) '' c.T ∩
          (fun y : G => (x₂ : G) * y * (x₂ : G)⁻¹) '' c.T)
    exact False.elim (by simpa using hz')
  let U : Finset G := t.biUnion Sx
  have h1notU : (1 : G) ∉ U := by
    intro h
    rw [Finset.mem_biUnion] at h
    rcases h with ⟨x, hx, h1⟩
    exact h1not_conj x (Finset.mem_filter.mp h1).2
  have hU_sum : (∑ y ∈ U, f y) = ∑ x ∈ t, ∑ y ∈ Sx x, f y := by
    simpa [U] using Finset.sum_biUnion (s := t) (t := Sx) (f := f) hdisjSx
  have hU1_sum : (∑ y ∈ U ∪ ({1} : Finset G), f y) = (∑ y ∈ U, f y) + f 1 := by
    rw [Finset.sum_union]
    · simp
    · rw [Finset.disjoint_left]
      intro y hy hys
      have hy1 : y = 1 := Finset.mem_singleton.mp hys
      exact h1notU (hy1 ▸ hy)
  have hle_total : (∑ y ∈ U ∪ ({1} : Finset G), f y) ≤ ∑ y : G, f y := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro y hy
      simp
    · intro y hy hy'
      exact hf_nonneg y
  have hmain_ineq : (∑ x ∈ t, ∑ y ∈ Sx x, f y) + f 1 ≤ (∑ y : G, f y) := by
    calc
      (∑ x ∈ t, ∑ y ∈ Sx x, f y) + f 1 = (∑ y ∈ U, f y) + f 1 := by rw [hU_sum]
      _ = ∑ y ∈ U ∪ ({1} : Finset G), f y := hU1_sum.symm
      _ ≤ ∑ y : G, f y := hle_total
  have hsum_eq : (∑ x ∈ t, ∑ y ∈ Sx x, f y) = (t.card : ℝ) * ∑ y ∈ TF, f y := by
    calc
      (∑ x ∈ t, ∑ y ∈ Sx x, f y) = ∑ x ∈ t, (∑ y ∈ TF, f y) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hSx_eq x
      _ = (t.card : ℝ) * (∑ y ∈ TF, f y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hGsum : (∑ y : G, f y) = (Nat.card G : ℝ) := by
    simpa [f] using sum_normSq_eq_card hχ
  have hlt : (t.card : ℝ) * (∑ y ∈ TF, f y) < (Nat.card G : ℝ) := by
    have h2 : (t.card : ℝ) * (∑ y ∈ TF, f y) + f 1 ≤ (Nat.card G : ℝ) := by
      rw [hsum_eq] at hmain_ineq
      rwa [hGsum] at hmain_ineq
    nlinarith
  have hcard_real : (t.card : ℝ) = (c.H.index : ℝ) := by exact_mod_cast hcard_t
  have hindex : (Nat.card (↥c.H) : ℝ) * (c.H.index : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast (Subgroup.card_mul_index c.H)
  have hidx_pos : 0 < (c.H.index : ℝ) := by
    have hne : c.H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact_mod_cast (Nat.pos_iff_ne_zero.mpr hne)
  have hlt' : (c.H.index : ℝ) * (∑ y ∈ TF, f y) < (Nat.card G : ℝ) := by
    rwa [hcard_real] at hlt
  have : (∑ y ∈ TF, f y) < (Nat.card (↥c.H) : ℝ) := by
    have hdiv : (Nat.card G : ℝ) / (c.H.index : ℝ) = (Nat.card (↥c.H) : ℝ) := by
      field_simp [ne_of_gt hidx_pos]
      rw [← hindex]
      ring
    have hlt'' : (∑ y ∈ TF, f y) < (Nat.card G : ℝ) / (c.H.index : ℝ) := by
      nlinarith
    rwa [hdiv] at hlt''
  simpa [TF] using this

/-- `Σ_{x∈T} δ1(x)·conj(δ2(x)) = |H0|·(δ1,δ2)_{H0} − |U|·(δ1|_U,δ2|_U)_U`
for class functions on `H0` (the combinatorial identity behind Theorem 3.2;
`T = H0 ∖ U`). -/
private lemma T_sum_scalarProduct (c : Hyp11 G) (h12 : Hyp12 c)
    (δ1 δ2 : ClassFunction (↥c.H0)) :
    (∑ x : ↥c.H0, if (x : G) ∈ c.T then δ1 x * star (δ2 x) else 0) =
      (Nat.card (↥c.H0) : ℂ) * scalarProduct (↥c.H0) δ1 δ2 -
        (Nat.card (↥c.U) : ℂ) * scalarProduct (↥c.U)
          (restrictU c h12 δ1) (restrictU c h12 δ2) := by
  classical
  let f : ↥c.H0 → ℂ := fun x => δ1 x * star (δ2 x)
  have hsumU : (∑ u : ↥c.U, f ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩) =
      (Nat.card (↥c.U) : ℂ) * scalarProduct (↥c.U)
        (restrictU c h12 δ1) (restrictU c h12 δ2) := by
    rw [scalarProduct]
    have hcard : (Nat.card (↥c.U) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := ↥c.U)).ne'
    field_simp [hcard]
    ring_nf
    rfl
  have hsplit : (∑ x : ↥c.H0, if (x : G) ∈ c.T then f x else 0) =
      (∑ x : ↥c.H0, f x) - ∑ u : ↥c.U, f ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ := by
    -- `if x ∈ T then f x else 0 = f x - if x ∈ U then f x else 0` pointwise
    have hpoint : ∀ x : ↥c.H0,
        (if (x : G) ∈ c.T then f x else 0) =
          f x - if (x : G) ∈ c.U then f x else 0 := by
      intro x
      by_cases hxU : (x : G) ∈ c.U
      · have hxT : ¬ (x : G) ∈ c.T := by
          intro hxT
          exact hxT.2 hxU
        simp [hxU, hxT]
      · have hxT : (x : G) ∈ c.T := by
          dsimp [Hyp11.T]
          simp [Set.mem_diff, x.2, hxU]
        simp [hxU, hxT]
    calc
      (∑ x : ↥c.H0, if (x : G) ∈ c.T then f x else 0)
          = ∑ x : ↥c.H0, (f x - if (x : G) ∈ c.U then f x else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact hpoint x
      _ = (∑ x : ↥c.H0, f x) -
          ∑ x : ↥c.H0, (if (x : G) ∈ c.U then f x else 0) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ x : ↥c.H0, f x) - ∑ u : ↥c.U, f ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ := by
            congr 1
            have hEq : (∑ x : ↥c.H0, (if (x : G) ∈ c.U then f x else 0)) =
                ∑ u : ↥c.U, f ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ := by
              let SU : Finset (↥c.H0) := Finset.univ.filter (fun x : ↥c.H0 => (x : G) ∈ c.U)
              have hLHS : (∑ x : ↥c.H0, (if (x : G) ∈ c.U then f x else 0)) =
                  ∑ x ∈ SU, f x := by
                change (∑ x : ↥c.H0, (if (x : G) ∈ c.U then f x else 0)) =
                  ∑ x ∈ (Finset.univ.filter (fun x : ↥c.H0 => (x : G) ∈ c.U)), f x
                exact (Finset.sum_filter (s := Finset.univ)
                  (p := fun x : ↥c.H0 => (x : G) ∈ c.U) f).symm
              have hRHS : (∑ x ∈ SU, f x) =
                  ∑ u : ↥c.U, f ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ := by
                refine Finset.sum_bij (fun x : ↥c.H0 => fun hx : x ∈ SU =>
                    (⟨(x : G), (Finset.mem_filter.mp hx).2⟩ : ↥c.U)) ?_ ?_ ?_ ?_
                · intro x hx
                  simp
                · intro x₁ hx₁ x₂ hx₂ hEq
                  apply Subtype.ext
                  exact congrArg (fun y : ↥c.U => (y : G)) hEq
                · intro u hu
                  refine ⟨⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩, ?_, ?_⟩
                  · rw [Finset.mem_filter]
                    exact ⟨Finset.mem_univ _, u.2⟩
                  · apply Subtype.ext
                    rfl
                · intro x hx
                  rfl
              exact hLHS.trans hRHS
            exact hEq
  calc
    (∑ x : ↥c.H0, if (x : G) ∈ c.T then δ1 x * star (δ2 x) else 0)
        = (∑ x : ↥c.H0, f x) - ∑ u : ↥c.U, f ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ := by
          simpa [f] using hsplit
    _ = (Nat.card (↥c.H0) : ℂ) * scalarProduct (↥c.H0) δ1 δ2 -
          (Nat.card (↥c.U) : ℂ) * scalarProduct (↥c.U)
            (restrictU c h12 δ1) (restrictU c h12 δ2) := by
          rw [hsumU]
          congr 1
          rw [scalarProduct]
          have hcard : (Nat.card (↥c.H0) : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.card_pos (α := ↥c.H0)).ne'
          field_simp [hcard]
          ring_nf
          rfl

/-- A `Λ`-orbit is nonempty. -/
private lemma orbitSet_mem_nonempty' (c : Hyp11 G)
    {L : Finset (ClassFunction (↥c.H0))}
    (hL : L ∈ ((Finset.univ : Finset (Irr (↥c.H0))).image
      (fun ν : Irr (↥c.H0) => orbit c.H0 c.U ν.1))) :
    L.Nonempty := by
  classical
  rcases Finset.mem_image.mp hL with ⟨ν, hν, hLν⟩
  refine ⟨ν.1, ?_⟩
  rw [← hLν]
  exact orbit_self_mem' c ν.1

/- A system of orbit representatives for the `Λ`-orbits of `Irr(H0)` (a
re-derivation of the Lemma-2.4 helper, using only public API). -/
private lemma exists_orbit_reps' (c : Hyp11 G) (h12 : Hyp12 c) :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → ClassFunction (↥c.H0)),
      (∀ i : ι, IsIrreducibleCharacter (rep i)) ∧
      (∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i)) := by
  classical
  let orbitSet : Finset (Finset (ClassFunction (↥c.H0))) :=
    (Finset.univ : Finset (Irr (↥c.H0))).image
      (fun ν : Irr (↥c.H0) => orbit c.H0 c.U ν.1)
  let ι : Type u := {L : Finset (ClassFunction (↥c.H0)) // L ∈ orbitSet}
  let rep : ι → ClassFunction (↥c.H0) := fun L =>
    Classical.choose (orbitSet_mem_nonempty' c L.2)
  have rep_mem (L : ι) : rep L ∈ L.1 :=
    Classical.choose_spec (orbitSet_mem_nonempty' c L.2)
  refine ⟨ι, inferInstance, rep, ?_, ?_⟩
  · intro L
    rcases Finset.mem_image.mp L.2 with ⟨ν, hν, hLν⟩
    have hνL' : rep L ∈ orbit c.H0 c.U ν.1 := hLν ▸ rep_mem L
    exact orbit_mem_isIrreducible c.H0 c.U ν.2 hνL'
  · intro ν
    refine ⟨⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩, ?_, ?_⟩
    · have hspec : rep ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩ ∈
          orbit c.H0 c.U ν.1 :=
        rep_mem ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩
      change ν.1 ∈ orbit c.H0 c.U
        (rep ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩)
      rw [orbit_eq_of_mem' c hspec]
      exact orbit_self_mem' c ν.1
    · intro L hLmem
      apply Subtype.ext
      have hEqOrbit : L.1 = orbit c.H0 c.U ν.1 := by
        rcases Finset.mem_image.mp L.2 with ⟨μ, hμ, hLμ⟩
        have hspecL : rep L ∈ L.1 := rep_mem L
        have ho1 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U ν.1 :=
          (orbit_eq_of_mem' c hLmem).symm
        have ho2 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U μ.1 := by
          rw [← hLμ] at hspecL
          exact orbit_eq_of_mem' c hspecL
        have ho3 : orbit c.H0 c.U μ.1 = L.1 := hLμ
        rw [← ho1, ho2, ho3]
      exact hEqOrbit

/-- `Σ_{μ,ν∈s} a μ · a ν · c = c · (Σ_{ν∈s} a ν)²`. -/
private lemma sum_pair_const_factor {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ℂ) :
    (∑ μ ∈ s, ∑ ν ∈ s, a μ * a ν * c) = c * (∑ ν ∈ s, a ν) ^ 2 := by
  calc
    (∑ μ ∈ s, ∑ ν ∈ s, a μ * a ν * c)
        = ∑ μ ∈ s, c * (∑ ν ∈ s, a μ * a ν) := by
            refine Finset.sum_congr rfl ?_
            intro μ hμ
            calc
              (∑ ν ∈ s, a μ * a ν * c) = ∑ ν ∈ s, (a μ * c) * a ν := by
                refine Finset.sum_congr rfl ?_
                intro ν hν
                ring
              _ = (a μ * c) * ∑ ν ∈ s, a ν := by
                rw [Finset.mul_sum]
              _ = c * (a μ * ∑ ν ∈ s, a ν) := by ring
              _ = c * (∑ ν ∈ s, a μ * a ν) := by
                congr 1
                rw [Finset.mul_sum]
    _ = c * (∑ μ ∈ s, ∑ ν ∈ s, a μ * a ν) := by
            rw [Finset.mul_sum]
    _ = c * ((∑ ν ∈ s, a ν) * (∑ ν ∈ s, a ν)) := by
            congr 1
            calc
              (∑ μ ∈ s, ∑ ν ∈ s, a μ * a ν)
                  = ∑ μ ∈ s, (∑ ν ∈ s, a ν) * a μ := by
                      refine Finset.sum_congr rfl ?_
                      intro μ hμ
                      rw [Finset.sum_mul]
                      ring
              _ = (∑ ν ∈ s, a ν) * (∑ μ ∈ s, a μ) := by
                      rw [Finset.mul_sum]
    _ = c * (∑ ν ∈ s, a ν) ^ 2 := by ring

/-- The `U`-scalar-product contribution of the Theorem-3.2 expansion:
`(Ψ|_U, Ψ|_U)_U = Σ_i S_i²/n_i` where `Ψ = Σ_{ν∈B} e_ν·ν`,
`S_i = Σ_{ν∈B∩orbit_i} e_ν` and `n_i = |orbit_i|` (orbits indexed by a
system of representatives `rep`). -/
private lemma U_scalarProduct_orbitSum (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i)) :
    ((c.U.subgroupOf c.H0).index : ℂ)⁻¹ *
      scalarProduct (↥c.U) (restrictU c h12
        (∑ ν ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 ν) • ν.1))
        (restrictU c h12
        (∑ ν ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 ν) • ν.1)) =
      ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) *
        (∑ ν ∈ (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
          ν.1 ∈ orbit c.H0 c.U (rep i)),
            scalarProduct G χ (tildeNu c h12 ν)) ^ 2 := by
  classical
  let B := BOf c h12 χ
  let B_i : ι → Finset (Irr (↥c.H0)) := fun i =>
    B.filter (fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U (rep i))
  let e : Irr (↥c.H0) → ℂ := fun ν => scalarProduct G χ (tildeNu c h12 ν)
  let sp : Irr (↥c.H0) → Irr (↥c.H0) → ℂ := fun μ ν =>
    scalarProduct (↥c.U) (restrictU c h12 μ.1) (restrictU c h12 ν.1)
  have he_real : ∀ ν : Irr (↥c.H0), star (e ν) = e ν := by
    intro ν
    by_cases hνB : ν ∈ B
    · rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
      · change star (scalarProduct G χ (tildeNu c h12 ν)) =
          scalarProduct G χ (tildeNu c h12 ν)
        rw [h1]
        norm_num
      · change star (scalarProduct G χ (tildeNu c h12 ν)) =
          scalarProduct G χ (tildeNu c h12 ν)
        rw [hm1]
        norm_num
    · have hzero : e ν = 0 := by
        by_contra hne
        exact hνB ((BOf_mem_iff c h12 χ ν).2 hne)
      change star (e ν) = e ν
      rw [hzero]
      simp
  have hleft : scalarProduct (↥c.U) (restrictU c h12
        (∑ ν ∈ B, e ν • ν.1)) (restrictU c h12
        (∑ ν ∈ B, e ν • ν.1)) =
      ∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν := by
    have hresL : restrictU c h12 (∑ ν ∈ B, e ν • ν.1) =
        ∑ ν ∈ B, e ν • restrictU c h12 ν.1 := by
      ext u
      simp [restrictU, Finset.sum_apply, Pi.smul_apply]
    calc
      scalarProduct (↥c.U) (restrictU c h12
          (∑ ν ∈ B, e ν • ν.1))
          (restrictU c h12
          (∑ ν ∈ B, e ν • ν.1))
          = scalarProduct (↥c.U)
              (∑ ν ∈ B, e ν • restrictU c h12 ν.1)
              (∑ ν ∈ B, e ν • restrictU c h12 ν.1) := by
                rw [hresL]
      _ = ∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν := by
                rw [scalarProduct_sum_left_finset]
                refine Finset.sum_congr rfl ?_
                intro μ hμ
                rw [scalarProduct_sum_right_finset]
                refine Finset.sum_congr rfl ?_
                intro ν hν
                rw [scalarProduct_smul_left]
                rw [scalarProduct_smul_right]
                rw [← mul_assoc]
                rw [he_real ν]
                ring
  have hsp_same : ∀ i : ι, ∀ μ ν : Irr (↥c.H0),
      μ.1 ∈ orbit c.H0 c.U (rep i) → ν.1 ∈ orbit c.H0 c.U (rep i) →
        sp μ ν = ((c.U.subgroupOf c.H0).index : ℂ) /
          ((orbit c.H0 c.U (rep i)).card : ℂ) := by
    intro i μ ν hμ hν
    have hμν : μ.1 ∈ orbit c.H0 c.U ν.1 := by
      rw [orbit_eq_of_mem' c hν]
      exact hμ
    have hEq := (restrictU_scalarProduct c h12 hSC μ ν).2 hμν
    have horbit : orbit c.H0 c.U ν.1 = orbit c.H0 c.U (rep i) := orbit_eq_of_mem' c hν
    rwa [horbit] at hEq
  have hsp_diff : ∀ μ ν : Irr (↥c.H0), ¬ μ.1 ∈ orbit c.H0 c.U ν.1 → sp μ ν = 0 :=
    fun μ ν h => (restrictU_scalarProduct c h12 hSC μ ν).1 h
  have hB_union : B = Finset.univ.biUnion B_i := by
    ext ν
    constructor
    · intro hνB
      rw [Finset.mem_biUnion]
      rcases hrep ⟨ν.1, ν.2⟩ with ⟨i, hi, _⟩
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp [B_i, B, Finset.mem_filter, hνB, hi]
    · intro hν
      rw [Finset.mem_biUnion] at hν
      rcases hν with ⟨i, hi, hνi⟩
      exact (Finset.mem_filter.mp hνi).1
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint B_i := by
    intro i hi j hj hij
    change Disjoint (B_i i) (B_i j)
    rw [Finset.disjoint_left]
    intro ν hνi hνj
    have hνi' : ν.1 ∈ orbit c.H0 c.U (rep i) := (Finset.mem_filter.mp hνi).2
    have hνj' : ν.1 ∈ orbit c.H0 c.U (rep j) := (Finset.mem_filter.mp hνj).2
    have hEq : orbit c.H0 c.U (rep i) = orbit c.H0 c.U (rep j) := by
      calc
        orbit c.H0 c.U (rep i) = orbit c.H0 c.U ν.1 := (orbit_eq_of_mem' c hνi').symm
        _ = orbit c.H0 c.U (rep j) := orbit_eq_of_mem' c hνj'
    have hmem_i : (⟨rep j, hrep_irr j⟩ : {ν : ClassFunction (↥c.H0) //
        IsIrreducibleCharacter ν}).1 ∈ orbit c.H0 c.U (rep i) := by
      rw [hEq]
      exact orbit_self_mem' c (rep j)
    have hmem_j : (⟨rep j, hrep_irr j⟩ : {ν : ClassFunction (↥c.H0) //
        IsIrreducibleCharacter ν}).1 ∈ orbit c.H0 c.U (rep j) :=
      orbit_self_mem' c (rep j)
    rcases hrep ⟨rep j, hrep_irr j⟩ with ⟨i0, hi0, huniq⟩
    have h_i : i0 = i := (huniq i hmem_i).symm
    have h_j : i0 = j := (huniq j hmem_j).symm
    exact hij (h_i.symm.trans h_j)
  have hcross : ∀ i j : ι, i ≠ j → ∀ μ ∈ B_i i, ∀ ν ∈ B_i j,
      e μ * e ν * sp μ ν = 0 := by
    intro i j hij μ hμ ν hν
    have hμi : μ.1 ∈ orbit c.H0 c.U (rep i) := (Finset.mem_filter.mp hμ).2
    have hνj : ν.1 ∈ orbit c.H0 c.U (rep j) := (Finset.mem_filter.mp hν).2
    have hnot : ¬ μ.1 ∈ orbit c.H0 c.U ν.1 := by
      intro hμν
      have hEq : orbit c.H0 c.U (rep i) = orbit c.H0 c.U (rep j) := by
        calc
          orbit c.H0 c.U (rep i) = orbit c.H0 c.U μ.1 := (orbit_eq_of_mem' c hμi).symm
          _ = orbit c.H0 c.U ν.1 := orbit_eq_of_mem' c hμν
          _ = orbit c.H0 c.U (rep j) := orbit_eq_of_mem' c hνj
      have hmem_i : (⟨rep j, hrep_irr j⟩ : {ν : ClassFunction (↥c.H0) //
          IsIrreducibleCharacter ν}).1 ∈ orbit c.H0 c.U (rep i) := by
        rw [hEq]
        exact orbit_self_mem' c (rep j)
      have hmem_j : (⟨rep j, hrep_irr j⟩ : {ν : ClassFunction (↥c.H0) //
          IsIrreducibleCharacter ν}).1 ∈ orbit c.H0 c.U (rep j) :=
        orbit_self_mem' c (rep j)
      rcases hrep ⟨rep j, hrep_irr j⟩ with ⟨i0, hi0, huniq⟩
      have h_i : i0 = i := (huniq i hmem_i).symm
      have h_j : i0 = j := (huniq j hmem_j).symm
      exact hij (h_i.symm.trans h_j)
    rw [hsp_diff μ ν hnot]
    ring
  have hinner : ∀ μ ∈ B, (∑ ν ∈ B, e μ * e ν * sp μ ν) =
      ∑ i : ι, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν := by
    intro μ hμ
    rw [hB_union]
    rw [Finset.sum_biUnion hdisj]
  have hcollapse : ∀ i : ι,
      (∑ μ ∈ B_i i, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν) =
        (∑ μ ∈ B, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν) := by
    intro i
    refine Finset.sum_subset (s₁ := B_i i) (s₂ := B) ?_ ?_
    · intro μ hμ
      exact (Finset.mem_filter.mp hμ).1
    · intro μ hμ hnot
      have hzero : (∑ ν ∈ B_i i, e μ * e ν * sp μ ν) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ν hν
        have hμnotorbit : ¬ μ.1 ∈ orbit c.H0 c.U (rep i) := by
          intro hμi
          exact hnot (Finset.mem_filter.mpr ⟨hμ, hμi⟩)
        have hnotEq : ¬ μ.1 ∈ orbit c.H0 c.U ν.1 := by
          intro hμν
          have hνi : ν.1 ∈ orbit c.H0 c.U (rep i) := (Finset.mem_filter.mp hν).2
          have hμi : μ.1 ∈ orbit c.H0 c.U (rep i) := by
            rw [← orbit_eq_of_mem' c hνi]
            exact hμν
          exact hμnotorbit hμi
        rw [hsp_diff μ ν hnotEq]
        ring
      exact hzero
  have hsplit : (∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν) =
      ∑ i : ι, ∑ μ ∈ B_i i, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν := by
    calc
      (∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν)
          = ∑ μ ∈ B, ∑ i : ι, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν := by
              refine Finset.sum_congr rfl ?_
              intro μ hμ
              exact hinner μ hμ
      _ = ∑ i : ι, ∑ μ ∈ B, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν := by
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ μ ∈ B_i i, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact (hcollapse i).symm
  have hfiber : ∀ i : ι,
      (∑ μ ∈ B_i i, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν) =
        ((c.U.subgroupOf c.H0).index : ℂ) /
          ((orbit c.H0 c.U (rep i)).card : ℂ) *
          (∑ ν ∈ B_i i, e ν) ^ 2 := by
    intro i
    calc
      (∑ μ ∈ B_i i, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν)
          = ∑ μ ∈ B_i i, ∑ ν ∈ B_i i,
              e μ * e ν * (((c.U.subgroupOf c.H0).index : ℂ) /
                ((orbit c.H0 c.U (rep i)).card : ℂ)) := by
              refine Finset.sum_congr rfl ?_
              intro μ hμ
              refine Finset.sum_congr rfl ?_
              intro ν hν
              rw [hsp_same i μ ν (Finset.mem_filter.mp hμ).2 (Finset.mem_filter.mp hν).2]
      _ = ((c.U.subgroupOf c.H0).index : ℂ) /
            ((orbit c.H0 c.U (rep i)).card : ℂ) *
            (∑ ν ∈ B_i i, e ν) ^ 2 := by
              exact sum_pair_const_factor (B_i i) e
                (((c.U.subgroupOf c.H0).index : ℂ) /
                  ((orbit c.H0 c.U (rep i)).card : ℂ))
  have hgroup : (∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν) =
      ((c.U.subgroupOf c.H0).index : ℂ) *
        ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) *
          (∑ ν ∈ B_i i, e ν) ^ 2 := by
    calc
      (∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν)
          = ∑ i : ι, ∑ μ ∈ B_i i, ∑ ν ∈ B_i i, e μ * e ν * sp μ ν := hsplit
      _ = ∑ i : ι, (((c.U.subgroupOf c.H0).index : ℂ) /
            ((orbit c.H0 c.U (rep i)).card : ℂ)) *
            (∑ ν ∈ B_i i, e ν) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hfiber i
      _ = ((c.U.subgroupOf c.H0).index : ℂ) *
            ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) *
              (∑ ν ∈ B_i i, e ν) ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [div_eq_mul_inv]
              ring
  calc
    ((c.U.subgroupOf c.H0).index : ℂ)⁻¹ *
        scalarProduct (↥c.U) (restrictU c h12
          (∑ ν ∈ B, e ν • ν.1)) (restrictU c h12
          (∑ ν ∈ B, e ν • ν.1))
        = ((c.U.subgroupOf c.H0).index : ℂ)⁻¹ *
            (∑ μ ∈ B, ∑ ν ∈ B, e μ * e ν * sp μ ν) := by
              rw [hleft]
    _ = ((c.U.subgroupOf c.H0).index : ℂ)⁻¹ *
          (((c.U.subgroupOf c.H0).index : ℂ) *
            ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) *
              (∑ ν ∈ B_i i, e ν) ^ 2) := by
              rw [hgroup]
    _ = ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) *
          (∑ ν ∈ B_i i, e ν) ^ 2 := by
              have hmne : ((c.U.subgroupOf c.H0).index : ℂ) ≠ 0 := by
                exact_mod_cast (Subgroup.index_ne_zero_of_finite
                  (H := c.U.subgroupOf c.H0))
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              field_simp [hmne]
    _ = ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) *
          (∑ ν ∈ (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
            ν.1 ∈ orbit c.H0 c.U (rep i)),
              scalarProduct G χ (tildeNu c h12 ν)) ^ 2 := by
              rfl

/-- `|U| · |H0 : U| = |H0|`. -/
private lemma U_index_card_mul (c : Hyp11 G) (h12 : Hyp12 c) :
    (Nat.card (↥c.U) : ℂ) * ((c.U.subgroupOf c.H0).index : ℂ) =
      (Nat.card (↥c.H0) : ℂ) := by
  have hUcard : Nat.card (↥(c.U.subgroupOf c.H0)) = Nat.card (↥c.U) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.U.subgroupOf c.H0) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩,
        Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have hEq : Nat.card (↥c.U) * (c.U.subgroupOf c.H0).index = Nat.card (↥c.H0) := by
    rw [← hUcard]
    exact hcm
  exact_mod_cast hEq

/-- For a real-valued sum, the complex square agrees with `Complex.normSq`. -/
private lemma complex_sq_eq_normSq_of_real_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hreal : ∀ i ∈ s, star (f i) = f i) :
    (∑ i ∈ s, f i) ^ 2 = (Complex.normSq (∑ i ∈ s, f i) : ℂ) := by
  have hstar : star (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
    rw [star_sum]
    exact Finset.sum_congr rfl (fun i hi => hreal i hi)
  calc
    (∑ i ∈ s, f i) ^ 2 = (∑ i ∈ s, f i) * (∑ i ∈ s, f i) := by ring
    _ = star (∑ i ∈ s, f i) * (∑ i ∈ s, f i) := by
            nth_rw 1 [← hstar]
    _ = (Complex.normSq (∑ i ∈ s, f i) : ℂ) := by
            rw [mul_comm]
            exact Complex.mul_conj (∑ i ∈ s, f i)

/-- `B(χ)` intersects a `Λ`-orbit in at most half of the orbit. -/
private lemma BOf_orbit_fiber_card_le_half (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) (ν : Irr (↥c.H0)) :
    (((BOf c h12 χ).filter (fun μ : Irr (↥c.H0) =>
      μ.1 ∈ orbit c.H0 c.U ν.1)).card : ℝ) ≤
      ((orbit c.H0 c.U ν.1).card : ℝ) / 2 := by
  classical
  let t : ℕ := (BOf c h12 χ).filter (fun μ : Irr (↥c.H0) =>
    μ.1 ∈ orbit c.H0 c.U ν.1) |>.card
  have ht_le_two : t ≤ 2 := by
    simpa [t] using BOf_orbit_card_le_two c h12 χ hχ ν
  have hn_ge_two : 2 ≤ (orbit c.H0 c.U ν.1).card := orbit_card_ge_two c h12 ν
  have ht_le_half_nat : t * 2 ≤ (orbit c.H0 c.U ν.1).card := by
    by_cases ht0 : t = 0
    · omega
    by_cases ht1 : t = 1
    · omega
    · have ht2 : t = 2 := by omega
      have hn_ge_four : 4 ≤ (orbit c.H0 c.U ν.1).card := by
        by_contra hnot
        have hpow := orbit_card_is_pow_two c h12 ν
        rcases hpow with ⟨k, hk⟩
        have hcard_lt : (orbit c.H0 c.U ν.1).card < 4 := by omega
        have hk_le : k ≤ 1 := by
          by_contra hknot
          have hkge2 : 2 ≤ k := by omega
          have hpow_ge : 4 ≤ 2 ^ k := by
            have hk2 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkge2
            norm_num at hk2 ⊢
            exact hk2
          have hcard_ge : 4 ≤ (orbit c.H0 c.U ν.1).card := by
            rw [hk]
            exact hpow_ge
          omega
        have hk_ge : 1 ≤ k := by
          by_contra hk0
          have hk0' : k = 0 := by omega
          rw [hk0'] at hk
          simp at hk
          omega
        have hk_eq_one : k = 1 := by omega
        have hn2 : (orbit c.H0 c.U ν.1).card = 2 := by
          rw [hk, hk_eq_one]
          norm_num
        have ht2' : t = 2 := ht2
        rcases Finset.card_eq_two.mp ht2' with ⟨μ, η, hμη, hs⟩
        have hμB : μ ∈ BOf c h12 χ := by
          have hmem : μ ∈ (BOf c h12 χ).filter (fun μ : Irr (↥c.H0) =>
              μ.1 ∈ orbit c.H0 c.U ν.1) := by
            rw [hs]
            simp
          exact (Finset.mem_filter.mp hmem).1
        have hηB : η ∈ BOf c h12 χ := by
          have hmem : η ∈ (BOf c h12 χ).filter (fun μ : Irr (↥c.H0) =>
              μ.1 ∈ orbit c.H0 c.U ν.1) := by
            rw [hs]
            simp
          exact (Finset.mem_filter.mp hmem).1
        have hμL : μ.1 ∈ orbit c.H0 c.U ν.1 := by
          have hmem : μ ∈ (BOf c h12 χ).filter (fun μ : Irr (↥c.H0) =>
              μ.1 ∈ orbit c.H0 c.U ν.1) := by
            rw [hs]
            simp
          exact (Finset.mem_filter.mp hmem).2
        have hηL : η.1 ∈ orbit c.H0 c.U ν.1 := by
          have hmem : η ∈ (BOf c h12 χ).filter (fun μ : Irr (↥c.H0) =>
              μ.1 ∈ orbit c.H0 c.U ν.1) := by
            rw [hs]
            simp
          exact (Finset.mem_filter.mp hmem).2
        have hμLη : μ.1 ∈ orbit c.H0 c.U η.1 := by
          rw [orbit_eq_of_mem' c hηL]
          exact hμL
        have hconj := BOf_orbit_pair_conj c h12 hχ hμB hηB hμLη hμη
        have hηs : conjChar c.H0 (s_normalizes_H0 c h12) η.1 ∈
            orbit c.H0 c.U ν.1 := by
          have hηs' : conjChar c.H0 (s_normalizes_H0 c h12) η.1 = μ.1 := by
            calc
              conjChar c.H0 (s_normalizes_H0 c h12) η.1
                  = conjChar c.H0 (s_normalizes_H0 c h12)
                      (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) := by rw [hconj]
              _ = μ.1 := conjChar_involution c h12 μ.1
          rw [hηs']
          exact hμL
        have hηs' : conjChar c.H0 (s_normalizes_H0 c h12) η.1 ∈
            orbit c.H0 c.U η.1 := by
          rw [orbit_eq_of_mem' c hηL]
          exact hηs
        have hfixcount := lemma_2_1_b c h12 (ν := η.1) η.2 hηs'
        rw [orbit_eq_of_mem' c hηL] at hfixcount
        have hfixall : ∀ x ∈ orbit c.H0 c.U ν.1,
            conjChar c.H0 (s_normalizes_H0 c h12) x = x := by
          exact Finset.filter_card_eq
            (s := orbit c.H0 c.U ν.1)
            (p := fun x : ClassFunction (↥c.H0) =>
              conjChar c.H0 (s_normalizes_H0 c h12) x = x)
            (by rw [hfixcount, hn2])
        have hfixμ := hfixall μ.1 hμL
        have hμneη : μ.1 ≠ η.1 := by
          intro hEq
          exact hμη (Subtype.ext hEq)
        exact hμneη (by rw [← hfixμ, hconj])
      omega
  have hnat' : (t : ℝ) * 2 ≤ (orbit c.H0 c.U ν.1).card := by
    exact_mod_cast ht_le_half_nat
  have hpos : (0 : ℝ) < 2 := by norm_num
  nlinarith

/-- The sum over `T ⊆ G` equals the sum over `H0` with the `T`-indicator. -/
private lemma Tsum_G_eq_H0 (c : Hyp11 G) {χ : ClassFunction G} :
    (∑ x ∈ (Finset.univ.filter (fun x : G => x ∈ c.T)), Complex.normSq (χ x)) =
      ∑ x : ↥c.H0, if (x : G) ∈ c.T then Complex.normSq (χ (x : G)) else 0 := by
  classical
  rw [← Finset.sum_filter (s := Finset.univ)
    (p := fun x : ↥c.H0 => (x : G) ∈ c.T)
    (f := fun x : ↥c.H0 => Complex.normSq (χ (x : G)))]
  let TG : Finset G := Finset.univ.filter (fun x : G => x ∈ c.T)
  let TH : Finset (↥c.H0) := Finset.univ.filter (fun x : ↥c.H0 => (x : G) ∈ c.T)
  change (∑ x ∈ TG, Complex.normSq (χ x)) =
    ∑ x ∈ TH, Complex.normSq (χ (x : G))
  refine Finset.sum_bij (fun y : G => fun hy : y ∈ TG =>
      (⟨y, (Finset.mem_filter.mp hy).2.1⟩ : ↥c.H0)) ?_ ?_ ?_ ?_
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  · intro a ha b hb hEq
    exact congrArg Subtype.val hEq
  · intro x hx
    refine ⟨(x : G), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · apply Subtype.ext
      rfl
  · intro y hy
    rfl

/-- The key counting inequality of Theorem 3.2:
`Σ_{x∈T} |χ(x)|² ≥ |H0|·(|B(χ)| − Σ_i t_i²/n_i)`. -/
private lemma T_sum_ge (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    (∑ x : ↥c.H0, if (x : G) ∈ c.T then Complex.normSq (χ (x : G)) else 0) ≥
      (Nat.card (↥c.H0) : ℝ) * ((BOf c h12 χ).card : ℝ) - (Nat.card (↥c.H0) : ℝ) * (1 / 2) *
        (BOf c h12 χ).card := by
  classical
  let B := BOf c h12 χ
  let e : Irr (↥c.H0) → ℂ := fun ν => scalarProduct G χ (tildeNu c h12 ν)
  let Ψ : ClassFunction (↥c.H0) := ∑ ν ∈ B, e ν • ν.1
  let Tsum : ℝ := ∑ x : ↥c.H0,
    if (x : G) ∈ c.T then Complex.normSq (χ (x : G)) else 0
  have he_real : ∀ ν : Irr (↥c.H0), star (e ν) = e ν := by
    intro ν
    by_cases hνB : ν ∈ B
    · rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
      · change star (scalarProduct G χ (tildeNu c h12 ν)) =
          scalarProduct G χ (tildeNu c h12 ν)
        rw [h1]
        norm_num
      · change star (scalarProduct G χ (tildeNu c h12 ν)) =
          scalarProduct G χ (tildeNu c h12 ν)
        rw [hm1]
        norm_num
    · have hzero : e ν = 0 := by
        by_contra hne
        exact hνB ((BOf_mem_iff c h12 χ ν).2 hne)
      change star (e ν) = e ν
      rw [hzero]
      simp
  have hχΨT : ∀ x : ↥c.H0, (x : G) ∈ c.T → χ (x : G) = Ψ x := by
    intro x hxT
    have h24 := (lemma_2_4 c h12 hχ).1 (x : G) hxT x.2
    simpa [B, e, Ψ] using h24
  have hTsum_eq : Tsum = ∑ x : ↥c.H0,
      if (x : G) ∈ c.T then Complex.normSq (Ψ x) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    by_cases hxT : (x : G) ∈ c.T
    · rw [if_pos hxT, if_pos hxT]
      rw [hχΨT x hxT]
    · rw [if_neg hxT, if_neg hxT]
  have hTsumC : (Tsum : ℂ) = ∑ x : ↥c.H0,
      if (x : G) ∈ c.T then Ψ x * star (Ψ x) else 0 := by
    rw [hTsum_eq]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    by_cases hxT : (x : G) ∈ c.T
    · rw [if_pos hxT, if_pos hxT]
      exact (Complex.mul_conj (Ψ x)).symm
    · rw [if_neg hxT, if_neg hxT]
      simp
  have hEq0 : (Tsum : ℂ) =
      (Nat.card (↥c.H0) : ℂ) * scalarProduct (↥c.H0) Ψ Ψ -
        (Nat.card (↥c.U) : ℂ) * scalarProduct (↥c.U)
          (restrictU c h12 Ψ) (restrictU c h12 Ψ) := by
    rw [hTsumC]
    exact T_sum_scalarProduct c h12 Ψ Ψ
  have hPsi_norm : scalarProduct (↥c.H0) Ψ Ψ = (B.card : ℂ) := by
    have hdist : ∀ μ ∈ B, ∀ ν ∈ B, μ ≠ ν → μ ≠ ν := by
      intro μ hμ ν hν h
      exact h
    have hsq : ∀ ν ∈ B, e ν * e ν = 1 := by
      intro ν hν
      rcases BOf_scalar_eq_pm_one c h12 hχ hν with h1 | hm1
      · simp [e, h1]
      · simp [e, hm1]
    simpa [Ψ] using scalarProduct_sum_smul_self_distinct B
      (fun ν : Irr (↥c.H0) => ν) e hdist (fun ν hν => he_real ν) hsq
  rcases exists_orbit_reps' c h12 with ⟨ι, hι, rep, hrep_irr, hrep⟩
  let : Fintype ι := hι
  let B_i : ι → Finset (Irr (↥c.H0)) := fun i =>
    B.filter (fun ν : Irr (↥c.H0) => ν.1 ∈ orbit c.H0 c.U (rep i))
  let S : ι → ℂ := fun i => ∑ ν ∈ B_i i, e ν
  let Rsum : ℝ := ∑ i : ι, Complex.normSq (S i) / (orbit c.H0 c.U (rep i)).card
  have hOrbit := U_scalarProduct_orbitSum c h12 hSC hχ (ι := ι) rep hrep_irr hrep
  have hS_real : ∀ i : ι, star (S i) = S i := by
    intro i
    dsimp [S]
    change star (∑ ν ∈ B_i i, e ν) = ∑ ν ∈ B_i i, e ν
    rw [star_sum]
    refine Finset.sum_congr rfl ?_
    intro ν hν
    exact he_real ν
  have hS_sq (i : ι) : (S i) ^ 2 = (Complex.normSq (S i) : ℂ) := by
    simpa [S] using complex_sq_eq_normSq_of_real_sum (B_i i) e (fun ν hν => he_real ν)
  have hCast (i : ι) :
      (((Complex.normSq (S i) / (orbit c.H0 c.U (rep i)).card : ℝ) : ℂ)) =
        ((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹ * (Complex.normSq (S i) : ℂ) := by
    rw [div_eq_mul_inv]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
    norm_num
    ring
  have hSumCast : (Rsum : ℂ) =
      ∑ i : ι, (((orbit c.H0 c.U (rep i)).card : ℂ)⁻¹) * (S i) ^ 2 := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hCast i]
    rw [← hS_sq i]
  have hOrbitReal : ((c.U.subgroupOf c.H0).index : ℂ)⁻¹ *
      scalarProduct (↥c.U) (restrictU c h12 Ψ) (restrictU c h12 Ψ) =
        (Rsum : ℂ) := by
    rw [hOrbit]
    rw [← hSumCast]
  have hindex_ne : ((c.U.subgroupOf c.H0).index : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := c.U.subgroupOf c.H0))
  have hspU : scalarProduct (↥c.U) (restrictU c h12 Ψ) (restrictU c h12 Ψ) =
      ((c.U.subgroupOf c.H0).index : ℂ) * (Rsum : ℂ) := by
    have h := congrArg (fun z : ℂ => ((c.U.subgroupOf c.H0).index : ℂ) * z) hOrbitReal
    field_simp [hindex_ne] at h
    simpa [mul_assoc] using h
  have hUsp : (Nat.card (↥c.U) : ℂ) *
      scalarProduct (↥c.U) (restrictU c h12 Ψ) (restrictU c h12 Ψ) =
        (Nat.card (↥c.H0) : ℂ) * (Rsum : ℂ) := by
    rw [hspU]
    rw [← mul_assoc]
    rw [U_index_card_mul c h12]
  have hEq1 : (Tsum : ℂ) =
      (Nat.card (↥c.H0) : ℂ) * ((B.card : ℂ) - (Rsum : ℂ)) := by
    rw [hEq0, hPsi_norm, hUsp]
    ring_nf
  have hEqReal : Tsum = (Nat.card (↥c.H0) : ℝ) * (B.card : ℝ) -
      (Nat.card (↥c.H0) : ℝ) * Rsum := by
    apply Complex.ofReal_injective
    calc
      (Tsum : ℂ) = (Nat.card (↥c.H0) : ℂ) * ((B.card : ℂ) - (Rsum : ℂ)) := hEq1
      _ = (((Nat.card (↥c.H0) : ℝ) * ((B.card : ℝ) - Rsum) : ℝ) : ℂ) := by
            norm_num [Complex.ofReal_sub, Complex.ofReal_mul]
      _ = ((((Nat.card (↥c.H0) : ℝ) * (B.card : ℝ) -
            (Nat.card (↥c.H0) : ℝ) * Rsum) : ℝ) : ℂ) := by
            ring_nf
  have hB_union : B = Finset.univ.biUnion B_i := by
    ext ν
    constructor
    · intro hνB
      rw [Finset.mem_biUnion]
      rcases hrep ⟨ν.1, ν.2⟩ with ⟨i, hi, _⟩
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp [B_i, B, Finset.mem_filter, hνB, hi]
    · intro hν
      rw [Finset.mem_biUnion] at hν
      rcases hν with ⟨i, hi, hνi⟩
      exact (Finset.mem_filter.mp hνi).1
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint B_i := by
    intro i hi j hj hij
    change Disjoint (B_i i) (B_i j)
    rw [Finset.disjoint_left]
    intro ν hνi hνj
    have hνi' : ν.1 ∈ orbit c.H0 c.U (rep i) := (Finset.mem_filter.mp hνi).2
    have hνj' : ν.1 ∈ orbit c.H0 c.U (rep j) := (Finset.mem_filter.mp hνj).2
    have hEq : orbit c.H0 c.U (rep i) = orbit c.H0 c.U (rep j) := by
      calc
        orbit c.H0 c.U (rep i) = orbit c.H0 c.U ν.1 := (orbit_eq_of_mem' c hνi').symm
        _ = orbit c.H0 c.U (rep j) := orbit_eq_of_mem' c hνj'
    have hmem_i : (⟨rep j, hrep_irr j⟩ : {ν : ClassFunction (↥c.H0) //
        IsIrreducibleCharacter ν}).1 ∈ orbit c.H0 c.U (rep i) := by
      rw [hEq]
      exact orbit_self_mem' c (rep j)
    have hmem_j : (⟨rep j, hrep_irr j⟩ : {ν : ClassFunction (↥c.H0) //
        IsIrreducibleCharacter ν}).1 ∈ orbit c.H0 c.U (rep j) :=
      orbit_self_mem' c (rep j)
    rcases hrep ⟨rep j, hrep_irr j⟩ with ⟨i0, hi0, huniq⟩
    have h_i : i0 = i := (huniq i hmem_i).symm
    have h_j : i0 = j := (huniq j hmem_j).symm
    exact hij (h_i.symm.trans h_j)
  have hcards : (∑ i : ι, (B_i i).card) = B.card := by
    rw [hB_union]
    rw [Finset.card_biUnion hdisj]
  have hS_le (i : ι) : Complex.normSq (S i) ≤ (B_i i).card ^ 2 := by
    have hnorm (ν : Irr (↥c.H0)) (hν : ν ∈ B_i i) : ‖e ν‖ = 1 := by
      have hνB : ν ∈ B := (Finset.mem_filter.mp hν).1
      rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
      · have hsq : Complex.normSq (e ν) = 1 := by
          simp [e, h1]
        rw [Complex.normSq_eq_norm_sq] at hsq
        have hnn : 0 ≤ ‖e ν‖ := norm_nonneg _
        nlinarith
      · have hsq : Complex.normSq (e ν) = 1 := by
          simp [e, hm1]
        rw [Complex.normSq_eq_norm_sq] at hsq
        have hnn : 0 ≤ ‖e ν‖ := norm_nonneg _
        nlinarith
    have hsum : ‖∑ ν ∈ B_i i, e ν‖ ≤ (B_i i).card := by
      calc
        ‖∑ ν ∈ B_i i, e ν‖ ≤ ∑ ν ∈ B_i i, ‖e ν‖ := norm_sum_le _ _
        _ = (B_i i).card := by
              rw [Finset.sum_congr rfl (fun ν hν => hnorm ν hν)]
              simp
    have hnn : 0 ≤ ‖S i‖ := norm_nonneg _
    have hsq2 : ‖S i‖ ^ 2 ≤ (B_i i).card ^ 2 := by
      nlinarith
    have hnormSq : Complex.normSq (S i) = ‖S i‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rwa [hnormSq]
  have hti_le_half (i : ι) :
      ((B_i i).card : ℝ) ≤ ((orbit c.H0 c.U (rep i)).card : ℝ) / 2 := by
    have h := BOf_orbit_fiber_card_le_half c h12 hχ ⟨rep i, hrep_irr i⟩
    simpa [B_i, B] using h
  have hn_pos (i : ι) : 0 < ((orbit c.H0 c.U (rep i)).card : ℝ) := by
    have hmem : rep i ∈ orbit c.H0 c.U (rep i) := orbit_self_mem' c (rep i)
    have hpos : 0 < (orbit c.H0 c.U (rep i)).card :=
      Finset.card_pos.mpr ⟨rep i, hmem⟩
    exact_mod_cast hpos
  have hterm (i : ι) :
      Complex.normSq (S i) / ((orbit c.H0 c.U (rep i)).card : ℝ) ≤
        ((B_i i).card : ℝ) / 2 := by
    have hnonneg : 0 ≤ ((B_i i).card : ℝ) := by
      exact_mod_cast (Nat.zero_le ((B_i i).card))
    have h2 : 2 * Complex.normSq (S i) ≤
        ((orbit c.H0 c.U (rep i)).card : ℝ) * ((B_i i).card : ℝ) := by
      nlinarith [hS_le i, hti_le_half i, hnonneg, hn_pos i]
    rw [div_le_iff₀ (hn_pos i)]
    nlinarith
  have hsumR : Rsum ≤ (B.card : ℝ) / 2 := by
    calc
      Rsum = ∑ i : ι, Complex.normSq (S i) / ((orbit c.H0 c.U (rep i)).card : ℝ) := rfl
      _ ≤ ∑ i : ι, ((B_i i).card : ℝ) / 2 := by
            exact Finset.sum_le_sum (fun i hi => hterm i)
      _ = (∑ i : ι, (B_i i).card) / 2 := by
            rw [← Finset.sum_div]
            norm_cast
      _ = (B.card : ℝ) / 2 := by
            rw [hcards]
  have hposH0 : 0 ≤ (Nat.card (↥c.H0) : ℝ) := by positivity
  have hgoal : (Nat.card (↥c.H0) : ℝ) * (B.card : ℝ) / 2 ≤ Tsum := by
    nlinarith [hEqReal, hsumR, hposH0]
  change (Nat.card (↥c.H0) : ℝ) * ((BOf c h12 χ).card : ℝ) -
      (Nat.card (↥c.H0) : ℝ) * (1 / 2) * ((BOf c h12 χ).card : ℝ) ≤ Tsum
  nlinarith [hgoal]

/-- Distinct members of `B(χ)` lying in one `Λ`-orbit are `s`-conjugate
(`BOf_orbit_pair_conj`), hence have equal coefficients
(`tildeNu_invariance`).  This is the signed-orbit fact needed for the
counting bound: in a 2-element orbit containing both members of `B(χ)`,
the signed sum is `±2`, so `S_i²/n_i = 2 = t_i²/n_i`. -/
private lemma BOf_orbit_pair_coeff_eq (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {μ ν : Irr (↥c.H0)}
    (hμB : μ ∈ BOf c h12 χ) (hνB : ν ∈ BOf c h12 χ)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) (hμν : μ ≠ ν) :
    scalarProduct G χ (tildeNu c h12 μ) = scalarProduct G χ (tildeNu c h12 ν) := by
  classical
  have hconj : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 :=
    BOf_orbit_pair_conj c h12 hχ hμB hνB hμL hμν
  -- `ν̃ = μ̃` because `ν = μ^s`
  have htilde : tildeNu c h12 ν = tildeNu c h12 μ := by
    have hνs : ν = conjIrr c h12 μ := by
      apply Subtype.ext
      rw [conjIrr_coe]
      exact hconj.symm
    rw [hνs]
    exact tildeNu_invariance c h12 μ
  rw [htilde]


/-- Theorem 3.2: each `χ ∈ ±Irr(G)` satisfies `|B(χ)| ≤ 3`. -/
public theorem theorem_3_2 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    (BOf c h12 χ).card ≤ 3 := by
  classical
  let B := BOf c h12 χ
  have hTsumGe := T_sum_ge c h12 hSC hχ
  have hTsumEq := Tsum_G_eq_H0 (c := c) (χ := χ)
  have hTsumLt := TI_sum_lt_card c h12 hχ
  have hge : (Nat.card (↥c.H0) : ℝ) * (B.card : ℝ) / 2 ≤
      ∑ x : ↥c.H0, if (x : G) ∈ c.T then Complex.normSq (χ (x : G)) else 0 := by
    nlinarith [hTsumGe]
  have hlt : (Nat.card (↥c.H0) : ℝ) * (B.card : ℝ) / 2 <
      (Nat.card (↥c.H) : ℝ) := by
    calc
      (Nat.card (↥c.H0) : ℝ) * (B.card : ℝ) / 2 ≤
          ∑ x : ↥c.H0, if (x : G) ∈ c.T then Complex.normSq (χ (x : G)) else 0 := hge
      _ = ∑ x ∈ (Finset.univ.filter (fun x : G => x ∈ c.T)),
            Complex.normSq (χ x) := hTsumEq.symm
      _ < (Nat.card (↥c.H) : ℝ) := hTsumLt
  have hHcard : (Nat.card (↥c.H) : ℝ) = 2 * (Nat.card (↥c.H0) : ℝ) := by
    have hU : Nat.card (↥(c.H0.subgroupOf c.H)) = Nat.card (↥c.H0) := by
      exact Nat.card_congr {
        toFun := fun x : ↥(c.H0.subgroupOf c.H) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y : ↥c.H0 => ⟨⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩,
          Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro y; apply Subtype.ext; rfl }
    have hcm := Subgroup.card_mul_index (c.H0.subgroupOf c.H)
    have hindex : (c.H0.subgroupOf c.H).index = 2 := H0_index c h12
    have hNat : Nat.card (↥c.H0) * 2 = Nat.card (↥c.H) := by
      rw [hU, hindex] at hcm
      simpa [mul_comm] using hcm
    have hNat' : 2 * Nat.card (↥c.H0) = Nat.card (↥c.H) := by
      simpa [mul_comm] using hNat
    exact_mod_cast hNat'.symm
  have hH0pos : 0 < (Nat.card (↥c.H0) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := ↥c.H0))
  have hB4 : (B.card : ℝ) < 4 := by
    nlinarith [hlt, hHcard, hH0pos]
  have hBnat : B.card < 4 := by
    exact_mod_cast hB4
  have hBnat' : (BOf c h12 χ).card < 4 := by
    simpa [B] using hBnat
  omega

end Section3

end CFSG.BenderGlauberman
