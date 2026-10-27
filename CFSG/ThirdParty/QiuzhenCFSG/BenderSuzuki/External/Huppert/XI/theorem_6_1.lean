module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.SharpNearField
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.InducedIrreducible
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.theorem_7_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.theorem_7_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Mackey
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation

namespace CFSG
end CFSG
open CFSG

attribute [local simp] Representation.isTrivial_def

/-!
# Feit XI.6.1

The central-prime comparison used in Huppert--Blackburn XI.11.16 is isolated
as an independent source leaf.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u v

open scoped commutatorElement


/-- A nonidentity element of the point-stabilizer Frobenius kernel fixes
exactly the base point. -/
private theorem huppert_XI_6_4_frobeniusKernel_uniqueFixedPoint
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (z : F) (hzne : z ≠ 1) :
    ∀ c : Omega,
      ((((z : MulAction.stabilizer G a) : G) • c = c) ↔ c = a) := by
  intro c
  constructor
  · intro hzc
    by_contra hca
    let cSub : SubMulAction.ofStabilizer G a := ⟨c, hca⟩
    have hzcSub :
        (z : MulAction.stabilizer G a) • cSub = cSub := by
      exact Subtype.ext hzc
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstab_multi :
        MulAction.IsMultiplyPretransitive
            (MulAction.stabilizer G a)
            (SubMulAction.ofStabilizer G a) 1 :=
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := G) (a := a)).mp htwo
    have hpretrans :
        MulAction.IsPretransitive
          (MulAction.stabilizer G a)
          (SubMulAction.ofStabilizer G a) :=
      (MulAction.is_one_pretransitive_iff
        (G := MulAction.stabilizer G a)
        (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
    have hregular :
        ∀ x y : SubMulAction.ofStabilizer G a,
          ∃! f : F, (f : MulAction.stabilizer G a) • x = y :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        hFrob.isComplement' hpretrans
    obtain ⟨k, _hk, hunique⟩ := hregular cSub cSub
    have hzk : z = k := hunique z hzcSub
    have honek : (1 : F) = k := hunique 1 (by simp)
    exact hzne (hzk.trans honek.symm)
  · intro hca
    rw [hca]
    exact (z : MulAction.stabilizer G a).property

/-- The nonidentity Frobenius-kernel carrier is a relative TI subset of the
point stabilizer in the ambient Zassenhaus group. -/
private theorem huppert_XI_6_5_kernelCarrier_relativeTI
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    let H := MulAction.stabilizer G a
    let K : Set G := (F.map H.subtype : Set G)
    Suzuki.VI.IsTISubsetRelative H K := by
  let H := MulAction.stabilizer G a
  let Fg : Subgroup G := F.map H.subtype
  change Suzuki.VI.IsTISubsetRelative H (Fg : Set G)
  have hFgH : (Fg : Set G) ⊆ H := by
    intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    exact f.property
  have hHnorm : H ≤ Subgroup.normalizer (Fg : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    let hH : H := ⟨h, hh⟩
    constructor
    · intro hx
      rcases hx with ⟨f, hf, hfx⟩
      let cF : F := ⟨hH * f * hH⁻¹,
        hFrob.normal.conj_mem f hf hH⟩
      refine ⟨(cF : H), cF.property, ?_⟩
      change ((cF : H) : G) = h * x * h⁻¹
      simp only [cF, hH]
      rw [← hfx]
      rfl
    · intro hx
      rcases hx with ⟨f, hf, hfx⟩
      let cF : F := ⟨hH⁻¹ * f * hH, by
        simpa using hFrob.normal.conj_mem f hf hH⁻¹⟩
      refine ⟨(cF : H), cF.property, ?_⟩
      have hfx' : ((f : H) : G) = h * x * h⁻¹ := hfx
      calc
        ((cF : H) : G) = h⁻¹ * ((f : H) : G) * h := rfl
        _ = h⁻¹ * (h * x * h⁻¹) * h := by rw [hfx']
        _ = x := by group
  have hKnontrivial : ∃ k : G, k ∈ (Fg : Set G) ∧ k ≠ 1 := by
    obtain ⟨f, hfne⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot)
    refine ⟨((f : H) : G), ?_, ?_⟩
    · exact ⟨f, f.property, rfl⟩
    · intro hf
      apply hfne
      exact Subtype.ext (Subtype.ext hf)
  apply
    (Suzuki.VI.suzuki_ch6_proposition_2_8
      H (Fg : Set G) hFgH hHnorm hKnontrivial).2
  intro g hgH z hz
  rcases hz with ⟨⟨x, hxFg, rfl⟩, hzxFg⟩
  simp only [Set.mem_singleton_iff]
  by_contra hzne
  rcases hxFg with ⟨xf, hxfF, hxfval⟩
  rcases hzxFg with ⟨zf, hzfF, hzfval⟩
  let xF : F := ⟨xf, hxfF⟩
  let zF : F := ⟨zf, hzfF⟩
  have hxFne : xF ≠ 1 := by
    intro hxone
    apply hzne
    have hxvalOne : x = 1 := by
      rw [← hxfval]
      simpa [xF] using congrArg Subtype.val hxone
    simp [hxvalOne]
  have hzFne : zF ≠ 1 := by
    intro hzone
    apply hzne
    calc
      g * x * g⁻¹ = ((zF : H) : G) := hzfval.symm
      _ = 1 := by simpa using congrArg Subtype.val hzone
  have hxfixa : x • a = a := by
    rw [← hxfval]
    exact xf.property
  have hzfval' : ((zF : H) : G) = g * x * g⁻¹ := hzfval
  have hzfixga : ((zF : H) : G) • (g • a) = g • a := by
    calc
      ((zF : H) : G) • (g • a) =
          (g * x * g⁻¹) • (g • a) := by rw [hzfval']
      _ = g • (x • a) := by simp only [mul_smul, inv_smul_smul]
      _ = g • a := by rw [hxfixa]
  have hga : g • a = a :=
    (huppert_XI_6_4_frobeniusKernel_uniqueFixedPoint
      htwo a b hab F hFrob zF hzFne (g • a)).mp hzfixga
  exact hgH (MulAction.mem_stabilizer_iff.mpr hga)

/-- The arithmetic core of XI.6.2: in a complete list of prime-power
character degrees whose squares sum to the group order, the degrees below
`p ^ s` contribute a multiple of `p ^ (2 * s)`. -/
private theorem huppert_XI_6_2_lower_degree_sq_sum_dvd
    {ι : Type*} [Fintype ι] (p n s : ℕ) (hp : Nat.Prime p)
    (h2s : 2 * s ≤ n) (degreeNat : ι → ℕ)
    (hdegreePow : ∀ i, ∃ t : ℕ, degreeNat i = p ^ t)
    (htotal : ∑ i, degreeNat i ^ 2 = p ^ n) :
    p ^ (2 * s) ∣
      ∑ i ∈ Finset.univ.filter (fun i => degreeNat i < p ^ s),
        degreeNat i ^ 2 := by
  classical
  let low : Finset ι :=
    Finset.univ.filter (fun i => degreeNat i < p ^ s)
  let high : Finset ι :=
    Finset.univ.filter (fun i => p ^ s ≤ degreeNat i)
  have hpartition : low ∪ high = Finset.univ := by
    ext i
    simp [low, high, lt_or_ge]
  have hdisjoint : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro i hilow ihigh
    exact (not_le_of_gt (Finset.mem_filter.mp hilow).2)
      (Finset.mem_filter.mp ihigh).2
  have hsplit :
      (∑ i, degreeNat i ^ 2) =
        (∑ i ∈ low, degreeNat i ^ 2) +
          ∑ i ∈ high, degreeNat i ^ 2 := by
    rw [← Finset.sum_union hdisjoint, hpartition]
  have hdivTotal : p ^ (2 * s) ∣ ∑ i, degreeNat i ^ 2 := by
    rw [htotal]
    exact pow_dvd_pow p h2s
  have hdivHigh : p ^ (2 * s) ∣ ∑ i ∈ high, degreeNat i ^ 2 := by
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨t, hit⟩ := hdegreePow i
    have hst : s ≤ t := by
      apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
      rw [← hit]
      exact (Finset.mem_filter.mp hi).2
    simpa [hit, pow_two, ← pow_add, two_mul] using
      (pow_dvd_pow p (Nat.mul_le_mul_left 2 hst))
  rw [hsplit] at hdivTotal
  exact (Nat.dvd_add_iff_left hdivHigh).mpr hdivTotal

private noncomputable def huppertXI61CharacterDegreeNat
    {Q : Type*} [Group Q] [Finite Q]
    (chi : Theory.Character.ConjClassFunction Q)
    (hchi : Theory.Character.IsConjCharacter chi) : ℕ :=
  Classical.choose hchi

private theorem huppertXI61CharacterDegreeNat_spec
    {Q : Type*} [Group Q] [Finite Q]
    (chi : Theory.Character.ConjClassFunction Q)
    (hchi : Theory.Character.IsConjCharacter chi) :
    ∃ rho : Representation ℂ Q
        (Fin (huppertXI61CharacterDegreeNat chi hchi) → ℂ),
      chi = (Theory.Character.characterClassFunction rho) :=
  Classical.choose_spec hchi

private theorem huppertXI61CharacterDegreeNat_value_one
    {Q : Type*} [Group Q] [Finite Q]
    (chi : Theory.Character.ConjClassFunction Q)
    (hchi : Theory.Character.IsConjCharacter chi) :
    chi (ConjClasses.mk (1 : Q)) =
      (huppertXI61CharacterDegreeNat chi hchi : ℂ) := by
  obtain ⟨rho, hrho⟩ := huppertXI61CharacterDegreeNat_spec chi hchi
  calc
    chi (ConjClasses.mk (1 : Q)) =
        (Theory.Character.characterClassFunction rho) (ConjClasses.mk (1 : Q)) :=
      congrArg (fun psi => psi (ConjClasses.mk (1 : Q))) hrho
    _ = (huppertXI61CharacterDegreeNat chi hchi : ℂ) := by
      change rho.character (1 : Q) =
        (huppertXI61CharacterDegreeNat chi hchi : ℂ)
      simp

private theorem huppertXI61CharacterDegreeNat_dvd_card
    {Q : Type*} [Group Q] [Finite Q]
    (chi : Theory.Character.ConjClassFunction Q)
    (hchi : Theory.Character.IsIrreducibleConjCharacter chi) :
    huppertXI61CharacterDegreeNat chi hchi.1 ∣ Nat.card Q := by
  obtain ⟨rho, hrho⟩ :=
    huppertXI61CharacterDegreeNat_spec chi hchi.1
  have hrhoIrreducible : Representation.IsIrreducible rho := by
    apply (Theory.Character.irreducible_iff_character_norm_one rho).2
    simpa [hrho] using hchi.2
  let : Representation.IsIrreducible rho := hrhoIrreducible
  simpa using Theory.Character.irreducible_dimension_dvd_group_order rho

/-- XI.6.2 in a complete-family form suited to the later Feit count. -/
private theorem huppert_XI_6_2_character_degree_lower_sum_dvd_of_complete_family
    {Q ι : Type*} [Group Q] [Finite Q] [Fintype ι]
    {p n : ℕ} (hp : Nat.Prime p) (hQcard : Nat.card Q = p ^ n)
    (chi : ι → Theory.Character.ConjClassFunction Q)
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi)
    (hsum :
      ∑ i : ι, Complex.normSq (chi i (ConjClasses.mk (1 : Q))) =
        (Nat.card Q : ℝ)) (i0 : ι) :
    let degreeNat : ι → ℕ := fun i =>
      huppertXI61CharacterDegreeNat (chi i) (hchi.1 i).1
    degreeNat i0 ^ 2 ∣
      ∑ i ∈ Finset.univ.filter (fun i => degreeNat i < degreeNat i0),
        degreeNat i ^ 2 := by
  classical
  let degreeNat : ι → ℕ := fun i =>
    huppertXI61CharacterDegreeNat (chi i) (hchi.1 i).1
  have hvalue (i : ι) :
      chi i (ConjClasses.mk (1 : Q)) = (degreeNat i : ℂ) :=
    huppertXI61CharacterDegreeNat_value_one (chi i) (hchi.1 i).1
  have hterm (i : ι) :
      Complex.normSq (chi i (ConjClasses.mk (1 : Q))) =
        (degreeNat i ^ 2 : ℝ) := by
    rw [hvalue]
    norm_num [Complex.normSq, pow_two]
  have hsumReal :
      (∑ i : ι, (degreeNat i ^ 2 : ℝ)) = (Nat.card Q : ℝ) := by
    calc
      (∑ i : ι, (degreeNat i ^ 2 : ℝ)) =
          ∑ i : ι, Complex.normSq (chi i (ConjClasses.mk (1 : Q))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (hterm i).symm
      _ = (Nat.card Q : ℝ) := hsum
  have htotalNat : ∑ i : ι, degreeNat i ^ 2 = Nat.card Q := by
    exact_mod_cast hsumReal
  have hdegreePow : ∀ i, ∃ t : ℕ, degreeNat i = p ^ t := by
    intro i
    have hdiv := huppertXI61CharacterDegreeNat_dvd_card (chi i) (hchi.1 i)
    rw [hQcard] at hdiv
    rcases (Nat.dvd_prime_pow hp).mp hdiv with ⟨t, _ht, hit⟩
    exact ⟨t, hit⟩
  obtain ⟨s, hi0Pow⟩ := hdegreePow i0
  have hi0SqLe : degreeNat i0 ^ 2 ≤ ∑ i : ι, degreeNat i ^ 2 := by
    exact Finset.single_le_sum (fun i _hi => Nat.zero_le (degreeNat i ^ 2))
      (Finset.mem_univ i0)
  have h2s : 2 * s ≤ n := by
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (by
      rw [htotalNat, hQcard, hi0Pow] at hi0SqLe
      simpa [pow_two, ← pow_add, two_mul] using hi0SqLe)
  have htotalPow : ∑ i : ι, degreeNat i ^ 2 = p ^ n :=
    htotalNat.trans hQcard
  simpa [degreeNat, hi0Pow, pow_two, ← pow_add, two_mul] using
    (huppert_XI_6_2_lower_degree_sq_sum_dvd
      p n s hp h2s degreeNat hdegreePow htotalPow)

/-- Huppert--Blackburn XI.6.2: for an irreducible character of a finite
`p`-group, its squared degree divides the sum of the squared smaller
irreducible-character degrees in a complete family. -/
public theorem huppert_XI_6_2_character_degree_lower_sum_dvd
    {Q : Type*} [Group Q] [Finite Q]
    (p n : ℕ) (hp : Nat.Prime p) (hQcard : Nat.card Q = p ^ n)
    (chi0 : Theory.Character.ConjClassFunction Q)
    (hchi0 : Theory.Character.IsIrreducibleConjCharacter chi0) :
    ∃ (ι : Type) (_ : Fintype ι)
      (chi : ι → Theory.Character.ConjClassFunction Q) (i0 : ι)
      (degreeNat : ι → ℕ),
      Theory.Character.IsCompleteIrreducibleCharacterFamily chi ∧
        chi i0 = chi0 ∧
        (∀ i, chi i (ConjClasses.mk (1 : Q)) = (degreeNat i : ℂ)) ∧
        degreeNat i0 ^ 2 ∣
          ∑ i ∈ Finset.univ.filter
            (fun i => degreeNat i < degreeNat i0), degreeNat i ^ 2 := by
  classical
  obtain ⟨ι, hι, chi, hchi, hsum⟩ :=
    Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := Q)
  let : Fintype ι := hι
  obtain ⟨i0, hi0⟩ := hchi.2.1 chi0 hchi0
  let degreeNat : ι → ℕ := fun i =>
    huppertXI61CharacterDegreeNat (chi i) (hchi.1 i).1
  have hvalue : ∀ i, chi i (ConjClasses.mk (1 : Q)) = (degreeNat i : ℂ) :=
    fun i => huppertXI61CharacterDegreeNat_value_one (chi i) (hchi.1 i).1
  refine ⟨ι, hι, chi, i0, degreeNat, hchi, hi0, hvalue, ?_⟩
  simpa [degreeNat] using
    (huppert_XI_6_2_character_degree_lower_sum_dvd_of_complete_family
      hp hQcard chi hchi hsum i0)

private theorem huppert_XI_6_2_degree_sq_le_lower_sum
    {Q ι : Type*} [Group Q] [Finite Q] [Fintype ι]
    (chi : ι → Theory.Character.ConjClassFunction Q)
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi)
    (degreeNat : ι → ℕ)
    (hvalue : ∀ i, chi i (ConjClasses.mk (1 : Q)) = (degreeNat i : ℂ))
    (i0 : ι) (hdegree : 1 < degreeNat i0)
    (hdvd : degreeNat i0 ^ 2 ∣
      ∑ i ∈ Finset.univ.filter
        (fun i => degreeNat i < degreeNat i0), degreeNat i ^ 2) :
    degreeNat i0 ^ 2 ≤
      ∑ i ∈ Finset.univ.filter
        (fun i => degreeNat i < degreeNat i0), degreeNat i ^ 2 := by
  classical
  let rho0 : Representation ℂ Q (Fin 1 → ℂ) :=
    Representation.trivial ℂ Q (Fin 1 → ℂ)
  have hrho0 : Representation.IsIrreducible rho0 := by
    let e : rho0 ≃ₗ Representation.trivial ℂ Q ℂ :=
      Theory.Representation.RepEquiv.mk
        (LinearEquiv.funUnique (Fin 1) ℂ ℂ) (by
          intro g
          ext v
          simp [rho0])
    exact (Theory.Representation.RepEquiv.irreducible_euqiv e).2
      Theory.Character.trivial_complex_irreducible
  let chi0 : Theory.Character.ConjClassFunction Q :=
    Theory.Character.characterClassFunction rho0
  have hchi0 : Theory.Character.IsIrreducibleConjCharacter chi0 := by
    refine ⟨⟨1, rho0, rfl⟩, ?_⟩
    exact (Theory.Character.irreducible_iff_character_norm_one rho0).1 hrho0
  obtain ⟨j0, hj0⟩ := hchi.2.1 chi0 hchi0
  have hdegreeJ0 : degreeNat j0 = 1 := by
    have h := hvalue j0
    rw [hj0] at h
    have hchi0one : chi0 (ConjClasses.mk (1 : Q)) = 1 := by
      dsimp [chi0]
      change rho0.character (1 : Q) = 1
      simp [rho0]
    rw [hchi0one] at h
    exact_mod_cast h.symm
  have hj0mem : j0 ∈ Finset.univ.filter
      (fun i => degreeNat i < degreeNat i0) := by
    simp [hdegreeJ0, hdegree]
  have hsumPos : 0 <
      ∑ i ∈ Finset.univ.filter
        (fun i => degreeNat i < degreeNat i0), degreeNat i ^ 2 := by
    have hone : 1 ≤
        ∑ i ∈ Finset.univ.filter
          (fun i => degreeNat i < degreeNat i0), degreeNat i ^ 2 := by
      have htemp : degreeNat j0 ^ 2 ≤
          ∑ i ∈ Finset.univ.filter
            (fun i => degreeNat i < degreeNat i0), degreeNat i ^ 2 :=
        Finset.single_le_sum
          (fun i _hi => Nat.zero_le (degreeNat i ^ 2)) hj0mem
      rw [hdegreeJ0] at htemp
      exact htemp
    omega
  exact Nat.le_of_dvd hsumPos hdvd

private theorem huppert_XI_6_1_actor_card_dvd_group_card_sub_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, a • v = v → v = 1) :
    Nat.card A ∣ Nat.card V - 1 := by
  classical
  let V0 := {v : V // v ≠ 1}
  let : MulAction A V0 :=
    { smul := fun a v => ⟨a • (v : V), by
        intro h
        apply v.2
        have h' := congrArg (fun x : V => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro v
        apply Subtype.ext
        change (1 : A) • (v : V) = (v : V)
        simp
      mul_smul := by
        intro a b v
        apply Subtype.ext
        change (a * b) • (v : V) = a • (b • (v : V))
        rw [mul_smul] }
  have hstab : ∀ v : V0, MulAction.stabilizer A v = ⊥ := by
    intro v
    rw [eq_bot_iff]
    intro a ha
    have hav : a • v = v := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact v.2 (hfree a hane (v : V) (congrArg Subtype.val hav))
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardV0 : Nat.card V0 = Nat.card V - 1 := by
    let : Fintype V := Fintype.ofFinite V
    let : Fintype V0 := Fintype.ofFinite V0
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {v : V // v ≠ 1} = Fintype.card V - 1
    simp
  rw [hcardV0, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A V0)), by
    rw [mul_comm]
    exact hcard⟩


/-- A pointwise fixed-point-free coprime action on a finite solvable group is
still pointwise fixed-point-free on its abelianization. -/
private theorem huppert_XI_6_1_abelianization_fixedPointFree
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q]
    (hsolv : Group.IsSolvable Q)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card Q))
    (hfree : ∀ a : A, a ≠ 1 → ∀ q : Q, a • q = q → q = 1) :
    let C := commutator Q
    let hCinv : IsInvariant A Q C :=
      isInvariant_of_characteristic (A := A) (G := Q) C
    letI : MulDistribMulAction A (Q ⧸ C) :=
      quotientMulDistribMulAction (A := A) (G := Q) C hCinv
    ∀ a : A, a ≠ 1 → ∀ x : Q ⧸ C, a • x = x → x = 1 := by
  dsimp only
  let C := commutator Q
  let hCinv : IsInvariant A Q C :=
    isInvariant_of_characteristic (A := A) (G := Q) C
  let : MulDistribMulAction A (Q ⧸ C) :=
    quotientMulDistribMulAction (A := A) (G := Q) C hCinv
  have : C.Normal := by dsimp [C]; infer_instance
  intro a ha x hx
  let S := Subgroup.zpowers a
  have hScardDvd : Nat.card S ∣ Nat.card A :=
    Subgroup.card_subgroup_dvd_card S
  have hcopS : Nat.Coprime (Nat.card S) (Nat.card Q) :=
    Nat.Coprime.of_dvd_left hScardDvd hcop
  let hCinvS : IsInvariant S Q C :=
    isInvariant_of_characteristic (A := S) (G := Q) C
  have hquot := fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
    (G := Q) (A := S) hsolv hcopS C hCinvS
  have hfixQ : fixedPointSubgroup (↥S) Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    have hqa : a • (q : Q) = q := by
      simpa [S] using hq (⟨a, Subgroup.mem_zpowers a⟩ : S)
    exact hfree a ha q hqa
  rw [hfixQ] at hquot
  have hquotBot : fixedPointSubgroup (↥S) (Q ⧸ C) = ⊥ := by
    simpa [C] using hquot
  have hxS : x ∈ fixedPointSubgroup (↥S) (Q ⧸ C) := by
    change ∀ s : S, s • x = x
    intro s
    apply smul_eq_self_of_mem_zpowers (y := (⟨a, Subgroup.mem_zpowers a⟩ : S))
    · rcases Subgroup.mem_zpowers_iff.mp s.property with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    · simpa [S] using hx
  rw [hquotBot] at hxS
  simpa using hxS
/-- The abelianization of a nontrivial finite solvable group is nontrivial. -/
private theorem huppert_XI_6_3_abelianization_one_lt_card
    {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    (hsolv : Group.IsSolvable Q) :
    1 < Nat.card (Q ⧸ commutator Q) := by
  let : Group.IsSolvable Q := hsolv
  have hcommLt : commutator Q < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)
  have hindex : 1 < (commutator Q).index :=
    Subgroup.one_lt_index_of_ne_top hcommLt.ne
  simpa [Subgroup.index_eq_card] using hindex

/-- A nontrivial cardinal congruent to one modulo `d` is at least `d + 1`. -/
private theorem huppert_XI_6_3_dvd_sub_one_card_lower
    (d L : ℕ) (hL : 1 < L) (hdiv : d ∣ L - 1) :
    d + 1 ≤ L := by
  have hdle : d ≤ L - 1 := Nat.le_of_dvd (by omega) hdiv
  omega

/-- If both cardinals are odd, a nontrivial cardinal congruent to one modulo
`d` is at least `2*d + 1`. -/
private theorem huppert_XI_6_3_odd_dvd_sub_one_card_lower
    (d L : ℕ) (hL : 1 < L)
    (hoddD : Odd d) (hoddL : Odd L) (hdiv : d ∣ L - 1) :
    2 * d + 1 ≤ L := by
  obtain ⟨k, hk⟩ := hdiv
  have hLsubPos : 0 < L - 1 := by omega
  have hkPos : 0 < k := by
    by_contra hk0
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkZero, mul_zero] at hk
    omega
  have hprodEven : Even (d * k) := by
    rw [← hk]
    rcases hoddL with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  have hkEven : Even k :=
    (Nat.even_mul.mp hprodEven).resolve_left
      (Nat.not_even_iff_odd.mpr hoddD)
  rcases hkEven with ⟨j, hj⟩
  have hkTwo : 2 ≤ k := by omega
  have htwoD : 2 * d ≤ d * k := by nlinarith
  rw [← hk] at htwoD
  omega
/-- A characteristic nontrivial solvable factor inherits a coprime
fixed-point-free action, so its abelianization is nontrivial and has cardinal
congruent to one modulo the actor cardinal. -/
private theorem huppert_XI_6_3_characteristic_factor_abelianization_data
    {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q]
    (P : Subgroup Q) [P.Characteristic] [Nontrivial P]
    (hsolv : Group.IsSolvable P)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ q : Q, d • q = q → q = 1) :
    Nat.card D ∣ Nat.card (Abelianization P) - 1 ∧
      1 < Nat.card (Abelianization P) := by
  let : IsInvariant D Q P := isInvariant_of_characteristic P
  have hcopP : Nat.Coprime (Nat.card D) (Nat.card P) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_subgroup_dvd_card P) hcop
  have hfreeP : ∀ d : D, d ≠ 1 → ∀ x : P, d • x = x → x = 1 := by
    intro d hd x hx
    apply Subtype.ext
    exact hfree d hd (x : Q) (congrArg Subtype.val hx)
  let C := commutator P
  let hCinv : IsInvariant D P C :=
    isInvariant_of_characteristic (A := D) (G := P) C
  let : MulDistribMulAction D (P ⧸ C) :=
    quotientMulDistribMulAction (A := D) (G := P) C hCinv
  have hfreeAb :
      ∀ d : D, d ≠ 1 → ∀ x : P ⧸ C, d • x = x → x = 1 := by
    simpa [C] using
      (huppert_XI_6_1_abelianization_fixedPointFree hsolv hcopP hfreeP)
  constructor
  · simpa [Abelianization, C] using
      (huppert_XI_6_1_actor_card_dvd_group_card_sub_one hfreeAb)
  · simpa [Abelianization, C] using
      (huppert_XI_6_3_abelianization_one_lt_card hsolv)
/-- Inflate a linear character of the abelianization back to the group. -/
private noncomputable def huppert_XI_6_3_abelianizationLinearCharacter
    {Q : Type*} [Group Q]
    (chi : Abelianization Q →* ℂˣ) : Section1.ClassFunction Q :=
  Section1.characterInflationByHom Abelianization.of chi

private theorem huppert_XI_6_3_abelianizationLinearCharacter_degree
    {Q : Type*} [Group Q]
    (chi : Abelianization Q →* ℂˣ) :
    Section1.degree (huppert_XI_6_3_abelianizationLinearCharacter chi) = 1 := by
  simp [huppert_XI_6_3_abelianizationLinearCharacter, Section1.degree,
    Section1.characterInflationByHom]

private theorem huppert_XI_6_3_abelianizationLinearCharacter_irreducible
    {Q : Type*} [Group Q] [Finite Q]
    (chi : Abelianization Q →* ℂˣ) :
    Section1.IsIrreducibleCharacterOnGroup
      (huppert_XI_6_3_abelianizationLinearCharacter chi) := by
  exact Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
    Abelianization.of chi

private theorem huppert_XI_6_3_abelianizationLinearCharacter_injective
    {Q : Type*} [Group Q] :
    Function.Injective
      (huppert_XI_6_3_abelianizationLinearCharacter (Q := Q)) := by
  intro chi psi h
  apply DFunLike.ext chi psi
  intro q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (commutator Q) q
  apply Units.ext
  have hval := congrFun h x
  change (chi (Abelianization.of x) : ℂ) =
    (psi (Abelianization.of x) : ℂ) at hval
  rw [← hx]
  exact hval

private theorem huppert_XI_6_3_abelianizationLinearCharacter_card
    {Q : Type*} [Group Q] [Finite Q] :
    Nat.card (Abelianization Q →* ℂˣ) = Nat.card (Abelianization Q) := by
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent (Abelianization Q)) := by
    have : NeZero (Monoid.exponent (Abelianization Q)) := by infer_instance
    exact Section1.complex_hasEnoughRootsOfUnity
      (Monoid.exponent (Abelianization Q))
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Abelianization Q) ℂ
/-- Combine linear characters of two direct factors and transport them to the
abelianization of the product group. -/
private noncomputable def huppert_XI_6_3_productLinearCharacter
    {A B Q : Type*} [Group A] [Group B] [Group Q]
    (e : A × B ≃* Q)
    (chi : Abelianization A →* ℂˣ)
    (psi : Abelianization B →* ℂˣ) :
    Abelianization Q →* ℂˣ :=
  Abelianization.lift
    ((MonoidHom.coprod
      (chi.comp Abelianization.of)
      (psi.comp Abelianization.of)).comp e.symm.toMonoidHom)

set_option backward.isDefEq.respectTransparency false in
private theorem huppert_XI_6_3_productLinearCharacter_injective
    {A B Q : Type*} [Group A] [Group B] [Group Q]
    (e : A × B ≃* Q) :
    Function.Injective
      (fun x : (Abelianization A →* ℂˣ) ×
          (Abelianization B →* ℂˣ) =>
        huppert_XI_6_3_productLinearCharacter e x.1 x.2) := by
  intro x y hxy
  have hfirst : x.1 = y.1 := by
    apply DFunLike.ext _ _
    intro a
    obtain ⟨a0, rfl⟩ := QuotientGroup.mk'_surjective (commutator A) a
    have hval := DFunLike.congr_fun hxy
      (Abelianization.of (e (a0, 1)))
    have htemp : x.1 (Abelianization.of a0) = y.1 (Abelianization.of a0) := by
      have : huppert_XI_6_3_productLinearCharacter e x.1 x.2 (Abelianization.of (e (a0, 1))) =
          huppert_XI_6_3_productLinearCharacter e y.1 y.2 (Abelianization.of (e (a0, 1))) := hval
      unfold huppert_XI_6_3_productLinearCharacter at this
      simpa [MonoidHom.coprod_apply, MonoidHom.comp_apply,
        MulEquiv.symm_apply_apply, MonoidHom.map_one, mul_one] using this
    simpa [show a = Abelianization.of a0 from rfl.symm,
      Abelianization.of] using htemp
  have hsecond : x.2 = y.2 := by
    apply DFunLike.ext _ _
    intro b
    obtain ⟨b0, rfl⟩ := QuotientGroup.mk'_surjective (commutator B) b
    have hval := DFunLike.congr_fun hxy
      (Abelianization.of (e (1, b0)))
    have htemp : x.2 (Abelianization.of b0) = y.2 (Abelianization.of b0) := by
      have : huppert_XI_6_3_productLinearCharacter e x.1 x.2 (Abelianization.of (e (1, b0))) =
          huppert_XI_6_3_productLinearCharacter e y.1 y.2 (Abelianization.of (e (1, b0))) := hval
      unfold huppert_XI_6_3_productLinearCharacter at this
      simpa [MonoidHom.coprod_apply, MonoidHom.comp_apply,
        MulEquiv.symm_apply_apply, MonoidHom.map_one, mul_one] using this
    simpa [show b = Abelianization.of b0 from rfl.symm,
      Abelianization.of] using htemp
  exact Prod.ext hfirst hsecond

/-- The abelianization of a direct product has at least the product of the
abelianization cardinals of its two factors. -/
private theorem huppert_XI_6_3_product_abelianization_card_le
    {A B Q : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Group Q] [Finite Q]
    (e : A × B ≃* Q) :
    Nat.card (Abelianization A) * Nat.card (Abelianization B) ≤
      Nat.card (Abelianization Q) := by
  let CharA := Abelianization A →* ℂˣ
  let CharB := Abelianization B →* ℂˣ
  let CharQ := Abelianization Q →* ℂˣ
  let : Fintype CharA := Fintype.ofFinite _
  let : Fintype CharB := Fintype.ofFinite _
  let : Fintype CharQ := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective
    (fun x : CharA × CharB =>
      huppert_XI_6_3_productLinearCharacter e x.1 x.2)
    (huppert_XI_6_3_productLinearCharacter_injective e)
  rw [Fintype.card_prod] at hcard
  have hA : Fintype.card CharA = Nat.card (Abelianization A) := by
    rw [← Nat.card_eq_fintype_card]
    exact huppert_XI_6_3_abelianizationLinearCharacter_card (Q := A)
  have hB : Fintype.card CharB = Nat.card (Abelianization B) := by
    rw [← Nat.card_eq_fintype_card]
    exact huppert_XI_6_3_abelianizationLinearCharacter_card (Q := B)
  have hQ : Fintype.card CharQ = Nat.card (Abelianization Q) := by
    rw [← Nat.card_eq_fintype_card]
    exact huppert_XI_6_3_abelianizationLinearCharacter_card (Q := Q)
  change Fintype.card CharA * Fintype.card CharB ≤
    Fintype.card CharQ at hcard
  rw [hA, hB, hQ] at hcard
  exact hcard
/-- The elementary cardinal parameters of the Zassenhaus action, placed
before the XI.1.5 helpers that use them. -/
private theorem huppert_XI_6_1_action_parameters_core
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    Fintype.card Omega = Nat.card F + 1 ∧
      Nat.card (MulAction.stabilizer G a) =
        Nat.card F * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card G = Fintype.card Omega * Nat.card F * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣
        Nat.card F - 1 := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change Fintype.card Omega = Nat.card F + 1 ∧
    Nat.card H = Nat.card F * Nat.card D ∧
    Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D ∧
    Nat.card D ∣ Nat.card F - 1
  have hOmegaCard : 1 < Fintype.card Omega :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  let n := Fintype.card Omega - 1
  have hdegree : Fintype.card Omega = n + 1 := by
    dsimp [n]
    omega
  have hFcard : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo a b hab F hFrob
  have hOmegaEq : Fintype.card Omega = Nat.card F + 1 := by
    rw [hFcard, ← hdegree]
  have hHcard : Nat.card H = Nat.card F * Nat.card D :=
    hFrob.isComplement'.card_mul_card.symm
  have hGcard : Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D := by
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex : H.index = Fintype.card Omega := by
      calc
        H.index = Nat.card Omega := MulAction.index_stabilizer_of_transitive G a
        _ = Fintype.card Omega := Nat.card_eq_fintype_card
    have hmul := H.card_mul_index
    rw [hindex] at hmul
    calc
      Nat.card G = Nat.card H * Fintype.card Omega := hmul.symm
      _ = Fintype.card Omega * Nat.card F * Nat.card D := by
        rw [hHcard]
        ac_rfl
  have hdiv : Nat.card D ∣ Nat.card F - 1 := by
    let : F.Normal := hFrob.normal
    let : MulDistribMulAction D F :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer D F
        (Subgroup.le_normalizer_of_normal (H := F))
    apply huppert_XI_6_1_actor_card_dvd_group_card_sub_one
    intro d hd f hfix
    have hconj : (d : H) * (f : H) * (d : H)⁻¹ = (f : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (d : H) * (f : H) = (f : H) * (d : H) := by
      have h := congrArg (fun x : H => x * (d : H)) hconj
      simpa [mul_assoc] using h
    have hfcent : (f : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨f.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hfbot : (f : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hfcent
    exact Subtype.ext (by simpa using hfbot)
  exact ⟨hOmegaEq, hHcard, hGcard, hdiv⟩

/-- XI.1.4(b), in the prime-power form needed here: a nilpotent Frobenius
kernel is a p-group as soon as the complement has at least half the
nonidentity kernel size. -/
private theorem huppert_XI_1_4_b_primePower_of_large_complement
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFnil : Group.IsNilpotent F)
    (hlarge : Nat.card F - 1 ≤ 2 * Nat.card D) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ Nat.card F = p ^ f := by
  classical
  let : F.Normal := hFrob.normal
  have hFnontrivial : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  let : Nontrivial F := hFnontrivial
  have hFcard_ne_one : Nat.card F ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr hFnontrivial)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hFcard_ne_one
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hzne : z ≠ 1 := by
    intro hz
    have hpone : p = 1 := by simpa [hz] using hzorder.symm
    exact hp.ne_one hpone
  have hzp : IsPGroup p (Subgroup.zpowers z) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hdiv : orderOf (x : F) ∣ orderOf z :=
      orderOf_dvd_of_mem_zpowers x.property
    have hdivp : orderOf (x : F) ∣ p ^ 1 := by
      simpa [hzorder] using hdiv
    rcases (Nat.dvd_prime_pow hp).mp hdivp with ⟨m, _hm, hm⟩
    exact ⟨m, by simpa [Subgroup.orderOf_coe] using hm⟩
  obtain ⟨P, hzP⟩ := IsPGroup.exists_le_sylow hzp
  have hzmemP : z ∈ (P : Subgroup F) := hzP (Subgroup.mem_zpowers z)
  have hPnormal : (P : Subgroup F).Normal :=
    Group.IsNilpotent.sylow_normal hFnil p P
  let : (P : Subgroup F).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  let Pmap : Subgroup H := (P : Subgroup F).map F.subtype
  have hPmapNormal : Pmap.Normal := by
    simpa [Pmap] using
      (ConjAct.normal_of_characteristic_of_normal
        (H := F) (K := (P : Subgroup F)))
  let : Pmap.Normal := hPmapNormal
  let : MulDistribMulAction D Pmap :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D Pmap
      (Subgroup.le_normalizer_of_normal (H := Pmap))
  have hfree :
      ∀ d : D, d ≠ 1 → ∀ x : Pmap, d • x = x → x = 1 := by
    intro d hd x hfix
    have hconj : (d : H) * (x : H) * (d : H)⁻¹ = (x : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (d : H) * (x : H) = (x : H) * (d : H) := by
      have h := congrArg (fun y : H => y * (d : H)) hconj
      simpa [mul_assoc] using h
    have hxF : (x : H) ∈ F := by
      rcases x.property with ⟨y, hyP, hyx⟩
      rw [← hyx]
      exact y.property
    have hxcent : (x : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨hxF, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hxcent
    exact Subtype.ext (by simpa using hxbot)
  have hdivD : Nat.card D ∣ Nat.card Pmap - 1 :=
    huppert_XI_6_1_actor_card_dvd_group_card_sub_one hfree
  let zPmap : Pmap := ⟨(z : H), ⟨z, hzmemP, rfl⟩⟩
  have hzPmap_ne : zPmap ≠ 1 := by
    intro hz
    apply hzne
    exact F.subtype_injective (congrArg Subtype.val hz)
  have hPmap_ne : Pmap ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨zPmap, hzPmap_ne⟩
  have hPmap_nontrivial : Nontrivial Pmap :=
    (Subgroup.nontrivial_iff_ne_bot Pmap).2 hPmap_ne
  have hPmap_card_gt : 1 < Nat.card Pmap :=
    Finite.one_lt_card_iff_nontrivial.mpr hPmap_nontrivial
  have hDle : Nat.card D ≤ Nat.card Pmap - 1 :=
    Nat.le_of_dvd (by omega) hdivD
  have hPmap_card : Nat.card Pmap = Nat.card (P : Subgroup F) := by
    simpa [Pmap] using
      (Subgroup.card_map_of_injective
        (K := (P : Subgroup F)) (f := F.subtype) F.subtype_injective)
  have hPmap_dvd_F : Nat.card Pmap ∣ Nat.card F := by
    rw [hPmap_card]
    exact Subgroup.card_subgroup_dvd_card (P : Subgroup F)
  have hlt : Nat.card F < 2 * Nat.card Pmap := by omega
  have hFcard : Nat.card F = Nat.card Pmap :=
    Nat.eq_of_dvd_of_lt_two_mul Nat.card_pos.ne' hPmap_dvd_F hlt
  obtain ⟨f, hPpow⟩ := P.isPGroup'.exists_card_eq
  have hfpos : 0 < f := by
    by_contra hf
    have hfzero : f = 0 := Nat.eq_zero_of_not_pos hf
    have hPone : Nat.card (P : Subgroup F) = 1 := by
      simpa [hfzero] using hPpow
    have hPmap_one : Nat.card Pmap = 1 := hPmap_card.trans hPone
    omega
  exact ⟨p, f, hp, hfpos, hFcard.trans (hPmap_card.trans hPpow)⟩


/-- Membership in the ambient image of a two-point stabilizer is exactly
fixing both distinguished points. -/
private theorem twoPointStabilizer_map_mem_iff
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b) (g : G) :
    g ∈
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype ↔
      g • a = a ∧ g • b = b := by
  constructor
  · rintro ⟨h, hhD, rfl⟩
    exact ⟨h.property,
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hhD)⟩
  · rintro ⟨hga, hgb⟩
    let h : MulAction.stabilizer G a := ⟨g, hga⟩
    let d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
      ⟨h, by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        exact hgb⟩
    exact ⟨d, d.property, rfl⟩

/-- Any element interchanging the distinguished points normalizes their
pointwise stabilizer. -/
private theorem zassenhaus_swap_mem_twoPointStabilizer_normalizer
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b) (s : G)
    (hsa : s • a = b) (hsb : s • b = a) :
    s ∈ Subgroup.normalizer
      (((MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
          (MulAction.stabilizer G a).subtype : Subgroup G) : Set G) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  have hsinva : s⁻¹ • a = b := by
    calc
      s⁻¹ • a = s⁻¹ • (s • b) := by rw [hsb]
      _ = b := inv_smul_smul s b
  have hsinvb : s⁻¹ • b = a := by
    calc
      s⁻¹ • b = s⁻¹ • (s • a) := by rw [hsa]
      _ = a := inv_smul_smul s a
  change s ∈ Subgroup.normalizer (Dg : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
    simpa [H, D, Dg] using twoPointStabilizer_map_mem_iff a b hab g]
  rw [show s * g * s⁻¹ ∈ Dg ↔
      (s * g * s⁻¹) • a = a ∧ (s * g * s⁻¹) • b = b by
    simpa [H, D, Dg] using
      twoPointStabilizer_map_mem_iff a b hab (s * g * s⁻¹)]
  constructor
  · rintro ⟨hga, hgb⟩
    constructor
    · simp only [mul_smul, hsinva, hgb, hsb]
    · simp only [mul_smul, hsinvb, hga, hsa]
  · rintro ⟨hcga, hcgb⟩
    constructor
    · calc
        g • a = s⁻¹ • ((s * g * s⁻¹) • (s • a)) := by
          simp only [mul_smul, inv_smul_smul]
        _ = s⁻¹ • ((s * g * s⁻¹) • b) := by rw [hsa]
        _ = s⁻¹ • b := by rw [hcgb]
        _ = a := hsinvb
    · calc
        g • b = s⁻¹ • ((s * g * s⁻¹) • (s • b)) := by
          simp only [mul_smul, inv_smul_smul]
        _ = s⁻¹ • ((s * g * s⁻¹) • a) := by rw [hsb]
        _ = s⁻¹ • a := by rw [hcga]
        _ = b := hsinva

/-- An ambient normalizer element outside the two-point stabilizer
interchanges the two distinguished points. -/
private theorem zassenhaus_twoPointStabilizer_normalizer_notMem_swaps
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (x : G)
    (hxnorm :
      x ∈ Subgroup.normalizer
        (((MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype : Subgroup G) : Set G))
    (hxnot :
      x ∉
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype) :
    x • a = b ∧ x • b = a := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  let zg : G := ((z : H) : G)
  have hzgD : zg ∈ Dg := by
    exact ⟨(z : H), z.property, rfl⟩
  have hzgne : zg ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzga : zg • a = a := (z : H).property
  have hzgb : zg • b = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp z.property)
  have hxconjD : x * zg * x⁻¹ ∈ Dg :=
    (Subgroup.mem_normalizer_iff.mp (by simpa [H, D, Dg] using hxnorm) zg).mp hzgD
  have hxconjne : x * zg * x⁻¹ ≠ 1 := by
    intro h
    apply hzgne
    have := congrArg (fun q : G => x⁻¹ * q * x) h
    simpa [mul_assoc] using this
  have hxconjfix :=
    (twoPointStabilizer_map_mem_iff a b hab (x * zg * x⁻¹)).mp (by
      simpa [H, D, Dg] using hxconjD)
  have himage (c : Omega) (hzc : zg • c = c) :
      x • c = a ∨ x • c = b := by
    by_cases hca : x • c = a
    · exact Or.inl hca
    by_cases hcb : x • c = b
    · exact Or.inr hcb
    exfalso
    apply
      (hat_most_two_fixed_points
        (x * zg * x⁻¹) hxconjne a b (x • c)
        hab (Ne.symm hca) (Ne.symm hcb))
    refine ⟨hxconjfix.1, hxconjfix.2, ?_⟩
    calc
      (x * zg * x⁻¹) • (x • c) = x • (zg • c) := by
        simp only [mul_smul, inv_smul_smul]
      _ = x • c := by rw [hzc]
  have hxa := himage a hzga
  have hxb := himage b hzgb
  rcases hxa with hxa | hxa
  · have hxb' : x • b = b := by
      rcases hxb with hxba | hxbb
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxa, hxba]
      · exact hxbb
    exfalso
    apply hxnot
    apply (twoPointStabilizer_map_mem_iff a b hab x).mpr
    exact ⟨hxa, hxb'⟩
  · have hxb' : x • b = a := by
      rcases hxb with hxba | hxbb
      · exact hxba
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxa, hxbb]
    exact ⟨hxa, hxb'⟩

/-- The ambient normalizer of a nontrivial two-point stabilizer has index two
over that stabilizer: its elements either fix or interchange the two points. -/
private theorem zassenhaus_twoPointStabilizer_normalizer_index_two
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg := D.map H.subtype
    (Dg.subgroupOf (Subgroup.normalizer (Dg : Set G))).index = 2 := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change Dsub.index = 2
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  let zg : G := ((z : H) : G)
  have hzgD : zg ∈ Dg := by
    exact ⟨(z : H), z.property, rfl⟩
  have hzgne : zg ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzga : zg • a = a := (z : H).property
  have hzgb : zg • b = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp z.property)
  obtain ⟨s, hsa, hsb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hab hab.symm
  have hsinva : s⁻¹ • a = b := by
    rw [← hsb, inv_smul_smul]
  have hsinvb : s⁻¹ • b = a := by
    rw [← hsa, inv_smul_smul]
  have hsT : s ∈ T := by
    rw [show T = Subgroup.normalizer (Dg : Set G) from rfl,
      Subgroup.mem_normalizer_iff]
    intro g
    rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
      simpa [H, D, Dg] using twoPointStabilizer_map_mem_iff a b hab g]
    rw [show s * g * s⁻¹ ∈ Dg ↔
        (s * g * s⁻¹) • a = a ∧ (s * g * s⁻¹) • b = b by
      simpa [H, D, Dg] using
        twoPointStabilizer_map_mem_iff a b hab (s * g * s⁻¹)]
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hsinva, hgb, hsb]
      · simp only [mul_smul, hsinvb, hga, hsa]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = s⁻¹ • ((s * g * s⁻¹) • (s • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = s⁻¹ • ((s * g * s⁻¹) • b) := by rw [hsa]
          _ = s⁻¹ • b := by rw [hcgb]
          _ = a := hsinvb
      · calc
          g • b = s⁻¹ • ((s * g * s⁻¹) • (s • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = s⁻¹ • ((s * g * s⁻¹) • a) := by rw [hsb]
          _ = s⁻¹ • a := by rw [hcga]
          _ = b := hsinva
  let sT : T := ⟨s, hsT⟩
  have hsTnot : sT ∉ Dsub := by
    intro hsD
    have hsDg : s ∈ Dg := hsD
    have hsfix :=
      (twoPointStabilizer_map_mem_iff a b hab s).mp (by
        simpa [H, D, Dg] using hsDg)
    exact hab (hsfix.1.symm.trans hsa)
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨sT, hsTnot, ?_⟩
  intro x
  by_cases hxD : (x : G) ∈ Dg
  · exact Or.inr hxD
  · have hxswap :
        (x : G) • a = b ∧ (x : G) • b = a := by
      exact zassenhaus_twoPointStabilizer_normalizer_notMem_swaps
        hat_most_two_fixed_points a b hab F hFrob (x : G)
        (by
          change (x : G) ∈ T
          exact x.2) (by exact hxD)
    left
    change ((x * sT : T) : G) ∈ Dg
    apply (twoPointStabilizer_map_mem_iff a b hab ((x * sT : T) : G)).mpr
    constructor
    · change ((x : G) * s) • a = a
      rw [mul_smul, hsa, hxswap.2]
    · change ((x : G) * s) • b = b
      rw [mul_smul, hsb, hxswap.1]

/-- When the two-point stabilizer has odd order, its index-two ambient
normalizer contains an involution interchanging the two points. -/
public theorem zassenhaus_odd_twoPointStabilizer_exists_swap_involution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    ∃ s : G, s ^ 2 = 1 ∧ s • a = b ∧ s • b = a := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      zassenhaus_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  have hcop : (Nat.card Dsub).Coprime Dsub.index := by
    rw [hindex, hDsubcard]
    simpa [D] using hodd.coprime_two_right
  obtain ⟨C, hC⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hCcard : Nat.card C = 2 :=
    hC.index_eq_card.symm.trans hindex
  have hCnontrivial : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial C := hCnontrivial
  obtain ⟨c, hcne⟩ := exists_ne (1 : C)
  have hcnotD : (c : T) ∉ Dsub := by
    intro hcD
    have hcone : (c : T) = 1 :=
      Subgroup.disjoint_def.mp hC.disjoint c.property hcD
    apply hcne
    exact Subtype.ext hcone
  have hcpowC : c ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa [hCcard] using orderOf_dvd_natCard c
  have hcpowG : (((c : C) : T) : G) ^ 2 = 1 := by
    simpa using congrArg (fun q : C => (((q : C) : T) : G)) hcpowC
  have hcswap :
      (((c : C) : T) : G) • a = b ∧
        (((c : C) : T) : G) • b = a := by
    apply zassenhaus_twoPointStabilizer_normalizer_notMem_swaps
      hat_most_two_fixed_points a b hab F hFrob
    · change (((c : C) : T) : G) ∈ T
      exact ((c : C) : T).2
    · intro hcDg
      apply hcnotD
      exact hcDg
  exact ⟨(((c : C) : T) : G), hcpowG, hcswap⟩

/-- The normalizer of a nontrivial subgroup of the two-point stabilizer
already normalizes the whole two-point stabilizer.  This is the fixed-point
argument used in XI.1.5 before applying Burnside transfer. -/
private theorem zassenhaus_twoPointSubgroup_normalizer_le
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (Q : Subgroup G)
    (hQle :
      Q ≤
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype)
    (hQne : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer
        (((MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype : Subgroup G) : Set G) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  change Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Dg : Set G)
  intro x hx
  obtain ⟨zQ, hzQne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  let z : G := zQ
  have hzQ : z ∈ Q := zQ.property
  have hzne : z ≠ 1 := by
    intro hz
    apply hzQne
    exact Subtype.ext hz
  have hzD : z ∈ Dg := by simpa [H, D, Dg] using hQle hzQ
  have hzfix : z • a = a ∧ z • b = b :=
    (twoPointStabilizer_map_mem_iff a b hab z).mp (by
      simpa [H, D, Dg] using hzD)
  have hxzQ : x * z * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hx z).mp hzQ
  have hxzD : x * z * x⁻¹ ∈ Dg := by
    simpa [H, D, Dg] using hQle hxzQ
  have hxzne : x * z * x⁻¹ ≠ 1 := by
    intro h
    apply hzne
    have := congrArg (fun q : G => x⁻¹ * q * x) h
    simpa [mul_assoc] using this
  have hxzfix :
      (x * z * x⁻¹) • a = a ∧ (x * z * x⁻¹) • b = b :=
    (twoPointStabilizer_map_mem_iff a b hab (x * z * x⁻¹)).mp (by
      simpa [H, D, Dg] using hxzD)
  have himage (c : Omega) (hzc : z • c = c) :
      x • c = a ∨ x • c = b := by
    by_cases hca : x • c = a
    · exact Or.inl hca
    by_cases hcb : x • c = b
    · exact Or.inr hcb
    exfalso
    apply
      (hat_most_two_fixed_points (x * z * x⁻¹) hxzne a b (x • c)
        hab (Ne.symm hca) (Ne.symm hcb))
    refine ⟨hxzfix.1, hxzfix.2, ?_⟩
    calc
      (x * z * x⁻¹) • (x • c) = x • (z • c) := by
        simp only [mul_smul, inv_smul_smul]
      _ = x • c := by rw [hzc]
  have hxa := himage a hzfix.1
  have hxb := himage b hzfix.2
  have hxpair :
      (x • a = a ∧ x • b = b) ∨ (x • a = b ∧ x • b = a) := by
    rcases hxa with hxaa | hxab
    · left
      refine ⟨hxaa, ?_⟩
      rcases hxb with hxba | hxbb
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxaa, hxba]
      · exact hxbb
    · right
      refine ⟨hxab, ?_⟩
      rcases hxb with hxba | hxbb
      · exact hxba
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxab, hxbb]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
    simpa [H, D, Dg] using twoPointStabilizer_map_mem_iff a b hab g]
  rw [show x * g * x⁻¹ ∈ Dg ↔
      (x * g * x⁻¹) • a = a ∧ (x * g * x⁻¹) • b = b by
    simpa [H, D, Dg] using
      twoPointStabilizer_map_mem_iff a b hab (x * g * x⁻¹)]
  rcases hxpair with ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
  · have hxinva : x⁻¹ • a = a := by
      calc
        x⁻¹ • a = x⁻¹ • (x • a) := by rw [hxa]
        _ = a := inv_smul_smul x a
    have hxinvb : x⁻¹ • b = b := by
      calc
        x⁻¹ • b = x⁻¹ • (x • b) := by rw [hxb]
        _ = b := inv_smul_smul x b
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hxinva, hga, hxa]
      · simp only [mul_smul, hxinvb, hgb, hxb]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = x⁻¹ • ((x * g * x⁻¹) • (x • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • a) := by rw [hxa]
          _ = x⁻¹ • a := by rw [hcga]
          _ = a := hxinva
      · calc
          g • b = x⁻¹ • ((x * g * x⁻¹) • (x • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • b) := by rw [hxb]
          _ = x⁻¹ • b := by rw [hcgb]
          _ = b := hxinvb
  · have hxinva : x⁻¹ • a = b := by
      calc
        x⁻¹ • a = x⁻¹ • (x • b) := by rw [hxb]
        _ = b := inv_smul_smul x b
    have hxinvb : x⁻¹ • b = a := by
      calc
        x⁻¹ • b = x⁻¹ • (x • a) := by rw [hxa]
        _ = a := inv_smul_smul x a
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hxinva, hgb, hxb]
      · simp only [mul_smul, hxinvb, hga, hxa]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = x⁻¹ • ((x * g * x⁻¹) • (x • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • b) := by rw [hxa]
          _ = x⁻¹ • b := by rw [hcgb]
          _ = a := hxinvb
      · calc
          g • b = x⁻¹ • ((x * g * x⁻¹) • (x • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • a) := by rw [hxb]
          _ = x⁻¹ • a := by rw [hcga]
          _ = b := hxinva

/-- For odd two-point-stabilizer order, its index-two ambient normalizer is a
Z-group.  This packages the coprime extension step in XI.1.5. -/
private theorem zassenhaus_odd_twoPointNormalizer_isZGroup
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg : Subgroup G := D.map H.subtype
    IsZGroup (Subgroup.normalizer (Dg : Set G)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change IsZGroup T
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      zassenhaus_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  let : IsZGroup D :=
    isZGroup_of_frobenius_complement_of_odd F D (by simpa [D] using hFrob)
      (by simpa [H, D, MulAction.stabilizer] using hodd)
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eD : Dsub ≃* D := eDsub.trans eDg.symm
  let : IsZGroup Dsub :=
    IsZGroup.of_injective (f := eD.toMonoidHom) eD.injective
  have hquotCard : Nat.card (T ⧸ Dsub) = 2 := by
    rw [← Dsub.index_eq_card]
    exact hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (T ⧸ Dsub) :=
    isCyclic_of_card_dvd_prime (by rw [hquotCard])
  have hcop : (Nat.card Dsub).Coprime (Nat.card (T ⧸ Dsub)) := by
    rw [hDsubcard, hquotCard]
    simpa [D] using hodd.coprime_two_right
  exact isZGroup_of_coprime
    (f := Dsub.subtype) (f' := QuotientGroup.mk' Dsub)
    (by simp) hcop

/-- XI.1.5, cyclicity part: in a simple Zassenhaus group the odd two-point
stabilizer is cyclic. -/
private theorem zassenhaus_odd_twoPointStabilizer_cyclic_and_commutator_eq
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg : Subgroup G := D.map H.subtype
    let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
    IsCyclic D ∧ commutator T = Dg.subgroupOf T := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change IsCyclic D ∧ commutator T = Dsub
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      zassenhaus_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  have hTcard : Nat.card T = 2 * Nat.card D := by
    calc
      Nat.card T = Nat.card Dsub * Dsub.index := Dsub.card_mul_index.symm
      _ = 2 * Nat.card D := by rw [hDsubcard, hindex]; omega
  let : IsZGroup T := by
    simpa [H, D, Dg, T] using
      zassenhaus_odd_twoPointNormalizer_isZGroup
        htwo hat_most_two_fixed_points a b hab F hFrob hodd
  have hcommCyclic : IsCyclic (commutator T) :=
    IsZGroup.isCyclic_commutator T
  have hquotCard : Nat.card (T ⧸ Dsub) = 2 := by
    rw [← Dsub.index_eq_card]
    exact hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (T ⧸ Dsub) :=
    isCyclic_of_card_dvd_prime (by rw [hquotCard])
  let : CommGroup (T ⧸ Dsub) := IsCyclic.commGroup
  have hcommLe : commutator T ≤ Dsub := by
    simpa using
      (Abelianization.commutator_subset_ker (QuotientGroup.mk' Dsub))
  have hnoOddPrime :
      ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ (commutator T).index := by
    intro q hq hqne hqindex
    let : Fact q.Prime := ⟨hq⟩
    have hqT : q ∣ Nat.card T :=
      hqindex.trans (commutator T).index_dvd_card
    have hqcommNot : ¬ q ∣ Nat.card (commutator T) := by
      apply hq.coprime_iff_not_dvd.mp
      exact Nat.Coprime.of_dvd_left hqindex
        (IsZGroup.coprime_commutator_index T).symm
    let Qd : Sylow q D := default
    let iotaD : D →* G := H.subtype.comp D.subtype
    have hiotaD : Function.Injective iotaD :=
      H.subtype_injective.comp D.subtype_injective
    let Qg : Subgroup G := (Qd : Subgroup D).map iotaD
    have hDgRange : iotaD.range = Dg := by
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨(d : H), d.property, rfl⟩
      · rintro ⟨d, hdD, rfl⟩
        exact ⟨⟨d, hdD⟩, rfl⟩
    have hDgMapTop : Subgroup.map iotaD (⊤ : Subgroup D) = Dg := by
      calc
        Subgroup.map iotaD (⊤ : Subgroup D) = iotaD.range := by
          ext x
          constructor
          · rintro ⟨d, _hd, rfl⟩
            exact ⟨d, rfl⟩
          · rintro ⟨d, rfl⟩
            exact ⟨d, trivial, rfl⟩
        _ = Dg := hDgRange
    have hQgDg : Qg ≤ Dg := by
      simpa [Qg, hDgRange] using
        (Subgroup.map_le_range iotaD (Qd : Subgroup D))
    have hQgT : Qg ≤ T := hQgDg.trans Subgroup.le_normalizer
    have hQgP : IsPGroup q Qg := Qd.isPGroup'.map iotaD
    let QTsub : Subgroup T := Qg.subgroupOf T
    have hQTsubP : IsPGroup q QTsub :=
      hQgP.of_equiv (Subgroup.subgroupOfEquivOfLe hQgT).symm
    have hrelQD : Qg.relIndex Dg = Qd.index := by
      rw [show Qg = Subgroup.map iotaD (Qd : Subgroup D) from rfl,
        ← hDgMapTop,
        Subgroup.relIndex_map_map_of_injective
          (Qd : Subgroup D) (⊤ : Subgroup D) hiotaD,
        Subgroup.relIndex_top_right]
    have hrelQT : Qg.relIndex T = Qd.index * 2 := by
      calc
        Qg.relIndex T = Qg.relIndex Dg * Dg.relIndex T :=
          (Subgroup.relIndex_mul_relIndex Qg Dg T hQgDg
            Subgroup.le_normalizer).symm
        _ = Qd.index * Dsub.index := by rw [hrelQD]; rfl
        _ = Qd.index * 2 := by rw [hindex]
    have hQTsubIndex : QTsub.index = Qd.index * 2 := by
      change Qg.relIndex T = Qd.index * 2
      exact hrelQT
    have hqQTsubIndex : ¬ q ∣ QTsub.index := by
      rw [hQTsubIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqQd | hq2
      · exact Qd.not_dvd_index hqQd
      · rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with hq1 | hq2eq
        · exact hq.ne_one hq1
        · exact hqne hq2eq
    let QT : Sylow q T := hQTsubP.toSylow hqQTsubIndex
    have hQTcoe : (QT : Subgroup T) = QTsub :=
      IsPGroup.toSylow_coe hQTsubP hqQTsubIndex
    have hnormalizerCentralT :
        Subgroup.normalizer ((QTsub : Subgroup T) : Set T) ≤
          Subgroup.centralizer (QTsub : Set T) := by
      rcases Sylow.normalizer_le_centralizer_or_le_commutator QT with hcent | hle
      · have hQTcoe_set : (QT : Set T) = (QTsub : Set T) :=
          congrArg (fun (s : Subgroup T) => (s : Set T)) hQTcoe
        simpa [hQTcoe_set] using hcent
      · exfalso
        apply hqcommNot
        exact (QT.dvd_card_of_dvd_card hqT).trans
          (Subgroup.card_dvd_of_le hle)
    obtain ⟨hOmegaCard, _hHcard, hGcard, hDdvd⟩ :=
      huppert_XI_6_1_action_parameters_core htwo a b hab F hFrob
    have hqD : q ∣ Nat.card D := by
      have hq2D : q ∣ 2 * Nat.card D := by
        rw [← hTcard]
        exact hqT
      rcases hq.dvd_mul.mp hq2D with hq2 | hqD
      · rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with hq1 | hq2eq
        · exact (hq.ne_one hq1).elim
        · exact (hqne hq2eq).elim
      · exact hqD
    have hqFsub : q ∣ Nat.card F - 1 := hqD.trans (by simpa [D] using hDdvd)
    have hFcardGt : 1 < Nat.card F :=
      (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot |>
        Finite.one_lt_card_iff_nontrivial.mpr
    have hqFnot : ¬ q ∣ Nat.card F := by
      intro hqF
      have hqone : q ∣ 1 := by
        have := Nat.dvd_sub hqF hqFsub
        (convert this using 1; omega)
      exact hq.not_dvd_one hqone
    have hqFplusNot : ¬ q ∣ Nat.card F + 1 := by
      intro hqFplus
      have hqtwo : q ∣ 2 := by
        have := Nat.dvd_sub hqFplus hqFsub
        (convert this using 1; omega)
      rcases (Nat.dvd_prime Nat.prime_two).mp hqtwo with hq1 | hq2eq
      · exact hq.ne_one hq1
      · exact hqne hq2eq
    have hDgIndex : Dg.index = (Nat.card F + 1) * Nat.card F := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D))
      calc
        Nat.card D * Dg.index = Nat.card Dg * Dg.index := by rw [hDgcard]
        _ = Nat.card G := Dg.card_mul_index
        _ = Fintype.card Omega * Nat.card F * Nat.card D := by
          simpa [D] using hGcard
        _ = Nat.card D * ((Nat.card F + 1) * Nat.card F) := by
          rw [hOmegaCard]
          ring
    have hqDgIndex : ¬ q ∣ Dg.index := by
      rw [hDgIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqFplus | hqF
      · exact hqFplusNot hqFplus
      · exact hqFnot hqF
    have hiotaKer : iotaD.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff iotaD).mpr hiotaD
    have hQgIndex : Qg.index = Qd.index * Dg.index := by
      calc
        Qg.index =
            ((Qd : Subgroup D) ⊔ iotaD.ker).index * iotaD.range.index :=
          Subgroup.index_map (Qd : Subgroup D) iotaD
        _ = Qd.index * Dg.index := by
          rw [hiotaKer, sup_bot_eq, hDgRange]
    have hqQgIndex : ¬ q ∣ Qg.index := by
      rw [hQgIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqQd | hqDg
      · exact Qd.not_dvd_index hqQd
      · exact hqDgIndex hqDg
    let QG : Sylow q G := hQgP.toSylow hqQgIndex
    have hQGcoe : (QG : Subgroup G) = Qg :=
      IsPGroup.toSylow_coe hQgP hqQgIndex
    have hqG : q ∣ Nat.card G :=
      hqT.trans (Subgroup.card_subgroup_dvd_card T)
    have hQgNe : Qg ≠ ⊥ := by
      rw [← hQGcoe]
      exact Sylow.ne_bot_of_dvd_card QG hqG
    have hnormalizerLeT : Subgroup.normalizer (Qg : Set G) ≤ T := by
      simpa [H, D, Dg, T] using
        zassenhaus_twoPointSubgroup_normalizer_le
          hat_most_two_fixed_points a b hab Qg hQgDg hQgNe
    have hnormalizerCentralG :
        Subgroup.normalizer (Qg : Set G) ≤
          Subgroup.centralizer (Qg : Set G) := by
      intro x hx
      let xT : T := ⟨x, hnormalizerLeT hx⟩
      have hxNormT : xT ∈ Subgroup.normalizer (QTsub : Set T) := by
        rw [Subgroup.mem_normalizer_iff] at hx ⊢
        intro y
        change ((y : T) : G) ∈ Qg ↔
          (((xT * y * xT⁻¹ : T) : G) ∈ Qg)
        exact hx ((y : T) : G)
      have hxCentT : xT ∈ Subgroup.centralizer (QTsub : Set T) :=
        hnormalizerCentralT hxNormT
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yT : T := ⟨y, hQgT hy⟩
      have hyQT : yT ∈ QTsub := hy
      have hcommT :=
        (Subgroup.mem_centralizer_iff.mp hxCentT) yT hyQT
      exact congrArg Subtype.val hcommT
    have hcentralG :
        Subgroup.normalizer ((QG : Subgroup G) : Set G) ≤
          Subgroup.centralizer ((QG : Subgroup G) : Set G) := by
      simpa [hQGcoe] using hnormalizerCentralG
    have hcomp := MonoidHom.ker_transferSylow_isComplement' QG hcentralG
    let K : Subgroup G := (MonoidHom.transferSylow QG hcentralG).ker
    have hQGne : (QG : Subgroup G) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card QG hqG
    obtain ⟨s, _hsq, hsa, _hsb⟩ :=
      zassenhaus_odd_twoPointStabilizer_exists_swap_involution
        htwo hat_most_two_fixed_points a b hab F hFrob hodd
    have hQGtop : (QG : Subgroup G) ≠ ⊤ := by
      intro htop
      have hsQg : s ∈ Qg := by
        rw [← hQGcoe, htop]
        trivial
      have hsfix :=
        (twoPointStabilizer_map_mem_iff a b hab s).mp (hQgDg hsQg)
      exact hab (hsfix.1.symm.trans hsa)
    by_cases hKbot : K = ⊥
    · apply hQGtop
      apply Subgroup.isComplement'_bot_left.mp
      simpa [K, hKbot] using hcomp
    · have hKtop : K = ⊤ := hsimple K inferInstance hKbot
      apply hQGne
      apply Subgroup.isComplement'_top_left.mp
      simpa [K, hKtop] using hcomp
  have htwoDvd : 2 ∣ (commutator T).index := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le hcommLe
  have hcommIndexDvd : (commutator T).index ∣ 2 * Nat.card D := by
    rw [← hTcard]
    exact (commutator T).index_dvd_card
  obtain ⟨m, hm⟩ := htwoDvd
  have hmDvd : m ∣ Nat.card D := by
    obtain ⟨r, hr⟩ := hcommIndexDvd
    refine ⟨r, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by omega)
    calc
      2 * Nat.card D = (commutator T).index * r := hr
      _ = (2 * m) * r := by rw [hm]
      _ = 2 * (m * r) := by ring
  have hmOne : m = 1 := by
    by_contra hmne
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hmne
    have hqD : q ∣ Nat.card D := hqm.trans hmDvd
    have hqne : q ≠ 2 := by
      intro hqeq
      subst q
      exact (Nat.not_even_iff_odd.mpr (by simpa [D] using hodd))
        (even_iff_two_dvd.mpr (by simpa [D] using hqD))
    exact hnoOddPrime q hq hqne
      (hqm.trans (by rw [hm]; exact dvd_mul_left m 2))
  have hcommIndex : (commutator T).index = 2 := by
    rw [hm, hmOne]
  have hcommCard : Nat.card (commutator T) = Nat.card Dsub := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by omega)
    calc
      Nat.card (commutator T) * 2 = Nat.card T := by
        rw [← hcommIndex]
        exact (commutator T).card_mul_index
      _ = Nat.card Dsub * 2 := by
        rw [← hindex]
        exact Dsub.card_mul_index.symm
  have hcommEq : commutator T = Dsub :=
    Subgroup.eq_of_le_of_card_ge hcommLe (by rw [hcommCard])
  have hDsubCyclic : IsCyclic Dsub := by
    rw [hcommEq] at hcommCyclic
    exact hcommCyclic
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eD : Dsub ≃* D := eDsub.trans eDg.symm
  exact ⟨isCyclic_of_surjective eD eD.surjective, hcommEq⟩

public theorem zassenhaus_odd_twoPointStabilizer_isCyclic
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :=
  (zassenhaus_odd_twoPointStabilizer_cyclic_and_commutator_eq
    htwo hat_most_two_fixed_points hsimple a b hab F hFrob hodd).1

private theorem isMulCommutative_sup_of_le_centralizer
    {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hAcomm : IsMulCommutative A) (hBcomm : IsMulCommutative B)
    (hBcentral : B ≤ Subgroup.centralizer (A : Set Q)) :
    IsMulCommutative (A ⊔ B : Subgroup Q) := by
  rw [Subgroup.sup_eq_closure]
  exact Subgroup.isMulCommutative_closure (by
    intro x hx y hy _
    rcases hx with hxA | hxB
    · rcases hy with hyA | hyB
      · exact setLike_mul_comm (s := A) hxA hyA
      · exact Subgroup.mem_centralizer_iff.mp (hBcentral hyB) x hxA
    · rcases hy with hyA | hyB
      · exact (Subgroup.mem_centralizer_iff.mp (hBcentral hxB) y hyA).symm
      · exact setLike_mul_comm (s := B) hxB hyB)

/-- XI.1.5, inversion part: every element interchanging the two points acts
by inversion on the odd cyclic two-point stabilizer. -/
public theorem zassenhaus_odd_twoPointStabilizer_swap_inverts
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (s : G) (hsa : s • a = b) (hsb : s • b = a) :
    ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change ∀ x : D, s * (((x : H) : G)) * s⁻¹ = (((x⁻¹ : D) : H) : G)
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      zassenhaus_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  obtain ⟨hDcyclic, hcommEq⟩ :=
    zassenhaus_odd_twoPointStabilizer_cyclic_and_commutator_eq
      htwo hat_most_two_fixed_points hsimple a b hab F hFrob hodd
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eDDsub : D ≃* Dsub := eDg.trans eDsub.symm
  let : IsCyclic D := hDcyclic
  let : IsCyclic Dsub :=
    isCyclic_of_surjective eDDsub eDDsub.surjective
  let : CommGroup Dsub := IsCyclic.commGroup
  have hDsubComm : IsMulCommutative Dsub := inferInstance
  have hDsubcard : Nat.card Dsub = Nat.card D :=
    Nat.card_congr eDDsub.symm.toEquiv
  obtain ⟨c, hcSq, hca, hcb⟩ :=
    zassenhaus_odd_twoPointStabilizer_exists_swap_involution
      htwo hat_most_two_fixed_points a b hab F hFrob hodd
  have hcTmem : c ∈ T := by
    simpa [H, D, Dg, T] using
      zassenhaus_swap_mem_twoPointStabilizer_normalizer a b hab c hca hcb
  let cT : T := ⟨c, hcTmem⟩
  have hcTnotD : cT ∉ Dsub := by
    intro hcD
    have hcDg : c ∈ Dg := hcD
    have hcfix :=
      (twoPointStabilizer_map_mem_iff a b hab c).mp hcDg
    exact hab (hcfix.1.symm.trans hca)
  have hcTne : cT ≠ 1 := by
    intro hcOne
    apply hcTnotD
    simp [hcOne]
  have hcTSq : cT ^ 2 = 1 := by
    apply Subtype.ext
    exact hcSq
  let R : Subgroup T := Subgroup.zpowers cT
  let : IsCyclic R := inferInstance
  let : CommGroup R := IsCyclic.commGroup
  have hRcomm : IsMulCommutative R := inferInstance
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcTorder : orderOf cT = 2 := orderOf_eq_prime hcTSq hcTne
  have hRcard : Nat.card R = 2 := by
    simp [R, hcTorder]
  have hsup : Dsub ⊔ R = ⊤ := by
    apply top_unique
    intro x _hx
    by_cases hxD : (x : T) ∈ Dsub
    · exact Subgroup.mem_sup_left hxD
    · have hxswap :
          ((x : T) : G) • a = b ∧ ((x : T) : G) • b = a := by
        have hxnotDg : ((x : T) : G) ∉ Dg := by
          intro hxDg
          exact hxD hxDg
        exact zassenhaus_twoPointStabilizer_normalizer_notMem_swaps
          hat_most_two_fixed_points a b hab F hFrob ((x : T) : G)
          (by
            change ((x : T) : G) ∈ T
            exact x.2) hxnotDg
      have hxcDg : (((x * cT : T) : G)) ∈ Dg := by
        apply (twoPointStabilizer_map_mem_iff a b hab ((x * cT : T) : G)).mpr
        constructor
        · change (((x : T) : G) * c) • a = a
          rw [mul_smul, hca, hxswap.2]
        · change (((x : T) : G) * c) • b = b
          rw [mul_smul, hcb, hxswap.1]
      have hxcD : x * cT ∈ Dsub := by
        simpa [Dsub, Subgroup.mem_subgroupOf] using hxcDg
      have hcR : cT ∈ R := Subgroup.mem_zpowers cT
      have hcMul : cT * cT = 1 := by simpa [pow_two] using hcTSq
      have hxrepr : x = (x * cT) * cT := by
        rw [mul_assoc, hcMul, mul_one]
      rw [hxrepr]
      exact (Dsub ⊔ R).mul_mem
        (Subgroup.mem_sup_left hxcD) (Subgroup.mem_sup_right hcR)
  have hRnormD : R ≤ Subgroup.normalizer (Dsub : Set T) := by
    simp [Dsub.normalizer_eq_top]
  let N : Subgroup T := ⁅Dsub, R⁆
  have : N.Normal := by
    have hNnormal := commutator_normal_in_sup Dsub R
    have hsupLe : Dsub ⊔ R ≤ Subgroup.normalizer (N : Set T) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := N) (K := Dsub ⊔ R) (by simpa [N] using commutator_le_sup Dsub R)).mp
          (by simpa [N] using hNnormal)
    have htopLe : (⊤ : Subgroup T) ≤ Subgroup.normalizer (N : Set T) := by
      simpa [hsup] using hsupLe
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique htopLe)
  let pi : T →* T ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (T ⧸ N) := Dsub.map pi
  let B : Subgroup (T ⧸ N) := R.map pi
  have hAcomm : IsMulCommutative A := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    rcases x.property with ⟨xT, hxD, hx⟩
    rcases y.property with ⟨yT, hyD, hy⟩
    change (x : T ⧸ N) * y = y * x
    rw [← hx, ← hy]
    exact congrArg pi
      (setLike_mul_comm (s := Dsub) hxD hyD)
  have hBcomm : IsMulCommutative B := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    rcases x.property with ⟨xT, hxR, hx⟩
    rcases y.property with ⟨yT, hyR, hy⟩
    change (x : T ⧸ N) * y = y * x
    rw [← hx, ← hy]
    exact congrArg pi
      (setLike_mul_comm (s := R) hxR hyR)
  have hBcentralA : B ≤ Subgroup.centralizer (A : Set (T ⧸ N)) := by
    intro rbar hrbar
    rcases hrbar with ⟨r, hrR, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro dbar hdbar
    rcases hdbar with ⟨d, hdD, rfl⟩
    have hdrN : ⁅d, r⁆ ∈ N :=
      Subgroup.commutator_mem_commutator
        (H₁ := Dsub) (H₂ := R) hdD hrR
    have hcomm : Commute (pi d) (pi r) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff ⁅d, r⁆).2 hdrN
    exact hcomm.eq
  have hABtop : A ⊔ B = ⊤ := by
    calc
      A ⊔ B = Subgroup.map pi (Dsub ⊔ R) :=
        (Subgroup.map_sup Dsub R pi).symm
      _ = Subgroup.map pi ⊤ := by rw [hsup]
      _ = pi.range := (MonoidHom.range_eq_map pi).symm
      _ = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hquotComm : IsMulCommutative (T ⧸ N) := by
    have h := isMulCommutative_sup_of_le_centralizer hAcomm hBcomm hBcentralA
    rw [hABtop] at h
    let : IsMulCommutative (⊤ : Subgroup (T ⧸ N)) := h
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxy :
        (⟨x, trivial⟩ : (⊤ : Subgroup (T ⧸ N))) * ⟨y, trivial⟩ =
          ⟨y, trivial⟩ * ⟨x, trivial⟩ := by
      ext
      exact congrArg Subtype.val (h.1.1 ⟨x, trivial⟩ ⟨y, trivial⟩)
    exact congrArg Subtype.val hxy
  have hcommLeN : commutator T ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp
      hquotComm
  have hNleComm : N ≤ commutator T := by
    exact Subgroup.commutator_mono le_top le_top
  have hNeqD : N = Dsub :=
    (le_antisymm hNleComm hcommLeN).trans hcommEq
  let : Subgroup.Normalizes R Dsub := ⟨hRnormD⟩
  let : MulDistribMulAction R Dsub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R Dsub hRnormD
  have hactionMap :
      (commutatorAction (A := R) (G := Dsub)).map Dsub.subtype = N := by
    simpa [N] using
      commutatorAction_subgroup_conj_map_eq_commutator Dsub R hRnormD
  have hactionTop : commutatorAction (A := R) (G := Dsub) = ⊤ := by
    apply Subgroup.map_injective Dsub.subtype_injective
    calc
      Subgroup.map Dsub.subtype (commutatorAction (A := R) (G := Dsub)) = N :=
        hactionMap
      _ = Dsub := hNeqD
      _ = Dsub.subtype.range := (Dsub.range_subtype).symm
      _ = Subgroup.map Dsub.subtype ⊤ := MonoidHom.range_eq_map Dsub.subtype
  have hcop : (Nat.card R).Coprime (Nat.card Dsub) := by
    rw [hRcard, hDsubcard]
    exact (by simpa [D] using hodd.coprime_two_right.symm)
  have hcompl :
      IsCompl (fixedPointSubgroup R Dsub)
        (commutatorAction (A := R) (G := Dsub)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm hDsubComm.is_comm.comm) hcop hDsubComm
  have hfixedBot : fixedPointSubgroup R Dsub = ⊥ := by
    apply bot_unique
    have hle := hcompl.disjoint.le_bot
    simpa [hactionTop] using hle
  have hcNorm : cT ∈ Subgroup.normalizer (Dsub : Set T) := by
    rw [Dsub.normalizer_eq_top]
    trivial
  let cN : Subgroup.normalizer (Dsub : Set T) := ⟨cT, hcNorm⟩
  let phi : MulAut Dsub := Dsub.normalizerMonoidHom cN
  have hphiSq : phi ^ 2 = 1 := by
    change (Dsub.normalizerMonoidHom cN) ^ 2 = 1
    have hcNSq : cN ^ 2 = 1 := by
      apply Subtype.ext
      exact hcTSq
    rw [← map_pow, hcNSq, map_one]
  have hphiInv : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut Dsub => psi x) hphiSq
    simpa [pow_two] using hx
  have hphiFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hconjFix : cT * (x : T) * cT⁻¹ = (x : T) := by
      simpa [phi, cN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hx
    have hccomm : Commute cT (x : T) := by
      apply commutatorElement_eq_one_iff_commute.mp
      simp [commutatorElement_def, hconjFix]
    have hxFixed : x ∈ fixedPointSubgroup R Dsub := by
      change ∀ r : R, r • x = x
      intro r
      rcases Subgroup.mem_zpowers_iff.mp r.property with ⟨k, hk⟩
      have hrcomm : Commute (r : T) (x : T) := by
        rw [← hk]
        exact hccomm.zpow_left k
      apply Subtype.ext
      change (r : T) * (x : T) * (r : T)⁻¹ = (x : T)
      rw [hrcomm.eq]
      simp [mul_assoc]
    have hxBot : x ∈ (⊥ : Subgroup Dsub) := by
      simpa [hfixedBot] using hxFixed
    exact Subgroup.mem_bot.mp hxBot
  have hphiEqInv : ⇑phi = fun x : Dsub => x⁻¹ :=
    hphiFree.coe_eq_inv_of_involutive hphiInv
  have hcInverts (x : Dsub) :
      cT * (x : T) * cT⁻¹ = ((x⁻¹ : Dsub) : T) := by
    have hx := congrArg Subtype.val (congrFun hphiEqInv x)
    simpa [phi, cN, Subgroup.normalizerMonoidHom_apply_apply_coe] using hx
  have hsTmem : s ∈ T := by
    simpa [H, D, Dg, T] using
      zassenhaus_swap_mem_twoPointStabilizer_normalizer a b hab s hsa hsb
  let sT : T := ⟨s, hsTmem⟩
  intro x
  let xDg : Dg := ⟨((x : H) : G), ⟨(x : H), x.property, rfl⟩⟩
  let xT : T := ⟨(xDg : G), Subgroup.le_normalizer xDg.property⟩
  let xDsub : Dsub := ⟨xT, xDg.property⟩
  have hscDg : (((sT * cT : T) : G)) ∈ Dg := by
    apply (twoPointStabilizer_map_mem_iff a b hab ((sT * cT : T) : G)).mpr
    constructor
    · change (s * c) • a = a
      rw [mul_smul, hca, hsb]
    · change (s * c) • b = b
      rw [mul_smul, hcb, hsa]
  let dT : Dsub := ⟨sT * cT, by simpa [Dsub, Subgroup.mem_subgroupOf] using hscDg⟩
  have hcMul : cT * cT = 1 := by simpa [pow_two] using hcTSq
  have hsEq : sT = (dT : T) * cT := by
    change sT = (sT * cT) * cT
    rw [mul_assoc, hcMul, mul_one]
  have hdcomm : Commute (dT : T) (xDsub : T) := by
    exact setLike_mul_comm (s := Dsub) dT.property xDsub.property
  have hcalc :
      sT * (xDsub : T) * sT⁻¹ = ((xDsub⁻¹ : Dsub) : T) := by
    calc
      sT * (xDsub : T) * sT⁻¹ =
          ((dT : T) * cT) * (xDsub : T) * ((dT : T) * cT)⁻¹ := by
        rw [← hsEq]
      _ = (dT : T) * (cT * (xDsub : T) * cT⁻¹) * (dT : T)⁻¹ := by
        group
      _ = (dT : T) * ((xDsub⁻¹ : Dsub) : T) * (dT : T)⁻¹ := by
        rw [hcInverts]
      _ = ((xDsub⁻¹ : Dsub) : T) := by
        have hdcommInv : Commute (dT : T) ((xDsub⁻¹ : Dsub) : T) := by
          simpa using hdcomm.inv_right
        rw [hdcommInv.eq]
        simp [mul_assoc]
  have hcalcG := congrArg (fun z : T => (z : G)) hcalc
  simpa [sT, xDsub, xDg] using hcalcG

/-- A normal subgroup of a Frobenius group either lies in the kernel or
contains the kernel. -/
private theorem frobenius_normal_subgroup_le_kernel_or_kernel_le
    {H : Type*} [Group H] [Finite H]
    (F D N : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hN : N.Normal) :
    N ≤ F ∨ F ≤ N := by
  classical
  by_cases hNF : N ≤ F
  · exact Or.inl hNF
  right
  obtain ⟨n, hnN, hnnotF⟩ := SetLike.not_le_iff_exists.mp hNF
  let : F.Normal := hFrob.normal
  have hcentD :
      ∀ r : D, r ≠ 1 → Section2.centralizerIn F (r : H) = ⊥ := by
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using
      ((lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob r hr)
  have hcentN : Section2.centralizerIn F n = ⊥ :=
    Section6.theorem_6_8_frobenius_complement_centralizerIn_eq_bot
      (K := F) (R := D) hFrob.isComplement' hcentD hnnotF
  let delta : F → F := fun a =>
    ⟨(a : H) * n * (a : H)⁻¹ * n⁻¹, by
      have hconjF : n * (a : H)⁻¹ * n⁻¹ ∈ F :=
        hFrob.normal.conj_mem ((a : H)⁻¹) (F.inv_mem a.2) n
      simpa [mul_assoc] using F.mul_mem a.2 hconjF⟩
  have hdelta_inj : Function.Injective delta := by
    intro a b hab
    have habH :
        (a : H) * n * (a : H)⁻¹ * n⁻¹ =
          (b : H) * n * (b : H)⁻¹ * n⁻¹ :=
      congrArg Subtype.val hab
    have hcomm :
        (b : H)⁻¹ * (a : H) * n =
          n * ((b : H)⁻¹ * (a : H)) := by
      have hab1 :
          (a : H) * n * (a : H)⁻¹ =
            (b : H) * n * (b : H)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : H => t * n) habH
      have hab2 := congrArg (fun t : H => (b : H)⁻¹ * t * (a : H)) hab1
      simpa [mul_assoc] using hab2
    let c : F :=
      ⟨(b : H)⁻¹ * (a : H), F.mul_mem (F.inv_mem b.2) a.2⟩
    have hcCent : (c : H) ∈ Section2.centralizerIn F n := by
      refine ⟨c.2, ?_⟩
      change (c : H) ∈ Subgroup.centralizer ({n} : Set H)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [c] using hcomm)
    have hcBot : (c : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcentN] using hcCent
    have hc_eq : (c : H) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : H => (b : H) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hdelta_surj : Function.Surjective delta :=
    Finite.surjective_of_injective hdelta_inj
  intro k hk
  rcases hdelta_surj ⟨k, hk⟩ with ⟨a, ha⟩
  have haH : (a : H) * n * (a : H)⁻¹ * n⁻¹ = k :=
    congrArg Subtype.val ha
  rw [← haH]
  exact N.mul_mem (hN.conj_mem n hnN (a : H)) (N.inv_mem hnN)

/-- Every element outside a finite Frobenius kernel is conjugate by a kernel
element into the complement. -/
private theorem frobenius_not_mem_kernel_conjugate_mem_complement
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    {x : H} (hxnotF : x ∉ F) :
    ∃ a : F, ∃ r : D,
      (a : H)⁻¹ * x * (a : H) = (r : H) := by
  classical
  let : F.Normal := hFrob.normal
  have hxSup : x ∈ F ⊔ D := by
    simp [hFrob.isComplement'.sup_eq_top]
  rcases (Subgroup.mem_sup_of_normal_left (s := F) (t := D) (x := x)).1 hxSup with
    ⟨k, hkF, r, hrD, hkr⟩
  let rD : D := ⟨r, hrD⟩
  have hrne : rD ≠ 1 := by
    intro hr1
    apply hxnotF
    rw [← hkr]
    have hr_eq : r = 1 := by
      simpa [rD] using congrArg Subtype.val hr1
    simp [hr_eq, hkF]
  have hcent : elementCentralizerIn F (rD : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob rD hrne
  let delta : F → F := fun a =>
    ⟨(a : H) * r * (a : H)⁻¹ * r⁻¹, by
      have hconjF : r * (a : H)⁻¹ * r⁻¹ ∈ F :=
        hFrob.normal.conj_mem ((a : H)⁻¹) (F.inv_mem a.2) r
      simpa [mul_assoc] using F.mul_mem a.2 hconjF⟩
  have hdelta_inj : Function.Injective delta := by
    intro a b hab
    have habH :
        (a : H) * r * (a : H)⁻¹ * r⁻¹ =
          (b : H) * r * (b : H)⁻¹ * r⁻¹ :=
      congrArg Subtype.val hab
    have hcomm :
        (b : H)⁻¹ * (a : H) * r =
          r * ((b : H)⁻¹ * (a : H)) := by
      have hab1 :
          (a : H) * r * (a : H)⁻¹ =
            (b : H) * r * (b : H)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : H => t * r) habH
      have hab2 := congrArg (fun t : H => (b : H)⁻¹ * t * (a : H)) hab1
      simpa [mul_assoc] using hab2
    let c : F :=
      ⟨(b : H)⁻¹ * (a : H), F.mul_mem (F.inv_mem b.2) a.2⟩
    have hcCent : (c : H) ∈ elementCentralizerIn F (rD : H) := by
      refine ⟨c.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [c, rD] using hcomm)
    have hcBot : (c : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hcCent
    have hc_eq : (c : H) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : H => (b : H) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hdelta_surj : Function.Surjective delta :=
    Finite.surjective_of_injective hdelta_inj
  rcases hdelta_surj ⟨k, hkF⟩ with ⟨a, ha⟩
  have haH : (a : H) * r * (a : H)⁻¹ * r⁻¹ = k :=
    congrArg Subtype.val ha
  have hconj_x : (a : H)⁻¹ * x * (a : H) = r := by
    rw [← hkr]
    have hk_eq : k = (a : H) * r * (a : H)⁻¹ * r⁻¹ := haH.symm
    rw [hk_eq]
    group
  exact ⟨a, rD, by simpa [rD] using hconj_x⟩

/-- The centralizer in a Frobenius group of a nonidentity kernel element is
contained in the kernel. -/
private theorem frobenius_kernel_centralizer_le
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (z : F) (hzne : z ≠ 1) :
    Subgroup.centralizer ({(z : H)} : Set H) ≤ F := by
  intro x hx
  by_contra hxF
  obtain ⟨a, r, hconj⟩ :=
    frobenius_not_mem_kernel_conjugate_mem_complement F D hFrob hxF
  let za : F :=
    ⟨(a : H)⁻¹ * (z : H) * (a : H), by
      simpa using hFrob.normal.conj_mem (z : H) z.property (a : H)⁻¹⟩
  have hza_ne : za ≠ 1 := by
    intro hza
    apply hzne
    apply Subtype.ext
    have hzaH : (a : H)⁻¹ * (z : H) * (a : H) = 1 :=
      congrArg Subtype.val hza
    have := congrArg (fun y : H => (a : H) * y * (a : H)⁻¹) hzaH
    simpa [za, mul_assoc] using this
  have hxcomm : x * (z : H) = (z : H) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hrcomm : (r : H) * (za : H) = (za : H) * (r : H) := by
    rw [← hconj]
    dsimp [za]
    calc
      (a : H)⁻¹ * x * (a : H) * ((a : H)⁻¹ * (z : H) * (a : H)) =
          (a : H)⁻¹ * (x * (z : H)) * (a : H) := by group
      _ = (a : H)⁻¹ * ((z : H) * x) * (a : H) := by rw [hxcomm]
      _ = (a : H)⁻¹ * (z : H) * (a : H) *
          ((a : H)⁻¹ * x * (a : H)) := by group
  have hzaCent : (za : H) ∈ elementCentralizerIn F (r : H) :=
    ⟨za.property, Subgroup.mem_centralizer_singleton_iff.mpr hrcomm.symm⟩
  have hrne : r ≠ 1 := by
    intro hr
    have hrH : (r : H) = 1 := congrArg Subtype.val hr
    have hconjOne : (a : H)⁻¹ * x * (a : H) = 1 := hconj.trans hrH
    have := congrArg (fun y : H => (a : H) * y * (a : H)⁻¹) hconjOne
    have hxone : x = 1 := by simpa [mul_assoc] using this
    exact hxF (by simp [hxone])
  have hcent : elementCentralizerIn F (r : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob r hrne
  have hzaOne : za = 1 := by
    apply Subtype.ext
    have : (za : H) ∈ (⊥ : Subgroup H) := by simpa [hcent] using hzaCent
    simpa using this
  exact hza_ne hzaOne

/-- An irreducible character of a Frobenius group which is nontrivial on the
kernel is induced from an irreducible character of the kernel. -/
private theorem frobenius_irreducible_character_eq_induced_of_not_kernel
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (chi : Section1.ClassFunction H)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hnotker : ¬ Section1.subgroupInKernel' chi F) :
    ∃ theta : Section1.ClassFunction F,
      Section1.IsIrreducibleCharacterOnGroup theta ∧
        chi = Section1.inducedCF F theta := by
  let : F.Normal := hFrob.normal
  rcases hchi with ⟨n, rho, hrho, hchiEq⟩
  have hnotkerRho : ¬ F ≤ rho.ker := by
    intro hle
    apply hnotker
    rw [hchiEq]
    apply (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho F).2
    intro f
    exact hle f.property
  have hcentralizer : ∀ z : F, z ≠ 1 →
      Subgroup.centralizer ({(z : H)} : Set H) ≤ F :=
    fun z hz => frobenius_kernel_centralizer_le F D hFrob z hz
  obtain ⟨V, instAddV, instModuleV, instFiniteV, phi, hphi, e⟩ :=
    (Theory.Representation.isaacs_theorem_6_34.{u, 0, 0, 0}
      F hcentralizer).2 rho hrho hnotkerRho
  rcases e with ⟨e⟩
  refine ⟨phi.character,
    Section1.isIrreducibleCharacterOnGroup_of_representation phi hphi, ?_⟩
  rw [hchiEq, Section1.inducedCF_eq_representation_character]
  exact Representation.char_iso e.toRepresentationEquiv

/-- A nonprincipal irreducible character cannot have the whole group in its
kernel. -/
private theorem huppert_XI_6_not_subgroupInKernel_top_of_ne_principal
    {H : Type u} [Group H] [Finite H]
    {theta : Section1.ClassFunction H}
    (hthetaIrr : Section1.IsIrreducibleCharacterOnGroup theta)
    (hthetaNe : theta ≠ Section1.principalCharacter H) :
    ¬ Section1.subgroupInKernel' theta (⊤ : Subgroup H) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  intro hker
  have horth :=
    Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hthetaIrr hthetaNe
  have hspdeg :
      Section1.scalarProduct H theta (Section1.principalCharacter H) =
        Section1.degree theta := by
    unfold Section1.scalarProduct Section1.principalCharacter Section1.degree
    have hsum :
        (∑ g : H, theta g * star (1 : ℂ)) = ∑ _g : H, theta 1 := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      have hg := hker ⟨g, by simp⟩
      simpa [Section1.degree] using hg
    rw [hsum]
    simp
  have hdeg0 : Section1.degree theta = 0 := by
    rw [← hspdeg, horth]
  rcases hthetaIrr with ⟨_n, rho, hrhoIrr, hthetaEq⟩
  have hself : Section1.scalarProduct H theta theta = 1 := by
    rw [hthetaEq]
    exact Section1.scalarProduct_representation_char_self rho hrhoIrr
  have hself0 : Section1.scalarProduct H theta theta = 0 := by
    unfold Section1.scalarProduct Section1.degree at hdeg0
    unfold Section1.scalarProduct
    have hzero : ∀ g : H, theta g = 0 := by
      intro g
      have hg := hker ⟨g, by simp⟩
      simpa [Section1.degree, hdeg0] using hg
    simp [hzero]
  norm_num [hself0] at hself

/-- Kernel containment for irreducible characters is closed under subgroup suprema. -/
private theorem huppert_XI_6_subgroupInKernel_sup
    {L : Type u} [Group L] [Finite L]
    {A B : Subgroup L} {chi : Section1.ClassFunction L}
    (hirr : Section1.IsIrreducibleCharacterOnGroup chi)
    (hA : Section1.subgroupInKernel' chi A)
    (hB : Section1.subgroupInKernel' chi B) :
    Section1.subgroupInKernel' chi (A ⊔ B) := by
  rcases hirr with ⟨n, rho, hrho, hchi⟩
  have hAchar : Section1.subgroupInKernel' rho.character A := by
    exact Section1.subgroupInKernel'_of_eq hchi hA
  have hBchar : Section1.subgroupInKernel' rho.character B := by
    exact Section1.subgroupInKernel'_of_eq hchi hB
  have hArep : Section1.subgroupInRepresentationKernel rho A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel rho A).mp hAchar
  have hBrep : Section1.subgroupInRepresentationKernel rho B :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel rho B).mp hBchar
  have hAle : A ≤ rho.ker := by
    intro a ha
    exact hArep ⟨a, ha⟩
  have hBle : B ≤ rho.ker := by
    intro b hb
    exact hBrep ⟨b, hb⟩
  have hsupRep : Section1.subgroupInRepresentationKernel rho (A ⊔ B) := by
    intro x
    exact (sup_le hAle hBle) x.property
  have hsupChar : Section1.subgroupInKernel' rho.character (A ⊔ B) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho (A ⊔ B)).mpr hsupRep
  exact Section1.subgroupInKernel'_of_eq hchi.symm hsupChar

/-- Such a kernel-nontrivial irreducible character vanishes off the
Frobenius kernel. -/
private theorem frobenius_irreducible_character_eq_zero_of_not_mem_kernel
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (chi : Section1.ClassFunction H)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hnotker : ¬ Section1.subgroupInKernel' chi F)
    {x : H} (hx : x ∉ F) : chi x = 0 := by
  let : F.Normal := hFrob.normal
  obtain ⟨theta, _htheta, hchiInd⟩ :=
    frobenius_irreducible_character_eq_induced_of_not_kernel
      F D hFrob chi hchi hnotker
  rw [hchiInd]
  exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal F theta hx

private theorem huppert_XI_6_virtualCharacter_zsmul
    {Q : Type u} [Group Q]
    (n : ℤ) {chi : Section1.ClassFunction Q}
    (hchi : Theory.Character.IsVirtualCharacter chi) :
    Theory.Character.IsVirtualCharacter ((n : ℂ) • chi) := by
  classical
  rcases hchi with ⟨r, m, k, rho, rfl⟩
  refine ⟨r, fun i => n * m i, k, rho, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations,
    Finset.mul_sum, mul_assoc]

private theorem huppert_XI_6_virtualCharacter_finset_sum
    {Q : Type u} [Group Q] [Finite Q]
    {I : Type*} (s : Finset I) (Phi : I → Section1.ClassFunction Q)
    (hPhi : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Phi i)) :
    Theory.Character.IsVirtualCharacter (s.sum Phi) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (Section3.isVirtualCharacter_sub
          (G := Q)
          Section3.isVirtualCharacter_principalCharacter
          Section3.isVirtualCharacter_principalCharacter)
  | @insert a s ha ih =>
      have ha' := hPhi a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (s.sum Phi) := by
        apply ih
        intro i hi
        exact hPhi i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

private theorem huppert_XI_6_virtualCharacter_evalCoeff
    {Q I : Type u} [Group Q] [Finite Q] [Fintype I] [DecidableEq I]
    (mu : I → Section1.ClassFunction Q)
    (hmu : ∀ i, Theory.Character.IsVirtualCharacter (mu i))
    (v : Section1.CoeffVector I) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff mu v) := by
  classical
  rw [Section1.evalCoeff]
  apply huppert_XI_6_virtualCharacter_finset_sum Finset.univ
    (fun i => ((v i : ℂ) • mu i))
  intro i _hi
  exact huppert_XI_6_virtualCharacter_zsmul (v i) (hmu i)

/-- On the degree-zero lattice spanned by the kernel-nontrivial irreducible
characters of a Frobenius point stabilizer, induction is an integral
isometry. -/
private theorem frobenius_nonker_induction_isometry_data
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hTI : Suzuki.VI.IsTISubsetRelative H (F.map H.subtype : Set G))
    (Y : Finset (Section1.ClassFunction H))
    (hYirr : ∀ chi : Y,
      Section1.IsIrreducibleCharacterOnGroup (chi : Section1.ClassFunction H))
    (hYnonker : ∀ chi : Y,
      ¬ Section1.subgroupInKernel' (chi : Section1.ClassFunction H) F) :
    Section5.isCFLinearIsometryOnSpanOn Y Section5.puncturedSet
        (Section1.inducedCFLinear H) ∧
      ∀ phi : Section1.ClassFunction H,
        Section5.integerSpanOn Y Section5.puncturedSet phi →
          Theory.Character.IsVirtualCharacter (Section1.inducedCFLinear H phi) ∧
            Section1.supportedOn (Section1.inducedCFLinear H phi)
              Section5.puncturedSet := by
  classical
  let : F.Normal := hFrob.normal
  have hmem_map_iff (x : H) :
      (x : G) ∈ F.map H.subtype ↔ x ∈ F := by
    constructor
    · rintro ⟨f, hf, hfx⟩
      have : (f : H) = x := by exact Subtype.ext hfx
      simpa [this] using hf
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hspanVirtual {phi : Section1.ClassFunction H}
      (hphi : Section5.integerSpan Y phi) :
      Theory.Character.IsVirtualCharacter phi := by
    rcases hphi with ⟨v, rfl⟩
    apply huppert_XI_6_virtualCharacter_evalCoeff
    intro chi
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hYirr chi)
  have hspanSupport {phi : Section1.ClassFunction H}
      (hphi : Section5.integerSpan Y phi) :
      ∀ x : H, (x : G) ∉ (F.map H.subtype : Set G) → phi x = 0 := by
    rcases hphi with ⟨v, rfl⟩
    intro x hx
    unfold Section1.evalCoeff
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro chi _hchi
    have hxF : x ∉ F := by simpa [hmem_map_iff] using hx
    have hzero :=
      frobenius_irreducible_character_eq_zero_of_not_mem_kernel
        F D hFrob (chi : Section1.ClassFunction H)
          (hYirr chi) (hYnonker chi) hxF
    simp [hzero]
  constructor
  · intro phi psi hphi hpsi
    have hphiVirtual := hspanVirtual hphi.1
    have hpsiVirtual := hspanVirtual hpsi.1
    have hphiSupport := hspanSupport hphi.1
    have hpsiSupport := hspanSupport hpsi.1
    have hphiOne : phi 1 = 0 := by
      exact (Section1.supportedOn_iff.mp hphi.2) 1 (by simp [Section5.puncturedSet])
    have hprop := Suzuki.VI.suzuki_ch6_proposition_2_9
      H (F.map H.subtype : Set G) hTI phi hphiVirtual hphiSupport
    simpa [Section1.inducedCFLinear_apply] using
      hprop.2.2 hphiOne psi hpsiVirtual hpsiSupport
  · intro phi hphi
    have hphiVirtual := hspanVirtual hphi.1
    constructor
    · simpa [Section1.inducedCFLinear_apply] using
        (Section2.inducedCF_isVirtualCharacter_of_virtualCharacter H hphiVirtual)
    · apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
      have hdegreePhi : Section1.degree phi = 0 :=
        (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).1 hphi.2
      rw [Section1.inducedCFLinear_apply,
        Section1.degree_inducedClassFunction, hdegreePhi]
      simp

private theorem huppert_XI_6_ofConjClassFunction_irreducibleOnGroup
    {Q : Type u} [Group Q] [Finite Q]
    {chi : Theory.Character.ConjClassFunction Q}
    (hchi : Theory.Character.IsIrreducibleConjCharacter chi) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction chi) := by
  rcases hchi with ⟨hchar, hnorm⟩
  rcases hchar with ⟨n, rho, hchiEq⟩
  have hrhoNorm :
      Theory.Character.classFunctionInner
          ((Theory.Character.characterClassFunction rho))
          ((Theory.Character.characterClassFunction rho)) = 1 := by
    simpa [hchiEq] using hnorm
  have hrhoIrr : Representation.IsIrreducible rho :=
    (Theory.Character.irreducible_iff_character_norm_one (ρ := rho)).2 hrhoNorm
  refine ⟨n, rho, hrhoIrr, ?_⟩
  rw [hchiEq]
  exact Section1.ofConjClassFunction_characterClassFunction rho

private theorem huppert_XI_6_toConjClassFunction_irreducible
    {Q : Type u} [Group Q] [Finite Q]
    {chi : Section1.ClassFunction Q}
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi) :
    Theory.Character.IsIrreducibleConjCharacter
      (Section1.toConjClassFunction chi
        (Section1.isCharacter_isClassFunction chi
          (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi))) := by
  let hclass : Section1.IsClassFunction chi :=
    Section1.isCharacter_isClassFunction chi
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi)
  rcases hchi with ⟨n, rho, hrhoIrr, hchiEq⟩
  have hchar_eq : Section1.toConjClassFunction chi hclass = (Theory.Character.characterClassFunction rho) := by
    apply Section1.toConjClassFunction_eq_of_apply
    intro g
    rw [hchiEq]
    rfl
  refine ⟨⟨n, rho, hchar_eq⟩, ?_⟩
  · have hnorm :=
      (Theory.Character.irreducible_iff_character_norm_one (ρ := rho)).1 hrhoIrr
    simpa [hchar_eq] using hnorm

private theorem huppert_XI_6_positive_degree_nat
    {Q : Type u} [Group Q] [Finite Q]
    {chi : Section1.ClassFunction Q}
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi) :
    ∃ d : ℕ, 0 < d ∧ Section1.degree chi = (d : ℂ) ∧ d ∣ Nat.card Q := by
  obtain ⟨d, hdegree, hdvd⟩ :=
    Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter chi
      (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi)
  refine ⟨d, ?_, hdegree, hdvd⟩
  by_contra hd0
  have hdzero : d = 0 := Nat.eq_zero_of_not_pos hd0
  have hdegreeZero : Section1.degree chi = 0 := by simpa [hdzero] using hdegree
  exact (Section1.degree_ne_zero_of_isBookIrreducibleCharacter chi
    (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi))
    hdegreeZero
private theorem huppert_XI_6_complete_irreducible_finset
    {Q : Type u} [Group Q] [Finite Q] :
    ∃ K : Finset (Section1.ClassFunction Q),
      (∀ chi : K,
        Section1.IsIrreducibleCharacterOnGroup
          (chi : Section1.ClassFunction Q)) ∧
      ∀ chi : Section1.ClassFunction Q,
        Section1.IsIrreducibleCharacterOnGroup chi →
        chi ∈ K := by
  classical
  obtain ⟨I, hIFintype, phi, hphi, _hsum⟩ :=
    Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := Q)
  let : Fintype I := hIFintype
  let mu : I → Section1.ClassFunction Q := fun i =>
    Section1.ofConjClassFunction (phi i)
  let K : Finset (Section1.ClassFunction Q) := Finset.univ.image mu
  refine ⟨K, ?_, ?_⟩
  · intro chi
    rcases Finset.mem_image.mp chi.property with ⟨i, _hi, hichi⟩
    rw [← hichi]
    exact huppert_XI_6_ofConjClassFunction_irreducibleOnGroup (hphi.1 i)
  · intro chi hchi
    let hclass : Section1.IsClassFunction chi :=
      Section1.isCharacter_isClassFunction chi
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi)
    let Phi : Theory.Character.ConjClassFunction Q :=
      Section1.toConjClassFunction chi hclass
    have hPhiIrr : Theory.Character.IsIrreducibleConjCharacter Phi := by
      simpa [Phi, hclass] using
        (huppert_XI_6_toConjClassFunction_irreducible hchi)
    obtain ⟨i, hi⟩ := hphi.2.1 Phi hPhiIrr
    have hmu : mu i = chi := by
      ext g
      change phi i (ConjClasses.mk g) = chi g
      rw [hi]
      exact Section1.toConjClassFunction_apply chi hclass g
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ i, hmu⟩

/-- XI.6.5 interface: the kernel-nontrivial irreducible characters of a
finite group form a finite complete family in the elementwise class-function
model used by the coherent-isometry theorems. -/
private theorem huppert_XI_6_5_nonker_irreducible_finset
    {Q : Type u} [Group Q] [Finite Q] (F : Subgroup Q) :
    ∃ Y : Finset (Section1.ClassFunction Q),
      (∀ chi : Y,
        Section1.IsIrreducibleCharacterOnGroup
          (chi : Section1.ClassFunction Q)) ∧
      (∀ chi : Y,
        ¬ Section1.subgroupInKernel'
          (chi : Section1.ClassFunction Q) F) ∧
      ∀ chi : Section1.ClassFunction Q,
        Section1.IsIrreducibleCharacterOnGroup chi →
        ¬ Section1.subgroupInKernel' chi F →
        chi ∈ Y := by
  classical
  obtain ⟨I, hIFintype, phi, hphi, _hsum⟩ :=
    Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := Q)
  let : Fintype I := hIFintype
  let mu : I → Section1.ClassFunction Q := fun i =>
    Section1.ofConjClassFunction (phi i)
  let good : Finset I :=
    Finset.univ.filter fun i =>
      ¬ Section1.subgroupInKernel' (mu i) F
  let Y : Finset (Section1.ClassFunction Q) := good.image mu
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro chi
    rcases Finset.mem_image.mp chi.property with ⟨i, hi, hichi⟩
    rw [← hichi]
    exact huppert_XI_6_ofConjClassFunction_irreducibleOnGroup (hphi.1 i)
  · intro chi
    rcases Finset.mem_image.mp chi.property with ⟨i, hi, hichi⟩
    rw [← hichi]
    exact (Finset.mem_filter.mp hi).2
  · intro chi hchi hnonker
    let hclass : Section1.IsClassFunction chi :=
      Section1.isCharacter_isClassFunction chi
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi)
    let Phi : Theory.Character.ConjClassFunction Q :=
      Section1.toConjClassFunction chi hclass
    have hPhiIrr : Theory.Character.IsIrreducibleConjCharacter Phi := by
      simpa [Phi, hclass] using
        (huppert_XI_6_toConjClassFunction_irreducible hchi)
    obtain ⟨i, hi⟩ := hphi.2.1 Phi hPhiIrr
    have hmu : mu i = chi := by
      ext g
      change phi i (ConjClasses.mk g) = chi g
      rw [hi]
      exact Section1.toConjClassFunction_apply chi hclass g
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hmu⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ i, by simpa [hmu] using hnonker⟩
set_option backward.isDefEq.respectTransparency false in
/-- The complete family of irreducible characters nontrivial on a Frobenius
kernel is exactly Peterfalvi's base induced-kernel family. -/
private theorem huppert_XI_6_5_complete_nonker_is_inducedKernelFamily
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (Y : Finset (Section1.ClassFunction H))
    (hYirr : ∀ chi : Y,
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction H))
    (hYnonker : ∀ chi : Y,
      ¬ Section1.subgroupInKernel'
        (chi : Section1.ClassFunction H) F)
    (hYcomplete : ∀ chi : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup chi →
      ¬ Section1.subgroupInKernel' chi F →
      chi ∈ Y) :
    Section6.inducedKernelFamily F ⊥ Y := by
  classical
  let : F.Normal := hFrob.normal
  refine ⟨bot_le, ?_⟩
  intro chi
  constructor
  · intro hchiY
    let chiY : Y := ⟨chi, hchiY⟩
    obtain ⟨theta, hthetaIrr, hchiInd⟩ :=
      frobenius_irreducible_character_eq_induced_of_not_kernel
        F D hFrob chi (hYirr chiY) (hYnonker chiY)
    refine ⟨theta, hthetaIrr, ?_, ?_, hchiInd⟩
    · intro x
      have hx : x = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using x.property
      simp [hx, Section1.degree]
    · intro hthetaPrincipal
      apply hYnonker chiY
      change Section1.subgroupInKernel' chi F
      rw [hchiInd, hthetaPrincipal]
      let rho0 : Representation ℂ F ℂ := Representation.trivial ℂ F ℂ
      have hchar0 : rho0.character = Section1.principalCharacter F := by
        ext f
        simp [rho0, Section1.principalCharacter, Representation.character]
      have hsourceKer :
          Section1.subgroupInKernel' rho0.character (F.subgroupOf F) := by
        intro f
        simp [rho0, Section1.degree, Representation.character]
      have hindKer :=
        (Section1.proposition_1_6_a F F le_rfl rho0).mp hsourceKer
      simpa [hchar0] using hindKer
  · rintro ⟨theta, hthetaIrr, _hthetaBot, hthetaNe, rfl⟩
    rcases hthetaIrr with ⟨n, rho, hrhoIrr, hthetaEq⟩
    have hrhoNonprincipal :
        ¬ Nonempty (rho ≃ₗ Representation.trivial ℂ F ℂ) := by
      rintro ⟨e⟩
      apply hthetaNe
      rw [hthetaEq]
      calc
        rho.character = (Representation.trivial ℂ F ℂ).character :=
          Representation.char_iso e.toRepresentationEquiv
        _ = Section1.principalCharacter F := by
          ext f
          simp [Section1.principalCharacter, Representation.character]
    have hcentralizer : ∀ z : F, z ≠ 1 →
        Subgroup.centralizer ({(z : H)} : Set H) ≤ F :=
      fun z hz => frobenius_kernel_centralizer_le F D hFrob z hz
    have hIndRepIrr :=
      ((Theory.Representation.isaacs_theorem_6_34.{u, 0, 0, 0}
        F hcentralizer).1 rho hrhoIrr hrhoNonprincipal).2
    have hIndIrr : Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF F theta) := by
      rw [hthetaEq, Section1.inducedCF_eq_representation_character]
      exact Section1.isIrreducibleCharacterOnGroup_of_representation
        (Representation.ind F.subtype rho) hIndRepIrr
    apply hYcomplete _ hIndIrr
    intro hIndKer
    have hIndKerRho :
        Section1.subgroupInKernel' (Section1.inducedCF F rho.character) F := by
      simpa [hthetaEq] using hIndKer
    have hrhoKer :
        Section1.subgroupInKernel' rho.character (F.subgroupOf F) :=
      (Section1.proposition_1_6_a F F le_rfl rho).mpr hIndKerRho
    have hthetaTop :
        Section1.subgroupInKernel' theta (⊤ : Subgroup F) := by
      intro f
      rw [hthetaEq]
      exact hrhoKer ⟨f, by simp⟩
    exact huppert_XI_6_not_subgroupInKernel_top_of_ne_principal
      ⟨n, rho, hrhoIrr, hthetaEq⟩ hthetaNe hthetaTop

/-- Complete XI.6.5 induction-isometry package, with no externally supplied
character family. -/
private theorem huppert_XI_6_5_complete_nonker_induction_isometry
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hTI : Suzuki.VI.IsTISubsetRelative H (F.map H.subtype : Set G)) :
    ∃ Y : Finset (Section1.ClassFunction H),
      (∀ chi : Y,
        Section1.IsIrreducibleCharacterOnGroup
          (chi : Section1.ClassFunction H)) ∧
      (∀ chi : Y,
        ¬ Section1.subgroupInKernel'
          (chi : Section1.ClassFunction H) F) ∧
      (∀ chi : Section1.ClassFunction H,
        Section1.IsIrreducibleCharacterOnGroup chi →
        ¬ Section1.subgroupInKernel' chi F →
        chi ∈ Y) ∧
      Section5.isCFLinearIsometryOnSpanOn Y Section5.puncturedSet
        (Section1.inducedCFLinear H) ∧
      ∀ phi : Section1.ClassFunction H,
        Section5.integerSpanOn Y Section5.puncturedSet phi →
          Theory.Character.IsVirtualCharacter
              (Section1.inducedCFLinear H phi) ∧
            Section1.supportedOn (Section1.inducedCFLinear H phi)
              Section5.puncturedSet := by
  obtain ⟨Y, hYirr, hYnonker, hYcomplete⟩ :=
    huppert_XI_6_5_nonker_irreducible_finset F
  obtain ⟨hisometry, hdegreeZero⟩ :=
    frobenius_nonker_induction_isometry_data
      H F D hFrob hTI Y hYirr hYnonker
  exact ⟨Y, hYirr, hYnonker, hYcomplete, hisometry, hdegreeZero⟩

/-- The derived-subgroup subfamily supplies the equal minimal degree and the
common divisibility needed by the XI.6.5 coherence induction. -/
private theorem huppert_XI_6_5_derived_base_degree_data
    {H : Type u} [Group H] [Finite H]
    (F : Subgroup H) [F.Normal]
    (Y : Finset (Section1.ClassFunction H))
    (hYbot : Section6.inducedKernelFamily F ⊥ Y) :
    let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
    ∃ degreeNat : Section1.ClassFunction H → ℕ,
      let m := F.relIndex (⊤ : Subgroup H)
      Y0 ⊆ Y ∧
        (∀ chi : Y,
          Section1.degree (chi : Section1.ClassFunction H) =
            (degreeNat chi : ℂ)) ∧
        (∀ chi : Y0, degreeNat chi = m) ∧
        (∀ chi : Y,
          (chi : Section1.ClassFunction H) ∉ Y0 → m ∣ degreeNat chi) := by
  classical
  let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
  have hcommLe : ⁅F, F⁆ ≤ F :=
    Subgroup.commutator_le_left (H₁ := F) (H₂ := F)
  have hY0 : Section6.inducedKernelFamily F ⁅F, F⁆ Y0 :=
    Section6.inducedKernelFamilyOf_isFamily hYbot hcommLe
  have hY0sub : Y0 ⊆ Y :=
    Section6.inducedKernelFamily_subset_base hYbot hY0
  let degreeNat : Section1.ClassFunction H → ℕ := fun chi =>
    if hchi : chi ∈ Y then
      Classical.choose (Classical.choose_spec
        (Section6.inducedKernelFamily_degree_data hYbot hchi))
    else 0
  have hdegree : ∀ chi : Y,
      Section1.degree (chi : Section1.ClassFunction H) =
        (degreeNat chi : ℂ) := by
    intro chi
    dsimp [degreeNat]
    rw [dif_pos chi.property]
    exact (Classical.choose_spec (Classical.choose_spec
      (Section6.inducedKernelFamily_degree_data hYbot chi.property))).1
  have hdiv : ∀ chi : Y,
      F.relIndex (⊤ : Subgroup H) ∣ degreeNat chi := by
    intro chi
    dsimp [degreeNat]
    rw [dif_pos chi.property]
    exact (Classical.choose_spec (Classical.choose_spec
      (Section6.inducedKernelFamily_degree_data hYbot chi.property))).2.2
  have hderNorm : ⁅F, F⁆.Normal := Subgroup.commutator_normal F F
  have hcommHyp :=
    Section6.theorem_6_8_commutatorQuotient_bot_commutator F
      (inferInstance : F.Normal)
  have hquotComm : IsMulCommutative (F ⧸ ⁅F, F⁆.subgroupOf F) :=
    Section6.commutatorQuotientHypothesis_quotient_commutative
      hderNorm hcommHyp
  have hY0degree : ∀ chi : Y0,
      degreeNat chi = F.relIndex (⊤ : Subgroup H) := by
    intro chi
    have hdegBase :=
      Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
        hY0 hderNorm hquotComm chi.property
    have hcast : (degreeNat chi : ℂ) =
        (F.relIndex (⊤ : Subgroup H) : ℂ) := by
      rw [← hdegree ⟨chi, hY0sub chi.property⟩]
      exact hdegBase
    exact_mod_cast hcast
  exact ⟨degreeNat, hY0sub, hdegree, hY0degree,
    fun chi _hchi => hdiv chi⟩

/-- Mixed-prime nilpotence supplies two distinct derived-layer induced characters. -/
private theorem huppert_XI_6_5_derived_base_card_two
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFnil : Group.IsNilpotent F)
    (hnotPrimePower : ¬ IsPrimePow (Nat.card F))
    (Y : Finset (Section1.ClassFunction H))
    (hYbot : Section6.inducedKernelFamily F ⊥ Y) :
    let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
    2 ≤ Y0.card := by
  classical
  let : F.Normal := hFrob.normal
  let : Group.IsNilpotent F := hFnil
  have hcommEq : ⁅F, F⁆.subgroupOf F = _root_.commutator F := by
    ext x
    constructor
    · intro hx
      have hxmap : (x : H) ∈ (_root_.commutator F).map F.subtype := by
        rw [Subgroup.map_subtype_commutator]
        exact hx
      rcases hxmap with ⟨y, hycomm, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hycomm
    · intro hx
      have hxmap : (x : H) ∈ (_root_.commutator F).map F.subtype :=
        ⟨x, hx, rfl⟩
      rwa [Subgroup.map_subtype_commutator] at hxmap
  have hcommLe : ⁅F, F⁆ ≤ F :=
    Subgroup.commutator_le_left (H₁ := F) (H₂ := F)
  let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
  have hY0 : Section6.inducedKernelFamily F ⁅F, F⁆ Y0 :=
    Section6.inducedKernelFamilyOf_isFamily hYbot hcommLe
  have hFcard_gt : 1 < Nat.card F :=
    (Subgroup.one_lt_card_iff_ne_bot F).2 hFrob.kernel_ne_bot
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hFcard_gt.ne'
  have hnotPow : ∀ n, Nat.card F ≠ p ^ n := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      have hcard_ne_one : Nat.card F ≠ 1 := Nat.ne_of_gt hFcard_gt
      exact hcard_ne_one (by simpa using hn)
    · apply hnotPrimePower
      exact (isPrimePow_nat_iff (Nat.card F)).2
        ⟨p, n, hp, Nat.pos_of_ne_zero hn0, hn.symm⟩
  obtain ⟨q, hq, hq_dvd, hq_ne_p⟩ :=
    hkt_exists_prime_dvd_ne_of_not_prime_power Nat.card_pos.ne' hnotPow
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hpCore_le_qPrimeCore : pCore p F ≤ pPrimeCore q F := by
    obtain ⟨n, hcard⟩ :=
      (pCore_isPGroup (G := F) (p := p)).exists_card_eq
    have hcop : Nat.Coprime q (Nat.card (pCore p F)) := by
      rw [hcard]
      exact ((Nat.coprime_primes hq hp).2 hq_ne_p).pow_right n
    exact le_sSup
      (show pCore p F ∈
        {K : Subgroup F | K.Normal ∧ Nat.Coprime q (Nat.card K)} from
        ⟨inferInstance, hcop⟩)
  have hpPrimeCore_ne_top : pPrimeCore p F ≠ ⊤ := by
    intro htop
    have hp_dvd_core : p ∣ Nat.card (pPrimeCore p F) := by
      simpa [htop] using hp_dvd
    exact (hp.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := F) (p := p))) hp_dvd_core
  have hqPrimeCore_ne_top : pPrimeCore q F ≠ ⊤ := by
    intro htop
    have hq_dvd_core : q ∣ Nat.card (pPrimeCore q F) := by
      simpa [htop] using hq_dvd
    exact (hq.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := F) (p := q))) hq_dvd_core
  let : Group.IsSolvable F := IsNilpotent.to_isSolvable
  have : Nontrivial (F ⧸ pPrimeCore p F) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hpPrimeCore_ne_top
  have : Nontrivial (F ⧸ pPrimeCore q F) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hqPrimeCore_ne_top
  obtain ⟨psiP, hpsiP⟩ :=
    Section6.exists_nontrivial_linear_character_of_solvable
      (F ⧸ pPrimeCore p F)
  obtain ⟨psiQ, hpsiQ⟩ :=
    Section6.exists_nontrivial_linear_character_of_solvable
      (F ⧸ pPrimeCore q F)
  let piP : F →* F ⧸ pPrimeCore p F := QuotientGroup.mk' (pPrimeCore p F)
  let piQ : F →* F ⧸ pPrimeCore q F := QuotientGroup.mk' (pPrimeCore q F)
  let lambdaP : F →* ℂˣ := psiP.comp piP
  let lambdaQ : F →* ℂˣ := psiQ.comp piQ
  let thetaP : Section1.ClassFunction F :=
    Section1.characterInflationByHom piP psiP
  let thetaQ : Section1.ClassFunction F :=
    Section1.characterInflationByHom piQ psiQ
  have hthetaPirr : Section1.IsIrreducibleCharacterOnGroup thetaP :=
    Section1.characterInflationByHom_isIrreducibleCharacterOnGroup piP psiP
  have hthetaQirr : Section1.IsIrreducibleCharacterOnGroup thetaQ :=
    Section1.characterInflationByHom_isIrreducibleCharacterOnGroup piQ psiQ
  have hthetaPne : thetaP ≠ Section1.principalCharacter F := by
    intro heq
    apply hpsiP
    ext z
    have hz := congrFun heq z
    simpa [thetaP, piP, Section1.characterInflationByHom,
      Section1.principalCharacter] using hz
  have hthetaQne : thetaQ ≠ Section1.principalCharacter F := by
    intro heq
    apply hpsiQ
    ext z
    have hz := congrFun heq z
    simpa [thetaQ, piQ, Section1.characterInflationByHom,
      Section1.principalCharacter] using hz
  have hthetaPprime :
      Section1.subgroupInKernel' thetaP (pPrimeCore p F) := by
    intro x
    have hxq : piP (x : F) = 1 := by
      exact (QuotientGroup.eq_one_iff (N := pPrimeCore p F) (x : F)).2 x.property
    simp [thetaP, piP, Section1.characterInflationByHom,
      Section1.degree, hxq]
  have hthetaQprime :
      Section1.subgroupInKernel' thetaQ (pPrimeCore q F) := by
    intro x
    have hxq : piQ (x : F) = 1 := by
      exact (QuotientGroup.eq_one_iff (N := pPrimeCore q F) (x : F)).2 x.property
    simp [thetaQ, piQ, Section1.characterInflationByHom,
      Section1.degree, hxq]
  have hthetaQpCore :
      Section1.subgroupInKernel' thetaQ (pCore p F) := by
    intro x
    exact hthetaQprime ⟨x, hpCore_le_qPrimeCore x.property⟩
  have hthetaPcomm :
      Section1.subgroupInKernel' thetaP (⁅F, F⁆.subgroupOf F) := by
    rw [hcommEq]
    intro x
    have hxker : lambdaP (x : F) = 1 :=
      Abelianization.commutator_subset_ker lambdaP x.property
    have hxkerC := congrArg (fun z : ℂˣ => (z : ℂ)) hxker
    simpa [thetaP, lambdaP, piP, Section1.characterInflationByHom,
      Section1.degree] using hxkerC
  have hthetaQcomm :
      Section1.subgroupInKernel' thetaQ (⁅F, F⁆.subgroupOf F) := by
    rw [hcommEq]
    intro x
    have hxker : lambdaQ (x : F) = 1 :=
      Abelianization.commutator_subset_ker lambdaQ x.property
    have hxkerC := congrArg (fun z : ℂˣ => (z : ℂ)) hxker
    simpa [thetaQ, lambdaQ, piQ, Section1.characterInflationByHom,
      Section1.degree] using hxkerC
  have hthetaPnotCore :
      ¬ Section1.subgroupInKernel' thetaP (pCore p F) := by
    intro hthetaPcore
    have hsup := huppert_XI_6_subgroupInKernel_sup
      hthetaPirr hthetaPcore hthetaPprime
    have htop : Section1.subgroupInKernel' thetaP (⊤ : Subgroup F) := by
      intro x
      exact hsup ⟨x,
        (nilpotent_top_le_pCore_sup_pPrimeCore (Q := F) (p := p) hFnil)
          x.property⟩
    exact huppert_XI_6_not_subgroupInKernel_top_of_ne_principal
      hthetaPirr hthetaPne htop
  let chiP : Section1.ClassFunction H := Section1.inducedCF F thetaP
  let chiQ : Section1.ClassFunction H := Section1.inducedCF F thetaQ
  have hchiP : chiP ∈ Y0 :=
    (hY0.2 chiP).2 ⟨thetaP, hthetaPirr, hthetaPcomm, hthetaPne, rfl⟩
  have hchiQ : chiQ ∈ Y0 :=
    (hY0.2 chiQ).2 ⟨thetaQ, hthetaQirr, hthetaQcomm, hthetaQne, rfl⟩
  have hchi_ne : chiP ≠ chiQ := by
    intro hInd
    rcases hthetaPirr with ⟨nP, rhoP, hrhoP, hthetaPEq⟩
    rcases hthetaQirr with ⟨nQ, rhoQ, hrhoQ, hthetaQEq⟩
    have hIndRep :
        Section1.inducedCF F rhoP.character =
          Section1.inducedCF F rhoQ.character := by
      simpa [chiP, chiQ, hthetaPEq, hthetaQEq] using hInd
    obtain ⟨i, hi⟩ :=
      Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
        F rhoP rhoQ hrhoP hrhoQ hIndRep
    obtain ⟨g, hg⟩ : ∃ g : H,
        rhoP.character =
          Section1.conjugateOnNormal F rhoQ.character g := by
      revert hi
      refine Quotient.inductionOn i ?_
      intro g hi
      exact ⟨g, hi⟩
    have hthetaConj :
        thetaP = Section1.conjugateOnNormal F thetaQ g := by
      rw [hthetaPEq, hthetaQEq]
      exact hg
    apply hthetaPnotCore
    intro x
    let phi : MulAut F := MulAut.conjNormal (H := F) g
    have hmap : (pCore p F).map phi = pCore p F :=
      (Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (pCore p F).Characteristic)) phi
    have hxphi : phi (x : F) ∈ pCore p F := by
      have hxmap : phi (x : F) ∈ (pCore p F).map phi :=
        ⟨x, x.property, rfl⟩
      rw [hmap] at hxmap
      exact hxmap
    have hval := hthetaQpCore ⟨phi (x : F), hxphi⟩
    calc
      thetaP (x : F) =
          Section1.conjugateOnNormal F thetaQ g (x : F) :=
        congrFun hthetaConj (x : F)
      _ = thetaQ (phi (x : F)) := by
        congr 1
      _ = Section1.degree thetaQ := hval
      _ = Section1.degree thetaP := by
        simp [thetaP, thetaQ, Section1.characterInflationByHom,
          Section1.degree]
  have hsub : {chiP, chiQ} ⊆ Y0 := by
    intro chi hchi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hchi
    rcases hchi with rfl | rfl
    · exact hchiP
    · exact hchiQ
  have hcard := Finset.card_le_card hsub
  simpa [hchi_ne] using hcard


section XI6CoherentDegree

open scoped BigOperators TensorProduct
open Section1 Section5

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

/-- The class-function inner product of two outer tensor characters factors
as the product of the two component inner products. -/
private theorem prod_tprod_character_inner
    {P Q V₁ V₂ W₁ W₂ : Type*}
    [Group P] [Finite P] [Group Q] [Finite Q]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup W₁] [Module ℂ W₁] [FiniteDimensional ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
    (rho₁ : Representation ℂ P V₁) (rho₂ : Representation ℂ P V₂)
    (sigma₁ : Representation ℂ Q W₁) (sigma₂ : Representation ℂ Q W₂) :
    Theory.Character.classFunctionInner
        (Theory.Character.characterClassFunction
          (Representation.tprod
            (rho₁.comp (MonoidHom.fst P Q))
            (sigma₁.comp (MonoidHom.snd P Q))))
        (Theory.Character.characterClassFunction
          (Representation.tprod
            (rho₂.comp (MonoidHom.fst P Q))
            (sigma₂.comp (MonoidHom.snd P Q)))) =
      Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction rho₁)
          (Theory.Character.characterClassFunction rho₂) *
        Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction sigma₁)
          (Theory.Character.characterClassFunction sigma₂) := by
  classical
  rw [Theory.Character.classFunctionInner,
    Theory.Character.classFunctionInner,
    Theory.Character.classFunctionInner]
  simp [Theory.Character.characterClassFunction,
    Theory.Character.conjClassFunctionOfInvariant, ConjClasses.mk,
    Representation.character]
  have hsumProd (f : P × Q → ℂ) :
      (∑ g ∈ @Finset.univ (P × Q) (Fintype.ofFinite (P × Q)), f g) =
        ∑ p : P, ∑ q : Q, f (p, q) := by
    have huniv :
        @Finset.univ (P × Q) (Fintype.ofFinite (P × Q)) =
          (Finset.univ : Finset P).product (Finset.univ : Finset Q) := by
      ext g
      simp
    calc
      (∑ g ∈ @Finset.univ (P × Q) (Fintype.ofFinite (P × Q)), f g) =
          ∑ g ∈ (Finset.univ : Finset P).product (Finset.univ : Finset Q), f g := by
            rw [huniv]
      _ = ∑ p : P, ∑ q : Q, f (p, q) := by
        exact Finset.sum_product (Finset.univ : Finset P)
          (Finset.univ : Finset Q) f
  rw [hsumProd]
  change (Fintype.card Q : ℂ)⁻¹ * (Fintype.card P : ℂ)⁻¹ *
      (∑ p : P, ∑ q : Q,
        rho₁.character p * sigma₁.character q *
          (star (rho₂.character p) * star (sigma₂.character q))) =
    ((Fintype.card P : ℂ)⁻¹ *
      ∑ p : P, rho₁.character p * star (rho₂.character p)) *
    ((Fintype.card Q : ℂ)⁻¹ *
      ∑ q : Q, sigma₁.character q * star (sigma₂.character q))
  have hfactor (p : P) (q : Q) :
      rho₁.character p * sigma₁.character q *
          (star (rho₂.character p) * star (sigma₂.character q)) =
        (rho₁.character p * star (rho₂.character p)) *
          (sigma₁.character q * star (sigma₂.character q)) := by
    ring
  simp_rw [hfactor]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- The outer tensor product of two irreducible complex representations is
irreducible on the direct-product group. -/
private theorem prod_tprod_irreducible
    {P Q V W : Type*}
    [Group P] [Finite P] [Group Q] [Finite Q]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ P V) (sigma : Representation ℂ Q W)
    (hrho : Representation.IsIrreducible rho)
    (hsigma : Representation.IsIrreducible sigma) :
    Representation.IsIrreducible
      (Representation.tprod
        (rho.comp (MonoidHom.fst P Q))
        (sigma.comp (MonoidHom.snd P Q))) := by
  apply (Theory.Character.irreducible_iff_character_norm_one _).2
  rw [prod_tprod_character_inner,
    (Theory.Character.irreducible_iff_character_norm_one rho).1 hrho,
    (Theory.Character.irreducible_iff_character_norm_one sigma).1 hsigma]
  simp

/-- A nilpotent finite group is the internal direct product of its p-core
and its p-prime core. -/
private theorem nilpotent_internalDirectProduct_pCore_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ) (hp : Nat.Prime p) (hnil : Group.IsNilpotent Q) :
    Section2.IsInternalDirectProduct (⊤ : Subgroup Q)
      (pCore p Q) (pPrimeCore p Q) := by
  let : Fact p.Prime := ⟨hp⟩
  have hsup : pCore p Q ⊔ pPrimeCore p Q = (⊤ : Subgroup Q) :=
    top_unique (nilpotent_top_le_pCore_sup_pPrimeCore hnil)
  have hcop : Nat.Coprime (Nat.card (pCore p Q))
      (Nat.card (pPrimeCore p Q)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := Q) (p := p)).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (G := Q) (p := p)).pow_left n
  have hinf : pCore p Q ⊓ pPrimeCore p Q = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hdis : Disjoint (pCore p Q) (pPrimeCore p Q) := disjoint_iff.mpr hinf
  refine
    { left_le := le_top
      right_le := le_top
      commute := ?_
      inf_eq_bot := hinf
      mul_surjective := ?_ }
  · intro x hx y hy
    exact (Subgroup.commute_of_normal_of_disjoint
      (pCore p Q) (pPrimeCore p Q) (inferInstance : (pCore p Q).Normal)
      (pPrimeCore_normal (G := Q) (p := p)) hdis x y hx hy).eq
  · intro q hq
    have hqSup : q ∈ pCore p Q ⊔ pPrimeCore p Q := by
      rw [hsup]
      exact hq
    rcases Subgroup.mem_sup_of_normal_right.mp hqSup with
      ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hxy.symm⟩

/-- A prime divisor of the order of a finite nilpotent group occurs in its
corresponding p-core. -/
private theorem huppert_XI_6_3_pCore_ne_bot_of_nilpotent_dvd_card
    {Q : Type*} [Group Q] [Finite Q]
    (p : ℕ) (hp : Nat.Prime p) (hnil : Group.IsNilpotent Q)
    (hpdvd : p ∣ Nat.card Q) :
    pCore p Q ≠ ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let S : Sylow p Q := Classical.choice inferInstance
  have hSnormal : (S : Subgroup Q).Normal :=
    Group.IsNilpotent.sylow_normal hnil p S
  have hSle : (S : Subgroup Q) ≤ pCore p Q :=
    le_sSup ⟨hSnormal, S.isPGroup'⟩
  have hpS : p ∣ Nat.card (S : Subgroup Q) :=
    Sylow.dvd_card_of_dvd_card S hpdvd
  intro hbot
  have hSbot : (S : Subgroup Q) = ⊥ :=
    le_bot_iff.mp (hSle.trans (le_of_eq hbot))
  have hcardS : Nat.card (S : Subgroup Q) = 1 := by
    simp [hSbot]
  rw [hcardS] at hpS
  exact hp.not_dvd_one hpS

/-- In a nilpotent p-core decomposition, the abelianization of the p-core
injects at the level of linear-character cardinality into the abelianization
of the whole group. -/
private theorem huppert_XI_6_3_pCore_abelianization_card_le
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ) (hp : Nat.Prime p) (hnil : Group.IsNilpotent Q) :
    Nat.card (Abelianization (pCore p Q)) ≤
      Nat.card (Abelianization Q) := by
  let hprod :=
    nilpotent_internalDirectProduct_pCore_pPrimeCore p hp hnil
  let e : (pCore p Q) × (pPrimeCore p Q) ≃* Q :=
    (Section3.internalDirectProductMulEquiv hprod).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hproduct :=
    huppert_XI_6_3_product_abelianization_card_le e
  have hright :
      1 ≤ Nat.card (Abelianization (pPrimeCore p Q)) :=
    Nat.card_pos
  calc
    Nat.card (Abelianization (pCore p Q)) =
        Nat.card (Abelianization (pCore p Q)) * 1 := by simp
    _ ≤ Nat.card (Abelianization (pCore p Q)) *
        Nat.card (Abelianization (pPrimeCore p Q)) :=
      Nat.mul_le_mul_left _ hright
    _ ≤ Nat.card (Abelianization Q) := hproduct

/-- Two prime components of a nilpotent group contribute independently to
its abelianization: the second component is taken inside the p-prime core of
the first. -/
private theorem huppert_XI_6_3_two_prime_components_abelianization_product_le
    {Q : Type u} [Group Q] [Finite Q]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hnil : Group.IsNilpotent Q) :
    Nat.card (Abelianization (pCore p Q)) *
        Nat.card (Abelianization (pCore q (pPrimeCore p Q))) ≤
      Nat.card (Abelianization Q) := by
  let : Fact p.Prime := ⟨hp⟩
  let R := pPrimeCore p Q
  let : Group.IsNilpotent Q := hnil
  have hnilR : Group.IsNilpotent R := by infer_instance
  have hsecond :
      Nat.card (Abelianization (pCore q R)) ≤
        Nat.card (Abelianization R) :=
    huppert_XI_6_3_pCore_abelianization_card_le q hq hnilR
  let hprod :=
    nilpotent_internalDirectProduct_pCore_pPrimeCore p hp hnil
  let e : (pCore p Q) × R ≃* Q :=
    (Section3.internalDirectProductMulEquiv hprod).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hwhole :=
    huppert_XI_6_3_product_abelianization_card_le e
  exact (Nat.mul_le_mul_left _ hsecond).trans hwhole

/-- A prime different from p remains in the p-prime core of a finite
nilpotent group. -/
private theorem huppert_XI_6_3_prime_dvd_pPrimeCore_card
    {Q : Type u} [Group Q] [Finite Q]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hnil : Group.IsNilpotent Q) (hqdvd : q ∣ Nat.card Q) :
    q ∣ Nat.card (pPrimeCore p Q) := by
  let : Fact p.Prime := ⟨hp⟩
  let hprod :=
    nilpotent_internalDirectProduct_pCore_pPrimeCore p hp hnil
  let e : (pCore p Q) × (pPrimeCore p Q) ≃* Q :=
    (Section3.internalDirectProductMulEquiv hprod).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hcard :
      Nat.card (pCore p Q) * Nat.card (pPrimeCore p Q) =
        Nat.card Q := by
    simpa [Nat.card_prod] using Nat.card_congr e.toEquiv
  obtain ⟨n, hn⟩ :=
    (pCore_isPGroup (G := Q) (p := p)).exists_card_eq
  have hcop : Nat.Coprime q (Nat.card (pCore p Q)) := by
    rw [hn]
    exact ((Nat.coprime_primes hq hp).2 hpq.symm).pow_right n
  apply hcop.dvd_of_dvd_mul_left
  rw [hcard]
  exact hqdvd
/-- A nontrivial prime component of a nilpotent fixed-point-free kernel has at
least d+1 linear characters, sharpened to 2d+1 for an odd prime component. -/
private theorem huppert_XI_6_3_prime_component_abelianization_lower
    {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q]
    (p : ℕ) (hp : Nat.Prime p) (hnil : Group.IsNilpotent Q)
    (hpdvd : p ∣ Nat.card Q)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ q : Q, d • q = q → q = 1)
    (hoddD : Odd (Nat.card D)) :
    Nat.card D + 1 ≤ Nat.card (Abelianization (pCore p Q)) ∧
      (p ≠ 2 →
        2 * Nat.card D + 1 ≤ Nat.card (Abelianization (pCore p Q))) := by
  let : Fact p.Prime := ⟨hp⟩
  have hPne : pCore p Q ≠ ⊥ :=
    huppert_XI_6_3_pCore_ne_bot_of_nilpotent_dvd_card
      p hp hnil hpdvd
  let : Nontrivial (pCore p Q) :=
    (Subgroup.nontrivial_iff_ne_bot (pCore p Q)).2 hPne
  have hPsolv : Group.IsSolvable (pCore p Q) := by
    let : Group.IsNilpotent (pCore p Q) := pCore_isNilpotent
    exact IsNilpotent.to_isSolvable
  obtain ⟨hdiv, hcard⟩ :=
    huppert_XI_6_3_characteristic_factor_abelianization_data
      (D := D) (Q := Q) (pCore p Q) hPsolv hcop hfree
  constructor
  · exact huppert_XI_6_3_dvd_sub_one_card_lower
      (Nat.card D) (Nat.card (Abelianization (pCore p Q))) hcard hdiv
  · intro hpTwo
    obtain ⟨n, hn⟩ :=
      (pCore_isPGroup (G := Q) (p := p)).exists_card_eq
    have hPodd : Odd (Nat.card (pCore p Q)) := by
      rw [hn]
      exact (hp.odd_of_ne_two hpTwo).pow
    have hAbOdd : Odd (Nat.card (Abelianization (pCore p Q))) :=
      Odd.of_dvd_nat hPodd
        (Subgroup.card_quotient_dvd_card (commutator (pCore p Q)))
    exact huppert_XI_6_3_odd_dvd_sub_one_card_lower
      (Nat.card D) (Nat.card (Abelianization (pCore p Q)))
      hcard hoddD hAbOdd hdiv
/-- Package the abelianization lower bounds for two distinct prime components
of a nilpotent group under the same fixed-point-free actor. -/
private theorem huppert_XI_6_3_two_prime_components_abelianization_lower
    {D Q : Type u} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hnil : Group.IsNilpotent Q)
    (hpdvd : p ∣ Nat.card Q) (hqdvd : q ∣ Nat.card Q)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ x : Q, d • x = x → x = 1)
    (hoddD : Odd (Nat.card D)) :
    let R := pPrimeCore p Q
    let Lp := Nat.card (Abelianization (pCore p Q))
    let Lq := Nat.card (Abelianization (pCore q R))
    (Nat.card D + 1 ≤ Lp ∧
      (p ≠ 2 → 2 * Nat.card D + 1 ≤ Lp)) ∧
    (Nat.card D + 1 ≤ Lq ∧
      (q ≠ 2 → 2 * Nat.card D + 1 ≤ Lq)) ∧
    Lp * Lq ≤ Nat.card (Abelianization Q) := by
  dsimp only
  have hpLower :=
    huppert_XI_6_3_prime_component_abelianization_lower
      (D := D) (Q := Q) p hp hnil hpdvd hcop hfree hoddD
  let : Fact p.Prime := ⟨hp⟩
  let R := pPrimeCore p Q
  let : IsInvariant D Q R := isInvariant_of_characteristic R
  let : Group.IsNilpotent Q := hnil
  have hnilR : Group.IsNilpotent R := by infer_instance
  have hqdvdR : q ∣ Nat.card R := by
    simpa [R] using
      huppert_XI_6_3_prime_dvd_pPrimeCore_card
        p q hp hq hpq hnil hqdvd
  have hcopR : Nat.Coprime (Nat.card D) (Nat.card R) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_subgroup_dvd_card (pPrimeCore p Q)) hcop
  have hfreeR :
      ∀ d : D, d ≠ 1 → ∀ x : R, d • x = x → x = 1 := by
    intro d hd x hx
    apply Subtype.ext
    exact hfree d hd (x : Q) (congrArg Subtype.val hx)
  have hqLower :=
    huppert_XI_6_3_prime_component_abelianization_lower
      (D := D) (Q := R) q hq hnilR hqdvdR hcopR hfreeR hoddD
  refine ⟨hpLower, hqLower, ?_⟩
  simpa [R] using
    huppert_XI_6_3_two_prime_components_abelianization_product_le
      p q hp hq hnil
/-- A prime component inside the p-prime core supplies the same linear-character
lower bound for the whole p-prime core. -/
private theorem huppert_XI_6_3_pPrimeCore_abelianization_lower
    {D Q : Type u} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hnil : Group.IsNilpotent Q) (hqdvd : q ∣ Nat.card Q)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ x : Q, d • x = x → x = 1)
    (hoddD : Odd (Nat.card D)) :
    Nat.card D + 1 ≤
        Nat.card (Abelianization (pPrimeCore p Q)) ∧
      (q ≠ 2 →
        2 * Nat.card D + 1 ≤
          Nat.card (Abelianization (pPrimeCore p Q))) := by
  let : Fact p.Prime := ⟨hp⟩
  let R := pPrimeCore p Q
  let : IsInvariant D Q R := isInvariant_of_characteristic R
  let : Group.IsNilpotent Q := hnil
  have hnilR : Group.IsNilpotent R := by infer_instance
  have hqdvdR : q ∣ Nat.card R := by
    simpa [R] using
      huppert_XI_6_3_prime_dvd_pPrimeCore_card
        p q hp hq hpq hnil hqdvd
  have hcopR : Nat.Coprime (Nat.card D) (Nat.card R) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_subgroup_dvd_card (pPrimeCore p Q)) hcop
  have hfreeR :
      ∀ d : D, d ≠ 1 → ∀ x : R, d • x = x → x = 1 := by
    intro d hd x hx
    apply Subtype.ext
    exact hfree d hd (x : Q) (congrArg Subtype.val hx)
  have hqLower :=
    huppert_XI_6_3_prime_component_abelianization_lower
      (D := D) (Q := R) q hq hnilR hqdvdR hcopR hfreeR hoddD
  have hqLe :
      Nat.card (Abelianization (pCore q R)) ≤
        Nat.card (Abelianization R) :=
    huppert_XI_6_3_pCore_abelianization_card_le q hq hnilR
  exact ⟨hqLower.1.trans hqLe,
    fun hqTwo => (hqLower.2 hqTwo).trans hqLe⟩
private theorem huppert_XI_6_3_exists_distinct_prime_factors
    (n : ℕ) (hn : 2 ≤ n) (hnot : ¬ IsPrimePow n) :
    ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p ∣ n ∧ q ∣ n ∧ p ≠ q := by
  have hnontrivial : n.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hnot
  rw [Finset.nontrivial_def] at hnontrivial
  obtain ⟨p, hpMem, q, hqMem, hpq⟩ := hnontrivial
  exact ⟨p, q, Nat.prime_of_mem_primeFactors hpMem,
    Nat.prime_of_mem_primeFactors hqMem,
    Nat.dvd_of_mem_primeFactors hpMem,
    Nat.dvd_of_mem_primeFactors hqMem, hpq⟩

/-- XI.6.3(b), structural core of the small-sum case.  Two odd prime
components would already make the abelianization too large; hence the two
selected components have types 2 and odd, contributing (d+1)(2d+1). -/
private theorem huppert_XI_6_3_mixed_prime_abelianization_lower
    {D Q : Type u} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q] [Nontrivial Q]
    (hnil : Group.IsNilpotent Q)
    (hnotPrimePower : ¬ IsPrimePow (Nat.card Q))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ x : Q, d • x = x → x = 1)
    (hoddD : Odd (Nat.card D))
    (hAbUpper :
      Nat.card (Abelianization Q) < 4 * Nat.card D ^ 2 + 1) :
    (Nat.card D + 1) * (2 * Nat.card D + 1) ≤
      Nat.card (Abelianization Q) := by
  obtain ⟨p, q, hp, hq, hpdvd, hqdvd, hpq⟩ :=
    huppert_XI_6_3_exists_distinct_prime_factors
      (Nat.card Q) (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
      hnotPrimePower
  obtain ⟨hpLower, hqLower, hprod⟩ :=
    huppert_XI_6_3_two_prime_components_abelianization_lower
      (D := D) (Q := Q) p q hp hq hpq hnil hpdvd hqdvd
      hcop hfree hoddD
  by_cases hpTwo : p = 2
  · have hqTwo : q ≠ 2 := by
      intro hq2
      exact hpq (hpTwo.trans hq2.symm)
    exact (Nat.mul_le_mul hpLower.1 (hqLower.2 hqTwo)).trans hprod
  · by_cases hqTwo : q = 2
    · have hbound :=
        (Nat.mul_le_mul (hpLower.2 hpTwo) hqLower.1).trans hprod
      simpa [mul_comm] using hbound
    · have hsq :=
        (Nat.mul_le_mul (hpLower.2 hpTwo) (hqLower.2 hqTwo)).trans hprod
      nlinarith
private theorem isConj_prod_iff
    {A : Type u} {B : Type v} [Group A] [Group B]
    (x y : A × B) :
    IsConj x y ↔ IsConj x.1 y.1 ∧ IsConj x.2 y.2 := by
  constructor
  · intro h
    exact ⟨(MonoidHom.fst A B).map_isConj h,
      (MonoidHom.snd A B).map_isConj h⟩
  · rintro ⟨hx, hy⟩
    rw [isConj_iff] at hx hy ⊢
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    refine ⟨(a, b), ?_⟩
    ext
    · exact ha
    · exact hb

private noncomputable def conjClassesProdEquiv
    {A : Type u} {B : Type v} [Group A] [Group B] :
    ConjClasses (A × B) ≃ ConjClasses A × ConjClasses B :=
  (Quotient.congrRight (fun x y => isConj_prod_iff x y)).trans
    (Setoid.prodQuotientEquiv (IsConj.setoid A) (IsConj.setoid B)).symm


private noncomputable def extProdClassFunction
    {A : Type u} {B : Type v} [Group A] [Group B]
    (chi : Theory.Character.ConjClassFunction A)
    (psi : Theory.Character.ConjClassFunction B) :
    Theory.Character.ConjClassFunction (A × B) := fun c =>
  chi (conjClassesProdEquiv c).1 * psi (conjClassesProdEquiv c).2

private theorem extProdClassFunction_mk
    {A : Type u} {B : Type v} [Group A] [Group B]
    (chi : Theory.Character.ConjClassFunction A)
    (psi : Theory.Character.ConjClassFunction B)
    (a : A) (b : B) :
    extProdClassFunction chi psi (ConjClasses.mk (a, b)) =
      chi (ConjClasses.mk a) * psi (ConjClasses.mk b) := by
  rfl

private noncomputable def extTprodRep
    {A : Type u} {B : Type v} [Group A] [Group B]
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ A V) (sigma : Representation ℂ B W) :
    Representation ℂ (A × B) (V ⊗[ℂ] W) :=
  Representation.tprod
    (rho.comp (MonoidHom.fst A B))
    (sigma.comp (MonoidHom.snd A B))

private theorem extTprodRep_character
    {A : Type u} {B : Type v} [Group A] [Group B]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ A V) (sigma : Representation ℂ B W)
    (a : A) (b : B) :
    (extTprodRep rho sigma).character (a, b) =
      rho.character a * sigma.character b := by
  change (Representation.tprod
    (rho.comp (MonoidHom.fst A B))
    (sigma.comp (MonoidHom.snd A B))).character (a, b) = _
  rw [Representation.char_tensor]
  rfl

private theorem extProdClassFunction_characterClassFunction
    {A : Type u} {B : Type v} [Group A] [Group B]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ A V) (sigma : Representation ℂ B W) :
    extProdClassFunction
        ((Theory.Character.characterClassFunction rho))
        (Theory.Character.characterClassFunction sigma) =
      Theory.Character.characterClassFunction (extTprodRep rho sigma) := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨⟨a, b⟩, rfl⟩
  change rho.character a * sigma.character b =
    (extTprodRep rho sigma).character (a, b)
  exact (extTprodRep_character rho sigma a b).symm

private theorem extProdClassFunction_inner
    {A : Type u} {B : Type v} [Group A] [Finite A] [Group B] [Finite B]
    (chi chi' : Theory.Character.ConjClassFunction A)
    (psi psi' : Theory.Character.ConjClassFunction B) :
    Theory.Character.classFunctionInner
        (extProdClassFunction chi psi) (extProdClassFunction chi' psi') =
      Theory.Character.classFunctionInner chi chi' *
        Theory.Character.classFunctionInner psi psi' := by
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  have hgoal :
      (Nat.card (A × B) : ℂ)⁻¹ *
          ∑ x : A × B,
            extProdClassFunction chi psi (ConjClasses.mk x) *
              star (extProdClassFunction chi' psi' (ConjClasses.mk x)) =
        ((Nat.card A : ℂ)⁻¹ *
            ∑ a : A, chi (ConjClasses.mk a) * star (chi' (ConjClasses.mk a))) *
          ((Nat.card B : ℂ)⁻¹ *
            ∑ b : B, psi (ConjClasses.mk b) * star (psi' (ConjClasses.mk b))) := by
    rw [Fintype.sum_prod_type]
    simp_rw [extProdClassFunction_mk, star_mul]
    have hterm (a : A) (b : B) :
        chi (ConjClasses.mk a) * psi (ConjClasses.mk b) *
            (star (psi' (ConjClasses.mk b)) * star (chi' (ConjClasses.mk a))) =
          (chi (ConjClasses.mk a) * star (chi' (ConjClasses.mk a))) *
            (psi (ConjClasses.mk b) * star (psi' (ConjClasses.mk b))) := by
      ring
    simp_rw [hterm]
    rw [← Fintype.sum_mul_sum]
    norm_num [Nat.card_prod]
    ring
  have huniv :
      @Finset.univ (A × B) (Fintype.ofFinite (A × B)) =
        @Finset.univ (A × B) (inferInstance : Fintype (A × B)) := by
    ext x
    simp
  simp only [Theory.Character.classFunctionInner]
  rw [huniv]
  exact hgoal

private theorem completeFamily_card_eq_conjClasses
    {A I : Type*} [Group A] [Finite A] [Fintype I]
    (chi : I → Theory.Character.ConjClassFunction A)
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi) :
    Fintype.card I = Nat.card (ConjClasses A) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  rcases Theory.Character.completeFamily_form_basis hchi with ⟨b, _hb⟩
  calc
    Fintype.card I = Module.finrank ℂ (Theory.Character.ConjClassFunction A) :=
      (Module.finrank_eq_card_basis b).symm
    _ = Fintype.card (ConjClasses A) := by
      simp [Theory.Character.ConjClassFunction]
    _ = Nat.card (ConjClasses A) := by rw [Nat.card_eq_fintype_card]

/-- A duplicate-free finite set containing every irreducible character has
cardinality equal to the number of conjugacy classes. -/
private theorem huppert_XI_6_complete_irreducible_finset_card_eq_conjClasses
    {Q : Type u} [Group Q] [Finite Q]
    (K : Finset (Section1.ClassFunction Q))
    (hKirr : ∀ chi : K,
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction Q))
    (hKcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ K) :
    K.card = Nat.card (ConjClasses Q) := by
  classical
  let phi : K → Theory.Character.ConjClassFunction Q := fun chi =>
    Section1.toConjClassFunction (chi : Section1.ClassFunction Q)
      (Section1.isCharacter_isClassFunction (chi : Section1.ClassFunction Q)
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup (hKirr chi)))
  have hphiIrr : ∀ chi,
      Theory.Character.IsIrreducibleConjCharacter (phi chi) := by
    intro chi
    exact huppert_XI_6_toConjClassFunction_irreducible (hKirr chi)
  have hphiInj : Function.Injective phi := by
    intro chi psi hEq
    apply Subtype.ext
    ext g
    have hval := congrFun hEq (ConjClasses.mk g)
    simpa [phi, Section1.toConjClassFunction_apply] using hval
  have hphiComplete : ∀ theta : Theory.Character.ConjClassFunction Q,
      Theory.Character.IsIrreducibleConjCharacter theta →
        ∃ chi, phi chi = theta := by
    intro theta htheta
    let theta' : Section1.ClassFunction Q :=
      Section1.ofConjClassFunction theta
    have htheta'Irr :
        Section1.IsIrreducibleCharacterOnGroup theta' :=
      huppert_XI_6_ofConjClassFunction_irreducibleOnGroup htheta
    let chi : K := ⟨theta', hKcomplete theta' htheta'Irr⟩
    refine ⟨chi, ?_⟩
    simpa [phi, chi, theta'] using
      Section1.toConjClassFunction_ofConjClassFunction theta
  have hfamily :
      Theory.Character.IsCompleteIrreducibleCharacterFamily phi :=
    ⟨hphiIrr, hphiComplete, hphiInj⟩
  simpa [Nat.card_eq_fintype_card] using
    completeFamily_card_eq_conjClasses phi hfamily

/-- Fourier expansion against a duplicate-free finite set containing every
irreducible character. -/
private theorem huppert_XI_6_complete_irreducible_finset_apply_eq_sum_scalarProduct
    {Q : Type u} [Group Q] [Finite Q]
    (K : Finset (Section1.ClassFunction Q))
    (hKirr : ∀ chi : K,
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction Q))
    (hKcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ K)
    (phi : Section1.ClassFunction Q)
    (hphi : Section1.IsClassFunction phi)
    (g : Q) :
    phi g = ∑ chi : K,
      Section1.scalarProduct Q phi (chi : Section1.ClassFunction Q) *
        (chi : Section1.ClassFunction Q) g := by
  classical
  let family : K → Theory.Character.ConjClassFunction Q := fun chi =>
    Section1.toConjClassFunction (chi : Section1.ClassFunction Q)
      (Section1.isCharacter_isClassFunction (chi : Section1.ClassFunction Q)
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup (hKirr chi)))
  have hfamilyIrr : ∀ chi,
      Theory.Character.IsIrreducibleConjCharacter (family chi) := by
    intro chi
    exact huppert_XI_6_toConjClassFunction_irreducible (hKirr chi)
  have hfamilyInj : Function.Injective family := by
    intro chi psi hEq
    apply Subtype.ext
    ext x
    have hval := congrFun hEq (ConjClasses.mk x)
    simpa [family, Section1.toConjClassFunction_apply] using hval
  have hfamilyComplete : ∀ theta : Theory.Character.ConjClassFunction Q,
      Theory.Character.IsIrreducibleConjCharacter theta →
        ∃ chi, family chi = theta := by
    intro theta htheta
    let theta' : Section1.ClassFunction Q :=
      Section1.ofConjClassFunction theta
    have htheta'Irr :
        Section1.IsIrreducibleCharacterOnGroup theta' :=
      huppert_XI_6_ofConjClassFunction_irreducibleOnGroup htheta
    let chi : K := ⟨theta', hKcomplete theta' htheta'Irr⟩
    refine ⟨chi, ?_⟩
    simpa [family, chi, theta'] using
      Section1.toConjClassFunction_ofConjClassFunction theta
  have hcomplete :
      Theory.Character.IsCompleteIrreducibleCharacterFamily family :=
    ⟨hfamilyIrr, hfamilyComplete, hfamilyInj⟩
  have hexpand := Theory.Character.completeFamily_apply_eq_sum_inner hcomplete
    (Section1.toConjClassFunction phi hphi) (ConjClasses.mk g)
  simpa [family, Section1.toConjClassFunction_apply,
    Section1.classFunctionInner_toConjClassFunction] using hexpand
/-- Two disjoint complete irreducible subfamilies partition the conjugacy
classes numerically. -/
private theorem huppert_XI_6_disjoint_irreducible_finsets_card_eq_conjClasses
    {Q : Type u} [Group Q] [Finite Q]
    (Y Z : Finset (Section1.ClassFunction Q))
    (hdisjoint : Disjoint Y Z)
    (hYirr : ∀ chi : Y,
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction Q))
    (hZirr : ∀ chi : Z,
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction Q))
    (hcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi →
        chi ∈ Y ∨ chi ∈ Z) :
    Y.card + Z.card = Nat.card (ConjClasses Q) := by
  have hunionIrr : ∀ chi : ↥(Y ∪ Z),
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction Q) := by
    intro chi
    rcases Finset.mem_union.mp chi.property with hchi | hchi
    · exact hYirr ⟨chi, hchi⟩
    · exact hZirr ⟨chi, hchi⟩
  have hunionComplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ Y ∪ Z := by
    intro chi hchi
    exact Finset.mem_union.mpr (hcomplete chi hchi)
  have hcard :=
    huppert_XI_6_complete_irreducible_finset_card_eq_conjClasses
      (Y ∪ Z) hunionIrr hunionComplete
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  exact hcard

private theorem extProdClassFunction_irreducible
    {A : Type u} {B : Type v} [Group A] [Finite A] [Group B] [Finite B]
    (chi : Theory.Character.ConjClassFunction A)
    (psi : Theory.Character.ConjClassFunction B)
    (hchi : Theory.Character.IsIrreducibleConjCharacter chi)
    (hpsi : Theory.Character.IsIrreducibleConjCharacter psi) :
    Theory.Character.IsIrreducibleConjCharacter (extProdClassFunction chi psi) := by
  rcases Section1.representation_irreducibleCharacter_witness_irreducible
    chi hchi with ⟨n, rho, hchiEq, hrho⟩
  rcases Section1.representation_irreducibleCharacter_witness_irreducible
    psi hpsi with ⟨m, sigma, hpsiEq, hsigma⟩
  rw [hchiEq, hpsiEq, extProdClassFunction_characterClassFunction]
  exact Theory.Character.isIrreducibleCharacter_characterClassFunction
    (extTprodRep rho sigma) (prod_tprod_irreducible rho sigma hrho hsigma)

private theorem extProdClassFunction_completeFamily
    {A : Type u} {B : Type v} [Group A] [Finite A] [Group B] [Finite B]
    {I J : Type*} [Fintype I] [Fintype J]
    (chi : I → Theory.Character.ConjClassFunction A)
    (psi : J → Theory.Character.ConjClassFunction B)
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi)
    (hpsi : Theory.Character.IsCompleteIrreducibleCharacterFamily psi) :
    Theory.Character.IsCompleteIrreducibleCharacterFamily
      (fun ij : I × J => extProdClassFunction (chi ij.1) (psi ij.2)) := by
  classical
  let ext : I × J → Theory.Character.ConjClassFunction (A × B) := fun ij =>
    extProdClassFunction (chi ij.1) (psi ij.2)
  have hirr : ∀ ij, Theory.Character.IsIrreducibleConjCharacter (ext ij) := by
    rintro ⟨i, j⟩
    exact extProdClassFunction_irreducible (chi i) (psi j)
      (hchi.1 i) (hpsi.1 j)
  have hinj : Function.Injective ext := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ heq
    have hinner :
        Theory.Character.classFunctionInner (ext (i, j)) (ext (i', j')) = 1 := by
      rw [heq]
      exact (hirr (i', j')).2
    rw [extProdClassFunction_inner,
      Section1.representation_completeFamily_orthonormal hchi,
      Section1.representation_completeFamily_orthonormal hpsi] at hinner
    by_cases hi : i = i'
    · by_cases hj : j = j'
      · exact Prod.ext hi hj
      · simp [hi, hj] at hinner
    · simp [hi] at hinner
  obtain ⟨K, hKFintype, theta, htheta, hKcard⟩ :=
    Theory.Character.card_irreducible_characters_eq_card_conjClasses
      (G := A × B)
  let : Fintype K := hKFintype
  let f : I × J → K := fun ij =>
    Classical.choose (htheta.2.1 (ext ij) (hirr ij))
  have hf : ∀ ij, theta (f ij) = ext ij := fun ij =>
    Classical.choose_spec (htheta.2.1 (ext ij) (hirr ij))
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply hinj
    rw [← hf x, ← hf y, hxy]
  have hdomainCard : Fintype.card (I × J) = Fintype.card K := by
    rw [Fintype.card_prod,
      completeFamily_card_eq_conjClasses chi hchi,
      completeFamily_card_eq_conjClasses psi hpsi]
    calc
      Nat.card (ConjClasses A) * Nat.card (ConjClasses B) =
          Nat.card (ConjClasses A × ConjClasses B) := by
        rw [Nat.card_prod]
      _ = Nat.card (ConjClasses (A × B)) :=
        (Nat.card_congr (conjClassesProdEquiv (A := A) (B := B))).symm
      _ = Fintype.card K := hKcard.symm
  have hfsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, hdomainCard⟩).2
  refine ⟨hirr, ?_, hinj⟩
  intro phi hphi
  obtain ⟨k, hk⟩ := htheta.2.1 phi hphi
  obtain ⟨ij, hij⟩ := hfsurj k
  refine ⟨ij, ?_⟩
  rw [← hk, ← hij, hf]


private theorem irreducibleCharacter_eq_extProdClassFunction
    {A : Type u} {B : Type v} [Group A] [Finite A] [Group B] [Finite B]
    (phi : Theory.Character.ConjClassFunction (A × B))
    (hphi : Theory.Character.IsIrreducibleConjCharacter phi) :
    ∃ chi : Theory.Character.ConjClassFunction A,
      ∃ psi : Theory.Character.ConjClassFunction B,
        Theory.Character.IsIrreducibleConjCharacter chi ∧
          Theory.Character.IsIrreducibleConjCharacter psi ∧
          phi = extProdClassFunction chi psi := by
  classical
  obtain ⟨I, hIFintype, chi, hchi, _hchiSum⟩ :=
    Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := A)
  obtain ⟨J, hJFintype, psi, hpsi, _hpsiSum⟩ :=
    Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := B)
  let : Fintype I := hIFintype
  let : Fintype J := hJFintype
  have hprod := extProdClassFunction_completeFamily chi psi hchi hpsi
  obtain ⟨ij, hij⟩ := hprod.2.1 phi hphi
  exact ⟨chi ij.1, psi ij.2, hchi.1 ij.1, hpsi.1 ij.2, hij.symm⟩


/-- Pointwise outer product in the elementwise class-function model. -/
private noncomputable def extProdSection1ClassFunction
    {A : Type u} {B : Type v} [Group A] [Group B]
    (chi : Section1.ClassFunction A) (psi : Section1.ClassFunction B) :
    Section1.ClassFunction (A × B) := fun x => chi x.1 * psi x.2

private theorem extProdSection1ClassFunction_degree
    {A : Type u} {B : Type v} [Group A] [Group B]
    (chi : Section1.ClassFunction A) (psi : Section1.ClassFunction B) :
    Section1.degree (extProdSection1ClassFunction chi psi) =
      Section1.degree chi * Section1.degree psi := by
  simp [extProdSection1ClassFunction, Section1.degree]

private theorem classFunctionLinearEquivOfMulEquiv_degree
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (chi : Section1.ClassFunction A) :
    Section1.degree
        (Section1.classFunctionLinearEquivOfMulEquiv e chi) =
      Section1.degree chi := by
  simp [Section1.classFunctionLinearEquivOfMulEquiv, Section1.degree]

private theorem extProdSection1ClassFunction_irreducible
    {A : Type u} {B : Type v} [Group A] [Finite A] [Group B] [Finite B]
    (chi : Section1.ClassFunction A) (psi : Section1.ClassFunction B)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hpsi : Section1.IsIrreducibleCharacterOnGroup psi) :
    Section1.IsIrreducibleCharacterOnGroup
      (extProdSection1ClassFunction chi psi) := by
  rcases hchi with ⟨n, rho, hrho, hchiEq⟩
  rcases hpsi with ⟨m, sigma, hsigma, hpsiEq⟩
  have hirr := Section1.isIrreducibleCharacterOnGroup_of_representation
    (extTprodRep rho sigma) (prod_tprod_irreducible rho sigma hrho hsigma)
  have heq : extProdSection1ClassFunction chi psi =
      (extTprodRep rho sigma).character := by
    ext x
    rcases x with ⟨a, b⟩
    rw [hchiEq, hpsiEq]
    exact (extTprodRep_character rho sigma a b).symm
  rw [heq]
  exact hirr

/-- Equality of transported external products of irreducible characters forces
equality of both component characters. -/
private theorem huppert_XI_6_3_transport_extProd_eq_components
    {A B Q : Type u}
    [Group A] [Finite A] [Group B] [Finite B] [Group Q]
    (e : A × B ≃* Q)
    (chi chi' : Section1.ClassFunction A)
    (psi psi' : Section1.ClassFunction B)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hchi' : Section1.IsIrreducibleCharacterOnGroup chi')
    (hpsi : Section1.IsIrreducibleCharacterOnGroup psi)
    (hpsi' : Section1.IsIrreducibleCharacterOnGroup psi')
    (hEq :
      Section1.classFunctionLinearEquivOfMulEquiv e
          (extProdSection1ClassFunction chi psi) =
        Section1.classFunctionLinearEquivOfMulEquiv e
          (extProdSection1ClassFunction chi' psi')) :
    chi = chi' ∧ psi = psi' := by
  let hchiClass : Section1.IsClassFunction chi :=
    Section1.isCharacter_isClassFunction chi
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi)
  let hchiClass' : Section1.IsClassFunction chi' :=
    Section1.isCharacter_isClassFunction chi'
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi')
  let hpsiClass : Section1.IsClassFunction psi :=
    Section1.isCharacter_isClassFunction psi
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hpsi)
  let hpsiClass' : Section1.IsClassFunction psi' :=
    Section1.isCharacter_isClassFunction psi'
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hpsi')
  let Chi := Section1.toConjClassFunction chi hchiClass
  let Chi' := Section1.toConjClassFunction chi' hchiClass'
  let Psi := Section1.toConjClassFunction psi hpsiClass
  let Psi' := Section1.toConjClassFunction psi' hpsiClass'
  have hprodPoint :
      extProdSection1ClassFunction chi psi =
        extProdSection1ClassFunction chi' psi' :=
    (Section1.classFunctionLinearEquivOfMulEquiv e).injective hEq
  have hprodR :
      extProdClassFunction Chi Psi = extProdClassFunction Chi' Psi' := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨⟨a, b⟩, rfl⟩
    have hval := congrFun hprodPoint (a, b)
    simpa [Chi, Chi', Psi, Psi', extProdClassFunction_mk,
      extProdSection1ClassFunction, Section1.toConjClassFunction_apply]
      using hval
  have hChiIrr : Theory.Character.IsIrreducibleConjCharacter Chi := by
    simpa [Chi, hchiClass] using
      huppert_XI_6_toConjClassFunction_irreducible hchi
  have hChiIrr' : Theory.Character.IsIrreducibleConjCharacter Chi' := by
    simpa [Chi', hchiClass'] using
      huppert_XI_6_toConjClassFunction_irreducible hchi'
  have hPsiIrr : Theory.Character.IsIrreducibleConjCharacter Psi := by
    simpa [Psi, hpsiClass] using
      huppert_XI_6_toConjClassFunction_irreducible hpsi
  have hPsiIrr' : Theory.Character.IsIrreducibleConjCharacter Psi' := by
    simpa [Psi', hpsiClass'] using
      huppert_XI_6_toConjClassFunction_irreducible hpsi'
  have hinner :
      Theory.Character.classFunctionInner
          (extProdClassFunction Chi Psi)
          (extProdClassFunction Chi' Psi') = 1 := by
    rw [hprodR]
    exact (extProdClassFunction_irreducible
      Chi' Psi' hChiIrr' hPsiIrr').2
  rw [extProdClassFunction_inner] at hinner
  have hchiEq : chi = chi' := by
    by_contra hne
    have hzero :
        Theory.Character.classFunctionInner Chi Chi' = 0 := by
      rw [Section1.classFunctionInner_toConjClassFunction]
      exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hchi hchi' hne
    rw [hzero] at hinner
    simp at hinner
  have hpsiEq : psi = psi' := by
    by_contra hne
    have hzero :
        Theory.Character.classFunctionInner Psi Psi' = 0 := by
      rw [Section1.classFunctionInner_toConjClassFunction]
      exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hpsi hpsi' hne
    rw [hzero] at hinner
    simp at hinner
  exact ⟨hchiEq, hpsiEq⟩
/-- Irreducible characters factor across an internal direct product. -/
private theorem irreducibleCharacter_eq_transport_extProd_of_internalDirectProduct
    {Q : Type u} [Group Q] [Finite Q]
    (A B : Subgroup Q)
    (hprod : Section2.IsInternalDirectProduct (⊤ : Subgroup Q) A B)
    (theta : Section1.ClassFunction Q)
    (htheta : Section1.IsIrreducibleCharacterOnGroup theta) :
    let e : A × B ≃* Q :=
      (Section3.internalDirectProductMulEquiv hprod).trans (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
    ∃ chi : Section1.ClassFunction A,
      ∃ psi : Section1.ClassFunction B,
        Section1.IsIrreducibleCharacterOnGroup chi ∧
          Section1.IsIrreducibleCharacterOnGroup psi ∧
          theta = Section1.classFunctionLinearEquivOfMulEquiv e
            (extProdSection1ClassFunction chi psi) := by
  classical
  let e : A × B ≃* Q :=
    (Section3.internalDirectProductMulEquiv hprod).trans (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  let thetaProd : Section1.ClassFunction (A × B) :=
    Section1.classFunctionLinearEquivOfMulEquiv e.symm theta
  have hthetaProd : Section1.IsIrreducibleCharacterOnGroup thetaProd :=
    Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e.symm htheta
  let hthetaClass : Section1.IsClassFunction thetaProd :=
    Section1.isCharacter_isClassFunction thetaProd
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hthetaProd)
  let Phi : Theory.Character.ConjClassFunction (A × B) :=
    Section1.toConjClassFunction thetaProd hthetaClass
  have hPhi : Theory.Character.IsIrreducibleConjCharacter Phi := by
    simpa [Phi, hthetaClass] using
      (huppert_XI_6_toConjClassFunction_irreducible hthetaProd)
  obtain ⟨chiR, psiR, hchiR, hpsiR, hfactor⟩ :=
    irreducibleCharacter_eq_extProdClassFunction Phi hPhi
  let chi : Section1.ClassFunction A := Section1.ofConjClassFunction chiR
  let psi : Section1.ClassFunction B := Section1.ofConjClassFunction psiR
  have hchi : Section1.IsIrreducibleCharacterOnGroup chi :=
    huppert_XI_6_ofConjClassFunction_irreducibleOnGroup hchiR
  have hpsi : Section1.IsIrreducibleCharacterOnGroup psi :=
    huppert_XI_6_ofConjClassFunction_irreducibleOnGroup hpsiR
  have hfactorPoint : thetaProd = extProdSection1ClassFunction chi psi := by
    ext x
    have hval := congrArg (fun f => f (ConjClasses.mk x)) hfactor
    have h_ext := extProdClassFunction_mk chiR psiR x.1 x.2
    simpa [Phi, hthetaClass, chi, psi, extProdSection1ClassFunction,
      Section1.ofConjClassFunction, Section1.toConjClassFunction_apply,
      Prod.mk.eta, h_ext] using hval
  refine ⟨chi, psi, hchi, hpsi, ?_⟩
  ext q
  calc
    theta q = thetaProd (e.symm q) := by
      simp [thetaProd, e, Section1.classFunctionLinearEquivOfMulEquiv]
    _ = extProdSection1ClassFunction chi psi (e.symm q) :=
      congrFun hfactorPoint (e.symm q)
    _ = Section1.classFunctionLinearEquivOfMulEquiv e
        (extProdSection1ClassFunction chi psi) q := rfl
/-- An irreducible character of a finite nilpotent group factors across its
`p`-core and `p`-prime core, with its natural degree factoring accordingly. -/
private theorem huppert_XI_6_3_nilpotent_character_factor
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ) (hp : Nat.Prime p) (hnil : Group.IsNilpotent Q)
    (theta : Section1.ClassFunction Q)
    (htheta : Section1.IsIrreducibleCharacterOnGroup theta) :
    ∃ e : (pCore p Q) × (pPrimeCore p Q) ≃* Q,
      ∃ chi : Section1.ClassFunction (pCore p Q),
        ∃ psi : Section1.ClassFunction (pPrimeCore p Q),
          ∃ a b : ℕ,
            Section1.IsIrreducibleCharacterOnGroup chi ∧
              Section1.IsIrreducibleCharacterOnGroup psi ∧
              theta = Section1.classFunctionLinearEquivOfMulEquiv e
                (extProdSection1ClassFunction chi psi) ∧
              0 < a ∧ 0 < b ∧
              Section1.degree chi = (a : ℂ) ∧
              Section1.degree psi = (b : ℂ) ∧
              a ∣ Nat.card (pCore p Q) ∧
              b ∣ Nat.card (pPrimeCore p Q) ∧
              Section1.degree theta = ((a * b : ℕ) : ℂ) := by
  let : Fact p.Prime := ⟨hp⟩
  let hprod :=
    nilpotent_internalDirectProduct_pCore_pPrimeCore p hp hnil
  let e : (pCore p Q) × (pPrimeCore p Q) ≃* Q :=
    (Section3.internalDirectProductMulEquiv hprod).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  obtain ⟨chi, psi, hchi, hpsi, hfactor⟩ :=
    irreducibleCharacter_eq_transport_extProd_of_internalDirectProduct
      (pCore p Q) (pPrimeCore p Q) hprod theta htheta
  obtain ⟨a, haPos, hachi, haDvd⟩ :=
    huppert_XI_6_positive_degree_nat hchi
  obtain ⟨b, hbPos, hbpsi, hbDvd⟩ :=
    huppert_XI_6_positive_degree_nat hpsi
  have hfactor' :
      theta = Section1.classFunctionLinearEquivOfMulEquiv e
        (extProdSection1ClassFunction chi psi) := by
    simpa [e, hprod] using hfactor
  have hthetaDegree :
      Section1.degree theta = ((a * b : ℕ) : ℂ) := by
    rw [hfactor', classFunctionLinearEquivOfMulEquiv_degree,
      extProdSection1ClassFunction_degree, hachi, hbpsi]
    norm_num
  exact ⟨e, chi, psi, a, b, hchi, hpsi, hfactor', haPos, hbPos,
    hachi, hbpsi, haDvd, hbDvd, hthetaDegree⟩

private theorem huppert_XI_6_3_pcore_factor_degree_gt_one
    {Q : Type u} [Group Q] [Finite Q]
    (p a b : ℕ) (hp : Nat.Prime p)
    (haPos : 0 < a)
    (hbDvd : b ∣ Nat.card (pPrimeCore p Q))
    (hpDvd : p ∣ a * b) :
    1 < a := by
  let : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p b :=
    Nat.Coprime.of_dvd_right hbDvd
      (pPrimeCore_coprime_card (G := Q) (p := p))
  have hpDvdA : p ∣ a := hcop.dvd_of_dvd_mul_right hpDvd
  have hpa : p ≤ a := Nat.le_of_dvd haPos hpDvdA
  exact lt_of_lt_of_le hp.one_lt hpa

private theorem huppert_XI_6_3_pcore_lower_degree_family
    {Q : Type u} [Group Q] [Finite Q]
    (p a : ℕ) (hp : Nat.Prime p)
    (chi : Section1.ClassFunction (pCore p Q))
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hachi : Section1.degree chi = (a : ℂ))
    (ha : 1 < a) :
    ∃ (ι : Type) (_ : Fintype ι)
      (rho : ι → Theory.Character.ConjClassFunction (pCore p Q))
      (degreeNat : ι → ℕ),
      Theory.Character.IsCompleteIrreducibleCharacterFamily rho ∧
        (∀ i, rho i (ConjClasses.mk (1 : pCore p Q)) =
          (degreeNat i : ℂ)) ∧
        a ^ 2 ≤
          ∑ i ∈ Finset.univ.filter (fun i => degreeNat i < a),
            degreeNat i ^ 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hcard⟩ :=
    (pCore_isPGroup (G := Q) (p := p)).exists_card_eq
  let hclass : Section1.IsClassFunction chi :=
    Section1.isCharacter_isClassFunction chi
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi)
  let Phi : Theory.Character.ConjClassFunction (pCore p Q) :=
    Section1.toConjClassFunction chi hclass
  have hPhi : Theory.Character.IsIrreducibleConjCharacter Phi := by
    simpa [Phi, hclass] using
      (huppert_XI_6_toConjClassFunction_irreducible hchi)
  obtain ⟨ι, hι, rho, i0, degreeNat, hrho, hi0, hvalue, hdvd⟩ :=
    huppert_XI_6_2_character_degree_lower_sum_dvd
      p n hp hcard Phi hPhi
  let : Fintype ι := hι
  have hi0Degree : degreeNat i0 = a := by
    have h := hvalue i0
    rw [hi0] at h
    have hPhiOne : Phi (ConjClasses.mk (1 : pCore p Q)) = (a : ℂ) := by
      change chi 1 = (a : ℂ)
      simpa [Section1.degree] using hachi
    rw [hPhiOne] at h
    exact_mod_cast h.symm
  have hlower :=
    huppert_XI_6_2_degree_sq_le_lower_sum
      rho hrho degreeNat hvalue i0 (by simpa [hi0Degree] using ha) hdvd
  refine ⟨ι, hι, rho, degreeNat, hrho, hvalue, ?_⟩
  simpa [hi0Degree] using hlower

private noncomputable def huppert_XI_6_3_lift_pcore_character
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (psi : Section1.ClassFunction (pPrimeCore p Q))
    (rho : Theory.Character.ConjClassFunction (pCore p Q)) :
    Section1.ClassFunction Q :=
  Section1.classFunctionLinearEquivOfMulEquiv e
    (extProdSection1ClassFunction
      (Section1.ofConjClassFunction rho) psi)

private theorem huppert_XI_6_3_lift_pcore_character_irreducible
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (psi : Section1.ClassFunction (pPrimeCore p Q))
    (hpsi : Section1.IsIrreducibleCharacterOnGroup psi)
    (rho : Theory.Character.ConjClassFunction (pCore p Q))
    (hrho : Theory.Character.IsIrreducibleConjCharacter rho) :
    Section1.IsIrreducibleCharacterOnGroup
      (huppert_XI_6_3_lift_pcore_character p e psi rho) := by
  apply Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
  exact extProdSection1ClassFunction_irreducible
    (Section1.ofConjClassFunction rho) psi
    (huppert_XI_6_ofConjClassFunction_irreducibleOnGroup hrho) hpsi

private theorem huppert_XI_6_3_lift_pcore_character_degree
    {Q : Type u} [Group Q] [Finite Q]
    (p c b : ℕ)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (psi : Section1.ClassFunction (pPrimeCore p Q))
    (hpsiDegree : Section1.degree psi = (b : ℂ))
    (rho : Theory.Character.ConjClassFunction (pCore p Q))
    (hrhoDegree : rho (ConjClasses.mk (1 : pCore p Q)) = (c : ℂ)) :
    Section1.degree (huppert_XI_6_3_lift_pcore_character p e psi rho) =
      ((c * b : ℕ) : ℂ) := by
  rw [huppert_XI_6_3_lift_pcore_character,
    classFunctionLinearEquivOfMulEquiv_degree,
    extProdSection1ClassFunction_degree]
  change rho (ConjClasses.mk (1 : pCore p Q)) * Section1.degree psi =
    ((c * b : ℕ) : ℂ)
  rw [hrhoDegree, hpsiDegree]
  norm_num

private theorem huppert_XI_6_3_lift_pcore_character_injective
    {Q : Type u} [Group Q] [Finite Q]
    (p b : ℕ) (hb : 0 < b)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (psi : Section1.ClassFunction (pPrimeCore p Q))
    (hpsiDegree : Section1.degree psi = (b : ℂ)) :
    Function.Injective
      (huppert_XI_6_3_lift_pcore_character p e psi) := by
  intro rho sigma hEq
  have hprod :
      extProdSection1ClassFunction (Section1.ofConjClassFunction rho) psi =
        extProdSection1ClassFunction (Section1.ofConjClassFunction sigma) psi := by
    apply (Section1.classFunctionLinearEquivOfMulEquiv e).injective
    exact hEq
  ext c
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  have hval := congrFun hprod (x, 1)
  change rho (ConjClasses.mk x) * psi 1 =
    sigma (ConjClasses.mk x) * psi 1 at hval
  have hpsiOne : psi 1 = (b : ℂ) := by
    simpa [Section1.degree] using hpsiDegree
  rw [hpsiOne] at hval
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hb)) hval

private theorem huppert_XI_6_3_completeFamily_degree_pos
    {P : Type*} [Group P] [Finite P]
    {ι : Type*} [Fintype ι]
    (rho : ι → Theory.Character.ConjClassFunction P)
    (degreeNat : ι → ℕ)
    (hrho : Theory.Character.IsCompleteIrreducibleCharacterFamily rho)
    (hvalue : ∀ i, rho i (ConjClasses.mk (1 : P)) = (degreeNat i : ℂ)) :
    ∀ i, 0 < degreeNat i := by
  intro i
  have hirr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction (rho i)) :=
    Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hrho.1 i)
  have hne :=
    Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction (rho i)) hirr
  have hdegree :
      Section1.degree (Section1.ofConjClassFunction (rho i)) =
        (degreeNat i : ℂ) := by
    change rho i (ConjClasses.mk (1 : P)) = (degreeNat i : ℂ)
    exact hvalue i
  have hcastNe : (degreeNat i : ℂ) ≠ 0 := by
    rw [← hdegree]
    exact hne
  exact Nat.pos_of_ne_zero (by exact_mod_cast hcastNe)

/-- Varying both the p-core character and the inflated linear character of the
complementary factor remains injective after transport to the nilpotent group. -/
private theorem huppert_XI_6_3_lift_pcore_linear_character_injective
    {Q : Type u} [Group Q] [Finite Q]
    {ι : Type*} [Fintype ι]
    (p : ℕ)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (rho : ι → Theory.Character.ConjClassFunction (pCore p Q))
    (degreeNat : ι → ℕ)
    (hrhoInj : Function.Injective rho)
    (hvalue : ∀ i, rho i (ConjClasses.mk (1 : pCore p Q)) =
      (degreeNat i : ℂ))
    (hdegreePos : ∀ i, 0 < degreeNat i) :
    Function.Injective
      (fun i : ι × (Abelianization (pPrimeCore p Q) →* ℂˣ) =>
        huppert_XI_6_3_lift_pcore_character p e
          (huppert_XI_6_3_abelianizationLinearCharacter i.2) (rho i.1)) := by
  intro i j hij
  have hprod :
      extProdSection1ClassFunction (Section1.ofConjClassFunction (rho i.1))
          (huppert_XI_6_3_abelianizationLinearCharacter i.2) =
        extProdSection1ClassFunction (Section1.ofConjClassFunction (rho j.1))
          (huppert_XI_6_3_abelianizationLinearCharacter j.2) := by
    apply (Section1.classFunctionLinearEquivOfMulEquiv e).injective
    exact hij
  have hfirst : i.1 = j.1 := by
    apply hrhoInj
    ext c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    have hval := congrFun hprod (x, 1)
    simpa [Section1.ofConjClassFunction, extProdSection1ClassFunction,
      huppert_XI_6_3_abelianizationLinearCharacter,
      Section1.characterInflationByHom] using hval

  have hlinear :
      huppert_XI_6_3_abelianizationLinearCharacter i.2 =
        huppert_XI_6_3_abelianizationLinearCharacter j.2 := by
    ext y
    have hval := congrFun hprod (1, y)
    change rho i.1 (ConjClasses.mk (1 : pCore p Q)) *
        huppert_XI_6_3_abelianizationLinearCharacter i.2 y =
      rho j.1 (ConjClasses.mk (1 : pCore p Q)) *
        huppert_XI_6_3_abelianizationLinearCharacter j.2 y at hval
    rw [hvalue i.1, hvalue j.1, hfirst] at hval
    exact mul_left_cancel₀
      (by exact_mod_cast (Nat.ne_of_gt (hdegreePos j.1))) hval
  have hsecond : i.2 = j.2 :=
    huppert_XI_6_3_abelianizationLinearCharacter_injective hlinear
  exact Prod.ext hfirst hsecond
private theorem huppert_XI_6_3_lifted_lower_family
    {Q : Type u} [Group Q] [Finite Q]
    {ι : Type} [Fintype ι]
    (p a b : ℕ) (hb : 0 < b)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (psi : Section1.ClassFunction (pPrimeCore p Q))
    (hpsi : Section1.IsIrreducibleCharacterOnGroup psi)
    (hpsiDegree : Section1.degree psi = (b : ℂ))
    (rho : ι → Theory.Character.ConjClassFunction (pCore p Q))
    (degreeNat : ι → ℕ)
    (hrho : Theory.Character.IsCompleteIrreducibleCharacterFamily rho)
    (hvalue : ∀ i, rho i (ConjClasses.mk (1 : pCore p Q)) =
      (degreeNat i : ℂ))
    (hlower : a ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => degreeNat i < a),
        degreeNat i ^ 2) :
    ∃ (I : Type) (_ : Fintype I)
      (theta : I → Section1.ClassFunction Q)
      (thetaDegree : I → ℕ),
      Function.Injective theta ∧
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (theta i)) ∧
        (∀ i, Section1.degree (theta i) = (thetaDegree i : ℂ)) ∧
        (∀ i, thetaDegree i < a * b) ∧
        (a * b) ^ 2 ≤ ∑ i, thetaDegree i ^ 2 := by
  classical
  let lower : Finset ι :=
    Finset.univ.filter (fun i => degreeNat i < a)
  let I := {i : ι // i ∈ lower}
  let theta : I → Section1.ClassFunction Q := fun i =>
    huppert_XI_6_3_lift_pcore_character p e psi (rho i.1)
  let thetaDegree : I → ℕ := fun i => degreeNat i.1 * b
  have hthetaInj : Function.Injective theta := by
    intro i j hij
    apply Subtype.ext
    apply hrho.2.2
    apply huppert_XI_6_3_lift_pcore_character_injective
      p b hb e psi hpsiDegree
    exact hij
  have hthetaIrr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (theta i) := by
    intro i
    exact huppert_XI_6_3_lift_pcore_character_irreducible
      p e psi hpsi (rho i.1) (hrho.1 i.1)
  have hthetaDegree : ∀ i,
      Section1.degree (theta i) = (thetaDegree i : ℂ) := by
    intro i
    exact huppert_XI_6_3_lift_pcore_character_degree
      p (degreeNat i.1) b e psi hpsiDegree (rho i.1) (hvalue i.1)
  have hthetaLt : ∀ i, thetaDegree i < a * b := by
    intro i
    have hi : degreeNat i.1 < a := by
      exact (Finset.mem_filter.mp i.2).2
    exact Nat.mul_lt_mul_of_pos_right hi hb
  have hsum :
      (∑ i : I, thetaDegree i ^ 2) =
        (∑ i ∈ lower, degreeNat i ^ 2) * b ^ 2 := by
    change (∑ i : I, (degreeNat i.1 * b) ^ 2) =
      (∑ i ∈ lower, degreeNat i ^ 2) * b ^ 2
    have hsubtype :
        (∑ i : I, (degreeNat i.1 * b) ^ 2) =
          ∑ i ∈ lower, (degreeNat i * b) ^ 2 := by
      symm
      exact Finset.sum_subtype (s := lower)
        (f := fun i => (degreeNat i * b) ^ 2) (by intro i; rfl)
    rw [hsubtype]
    simp_rw [mul_pow]
    rw [Finset.sum_mul]
  have hbound : (a * b) ^ 2 ≤
      (∑ i ∈ lower, degreeNat i ^ 2) * b ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right (b ^ 2) (by simpa [lower] using hlower)
  refine ⟨I, inferInstance, theta, thetaDegree, hthetaInj,
    hthetaIrr, hthetaDegree, hthetaLt, ?_⟩
  rw [hsum]
  exact hbound
/-- Pair the complete lower p-core family with every linear character of the
complementary factor.  The resulting injective family contributes the product
of the p-core lower square sum and the abelianization cardinal. -/
private theorem huppert_XI_6_3_linear_lifted_lower_family
    {Q : Type u} [Group Q] [Finite Q]
    {ι : Type} [Fintype ι]
    (p a : ℕ)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (rho : ι → Theory.Character.ConjClassFunction (pCore p Q))
    (degreeNat : ι → ℕ)
    (hrho : Theory.Character.IsCompleteIrreducibleCharacterFamily rho)
    (hvalue : ∀ i, rho i (ConjClasses.mk (1 : pCore p Q)) =
      (degreeNat i : ℂ)) :
    let lower : Finset ι :=
      Finset.univ.filter (fun i => degreeNat i < a)
    ∃ (I : Type) (_ : Fintype I)
      (theta : I → Section1.ClassFunction Q)
      (thetaDegree : I → ℕ),
      Function.Injective theta ∧
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (theta i)) ∧
        (∀ i, Section1.degree (theta i) = (thetaDegree i : ℂ)) ∧
        (∀ i, thetaDegree i < a) ∧
        (∑ i ∈ lower, degreeNat i ^ 2) *
            Nat.card (Abelianization (pPrimeCore p Q)) ≤
          ∑ i, thetaDegree i ^ 2 := by
  classical
  dsimp only
  let lower : Finset ι :=
    Finset.univ.filter (fun i => degreeNat i < a)
  let L := {i : ι // i ∈ lower}
  let Char := Abelianization (pPrimeCore p Q) →* ℂˣ
  let : Fintype Char := Fintype.ofFinite _
  let charEquiv : Char ≃ Fin (Fintype.card Char) := Fintype.equivFin Char
  let I := L × Fin (Fintype.card Char)
  let theta : I → Section1.ClassFunction Q := fun i =>
    huppert_XI_6_3_lift_pcore_character p e
      (huppert_XI_6_3_abelianizationLinearCharacter (charEquiv.symm i.2))
      (rho i.1.1)
  let thetaDegree : I → ℕ := fun i => degreeNat i.1.1
  have hdegreePosAll :=
    huppert_XI_6_3_completeFamily_degree_pos rho degreeNat hrho hvalue
  have hrhoInjL : Function.Injective (fun i : L => rho i.1) := by
    intro i j hij
    apply Subtype.ext
    exact hrho.2.2 hij
  have hpairInj :=
    huppert_XI_6_3_lift_pcore_linear_character_injective p e
      (fun i : L => rho i.1) (fun i : L => degreeNat i.1) hrhoInjL
      (fun i => hvalue i.1) (fun i => hdegreePosAll i.1)
  have hthetaInj : Function.Injective theta := by
    intro i j hij
    have hpair :
        (i.1, charEquiv.symm i.2) = (j.1, charEquiv.symm j.2) := by
      apply hpairInj
      simpa [theta, I] using hij
    have hfirst : i.1 = j.1 :=
      congrArg (fun x : L × Char => x.1) hpair
    have hsecond : charEquiv.symm i.2 = charEquiv.symm j.2 :=
      congrArg (fun x : L × Char => x.2) hpair
    exact Prod.ext hfirst (charEquiv.symm.injective hsecond)
  have hthetaIrr : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (theta i) := by
    intro i
    exact huppert_XI_6_3_lift_pcore_character_irreducible p e
      (huppert_XI_6_3_abelianizationLinearCharacter (charEquiv.symm i.2))
      (huppert_XI_6_3_abelianizationLinearCharacter_irreducible
        (charEquiv.symm i.2))
      (rho i.1.1) (hrho.1 i.1.1)
  have hthetaDegree : ∀ i,
      Section1.degree (theta i) = (thetaDegree i : ℂ) := by
    intro i
    have h := huppert_XI_6_3_lift_pcore_character_degree
      p (degreeNat i.1.1) 1 e
      (huppert_XI_6_3_abelianizationLinearCharacter (charEquiv.symm i.2))
      (by simpa using
        huppert_XI_6_3_abelianizationLinearCharacter_degree (charEquiv.symm i.2))
      (rho i.1.1) (hvalue i.1.1)
    simpa [theta, thetaDegree] using h
  have hthetaLt : ∀ i, thetaDegree i < a := by
    intro i
    exact (Finset.mem_filter.mp i.1.2).2
  have hcharCard :
      Fintype.card Char = Nat.card (Abelianization (pPrimeCore p Q)) := by
    rw [← Nat.card_eq_fintype_card]
    exact huppert_XI_6_3_abelianizationLinearCharacter_card
      (Q := pPrimeCore p Q)
  have hfinCard :
      Fintype.card (Fin (Fintype.card Char)) =
        Nat.card (Abelianization (pPrimeCore p Q)) := by
    simpa using hcharCard
  have hsubtype :
      (∑ i : L, degreeNat i.1 ^ 2) =
        ∑ i ∈ lower, degreeNat i ^ 2 := by
    symm
    exact Finset.sum_subtype (s := lower)
      (f := fun i => degreeNat i ^ 2) (by intro i; rfl)
  have hsum :
      (∑ i : I, thetaDegree i ^ 2) =
        (∑ i ∈ lower, degreeNat i ^ 2) *
          Nat.card (Abelianization (pPrimeCore p Q)) := by
    change (∑ i : L × Fin (Fintype.card Char), degreeNat i.1.1 ^ 2) = _
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hfinCard, ← Finset.mul_sum, hsubtype]
    ac_rfl
  refine ⟨I, inferInstance, theta, thetaDegree, hthetaInj, hthetaIrr,
    hthetaDegree, hthetaLt, ?_⟩
  rw [hsum]
private theorem huppert_XI_6_3_injective_family_bound_le_complete_lower_sum
    {Q : Type u} [Group Q] [Finite Q]
    {I : Type} [Fintype I]
    (K : Finset (Section1.ClassFunction Q))
    (hKcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ K)
    (degreeNat : Section1.ClassFunction Q → ℕ)
    (hdegree : ∀ chi : K,
      Section1.degree (chi : Section1.ClassFunction Q) =
        (degreeNat chi : ℂ))
    (B z : ℕ)
    (theta : I → Section1.ClassFunction Q)
    (thetaDegree : I → ℕ)
    (hthetaInj : Function.Injective theta)
    (hthetaIrr : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (theta i))
    (hthetaDegree : ∀ i,
      Section1.degree (theta i) = (thetaDegree i : ℂ))
    (hthetaLt : ∀ i, thetaDegree i < z)
    (hbound : B ≤ ∑ i, thetaDegree i ^ 2) :
    B ≤ ∑ chi ∈ K.filter (fun chi => degreeNat chi < z),
      degreeNat chi ^ 2 := by
  classical
  let S : Finset (Section1.ClassFunction Q) :=
    Finset.univ.image theta
  have hdegreeNat : ∀ i, degreeNat (theta i) = thetaDegree i := by
    intro i
    have hmem : theta i ∈ K := hKcomplete (theta i) (hthetaIrr i)
    have hcast : (degreeNat (theta i) : ℂ) = (thetaDegree i : ℂ) := by
      rw [← hdegree ⟨theta i, hmem⟩]
      exact hthetaDegree i
    exact_mod_cast hcast
  have hSsub :
      S ⊆ K.filter (fun chi => degreeNat chi < z) := by
    intro chi hchi
    rcases Finset.mem_image.mp hchi with ⟨i, _hi, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨hKcomplete (theta i) (hthetaIrr i),
        by rw [hdegreeNat i]; exact hthetaLt i⟩
  have hsumS :
      (∑ chi ∈ S, degreeNat chi ^ 2) =
        ∑ i, thetaDegree i ^ 2 := by
    dsimp [S]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [hdegreeNat i]
    · intro i _hi j _hj hij
      exact hthetaInj hij
  calc
    B ≤ ∑ i, thetaDegree i ^ 2 := hbound
    _ = ∑ chi ∈ S, degreeNat chi ^ 2 := hsumS.symm
    _ ≤ ∑ chi ∈ K.filter (fun chi => degreeNat chi < z),
        degreeNat chi ^ 2 := Finset.sum_le_sum_of_subset hSsub
/-- Pair the complete lower p-core family with all linear characters of the
complementary factor and inject the result into the complete lower-degree
family of the whole nilpotent group. -/
private theorem huppert_XI_6_3_linear_component_le_complete_lower_sum
    {Q : Type u} [Group Q] [Finite Q]
    {ι : Type} [Fintype ι]
    (p a : ℕ)
    (e : (pCore p Q) × (pPrimeCore p Q) ≃* Q)
    (rho : ι → Theory.Character.ConjClassFunction (pCore p Q))
    (rhoDegree : ι → ℕ)
    (hrho : Theory.Character.IsCompleteIrreducibleCharacterFamily rho)
    (hvalue : ∀ i, rho i (ConjClasses.mk (1 : pCore p Q)) =
      (rhoDegree i : ℂ))
    (hlower : a ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => rhoDegree i < a),
        rhoDegree i ^ 2)
    (K : Finset (Section1.ClassFunction Q))
    (hKcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ K)
    (degreeNat : Section1.ClassFunction Q → ℕ)
    (hdegree : ∀ chi : K,
      Section1.degree (chi : Section1.ClassFunction Q) =
        (degreeNat chi : ℂ)) :
    a ^ 2 * Nat.card (Abelianization (pPrimeCore p Q)) ≤
      ∑ chi ∈ K.filter (fun chi => degreeNat chi < a),
        degreeNat chi ^ 2 := by
  classical
  obtain ⟨I, hIFintype, theta, thetaDegree, hthetaInj,
      hthetaIrr, hthetaDegree, hthetaLt, hthetaBound⟩ :=
    huppert_XI_6_3_linear_lifted_lower_family
      p a e rho rhoDegree hrho hvalue
  let : Fintype I := hIFintype
  have hfamily :
      (∑ i ∈ Finset.univ.filter (fun i => rhoDegree i < a),
          rhoDegree i ^ 2) *
          Nat.card (Abelianization (pPrimeCore p Q)) ≤
        ∑ chi ∈ K.filter (fun chi => degreeNat chi < a),
          degreeNat chi ^ 2 :=
    huppert_XI_6_3_injective_family_bound_le_complete_lower_sum
      (I := I) K hKcomplete degreeNat hdegree
      ((∑ i ∈ Finset.univ.filter (fun i => rhoDegree i < a),
          rhoDegree i ^ 2) *
        Nat.card (Abelianization (pPrimeCore p Q)))
      a theta thetaDegree hthetaInj hthetaIrr hthetaDegree hthetaLt
      hthetaBound
  exact (Nat.mul_le_mul_right
    (Nat.card (Abelianization (pPrimeCore p Q))) hlower).trans hfamily

/-- Every linear character lies below any nonlinear degree, so the complete
lower-degree square sum contains at least the abelianization cardinal. -/
private theorem huppert_XI_6_3_abelianization_card_le_complete_lower_sum
    {Q : Type u} [Group Q] [Finite Q]
    (K : Finset (Section1.ClassFunction Q))
    (hKcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ K)
    (degreeNat : Section1.ClassFunction Q → ℕ)
    (hdegree : ∀ chi : K,
      Section1.degree (chi : Section1.ClassFunction Q) =
        (degreeNat chi : ℂ))
    (z : ℕ) (hz : 1 < z) :
    Nat.card (Abelianization Q) ≤
      ∑ chi ∈ K.filter (fun chi => degreeNat chi < z),
        degreeNat chi ^ 2 := by
  let Char := Abelianization Q →* ℂˣ
  let : Fintype Char := Fintype.ofFinite _
  let charEquiv : Char ≃ Fin (Fintype.card Char) := Fintype.equivFin Char
  let I := Fin (Fintype.card Char)
  let theta : I → Section1.ClassFunction Q := fun i =>
    huppert_XI_6_3_abelianizationLinearCharacter (charEquiv.symm i)
  let thetaDegree : I → ℕ := fun _ => 1
  have hthetaInj : Function.Injective theta := by
    intro i j hij
    apply charEquiv.symm.injective
    apply huppert_XI_6_3_abelianizationLinearCharacter_injective
    simpa [theta] using hij
  have hthetaIrr : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (theta i) := by
    intro i
    exact huppert_XI_6_3_abelianizationLinearCharacter_irreducible
      (charEquiv.symm i)
  have hthetaDegree : ∀ i,
      Section1.degree (theta i) = (thetaDegree i : ℂ) := by
    intro i
    simpa [theta, thetaDegree] using
      huppert_XI_6_3_abelianizationLinearCharacter_degree (charEquiv.symm i)
  have hthetaLt : ∀ i, thetaDegree i < z := by
    intro i
    simpa [thetaDegree] using hz
  have hcharCard : Fintype.card Char = Nat.card (Abelianization Q) := by
    rw [← Nat.card_eq_fintype_card]
    exact huppert_XI_6_3_abelianizationLinearCharacter_card (Q := Q)
  have hbound :
      Nat.card (Abelianization Q) ≤ ∑ i : I, thetaDegree i ^ 2 := by
    simp [I, thetaDegree, hcharCard]
  exact huppert_XI_6_3_injective_family_bound_le_complete_lower_sum
    (I := I) K hKcomplete degreeNat hdegree
    (Nat.card (Abelianization Q)) z theta thetaDegree
    hthetaInj hthetaIrr hthetaDegree hthetaLt hbound


/-- XI.6.3(b), linear-character contribution in the small-sum branch.  The
mixed-prime abelianization bound forces at least `2*d^2` nonprincipal degree
square contribution. -/
private theorem huppert_XI_6_3_mixed_prime_nonprincipal_linear_lower
    {D Q : Type u} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q] [Nontrivial Q]
    (hnil : Group.IsNilpotent Q)
    (hnotPrimePower : ¬ IsPrimePow (Nat.card Q))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ x : Q, d • x = x → x = 1)
    (hoddD : Odd (Nat.card D))
    (A : ℕ)
    (hAb : Nat.card (Abelianization Q) ≤ A + 1)
    (hsmall : A < 4 * Nat.card D ^ 2) :
    2 * Nat.card D ^ 2 ≤ A := by
  have hAbUpper :
      Nat.card (Abelianization Q) < 4 * Nat.card D ^ 2 + 1 := by
    omega
  have hlower :=
    huppert_XI_6_3_mixed_prime_abelianization_lower
      hnil hnotPrimePower hcop hfree hoddD hAbUpper
  have hbound :
      (Nat.card D + 1) * (2 * Nat.card D + 1) ≤ A + 1 :=
    hlower.trans hAb
  nlinarith


/-- A nonlinear irreducible character of a finite nilpotent group admits an
injectively indexed family of lower-degree irreducible characters whose
degree-square sum dominates the original degree square. -/
private theorem huppert_XI_6_3_nilpotent_lower_family
    {Q : Type u} [Group Q] [Finite Q]
    (hnil : Group.IsNilpotent Q)
    (theta : Section1.ClassFunction Q)
    (htheta : Section1.IsIrreducibleCharacterOnGroup theta)
    (z : ℕ) (hz : 1 < z)
    (hthetaDegree : Section1.degree theta = (z : ℂ)) :
    ∃ (I : Type) (_ : Fintype I)
      (lowerChar : I → Section1.ClassFunction Q)
      (lowerDegree : I → ℕ),
      Function.Injective lowerChar ∧
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (lowerChar i)) ∧
        (∀ i, Section1.degree (lowerChar i) = (lowerDegree i : ℂ)) ∧
        (∀ i, lowerDegree i < z) ∧
        z ^ 2 ≤ ∑ i, lowerDegree i ^ 2 := by
  classical
  obtain ⟨p, hp, hpDvdZ⟩ := Nat.exists_prime_and_dvd hz.ne'
  obtain ⟨e, chi, psi, a, b, hchi, hpsi, _hfactor,
      haPos, hbPos, hachi, hbpsi, _haDvd, hbDvd, hthetaDegreeAB⟩ :=
    huppert_XI_6_3_nilpotent_character_factor p hp hnil theta htheta
  have hab : a * b = z := by
    have hcast : ((a * b : ℕ) : ℂ) = (z : ℂ) := by
      rw [← hthetaDegreeAB, hthetaDegree]
    exact_mod_cast hcast
  have ha : 1 < a := by
    apply huppert_XI_6_3_pcore_factor_degree_gt_one p a b hp haPos hbDvd
    rw [hab]
    exact hpDvdZ
  obtain ⟨ι, hι, rho, rhoDegree, hrho, hvalue, hlower⟩ :=
    huppert_XI_6_3_pcore_lower_degree_family
      p a hp chi hchi hachi ha
  let : Fintype ι := hι
  obtain ⟨I, hIFintype, lowerChar, lowerDegree, hlowerInj,
      hlowerIrr, hlowerDegree, hlowerLt, hlowerSq⟩ :=
    huppert_XI_6_3_lifted_lower_family
      p a b hbPos e psi hpsi hbpsi rho rhoDegree hrho hvalue hlower
  refine ⟨I, hIFintype, lowerChar, lowerDegree, hlowerInj,
    hlowerIrr, hlowerDegree, ?_, ?_⟩
  · intro i
    simpa [hab] using hlowerLt i
  · simpa [hab] using hlowerSq
/-- If both direct-product factors of an irreducible character are nonlinear,
three pairwise disjoint lower external-product families each contribute at
least the square of the original product degree. -/
private theorem huppert_XI_6_3_two_nonlinear_lower_family
    {A B Q : Type u}
    [Group A] [Finite A] [Group B] [Finite B] [Group Q] [Finite Q]
    {I J : Type} [Fintype I] [Fintype J]
    (e : A × B ≃* Q)
    (chi : Section1.ClassFunction A)
    (psi : Section1.ClassFunction B)
    (a b : ℕ)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hpsi : Section1.IsIrreducibleCharacterOnGroup psi)
    (hchiDegree : Section1.degree chi = (a : ℂ))
    (hpsiDegree : Section1.degree psi = (b : ℂ))
    (ha : 1 < a) (hb : 1 < b)
    (lowerA : I → Section1.ClassFunction A)
    (degreeA : I → ℕ)
    (hlowerAInj : Function.Injective lowerA)
    (hlowerAIrr : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (lowerA i))
    (hlowerADegree : ∀ i,
      Section1.degree (lowerA i) = (degreeA i : ℂ))
    (hlowerALt : ∀ i, degreeA i < a)
    (hlowerASq : a ^ 2 ≤ ∑ i, degreeA i ^ 2)
    (lowerB : J → Section1.ClassFunction B)
    (degreeB : J → ℕ)
    (hlowerBInj : Function.Injective lowerB)
    (hlowerBIrr : ∀ j,
      Section1.IsIrreducibleCharacterOnGroup (lowerB j))
    (hlowerBDegree : ∀ j,
      Section1.degree (lowerB j) = (degreeB j : ℂ))
    (hlowerBLt : ∀ j, degreeB j < b)
    (hlowerBSq : b ^ 2 ≤ ∑ j, degreeB j ^ 2) :
    ∃ (T : Type) (_ : Fintype T)
      (lowerChar : T → Section1.ClassFunction Q)
      (lowerDegree : T → ℕ),
      Function.Injective lowerChar ∧
        (∀ t, Section1.IsIrreducibleCharacterOnGroup (lowerChar t)) ∧
        (∀ t, Section1.degree (lowerChar t) = (lowerDegree t : ℂ)) ∧
        (∀ t, lowerDegree t < a * b) ∧
        3 * (a * b) ^ 2 ≤ ∑ t, lowerDegree t ^ 2 := by
  classical
  have hlowerAPos : ∀ i, 0 < degreeA i := by
    intro i
    obtain ⟨c, hc, hcDegree, _hcDvd⟩ :=
      huppert_XI_6_positive_degree_nat (hlowerAIrr i)
    have hcast : (degreeA i : ℂ) = (c : ℂ) := by
      rw [← hlowerADegree i, hcDegree]
    have heq : degreeA i = c := by exact_mod_cast hcast
    simpa [heq] using hc
  have hlowerBPos : ∀ j, 0 < degreeB j := by
    intro j
    obtain ⟨c, hc, hcDegree, _hcDvd⟩ :=
      huppert_XI_6_positive_degree_nat (hlowerBIrr j)
    have hcast : (degreeB j : ℂ) = (c : ℂ) := by
      rw [← hlowerBDegree j, hcDegree]
    have heq : degreeB j = c := by exact_mod_cast hcast
    simpa [heq] using hc
  have hlowerANe : ∀ i, lowerA i ≠ chi := by
    intro i hEq
    have hcast := congrArg Section1.degree hEq
    rw [hlowerADegree i, hchiDegree] at hcast
    have heq : degreeA i = a := by exact_mod_cast hcast
    exact (Nat.ne_of_lt (hlowerALt i)) heq
  have hlowerBNe : ∀ j, lowerB j ≠ psi := by
    intro j hEq
    have hcast := congrArg Section1.degree hEq
    rw [hlowerBDegree j, hpsiDegree] at hcast
    have heq : degreeB j = b := by exact_mod_cast hcast
    exact (Nat.ne_of_lt (hlowerBLt j)) heq
  let T := I ⊕ (J ⊕ (I × J))
  let lowerChar : T → Section1.ClassFunction Q
    | Sum.inl i =>
        Section1.classFunctionLinearEquivOfMulEquiv e
          (extProdSection1ClassFunction (lowerA i) psi)
    | Sum.inr (Sum.inl j) =>
        Section1.classFunctionLinearEquivOfMulEquiv e
          (extProdSection1ClassFunction chi (lowerB j))
    | Sum.inr (Sum.inr ij) =>
        Section1.classFunctionLinearEquivOfMulEquiv e
          (extProdSection1ClassFunction (lowerA ij.1) (lowerB ij.2))
  let lowerDegree : T → ℕ
    | Sum.inl i => degreeA i * b
    | Sum.inr (Sum.inl j) => a * degreeB j
    | Sum.inr (Sum.inr ij) => degreeA ij.1 * degreeB ij.2
  have hlowerInj : Function.Injective lowerChar := by
    rintro (i | (j | ij)) (i' | (j' | ij')) hEq
    · obtain ⟨hfirst, _hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          (lowerA i) (lowerA i') psi psi
          (hlowerAIrr i) (hlowerAIrr i') hpsi hpsi
          (by simpa [lowerChar] using hEq)
      have hii : i = i' := hlowerAInj hfirst
      subst i'
      rfl
    · obtain ⟨hfirst, _hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          (lowerA i) chi psi (lowerB j')
          (hlowerAIrr i) hchi hpsi (hlowerBIrr j')
          (by simpa [lowerChar] using hEq)
      exfalso
      exact (hlowerANe i) hfirst
    · obtain ⟨_hfirst, hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          (lowerA i) (lowerA ij'.1) psi (lowerB ij'.2)
          (hlowerAIrr i) (hlowerAIrr ij'.1) hpsi (hlowerBIrr ij'.2)
          (by simpa [lowerChar] using hEq)
      exfalso
      exact (hlowerBNe ij'.2) hsecond.symm
    · obtain ⟨hfirst, _hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          chi (lowerA i') (lowerB j) psi
          hchi (hlowerAIrr i') (hlowerBIrr j) hpsi
          (by simpa [lowerChar] using hEq)
      exfalso
      exact (hlowerANe i') hfirst.symm
    · obtain ⟨_hfirst, hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          chi chi (lowerB j) (lowerB j')
          hchi hchi (hlowerBIrr j) (hlowerBIrr j')
          (by simpa [lowerChar] using hEq)
      have hjj : j = j' := hlowerBInj hsecond
      subst j'
      rfl
    · obtain ⟨hfirst, _hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          chi (lowerA ij'.1) (lowerB j) (lowerB ij'.2)
          hchi (hlowerAIrr ij'.1) (hlowerBIrr j) (hlowerBIrr ij'.2)
          (by simpa [lowerChar] using hEq)
      exfalso
      exact (hlowerANe ij'.1) hfirst.symm
    · obtain ⟨_hfirst, hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          (lowerA ij.1) (lowerA i') (lowerB ij.2) psi
          (hlowerAIrr ij.1) (hlowerAIrr i') (hlowerBIrr ij.2) hpsi
          (by simpa [lowerChar] using hEq)
      exfalso
      exact (hlowerBNe ij.2) hsecond
    · obtain ⟨hfirst, _hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          (lowerA ij.1) chi (lowerB ij.2) (lowerB j')
          (hlowerAIrr ij.1) hchi (hlowerBIrr ij.2) (hlowerBIrr j')
          (by simpa [lowerChar] using hEq)
      exfalso
      exact (hlowerANe ij.1) hfirst
    · obtain ⟨hfirst, hsecond⟩ :=
        huppert_XI_6_3_transport_extProd_eq_components e
          (lowerA ij.1) (lowerA ij'.1) (lowerB ij.2) (lowerB ij'.2)
          (hlowerAIrr ij.1) (hlowerAIrr ij'.1)
          (hlowerBIrr ij.2) (hlowerBIrr ij'.2)
          (by simpa [lowerChar] using hEq)
      have hfirstIdx : ij.1 = ij'.1 := hlowerAInj hfirst
      have hsecondIdx : ij.2 = ij'.2 := hlowerBInj hsecond
      have hij : ij = ij' := Prod.ext hfirstIdx hsecondIdx
      subst ij'
      rfl
  have hlowerIrr : ∀ t,
      Section1.IsIrreducibleCharacterOnGroup (lowerChar t) := by
    rintro (i | (j | ij))
    · apply Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      exact extProdSection1ClassFunction_irreducible
        (lowerA i) psi (hlowerAIrr i) hpsi
    · apply Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      exact extProdSection1ClassFunction_irreducible
        chi (lowerB j) hchi (hlowerBIrr j)
    · apply Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      exact extProdSection1ClassFunction_irreducible
        (lowerA ij.1) (lowerB ij.2)
        (hlowerAIrr ij.1) (hlowerBIrr ij.2)
  have hlowerDegree : ∀ t,
      Section1.degree (lowerChar t) = (lowerDegree t : ℂ) := by
    rintro (i | (j | ij))
    · rw [classFunctionLinearEquivOfMulEquiv_degree,
        extProdSection1ClassFunction_degree, hlowerADegree i, hpsiDegree]
      norm_num [lowerDegree]
    · rw [classFunctionLinearEquivOfMulEquiv_degree,
        extProdSection1ClassFunction_degree, hchiDegree, hlowerBDegree j]
      norm_num [lowerDegree]
    · rw [classFunctionLinearEquivOfMulEquiv_degree,
        extProdSection1ClassFunction_degree,
        hlowerADegree ij.1, hlowerBDegree ij.2]
      norm_num [lowerDegree]
  have hlowerLt : ∀ t, lowerDegree t < a * b := by
    rintro (i | (j | ij))
    · exact Nat.mul_lt_mul_of_pos_right (hlowerALt i) (by omega)
    · exact Nat.mul_lt_mul_of_pos_left (hlowerBLt j) (by omega)
    · exact (Nat.mul_lt_mul_of_pos_right
        (hlowerALt ij.1) (hlowerBPos ij.2)).trans
          (Nat.mul_lt_mul_of_pos_left (hlowerBLt ij.2) (by omega))
  have hsumA :
      (∑ i : I, (degreeA i * b) ^ 2) =
        (∑ i : I, degreeA i ^ 2) * b ^ 2 := by
    simp_rw [mul_pow]
    rw [Finset.sum_mul]
  have hsumB :
      (∑ j : J, (a * degreeB j) ^ 2) =
        a ^ 2 * ∑ j : J, degreeB j ^ 2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  have hsumAB :
      (∑ ij : I × J, (degreeA ij.1 * degreeB ij.2) ^ 2) =
        (∑ i : I, degreeA i ^ 2) * ∑ j : J, degreeB j ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow]
    rw [← Fintype.sum_mul_sum]
  have hsum :
      (∑ t : T, lowerDegree t ^ 2) =
        (∑ i : I, degreeA i ^ 2) * b ^ 2 +
          (a ^ 2 * ∑ j : J, degreeB j ^ 2 +
            (∑ i : I, degreeA i ^ 2) *
              ∑ j : J, degreeB j ^ 2) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simpa [lowerDegree] using congrArg₂ (fun x y => x + y)
      hsumA (congrArg₂ (fun x y => x + y) hsumB hsumAB)
  have hfirst :
      (a * b) ^ 2 ≤ (∑ i : I, degreeA i ^ 2) * b ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right (b ^ 2) hlowerASq
  have hsecond :
      (a * b) ^ 2 ≤ a ^ 2 * ∑ j : J, degreeB j ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_left (a ^ 2) hlowerBSq
  have hthird :
      (a * b) ^ 2 ≤
        (∑ i : I, degreeA i ^ 2) * ∑ j : J, degreeB j ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul hlowerASq hlowerBSq
  refine ⟨T, inferInstance, lowerChar, lowerDegree, hlowerInj,
    hlowerIrr, hlowerDegree, hlowerLt, ?_⟩
  rw [hsum]
  have hthree :
      3 * (a * b) ^ 2 =
        (a * b) ^ 2 + ((a * b) ^ 2 + (a * b) ^ 2) := by ring
  rw [hthree]
  exact Nat.add_le_add hfirst (Nat.add_le_add hsecond hthird)

/-- The degree/norm contribution of one induced irreducible kernel character,
expressed over its ambient conjugation orbit. -/
private theorem huppert_XI_6_orbit_contribution
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} [K.Normal]
    {theta : ClassFunction K}
    (htheta : IsIrreducibleCharacterOnGroup theta) :
    ∃ dtheta dchi : ℕ,
      degree theta = (dtheta : Complex) ∧
      degree (inducedCF K theta) = (dchi : Complex) ∧
      (dchi : ℝ) ^ 2 / cfNormSq (inducedCF K theta) =
        (K.relIndex (⊤ : Subgroup L) : ℝ) *
          ∑ _o : conjugateOrbitIndex K theta, (dtheta : ℝ) ^ 2 := by
  classical
  rcases htheta with ⟨n, rho, hrho, rfl⟩
  refine ⟨n, K.relIndex (⊤ : Subgroup L) * n, ?_, ?_, ?_⟩
  · rw [degree_representation_character]
    simp
  · rw [degree_inducedClassFunction, degree_representation_character]
    simp [Subgroup.relIndex_top_right, Nat.cast_mul]
  · have hres :=
      proposition_1_5_d_rep_orbit_relIndex_canonical K rho hrho
    have hresOne := congrFun hres (1 : K)
    have huniv :
        @Finset.univ (conjugateOrbitIndex K rho.character)
            (Fintype.ofFinite _) =
          @Finset.univ (conjugateOrbitIndex K rho.character)
            (Quotient.fintype (conjugateOrbitSetoid K rho.character)) := by
      ext o
      simp
    rw [huniv] at hresOne
    have hnorm :
        scalarProduct L (inducedCF K rho.character)
          (inducedCF K rho.character) =
        (K.relIndex (inertiaSubgroup K rho.character) : Complex) :=
      proposition_1_5_b_rep_orbit_relIndex_canonical K rho hrho
    have hcomplex :
        ((((K.relIndex (⊤ : Subgroup L) * n : ℕ) : Complex) ^ 2) /
            (K.relIndex (inertiaSubgroup K rho.character) : Complex)) =
          (K.relIndex (⊤ : Subgroup L) : Complex) *
            ∑ o : conjugateOrbitIndex K rho.character,
              (n : Complex) ^ 2 := by
      calc
        ((((K.relIndex (⊤ : Subgroup L) * n : ℕ) : Complex) ^ 2) /
            (K.relIndex (inertiaSubgroup K rho.character) : Complex)) =
            (degree (inducedCF K rho.character) /
                scalarProduct L (inducedCF K rho.character)
                  (inducedCF K rho.character)) *
              degree (inducedCF K rho.character) := by
          rw [hnorm, degree_inducedClassFunction,
            degree_representation_character]
          simp [Subgroup.relIndex_top_right, Nat.cast_mul, pow_two]
          ring
        _ = (Subgroup.index K : Complex) *
            ∑ o : conjugateOrbitIndex K rho.character,
              degree (conjugateOrbitConj K rho.character o) *
                degree (conjugateOrbitConj K rho.character o) := by
          simpa [degree, subgroupRestriction] using hresOne
        _ = (K.relIndex (⊤ : Subgroup L) : Complex) *
            ∑ _o : conjugateOrbitIndex K rho.character,
              (n : Complex) ^ 2 := by
          rw [Subgroup.relIndex_top_right]
          congr 1
          apply Finset.sum_congr rfl
          intro o _ho
          have hdeg :
              degree (conjugateOrbitConj K rho.character o) =
                (n : Complex) := by
            refine Quotient.inductionOn o ?_
            intro g
            unfold degree conjugateOrbitConj
            dsimp [conjugateOnNormal]
            have hone :
                (⟨g * 1 * g⁻¹, by simp⟩ : K) = 1 := by
              ext
              simp
            rw [hone]
            simp
          rw [hdeg]
          ring
    have hcf :
        cfNormSq (inducedCF K rho.character) =
          (K.relIndex (inertiaSubgroup K rho.character) : ℝ) := by
      unfold cfNormSq
      rw [hnorm]
      simp
    rw [hcf]
    have hreal := congrArg Complex.re hcomplex
    simpa [Complex.ofReal_div, Nat.cast_sum, Finset.mul_sum,
      pow_two, Nat.cast_mul] using hreal
/-- Orbit-fiber transfer for the lower kernel-character family used in XI.6.3.
This is specialized to a supplied family of induced images, so it does not
reuse the private PF6.8 transfer proof. -/
private theorem huppert_XI_6_3_induced_indexed_degree_sum_le
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} [K.Normal]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S1 : Finset (ClassFunction L)}
    (theta : ι → ClassFunction K)
    (hthetaIrr : ∀ i, IsIrreducibleCharacterOnGroup (theta i))
    (hthetaInj : Function.Injective theta)
    (dtheta : ι → ℕ)
    (hthetaDegree : ∀ i, degree (theta i) = (dtheta i : Complex))
    (hIndMem : ∀ i, inducedCF K (theta i) ∈ S1)
    (dS1 : S1 → ℕ)
    (hS1Degree : ∀ eta : S1,
      degree (eta : ClassFunction L) = (dS1 eta : Complex)) :
    (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ i : ι, (dtheta i : ℝ) ^ 2 ≤
      ∑ eta : S1,
        (dS1 eta : ℝ) ^ 2 /
          cfNormSq (eta : ClassFunction L) := by
  classical
  let imageInS1 : ι → S1 := fun i =>
    ⟨inducedCF K (theta i), hIndMem i⟩
  let weight : ι → ℝ := fun i =>
    (K.relIndex (⊤ : Subgroup L) : ℝ) * (dtheta i : ℝ) ^ 2
  let contribution : S1 → ℝ := fun eta =>
    (dS1 eta : ℝ) ^ 2 / cfNormSq (eta : ClassFunction L)
  have hcontribution_nonneg : ∀ eta : S1, 0 ≤ contribution eta := by
    intro eta
    exact div_nonneg (sq_nonneg _) (cfNormSq_nonneg _)
  have hcontribution :
      ∀ i, contribution (imageInS1 i) =
        (K.relIndex (⊤ : Subgroup L) : ℝ) *
          ∑ o : conjugateOrbitIndex K (theta i),
            (dtheta i : ℝ) ^ 2 := by
    intro i
    obtain ⟨a, b, ha, hb, hterm⟩ :=
      huppert_XI_6_orbit_contribution
        (L := L) (K := K) (hthetaIrr i)
    have ha' : a = dtheta i := by
      have : (a : Complex) = (dtheta i : Complex) := by
        rw [← ha, hthetaDegree]
      exact_mod_cast this
    have hb' : b = dS1 (imageInS1 i) := by
      have : (b : Complex) = (dS1 (imageInS1 i) : Complex) := by
        rw [← hb]
        exact hS1Degree (imageInS1 i)
      exact_mod_cast this
    change (dS1 (imageInS1 i) : ℝ) ^ 2 /
        cfNormSq (inducedCF K (theta i)) =
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ o : conjugateOrbitIndex K (theta i),
          (dtheta i : ℝ) ^ 2
    rw [← hb', hterm, ha']
  have hsameOrbit :
      ∀ i j, imageInS1 j = imageInS1 i →
        ∃ o : conjugateOrbitIndex K (theta i),
          theta j = conjugateOrbitConj K (theta i) o := by
    intro i j hij
    have hInd :
        inducedCF K (theta j) = inducedCF K (theta i) := by
      exact congrArg Subtype.val hij
    rcases hthetaIrr j with ⟨nj, rhoj, hrhoj, hj⟩
    rcases hthetaIrr i with ⟨ni, rhoi, hrhoi, hi⟩
    have hIndRep :
        inducedCF K rhoj.character = inducedCF K rhoi.character := by
      simpa [hj, hi] using hInd
    obtain ⟨o, ho⟩ :=
      proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
        K rhoj rhoi hrhoj hrhoi hIndRep
    obtain ⟨g, hg⟩ : ∃ g : L,
        rhoj.character = conjugateOnNormal K rhoi.character g := by
      revert ho
      refine Quotient.inductionOn o ?_
      intro g ho
      exact ⟨g, ho⟩
    refine ⟨conjugateOrbitFiber K (theta i) g, ?_⟩
    change theta j = conjugateOnNormal K (theta i) g
    simpa [hj, hi] using hg
  have hfiber :
      ∀ i, (Finset.univ.filter fun j => imageInS1 j = imageInS1 i).sum weight ≤
        contribution (imageInS1 i) := by
    intro i
    let fiber := Finset.univ.filter fun j => imageInS1 j = imageInS1 i
    let orbitMap : ι → conjugateOrbitIndex K (theta i) := fun j =>
      if h : imageInS1 j = imageInS1 i then
        Classical.choose (hsameOrbit i j h)
      else
        conjugateOrbitFiber K (theta i) 1
    have horbit :
        ∀ j, j ∈ fiber →
          theta j = conjugateOrbitConj K (theta i) (orbitMap j) := by
      intro j hj
      have heq : imageInS1 j = imageInS1 i := by
        simpa [fiber] using hj
      simp only [orbitMap, dif_pos heq]
      exact Classical.choose_spec (hsameOrbit i j heq)
    have horbitInj : Set.InjOn orbitMap (fiber : Set ι) := by
      intro j hj k hk heq
      apply hthetaInj
      rw [horbit j hj, horbit k hk, heq]
    have hcard :
        fiber.card ≤ Fintype.card (conjugateOrbitIndex K (theta i)) := by
      apply Finset.card_le_card_of_injOn orbitMap
      · intro j hj
        simp
      · exact horbitInj
    have hdegree :
        ∀ j ∈ fiber, dtheta j = dtheta i := by
      intro j hj
      have hjOrbit := horbit j hj
      have hdegreeOrbit :
          degree (conjugateOrbitConj K (theta i) (orbitMap j)) =
            degree (theta i) := by
        refine Quotient.inductionOn (orbitMap j) ?_
        intro g
        unfold degree conjugateOrbitConj
        dsimp [conjugateOnNormal]
        congr 1
        ext
        simp
      have : (dtheta j : Complex) = (dtheta i : Complex) := by
        rw [← hthetaDegree j, hjOrbit, hdegreeOrbit, hthetaDegree i]
      exact_mod_cast this
    have hfiberSum :
        fiber.sum weight =
          fiber.card *
            ((K.relIndex (⊤ : Subgroup L) : ℝ) *
              (dtheta i : ℝ) ^ 2) := by
      calc
        fiber.sum weight =
            fiber.sum (fun _ =>
              (K.relIndex (⊤ : Subgroup L) : ℝ) *
                (dtheta i : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [weight, hdegree j hj]
        _ = fiber.card *
            ((K.relIndex (⊤ : Subgroup L) : ℝ) *
              (dtheta i : ℝ) ^ 2) := by
          simp [nsmul_eq_mul]
    have horbitSum :
        (∑ _o : conjugateOrbitIndex K (theta i),
          (dtheta i : ℝ) ^ 2) =
        Fintype.card (conjugateOrbitIndex K (theta i)) *
          (dtheta i : ℝ) ^ 2 := by
      simp [nsmul_eq_mul]
    change fiber.sum weight ≤ contribution (imageInS1 i)
    rw [hfiberSum, hcontribution i, horbitSum]
    have hcardReal :
        (fiber.card : ℝ) ≤
          Fintype.card (conjugateOrbitIndex K (theta i)) := by
      exact_mod_cast hcard
    have hfactor_nonneg :
        0 ≤ (K.relIndex (⊤ : Subgroup L) : ℝ) *
          (dtheta i : ℝ) ^ 2 := by positivity
    calc
      (fiber.card : ℝ) *
          ((K.relIndex (⊤ : Subgroup L) : ℝ) *
            (dtheta i : ℝ) ^ 2) ≤
        (Fintype.card (conjugateOrbitIndex K (theta i)) : ℝ) *
          ((K.relIndex (⊤ : Subgroup L) : ℝ) *
            (dtheta i : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcardReal hfactor_nonneg
      _ = (K.relIndex (⊤ : Subgroup L) : ℝ) *
          ((Fintype.card (conjugateOrbitIndex K (theta i)) : ℝ) *
            (dtheta i : ℝ) ^ 2) := by ring
  have hfiberAll :
      ∀ eta : S1,
        (Finset.univ.filter fun i => imageInS1 i = eta).sum weight ≤
          contribution eta := by
    intro eta
    by_cases h : ∃ i, imageInS1 i = eta
    · obtain ⟨i, rfl⟩ := h
      exact hfiber i
    · have hempty :
          Finset.univ.filter (fun i => imageInS1 i = eta) = ∅ := by
        ext i
        simp
        exact fun hi => h ⟨i, hi⟩
      rw [hempty]
      simpa using hcontribution_nonneg eta
  have hsum :
      (∑ i, weight i) ≤ ∑ eta : S1, contribution eta := by
    rw [← Finset.sum_fiberwise
      (s := (Finset.univ : Finset ι)) (g := imageInS1) (f := weight)]
    apply Finset.sum_le_sum
    intro eta _heta
    exact hfiberAll eta
  simpa [weight, contribution, Finset.mul_sum] using hsum

private theorem huppert_XI_6_coherent_of_degree_growth
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G)
    (Y Y0 : Finset (ClassFunction N))
    (tau : ClassFunction N →ₗ[Complex] ClassFunction G)
    (degreeNat : ClassFunction N → ℕ) (m : ℕ)
    (hY0sub : Y0 ⊆ Y)
    (hirreducible : ∀ chi : Y,
      IsIrreducibleCharacterOnGroup (chi : ClassFunction N))
    (hisometry : isCFLinearIsometryOnSpanOn Y puncturedSet tau)
    (hdegreeZero : ∀ phi : ClassFunction N,
      integerSpanOn Y puncturedSet phi →
        Theory.Character.IsVirtualCharacter (tau phi) ∧
          supportedOn (tau phi) puncturedSet)
    (hdegree : ∀ chi : Y, degree (chi : ClassFunction N) = (degreeNat chi : Complex))
    (hY0degree : ∀ chi : Y0, degreeNat chi = m)
    (hY0card : 2 ≤ Y0.card)
    (hdiv : ∀ chi : Y, (chi : ClassFunction N) ∉ Y0 → m ∣ degreeNat chi)
    (hgrowth : ∀ chi : Y, (chi : ClassFunction N) ∉ Y0 →
      2 * degreeNat chi * m <
        ∑ xi ∈ Y.filter (fun xi => degreeNat xi < degreeNat chi), degreeNat xi ^ 2) :
    IsCoherentTriple puncturedSet Y tau := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases hdiff : Y \ Y0 = ∅
    · have hYsub : Y ⊆ Y0 := Finset.sdiff_eq_empty_iff_subset.mp hdiff
      have hYY0 : Y = Y0 := Finset.Subset.antisymm hYsub hY0sub
      subst Y
      apply BenderSuzuki.External.Isaacs.VII.isaacs_theorem_7_15
        N Y0 tau hirreducible hisometry hdegreeZero
      · intro chi psi
        rw [hdegree chi, hdegree psi, hY0degree chi, hY0degree psi]
      · exact hY0card
    · have hdiffne : (Y \ Y0).Nonempty := by
        exact Finset.nonempty_iff_ne_empty.mpr hdiff
      obtain ⟨chi, hchiDiff, hmax⟩ :=
        Finset.exists_max_image (Y \ Y0) degreeNat hdiffne
      have hchiY : chi ∈ Y := (Finset.mem_sdiff.mp hchiDiff).1
      have hchiNotY0 : chi ∉ Y0 := (Finset.mem_sdiff.mp hchiDiff).2
      let S : Finset (ClassFunction N) := Y.erase chi
      have hSproper : S ⊂ Y := Finset.erase_ssubset hchiY
      have hY0subS : Y0 ⊆ S := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hchiNotY0 (h ▸ hx), hY0sub hx⟩
      have hSsubY : S ⊆ Y := Finset.erase_subset chi Y
      have hirreducibleS : ∀ psi : S,
          IsIrreducibleCharacterOnGroup (psi : ClassFunction N) := by
        intro psi
        exact hirreducible ⟨psi, hSsubY psi.property⟩
      have hisometryS : isCFLinearIsometryOnSpanOn S puncturedSet tau := by
        intro phi psi hphi hpsi
        exact hisometry phi psi
          ⟨integerSpan_mono hSsubY hphi.1, hphi.2⟩
          ⟨integerSpan_mono hSsubY hpsi.1, hpsi.2⟩
      have hdegreeZeroS : ∀ phi : ClassFunction N,
          integerSpanOn S puncturedSet phi →
            Theory.Character.IsVirtualCharacter (tau phi) ∧
              supportedOn (tau phi) puncturedSet := by
        intro phi hphi
        exact hdegreeZero phi ⟨integerSpan_mono hSsubY hphi.1, hphi.2⟩
      have hdegreeS : ∀ psi : S,
          degree (psi : ClassFunction N) = (degreeNat psi : Complex) := by
        intro psi
        exact hdegree ⟨psi, hSsubY psi.property⟩
      have hdivS : ∀ psi : S, (psi : ClassFunction N) ∉ Y0 →
          m ∣ degreeNat psi := by
        intro psi hpsi
        exact hdiv ⟨psi, hSsubY psi.property⟩ hpsi
      have hgrowthS : ∀ psi : S, (psi : ClassFunction N) ∉ Y0 →
          2 * degreeNat psi * m <
            ∑ xi ∈ S.filter (fun xi => degreeNat xi < degreeNat psi),
              degreeNat xi ^ 2 := by
        intro psi hpsiNot
        have hpsiDiff : (psi : ClassFunction N) ∈ Y \ Y0 :=
          Finset.mem_sdiff.mpr ⟨hSsubY psi.property, hpsiNot⟩
        have hle : degreeNat psi ≤ degreeNat chi := hmax psi hpsiDiff
        have hnlt : ¬ degreeNat chi < degreeNat psi := Nat.not_lt_of_ge hle
        have hfilterEq :
            S.filter (fun xi => degreeNat xi < degreeNat psi) =
              Y.filter (fun xi => degreeNat xi < degreeNat psi) := by
          ext x
          by_cases hx : x = chi
          · subst x
            simp [S, hnlt]
          · simp [S, hx]
        rw [hfilterEq]
        exact hgrowth ⟨psi, hSsubY psi.property⟩ hpsiNot
      have hcoherentS : IsCoherentTriple puncturedSet S tau :=
        ih S hSproper hY0subS hirreducibleS hisometryS hdegreeZeroS hdegreeS
          hdivS hgrowthS
      have hY0ne : Y0.Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hzero
        rw [hzero] at hY0card
        simp at hY0card
      obtain ⟨psi, hpsiY0⟩ := hY0ne
      let psiS : S := ⟨psi, hY0subS hpsiY0⟩
      have hdivComplex : ∃ d : ℕ,
          degree chi = (d : Complex) * degree (psiS : ClassFunction N) := by
        obtain ⟨d, hd⟩ := hdiv ⟨chi, hchiY⟩ hchiNotY0
        refine ⟨d, ?_⟩
        rw [hdegree ⟨chi, hchiY⟩, hdegreeS psiS, hY0degree ⟨psi, hpsiY0⟩]
        norm_cast
        simpa [Nat.mul_comm] using hd
      have hlowerSub :
          Y.filter (fun xi => degreeNat xi < degreeNat chi) ⊆ S := by
        intro xi hxi
        have hxiY := (Finset.mem_filter.mp hxi).1
        have hxilt := (Finset.mem_filter.mp hxi).2
        exact Finset.mem_erase.mpr ⟨fun h => by subst xi; omega, hxiY⟩
      have hsumle :
          (∑ xi ∈ Y.filter (fun xi => degreeNat xi < degreeNat chi),
            degreeNat xi ^ 2) ≤ ∑ xi ∈ S, degreeNat xi ^ 2 :=
        Finset.sum_le_sum_of_subset hlowerSub
      have hgrowthNat :
          2 * degreeNat chi * m < ∑ xi ∈ S, degreeNat xi ^ 2 :=
        lt_of_lt_of_le (hgrowth ⟨chi, hchiY⟩ hchiNotY0) hsumle
      have hsumAttach :
          (∑ xi : S, degreeNat xi ^ 2) = ∑ xi ∈ S, degreeNat xi ^ 2 := by
        rw [Finset.univ_eq_attach S]
        simpa using Finset.sum_attach S (fun xi => degreeNat xi ^ 2)
      have hgrowthNat' :
          2 * degreeNat chi * m < ∑ xi : S, degreeNat xi ^ 2 := by
        rw [hsumAttach]
        exact hgrowthNat
      have hgrowthComplex :
          2 * (degree chi).re * (degree (psiS : ClassFunction N)).re <
            ∑ xi : S, (degree (xi : ClassFunction N)).re ^ 2 := by
        rw [hdegree ⟨chi, hchiY⟩, hdegreeS psiS,
          hY0degree ⟨psi, hpsiY0⟩]
        simp_rw [hdegreeS]
        norm_num
        exact_mod_cast hgrowthNat'
      have hstep := BenderSuzuki.External.Isaacs.VII.isaacs_theorem_7_14
        N S chi (by simp [S]) psiS tau hirreducibleS
        (hirreducible ⟨chi, hchiY⟩)
        (by
          let : Fintype N := Fintype.ofFinite N
          let : DecidableEq (ClassFunction N) := Fintype.decidablePiFintype
          intro phi xi hphi hxi
          apply hisometry phi xi
          · refine ⟨integerSpan_mono ?_ hphi.1, hphi.2⟩
            intro z hz
            rcases (@Finset.mem_insert _ _ _ _ _).mp hz with rfl | hz
            · exact hchiY
            · exact hSsubY hz
          · refine ⟨integerSpan_mono ?_ hxi.1, hxi.2⟩
            intro z hz
            rcases (@Finset.mem_insert _ _ _ _ _).mp hz with rfl | hz
            · exact hchiY
            · exact hSsubY hz)
        (by
          let : Fintype N := Fintype.ofFinite N
          let : DecidableEq (ClassFunction N) := Fintype.decidablePiFintype
          intro phi hphi
          apply hdegreeZero phi
          refine ⟨integerSpan_mono ?_ hphi.1, hphi.2⟩
          intro z hz
          rcases (@Finset.mem_insert _ _ _ _ _).mp hz with rfl | hz
          · exact hchiY
          · exact hSsubY hz)
        hcoherentS hdivComplex hgrowthComplex
      convert hstep using 1
      ext x
      by_cases hx : x = chi
      · subst x
        simp [S, hchiY]
      · simp [S, hx]

end XI6CoherentDegree

/-- In a transitive Frobenius action with point-stabilizer complement, the
kernel consists exactly of the identity and the derangements. -/
private theorem frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
    {H X : Type*} [Group H] [Finite H] [MulAction H X]
    (htrans : MulAction.IsPretransitive H X) (a : X)
    (F : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer H a)) (x : H) :
    x ∈ F ↔ x = 1 ∨ ∀ y : X, x • y ≠ y := by
  let : MulAction.IsPretransitive H X := htrans
  constructor
  · intro hx
    by_cases hxone : x = 1
    · exact Or.inl hxone
    right
    intro y hxy
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a y
    have hfix : (g⁻¹ * x * g) • a = a := by
      calc
        (g⁻¹ * x * g) • a = g⁻¹ • (x • (g • a)) := by
          simp only [mul_smul]
        _ = g⁻¹ • (x • y) := by rw [hg]
        _ = g⁻¹ • y := by rw [hxy]
        _ = a := by rw [← hg, inv_smul_smul]
    have hmemD : g⁻¹ * x * g ∈ MulAction.stabilizer H a :=
      MulAction.mem_stabilizer_iff.mpr hfix
    have hmemF : g⁻¹ * x * g ∈ F := by
      simpa using hFrob.normal.conj_mem x hx g⁻¹
    have hconjOne : g⁻¹ * x * g = 1 :=
      Subgroup.disjoint_def.mp hFrob.isComplement'.disjoint hmemF hmemD
    apply hxone
    have := congrArg (fun z : H => g * z * g⁻¹) hconjOne
    simpa [mul_assoc] using this
  · rintro (rfl | hfree)
    · simp
    by_contra hxF
    obtain ⟨f, r, hconj⟩ :=
      frobenius_not_mem_kernel_conjugate_mem_complement
        F (MulAction.stabilizer H a) hFrob hxF
    have hxEq : x = (f : H) * (r : H) * (f : H)⁻¹ := by
      have := congrArg (fun z : H => (f : H) * z * (f : H)⁻¹) hconj
      simpa [mul_assoc] using this
    apply hfree ((f : H) • a)
    calc
      x • ((f : H) • a) =
          ((f : H) * (r : H) * (f : H)⁻¹) • ((f : H) • a) := by
            rw [hxEq]
      _ = (f : H) • ((r : H) • a) := by
        simp only [mul_smul, inv_smul_smul]
      _ = (f : H) • a := by
        rw [MulAction.mem_stabilizer_iff.mp r.property]

/-- A Frobenius kernel inside an ambient normal subgroup is ambient-normal:
its elements are characterized as the identity and the derangements. -/
private theorem frobenius_kernel_map_normal_of_ambient_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (N : Subgroup G) (hN : N.Normal) (a : X)
    (K : Subgroup N) (htrans : MulAction.IsPretransitive N X)
    (hFrob : IsFrobeniusGroupWithKernelComplement K
      (MulAction.stabilizer N a)) :
    (K.map N.subtype).Normal := by
  let Kmap : Subgroup G := K.map N.subtype
  change Kmap.Normal
  refine ⟨?_⟩
  intro x hx g
  rcases hx with ⟨k, hkK, hkx⟩
  have hxN : x ∈ N := by
    rw [← hkx]
    exact k.property
  let yN : N := ⟨g * x * g⁻¹, hN.conj_mem x hxN g⟩
  have hyK : yN ∈ K := by
    apply (frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      htrans a K hFrob yN).2
    rcases (frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      htrans a K hFrob k).1 hkK with hkone | hkfree
    · left
      apply Subtype.ext
      have hxone : x = 1 := by
        calc
          x = (k : G) := hkx.symm
          _ = 1 := by simpa using congrArg Subtype.val hkone
      simp [yN, hxone]
    · right
      intro z hyfix
      apply hkfree (g⁻¹ • z)
      have hyfixG : (g * x * g⁻¹) • z = z := by
        simpa [yN] using hyfix
      have hkxG : (k : G) = x := hkx
      change (k : G) • (g⁻¹ • z) = g⁻¹ • z
      rw [hkxG]
      calc
        x • (g⁻¹ • z) = (x * g⁻¹) • z := by rw [mul_smul]
        _ = (g⁻¹ * (g * x * g⁻¹)) • z := by group
        _ = g⁻¹ • ((g * x * g⁻¹) • z) := by rw [mul_smul]
        _ = g⁻¹ • z := by rw [hyfixG]
  exact ⟨yN, hyK, rfl⟩

/-- Every nontrivial ambient normal subgroup has point stabilizer containing
the point-stabilizer Frobenius kernel. -/
public theorem zassenhaus_normal_stabilizer_contains_frobeniusKernel
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    let H := MulAction.stabilizer G a
    F ≤ N.comap H.subtype := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Na : Subgroup H := N.comap H.subtype
  change F ≤ Na
  let : N.Normal := hNnormal
  let : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let : MulAction.IsQuasiPreprimitive G X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn_one : n = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) n (by
        intro x
        have hx : x ∈ MulAction.fixedPoints N X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩)
    exact Subgroup.mem_bot.mpr hn_one
  have hNtrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  have hNaNormal : Na.Normal := by
    simpa [Na] using hNnormal.comap H.subtype
  rcases frobenius_normal_subgroup_le_kernel_or_kernel_le
      F D Na (by simpa [D] using hFrob) hNaNormal with hNaF | hFNa
  · exfalso
    let R := MulAction.stabilizer N a
    have hRne : R ≠ ⊥ := by
      intro hRbot
      apply hno_regular_normal
      refine ⟨N, hNnormal, hNne, ?_⟩
      have hcomp : (⊤ : Subgroup N).IsComplement' R := by
        rw [hRbot]
        exact Subgroup.isComplement'_top_bot
      have hregularTop :=
        huppert_blackburn_XI_regular_of_isComplement_stabilizer
          (a := a) hcomp hNtrans
      intro x y
      obtain ⟨r, hr, hrunique⟩ := hregularTop x y
      refine ⟨(r : N), by simpa [Subgroup.smul_def] using hr, ?_⟩
      intro n hn
      let nTop : (⊤ : Subgroup N) := ⟨n, trivial⟩
      have hnTop : (nTop : N) • x = y := by simpa [nTop, Subgroup.smul_def] using hn
      have heq : nTop = r := hrunique nTop hnTop
      exact congrArg Subtype.val heq
    have hRproper : R ≠ ⊤ := by
      intro hRtop
      obtain ⟨n, hn⟩ := hNtrans.exists_smul_eq a b
      have hnR : n ∈ R := by rw [hRtop]; simp
      have hfix : n • a = a := MulAction.mem_stabilizer_iff.mp hnR
      exact hab (hfix.symm.trans hn)
    let rToH : R → H := fun r =>
      ⟨((r : N) : G), by
        apply MulAction.mem_stabilizer_iff.mpr
        simpa [Subgroup.smul_def] using MulAction.mem_stabilizer_iff.mp r.property⟩
    have hRtoF : ∀ r : R, rToH r ∈ F := by
      intro r
      apply hNaF
      change ((rToH r : H) : G) ∈ N
      exact (r : N).property
    have hRTI : ∀ g : N, g ∉ R → Disjoint R (R.conjBy g) := by
      intro g hgR
      rw [Subgroup.disjoint_def]
      intro x hxR hxconj
      by_contra hxne
      let xF : F := ⟨rToH ⟨x, hxR⟩, hRtoF ⟨x, hxR⟩⟩
      have hxFne : xF ≠ 1 := by
        intro hxone
        apply hxne
        apply Subtype.ext
        simpa [xF, rToH] using
          congrArg Subtype.val (congrArg Subtype.val hxone)
      rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
      rcases hxconj with ⟨r, hrR, hrx⟩
      have hxfixga : ((x : N) : G) • (((g : N) : G) • a) =
          ((g : N) : G) • a := by
        have hrfix : (r : N) • a = a :=
          MulAction.mem_stabilizer_iff.mp hrR
        have hxval : (x : N) = g * r * g⁻¹ := hrx.symm
        have hxvalG : ((x : N) : G) =
            ((g : N) : G) * ((r : N) : G) * ((g : N) : G)⁻¹ := by
          exact congrArg Subtype.val hxval
        have hrfixG : ((r : N) : G) • a = a := by simpa [Subgroup.smul_def] using hrfix
        calc
          ((x : N) : G) • (((g : N) : G) • a) =
              (((g : N) : G) * ((r : N) : G) * ((g : N) : G)⁻¹) •
                (((g : N) : G) • a) := by rw [hxvalG]
          _ = ((g : N) : G) • (((r : N) : G) • a) := by
            simp only [mul_smul, inv_smul_smul]
          _ = ((g : N) : G) • a := by rw [hrfixG]
      have hga : ((g : N) : G) • a = a :=
        (huppert_XI_6_4_frobeniusKernel_uniqueFixedPoint
          htwo a b hab F hFrob xF hxFne (((g : N) : G) • a)).mp (by simpa [xF, rToH] using hxfixga)
      apply hgR
      exact MulAction.mem_stabilizer_iff.mpr (by simpa [Subgroup.smul_def] using hga)
    obtain ⟨K, hKFrob⟩ :=
      Suzuki.VI.suzuki_ch6_theorem_2_3 R hRne hRproper hRTI
    let Kmap : Subgroup G := K.map N.subtype
    have hKmapNormal : Kmap.Normal := by
      simpa [Kmap] using
        frobenius_kernel_map_normal_of_ambient_normal
          N hNnormal a K hNtrans hKFrob
    have hKmapNe : Kmap ≠ ⊥ := by
      intro hKmapBot
      apply hKFrob.kernel_ne_bot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := N.subtype) N.subtype_injective).mp
          (by simpa [Kmap] using hKmapBot)
    apply hno_regular_normal
    refine ⟨Kmap, hKmapNormal, hKmapNe, ?_⟩
    have hKregular :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        (a := a) hKFrob.isComplement' hNtrans
    intro x y
    obtain ⟨k, hk, hkunique⟩ := hKregular x y
    let kg : Kmap := ⟨((k : N) : G), ⟨(k : N), k.property, rfl⟩⟩
    refine ⟨kg, by simpa [kg, Subgroup.smul_def] using hk, ?_⟩
    intro z hz
    rcases z.property with ⟨n, hnK, hnz⟩
    let nK : K := ⟨n, hnK⟩
    have hnact : (nK : N) • x = y := by
      have hnzG : ((nK : N) : G) = (z : G) := by
        simpa [nK] using hnz
      calc
        (nK : N) • x = ((nK : N) : G) • x := rfl
        _ = (z : G) • x := by rw [hnzG]
        _ = y := hz
    have hnk : nK = k := hkunique nK hnact
    apply Subtype.ext
    calc
      (z : G) = (n : G) := hnz.symm
      _ = ((k : N) : G) := by rw [show n = (k : N) from congrArg Subtype.val hnk]
      _ = (kg : G) := rfl
  · exact hFNa

/-- Every nontrivial ambient normal subgroup is doubly transitive. -/
public theorem zassenhaus_nontrivial_normal_is_two_pretransitive
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    MulAction.IsMultiplyPretransitive N X 2 := by
  let H := MulAction.stabilizer G a
  let : N.Normal := hNnormal
  let : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let : MulAction.IsQuasiPreprimitive G X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn_one : n = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) n (by
        intro x
        have hx : x ∈ MulAction.fixedPoints N X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩)
    exact Subgroup.mem_bot.mpr hn_one
  have hNtrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  have hFNa : F ≤ N.comap H.subtype := by
    simpa [H] using
      zassenhaus_normal_stabilizer_contains_frobeniusKernel
        htwo hno_regular_normal a b hab F hFrob N hNnormal hNne
  have hstab_multi :
      MulAction.IsMultiplyPretransitive H
        (SubMulAction.ofStabilizer G a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hHtrans :
      MulAction.IsPretransitive H (SubMulAction.ofStabilizer G a) :=
    (MulAction.is_one_pretransitive_iff
      (G := H) (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
  have hFregular :
      ∀ x y : SubMulAction.ofStabilizer G a,
        ∃! f : F, (f : H) • x = y :=
    huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrob.isComplement' hHtrans
  have htoBase : ∀ x y : X, x ≠ y →
      ∃ n : N, n • x = a ∧ n • y = b := by
    intro x y hxy
    obtain ⟨n0, hn0x⟩ := hNtrans.exists_smul_eq x a
    have hn0y_ne : n0 • y ≠ a := by
      intro hn0y
      apply hxy
      exact smul_left_cancel n0 (hn0x.trans hn0y.symm)
    let ySub : SubMulAction.ofStabilizer G a := ⟨n0 • y, hn0y_ne⟩
    let bSub : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
    obtain ⟨f, hf, _hfunique⟩ := hFregular ySub bSub
    have hfNmem : ((f : H) : G) ∈ N := by
      exact hFNa f.property
    let fN : N := ⟨((f : H) : G), hfNmem⟩
    have hfixa : fN • a = a := by
      change ((f : H) : G) • a = a
      exact MulAction.mem_stabilizer_iff.mp (f : H).property
    have hfY : fN • (n0 • y) = b := by
      simpa [fN, ySub, bSub, Subgroup.smul_def] using congrArg Subtype.val hf
    refine ⟨fN * n0, ?_, ?_⟩
    · rw [mul_smul, hn0x, hfixa]
    · rw [mul_smul, hfY]
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y u v hxy huv
  obtain ⟨p, hpx, hpy⟩ := htoBase x y hxy
  obtain ⟨q, hqu, hqv⟩ := htoBase u v huv
  refine ⟨q⁻¹ * p, ?_, ?_⟩
  · rw [mul_smul, hpx, ← hqu, inv_smul_smul]
  · rw [mul_smul, hpy, ← hqv, inv_smul_smul]

/-- Swapping the two subtype layers identifies `N ∩ G_a` with `N_a`. -/
@[expose] public def normalSubgroup_pointStabilizerEquiv
    {G X : Type*} [Group G] [MulAction G X]
    (N : Subgroup G) (a : X) :
    N.comap (MulAction.stabilizer G a).subtype ≃*
      MulAction.stabilizer N a where
  toFun x :=
    ⟨⟨((x : MulAction.stabilizer G a) : G), x.property⟩,
      (x : MulAction.stabilizer G a).property⟩
  invFun y :=
    ⟨⟨((y : N) : G), y.property⟩, (y : N).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Restrict a Frobenius decomposition to a subgroup containing its kernel. -/
public theorem frobenius_restrict_to_subgroup_containing_kernel
    {H : Type*} [Group H]
    (K R N : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    (hKN : K ≤ N)
    (hRcap_ne : R.comap N.subtype ≠ ⊥) :
    IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf N) (R.comap N.subtype) := by
  have hKsub_normal : (K.subgroupOf N).Normal :=
    hFrob.normal.subgroupOf N
  have hKsub_ne : K.subgroupOf N ≠ ⊥ := by
    intro hbot
    apply hFrob.kernel_ne_bot
    rw [eq_bot_iff]
    intro k hk
    let kN : N := ⟨k, hKN hk⟩
    have hkSub : kN ∈ K.subgroupOf N := hk
    have hkBot : kN ∈ (⊥ : Subgroup N) := by simpa [hbot] using hkSub
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hkBot))
  have hcomp :
      (K.subgroupOf N).IsComplement' (R.comap N.subtype) := by
    apply (Subgroup.isComplement_iff_existsUnique).mpr
    intro n
    obtain ⟨kr, hkr, huniq⟩ :=
      (Subgroup.isComplement_iff_existsUnique.mp hFrob.isComplement')
        (n : H)
    let kN : N := ⟨(kr.1 : H), hKN kr.1.property⟩
    have hrNmem : (kr.2 : H) ∈ N := by
      have hnmem : (n : H) ∈ N := n.property
      have hkInv : (kr.1 : H)⁻¹ ∈ N := N.inv_mem (hKN kr.1.property)
      have hEq : (kr.2 : H) = (kr.1 : H)⁻¹ * (n : H) := by
        rw [← hkr]
        simp
      rw [hEq]
      exact N.mul_mem hkInv hnmem
    let rN : N := ⟨(kr.2 : H), hrNmem⟩
    let kSub : K.subgroupOf N := ⟨kN, kr.1.property⟩
    let rSub : R.comap N.subtype := ⟨rN, kr.2.property⟩
    refine ⟨(kSub, rSub), ?_, ?_⟩
    · apply Subtype.ext
      exact hkr
    · intro yz hyz
      let yK : K := ⟨((yz.1 : N) : H), yz.1.property⟩
      let yR : R := ⟨((yz.2 : N) : H), yz.2.property⟩
      have hyzH : (yK : H) * (yR : H) = (n : H) :=
        congrArg Subtype.val hyz
      have hpair : (yK, yR) = kr := huniq (yK, yR) hyzH
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun q : K × R => (q.1 : H)) hpair
      · apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun q : K × R => (q.2 : H)) hpair
  refine ⟨hKsub_normal, hcomp, ?_, hKsub_ne, hRcap_ne⟩
  intro g hgRcap
  have hgR : ((g : N) : H) ∉ R := by
    intro hg
    exact hgRcap hg
  rw [Subgroup.disjoint_def]
  intro x hxR hxconj
  have hxRH : ((x : N) : H) ∈ R := hxR
  have hxconjH : ((x : N) : H) ∈ R.conjBy ((g : N) : H) := by
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj ⊢
    rcases hxconj with ⟨r, hr, hrx⟩
    refine ⟨((r : N) : H), hr, ?_⟩
    exact congrArg Subtype.val hrx
  have hxBot : ((x : N) : H) ∈ (⊥ : Subgroup H) :=
    (Subgroup.disjoint_def.mp
      (hFrob.disjoint_conjBy ((g : N) : H) hgR)) hxRH hxconjH
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hxBot

/-- A nontrivial regular normal subgroup of a finite doubly transitive group
is elementary Abelian. -/
private theorem zassenhaus_regular_normal_elementaryAbelian
    {N X : Type*} [Group N] [Finite N] [MulAction N X]
    [FaithfulSMul N X]
    (htwo : MulAction.IsMultiplyPretransitive N X 2)
    (a : X) (M : Subgroup N) (hMnormal : M.Normal) (hMne : M ≠ ⊥)
    (hMregular :
      ∀ x y : X, ∃! m : M, (m : N) • x = y) :
    ∃ p : ℕ, Nat.Prime p ∧ IsElementaryAbelian p M := by
  classical
  let : M.Normal := hMnormal
  have hmove (m : M) (hm : m ≠ 1) : (m : N) • a ≠ a := by
    intro hma
    obtain ⟨m0, hm0, huniq⟩ := hMregular a a
    have hmm0 : m = m0 := huniq m hma
    have h1m0 : (1 : M) = m0 := huniq 1 (by simp)
    exact hm (hmm0.trans h1m0.symm)
  have hconj_transitive :
      ∀ x y : M, x ≠ 1 → y ≠ 1 →
        ∃ d : N, d * (x : N) * d⁻¹ = (y : N) := by
    intro x y hx hy
    obtain ⟨d, hda, hdxy⟩ :=
      MulAction.is_two_pretransitive_iff.mp htwo
        (hmove x hx) (hmove y hy)
    let xconj : M :=
      ⟨d * (x : N) * d⁻¹,
        hMnormal.conj_mem (x : N) x.property d⟩
    have hdia : d⁻¹ • a = a := by
      calc
        d⁻¹ • a = d⁻¹ • (d • a) := by rw [hdxy]
        _ = a := inv_smul_smul d a
    have hxconj_act : (xconj : N) • a = (y : N) • a := by
      change (d * (x : N) * d⁻¹) • a = (y : N) • a
      rw [mul_smul, mul_smul, hdia]
      exact hda
    obtain ⟨m0, hm0, huniq⟩ := hMregular a ((y : N) • a)
    have hxm0 : xconj = m0 := huniq xconj hxconj_act
    have hym0 : y = m0 := huniq y rfl
    exact ⟨d, congrArg Subtype.val (hxm0.trans hym0.symm)⟩
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hMne
  have hMcard_ne_one : Nat.card M ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hMcard_ne_one
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hzne : z ≠ 1 := by
    intro hz
    have : p = 1 := by simpa [hz] using hzorder.symm
    exact hp.ne_one this
  have hprime_order (x : M) (hx : x ≠ 1) : orderOf x = p := by
    obtain ⟨d, hd⟩ := hconj_transitive x z hx hzne
    have hsemi : SemiconjBy d (x : N) (z : N) := by
      change d * (x : N) = (z : N) * d
      calc
        d * (x : N) = (d * (x : N) * d⁻¹) * d := by group
        _ = (z : N) * d := by rw [hd]
    calc
      orderOf x = orderOf (x : N) :=
        (orderOf_injective M.subtype M.subtype_injective x).symm
      _ = orderOf (z : N) := SemiconjBy.orderOf_eq d hsemi
      _ = orderOf z := orderOf_injective M.subtype M.subtype_injective z
      _ = p := hzorder
  have hMp : IsPGroup p M := (IsPGroup.iff_orderOf).2 (by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hprime_order x hx]⟩)
  have hMcomm : IsMulCommutative M := by
    let : Nontrivial (Subgroup.center M) := hMp.center_nontrivial
    obtain ⟨zc, hzc⟩ := exists_ne (1 : Subgroup.center M)
    let zM : M := zc
    have hzM_ne : zM ≠ 1 := by
      intro hzM
      apply hzc
      exact Subtype.ext hzM
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    by_cases hx : x = 1
    · simp [hx]
    obtain ⟨d, hd⟩ := hconj_transitive x zM hx hzM_ne
    let ydy : M :=
      ⟨d * (y : N) * d⁻¹,
        hMnormal.conj_mem (y : N) y.property d⟩
    have hz_comm : zM * ydy = ydy * zM :=
      ((Subgroup.mem_center_iff.mp zc.property) ydy).symm
    have hz_comm_N :
        (zM : N) * (d * (y : N) * d⁻¹) =
          (d * (y : N) * d⁻¹) * (zM : N) := by
      simpa [ydy, zM] using congrArg Subtype.val hz_comm
    apply Subtype.ext
    change (x : N) * (y : N) = (y : N) * (x : N)
    calc
      (x : N) * (y : N) =
          d⁻¹ * (zM : N) * d * (y : N) := by
            rw [← hd]
            group
      _ = d⁻¹ * ((zM : N) * (d * (y : N) * d⁻¹)) * d := by
            group
      _ = d⁻¹ * ((d * (y : N) * d⁻¹) * (zM : N)) * d := by
            rw [hz_comm_N]
      _ = (y : N) * (d⁻¹ * (zM : N) * d) := by
            group
      _ = (y : N) * (x : N) := by
            rw [← hd]
            group
  have hMelem : IsElementaryAbelian p M := by
    refine
      { toIsMulCommutative := hMcomm
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    intro x
    by_cases hx : x = 1
    · simp [hx]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hprime_order x hx]
  exact ⟨p, hp, hMelem⟩

/-- A finite faithful doubly transitive group has at most one nontrivial
regular normal subgroup. -/
private theorem zassenhaus_regular_normal_unique
    {N X : Type*} [Group N] [Finite N] [MulAction N X]
    [FaithfulSMul N X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive N X 2)
    (a : X) (M R : Subgroup N)
    (hMnormal : M.Normal) (hRnormal : R.Normal)
    (hMne : M ≠ ⊥) (_hRne : R ≠ ⊥)
    (hMregular :
      ∀ x y : X, ∃! m : M, (m : N) • x = y)
    (hRregular :
      ∀ x y : X, ∃! r : R, (r : N) • x = y) :
    M = R := by
  classical
  let : M.Normal := hMnormal
  let : R.Normal := hRnormal
  let : MulAction.IsPreprimitive N X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let : MulAction.IsQuasiPreprimitive N X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have normal_transitive (K : Subgroup N) (hKnormal : K.Normal)
      (hKne : K ≠ ⊥) : MulAction.IsPretransitive K X := by
    let : K.Normal := hKnormal
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply hKne
    rw [eq_bot_iff]
    intro k hk
    have hk_one : k = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul N X)) k (by
        intro x
        have hx : x ∈ MulAction.fixedPoints K X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨k, hk⟩)
    exact Subgroup.mem_bot.mpr hk_one
  let J := M ⊓ R
  have hJnormal : J.Normal := by
    dsimp [J]
    infer_instance
  by_cases hJne : J ≠ ⊥
  · have hJtrans : MulAction.IsPretransitive J X :=
      normal_transitive J hJnormal hJne
    have hMleR : M ≤ R := by
      intro m hm
      let mM : M := ⟨m, hm⟩
      obtain ⟨j, hj⟩ := hJtrans.exists_smul_eq a (m • a)
      let jM : M := ⟨(j : N), j.property.1⟩
      obtain ⟨m0, hm0, huniq⟩ := hMregular a (m • a)
      have hjm0 : jM = m0 := huniq jM (by simpa [jM, Subgroup.smul_def] using hj)
      have hmm0 : mM = m0 := huniq mM rfl
      have hmj : m = (j : N) :=
        congrArg Subtype.val (hmm0.trans hjm0.symm)
      rw [hmj]
      exact j.property.2
    have hRleM : R ≤ M := by
      intro r hr
      let rR : R := ⟨r, hr⟩
      obtain ⟨j, hj⟩ := hJtrans.exists_smul_eq a (r • a)
      let jR : R := ⟨(j : N), j.property.2⟩
      obtain ⟨r0, hr0, huniq⟩ := hRregular a (r • a)
      have hjr0 : jR = r0 := huniq jR (by simpa [jR, Subgroup.smul_def] using hj)
      have hrr0 : rR = r0 := huniq rR rfl
      have hrj : r = (j : N) :=
        congrArg Subtype.val (hrr0.trans hjr0.symm)
      rw [hrj]
      exact j.property.1
    exact le_antisymm hMleR hRleM
  · have hJbot : J = ⊥ := not_ne_iff.mp hJne
    have hcomm_bot : ⁅M, R⁆ = ⊥ := by
      apply eq_bot_iff.mpr
      rw [← hJbot]
      exact Subgroup.commutator_le_inf M R
    have hMcentR : M ≤ Subgroup.centralizer R :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := M) (H₂ := R)).mp hcomm_bot
    obtain ⟨p, hp, hMelem⟩ :=
      zassenhaus_regular_normal_elementaryAbelian
        htwo a M hMnormal hMne hMregular
    let : IsMulCommutative M := hMelem.toIsMulCommutative
    have hRleM : R ≤ M := by
      intro r hr
      obtain ⟨m, hmact, _hmunique⟩ := hMregular a (r • a)
      have hrm : r = (m : N) := by
        apply eq_of_smul_eq_smul (α := X)
        intro x
        obtain ⟨k, hkact, _hkunique⟩ := hMregular a x
        have hrk : r * (k : N) = (k : N) * r :=
          (Subgroup.mem_centralizer_iff.mp (hMcentR k.property)) r hr
        have hkm : (k : N) * (m : N) = (m : N) * (k : N) := by
          simpa [Subgroup.coe_mul] using
            congrArg Subtype.val (hMelem.toIsMulCommutative.1.comm k m)
        calc
          r • x = r • ((k : N) • a) := by rw [hkact]
          _ = (r * (k : N)) • a := (mul_smul r (k : N) a).symm
          _ = ((k : N) * r) • a := by rw [hrk]
          _ = (k : N) • (r • a) := mul_smul (k : N) r a
          _ = (k : N) • ((m : N) • a) := by rw [hmact]
          _ = ((k : N) * (m : N)) • a :=
            (mul_smul (k : N) (m : N) a).symm
          _ = ((m : N) * (k : N)) • a := by rw [hkm]
          _ = (m : N) • ((k : N) • a) := mul_smul (m : N) (k : N) a
          _ = (m : N) • x := by rw [hkact]
      rw [hrm]
      exact m.property
    have hMleR : M ≤ R := by
      intro m hm
      let mM : M := ⟨m, hm⟩
      obtain ⟨r, hract, _hrunique⟩ := hRregular a (m • a)
      have hrM : (r : N) ∈ M := hRleM r.property
      let rM : M := ⟨(r : N), hrM⟩
      obtain ⟨m0, hm0, huniq⟩ := hMregular a (m • a)
      have hrm0 : rM = m0 := huniq rM (by simpa [rM] using hract)
      have hmm0 : mM = m0 := huniq mM rfl
      have hmr : m = (r : N) :=
        congrArg Subtype.val (hmm0.trans hrm0.symm)
      rw [hmr]
      exact r.property
    exact le_antisymm hMleR hRleM

/-- A nontrivial ambient normal subgroup inherits the absence of regular
normal subgroups. -/
public theorem zassenhaus_normal_subgroup_no_regular_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (N : Subgroup G) (hNnormal : N.Normal) (a : X)
    (hNtwo : MulAction.IsMultiplyPretransitive N X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y) :
    ¬ ∃ M : Subgroup N, M.Normal ∧ M ≠ ⊥ ∧
      ∀ x y : X, ∃! m : M, (m : N) • x = y := by
  classical
  let : N.Normal := hNnormal
  rintro ⟨M, hMnormal, hMne, hMregular⟩
  let : M.Normal := hMnormal
  have hMconj_eq (g : G) :
      M.map (MulAut.conjNormal (H := N) g) = M := by
    let phi : MulAut N := MulAut.conjNormal (H := N) g
    let Mg : Subgroup N := M.map phi
    have hMgnormal : Mg.Normal := by
      exact hMnormal.map phi.toMonoidHom phi.surjective
    have hMgne : Mg ≠ ⊥ := by
      intro hMgBot
      apply hMne
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := M) (f := phi) phi.injective).mp (by simpa [Mg] using hMgBot)
    have hMgregular :
        ∀ x y : X, ∃! mg : Mg, (mg : N) • x = y := by
      intro x y
      obtain ⟨m, hmact, hmunique⟩ :=
        hMregular (g⁻¹ • x) (g⁻¹ • y)
      let mg : Mg :=
        ⟨phi (m : N), ⟨(m : N), m.property, rfl⟩⟩
      have hmgact : (mg : N) • x = y := by
        change ((phi (m : N) : N) : G) • x = y
        change (g * ((m : N) : G) * g⁻¹) • x = y
        calc
          (g * ((m : N) : G) * g⁻¹) • x =
              g • (((m : N) : G) • (g⁻¹ • x)) := by
                simp only [mul_smul]
          _ = g • (g⁻¹ • y) := by
            simpa [Subgroup.smul_def] using congrArg (fun z => g • z) hmact
          _ = y := smul_inv_smul g y
      refine ⟨mg, hmgact, ?_⟩
      intro z hz
      rcases z.property with ⟨n, hnM, hnz⟩
      let nM : M := ⟨n, hnM⟩
      have hnzG :
          g * ((n : N) : G) * g⁻¹ = ((z : N) : G) := by
        simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
          congrArg (fun q : N => (q : G)) hnz
      have hnact : (nM : N) • (g⁻¹ • x) = g⁻¹ • y := by
        change ((n : N) : G) • (g⁻¹ • x) = g⁻¹ • y
        calc
          ((n : N) : G) • (g⁻¹ • x) =
              (((n : N) : G) * g⁻¹) • x :=
                (mul_smul ((n : N) : G) g⁻¹ x).symm
          _ = (g⁻¹ * (g * ((n : N) : G) * g⁻¹)) • x := by
                congr 1
                group
          _ = g⁻¹ • ((g * ((n : N) : G) * g⁻¹) • x) :=
                mul_smul g⁻¹ (g * ((n : N) : G) * g⁻¹) x
          _ = g⁻¹ • (((z : N) : G) • x) := by rw [hnzG]
          _ = g⁻¹ • y := by
            simpa [Subgroup.smul_def] using congrArg (fun q => g⁻¹ • q) hz
      have hnm : nM = m := hmunique nM hnact
      apply Subtype.ext
      calc
        (z : N) = phi n := hnz.symm
        _ = phi (m : N) := by rw [show n = (m : N) from congrArg Subtype.val hnm]
        _ = (mg : N) := rfl
    have hEq : Mg = M :=
      (zassenhaus_regular_normal_unique
        hNtwo a M Mg hMnormal hMgnormal hMne hMgne hMregular hMgregular).symm
    simpa [Mg, phi] using hEq
  let K : Subgroup G := M.map N.subtype
  have hKnormal : K.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases hx with ⟨n, hnM, hnx⟩
    let phi : MulAut N := MulAut.conjNormal (H := N) g
    have hphiM : phi n ∈ M := by
      have hmem : phi n ∈ M.map phi :=
        Subgroup.mem_map_of_mem phi.toMonoidHom hnM
      rw [hMconj_eq g] at hmem
      exact hmem
    refine ⟨phi n, hphiM, ?_⟩
    rw [← hnx]
    rfl
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hMne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := M) (f := N.subtype) N.subtype_injective).mp
        (by simpa [K] using hKbot)
  apply hno_regular_normal
  refine ⟨K, hKnormal, hKne, ?_⟩
  intro x y
  obtain ⟨m, hmact, hmunique⟩ := hMregular x y
  let kg : K :=
    ⟨((m : N) : G), ⟨(m : N), m.property, rfl⟩⟩
  refine ⟨kg, by simpa [kg, Subgroup.smul_def] using hmact, ?_⟩
  intro z hz
  rcases z.property with ⟨n, hnM, hnz⟩
  let nM : M := ⟨n, hnM⟩
  have hnact : (nM : N) • x = y := by
    have hnzG : ((nM : N) : G) = (z : G) := by
      simpa [nM] using hnz
    calc
      (nM : N) • x = ((nM : N) : G) • x := rfl
      _ = (z : G) • x := by rw [hnzG]
      _ = y := hz
  have hnm : nM = m := hmunique nM hnact
  apply Subtype.ext
  calc
    (z : G) = (n : G) := hnz.symm
    _ = ((m : N) : G) := by rw [show n = (m : N) from congrArg Subtype.val hnm]
    _ = (kg : G) := rfl

/-- The kernel of a finite Frobenius group is commutative when the complement
has even order. -/
private theorem frobenius_kernel_commutative_of_even_complement_card
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hDcardEven : Even (Nat.card D)) :
    IsMulCommutative F := by
  have htwoD : 2 ∣ Nat.card D := even_iff_two_dvd.mp hDcardEven
  obtain ⟨t, htorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 htwoD
  have htne : t ≠ 1 := by
    intro ht
    subst t
    simp at htorder
  have htsq : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  have htsqH : (t : H) ^ 2 = 1 := by
    simpa using congrArg Subtype.val htsq
  let : F.Normal := hFrob.normal
  let phi : MulAut F := MulAut.conjNormal (H := F) (t : H)
  have hphi_sq : phi ^ 2 = 1 := by
    change (MulAut.conjNormal (H := F) (t : H)) ^ 2 = 1
    rw [← map_pow, htsqH, map_one]
  have hphi_involutive : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut F => psi x) hphi_sq
    simpa [pow_two] using hx
  have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hconj :
        (t : H) * (x : H) * (t : H)⁻¹ = (x : H) := by
      simpa [phi] using congrArg Subtype.val hx
    have hcomm : (t : H) * (x : H) = (x : H) * (t : H) := by
      calc
        (t : H) * (x : H) =
            ((t : H) * (x : H) * (t : H)⁻¹) * (t : H) := by
              simp [mul_assoc]
        _ = (x : H) * (t : H) := by rw [hconj]
    have hcent :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob t htne
    have hxcent : (x : H) ∈ elementCentralizerIn F (t : H) :=
      ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [hcent] at hxcent
    exact Subtype.ext (Subgroup.mem_bot.mp hxcent)
  refine ⟨⟨fun x y => ?_⟩⟩
  exact (hphi_fixedPointFree.commute_all_of_involutive
    hphi_involutive x y).eq

/-- A finite Frobenius complement contains at most one involution.  Both
involutions would act as inversion on the kernel, and the conjugation action
of the complement on the nontrivial kernel is faithful. -/
public theorem frobenius_complement_involutions_eq
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (t u : D) (htorder : orderOf t = 2) (huorder : orderOf u = 2) :
    t = u := by
  let : F.Normal := hFrob.normal
  have hconjInv : ∀ r : D, orderOf r = 2 → ∀ x : F,
      (r : H) * (x : H) * (r : H)⁻¹ = (x⁻¹ : F) := by
    intro r hrorder x
    have hrne : r ≠ 1 := by
      intro hr
      subst r
      simp at hrorder
    have hrsqD : r ^ 2 = 1 := by
      rw [← hrorder]
      exact pow_orderOf_eq_one r
    have hrsqH : (r : H) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hrsqD
    let phi : MulAut F := MulAut.conjNormal (H := F) (r : H)
    have hphi_sq : phi ^ 2 = 1 := by
      change (MulAut.conjNormal (H := F) (r : H)) ^ 2 = 1
      rw [← map_pow, hrsqH, map_one]
    have hphi_involutive : Function.Involutive phi := by
      intro y
      have hy := congrArg (fun psi : MulAut F => psi y) hphi_sq
      simpa [pow_two] using hy
    have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
      intro y hy
      have hyconj :
          (r : H) * (y : H) * (r : H)⁻¹ = (y : H) := by
        simpa [phi] using congrArg Subtype.val hy
      have hycomm : (r : H) * (y : H) = (y : H) * (r : H) := by
        have := congrArg (fun z : H => z * (r : H)) hyconj
        simpa [mul_assoc] using this
      have hycent : (y : H) ∈ elementCentralizerIn F (r : H) :=
        ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr hycomm.symm⟩
      have hcent : elementCentralizerIn F (r : H) = ⊥ :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob r hrne
      have hybot : (y : H) ∈ (⊥ : Subgroup H) := by
        simpa [hcent] using hycent
      exact Subtype.ext (by simpa using hybot)
    have hinv := hphi_fixedPointFree.coe_eq_inv_of_involutive hphi_involutive
    simpa [phi] using congrArg Subtype.val (congrFun hinv x)
  have htInv := hconjInv t htorder
  have huInv := hconjInv u huorder
  let v : D := t⁻¹ * u
  by_contra htu
  have hvne : v ≠ 1 := by
    intro hv
    apply htu
    have := congrArg (fun z : D => t * z) hv
    simpa [v, mul_assoc] using this.symm
  obtain ⟨x, hx⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot
  have hvcomm : (v : H) * (x : H) = (x : H) * (v : H) := by
    have ht := htInv x
    have hu := huInv x
    have ht' : (t : H) * (x : H) * (t : H)⁻¹ = (x : H)⁻¹ := by
      simpa using ht
    have hu' : (u : H) * (x : H) * (u : H)⁻¹ = (x : H)⁻¹ := by
      simpa using hu
    have huMove : (u : H) * (x : H) = (x : H)⁻¹ * (u : H) := by
      calc
        (u : H) * (x : H) =
            ((u : H) * (x : H) * (u : H)⁻¹) * (u : H) := by group
        _ = (x : H)⁻¹ * (u : H) := by rw [hu']
    have htMove : (t : H)⁻¹ * (x : H)⁻¹ =
        (x : H) * (t : H)⁻¹ := by
      calc
        (t : H)⁻¹ * (x : H)⁻¹ =
            (t : H)⁻¹ * ((t : H) * (x : H) * (t : H)⁻¹) := by rw [ht']
        _ = (x : H) * (t : H)⁻¹ := by group
    change ((t : H)⁻¹ * (u : H)) * (x : H) =
      (x : H) * ((t : H)⁻¹ * (u : H))
    calc
      ((t : H)⁻¹ * (u : H)) * (x : H) =
          (t : H)⁻¹ * ((x : H)⁻¹ * (u : H)) := by
            rw [mul_assoc, huMove]
      _ = (x : H) * ((t : H)⁻¹ * (u : H)) := by
            rw [← mul_assoc, htMove, mul_assoc]
  have hxcent : (x : H) ∈ elementCentralizerIn F (v : H) :=
    ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hvcomm.symm⟩
  have hcent : elementCentralizerIn F (v : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob v hvne
  have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
    simpa [hcent] using hxcent
  apply hx
  apply Subtype.ext
  simpa using hxbot

/-- XI.1.7(c): if the two-point stabilizer has even order, a conjugate of
one of its involutions interchanges the two distinguished points. -/
public theorem zassenhaus_even_twoPointStabilizer_exists_swap_involution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (heven : Even (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    ∃ s : G, s ≠ 1 ∧ s ^ 2 = 1 ∧ s • a = b ∧ s • b = a ∧
      ∃ c : Omega, s • c = c := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Even (Nat.card D) at heven
  obtain ⟨t, htorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 (even_iff_two_dvd.mp heven)
  have htne : t ≠ 1 := by
    intro ht
    subst t
    simp at htorder
  have htsqD : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  let tG : G := ((t : H) : G)
  have htsqG : tG ^ 2 = 1 := by
    simpa [tG] using congrArg (fun x : D => (((x : H) : G))) htsqD
  have htGne : tG ≠ 1 := by
    intro ht
    apply htne
    apply Subtype.ext
    apply Subtype.ext
    exact ht
  have hta : tG • a = a := (t : H).property
  have htb : tG • b = b := by
    simpa [tG, b', Subgroup.smul_def] using
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp t.property)
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot
  let c : Omega := (((z : H) : G) • b)
  have hca : c ≠ a := by
    intro hca
    have hzfixa : (((z : H) : G) • a) = a := (z : H).property
    exact hab (smul_left_cancel (((z : H) : G)) (hzfixa.trans hca.symm))
  have hcb : c ≠ b := by
    intro hcb
    have hzD : (z : H) ∈ D := by
      apply MulAction.mem_stabilizer_iff.mpr
      exact Subtype.ext hcb
    have hzbot : (z : H) ∈ (⊥ : Subgroup H) :=
      hFrob.isComplement'.disjoint.le_bot ⟨z.property, hzD⟩
    apply hz
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hzbot
  have htc : tG • c ≠ c := by
    intro hfix
    exact hat_most_two_fixed_points tG htGne a b c hab hca.symm hcb.symm
      ⟨hta, htb, hfix⟩
  obtain ⟨g, hgc, hgtc⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) htc.symm hab
  let s : G := g * tG * g⁻¹
  have hsa : s • a = b := by
    calc
      s • a = g • (tG • (g⁻¹ • a)) := by simp [s, mul_smul]
      _ = g • (tG • c) := by rw [← hgc, inv_smul_smul]
      _ = b := hgtc
  have hsb : s • b = a := by
    calc
      s • b = g • (tG • (g⁻¹ • b)) := by simp [s, mul_smul]
      _ = g • (tG • (tG • c)) := by rw [← hgtc, inv_smul_smul]
      _ = g • ((tG ^ 2) • c) := by rw [pow_two, mul_smul]
      _ = a := by rw [htsqG, one_smul, hgc]
  have hsne : s ≠ 1 := by
    intro hs
    apply hab
    simpa [hs] using hsa
  have hssq : s ^ 2 = 1 := by
    dsimp [s]
    rw [pow_two]
    calc
      (g * tG * g⁻¹) * (g * tG * g⁻¹) =
          g * (tG ^ 2) * g⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [htsqG]; simp
  have hsfix : s • (g • a) = g • a := by
    simp [s, mul_smul, hta]
  exact ⟨s, hsne, hssq, hsa, hsb, ⟨g • a, hsfix⟩⟩

/-- XI.1.7(a), in left-action order: relative to a point-swap involution,
every `s*f*s` with `f` a nonidentity kernel element has the form
`f₁*s*f₂*d`. -/
public theorem zassenhaus_swap_kernel_bruhat_decomposition
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (s : G) (hssq : s ^ 2 = 1) (hsa : s • a = b) (hsb : s • b = a)
    (f : F) (hf : f ≠ 1) :
    ∃ f₁ f₂ : F,
      ∃ d : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        s * (((f : MulAction.stabilizer G a) : G)) * s =
          (((f₁ : MulAction.stabilizer G a) : G)) * s *
            (((f₂ : MulAction.stabilizer G a) : G)) *
              (((d : MulAction.stabilizer G a) : G)) := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  let : F.Normal := hFrob.normal
  let g : G := s * (((f : H) : G)) * s
  have hgnotH : g ∉ H := by
    intro hgH
    have hgfix : g • a = a := hgH
    have hfb : (((f : H) : G)) • b = b := by
      apply smul_left_cancel s
      calc
        s • ((((f : H) : G)) • b) = g • a := by
          simp [g, mul_smul, hsa]
        _ = a := hgfix
        _ = s • b := hsb.symm
    have hfD : (f : H) ∈ D := by
      apply MulAction.mem_stabilizer_iff.mpr
      exact Subtype.ext hfb
    have hfbot : (f : H) ∈ (⊥ : Subgroup H) :=
      hFrob.isComplement'.disjoint.le_bot ⟨f.property, hfD⟩
    apply hf
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hfbot
  have hs_moves : s • a ≠ a := by simpa [hsa] using hab.symm
  have hcover :=
    huppert_II_1_12_b_doubleCoset_decomposition htwo a s hs_moves
  have hgUnion :
      g ∈ (H : Set G) ∪ DoubleCoset.doubleCoset s H H := by
    rw [hcover]
    exact Set.mem_univ g
  have hgDouble : g ∈ DoubleCoset.doubleCoset s H H :=
    hgUnion.resolve_left hgnotH
  rcases DoubleCoset.mem_doubleCoset.mp hgDouble with
    ⟨h₁, hh₁, h₂, hh₂, hgEq⟩
  let h1 : H := ⟨h₁, hh₁⟩
  let h2 : H := ⟨h₂, hh₂⟩
  obtain ⟨fd1, hfd1, _⟩ := hFrob.isComplement'.existsUnique h1
  obtain ⟨fd2, hfd2, _⟩ := hFrob.isComplement'.existsUnique h2
  let f1 : F := fd1.1
  let d1 : D := fd1.2
  let f2 : F := fd2.1
  let d2 : D := fd2.2
  have hh1Eq : (h1 : G) = ((f1 : H) : G) * ((d1 : H) : G) := by
    exact congrArg Subtype.val hfd1.symm
  have hh2Eq : (h2 : G) = ((f2 : H) : G) * ((d2 : H) : G) := by
    exact congrArg Subtype.val hfd2.symm
  have hd1a : ((d1 : H) : G) • a = a := (d1 : H).property
  have hd1b : ((d1 : H) : G) • b = b := by
    simpa [b', Subgroup.smul_def] using
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp d1.property)
  have hd1sa : (s * ((d1 : H) : G) * s) • a = a := by
    simp [mul_smul, hsa, hsb, hd1b]
  have hd1sb : (s * ((d1 : H) : G) * s) • b = b := by
    simp [mul_smul, hsa, hsb, hd1a]
  let d1sH : H := ⟨s * ((d1 : H) : G) * s, hd1sa⟩
  let d1s : D := ⟨d1sH, by
    apply MulAction.mem_stabilizer_iff.mpr
    exact Subtype.ext hd1sb⟩
  let fmid : F :=
    ⟨(d1s : H) * (f2 : H) * (d1s : H)⁻¹,
      hFrob.normal.conj_mem (f2 : H) f2.property (d1s : H)⟩
  refine ⟨f1, fmid, d1s * d2, ?_⟩
  change g = ((f1 : H) : G) * s * ((fmid : H) : G) *
    (((d1s * d2 : D) : H) : G)
  calc
    g = (h1 : G) * s * (h2 : G) := hgEq
    _ = (((f1 : H) : G) * ((d1 : H) : G)) * s *
        (((f2 : H) : G) * ((d2 : H) : G)) := by rw [hh1Eq, hh2Eq]
    _ = ((f1 : H) : G) * s * ((d1s : H) : G) *
        ((f2 : H) : G) * ((d2 : H) : G) := by
      change _ = ((f1 : H) : G) * s *
        (s * ((d1 : H) : G) * s) * ((f2 : H) : G) * ((d2 : H) : G)
      have hdMove : ((d1 : H) : G) * s =
          s * (s * ((d1 : H) : G) * s) := by
        calc
          ((d1 : H) : G) * s = 1 * (((d1 : H) : G) * s) := by simp
          _ = (s * s) * (((d1 : H) : G) * s) := by
            rw [show s * s = 1 by simpa [pow_two] using hssq]
          _ = s * (s * ((d1 : H) : G) * s) := by group
      calc
        (((f1 : H) : G) * ((d1 : H) : G)) * s *
            (((f2 : H) : G) * ((d2 : H) : G)) =
            ((f1 : H) : G) * (((d1 : H) : G) * s) *
              (((f2 : H) : G) * ((d2 : H) : G)) := by group
        _ = ((f1 : H) : G) * (s * (s * ((d1 : H) : G) * s)) *
              (((f2 : H) : G) * ((d2 : H) : G)) := by rw [hdMove]
        _ = ((f1 : H) : G) * s * (s * ((d1 : H) : G) * s) *
              ((f2 : H) : G) * ((d2 : H) : G) := by group
    _ = ((f1 : H) : G) * s * ((fmid : H) : G) *
        (((d1s * d2 : D) : H) : G) := by
      dsimp [fmid]
      group

/-- XI.1.10(b): an even two-point stabilizer has at least half as many
elements as the punctured Frobenius kernel. -/
private theorem zassenhaus_even_twoPointStabilizer_card_bound
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (heven : Even (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    Nat.card F - 1 ≤ 2 * Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Even (Nat.card D) at heven
  change Nat.card F - 1 ≤ 2 * Nat.card D
  have hFcomm : IsMulCommutative F :=
    frobenius_kernel_commutative_of_even_complement_card F D hFrob heven
  let : IsMulCommutative F := hFcomm
  let : CommGroup F := IsMulCommutative.instCommGroup
  let eAdd : Additive F ≃+ Additive F := AddEquiv.refl (Additive F)
  obtain ⟨ePoint, hPointA, hPointB, hPointF⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
      htwo a b hab F hFrob eAdd
  have hKernelAction :=
    huppert_blackburn_XI_projectivePointEquiv_kernel_action
      a b F eAdd ePoint hPointA hPointF
  obtain ⟨s, hsne, hssq, hsa, hsb, _hsfix⟩ :=
    zassenhaus_even_twoPointStabilizer_exists_swap_involution
      htwo hat_most_two_fixed_points a b hab F hFrob heven
  let tau : Equiv.Perm (Option (Additive F)) :=
    ePoint.symm.trans ((MulAction.toPerm s).trans ePoint)
  have hTau_apply (y : Option (Additive F)) :
      tau y = ePoint (s • ePoint.symm y) := rfl
  have hPointA_symm : ePoint.symm none = a := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointA]
  have hPointB_symm : ePoint.symm (some 0) = b := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointB]
  have hTauInf : tau none = some 0 := by
    rw [hTau_apply, hPointA_symm, hsa, hPointB]
  have hTauZero : tau (some 0) = none := by
    rw [hTau_apply, hPointB_symm, hsb, hPointA]
  have hTauSq (y : Option (Additive F)) : tau (tau y) = y := by
    rw [hTau_apply, hTau_apply, ePoint.symm_apply_apply]
    rw [← mul_smul, ← pow_two, hssq, one_smul, ePoint.apply_symm_apply]
  let dAct (d : D) (x : Additive F) : Additive F :=
    Additive.ofMul
      (⟨(d : H) * (Additive.toMul x : F) * (d : H)⁻¹,
        hFrob.normal.conj_mem
          ((Additive.toMul x : F) : H) (Additive.toMul x : F).property
          (d : H)⟩ : F)
  have hDAction (d : D) (y : Option (Additive F)) :
      ePoint ((((d : H) : G)) • ePoint.symm y) =
        Option.map (dAct d) y := by
    cases y with
    | none =>
        rw [hPointA_symm, (d : H).property, hPointA]
        rfl
    | some x =>
        let fx : F := Additive.toMul x
        let cfx : F :=
          ⟨(d : H) * (fx : H) * (d : H)⁻¹,
            hFrob.normal.conj_mem (fx : H) fx.property (d : H)⟩
        have hPointFx :
            ePoint ((((fx : H) : G)) • b) = some x := by
          simpa [fx, eAdd] using hPointF fx
        have hPointFxSymm :
            ePoint.symm (some x) = (((fx : H) : G)) • b := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hPointFx]
        have hdb : (((d : H) : G)) • b = b := by
          simpa [b', Subgroup.smul_def] using
            congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp d.property)
        calc
          ePoint ((((d : H) : G)) • ePoint.symm (some x)) =
              ePoint ((((d : H) : G)) • ((((fx : H) : G)) • b)) := by
                rw [hPointFxSymm]
          _ = ePoint (((((d : H) : G)) * (((fx : H) : G))) • b) := by
                rw [mul_smul]
          _ = ePoint (((((cfx : H) : G)) * (((d : H) : G))) • b) := by
                congr 2
                dsimp [cfx]
                group
          _ = ePoint ((((cfx : H) : G)) • ((((d : H) : G)) • b)) := by
                rw [mul_smul]
          _ = ePoint ((((cfx : H) : G)) • b) := by rw [hdb]
          _ = some (dAct d x) := by
                simpa [cfx, dAct, fx, eAdd] using hPointF cfx
  have hDZero (d : D) : dAct d 0 = 0 := by
    apply Additive.toMul.injective
    dsimp [dAct]
    simp
  have hDNeg (d : D) (x : Additive F) : dAct d (-x) = -(dAct d x) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    dsimp [dAct]
    group
  obtain ⟨t, htorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 (even_iff_two_dvd.mp heven)
  have htne : t ≠ 1 := by
    intro ht
    subst t
    simp at htorder
  have htsqD : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  let tG : G := ((t : H) : G)
  have htsqG : tG ^ 2 = 1 := by
    simpa [tG] using congrArg (fun x : D => (((x : H) : G))) htsqD
  have hta : tG • a = a := (t : H).property
  have htb : tG • b = b := by
    simpa [tG, b', Subgroup.smul_def] using
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp t.property)
  have htsa : (s * tG * s) • a = a := by
    simp [mul_smul, hsa, hsb, htb]
  have htsb : (s * tG * s) • b = b := by
    simp [mul_smul, hsa, hsb, hta]
  let tsH : H := ⟨s * tG * s, htsa⟩
  let ts : D := ⟨tsH, by
    apply MulAction.mem_stabilizer_iff.mpr
    exact Subtype.ext htsb⟩
  have htssq : ts ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (s * tG * s) ^ 2 = 1
    rw [pow_two]
    calc
      (s * tG * s) * (s * tG * s) = s * (tG ^ 2) * s := by
        have hss : s * s = 1 := by simpa [pow_two] using hssq
        rw [show (s * tG * s) * (s * tG * s) =
          s * tG * (s * s) * tG * s by group, hss]
        simp [pow_two, mul_assoc]
      _ = 1 := by rw [htsqG]; simpa [pow_two] using hssq
  have htsne : ts ≠ 1 := by
    intro hts
    apply htne
    apply Subtype.ext
    apply Subtype.ext
    have htsG := congrArg (fun x : D => (((x : H) : G))) hts
    change s * tG * s = 1 at htsG
    have hss : s * s = 1 := by simpa [pow_two] using hssq
    change tG = 1
    have hrecover : s * (s * tG * s) * s = tG := by
      calc
        s * (s * tG * s) * s = (s * s) * tG * (s * s) := by group
        _ = tG := by rw [hss]; simp
    calc
      tG = s * (s * tG * s) * s := hrecover.symm
      _ = s * 1 * s := by rw [htsG]
      _ = 1 := by simpa [mul_assoc] using hss
  have htsorder : orderOf ts = 2 := orderOf_eq_prime htssq htsne
  have htseq : ts = t :=
    frobenius_complement_involutions_eq F D hFrob ts t htsorder htorder
  have hstcomm : s * tG = tG * s := by
    have hconj := congrArg (fun x : D => (((x : H) : G))) htseq
    change s * tG * s = tG at hconj
    have hss : s * s = 1 := by simpa [pow_two] using hssq
    have hmove : (s * tG * s) * s = s * tG := by
      calc
        (s * tG * s) * s = s * tG * (s * s) := by group
        _ = s * tG := by rw [hss]; simp
    calc
      s * tG = (s * tG * s) * s := hmove.symm
      _ = tG * s := by rw [hconj]
  have htConjInv (x : F) :
      (t : H) * (x : H) * (t : H)⁻¹ = (x⁻¹ : F) := by
    let : F.Normal := hFrob.normal
    let phi : MulAut F := MulAut.conjNormal (H := F) (t : H)
    have hphi_sq : phi ^ 2 = 1 := by
      change (MulAut.conjNormal (H := F) (t : H)) ^ 2 = 1
      have htsqH : (t : H) ^ 2 = 1 := by
        simpa using congrArg Subtype.val htsqD
      rw [← map_pow, htsqH, map_one]
    have hphi_involutive : Function.Involutive phi := by
      intro x
      have hx := congrArg (fun psi : MulAut F => psi x) hphi_sq
      simpa [pow_two] using hx
    have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
      intro x hx
      have hxconj :
          (t : H) * (x : H) * (t : H)⁻¹ = (x : H) := by
        simpa [phi] using congrArg Subtype.val hx
      have hxcomm : (t : H) * (x : H) = (x : H) * (t : H) := by
        have := congrArg (fun z : H => z * (t : H)) hxconj
        simpa [mul_assoc] using this
      have hxcent : (x : H) ∈ elementCentralizerIn F (t : H) :=
        ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hxcomm.symm⟩
      have hcent : elementCentralizerIn F (t : H) = ⊥ :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob t htne
      have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
        simpa [hcent] using hxcent
      exact Subtype.ext (by simpa using hxbot)
    have hinv := hphi_fixedPointFree.coe_eq_inv_of_involutive hphi_involutive
    simpa [phi] using congrArg Subtype.val (congrFun hinv x)
  have hDActT (x : Additive F) : dAct t x = -x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa [dAct] using htConjInv (Additive.toMul x)
  have htPoint (y : Option (Additive F)) :
      ePoint.symm (Option.map (fun x => -x) y) =
        tG • ePoint.symm y := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply]
    rw [hDAction]
    cases y <;> simp [hDActT]
  have hTauNeg (y : Option (Additive F)) :
      tau (Option.map (fun x => -x) y) =
        Option.map (fun x => -x) (tau y) := by
    have hTauPoint : ePoint.symm (tau y) = s • ePoint.symm y := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hTau_apply]
    calc
      tau (Option.map (fun x => -x) y) =
          ePoint (s • ePoint.symm (Option.map (fun x => -x) y)) :=
            hTau_apply _
      _ = ePoint (s • (tG • ePoint.symm y)) := by rw [htPoint]
      _ = ePoint ((s * tG) • ePoint.symm y) := by rw [mul_smul]
      _ = ePoint ((tG * s) • ePoint.symm y) := by rw [hstcomm]
      _ = ePoint (tG • (s • ePoint.symm y)) := by rw [mul_smul]
      _ = ePoint (tG • ePoint.symm (tau y)) := by rw [hTauPoint]
      _ = Option.map (fun x => -x) (tau y) := by
        rw [hDAction]
        cases tau y <;> simp [hDActT]
  let F0 := {f : F // f ≠ 1}
  have hBruhat : ∀ x : F0, ∃ f1 f2 : F, ∃ d : D,
      s * (((x.1 : F) : H) : G) * s =
        (((f1 : H) : G)) * s * (((f2 : H) : G)) * (((d : H) : G)) := by
    intro x
    have hmem : ∀ (g : H), g ∈ D ↔ (g : G) • b = b := by
      intro g
      have hD_def : D = MulAction.stabilizer H (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) := rfl
      rw [hD_def]
      constructor
      · intro hg
        have hg' := MulAction.mem_stabilizer_iff.mp hg
        apply_fun Subtype.val at hg'
        simpa [Subgroup.smul_def] using hg'
      · intro hg
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        simpa [Subgroup.smul_def] using hg
    rcases zassenhaus_swap_kernel_bruhat_decomposition
      htwo a b hab F hFrob s hssq hsa hsb x.1 x.2 with ⟨f1, f2, d, h⟩
    refine ⟨f1, f2, d, ?_⟩
    simpa [H] using h
  choose f1 f2 d hdecomp using hBruhat
  let k (x : F0) : Additive F := Additive.ofMul x.1
  let ell (x : F0) : Additive F := Additive.ofMul (f1 x)
  let m (x : F0) : Additive F := Additive.ofMul (f2 x)
  have hTauPoint' (z : Option (Additive F)) :
      ePoint.symm (tau z) = s • ePoint.symm z := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hTau_apply]
  have hKernelPoint (f : F) (z : Option (Additive F)) :
      ePoint.symm
          (Option.map (fun w => Additive.ofMul f + w) z) =
        (((f : H) : G)) • ePoint.symm z := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply]
    simpa [eAdd] using (hKernelAction f z).symm
  have hDPoint (q : D) (z : Option (Additive F)) :
      ePoint.symm (Option.map (dAct q) z) =
        (((q : H) : G)) • ePoint.symm z := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hDAction]
  have hCoordEq (x : F0) (z : Option (Additive F)) :
      tau (Option.map (fun w => k x + w) (tau z)) =
        Option.map (fun w => ell x + w)
          (tau (Option.map (fun w => m x + w)
            (Option.map (dAct (d x)) z))) := by
    apply ePoint.symm.injective
    rw [hTauPoint', hKernelPoint, hTauPoint', hKernelPoint,
      hTauPoint', hKernelPoint, hDPoint]
    simp only [← mul_smul]
    simpa [mul_assoc] using
      congrArg (fun q : G => q • ePoint.symm z) (hdecomp x)
  have hTauK (x : F0) : tau (some (k x)) = some (ell x) := by
    have hx := hCoordEq x none
    simpa [hTauInf] using hx
  have hTauM (x : F0) : tau (some (m x)) = some (-(ell x)) := by
    have hx := hCoordEq x (some 0)
    simp only [hTauZero, Option.map_none, hTauInf, Option.map_some,
      hDZero, add_zero] at hx
    cases hm : tau (some (m x)) with
    | none => simp [hm] at hx
    | some z =>
        have hz : 0 = ell x + z := Option.some.inj (by simpa [hm] using hx)
        have hzeq : z = -(ell x) := by
          exact eq_neg_of_add_eq_zero_right hz.symm
        simp [hzeq]
  have hMeq (x : F0) : m x = -(k x) := by
    have hTauNegK : tau (some (-(k x))) = some (-(ell x)) := by
      simpa [hTauK] using hTauNeg (some (k x))
    exact Option.some.inj (tau.injective ((hTauM x).trans hTauNegK.symm))
  have hFunc (x : F0) (z : Option (Additive F)) :
      tau (Option.map (fun w => k x + w) (tau z)) =
        Option.map (fun w => ell x + w)
          (tau (Option.map (fun w => -(k x) + w)
            (Option.map (dAct (d x)) z))) := by
    simpa [hMeq] using hCoordEq x z
  have hTauEll (x : F0) : tau (some (ell x)) = some (k x) := by
    calc
      tau (some (ell x)) = tau (tau (some (k x))) := by rw [hTauK]
      _ = some (k x) := hTauSq _
  have hLeadAction (x : F0) : dAct (d x) (ell x) = -(k x) := by
    have hTauNegEll : tau (some (-(ell x))) = some (-(k x)) := by
      simpa [hTauEll] using hTauNeg (some (ell x))
    have hx := hFunc x (some (-(ell x)))
    have hnone :
        Option.map (fun w => ell x + w)
            (tau (some (-(k x) + dAct (d x) (-(ell x))))) = none := by
      simpa [hTauNegEll, hTauZero] using hx.symm
    have hinner :
        tau (some (-(k x) + dAct (d x) (-(ell x)))) = none := by
      cases hopt : tau (some (-(k x) + dAct (d x) (-(ell x)))) with
      | none => rfl
      | some z => simp [hopt] at hnone
    have harg : -(k x) + dAct (d x) (-(ell x)) = 0 := by
      exact Option.some.inj
        (tau.injective (hinner.trans hTauZero.symm))
    rw [hDNeg] at harg
    have hk : k x = -(dAct (d x) (ell x)) := neg_add_eq_zero.mp harg
    simpa using (congrArg (fun z : Additive F => -z) hk).symm
  have hParamFiber : ∀ x y : F0, d x = d y →
      y.1 = x.1 ∨ y.1 = x.1⁻¹ := by
    intro x y hdxy
    have hActY : dAct (d x) (ell y) = -(k y) := by
      rw [hdxy]
      exact hLeadAction y
    have hActX : dAct (d y) (ell x) = -(k x) := by
      rw [← hdxy]
      exact hLeadAction x
    have hx := hFunc x (some (ell y))
    have hy := hFunc y (some (ell x))
    have hx' :
        tau (some (k x + k y)) =
          Option.map (fun w => ell x + w)
            (tau (some (-(k x) + -(k y)))) := by
      simpa [hTauEll, hActY] using hx
    have hy' :
        tau (some (k y + k x)) =
          Option.map (fun w => ell y + w)
            (tau (some (-(k y) + -(k x)))) := by
      simpa [hTauEll, hActX] using hy
    have hrhs :
        Option.map (fun w => ell x + w)
            (tau (some (-(k x) + -(k y)))) =
          Option.map (fun w => ell y + w)
            (tau (some (-(k x) + -(k y)))) := by
      exact hx'.symm.trans (by simpa [add_comm] using hy')
    cases hopt : tau (some (-(k x) + -(k y))) with
    | none =>
        right
        have hsum : -(k x) + -(k y) = 0 := by
          exact Option.some.inj
            (tau.injective (hopt.trans hTauZero.symm))
        have hkxy : k x = -(k y) := neg_add_eq_zero.mp hsum
        have hkyx : k y = -(k x) := by
          simpa using (congrArg (fun z : Additive F => -z) hkxy).symm
        exact congrArg Additive.toMul hkyx
    | some z =>
        left
        have hell : ell x = ell y := by
          have hadd : ell x + z = ell y + z :=
            Option.some.inj (by simpa [hopt] using hrhs)
          exact add_right_cancel hadd
        have hkxy : k x = k y := by
          have htau : tau (some (k x)) = tau (some (k y)) := by
            rw [hTauK, hTauK, hell]
          exact Option.some.inj (tau.injective htau)
        exact (congrArg Additive.toMul hkxy).symm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype D := Fintype.ofFinite D
  let : Fintype F0 := Fintype.ofFinite F0
  have hFiberCard : ∀ q ∈ (Finset.univ : Finset F0).image d,
      ({x ∈ (Finset.univ : Finset F0) | d x = q}).card ≤ 2 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, _hx, hdx⟩
    let xinv : F0 := ⟨x.1⁻¹, by
      intro hinv
      apply x.2
      have := congrArg (fun z : F => z⁻¹) hinv
      simpa using this⟩
    have hsub : {y ∈ (Finset.univ : Finset F0) | d y = q} ⊆ {x, xinv} := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hdyx : d y = d x := hy.trans hdx.symm
      rcases hParamFiber x y hdyx.symm with hval | hval
      · have hyx : y = x := Subtype.ext hval
        simp [hyx]
      · have hyinv : y = xinv := Subtype.ext hval
        simp [hyinv]
    calc
      ({y ∈ (Finset.univ : Finset F0) | d y = q}).card ≤
          ({x, xinv} : Finset F0).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hDomainLe : Fintype.card F0 ≤ 2 * Fintype.card D := by
    calc
      Fintype.card F0 = (Finset.univ : Finset F0).card := by
        rw [Finset.card_univ]
      _ ≤ 2 * ((Finset.univ : Finset F0).image d).card :=
        Finset.card_le_mul_card_image _ 2 hFiberCard
      _ ≤ 2 * (Finset.univ : Finset D).card := by
        exact Nat.mul_le_mul_left 2
          (Finset.card_le_card (by intro q hq; simp))
      _ = 2 * Fintype.card D := by rw [Finset.card_univ]
  have hCardF0 : Nat.card F0 = Nat.card F - 1 := by
    change Nat.card {f : F // f ≠ 1} = Nat.card F - 1
    simp only [Nat.card_eq_fintype_card]
    simp only [Fintype.card_subtype_compl (p := fun f : F => f = 1)]
    simp
  calc
    Nat.card F - 1 = Nat.card F0 := hCardF0.symm
    _ = Fintype.card F0 := Nat.card_eq_fintype_card
    _ ≤ 2 * Fintype.card D := hDomainLe
    _ = 2 * Nat.card D := by rw [Nat.card_eq_fintype_card]

/-- Pointwise stabilizers of ordered pairs have the same cardinality in a
doubly transitive action. -/
public theorem zassenhaus_twoPointStabilizer_card_eq
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b x y : Omega) (hab : a ≠ b) (hxy : x ≠ y) :
    Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G x)
          (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x)) =
      Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  classical
  obtain ⟨g, hgx, hgy⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hxy hab
  let Dx := MulAction.stabilizer (MulAction.stabilizer G x)
    (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x)
  let Da := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let e : Dx ≃* Da := {
    toFun d := by
      let z : G := g * (((d : MulAction.stabilizer G x) : G)) * g⁻¹
      have hza : z • a = a := by
        calc
          z • a = g • ((((d : MulAction.stabilizer G x) : G)) •
              (g⁻¹ • a)) := by simp [z, mul_smul]
          _ = g • ((((d : MulAction.stabilizer G x) : G)) • x) := by
            rw [← hgx, inv_smul_smul]
          _ = g • x := by rw [(d : MulAction.stabilizer G x).property]
          _ = a := hgx
      have hzy : (((d : MulAction.stabilizer G x) : G)) • y = y := by
        simpa [Subgroup.smul_def] using congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp d.property)
      have hzb : z • b = b := by
        calc
          z • b = g • ((((d : MulAction.stabilizer G x) : G)) •
              (g⁻¹ • b)) := by simp [z, mul_smul]
          _ = g • ((((d : MulAction.stabilizer G x) : G)) • y) := by
            rw [← hgy, inv_smul_smul]
          _ = g • y := by rw [hzy]
          _ = b := hgy
      exact ⟨⟨z, hza⟩, by
        apply MulAction.mem_stabilizer_iff.mpr
        exact Subtype.ext hzb⟩
    invFun d := by
      let z : G := g⁻¹ * (((d : MulAction.stabilizer G a) : G)) * g
      have hzx : z • x = x := by
        calc
          z • x = g⁻¹ • ((((d : MulAction.stabilizer G a) : G)) •
              (g • x)) := by simp [z, mul_smul]
          _ = g⁻¹ • ((((d : MulAction.stabilizer G a) : G)) • a) := by rw [hgx]
          _ = g⁻¹ • a := by rw [(d : MulAction.stabilizer G a).property]
          _ = x := by rw [← hgx, inv_smul_smul]
      have hdb : (((d : MulAction.stabilizer G a) : G)) • b = b := by
        simpa [Subgroup.smul_def] using congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp d.property)
      have hzy : z • y = y := by
        calc
          z • y = g⁻¹ • ((((d : MulAction.stabilizer G a) : G)) •
              (g • y)) := by simp [z, mul_smul]
          _ = g⁻¹ • ((((d : MulAction.stabilizer G a) : G)) • b) := by rw [hgy]
          _ = g⁻¹ • b := by rw [hdb]
          _ = y := by rw [← hgy, inv_smul_smul]
      exact ⟨⟨z, hzx⟩, by
        apply MulAction.mem_stabilizer_iff.mpr
        exact Subtype.ext hzy⟩
    left_inv d := by
      apply Subtype.ext
      apply Subtype.ext
      change g⁻¹ * (g * (((d : Dx) : MulAction.stabilizer G x) : G) * g⁻¹) * g =
        (((d : Dx) : MulAction.stabilizer G x) : G)
      group
    right_inv d := by
      apply Subtype.ext
      apply Subtype.ext
      change g * (g⁻¹ * (((d : Da) : MulAction.stabilizer G a) : G) * g) * g⁻¹ =
        (((d : Da) : MulAction.stabilizer G a) : G)
      group
    map_mul' d₁ d₂ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
  }
  exact Nat.card_congr e.toEquiv

public theorem huppert_XI_6_1_action_parameters
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    Fintype.card Omega = Nat.card F + 1 ∧
      Nat.card (MulAction.stabilizer G a) =
        Nat.card F * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card G = Fintype.card Omega * Nat.card F * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣
        Nat.card F - 1 := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change Fintype.card Omega = Nat.card F + 1 ∧
    Nat.card H = Nat.card F * Nat.card D ∧
    Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D ∧
    Nat.card D ∣ Nat.card F - 1
  have hOmegaCard : 1 < Fintype.card Omega :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  let n := Fintype.card Omega - 1
  have hdegree : Fintype.card Omega = n + 1 := by
    dsimp [n]
    omega
  have hFcard : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo a b hab F hFrob
  have hOmegaEq : Fintype.card Omega = Nat.card F + 1 := by
    rw [hFcard, ← hdegree]
  have hHcard : Nat.card H = Nat.card F * Nat.card D := by
    exact hFrob.isComplement'.card_mul_card.symm
  have hGcard : Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D := by
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex : H.index = Fintype.card Omega := by
      calc
        H.index = Nat.card Omega := MulAction.index_stabilizer_of_transitive G a
        _ = Fintype.card Omega := Nat.card_eq_fintype_card
    have hmul := H.card_mul_index
    rw [hindex] at hmul
    calc
      Nat.card G = Nat.card H * Fintype.card Omega := hmul.symm
      _ = Fintype.card Omega * Nat.card F * Nat.card D := by
        rw [hHcard]
        ac_rfl
  have hdiv : Nat.card D ∣ Nat.card F - 1 := by
    let : F.Normal := hFrob.normal
    let : MulDistribMulAction D F :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer D F
        (Subgroup.le_normalizer_of_normal (H := F))
    apply huppert_XI_6_1_actor_card_dvd_group_card_sub_one
    intro d hd f hfix
    have hconj : (d : H) * (f : H) * (d : H)⁻¹ = (f : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (d : H) * (f : H) = (f : H) * (d : H) := by
      have h := congrArg (fun x : H => x * (d : H)) hconj
      simpa [mul_assoc] using h
    have hfcent : (f : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨f.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hfbot : (f : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hfcent
    exact Subtype.ext (by simpa using hfbot)
  exact ⟨hOmegaEq, hHcard, hGcard, hdiv⟩

/-- XI.6.3(a), arithmetic core: the lower-degree square sum is already
strictly larger than `2*d*z` once it reaches `4*d^2`. -/
private theorem huppert_XI_6_3_large_lower_sum
    (A d z : ℕ) (hd : 1 < d) (hz : 1 < z) (hcop : Nat.Coprime z d)
    (hlarge : 4 * d ^ 2 ≤ A) (hzsq : z ^ 2 ≤ A + 1) :
    2 * d * z < A := by
  have htwoDSq : (2 * d) ^ 2 ≤ A := by
    calc
      (2 * d) ^ 2 = 4 * d ^ 2 := by ring
      _ ≤ A := hlarge
  have hfour : 4 * d * z ≤ 2 * A + 1 := by
    calc
      4 * d * z = 2 * (2 * d) * z := by ring
      _ ≤ (2 * d) ^ 2 + z ^ 2 := two_mul_le_add_sq (2 * d) z
      _ ≤ A + (A + 1) := Nat.add_le_add htwoDSq hzsq
      _ = 2 * A + 1 := by ring
  have htwo : 2 * d * z ≤ A := by
    have hfourEq : 4 * d * z = 2 * (2 * d * z) := by ring
    rw [hfourEq] at hfour
    omega
  apply lt_of_le_of_ne htwo
  intro hEq
  have hAeq : A = 2 * d * z := hEq.symm
  have hzge : 2 * d ≤ z := by
    rw [hAeq] at hlarge
    nlinarith
  have hzNe : z ≠ 2 * d := by
    intro hzEq
    have hdvd : d ∣ z := by
      rw [hzEq]
      exact dvd_mul_left d 2
    have hdOne : d = 1 := hcop.symm.eq_one_of_dvd hdvd
    omega
  have hzgt : 2 * d < z := lt_of_le_of_ne hzge hzNe.symm
  rw [hAeq] at hzsq
  nlinarith

/-- XI.6.3(b), odd-Sylow nonlinear component. -/
private theorem huppert_XI_6_3_odd_component_lower_sum
    (A d z S L : ℕ) (hz : 3 ≤ z)
    (hS : z ^ 2 - 1 ≤ S) (hL : d + 1 ≤ L) (hA : S * L ≤ A) :
    2 * d * z < A := by
  have hzsq : z ^ 2 - 1 + 1 = z ^ 2 :=
    Nat.sub_add_cancel (Nat.one_le_pow 2 z (by omega))
  have hzineq : 2 * z < z ^ 2 - 1 := by nlinarith
  nlinarith

/-- XI.6.3(b), nonlinear 2-Sylow component. -/
private theorem huppert_XI_6_3_two_component_lower_sum
    (A d z S L : ℕ) (hz : 2 ≤ z)
    (hS : z ^ 2 - 1 ≤ S) (hL : 2 * d + 1 ≤ L)
    (hA : S * L ≤ A) : 2 * d * z < A := by
  have hzsq : z ^ 2 - 1 + 1 = z ^ 2 :=
    Nat.sub_add_cancel (Nat.one_le_pow 2 z (by omega))
  have hzineq : z ≤ z ^ 2 - 1 := by nlinarith
  nlinarith

/-- XI.6.3(b), both Sylow character factors nonlinear. -/
private theorem huppert_XI_6_3_two_nonlinear_components_impossible
    (A d z : ℕ) (hz : 1 < z)
    (hlinear : 2 * d ^ 2 ≤ A) (hupper : A ≤ 2 * d * z)
    (hthree : 3 * z ^ 2 ≤ A + 1) : False := by
  nlinarith

/-- A degree-one irreducible character is trivial on the commutator subgroup. -/
private theorem huppert_XI_6_3_subgroupInKernel_commutator_of_degree_one
    {Q : Type u} [Group Q] [Finite Q]
    {theta : Section1.ClassFunction Q}
    (htheta : Section1.IsIrreducibleCharacterOnGroup theta)
    (hdegree : Section1.degree theta = 1) :
    Section1.subgroupInKernel' theta (_root_.commutator Q) := by
  classical
  rcases htheta with ⟨n, rho, _hrhoIrr, hthetaEq⟩
  have hnCast : (n : ℂ) = 1 := by
    simpa [hthetaEq, Section1.degree_representation_character rho] using hdegree
  have hn : n = 1 := by
    exact_mod_cast hnCast
  subst n
  have hscalar :
      ∀ g : Q, ∃ a : ℂ, ∀ v : Fin 1 → ℂ, rho g v = a • v := by
    intro g
    obtain ⟨a, ha, _haUnique⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
        (R := ℂ) (M := Fin 1 → ℂ) (by simp) (rho g)
    refine ⟨a, ?_⟩
    intro v
    simpa using congrArg (fun f : Module.End ℂ (Fin 1 → ℂ) => f v) ha
  have hcommUnits :
      _root_.commutator Q ≤ (Representation.asGroupHom rho).ker := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro g _hg h _hh
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    apply Units.ext
    apply LinearMap.ext
    intro v
    change rho g (rho h v) = rho h (rho g v)
    obtain ⟨a, ha⟩ := hscalar g
    obtain ⟨b, hb⟩ := hscalar h
    calc
      rho g (rho h v) = rho g (b • v) := by rw [hb]
      _ = b • rho g v := by simp
      _ = b • (a • v) := by rw [ha]
      _ = a • (b • v) := by simp [smul_smul, mul_comm]
      _ = a • rho h v := by rw [hb]
      _ = rho h (a • v) := by simp
      _ = rho h (rho g v) := by rw [ha]
  have hker :
      Section1.subgroupInRepresentationKernel rho (_root_.commutator Q) := by
    intro x
    have hx := hcommUnits x.property
    have hxUnits :
        Representation.asGroupHom rho (x : Q) = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxEnd := congrArg
      (fun y : Units (Module.End ℂ (Fin 1 → ℂ)) =>
        (y : Module.End ℂ (Fin 1 → ℂ))) hxUnits
    simpa [Representation.asGroupHom_apply] using hxEnd
  simpa [hthetaEq] using
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho (_root_.commutator Q)).mpr hker
/-- XI.6.3 in the form consumed by the coherence induction: the nonprincipal
lower-degree square sum for every nonlinear irreducible character of the
nilpotent Frobenius kernel is strictly larger than 2*d*z. -/
private theorem huppert_XI_6_3_nilpotent_degree_growth
    {D Q : Type u} [Group D] [Finite D] [Group Q] [Finite Q]
    [MulDistribMulAction D Q] [Nontrivial Q]
    (hnil : Group.IsNilpotent Q)
    (hnotPrimePower : ¬ IsPrimePow (Nat.card Q))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hfree : ∀ d : D, d ≠ 1 → ∀ x : Q, d • x = x → x = 1)
    (hoddD : Odd (Nat.card D))
    (hd : 1 < Nat.card D)
    (theta : Section1.ClassFunction Q)
    (htheta : Section1.IsIrreducibleCharacterOnGroup theta)
    (z : ℕ) (hz : 1 < z)
    (hthetaDegree : Section1.degree theta = (z : ℂ))
    (K : Finset (Section1.ClassFunction Q))
    (hKcomplete : ∀ chi : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup chi → chi ∈ K)
    (degreeNat : Section1.ClassFunction Q → ℕ)
    (hdegree : ∀ chi : K,
      Section1.degree (chi : Section1.ClassFunction Q) =
        (degreeNat chi : ℂ)) :
    2 * Nat.card D * z + 1 <
      ∑ chi ∈ K.filter (fun chi => degreeNat chi < z),
        degreeNat chi ^ 2 := by
  classical
  let C :=
    ∑ chi ∈ K.filter (fun chi => degreeNat chi < z),
      degreeNat chi ^ 2
  let A := C - 1
  obtain ⟨c, _hcPos, hcDegree, hcDvd⟩ :=
    huppert_XI_6_positive_degree_nat htheta
  have hzc : z = c := by
    have hcast : (z : ℂ) = (c : ℂ) := by
      rw [← hthetaDegree, hcDegree]
    exact_mod_cast hcast
  have hzDvd : z ∣ Nat.card Q := by simpa [hzc] using hcDvd
  have hcopZD : Nat.Coprime z (Nat.card D) :=
    Nat.Coprime.of_dvd_left hzDvd hcop.symm
  obtain ⟨I0, hI0Fintype, lower0, lowerDegree0, hlower0Inj,
      hlower0Irr, hlower0Degree, hlower0Lt, hlower0Sq⟩ :=
    huppert_XI_6_3_nilpotent_lower_family
      hnil theta htheta z hz hthetaDegree
  let : Fintype I0 := hI0Fintype
  have hlowerComplete :
      z ^ 2 ≤ ∑ chi ∈ K.filter (fun chi => degreeNat chi < z),
        degreeNat chi ^ 2 :=
    huppert_XI_6_3_injective_family_bound_le_complete_lower_sum
      (I := I0) K hKcomplete degreeNat hdegree
      (z ^ 2) z lower0 lowerDegree0 hlower0Inj hlower0Irr
      hlower0Degree hlower0Lt hlower0Sq
  have hCpos : 0 < C := by
    have hzPos : 0 < z ^ 2 := by positivity
    exact lt_of_lt_of_le hzPos (by simpa [C] using hlowerComplete)
  have hCA : C = A + 1 := by
    dsimp [A]
    exact (Nat.sub_add_cancel hCpos).symm
  suffices hAGrowth : 2 * Nat.card D * z < A by
    have hbound : 2 * Nat.card D * z + 1 ≤ A := by omega
    have hstrict : A < A + 1 := Nat.lt_succ_self A
    change 2 * Nat.card D * z + 1 < C
    rw [hCA]
    exact lt_of_le_of_lt hbound hstrict
  have hzSq :
      z ^ 2 ≤ A + 1 := by
    rw [← hCA]
    simpa [C] using hlowerComplete
  by_cases hlarge : 4 * Nat.card D ^ 2 ≤ A
  · exact huppert_XI_6_3_large_lower_sum
      A (Nat.card D) z hd hz hcopZD hlarge hzSq
  · have hsmallA : A < 4 * Nat.card D ^ 2 :=
      Nat.lt_of_not_ge hlarge
    have hAb :
        Nat.card (Abelianization Q) ≤ A + 1 := by
      rw [← hCA]
      simpa [C] using
        huppert_XI_6_3_abelianization_card_le_complete_lower_sum
          K hKcomplete degreeNat hdegree z hz
    have hlinear : 2 * Nat.card D ^ 2 ≤ A :=
      huppert_XI_6_3_mixed_prime_nonprincipal_linear_lower
        hnil hnotPrimePower hcop hfree hoddD A hAb hsmallA
    by_contra hnotGrowth
    have hupper : A ≤ 2 * Nat.card D * z :=
      Nat.le_of_not_gt hnotGrowth
    obtain ⟨p, hp, hpDvdZ⟩ := Nat.exists_prime_and_dvd hz.ne'
    obtain ⟨e, chi, psi, a, b, hchi, hpsi, _hfactor,
        haPos, hbPos, hachi, hbpsi, _haDvd, hbDvd, hthetaDegreeAB⟩ :=
      huppert_XI_6_3_nilpotent_character_factor p hp hnil theta htheta
    have hab : a * b = z := by
      have hcast : ((a * b : ℕ) : ℂ) = (z : ℂ) := by
        rw [← hthetaDegreeAB, hthetaDegree]
      exact_mod_cast hcast
    have ha : 1 < a := by
      apply huppert_XI_6_3_pcore_factor_degree_gt_one
        p a b hp haPos hbDvd
      rw [hab]
      exact hpDvdZ
    obtain ⟨ι, hι, rho, rhoDegree, hrho, hvalue, hlowerA⟩ :=
      huppert_XI_6_3_pcore_lower_degree_family
        p a hp chi hchi hachi ha
    let : Fintype ι := hι
    by_cases hbOne : b = 1
    · have haEqZ : a = z := by
        simpa [hbOne] using hab
      have hpDvdQ : p ∣ Nat.card Q := hpDvdZ.trans hzDvd
      have hcardQ : 1 < Nat.card Q :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have hnotPow : ∀ n, Nat.card Q ≠ p ^ n := by
        intro n hn
        by_cases hn0 : n = 0
        · subst n
          exact (Nat.ne_of_gt hcardQ) (by simpa using hn)
        · apply hnotPrimePower
          exact (isPrimePow_nat_iff (Nat.card Q)).2
            ⟨p, n, hp, Nat.pos_of_ne_zero hn0, hn.symm⟩
      obtain ⟨q, hq, hqDvdQ, hqNeP⟩ :=
        hkt_exists_prime_dvd_ne_of_not_prime_power
          Nat.card_pos.ne' hnotPow
      have hcompLower :=
        huppert_XI_6_3_pPrimeCore_abelianization_lower
          (D := D) (Q := Q) p q hp hq hqNeP.symm hnil hqDvdQ
          hcop hfree hoddD
      let L := Nat.card (Abelianization (pPrimeCore p Q))
      have hfull :
          z ^ 2 * L ≤ A + 1 := by
        have hfamily :=
          huppert_XI_6_3_linear_component_le_complete_lower_sum
            p a e rho rhoDegree hrho hvalue hlowerA
            K hKcomplete degreeNat hdegree
        rw [haEqZ] at hfamily
        calc
          z ^ 2 * L ≤
              ∑ phi ∈ K.filter (fun phi => degreeNat phi < z),
                degreeNat phi ^ 2 := by
            simpa [L] using hfamily
          _ = A + 1 := by
            simpa [C] using hCA
      let S := z ^ 2 - 1
      have hS : S + 1 = z ^ 2 := by
        dsimp [S]
        exact Nat.sub_add_cancel (Nat.one_le_pow 2 z (by omega))
      have hAprod : S * L ≤ A := by
        have hfull' := hfull
        rw [← hS, add_mul, one_mul] at hfull'
        omega
      by_cases hpTwo : p = 2
      · have hqTwo : q ≠ 2 := by
          intro hqEq
          apply hqNeP
          omega
        have hL : 2 * Nat.card D + 1 ≤ L := by
          simpa [L] using hcompLower.2 hqTwo
        have hgt :=
          huppert_XI_6_3_two_component_lower_sum
            A (Nat.card D) z S L (by omega) (by exact le_rfl) hL hAprod
        exact hnotGrowth hgt
      · have hpThree : 3 ≤ p := by
          have hpTwoLe := hp.two_le
          omega
        have hpLeZ : p ≤ z :=
          Nat.le_of_dvd (by omega) hpDvdZ
        have hzThree : 3 ≤ z := hpThree.trans hpLeZ
        have hL : Nat.card D + 1 ≤ L := by
          simpa [L] using hcompLower.1
        have hgt :=
          huppert_XI_6_3_odd_component_lower_sum
            A (Nat.card D) z S L hzThree (by exact le_rfl) hL hAprod
        exact hnotGrowth hgt
    · have hb : 1 < b := by omega
      let : Fact p.Prime := ⟨hp⟩
      let R := pPrimeCore p Q
      let : Group.IsNilpotent Q := hnil
      have hnilR : Group.IsNilpotent R := by infer_instance
      obtain ⟨J, hJFintype, lowerB, degreeB, hlowerBInj,
          hlowerBIrr, hlowerBDegree, hlowerBLt, hlowerBSq⟩ :=
        huppert_XI_6_3_nilpotent_lower_family
          hnilR psi hpsi b hb hbpsi
      let : Fintype J := hJFintype
      let lowerASet : Finset ι :=
        Finset.univ.filter (fun i => rhoDegree i < a)
      let IA := {i : ι // i ∈ lowerASet}
      let lowerA : IA → Section1.ClassFunction (pCore p Q) := fun i =>
        Section1.ofConjClassFunction (rho i.1)
      let degreeA : IA → ℕ := fun i => rhoDegree i.1
      have hlowerAInj : Function.Injective lowerA := by
        intro i j hij
        apply Subtype.ext
        apply hrho.2.2
        ext c
        rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
        exact congrFun hij x
      have hlowerAIrr : ∀ i,
          Section1.IsIrreducibleCharacterOnGroup (lowerA i) := by
        intro i
        exact huppert_XI_6_ofConjClassFunction_irreducibleOnGroup
          (hrho.1 i.1)
      have hlowerADegree : ∀ i,
          Section1.degree (lowerA i) = (degreeA i : ℂ) := by
        intro i
        change rho i.1 (ConjClasses.mk (1 : pCore p Q)) =
          (rhoDegree i.1 : ℂ)
        exact hvalue i.1
      have hlowerALt : ∀ i, degreeA i < a := by
        intro i
        exact (Finset.mem_filter.mp i.2).2
      have hsumA :
          (∑ i : IA, degreeA i ^ 2) =
            ∑ i ∈ Finset.univ.filter (fun i => rhoDegree i < a),
              rhoDegree i ^ 2 := by
        symm
        exact Finset.sum_subtype
          (s := lowerASet) (f := fun i => rhoDegree i ^ 2)
          (by intro i; rfl)
      have hlowerASq : a ^ 2 ≤ ∑ i : IA, degreeA i ^ 2 := by
        rw [hsumA]
        simpa [lowerASet] using hlowerA
      obtain ⟨T, hTFintype, lowerChar, lowerDegree, hlowerInj,
          hlowerIrr, hlowerDegree, hlowerLt, hlowerSq⟩ :=
        huppert_XI_6_3_two_nonlinear_lower_family
          e chi psi a b hchi hpsi hachi hbpsi ha hb
          lowerA degreeA hlowerAInj hlowerAIrr hlowerADegree
          hlowerALt hlowerASq
          lowerB degreeB hlowerBInj hlowerBIrr hlowerBDegree
          hlowerBLt hlowerBSq
      let : Fintype T := hTFintype
      have hlowerLtZ : ∀ t, lowerDegree t < z := by
        intro t
        simpa [hab] using hlowerLt t
      have hlowerSqZ :
          3 * z ^ 2 ≤ ∑ t, lowerDegree t ^ 2 := by
        simpa [hab] using hlowerSq
      have hthreeComplete :
          3 * z ^ 2 ≤
            ∑ phi ∈ K.filter (fun phi => degreeNat phi < z),
              degreeNat phi ^ 2 :=
        huppert_XI_6_3_injective_family_bound_le_complete_lower_sum
          (I := T) K hKcomplete degreeNat hdegree
          (3 * z ^ 2) z lowerChar lowerDegree hlowerInj hlowerIrr
          hlowerDegree hlowerLtZ hlowerSqZ
      have hthree : 3 * z ^ 2 ≤ A + 1 := by
        calc
          3 * z ^ 2 ≤
              ∑ phi ∈ K.filter (fun phi => degreeNat phi < z),
                degreeNat phi ^ 2 := hthreeComplete
          _ = A + 1 := by
            simpa [C] using hCA
      exact huppert_XI_6_3_two_nonlinear_components_impossible
        A (Nat.card D) z hz hlinear hupper hthree
private theorem huppert_XI_6_6_card_actor_dvd_of_fixedPointFree
    {A Omega : Type*} [Group A] [Finite A] [Finite Omega] [MulAction A Omega]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : Omega, a • x = x → False) :
    Nat.card A ∣ Nat.card Omega := by
  classical
  have hstab : ∀ x : Omega, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact hfree a hane x hax
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A Omega)), by
    rw [mul_comm]
    exact hcard⟩

private noncomputable def huppert_XI_6_6_stabilizerCentralizerEquiv
    {G : Type*} [Group G] (g : G) :
    MulAction.stabilizer (ConjAct G) g ≃ {x : G // x * g = g * x} where
  toFun x :=
    ⟨ConjAct.ofConjAct x.1, by
      have hx : x.1 • g = g := x.2
      rw [ConjAct.smul_def] at hx
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hx)⟩
  invFun x :=
    ⟨ConjAct.toConjAct x.1, by
      change ConjAct.toConjAct x.1 • g = g
      rw [ConjAct.toConjAct_smul]
      exact mul_inv_eq_of_eq_mul x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

public theorem huppert_XI_6_6_class_card_mul_centralizer_card
    {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hst :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have hst' : Fintype.card (ConjClasses.mk g).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) g) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  have hstabCard :
      Nat.card (MulAction.stabilizer (ConjAct G) g) =
        Nat.card {x : G // x * g = g * x} :=
    Nat.card_congr (huppert_XI_6_6_stabilizerCentralizerEquiv g)
  have hcentCard :
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Nat.card {x : G // x * g = g * x} := by
    exact Nat.card_congr
      (Equiv.subtypeEquivRight (fun x =>
        Subgroup.mem_centralizer_singleton_iff))
  simp only [Nat.card_eq_fintype_card] at hstabCard hcentCard ⊢
  rw [hcentCard, ← hstabCard]
  exact hst'

/-- Transfer XI.6.3 from nonprincipal kernel characters to the complete
nonkernel irreducible family of a Frobenius group. -/
private theorem huppert_XI_6_5_frobenius_degree_growth
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFnil : Group.IsNilpotent F)
    (hnotPrimePower : ¬ IsPrimePow (Nat.card F))
    (hdiv : Nat.card D ∣ Nat.card F - 1)
    (hoddD : Odd (Nat.card D))
    (hd : 1 < Nat.card D)
    (Y : Finset (Section1.ClassFunction H))
    (hYirr : ∀ chi : Y,
      Section1.IsIrreducibleCharacterOnGroup
        (chi : Section1.ClassFunction H))
    (hYbot : Section6.inducedKernelFamily F ⊥ Y)
    (degreeNat : Section1.ClassFunction H → ℕ)
    (hdegree : ∀ chi : Y,
      Section1.degree (chi : Section1.ClassFunction H) =
        (degreeNat chi : ℂ)) :
    ∀ chi : Y,
      (chi : Section1.ClassFunction H) ∉
          Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y →
      2 * degreeNat chi * F.relIndex (⊤ : Subgroup H) <
        ∑ xi ∈ Y.filter (fun xi => degreeNat xi < degreeNat chi),
          degreeNat xi ^ 2 := by
  classical
  let : F.Normal := hFrob.normal
  let : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  let : MulDistribMulAction D F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D F
      (Subgroup.le_normalizer_of_normal (H := F))
  have hregular : ActsRegularly D F :=
    hFrob.regular_conj_action
  have hfree :
      ∀ d : D, d ≠ 1 → ∀ x : F, d • x = x → x = 1 := by
    intro d hdne x hx
    have hxmem :
        x ∈ fixedPointSubgroup (Subgroup.zpowers d) F := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro z
      exact smul_eq_self_of_mem_zpowers z.2 hx
    rw [hregular d hdne] at hxmem
    exact Subgroup.mem_bot.mp hxmem
  have hcopPred :
      Nat.Coprime (Nat.card F - 1) (Nat.card F) :=
    (Nat.coprime_self_sub_left
        (m := 1) (n := Nat.card F) Nat.card_pos).2
      (Nat.coprime_one_left _)
  have hcop : Nat.Coprime (Nat.card D) (Nat.card F) :=
    Nat.Coprime.of_dvd_left hdiv hcopPred
  have hFindex :
      F.relIndex (⊤ : Subgroup H) = Nat.card D := by
    simpa [Subgroup.relIndex_top_right] using
      hFrob.isComplement'.symm.index_eq_card
  let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
  have hcommLe : ⁅F, F⁆ ≤ F :=
    Subgroup.commutator_le_left (H₁ := F) (H₂ := F)
  have hY0family : Section6.inducedKernelFamily F ⁅F, F⁆ Y0 :=
    Section6.inducedKernelFamilyOf_isFamily hYbot hcommLe
  have hcommEq : ⁅F, F⁆.subgroupOf F = _root_.commutator F := by
    ext x
    constructor
    · intro hx
      have hxmap :
          (x : H) ∈ (_root_.commutator F).map F.subtype := by
        rw [Subgroup.map_subtype_commutator]
        exact hx
      rcases hxmap with ⟨y, hycomm, hyx⟩
      have hyEq : y = x := Subtype.ext hyx
      simpa [hyEq] using hycomm
    · intro hx
      have hxmap :
          (x : H) ∈ (_root_.commutator F).map F.subtype :=
        ⟨x, hx, rfl⟩
      rwa [Subgroup.map_subtype_commutator] at hxmap
  intro chi hchiNotY0
  rcases (hYbot.2 (chi : Section1.ClassFunction H)).mp chi.property with
    ⟨theta, hthetaIrr, _hthetaBot, hthetaNe, hchiEq⟩
  obtain ⟨z, hzPos, hthetaDegree, _hzDvd⟩ :=
    huppert_XI_6_positive_degree_nat hthetaIrr
  have hzNeOne : z ≠ 1 := by
    intro hzOne
    apply hchiNotY0
    apply (hY0family.2 (chi : Section1.ClassFunction H)).mpr
    refine ⟨theta, hthetaIrr, ?_, hthetaNe, hchiEq⟩
    have hthetaComm :
        Section1.subgroupInKernel' theta (_root_.commutator F) :=
      huppert_XI_6_3_subgroupInKernel_commutator_of_degree_one
        hthetaIrr (by simpa [hzOne] using hthetaDegree)
    simpa [hcommEq] using hthetaComm
  have hz : 1 < z := by omega
  have hchiDegreeNat :
      degreeNat chi = F.relIndex (⊤ : Subgroup H) * z := by
    rw [Subgroup.relIndex_top_right]
    have hcast :
        (degreeNat chi : ℂ) = (F.index * z : ℕ) := by
      rw [← hdegree chi, hchiEq,
        Section1.degree_inducedClassFunction F theta, hthetaDegree]
      norm_cast
    exact_mod_cast hcast
  obtain ⟨K, hKirr, hKcomplete⟩ :=
    huppert_XI_6_complete_irreducible_finset (Q := F)
  let kernelDegree : Section1.ClassFunction F → ℕ := fun eta =>
    if heta : eta ∈ K then
      Classical.choose
        (huppert_XI_6_positive_degree_nat
          (hKirr ⟨eta, heta⟩))
    else 0
  have hKernelDegree : ∀ eta : K,
      Section1.degree (eta : Section1.ClassFunction F) =
        (kernelDegree eta : ℂ) := by
    intro eta
    dsimp [kernelDegree]
    rw [dif_pos eta.property]
    exact (Classical.choose_spec
      (huppert_XI_6_positive_degree_nat (hKirr eta))).2.1
  have hkernelGrowth :
      2 * Nat.card D * z + 1 <
        ∑ eta ∈ K.filter (fun eta => kernelDegree eta < z),
          kernelDegree eta ^ 2 :=
    huppert_XI_6_3_nilpotent_degree_growth
      hFnil hnotPrimePower hcop hfree hoddD hd
      theta hthetaIrr z hz hthetaDegree
      K hKcomplete kernelDegree hKernelDegree
  let lower : Finset (Section1.ClassFunction F) :=
    K.filter (fun eta => kernelDegree eta < z)
  let lowerNonprincipal : Finset (Section1.ClassFunction F) :=
    lower.erase (Section1.principalCharacter F)
  let I := {eta : Section1.ClassFunction F // eta ∈ lowerNonprincipal}
  let thetaLower : I → Section1.ClassFunction F := fun eta => eta.1
  let dtheta : I → ℕ := fun eta => kernelDegree eta.1
  have hsumI :
      (∑ eta : I, dtheta eta ^ 2) =
        ∑ eta ∈ lowerNonprincipal, kernelDegree eta ^ 2 := by
    change (∑ eta : I, kernelDegree eta.1 ^ 2) =
      ∑ eta ∈ lowerNonprincipal, kernelDegree eta ^ 2
    symm
    exact Finset.sum_subtype (s := lowerNonprincipal)
      (f := fun eta => kernelDegree eta ^ 2) (by intro eta; rfl)
  have honeIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.principalCharacter F) :=
    Section3.principalCharacter_isIrreducibleCharacterOnGroup
  have honeK : Section1.principalCharacter F ∈ K :=
    hKcomplete _ honeIrr
  have honeDegree : kernelDegree (Section1.principalCharacter F) = 1 := by
    have hcast : (kernelDegree (Section1.principalCharacter F) : ℂ) = 1 := by
      rw [← hKernelDegree ⟨Section1.principalCharacter F, honeK⟩]
      simp [Section1.degree, Section1.principalCharacter]
    exact_mod_cast hcast
  have honeLower : Section1.principalCharacter F ∈ lower := by
    apply Finset.mem_filter.mpr
    exact ⟨honeK, by simpa [honeDegree] using hz⟩
  have hsplitRaw := Finset.sum_erase_add lower
    (fun eta => kernelDegree eta ^ 2) honeLower
  have hsplit' :
      (∑ eta ∈ K.filter (fun eta => kernelDegree eta < z),
          kernelDegree eta ^ 2) =
        (∑ eta ∈ lowerNonprincipal, kernelDegree eta ^ 2) + 1 := by
    simpa [lower, lowerNonprincipal, honeDegree] using hsplitRaw.symm
  have hlowerGrowth :
      2 * Nat.card D * z < ∑ eta : I, dtheta eta ^ 2 := by
    rw [hsumI]
    omega
  have hthetaLowerInj : Function.Injective thetaLower :=
    Subtype.val_injective
  have hthetaLowerIrr :
      ∀ eta : I,
        Section1.IsIrreducibleCharacterOnGroup (thetaLower eta) := by
    intro eta
    have hetaLower :
        eta.1 ∈ K.filter (fun xi => kernelDegree xi < z) :=
      (Finset.mem_erase.mp eta.property).2
    exact hKirr ⟨eta.1, (Finset.mem_filter.mp hetaLower).1⟩
  have hthetaLowerDegree :
      ∀ eta : I,
        Section1.degree (thetaLower eta) = (dtheta eta : ℂ) := by
    intro eta
    have hetaLower :
        eta.1 ∈ K.filter (fun xi => kernelDegree xi < z) :=
      (Finset.mem_erase.mp eta.property).2
    exact hKernelDegree ⟨eta.1, (Finset.mem_filter.mp hetaLower).1⟩
  let S1 :=
    Y.filter (fun xi => degreeNat xi < degreeNat chi)
  have hIndMem : ∀ eta : I,
      Section1.inducedCF F (thetaLower eta) ∈ S1 := by
    intro eta
    have hetaErase := Finset.mem_erase.mp eta.property
    have hetaLower :
        eta.1 ∈ K.filter (fun xi => kernelDegree xi < z) :=
      hetaErase.2
    have hetaK : eta.1 ∈ K :=
      (Finset.mem_filter.mp hetaLower).1
    have hetaLt : kernelDegree eta.1 < z :=
      (Finset.mem_filter.mp hetaLower).2
    have hetaBot :
        Section1.subgroupInKernel'
          (thetaLower eta) ((⊥ : Subgroup H).subgroupOf F) := by
      intro x
      have hx : x = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using x.property
      simp [hx, Section1.degree]
    have hetaY :
        Section1.inducedCF F (thetaLower eta) ∈ Y := by
      apply (hYbot.2
        (Section1.inducedCF F (thetaLower eta))).mpr
      exact ⟨thetaLower eta, hthetaLowerIrr eta, hetaBot,
        hetaErase.1, rfl⟩
    have hetaDegreeNat :
        degreeNat (Section1.inducedCF F (thetaLower eta)) =
          F.relIndex (⊤ : Subgroup H) * dtheta eta := by
      rw [Subgroup.relIndex_top_right]
      have hcast :
          (degreeNat (Section1.inducedCF F (thetaLower eta)) : ℂ) =
            (F.index * dtheta eta : ℕ) := by
        rw [← hdegree
          ⟨Section1.inducedCF F (thetaLower eta), hetaY⟩,
          Section1.degree_inducedClassFunction F (thetaLower eta),
          hthetaLowerDegree eta]
        norm_cast
      exact_mod_cast hcast
    apply Finset.mem_filter.mpr
    refine ⟨hetaY, ?_⟩
    rw [hetaDegreeNat, hchiDegreeNat]
    exact Nat.mul_lt_mul_of_pos_left hetaLt (by
      rw [hFindex]
      omega)
  have hS1Degree : ∀ eta : S1,
      Section1.degree (eta : Section1.ClassFunction H) =
        (degreeNat eta : ℂ) := by
    intro eta
    exact hdegree
      ⟨eta, (Finset.mem_filter.mp eta.property).1⟩
  have htransfer :=
    huppert_XI_6_3_induced_indexed_degree_sum_le
      (L := H) (K := F) (ι := I) (S1 := S1)
      thetaLower hthetaLowerIrr hthetaLowerInj dtheta
      hthetaLowerDegree hIndMem
      (fun eta : S1 => degreeNat eta) hS1Degree
  have hcf : ∀ eta : S1,
      Section5.cfNormSq (eta : Section1.ClassFunction H) = 1 := by
    intro eta
    let hetaIrr : Section1.IsIrreducibleCharacterOnGroup
        (eta : Section1.ClassFunction H) :=
      hYirr ⟨eta, (Finset.mem_filter.mp eta.property).1⟩
    let hbook :=
      Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        hetaIrr
    have hcast :
        (Section5.cfNormSq (eta : Section1.ClassFunction H) : ℂ) = 1 := by
      rw [← Section5.scalarProduct_self_eq_cfNormSq_of_character hbook.1]
      exact hbook.2
    exact_mod_cast hcast
  have htransferReal :
      (F.relIndex (⊤ : Subgroup H) : ℝ) *
          ∑ eta : I, (dtheta eta : ℝ) ^ 2 ≤
        ∑ eta : S1, (degreeNat eta : ℝ) ^ 2 := by
    simpa [hcf] using htransfer
  have htransferNat :
      F.relIndex (⊤ : Subgroup H) *
          ∑ eta : I, dtheta eta ^ 2 ≤
        ∑ eta : S1, degreeNat eta ^ 2 := by
    exact_mod_cast htransferReal
  have hrelPos : 0 < F.relIndex (⊤ : Subgroup H) := by
    rw [hFindex]
    exact Nat.zero_lt_of_lt hd
  have hlowerGrowthRel :
      2 * F.relIndex (⊤ : Subgroup H) * z <
        ∑ eta : I, dtheta eta ^ 2 := by
    simpa [hFindex] using hlowerGrowth
  have hmulGrowth :
      F.relIndex (⊤ : Subgroup H) *
          (2 * F.relIndex (⊤ : Subgroup H) * z) <
        F.relIndex (⊤ : Subgroup H) *
          ∑ eta : I, dtheta eta ^ 2 :=
    Nat.mul_lt_mul_of_pos_left hlowerGrowthRel hrelPos
  have hsumS1 :
      (∑ eta : S1, degreeNat eta ^ 2) =
        ∑ eta ∈ Y.filter
          (fun xi => degreeNat xi < degreeNat chi),
          degreeNat eta ^ 2 := by
    change (∑ eta : S1, degreeNat eta ^ 2) =
      ∑ eta ∈ S1, degreeNat eta ^ 2
    rw [Finset.univ_eq_attach S1]
    simpa using Finset.sum_attach S1 (fun eta => degreeNat eta ^ 2)
  calc
    2 * degreeNat chi * F.relIndex (⊤ : Subgroup H) =
        F.relIndex (⊤ : Subgroup H) *
          (2 * F.relIndex (⊤ : Subgroup H) * z) := by
      rw [hchiDegreeNat]
      ring
    _ < F.relIndex (⊤ : Subgroup H) *
          ∑ eta : I, dtheta eta ^ 2 := hmulGrowth
    _ ≤ ∑ eta : S1, degreeNat eta ^ 2 := htransferNat
    _ = ∑ eta ∈ Y.filter
          (fun xi => degreeNat xi < degreeNat chi),
          degreeNat eta ^ 2 := hsumS1
/-- XI.6.6, arithmetic endpoint of the one-derangement-class contradiction. -/
private theorem huppert_XI_6_6_single_derangement_class_impossible
    (n d u : ℕ) (hn : 1 < n) (hd : 1 < d) (hu : 0 < u)
    (hodd : Odd d) (hudeg : u ∣ n + 1)
    (hcount : (n + 1) * ((d + 1) / 2) = n + d * u) : False := by
  have hudn : u ∣ n := by
    have hleft : u ∣ (n + 1) * ((d + 1) / 2) :=
      dvd_mul_of_dvd_left hudeg ((d + 1) / 2)
    rw [hcount] at hleft
    exact (Nat.dvd_add_iff_left (dvd_mul_left u d)).mpr hleft
  have hcopN : Nat.Coprime n (n + 1) := by
    exact (Nat.coprime_self_add_right (m := n) (n := 1)).2
      (Nat.coprime_one_right n)
  have huone : u = 1 := Nat.eq_one_of_dvd_coprimes hcopN hudn hudeg
  subst u
  rcases hodd with ⟨k, hk⟩
  rw [hk] at hcount hd
  have hhalf : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [hhalf] at hcount
  nlinarith

private theorem huppert_XI_6_6_eq_one_of_sq_eq_one_of_odd_card
    {X : Type*} [Group X] [Finite X] (hodd : Odd (Nat.card X))
    (x : X) (hx : x ^ 2 = 1) : x = 1 := by
  have hordTwo : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime 2 (Nat.card X) := hodd.coprime_two_left
  have hordOne : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hordTwo (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hordOne)

private theorem huppert_XI_6_6_derangement_centralizer_fixedPointFree
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (hat_most_two_fixed_points :
      ∀ x : G, x ≠ 1 → ∀ a b c : Omega,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (x • a = a ∧ x • b = b ∧ x • c = c))
    (hpairOdd : ∀ a b : Omega, ∀ hab : a ≠ b,
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hswapInverts :
      ∀ a b : Omega, ∀ hab : a ≠ b, ∀ s : G,
        s • a = b → s • b = a →
          ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
            s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
              ((((x⁻¹ : MulAction.stabilizer
                (MulAction.stabilizer G a)
                (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
                  MulAction.stabilizer G a) : G)))
    (g : G) (hg : ∀ x : Omega, g • x ≠ x) :
    ∀ c : Subgroup.centralizer ({g} : Set G), c ≠ 1 →
      ∀ a : Omega, (c : G) • a = a → False := by
  intro c hc a hca
  let b : Omega := g • a
  have hab : a ≠ b := Ne.symm (hg a)
  have hcne : (c : G) ≠ 1 := by
    intro h
    apply hc
    exact Subtype.ext h
  have hccomm : (c : G) * g = g * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hcb : (c : G) • b = b := by
    dsimp [b]
    calc
      (c : G) • (g • a) = ((c : G) * g) • a := by rw [mul_smul]
      _ = (g * (c : G)) • a := by rw [hccomm]
      _ = g • ((c : G) • a) := by rw [mul_smul]
      _ = g • a := by rw [hca]
  have hcgb : (c : G) • (g • b) = g • b := by
    calc
      (c : G) • (g • b) = ((c : G) * g) • b := by rw [mul_smul]
      _ = (g * (c : G)) • b := by rw [hccomm]
      _ = g • ((c : G) • b) := by rw [mul_smul]
      _ = g • b := by rw [hcb]
  have hgba : g • b = a := by
    by_contra hga
    exact (hat_most_two_fixed_points (c : G) hcne a b (g • b)
      hab (Ne.symm hga) (Ne.symm (hg b))) ⟨hca, hcb, hcgb⟩
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  let cH : H := ⟨(c : G), hca⟩
  let cD : D := ⟨cH, by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact hcb⟩
  have hconjInv : g * (c : G) * g⁻¹ = (c : G)⁻¹ := by
    simpa [H, b', D, cH, cD] using
      hswapInverts a b hab g rfl hgba cD
  have hconjFixed : g * (c : G) * g⁻¹ = (c : G) := by
    calc
      g * (c : G) * g⁻¹ = ((c : G) * g) * g⁻¹ := by rw [← hccomm]
      _ = (c : G) := by simp [mul_assoc]
  have hcInv : (c : G) = (c : G)⁻¹ := hconjFixed.symm.trans hconjInv
  have hcSqG : (c : G) ^ 2 = 1 := by
    calc
      (c : G) ^ 2 = (c : G) * (c : G) := pow_two _
      _ = (c : G) * (c : G)⁻¹ := congrArg (fun x : G => (c : G) * x) hcInv
      _ = 1 := mul_inv_cancel _
  have hcSqD : cD ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hcSqG
  have hcDone : cD = 1 :=
    huppert_XI_6_6_eq_one_of_sq_eq_one_of_odd_card
      (hpairOdd a b hab) cD hcSqD
  apply hc
  have := congrArg (fun x : D => (((x : H) : G))) hcDone
  simpa [cD, cH] using this

/-- XI.6.6: if centralizers of derangements act freely and the standard
Zassenhaus element count holds, derangements occupy at least two conjugacy
classes. -/
private theorem huppert_XI_6_6_two_derangement_classes_of_centralizer_fixedPointFree
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (n d : ℕ) (hn : 1 < n) (hd : 1 < d) (hodd : Odd d)
    (hOmegaCard : Nat.card Omega = n + 1)
    (hGcard : Nat.card G = (n + 1) * n * d)
    (hderCount :
      let Der := {g : G // ∀ x : Omega, g • x ≠ x}
      2 * Nat.card Der + 2 * n ^ 2 = (n + 1) * n * (d + 1))
    (hderNonempty : Nonempty {g : G // ∀ x : Omega, g • x ≠ x})
    (hcentralizerFree :
      ∀ g : G, (∀ x : Omega, g • x ≠ x) →
        ∀ c : Subgroup.centralizer ({g} : Set G), c ≠ 1 →
          ∀ x : Omega, (c : G) • x = x → False) :
    ∃ g h : G,
      (∀ x : Omega, g • x ≠ x) ∧
        (∀ x : Omega, h • x ≠ x) ∧ ¬ IsConj g h := by
  classical
  let Der := {g : G // ∀ x : Omega, g • x ≠ x}
  by_cases htwo : ∃ g h : G,
      (∀ x : Omega, g • x ≠ x) ∧
        (∀ x : Omega, h • x ≠ x) ∧ ¬ IsConj g h
  · exact htwo
  exfalso
  obtain ⟨g, hg⟩ := hderNonempty
  have hconj (x : Der) : IsConj x.1 g := by
    by_contra hx
    exact htwo ⟨x.1, g, x.2, hg, hx⟩
  have hder_of_isConj {x y : G} (hxy : IsConj x y)
      (hy : ∀ a : Omega, y • a ≠ a) : ∀ a : Omega, x • a ≠ a := by
    intro a hxa
    rcases hxy with ⟨c, hc⟩
    have hconjEq : (c : G) * x * (c : G)⁻¹ = y := by
      calc
        (c : G) * x * (c : G)⁻¹ = (y * (c : G)) * (c : G)⁻¹ := by
          rw [hc.eq]
        _ = y := by simp [mul_assoc]
    apply hy ((c : G) • a)
    calc
      y • ((c : G) • a) = ((c : G) * x * (c : G)⁻¹) • ((c : G) • a) := by
        rw [hconjEq]
      _ = (c : G) • (x • a) := by
        simp only [mul_smul, inv_smul_smul]
      _ = (c : G) • a := by rw [hxa]
  let eDerClass : Der ≃ (ConjClasses.mk g).carrier :=
    { toFun := fun x =>
        ⟨x.1, (ConjClasses.mem_carrier_iff_mk_eq.mpr
          ((ConjClasses.mk_eq_mk_iff_isConj.mpr (hconj x))))⟩
      invFun := fun x =>
        ⟨x.1, hder_of_isConj
          (ConjClasses.mk_eq_mk_iff_isConj.mp
            (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)) hg⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  have hderClass : Nat.card Der = Nat.card (ConjClasses.mk g).carrier :=
    Nat.card_congr eDerClass
  let C := Subgroup.centralizer ({g} : Set G)
  have hCdiv : Nat.card C ∣ Nat.card Omega :=
    huppert_XI_6_6_card_actor_dvd_of_fixedPointFree
      (A := C) (Omega := Omega) (by
        intro c hc x hfix
        exact hcentralizerFree g hg c hc x hfix)
  obtain ⟨u, hu⟩ := hCdiv
  have hCu : Nat.card C * u = n + 1 := by
    exact hu.symm.trans hOmegaCard
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hupos : 0 < u := by
    have : 0 < n + 1 := by omega
    nlinarith
  have hderMul : Nat.card Der * Nat.card C = Nat.card G := by
    rw [hderClass]
    exact huppert_XI_6_6_class_card_mul_centralizer_card g
  have hderEq : Nat.card Der = n * d * u := by
    apply Nat.eq_of_mul_eq_mul_right hCpos
    calc
      Nat.card Der * Nat.card C = Nat.card G := hderMul
      _ = (n + 1) * n * d := hGcard
      _ = (n * d * u) * Nat.card C := by
        rw [← hCu]
        ring
  have hcountRaw : 2 * (n * d * u) + 2 * n ^ 2 =
      (n + 1) * n * (d + 1) := by
    simpa [Der, hderEq] using hderCount
  rcases hodd with ⟨k, hk⟩
  have hhalf : (d + 1) / 2 = k + 1 := by
    rw [hk]
    omega
  have hcount : (n + 1) * ((d + 1) / 2) = n + d * u := by
    rw [hhalf, hk]
    rw [hk] at hcountRaw
    nlinarith
  exact huppert_XI_6_6_single_derangement_class_impossible
    n d u hn hd hupos ⟨k, hk⟩
      ⟨Nat.card C, by rw [← hCu, mul_comm]⟩ hcount


/-- Burnside's lemma on points and ordered pairs gives the standard
Zassenhaus derangement count without separately enumerating the one- and
two-fixed-point strata. -/
private theorem zassenhaus_derangement_count
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 → ∀ a b c : Omega,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (n d : ℕ)
    (hOmegaCard : Fintype.card Omega = n + 1)
    (hGcard : Nat.card G = (n + 1) * n * d) :
    let Der := {g : G // ∀ x : Omega, g • x ≠ x}
    2 * Nat.card Der + 2 * n ^ 2 = (n + 1) * n * (d + 1) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let fix : G → ℕ := fun g => Fintype.card (MulAction.fixedBy Omega g)
  have hfixOne : fix 1 = n + 1 := by
    simp [fix, hOmegaCard]
  have hfixLe (g : G) (hg : g ≠ 1) : fix g ≤ 2 := by
    by_contra hle
    have hthree : 2 < Fintype.card (MulAction.fixedBy Omega g) := by
      simpa [fix] using Nat.lt_of_not_ge hle
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hthree
    exact hat_most_two_fixed_points g hg x y z
      (fun h => hxy (Subtype.ext h))
      (fun h => hxz (Subtype.ext h))
      (fun h => hyz (Subtype.ext h))
      ⟨x.property, y.property, z.property⟩
  let Q1 := Quotient (MulAction.orbitRel G Omega)
  let : Fintype Q1 := Fintype.ofFinite Q1
  let : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hQ1card : Fintype.card Q1 = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let q0 : Q1 := Quotient.mk (MulAction.orbitRel G Omega) a
    refine ⟨q0, ?_⟩
    intro q
    rw [← Quotient.out_eq q]
    apply Quotient.sound
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (Quotient.out q)
    exact ⟨g, hg⟩
  have hsumFix : ∑ g : G, fix g = Nat.card G := by
    have hburnside :=
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G Omega
    simpa [fix, Q1, hQ1card, Nat.card_eq_fintype_card] using hburnside
  let Q2 := Quotient (MulAction.orbitRel G (Omega × Omega))
  let : Fintype Q2 := Fintype.ofFinite Q2
  have hQ2card : Fintype.card Q2 = 2 := by
    have hcardNat : Nat.card Q2 = 2 := by
      rw [Nat.card_eq_two_iff]
      let qdiag : Q2 := Quotient.mk (MulAction.orbitRel G (Omega × Omega)) (a, a)
      let qoff : Q2 := Quotient.mk (MulAction.orbitRel G (Omega × Omega)) (a, b)
      have hne : qdiag ≠ qoff := by
        intro heq
        have hrel := Quotient.exact heq
        rcases hrel with ⟨g, hg⟩
        have hga : g • a = a := congrArg Prod.fst hg
        have hgb : g • b = a := congrArg Prod.snd hg
        apply hab
        exact (MulAction.toPerm g).injective (hga.trans hgb.symm)
      refine ⟨qdiag, qoff, hne, ?_⟩
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_univ, iff_true]
      rcases hq : Quotient.out q with ⟨x, y⟩
      by_cases hxy : x = y
      · left
        rw [← Quotient.out_eq q]
        apply Quotient.sound
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a x
        refine ⟨g, ?_⟩
        simpa [hq, hxy] using congrArg (fun z => (z, z)) hg
      · right
        rw [← Quotient.out_eq q]
        apply Quotient.sound
        obtain ⟨g, hgx, hgy⟩ :=
          (MulAction.is_two_pretransitive_iff.mp htwo) hab hxy
        exact ⟨g, by rw [hq]; simp [hgx, hgy]⟩
    simpa [Nat.card_eq_fintype_card] using hcardNat
  have hfixProd (g : G) :
      Fintype.card (MulAction.fixedBy (Omega × Omega) g) = fix g ^ 2 := by
    let e : MulAction.fixedBy (Omega × Omega) g ≃
        MulAction.fixedBy Omega g × MulAction.fixedBy Omega g :=
      { toFun := fun x =>
          (⟨x.1.1, congrArg Prod.fst x.2⟩,
            ⟨x.1.2, congrArg Prod.snd x.2⟩)
        invFun := fun x => ⟨(x.1.1, x.2.1), by exact Prod.ext x.1.2 x.2.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro x; ext <;> rfl }
    calc
      Fintype.card (MulAction.fixedBy (Omega × Omega) g) =
          Fintype.card (MulAction.fixedBy Omega g ×
            MulAction.fixedBy Omega g) := Fintype.card_congr e
      _ = fix g ^ 2 := by simp [fix, pow_two]
  have hsumFixSq : ∑ g : G, fix g ^ 2 = 2 * Nat.card G := by
    have hburnside :=
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Omega × Omega)
    rw [hQ2card] at hburnside
    simpa [hfixProd, Nat.card_eq_fintype_card] using hburnside
  have hfixZero (g : G) :
      fix g = 0 ↔ ∀ x : Omega, g • x ≠ x := by
    constructor
    · intro hzero x hfix
      have : IsEmpty (MulAction.fixedBy Omega g) :=
        Fintype.card_eq_zero_iff.mp (by simpa [fix] using hzero)
      exact isEmptyElim (⟨x, hfix⟩ : MulAction.fixedBy Omega g)
    · intro hfree
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun x => hfree x.1 x.2⟩
  let Der := {g : G // ∀ x : Omega, g • x ≠ x}
  have hDerCard :
      Nat.card Der = ((Finset.univ : Finset G).filter fun g => fix g = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext g
    simp [hfixZero]
  let delta : G → ℕ := fun g => if fix g = 0 then 1 else 0
  have hdeltaSum :
      ∑ g ∈ (Finset.univ : Finset G).erase 1, delta g = Nat.card Der := by
    calc
      ∑ g ∈ (Finset.univ : Finset G).erase 1, delta g =
          (((Finset.univ : Finset G).erase 1).filter fun g => fix g = 0).card := by
            simp [delta]
      _ = ((Finset.univ : Finset G).filter fun g => fix g = 0).card := by
        congr 1
        ext g
        by_cases hg : g = 1
        · subst g
          simp [hfixOne]
        · simp [hg]
      _ = Nat.card Der := hDerCard.symm
  have hsumFixErase :
      (n + 1) + ∑ g ∈ (Finset.univ : Finset G).erase 1, fix g =
        Nat.card G := by
    calc
      (n + 1) + ∑ g ∈ (Finset.univ : Finset G).erase 1, fix g =
          fix 1 + ∑ g ∈ (Finset.univ : Finset G).erase 1, fix g := by
            rw [hfixOne]
      _ = ∑ g : G, fix g := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
      _ = Nat.card G := hsumFix
  have hsumFixSqErase :
      (n + 1) ^ 2 +
          ∑ g ∈ (Finset.univ : Finset G).erase 1, fix g ^ 2 =
        2 * Nat.card G := by
    calc
      (n + 1) ^ 2 +
          ∑ g ∈ (Finset.univ : Finset G).erase 1, fix g ^ 2 =
          fix 1 ^ 2 +
            ∑ g ∈ (Finset.univ : Finset G).erase 1, fix g ^ 2 := by
              rw [hfixOne]
      _ = ∑ g : G, fix g ^ 2 := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
      _ = 2 * Nat.card G := hsumFixSq
  have hpoly (g : G) (hg : g ≠ 1) :
      2 * delta g + 3 * fix g = fix g ^ 2 + 2 := by
    have hle := hfixLe g hg
    by_cases hzero : fix g = 0
    · simp [delta, hzero]
    · have hcases : fix g = 1 ∨ fix g = 2 := by omega
      rcases hcases with hfix | hfix <;> simp [delta, hfix]
  have hpolySum :
      ∑ g ∈ (Finset.univ : Finset G).erase 1,
          (2 * delta g + 3 * fix g) =
        ∑ g ∈ (Finset.univ : Finset G).erase 1,
          (fix g ^ 2 + 2) := by
    apply Finset.sum_congr rfl
    intro g hg
    exact hpoly g (Finset.mem_erase.mp hg).1
  have haggregate :
      2 * Nat.card Der +
          3 * (∑ g ∈ (Finset.univ : Finset G).erase 1, fix g) =
        (∑ g ∈ (Finset.univ : Finset G).erase 1, fix g ^ 2) +
          2 * (Nat.card G - 1) := by
    rw [← hdeltaSum]
    simpa [Finset.sum_add_distrib, Finset.mul_sum,
      Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),
      Nat.card_eq_fintype_card, Nat.mul_comm] using hpolySum
  change 2 * Nat.card Der + 2 * n ^ 2 = (n + 1) * n * (d + 1)
  rw [hGcard] at hsumFixErase hsumFixSqErase haggregate
  have hGpos : 0 < (n + 1) * n * d := by
    rw [← hGcard]
    exact Nat.card_pos
  have hGsub : (n + 1) * n * d - 1 + 1 = (n + 1) * n * d :=
    Nat.sub_add_cancel hGpos
  nlinarith


/-- XI.6.7, final arithmetic contradiction: a hypothetical remaining
character of degree `n-1` would force `n-1` to divide `2*d`. -/
private theorem huppert_XI_6_7_divisibility_contradiction
    (n d : ℕ) (hn : 1 < n) (hd : 0 < d)
    (hsmall : 2 * d < n - 1)
    (hdegreeDvd : n - 1 ∣ (n + 1) * n * d) : False := by
  let m := n - 1
  have hnm : n = m + 1 := by
    dsimp [m]
    omega
  have hcop : Nat.Coprime m n := by
    rw [hnm]
    exact (Nat.coprime_self_add_right (m := m) (n := 1)).2
      (Nat.coprime_one_right m)
  have hdivTail : m ∣ (n + 1) * d := by
    apply hcop.dvd_of_dvd_mul_left
    simpa [m, mul_assoc, mul_left_comm, mul_comm] using hdegreeDvd
  have hnplus : n + 1 = m + 2 := by omega
  rw [hnplus, add_mul] at hdivTail
  have hdivSelf : m ∣ m * d := dvd_mul_right m d
  have hdivTwo : m ∣ 2 * d :=
    (Nat.dvd_add_iff_right hdivSelf).mpr hdivTail
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hmle : m ≤ 2 * d := Nat.le_of_dvd (by positivity) hdivTwo
  dsimp [m] at hmle
  omega

set_option backward.isDefEq.respectTransparency false in
/-- An irreducible character trivial on a normal subgroup with cyclic quotient
has degree one.  This is the quotient-linear input in XI.5.3. -/
public theorem huppert_XI_5_3_degree_one_of_quotient_commutative
    {H : Type u} [Group H] [Finite H]
    (F : Subgroup H) [F.Normal]
    [IsMulCommutative (H ⧸ F)]
    (theta : Section1.ClassFunction H)
    (hthetaIrr : Section1.IsIrreducibleCharacterOnGroup theta)
    (hthetaKer : Section1.subgroupInKernel' theta F) :
    Section1.degree theta = 1 := by
  classical
  rcases hthetaIrr with ⟨n, rho, hrhoIrr, hthetaEq⟩
  have hthetaKerRho :
      Section1.subgroupInKernel' rho.character F := by
    simpa [hthetaEq] using hthetaKer
  have hkerRho :
      Section1.subgroupInRepresentationKernel rho F :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho F).mp hthetaKerRho
  let q : H →* H ⧸ F := QuotientGroup.mk' F
  let rhoq : Representation ℂ (H ⧸ F) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup rho F hkerRho
  have hcomp : rhoq.comp q = rho := by
    apply MonoidHom.ext
    intro h
    exact Section1.quotientRepresentationOfKernelSubgroup_mk
      rho F hkerRho h
  have hrhoqIrr : Representation.IsIrreducible rhoq := by
    apply Section6.representation_isIrreducible_of_comp_surjective
      rhoq q (QuotientGroup.mk'_surjective F)
    simpa [hcomp] using hrhoIrr
  have hn : n = 1 := by
    let : Representation.IsIrreducible rhoq := hrhoqIrr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (ρ := rhoq))
  rw [hthetaEq, Section1.degree_representation_character]
  simp [hn]

set_option backward.isDefEq.respectTransparency false in
/-- XI.5.3 point-stabilizer input: the irreducible characters whose kernels
contain the Frobenius kernel are exactly the inflated linear characters of the
cyclic quotient, and there are `|D|` of them. -/
public theorem huppert_XI_5_3_kernel_quotient_linear_family
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hcyclic : IsCyclic D) :
    ∃ Z : Finset (Section1.ClassFunction H),
      (∀ theta : Z,
        Section1.IsIrreducibleCharacterOnGroup
          (theta : Section1.ClassFunction H)) ∧
      (∀ theta : Z,
        Section1.subgroupInKernel'
          (theta : Section1.ClassFunction H) F) ∧
      Z.card = Nat.card D ∧
      ∀ theta : Section1.ClassFunction H,
        Section1.IsIrreducibleCharacterOnGroup theta →
        Section1.subgroupInKernel' theta F →
        theta ∈ Z := by
  classical
  let : F.Normal := hFrob.normal
  let Q := H ⧸ F
  let q : H →* Q := QuotientGroup.mk' F
  let e : Q ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
  have hQcyclic : IsCyclic Q := e.isCyclic.mpr hcyclic
  let : IsCyclic Q := hQcyclic
  let : IsMulCommutative Q := IsCyclic.isMulCommutative
  let : CommGroup Q := IsMulCommutative.instCommGroup
  let inflate : (Q →* ℂˣ) → Section1.ClassFunction H :=
    fun chi => Section1.characterInflationByHom q chi
  have hinflate : Function.Injective inflate := by
    intro chi psi hEq
    apply DFunLike.ext chi psi
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective F x
    apply Units.ext
    calc
      (chi x : ℂ) = (chi (q h) : ℂ) := by rw [← hh]
      _ = (inflate chi h : ℂ) := rfl
      _ = (inflate psi h : ℂ) := by rw [hEq]
      _ = (psi (q h) : ℂ) := rfl
      _ = (psi x : ℂ) := by rw [hh]
  let : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
  let Z : Finset (Section1.ClassFunction H) :=
    Finset.univ.image inflate
  have hZirr : ∀ theta : Z,
      Section1.IsIrreducibleCharacterOnGroup
        (theta : Section1.ClassFunction H) := by
    intro theta
    rcases Finset.mem_image.mp theta.property with
      ⟨chi, _hchi, hchiEq⟩
    rw [← hchiEq]
    exact Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
      q chi
  have hZker : ∀ theta : Z,
      Section1.subgroupInKernel'
        (theta : Section1.ClassFunction H) F := by
    intro theta
    rcases Finset.mem_image.mp theta.property with
      ⟨chi, _hchi, hchiEq⟩
    rw [← hchiEq]
    intro f
    have hq : q (f : H) = 1 := by
      exact (QuotientGroup.eq_one_iff (N := F) (f : H)).2 f.property
    simp [inflate, q, Section1.characterInflationByHom, hq,
      Section1.degree]
  have hZcard : Z.card = Nat.card D := by
    let : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) := by
      have : NeZero (Monoid.exponent Q) := by infer_instance
      exact Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
    have hdual :
        Nat.card (Q →* ℂˣ) = Nat.card Q :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
    change (Finset.univ.image inflate).card = Nat.card D
    rw [Finset.card_image_of_injective _ hinflate, Finset.card_univ]
    simpa [Nat.card_eq_fintype_card] using
      hdual.trans (Nat.card_congr e.toEquiv)
  refine ⟨Z, hZirr, hZker, hZcard, ?_⟩
  intro theta hthetaIrr hthetaKer
  have hthetaDegree : Section1.degree theta = 1 :=
    huppert_XI_5_3_degree_one_of_quotient_commutative
      F theta hthetaIrr hthetaKer
  obtain ⟨lambda, hthetaEq⟩ :=
    Section1.exists_linearCharacter_of_irreducible_degree_one
      hthetaIrr hthetaDegree
  have hFle : F ≤ lambda.ker := by
    intro f hf
    change lambda f = 1
    apply Units.ext
    have hval := hthetaKer ⟨f, hf⟩
    rw [hthetaEq] at hval
    simpa [Section1.degree, hthetaDegree] using hval
  let chi : Q →* ℂˣ := QuotientGroup.lift F lambda hFle
  have hthetaInflate : theta = inflate chi := by
    ext h
    rw [hthetaEq]
    exact congrArg Units.val
      (QuotientGroup.lift_mk' (N := F) (φ := lambda) hFle h).symm
  apply Finset.mem_image.mpr
  exact ⟨chi, Finset.mem_univ chi, hthetaInflate.symm⟩
private theorem huppert_XI_6_coherentExtension_signed_irreducible_family
    {L G : Type u} [Group L] [Finite L] [Group G] [Finite G]
    {Y : Finset (Section1.ClassFunction L)}
    {T tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (htau : Section6.coherentExtension Y T tau)
    (hYirr : ∀ eta : Y,
      Section1.IsIrreducibleCharacterOnGroup (eta : Section1.ClassFunction L)) :
    ∃ epsilon : Y → ℂ, ∃ mu : Y → Section1.ClassFunction G,
      (∀ eta, Section1.IsSign (epsilon eta)) ∧
        (∀ eta, Section1.IsIrreducibleCharacterOnGroup (mu eta)) ∧
          (∀ eta : Y, tau (eta : Section1.ClassFunction L) = epsilon eta • mu eta) ∧
            Function.Injective mu := by
  classical
  have hsigned : ∀ eta : Y,
      Section3.IsSignedIrreducibleCharacter
        (tau (eta : Section1.ClassFunction L)) := by
    intro eta
    exact Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      htau eta.2 (hYirr eta)
  choose epsilon hepsilon mu hmu htau_mu using hsigned
  refine ⟨epsilon, mu, hepsilon, hmu, htau_mu, ?_⟩
  intro eta xi hmu_eq
  apply Subtype.ext
  by_contra heta_xi
  have hsource_zero :
      Section1.scalarProduct L (eta : Section1.ClassFunction L)
        (xi : Section1.ClassFunction L) = 0 :=
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hYirr eta) (hYirr xi) heta_xi
  have himage_zero :
      Section1.scalarProduct G
        (tau (eta : Section1.ClassFunction L))
        (tau (xi : Section1.ClassFunction L)) = 0 := by
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
      htau.1 eta.2 xi.2, hsource_zero]
  rw [htau_mu eta, htau_mu xi, hmu_eq,
    Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    Section1.scalarProduct_irreducibleCharacter_self (hmu xi)] at himage_zero
  rcases hepsilon eta with hepsilon_eta | hepsilon_eta <;>
    rcases hepsilon xi with hepsilon_xi | hepsilon_xi <;>
      simp [hepsilon_eta, hepsilon_xi] at himage_zero
private lemma huppert_XI_5_3_mackeyIntersection_eq_twoPointStabilizer
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b)
    (t : G) (_hta : t • a = b) (htb : t • b = a) :
    Section1.mackeyIntersection
        (MulAction.stabilizer G a) (MulAction.stabilizer G a) t =
      MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) := by
  ext k
  rw [Section1.mackeyIntersection_mem_iff]
  change (t * ((k : MulAction.stabilizer G a) : G) * t⁻¹) • a = a ↔
    (k : MulAction.stabilizer G a) •
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) =
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have htinvA : t⁻¹ • a = b := by
    calc
      t⁻¹ • a = t⁻¹ • (t • b) := by rw [htb]
      _ = b := inv_smul_smul t b
  constructor
  · intro hk
    apply Subtype.ext
    have hk'' : t • (((k : MulAction.stabilizer G a) : G) • b) = a := by
      calc
        t • (((k : MulAction.stabilizer G a) : G) • b) =
            (t * ((k : MulAction.stabilizer G a) : G)) • b := by
              rw [mul_smul]
        _ = (t * ((k : MulAction.stabilizer G a) : G)) • (t⁻¹ • a) := by
              rw [htinvA]
        _ = (t * ((k : MulAction.stabilizer G a) : G)) • (t⁻¹ • a) := rfl
        _ = (t * ((k : MulAction.stabilizer G a) : G) * t⁻¹) • a :=
              (mul_smul (t * (((k : MulAction.stabilizer G a) : G))) t⁻¹ a).symm
        _ = a := hk
    exact (MulAction.toPerm t).injective (by simpa [htb, Subgroup.smul_def] using hk'')
  · intro hk
    have hk'' : ((k : MulAction.stabilizer G a) : G) • b = b := by
      exact congrArg Subtype.val hk
    calc
      (t * ((k : MulAction.stabilizer G a) : G) * t⁻¹) • a =
          t • (((k : MulAction.stabilizer G a) : G) • (t⁻¹ • a)) := by
            simp only [mul_smul]
      _ = t • (((k : MulAction.stabilizer G a) : G) • b) := by rw [htinvA]
      _ = t • b := by rw [hk'']
      _ = a := htb


private lemma huppert_XI_5_3_doubleCoset_eq_one_or_swap
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (h2 : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (t : G) (hta : t • a = b) :
    ∀ q : DoubleCoset.Quotient
        (MulAction.stabilizer G a : Set G) (MulAction.stabilizer G a),
      q = DoubleCoset.mk (MulAction.stabilizer G a)
          (MulAction.stabilizer G a) 1 ∨
        q = DoubleCoset.mk (MulAction.stabilizer G a)
          (MulAction.stabilizer G a) t := by
  intro q
  let H := MulAction.stabilizer G a
  have ht : t • a ≠ a := by simpa [hta] using hab.symm
  have hdecomp :=
    huppert_II_1_12_b_doubleCoset_decomposition h2 a t ht
  have hmem : q.out ∈ (H : Set G) ∪ DoubleCoset.doubleCoset t H H := by
    rw [hdecomp]
    exact Set.mem_univ q.out
  rcases hmem with hH | hdouble
  · exact Or.inl (Section1.DoubleCoset.eq_mk_one_of_out_mem H hH)
  · right
    rw [← DoubleCoset.out_eq' (H := H) (K := H) q]
    exact ((DoubleCoset.eq (H := H) (K := H) (a := t) (b := q.out)).mpr
      (DoubleCoset.mem_doubleCoset.mp hdouble)).symm


private lemma xi61_sum_eq_of_eq_one_or_swap
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q0 qt : Q) (hne : q0 ≠ qt)
    (hcases : ∀ q : Q, q = q0 ∨ q = qt)
    (f : Q → ℂ) :
    ∑ q : Q, f q = f q0 + f qt := by
  have huniv : (Finset.univ : Finset Q) = {q0, qt} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcases q
  rw [huniv]
  simp [hne]


private lemma huppert_XI_5_3_subgroupRestriction_inducedCF_twoCoset
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (h2 : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (t : G) (hta : t • a = b)
    (phi : Section1.ClassFunction (MulAction.stabilizer G a))
    (hphi : Section1.IsClassFunction phi) :
    Section1.subgroupRestriction (MulAction.stabilizer G a)
        (Section1.inducedCF (MulAction.stabilizer G a) phi) =
      phi + Section1.mackeySummandAmbientFormula
        (MulAction.stabilizer G a) (MulAction.stabilizer G a) t phi := by
  classical
  let H := MulAction.stabilizer G a
  let q0 : DoubleCoset.Quotient (H : Set G) H :=
    DoubleCoset.mk H H 1
  let qt : DoubleCoset.Quotient (H : Set G) H :=
    DoubleCoset.mk H H t
  let : Fintype (DoubleCoset.Quotient (H : Set G) H) :=
    Fintype.ofFinite _
  have htNotH : t ∉ H := by
    intro htH
    exact hab.symm (by simpa [H, hta] using htH)
  have hqtNe : qt ≠ q0 := by
    intro hEq
    have hEq' : DoubleCoset.mk H H 1 = DoubleCoset.mk H H t := hEq.symm
    rcases (DoubleCoset.eq (H := H) (K := H) (a := 1) (b := t)).mp hEq' with
      ⟨x, hx, y, hy, htEq⟩
    apply htNotH
    rw [htEq]
    simpa using H.mul_mem hx hy
  ext k
  rw [Section1.subgroupRestriction_inducedCF_eq_doubleCoset_fiber_sum]
  have hcases :
      ∀ q : DoubleCoset.Quotient (H : Set G) H, q = q0 ∨ q = qt := by
    intro q
    simpa [H, q0, qt] using
      (huppert_XI_5_3_doubleCoset_eq_one_or_swap h2 a b hab t hta q)
  have hsum :
      (∑ q : DoubleCoset.Quotient (H : Set G) H,
        Section1.inducedCFDoubleCosetFiberSum H H phi k q) =
        Section1.inducedCFDoubleCosetFiberSum H H phi k q0 +
          Section1.inducedCFDoubleCosetFiberSum H H phi k qt :=
    xi61_sum_eq_of_eq_one_or_swap q0 qt hqtNe.symm hcases
      (fun q => Section1.inducedCFDoubleCosetFiberSum H H phi k q)
  rw [hsum, mul_add]
  have hq0 :
      Section1.inducedCFDoubleCosetFiberSum H H phi k q0 =
        Section1.inducedCFDoubleCosetFiberAt H H phi k 1 := by
    rfl
  have hqt :
      Section1.inducedCFDoubleCosetFiberSum H H phi k qt =
        Section1.inducedCFDoubleCosetFiberAt H H phi k t := by
    rfl
  rw [hq0, hqt,
    Section1.inducedCFDoubleCosetFiberAt_normalized_eq_mackeySummandAmbientFormula
      H H 1 phi hphi k,
    Section1.inducedCFDoubleCosetFiberAt_normalized_eq_mackeySummandAmbientFormula
      H H t phi hphi k]
  rw [Section1.mackeySummandAmbientFormula_self_eq_of_mem H H.one_mem phi hphi k]
  rfl


private lemma huppert_XI_5_3_scalarProduct_inducedCF_twoCoset
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (h2 : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (t : G) (hta : t • a = b) (_htb : t • b = a)
    (psi phi : Section1.ClassFunction (MulAction.stabilizer G a))
    (hpsi : Section1.IsClassFunction psi)
    (hphi : Section1.IsClassFunction phi) :
    Section1.scalarProduct G
        (Section1.inducedCF (MulAction.stabilizer G a) psi)
        (Section1.inducedCF (MulAction.stabilizer G a) phi) =
      Section1.scalarProduct (MulAction.stabilizer G a) psi phi +
        Section1.scalarProduct
          (Section1.mackeyIntersection
            (MulAction.stabilizer G a) (MulAction.stabilizer G a) t)
          (Section1.subgroupRestriction
            (Section1.mackeyIntersection
              (MulAction.stabilizer G a) (MulAction.stabilizer G a) t) psi)
          (Section1.mackeyConjugateRestriction
            (MulAction.stabilizer G a) (MulAction.stabilizer G a) t phi) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have hres :
      Section1.subgroupRestriction H (Section1.inducedCF H phi) =
        phi + Section1.mackeySummandAmbientFormula H H t phi :=
    huppert_XI_5_3_subgroupRestriction_inducedCF_twoCoset h2 a b hab t hta phi hphi
  have hmackey :
      Section1.mackeySummandAmbientFormula H H t phi =
        Section1.mackeySummand H H t phi := by
    ext k
    rw [Section1.mackeySummand_apply,
      Section1.mackeySummandFormula_eq_ambient]
  rw [Section1.scalarProduct_inducedCF_inducedCF_left H psi phi, hres,
    Section5.scalarProduct_add_right, hmackey,
    Section1.scalarProduct_mackeySummand_right H t psi phi hpsi]


private lemma huppert_XI_5_3_mackeyCrossTerm_eq_conjugate
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b)
    (t : G) (hta : t • a = b) (htb : t • b = a)
    (hswapInverts : ∀ x : MulAction.stabilizer
        (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      t * (((x : MulAction.stabilizer G a) : G)) * t⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G)))
    (psi phi : Section1.ClassFunction (MulAction.stabilizer G a))
    (hphiChar : Section1.IsCharacter phi) :
    Section1.scalarProduct
        (Section1.mackeyIntersection
          (MulAction.stabilizer G a) (MulAction.stabilizer G a) t)
        (Section1.subgroupRestriction
          (Section1.mackeyIntersection
            (MulAction.stabilizer G a) (MulAction.stabilizer G a) t) psi)
        (Section1.mackeyConjugateRestriction
          (MulAction.stabilizer G a) (MulAction.stabilizer G a) t phi) =
      Section1.scalarProduct
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))
        (Section1.subgroupRestriction
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) psi)
        (Section1.conjugateCharacter
          (Section1.subgroupRestriction
            (MulAction.stabilizer (MulAction.stabilizer G a)
              (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) phi)) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let I := Section1.mackeyIntersection H H t
  have hInter : I = D := by
    simpa [H, D, I] using
      (huppert_XI_5_3_mackeyIntersection_eq_twoPointStabilizer a b hab t hta htb)
  let eD : I ≃* D :=
    { toFun := fun x => ⟨x.1, by
        rw [← hInter]
        exact x.2⟩
      invFun := fun x => ⟨x.1, by
        rw [hInter]
        exact x.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_mul' := by intro x y; apply Subtype.ext; rfl }
  have hresPsi :
      Section1.classFunctionLinearEquivOfMulEquiv eD
          (Section1.subgroupRestriction I psi) =
        Section1.subgroupRestriction D psi := by
    ext d
    rfl
  have hconjPhi :
      Section1.classFunctionLinearEquivOfMulEquiv eD
          (Section1.mackeyConjugateRestriction H H t phi) =
        Section1.conjugateCharacter
          (Section1.subgroupRestriction D phi) := by
    ext d
    rcases hphiChar with ⟨V, _hadd, _hmod, _hfd, rho, hphiEq⟩
    rw [hphiEq]
    have hconj :
        (⟨t * (((d : D) : H) : G) * t⁻¹, by
          have hdI := (eD.symm d).property
          change t * ((((eD.symm d : I) : H) : G)) * t⁻¹ ∈ H at hdI
          simpa [eD] using hdI⟩ : H) =
          ((d : H)⁻¹) := by
      apply Subtype.ext
      exact hswapInverts d
    change rho.character
        (⟨t * (((d : D) : H) : G) * t⁻¹, _⟩ : H) =
      star (rho.character (d : H))
    rw [hconj]
    exact Section1.representation_character_inv_eq_star_character rho (d : H)
  calc
    Section1.scalarProduct I
        (Section1.subgroupRestriction I psi)
        (Section1.mackeyConjugateRestriction H H t phi) =
      Section1.scalarProduct D
        (Section1.classFunctionLinearEquivOfMulEquiv eD
          (Section1.subgroupRestriction I psi))
        (Section1.classFunctionLinearEquivOfMulEquiv eD
          (Section1.mackeyConjugateRestriction H H t phi)) := by
            symm
            exact Section1.scalarProduct_classFunctionLinearEquivOfMulEquiv
              eD _ _
    _ = Section1.scalarProduct D
        (Section1.subgroupRestriction D psi)
        (Section1.conjugateCharacter
          (Section1.subgroupRestriction D phi)) := by rw [hresPsi, hconjPhi]


public lemma huppert_XI_5_3_ambient_induced_pairing
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (h2 : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (t : G) (hta : t • a = b) (htb : t • b = a)
    (hswapInverts : ∀ x : MulAction.stabilizer
        (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      t * (((x : MulAction.stabilizer G a) : G)) * t⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G)))
    (psi phi : Section1.ClassFunction (MulAction.stabilizer G a))
    (hpsiClass : Section1.IsClassFunction psi)
    (hphiClass : Section1.IsClassFunction phi)
    (hphiChar : Section1.IsCharacter phi) :
    Section1.scalarProduct G
        (Section1.inducedCF (MulAction.stabilizer G a) psi)
        (Section1.inducedCF (MulAction.stabilizer G a) phi) =
      Section1.scalarProduct (MulAction.stabilizer G a) psi phi +
        Section1.scalarProduct
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))
          (Section1.subgroupRestriction
            (MulAction.stabilizer (MulAction.stabilizer G a)
              (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) psi)
          (Section1.conjugateCharacter
            (Section1.subgroupRestriction
              (MulAction.stabilizer (MulAction.stabilizer G a)
                (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) phi)) := by
  rw [huppert_XI_5_3_scalarProduct_inducedCF_twoCoset h2 a b hab t hta htb
    psi phi hpsiClass hphiClass]
  rw [huppert_XI_5_3_mackeyCrossTerm_eq_conjugate a b hab t hta htb
    hswapInverts psi phi hphiChar]


public lemma huppert_XI_5_3_characterInflationByHom_conjugate_eq_inv
    {T Q : Type u} [Group T] [Finite T] [Group Q]
    (pi : T →* Q) (chi : Q →* ℂˣ) :
    Section1.conjugateCharacter
        (Section1.characterInflationByHom pi chi) =
      Section1.characterInflationByHom pi (chi⁻¹) := by
  ext t
  obtain ⟨n, rho, _hirr, hchar⟩ :=
    Section1.characterInflationByHom_isIrreducibleCharacterOnGroup pi chi
  have hinv :=
    Section1.representation_character_inv_eq_star_character rho t
  rw [← hchar] at hinv
  simpa [Section1.conjugateCharacter,
    Section1.characterInflationByHom] using hinv.symm

private theorem huppert_XI_5_3_inflation_injective_of_surjective
    {T Q : Type u} [Group T] [Finite T] [Group Q] [DecidableEq (Q →* ℂˣ)]
    (pi : T →* Q) (hpi : Function.Surjective pi) :
    Function.Injective
      (fun chi : Q →* ℂˣ =>
        Section1.characterInflationByHom pi chi) := by
  intro chi psi hEq
  apply DFunLike.ext chi psi
  intro q
  obtain ⟨t, rfl⟩ := hpi q
  apply Units.ext
  exact congrFun hEq t

private theorem huppert_XI_5_3_quotient_complement_map_bijective
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H) [F.Normal]
    (hcomp : F.IsComplement' D) :
    Function.Bijective
      ((QuotientGroup.mk' F).comp D.subtype) := by
  let qD : D →* H ⧸ F := (QuotientGroup.mk' F).comp D.subtype
  let e : H ⧸ F ≃* D := hcomp.symm.QuotientMulEquiv
  have heq : ∀ d : D, e (qD d) = d := by
    intro d
    exact quotientMulEquiv_mk_apply_of_isComplement' hcomp.symm d
  constructor
  · intro x y hxy
    exact (heq x).symm.trans ((congrArg e hxy).trans (heq y))
  · intro z
    refine ⟨e z, ?_⟩
    apply e.injective
    rw [heq]

private theorem huppert_XI_5_3_scalarProduct_inflations
    {T Q : Type u} [Group T] [Finite T] [Group Q] [DecidableEq (Q →* ℂˣ)]
    (pi : T →* Q) (hpi : Function.Surjective pi)
    (chi psi : Q →* ℂˣ) :
    Section1.scalarProduct T
        (Section1.characterInflationByHom pi chi)
        (Section1.characterInflationByHom pi psi) =
      if chi = psi then 1 else 0 := by
  classical
  have hchi :=
    Section1.characterInflationByHom_isIrreducibleCharacterOnGroup pi chi
  have hpsi :=
    Section1.characterInflationByHom_isIrreducibleCharacterOnGroup pi psi
  by_cases h : chi = psi
  · subst psi
    rw [if_pos rfl]
    exact Section1.scalarProduct_irreducibleCharacter_self hchi
  · rw [if_neg h]
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      hchi hpsi (fun hEq => h
        ((huppert_XI_5_3_inflation_injective_of_surjective pi hpi) hEq))

public theorem huppert_XI_5_3_quotient_linear_induced_pairing
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (h2 : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a)) [F.Normal]
    [DecidableEq ((MulAction.stabilizer G a ⧸ F) →* ℂˣ)]
    (D : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (t : G) (hta : t • a = b) (htb : t • b = a)
    (hD : D = MulAction.stabilizer (MulAction.stabilizer G a)
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))
    (hswapInverts : ∀ x : MulAction.stabilizer
        (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      t * (((x : MulAction.stabilizer G a) : G)) * t⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G)))
    (chi psi : (MulAction.stabilizer G a ⧸ F) →* ℂˣ) :
    let q : MulAction.stabilizer G a →*
        MulAction.stabilizer G a ⧸ F := QuotientGroup.mk' F
    let inflate : ((MulAction.stabilizer G a ⧸ F) →* ℂˣ) →
        Section1.ClassFunction (MulAction.stabilizer G a) :=
      fun z => Section1.characterInflationByHom q z
    Section1.scalarProduct G
        (Section1.inducedCF (MulAction.stabilizer G a) (inflate chi))
        (Section1.inducedCF (MulAction.stabilizer G a) (inflate psi)) =
      (if chi = psi then 1 else 0) +
        (if chi = psi⁻¹ then 1 else 0) := by
  classical
  let H := MulAction.stabilizer G a
  let Q := H ⧸ F
  let q : H →* Q := QuotientGroup.mk' F
  let inflate : (Q →* ℂˣ) → Section1.ClassFunction H :=
    fun z => Section1.characterInflationByHom q z
  let qD : D →* Q := q.comp D.subtype
  have hqSurj : Function.Surjective q := QuotientGroup.mk'_surjective F
  have hqDBij : Function.Bijective qD :=
    huppert_XI_5_3_quotient_complement_map_bijective F D hFrob.isComplement'
  have hrestrict : ∀ z : Q →* ℂˣ,
      Section1.subgroupRestriction D (inflate z) =
        Section1.characterInflationByHom qD z := by
    intro z
    ext d
    rfl
  have hpair := huppert_XI_5_3_ambient_induced_pairing
    h2 a b hab t hta htb hswapInverts (inflate chi) (inflate psi)
    (Section1.characterInflationByHom_isClassFunction q chi)
    (Section1.characterInflationByHom_isClassFunction q psi)
    (Section6.theorem_6_8_isCharacter_of_irreducible
      (Section1.characterInflationByHom_isIrreducibleCharacterOnGroup q psi))
  change Section1.scalarProduct G
      (Section1.inducedCF H (inflate chi))
      (Section1.inducedCF H (inflate psi)) =
    (if chi = psi then 1 else 0) + (if chi = psi⁻¹ then 1 else 0)
  rw [hpair]
  rw [huppert_XI_5_3_scalarProduct_inflations q hqSurj chi psi]
  rw [← hD]
  rw [hrestrict chi, hrestrict psi,
    huppert_XI_5_3_characterInflationByHom_conjugate_eq_inv]
  rw [huppert_XI_5_3_scalarProduct_inflations qD hqDBij.2 chi psi⁻¹]


public theorem huppert_XI_5_3_nonprincipal_induced_family
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    (h2 : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a)) [F.Normal]
    (D : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hD : D = MulAction.stabilizer (MulAction.stabilizer G a)
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))
    (hcyclic : IsCyclic D)
    (hodd : Odd (Nat.card D))
    (s : G) (hsa : s • a = b) (hsb : s • b = a)
    (hswapInverts : ∀ x : MulAction.stabilizer
        (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G))) :
    ∃ B : Finset (Section1.ClassFunction G),
      (∀ beta : B,
        Section1.IsIrreducibleCharacterOnGroup
          (beta : Section1.ClassFunction G)) ∧
      B.card = (Nat.card D - 1) / 2 ∧
      ∀ beta : Section1.ClassFunction G,
        beta ∈ B ↔
          ∃ chi : (MulAction.stabilizer G a ⧸ F) →* ℂˣ,
            chi ≠ 1 ∧
              Section1.inducedCF (MulAction.stabilizer G a)
                (Section1.characterInflationByHom
                  (QuotientGroup.mk' F) chi) = beta := by
  classical
  let H := MulAction.stabilizer G a
  let Q := H ⧸ F
  let q : H →* Q := QuotientGroup.mk' F
  let inflate : (Q →* ℂˣ) → Section1.ClassFunction H :=
    fun chi => Section1.characterInflationByHom q chi
  let ind : (Q →* ℂˣ) → Section1.ClassFunction G :=
    fun chi => Section1.inducedCF H (inflate chi)
  let A := Q →* ℂˣ
  let A0 := {chi : A // chi ≠ 1}
  let e : Q ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
  have hQcyclic : IsCyclic Q := e.isCyclic.mpr hcyclic
  let : IsCyclic Q := hQcyclic
  let : IsMulCommutative Q := IsCyclic.isMulCommutative
  let : CommGroup Q := IsMulCommutative.instCommGroup
  let : Fintype A := Fintype.ofFinite A
  let : Fintype A0 := Fintype.ofFinite A0
  have hdual : Nat.card A = Nat.card Q := by
    let : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) := by
      have : NeZero (Monoid.exponent Q) := by infer_instance
      exact Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  have hAcard : Nat.card A = Nat.card D :=
    hdual.trans (Nat.card_congr e.toEquiv)
  have hoddA : Odd (Nat.card A) := by
    rw [hAcard]
    exact hodd
  have hinv_ne : ∀ chi : A0, (chi : A) ≠ (chi : A)⁻¹ := by
    intro chi hfix
    apply chi.2
    apply huppert_XI_6_6_eq_one_of_sq_eq_one_of_odd_card hoddA
    calc
      (chi : A) ^ 2 = (chi : A) * (chi : A) := by rw [pow_two]
      _ = (chi : A) * (chi : A)⁻¹ :=
        congrArg (fun z : A => (chi : A) * z) hfix
      _ = 1 := by
        apply DFunLike.ext _ _
        intro x
        change (chi : A) x * ((chi : A) x)⁻¹ = 1
        exact mul_inv_cancel _
  have hpair : ∀ chi psi : A,
      Section1.scalarProduct G (ind chi) (ind psi) =
        (if chi = psi then 1 else 0) +
          (if chi = psi⁻¹ then 1 else 0) := by
    intro chi psi
    simpa [H, Q, q, inflate, ind] using
      (huppert_XI_5_3_quotient_linear_induced_pairing
        h2 a b hab F D hFrob s hsa hsb hD hswapInverts chi psi)
  have hirr : ∀ chi : A0,
      Section1.IsIrreducibleCharacterOnGroup (ind chi) := by
    intro chi
    have hnorm := hpair chi chi
    rw [if_pos rfl, if_neg (hinv_ne chi)] at hnorm
    norm_num at hnorm
    apply Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
    exact ⟨Section1.isCharacter_inducedCF_of_isCharacter H (inflate chi)
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
        (Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
          q (chi : A))), hnorm⟩
  have hIndEq : ∀ chi psi : A0,
      ind chi = ind psi ↔
        (chi : A) = (psi : A) ∨ (chi : A) = (psi : A)⁻¹ := by
    intro chi psi
    constructor
    · intro hEq
      have hsp : Section1.scalarProduct G (ind chi) (ind psi) = 1 := by
        rw [hEq]
        exact Section1.scalarProduct_irreducibleCharacter_self (hirr psi)
      rw [hpair] at hsp
      by_cases hsame : (chi : A) = (psi : A)
      · exact Or.inl hsame
      · rw [if_neg hsame] at hsp
        by_cases hinv : (chi : A) = (psi : A)⁻¹
        · exact Or.inr hinv
        · rw [if_neg hinv] at hsp
          norm_num at hsp
    · rintro (hsame | hinv)
      · exact congrArg ind hsame
      · have hsame : (chi : A) ≠ (psi : A) := by
          intro hEq
          exact hinv_ne chi (hinv.trans (by rw [← hEq]))
        have hsp := hpair chi psi
        rw [if_neg hsame, if_pos hinv] at hsp
        norm_num at hsp
        by_contra hne
        have hzero :=
          Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
            (hirr chi) (hirr psi) hne
        rw [hsp] at hzero
        norm_num at hzero
  let inv0 : A0 → A0 := fun chi =>
    ⟨(chi : A)⁻¹, by
      intro h
      apply chi.2
      calc
        (chi : A) = ((chi : A)⁻¹)⁻¹ := (inv_inv (chi : A)).symm
        _ = 1⁻¹ := by rw [congrArg (fun z : A => z⁻¹) h]
        _ = 1 := inv_one (G := A)⟩
  have hinv0_ne : ∀ chi : A0, inv0 chi ≠ chi := by
    intro chi hEq
    exact hinv_ne chi (congrArg Subtype.val hEq).symm
  let ind0 : A0 → Section1.ClassFunction G := fun chi => ind chi
  let B : Finset (Section1.ClassFunction G) := Finset.univ.image ind0
  have hfiberCard : ∀ beta ∈ B,
      ({chi ∈ (Finset.univ : Finset A0) | ind0 chi = beta}).card = 2 := by
    intro beta hbeta
    rcases Finset.mem_image.mp hbeta with ⟨chi, _hchi, hchiEq⟩
    have hfiber :
        {eta ∈ (Finset.univ : Finset A0) | ind0 eta = beta} =
          {chi, inv0 chi} := by
      ext eta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro heta
        have hEq : ind eta = ind chi := by
          simpa [ind0, hchiEq] using heta
        rcases (hIndEq eta chi).mp hEq with hsame | hinv
        · exact Or.inl (Subtype.ext hsame)
        · exact Or.inr (Subtype.ext hinv)
      · rintro (rfl | rfl)
        · exact hchiEq
        · have hEq : ind (inv0 chi) = ind chi :=
            (hIndEq (inv0 chi) chi).mpr (Or.inr rfl)
          exact hEq.trans hchiEq
    rw [hfiber]
    simp [Ne.symm (hinv0_ne chi)]
  have hcardEq : Fintype.card A0 = 2 * B.card := by
    apply Nat.le_antisymm
    · exact Finset.card_le_mul_card_image (Finset.univ : Finset A0) 2
        (fun beta hbeta => (hfiberCard beta hbeta).le)
    · exact Finset.mul_card_image_le_card (Finset.univ : Finset A0) 2
        (fun beta hbeta => (hfiberCard beta hbeta).ge)
  have hA0card : Fintype.card A0 = Nat.card D - 1 := by
    calc
      Fintype.card A0 = Nat.card A - 1 := by
        change Fintype.card {chi : A // chi ≠ 1} = Nat.card A - 1
        rw [Nat.card_eq_fintype_card]
        simp only [Fintype.card_subtype_compl (p := fun chi : A => chi = 1)]
        simp
      _ = Nat.card D - 1 := by rw [hAcard]
  have hBcard : B.card = (Nat.card D - 1) / 2 := by
    rw [hA0card] at hcardEq
    omega
  refine ⟨B, ?_, hBcard, ?_⟩
  · intro beta
    rcases Finset.mem_image.mp beta.2 with ⟨chi, _hchi, hchiEq⟩
    rw [← hchiEq]
    exact hirr chi
  · intro beta
    constructor
    · intro hbeta
      rcases Finset.mem_image.mp hbeta with ⟨chi, _hchi, hchiEq⟩
      exact ⟨chi, chi.property, hchiEq⟩
    · rintro ⟨chi, hchi, rfl⟩
      apply Finset.mem_image.mpr
      exact ⟨⟨chi, hchi⟩, Finset.mem_univ _, rfl⟩
/-- In a Frobenius group with cyclic complement, the conjugacy classes not
represented by a nonidentity kernel element are indexed by the complement. -/
private theorem huppert_XI_6_7_nontrivial_kernel_conjClasses_card
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hDcyclic : IsCyclic D) :
    Nat.card {C : ConjClasses H //
        ∃ x : H, x ∈ F ∧ x ≠ 1 ∧ C = ConjClasses.mk x} +
      Nat.card D = Nat.card (ConjClasses H) := by
  classical
  let : F.Normal := hFrob.normal
  let kerPred : ConjClasses H → Prop := fun C =>
    ∃ x : H, x ∈ F ∧ x ≠ 1 ∧ C = ConjClasses.mk x
  let KerClass := {C : ConjClasses H // kerPred C}
  let OtherClass := {C : ConjClasses H // ¬ kerPred C}
  let q : H →* H ⧸ F := QuotientGroup.mk' F
  let qD : D →* H ⧸ F := q.comp D.subtype
  let e : H ⧸ F ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
  let : IsMulCommutative D := IsCyclic.isMulCommutative
  let : CommGroup D := IsMulCommutative.instCommGroup
  have hquotComm (x y : H ⧸ F) : x * y = y * x := by
    apply e.injective
    simpa only [map_mul] using (mul_comm (e x) (e y))
  have hquotConj (c x : H) : q (c * x * c⁻¹) = q x := by
    calc
      q (c * x * c⁻¹) = q c * q x * (q c)⁻¹ := by
        simp only [map_mul, map_inv]
      _ = q x := by rw [hquotComm (q c) (q x)]; simp [mul_assoc]
  have hqDinj : Function.Injective qD :=
    (huppert_XI_5_3_quotient_complement_map_bijective
      F D hFrob.isComplement').1
  let otherClass : D → OtherClass := fun d =>
    ⟨ConjClasses.mk (d : H), by
      intro hker
      rcases hker with ⟨x, hxF, hxne, hclass⟩
      have hconj : IsConj (d : H) x :=
        ConjClasses.mk_eq_mk_iff_isConj.mp hclass
      rcases isConj_iff.mp hconj with ⟨c, hc⟩
      have hqdx : q (d : H) = q x :=
        (hquotConj c (d : H)).symm.trans (congrArg q hc)
      have hqx : q x = 1 :=
        (QuotientGroup.eq_one_iff (N := F) x).2 hxF
      have hdOne : d = 1 := by
        apply hqDinj
        change q (d : H) = q ((1 : D) : H)
        simpa [hqx] using hqdx
      have honeClass : ConjClasses.mk (1 : H) = ConjClasses.mk x := by
        simpa [hdOne] using hclass
      rcases isConj_iff.mp
          (ConjClasses.mk_eq_mk_iff_isConj.mp honeClass) with ⟨c, hc⟩
      apply hxne
      calc
        x = c * 1 * c⁻¹ := hc.symm
        _ = 1 := by simp⟩
  have hotherInjective : Function.Injective otherClass := by
    intro d₁ d₂ hEq
    have hclass : ConjClasses.mk (d₁ : H) = ConjClasses.mk (d₂ : H) :=
      congrArg Subtype.val hEq
    rcases isConj_iff.mp
        (ConjClasses.mk_eq_mk_iff_isConj.mp hclass) with ⟨c, hc⟩
    apply hqDinj
    change q (d₁ : H) = q (d₂ : H)
    exact (hquotConj c (d₁ : H)).symm.trans (congrArg q hc)
  have hotherSurjective : Function.Surjective otherClass := by
    intro C
    let x : H := Quotient.out C.1
    have hxClass : ConjClasses.mk x = C.1 := Quotient.out_eq C.1
    by_cases hxF : x ∈ F
    · have hxOne : x = 1 := by
        by_contra hxne
        exact C.2 ⟨x, hxF, hxne, hxClass.symm⟩
      refine ⟨1, ?_⟩
      apply Subtype.ext
      change ConjClasses.mk ((1 : D) : H) = C.1
      simpa [hxOne] using hxClass
    · obtain ⟨a, d, hconj⟩ :=
        frobenius_not_mem_kernel_conjugate_mem_complement F D hFrob hxF
      refine ⟨d, ?_⟩
      apply Subtype.ext
      change ConjClasses.mk (d : H) = C.1
      have hxd : ConjClasses.mk x = ConjClasses.mk (d : H) :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr
          (isConj_iff.mpr ⟨(a : H)⁻¹, by simpa using hconj⟩)
      exact hxd.symm.trans hxClass
  let otherEquiv : D ≃ OtherClass :=
    Equiv.ofBijective otherClass ⟨hotherInjective, hotherSurjective⟩
  have hotherCard : Nat.card OtherClass = Nat.card D :=
    (Nat.card_congr otherEquiv).symm
  let : Fintype (ConjClasses H) := Fintype.ofFinite (ConjClasses H)
  have hsub : Nat.card OtherClass =
      Nat.card (ConjClasses H) - Nat.card KerClass := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_compl kerPred)
  have hkerLe : Nat.card KerClass ≤ Nat.card (ConjClasses H) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  change Nat.card KerClass + Nat.card D = Nat.card (ConjClasses H)
  rw [hotherCard] at hsub
  omega
private theorem mulAction_fixedBy_card_eq_of_isConj
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {x y : G} (hxy : IsConj x y) :
    Nat.card (MulAction.fixedBy Omega x) =
      Nat.card (MulAction.fixedBy Omega y) := by
  rcases isConj_iff.mp hxy with ⟨c, rfl⟩
  let e : MulAction.fixedBy Omega x ≃
      MulAction.fixedBy Omega (c * x * c⁻¹) := {
    toFun z := ⟨c • z.1, by
      calc
        (c * x * c⁻¹) • (c • z.1) = c • (x • z.1) := by
          simp only [mul_smul, inv_smul_smul]
        _ = c • z.1 := by rw [z.2]⟩
    invFun z := ⟨c⁻¹ • z.1, by
      calc
        x • (c⁻¹ • z.1) =
            c⁻¹ • ((c * x * c⁻¹) • z.1) := by
              simp only [mul_smul, inv_smul_smul]
        _ = c⁻¹ • z.1 := by rw [z.2]⟩
    left_inv := by
      intro z
      apply Subtype.ext
      exact inv_smul_smul c z.1
    right_inv := by
      intro z
      apply Subtype.ext
      exact smul_inv_smul c z.1 }
  exact Nat.card_congr e
private theorem huppert_XI_6_7_orthogonal_to_principal_induced
    {G : Type u} [Group G] [Finite G]
    (perm chi : Section1.ClassFunction G)
    (hpermChar : Section1.IsCharacter perm)
    (hpermNorm : Section1.scalarProduct G perm perm = 2)
    (hpermOne : Section1.scalarProduct G perm
      (Section1.principalCharacter G) = 1)
    (honePerm : Section1.scalarProduct G
      (Section1.principalCharacter G) perm = 1)
    (hchiIrr : Section1.IsIrreducibleCharacterOnGroup chi)
    (hchiOne : chi ≠ Section1.principalCharacter G)
    (hchiAlpha : chi ≠ perm - Section1.principalCharacter G) :
    Section1.scalarProduct G chi perm = 0 := by
  classical
  have honeIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.principalCharacter G) :=
    Section3.principalCharacter_isIrreducibleCharacterOnGroup
  have hchiChar : Section1.IsCharacter chi :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchiIrr
  have hchiOneZero : Section1.scalarProduct G chi
      (Section1.principalCharacter G) = 0 :=
    Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hchiIrr hchiOne
  have honeChiZero : Section1.scalarProduct G
      (Section1.principalCharacter G) chi = 0 := by
    rw [← Section1.scalarProduct_star_swap]
    simp [hchiOneZero]
  have hchiSelf : Section1.scalarProduct G chi chi = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hchiIrr
  have honeSelf : Section1.scalarProduct G
      (Section1.principalCharacter G) (Section1.principalCharacter G) = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self honeIrr
  obtain ⟨n, hn⟩ :=
    Section1.scalarProduct_character_character_eq_nat perm chi hpermChar hchiChar
  have hnSwap : Section1.scalarProduct G chi perm = (n : ℂ) := by
    rw [← Section1.scalarProduct_star_swap]
    simp [hn]
  have hnLe : n ≤ 1 := by
    have hnonneg := Section5.cfNormSq_nonneg
      (perm - (n : ℂ) • chi)
    have heq : Section5.cfNormSq (perm - (n : ℂ) • chi) =
        2 - (n : ℝ) ^ 2 := by
      unfold Section5.cfNormSq
      simp only [Section5.scalarProduct_sub_left,
        Section5.scalarProduct_sub_right,
        Section1.scalarProduct_smul_right,
        Section1.scalarProduct_smul_left]
      rw [hpermNorm, hn, hnSwap, hchiSelf]
      norm_num
      ring
    rw [heq] at hnonneg
    have hnSq : n ^ 2 ≤ 2 := by exact_mod_cast (show (n : ℝ) ^ 2 ≤ 2 by linarith)
    nlinarith
  by_cases hnZero : n = 0
  · simpa [hnZero] using hnSwap
  have hnOne : n = 1 := by omega
  exfalso
  apply hchiAlpha
  have hzeroNorm : Section5.cfNormSq
      (perm - Section1.principalCharacter G - chi) = 0 := by
    unfold Section5.cfNormSq
    simp only [Section5.scalarProduct_sub_left,
      Section5.scalarProduct_sub_right]
    rw [hpermNorm, hpermOne, honePerm, honeSelf,
      hn, hnSwap, hchiOneZero, honeChiZero, hchiSelf]
    norm_num [hnOne]
  have hzero := Section5.cfNormSq_eq_zero hzeroNorm
  exact (sub_eq_zero.mp hzero).symm

set_option maxHeartbeats 800000 in
/-- The character-theoretic content of XI.6.5--XI.6.7: if the nilpotent
Frobenius kernel has mixed-prime order, the omitted irreducible character has
degree `|F| - 1`, hence that number divides the ambient group order. -/
private theorem huppert_XI_6_1_simple_odd_character_divisibility
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnil : Group.IsNilpotent F)
    (hsmall :
      2 * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) <
        Nat.card F - 1)
    (hodd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hcyclic : IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hswapInverts : ∀ s : G, s • a = b → s • b = a →
      ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : MulAction.stabilizer
            (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
              MulAction.stabilizer G a) : G)))
    (hsource :
      ¬ IsPrimePow (Nat.card F) ∨ IsMulCommutative F) :
    Nat.card F - 1 ∣ Nat.card G := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have hsmallD : 2 * Nat.card D < Nat.card F - 1 := by
    simpa [D, H] using hsmall
  let : F.Normal := hFrob.normal
  obtain ⟨_hOmegaCard, _hHcard, hGcard, hDdiv⟩ :=
    huppert_XI_6_1_action_parameters htwo_transitive a b hab F hFrob
  have hDgt : 1 < Nat.card D :=
    (Subgroup.one_lt_card_iff_ne_bot D).2 hFrob.complement_ne_bot
  have hTI :
      Suzuki.VI.IsTISubsetRelative H (F.map H.subtype : Set G) := by
    simpa [H] using
      (huppert_XI_6_5_kernelCarrier_relativeTI
        htwo_transitive a b hab F hFrob)
  obtain ⟨Y, hYirr, hYnonker, hYcomplete, hisometry, hdegreeZero⟩ :=
    huppert_XI_6_5_complete_nonker_induction_isometry
      H F D hFrob hTI
  have hYbot : Section6.inducedKernelFamily F ⊥ Y :=
    huppert_XI_6_5_complete_nonker_is_inducedKernelFamily
      F D hFrob Y hYirr hYnonker hYcomplete
  let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
  obtain ⟨degreeNat, hY0sub, hdegree, hY0degree, hdivDegree⟩ :=
    huppert_XI_6_5_derived_base_degree_data F Y hYbot
  have hY0eq_of_comm : IsMulCommutative F → Y0 = Y := by
    intro hFcomm
    let : IsMulCommutative F := hFcomm
    let : CommGroup F := IsMulCommutative.instCommGroup
    have hcommRoot : _root_.commutator F = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact CommGroup.center_eq_top
    have hcommAmbient : ⁅F, F⁆ = ⊥ := by
      rw [← Subgroup.map_subtype_commutator, hcommRoot]
      simp
    simpa [Y0, hcommAmbient] using
      (Section6.inducedKernelFamilyOf_eq_of_family hYbot hYbot)
  have hY0card : 2 ≤ Y0.card := by
    rcases hsource with hnotPrimePower | hFcomm
    · simpa [Y0] using
        (huppert_XI_6_5_derived_base_card_two
          F D hFrob hFnil hnotPrimePower Y hYbot)
    · have hY0eq : Y0 = Y := hY0eq_of_comm hFcomm
      have hYcharacter : ∀ theta : Section1.ClassFunction H,
          theta ∈ Y ↔
            Section1.IsIrreducibleCharacterOnGroup theta ∧
              ¬ Section1.subgroupInKernel' theta F := by
        intro theta
        constructor
        · intro htheta
          exact ⟨hYirr ⟨theta, htheta⟩,
            hYnonker ⟨theta, htheta⟩⟩
        · rintro ⟨hthetaIrr, hthetaNonker⟩
          exact hYcomplete theta hthetaIrr hthetaNonker
      have hsumEq :=
        Section6.theorem_6_6_Xset_sum_degree_sq_add_quotient_card
          hYcharacter (fun eta : Y => degreeNat eta) hdegree
      let eQ : H ⧸ F ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
      have hquotientCard : Nat.card (H ⧸ F) = Nat.card D :=
        Nat.card_congr eQ.toEquiv
      rw [hquotientCard, _hHcard] at hsumEq
      have hFindex :
          F.relIndex (⊤ : Subgroup H) = Nat.card D := by
        simpa [D, Subgroup.relIndex_top_right] using
          hFrob.isComplement'.symm.index_eq_card
      have hallDegree : ∀ eta : Y, degreeNat eta = Nat.card D := by
        intro eta
        rw [← hFindex]
        exact hY0degree ⟨eta, by
          change (eta : Section1.ClassFunction H) ∈ Y0
          rw [hY0eq]
          exact eta.property⟩
      have hsumCard :
          (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) =
            Y.card * Nat.card D ^ (2 : ℕ) := by
        calc
          (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) =
              ∑ _eta : Y, Nat.card D ^ (2 : ℕ) := by
                apply Finset.sum_congr rfl
                intro eta _heta
                rw [hallDegree eta]
          _ = Y.card * Nat.card D ^ (2 : ℕ) := by simp
      have hfactorEq :
          (Y.card * Nat.card D + 1) * Nat.card D =
            Nat.card F * Nat.card D := by
        calc
          (Y.card * Nat.card D + 1) * Nat.card D =
              Y.card * Nat.card D ^ (2 : ℕ) + Nat.card D := by ring
          _ = (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) + Nat.card D := by
            rw [hsumCard]
          _ = Nat.card F * Nat.card D := hsumEq
      have hcardFactor : Y.card * Nat.card D + 1 = Nat.card F :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos hfactorEq
      have hmulEq : Y.card * Nat.card D = Nat.card F - 1 := by omega
      by_contra hcard
      rw [hY0eq] at hcard
      have hYcardLe : Y.card ≤ 1 := by omega
      have hmulLe : Y.card * Nat.card D ≤ Nat.card D := by
        simpa using Nat.mul_le_mul_right (Nat.card D) hYcardLe
      have hFle : Nat.card F ≤ Nat.card D + 1 := by omega
      have hsubLe : Nat.card F - 1 ≤ Nat.card D := by omega
      omega
  have hgrowth : ∀ chi : Y,
      (chi : Section1.ClassFunction H) ∉ Y0 →
        2 * degreeNat chi * F.relIndex (⊤ : Subgroup H) <
          ∑ xi ∈ Y.filter
            (fun xi => degreeNat xi < degreeNat chi),
            degreeNat xi ^ 2 := by
    rcases hsource with hnotPrimePower | hFcomm
    · simpa [Y0] using
        (huppert_XI_6_5_frobenius_degree_growth
          F D hFrob hFnil hnotPrimePower hDdiv hodd hDgt
          Y hYirr hYbot degreeNat hdegree)
    · intro chi hchi
      exact (hchi (by rw [hY0eq_of_comm hFcomm]; exact chi.property)).elim
  have hcoherent :
      Section5.IsCoherentTriple Section5.puncturedSet Y
        (Section1.inducedCFLinear H) :=
    huppert_XI_6_coherent_of_degree_growth
      H Y Y0 (Section1.inducedCFLinear H)
      degreeNat (F.relIndex (⊤ : Subgroup H))
      hY0sub hYirr hisometry hdegreeZero hdegree
      hY0degree hY0card hdivDegree hgrowth
  rcases hcoherent with
    ⟨_hsource, _hnonempty, tau, htauIso, htauVirtual, htauAgree⟩
  have htau :
      Section6.coherentExtension Y (Section1.inducedCFLinear H) tau :=
    ⟨htauIso, htauVirtual, htauAgree⟩
  obtain ⟨epsilon, mu, hepsilon, hmuIrr, htau_mu, hmuInjective⟩ :=
    huppert_XI_6_coherentExtension_signed_irreducible_family htau hYirr
  obtain ⟨Z, hZirr, hZker, hZcard, hZcomplete⟩ :=
    huppert_XI_5_3_kernel_quotient_linear_family
      F D hFrob (by simpa [D, H] using hcyclic)
  have hYZdisjoint : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro chi hchiY hchiZ
    exact (hYnonker ⟨chi, hchiY⟩) (hZker ⟨chi, hchiZ⟩)
  have hYZcomplete : ∀ chi : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup chi →
        chi ∈ Y ∨ chi ∈ Z := by
    intro chi hchi
    by_cases hchiKer : Section1.subgroupInKernel' chi F
    · exact Or.inr (hZcomplete chi hchi hchiKer)
    · exact Or.inl (hYcomplete chi hchi hchiKer)
  have hHclassCount :
      Y.card + Nat.card D = Nat.card (ConjClasses H) := by
    rw [← hZcard]
    exact huppert_XI_6_disjoint_irreducible_finsets_card_eq_conjClasses
      Y Z hYZdisjoint hYirr hZirr hYZcomplete
  have hnonprincipalInducedFamily :
      ∃ B : Finset (Section1.ClassFunction G),
        (∀ beta : B,
          Section1.IsIrreducibleCharacterOnGroup
            (beta : Section1.ClassFunction G)) ∧
        B.card = (Nat.card D - 1) / 2 ∧
        ∀ zeta : (H ⧸ F) →* ℂˣ,
          zeta ≠ 1 →
            Section1.inducedCF H
              (Section1.characterInflationByHom (QuotientGroup.mk' F) zeta) ∈ B := by
    obtain ⟨s, hsa, hsb⟩ :=
      (MulAction.is_two_pretransitive_iff.mp htwo_transitive) hab hab.symm
    obtain ⟨B, hBirr, hBcard, _hBcomplete⟩ :=
      huppert_XI_5_3_nonprincipal_induced_family
        htwo_transitive a b hab F D hFrob rfl
        (by simpa [D, H] using hcyclic) (by simpa [D, H] using hodd)
        s hsa hsb (hswapInverts s hsa hsb)
    refine ⟨B, hBirr, hBcard, ?_⟩
    intro zeta hzeta
    apply (_hBcomplete _).2
    exact ⟨zeta, hzeta, rfl⟩
  obtain ⟨B, hBirr, hBcard, hBcomplete⟩ := hnonprincipalInducedFamily
  let alpha : Section1.ClassFunction G :=
    Section1.inducedCF H (Section1.principalCharacter H) -
      Section1.principalCharacter G
  have hkernelAmbientClasses :
      Y.card ≤ Nat.card (ConjClasses G) := by
    obtain ⟨K, hKirr, hKcomplete⟩ :=
      huppert_XI_6_complete_irreducible_finset (Q := G)
    have hKcard :
        K.card = Nat.card (ConjClasses G) :=
      huppert_XI_6_complete_irreducible_finset_card_eq_conjClasses
        K hKirr hKcomplete
    let f : Y → K := fun eta =>
      ⟨mu eta, hKcomplete (mu eta) (hmuIrr eta)⟩
    have hf : Function.Injective f := by
      intro eta xi hEq
      apply hmuInjective
      exact congrArg Subtype.val hEq
    calc
      Y.card = Nat.card Y := by simp
      _ ≤ Nat.card K := Nat.card_le_card_of_injective f hf
      _ = K.card := by simp
      _ = Nat.card (ConjClasses G) := hKcard
  have htwoPointAmbientClasses :
      (Nat.card D - 1) / 2 ≤ Nat.card (ConjClasses G) := by
    obtain ⟨K, hKirr, hKcomplete⟩ :=
      huppert_XI_6_complete_irreducible_finset (Q := G)
    have hKcard :
        K.card = Nat.card (ConjClasses G) :=
      huppert_XI_6_complete_irreducible_finset_card_eq_conjClasses
        K hKirr hKcomplete
    let f : B → K := fun beta =>
      ⟨beta, hKcomplete beta (hBirr beta)⟩
    have hf : Function.Injective f := by
      intro beta gamma hEq
      apply Subtype.ext
      exact congrArg (fun x : K =>
        (x : Section1.ClassFunction G)) hEq
    calc
      (Nat.card D - 1) / 2 = B.card := hBcard.symm
      _ = Nat.card B := by simp
      _ ≤ Nat.card K := Nat.card_le_card_of_injective f hf
      _ = K.card := by simp
      _ = Nat.card (ConjClasses G) := hKcard
  have htwoDerangementClasses :
      ∃ g h : G,
        (∀ x : Omega, g • x ≠ x) ∧
        (∀ x : Omega, h • x ≠ x) ∧
        ¬ IsConj g h := by
    have hpairOdd : ∀ x y : Omega, ∀ hxy : x ≠ y,
        Odd (Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G x)
            (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x))) := by
      intro x y hxy
      rw [zassenhaus_twoPointStabilizer_card_eq
        htwo_transitive a b x y hab hxy]
      simpa [D, H] using hodd
    have hswapAll :
        ∀ x y : Omega, ∀ hxy : x ≠ y, ∀ s : G,
          s • x = y → s • y = x →
            ∀ z : MulAction.stabilizer (MulAction.stabilizer G x)
              (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x),
              s * (((z : MulAction.stabilizer G x) : G)) * s⁻¹ =
                ((((z⁻¹ : MulAction.stabilizer
                  (MulAction.stabilizer G x)
                  (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x)) :
                    MulAction.stabilizer G x) : G)) := by
      intro x y hxy s hsx hsy z
      obtain ⟨g, hgx, hgy⟩ :=
        (MulAction.is_two_pretransitive_iff.mp htwo_transitive) hxy hab
      have hginva : g⁻¹ • a = x := by
        rw [← hgx, inv_smul_smul]
      have hginvb : g⁻¹ • b = y := by
        rw [← hgy, inv_smul_smul]
      let zg : G := ((z : MulAction.stabilizer G x) : G)
      have hzgx : zg • x = x := (z : MulAction.stabilizer G x).property
      have hzgy : zg • y = y := by
        exact congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp z.property)
      let zH : H := ⟨g * zg * g⁻¹, by
        calc
          (g * zg * g⁻¹) • a = g • (zg • (g⁻¹ • a)) := by
            simp only [mul_smul]
          _ = g • (zg • x) := by rw [hginva]
          _ = g • x := by rw [hzgx]
          _ = a := hgx⟩
      let zD : D := ⟨zH, by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        calc
          ((zH : H) : G) • b = g • (zg • (g⁻¹ • b)) := by
            simp only [zH, mul_smul]
          _ = g • (zg • y) := by rw [hginvb]
          _ = g • y := by rw [hzgy]
          _ = b := hgy⟩
      let sg : G := g * s * g⁻¹
      have hsga : sg • a = b := by
        calc
          sg • a = g • (s • (g⁻¹ • a)) := by
            simp only [sg, mul_smul]
          _ = g • (s • x) := by rw [hginva]
          _ = g • y := by rw [hsx]
          _ = b := hgy
      have hsgb : sg • b = a := by
        calc
          sg • b = g • (s • (g⁻¹ • b)) := by
            simp only [sg, mul_smul]
          _ = g • (s • y) := by rw [hginvb]
          _ = g • x := by rw [hsy]
          _ = a := hgx
      have hlocal := hswapInverts sg hsga hsgb zD
      change s * zg * s⁻¹ = zg⁻¹
      calc
        s * zg * s⁻¹ =
            g⁻¹ * (sg * (((zD : D) : H) : G) * sg⁻¹) * g := by
              dsimp [sg, zD, zH]
              group
        _ = g⁻¹ * ((((zD⁻¹ : D) : H) : G)) * g :=
          congrArg (fun q : G => g⁻¹ * q * g) hlocal
        _ = zg⁻¹ := by
          dsimp [zD, zH]
          group
    have hn : 1 < Nat.card F :=
      (Subgroup.one_lt_card_iff_ne_bot F).2 hFrob.kernel_ne_bot
    have hd : 1 < Nat.card D := hDgt
    have hOmegaCard : Nat.card Omega = Nat.card F + 1 := by
      simpa [Nat.card_eq_fintype_card] using _hOmegaCard
    have hGcard' :
        Nat.card G = (Nat.card F + 1) * Nat.card F * Nat.card D := by
      simpa only [_hOmegaCard] using hGcard
    let Der := {g : G // ∀ x : Omega, g • x ≠ x}
    have hderCount :
        2 * Nat.card Der + 2 * (Nat.card F) ^ 2 =
          (Nat.card F + 1) * Nat.card F * (Nat.card D + 1) :=
      zassenhaus_derangement_count
        htwo_transitive hat_most_two_fixed_points a b hab
        (Nat.card F) (Nat.card D) _hOmegaCard hGcard'
    have hDerPos : 0 < Nat.card Der := by
      by_contra hpos
      have hzero : Nat.card Der = 0 := Nat.eq_zero_of_not_pos hpos
      rw [hzero] at hderCount
      nlinarith [hsmall]
    have hDerNonempty : Nonempty Der :=
      (Nat.card_pos_iff.mp hDerPos).1
    apply huppert_XI_6_6_two_derangement_classes_of_centralizer_fixedPointFree
      (Nat.card F) (Nat.card D) hn hd (by simpa [D, H] using hodd)
      hOmegaCard hGcard' hderCount hDerNonempty
    intro g hg
    exact huppert_XI_6_6_derangement_centralizer_fixedPointFree
      hat_most_two_fixed_points hpairOdd hswapAll g hg
  have hambientClassLowerCore :
      Y.card ≤ Nat.card (ConjClasses G) →
      (Nat.card D - 1) / 2 ≤ Nat.card (ConjClasses G) →
      (∃ g h : G,
        (∀ x : Omega, g • x ≠ x) ∧
        (∀ x : Omega, h • x ≠ x) ∧
        ¬ IsConj g h) →
      Y.card + (Nat.card D - 1) / 2 + 3 ≤
        Nat.card (ConjClasses G) := by
    intro _hkernelLe _htwoPointLe hder
    obtain ⟨g, h, hgfree, hhfree, hgh⟩ := hder
    let KerClass := {C : ConjClasses H //
      ∃ x : H, x ∈ F ∧ x ≠ 1 ∧ C = ConjClasses.mk x}
    let : Fintype KerClass := Fintype.ofFinite KerClass
    let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
    have hKerCount :
        Nat.card KerClass + Nat.card D = Nat.card (ConjClasses H) := by
      simpa [KerClass, H, MulAction.mem_stabilizer_iff] using
        (huppert_XI_6_7_nontrivial_kernel_conjClasses_card
          F D hFrob (by simpa [D, H] using hcyclic))
    have hKerCard : Nat.card KerClass = Y.card := by
      omega
    let kerRep : KerClass → H := fun C => Classical.choose C.2
    have hkerRep_mem (C : KerClass) : kerRep C ∈ F :=
      (Classical.choose_spec C.2).1
    have hkerRep_ne (C : KerClass) : kerRep C ≠ 1 :=
      (Classical.choose_spec C.2).2.1
    have hkerRep_class (C : KerClass) :
        C.1 = ConjClasses.mk (kerRep C) :=
      (Classical.choose_spec C.2).2.2
    let kerRepF : KerClass → F := fun C => ⟨kerRep C, hkerRep_mem C⟩
    let oneMap : KerClass → ConjClasses G := fun C =>
      ConjClasses.mk (((kerRep C : H) : G))
    have honeMapInjective : Function.Injective oneMap := by
      intro C E hCE
      have hconj :
          IsConj (((kerRep C : H) : G)) (((kerRep E : H) : G)) :=
        ConjClasses.mk_eq_mk_iff_isConj.mp hCE
      rcases isConj_iff.mp hconj with ⟨c, hc⟩
      have hfix :
          (((kerRep E : H) : G)) • (c • a) = c • a := by
        rw [← hc]
        calc
          (c * (((kerRep C : H) : G)) * c⁻¹) • (c • a) =
              c • ((((kerRep C : H) : G)) • a) := by
                simp only [mul_smul, inv_smul_smul]
          _ = c • a := by rw [(kerRep C).property]
      have hca : c • a = a :=
        (huppert_XI_6_4_frobeniusKernel_uniqueFixedPoint
          htwo_transitive a b hab F hFrob (kerRepF E)
          (by
            intro hOne
            apply hkerRep_ne E
            exact congrArg Subtype.val hOne)
          (c • a)).mp hfix
      let cH : H := ⟨c, hca⟩
      have hcH :
          cH * kerRep C * cH⁻¹ = kerRep E := by
        apply Subtype.ext
        exact hc
      apply Subtype.ext
      calc
        C.1 = ConjClasses.mk (kerRep C) := hkerRep_class C
        _ = ConjClasses.mk (kerRep E) :=
          ConjClasses.mk_eq_mk_iff_isConj.mpr
            (isConj_iff.mpr ⟨cH, hcH⟩)
        _ = E.1 := (hkerRep_class E).symm
    let One : Finset (ConjClasses G) := Finset.univ.image oneMap
    have hOneCard : One.card = Y.card := by
      calc
        One.card = Fintype.card KerClass := by
          rw [Finset.card_image_of_injective _ honeMapInjective,
            Finset.card_univ]
        _ = Nat.card KerClass := Nat.card_eq_fintype_card.symm
        _ = Y.card := hKerCard
    let classFix : ConjClasses G → ℕ := fun C =>
      Nat.card (MulAction.fixedBy Omega (Quotient.out C))
    have hclassFix_mk (x : G) :
        classFix (ConjClasses.mk x) =
          Nat.card (MulAction.fixedBy Omega x) := by
      apply mulAction_fixedBy_card_eq_of_isConj
      exact ConjClasses.mk_eq_mk_iff_isConj.mp
        (Quotient.out_eq (ConjClasses.mk x))
    have hOneFix (C : One) : classFix C = 1 := by
      rcases Finset.mem_image.mp C.2 with ⟨K, _hK, hKC⟩
      rw [← hKC, hclassFix_mk]
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨a, (kerRep K).property⟩, ?_⟩
      intro z
      apply Subtype.ext
      exact
        (huppert_XI_6_4_frobeniusKernel_uniqueFixedPoint
          htwo_transitive a b hab F hFrob (kerRepF K)
          (by
            intro hOne
            apply hkerRep_ne K
            exact congrArg Subtype.val hOne)
          z.1).mp z.2
    let : Fintype D := Fintype.ofFinite D
    let D0 := {d : D // d ≠ 1}
    let : Fintype D0 := Fintype.ofFinite D0
    let twoMap : D0 → ConjClasses G := fun d =>
      ConjClasses.mk ((((d : D) : H) : G))
    have hDcyclic : IsCyclic D := by simpa [D, H] using hcyclic
    let : IsMulCommutative D := IsCyclic.isMulCommutative
    let : CommGroup D := IsMulCommutative.instCommGroup
    have htwoMapEq : ∀ d e : D0, twoMap d = twoMap e →
        (e : D) = (d : D) ∨ (e : D) = (d : D)⁻¹ := by
      intro d e hde
      let dg : G := (((d : D) : H) : G)
      let eg : G := (((e : D) : H) : G)
      have hconj : IsConj dg eg :=
        ConjClasses.mk_eq_mk_iff_isConj.mp hde
      rcases isConj_iff.mp hconj with ⟨c, hc⟩
      have hdne : dg ≠ 1 := by
        intro hOne
        apply d.2
        apply Subtype.ext
        apply Subtype.ext
        exact hOne
      have hene : eg ≠ 1 := by
        intro hOne
        apply e.2
        apply Subtype.ext
        apply Subtype.ext
        exact hOne
      have hdfa : dg • a = a := ((d : D) : H).property
      have hdfb : dg • b = b := by
        exact congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp (d : D).property)
      have hefa : eg • a = a := ((e : D) : H).property
      have hefb : eg • b = b := by
        exact congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp (e : D).property)
      have hefcA : eg • (c • a) = c • a := by
        rw [← hc]
        calc
          (c * dg * c⁻¹) • (c • a) = c • (dg • a) := by
            simp only [mul_smul, inv_smul_smul]
          _ = c • a := by rw [hdfa]
      have hefcB : eg • (c • b) = c • b := by
        rw [← hc]
        calc
          (c * dg * c⁻¹) • (c • b) = c • (dg • b) := by
            simp only [mul_smul, inv_smul_smul]
          _ = c • b := by rw [hdfb]
      have hca : c • a = a ∨ c • a = b := by
        by_cases hA : c • a = a
        · exact Or.inl hA
        by_cases hB : c • a = b
        · exact Or.inr hB
        exfalso
        exact (hat_most_two_fixed_points eg hene a b (c • a)
          hab (Ne.symm hA) (Ne.symm hB)) ⟨hefa, hefb, hefcA⟩
      have hcb : c • b = a ∨ c • b = b := by
        by_cases hA : c • b = a
        · exact Or.inl hA
        by_cases hB : c • b = b
        · exact Or.inr hB
        exfalso
        exact (hat_most_two_fixed_points eg hene a b (c • b)
          hab (Ne.symm hA) (Ne.symm hB)) ⟨hefa, hefb, hefcB⟩
      rcases hca with hca | hca
      · rcases hcb with hcb | hcb
        · exfalso
          apply hab
          exact (MulAction.toPerm c).injective (hca.trans hcb.symm)
        · left
          let cH : H := ⟨c, hca⟩
          let cD : D := ⟨cH, by
            rw [MulAction.mem_stabilizer_iff]
            exact Subtype.ext hcb⟩
          have hcommD : cD * (d : D) * cD⁻¹ = (d : D) := by
            rw [mul_comm cD (d : D)]
            simp [mul_assoc]
          have hcommG : c * dg * c⁻¹ = dg := by
            change c * (((d : D) : H) : G) * c⁻¹ = (((d : D) : H) : G)
            exact congrArg (fun q : D => (((q : D) : H) : G)) hcommD
          apply Subtype.ext
          apply Subtype.ext
          exact hc.symm.trans hcommG
      · rcases hcb with hcb | hcb
        · right
          have hinv :=
            hswapInverts c hca hcb (d : D)
          apply Subtype.ext
          apply Subtype.ext
          exact hc.symm.trans hinv
        · exfalso
          apply hab
          exact (MulAction.toPerm c).injective (hca.trans hcb.symm)
    let inv0 : D0 → D0 := fun d => ⟨(d : D)⁻¹, by
      intro hOne
      apply d.2
      have := congrArg (fun z : D => z⁻¹) hOne
      simpa using this⟩
    let Two : Finset (ConjClasses G) := Finset.univ.image twoMap
    have htwoFiberCard : ∀ C ∈ Two,
        ({d ∈ (Finset.univ : Finset D0) | twoMap d = C}).card ≤ 2 := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨d, _hd, hdC⟩
      have hsub :
          {e ∈ (Finset.univ : Finset D0) | twoMap e = C} ⊆
            {d, inv0 d} := by
        intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have hEq : twoMap d = twoMap e := hdC.trans he.symm
        rcases htwoMapEq d e hEq with hsame | hinv
        · exact Or.inl (Subtype.ext hsame)
        · exact Or.inr (Subtype.ext hinv)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    have hD0le : Fintype.card D0 ≤ 2 * Two.card := by
      calc
        Fintype.card D0 = (Finset.univ : Finset D0).card := by
          rw [Finset.card_univ]
        _ ≤ 2 * ((Finset.univ : Finset D0).image twoMap).card :=
          Finset.card_le_mul_card_image _ 2 htwoFiberCard
        _ = 2 * Two.card := rfl
    have hD0card : Fintype.card D0 = Nat.card D - 1 := by
      let : Fintype {d : D // d = 1} := Fintype.ofFinite _
      calc
        Fintype.card D0 =
            Fintype.card D - Fintype.card {d : D // d = 1} := by
          simp [D0]
        _ = Fintype.card D - 1 := by simp
        _ = Nat.card D - 1 := by rw [Nat.card_eq_fintype_card]
    have hTwoLower : (Nat.card D - 1) / 2 ≤ Two.card := by
      omega
    have hTwoFix (C : Two) : classFix C = 2 := by
      rcases Finset.mem_image.mp C.2 with ⟨d, _hd, hdC⟩
      rw [← hdC, hclassFix_mk]
      apply Nat.card_eq_two_iff.mpr
      let da : MulAction.fixedBy Omega ((((d : D) : H) : G)) :=
        ⟨a, ((d : D) : H).property⟩
      let db : MulAction.fixedBy Omega ((((d : D) : H) : G)) :=
        ⟨b, congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp (d : D).property)⟩
      refine ⟨da, db, ?_, ?_⟩
      · intro hEq
        exact hab (congrArg Subtype.val hEq)
      · ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_univ, iff_true]
        by_cases hza : z.1 = a
        · exact Or.inl (Subtype.ext hza)
        by_cases hzb : z.1 = b
        · exact Or.inr (Subtype.ext hzb)
        exfalso
        have hdneG : ((((d : D) : H) : G)) ≠ 1 := by
          intro hOne
          apply d.2
          apply Subtype.ext
          apply Subtype.ext
          exact hOne
        exact (hat_most_two_fixed_points
          ((((d : D) : H) : G)) hdneG a b z.1
          hab (Ne.symm hza) (Ne.symm hzb))
          ⟨da.2, db.2, z.2⟩
    have hOneTwo : Disjoint One Two := by
      rw [Finset.disjoint_left]
      intro C hCOne hCTwo
      have hOne := hOneFix ⟨C, hCOne⟩
      have hTwo := hTwoFix ⟨C, hCTwo⟩
      omega
    let C1 : ConjClasses G := ConjClasses.mk (1 : G)
    let Cg : ConjClasses G := ConjClasses.mk g
    let Ch : ConjClasses G := ConjClasses.mk h
    have hC1Fix : classFix C1 = Nat.card Omega := by
      rw [show C1 = ConjClasses.mk (1 : G) from rfl, hclassFix_mk]
      simp
    have hCgFix : classFix Cg = 0 := by
      rw [show Cg = ConjClasses.mk g from rfl, hclassFix_mk,
        Nat.card_eq_fintype_card]
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun z => hgfree z.1 z.2⟩
    have hChFix : classFix Ch = 0 := by
      rw [show Ch = ConjClasses.mk h from rfl, hclassFix_mk,
        Nat.card_eq_fintype_card]
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun z => hhfree z.1 z.2⟩
    have hOmegaGt : 2 < Nat.card Omega := by
      rw [show Nat.card Omega = Nat.card F + 1 by
        simpa [Nat.card_eq_fintype_card] using _hOmegaCard]
      omega
    have hC1g : C1 ≠ Cg := by
      intro hEq
      have := congrArg classFix hEq
      rw [hC1Fix, hCgFix] at this
      omega
    have hC1h : C1 ≠ Ch := by
      intro hEq
      have := congrArg classFix hEq
      rw [hC1Fix, hChFix] at this
      omega
    have hCgh : Cg ≠ Ch := by
      intro hEq
      exact hgh (ConjClasses.mk_eq_mk_iff_isConj.mp hEq)
    let Extra : Finset (ConjClasses G) := {C1, Cg, Ch}
    have hExtraCard : Extra.card = 3 := by
      simp [Extra, hC1g, hC1h, hCgh]
    have hOneExtra : Disjoint One Extra := by
      rw [Finset.disjoint_left]
      intro C hCOne hCExtra
      have hfix := hOneFix ⟨C, hCOne⟩
      change classFix C = 1 at hfix
      simp only [Extra, Finset.mem_insert, Finset.mem_singleton] at hCExtra
      rcases hCExtra with hEq | hEq | hEq
      · rw [hEq, hC1Fix] at hfix
        omega
      · rw [hEq, hCgFix] at hfix
        omega
      · rw [hEq, hChFix] at hfix
        omega
    have hTwoExtra : Disjoint Two Extra := by
      rw [Finset.disjoint_left]
      intro C hCTwo hCExtra
      have hfix := hTwoFix ⟨C, hCTwo⟩
      change classFix C = 2 at hfix
      simp only [Extra, Finset.mem_insert, Finset.mem_singleton] at hCExtra
      rcases hCExtra with hEq | hEq | hEq
      · rw [hEq, hC1Fix] at hfix
        omega
      · rw [hEq, hCgFix] at hfix
        omega
      · rw [hEq, hChFix] at hfix
        omega
    have hBaseExtra : Disjoint (One ∪ Two) Extra := by
      rw [Finset.disjoint_left]
      intro C hCBase hCExtra
      rcases Finset.mem_union.mp hCBase with hCOne | hCTwo
      · exact (Finset.disjoint_left.mp hOneExtra) hCOne hCExtra
      · exact (Finset.disjoint_left.mp hTwoExtra) hCTwo hCExtra
    have hUnionCard :
        ((One ∪ Two) ∪ Extra).card =
          One.card + Two.card + 3 := by
      rw [Finset.card_union_of_disjoint hBaseExtra,
        Finset.card_union_of_disjoint hOneTwo, hExtraCard]
    have hUpper :
        ((One ∪ Two) ∪ Extra).card ≤ Nat.card (ConjClasses G) := by
      calc
        ((One ∪ Two) ∪ Extra).card ≤
            (Finset.univ : Finset (ConjClasses G)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = Nat.card (ConjClasses G) := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [hUnionCard, hOneCard] at hUpper
    omega
  have hambientClassLower :
      Y.card + B.card + 3 ≤ Nat.card (ConjClasses G) := by
    rw [hBcard]
    exact hambientClassLowerCore hkernelAmbientClasses
      htwoPointAmbientClasses htwoDerangementClasses
  have homittedIrreducibleCore :
      Y.card + B.card + 3 ≤ Nat.card (ConjClasses G) →
      ∃ chi : Section1.ClassFunction G,
        Section1.IsIrreducibleCharacterOnGroup chi ∧
        chi ∉ B ∧
        (∀ eta : Y, chi ≠ mu eta) ∧
        chi ≠ Section1.principalCharacter G ∧
        chi ≠ alpha := by
    intro hlower
    obtain ⟨K, hKirr, hKcomplete⟩ :=
      huppert_XI_6_complete_irreducible_finset (Q := G)
    have hKcard : K.card = Nat.card (ConjClasses G) :=
      huppert_XI_6_complete_irreducible_finset_card_eq_conjClasses
        K hKirr hKcomplete
    let M : Finset (Section1.ClassFunction G) := Finset.univ.image mu
    have hMcard : M.card = Y.card := by
      dsimp [M]
      rw [Finset.card_image_of_injective _ hmuInjective]
      simp
    let P : Finset (Section1.ClassFunction G) :=
      {Section1.principalCharacter G, alpha}
    have hPcard : P.card ≤ 2 := by
      simpa [P] using
        (Finset.card_le_two (a := Section1.principalCharacter G) (b := alpha))
    let S : Finset (Section1.ClassFunction G) := (B ∪ M) ∪ P
    have hScard : S.card ≤ B.card + Y.card + 2 := by
      calc
        S.card ≤ (B ∪ M).card + P.card := by
          simpa [S] using Finset.card_union_le (B ∪ M) P
        _ ≤ (B.card + M.card) + 2 :=
          Nat.add_le_add (Finset.card_union_le B M) hPcard
        _ = B.card + Y.card + 2 := by rw [hMcard]
    have hSltK : S.card < K.card := by
      rw [hKcard]
      omega
    have hnotSubset : ¬ K ⊆ S := by
      intro hsub
      exact (not_lt_of_ge (Finset.card_le_card hsub)) hSltK
    rcases Finset.not_subset.mp hnotSubset with ⟨chi, hchiK, hchiS⟩
    refine ⟨chi, hKirr ⟨chi, hchiK⟩, ?_, ?_, ?_, ?_⟩
    · intro hchiB
      apply hchiS
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hchiB)
    · intro eta hchiMu
      apply hchiS
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [hchiMu]
      exact Finset.mem_image.mpr ⟨eta, Finset.mem_univ eta, rfl⟩
    · intro hchiOne
      apply hchiS
      apply Finset.mem_union_right
      simp [P, hchiOne]
    · intro hchiAlpha
      apply hchiS
      apply Finset.mem_union_right
      simp [P, hchiAlpha]
  obtain ⟨chi, hchiIrr, hchiB, hchiMu, hchiOne, hchiAlpha⟩ :=
    homittedIrreducibleCore hambientClassLower
  have homittedDegreeMultipleCore :
      Section1.IsIrreducibleCharacterOnGroup chi →
      chi ∉ B →
      (∀ eta : Y, chi ≠ mu eta) →
      chi ≠ Section1.principalCharacter G →
      chi ≠ alpha →
      ∃ nu : ℕ, 0 < nu ∧
        Section1.degree chi = ((nu * (Nat.card F - 1) : ℕ) : ℂ) := by
      intro hchiIrr' hchiB' hchiMu' hchiOne' hchiAlpha'
      have hchiChar : Section1.IsCharacter chi :=
        Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchiIrr'
      have hchiClass : Section1.IsClassFunction chi :=
        Section1.isCharacter_isClassFunction chi hchiChar
      let resChi : Section1.ClassFunction H :=
        Section1.subgroupRestriction H chi
      have hresChiChar : Section1.IsCharacter resChi := by
        rcases
            Section1.subgroupRestriction_eq_representation_character_of_isCharacter
              H chi hchiChar with
          ⟨V, _hadd, _hmod, _hfd, rho, hres⟩
        exact ⟨V, inferInstance, inferInstance, inferInstance, rho, hres⟩
      have hresChiClass : Section1.IsClassFunction resChi :=
        Section1.isCharacter_isClassFunction resChi hresChiChar
      let eQ : H ⧸ F ≃* D :=
        hFrob.isComplement'.symm.QuotientMulEquiv
      have hQcyclic : IsCyclic (H ⧸ F) :=
        eQ.isCyclic.mpr (by simpa [D, H] using hcyclic)
      let : IsCyclic (H ⧸ F) := hQcyclic
      let : IsMulCommutative (H ⧸ F) :=
        IsCyclic.isMulCommutative
      let : CommGroup (H ⧸ F) :=
        IsMulCommutative.instCommGroup
      have hFindex :
          F.relIndex (⊤ : Subgroup H) = Nat.card D := by
        simpa [D, Subgroup.relIndex_top_right] using
          hFrob.isComplement'.symm.index_eq_card
      have hindexPos : 0 < F.relIndex (⊤ : Subgroup H) := by
        rw [hFindex]
        exact Nat.card_pos
      have hY0ne : Y0.Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨eta0, heta0Y0⟩ := hY0ne
      let eta0Y : Y := ⟨eta0, hY0sub heta0Y0⟩
      let multiplicity : Y → ℕ := fun eta =>
        Classical.choose
          (Section1.scalarProduct_character_character_eq_nat
            (eta : Section1.ClassFunction H) resChi
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              (hYirr eta))
            hresChiChar)
      have hmultiplicity : ∀ eta : Y,
          Section1.scalarProduct H
              (eta : Section1.ClassFunction H) resChi =
            (multiplicity eta : ℂ) := by
        intro eta
        exact Classical.choose_spec
          (Section1.scalarProduct_character_character_eq_nat
            (eta : Section1.ClassFunction H) resChi
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              (hYirr eta))
            hresChiChar)
      let nu : ℕ := multiplicity eta0Y
      have hdivAll : ∀ eta : Y,
          F.relIndex (⊤ : Subgroup H) ∣ degreeNat eta := by
        intro eta
        by_cases heta0 : (eta : Section1.ClassFunction H) ∈ Y0
        · rw [hY0degree
            (⟨eta, heta0⟩ : Y0)]
        · exact hdivDegree eta heta0
      let dtheta : Y → ℕ := fun eta =>
        Classical.choose (hdivAll eta)
      have hdegreeFactor : ∀ eta : Y,
          degreeNat eta =
            F.relIndex (⊤ : Subgroup H) * dtheta eta := by
        intro eta
        exact Classical.choose_spec (hdivAll eta)
      have hmuZero : ∀ eta : Y,
          Section1.scalarProduct G (mu eta) chi = 0 := by
        intro eta
        exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hmuIrr eta) hchiIrr' (Ne.symm (hchiMu' eta))
      have htauZero : ∀ eta : Y,
          Section1.scalarProduct G
              (tau (eta : Section1.ClassFunction H)) chi = 0 := by
        intro eta
        rw [htau_mu eta, Section1.scalarProduct_smul_left,
          hmuZero eta]
        simp
      have hratio : ∀ eta : Y,
          F.relIndex (⊤ : Subgroup H) * multiplicity eta =
            degreeNat eta * nu := by
        intro eta
        let combo : Section1.ClassFunction H :=
          ((F.relIndex (⊤ : Subgroup H) : ℕ) : ℂ) •
              (eta : Section1.ClassFunction H) -
            (degreeNat eta : ℂ) •
              (eta0Y : Section1.ClassFunction H)
        have hcomboMem :
            Section5.integerSpanOn Y Section5.puncturedSet combo := by
          refine ⟨Section5.integerSpan_sub
              (Section5.integerSpan_zsmul
                (F.relIndex (⊤ : Subgroup H) : ℤ)
                (Section5.integerSpan_of_mem Y eta.property))
              (Section5.integerSpan_zsmul
                (degreeNat eta : ℤ)
                (Section5.integerSpan_of_mem Y eta0Y.property)), ?_⟩
          rw [Section1.supportedOn_iff]
          intro g hg
          have hg1 : g = 1 := by
            simpa [Section5.puncturedSet] using hg
          subst g
          have hetaOne :
              (eta : Section1.ClassFunction H) 1 =
                (degreeNat eta : ℂ) := by
            simpa [Section1.degree_apply] using hdegree eta
          have heta0One :
              (eta0Y : Section1.ClassFunction H) 1 =
                (F.relIndex (⊤ : Subgroup H) : ℂ) := by
            have hbase := hY0degree
              (⟨eta0, heta0Y0⟩ : Y0)
            have hdegree0 := hdegree eta0Y
            rw [hbase] at hdegree0
            simpa [Section1.degree_apply] using hdegree0
          simp [combo, hetaOne, heta0One]
          ring
        have hcomboTauZero :
            Section1.scalarProduct G (tau combo) chi = 0 := by
          dsimp [combo]
          rw [map_sub, map_smul, map_smul,
            Section5.scalarProduct_sub_left,
            Section1.scalarProduct_smul_left,
            Section1.scalarProduct_smul_left,
            htauZero eta, htauZero eta0Y]
          simp
        have hagree :
            tau combo = Section1.inducedCFLinear H combo :=
          htauAgree combo hcomboMem
        rw [hagree] at hcomboTauZero
        change Section1.scalarProduct G
            (Section1.inducedCF H combo) chi = 0 at hcomboTauZero
        rw [Section1.scalarProduct_inducedCF_left
          H combo chi hchiClass] at hcomboTauZero
        dsimp [combo] at hcomboTauZero
        rw [Section5.scalarProduct_sub_left,
          Section1.scalarProduct_smul_left,
          Section1.scalarProduct_smul_left,
          hmultiplicity eta, hmultiplicity eta0Y] at hcomboTauZero
        change
          (F.relIndex (⊤ : Subgroup H) : ℂ) *
                (multiplicity eta : ℂ) -
              (degreeNat eta : ℂ) * (nu : ℂ) = 0
          at hcomboTauZero
        have hratioComplex :
            (F.relIndex (⊤ : Subgroup H) : ℂ) *
                (multiplicity eta : ℂ) =
              (degreeNat eta : ℂ) * (nu : ℂ) :=
          sub_eq_zero.mp hcomboTauZero
        exact_mod_cast hratioComplex
      have hmultiplicityFactor : ∀ eta : Y,
          multiplicity eta = dtheta eta * nu := by
        intro eta
        apply Nat.eq_of_mul_eq_mul_left hindexPos
        have h := hratio eta
        rw [hdegreeFactor eta] at h
        simpa [Nat.mul_assoc] using h
      let perm : Section1.ClassFunction G :=
        Section1.inducedCF H (Section1.principalCharacter H)
      have honeIrrH :
          Section1.IsIrreducibleCharacterOnGroup
            (Section1.principalCharacter H) :=
        Section3.principalCharacter_isIrreducibleCharacterOnGroup
      have honeIrrD :
          Section1.IsIrreducibleCharacterOnGroup
            (Section1.principalCharacter D) :=
        Section3.principalCharacter_isIrreducibleCharacterOnGroup
      have honeCharH :
          Section1.IsCharacter (Section1.principalCharacter H) :=
        Section1.isCharacter_of_isIrreducibleCharacterOnGroup honeIrrH
      have honeClassH :
          Section1.IsClassFunction (Section1.principalCharacter H) :=
        Section1.isCharacter_isClassFunction
          (Section1.principalCharacter H) honeCharH
      have hpermChar : Section1.IsCharacter perm :=
        Section1.isCharacter_inducedCF_of_isCharacter
          H (Section1.principalCharacter H) honeCharH
      have hpermNorm :
          Section1.scalarProduct G perm perm = 2 := by
        obtain ⟨s, hsa, hsb⟩ :=
          (MulAction.is_two_pretransitive_iff.mp htwo_transitive)
            hab hab.symm
        have hpair := huppert_XI_5_3_ambient_induced_pairing
          htwo_transitive a b hab s hsa hsb
          (hswapInverts s hsa hsb)
          (Section1.principalCharacter H)
          (Section1.principalCharacter H)
          honeClassH honeClassH honeCharH
        have hresOne :
            Section1.subgroupRestriction D
                (Section1.principalCharacter H) =
              Section1.principalCharacter D := by
          ext d
          rfl
        have hconjOne :
            Section1.conjugateCharacter
                (Section1.principalCharacter D) =
              Section1.principalCharacter D := by
          ext d
          simp [Section1.conjugateCharacter,
            Section1.principalCharacter]
        change Section1.scalarProduct G perm perm =
          Section1.scalarProduct H
              (Section1.principalCharacter H)
              (Section1.principalCharacter H) +
            Section1.scalarProduct D
              (Section1.subgroupRestriction D
                (Section1.principalCharacter H))
              (Section1.conjugateCharacter
                (Section1.subgroupRestriction D
                  (Section1.principalCharacter H))) at hpair
        rw [Section1.scalarProduct_irreducibleCharacter_self honeIrrH,
          hresOne, hconjOne,
          Section1.scalarProduct_irreducibleCharacter_self honeIrrD] at hpair
        norm_num at hpair
        exact hpair
      have hpermOne :
          Section1.scalarProduct G perm
              (Section1.principalCharacter G) = 1 := by
        have honeClassG : Section1.IsClassFunction
            (Section1.principalCharacter G) :=
          Section1.isCharacter_isClassFunction
            (Section1.principalCharacter G)
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              Section3.principalCharacter_isIrreducibleCharacterOnGroup)
        have hpair := Section1.scalarProduct_inducedCF_left
          H (Section1.principalCharacter H)
          (Section1.principalCharacter G) honeClassG
        change Section1.scalarProduct G perm
            (Section1.principalCharacter G) =
          Section1.scalarProduct H
            (Section1.principalCharacter H)
            (Section1.subgroupRestriction H
              (Section1.principalCharacter G)) at hpair
        have hresOne :
            Section1.subgroupRestriction H
                (Section1.principalCharacter G) =
              Section1.principalCharacter H := by
          ext h
          rfl
        rw [hresOne,
          Section1.scalarProduct_irreducibleCharacter_self honeIrrH] at hpair
        exact hpair
      have honePerm :
          Section1.scalarProduct G
              (Section1.principalCharacter G) perm = 1 := by
        rw [← Section1.scalarProduct_star_swap
          (Section1.principalCharacter G) perm, hpermOne]
        simp
      have hchiPermZero :
          Section1.scalarProduct G chi perm = 0 := by
        apply huppert_XI_6_7_orthogonal_to_principal_induced
          perm chi hpermChar hpermNorm hpermOne honePerm hchiIrr'
          hchiOne'
        simpa [perm, alpha] using hchiAlpha'
      have hpermChiZero :
          Section1.scalarProduct G perm chi = 0 := by
        rw [← Section1.scalarProduct_star_swap perm chi,
          hchiPermZero]
        simp
      have hZcoefficient : ∀ zeta : Z,
          Section1.scalarProduct H
              (zeta : Section1.ClassFunction H) resChi = 0 := by
        intro zeta
        have hzetaDegree :
            Section1.degree (zeta : Section1.ClassFunction H) = 1 :=
          huppert_XI_5_3_degree_one_of_quotient_commutative
            F (zeta : Section1.ClassFunction H)
            (hZirr zeta) (hZker zeta)
        obtain ⟨lambda, hzetaEq⟩ :=
          Section1.exists_linearCharacter_of_irreducible_degree_one
            (hZirr zeta) hzetaDegree
        have hFle : F ≤ lambda.ker := by
          intro f hf
          change lambda f = 1
          apply Units.ext
          have hval := hZker zeta ⟨f, hf⟩
          rw [hzetaEq] at hval
          simpa [Section1.degree, hzetaDegree] using hval
        let quotientChar : (H ⧸ F) →* ℂˣ :=
          QuotientGroup.lift F lambda hFle
        have hzetaInflate :
            (zeta : Section1.ClassFunction H) =
              Section1.characterInflationByHom
                (QuotientGroup.mk' F) quotientChar := by
          ext h
          rw [hzetaEq]
          exact congrArg Units.val
            (QuotientGroup.lift_mk'
              (N := F) (φ := lambda) hFle h).symm
        by_cases hquotientOne : quotientChar = 1
        · have hzetaOne :
              (zeta : Section1.ClassFunction H) =
                Section1.principalCharacter H := by
            rw [hzetaInflate, hquotientOne]
            ext h
            simp [Section1.characterInflationByHom,
              Section1.principalCharacter]
          calc
            Section1.scalarProduct H
                (zeta : Section1.ClassFunction H) resChi =
              Section1.scalarProduct G
                (Section1.inducedCF H
                  (zeta : Section1.ClassFunction H)) chi := by
                symm
                exact Section1.scalarProduct_inducedCF_left
                  H (zeta : Section1.ClassFunction H) chi hchiClass
            _ = Section1.scalarProduct G perm chi := by
              rw [hzetaOne]
            _ = 0 := hpermChiZero
        · have hIndMem :
              Section1.inducedCF H
                  (Section1.characterInflationByHom
                    (QuotientGroup.mk' F) quotientChar) ∈ B :=
            hBcomplete quotientChar hquotientOne
          have hIndIrr :
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF H
                  (Section1.characterInflationByHom
                    (QuotientGroup.mk' F) quotientChar)) :=
            hBirr ⟨_, hIndMem⟩
          have hIndNe :
              Section1.inducedCF H
                  (Section1.characterInflationByHom
                    (QuotientGroup.mk' F) quotientChar) ≠ chi := by
            intro hEq
            apply hchiB'
            rw [← hEq]
            exact hIndMem
          have hIndZero :
              Section1.scalarProduct G
                (Section1.inducedCF H
                  (Section1.characterInflationByHom
                    (QuotientGroup.mk' F) quotientChar)) chi = 0 :=
            Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              hIndIrr hchiIrr' hIndNe
          calc
            Section1.scalarProduct H
                (zeta : Section1.ClassFunction H) resChi =
              Section1.scalarProduct G
                (Section1.inducedCF H
                  (zeta : Section1.ClassFunction H)) chi := by
                symm
                exact Section1.scalarProduct_inducedCF_left
                  H (zeta : Section1.ClassFunction H) chi hchiClass
            _ = Section1.scalarProduct G
                (Section1.inducedCF H
                  (Section1.characterInflationByHom
                    (QuotientGroup.mk' F) quotientChar)) chi := by
              rw [hzetaInflate]
            _ = 0 := hIndZero
      have hZcoefficientSwap : ∀ zeta : Z,
          Section1.scalarProduct H resChi
              (zeta : Section1.ClassFunction H) = 0 := by
        intro zeta
        rw [← Section1.scalarProduct_star_swap resChi zeta,
          hZcoefficient zeta]
        simp
      have hYcharacter : ∀ theta : Section1.ClassFunction H,
          theta ∈ Y ↔
            Section1.IsIrreducibleCharacterOnGroup theta ∧
              ¬ Section1.subgroupInKernel' theta F := by
        intro theta
        constructor
        · intro htheta
          exact ⟨hYirr ⟨theta, htheta⟩,
            hYnonker ⟨theta, htheta⟩⟩
        · rintro ⟨hthetaIrr, hthetaNonker⟩
          exact hYcomplete theta hthetaIrr hthetaNonker
      have hsumSqRaw :=
        Section6.theorem_6_6_Xset_sum_degree_sq_add_quotient_card
          hYcharacter (fun eta : Y => degreeNat eta) hdegree
      have hquotientCard : Nat.card (H ⧸ F) = Nat.card D :=
        Nat.card_congr eQ.toEquiv
      have hFcardOne : 1 ≤ Nat.card F := Nat.card_pos
      have hcardSplit :
          Nat.card F * Nat.card D =
            Nat.card D * (Nat.card F - 1) + Nat.card D := by
        calc
          Nat.card F * Nat.card D =
              ((Nat.card F - 1) + 1) * Nat.card D := by
                rw [Nat.sub_add_cancel hFcardOne]
          _ = Nat.card D * (Nat.card F - 1) + Nat.card D := by
            ring
      have hsumSq :
          (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) =
            F.relIndex (⊤ : Subgroup H) * (Nat.card F - 1) := by
        rw [hquotientCard, _hHcard] at hsumSqRaw
        rw [hcardSplit] at hsumSqRaw
        rw [hFindex]
        exact Nat.add_right_cancel hsumSqRaw
      have hsumFactor :
          (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) =
            F.relIndex (⊤ : Subgroup H) *
              ∑ eta : Y, dtheta eta * degreeNat eta := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro eta _heta
        rw [hdegreeFactor eta]
        ring
      have hweightedDegree :
          (∑ eta : Y, dtheta eta * degreeNat eta) =
            Nat.card F - 1 := by
        apply Nat.eq_of_mul_eq_mul_left hindexPos
        calc
          F.relIndex (⊤ : Subgroup H) *
                ∑ eta : Y, dtheta eta * degreeNat eta =
              ∑ eta : Y, degreeNat eta ^ (2 : ℕ) :=
            hsumFactor.symm
          _ = F.relIndex (⊤ : Subgroup H) *
              (Nat.card F - 1) := hsumSq
      let W : Finset (Section1.ClassFunction H) := Y ∪ Z
      have hWirr : ∀ theta : W,
          Section1.IsIrreducibleCharacterOnGroup
            (theta : Section1.ClassFunction H) := by
        intro theta
        rcases Finset.mem_union.mp theta.property with htheta | htheta
        · exact hYirr ⟨theta, htheta⟩
        · exact hZirr ⟨theta, htheta⟩
      have hWcomplete : ∀ theta : Section1.ClassFunction H,
          Section1.IsIrreducibleCharacterOnGroup theta →
            theta ∈ W := by
        intro theta htheta
        exact Finset.mem_union.mpr (hYZcomplete theta htheta)
      let term : Section1.ClassFunction H → ℂ := fun theta =>
        Section1.scalarProduct H resChi theta * theta 1
      have hExpandSubtype :
          resChi 1 = ∑ theta : W, term theta := by
        simpa [term] using
          (huppert_XI_6_complete_irreducible_finset_apply_eq_sum_scalarProduct
            W hWirr hWcomplete resChi hresChiClass (1 : H))
      have hAttachW :
          (∑ theta : W, term theta) =
            ∑ theta ∈ W, term theta := by
        rw [Finset.univ_eq_attach W]
        simpa using Finset.sum_attach W term
      have hExpandFinset :
          resChi 1 = ∑ theta ∈ W, term theta :=
        hExpandSubtype.trans hAttachW
      have hYcoefficient : ∀ eta : Y,
          Section1.scalarProduct H resChi
              (eta : Section1.ClassFunction H) =
            (multiplicity eta : ℂ) := by
        intro eta
        rw [← Section1.scalarProduct_star_swap resChi eta,
          hmultiplicity eta]
        simp
      have hYone : ∀ eta : Y,
          (eta : Section1.ClassFunction H) 1 =
            (degreeNat eta : ℂ) := by
        intro eta
        simpa [Section1.degree_apply] using hdegree eta
      have hYterm : ∀ eta : Y,
          term (eta : Section1.ClassFunction H) =
            ((nu * (dtheta eta * degreeNat eta) : ℕ) : ℂ) := by
        intro eta
        change Section1.scalarProduct H resChi
            (eta : Section1.ClassFunction H) *
              (eta : Section1.ClassFunction H) 1 = _
        rw [hYcoefficient eta, hYone eta,
          hmultiplicityFactor eta]
        norm_cast
        ring
      have hAttachY :
          (∑ eta : Y, term (eta : Section1.ClassFunction H)) =
            ∑ eta ∈ Y, term eta := by
        rw [Finset.univ_eq_attach Y]
        simpa using Finset.sum_attach Y term
      have hYsum :
          (∑ eta ∈ Y, term eta) =
            ((nu * (Nat.card F - 1) : ℕ) : ℂ) := by
        calc
          (∑ eta ∈ Y, term eta) =
              ∑ eta : Y, term (eta : Section1.ClassFunction H) :=
            hAttachY.symm
          _ = ∑ eta : Y,
              ((nu * (dtheta eta * degreeNat eta) : ℕ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro eta _heta
            exact hYterm eta
          _ = ((nu *
                ∑ eta : Y, dtheta eta * degreeNat eta : ℕ) : ℂ) := by
            norm_cast
            rw [Finset.mul_sum]
          _ = ((nu * (Nat.card F - 1) : ℕ) : ℂ) := by
            rw [hweightedDegree]
      have hZterm : ∀ zeta : Z,
          term (zeta : Section1.ClassFunction H) = 0 := by
        intro zeta
        change Section1.scalarProduct H resChi
            (zeta : Section1.ClassFunction H) *
              (zeta : Section1.ClassFunction H) 1 = 0
        rw [hZcoefficientSwap zeta]
        simp
      have hAttachZ :
          (∑ zeta : Z, term (zeta : Section1.ClassFunction H)) =
            ∑ zeta ∈ Z, term zeta := by
        rw [Finset.univ_eq_attach Z]
        simpa using Finset.sum_attach Z term
      have hZsum : (∑ zeta ∈ Z, term zeta) = 0 := by
        rw [← hAttachZ]
        apply Finset.sum_eq_zero
        intro zeta _hzeta
        exact hZterm zeta
      have hdegreeEq :
          Section1.degree chi =
            ((nu * (Nat.card F - 1) : ℕ) : ℂ) := by
        calc
          Section1.degree chi = resChi 1 := by
            rfl
          _ = ∑ theta ∈ W, term theta := hExpandFinset
          _ = (∑ eta ∈ Y, term eta) +
              ∑ zeta ∈ Z, term zeta := by
            simpa [W] using
              (Finset.sum_union hYZdisjoint
                (f := term))
          _ = ((nu * (Nat.card F - 1) : ℕ) : ℂ) := by
            rw [hYsum, hZsum]
            simp
      have hnuPos : 0 < nu := by
        by_contra hnu
        have hnuZero : nu = 0 := Nat.eq_zero_of_not_pos hnu
        have hdegreeZero : Section1.degree chi = 0 := by
          simpa [hnuZero] using hdegreeEq
        obtain ⟨dchi, hdchi, hdegreeChi, _hdvd⟩ :=
          huppert_XI_6_positive_degree_nat hchiIrr'
        rw [hdegreeZero] at hdegreeChi
        have hdchiZero : dchi = 0 := by
          exact_mod_cast hdegreeChi.symm
        omega
      exact ⟨nu, hnuPos, hdegreeEq⟩
  obtain ⟨nu, hnu, hchiDegree⟩ :=
    homittedDegreeMultipleCore hchiIrr hchiB hchiMu hchiOne hchiAlpha
  obtain ⟨degreeChi, _hdegreeChiPos, hdegreeChi, hdegreeChiDiv⟩ :=
    huppert_XI_6_positive_degree_nat hchiIrr
  have hdegreeChiEq : degreeChi = nu * (Nat.card F - 1) := by
    exact_mod_cast hdegreeChi.symm.trans hchiDegree
  obtain ⟨k, hk⟩ := hdegreeChiDiv
  refine ⟨nu * k, ?_⟩
  rw [hk, hdegreeChiEq]
  ac_rfl

/-- The simple minimal-counterexample branch of XI.6.1.  The strict
complement bound is the negation of the XI.1.4(b) cutoff. -/
private theorem huppert_XI_6_1_simple_odd_character_core
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (_hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (_hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnil : Group.IsNilpotent F)
    (hsmall :
      2 * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) <
        Nat.card F - 1)
    (hodd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hcyclic : IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hswapInverts : ∀ s : G, s • a = b → s • b = a →
      ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : MulAction.stabilizer
            (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
              MulAction.stabilizer G a) : G))) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ Nat.card F = p ^ f := by
  classical
  by_contra hprimePower
  have hnotPrimePower : ¬ IsPrimePow (Nat.card F) := by
    intro hpp
    rcases (isPrimePow_nat_iff (Nat.card F)).mp hpp with
      ⟨p, f, hp, hf, hpow⟩
    exact hprimePower ⟨p, f, hp, hf, hpow.symm⟩
  have hdegreeDvd : Nat.card F - 1 ∣ Nat.card G :=
    huppert_XI_6_1_simple_odd_character_divisibility
      htwo_transitive hat_most_two_fixed_points a b hab F hFrob hFnil
      hsmall hodd hcyclic hswapInverts (Or.inl hnotPrimePower)
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change 2 * Nat.card D < Nat.card F - 1 at hsmall
  obtain ⟨hOmegaCard, _hHcard, hGcard, _hdiv⟩ :=
    huppert_XI_6_1_action_parameters
      htwo_transitive a b hab F hFrob
  rw [hOmegaCard] at hGcard
  change Nat.card G = (Nat.card F + 1) * Nat.card F * Nat.card D at hGcard
  have hn : 1 < Nat.card F :=
    (Subgroup.one_lt_card_iff_ne_bot F).2 hFrob.kernel_ne_bot
  have hd : 0 < Nat.card D := Nat.card_pos
  apply huppert_XI_6_7_divisibility_contradiction
    (Nat.card F) (Nat.card D) hn hd hsmall
  rw [hGcard] at hdegreeDvd
  exact hdegreeDvd

/-- The abelian-kernel counterexample branch of XI.6.1(c).  Once the
two-point stabilizer is odd and cyclic, the completed XI.6.5--6.7 character
argument gives the same divisibility contradiction as in XI.6.1(a). -/
private theorem huppert_XI_6_1_simple_abelian_small_contradiction
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcomm : IsMulCommutative F)
    (hsmall :
      2 * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) <
        Nat.card F - 1) : False := by
  classical
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change 2 * Nat.card D < Nat.card F - 1 at hsmall
  have hnotEven : ¬ Even (Nat.card D) := by
    intro heven
    have hbound : Nat.card F - 1 ≤ 2 * Nat.card D :=
      zassenhaus_even_twoPointStabilizer_card_bound
        htwo_transitive hat_most_two_fixed_points a b hab F hFrob heven
    omega
  have hodd : Odd (Nat.card D) := Nat.not_even_iff_odd.mp hnotEven
  have hcyclic : IsCyclic D :=
    zassenhaus_odd_twoPointStabilizer_isCyclic
      htwo_transitive hat_most_two_fixed_points hsimple
      a b hab F hFrob hodd
  have hswapInverts : ∀ s : G, s • a = b → s • b = a →
      ∀ x : D,
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : D) : MulAction.stabilizer G a) : G)) := by
    intro s hsa hsb
    exact zassenhaus_odd_twoPointStabilizer_swap_inverts
      htwo_transitive hat_most_two_fixed_points hsimple
      a b hab F hFrob hodd s hsa hsb
  let : IsMulCommutative F := hFcomm
  let : CommGroup F := IsMulCommutative.instCommGroup
  have hFnil : Group.IsNilpotent F := inferInstance
  have hdegreeDvd : Nat.card F - 1 ∣ Nat.card G :=
    huppert_XI_6_1_simple_odd_character_divisibility
      htwo_transitive hat_most_two_fixed_points a b hab F hFrob hFnil
      hsmall hodd hcyclic hswapInverts (Or.inr hFcomm)
  obtain ⟨hOmegaCard, _hHcard, hGcard, _hdiv⟩ :=
    huppert_XI_6_1_action_parameters
      htwo_transitive a b hab F hFrob
  rw [hOmegaCard] at hGcard
  change Nat.card G = (Nat.card F + 1) * Nat.card F * Nat.card D at hGcard
  have hn : 1 < Nat.card F :=
    (Subgroup.one_lt_card_iff_ne_bot F).2 hFrob.kernel_ne_bot
  have hd : 0 < Nat.card D := Nat.card_pos
  apply huppert_XI_6_7_divisibility_contradiction
    (Nat.card F) (Nat.card D) hn hd hsmall
  rw [hGcard] at hdegreeDvd
  exact hdegreeDvd

private theorem huppert_XI_6_1_simple_small_core
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnil : Group.IsNilpotent F)
    (hsmall :
      2 * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) <
        Nat.card F - 1) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ Nat.card F = p ^ f := by
  classical
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change 2 * Nat.card D < Nat.card F - 1 at hsmall
  have hnotEven : ¬ Even (Nat.card D) := by
    intro heven
    have hbound : Nat.card F - 1 ≤ 2 * Nat.card D :=
      zassenhaus_even_twoPointStabilizer_card_bound
        htwo_transitive hat_most_two_fixed_points a b hab F hFrob heven
    omega
  have hodd : Odd (Nat.card D) := Nat.not_even_iff_odd.mp hnotEven
  have hcyclic : IsCyclic D :=
    zassenhaus_odd_twoPointStabilizer_isCyclic
      htwo_transitive hat_most_two_fixed_points hsimple
      a b hab F hFrob hodd
  have hswapInverts : ∀ s : G, s • a = b → s • b = a →
      ∀ x : D,
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : D) : MulAction.stabilizer G a) : G)) := by
    intro s hsa hsb
    exact zassenhaus_odd_twoPointStabilizer_swap_inverts
      htwo_transitive hat_most_two_fixed_points hsimple
      a b hab F hFrob hodd s hsa hsb
  exact huppert_XI_6_1_simple_odd_character_core
    htwo_transitive hat_most_two_fixed_points hno_regular_normal hsimple
    a b hab F hFrob hFnil hsmall hodd hcyclic hswapInverts

/-- Huppert--Blackburn XI.6.1(a), specialized to the Frobenius kernel of a
point stabilizer in a Zassenhaus action. -/
private theorem huppert_XI_6_1_frobeniusKernel_card_primePower_aux
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnil : Group.IsNilpotent F) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ Nat.card F = p ^ f := by
  classical
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  by_cases hlarge : Nat.card F - 1 ≤ 2 * Nat.card D
  · exact huppert_XI_1_4_b_primePower_of_large_complement
      F D hFrob hFnil hlarge
  · have hsmall : 2 * Nat.card D < Nat.card F - 1 := by omega
    by_cases hsimple :
        ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤
    · exact huppert_XI_6_1_simple_small_core
        htwo_transitive hat_most_two_fixed_points hno_regular_normal hsimple
        a b hab F hFrob hFnil hsmall
    · push Not at hsimple
      obtain ⟨N, hNnormal, hNne, hNtop⟩ := hsimple
      have hNtwo : MulAction.IsMultiplyPretransitive N Omega 2 :=
        zassenhaus_nontrivial_normal_is_two_pretransitive
          htwo_transitive hno_regular_normal a b hab F hFrob
          N hNnormal hNne
      have hatN :
          ∀ g : N, g ≠ 1 →
            ∀ x y z : Omega,
              x ≠ y → x ≠ z → y ≠ z →
                ¬ (g • x = x ∧ g • y = y ∧ g • z = z) := by
        intro g hg x y z hxy hxz hyz hfix
        apply hat_most_two_fixed_points ((g : N) : G)
        · intro hgG
          apply hg
          apply Subtype.ext
          exact hgG
        · exact hxy
        · exact hxz
        · exact hyz
        · exact hfix
      have hnoN :
          ¬ ∃ R : Subgroup N, R.Normal ∧ R ≠ ⊥ ∧
            ∀ x y : Omega, ∃! r : R, (r : N) • x = y :=
        zassenhaus_normal_subgroup_no_regular_normal
          N hNnormal a hNtwo hno_regular_normal
      obtain ⟨Fother, hFother⟩ :=
        huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
          hNtwo hatN hnoN a b hab
      let H := MulAction.stabilizer G a
      let Na : Subgroup (MulAction.stabilizer G a) := N.comap (MulAction.stabilizer G a).subtype
      have hFNa : F ≤ Na := by
        simpa [Na] using
          zassenhaus_normal_stabilizer_contains_frobeniusKernel
            htwo_transitive hno_regular_normal a b hab F hFrob
            N hNnormal hNne
      let HN := MulAction.stabilizer N a
      let eNa : Na ≃* HN := normalSubgroup_pointStabilizerEquiv N a
      let DNa : Subgroup Na := D.comap Na.subtype
      let DN : Subgroup HN :=
        MulAction.stabilizer HN
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer N a)
      have hDmap : DNa.map eNa.toMonoidHom = DN := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hyD, hyx⟩
          apply MulAction.mem_stabilizer_iff.mpr
          apply Subtype.ext
          have hyfix := MulAction.mem_stabilizer_iff.mp hyD
          have hyfixOmega :
              (((y : Na) : MulAction.stabilizer G a) : G) • b = b :=
            congrArg Subtype.val hyfix
          rw [← hyx]
          have hmap : (eNa y : G) = (((y : Na) : MulAction.stabilizer G a) : G) := rfl
          simpa [hmap, Subgroup.smul_def] using hyfixOmega
        · intro hx
          let y : Na := eNa.symm x
          refine ⟨y, ?_, eNa.apply_symm_apply x⟩
          change ((y : Na) : MulAction.stabilizer G a) ∈ D
          apply MulAction.mem_stabilizer_iff.mpr
          apply Subtype.ext
          have hxfix := MulAction.mem_stabilizer_iff.mp hx
          have hxfixOmega : (((x : HN) : N) : G) • b = b :=
            congrArg Subtype.val hxfix
          have hmap : (eNa.symm x : G) = (((x : HN) : N) : G) := rfl
          simpa [y, hmap, Subgroup.smul_def] using hxfixOmega
      have hDNne : DN ≠ ⊥ := by
        simpa [HN, DN] using hFother.complement_ne_bot
      have hDNa_ne : DNa ≠ (⊥ : Subgroup Na) := by
        intro hbot
        apply hDNne
        rw [← hDmap, hbot]
        simp
      have hFrobNa :
          IsFrobeniusGroupWithKernelComplement (F.subgroupOf Na) DNa := by
        have htemp := frobenius_restrict_to_subgroup_containing_kernel
          (H := (MulAction.stabilizer G a : Type _))
          F D Na hFrob hFNa
          (by simpa [DNa] using hDNa_ne)
        simpa [DNa] using htemp
      let FN : Subgroup HN := (F.subgroupOf Na).map eNa.toMonoidHom
      have hFrobN : IsFrobeniusGroupWithKernelComplement FN DN := by
        have hmap := hFrobNa.map_mulEquiv eNa
        rw [hDmap] at hmap
        simpa [FN, H] using hmap
      have hFNnil : Group.IsNilpotent FN :=
        huppert_blackburn_XI_frobeniusKernel_nilpotent FN DN hFrobN
      have hcardN : Nat.card N < Nat.card G := by
        have hNlt : N < (⊤ : Subgroup G) :=
          lt_of_le_of_ne le_top hNtop
        simpa using natCard_lt_of_subgroup_lt hNlt
      obtain ⟨p, f, hp, hf, hFNpow⟩ :=
        huppert_XI_6_1_frobeniusKernel_card_primePower_aux
          hNtwo hatN hnoN a b hab FN hFrobN hFNnil
      have hFNcard : Nat.card FN = Nat.card F := by
        calc
          Nat.card FN = Nat.card (F.subgroupOf Na) := by
            simpa [FN, H, MulAction.mem_stabilizer_iff] using
              (Subgroup.card_map_of_injective
                (K := F.subgroupOf Na) (f := eNa.toMonoidHom) eNa.injective)
          _ = Nat.card F := natCard_subgroupOf_eq F Na hFNa
      exact ⟨p, f, hp, hf, hFNcard.symm.trans hFNpow⟩
termination_by Nat.card G
decreasing_by
  · simpa using hcardN

/-- Huppert--Blackburn XI.6.1(a), specialized to the Frobenius kernel of a
point stabilizer in a Zassenhaus action. -/
public theorem huppert_XI_6_1_frobeniusKernel_card_primePower
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnil : Group.IsNilpotent F) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ Nat.card F = p ^ f := by
  exact huppert_XI_6_1_frobeniusKernel_card_primePower_aux
    htwo_transitive hat_most_two_fixed_points hno_regular_normal
    a b hab F hFrob hFnil

/-- Feit's XI.6.1 centralizer comparison, in the form used by XI.11.16. -/
public theorem huppert_XI_6_1_centralPrime_eq_noncommutativeSylowPrime
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnil : Group.IsNilpotent F)
    (p : ℕ) (hp : Nat.Prime p)
    (P : Sylow p F) (hPnoncomm : ¬ IsMulCommutative P)
    (z : F) (hzprime : Nat.Prime (orderOf z))
    (_hcentralizer :
      Subgroup.centralizer
          ({((z : MulAction.stabilizer G a) : G)} : Set G) =
        F.map (MulAction.stabilizer G a).subtype) :
    orderOf z = p := by
  obtain ⟨q, f, hq, hf, hFcard⟩ :=
    huppert_XI_6_1_frobeniusKernel_card_primePower
      htwo_transitive hat_most_two_fixed_points hno_regular_normal
      a b hab F hFrob hFnil
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have : Nontrivial P := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hPsub
    apply hPnoncomm
    let : Subsingleton P := hPsub
    exact ⟨⟨fun x y => Subsingleton.elim (x * y) (y * x)⟩⟩
  obtain ⟨k, hk, hPcard⟩ :=
    P.isPGroup'.nontrivial_iff_card.mp (inferInstance : Nontrivial P)
  have hp_dvd_P : p ∣ Nat.card P := by
    rw [hPcard]
    exact dvd_pow_self p hk.ne'
  have hp_dvd_F : p ∣ Nat.card F :=
    hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup F))
  have hp_eq_q : p = q :=
    Nat.prime_eq_prime_of_dvd_pow hp hq (by
      rw [← hFcard]
      exact hp_dvd_F)
  have hz_dvd_F : orderOf z ∣ Nat.card F := orderOf_dvd_natCard z
  have hz_eq_q : orderOf z = q :=
    Nat.prime_eq_prime_of_dvd_pow hzprime hq (by
      rw [← hFcard]
      exact hz_dvd_F)
  exact hz_eq_q.trans hp_eq_q.symm

set_option maxHeartbeats 800000 in
/-- The well-founded minimal-counterexample wrapper for XI.6.1(c). -/
private theorem huppert_XI_6_1_abelianKernel_complement_bound_aux
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcomm : IsMulCommutative F) :
    Nat.card F - 1 ≤
      2 * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  classical
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Nat.card F - 1 ≤ 2 * Nat.card D
  by_contra hbound
  have hsmall : 2 * Nat.card D < Nat.card F - 1 := by omega
  have hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤ := by
    intro N hNnormal hNne
    by_contra hNtop
    have hNtwo : MulAction.IsMultiplyPretransitive N Omega 2 :=
      zassenhaus_nontrivial_normal_is_two_pretransitive
        htwo_transitive hno_regular_normal a b hab F hFrob
        N hNnormal hNne
    have hatN :
        ∀ g : N, g ≠ 1 →
          ∀ x y z : Omega,
            x ≠ y → x ≠ z → y ≠ z →
              ¬ (g • x = x ∧ g • y = y ∧ g • z = z) := by
      intro g hg x y z hxy hxz hyz hfix
      apply hat_most_two_fixed_points (g : G)
      · intro hgG
        apply hg
        apply Subtype.ext
        exact hgG
      · exact hxy
      · exact hxz
      · exact hyz
      · exact hfix
    have hnoN :
        ¬ ∃ R : Subgroup N, R.Normal ∧ R ≠ ⊥ ∧
          ∀ x y : Omega, ∃! r : R, (r : N) • x = y :=
      zassenhaus_normal_subgroup_no_regular_normal
        N hNnormal a hNtwo hno_regular_normal
    obtain ⟨Fother, hFother⟩ :=
      huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
        hNtwo hatN hnoN a b hab
    let H := MulAction.stabilizer G a
    let Na : Subgroup H := N.comap H.subtype
    let HN := MulAction.stabilizer N a
    let eNa : Na ≃* HN := normalSubgroup_pointStabilizerEquiv N a
    let DNa : Subgroup Na := D.comap Na.subtype
    let DN : Subgroup HN :=
      MulAction.stabilizer HN
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer N a)
    have hFNa : F ≤ Na := by
      simpa [H, Na] using
        zassenhaus_normal_stabilizer_contains_frobeniusKernel
          htwo_transitive hno_regular_normal a b hab F hFrob
          N hNnormal hNne
    have hDmap : DNa.map eNa.toMonoidHom = DN := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hyD, hyx⟩
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        have hyfix := MulAction.mem_stabilizer_iff.mp hyD
        have hyfixOmega : (((y : Na) : H) : G) • b = b :=
          congrArg Subtype.val hyfix
        rw [← hyx]
        have hmap : (eNa y : G) = (((y : Na) : H) : G) := rfl
        simpa [hmap, Subgroup.smul_def] using hyfixOmega
      · intro hx
        let y : Na := eNa.symm x
        refine ⟨y, ?_, eNa.apply_symm_apply x⟩
        change ((y : Na) : H) ∈ D
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        have hxfix := MulAction.mem_stabilizer_iff.mp hx
        have hxfixOmega : (((x : HN) : N) : G) • b = b :=
          congrArg Subtype.val hxfix
        have hmap : (eNa.symm x : G) = (((x : HN) : N) : G) := rfl
        simpa [y, hmap, Subgroup.smul_def] using hxfixOmega
    have hDNne : DN ≠ ⊥ := by
      simpa [HN, DN] using hFother.complement_ne_bot
    have hDNa_ne : DNa ≠ ⊥ := by
      intro hbot
      apply hDNne
      rw [← hDmap, hbot]
      simp
    have hFrobNa :
        IsFrobeniusGroupWithKernelComplement (F.subgroupOf Na) DNa := by
      simpa [DNa, H] using
        frobenius_restrict_to_subgroup_containing_kernel
          F D Na hFrob hFNa hDNa_ne
    let FN : Subgroup HN := (F.subgroupOf Na).map eNa.toMonoidHom
    have hFrobN : IsFrobeniusGroupWithKernelComplement FN DN := by
      have hmap := hFrobNa.map_mulEquiv eNa
      rw [hDmap] at hmap
      simpa [FN] using hmap
    have hFcardN : Nat.card FN = Nat.card F := by
      calc
        Nat.card FN = Nat.card (F.subgroupOf Na) := by
          simpa [FN, H, MulAction.mem_stabilizer_iff] using
            (Subgroup.card_map_of_injective
              (K := F.subgroupOf Na) (f := eNa.toMonoidHom) eNa.injective)
        _ = Nat.card F := natCard_subgroupOf_eq F Na hFNa
    have hDNle : Nat.card DN ≤ Nat.card D := by
      rw [← hDmap]
      calc
        Nat.card (DNa.map eNa.toMonoidHom) = Nat.card DNa := by
          rw [Subgroup.card_map_of_injective eNa.injective]
        _ ≤ Nat.card D := Nat.card_le_card_of_injective
          (fun x : DNa =>
            (⟨((x : Na) : H), x.property⟩ : D)) (by
              intro x y hxy
              apply Subtype.ext
              apply Subtype.ext
              exact congrArg (fun z : D => (z : H)) hxy)
    let : IsMulCommutative F := hFcomm
    have hFNcomm : IsMulCommutative FN := by
      simpa only [FN] using
        (inferInstance : IsMulCommutative
          ((F.subgroupOf Na).map eNa.toMonoidHom))
    have hcardN : Nat.card N < Nat.card G := by
      have hNlt : N < (⊤ : Subgroup G) :=
        lt_of_le_of_ne le_top hNtop
      simpa using natCard_lt_of_subgroup_lt hNlt
    have hboundN :=
      huppert_XI_6_1_abelianKernel_complement_bound_aux
        hNtwo hatN hnoN a b hab FN hFrobN hFNcomm
    change Nat.card FN - 1 ≤ 2 * Nat.card DN at hboundN
    rw [hFcardN] at hboundN
    omega
  exact (huppert_XI_6_1_simple_abelian_small_contradiction
    htwo_transitive hat_most_two_fixed_points hsimple
    a b hab F hFrob hFcomm hsmall).elim
termination_by Nat.card G
decreasing_by simpa using hcardN

/-- Huppert--Blackburn XI.6.1(c): when the point-stabilizer Frobenius
kernel is abelian, the two-point stabilizer has at least half the
nonidentity kernel size.  This is retained as the explicit source conclusion
consumed by XI.6.8. -/
public theorem huppert_XI_6_1_abelianKernel_complement_bound
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcomm : IsMulCommutative F) :
    Nat.card F - 1 ≤
      2 * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  exact huppert_XI_6_1_abelianKernel_complement_bound_aux
    htwo_transitive hat_most_two_fixed_points hno_regular_normal
    a b hab F hFrob hFcomm

/-!
  A small, reusable interface to the XI.6.5 character package in the
  abelian-kernel case.  The proof below is the initial (abelian) branch of
  the XI.6.1 argument above, exposed so that later source leaves do not need
  to depend on private implementation details.
-/
public theorem huppert_XI_6_5_abelian_frobenius_nonker_family
    {X : Type u} [Group X] [Finite X]
    (N : Subgroup X) (F D : Subgroup N)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFcomm : IsMulCommutative F)
    (hTI : Suzuki.VI.IsTISubsetRelative N
      (F.map N.subtype : Set X)) :
    ∃ Y : Finset (Section1.ClassFunction N),
      (∀ chi : Y,
        Section1.IsIrreducibleCharacterOnGroup
          (chi : Section1.ClassFunction N)) ∧
      (∀ chi : Y,
        ¬ Section1.subgroupInKernel'
          (chi : Section1.ClassFunction N) F) ∧
      (∀ chi : Section1.ClassFunction N,
        Section1.IsIrreducibleCharacterOnGroup chi →
        ¬ Section1.subgroupInKernel' chi F →
        chi ∈ Y) ∧
      Section5.isCFLinearIsometryOnSpanOn Y Section5.puncturedSet
        (Section1.inducedCFLinear N) ∧
      (∀ phi : Section1.ClassFunction N,
        Section5.integerSpanOn Y Section5.puncturedSet phi →
          Theory.Character.IsVirtualCharacter
              (Section1.inducedCFLinear N phi) ∧
            Section1.supportedOn (Section1.inducedCFLinear N phi)
              Section5.puncturedSet) ∧
      Section6.inducedKernelFamily F ⊥ Y ∧
      (∀ chi : Y,
        Section1.degree (chi : Section1.ClassFunction N) =
          (Nat.card D : ℂ)) ∧
      Y.card * Nat.card D = Nat.card F - 1 := by
  classical
  let : F.Normal := hFrob.normal
  obtain ⟨Y, hYirr, hYnonker, hYcomplete, hYisometry, hYvirtual⟩ :=
    huppert_XI_6_5_complete_nonker_induction_isometry
      N F D hFrob hTI
  have hYbot : Section6.inducedKernelFamily F ⊥ Y :=
    huppert_XI_6_5_complete_nonker_is_inducedKernelFamily
      F D hFrob Y hYirr hYnonker hYcomplete
  let Y0 := Section6.inducedKernelFamilyOf F ⁅F, F⁆ Y
  obtain ⟨degreeNat, hY0sub, hdegree, hY0degree, _hdivDegree⟩ :=
    huppert_XI_6_5_derived_base_degree_data F Y hYbot
  have hY0eq : Y0 = Y := by
    let : IsMulCommutative F := hFcomm
    let : CommGroup F := IsMulCommutative.instCommGroup
    have hcommRoot : _root_.commutator F = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact CommGroup.center_eq_top
    have hcommAmbient : ⁅F, F⁆ = ⊥ := by
      rw [← Subgroup.map_subtype_commutator, hcommRoot]
      simp
    simpa [Y0, hcommAmbient] using
      (Section6.inducedKernelFamilyOf_eq_of_family hYbot hYbot)
  have hFindex : F.relIndex (⊤ : Subgroup N) = Nat.card D := by
    simpa [Subgroup.relIndex_top_right] using
      hFrob.isComplement'.symm.index_eq_card
  have hYdegreeD : ∀ chi : Y,
      Section1.degree (chi : Section1.ClassFunction N) =
        (Nat.card D : ℂ) := by
    intro chi
    rw [hdegree chi]
    have hnat : degreeNat chi = Nat.card D := by
      rw [← hFindex]
      exact hY0degree ⟨chi, by
        change (chi : Section1.ClassFunction N) ∈ Y0
        rw [hY0eq]
        exact chi.property⟩
    rw [hnat]
  have hYcharacter : ∀ theta : Section1.ClassFunction N,
      theta ∈ Y ↔
        Section1.IsIrreducibleCharacterOnGroup theta ∧
          ¬ Section1.subgroupInKernel' theta F := by
    intro theta
    constructor
    · intro htheta
      exact ⟨hYirr ⟨theta, htheta⟩, hYnonker ⟨theta, htheta⟩⟩
    · rintro ⟨hthetaIrr, hthetaNonker⟩
      exact hYcomplete theta hthetaIrr hthetaNonker
  have hsumEq :=
    Section6.theorem_6_6_Xset_sum_degree_sq_add_quotient_card
      hYcharacter (fun eta : Y => degreeNat eta) hdegree
  let eQ : N ⧸ F ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
  have hquotientCard : Nat.card (N ⧸ F) = Nat.card D :=
    Nat.card_congr eQ.toEquiv
  have hNcard : Nat.card N = Nat.card F * Nat.card D :=
    hFrob.isComplement'.card_mul_card.symm
  rw [hquotientCard, hNcard] at hsumEq
  have hsumCard :
      (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) =
        Y.card * Nat.card D ^ (2 : ℕ) := by
    calc
      (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) =
          ∑ _eta : Y, Nat.card D ^ (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro eta _heta
            have hnat : degreeNat eta = Nat.card D := by
              rw [← hFindex]
              exact hY0degree ⟨eta, by
                change (eta : Section1.ClassFunction N) ∈ Y0
                rw [hY0eq]
                exact eta.property⟩
            rw [hnat]
      _ = Y.card * Nat.card D ^ (2 : ℕ) := by simp
  have hfactorEq :
      (Y.card * Nat.card D + 1) * Nat.card D =
        Nat.card F * Nat.card D := by
    calc
      (Y.card * Nat.card D + 1) * Nat.card D =
          Y.card * Nat.card D ^ (2 : ℕ) + Nat.card D := by ring
      _ = (∑ eta : Y, degreeNat eta ^ (2 : ℕ)) + Nat.card D := by
        rw [hsumCard]
      _ = Nat.card F * Nat.card D := hsumEq
  have hcardFactor : Y.card * Nat.card D + 1 = Nat.card F :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hfactorEq
  have hYcardEq : Y.card * Nat.card D = Nat.card F - 1 := by
    omega
  exact ⟨Y, hYirr, hYnonker, hYcomplete, hYisometry, hYvirtual,
    hYbot, hYdegreeD, hYcardEq⟩
section RegularRestriction

open Section1

/-- If a character restricts to the regular character of an abelian subgroup,
then its irreducible decomposition is multiplicity-free and distinct ambient
constituents have orthogonal restrictions.  This is the character-theoretic
form of the first Burnside equation used in `[II1; 2.6]`. -/
public theorem huppert_XI_regular_restriction_multiplicity_free
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G)
    (hKcomm : IsMulCommutative K)
    (pi : ClassFunction G)
    (hpiChar : IsCharacter pi)
    (hpiK : subgroupRestriction K pi = Section6.regularCharacter K) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ psi : ι → ClassFunction G,
        (∀ i, IsIrreducibleCharacterOnGroup (psi i)) ∧
        Pairwise (fun i j => psi i ≠ psi j) ∧
        pi = weightedFamilySum (fun _ : ι => (1 : ℂ)) psi ∧
        (∀ i j, i ≠ j →
          scalarProduct K (subgroupRestriction K (psi i))
            (subgroupRestriction K (psi j)) = 0) ∧
        ∀ theta : ClassFunction K,
          IsIrreducibleCharacterOnGroup theta →
          ∃ i, ∀ j,
            scalarProduct K theta (subgroupRestriction K (psi j)) =
              if j = i then 1 else 0 := by
  classical
  let : IsMulCommutative K := hKcomm
  let : CommGroup K := IsMulCommutative.instCommGroup
  have hpiNe : pi ≠ 0 := by
    intro hzero
    have hzeroK : subgroupRestriction K pi = 0 := by rw [hzero]; rfl
    rw [hpiK] at hzeroK
    have hone := congrFun hzeroK (1 : K)
    have hcardPos : 0 < Nat.card K := Nat.card_pos
    simp [Section6.regularCharacter] at hone
    omega
  obtain ⟨ι, hι, hdec, e, psi, _i0, hepos, hpsiBook, hpair, hdecomp⟩ :=
    exists_positive_irreducible_decomposition_of_character pi hpiChar hpiNe
  let : Fintype ι := hι
  let : DecidableEq ι := hdec
  have hpsiIrr : ∀ i, IsIrreducibleCharacterOnGroup (psi i) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (psi i) (hpsiBook i)
  have hpsiChar : ∀ i, IsCharacter (psi i) := fun i => (hpsiBook i).1
  have hresChar : ∀ i, IsCharacter (subgroupRestriction K (psi i)) := by
    intro i
    rcases subgroupRestriction_eq_representation_character_of_isCharacter
        K (psi i) (hpsiChar i) with
      ⟨V, _hadd, _hmod, _hfd, rho, hrho⟩
    exact ⟨V, inferInstance, inferInstance, inferInstance, rho, hrho⟩
  have hresDecomp : subgroupRestriction K pi =
      weightedFamilySum (fun i => (e i : ℂ))
        (fun i => subgroupRestriction K (psi i)) := by
    rw [hdecomp]
    ext k
    simp [subgroupRestriction, weightedFamilySum]
  have hbudget : ∀ (theta : ClassFunction K),
      IsIrreducibleCharacterOnGroup theta →
      ∃ c : ι → ℕ,
        (∀ i, scalarProduct K theta (subgroupRestriction K (psi i)) = (c i : ℂ)) ∧
        ∑ i, e i * c i = 1 := by
    intro theta htheta
    have hthetaChar : IsCharacter theta :=
      isCharacter_of_isIrreducibleCharacterOnGroup htheta
    have hthetaDegree : degree theta = 1 :=
      isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative htheta
    have hthetaOne : theta 1 = 1 := by simpa [degree_apply] using hthetaDegree
    have hcExists : ∀ i, ∃ c : ℕ,
        scalarProduct K theta (subgroupRestriction K (psi i)) = (c : ℂ) := by
      intro i
      exact scalarProduct_character_character_eq_nat theta
        (subgroupRestriction K (psi i)) hthetaChar (hresChar i)
    choose c hc using hcExists
    refine ⟨c, hc, ?_⟩
    have hsp : scalarProduct K theta (Section6.regularCharacter K) = 1 := by
      let : Fintype K := Fintype.ofFinite K
      unfold scalarProduct Section6.regularCharacter
      rw [Finset.sum_eq_single (1 : K)]
      · simp only [if_true]
        rw [hthetaOne]
        have hstar : star ((Nat.card K : ℂ)) = (Nat.card K : ℂ) := by
          simp
        rw [hstar]
        have hcard : (Fintype.card K : ℂ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
        field_simp [hcard, Nat.card_eq_fintype_card]
      · intro k _hk hkne
        simp [hkne]
      · intro hone
        simp at hone
    have hsumComplex :
        (∑ i, (e i : ℂ) * (c i : ℂ)) = 1 := by
      calc
        (∑ i, (e i : ℂ) * (c i : ℂ)) =
            scalarProduct K theta
              (weightedFamilySum (fun i => (e i : ℂ))
                (fun i => subgroupRestriction K (psi i))) := by
          rw [scalarProduct_weightedFamilySum_right]
          have hterm :
              (fun i => star (e i : ℂ) *
                scalarProduct K theta (subgroupRestriction K (psi i))) =
                fun i => (e i : ℂ) * (c i : ℂ) := by
            funext i
            rw [hc i]
            simp
          rw [hterm]
          apply Finset.sum_congr
          · ext i
            simp
          · intro i _hi
            rfl
        _ = scalarProduct K theta (subgroupRestriction K pi) := by
          rw [hresDecomp]
        _ = scalarProduct K theta (Section6.regularCharacter K) := by
          rw [hpiK]
        _ = 1 := hsp
    exact_mod_cast hsumComplex
  have heOne : ∀ i, e i = 1 := by
    intro i
    have hresNe : subgroupRestriction K (psi i) ≠ 0 := by
      intro hzero
      have hone := congrFun hzero (1 : K)
      have hdegNe : degree (psi i) ≠ 0 :=
        degree_ne_zero_of_isBookIrreducibleCharacter (psi i) (hpsiBook i)
      apply hdegNe
      simpa [subgroupRestriction, degree_apply] using hone
    obtain ⟨κ, hκ, hκdec, a, theta, k0, hapos, hthetaBook,
        _hthetaPair, hresEq⟩ :=
      exists_positive_irreducible_decomposition_of_character
        (subgroupRestriction K (psi i)) (hresChar i) hresNe
    let : Fintype κ := hκ
    let : DecidableEq κ := hκdec
    have hthetaOrth : ∀ r s : κ,
        scalarProduct K (theta r) (theta s) = if r = s then 1 else 0 :=
      scalarProduct_isBookIrreducible_family theta hthetaBook _hthetaPair
    have hcoeff : scalarProduct K (theta k0)
        (subgroupRestriction K (psi i)) = (a k0 : ℂ) := by
      rw [hresEq]
      rw [← scalarProduct_star_swap]
      rw [scalarProduct_weightedFamilySum_left_orthonormal
        (fun r => (a r : ℂ)) theta hthetaOrth k0]
      simp
    have hthetaIrr : IsIrreducibleCharacterOnGroup (theta k0) :=
      isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (theta k0) (hthetaBook k0)
    obtain ⟨c, hc, hsum⟩ := hbudget (theta k0) hthetaIrr
    have hci : c i = a k0 := by
      exact_mod_cast (hc i).symm.trans hcoeff
    have htermLe : e i * c i ≤ ∑ j, e j * c j := by
      exact Finset.single_le_sum (fun j _hj => Nat.zero_le (e j * c j))
        (Finset.mem_univ i)
    rw [hsum, hci] at htermLe
    have heiPos : 0 < e i := hepos i
    have haPos : 0 < a k0 := hapos k0
    have hprodPos : 0 < e i * a k0 := Nat.mul_pos heiPos haPos
    have hprodEq : e i * a k0 = 1 := by omega
    exact Nat.dvd_one.mp ⟨a k0, hprodEq.symm⟩
  have hresPartition : ∀ theta : ClassFunction K,
      IsIrreducibleCharacterOnGroup theta →
      ∃ i, ∀ j,
        scalarProduct K theta (subgroupRestriction K (psi j)) =
          if j = i then 1 else 0 := by
    intro theta htheta
    obtain ⟨c, hc, hsum⟩ := hbudget theta htheta
    have hsum' : ∑ j, c j = 1 := by
      simpa [heOne] using hsum
    have hex : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      have hzero : ∑ j, c j = 0 := by simp [h]
      omega
    obtain ⟨i, hciNe⟩ := hex
    have hci : c i = 1 := by
      have hle : c i ≤ ∑ j, c j := by
        exact Finset.single_le_sum (fun j _hj => Nat.zero_le (c j))
          (Finset.mem_univ i)
      rw [hsum'] at hle
      omega
    refine ⟨i, ?_⟩
    intro j
    rw [hc j]
    by_cases hji : j = i
    · subst j
      simp [hci]
    · have hrest : ∑ k ∈ (Finset.univ.erase i), c k = 0 := by
        have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset ι))
          (f := c) (Finset.mem_univ i)
        change (∑ k ∈ (Finset.univ.erase i), c k) + c i = ∑ k, c k at hsplit
        rw [hsum', hci] at hsplit
        omega
      have hjmem : j ∈ (Finset.univ : Finset ι).erase i := by
        simp [hji]
      have hle : c j ≤ ∑ k ∈ (Finset.univ.erase i), c k := by
        exact Finset.single_le_sum (fun k _hk => Nat.zero_le (c k)) hjmem
      rw [hrest] at hle
      have hcj : c j = 0 := by omega
      simp [hji, hcj]
  have hresOrth : ∀ i j, i ≠ j →
      scalarProduct K (subgroupRestriction K (psi i))
        (subgroupRestriction K (psi j)) = 0 := by
    intro i j hij
    have hresNe : subgroupRestriction K (psi i) ≠ 0 := by
      intro hzero
      have hone := congrFun hzero (1 : K)
      have hdegNe : degree (psi i) ≠ 0 :=
        degree_ne_zero_of_isBookIrreducibleCharacter (psi i) (hpsiBook i)
      apply hdegNe
      simpa [subgroupRestriction, degree_apply] using hone
    obtain ⟨κ, hκ, hκdec, a, theta, _k0, hapos, hthetaBook,
        hthetaPair, hresEq⟩ :=
      exists_positive_irreducible_decomposition_of_character
        (subgroupRestriction K (psi i)) (hresChar i) hresNe
    let : Fintype κ := hκ
    let : DecidableEq κ := hκdec
    have hthetaOrth : ∀ r s : κ,
        scalarProduct K (theta r) (theta s) = if r = s then 1 else 0 :=
      scalarProduct_isBookIrreducible_family theta hthetaBook hthetaPair
    have hcoeffSelf : ∀ r : κ,
        scalarProduct K (theta r) (subgroupRestriction K (psi i)) =
          (a r : ℂ) := by
      intro r
      rw [hresEq]
      rw [← scalarProduct_star_swap]
      rw [scalarProduct_weightedFamilySum_left_orthonormal
        (fun s => (a s : ℂ)) theta hthetaOrth r]
      simp
    have hcoeffOther : ∀ r : κ,
        scalarProduct K (theta r) (subgroupRestriction K (psi j)) = 0 := by
      intro r
      have hthetaIrr : IsIrreducibleCharacterOnGroup (theta r) :=
        isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (theta r) (hthetaBook r)
      obtain ⟨c, hc, hsum⟩ := hbudget (theta r) hthetaIrr
      have hci : c i = a r := by
        exact_mod_cast (hc i).symm.trans (hcoeffSelf r)
      have haPos : 0 < a r := hapos r
      have hciOne : e i * c i = 1 := by
        rw [heOne i, hci]
        have haLe : a r ≤ 1 := by
          have htermLe : e i * c i ≤ ∑ l, e l * c l := by
            exact Finset.single_le_sum
              (fun l _hl => Nat.zero_le (e l * c l)) (Finset.mem_univ i)
          rw [hsum, heOne i, hci] at htermLe
          simpa using htermLe
        have haOne : a r = 1 := by omega
        simp [haOne]
      have hrest : ∑ l ∈ (Finset.univ.erase i), e l * c l = 0 := by
        have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset ι))
          (f := fun l => e l * c l) (Finset.mem_univ i)
        change (∑ l ∈ (Finset.univ.erase i), e l * c l) +
          e i * c i = ∑ l, e l * c l at hsplit
        rw [hsum, hciOne] at hsplit
        omega
      have hjmem : j ∈ (Finset.univ : Finset ι).erase i := by
        simp [Ne.symm hij]
      have htermjLe : e j * c j ≤
          ∑ l ∈ (Finset.univ.erase i), e l * c l := by
        exact Finset.single_le_sum
          (fun l _hl => Nat.zero_le (e l * c l)) hjmem
      rw [hrest] at htermjLe
      have hcj : c j = 0 := by
        have hejPos : 0 < e j := hepos j
        have hprodZero : e j * c j = 0 := by omega
        rcases mul_eq_zero.mp hprodZero with hejZero | hcjZero
        · omega
        · exact hcjZero
      rw [hc j, hcj]
      simp
    rw [hresEq, scalarProduct_weightedFamilySum_left]
    apply Finset.sum_eq_zero
    intro r _hr
    rw [hcoeffOther r]
    simp
  refine ⟨ι, hι, hdec, psi, hpsiIrr, hpair, ?_, hresOrth, hresPartition⟩
  calc
    pi = weightedFamilySum (fun i => (e i : ℂ)) psi := hdecomp
    _ = weightedFamilySum (fun _ : ι => (1 : ℂ)) psi := by
      ext g
      simp [weightedFamilySum, heOne]

end RegularRestriction
end External
end CFSG.BenderSuzuki
