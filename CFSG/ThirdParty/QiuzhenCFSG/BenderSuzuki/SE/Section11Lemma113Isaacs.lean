module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Callbacks
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.3: internal Isaacs 3.8--3.9 endpoint

This module proves the earlier-book character-theoretic callback used by the
Burnside endpoint.  The involution case needs only the projector onto the
`+1`-eigenspace: its trace is an integer, so class-sum integrality and
coprimality force the character value to vanish unless the involution acts as a
scalar.  Second orthogonality then supplies a nonprincipal scalar constituent.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII
open Representation
open Theory.Representation
open Theory.Character
open scoped BigOperators

private lemma involution_trace_data
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (s : G) (hs : s ^ 2 = 1) :
    ∃ r : ℕ,
      r ≤ Module.finrank ℂ V ∧
      rho.character s = (2 : ℤ) * r - Module.finrank ℂ V ∧
      (r = 0 → rho s = (-1 : ℂ) • (1 : Module.End ℂ V)) ∧
      (r = Module.finrank ℂ V → rho s = 1) := by
  let T : Module.End ℂ V := rho s
  have hT : T * T = 1 := by
    change rho s * rho s = 1
    rw [← map_mul, ← pow_two, hs, map_one]
  let P : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 + T)
  have hP : IsIdempotentElem P := by
    rw [isIdempotentElem_iff]
    ext v
    change ((2 : ℂ)⁻¹ • (1 + T)) (((2 : ℂ)⁻¹ • (1 + T)) v) =
      ((2 : ℂ)⁻¹ • (1 + T)) v
    simp only [LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply]
    have hTv := LinearMap.congr_fun hT v
    change T (T v) = v at hTv
    rw [map_smul, map_add, hTv]
    module
  have htrace := (LinearMap.IsIdempotentElem.isProj_range P hP).trace
  let r := Module.finrank ℂ (LinearMap.range P)
  have hqle : r ≤ Module.finrank ℂ V := LinearMap.finrank_range_le P
  have htraceP : LinearMap.trace ℂ V P = (r : ℂ) := by
    simpa [r] using htrace
  have htraceFormula :
      LinearMap.trace ℂ V P = (2 : ℂ)⁻¹ *
        ((Module.finrank ℂ V : ℂ) + LinearMap.trace ℂ V T) := by
    simp [P, LinearMap.trace_one]
    ring
  have hchar : rho.character s = LinearMap.trace ℂ V T := by rfl
  rw [htraceFormula, ← hchar] at htraceP
  push_cast
  have htraceEq : rho.character s =
      (2 : ℤ) * r - Module.finrank ℂ V := by
    push_cast
    linear_combination 2 * htraceP
  refine ⟨r, hqle, htraceEq, ?_, ?_⟩
  · intro hr
    have hrange : LinearMap.range P = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa [r] using hr
    have hPzero : P = 0 := LinearMap.range_eq_bot.mp hrange
    ext v
    have hv := LinearMap.congr_fun hPzero v
    change ((2 : ℂ)⁻¹ • (1 + rho s)) v = 0 at hv
    simp only [LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply] at hv
    have hv' := congrArg (fun x : V => (2 : ℂ) • x) hv
    simp only [smul_smul] at hv'
    norm_num at hv'
    change rho s v = ((-1 : ℂ) • (1 : Module.End ℂ V)) v
    simp only [LinearMap.smul_apply, Module.End.one_apply]
    simpa using (eq_neg_of_add_eq_zero_right hv')
  · intro hr
    have hrange : LinearMap.range P = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa [r] using hr
    have hPone : P = 1 := by
      ext v
      exact (LinearMap.IsIdempotentElem.isProj_range P hP).map_id v
        (by rw [hrange]; exact Submodule.mem_top)
    ext v
    have hv := LinearMap.congr_fun hPone v
    change ((2 : ℂ)⁻¹ • (1 + rho s)) v = v at hv
    simp only [LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply] at hv
    have hv' := congrArg (fun x : V => (2 : ℂ) • x) hv
    simp only [smul_smul] at hv'
    norm_num at hv'
    change rho s v = v
    rw [two_smul ℂ v] at hv'
    exact add_left_cancel hv'

private lemma involution_trace_int
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (s : G) (hs : s ^ 2 = 1) :
    ∃ r : ℕ, rho.character s =
      (2 : ℤ) * r - Module.finrank ℂ V := by
  obtain ⟨r, _hrle, htrace, _hrzero, _hrtop⟩ :=
    involution_trace_data rho s hs
  exact ⟨r, htrace⟩

private lemma involution_character_zero_or_scalar
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (hirr : rho.IsIrreducible)
    {s : G} (hs : s ^ 2 = 1) {m : ℕ}
    (hclassCard : Nat.card (ConjClasses.mk s).carrier = m)
    (hcoprime : Nat.Coprime (Module.finrank ℂ V) m) :
    rho.character s = 0 ∨
      ∃ a : ℂ, rho s = a • (1 : Module.End ℂ V) := by
  letI : rho.IsIrreducible := hirr
  letI : Nontrivial V := Theory.Character.irreducible_nontrivial rho
  let d := Module.finrank ℂ V
  have hdpos : 0 < d := by
    exact (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  obtain ⟨q, hqle, htrace, hqzero, hqtop⟩ :=
    involution_trace_data rho s hs
  let k : ℤ := (2 : ℤ) * q - d
  have hvalue : rho.character s = (k : ℂ) := by
    simpa [k, d] using htrace
  have hclassIntegral :=
    Theory.Character.classSumScalar_isIntegral rho (ConjClasses.mk s)
  rw [Theory.Character.classSumScalar_eq_card_mul_character_div rho
      (ConjClasses.mk s) ConjClasses.mem_carrier_mk,
    hclassCard, hvalue,
    show rho.character 1 = (d : ℂ) by simp [d, Representation.character]] at hclassIntegral
  have hquotientIntegral :
      IsIntegral ℤ (((((m : ℤ) * k : ℤ)) : ℂ) / ((d : ℤ) : ℂ)) := by
    simpa using hclassIntegral
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hddvdInt : (d : ℤ) ∣ (m : ℤ) * k :=
    Theory.Character.integer_division_of_integral_quotient hdne
      hquotientIntegral
  have hddvdAbs : d ∣ k.natAbs := by
    have habs : d ∣ m * k.natAbs := by
      have h' : ((d : ℤ).natAbs) ∣ (((m : ℤ) * k).natAbs) :=
        Int.natAbs_dvd_natAbs.mpr hddvdInt
      simpa [Int.natAbs_mul] using h'
    exact hcoprime.dvd_of_dvd_mul_left habs
  have hkLower : -(d : ℤ) ≤ k := by
    dsimp [k, d]
    omega
  have hkUpper : k ≤ (d : ℤ) := by
    dsimp [k, d]
    omega
  have habsLe : k.natAbs ≤ d := by
    rcases Int.natAbs_eq k with hk | hk
    · have : (k.natAbs : ℤ) ≤ d := by omega
      exact_mod_cast this
    · have : (k.natAbs : ℤ) ≤ d := by omega
      exact_mod_cast this
  have habsCases : k.natAbs = 0 ∨ k.natAbs = d := by
    by_cases habs0 : k.natAbs = 0
    · exact Or.inl habs0
    · exact Or.inr (le_antisymm habsLe
        (Nat.le_of_dvd (Nat.pos_of_ne_zero habs0) hddvdAbs))
  rcases habsCases with habs | habs
  · left
    have hkzero : k = 0 := Int.natAbs_eq_zero.mp habs
    rw [hvalue, hkzero]
    norm_num
  · right
    rcases Int.natAbs_eq_iff.mp habs with hk | hk
    · have hqd : q = Module.finrank ℂ V := by
        dsimp [k, d] at hk
        omega
      exact ⟨1, by simpa using hqtop hqd⟩
    · have hq0 : q = 0 := by
        dsimp [k, d] at hk
        omega
      exact ⟨-1, hqzero hq0⟩

private lemma finrank_eq_one_of_irreducible_ker_eq_top
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (hirr : rho.IsIrreducible)
    (hker : rho.ker = ⊤) : Module.finrank ℂ V = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : rho.IsIrreducible := hirr
  have hrho : rho = 1 := MonoidHom.ker_eq_top_iff.mp hker
  let d := Module.finrank ℂ V
  have hcf (x : G) :
      (Theory.Character.characterClassFunction rho) (ConjClasses.mk x) = (d : ℂ) := by
    change rho.character x = (d : ℂ)
    rw [hrho]
    simp [Representation.character, d]
  have hnorm :=
    (Theory.Character.irreducible_iff_character_norm_one rho).1 hirr
  rw [Theory.Character.classFunctionInner] at hnorm
  simp_rw [hcf] at hnorm
  have hcardpos : 0 < Nat.card G := Nat.card_pos (α := G)
  have hcardne : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast hcardpos.ne'
  field_simp [hcardne] at hnorm
  norm_num [Complex.normSq_eq_conj_mul_self] at hnorm
  have hnormNat : d * d = 1 := by exact_mod_cast hnorm
  have hdpos : 0 < d := by
    letI : Nontrivial V := Theory.Character.irreducible_nontrivial rho
    exact (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  nlinarith

private lemma exists_nontrivial_scalar_rep_of_prime_power_class
    {G : Type*} [Group G] [Finite G]
    {s : G} (hsne : s ≠ 1) (hsq : s ^ 2 = 1)
    {r n : ℕ} (hr : r.Prime)
    (hcard : Nat.card (ConjClasses.mk s).carrier = r ^ n) :
    ∃ d : ℕ, ∃ rho : Representation ℂ G (Fin d → ℂ),
      rho.IsIrreducible ∧ rho.ker ≠ ⊤ ∧
        (∃ a : ℂ, rho s = a • (1 : Module.End ℂ (Fin d → ℂ))) := by
  classical
  rcases Theory.Character.second_orthogonality (G := G) with
    ⟨ι, hι, chi, hchi, horth⟩
  letI : Fintype ι := hι
  choose d rho hchiRho using fun i => (hchi.1 i).1
  have hirr : ∀ i : ι, (rho i).IsIrreducible := by
    intro i
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := rho i)).2
    simpa [hchiRho i] using (hchi.1 i).2
  have hvalCF : ∀ i : ι,
      chi i (ConjClasses.mk s) = (rho i).character s := by
    intro i
    rw [hchiRho i]
    rfl
  have hdegCF : ∀ i : ι,
      chi i (ConjClasses.mk (1 : G)) =
        (Module.finrank ℂ (Fin (d i) → ℂ) : ℂ) := by
    intro i
    rw [hchiRho i]
    change (rho i).character (1 : G) = _
    simp [Representation.character]
  have hclassne : ConjClasses.mk s ≠ ConjClasses.mk (1 : G) := by
    intro h
    have hconj : IsConj s (1 : G) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp h
    exact hsne (isConj_one_left.mp hconj)
  by_contra hnone
  push_neg at hnone
  choose q htrace using fun i => involution_trace_int (rho i) s hsq
  let z : ι → ℤ := fun i => (2 : ℤ) * q i - d i
  have hvalueInt : ∀ i : ι, (rho i).character s = (z i : ℂ) := by
    intro i
    simpa [z] using htrace i
  have hdegree : ∀ i : ι,
      Module.finrank ℂ (Fin (d i) → ℂ) = d i := by
    intro i
    simp
  have hdegCF' : ∀ i : ι,
      chi i (ConjClasses.mk (1 : G)) = (d i : ℂ) := by
    intro i
    simpa [hdegree i] using hdegCF i
  have hzero := (horth s 1).2 hclassne
  have hsumComplex :
      (∑ i : ι, (((z i) * (d i : ℤ) : ℤ) : ℂ)) = 0 := by
    calc
      (∑ i : ι, (((z i) * (d i : ℤ) : ℤ) : ℂ)) =
          ∑ i : ι, chi i (ConjClasses.mk s) *
            star (chi i (ConjClasses.mk (1 : G))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hvalCF i, hvalueInt i, hdegCF' i]
        push_cast
        simp
      _ = 0 := hzero
  have hsumInt : ∑ i : ι, z i * (d i : ℤ) = 0 := by
    exact_mod_cast hsumComplex
  let triv : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
  have htrivIrr : triv.IsIrreducible :=
    Theory.Character.trivial_complex_irreducible
  have htrivChar : Theory.Character.IsIrreducibleConjCharacter
      (Theory.Character.characterClassFunction triv) :=
    Theory.Character.isIrreducibleCharacter_characterClassFunction triv htrivIrr
  obtain ⟨i0, hi0⟩ := hchi.2.1 (Theory.Character.characterClassFunction triv) htrivChar
  have hrho0cf : (Theory.Character.characterClassFunction (rho i0)) =
      (Theory.Character.characterClassFunction triv) := (hchiRho i0).symm.trans hi0
  have hdi0 : d i0 = 1 := by
    have h := congrFun hrho0cf (ConjClasses.mk (1 : G))
    change (rho i0).character (1 : G) = triv.character (1 : G) at h
    simpa [Representation.character, triv] using h
  have hzi0 : z i0 = 1 := by
    have h := congrFun hrho0cf (ConjClasses.mk s)
    change (rho i0).character s = triv.character s at h
    rw [hvalueInt i0] at h
    have : (z i0 : ℂ) = 1 := by
      simpa [Representation.character, triv, Representation.isTrivial_def] using h
    exact_mod_cast this
  have index_eq_i0 : ∀ i : ι, (rho i).ker = ⊤ → i = i0 := by
    intro i hker
    have hdim1 : Module.finrank ℂ (Fin (d i) → ℂ) = 1 :=
      finrank_eq_one_of_irreducible_ker_eq_top (rho i) (hirr i) hker
    have hdi : d i = 1 := by simpa using hdim1
    have hrho : rho i = 1 := MonoidHom.ker_eq_top_iff.mp hker
    apply hchi.2.2
    rw [hi0, hchiRho i]
    ext c
    refine Quotient.inductionOn c ?_
    intro x
    change (rho i).character x = triv.character x
    rw [hrho]
    simp [Representation.character, hdi, triv, Representation.isTrivial_def]
  have htermDvd : ∀ i : ι, i ≠ i0 →
      (r : ℤ) ∣ z i * (d i : ℤ) := by
    intro i hi
    by_cases hrd : r ∣ d i
    · exact dvd_mul_of_dvd_right
        (Int.natCast_dvd_natCast.mpr hrd) (z i)
    · have hcop : Nat.Coprime
          (Module.finrank ℂ (Fin (d i) → ℂ)) (r ^ n) := by
        simpa using (hr.coprime_iff_not_dvd.mpr hrd).symm.pow_right n
      rcases involution_character_zero_or_scalar (rho i) (hirr i)
          hsq hcard hcop with hzeroValue | hscalar
      · have hzzero : z i = 0 := by
          have : (z i : ℂ) = 0 := by
            rw [← hvalueInt i, hzeroValue]
          exact_mod_cast this
        simp [hzzero]
      · obtain ⟨a, ha⟩ := hscalar
        have hkerTop : (rho i).ker = ⊤ := by
          by_contra hker
          exact (hnone (d i) (rho i) (hirr i) hker a) ha
        exact (hi (index_eq_i0 i hkerTop)).elim
  have hrestDvd : (r : ℤ) ∣
      ∑ i ∈ (Finset.univ.erase i0), z i * (d i : ℤ) := by
    apply Finset.dvd_sum
    intro i hi
    exact htermDvd i (Finset.ne_of_mem_erase hi)
  have hsplit :
      z i0 * (d i0 : ℤ) +
        ∑ i ∈ (Finset.univ.erase i0), z i * (d i : ℤ) = 0 := by
    calc
      z i0 * (d i0 : ℤ) +
          ∑ i ∈ (Finset.univ.erase i0), z i * (d i : ℤ) =
          ∑ i : ι, z i * (d i : ℤ) :=
        Finset.add_sum_erase Finset.univ
          (fun i => z i * (d i : ℤ)) (Finset.mem_univ i0)
      _ = 0 := hsumInt
  have hrestEq :
      ∑ i ∈ (Finset.univ.erase i0), z i * (d i : ℤ) = -1 := by
    rw [hzi0, hdi0] at hsplit
    norm_num at hsplit
    simpa using (eq_neg_of_add_eq_zero_right hsplit)
  have hrDvdOne : (r : ℤ) ∣ 1 := by
    rw [hrestEq] at hrestDvd
    rcases hrestDvd with ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    linear_combination -hc
  have hrNatDvdOne : r ∣ 1 := Int.natCast_dvd_natCast.mp hrDvdOne
  exact hr.not_dvd_one hrNatDvdOne

private lemma conjClass_card_eq_set_card
    {X : Type*} [Group X] [Finite X]
    (W : Subgroup X) (Z : Set X) {z : X} (hz : z ∈ Z)
    (hZleW : Z ⊆ W)
    (hstable : ∀ x : X, x ∈ Z → ∀ w : X, w ∈ W →
      rightConjugateElem x w ∈ Z)
    (hclass : ∀ x : X, x ∈ Z → ∀ y : X, y ∈ Z →
      ∃ w : X, w ∈ W ∧ y = rightConjugateElem x w) :
    Nat.card (ConjClasses.mk (⟨z, hZleW hz⟩ : W)).carrier =
      Nat.card Z := by
  classical
  let zW : W := ⟨z, hZleW hz⟩
  let e : (ConjClasses.mk zW).carrier ≃ Z :=
    { toFun := fun y => by
        refine ⟨(y.1 : X), ?_⟩
        have hmk : ConjClasses.mk (y.1 : W) = ConjClasses.mk zW :=
          ConjClasses.mem_carrier_iff_mk_eq.mp y.2
        rcases isConj_iff.mp
            (ConjClasses.mk_eq_mk_iff_isConj.mp hmk) with ⟨w, hw⟩
        have hy : (y.1 : W) = rightConjugateElem zW w := by
          calc
            (y.1 : W) = w⁻¹ * (w * y.1 * w⁻¹) * w := by group
            _ = rightConjugateElem zW w := by
              rw [hw]
              rfl
        simpa [hy, zW, rightConjugateElem] using
          hstable z hz (w : X) w.property
      invFun := fun y => by
        refine ⟨⟨y.1, hZleW y.2⟩, ?_⟩
        apply ConjClasses.mem_carrier_iff_mk_eq.mpr
        apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        obtain ⟨w, hwW, hy⟩ := hclass z hz y.1 y.2
        let wW : W := ⟨w, hwW⟩
        refine isConj_iff.mpr ⟨wW, ?_⟩
        apply Subtype.ext
        simp [wW, zW, rightConjugateElem, hy, mul_assoc]
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }
  simpa [zW] using Nat.card_congr e

private lemma smul_one_comm
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : ℂ) (f : Module.End ℂ V) :
    (a • (1 : Module.End ℂ V)) * f =
      f * (a • (1 : Module.End ℂ V)) := by
  ext v
  simp

/-- Internal proof of the source `[Is1; 3.8,3.9]` callback. -/
public theorem is1_38_39
    {X : Type*} [Group X] [Finite X] :
    Is1Lemma38_39PrimePowerInvolutionClass (X := X) := by
  intro W Z r n hr hZne hZleW hZinv hZstable hclass hZcard
  obtain ⟨z0, hz0⟩ := hZne
  let z0W : W := ⟨z0, hZleW hz0⟩
  have hz0ne : z0W ≠ 1 := by
    intro h
    apply (hZinv z0 hz0).ne_one
    exact congrArg Subtype.val h
  have hz0sq : z0W ^ 2 = 1 := by
    apply Subtype.ext
    exact (hZinv z0 hz0).sq_eq_one
  have hclassCard : Nat.card (ConjClasses.mk z0W).carrier = r ^ n := by
    rw [conjClass_card_eq_set_card W Z hz0 hZleW hZstable hclass,
      hZcard]
  obtain ⟨d, rho, hirr, hkerne, a, ha⟩ :=
    exists_nontrivial_scalar_rep_of_prime_power_class
      hz0ne hz0sq hr hclassCard
  let K : Subgroup W := rho.ker
  let H : Subgroup X := K.map W.subtype
  have hKlt : K < ⊤ := lt_top_iff_ne_top.mpr hkerne
  have hHlt : H < W := by
    have hmaplt : K.map W.subtype <
        (⊤ : Subgroup W).map W.subtype :=
      (Subgroup.map_subtype_lt_map_subtype
        (G' := W) (H := K) (K := ⊤)).mpr hKlt
    have hmapTop : (⊤ : Subgroup W).map W.subtype = W := by
      ext x
      simp
    simpa only [H, hmapTop] using hmaplt
  have hHnormal : (H.subgroupOf W).Normal := by
    simpa [H, K, subgroupOf_map_subtype_eq] using
      MonoidHom.normal_ker rho
  refine ⟨⟨H, hHlt, hHnormal, ?_⟩⟩
  intro z hz w hw
  let zW : W := ⟨z, hZleW hz⟩
  let wW : W := ⟨w, hw⟩
  have hzscalar : rho zW = a • (1 : Module.End ℂ (Fin d → ℂ)) := by
    obtain ⟨g, hgW, hzg⟩ := hclass z0 hz0 z hz
    let gW : W := ⟨g, hgW⟩
    have hzW : zW = rightConjugateElem z0W gW := by
      apply Subtype.ext
      exact hzg
    rw [hzW, rightConjugateElem, map_mul, map_mul, ha]
    calc
      rho gW⁻¹ * (a • (1 : Module.End ℂ (Fin d → ℂ))) * rho gW =
          rho gW⁻¹ *
            ((a • (1 : Module.End ℂ (Fin d → ℂ))) * rho gW) := by
        rw [mul_assoc]
      _ = rho gW⁻¹ *
            (rho gW * (a • (1 : Module.End ℂ (Fin d → ℂ)))) := by
        rw [smul_one_comm a (rho gW)]
      _ = (rho gW⁻¹ * rho gW) *
            (a • (1 : Module.End ℂ (Fin d → ℂ))) := by
        rw [mul_assoc]
      _ = a • (1 : Module.End ℂ (Fin d → ℂ)) := by
        rw [← map_mul]
        simp
  have hcomm : rho zW * rho wW = rho wW * rho zW := by
    rw [hzscalar]
    exact smul_one_comm a (rho wW)
  have hkernel : rightConjugateElem zW wW * zW⁻¹ ∈ K := by
    change rightConjugateElem zW wW * zW⁻¹ ∈ rho.ker
    rw [MonoidHom.mem_ker]
    change rho (rightConjugateElem zW wW * zW⁻¹) = 1
    rw [rightConjugateElem, map_mul, map_mul, map_mul]
    calc
      rho wW⁻¹ * rho zW * rho wW * rho zW⁻¹ =
          rho wW⁻¹ * (rho zW * rho wW) * rho zW⁻¹ := by
        simp [mul_assoc]
      _ = rho wW⁻¹ * (rho wW * rho zW) * rho zW⁻¹ := by
        rw [hcomm]
      _ = rho wW⁻¹ * rho wW * (rho zW * rho zW⁻¹) := by
        simp [mul_assoc]
      _ = 1 := by
        rw [← map_mul, ← map_mul]
        simp
  have hmapmem :
      (W.subtype (rightConjugateElem zW wW * zW⁻¹)) ∈ H := by
    exact Subgroup.mem_map_of_mem W.subtype hkernel
  simpa [H, zW, wW, rightConjugateElem] using hmapmem

end CFSG.BenderSuzuki
