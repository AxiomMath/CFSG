module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_10
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_11
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2, Theorem (2.6)

This file proves the Dade isometry theorem in the order used by PF.  The
first local node records the part of the proof saying that a Dade transform is
constant on each set `aH(a)`.
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2

universe u

/-! ## (2.6) -/

@[expose] public def theorem_2_6_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) : Prop :=
  (∀ α β : Section1.ClassFunction L,
      CFOn L A α → CFOn L A β →
        Section1.scalarProduct G (dadeTransform H hAL α) (dadeTransform H hAL β) =
          Section1.scalarProduct L α β) ∧
    ∀ α : Section1.ClassFunction L,
      virtualCharacterOn L A α →
        virtualCharacterOfG (dadeTransform H hAL α)


private noncomputable def standardizeRepresentation
    {G V : Type u} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem standardizeRepresentation_character
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

private noncomputable def uliftRepresentation
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift V) := by
  let e : V ≃ₗ[ℂ] ULift V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem uliftRepresentation_character
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isVirtualCharacter_of_isCharacter
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G) (hχ : Section1.IsCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  classical
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), fun _ : Fin 1 => Module.finrank ℂ V,
    fun _ : Fin 1 => standardizeRepresentation ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations,
    standardizeRepresentation_character]


private theorem character_cast_nat
    {G : Type u} [Group G] {n m : ℕ} (h : n = m)
    (ρ : Representation ℂ G (Fin n → ℂ)) (g : G) :
    Representation.character
        (cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) h) ρ) g =
      ρ.character g := by
  subst m
  simp [Representation.character]

private theorem isVirtualCharacter_add
    {G : Type u} [Group G] {χ ψ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    Theory.Character.IsVirtualCharacter (χ + ψ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  let mrs : Fin (r + s) → ℤ := Fin.addCases m m'
  let nrs : Fin (r + s) → ℕ := Fin.addCases n n'
  have hn_left (i : Fin r) : n i = nrs (Fin.castAdd s i) := by
    simp [nrs, Fin.addCases_left]
  have hn_right (j : Fin s) : n' j = nrs (Fin.natAdd r j) := by
    simp [nrs, Fin.addCases_right]
  let ρrs : (i : Fin (r + s)) → Representation ℂ G (Fin (nrs i) → ℂ) :=
    Fin.addCases
      (motive := fun i => Representation ℂ G (Fin (nrs i) → ℂ))
      (fun i =>
        cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) (hn_left i))
          (ρ i))
      (fun j =>
        cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) (hn_right j))
          (σ j))
  refine ⟨r + s, mrs, nrs, ρrs, ?_⟩
  ext g
  simp only [Pi.add_apply, Theory.Character.virtualCharacterOfRepresentations,
    mrs, nrs, ρrs, Fin.sum_univ_add]
  simp [Fin.addCases_left, Fin.addCases_right, character_cast_nat]

private theorem isVirtualCharacter_zsmul
    {G : Type u} [Group G] (n : ℤ) {χ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum
    {G : Type u} [Group G] {ι : Type*} [Fintype ι]
    (s : Finset ι) (χ : ι → G → ℂ)
    (hχ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (χ i)) :
    Theory.Character.IsVirtualCharacter (fun g => ∑ i ∈ s, χ i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i : Fin 0 => nomatch i), (fun i : Fin 0 => nomatch i),
        (fun i : Fin 0 => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert i s hi hs =>
      have htail :
          Theory.Character.IsVirtualCharacter (fun g => ∑ j ∈ s, χ j g) := by
        exact hs (by
          intro j hj
          exact hχ j (by simp [hj]))
      have hheadTail :=
        isVirtualCharacter_add (hχ i (by simp)) htail
      convert hheadTail using 1
      ext g
      simp [hi]


private theorem isVirtualCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Section1.IsClassFunction χ := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  intro x g
  unfold Theory.Character.virtualCharacterOfRepresentations
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hchar :
      (ρ i).character (x * g * x⁻¹) = (ρ i).character g := by
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ i) g x
  simp [hchar]

private theorem scalarProduct_isVirtualCharacter_eq_int
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    ∃ z : ℤ, Section1.scalarProduct G χ ψ = (z : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  have hpair :
      ∀ i : Fin r, ∀ j : Fin s,
        ∃ k : ℕ, Section1.scalarProduct G ((ρ i).character) ((σ j).character) = (k : ℂ) := by
    intro i j
    refine ⟨Module.finrank ℂ (Representation.IntertwiningMap (σ j) (ρ i)), ?_⟩
    simpa using
      (Section1.scalarProduct_representation_char_eq_finrank
        (rho := σ j) (sigma := ρ i))
  choose k hk using hpair
  refine ⟨∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j, ?_⟩
  have hcalc :
      Section1.scalarProduct G
          (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
          (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) =
        ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := by
    rw [Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [Section1.scalarProduct_fintype_sum_right]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    change
      Section1.scalarProduct G
          ((m i : ℂ) • (ρ i).character)
          ((m' j : ℂ) • (σ j).character) =
        (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ)
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, hk i j]
    simp
    ring
  calc
    Section1.scalarProduct G
        (Theory.Character.virtualCharacterOfRepresentations r m n ρ)
        (Theory.Character.virtualCharacterOfRepresentations s m' n' σ)
        =
          Section1.scalarProduct G
            (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
            (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) := by
          rfl
    _ = ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := hcalc
    _ = ((∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j : ℤ) : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul, mul_assoc]


private theorem isVirtualCharacter_comp_monoidHom
    {G K : Type u} [Group G] [Group K]
    (φ : K →* G) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (fun k : K => χ (φ k)) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, m, n, fun i => (ρ i).comp φ, ?_⟩
  ext k
  simp [Theory.Character.virtualCharacterOfRepresentations, Representation.character]

private theorem CFOn_of_virtualCharacterOn
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L] (A : Set G)
    (α : Section1.ClassFunction L) :
    virtualCharacterOn L A α → CFOn L A α := by
  intro hα
  exact ⟨isVirtualCharacter_isClassFunction hα.1, hα.2⟩

private theorem dadeTransform_add
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (α β : Section1.ClassFunction L) :
    dadeTransform H hAL (α + β) =
      dadeTransform H hAL α + dadeTransform H hAL β := by
  classical
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ H a, conjugateIn g (a * h)
  · simp [dadeTransform, hg]
  · simp [dadeTransform, hg]


public theorem inducedCF_isVirtualCharacter_of_virtualCharacter
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S] {ψ : Section1.ClassFunction S}
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    Theory.Character.IsVirtualCharacter (Section1.inducedCF S ψ) := by
  classical
  rcases hψ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, m, fun i => Module.finrank ℂ (Representation.IndV S.subtype (ρ i)),
    fun i => standardizeRepresentation (Representation.ind S.subtype (ρ i)), ?_⟩
  ext g
  change Section1.inducedCF S
      (Theory.Character.virtualCharacterOfRepresentations r m n ρ) g =
    ∑ i : Fin r, (m i : ℂ) *
      (standardizeRepresentation (Representation.ind S.subtype (ρ i))).character g
  have hvirtual :
      Theory.Character.virtualCharacterOfRepresentations r m n ρ =
        Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
          (fun i : Fin r => (ρ i).character) := by
    funext g
    have huniv :
        (@Finset.univ (Fin r) (Fin.fintype r)) =
          (@Finset.univ (Fin r) (Fintype.ofFinite (Fin r))) := by
      ext i
      simp
    unfold Theory.Character.virtualCharacterOfRepresentations Section1.weightedFamilySum
    simp
    rw [huniv]
  calc
    Section1.inducedCF S (Theory.Character.virtualCharacterOfRepresentations r m n ρ) g =
        Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
          (fun i : Fin r => Section1.inducedCF S ((ρ i).character)) g := by
          have hlin :
              Section1.inducedCF S (Theory.Character.virtualCharacterOfRepresentations r m n ρ) =
                Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
                  (fun i : Fin r => Section1.inducedCF S ((ρ i).character)) := by
            rw [hvirtual]
            exact Section1.inducedCF_weightedFamilySum S
              (fun i : Fin r => (m i : ℂ)) (fun i : Fin r => (ρ i).character)
          simpa using congrFun hlin g
    _ = ∑ i : Fin r, (m i : ℂ) *
          (standardizeRepresentation (Representation.ind S.subtype (ρ i))).character g := by
          have huniv :
              (@Finset.univ (Fin r) (Fin.fintype r)) =
                (@Finset.univ (Fin r) (Fintype.ofFinite (Fin r))) := by
            ext i
            simp
          rw [Section1.weightedFamilySum]
          rw [huniv]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [standardizeRepresentation_character,
            Section1.inducedCF_eq_representation_character]

public theorem MOfSet_isInternalSemidirectProduct
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A) :
    IsInternalSemidirectProduct
      (MOfSet H L B) (HInter H B) (normalizerIn L B) := by
  have h24 := (proposition_2_4 A L H).1 h
  have hrightNorm :
      ∀ x ∈ normalizerIn L B, ∀ y ∈ HInter H B, conjBy x y ∈ HInter H B := by
    intro x hx y hy
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
    have hxnorm : normalizesSet B x := (Subgroup.mem_inf.mp hx).2
    have hxnormInv : normalizesSet B x⁻¹ := normalizesSet_inv hxnorm
    change conjBy x y ∈ ⨅ b : B, H (b : G)
    rw [Subgroup.mem_iInf]
    intro b
    have hb' : conjBy x⁻¹ (b : G) ∈ B := (hxnormInv b).2 b.2
    have hyb : y ∈ H (conjBy x⁻¹ (b : G)) := by
      change y ∈ ⨅ b : B, H (b : G) at hy
      rw [Subgroup.mem_iInf] at hy
      exact hy ⟨conjBy x⁻¹ (b : G), hb'⟩
    have hEq : H (conjBy x⁻¹ (b : G)) = conjugateSubgroup x⁻¹ (H (b : G)) := by
      simpa [conjBy, mul_assoc] using
        h24 (a := (b : G)) (x := x⁻¹) (hBA b.2) (L.inv_mem hxL)
    have hyconj : y ∈ conjugateSubgroup x⁻¹ (H (b : G)) := by
      simpa [hEq] using hyb
    rcases hyconj with ⟨u, hu, hyu⟩
    have hcalc : conjBy x y = u := by
      rw [hyu]
      simp [conjBy, mul_assoc]
    simpa [hcalc] using hu
  refine
    { left_le := le_sup_left
      right_le := le_sup_right
      right_normalizes_left := hrightNorm
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rcases (Subgroup.mem_inf.mp hz) with ⟨hzH, hzN⟩
    rcases hB with ⟨b, hb⟩
    have hzHb : z ∈ H b := by
      change z ∈ ⨅ b : B, H (b : G) at hzH
      rw [Subgroup.mem_iInf] at hzH
      exact hzH ⟨b, hb⟩
    have hzCent : z ∈ elementCentralizer b :=
      (h.centralizer_eq_product (hBA hb)).left_le hzHb
    have hzCL : z ∈ centralizerIn L b := by
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hzN).1, hzCent⟩
    have hInf : z ∈ H b ⊓ centralizerIn L b :=
      Subgroup.mem_inf.mpr ⟨hzHb, hzCL⟩
    have hzBot : z ∈ (⊥ : Subgroup G) := by
      simpa [(h.centralizer_eq_product (hBA hb)).inf_eq_bot] using hInf
    simpa using hzBot
  · intro c hc
    let P : Subgroup G := {
      carrier := {z | ∃ h0 ∈ HInter H B, ∃ k0 ∈ normalizerIn L B, z = h0 * k0}
      one_mem' := by
        refine ⟨1, (HInter H B).one_mem, 1, (normalizerIn L B).one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨h1, hh1, k1, hk1, rfl⟩
        rcases hb with ⟨h2, hh2, k2, hk2, rfl⟩
        refine ⟨h1 * conjBy k1 h2, ?_,
          k1 * k2, (normalizerIn L B).mul_mem hk1 hk2, ?_⟩
        · exact (HInter H B).mul_mem hh1 (hrightNorm k1 hk1 h2 hh2)
        · simp [conjBy, mul_assoc]
      inv_mem' := by
        intro a ha
        rcases ha with ⟨h1, hh1, k1, hk1, rfl⟩
        refine ⟨conjBy k1⁻¹ h1⁻¹, ?_,
          k1⁻¹, (normalizerIn L B).inv_mem hk1, ?_⟩
        · exact hrightNorm k1⁻¹ ((normalizerIn L B).inv_mem hk1)
            h1⁻¹ ((HInter H B).inv_mem hh1)
        · simp [conjBy, mul_assoc]
    }
    have hHle : HInter H B ≤ P := by
      intro h0 hh0
      exact ⟨h0, hh0, 1, (normalizerIn L B).one_mem, by simp⟩
    have hKle : normalizerIn L B ≤ P := by
      intro k0 hk0
      exact ⟨1, (HInter H B).one_mem, k0, hk0, by simp⟩
    have hle : MOfSet H L B ≤ P := by
      simpa [MOfSet] using sup_le hHle hKle
    rcases hle hc with ⟨h0, hh0, x0, hx0, hmul⟩
    exact ⟨h0, hh0, x0, hx0, hmul⟩

private theorem internalSemidirectProduct_mul_unique
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H :=
    H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by
        simp
      _ = h₂ := by
        simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private theorem internalSemidirectProduct_card_mul
    {G : Type u} [Group G] [Finite G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) :
    Nat.card C = Nat.card H * Nat.card K := by
  classical
  let f : H × K → C := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      C.mul_mem (h.left_le p.1.2) (h.right_le p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    apply Prod.ext
    · apply Subtype.ext
      exact (internalSemidirectProduct_mul_unique h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq)).1
    · apply Subtype.ext
      exact (internalSemidirectProduct_mul_unique h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq)).2
  have hf_surj : Function.Surjective f := by
    intro c
    rcases h.mul_surjective (c : G) c.2 with ⟨h₀, hh₀, k₀, hk₀, hc⟩
    refine ⟨(⟨h₀, hh₀⟩, ⟨k₀, hk₀⟩), ?_⟩
    apply Subtype.ext
    exact hc.symm
  have hcard_equiv :
      Nat.card (H × K) = Nat.card C :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hprod : Nat.card (H × K) = Nat.card H * Nat.card K := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    exact Fintype.card_prod H K
  rw [← hcard_equiv, hprod]

private theorem internalSemidirectProduct_left_normal
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) :
    (H.subgroupOf C).Normal := by
  refine ⟨?_⟩
  intro y hyH x
  rcases h.mul_surjective (x : G) x.2 with ⟨h0, hh0, k0, hk0, hx⟩
  change ((x : G) * (y : G) * (x : G)⁻¹) ∈ H
  rw [hx]
  have hky : conjBy k0 (y : G) ∈ H :=
    h.right_normalizes_left k0 hk0 (y : G) hyH
  have hcalc :
      h0 * k0 * (y : G) * (h0 * k0)⁻¹ =
        h0 * conjBy k0 (y : G) * h0⁻¹ := by
    simp [conjBy, mul_assoc]
  rw [hcalc]
  exact H.mul_mem (H.mul_mem hh0 hky) (H.inv_mem hh0)

private noncomputable def internalSemidirectLeftComponent
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) (c : C) : H := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  exact ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩

private noncomputable def internalSemidirectRightComponent
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) (c : C) : K := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact ⟨Classical.choose hk, (Classical.choose_spec hk).1⟩

private theorem internalSemidirectLeft_mul_rightComponent
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) (c : C) :
    (internalSemidirectLeftComponent h c : G) *
        (internalSemidirectRightComponent h c : G) = c := by
  classical
  dsimp [internalSemidirectLeftComponent, internalSemidirectRightComponent]
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact (Classical.choose_spec hk).2.symm

private theorem internalSemidirectRightComponent_of_mul
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K)
    {h₀ k₀ : G} (hh₀ : h₀ ∈ H) (hk₀ : k₀ ∈ K) :
    internalSemidirectRightComponent h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩ =
      ⟨k₀, hk₀⟩ := by
  apply Subtype.ext
  have hdec :=
    internalSemidirectLeft_mul_rightComponent h
      ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩
  exact
    (internalSemidirectProduct_mul_unique h
      (internalSemidirectLeftComponent h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hh₀
      (internalSemidirectRightComponent h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hk₀ hdec).2

private noncomputable def internalSemidirectRightProjection
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) : C →* K where
  toFun := internalSemidirectRightComponent h
  map_one' := by
    apply Subtype.ext
    have hdec := internalSemidirectLeft_mul_rightComponent h (1 : C)
    exact
      (internalSemidirectProduct_mul_unique h
        (internalSemidirectLeftComponent h (1 : C)).2 H.one_mem
        (internalSemidirectRightComponent h (1 : C)).2 K.one_mem
        (by simpa using hdec)).2
  map_mul' := by
    intro c d
    apply Subtype.ext
    let lc := internalSemidirectLeftComponent h c
    let rc := internalSemidirectRightComponent h c
    let ld := internalSemidirectLeftComponent h d
    let rd := internalSemidirectRightComponent h d
    have hdec_c : (lc : G) * (rc : G) = (c : G) :=
      internalSemidirectLeft_mul_rightComponent h c
    have hdec_d : (ld : G) * (rd : G) = (d : G) :=
      internalSemidirectLeft_mul_rightComponent h d
    have hleft_mem : (lc : G) * conjBy (rc : G) (ld : G) ∈ H :=
      H.mul_mem lc.2 (h.right_normalizes_left (rc : G) rc.2 (ld : G) ld.2)
    have hright_mem : (rc : G) * (rd : G) ∈ K :=
      K.mul_mem rc.2 rd.2
    have hprod :
        ((lc : G) * conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
          ((c : G) * (d : G)) := by
      calc
        ((lc : G) * conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
            ((lc : G) * (rc : G)) * ((ld : G) * (rd : G)) := by
              simp [conjBy, mul_assoc]
        _ = (c : G) * (d : G) := by
              rw [hdec_c, hdec_d]
    have hdec_cd :=
      internalSemidirectLeft_mul_rightComponent h (c * d)
    exact
      (internalSemidirectProduct_mul_unique h
        (internalSemidirectLeftComponent h (c * d)).2 hleft_mem
        (internalSemidirectRightComponent h (c * d)).2 hright_mem
        (by simpa [hprod] using hdec_cd)).2

private noncomputable def normalizerInToL
    {G : Type u} [Group G] (L : Subgroup G) (B : Set G) :
    normalizerIn L B →* L where
  toFun x := ⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩
  map_one' := by
    ext
    rfl
  map_mul' := by
    intro x y
    ext
    rfl

private noncomputable def MOfSetProjectionToL
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A) :
    MOfSet H L B →* L :=
  (normalizerInToL L B).comp
    (internalSemidirectRightProjection
      (MOfSet_isInternalSemidirectProduct A L H h hB hBA))

private theorem MOfSetProjectionToL_apply_mul
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A)
    {h₀ x : G} (hh₀ : h₀ ∈ HInter H B) (hx : x ∈ normalizerIn L B) :
    MOfSetProjectionToL A L H h hB hBA
        ⟨h₀ * x, hInter_mul_normalizer_mem_MOfSet H L B hh₀ hx⟩ =
      ⟨x, (Subgroup.mem_inf.mp hx).1⟩ := by
  apply Subtype.ext
  change
    ((normalizerInToL L B)
      (internalSemidirectRightProjection
        (MOfSet_isInternalSemidirectProduct A L H h hB hBA)
          ⟨h₀ * x, hInter_mul_normalizer_mem_MOfSet H L B hh₀ hx⟩) : G) = x
  have hright :
      internalSemidirectRightProjection
          (MOfSet_isInternalSemidirectProduct A L H h hB hBA)
          ⟨h₀ * x, hInter_mul_normalizer_mem_MOfSet H L B hh₀ hx⟩ =
        ⟨x, hx⟩ := by
    exact internalSemidirectRightComponent_of_mul
      (MOfSet_isInternalSemidirectProduct A L H h hB hBA) hh₀ hx
  simp [normalizerInToL, hright]

private theorem MOfSet_card_mul
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A) :
    Nat.card (MOfSet H L B) =
      Nat.card (HInter H B) * Nat.card (normalizerIn L B) :=
  internalSemidirectProduct_card_mul
    (MOfSet_isInternalSemidirectProduct A L H h hB hBA)

public noncomputable def alphaBFromProjection
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A)
    (α : Section1.ClassFunction L) :
    Section1.ClassFunction (MOfSet H L B) :=
  fun m => α (MOfSetProjectionToL A L H h hB hBA m)

public theorem alphaBFromProjection_spec
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A)
    (α : Section1.ClassFunction L) :
    alphaBSpec H α B (alphaBFromProjection A L H h hB hBA α) := by
  intro h₀ x hh₀ hx
  unfold alphaBFromProjection
  rw [MOfSetProjectionToL_apply_mul A L H h hB hBA hh₀ hx]

public theorem alphaBFromProjection_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A)
    (α : Section1.ClassFunction L)
    (hα : Theory.Character.IsVirtualCharacter α) :
    Theory.Character.IsVirtualCharacter (alphaBFromProjection A L H h hB hBA α) := by
  exact isVirtualCharacter_comp_monoidHom
    (MOfSetProjectionToL A L H h hB hBA) hα

private theorem inducedCF_apply_unfold
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S] (θ : Section1.ClassFunction S) (g : G) :
    Section1.inducedCF S θ g =
      (Nat.card S : ℂ)⁻¹ *
        (by
          classical
          exact ∑ x : G,
            if hx : x * g * x⁻¹ ∈ S then
              θ ⟨x * g * x⁻¹, hx⟩
            else
              0) := by
  classical
  rfl

private theorem inducedCF_apply_unfold_inv
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S] (θ : Section1.ClassFunction S) (g : G) :
    Section1.inducedCF S θ g =
      (Nat.card S : ℂ)⁻¹ *
        (by
          classical
          exact ∑ x : G,
            if hx : x⁻¹ * g * x ∈ S then
              θ ⟨x⁻¹ * g * x, hx⟩
            else
              0) := by
  classical
  rw [inducedCF_apply_unfold S θ g]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ ?_
  intro x
  simp [mul_assoc]

private theorem mem_transporterSet_iff
    {G : Type u} [Group G] (g : G) (X : Set G) (x : G) :
    x ∈ transporterSet g X ↔ x⁻¹ * g * x ∈ X := by
  simp [transporterSet, conjBy, mul_assoc]


private theorem MOfSet_mem_decompose
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty) (hBA : B ⊆ A)
    {m : G} (hm : m ∈ MOfSet H L B) :
    ∃ h₀ ∈ HInter H B, ∃ x ∈ normalizerIn L B, m = h₀ * x := by
  exact
    (MOfSet_isInternalSemidirectProduct A L H h hB hBA).mul_surjective m hm


private theorem dadeInclusionExclusionSum_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (H : G → Subgroup G)
    (reps : Finset (Set G))
    (αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B))
    (hαB : ∀ B ∈ reps,
      Theory.Character.IsVirtualCharacter (αB B)) :
    Theory.Character.IsVirtualCharacter (dadeInclusionExclusionSum L H reps αB) := by
  classical
  have hterm :
      ∀ B ∈ reps,
        Theory.Character.IsVirtualCharacter
          (((-1 : ℤ) ^ Nat.card B) •
            Section1.inducedCF (MOfSet H L B) (αB B)) := by
    intro B hB
    exact isVirtualCharacter_zsmul ((-1 : ℤ) ^ Nat.card B)
      (inducedCF_isVirtualCharacter_of_virtualCharacter
        (MOfSet H L B) (hαB B hB))
  have hsum :
      Theory.Character.IsVirtualCharacter
        (fun g : G =>
          ∑ B ∈ reps, ((-1 : ℤ) ^ Nat.card B : ℂ) *
            Section1.inducedCF (MOfSet H L B) (αB B) g) := by
    simpa [zsmul_eq_mul] using
      (isVirtualCharacter_finset_sum reps
        (fun B : Set G => ((-1 : ℤ) ^ Nat.card B) •
          Section1.inducedCF (MOfSet H L B) (αB B))
        hterm)
  have hneg :
      dadeInclusionExclusionSum L H reps αB =
        (-1 : ℤ) •
          (fun g : G =>
            ∑ B ∈ reps, ((-1 : ℤ) ^ Nat.card B : ℂ) *
              Section1.inducedCF (MOfSet H L B) (αB B) g) := by
    ext g
    simp [dadeInclusionExclusionSum]
  rw [hneg]
  exact isVirtualCharacter_zsmul (-1) hsum


private theorem internalDirectProduct_mul_unique
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalDirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H :=
    H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by
        simp
      _ = h₂ := by
        simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private theorem internalSemidirectProduct_mem_left_of_order_coprime_right
    {G : Type u} [Group G] [Finite G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) {x : G}
    (hxC : x ∈ C) (hcop : Nat.Coprime (orderOf x) (Nat.card K)) :
    x ∈ H := by
  let cx : C := ⟨x, hxC⟩
  let π := internalSemidirectRightProjection h
  have horder_dvd_x : orderOf (π cx) ∣ orderOf x := by
    have hmap : orderOf (π cx) ∣ orderOf cx := orderOf_map_dvd π cx
    simpa [cx, Subgroup.orderOf_coe] using hmap
  have horder_dvd_K : orderOf (π cx) ∣ Nat.card K :=
    orderOf_dvd_natCard (π cx)
  have horder_one : orderOf (π cx) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder_dvd_x horder_dvd_K
  have hright_one : (internalSemidirectRightComponent h cx : G) = 1 := by
    have hπone : π cx = 1 := orderOf_eq_one_iff.mp horder_one
    simpa [π, internalSemidirectRightProjection] using congrArg Subtype.val hπone
  have hdec := internalSemidirectLeft_mul_rightComponent h cx
  have hx_eq_left : x = (internalSemidirectLeftComponent h cx : G) := by
    change (internalSemidirectLeftComponent h cx : G) *
        (internalSemidirectRightComponent h cx : G) = x at hdec
    simpa [hright_one] using hdec.symm
  simp [hx_eq_left]

public theorem centralizerIn_hInter_eq_hInter_union_singleton
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A) {a : G} (ha : a ∈ A) :
    centralizerIn (HInter H B) a =
      HInter H (Set.union B (Set.singleton a)) := by
  apply le_antisymm
  · intro x hx
    have hxB : x ∈ HInter H B := (Subgroup.mem_inf.mp hx).1
    rcases hB with ⟨b, hb⟩
    have hxHb : x ∈ H b := by
      exact hInter_le_of_mem H hb hxB
    have hxC : x ∈ elementCentralizer a := (Subgroup.mem_inf.mp hx).2
    have hx_order_dvd_Hb : orderOf x ∣ Nat.card (H b) :=
      Subgroup.orderOf_dvd_natCard (H b) hxHb
    have hcop :
        Nat.Coprime (orderOf x) (Nat.card (centralizerIn L a)) :=
      Nat.Coprime.of_dvd_left hx_order_dvd_Hb
        (h.coprime_orders (hBA hb) ha)
    have hxa : x ∈ H a :=
      internalSemidirectProduct_mem_left_of_order_coprime_right
        (h.centralizer_eq_product ha) hxC hcop
    change x ∈ ⨅ b : Set.union B (Set.singleton a), H (b : G)
    rw [Subgroup.mem_iInf]
    intro b'
    rcases b'.2 with hb' | ha'
    · exact hInter_le_of_mem H hb' hxB
    · have hb'_eq : (b' : G) = a := Set.mem_singleton_iff.mp ha'
      simpa [hb'_eq] using hxa
  · intro x hx
    have hxB : x ∈ HInter H B := by
      change x ∈ ⨅ b : B, H (b : G)
      rw [Subgroup.mem_iInf]
      intro b
      exact hInter_le_of_mem H (B := Set.union B (Set.singleton a))
        (by exact Or.inl b.2) hx
    have hxa : x ∈ H a :=
      hInter_le_of_mem H (B := Set.union B (Set.singleton a))
        (by exact Or.inr rfl) hx
    refine Subgroup.mem_inf.mpr ⟨hxB, ?_⟩
    exact (h.centralizer_eq_product ha).left_le hxa

private theorem conjugateIn_symm_early {G : Type u} [Group G] {a b : G}
    (h : conjugateIn a b) :
    conjugateIn b a := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  have hx' := congrArg (fun t : G => x⁻¹ * t * x) hx
  simpa [conjBy, mul_assoc] using hx'.symm

private theorem normalizerIn_conjBy_mem_hInter
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A)
    {x y : G} (hx : x ∈ normalizerIn L B) (hy : y ∈ HInter H B) :
    conjBy x y ∈ HInter H B := by
  have h24 := (proposition_2_4 A L H).1 h
  have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
  have hxnorm : normalizesSet B x := (Subgroup.mem_inf.mp hx).2
  have hxnormInv : normalizesSet B x⁻¹ := normalizesSet_inv hxnorm
  change conjBy x y ∈ ⨅ b : B, H (b : G)
  rw [Subgroup.mem_iInf]
  intro b
  have hb' : conjBy x⁻¹ (b : G) ∈ B := (hxnormInv b).2 b.2
  have hyb : y ∈ H (conjBy x⁻¹ (b : G)) := by
    change y ∈ ⨅ b : B, H (b : G) at hy
    rw [Subgroup.mem_iInf] at hy
    exact hy ⟨conjBy x⁻¹ (b : G), hb'⟩
  have hEq :
      H (conjBy x⁻¹ (b : G)) = conjugateSubgroup x⁻¹ (H (b : G)) := by
    simpa [conjBy, mul_assoc] using
      h24 (a := (b : G)) (x := x⁻¹) (hBA b.2) (L.inv_mem hxL)
  have hyconj : y ∈ conjugateSubgroup x⁻¹ (H (b : G)) := by
    simpa [hEq] using hyb
  rcases hyconj with ⟨u, hu, hyu⟩
  have hcalc : conjBy x y = u := by
    rw [hyu]
    simp [conjBy, mul_assoc]
  simpa [hcalc] using hu

private theorem normalizerIn_normalizes_hInter
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A)
    {x : G} (hx : x ∈ normalizerIn L B) :
    normalizesSet (HInter H B : Set G) x := by
  intro y
  constructor
  · intro hxy
    have hxinv : x⁻¹ ∈ normalizerIn L B := (normalizerIn L B).inv_mem hx
    have hy :=
      normalizerIn_conjBy_mem_hInter (A := A) (L := L) (H := H) h hBA
        hxinv hxy
    simpa [conjBy, mul_assoc] using hy
  · intro hy
    exact normalizerIn_conjBy_mem_hInter (A := A) (L := L) (H := H) h hBA
      hx hy

private theorem orderOf_mem_A_coprime_hInter
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A) {b : G} (hbA : b ∈ A) :
    Nat.Coprime (orderOf b) (Nat.card (HInter H B)) := by
  rcases hB with ⟨a, haB⟩
  have hHdiv : Nat.card (HInter H B) ∣ Nat.card (H a) := by
    exact Subgroup.card_dvd_of_le (hInter_le_of_mem H haB)
  have hbCL : b ∈ centralizerIn L b := by
    refine Subgroup.mem_inf.mpr ⟨h.subset_L b hbA, ?_⟩
    unfold elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    simp
  have hord : orderOf b ∣ Nat.card (centralizerIn L b) :=
    Subgroup.orderOf_dvd_natCard (centralizerIn L b) hbCL
  have hcop :
      Nat.Coprime (Nat.card (HInter H B)) (Nat.card (centralizerIn L b)) :=
    Nat.Coprime.of_dvd_left hHdiv (h.coprime_orders (hBA haB) hbA)
  exact (Nat.Coprime.of_dvd_right hord hcop).symm

private theorem hInter_mul_normalizer_mem_conjugateSet_cosetProduct
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {h₀ b : G} (hh₀ : h₀ ∈ HInter H B)
    (hbN : b ∈ normalizerIn L B) (hbA : b ∈ A) :
    h₀ * b ∈ conjugateSet (cosetProduct b (H b)) := by
  have hnorm :
      normalizesSet (HInter H B : Set G) b :=
    normalizerIn_normalizes_hInter (A := A) (L := L) (H := H) h hBA hbN
  have hcop : Nat.Coprime (orderOf b) (Nat.card (HInter H B)) :=
    orderOf_mem_A_coprime_hInter (A := A) (L := L) (H := H) h hB hBA hbA
  rcases proposition_2_1 b (HInter H B) hnorm hcop with
    ⟨reps, _hreps_card, _hreps_mem, _hreps_disj, hunion⟩
  have hmemb : h₀ * b ∈ subgroupCosetByElement (HInter H B) b := by
    exact ⟨h₀, hh₀, rfl⟩
  rw [hunion] at hmemb
  rcases hmemb with ⟨x, _hxrep, hpiece⟩
  unfold conjugateCosetPiece conjugateImage subgroupCosetByElement rightTranslateSet at hpiece
  rcases hpiece with ⟨s, hs, hsx⟩
  rcases hs with ⟨c, hc, hcs⟩
  have hcUnion : c ∈ HInter H (B ∪ Set.singleton b) := by
    have hcUnion' : c ∈ HInter H (Set.union B (Set.singleton b)) := by
      rw [← centralizerIn_hInter_eq_hInter_union_singleton h hB hBA hbA]
      exact hc
    have hunion : Set.union B (Set.singleton b) = B ∪ Set.singleton b := by
      rfl
    rw [← hunion]
    exact hcUnion'
  have hcHb : c ∈ H b :=
    hInter_le_of_mem H (B := B ∪ Set.singleton b) (by exact Or.inr rfl) hcUnion
  have hccomm : c * b = b * c := by
    have hcent : c ∈ elementCentralizer b := (Subgroup.mem_inf.mp hc).2
    unfold elementCentralizer at hcent
    rw [Subgroup.mem_centralizer_iff] at hcent
    exact (hcent b (by simp)).symm
  refine ⟨c * b, ?_, ?_⟩
  · refine ⟨b, by simp, c, hcHb, ?_⟩
    exact hccomm
  · refine ⟨x, ?_⟩
    simpa [hcs] using hsx.symm

private theorem hInter_mul_normalizer_mem_dadeSupport_of_right_mem_A
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {h₀ b : G} (hh₀ : h₀ ∈ HInter H B)
    (hbN : b ∈ normalizerIn L B) (hbA : b ∈ A) :
    h₀ * b ∈ dadeSupport A H := by
  rcases hInter_mul_normalizer_mem_conjugateSet_cosetProduct
      (A := A) (L := L) (H := H) h hB hBA hh₀ hbN hbA with
    ⟨s, hs, hconj⟩
  rcases hs with ⟨b', hb', k, hk, hs_eq⟩
  rw [Set.mem_singleton_iff] at hb'
  subst b'
  exact ⟨b, hbA, k, hk, by simpa [hs_eq] using conjugateIn_symm_early hconj⟩


  private theorem centralizer_card_eq_mul
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A) :
    Nat.card (elementCentralizer a) =
      Nat.card (H a) * Nat.card (centralizerIn L a) :=
  internalSemidirectProduct_card_mul (h.centralizer_eq_product ha)

private theorem mem_elementCentralizer_commute'
    {G : Type u} [Group G] {a c : G}
    (hc : c ∈ elementCentralizer a) :
    a * c = c * a := by
  unfold elementCentralizer at hc
  rw [Subgroup.mem_centralizer_iff] at hc
  exact hc a (by simp)

private theorem mem_elementCentralizer_of_conjBy_eq_self'
    {G : Type u} [Group G] {a g : G}
    (hga : conjBy g a = a) :
    g ∈ elementCentralizer a := by
  unfold elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  calc
    a * g = conjBy g a * g := by rw [hga]
    _ = g * a := by simp [conjBy, mul_assoc]

private theorem conjBy_pow'
    {G : Type u} [Group G] (x y : G) (n : ℕ) :
    conjBy x (y ^ n) = conjBy x y ^ n := by
  simp [conjBy]

private theorem conjBy_mem_H_of_mem_elementCentralizer'
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g u : G}
    (ha : a ∈ A) (hg : g ∈ elementCentralizer a) (hu : u ∈ H a) :
    conjBy g u ∈ H a := by
  let C := elementCentralizer a
  have hprod := h.centralizer_eq_product ha
  haveI : ((H a).subgroupOf C).Normal := by
    simpa [C] using internalSemidirectProduct_left_normal hprod
  have hmem :=
    Subgroup.Normal.conj_mem (show ((H a).subgroupOf C).Normal from inferInstance)
      (⟨u, hprod.left_le hu⟩ : C) hu (⟨g, hg⟩ : C)
  change (((⟨g, hg⟩ : C) * (⟨u, hprod.left_le hu⟩ : C) *
    (⟨g, hg⟩ : C)⁻¹ : C) : G) ∈ H a at hmem
  simpa [C, conjBy, mul_assoc] using hmem

private theorem conjBy_mem_cosetProduct_of_mem_elementCentralizer'
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g z : G}
    (ha : a ∈ A) (hg : g ∈ elementCentralizer a)
    (hz : z ∈ cosetProduct a (H a)) :
    conjBy g z ∈ cosetProduct a (H a) := by
  rcases hz with ⟨s, hs, u, hu, rfl⟩
  rw [Set.mem_singleton_iff] at hs
  subst s
  refine ⟨a, by simp, conjBy g u, conjBy_mem_H_of_mem_elementCentralizer' h ha hg hu, ?_⟩
  calc
    conjBy g (a * u) = conjBy g a * conjBy g u := by
      simp [conjBy, mul_assoc]
    _ = a * conjBy g u := by
      rw [show conjBy g a = a by
        calc
          conjBy g a = g * a * g⁻¹ := rfl
          _ = a * g * g⁻¹ := by rw [mem_elementCentralizer_commute' hg]
          _ = a := by simp [mul_assoc]]

private theorem conjBy_base_of_coset_conjEq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a b x u v : G}
    (ha : a ∈ A) (hb : b ∈ A) (hu : u ∈ H a) (hv : v ∈ H b)
    (hconj : conjBy x (a * u) = b * v) :
    conjBy x a = b := by
  let N := Nat.card (H a) * Nat.card (H b)
  have huN : u ^ N = 1 := by
    dsimp [N]
    have hu0 : u ^ Nat.card (H a) = 1 := by
      exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (H a) hu)
    rw [pow_mul, hu0]
    simp
  have hvN : v ^ N = 1 := by
    dsimp [N]
    have hv0 : v ^ Nat.card (H b) = 1 := by
      exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (H b) hv)
    rw [Nat.mul_comm, pow_mul, hv0]
    simp
  have haCL : a ∈ centralizerIn L a := by
    exact
      have haL : a ∈ L := h.subset_L a ha
      Subgroup.mem_inf.mpr
        ⟨haL, by
          unfold elementCentralizer
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          simp⟩
  have hbCL : b ∈ centralizerIn L b := by
    exact
      have hbL : b ∈ L := h.subset_L b hb
      Subgroup.mem_inf.mpr
        ⟨hbL, by
          unfold elementCentralizer
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          simp⟩
  have horda : orderOf a ∣ Nat.card (centralizerIn L a) := by
    exact Subgroup.orderOf_dvd_natCard (centralizerIn L a) haCL
  have hordb : orderOf b ∣ Nat.card (centralizerIn L b) := by
    exact Subgroup.orderOf_dvd_natCard (centralizerIn L b) hbCL
  have hHa_oa : Nat.Coprime (Nat.card (H a)) (orderOf a) := by
    exact (h.coprime_orders ha ha).of_dvd_right horda
  have hHa_ob : Nat.Coprime (Nat.card (H a)) (orderOf b) := by
    exact (h.coprime_orders ha hb).of_dvd_right hordb
  have hHb_oa : Nat.Coprime (Nat.card (H b)) (orderOf a) := by
    exact (h.coprime_orders hb ha).of_dvd_right horda
  have hHb_ob : Nat.Coprime (Nat.card (H b)) (orderOf b) := by
    exact (h.coprime_orders hb hb).of_dvd_right hordb
  have hprod :
      Nat.Coprime (Nat.card (H a) * Nat.card (H b)) (orderOf a * orderOf b) := by
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hHa_oa hHa_ob)
      (Nat.Coprime.mul_right hHb_oa hHb_ob)
  have hN_pair : Nat.Coprime N (orderOf (a, b)) := by
    dsimp [N]
    rw [Prod.orderOf_mk]
    exact hprod.of_dvd_right
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
  rcases exists_pow_eq_self_of_coprime (x := (a, b)) hN_pair with ⟨m, hm⟩
  have hpair : ((a, b) : G × G) ^ (N * m) = (a, b) := by
    simpa [pow_mul] using hm
  have haNm : a ^ (N * m) = a := by
    simpa using congrArg Prod.fst hpair
  have hbNm : b ^ (N * m) = b := by
    simpa using congrArg Prod.snd hpair
  have huNm : u ^ (N * m) = 1 := by
    rw [pow_mul, huN]
    simp
  have hvNm : v ^ (N * m) = 1 := by
    rw [pow_mul, hvN]
    simp
  have hau_comm : Commute a u := by
    exact
      let hcent : u ∈ elementCentralizer a := (h.centralizer_eq_product ha).left_le hu
      mem_elementCentralizer_commute' hcent
  have hbv_comm : Commute b v := by
    exact
      let hcent : v ∈ elementCentralizer b := (h.centralizer_eq_product hb).left_le hv
      mem_elementCentralizer_commute' hcent
  have hau_pow : (a * u) ^ (N * m) = a := by
    calc
      (a * u) ^ (N * m) = a ^ (N * m) * u ^ (N * m) := hau_comm.mul_pow (N * m)
      _ = a := by simp [haNm, huNm]
  have hbv_pow : (b * v) ^ (N * m) = b := by
    calc
      (b * v) ^ (N * m) = b ^ (N * m) * v ^ (N * m) := hbv_comm.mul_pow (N * m)
      _ = b := by simp [hbNm, hvNm]
  have hxpow : conjBy x ((a * u) ^ (N * m)) = (b * v) ^ (N * m) := by
    calc
      conjBy x ((a * u) ^ (N * m)) = conjBy x (a * u) ^ (N * m) := by
        exact conjBy_pow' x (a * u) (N * m)
      _ = (b * v) ^ (N * m) := by rw [hconj]
  simpa [hau_pow, hbv_pow] using hxpow

private theorem conjugateImage_cosetProduct_eq_of_nonempty_inter
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a x y : G}
    (ha : a ∈ A)
    (hint :
      (conjugateImage (cosetProduct a (H a)) x ∩
        conjugateImage (cosetProduct a (H a)) y).Nonempty) :
    conjugateImage (cosetProduct a (H a)) x =
      conjugateImage (cosetProduct a (H a)) y := by
  rcases hint with ⟨z, hz1, hz2⟩
  rcases hz1 with ⟨s1, hs1, hzs1⟩
  rcases hz2 with ⟨s2, hs2, hzs2⟩
  rcases hs1 with ⟨sa, hsa, u, hu, hs1eq⟩
  rw [Set.mem_singleton_iff] at hsa
  subst sa
  rcases hs2 with ⟨ta, hta, v, hv, hs2eq⟩
  rw [Set.mem_singleton_iff] at hta
  subst ta
  subst s1
  subst s2
  have hxy_conj :
      conjBy (y⁻¹ * x) (a * u) = a * v := by
    have : conjBy x (a * u) = conjBy y (a * v) := by
      calc
        conjBy x (a * u) = z := hzs1.symm
        _ = conjBy y (a * v) := hzs2
    have := congrArg (fun t : G => y⁻¹ * t * y) this
    simpa [conjBy, mul_assoc] using this
  have hfix :
      conjBy (y⁻¹ * x) a = a := by
    exact conjBy_base_of_coset_conjEq h ha ha hu hv hxy_conj
  have hcent : y⁻¹ * x ∈ elementCentralizer a := by
    exact mem_elementCentralizer_of_conjBy_eq_self' hfix
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨conjBy (y⁻¹ * x) s, ?_, ?_⟩
    · exact conjBy_mem_cosetProduct_of_mem_elementCentralizer' h ha hcent hs
    · simp [conjBy, mul_assoc]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨conjBy (x⁻¹ * y) s, ?_, ?_⟩
    · exact
        let hcent' : x⁻¹ * y ∈ elementCentralizer a := by
          simpa using (Subgroup.inv_mem (elementCentralizer a) hcent)
        conjBy_mem_cosetProduct_of_mem_elementCentralizer' h ha hcent' hs
    · simp [conjBy, mul_assoc]

private theorem isVirtualCharacter_neg
    {G : Type u} [Group G]
    {χ : G → ℂ} (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (-χ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, fun i => -m i, n, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations]

private theorem conjugateIn_refl {G : Type u} [Group G] (g : G) :
    conjugateIn g g := by
  refine ⟨1, ?_⟩
  simp [conjBy]

private theorem conjugateIn_trans {G : Type u} [Group G] {a b c : G}
    (hab : conjugateIn a b) (hbc : conjugateIn b c) :
    conjugateIn a c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨y * x, ?_⟩
  calc
    conjBy (y * x) a = conjBy y (conjBy x a) := by
      simp [conjBy, mul_assoc]
    _ = c := by
      rw [hx, hy]

private theorem alphaBSpec_nonzero_right_mem_A
    {G : Type u} [Group G] {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    {B : Set G} {α : Section1.ClassFunction L}
    {αB : Section1.ClassFunction (MOfSet H L B)}
    (hαA : ∀ l : L, (l : G) ∉ A → α l = 0)
    (hαB : alphaBSpec H α B αB)
    {h₀ b : G} (hh₀ : h₀ ∈ HInter H B) (hbN : b ∈ normalizerIn L B)
    (hne :
      αB ⟨h₀ * b, hInter_mul_normalizer_mem_MOfSet H L B hh₀ hbN⟩ ≠ 0) :
    b ∈ A := by
  by_contra hbA
  have hval :
      αB ⟨h₀ * b, hInter_mul_normalizer_mem_MOfSet H L B hh₀ hbN⟩ =
        α ⟨b, (Subgroup.mem_inf.mp hbN).1⟩ :=
    hαB hh₀ hbN
  exact hne (by rw [hval, hαA ⟨b, (Subgroup.mem_inf.mp hbN).1⟩ hbA])

private theorem alphaBSpec_nonzero_conjugate_mem_dadeSupport
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {α : Section1.ClassFunction L}
    {αB : Section1.ClassFunction (MOfSet H L B)}
    (hαA : ∀ l : L, (l : G) ∉ A → α l = 0)
    (hαB : alphaBSpec H α B αB)
    {g x : G} (hxM : x⁻¹ * g * x ∈ MOfSet H L B)
    (hne : αB ⟨x⁻¹ * g * x, hxM⟩ ≠ 0) :
    g ∈ dadeSupport A H := by
  rcases MOfSet_mem_decompose A L H h hB hBA hxM with
    ⟨h₀, hh₀, b, hbN, hdecomp⟩
  have hne' :
      αB ⟨h₀ * b, hInter_mul_normalizer_mem_MOfSet H L B hh₀ hbN⟩ ≠ 0 := by
    intro hzero
    exact hne (by
      convert hzero)
  have hbA : b ∈ A :=
    alphaBSpec_nonzero_right_mem_A hαA hαB hh₀ hbN hne'
  have hsupp :
      h₀ * b ∈ dadeSupport A H :=
    hInter_mul_normalizer_mem_dadeSupport_of_right_mem_A
      (A := A) (L := L) (H := H) h hB hBA hh₀ hbN hbA
  have hxconj : conjugateIn g (h₀ * b) := by
    refine ⟨x⁻¹, ?_⟩
    simpa [conjBy, mul_assoc] using hdecomp
  rcases hsupp with ⟨a, ha, k, hk, hconj⟩
  exact ⟨a, ha, k, hk, conjugateIn_trans hxconj hconj⟩

public theorem inducedCF_alphaB_eq_zero_of_not_mem_dadeSupport
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {α : Section1.ClassFunction L}
    {αB : Section1.ClassFunction (MOfSet H L B)}
    (hαA : ∀ l : L, (l : G) ∉ A → α l = 0)
    (hαB : alphaBSpec H α B αB)
    {g : G} (hg : g ∉ dadeSupport A H) :
    Section1.inducedCF (MOfSet H L B) αB g = 0 := by
  classical
  rw [inducedCF_apply_unfold_inv (MOfSet H L B) αB g]
  have hsum :
      (∑ x : G,
        if hx : x⁻¹ * g * x ∈ MOfSet H L B then
          αB ⟨x⁻¹ * g * x, hx⟩
        else
          0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxM : x⁻¹ * g * x ∈ MOfSet H L B
    · rw [dif_pos hxM]
      by_contra hne
      exact hg
        (alphaBSpec_nonzero_conjugate_mem_dadeSupport
          (A := A) (L := L) (H := H) h hB hBA hαA hαB hxM hne)
    · rw [dif_neg hxM]
  simp [hsum]

private theorem conjugateSet_closed_under_conjugateIn_left
    {G : Type u} [Group G] {S : Set G} {g y : G}
    (hg : g ∈ conjugateSet S) (hyg : conjugateIn y g) :
    y ∈ conjugateSet S := by
  rcases hg with ⟨s, hs, hsg⟩
  exact ⟨s, hs, conjugateIn_trans hsg (conjugateIn_symm_early hyg)⟩

private theorem classFunction_eq_of_conjugateInSubgroup
    {G : Type u} [Group G] {L : Subgroup G}
    (α : Section1.ClassFunction L) (hαclass : Section1.IsClassFunction α)
    {a b : G} (haL : a ∈ L) (hbL : b ∈ L)
    (hconj : conjugateInSubgroup L a b) :
    α ⟨b, hbL⟩ = α ⟨a, haL⟩ := by
  rcases hconj with ⟨x, hx⟩
  have hx_sub :
      x * ⟨a, haL⟩ * x⁻¹ = ⟨b, hbL⟩ := by
    ext
    exact hx
  calc
    α ⟨b, hbL⟩ = α (x * ⟨a, haL⟩ * x⁻¹) := by rw [hx_sub]
    _ = α ⟨a, haL⟩ := hαclass x ⟨a, haL⟩

private theorem alphaBSpec_apply_eq_of_mem_support_piece
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {α : Section1.ClassFunction L}
    {αB : Section1.ClassFunction (MOfSet H L B)}
    (hαclass : Section1.IsClassFunction α)
    (hαA : ∀ l : L, (l : G) ∉ A → α l = 0)
    (hαB : alphaBSpec H α B αB)
    {g x a : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a)))
    (hxM : x⁻¹ * g * x ∈ MOfSet H L B) :
    ((∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
        x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b) →
      αB ⟨x⁻¹ * g * x, hxM⟩ = α ⟨a, h.subset_L a ha⟩) ∧
    (¬ (∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
        x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b) →
      αB ⟨x⁻¹ * g * x, hxM⟩ = 0) := by
  classical
  rcases MOfSet_mem_decompose A L H h hB hBA hxM with
    ⟨h₀, hh₀, b, hbN, hdecomp⟩
  have hval :
      αB ⟨x⁻¹ * g * x, hxM⟩ =
        α ⟨b, (Subgroup.mem_inf.mp hbN).1⟩ := by
    convert hαB hh₀ hbN
  constructor
  · intro hexists
    rcases hexists with ⟨b', hb'N, hb'conj, hb'trans⟩
    rcases hb'trans with ⟨h₁, hh₁, hb'eq⟩
    have huniq : b' = b := by
      have hsemi := MOfSet_isInternalSemidirectProduct A L H h hB hBA
      exact (internalSemidirectProduct_mul_unique hsemi hh₁ hh₀ hb'N hbN
        (hb'eq.symm.trans hdecomp)).2
    have hab : conjugateInSubgroup L a b := by
      simpa [huniq] using hb'conj
    rw [hval]
    exact classFunction_eq_of_conjugateInSubgroup α hαclass
      (h.subset_L a ha) (Subgroup.mem_inf.mp hbN).1 hab
  · intro hnot
    rw [hval]
    by_cases hbA : b ∈ A
    · have hxb_piece :
          x⁻¹ * g * x ∈ conjugateSet (cosetProduct b (H b)) := by
        rw [hdecomp]
        exact hInter_mul_normalizer_mem_conjugateSet_cosetProduct
          (A := A) (L := L) (H := H) h hB hBA hh₀ hbN hbA
      have hg_conj_x : conjugateIn (x⁻¹ * g * x) g := by
        refine ⟨x, ?_⟩
        simp [conjBy, mul_assoc]
      have hg_b_piece : g ∈ conjugateSet (cosetProduct b (H b)) :=
        conjugateSet_closed_under_conjugateIn_left hxb_piece
          (conjugateIn_symm_early hg_conj_x)
      have hmeet :
          (conjugateSet (cosetProduct a (H a)) ∩
            conjugateSet (cosetProduct b (H b))).Nonempty :=
        ⟨g, hgpiece, hg_b_piece⟩
      have hab : conjugateInSubgroup L a b :=
        (proposition_2_4 A L H).2.1 h ha hbA hmeet
      exfalso
      exact hnot ⟨b, hbN, hab, ⟨h₀, hh₀, hdecomp⟩⟩
    · exact hαA ⟨b, (Subgroup.mem_inf.mp hbN).1⟩ hbA


private theorem inducedCF_alphaB_support_piece_filter_formula
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {α : Section1.ClassFunction L}
    {αB : Section1.ClassFunction (MOfSet H L B)}
    (hαclass : Section1.IsClassFunction α)
    (hαA : ∀ l : L, (l : G) ∉ A → α l = 0)
    (hαB : alphaBSpec H α B αB)
    {g a : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a))) :
    Section1.inducedCF (MOfSet H L B) αB g =
      (Nat.card (MOfSet H L B) : ℂ)⁻¹ *
        (by
          classical
          exact ∑ x : G,
            if _ :
                ∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
                  x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b then
              α ⟨a, h.subset_L a ha⟩
            else
              0) := by
  classical
  rw [inducedCF_apply_unfold_inv (MOfSet H L B) αB g]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hxM : x⁻¹ * g * x ∈ MOfSet H L B
  · rw [dif_pos hxM]
    by_cases hx :
        ∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
          x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b
    · rw [dif_pos hx]
      exact (alphaBSpec_apply_eq_of_mem_support_piece
        (A := A) (L := L) (H := H) h hB hBA
        hαclass hαA hαB ha hgpiece hxM).1 hx
    · rw [dif_neg hx]
      exact (alphaBSpec_apply_eq_of_mem_support_piece
        (A := A) (L := L) (H := H) h hB hBA
        hαclass hαA hαB ha hgpiece hxM).2 hx
  · rw [dif_neg hxM]
    rw [dif_neg]
    intro hx
    rcases hx with ⟨b, hbN, _hab, hxb⟩
    rcases hxb with ⟨h₀, hh₀, hxeq⟩
    exact hxM (by
      rw [hxeq]
      exact hInter_mul_normalizer_mem_MOfSet H L B hh₀ hbN)

private theorem support_piece_filter_sum_eq_transporter_card_sum
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A) (g a : G) (αa : ℂ) :
    (by
      classical
      exact ∑ x : G,
        if _ :
            ∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
              x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b then
          αa
        else
          0) =
      αa *
        ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
          (Nat.card (transporterSet g
            (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
  classical
  let P : G → Prop := fun x =>
    ∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
      x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b
  let idx : Type u := {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b}
  letI : DecidableEq G := Classical.decEq G
  letI : DecidableEq idx := Classical.decEq idx
  letI : Fintype idx := Fintype.ofFinite idx
  let fiber : idx → Finset G := fun b =>
    (transporterSet g
      (rightTranslateSet (HInter H B : Set G) (b : G))).toFinset
  have hfilter :
      (Finset.univ.filter P) = (Finset.univ : Finset idx).biUnion fiber := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨_hxuniv, hxP⟩
      rcases hxP with ⟨b, hbN, hab, hxb⟩
      rw [Finset.mem_biUnion]
      refine ⟨⟨b, hbN, hab⟩, by simp, ?_⟩
      exact (Set.mem_toFinset).2 (by
        rw [mem_transporterSet_iff]
        exact hxb)
    · intro hx
      rw [Finset.mem_filter]
      constructor
      · simp
      · rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨b, _hb, hxfiber⟩
        have hxtrans :
            x ∈ transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G)) :=
          (Set.mem_toFinset).1 hxfiber
        rw [mem_transporterSet_iff] at hxtrans
        exact ⟨b, b.2.1, b.2.2, hxtrans⟩
  have hpair :
      ((Finset.univ : Finset idx) : Set idx).PairwiseDisjoint fiber := by
    intro b _hb c _hc hbc
    dsimp [fiber, Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxb hxc
    have hxb' :
        x ∈ transporterSet g
          (rightTranslateSet (HInter H B : Set G) (b : G)) :=
      (Set.mem_toFinset).1 hxb
    have hxc' :
        x ∈ transporterSet g
          (rightTranslateSet (HInter H B : Set G) (c : G)) :=
      (Set.mem_toFinset).1 hxc
    rw [mem_transporterSet_iff] at hxb' hxc'
    rcases hxb' with ⟨h₁, hh₁, hxb_eq⟩
    rcases hxc' with ⟨h₂, hh₂, hxc_eq⟩
    have hbc_val : (b : G) = (c : G) := by
      have hsemi := MOfSet_isInternalSemidirectProduct A L H h hB hBA
      exact (internalSemidirectProduct_mul_unique hsemi hh₁ hh₂ b.2.1 c.2.1
        (hxb_eq.symm.trans hxc_eq)).2
    exact hbc (Subtype.ext hbc_val)
  have hsum_filter :
      (∑ x : G, if _hx : P x then αa else 0) =
        ∑ x ∈ Finset.univ.filter P, αa := by
    exact (Finset.sum_filter (s := (Finset.univ : Finset G))
      (p := P) (f := fun _x : G => αa)).symm
  have hcalc :
      (∑ x : G, if hx : P x then αa else 0) =
        αa *
          ∑ b : idx,
            (Nat.card (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
    calc
      (∑ x : G, if hx : P x then αa else 0) =
          ∑ x ∈ Finset.univ.filter P, αa := hsum_filter
      _ = ∑ x ∈ (Finset.univ : Finset idx).biUnion fiber, αa := by
            rw [hfilter]
      _ = ∑ b : idx, ∑ x ∈ fiber b, αa := by
            simpa [fiber] using (Finset.sum_biUnion hpair (f := fun _x : G => αa))
      _ = αa *
          ∑ b : idx,
            (Nat.card (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _hb
            have hcard :
                (fiber b).card =
                  Nat.card (transporterSet g
                    (rightTranslateSet (HInter H B : Set G) (b : G))) := by
              dsimp [fiber]
              simpa [Nat.card_coe_set_eq] using
                (Set.ncard_eq_toFinset_card'
                  (transporterSet g
                    (rightTranslateSet (HInter H B : Set G) (b : G)))).symm
            simp [Finset.sum_const, hcard, mul_comm]
  simpa [P, idx] using hcalc

public theorem inducedCF_alphaB_support_piece_formula
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A)
    {hAL : ∀ a ∈ A, a ∈ L}
    {α : Section1.ClassFunction L}
    {αB : Section1.ClassFunction (MOfSet H L B)}
    (hαclass : Section1.IsClassFunction α)
    (hαA : ∀ l : L, (l : G) ∉ A → α l = 0)
    (hαB : alphaBSpec H α B αB)
    {g a : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a))) :
    Section1.inducedCF (MOfSet H L B) αB g =
      dadeInductionFormulaTerm A L H α g a B hAL ha := by
  classical
  let αa : ℂ := α ⟨a, hAL a ha⟩
  let idx : Type u := {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b}
  letI : Fintype idx := Fintype.ofFinite idx
  have hαproof : α ⟨a, h.subset_L a ha⟩ = αa := by
    simp [αa]
  have hfilter :=
    inducedCF_alphaB_support_piece_filter_formula
      (A := A) (L := L) (H := H) h hB hBA
      hαclass hαA hαB ha hgpiece
  have hcount :=
    support_piece_filter_sum_eq_transporter_card_sum
      (A := A) (L := L) (H := H) h hB hBA g a αa
  have hsum :
      (by
        classical
        exact ∑ x : G,
          if hx :
              ∃ b : G, b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b ∧
                x⁻¹ * g * x ∈ rightTranslateSet (HInter H B : Set G) b then
            α ⟨a, h.subset_L a ha⟩
      else
            0) =
        αa *
          ∑ b : idx,
            (Nat.card (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
    simpa [αa, hαproof, idx] using hcount
  have hcalc :
      Section1.inducedCF (MOfSet H L B) αB g =
        (Nat.card (MOfSet H L B) : ℂ)⁻¹ *
          (αa *
            ∑ b : idx,
              (Nat.card (transporterSet g
                (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ)) := by
    rw [hfilter]
    rw [hsum]
  rw [hcalc]
  unfold dadeInductionFormulaTerm
  dsimp [αa, idx]
  ring

private theorem conjugateInSubgroup_refl {G : Type u} [Group G]
    (L : Subgroup G) (g : G) :
    conjugateInSubgroup L g g := by
  refine ⟨1, ?_⟩
  simp [conjBy]

private theorem conjugateInSubgroup_symm {G : Type u} [Group G]
    {L : Subgroup G} {a b : G}
    (h : conjugateInSubgroup L a b) :
    conjugateInSubgroup L b a := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  have hx' := congrArg (fun t : G => (x : G)⁻¹ * t * (x : G)) hx
  simpa [conjBy, mul_assoc] using hx'.symm

private theorem conjugateInSubgroup_trans {G : Type u} [Group G]
    {L : Subgroup G} {a b c : G}
    (hab : conjugateInSubgroup L a b)
    (hbc : conjugateInSubgroup L b c) :
    conjugateInSubgroup L a c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨y * x, ?_⟩
  calc
    conjBy ((y * x : L) : G) a = conjBy (y : G) (conjBy (x : G) a) := by
      simp [conjBy, mul_assoc]
    _ = c := by
      rw [hx, hy]

private theorem conjugateIn_conjBy_left_iff {G : Type u} [Group G]
    (x g y : G) :
    conjugateIn (conjBy x g) y ↔ conjugateIn g y := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t * x, ?_⟩
    simpa [conjBy, mul_assoc] using ht
  · rintro ⟨t, ht⟩
    refine ⟨t * x⁻¹, ?_⟩
    simpa [conjBy, mul_assoc] using ht

private theorem dadeSupport_conjBy_iff {G : Type u} [Group G]
    (A : Set G) (H : G → Subgroup G) (x g : G) :
    conjBy x g ∈ dadeSupport A H ↔ g ∈ dadeSupport A H := by
  constructor
  · rintro ⟨a, ha, h0, hh0, hconj⟩
    exact ⟨a, ha, h0, hh0,
      (conjugateIn_conjBy_left_iff x g (a * h0)).1 hconj⟩
  · rintro ⟨a, ha, h0, hh0, hconj⟩
    exact ⟨a, ha, h0, hh0,
      (conjugateIn_conjBy_left_iff x g (a * h0)).2 hconj⟩

public theorem dadeTransform_isClassFunction_of_CFOn
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (β : Section1.ClassFunction L) (hβ : CFOn L A β) :
    Section1.IsClassFunction (dadeTransform H hAL β) := by
  intro x g
  have hdef := definition_2_5 A L H h hAL β hβ
  by_cases hg : g ∈ dadeSupport A H
  · rcases hg with ⟨a, ha, h0, hh0, hconj⟩
    have hconj_x : conjugateIn (conjBy x g) (a * h0) :=
      (conjugateIn_conjBy_left_iff x g (a * h0)).2 hconj
    have hleft :
        dadeTransform H hAL β (conjBy x g) =
          β ⟨a, hAL a ha⟩ :=
      hdef.1 ha hh0 hconj_x
    have hright :
        dadeTransform H hAL β g =
          β ⟨a, hAL a ha⟩ :=
      hdef.1 ha hh0 hconj
    simpa [conjBy] using hleft.trans hright.symm
  · have hxg : conjBy x g ∉ dadeSupport A H := by
      intro hxg
      exact hg ((dadeSupport_conjBy_iff A H x g).1 hxg)
    have hleft := hdef.2 (conjBy x g) hxg
    have hright := hdef.2 g hg
    simpa [conjBy] using hleft.trans hright.symm

public theorem theorem_2_6_transform_constant_on_dade_cosets
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (β : Section1.ClassFunction L) :
    CFOn L A β →
      constantOnDadeCosets A H (dadeTransform H hAL β) := by
  intro hβ a x ha hx
  have hdef := definition_2_5 A L H h hAL β hβ
  calc
    dadeTransform H hAL β (a * x) = β ⟨a, hAL a ha⟩ := by
      exact hdef.1 ha hx (conjugateIn_refl (a * x))
    _ = dadeTransform H hAL β a := by
      have hvalue :
          dadeTransform H hAL β a = β ⟨a, hAL a ha⟩ := by
        simpa using hdef.1 ha (H a).one_mem
          (by simpa using conjugateIn_refl a)
      exact hvalue.symm

private theorem conjugateIn_symm {G : Type u} [Group G] {a b : G}
    (h : conjugateIn a b) :
    conjugateIn b a := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  have hx' := congrArg (fun t : G => x⁻¹ * t * x) hx
  simpa [conjBy, mul_assoc] using hx'.symm

private theorem dadeTransform_eq_of_isClassFunction
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (β : Section1.ClassFunction L) (hβ : Section1.IsClassFunction β)
    {g a h' : G} (ha : a ∈ A) (hh : h' ∈ H a)
    (hconj : conjugateIn g (a * h')) :
    dadeTransform H hAL β g = β ⟨a, hAL a ha⟩ := by
  let hex :
      ∃ a' ∈ A, ∃ h'' ∈ H a', conjugateIn g (a' * h'') :=
    ⟨a, ha, h', hh, hconj⟩
  let a0 : G := Classical.choose hex
  have ha0 : a0 ∈ A := (Classical.choose_spec hex).1
  rcases (Classical.choose_spec hex).2 with ⟨h0, hh0, hconj0⟩
  have hmeet :
      (conjugateSet (cosetProduct a (H a)) ∩
        conjugateSet (cosetProduct a0 (H a0))).Nonempty := by
    refine ⟨g, ?_, ?_⟩
    · refine ⟨a * h', ?_, conjugateIn_symm hconj⟩
      refine ⟨a, by simp, h', hh, rfl⟩
    · refine ⟨a0 * h0, ?_, conjugateIn_symm hconj0⟩
      refine ⟨a0, by simp, h0, hh0, rfl⟩
  have h24 := proposition_2_4 A L H
  have hLconj : conjugateInSubgroup L a a0 := h24.2.1 h ha ha0 hmeet
  rcases hLconj with ⟨x, hx⟩
  have hx' : conjBy x ⟨a, hAL a ha⟩ = ⟨a0, hAL a0 ha0⟩ := by
    ext
    exact hx
  have hβeq : β ⟨a0, hAL a0 ha0⟩ = β ⟨a, hAL a ha⟩ := by
    have htmp := hβ x ⟨a, hAL a ha⟩
    have hx_sub : x * ⟨a, hAL a ha⟩ * x⁻¹ = ⟨a0, hAL a0 ha0⟩ := by
      simpa [conjBy] using hx'
    simpa [hx_sub] using htmp
  have hvalue : dadeTransform H hAL β g = β ⟨a0, hAL a0 ha0⟩ := by
    simp [dadeTransform, hex, a0]
  simpa [hβeq] using hvalue

private theorem dadeTransform_eq_on_A
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (β : Section1.ClassFunction L) (hβ : CFOn L A β)
    {a : G} (ha : a ∈ A) :
    dadeTransform H hAL β a = β ⟨a, hAL a ha⟩ := by
  exact dadeTransform_eq_of_isClassFunction A L H h hAL β hβ.1 ha
    (H a).one_mem (by simpa using conjugateIn_refl a)

public theorem dadeTransform_eq_zero_of_not_mem_support
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) {g : G}
    (hg : g ∉ dadeSupport A H) :
    dadeTransform H hAL α g = 0 := by
  have hnot : ¬ ∃ a ∈ A, ∃ h ∈ H a, conjugateIn g (a * h) := by
    simpa [dadeSupport] using hg
  simp [dadeTransform, hnot]


public theorem scalarProduct_right_congr_on_left_support
    {G : Type u} [Finite G] {φ ψ χ : Section1.ClassFunction G}
    {A : Set G}
    (hφ : ∀ g : G, g ∉ A → φ g = 0)
    (hψχ : ∀ g : G, g ∈ A → ψ g = χ g) :
    Section1.scalarProduct G φ ψ = Section1.scalarProduct G φ χ := by
  classical
  unfold Section1.scalarProduct
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  by_cases hgA : g ∈ A
  · rw [hψχ g hgA]
  · rw [hφ g hgA]
    simp


private theorem scalarProduct_restrict_dadeTransform_eq_of_support
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α β : Section1.ClassFunction L)
    (hα : CFOn L A α) (hβ : CFOn L A β) :
    Section1.scalarProduct L α
        (Section1.subgroupRestriction L (dadeTransform H hAL β)) =
      Section1.scalarProduct L α β := by
  exact scalarProduct_right_congr_on_left_support
    (A := {l : L | (l : G) ∈ A}) (φ := α)
    (ψ := Section1.subgroupRestriction L (dadeTransform H hAL β)) (χ := β)
    (by
      intro l hlA
      exact hα.2 l hlA)
    (by
      intro l hlA
      have hvalue :=
        dadeTransform_eq_on_A A L H h hAL β hβ (a := (l : G)) hlA
      have hsub : (⟨(l : G), hAL (l : G) hlA⟩ : L) = l := by
        ext
        rfl
      simpa [Section1.subgroupRestriction, hsub] using hvalue)

private theorem scalarProduct_dadeAveraging_eq_restrict_of_constant
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (α : Section1.ClassFunction L) (χ : Section1.ClassFunction G)
    (hα : CFOn L A α)
    (hχ : constantOnDadeCosets A H χ) :
    Section1.scalarProduct L α (dadeAveragingFunction L H χ) =
      Section1.scalarProduct L α (Section1.subgroupRestriction L χ) := by
  classical
  exact scalarProduct_right_congr_on_left_support
    (A := {l : L | (l : G) ∈ A}) (φ := α)
    (ψ := dadeAveragingFunction L H χ)
    (χ := Section1.subgroupRestriction L χ)
    (by
      intro l hlA
      exact hα.2 l hlA)
    (by
      intro l hlA
      letI : Fintype (H (l : G)) := Fintype.ofFinite (H (l : G))
      have hsum :
          (∑ x : H (l : G), χ ((l : G) * (x : G))) =
            (Nat.card (H (l : G)) : ℂ) * χ (l : G) := by
        calc
          (∑ x : H (l : G), χ ((l : G) * (x : G))) =
              ∑ _x : H (l : G), χ (l : G) := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                exact hχ hlA x.2
          _ = (Nat.card (H (l : G)) : ℂ) * χ (l : G) := by
                simp [Finset.card_univ]
      have hcard_ne : (Nat.card (H (l : G)) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := H (l : G))).ne'
      have havg : dadeAveragingFunction L H χ l = χ (l : G) := by
        unfold dadeAveragingFunction
        have hmul :
            (Nat.card (H (l : G)) : ℂ)⁻¹ *
                ∑ x : H (l : G), χ ((l : G) * (x : G)) =
              (Nat.card (H (l : G)) : ℂ)⁻¹ *
                ((Nat.card (H (l : G)) : ℂ) * χ (l : G)) := by
          exact congrArg (fun z : ℂ => (Nat.card (H (l : G)) : ℂ)⁻¹ * z) hsum
        rw [hmul]
        field_simp [hcard_ne]
      simpa [Section1.subgroupRestriction] using havg)


private theorem exists_representative_system_for_nonempty_subsets
    {G : Type u} [Group G] [Finite G] (A : Set G) (L : Subgroup G) :
    ∃ reps : Finset (Set G),
      IsRepresentativeSystemForNonemptySubsets A L reps := by
  classical
  let S : Type u := {B : Set G // B.Nonempty ∧ B ⊆ A}
  let rel : S → S → Prop := fun B C => LConjugateSubsets L (B : Set G) (C : Set G)
  have hrel_refl : Std.Refl rel :=
    ⟨by
      intro B
      refine ⟨1, ?_⟩
      ext g
      constructor
      · intro hg
        exact ⟨g, hg, by simp [conjBy]⟩
      · intro hg
        simpa [setConjugateBy, conjBy] using hg⟩
  have hrel_symm : Std.Symm rel :=
    ⟨by
      intro B C hBC
      rcases hBC with ⟨x, hx⟩
      refine ⟨x⁻¹, ?_⟩
      rw [hx]
      simp [setConjugateBy, conjBy, mul_assoc]⟩
  have hrel_trans : IsTrans S rel :=
    ⟨by
      intro B C D hBC hCD
      rcases hBC with ⟨x, hx⟩
      rcases hCD with ⟨y, hy⟩
      refine ⟨y * x, ?_⟩
      rw [hy, hx]
      simp [setConjugateBy, conjBy, mul_assoc]⟩
  let s : Setoid S :=
    { r := rel
      iseqv :=
        { refl := hrel_refl.refl
          symm := by
            intro B C h
            exact hrel_symm.symm B C h
          trans := by
            intro B C D hBC hCD
            exact hrel_trans.trans B C D hBC hCD } }
  let Q := Quotient s
  haveI : Finite Q := by
    refine Finite.of_surjective (Quotient.mk s) ?_
    intro q
    refine ⟨Quotient.out q, ?_⟩
    exact Quotient.out_eq q
  letI : Fintype Q := Fintype.ofFinite Q
  let reps : Finset (Set G) := (Finset.univ : Finset Q).image fun q =>
    ((Quotient.out q : S) : Set G)
  refine ⟨reps, ?_⟩
  constructor
  · intro B hB
    dsimp [reps] at hB
    rcases Finset.mem_image.mp hB with ⟨q, _hq, rfl⟩
    exact (Quotient.out q).2
  · intro C hC hCA
    let c : S := ⟨C, hC, hCA⟩
    let qC : Q := Quotient.mk s c
    let B0 : S := Quotient.out qC
    refine ⟨B0.1, ?_, ?_, ?_⟩
    · dsimp [reps]
      exact Finset.mem_image.mpr ⟨qC, Finset.mem_univ qC, rfl⟩
    · have hq : Quotient.mk s B0 = qC := by
          simp [B0, qC]
      exact Quotient.exact (s := s) hq
    · intro D hD hconj
      rcases Finset.mem_image.mp hD with ⟨qD, _hqD, hDrep⟩
      have hrelD : rel (Quotient.out qD) c := by
        simpa [rel, S, hDrep] using hconj
      have hqDqC : qD = qC := by
        have hmkD : Quotient.mk s (Quotient.out qD) = qD := Quotient.out_eq qD
        have hmkC : Quotient.mk s (Quotient.out qD) = qC := by
          simpa [qC, c] using (Quotient.sound (s := s) hrelD)
        exact hmkD.symm.trans hmkC
      calc
        D = ((Quotient.out qD : S) : Set G) := by simpa using hDrep.symm
        _ = (B0 : Set G) := by
          simpa using congrArg (fun t : S => (t : Set G)) (congrArg Quotient.out hqDqC)

private noncomputable def nonemptySubsetsFinset
    {G : Type u} [Group G] [Finite G] (A : Set G) : Finset (Set G) :=
  by
    classical
    exact (Finset.univ : Finset (Set G)).filter fun B => B.Nonempty ∧ B ⊆ A

private theorem mem_nonemptySubsetsFinset
    {G : Type u} [Group G] [Finite G] {A B : Set G} :
    B ∈ nonemptySubsetsFinset A ↔ B.Nonempty ∧ B ⊆ A := by
  classical
  simp [nonemptySubsetsFinset]

private theorem sum_nonemptySubsetsFinset_pair_union_singleton
    {G : Type u} [Group G] [Finite G] {A : Set G} {a : G}
    (ha : a ∈ A) (f : Set G → ℂ)
    (hpair :
      ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A → a ∉ B →
        f (B ∪ Set.singleton a) = -f B) :
    (∑ B ∈ nonemptySubsetsFinset A, f B) = f (Set.singleton a) := by
  classical
  let s : Finset (Set G) := nonemptySubsetsFinset A
  let s0 : Finset (Set G) := s.filter fun B => a ∉ B
  let s1 : Finset (Set G) := s.filter fun B => a ∈ B
  let sadd : Finset (Set G) := s0.image fun B => B ∪ Set.singleton a
  have hs_split :=
    (Finset.sum_filter_add_sum_filter_not
      (s := s) (p := fun B : Set G => a ∈ B) (f := f)).symm
  have hs_contains : s1 = insert (Set.singleton a) sadd := by
    ext B
    constructor
    · intro hB
      rw [Finset.mem_insert]
      by_cases hBa : B = Set.singleton a
      · exact Or.inl hBa
      · right
        dsimp [sadd]
        rw [Finset.mem_image]
        have hBmems : B ∈ s := (Finset.mem_filter.mp hB).1
        have haB : a ∈ B := (Finset.mem_filter.mp hB).2
        have hBprops : B.Nonempty ∧ B ⊆ A := by
          simpa [nonemptySubsetsFinset] using
            (mem_nonemptySubsetsFinset (A := A) (B := B)).1 hBmems
        let C : Set G := B \ Set.singleton a
        have hCne : C.Nonempty := by
          by_contra hCempty
          have hsubset : B ⊆ Set.singleton a := by
            intro x hxB
            by_cases hxa : x = a
            · subst hxa
              exact Set.mem_singleton_iff.mpr rfl
            · exfalso
              exact hCempty ⟨x, ⟨hxB, fun hx => hxa (Set.mem_singleton_iff.mp hx)⟩⟩
          have hEq : B = Set.singleton a := by
            ext x
            constructor
            · intro hxB
              exact hsubset hxB
            · intro hx
              rcases Set.mem_singleton_iff.mp hx with rfl
              exact haB
          exact hBa hEq
        have hCsub : C ⊆ A := by
          intro x hxC
          exact hBprops.2 hxC.1
        have haC : a ∉ C := by
          intro haC
          exact haC.2 rfl
        have hCmem : C ∈ s0 := by
          dsimp [s0]
          rw [Finset.mem_filter]
          constructor
          · dsimp [s]
            exact (mem_nonemptySubsetsFinset (A := A) (B := C)).2
              ⟨hCne, hCsub⟩
          · exact haC
        have hCeq : C ∪ Set.singleton a = B := by
          ext x
          constructor
          · intro hx
            rcases hx with hxC | hxa
            · exact hxC.1
            · have hx_eq : x = a := Set.mem_singleton_iff.mp hxa
              simpa [hx_eq] using haB
          · intro hxB
            by_cases hxa : x = a
            · exact Or.inr (Set.mem_singleton_iff.mpr hxa)
            · exact Or.inl ⟨hxB, fun hx => hxa (Set.mem_singleton_iff.mp hx)⟩
        exact ⟨C, hCmem, hCeq⟩
    · intro hB
      rw [Finset.mem_insert] at hB
      rcases hB with hBsing | hBimg
      · dsimp [s1]
        subst hBsing
        rw [Finset.mem_filter]
        constructor
        · have hsingmem : Set.singleton a ∈ s := by
            exact (mem_nonemptySubsetsFinset (A := A) (B := Set.singleton a)).2
              ⟨⟨a, rfl⟩, by
                intro x hx
                rcases Set.mem_singleton_iff.mp hx with rfl
                exact ha⟩
          exact hsingmem
        · exact Set.mem_singleton_iff.mpr rfl
      · dsimp [sadd] at hBimg
        rw [Finset.mem_image] at hBimg
        rcases hBimg with ⟨C, hCmem, rfl⟩
        have hCprops : C.Nonempty ∧ C ⊆ A := by
          have hCs : C ∈ s := (Finset.mem_filter.mp hCmem).1
          simpa [nonemptySubsetsFinset] using
            (mem_nonemptySubsetsFinset (A := A) (B := C)).1 hCs
        dsimp [s1]
        rw [Finset.mem_filter]
        constructor
        · have hunionmem : C ∪ Set.singleton a ∈ s := by
            exact (mem_nonemptySubsetsFinset (A := A)
              (B := C ∪ Set.singleton a)).2
              ⟨⟨a, Or.inr rfl⟩, by
                intro x hx
                rcases hx with hxC | hxa
                · exact hCprops.2 hxC
                · rcases Set.mem_singleton_iff.mp hxa with rfl
                  exact ha⟩
          exact hunionmem
        · exact Or.inr rfl
  have hsingleton_not_mem_sadd : Set.singleton a ∉ sadd := by
    intro hmem
    dsimp [sadd] at hmem
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨C, hCmem, hCeq⟩
    have hCprops : C.Nonempty ∧ C ⊆ A := by
      have hCs : C ∈ s := (Finset.mem_filter.mp hCmem).1
      simpa [nonemptySubsetsFinset] using
        (mem_nonemptySubsetsFinset (A := A) (B := C)).1 hCs
    have haC : a ∉ C := (Finset.mem_filter.mp hCmem).2
    rcases hCprops.1 with ⟨x, hxC⟩
    have hxs : x ∈ Set.singleton a := by
      rw [← hCeq]
      exact Or.inl hxC
    have hx_eq : x = a := Set.mem_singleton_iff.mp hxs
    exact haC (by simpa [hx_eq] using hxC)
  have hsum_contains :
      ∑ B ∈ s1, f B = f (Set.singleton a) + (∑ B ∈ sadd, f B) := by
    rw [hs_contains]
    rw [Finset.sum_insert hsingleton_not_mem_sadd]
  have hsum_image :
      ∑ B ∈ sadd, f B = ∑ B ∈ s0, f (B ∪ Set.singleton a) := by
    dsimp [sadd]
    exact Finset.sum_image
      (s := s0) (g := fun B : Set G => B ∪ Set.singleton a) (f := f)
      (by
        intro B hB C hC hEq
        change B ∪ Set.singleton a = C ∪ Set.singleton a at hEq
        ext x
        by_cases hxa : x = a
        · subst x
          have haB : a ∉ B := (Finset.mem_filter.mp hB).2
          have haC : a ∉ C := (Finset.mem_filter.mp hC).2
          constructor <;> intro hx <;> contradiction
        · constructor
          · intro hxB
            have hxUnion : x ∈ B ∪ Set.singleton a := Or.inl hxB
            have hxUnionC : x ∈ C ∪ Set.singleton a := by
              rw [hEq] at hxUnion
              exact hxUnion
            rcases hxUnionC with hxC | hxS
            · exact hxC
            · exact False.elim (hxa (Set.mem_singleton_iff.mp hxS))
          · intro hxC
            have hxUnion : x ∈ C ∪ Set.singleton a := Or.inl hxC
            have hxUnionB : x ∈ B ∪ Set.singleton a := by
              rw [← hEq] at hxUnion
              exact hxUnion
            rcases hxUnionB with hxB | hxS
            · exact hxB
            · exact False.elim (hxa (Set.mem_singleton_iff.mp hxS)))
  have hzero :
      ∑ B ∈ s0, f (B ∪ Set.singleton a) + ∑ B ∈ s0, f B = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro B hB
    have hBprops : B.Nonempty ∧ B ⊆ A := by
      have hBs : B ∈ s := (Finset.mem_filter.mp hB).1
      simpa [nonemptySubsetsFinset] using
        (mem_nonemptySubsetsFinset (A := A) (B := B)).1 hBs
    have haB : a ∉ B := (Finset.mem_filter.mp hB).2
    rw [hpair hBprops.1 hBprops.2 haB]
    simp
  calc
    ∑ B ∈ s, f B =
        ∑ B ∈ s1, f B + ∑ B ∈ s0, f B := hs_split
    _ = (f (Set.singleton a) + ∑ B ∈ sadd, f B) + ∑ B ∈ s0, f B := by
          rw [hsum_contains]
    _ = (f (Set.singleton a) + ∑ B ∈ s0, f (B ∪ Set.singleton a)) +
        ∑ B ∈ s0, f B := by
          rw [hsum_image]
    _ = f (Set.singleton a) +
        (∑ B ∈ s0, f (B ∪ Set.singleton a) + ∑ B ∈ s0, f B) := by
          ring
    _ = f (Set.singleton a) := by
          rw [hzero]
          simp

private noncomputable def lSubsetOrbitFinset
    {G : Type u} [Group G] [Finite G] (L : Subgroup G) (B : Set G) :
    Finset (Set G) :=
  by
    classical
    exact (Finset.univ : Finset L).image fun x : L => setConjugateBy (x : G) B

private theorem mem_lSubsetOrbitFinset
    {G : Type u} [Group G] [Finite G] {L : Subgroup G}
    {B C : Set G} :
    C ∈ lSubsetOrbitFinset L B ↔ LConjugateSubsets L B C := by
  classical
  constructor
  · intro hC
    rw [lSubsetOrbitFinset, Finset.mem_image] at hC
    rcases hC with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    rw [lSubsetOrbitFinset, Finset.mem_image]
    exact ⟨x, by simp, rfl⟩

private theorem lSubsetOrbitFinset_subset_nonemptySubsets
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hB : B.Nonempty ∧ B ⊆ A) :
    lSubsetOrbitFinset L B ⊆ nonemptySubsetsFinset A := by
  classical
  intro C hC
  rw [mem_nonemptySubsetsFinset]
  rw [mem_lSubsetOrbitFinset] at hC
  rcases hC with ⟨x, rfl⟩
  constructor
  · rcases hB.1 with ⟨b, hb⟩
    exact ⟨conjBy (x : G) b, ⟨b, hb, rfl⟩⟩
  · intro c hc
    rcases hc with ⟨b, hb, rfl⟩
    exact (h.L_le_normalizer x.2 b).2 (hB.2 hb)

private theorem lSubsetOrbitFinset_pairwiseDisjoint
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {reps : Finset (Set G)}
    (hreps : IsRepresentativeSystemForNonemptySubsets A L reps) :
    ((reps : Set (Set G))).PairwiseDisjoint (lSubsetOrbitFinset L) := by
  classical
  intro B hB C hC hBC
  change Disjoint (lSubsetOrbitFinset L B) (lSubsetOrbitFinset L C)
  rw [Finset.disjoint_left]
  intro D hDB hDC
  have hDmem : D ∈ nonemptySubsetsFinset A := by
    exact lSubsetOrbitFinset_subset_nonemptySubsets
      (A := A) (L := L) (H := H) h (hreps.1 B hB) hDB
  have hDprops : D.Nonempty ∧ D ⊆ A := (mem_nonemptySubsetsFinset).1 hDmem
  rcases hreps.2 D hDprops.1 hDprops.2 with ⟨R, hR, hRD, huniq⟩
  have hBR : B = R := huniq B hB (mem_lSubsetOrbitFinset.1 hDB)
  have hCR : C = R := huniq C hC (mem_lSubsetOrbitFinset.1 hDC)
  exact hBC (hBR.trans hCR.symm)

private theorem biUnion_lSubsetOrbitFinset_eq_nonemptySubsetsFinset
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {reps : Finset (Set G)}
    (hreps : IsRepresentativeSystemForNonemptySubsets A L reps) :
    reps.biUnion (lSubsetOrbitFinset L) = nonemptySubsetsFinset A := by
  classical
  ext C
  constructor
  · intro hC
    rw [Finset.mem_biUnion] at hC
    rcases hC with ⟨B, hB, hBC⟩
    exact lSubsetOrbitFinset_subset_nonemptySubsets
      (A := A) (L := L) (H := H) h (hreps.1 B hB) hBC
  · intro hC
    rw [mem_nonemptySubsetsFinset] at hC
    rcases hreps.2 C hC.1 hC.2 with ⟨B, hB, hCB, _huniq⟩
    rw [Finset.mem_biUnion]
    exact ⟨B, hB, mem_lSubsetOrbitFinset.2 hCB⟩

private theorem sum_lSubsetOrbitFinset_eq_sum_nonemptySubsetsFinset
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {reps : Finset (Set G)}
    (hreps : IsRepresentativeSystemForNonemptySubsets A L reps)
    (f : Set G → ℂ) :
    Finset.sum reps (fun B => Finset.sum (lSubsetOrbitFinset L B) f) =
      Finset.sum (nonemptySubsetsFinset A) f := by
  classical
  rw [← Finset.sum_biUnion
    (s := reps)
    (t := fun B : Set G => lSubsetOrbitFinset L B)
    (f := f)
    (by
      simpa using lSubsetOrbitFinset_pairwiseDisjoint
        (A := A) (L := L) (H := H) h hreps)]
  rw [biUnion_lSubsetOrbitFinset_eq_nonemptySubsetsFinset
    (A := A) (L := L) (H := H) h hreps]

private theorem exists_representative_system_for_lconjugate_elements
    {G : Type u} [Group G] [Finite G] (A : Set G) (L : Subgroup G) :
    ∃ reps : Finset G,
      (∀ a ∈ reps, a ∈ A) ∧
        ∀ a : G, a ∈ A →
          ∃ b ∈ reps, conjugateInSubgroup L a b ∧
            ∀ c ∈ reps, conjugateInSubgroup L a c → c = b := by
  classical
  let S : Type u := {a : G // a ∈ A}
  let rel : S → S → Prop := fun a b => conjugateInSubgroup L (a : G) (b : G)
  have hrel_refl : Std.Refl rel :=
    ⟨by
      intro a
      refine ⟨1, ?_⟩
      simp [conjBy]⟩
  have hrel_symm : Std.Symm rel :=
    ⟨by
      intro a b hab
      rcases hab with ⟨x, hx⟩
      refine ⟨x⁻¹, ?_⟩
      calc
        conjBy (x⁻¹ : G) b = conjBy (x⁻¹ : G) (conjBy (x : G) a) := by
          rw [hx]
        _ = a := by
          simp [conjBy, mul_assoc]⟩
  have hrel_trans : IsTrans S rel :=
    ⟨by
      intro a b c hab hbc
      rcases hab with ⟨x, hx⟩
      rcases hbc with ⟨y, hy⟩
      refine ⟨y * x, ?_⟩
      calc
        conjBy ((y * x : L) : G) a = conjBy (y : G) (conjBy (x : G) a) := by
          simp [conjBy, mul_assoc]
        _ = c := by
          rw [hx, hy]⟩
  let s : Setoid S :=
    { r := rel
      iseqv :=
        { refl := hrel_refl.refl
          symm := by
            intro a b h
            exact hrel_symm.symm a b h
          trans := by
            intro a b c hab hbc
            exact hrel_trans.trans a b c hab hbc } }
  let Q := Quotient s
  haveI : Finite Q := by
    refine Finite.of_surjective (Quotient.mk s) ?_
    intro q
    refine ⟨Quotient.out q, ?_⟩
    exact Quotient.out_eq q
  letI : Fintype Q := Fintype.ofFinite Q
  let reps : Finset G := (Finset.univ : Finset Q).image fun q =>
    ((Quotient.out q : S) : G)
  refine ⟨reps, ?_⟩
  constructor
  · intro a ha
    dsimp [reps] at ha
    rcases Finset.mem_image.mp ha with ⟨q, _hq, rfl⟩
    exact (Quotient.out q).2
  · intro a ha
    let a0 : S := ⟨a, ha⟩
    let q0 : Q := Quotient.mk s a0
    let b0 : S := Quotient.out q0
    refine ⟨b0.1, ?_, ?_, ?_⟩
    · dsimp [reps]
      exact Finset.mem_image.mpr ⟨q0, Finset.mem_univ q0, rfl⟩
    · have hq : Quotient.mk s b0 = q0 := by
          simp [b0, q0]
      exact hrel_symm.symm _ _ (Quotient.exact (s := s) hq)
    · intro c hc hconj
      rcases Finset.mem_image.mp hc with ⟨q, _hq, hc0⟩
      have hcA : c ∈ A := by
        simpa [hc0] using (Quotient.out q).2
      have hrelac : rel a0 ⟨c, hcA⟩ := by
        simpa [rel, S, a0] using hconj
      have hrelc : rel (Quotient.out q) a0 := by
        simpa [rel, S, a0, hc0] using (hrel_symm.symm _ _ hrelac)
      have hqeq : q = q0 := by
        have hmkq : Quotient.mk s (Quotient.out q) = q := Quotient.out_eq q
        have hmk0 : Quotient.mk s (Quotient.out q) = q0 := by
          simpa [q0, a0] using (Quotient.sound (s := s) hrelc)
        exact hmkq.symm.trans hmk0
      calc
        c = ((Quotient.out q : S) : G) := by
          simpa using hc0.symm
        _ = b0 := by
          simpa using congrArg (fun t : S => (t : G)) (congrArg Quotient.out hqeq)

private theorem dadeAveragingFunction_eq_of_lconj
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (hconj : conjugateInSubgroup L a b) :
    dadeAveragingFunction L H χ ⟨a, hAL a ha⟩ =
      dadeAveragingFunction L H χ ⟨b, hAL b hb⟩ := by
  rcases hconj with ⟨x, hx⟩
  have hH :
      H (conjBy (x : G) a) = conjugateSubgroup (x : G) (H a) := by
    simpa [hx] using (proposition_2_4 A L H).1 h ha x.2
  letI : Fintype (H a) := Fintype.ofFinite (H a)
  letI : Fintype (H (conjBy (x : G) a)) := Fintype.ofFinite (H (conjBy (x : G) a))
  let e : H a ≃ H (conjBy (x : G) a) := by
    refine
      { toFun := fun y => ⟨conjBy (x : G) (y : G), ?_⟩
        invFun := fun y => ⟨conjBy ((x : G)⁻¹) (y : G), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [hH]
      exact ⟨y, y.2, rfl⟩
    · have hyH : (y : G) ∈ conjugateSubgroup (x : G) (H a) := by
        simpa [hH] using y.2
      rcases hyH with ⟨z, hz, hyz⟩
      have hyz' : conjBy ((x : G)⁻¹) (y : G) = z := by
        calc
          conjBy ((x : G)⁻¹) (y : G) =
              conjBy ((x : G)⁻¹) (conjBy (x : G) z) := by
                rw [hyz]
          _ = z := by
            simp [conjBy, mul_assoc]
      simpa [hyz'] using hz
    · intro y
      ext
      simp [conjBy, mul_assoc]
    · intro y
      have hyH : (y : G) ∈ conjugateSubgroup (x : G) (H a) := by
        simpa [hH] using y.2
      rcases hyH with ⟨z, hz, hyz⟩
      ext
      calc
        conjBy (x : G) (conjBy ((x : G)⁻¹) (y : G)) =
            conjBy (x : G) (conjBy ((x : G)⁻¹) (conjBy (x : G) z)) := by
              rw [hyz]
        _ = conjBy (x : G) z := by
          simp [conjBy, mul_assoc]
        _ = y := by
          simp [hyz, conjBy, mul_assoc]
  have hsum :
      ∑ y : H (conjBy (x : G) a), χ ((conjBy (x : G) a) * (y : G)) =
        ∑ y : H a, χ (a * (y : G)) := by
    classical
    refine (Fintype.sum_equiv e (fun y : H a => χ (a * (y : G)))
      (fun y : H (conjBy (x : G) a) => χ ((conjBy (x : G) a) * (y : G))) ?_
      ).symm
    intro y
    change χ (a * (y : G)) = χ ((conjBy (x : G) a) * (conjBy (x : G) (y : G)))
    calc
      χ (a * (y : G)) = χ (conjBy (x : G) (a * (y : G))) := by
        exact (hχclass (x : G) (a * (y : G))).symm
      _ = χ ((conjBy (x : G) a) * (conjBy (x : G) (y : G))) := by
        simp [conjBy, mul_assoc]
  have hcardH :
      Nat.card (H (conjBy (x : G) a)) = Nat.card (H a) :=
    (Nat.card_congr e).symm
  have hxaA : conjBy (x : G) a ∈ A := by
    simpa [hx] using hb
  have hb_sub :
      (⟨b, hAL b hb⟩ : L) =
        ⟨conjBy (x : G) a, hAL (conjBy (x : G) a) hxaA⟩ := by
    ext
    exact hx.symm
  calc
    dadeAveragingFunction L H χ ⟨a, hAL a ha⟩ =
        (Nat.card (H a) : ℂ)⁻¹ *
          ∑ y : H a, χ (a * (y : G)) := rfl
    _ =
        (Nat.card (H (conjBy (x : G) a)) : ℂ)⁻¹ *
          ∑ y : H (conjBy (x : G) a),
            χ ((conjBy (x : G) a) * (y : G)) := by
          rw [hcardH, hsum]
    _ =
        dadeAveragingFunction L H χ
          ⟨conjBy (x : G) a, hAL (conjBy (x : G) a) hxaA⟩ := rfl
    _ = dadeAveragingFunction L H χ ⟨b, hAL b hb⟩ := by
          rw [← hb_sub]

public theorem dadeAveragingFunction_isClassFunction_on_A
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ)
    (a : L) (ha : (a : G) ∈ A) (x : L) :
    dadeAveragingFunction L H χ (x * a * x⁻¹) =
      dadeAveragingFunction L H χ a := by
  have hxa : ((x * a * x⁻¹ : L) : G) ∈ A := by
    exact (h.L_le_normalizer x.2 (a : G)).2 ha
  have hconj :
      conjugateInSubgroup L (a : G) ((x * a * x⁻¹ : L) : G) := by
    refine ⟨x, ?_⟩
    simp [conjBy]
  have h :=
    dadeAveragingFunction_eq_of_lconj
      A L H h hAL χ hχclass ha hxa hconj
  exact h.symm

private theorem normalizesSet_iff_conjugateImage_eq_self
    {G : Type u} [Group G] {S : Set G} {x : G} :
    normalizesSet S x ↔ conjugateImage S x = S := by
  constructor
  · intro hx
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hx s).2 hs
    · intro hg
      refine ⟨conjBy x⁻¹ g, ?_, ?_⟩
      · exact (normalizesSet_inv hx g).2 hg
      · simp [conjBy, mul_assoc]
  · intro hEq g
    constructor
    · intro hg
      have hmem : conjBy x g ∈ conjugateImage S x := by
        simpa [hEq] using hg
      rcases hmem with ⟨s, hs, hsx⟩
      have hsg : g = s := by
        simpa [conjBy, mul_assoc] using hsx
      simpa [hsg] using hs
    · intro hg
      have hmem : conjBy x g ∈ S := by
        have : conjBy x g ∈ conjugateImage S x := ⟨g, hg, rfl⟩
        simpa [hEq] using this
      exact hmem


private theorem conjAct_smul_set_eq_conjugateImage
    {G : Type u} [Group G] (S : Set G) (x : G) :
    ((ConjAct.toConjAct x) • S : Set G) = conjugateImage S x := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp [conjBy, ConjAct.toConjAct_smul]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp [conjBy, ConjAct.toConjAct_smul]⟩

private theorem mem_setNormalizer_iff_conjAct_smul_eq
    {G : Type u} [Group G] (S : Set G) (x : G) :
    x ∈ setNormalizer S ↔ ((ConjAct.toConjAct x) • S : Set G) = S := by
  rw [conjAct_smul_set_eq_conjugateImage]
  exact normalizesSet_iff_conjugateImage_eq_self

private noncomputable def conjActStabilizerEquivSetNormalizer
    {G : Type u} [Group G] (S : Set G) :
    MulAction.stabilizer (ConjAct G) S ≃ setNormalizer S where
  toFun x :=
    ⟨ConjAct.ofConjAct (x : ConjAct G), by
      have hx : ((x : ConjAct G) • S : Set G) = S := by
        exact (MulAction.mem_stabilizer_iff).1 x.2
      simpa using
        (mem_setNormalizer_iff_conjAct_smul_eq S (ConjAct.ofConjAct (x : ConjAct G))).2
          (by simpa using hx)⟩
  invFun x :=
    ⟨ConjAct.toConjAct (x : G), by
      exact (MulAction.mem_stabilizer_iff).2
        ((mem_setNormalizer_iff_conjAct_smul_eq S (x : G)).1 x.2)⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

private theorem natCard_conjAct_stabilizer_set
    {G : Type u} [Group G] (S : Set G) :
    Nat.card (MulAction.stabilizer (ConjAct G) S) = Nat.card (setNormalizer S) :=
  Nat.card_congr (conjActStabilizerEquivSetNormalizer S)

private theorem ncard_conjAct_orbit_mul_card_setNormalizer
    {G : Type u} [Group G] [Finite G] (S : Set G) :
    Nat.card (MulAction.orbit (ConjAct G) S) * Nat.card (setNormalizer S) =
      Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hsurj :
      Function.Surjective
        (fun x : ConjAct G =>
          (⟨x • S, by exact ⟨x, rfl⟩⟩ :
            MulAction.orbit (ConjAct G) S)) := by
    intro T
    rcases T.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext g
    simp [hx]
  haveI : Finite (MulAction.orbit (ConjAct G) S) :=
    Finite.of_surjective
      (fun x : ConjAct G =>
        (⟨x • S, by exact ⟨x, rfl⟩⟩ :
          MulAction.orbit (ConjAct G) S)) hsurj
  letI : Fintype (MulAction.orbit (ConjAct G) S) :=
    Fintype.ofFinite (MulAction.orbit (ConjAct G) S)
  have hcard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct G) S
  have hstab :
      Fintype.card (MulAction.stabilizer (ConjAct G) S) =
        Fintype.card (setNormalizer S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact natCard_conjAct_stabilizer_set S
  have hcard' :
      Fintype.card (MulAction.orbit (ConjAct G) S) *
          Fintype.card (MulAction.stabilizer (ConjAct G) S) =
        Fintype.card G := by
    rw [ConjAct.card] at hcard
    exact hcard
  rw [hstab] at hcard'
  simpa [Nat.card_eq_fintype_card] using hcard'


private theorem conjugateImage_sum_eq
    {G : Type u} [Group G] [Finite G]
    (S : Set G) (x : G) (χ : Section1.ClassFunction G)
    (hχ : Section1.IsClassFunction χ) :
    (letI : Fintype (conjugateImage S x) := Fintype.ofFinite (conjugateImage S x)
      ∑ g : (conjugateImage S x), χ (g : G)) =
      (letI : Fintype S := Fintype.ofFinite S
        ∑ g : S, χ (g : G)) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (conjugateImage S x) := Fintype.ofFinite (conjugateImage S x)
  let f : S → conjugateImage S x := fun s =>
    ⟨conjBy x (s : G), ⟨s, s.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s1 s2 h
      ext
      simpa [f, conjBy, mul_assoc] using congrArg Subtype.val h
    · intro t
      rcases t.2 with ⟨s, hs, ht⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using ht.symm
  let e : S ≃ conjugateImage S x := Equiv.ofBijective f hf
  refine (Fintype.sum_equiv e
    (fun s : S => χ (s : G))
    (fun t : conjugateImage S x => χ (t : G)) ?_).symm
  intro s
  change χ (s : G) = χ (conjBy x (s : G))
  exact (hχ x (s : G)).symm


private theorem sum_cosetProduct_eq_sum_subgroup
    {G : Type u} [Group G] [Finite G] {M : Type*} [AddCommMonoid M]
    (a : G) (K : Subgroup G) (f : G → M) :
    ∑ g : cosetProduct a K, f (g : G) =
      ∑ k : K, f (a * (k : G)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (cosetProduct a K) := Fintype.ofFinite (cosetProduct a K)
  let toCoset : K → cosetProduct a K := fun k =>
    ⟨a * (k : G), ⟨a, by simp, (k : G), k.2, rfl⟩⟩
  have hbij : Function.Bijective toCoset := by
    constructor
    · intro k₁ k₂ hk
      apply Subtype.ext
      have hkval : a * (k₁ : G) = a * (k₂ : G) := by
        simpa [toCoset] using congrArg Subtype.val hk
      simpa using congrArg (fun z : G => a⁻¹ * z) hkval
    · intro g
      rcases g.2 with ⟨s, hs, k, hk, hg⟩
      rw [Set.mem_singleton_iff] at hs
      subst s
      refine ⟨⟨k, hk⟩, ?_⟩
      exact Subtype.ext (by simpa [toCoset] using hg.symm)
  let e : K ≃ cosetProduct a K := Equiv.ofBijective toCoset hbij
  refine (Fintype.sum_equiv e
    (fun k : K => f (a * (k : G)))
    (fun g : cosetProduct a K => f (g : G)) ?_).symm
  intro k
  rfl

private theorem sum_toFinset_eq_subtype
    {G : Type u} [Finite G] {M : Type*} [AddCommMonoid M]
    (S : Set G) (f : G → M) :
    ∑ g ∈ S.toFinset, f g =
      (letI : Fintype S := Fintype.ofFinite S
        ∑ g : S, f (g : G)) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  simp [Set.toFinset]


private theorem conjugateImage_cosetProduct_eq_cosetProduct_conjugateSubgroup
    {G : Type u} [Group G] (a x : G) (K : Subgroup G) :
    conjugateImage (cosetProduct a K) x =
      cosetProduct (conjBy x a) (conjugateSubgroup x K) := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases hs with ⟨a₀, ha₀, k, hk, rfl⟩
    rw [Set.mem_singleton_iff] at ha₀
    subst a₀
    refine ⟨conjBy x a, by simp, conjBy x k, ⟨k, hk, rfl⟩, ?_⟩
    simp [conjBy, mul_assoc]
  · rintro ⟨b, hb, k, hk, hg⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    rcases hk with ⟨k₀, hk₀, hk_eq⟩
    subst k
    refine ⟨a * k₀, ⟨a, by simp, k₀, hk₀, rfl⟩, ?_⟩
    simpa [conjBy, mul_assoc] using hg

private theorem conjugateSet_conjugateImage_eq
    {G : Type u} [Group G] (S : Set G) (x : G) :
    conjugateSet (conjugateImage S x) = conjugateSet S := by
  ext g
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hsg⟩
    refine ⟨t, ht, ?_⟩
    have hst : conjugateIn t (conjBy x t) := ⟨x, by simp [conjBy, mul_assoc]⟩
    exact conjugateIn_trans hst hsg
  · rintro ⟨t, ht, htg⟩
    refine ⟨conjBy x t, ⟨t, ht, rfl⟩, ?_⟩
    have hst : conjugateIn (conjBy x t) t := ⟨x⁻¹, by simp [conjBy, mul_assoc]⟩
    exact conjugateIn_trans hst htg

private theorem conjugateSet_cosetProduct_eq_of_lconj
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a b : G}
    (ha : a ∈ A) (hconj : conjugateInSubgroup L a b) :
    conjugateSet (cosetProduct b (H b)) =
      conjugateSet (cosetProduct a (H a)) := by
  rcases hconj with ⟨x, hx⟩
  have hb : b = conjBy (x : G) a := hx.symm
  have hH :
      H b = conjugateSubgroup (x : G) (H a) := by
    simpa [hb] using (proposition_2_4 A L H).1 h ha x.2
  calc
    conjugateSet (cosetProduct b (H b)) =
        conjugateSet
          (cosetProduct (conjBy (x : G) a)
            (conjugateSubgroup (x : G) (H a))) := by
          rw [hb]
          rw [show H (conjBy (x : G) a) = conjugateSubgroup (x : G) (H a) by
            simpa [hb] using hH]
    _ = conjugateSet (conjugateImage (cosetProduct a (H a)) (x : G)) := by
          rw [conjugateImage_cosetProduct_eq_cosetProduct_conjugateSubgroup]
    _ = conjugateSet (cosetProduct a (H a)) := by
          exact conjugateSet_conjugateImage_eq (cosetProduct a (H a)) (x : G)

private theorem sum_conjugateSet_cosetProduct_eq_orbit
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A)
    (χ : Section1.ClassFunction G) (hχ : Section1.IsClassFunction χ) :
    ∑ g : conjugateSet (cosetProduct a (H a)), χ (g : G) =
      (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
        ∑ g : cosetProduct a (H a), χ (g : G) := by
  classical
  let S : Set G := cosetProduct a (H a)
  let pieceValue : MulAction.orbit (ConjAct G) S → ℂ := fun T =>
    (@Finset.univ (T : Set G) (Fintype.ofFinite (T : Set G))).sum
      (fun g => χ (g : G))
  let conjValue : G → ℂ := fun x =>
    (@Finset.univ (conjugateImage S x)
      (Fintype.ofFinite (conjugateImage S x))).sum
      (fun g => χ (g : G))
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (conjugateSet S) := Fintype.ofFinite (conjugateSet S)
  change (∑ g : conjugateSet S, χ (g : G)) =
      (Nat.card (MulAction.orbit (ConjAct G) S) : ℂ) *
        (∑ g : S, χ (g : G))
  have hsurj :
      Function.Surjective
        (fun x : ConjAct G =>
          (⟨x • S, by exact ⟨x, rfl⟩⟩ : MulAction.orbit (ConjAct G) S)) := by
    intro T
    rcases T.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext g
    simp [hx]
  haveI : Finite (MulAction.orbit (ConjAct G) S) :=
    Finite.of_surjective
      (fun x : ConjAct G =>
        (⟨x • S, by exact ⟨x, rfl⟩⟩ : MulAction.orbit (ConjAct G) S)) hsurj
  letI : Fintype (MulAction.orbit (ConjAct G) S) :=
    Fintype.ofFinite (MulAction.orbit (ConjAct G) S)
  let pieces : MulAction.orbit (ConjAct G) S → Finset G := fun T =>
    letI : Fintype (T : Set G) := Fintype.ofFinite (T : Set G)
    (T : Set G).toFinset
  have hpair :
      ((Finset.univ : Finset (MulAction.orbit (ConjAct G) S)) : Set _).PairwiseDisjoint
        pieces := by
    intro T1 hT1 T2 hT2 hne
    change Disjoint (pieces T1) (pieces T2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    apply hne
    apply Subtype.ext
    rcases T1.2 with ⟨x, hx⟩
    rcases T2.2 with ⟨y, hy⟩
    have hsmulx : x • S = conjugateImage S (ConjAct.ofConjAct x) := by
      simpa using (conjAct_smul_set_eq_conjugateImage S (ConjAct.ofConjAct x))
    have hsmuly : y • S = conjugateImage S (ConjAct.ofConjAct y) := by
      simpa using (conjAct_smul_set_eq_conjugateImage S (ConjAct.ofConjAct y))
    have hT1 : (T1 : Set G) = conjugateImage S (ConjAct.ofConjAct x) := by
      exact hx.symm.trans hsmulx
    have hT2 : (T2 : Set G) = conjugateImage S (ConjAct.ofConjAct y) := by
      exact hy.symm.trans hsmuly
    have hint :
        (conjugateImage S (ConjAct.ofConjAct x) ∩
          conjugateImage S (ConjAct.ofConjAct y)).Nonempty := by
      refine ⟨g, ?_, ?_⟩
      · have hg1' : g ∈ (T1 : Set G) := by
          simpa [pieces] using hg1
        simpa [hT1] using hg1'
      · have hg2' : g ∈ (T2 : Set G) := by
          simpa [pieces] using hg2
        simpa [hT2] using hg2'
    have heq :
        conjugateImage S (ConjAct.ofConjAct x) =
          conjugateImage S (ConjAct.ofConjAct y) :=
      conjugateImage_cosetProduct_eq_of_nonempty_inter (h := h) ha hint
    have hset : (T1 : Set G) = (T2 : Set G) := by
      calc
        (T1 : Set G) = conjugateImage S (ConjAct.ofConjAct x) := hT1
        _ = conjugateImage S (ConjAct.ofConjAct y) := heq
        _ = (T2 : Set G) := hT2.symm
    exact hset
  have hunion :
      (Finset.univ.biUnion pieces : Finset G) = (conjugateSet S).toFinset := by
    ext g
    constructor
    · intro hg
      rw [Finset.mem_biUnion] at hg
      rcases hg with ⟨T, hT, hgT⟩
      rcases T.2 with ⟨x, hx⟩
      have hsmul : x • S = conjugateImage S (ConjAct.ofConjAct x) := by
        simpa using (conjAct_smul_set_eq_conjugateImage S (ConjAct.ofConjAct x))
      have hTset : (T : Set G) = conjugateImage S (ConjAct.ofConjAct x) := by
        exact hx.symm.trans hsmul
      have hgT' : g ∈ (T : Set G) := by
        simpa [pieces] using hgT
      rw [hTset] at hgT'
      rcases hgT' with ⟨s, hs, rfl⟩
      refine (Set.mem_toFinset).2 ?_
      exact ⟨s, hs, ⟨ConjAct.ofConjAct x, rfl⟩⟩
    · intro hg
      rw [Set.mem_toFinset] at hg
      rcases hg with ⟨s, hs, hconj⟩
      rcases hconj with ⟨x, hx⟩
      let T : MulAction.orbit (ConjAct G) S :=
        ⟨conjugateImage S x, by
          refine ⟨ConjAct.toConjAct x, ?_⟩
          simp [conjAct_smul_set_eq_conjugateImage]⟩
      rw [Finset.mem_biUnion]
      refine ⟨T, by simp [T], ?_⟩
      have hmem : g ∈ (conjugateImage S x) := by
        exact ⟨s, hs, hx.symm⟩
      simpa [pieces, T] using (Set.mem_toFinset).2 hmem
  have hsum_union :
    ∑ g : (conjugateSet S), χ (g : G) =
        ∑ T : MulAction.orbit (ConjAct G) S, pieceValue T := by
    calc
      ∑ g : (conjugateSet S), χ (g : G) =
          ∑ g ∈ (conjugateSet S).toFinset, χ g := by
            exact (sum_toFinset_eq_subtype (S := conjugateSet S) (f := fun g : G => χ g)).symm
      _ = ∑ g ∈ Finset.univ.biUnion pieces, χ g := by
            rw [hunion]
      _ = ∑ T : MulAction.orbit (ConjAct G) S, ∑ g ∈ pieces T, χ g := by
            simpa [pieces] using (Finset.sum_biUnion hpair)
      _ = ∑ T : MulAction.orbit (ConjAct G) S, pieceValue T := by
            refine Finset.sum_congr rfl ?_
            intro T hT
            simpa [pieces, pieceValue] using
              (sum_toFinset_eq_subtype (S := (T : Set G)) (f := fun g : G => χ g))
  have hinner :
      ∀ T : MulAction.orbit (ConjAct G) S,
        pieceValue T =
          ∑ g : S, χ (g : G) := by
    intro T
    rcases T.2 with ⟨x, hx⟩
    have hsmul : x • S = conjugateImage S (ConjAct.ofConjAct x) := by
      simpa using (conjAct_smul_set_eq_conjugateImage S (ConjAct.ofConjAct x))
    have hT : (T : Set G) = conjugateImage S (ConjAct.ofConjAct x) := by
      exact hx.symm.trans hsmul
    have hpiece : pieceValue T = conjValue (ConjAct.ofConjAct x) := by
      unfold pieceValue conjValue
      rw [hT]
    calc
      pieceValue T = conjValue (ConjAct.ofConjAct x) := hpiece
      _ = ∑ g : S, χ (g : G) := by
            simpa using (conjugateImage_sum_eq S (ConjAct.ofConjAct x) χ hχ)
  have hcard_orbit :
      ∑ _T : MulAction.orbit (ConjAct G) S, (1 : ℂ) =
        (Nat.card (MulAction.orbit (ConjAct G) S) : ℂ) := by
    simp
  calc
    ∑ g : (conjugateSet S), χ (g : G) =
        ∑ T : MulAction.orbit (ConjAct G) S, pieceValue T := hsum_union
    _ = ∑ _T : MulAction.orbit (ConjAct G) S, ∑ g : S, χ (g : G) := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          exact hinner T
    _ = (Nat.card (MulAction.orbit (ConjAct G) S) : ℂ) *
        ∑ g : S, χ (g : G) := by
          simp

private theorem sum_orbit_conjAct_eq_card_mul
    {G : Type u} [Group G] [Finite G] (L : Subgroup G)
    (ψ : Section1.ClassFunction L) (hψ : Section1.IsClassFunction ψ)
    (a : L) :
    ∑ b : MulAction.orbit (ConjAct L) a, ψ (b : L) =
      (Nat.card (MulAction.orbit (ConjAct L) a) : ℂ) * ψ a := by
  classical
  letI : Fintype (MulAction.orbit (ConjAct L) a) :=
    Fintype.ofFinite (MulAction.orbit (ConjAct L) a)
  have hconst : ∀ b : MulAction.orbit (ConjAct L) a, ψ (b : L) = ψ a := by
    intro b
    rcases (MulAction.mem_orbit_iff.1 b.2) with ⟨x, hx⟩
    have hclass : ψ (x • a) = ψ a := by
      rw [ConjAct.smul_def]
      exact hψ (ConjAct.ofConjAct x) a
    calc
      ψ (b : L) = ψ (x • a) := by rw [hx]
      _ = ψ a := hclass
  calc
    ∑ b : MulAction.orbit (ConjAct L) a, ψ (b : L) =
        ∑ _b : MulAction.orbit (ConjAct L) a, ψ a := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          exact hconst b
    _ = (Nat.card (MulAction.orbit (ConjAct L) a) : ℂ) * ψ a := by
          simp

private theorem orbit_card_mul_card_centralizerIn
    {G : Type u} [Group G] [Finite G] (L : Subgroup G) (a : L) :
    Nat.card (MulAction.orbit (ConjAct L) a) * Nat.card (centralizerIn L (a : G)) =
      Nat.card L := by
  classical
  have hcard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct L) a
  have hstab :
      Fintype.card { x : ConjAct L // x • a = a } =
        Fintype.card (centralizerIn L (a : G)) := by
    let e : { x : ConjAct L // x • a = a } ≃ centralizerIn L (a : G) := by
      refine
        { toFun := ?_
          invFun := ?_
          left_inv := ?_
          right_inv := ?_ }
      · intro x
        refine ⟨(ConjAct.ofConjAct (x : ConjAct L) : L), ?_⟩
        refine Subgroup.mem_inf.mpr ⟨(ConjAct.ofConjAct (x : ConjAct L) : L).2, ?_⟩
        unfold elementCentralizer
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        have hxstab : (x : ConjAct L) • a = a := x.2
        have hxconjL :
            ConjAct.ofConjAct (x : ConjAct L) * a *
                (ConjAct.ofConjAct (x : ConjAct L))⁻¹ =
              a := by
          simpa [ConjAct.smul_def, conjBy] using hxstab
        have hxconj :
            ((ConjAct.ofConjAct (x : ConjAct L) : L) : G) *
                (a : G) *
                  ((ConjAct.ofConjAct (x : ConjAct L) : L) : G)⁻¹ =
              (a : G) := by
          simpa using congrArg (fun y : L => (y : G)) hxconjL
        have hxcomm :
            ((ConjAct.ofConjAct (x : ConjAct L) : L) : G) * (a : G) =
              (a : G) * ((ConjAct.ofConjAct (x : ConjAct L) : L) : G) := by
          have hmul := congrArg
            (fun y : G =>
              y * ((ConjAct.ofConjAct (x : ConjAct L) : L) : G)) hxconj
          simpa [mul_assoc] using hmul
        exact hxcomm.symm
      · intro y
        let yL : L := ⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩
        refine ⟨ConjAct.toConjAct yL, ?_⟩
        have hycent : (y : G) ∈ elementCentralizer (a : G) :=
          (Subgroup.mem_inf.mp y.2).2
        unfold elementCentralizer at hycent
        rw [Subgroup.mem_centralizer_iff] at hycent
        have hycomm : (a : G) * (y : G) = (y : G) * (a : G) :=
          hycent (a : G) (by simp)
        have hyconj : (y : G) * (a : G) * (y : G)⁻¹ = (a : G) := by
          calc
            (y : G) * (a : G) * (y : G)⁻¹ =
                (a : G) * (y : G) * (y : G)⁻¹ := by
                  rw [← hycomm, mul_assoc]
            _ = (a : G) := by simp [mul_assoc]
        ext
        simpa [yL, ConjAct.toConjAct_smul, conjBy] using hyconj
      · intro x
        ext
        rfl
      · intro y
        ext
        rfl
    exact Fintype.card_congr e
  simpa [Nat.card_eq_fintype_card, hstab] using
    hcard


private theorem sum_cosetProduct_star_eq_card_mul_star_dadeAveraging
    {G : Type u} [Group G] [Finite G] (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) (a : L) :
    ∑ g : cosetProduct (a : G) (H (a : G)), star (χ (g : G)) =
      (Nat.card (H (a : G)) : ℂ) *
        star (dadeAveragingFunction L H χ a) := by
  classical
  have hsum :=
    (sum_cosetProduct_eq_sum_subgroup
      (a := (a : G)) (K := H (a : G)) (f := fun g : G => star (χ g)))
  rw [hsum]
  have hcard_ne : (Nat.card (H (a : G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H (a : G))).ne'
  have hstaravg :
      star (dadeAveragingFunction L H χ a) =
        (Nat.card (H (a : G)) : ℂ)⁻¹ *
          ∑ x : H (a : G), star (χ ((a : G) * (x : G))) := by
    simp [dadeAveragingFunction]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp
    · intro x _hx
      rfl
  rw [hstaravg]
  field_simp [hcard_ne]
  refine Finset.sum_congr ?_ ?_
  · ext x
    simp
  · intro x _hx
    rfl

private theorem sum_conjugateSet_cosetProduct_star_eq_orbit_h_avg
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ)
    {a : G} (ha : a ∈ A) :
    ∑ g : conjugateSet (cosetProduct a (H a)), star (χ (g : G)) =
      (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
        (Nat.card (H a) : ℂ) *
          star (dadeAveragingFunction L H χ ⟨a, hAL a ha⟩) := by
  classical
  letI : Fintype (conjugateSet (cosetProduct a (H a))) :=
    Fintype.ofFinite (conjugateSet (cosetProduct a (H a)))
  letI : Fintype (cosetProduct a (H a)) :=
    Fintype.ofFinite (cosetProduct a (H a))
  let χstar : Section1.ClassFunction G := fun g => star (χ g)
  have hχstarclass : Section1.IsClassFunction χstar := by
    intro x g
    simpa [χstar] using congrArg star (hχclass x g)
  have hsum :=
    sum_conjugateSet_cosetProduct_eq_orbit
      (h := h) (ha := ha) χstar hχstarclass
  calc
    ∑ g : conjugateSet (cosetProduct a (H a)), star (χ (g : G)) =
        (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
          ∑ g : cosetProduct a (H a), star (χ (g : G)) := by
          simpa [χstar] using hsum
    _ = (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
          ((Nat.card (H a) : ℂ) *
            star (dadeAveragingFunction L H χ ⟨a, hAL a ha⟩)) := by
          exact congrArg
            (fun z : ℂ => (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) * z)
            (sum_cosetProduct_star_eq_card_mul_star_dadeAveraging
              (L := L) (H := H) χ ⟨a, hAL a ha⟩)
    _ = (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
        (Nat.card (H a) : ℂ) *
          star (dadeAveragingFunction L H χ ⟨a, hAL a ha⟩) := by
          ring

private theorem cosetProduct_orbit_card_mul_h_card_centralizerIn
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A) :
    Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) *
        Nat.card (H a) * Nat.card (centralizerIn L a) =
      Nat.card G := by
  have hcard :=
    ncard_conjAct_orbit_mul_card_setNormalizer (G := G) (cosetProduct a (H a))
  have hnorm := ((proposition_2_4 A L H).2.2 h) (a := a) ha
  have hcent := centralizer_card_eq_mul h ha
  rw [hnorm, hcent] at hcard
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcard

private theorem mem_conjugateSet_cosetProduct_iff
    {G : Type u} [Group G] (a : G) (K : Subgroup G) (g : G) :
    g ∈ conjugateSet (cosetProduct a K) ↔
      ∃ k ∈ K, conjugateIn (a * k) g := by
  constructor
  · rintro ⟨s, hs, hsg⟩
    rcases hs with ⟨a', ha', k, hk, rfl⟩
    rw [Set.mem_singleton_iff] at ha'
    subst a'
    exact ⟨k, hk, hsg⟩
  · rintro ⟨k, hk, hconj⟩
    exact ⟨a * k, ⟨a, by simp, k, hk, rfl⟩, hconj⟩

private theorem conjugateSet_cosetProduct_subset_dadeSupport
    {G : Type u} [Group G] {A : Set G} {H : G → Subgroup G}
    {a : G} (ha : a ∈ A) :
    conjugateSet (cosetProduct a (H a)) ⊆ dadeSupport A H := by
  intro g hg
  rcases (mem_conjugateSet_cosetProduct_iff a (H a) g).1 hg with
    ⟨k, hk, hconj⟩
  exact ⟨a, ha, k, hk, conjugateIn_symm hconj⟩

public theorem dadeSupport_piece_mem_conjugateSet
    {G : Type u} [Group G] {H : G → Subgroup G}
    {g a k : G} (hk : k ∈ H a)
    (hconj : conjugateIn g (a * k)) :
    g ∈ conjugateSet (cosetProduct a (H a)) := by
  rw [mem_conjugateSet_cosetProduct_iff]
  exact ⟨k, hk, conjugateIn_symm hconj⟩

private theorem setConjugateBy_eq_conjugateImage
    {G : Type u} [Group G] (x : G) (B : Set G) :
    setConjugateBy x B = conjugateImage B x := by
  ext g
  constructor <;> intro hg
  · rcases hg with ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rcases hg with ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

private theorem setConjugateBy_card_eq
    {G : Type u} [Group G] [Finite G] (x : G) (B : Set G) :
    Nat.card (setConjugateBy x B) = Nat.card B := by
  classical
  let f : B → setConjugateBy x B := fun b =>
    ⟨conjBy x (b : G), ⟨b, b.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro b1 b2 h
    apply Subtype.ext
    simpa [f, conjBy, mul_assoc] using congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro g
    rcases g.2 with ⟨b, hb, hg⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    exact hg.symm
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

private theorem HInter_setConjugateBy_eq_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A) (x : L) :
    HInter H (setConjugateBy (x : G) B) =
      conjugateSubgroup (x : G) (HInter H B) := by
  ext g
  constructor
  · intro hg
    refine ⟨conjBy (x : G)⁻¹ g, ?_, ?_⟩
    · change conjBy (x : G)⁻¹ g ∈ ⨅ b : B, H (b : G)
      rw [Subgroup.mem_iInf]
      intro b
      have hgb : g ∈ H (conjBy (x : G) (b : G)) := by
        exact hInter_le_of_mem H
          (B := setConjugateBy (x : G) B)
          (by exact ⟨b, b.2, rfl⟩) hg
      have hHb :
          H (conjBy (x : G) (b : G)) =
            conjugateSubgroup (x : G) (H (b : G)) := by
        simpa using (proposition_2_4 A L H).1 h (hBA b.2) x.2
      have : g ∈ conjugateSubgroup (x : G) (H (b : G)) := by
        simpa [hHb] using hgb
      rcases this with ⟨h₀, hh₀, hg_eq⟩
      have hg_eq' : conjBy (x : G)⁻¹ g = h₀ := by
        rw [hg_eq]
        simp [conjBy, mul_assoc]
      simpa [hg_eq'] using hh₀
    · simp [conjBy, mul_assoc]
  · intro hg
    rcases hg with ⟨h₀, hh₀, rfl⟩
    change conjBy (x : G) h₀ ∈ ⨅ b : setConjugateBy (x : G) B, H (b : G)
    rw [Subgroup.mem_iInf]
    intro b
    rcases b.2 with ⟨c, hc, hb_eq⟩
    have hh₀c : h₀ ∈ H c := hInter_le_of_mem H hc hh₀
    have hh₀' : conjBy (x : G) h₀ ∈ H (conjBy (x : G) c) := by
      have hHb :
          H (conjBy (x : G) c) =
            conjugateSubgroup (x : G) (H c) := by
        simpa using (proposition_2_4 A L H).1 h (hBA hc) x.2
      exact by
        rw [hHb]
        exact ⟨h₀, hh₀c, rfl⟩
    simpa [hb_eq] using hh₀'

private theorem normalizesSet_setConjugateBy_iff
    {G : Type u} [Group G] (B : Set G) (x y : G) :
    normalizesSet (setConjugateBy x B) y ↔
      normalizesSet B (x⁻¹ * y * x) := by
  constructor
  · intro hy b
    constructor
    · intro hb
      have hconj_mem :
          conjBy y (conjBy x b) ∈ setConjugateBy x B := by
        refine ⟨conjBy (x⁻¹ * y * x) b, hb, ?_⟩
        simp [conjBy, mul_assoc]
      have hxb_mem : conjBy x b ∈ setConjugateBy x B :=
        (hy (conjBy x b)).1 hconj_mem
      rcases hxb_mem with ⟨c, hc, hc_eq⟩
      have hb_eq_c : b = c := by
        have := congrArg (fun t : G => conjBy x⁻¹ t) hc_eq
        simpa [conjBy, mul_assoc] using this
      simpa [hb_eq_c] using hc
    · intro hb
      have hxb_mem : conjBy x b ∈ setConjugateBy x B := ⟨b, hb, rfl⟩
      have hconj_mem : conjBy y (conjBy x b) ∈ setConjugateBy x B :=
        (hy (conjBy x b)).2 hxb_mem
      rcases hconj_mem with ⟨c, hc, hc_eq⟩
      have hzc : conjBy (x⁻¹ * y * x) b = c := by
        have := congrArg (fun t : G => conjBy x⁻¹ t) hc_eq
        simpa [conjBy, mul_assoc] using this
      simpa [hzc] using hc
  · intro hz t
    constructor
    · intro ht
      rcases ht with ⟨b, hb, ht_eq⟩
      let z := x⁻¹ * y * x
      have hcz : conjBy z⁻¹ b ∈ B := by
        exact ((normalizesSet_inv hz) b).2 hb
      refine ⟨conjBy z⁻¹ b, hcz, ?_⟩
      have ht_eq' := congrArg (fun u : G => conjBy y⁻¹ u) ht_eq
      simpa [z, conjBy, mul_assoc] using ht_eq'
    · intro ht
      rcases ht with ⟨b, hb, rfl⟩
      have hzb : conjBy (x⁻¹ * y * x) b ∈ B := (hz b).2 hb
      refine ⟨conjBy (x⁻¹ * y * x) b, hzb, ?_⟩
      simp [conjBy, mul_assoc]

private theorem normalizerIn_setConjugateBy_eq_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {B : Set G} (x : L) :
    normalizerIn L (setConjugateBy (x : G) B) =
      conjugateSubgroup (x : G) (normalizerIn L B) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_inf.mp hy with ⟨hyL, hyN⟩
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact L.mul_mem (L.mul_mem (L.inv_mem x.2) hyL) x.2
      · exact (normalizesSet_setConjugateBy_iff (B := B) (x := x) (y := y)).1 hyN
    · simp [conjBy, mul_assoc]
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem x.2 hz.1) (L.inv_mem x.2)
    · exact (normalizesSet_setConjugateBy_iff (B := B) (x := x)
        (y := conjBy (x : G) z)).2 (by
          simpa [setNormalizer, conjBy, mul_assoc] using hz.2)

private theorem rightTranslateSet_conjugateSubgroup_eq_conjugateImage
    {G : Type u} [Group G] (x b : G) (K : Subgroup G) :
    rightTranslateSet ((conjugateSubgroup x K : Subgroup G) : Set G)
        (conjBy x b) =
      conjugateImage (rightTranslateSet (K : Set G) b) x := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    rcases hh with ⟨k, hk, rfl⟩
    refine ⟨k * b, ?_, ?_⟩
    · exact ⟨k, hk, rfl⟩
    · simp [conjBy, mul_assoc]
  · rintro ⟨s, hs, rfl⟩
    rcases hs with ⟨k, hk, rfl⟩
    refine ⟨conjBy x k, ?_, ?_⟩
    · exact ⟨k, hk, rfl⟩
    · simp [conjBy, mul_assoc]

private theorem transporterSet_conjugateImage_card_eq
    {G : Type u} [Group G] (g x : G) (X : Set G) :
    Nat.card (transporterSet g (conjugateImage X x)) =
      Nat.card (transporterSet g X) := by
  classical
  let e : transporterSet g (conjugateImage X x) ≃ transporterSet g X := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro y
      refine ⟨(y : G) * x, ?_⟩
      rw [mem_transporterSet_iff]
      have hy :
          (y : G)⁻¹ * g * (y : G) ∈ conjugateImage X x :=
        (mem_transporterSet_iff (g := g) (X := conjugateImage X x)
          (x := (y : G))).1 y.2
      rcases hy with ⟨z, hz, hyz⟩
      have hcalc :
        ((y : G) * x)⁻¹ * g * ((y : G) * x) =
          z := by
        have h1 : x⁻¹ * conjBy x z * x = z := by
          simp [conjBy, mul_assoc]
        calc
          ((y : G) * x)⁻¹ * g * ((y : G) * x) =
              x⁻¹ * ((y : G)⁻¹ * g * (y : G)) * x := by
                simp [mul_assoc]
          _ = x⁻¹ * conjBy x z * x := by rw [hyz]
          _ = z := h1
      rw [hcalc]
      exact hz
    · intro y
      refine ⟨(y : G) * x⁻¹, ?_⟩
      rw [mem_transporterSet_iff]
      have hy :
          (y : G)⁻¹ * g * (y : G) ∈ X :=
        (mem_transporterSet_iff (g := g) (X := X) (x := (y : G))).1 y.2
      refine ⟨(y : G)⁻¹ * g * (y : G), hy, ?_⟩
      simp [conjBy, mul_assoc]
    · intro y
      ext
      change ((y : G) * x) * x⁻¹ = y
      simp [mul_assoc]
    · intro y
      ext
      change ((y : G) * x⁻¹) * x = y
      simp [mul_assoc]
  exact Nat.card_congr e

private theorem transporterSet_rightTranslate_setConjugateBy_card_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A)
    (x : L) (g b : G) :
    Nat.card (transporterSet g
        (rightTranslateSet
          (HInter H (setConjugateBy (x : G) B) : Set G)
          (conjBy (x : G) b))) =
      Nat.card (transporterSet g
        (rightTranslateSet (HInter H B : Set G) b)) := by
  rw [HInter_setConjugateBy_eq_conjugateSubgroup
    (A := A) (L := L) (H := H) h hBA x]
  rw [rightTranslateSet_conjugateSubgroup_eq_conjugateImage]
  exact transporterSet_conjugateImage_card_eq g (x : G)
    (rightTranslateSet (HInter H B : Set G) b)

private theorem MOfSet_setConjugateBy_eq_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A) (x : L) :
    MOfSet H L (setConjugateBy (x : G) B) =
      conjugateSubgroup (x : G) (MOfSet H L B) := by
  have hH :
      conjugateSubgroup (x : G) (HInter H B) =
        (HInter H B).map (MulAut.conj (x : G)).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_map.mpr ⟨z, hz, by simp [conjBy, MulAut.conj_apply]⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [conjBy, MulAut.conj_apply]⟩
  have hN :
      conjugateSubgroup (x : G) (normalizerIn L B) =
        (normalizerIn L B).map (MulAut.conj (x : G)).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_map.mpr ⟨z, hz, by simp [conjBy, MulAut.conj_apply]⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [conjBy, MulAut.conj_apply]⟩
  calc
    MOfSet H L (setConjugateBy (x : G) B)
        = HInter H (setConjugateBy (x : G) B) ⊔
            normalizerIn L (setConjugateBy (x : G) B) := rfl
    _ = conjugateSubgroup (x : G) (HInter H B) ⊔
        conjugateSubgroup (x : G) (normalizerIn L B) := by
          rw [HInter_setConjugateBy_eq_conjugateSubgroup
            (A := A) (L := L) (H := H) h hBA x,
            normalizerIn_setConjugateBy_eq_conjugateSubgroup
              (L := L) x]
    _ = conjugateSubgroup (x : G) (HInter H B ⊔ normalizerIn L B) := by
          have hJoin :
              conjugateSubgroup (x : G) (HInter H B ⊔ normalizerIn L B) =
                (HInter H B ⊔ normalizerIn L B).map
                  (MulAut.conj (x : G)).toMonoidHom := by
            ext y
            constructor
            · rintro ⟨z, hz, rfl⟩
              exact Subgroup.mem_map.mpr ⟨z, hz, by simp [conjBy, MulAut.conj_apply]⟩
            · rintro ⟨z, hz, rfl⟩
              exact ⟨z, hz, by simp [conjBy, MulAut.conj_apply]⟩
          rw [hH, hN]
          rw [← Subgroup.map_sup]
          simpa using hJoin.symm
    _ = conjugateSubgroup (x : G) (MOfSet H L B) := by
          simp [MOfSet]

private theorem conjugateInSubgroup_conjBy_iff
    {G : Type u} [Group G] {L : Subgroup G} (x : L) {a b : G} :
    conjugateInSubgroup L a b ↔
      conjugateInSubgroup L (conjBy (x : G) a) (conjBy (x : G) b) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨x * y * x⁻¹, ?_⟩
    calc
      conjBy (((x * y * x⁻¹ : L) : G)) (conjBy (x : G) a) =
          conjBy (x : G) (conjBy (y : G) a) := by
            simp [conjBy, mul_assoc]
      _ = conjBy (x : G) b := by rw [hy]
  · rintro ⟨y, hy⟩
    refine ⟨x⁻¹ * y * x, ?_⟩
    calc
      conjBy (((x⁻¹ * y * x : L) : G)) a =
          conjBy (x : G)⁻¹ (conjBy (y : G) (conjBy (x : G) a)) := by
            simp [conjBy, mul_assoc]
      _ = b := by
            rw [hy]
            simp [conjBy, mul_assoc]

private theorem conjugateSubgroup_card_eq
    {G : Type u} [Group G] [Finite G] (x : G) (K : Subgroup G) :
    Nat.card (conjugateSubgroup x K) = Nat.card K := by
  classical
  let f : K → conjugateSubgroup x K := fun k =>
    ⟨conjBy x (k : G), ⟨k, k.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro k1 k2 hk
    have hval : conjBy (x : G) (k1 : G) = conjBy (x : G) (k2 : G) := by
      simpa [f] using congrArg Subtype.val hk
    have hval' := congrArg (fun t : G => conjBy (x : G)⁻¹ t) hval
    simpa [conjBy, mul_assoc] using hval'
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y.2 with ⟨k, hk, hy⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    simpa [f] using hy.symm
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

private theorem MOfSet_setConjugateBy_card_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A) (x : L) :
    Nat.card (MOfSet H L (setConjugateBy (x : G) B)) =
      Nat.card (MOfSet H L B) := by
  rw [MOfSet_setConjugateBy_eq_conjugateSubgroup
    (A := A) (L := L) (H := H) h hBA x]
  exact conjugateSubgroup_card_eq (x : G) (MOfSet H L B)

private theorem dadeInductionFormulaTerm_setConjugateBy_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {α : Section1.ClassFunction L} (hα : CFOn L A α)
    {g a : G} (ha : a ∈ A) {B : Set G} (hBA : B ⊆ A)
    (x : L) :
    dadeInductionFormulaTerm A L H α g (conjBy (x : G) a)
        (setConjugateBy (x : G) B) hAL
        (by exact (h.L_le_normalizer x.2 a).2 ha) =
      dadeInductionFormulaTerm A L H α g a B hAL ha := by
  classical
  have hAconj : conjBy (x : G) a ∈ A := (h.L_le_normalizer x.2 a).2 ha
  let idx : Type u :=
    {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b}
  let idxc : Type u :=
    {b : G // b ∈ normalizerIn L (setConjugateBy (x : G) B) ∧
      conjugateInSubgroup L (conjBy (x : G) a) b}
  let f : idx → idxc := by
    intro b
    refine ⟨conjBy (x : G) (b : G), ?_, ?_⟩
    · rw [normalizerIn_setConjugateBy_eq_conjugateSubgroup
        (L := L) x]
      exact ⟨(b : G), b.2.1, rfl⟩
    · exact (conjugateInSubgroup_conjBy_iff x).1 b.2.2
  have hf : Function.Bijective f := by
    constructor
    · intro b1 b2 hfb
      apply Subtype.ext
      have hval :
          conjBy (x : G) (b1 : G) = conjBy (x : G) (b2 : G) := by
        simpa [f] using congrArg Subtype.val hfb
      have hval' := congrArg (fun t : G => conjBy (x : G)⁻¹ t) hval
      simpa [conjBy, mul_assoc] using hval'
    · intro c
      have hcN :
          (c : G) ∈ conjugateSubgroup (x : G) (normalizerIn L B) := by
        simpa [normalizerIn_setConjugateBy_eq_conjugateSubgroup
          (L := L)   x] using c.2.1
      rcases hcN with ⟨z, hz, hcz⟩
      refine ⟨⟨z, hz, ?_⟩, ?_⟩
      · have hcconj :
            conjugateInSubgroup L (conjBy (x : G) a) (conjBy (x : G) z) := by
          simpa [hcz] using c.2.2
        exact (conjugateInSubgroup_conjBy_iff x).2 hcconj
      · apply Subtype.ext
        simpa [f] using hcz.symm
  letI : Fintype idx := Fintype.ofFinite idx
  letI : Fintype idxc := Fintype.ofFinite idxc
  have hsum_idx :
      ∑ b : idxc,
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (HInter H (setConjugateBy (x : G) B) : Set G) (b : G))) : ℂ) =
      ∑ b : idx,
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
    have hsum' :
        ∑ b : idx,
            (Nat.card
              (transporterSet g
                (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) =
        ∑ b : idxc,
            (Nat.card
              (transporterSet g
                (rightTranslateSet
                  (HInter H (setConjugateBy (x : G) B) : Set G) (b : G))) : ℂ) := by
      refine Fintype.sum_equiv (Equiv.ofBijective f hf)
        (fun b : idx =>
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ))
        (fun b : idxc =>
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (HInter H (setConjugateBy (x : G) B) : Set G) (b : G))) : ℂ)) ?_
      intro b
      change
        (Nat.card
          (transporterSet g
            (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) =
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (HInter H (setConjugateBy (x : G) B) : Set G)
                (conjBy (x : G) (b : G)))) : ℂ)
      exact (congrArg (fun n : ℕ => (n : ℂ))
        (transporterSet_rightTranslate_setConjugateBy_card_eq
          (A := A) (L := L) (H := H) h hBA x g (b : G))).symm
    exact hsum'.symm
  have hαa :
      α ⟨conjBy (x : G) a, hAL _ hAconj⟩ =
        α ⟨a, hAL a ha⟩ := by
    exact classFunction_eq_of_conjugateInSubgroup α hα.1
      (hAL a ha) (hAL _ hAconj) ⟨x, rfl⟩
  unfold dadeInductionFormulaTerm
  rw [MOfSet_setConjugateBy_card_eq (A := A) (L := L) (H := H) h hBA x,
    hsum_idx]
  rw [hαa]

private theorem dadeInductionFormulaTerm_lconj_left_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (hAL : ∀ a ∈ A, a ∈ L)
    {α : Section1.ClassFunction L} (hα : CFOn L A α)
    {g a c : G} (ha : a ∈ A) (hc : c ∈ A)
    (hac : conjugateInSubgroup L a c) (B : Set G) :
    dadeInductionFormulaTerm A L H α g c B hAL hc =
      dadeInductionFormulaTerm A L H α g a B hAL ha := by
  classical
  let idxa : Type u :=
    {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b}
  let idxc : Type u :=
    {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L c b}
  let f : idxa → idxc := fun b =>
    ⟨(b : G), b.2.1, conjugateInSubgroup_trans
      (conjugateInSubgroup_symm hac) b.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b₁ b₂ hb
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hb
    · intro b
      refine ⟨⟨(b : G), b.2.1,
        conjugateInSubgroup_trans hac b.2.2⟩, ?_⟩
      apply Subtype.ext
      rfl
  letI : Fintype idxa := Fintype.ofFinite idxa
  letI : Fintype idxc := Fintype.ofFinite idxc
  have hsum :
      ∑ b : idxc,
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) =
      ∑ b : idxa,
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
    have hsum' :
        ∑ b : idxa,
            (Nat.card
              (transporterSet g
                (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) =
        ∑ b : idxc,
            (Nat.card
              (transporterSet g
                (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
      refine Fintype.sum_equiv (Equiv.ofBijective f hf)
        (fun b : idxa =>
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ))
        (fun b : idxc =>
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ)) ?_
      intro b
      rfl
    exact hsum'.symm
  have hαc :
      α ⟨c, hAL c hc⟩ = α ⟨a, hAL a ha⟩ := by
    exact classFunction_eq_of_conjugateInSubgroup α hα.1
      (hAL a ha) (hAL c hc) hac
  unfold dadeInductionFormulaTerm
  rw [hsum, hαc]


private theorem dadeInductionFormulaTerm_lconj_set_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {α : Section1.ClassFunction L} (hα : CFOn L A α)
    {g a : G} (ha : a ∈ A) {B C : Set G} (hBA : B ⊆ A)
    (hBC : LConjugateSubsets L B C) :
    dadeInductionFormulaTerm A L H α g a C hAL ha =
      dadeInductionFormulaTerm A L H α g a B hAL ha := by
  classical
  rcases hBC with ⟨x, rfl⟩
  have hxa : conjBy (x : G) a ∈ A :=
    (h.L_le_normalizer x.2 a).2 ha
  have hconj : conjugateInSubgroup L a (conjBy (x : G) a) := ⟨x, rfl⟩
  calc
    dadeInductionFormulaTerm A L H α g a
        (setConjugateBy (x : G) B) hAL ha =
        dadeInductionFormulaTerm A L H α g (conjBy (x : G) a)
          (setConjugateBy (x : G) B) hAL hxa := by
          exact (dadeInductionFormulaTerm_lconj_left_eq hAL hα
            ha hxa hconj (setConjugateBy (x : G) B)).symm
    _ = dadeInductionFormulaTerm A L H α g a B hAL ha := by
          exact dadeInductionFormulaTerm_setConjugateBy_eq
            (A := A) (L := L) (H := H) h hAL hα ha hBA x


private theorem signedDadeInductionFormulaTerm_lconj_set_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {α : Section1.ClassFunction L} (hα : CFOn L A α)
    {g a : G} (ha : a ∈ A) {B C : Set G} (hBA : B ⊆ A)
    (hBC : LConjugateSubsets L B C) :
    ((-1 : ℂ) ^ Nat.card C) *
        dadeInductionFormulaTerm A L H α g a C hAL ha =
      ((-1 : ℂ) ^ Nat.card B) *
        dadeInductionFormulaTerm A L H α g a B hAL ha := by
  classical
  rcases hBC with ⟨x, rfl⟩
  rw [setConjugateBy_card_eq]
  rw [dadeInductionFormulaTerm_lconj_set_eq
    (A := A) (L := L) (H := H) h hAL hα ha hBA
    (by exact ⟨x, rfl⟩)]

private theorem normalizerIn_card_eq_of_lconj_set
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {B C : Set G}
    (hBC : LConjugateSubsets L B C) :
    Nat.card (normalizerIn L C) = Nat.card (normalizerIn L B) := by
  rcases hBC with ⟨x, rfl⟩
  rw [normalizerIn_setConjugateBy_eq_conjugateSubgroup
    (L := L) x]
  exact conjugateSubgroup_card_eq (x : G) (normalizerIn L B)

private theorem setConjugateBy_nonemptySubsetsFinset_mem
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B ∈ nonemptySubsetsFinset A) (x : L) :
    setConjugateBy (x : G) B ∈ nonemptySubsetsFinset A := by
  rw [mem_nonemptySubsetsFinset] at hB ⊢
  constructor
  · rcases hB.1 with ⟨b, hb⟩
    exact ⟨conjBy (x : G) b, ⟨b, hb, rfl⟩⟩
  · intro c hc
    rcases hc with ⟨b, hb, rfl⟩
    exact (h.L_le_normalizer x.2 b).2 (hB.2 hb)

private theorem setConjugateBy_inv_setConjugateBy
    {G : Type u} [Group G] (x : G) (B : Set G) :
    setConjugateBy x⁻¹ (setConjugateBy x B) = B := by
  ext z
  constructor
  · rintro ⟨y, ⟨b, hb, rfl⟩, rfl⟩
    simpa [conjBy, mul_assoc] using hb
  · intro hz
    refine ⟨conjBy x z, ⟨z, hz, rfl⟩, ?_⟩
    simp [conjBy, mul_assoc]

private theorem setConjugateBy_setConjugateBy_inv
    {G : Type u} [Group G] (x : G) (B : Set G) :
    setConjugateBy x (setConjugateBy x⁻¹ B) = B := by
  simpa using setConjugateBy_inv_setConjugateBy (x := x⁻¹) (B := B)

private theorem sum_nonemptySubsetsFinset_setConjugateBy
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (x : L) (f : Set G → ℂ) :
    (∑ B ∈ nonemptySubsetsFinset A,
      f (setConjugateBy (x : G) B)) =
        ∑ B ∈ nonemptySubsetsFinset A, f B := by
  classical
  let s : Finset (Set G) := nonemptySubsetsFinset A
  refine Finset.sum_bij
    (s := s) (t := s)
    (f := fun B => f (setConjugateBy (x : G) B))
    (g := f)
    (fun B hB => setConjugateBy (x : G) B) ?_ ?_ ?_ ?_
  · intro B hB
    exact setConjugateBy_nonemptySubsetsFinset_mem
      (A := A) (L := L) (H := H) h hB x
  · intro B₁ _hB₁ B₂ _hB₂ hEq
    calc
      B₁ = setConjugateBy (x : G)⁻¹ (setConjugateBy (x : G) B₁) := by
        rw [setConjugateBy_inv_setConjugateBy]
      _ = setConjugateBy (x : G)⁻¹ (setConjugateBy (x : G) B₂) := by
        simpa using congrArg (setConjugateBy (x : G)⁻¹) hEq
      _ = B₂ := by
        rw [setConjugateBy_inv_setConjugateBy]
  · intro C hC
    let xinv : L := ⟨((x : G)⁻¹), L.inv_mem x.2⟩
    refine ⟨setConjugateBy (x : G)⁻¹ C, ?_, ?_⟩
    · exact setConjugateBy_nonemptySubsetsFinset_mem
        (A := A) (L := L) (H := H) h hC xinv
    · exact setConjugateBy_setConjugateBy_inv (x := (x : G)) (B := C)
  · intro B _hB
    rfl

private theorem normalizerIn_setConjugateBy_mem_iff
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {B : Set G} (x : L) (b : G) :
    conjBy (x : G) b ∈ normalizerIn L (setConjugateBy (x : G) B) ↔
      b ∈ normalizerIn L B := by
  rw [normalizerIn_setConjugateBy_eq_conjugateSubgroup (L := L) x]
  constructor
  · intro hmem
    rcases hmem with ⟨z, hz, hz_eq⟩
    have hbz : b = z := by
      have := congrArg (fun t : G => conjBy (x : G)⁻¹ t) hz_eq
      simpa [conjBy, mul_assoc] using this
    simpa [hbz] using hz
  · intro hb
    exact ⟨b, hb, rfl⟩

private theorem transporterContribution_setConjugateBy_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G} (hBA : B ⊆ A)
    (x : L) (g b : G) :
    ((-1 : ℂ) ^ Nat.card (setConjugateBy (x : G) B)) *
        (Nat.card (HInter H (setConjugateBy (x : G) B)) : ℂ)⁻¹ *
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (HInter H (setConjugateBy (x : G) B) : Set G)
                (conjBy (x : G) b))) : ℂ) =
      ((-1 : ℂ) ^ Nat.card B) *
        (Nat.card (HInter H B) : ℂ)⁻¹ *
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) b)) : ℂ) := by
  have hBcard :
      Nat.card (setConjugateBy (x : G) B) = Nat.card B :=
    setConjugateBy_card_eq (x : G) B
  have hHcard :
      Nat.card (HInter H (setConjugateBy (x : G) B)) =
        Nat.card (HInter H B) := by
    rw [HInter_setConjugateBy_eq_conjugateSubgroup
      (A := A) (L := L) (H := H) h hBA x]
    exact conjugateSubgroup_card_eq (x : G) (HInter H B)
  have hTcard :
      Nat.card
          (transporterSet g
            (rightTranslateSet
              (HInter H (setConjugateBy (x : G) B) : Set G)
              (conjBy (x : G) b))) =
        Nat.card
          (transporterSet g
            (rightTranslateSet (HInter H B : Set G) b)) :=
    transporterSet_rightTranslate_setConjugateBy_card_eq
      (A := A) (L := L) (H := H) h hBA x g b
  rw [hBcard, hHcard, hTcard]

private theorem conjugateInSubgroup_mem_L
    {G : Type u} [Group G] {L : Subgroup G} {a b : G}
    (haL : a ∈ L) (hab : conjugateInSubgroup L a b) :
    b ∈ L := by
  rcases hab with ⟨x, rfl⟩
  exact L.mul_mem (L.mul_mem x.2 haL) (L.inv_mem x.2)

private noncomputable def conjugateInSubgroupEquivOrbit
    {G : Type u} [Group G] {L : Subgroup G} (aL : L) :
    {b : G // conjugateInSubgroup L (aL : G) b} ≃
      MulAction.orbit (ConjAct L) aL := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    let bL : L := ⟨(b : G), conjugateInSubgroup_mem_L aL.2 b.2⟩
    refine ⟨bL, ?_⟩
    rcases b.2 with ⟨x, hx⟩
    refine MulAction.mem_orbit_iff.2 ⟨ConjAct.toConjAct x, ?_⟩
    apply Subtype.ext
    simpa [bL, ConjAct.toConjAct_smul, conjBy] using hx
  · intro b
    refine ⟨((b : L) : G), ?_⟩
    rcases (MulAction.mem_orbit_iff.1 b.2) with ⟨x, hx⟩
    refine ⟨ConjAct.ofConjAct x, ?_⟩
    have hx' := congrArg (fun y : L => (y : G)) hx
    simpa [ConjAct.smul_def, conjBy, mul_assoc] using hx'
  · intro b
    apply Subtype.ext
    rfl
  · intro b
    apply Subtype.ext
    rfl

private noncomputable def normalizerConjugateEquivOrbitNormalizer
    {G : Type u} [Group G] {L : Subgroup G} (aL : L) (B : Set G) :
    {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (aL : G) b} ≃
      {b : MulAction.orbit (ConjAct L) aL //
        ((b : L) : G) ∈ normalizerIn L B} := by
  classical
  let e := conjugateInSubgroupEquivOrbit (L := L) aL
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    refine ⟨e ⟨(b : G), b.2.2⟩, ?_⟩
    simpa [e, conjugateInSubgroupEquivOrbit] using b.2.1
  · intro b
    refine ⟨(((b : MulAction.orbit (ConjAct L) aL) : L) : G), ?_, ?_⟩
    · exact b.2
    · rcases (MulAction.mem_orbit_iff.1 (b : MulAction.orbit (ConjAct L) aL).2) with ⟨x, hx⟩
      refine ⟨ConjAct.ofConjAct x, ?_⟩
      have hx' := congrArg (fun y : L => (y : G)) hx
      simpa [ConjAct.smul_def, conjBy, mul_assoc] using hx'
  · intro b
    apply Subtype.ext
    rfl
  · intro b
    apply Subtype.ext
    rfl

private theorem sum_orbit_if_mem_normalizer_eq_subtype
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} [Finite L] (aL : L)
    (B : Set G)
    [DecidablePred
      (fun b : MulAction.orbit (ConjAct L) aL =>
        ((b : L) : G) ∈ normalizerIn L B)]
    (f : G → ℂ) :
    (∑ b : MulAction.orbit (ConjAct L) aL,
      if ((b : L) : G) ∈ normalizerIn L B then f ((b : L) : G) else 0) =
      ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (aL : G) b},
        f (b : G) := by
  classical
  let orbit := MulAction.orbit (ConjAct L) aL
  letI : Fintype orbit := Fintype.ofFinite orbit
  let p : orbit → Prop := fun b => ((b : L) : G) ∈ normalizerIn L B
  let e := normalizerConjugateEquivOrbitNormalizer (L := L) aL B
  have hfilter :
      (∑ b : orbit, if p b then f ((b : L) : G) else 0) =
        ∑ b : {b : orbit // p b}, f (((b : orbit) : L) : G) := by
    have hfilter_sum :
        (∑ b : orbit, if p b then f ((b : L) : G) else 0) =
          ∑ b ∈ (Finset.univ : Finset orbit).filter p,
            f ((b : L) : G) := by
      simpa [orbit, p] using
        (Finset.sum_filter
          (s := (Finset.univ : Finset orbit))
          (p := p)
          (f := fun b : orbit => f ((b : L) : G))).symm
    have hsubtype_filter :
        (∑ b : {b : orbit // p b}, f (((b : orbit) : L) : G)) =
          ∑ b ∈ (Finset.univ : Finset orbit).filter p,
            f ((b : L) : G) := by
      simpa [orbit, p] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset orbit))
          (f := fun b : orbit => f ((b : L) : G))
          (p := p))
    exact hfilter_sum.trans hsubtype_filter.symm
  have hsub :
      (∑ b : {b : orbit // p b}, f (((b : orbit) : L) : G)) =
        ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (aL : G) b},
          f (b : G) := by
    have hsub' :
        ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (aL : G) b},
          f (b : G) =
          (∑ b : {b : orbit // p b}, f (((b : orbit) : L) : G)) := by
      exact
        Fintype.sum_equiv e
          (fun b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (aL : G) b} =>
            f (b : G))
          (fun b : {b : orbit // p b} => f (((b : orbit) : L) : G))
          (by intro b; rfl)
    exact hsub'.symm
  have : Fintype.ofFinite { b // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (↑aL) b } = Subtype.fintype fun b ↦ b ∈ normalizerIn L B ∧ conjugateInSubgroup L (↑aL) b := of_decide_eq_true rfl
  exact hfilter.trans (by rw [hsub]; exact Finset.sum_congr (congrArg (@Finset.univ { b // b ∈ normalizerIn L B ∧ conjugateInSubgroup L (↑aL) b }) (id (Eq.symm this))) fun x ↦ congrFun rfl)

private theorem lSubsetOrbitFinset_card_mul_card_normalizerIn
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L] (B : Set G) :
    Nat.card (lSubsetOrbitFinset L B) * Nat.card (normalizerIn L B) =
      Nat.card L := by
  classical
  let toG : ConjAct L → G := fun x => ((ConjAct.ofConjAct x : L) : G)
  letI : MulAction (ConjAct L) (Set G) := {
    smul := fun x B => setConjugateBy (toG x) B
    one_smul := by
      intro B
      ext g
      constructor <;> intro hg
      · rcases hg with ⟨b, hb, rfl⟩
        simpa [toG, conjBy] using hb
      · exact ⟨g, hg, by simp [toG, conjBy]⟩
    mul_smul := by
      intro x y B
      ext g
      constructor <;> intro hg
      · rcases hg with ⟨b, hb, rfl⟩
        refine ⟨conjBy (toG y) b, ⟨b, hb, rfl⟩, ?_⟩
        simp [toG, conjBy, mul_assoc]
      · rcases hg with ⟨b, hb, rfl⟩
        rcases hb with ⟨c, hc, rfl⟩
        exact ⟨c, hc, by simp [toG, conjBy, mul_assoc]⟩
  }
  have horbit :
      MulAction.orbit (ConjAct L) B = lSubsetOrbitFinset L B := by
    ext C
    constructor
    · intro hC
      rw [MulAction.mem_orbit_iff] at hC
      rcases hC with ⟨x, rfl⟩
      change setConjugateBy (toG x) B ∈ lSubsetOrbitFinset L B
      simp [lSubsetOrbitFinset, toG]
    · intro hC
      change C ∈ lSubsetOrbitFinset L B at hC
      rw [lSubsetOrbitFinset, Finset.mem_image] at hC
      rcases hC with ⟨x, _hx, rfl⟩
      exact MulAction.mem_orbit_iff.2
        ⟨ConjAct.toConjAct x, by
          have hto : toG (ConjAct.toConjAct x) = (x : G) := rfl
          change setConjugateBy (toG (ConjAct.toConjAct x)) B =
            setConjugateBy (x : G) B
          simp [hto]⟩
  have hstab :
      Fintype.card (MulAction.stabilizer (ConjAct L) B) =
        Fintype.card (normalizerIn L B) := by
    classical
    let e : MulAction.stabilizer (ConjAct L) B ≃ normalizerIn L B := by
      refine
        { toFun := ?_
          invFun := ?_
          left_inv := ?_
          right_inv := ?_ }
      · intro x
        let xL : L := ConjAct.ofConjAct (x : ConjAct L)
        refine ⟨(xL : G), ?_⟩
        constructor
        · exact xL.2
        · have hxset : setConjugateBy (xL : G) B = B := by
            have hxfix : ((x : ConjAct L) • B : Set G) = B := x.2
            change setConjugateBy (xL : G) B = B at hxfix
            exact hxfix
          have hximg : conjugateImage B (xL : G) = B := by
            simpa [setConjugateBy_eq_conjugateImage] using hxset
          exact (normalizesSet_iff_conjugateImage_eq_self).2 hximg
      · intro x
        let xL : L := ⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩
        refine ⟨ConjAct.toConjAct xL, ?_⟩
        have hxnorm : normalizesSet B (x : G) := (Subgroup.mem_inf.mp x.2).2
        have hximg : conjugateImage B (x : G) = B :=
          (normalizesSet_iff_conjugateImage_eq_self).1 hxnorm
        have hxset : setConjugateBy (x : G) B = B := by
          simpa [setConjugateBy_eq_conjugateImage] using hximg
        change setConjugateBy (x : G) B = B
        exact hxset
      · intro x
        ext
        rfl
      · intro x
        ext
        rfl
    exact Fintype.card_congr e
  have hcard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct L) B
  rw [horbit, hstab] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard


private theorem representative_sum_signedDadeInductionFormulaTerm_eq_weighted_all
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} [Finite L] {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {reps : Finset (Set G)}
    (hreps : IsRepresentativeSystemForNonemptySubsets A L reps)
    {α : Section1.ClassFunction L} (hα : CFOn L A α)
    {g a : G} (ha : a ∈ A) :
    (reps.sum fun B =>
      ((-1 : ℂ) ^ Nat.card B) *
        dadeInductionFormulaTerm A L H α g a B hAL ha) =
      (Nat.card L : ℂ)⁻¹ *
        ∑ B ∈ nonemptySubsetsFinset A,
          (Nat.card (normalizerIn L B) : ℂ) *
            (((-1 : ℂ) ^ Nat.card B) *
              dadeInductionFormulaTerm A L H α g a B hAL ha) := by
  classical
  let signed : Set G → ℂ := fun B =>
    ((-1 : ℂ) ^ Nat.card B) *
      dadeInductionFormulaTerm A L H α g a B hAL ha
  let weighted : Set G → ℂ := fun B =>
    (Nat.card (normalizerIn L B) : ℂ) * signed B
  have horbit :
      ∀ B ∈ reps,
        ∑ C ∈ lSubsetOrbitFinset L B, weighted C =
          (Nat.card L : ℂ) * signed B := by
    intro B hBmem
    have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
    have hconst :
        ∀ C ∈ lSubsetOrbitFinset L B,
          weighted C =
            (Nat.card (normalizerIn L B) : ℂ) * signed B := by
      intro C hC
      have hBC : LConjugateSubsets L B C := (mem_lSubsetOrbitFinset).1 hC
      have hnorm :
          Nat.card (normalizerIn L C) =
            Nat.card (normalizerIn L B) :=
        normalizerIn_card_eq_of_lconj_set
          (L := L) hBC
      have hnormC :
          (Nat.card (normalizerIn L C) : ℂ) =
            (Nat.card (normalizerIn L B) : ℂ) := by
        exact_mod_cast hnorm
      have hsigned : signed C = signed B := by
        dsimp [signed]
        exact signedDadeInductionFormulaTerm_lconj_set_eq
          (A := A) (L := L) (H := H) h hAL hα ha hBprops.2 hBC
      dsimp [weighted]
      rw [hnormC, hsigned]
    calc
      ∑ C ∈ lSubsetOrbitFinset L B, weighted C =
          ∑ C ∈ lSubsetOrbitFinset L B,
            (Nat.card (normalizerIn L B) : ℂ) * signed B := by
            exact Finset.sum_congr rfl hconst
      _ =
          (Nat.card (lSubsetOrbitFinset L B) : ℂ) *
            ((Nat.card (normalizerIn L B) : ℂ) * signed B) := by
            simp [Finset.sum_const, Nat.card_eq_fintype_card]
      _ = (Nat.card L : ℂ) * signed B := by
            have hcardNat :=
              lSubsetOrbitFinset_card_mul_card_normalizerIn L B
            have hcard :
                (Nat.card (lSubsetOrbitFinset L B) : ℂ) *
                    (Nat.card (normalizerIn L B) : ℂ) =
                  (Nat.card L : ℂ) := by
              exact_mod_cast hcardNat
            rw [← mul_assoc, hcard]
  have hweighted_orbits :
      ∑ B ∈ reps, ∑ C ∈ lSubsetOrbitFinset L B, weighted C =
        (Nat.card L : ℂ) *
          (reps.sum fun B => signed B) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro B hBmem
    exact horbit B hBmem
  have hweighted_all :
      ∑ B ∈ reps, ∑ C ∈ lSubsetOrbitFinset L B, weighted C =
        ∑ B ∈ nonemptySubsetsFinset A, weighted B := by
    exact sum_lSubsetOrbitFinset_eq_sum_nonemptySubsetsFinset
      (A := A) (L := L) (H := H) h hreps weighted
  have hLne : (Nat.card L : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := L)).ne'
  have hmain :
      ∑ B ∈ nonemptySubsetsFinset A, weighted B =
        (Nat.card L : ℂ) * (reps.sum fun B => signed B) := by
    rw [← hweighted_all]
    exact hweighted_orbits
  have hmain' :
      (reps.sum fun B => signed B) =
        (Nat.card L : ℂ)⁻¹ *
          ∑ B ∈ nonemptySubsetsFinset A, weighted B := by
    have hmul :=
      congrArg (fun x : ℂ => (Nat.card L : ℂ)⁻¹ * x) hmain
    simpa [hLne, mul_assoc] using hmul.symm
  simpa [signed, weighted] using hmain'

private theorem normalizer_card_mul_dadeInductionFormulaTerm_eq
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} [Finite L] {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {α : Section1.ClassFunction L}
    {g a : G} (ha : a ∈ A) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A) :
    (Nat.card (normalizerIn L B) : ℂ) *
        dadeInductionFormulaTerm A L H α g a B hAL ha =
      α ⟨a, hAL a ha⟩ * (Nat.card (HInter H B) : ℂ)⁻¹ *
        ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
          (Nat.card (transporterSet g
            (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ) := by
  classical
  have hHne : (Nat.card (HInter H B) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := HInter H B)).ne'
  have hNne : (Nat.card (normalizerIn L B) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := normalizerIn L B)).ne'
  unfold dadeInductionFormulaTerm
  rw [MOfSet_card_mul A L H h hB hBA]
  field_simp [hHne, hNne]
  rw [Nat.cast_mul]
  ac_rfl

private theorem hInter_singleton_eq
    {G : Type u} [Group G] (H : G → Subgroup G) (a : G) :
    HInter H (Set.singleton a) = H a := by
  ext x
  constructor
  · intro hx
    exact hInter_le_of_mem H (B := Set.singleton a)
      (Set.mem_singleton a) hx
  · intro hx
    change x ∈ ⨅ b : Set.singleton a, H (b : G)
    rw [Subgroup.mem_iInf]
    intro b
    have hb : (b : G) = a := Set.mem_singleton_iff.mp b.2
    simpa [hb] using hx

private theorem normalizerIn_union_singleton_of_mem
    {G : Type u} [Group G] {L : Subgroup G} {B : Set G} {a : G}
    (haL : a ∈ L) (haN : a ∈ normalizerIn L B) :
    a ∈ normalizerIn L (B ∪ Set.singleton a) := by
  refine Subgroup.mem_inf.mpr ⟨haL, ?_⟩
  intro x
  constructor
  · intro hx
    rcases hx with hxB | hxa
    · have := ((Subgroup.mem_inf.mp haN).2 x).1 hxB
      exact Set.mem_union_left (Set.singleton a) this
    · have hx_eq : x = a := by
        have : a * x * a⁻¹ = a := hxa
        rw [← mul_inv_eq_one]
        have : a⁻¹ * (a * (x * a⁻¹)) = 1 := by
          trans a⁻¹ * (a * x * a⁻¹)
          rw [mul_assoc]
          rw [this]
          rw [inv_mul_cancel]
        rw [← mul_assoc, inv_mul_cancel, one_mul] at this
        exact this
      rw [hx_eq]
      right
      rfl
  · intro hx
    rcases hx with hxB | hxa
    · have := ((Subgroup.mem_inf.mp haN).2 x).2 hxB
      exact Set.mem_union_left (Set.singleton a) this
    · have hx_eq : x = a := Set.mem_singleton_iff.mp hxa
      subst x
      right
      simpa [conjBy]

private theorem self_mem_normalizerIn_singleton
    {G : Type u} [Group G] {L : Subgroup G} {a : G}
    (haL : a ∈ L) :
    a ∈ normalizerIn L (Set.singleton a) := by
  refine Subgroup.mem_inf.mpr ⟨haL, ?_⟩
  intro x
  constructor <;> intro hx
  · have hx_eq : x = a := by
        have : a * x * a⁻¹ = a := hx
        rw [← mul_inv_eq_one]
        have : a⁻¹ * (a * (x * a⁻¹)) = 1 := by
          trans a⁻¹ * (a * x * a⁻¹)
          rw [mul_assoc]
          rw [this]
          rw [inv_mul_cancel]
        rw [← mul_assoc, inv_mul_cancel, one_mul] at this
        exact this
    rw [hx_eq]
    rfl
  · have hx_eq : x = a := Set.mem_singleton_iff.mp hx
    subst x
    simpa [conjBy]

private theorem singleton_nonempty {G : Type u} (a : G) :
    (Set.singleton a).Nonempty :=
  ⟨a, rfl⟩


private theorem self_mem_normalizerIn_of_union_singleton
    {G : Type u} [Group G] {L : Subgroup G} {B : Set G} {a : G}
    (haB : a ∉ B) (haN : a ∈ normalizerIn L (B ∪ Set.singleton a)) :
    a ∈ normalizerIn L B := by
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp haN).1, ?_⟩
  intro x
  have hnorm : normalizesSet (B ∪ Set.singleton a) a :=
    (Subgroup.mem_inf.mp haN).2
  constructor
  · intro hx
    have hxUnion : x ∈ B ∪ Set.singleton a :=
      (hnorm x).1 (Or.inl hx)
    rcases hxUnion with hxB | hxa
    · exact hxB
    · have hx_eq : x = a := Set.mem_singleton_iff.mp hxa
      subst x
      have hconj : a ∈ B := by simpa [conjBy] using hx
      exact False.elim (haB hconj)
  · intro hxB
    have hxUnion : conjBy a x ∈ B ∪ Set.singleton a :=
      (hnorm x).2 (Or.inl hxB)
    rcases hxUnion with hxB' | hxa
    · exact hxB'
    · have hconj_eq : conjBy a x = a := Set.mem_singleton_iff.mp hxa
      have hx_eq : x = a := by
        have h := congrArg (fun y : G => a⁻¹ * y * a) hconj_eq
        simpa [conjBy, mul_assoc] using h
      subst x
      exact False.elim (haB hxB)

private theorem sum_normalizerSubsets_pair_union_singleton
    {G : Type u} [Group G] [Finite G] {A : Set G} {L : Subgroup G}
    {a : G} (ha : a ∈ A) (haL : a ∈ L) (f : Set G → ℂ)
    (hpair :
      ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
        a ∈ normalizerIn L B → a ∉ B →
        f (B ∪ Set.singleton a) = -f B) :
    (by
      classical
      exact ∑ B ∈ nonemptySubsetsFinset A,
        (if a ∈ normalizerIn L B then f B else 0)) = f (Set.singleton a) := by
  classical
  let filtered : Set G → ℂ := fun B =>
    if a ∈ normalizerIn L B then f B else 0
  have hpair' :
      ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A → a ∉ B →
        filtered (B ∪ Set.singleton a) = -filtered B := by
    intro B hB hBA haB
    by_cases hNB : a ∈ normalizerIn L B
    · have hNunion : a ∈ normalizerIn L (B ∪ Set.singleton a) :=
        normalizerIn_union_singleton_of_mem haL hNB
      simp [filtered, hNB, hNunion, hpair hB hBA hNB haB]
    · have hNunion : a ∉ normalizerIn L (B ∪ Set.singleton a) := by
        intro hNunion
        exact hNB (self_mem_normalizerIn_of_union_singleton haB hNunion)
      simp [filtered, hNB, hNunion]
  have hsum := sum_nonemptySubsetsFinset_pair_union_singleton ha filtered hpair'
  have hsingle : a ∈ normalizerIn L (Set.singleton a) :=
    self_mem_normalizerIn_singleton haL
  simpa [filtered, hsingle] using hsum


private theorem transporterSet_subgroupCosetByElement_card_eq_index_mul
    {G : Type u} [Group G] [Finite G]
    (g a : G) (K : Subgroup G)
    (hnorm : normalizesSet (K : Set G) a)
    (hcop : Nat.Coprime (orderOf a) (Nat.card K)) :
    Nat.card (transporterSet g (subgroupCosetByElement K a)) =
      (Nat.card K / Nat.card (centralizerIn K a)) *
        Nat.card (transporterSet g
          (subgroupCosetByElement (centralizerIn K a) a)) := by
  classical
  rcases proposition_2_1 a K hnorm hcop with
    ⟨reps, hreps_card, _hreps_mem, hreps_disj, hunion⟩
  let piece : G → Set G := fun x => transporterSet g (conjugateCosetPiece K a x)
  have hpre :
      (transporterSet g (subgroupCosetByElement K a)).toFinset =
        reps.biUnion fun x => (piece x).toFinset := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_biUnion]
      rw [Set.mem_toFinset] at hy
      rw [mem_transporterSet_iff] at hy
      rw [hunion] at hy
      rcases hy with ⟨x, hx, hyx⟩
      exact ⟨x, hx, by
        rw [Set.mem_toFinset, mem_transporterSet_iff]
        exact hyx⟩
    · intro hy
      rw [Finset.mem_biUnion] at hy
      rcases hy with ⟨x, hx, hyx⟩
      rw [Set.mem_toFinset] at hyx ⊢
      rw [mem_transporterSet_iff] at hyx ⊢
      rw [hunion]
      exact ⟨x, hx, hyx⟩
  have hpair :
      ((reps : Set G)).PairwiseDisjoint fun x => (piece x).toFinset := by
    intro x hx y hy hxy
    change Disjoint ((piece x).toFinset) ((piece y).toFinset)
    rw [Finset.disjoint_left]
    intro z hzx
    rw [Set.mem_toFinset] at hzx
    rw [mem_transporterSet_iff] at hzx
    intro hzy
    rw [Set.mem_toFinset] at hzy
    rw [mem_transporterSet_iff] at hzy
    have hnot :
        z⁻¹ * g * z ∉ conjugateCosetPiece K a y :=
      (Set.disjoint_left.mp (hreps_disj x hx y hy hxy)) hzx
    exact hnot hzy
  have hpiece_card :
      ∀ x ∈ reps, ((piece x).toFinset).card =
        Nat.card (transporterSet g
          (subgroupCosetByElement (centralizerIn K a) a)) := by
    intro x hx
    dsimp [piece, conjugateCosetPiece]
    have hcard :=
      transporterSet_conjugateImage_card_eq
        (g := g)
        (X := subgroupCosetByElement (centralizerIn K a) a)
        (x := x)
    calc
      ((transporterSet g
          (conjugateImage (subgroupCosetByElement (centralizerIn K a) a) x)).toFinset).card =
          (transporterSet g
            (conjugateImage (subgroupCosetByElement (centralizerIn K a) a) x)).ncard := by
              symm
              exact Set.ncard_eq_toFinset_card'
                (transporterSet g
                  (conjugateImage (subgroupCosetByElement (centralizerIn K a) a) x))
      _ = Nat.card (transporterSet g
            (conjugateImage (subgroupCosetByElement (centralizerIn K a) a) x)) := by
          rw [Nat.card_coe_set_eq]
      _ = Nat.card (transporterSet g
            (subgroupCosetByElement (centralizerIn K a) a)) := hcard
  have hUnionCard :
      (reps.biUnion fun x => (piece x).toFinset).card =
        reps.card *
          Nat.card (transporterSet g
            (subgroupCosetByElement (centralizerIn K a) a)) := by
    rw [Finset.card_biUnion hpair]
    exact Finset.sum_const_nat (s := reps)
      (f := fun x => ((piece x).toFinset).card)
      (m := Nat.card (transporterSet g
        (subgroupCosetByElement (centralizerIn K a) a))) hpiece_card
  calc
    Nat.card (transporterSet g (subgroupCosetByElement K a)) =
        ((transporterSet g (subgroupCosetByElement K a)).toFinset).card := by
          simp
    _ = (reps.biUnion fun x => (piece x).toFinset).card := by
          rw [hpre]
    _ = reps.card *
        Nat.card (transporterSet g
          (subgroupCosetByElement (centralizerIn K a) a)) := hUnionCard
    _ = (Nat.card K / Nat.card (centralizerIn K a)) *
        Nat.card (transporterSet g
          (subgroupCosetByElement (centralizerIn K a) a)) := by
          rw [hreps_card]

private theorem transporterSet_hInter_union_singleton_ratio
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {B : Set G}
    (hB : B.Nonempty) (hBA : B ⊆ A) {a g : G}
    (ha : a ∈ A) (haN : a ∈ normalizerIn L B) :
    (Nat.card (HInter H B) : ℂ)⁻¹ *
        (Nat.card
          (transporterSet g
            (rightTranslateSet (HInter H B : Set G) a)) : ℂ) =
      (Nat.card (HInter H (B ∪ Set.singleton a)) : ℂ)⁻¹ *
        (Nat.card
          (transporterSet g
            (rightTranslateSet (HInter H (B ∪ Set.singleton a) : Set G) a)) : ℂ) := by
  classical
  have hnorm :
      normalizesSet (HInter H B : Set G) a :=
    normalizerIn_normalizes_hInter
      (A := A) (L := L) (H := H) h hBA haN
  have hcop : Nat.Coprime (orderOf a) (Nat.card (HInter H B)) :=
    orderOf_mem_A_coprime_hInter
      (A := A) (L := L) (H := H) h hB hBA ha
  have hcardT :=
    transporterSet_subgroupCosetByElement_card_eq_index_mul
      g a (HInter H B) hnorm hcop
  have hcent :
      centralizerIn (HInter H B) a =
        HInter H (B ∪ Set.singleton a) := by
    exact centralizerIn_hInter_eq_hInter_union_singleton
      (A := A) (L := L) (H := H) h hB hBA ha
  have hcardHdiv :
      Nat.card (HInter H B) =
        (Nat.card (HInter H B) / Nat.card (centralizerIn (HInter H B) a)) *
          Nat.card (centralizerIn (HInter H B) a) := by
    have hle : centralizerIn (HInter H B) a ≤ HInter H B := by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).1
    exact (Nat.div_mul_cancel (Subgroup.card_dvd_of_le hle)).symm
  have hHBne : (Nat.card (HInter H B) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := HInter H B)).ne'
  have hHCne :
      (Nat.card (centralizerIn (HInter H B) a) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := centralizerIn (HInter H B) a)).ne'
  have hcardT' :
      (Nat.card
          (transporterSet g
            (rightTranslateSet (HInter H B : Set G) a)) : ℂ) =
        ((Nat.card (HInter H B) : ℂ) /
            (Nat.card (centralizerIn (HInter H B) a) : ℂ)) *
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (centralizerIn (HInter H B) a : Set G) a)) : ℂ) := by
    have hle : centralizerIn (HInter H B) a ≤ HInter H B := by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).1
    have hdivides : Nat.card (centralizerIn (HInter H B) a) ∣ Nat.card (HInter H B) :=
      Subgroup.card_dvd_of_le hle
    have hdiv :
        (((Nat.card (HInter H B) / Nat.card (centralizerIn (HInter H B) a)) : ℕ) : ℂ) =
          (Nat.card (HInter H B) : ℂ) /
            (Nat.card (centralizerIn (HInter H B) a) : ℂ) := by
      simpa using (Nat.cast_div (K := ℂ) hdivides
        (by exact_mod_cast (Nat.card_pos
          (α := centralizerIn (HInter H B) a)).ne'))
    have hcardTcast := congrArg (fun n : ℕ => (n : ℂ)) hcardT
    have hcardTcast' :
        (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) a)) : ℂ) =
          ((Nat.card (HInter H B) / Nat.card (centralizerIn (HInter H B) a) : ℕ) : ℂ) *
            (Nat.card
              (transporterSet g
                (rightTranslateSet
                  (centralizerIn (HInter H B) a : Set G) a)) : ℂ) := by
      simpa [subgroupCosetByElement, mul_assoc] using hcardTcast
    rw [hdiv] at hcardTcast'
    simpa [subgroupCosetByElement, mul_assoc] using hcardTcast'
  rw [hcardT']
  rw [← hcent]
  have hcardHC :
      ((Nat.card (HInter H B) : ℂ) /
          (Nat.card (centralizerIn (HInter H B) a) : ℂ)) *
        (Nat.card (centralizerIn (HInter H B) a) : ℂ) =
          (Nat.card (HInter H B) : ℂ) := by
    field_simp [hHBne, hHCne]
  calc
    (Nat.card (HInter H B) : ℂ)⁻¹ *
        (((Nat.card (HInter H B) : ℂ) /
              (Nat.card (centralizerIn (HInter H B) a) : ℂ)) *
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (centralizerIn (HInter H B) a : Set G) a)) : ℂ)) =
        (Nat.card (centralizerIn (HInter H B) a) : ℂ)⁻¹ *
          (Nat.card
            (transporterSet g
              (rightTranslateSet
                (centralizerIn (HInter H B) a : Set G) a)) : ℂ) := by
          apply mul_right_cancel₀ hHCne
          field_simp [hHBne, hHCne, hcardHC]
    _ = (Nat.card (centralizerIn (HInter H B) a) : ℂ)⁻¹ *
        (Nat.card
          (transporterSet g
            (rightTranslateSet (centralizerIn (HInter H B) a : Set G) a)) : ℂ) := rfl

private theorem conjugateImage_conjugateImage_eq
    {G : Type u} [Group G] (S : Set G) (x y : G) :
    conjugateImage (conjugateImage S x) y = conjugateImage S (y * x) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp [conjBy, mul_assoc]⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨conjBy x s, ⟨s, hs, rfl⟩, ?_⟩
    simp [conjBy, mul_assoc]

private theorem conjugateImage_one
    {G : Type u} [Group G] (S : Set G) :
    conjugateImage S (1 : G) = S := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [conjBy] using hs
  · intro hz
    exact ⟨z, hz, by simp [conjBy]⟩

private theorem normalizesSet_iff_conjugateImage_eq
    {G : Type u} [Group G] (S : Set G) (x : G) :
    normalizesSet S x ↔ conjugateImage S x = S := by
  constructor
  · intro hx
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hx s).2 hs
    · intro hz
      refine ⟨conjBy x⁻¹ z, ?_, ?_⟩
      · exact (hx (conjBy x⁻¹ z)).1 (by
          simpa [conjBy, mul_assoc] using hz)
      · simp [conjBy, mul_assoc]
  · intro hx z
    constructor
    · intro hz
      have hzImage : conjBy x z ∈ conjugateImage S x := by
        simpa [hx] using hz
      rcases hzImage with ⟨w, hw, hzw⟩
      have hzw' : z = w := by
        have := congrArg (fun t : G => conjBy x⁻¹ t) hzw
        simpa [conjBy, mul_assoc] using this
      simpa [hzw'] using hw
    · intro hz
      have : conjBy x z ∈ conjugateImage S x := ⟨z, hz, rfl⟩
      simpa [hx] using this

private theorem rightTranslate_H_eq_cosetProduct
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A) :
    rightTranslateSet (H a : Set G) a = cosetProduct a (H a) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcomm : a * u = u * a :=
      mem_elementCentralizer_commute' ((h.centralizer_eq_product ha).left_le hu)
    exact ⟨a, by simp, u, hu, hcomm.symm⟩
  · rintro ⟨s, hs, u, hu, rfl⟩
    have hs_eq : s = a := Set.mem_singleton_iff.mp hs
    subst s
    have hcomm : a * u = u * a :=
      mem_elementCentralizer_commute' ((h.centralizer_eq_product ha).left_le hu)
    exact ⟨u, hu, hcomm⟩

private theorem transporterSet_cosetProduct_card_eq_setNormalizer
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a))) :
    Nat.card (transporterSet g (cosetProduct a (H a))) =
      Nat.card (setNormalizer (cosetProduct a (H a))) := by
  classical
  let X : Set G := cosetProduct a (H a)
  rcases hgpiece with ⟨s, hs, x₀, hx₀⟩
  have hx₀trans : x₀ ∈ transporterSet g X := by
    rw [mem_transporterSet_iff]
    have := congrArg (fun z : G => x₀⁻¹ * z * x₀) hx₀
    have hx₀eq : x₀⁻¹ * g * x₀ = s := by
      simpa [conjBy, mul_assoc] using this.symm
    simpa [X, hx₀eq] using hs
  let e : transporterSet g X ≃ setNormalizer X := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro y
      refine ⟨x₀⁻¹ * (y : G), ?_⟩
      have hyX : (y : G)⁻¹ * g * (y : G) ∈ X := by
        exact (mem_transporterSet_iff (g := g) (X := X) (x := (y : G))).1 y.2
      have hg_y : g ∈ conjugateImage X (y : G) := by
        refine ⟨(y : G)⁻¹ * g * (y : G), hyX, ?_⟩
        simp [conjBy, mul_assoc]
      have hg_x₀ : g ∈ conjugateImage X x₀ := by
        exact ⟨s, by simpa [X] using hs, hx₀.symm⟩
      have hpieces :
          conjugateImage X (y : G) = conjugateImage X x₀ := by
        exact conjugateImage_cosetProduct_eq_of_nonempty_inter
          (A := A) (L := L) (H := H) h ha
          ⟨g, by simpa [X] using hg_y, by simpa [X] using hg_x₀⟩
      have himage :
          conjugateImage X (x₀⁻¹ * (y : G)) = X := by
        calc
          conjugateImage X (x₀⁻¹ * (y : G)) =
              conjugateImage (conjugateImage X (y : G)) x₀⁻¹ := by
                rw [conjugateImage_conjugateImage_eq]
          _ = conjugateImage (conjugateImage X x₀) x₀⁻¹ := by rw [hpieces]
          _ = conjugateImage X (x₀⁻¹ * x₀) := by
                rw [conjugateImage_conjugateImage_eq]
          _ = X := by
                simpa using conjugateImage_one (S := X)
      exact (normalizesSet_iff_conjugateImage_eq X (x₀⁻¹ * (y : G))).2 himage
    · intro n
      refine ⟨x₀ * (n : G), ?_⟩
      rw [mem_transporterSet_iff]
      have hx₀X : x₀⁻¹ * g * x₀ ∈ X := by
        exact (mem_transporterSet_iff (g := g) (X := X) (x := x₀)).1 hx₀trans
      have hninv : normalizesSet X ((n : G)⁻¹) := normalizesSet_inv n.2
      have hx : conjBy ((n : G)⁻¹) (x₀⁻¹ * g * x₀) ∈ X :=
        (hninv (x₀⁻¹ * g * x₀)).2 hx₀X
      simpa [conjBy, mul_assoc] using hx
    · intro y
      ext
      simp
    · intro n
      ext
      simp
  exact Nat.card_congr e

private theorem transporterSet_rightTranslate_H_card_eq_elementCentralizer
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a))) :
    Nat.card (transporterSet g (rightTranslateSet (H a : Set G) a)) =
      Nat.card (elementCentralizer a) := by
  rw [rightTranslate_H_eq_cosetProduct (A := A) (L := L) (H := H) h ha]
  rw [transporterSet_cosetProduct_card_eq_setNormalizer
    (A := A) (L := L) (H := H) h ha hgpiece]
  rw [((proposition_2_4 A L H).2.2 h) (a := a) ha]

public theorem dadeTransform_eq_on_conjugateSet_cosetProduct
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) (hαclass : Section1.IsClassFunction α)
    {a g : G} (ha : a ∈ A)
    (hg : g ∈ conjugateSet (cosetProduct a (H a))) :
    dadeTransform H hAL α g = α ⟨a, hAL a ha⟩ := by
  rcases (mem_conjugateSet_cosetProduct_iff a (H a) g).1 hg with
    ⟨k, hk, hconj⟩
  exact dadeTransform_eq_of_isClassFunction A L H h hAL α hαclass ha hk
    (conjugateIn_symm hconj)


set_option maxHeartbeats 800000 in
private theorem weighted_nonemptySubsets_dadeInductionFormulaTerm_support_cancel
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {α : Section1.ClassFunction L}
    {g a : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a))) :
    (∑ B ∈ nonemptySubsetsFinset A,
      (Nat.card (normalizerIn L B) : ℂ) *
        (((-1 : ℂ) ^ Nat.card B) *
          dadeInductionFormulaTerm A L H α g a B hAL ha)) =
      -(Nat.card L : ℂ) * α ⟨a, hAL a ha⟩ := by
  classical
  let weighted : Set G → ℂ := fun B =>
    (Nat.card (normalizerIn L B) : ℂ) *
      (((-1 : ℂ) ^ Nat.card B) *
        dadeInductionFormulaTerm A L H α g a B hAL ha)
  let fixedContribution : Set G → ℂ := fun B =>
    ((-1 : ℂ) ^ Nat.card B) *
      (Nat.card (HInter H B) : ℂ)⁻¹ *
        (Nat.card
          (transporterSet g
            (rightTranslateSet (HInter H B : Set G) a)) : ℂ)
  have hregroup :
      (∑ B ∈ nonemptySubsetsFinset A, weighted B) =
        α ⟨a, hAL a ha⟩ *
          ((Nat.card L : ℂ) *
            (Nat.card (centralizerIn L a) : ℂ)⁻¹) *
          (∑ B ∈ nonemptySubsetsFinset A,
            if a ∈ normalizerIn L B then fixedContribution B else 0) := by
    classical
    let orbit := MulAction.orbit (ConjAct L) (⟨a, hAL a ha⟩ : L)
    letI : Fintype orbit := Fintype.ofFinite orbit
    let contribution : Set G → G → ℂ := fun B b =>
      ((-1 : ℂ) ^ Nat.card B) *
        (Nat.card (HInter H B) : ℂ)⁻¹ *
          (Nat.card
            (transporterSet g
              (rightTranslateSet (HInter H B : Set G) b)) : ℂ)
    let ψ : Section1.ClassFunction L := fun b =>
      ∑ B ∈ nonemptySubsetsFinset A,
        if (b : G) ∈ normalizerIn L B then contribution B (b : G) else 0
    have hψclass : Section1.IsClassFunction ψ := by
      intro x b
      let f : Set G → ℂ := fun B =>
        if conjBy (x : G) (b : G) ∈ normalizerIn L B then
          contribution B (conjBy (x : G) (b : G))
        else
          0
      have hsum :=
        sum_nonemptySubsetsFinset_setConjugateBy
          (A := A) (L := L) (H := H) h x f
      have hleft :
          (∑ B ∈ nonemptySubsetsFinset A,
            f (setConjugateBy (x : G) B)) = ψ b := by
        refine Finset.sum_congr rfl ?_
        intro B hBmem
        dsimp [f]
        have hBA : B ⊆ A := ((mem_nonemptySubsetsFinset (A := A) (B := B)).1 hBmem).2
        have hiff :
            conjBy (x : G) (b : G) ∈
                normalizerIn L (setConjugateBy (x : G) B) ↔
              (b : G) ∈ normalizerIn L B :=
          normalizerIn_setConjugateBy_mem_iff
            (L := L) (B := B) x (b : G)
        by_cases hbN : (b : G) ∈ normalizerIn L B
        · rw [if_pos ((hiff).2 hbN), if_pos hbN]
          exact transporterContribution_setConjugateBy_eq
            (A := A) (L := L) (H := H) h hBA x g (b : G)
        · rw [if_neg (mt hiff.1 hbN), if_neg hbN]
      have hright :
          (∑ B ∈ nonemptySubsetsFinset A, f B) =
            ψ (x * b * x⁻¹) := by
        simp [ψ, f, contribution, conjBy, mul_assoc]
      exact hright.symm.trans (hsum.symm.trans hleft)
    have hweightedB :
        ∀ B ∈ nonemptySubsetsFinset A,
          weighted B =
            α ⟨a, hAL a ha⟩ *
              (∑ b : orbit,
                if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                  contribution B (((b : orbit) : L) : G)
                else
                  0) := by
      intro B hBmem
      have hBprops := (mem_nonemptySubsetsFinset (A := A) (B := B)).1 hBmem
      have hterm :=
        normalizer_card_mul_dadeInductionFormulaTerm_eq
          (A := A) (L := L) (H := H) h hAL
          (α := α) (g := g) ha hBprops.1 hBprops.2
      letI : Fintype {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b} :=
        Fintype.ofFinite _
      have horbit :
          (∑ b : orbit,
            if (((b : orbit) : L) : G) ∈ normalizerIn L B then
              contribution B (((b : orbit) : L) : G)
            else
              0) =
            ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
              contribution B (b : G) := by
        have h :=
          sum_orbit_if_mem_normalizer_eq_subtype
            (L := L) (aL := ⟨a, hAL a ha⟩) (B := B)
            (f := fun b : G => contribution B b)
        simpa [orbit, contribution] using h
      calc
        weighted B =
            ((-1 : ℂ) ^ Nat.card B) *
              ((Nat.card (normalizerIn L B) : ℂ) *
                dadeInductionFormulaTerm A L H α g a B hAL ha) := by
              dsimp [weighted]
              ring
        _ =
            ((-1 : ℂ) ^ Nat.card B) *
              (α ⟨a, hAL a ha⟩ *
                (Nat.card (HInter H B) : ℂ)⁻¹ *
                  ∑ b : {b : G //
                      b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
                    (Nat.card
                        (transporterSet g
                          (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ)) := by
              rw [hterm]
        _ =
            α ⟨a, hAL a ha⟩ *
              (∑ b : {b : G //
                    b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
                contribution B (b : G)) := by
              have hsumcontrib :
                  ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
                    contribution B (b : G) =
                    ((-1 : ℂ) ^ Nat.card B) *
                      ((Nat.card (HInter H B) : ℂ)⁻¹ *
                        ∑ b : {b : G //
                            b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
                          (Nat.card
                            (transporterSet g
                              (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ)) := by
                dsimp [contribution]
                rw [Finset.mul_sum]
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro b hb
                ring
              rw [hsumcontrib]
              ring
        _ =
            α ⟨a, hAL a ha⟩ *
              (∑ b : orbit,
                if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                  contribution B (((b : orbit) : L) : G)
                else
                  0) := by
              rw [horbit]
    have hweighted_orbit :
        (∑ B ∈ nonemptySubsetsFinset A, weighted B) =
          α ⟨a, hAL a ha⟩ * ∑ b : orbit, ψ (b : L) := by
      calc
        (∑ B ∈ nonemptySubsetsFinset A, weighted B) =
            ∑ B ∈ nonemptySubsetsFinset A,
              α ⟨a, hAL a ha⟩ *
                (∑ b : orbit,
                  if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                    contribution B (((b : orbit) : L) : G)
                  else
                    0) := by
              exact Finset.sum_congr rfl hweightedB
        _ =
            α ⟨a, hAL a ha⟩ *
              (∑ B ∈ nonemptySubsetsFinset A,
                ∑ b : orbit,
                  if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                    contribution B (((b : orbit) : L) : G)
                  else
                    0) := by
              rw [Finset.mul_sum]
        _ =
            α ⟨a, hAL a ha⟩ * ∑ b : orbit, ψ (b : L) := by
              congr 1
              have hcomm :
                  (∑ B ∈ nonemptySubsetsFinset A,
                      ∑ b : orbit,
                        (if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                          contribution B (((b : orbit) : L) : G)
                        else
                          (0 : ℂ))) =
                    (∑ b : orbit,
                      ∑ B ∈ nonemptySubsetsFinset A,
                        (if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                          contribution B (((b : orbit) : L) : G)
                        else
                          (0 : ℂ))) := by
                  simpa using
                    (Finset.sum_comm
                      (s := nonemptySubsetsFinset A)
                      (t := (Finset.univ : Finset orbit))
                      (f := fun B b =>
                        if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                          contribution B (((b : orbit) : L) : G)
                        else
                          (0 : ℂ)))
              calc
                (∑ B ∈ nonemptySubsetsFinset A,
                    ∑ b : orbit,
                      (if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                        contribution B (((b : orbit) : L) : G)
                      else
                        (0 : ℂ))) =
                    ∑ b : orbit,
                      ∑ B ∈ nonemptySubsetsFinset A,
                        (if (((b : orbit) : L) : G) ∈ normalizerIn L B then
                          contribution B (((b : orbit) : L) : G)
                        else
                          (0 : ℂ)) := hcomm
                _ = ∑ b : orbit, ψ (b : L) := by
                    refine Finset.sum_congr rfl ?_
                    intro b hb
                    rfl
    have horbit_sum :
        (∑ b : orbit, ψ (b : L)) =
          (Nat.card orbit : ℂ) * ψ ⟨a, hAL a ha⟩ := by
      change
        (∑ b : MulAction.orbit (ConjAct L) (⟨a, hAL a ha⟩ : L), ψ (b : L)) =
          (Nat.card (MulAction.orbit (ConjAct L) (⟨a, hAL a ha⟩ : L)) : ℂ) *
            ψ (⟨a, hAL a ha⟩ : L)
      exact sum_orbit_conjAct_eq_card_mul L ψ hψclass (⟨a, hAL a ha⟩ : L)
    have horbit_card :
        (Nat.card orbit : ℂ) =
          (Nat.card L : ℂ) * (Nat.card (centralizerIn L a) : ℂ)⁻¹ := by
      have hnat :=
        orbit_card_mul_card_centralizerIn L ⟨a, hAL a ha⟩
      have hcast :
          (Nat.card orbit : ℂ) *
              (Nat.card (centralizerIn L a) : ℂ) =
            (Nat.card L : ℂ) := by
        change
          (Nat.card (MulAction.orbit (ConjAct L) (⟨a, hAL a ha⟩ : L)) : ℂ) *
              (Nat.card (centralizerIn L a) : ℂ) =
            (Nat.card L : ℂ)
        exact_mod_cast hnat
      have hCne : (Nat.card (centralizerIn L a) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := centralizerIn L a)).ne'
      rw [← hcast]
      rw [mul_assoc, mul_inv_cancel₀ hCne, mul_one]
    calc
      (∑ B ∈ nonemptySubsetsFinset A, weighted B) =
          α ⟨a, hAL a ha⟩ * ∑ b : orbit, ψ (b : L) := hweighted_orbit
      _ =
          α ⟨a, hAL a ha⟩ *
            ((Nat.card orbit : ℂ) * ψ ⟨a, hAL a ha⟩) := by
          rw [horbit_sum]
      _ =
          α ⟨a, hAL a ha⟩ *
            (((Nat.card L : ℂ) *
                (Nat.card (centralizerIn L a) : ℂ)⁻¹) *
              (∑ B ∈ nonemptySubsetsFinset A,
                if a ∈ normalizerIn L B then fixedContribution B else 0)) := by
          rw [horbit_card]
      _ =
          α ⟨a, hAL a ha⟩ *
            ((Nat.card L : ℂ) *
              (Nat.card (centralizerIn L a) : ℂ)⁻¹) *
            (∑ B ∈ nonemptySubsetsFinset A,
              if a ∈ normalizerIn L B then fixedContribution B else 0) := by
          ring
  have hpair :
      ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
        a ∈ normalizerIn L B → a ∉ B →
        fixedContribution (B ∪ Set.singleton a) = -fixedContribution B := by
    -- PF (2.10): for `B ∈ P(a)`, Proposition (2.1) decomposes `H(B)a`
    -- into conjugates of `C_{H(B)}(a)a`; (2.10.2) identifies this centralizer
    -- with `H(B ∪ {a})`.
    intro B hB hBA haN haB
    have hratio :=
      transporterSet_hInter_union_singleton_ratio
        (A := A) (L := L) (H := H) h hB hBA ha haN (g := g)
    have hcard :
        (B ∪ Set.singleton a).ncard = B.ncard + 1 := by
      have hset : B ∪ Set.singleton a = Set.insert a B := by
        ext x
        constructor
        · intro hx
          change x = a ∨ x ∈ B
          rcases hx with hxB | hxa
          · exact Or.inr hxB
          · exact Or.inl (Set.mem_singleton_iff.mp hxa)
        · intro hx
          change x = a ∨ x ∈ B at hx
          rcases hx with hxa | hxB
          · exact Or.inr (Set.mem_singleton_iff.mpr hxa)
          · exact Or.inl hxB
      rw [hset]
      exact Set.ncard_insert_of_notMem (s := B) haB
    have hsign :
        ((-1 : ℂ) ^ (B ∪ Set.singleton a).ncard) =
          -((-1 : ℂ) ^ B.ncard) := by
      rw [hcard, pow_succ]
      ring
    have hratioN :
        (Nat.card (HInter H B) : ℂ)⁻¹ *
            ((transporterSet g
              (rightTranslateSet (HInter H B : Set G) a)).ncard : ℂ) =
          (Nat.card (HInter H (B ∪ Set.singleton a)) : ℂ)⁻¹ *
            ((transporterSet g
              (rightTranslateSet
                (HInter H (B ∪ Set.singleton a) : Set G) a)).ncard : ℂ) := by
      change
        (Nat.card (HInter H B) : ℂ)⁻¹ *
            (Nat.card
              (transporterSet g
                (rightTranslateSet (HInter H B : Set G) a)) : ℂ) =
          (Nat.card (HInter H (B ∪ Set.singleton a)) : ℂ)⁻¹ *
            (Nat.card
              (transporterSet g
                (rightTranslateSet
                  (HInter H (B ∪ Set.singleton a) : Set G) a)) : ℂ)
      exact hratio
    dsimp [fixedContribution]
    rw [hsign]
    rw [mul_assoc]
    rw [← hratioN]
    rw [neg_mul]
    rw [mul_assoc]
  have hsum :
      (∑ B ∈ nonemptySubsetsFinset A,
        if a ∈ normalizerIn L B then fixedContribution B else 0) =
        fixedContribution (Set.singleton a) :=
    sum_normalizerSubsets_pair_union_singleton ha (hAL a ha)
      fixedContribution hpair
  have hsingleton :
      fixedContribution (Set.singleton a) =
        -(Nat.card (centralizerIn L a) : ℂ) := by
    have hTcard :
        Nat.card (transporterSet g (rightTranslateSet (H a : Set G) a)) =
          Nat.card (elementCentralizer a) :=
      transporterSet_rightTranslate_H_card_eq_elementCentralizer
        (A := A) (L := L) (H := H) h ha hgpiece
    have hTncard :
        (transporterSet g (rightTranslateSet (H a : Set G) a)).ncard =
          Nat.card (elementCentralizer a) := by
      change Nat.card (transporterSet g (rightTranslateSet (H a : Set G) a)) =
        Nat.card (elementCentralizer a)
      exact hTcard
    have hcentcard :
        (Nat.card (elementCentralizer a) : ℂ) =
          (Nat.card (H a) : ℂ) * (Nat.card (centralizerIn L a) : ℂ) := by
      exact_mod_cast centralizer_card_eq_mul (A := A) (L := L) (H := H) h ha
    haveI : Nonempty (H a) := ⟨⟨1, (H a).one_mem⟩⟩
    have hHneNat : Nat.card (H a) ≠ 0 := Nat.card_pos.ne'
    have hHne : (Nat.card (H a) : ℂ) ≠ 0 := by
      exact_mod_cast hHneNat
    haveI : Nonempty (centralizerIn L a) := ⟨⟨1, by simp [centralizerIn]⟩⟩
    have hCneNat : Nat.card (centralizerIn L a) ≠ 0 := Nat.card_pos.ne'
    have hCne : (Nat.card (centralizerIn L a) : ℂ) ≠ 0 := by
      exact_mod_cast hCneNat
    calc
      fixedContribution (Set.singleton a) =
          (-1 : ℂ) * (Nat.card (H a) : ℂ)⁻¹ *
            (Nat.card (elementCentralizer a) : ℂ) := by
              dsimp [fixedContribution]
              rw [hInter_singleton_eq]
              rw [hTncard]
              have hs : (Set.singleton a : Set G).ncard = 1 := by
                exact Set.ncard_singleton a
              rw [hs]
              ring_nf
      _ = (-1 : ℂ) * (Nat.card (H a) : ℂ)⁻¹ *
            ((Nat.card (H a) : ℂ) * (Nat.card (centralizerIn L a) : ℂ)) := by
              rw [hcentcard]
      _ = -(Nat.card (centralizerIn L a) : ℂ) := by
              field_simp [hHne, hCne]
  calc
    (∑ B ∈ nonemptySubsetsFinset A, weighted B) =
        α ⟨a, hAL a ha⟩ *
          ((Nat.card L : ℂ) *
            (Nat.card (centralizerIn L a) : ℂ)⁻¹) *
          (∑ B ∈ nonemptySubsetsFinset A,
            if a ∈ normalizerIn L B then fixedContribution B else 0) := hregroup
    _ =
        α ⟨a, hAL a ha⟩ *
          ((Nat.card L : ℂ) *
            (Nat.card (centralizerIn L a) : ℂ)⁻¹) *
          fixedContribution (Set.singleton a) := by
          rw [hsum]
    _ = -(Nat.card L : ℂ) * α ⟨a, hAL a ha⟩ := by
          rw [hsingleton]
          have hCne : (Nat.card (centralizerIn L a) : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.card_pos (α := centralizerIn L a)).ne'
          field_simp [hCne]

public theorem dadeInductionFormulaTerm_representative_sum_support_cancel
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    {reps : Finset (Set G)}
    (hreps : IsRepresentativeSystemForNonemptySubsets A L reps)
    (α : Section1.ClassFunction L) (hα : CFOn L A α)
    {g a : G} (ha : a ∈ A)
    (hgpiece : g ∈ conjugateSet (cosetProduct a (H a))) :
    (reps.sum fun B =>
      ((-1 : ℂ) ^ Nat.card B) *
        dadeInductionFormulaTerm A L H α g a B hAL ha) =
      -α ⟨a, hAL a ha⟩ := by
  -- PF (2.10): reindex by all nonempty subsets of `A`; then pair each
  -- subset of `A \ {a}` with its union with `{a}`.  The only unpaired term is
  -- `{a}`, whose transporter is a coset of `C_G(a)`.
  classical
  have hweighted :=
    representative_sum_signedDadeInductionFormulaTerm_eq_weighted_all
      (A := A) (L := L) (H := H) h hAL hreps hα (g := g) ha
  rw [hweighted]
  rw [weighted_nonemptySubsets_dadeInductionFormulaTerm_support_cancel
    A L H h hAL ha hgpiece]
  have hLne : (Nat.card L : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := L)).ne'
  field_simp [hLne]

public theorem theorem_2_6_inner_product_core
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) (χ : Section1.ClassFunction G)
    (hα : CFOn L A α)
    (hχclass : Section1.IsClassFunction χ) :
    Section1.scalarProduct G (dadeTransform H hAL α) χ =
      Section1.scalarProduct L α (dadeAveragingFunction L H χ) := by
  have havg :
      Section1.scalarProduct G (dadeTransform H hAL α) χ =
        Section1.scalarProduct L α (dadeAveragingFunction L H χ) := by
    -- PF (2.7): partition the Dade support into the `L`-classes in `A`.
    classical
    rcases exists_representative_system_for_lconjugate_elements A L with
      ⟨areps, harepsA, hareps⟩
    let piece : G → Finset G := fun a => (conjugateSet (cosetProduct a (H a))).toFinset
    let repL : G → L := fun a =>
      if ha : a ∈ areps then ⟨a, hAL a (harepsA a ha)⟩ else 1
    have hpiece_pair :
        ((areps : Set G)).PairwiseDisjoint piece := by
      intro a ha b hb hab
      change Disjoint (piece a) (piece b)
      rw [Finset.disjoint_left]
      intro g hga hgb
      apply hab
      have haA : a ∈ A := harepsA a ha
      have hbA : b ∈ A := harepsA b hb
      have hmeet :
          (conjugateSet (cosetProduct a (H a)) ∩
            conjugateSet (cosetProduct b (H b))).Nonempty := by
        refine ⟨g, ?_, ?_⟩
        · simpa [piece] using hga
        · simpa [piece] using hgb
      have hconj : conjugateInSubgroup L a b :=
        (proposition_2_4 A L H).2.1 h haA hbA hmeet
      have ha_rep :
          a = (Classical.choose (hareps a haA)) :=
        (Classical.choose_spec (hareps a haA)).2.2
          a ha (conjugateInSubgroup_refl L a)
      have hb_rep :
          b = (Classical.choose (hareps a haA)) :=
        (Classical.choose_spec (hareps a haA)).2.2 b hb hconj
      exact ha_rep.trans hb_rep.symm
    have hunion :
        (areps.biUnion piece) = (dadeSupport A H).toFinset := by
      ext g
      constructor
      · intro hg
        rw [Finset.mem_biUnion] at hg
        rcases hg with ⟨a, ha, hga⟩
        have haA : a ∈ A := harepsA a ha
        have hgset :
            g ∈ conjugateSet (cosetProduct a (H a)) := by
          simpa [piece] using hga
        exact (Set.mem_toFinset).2
          (conjugateSet_cosetProduct_subset_dadeSupport (A := A) (H := H) haA hgset)
      · intro hg
        have hgS : g ∈ dadeSupport A H := (Set.mem_toFinset).1 hg
        rcases hgS with ⟨a, haA, k, hk, hconj⟩
        rcases hareps a haA with ⟨b, hb, hba, _huniq⟩
        have hbA : b ∈ A := harepsA b hb
        have hpiece_eq :
            conjugateSet (cosetProduct a (H a)) =
              conjugateSet (cosetProduct b (H b)) := by
          exact (conjugateSet_cosetProduct_eq_of_lconj (h := h) haA hba).symm
        rw [Finset.mem_biUnion]
        refine ⟨b, hb, ?_⟩
        have hga :
            g ∈ conjugateSet (cosetProduct a (H a)) :=
          dadeSupport_piece_mem_conjugateSet hk hconj
        have hgb :
            g ∈ conjugateSet (cosetProduct b (H b)) := by
          simpa [hpiece_eq] using hga
        exact (Set.mem_toFinset).2 hgb
    have hleft_sum :
        ∑ g : G, dadeTransform H hAL α g * star (χ g) =
          ∑ a ∈ areps,
            ∑ g : conjugateSet (cosetProduct a (H a)),
              dadeTransform H hAL α (g : G) * star (χ (g : G)) := by
      have hsupport_sum :
          ∑ g : G, dadeTransform H hAL α g * star (χ g) =
            ∑ g ∈ (dadeSupport A H).toFinset,
              dadeTransform H hAL α g * star (χ g) := by
        have hS : (dadeSupport A H).Finite := by
          refine (Set.finite_univ : (Set.univ : Set G).Finite).subset ?_
          intro g hg
          trivial
        rw [← Finset.sum_subset (Finset.subset_univ (dadeSupport A H).toFinset)]
        intro g _hg hgnot
        have hgS : g ∉ dadeSupport A H := by
          intro hgS
          exact hgnot (by simpa using hgS)
        change dadeTransform H hAL α g * star (χ g) = 0
        rw [dadeTransform_eq_zero_of_not_mem_support H hAL α hgS]
        simp
      calc
        ∑ g : G, dadeTransform H hAL α g * star (χ g) =
            ∑ g ∈ (dadeSupport A H).toFinset,
              dadeTransform H hAL α g * star (χ g) := hsupport_sum
        _ = ∑ g ∈ areps.biUnion piece,
              dadeTransform H hAL α g * star (χ g) := by
          rw [hunion]
        _ = ∑ a ∈ areps, ∑ g ∈ piece a,
              dadeTransform H hAL α g * star (χ g) := by
          simpa [piece] using (Finset.sum_biUnion hpiece_pair
            (f := fun g : G => dadeTransform H hAL α g * star (χ g)))
        _ = ∑ a ∈ areps,
            ∑ g : conjugateSet (cosetProduct a (H a)),
              dadeTransform H hAL α (g : G) * star (χ (g : G)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          letI : Fintype (conjugateSet (cosetProduct a (H a))) :=
            Subtype.fintype _
          rw [show
              ∑ g ∈ piece a, dadeTransform H hAL α g * star (χ g) =
                ∑ g : conjugateSet (cosetProduct a (H a)),
                  dadeTransform H hAL α (g : G) * star (χ (g : G)) by
                simpa [piece] using
                  (Finset.sum_subtype
                    (s := (conjugateSet (cosetProduct a (H a))).toFinset)
                    (p := fun g : G => g ∈ conjugateSet (cosetProduct a (H a)))
                    (by intro g; simp)
                    (fun g : G => dadeTransform H hAL α g * star (χ g)))]
    have hsum_to_A :
        ∑ a ∈ areps,
          ∑ g : conjugateSet (cosetProduct a (H a)),
            dadeTransform H hAL α (g : G) * star (χ (g : G)) =
          ∑ a ∈ areps,
            (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) *
                star (dadeAveragingFunction L H χ (repL a)) * α (repL a) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have haA : a ∈ A := harepsA a ha
      have hrepL : repL a = ⟨a, hAL a haA⟩ := by
        simp [repL, ha]
      have hsum_piece :=
        sum_conjugateSet_cosetProduct_star_eq_orbit_h_avg
          (A := A) (L := L) (H := H) h hAL χ hχclass haA
      have hda :
          ∑ g : conjugateSet (cosetProduct a (H a)),
            dadeTransform H hAL α (g : G) * star (χ (g : G)) =
            α ⟨a, hAL a haA⟩ *
              ((Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                (Nat.card (H a) : ℂ) *
                  star (dadeAveragingFunction L H χ ⟨a, hAL a haA⟩)) := by
        calc
          ∑ g : conjugateSet (cosetProduct a (H a)),
              dadeTransform H hAL α (g : G) * star (χ (g : G)) =
              ∑ g : conjugateSet (cosetProduct a (H a)),
                α ⟨a, hAL a haA⟩ * star (χ (g : G)) := by
                refine Finset.sum_congr rfl ?_
                intro g hg
                rw [dadeTransform_eq_on_conjugateSet_cosetProduct
                  (A := A) (L := L) (H := H) h hAL α hα.1 haA g.2]
          _ = α ⟨a, hAL a haA⟩ *
                ∑ g : conjugateSet (cosetProduct a (H a)), star (χ (g : G)) := by
                rw [← Finset.mul_sum]
          _ = α ⟨a, hAL a haA⟩ *
                ((Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                  (Nat.card (H a) : ℂ) *
                    star (dadeAveragingFunction L H χ ⟨a, hAL a haA⟩)) := by
                have hft :
                    (Subtype.fintype
                        (Membership.mem (conjugateSet (cosetProduct a (H a))))) =
                      Fintype.ofFinite (conjugateSet (cosetProduct a (H a))) := by
                  exact of_decide_eq_true rfl
                rw [hft]
                exact congrArg (fun z : ℂ => α ⟨a, hAL a haA⟩ * z) hsum_piece
      simpa [hrepL, mul_assoc, mul_left_comm, mul_comm] using hda
    have hsum_total :
        ∑ g : G, dadeTransform H hAL α g * star (χ g) =
          ∑ a ∈ areps,
            α (repL a) *
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) *
                star (dadeAveragingFunction L H χ (repL a)) := by
      calc
        ∑ g : G, dadeTransform H hAL α g * star (χ g) =
            ∑ a ∈ areps,
              ∑ g : conjugateSet (cosetProduct a (H a)),
                dadeTransform H hAL α (g : G) * star (χ (g : G)) := hleft_sum
        _ = ∑ a ∈ areps,
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                (Nat.card (H a) : ℂ) *
                  star (dadeAveragingFunction L H χ (repL a)) *
                    α (repL a) := hsum_to_A
        _ = ∑ a ∈ areps,
              α (repL a) *
                (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                (Nat.card (H a) : ℂ) *
                  star (dadeAveragingFunction L H χ (repL a)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
    let ψ : Section1.ClassFunction L := fun l =>
      α l * star (dadeAveragingFunction L H χ l)
    have hψclass : Section1.IsClassFunction ψ := by
      intro x l
      by_cases hlA : (l : G) ∈ A
      · have hαx := hα.1 x l
        have hχx :=
          dadeAveragingFunction_isClassFunction_on_A
            A L H h hAL χ hχclass l hlA x
        unfold ψ
        rw [hαx, hχx]
      · have hxnorm := h.L_le_normalizer x.2
        have hxnot : ((x * l * x⁻¹ : L) : G) ∉ A := by
          intro hxA
          have hxA' : conjBy (x : G) (l : G) ∈ A := by
            simpa [conjBy] using hxA
          exact hlA ((hxnorm (l : G)).1 hxA')
        simp [ψ, hα.2 l hlA, hα.2 (x * l * x⁻¹) hxnot]
    let AinL : Set L := {l | (l : G) ∈ A}
    let orbitPieceL : G → Finset L := fun a =>
      (MulAction.orbit (ConjAct L) (repL a)).toFinset
    have orbit_mem_conjugateInSubgroup
        {a : G} (ha : a ∈ areps) {l : L}
        (hl : l ∈ orbitPieceL a) :
        conjugateInSubgroup L a (l : G) := by
      have haA : a ∈ A := harepsA a ha
      have hrepL : repL a = ⟨a, hAL a haA⟩ := by
        simp [repL, ha]
      have hlSet : l ∈ MulAction.orbit (ConjAct L) (repL a) := by
        simpa [orbitPieceL] using (Set.mem_toFinset.mp hl)
      rcases (MulAction.mem_orbit_iff.mp hlSet) with ⟨x, hx⟩
      refine ⟨ConjAct.ofConjAct x, ?_⟩
      have hxval := congrArg (fun y : L => (y : G)) hx
      simpa [hrepL, ConjAct.smul_def, conjBy] using hxval
    have horbit_pair :
        ((areps : Set G)).PairwiseDisjoint orbitPieceL := by
      intro a ha b hb hab
      change Disjoint (orbitPieceL a) (orbitPieceL b)
      rw [Finset.disjoint_left]
      intro l hla hlb
      apply hab
      have haA : a ∈ A := harepsA a ha
      have hconj_a_l : conjugateInSubgroup L a (l : G) :=
        orbit_mem_conjugateInSubgroup ha hla
      have hconj_b_l : conjugateInSubgroup L b (l : G) :=
        orbit_mem_conjugateInSubgroup hb hlb
      have hconj_a_b : conjugateInSubgroup L a b :=
        conjugateInSubgroup_trans hconj_a_l
          (conjugateInSubgroup_symm hconj_b_l)
      have ha_rep :
          a = (Classical.choose (hareps a haA)) :=
        (Classical.choose_spec (hareps a haA)).2.2
          a ha (conjugateInSubgroup_refl L a)
      have hb_rep :
          b = (Classical.choose (hareps a haA)) :=
        (Classical.choose_spec (hareps a haA)).2.2 b hb hconj_a_b
      exact ha_rep.trans hb_rep.symm
    have horbit_union :
        areps.biUnion orbitPieceL = AinL.toFinset := by
      ext l
      constructor
      · intro hl
        rw [Finset.mem_biUnion] at hl
        rcases hl with ⟨a, ha, hla⟩
        have haA : a ∈ A := harepsA a ha
        rcases orbit_mem_conjugateInSubgroup ha hla with ⟨x, hx⟩
        have hxnorm := h.L_le_normalizer x.2
        have hconjA : conjBy (x : G) a ∈ A := (hxnorm a).2 haA
        exact (Set.mem_toFinset).2 (by
          change (l : G) ∈ A
          simpa [hx] using hconjA)
      · intro hl
        have hlA : (l : G) ∈ A := by
          simpa [AinL] using (Set.mem_toFinset.mp hl)
        rcases hareps (l : G) hlA with ⟨b, hb, hconj_l_b, _huniq⟩
        have hbA : b ∈ A := harepsA b hb
        have hrepL : repL b = ⟨b, hAL b hbA⟩ := by
          simp [repL, hb]
        rw [Finset.mem_biUnion]
        refine ⟨b, hb, ?_⟩
        rcases conjugateInSubgroup_symm hconj_l_b with ⟨x, hx⟩
        apply (Set.mem_toFinset).2
        rw [MulAction.mem_orbit_iff]
        refine ⟨ConjAct.toConjAct x, ?_⟩
        apply Subtype.ext
        have hxval : conjBy (x : G) b = (l : G) := hx
        simpa [hrepL, ConjAct.toConjAct_smul, conjBy] using hxval
    have hright_sum :
        ∑ l : L, ψ l =
          ∑ a ∈ areps,
            ∑ l : MulAction.orbit (ConjAct L) (repL a), ψ (l : L) := by
      have hsupport_sum :
          ∑ l : L, ψ l = ∑ l ∈ AinL.toFinset, ψ l := by
        rw [← Finset.sum_subset (Finset.subset_univ AinL.toFinset)]
        intro l _hl hlnot
        have hlA : (l : G) ∉ A := by
          intro hlA
          exact hlnot (by simpa [AinL] using hlA)
        simp [ψ, hα.2 l hlA]
      calc
        ∑ l : L, ψ l = ∑ l ∈ AinL.toFinset, ψ l := hsupport_sum
        _ = ∑ l ∈ areps.biUnion orbitPieceL, ψ l := by
          rw [horbit_union]
        _ = ∑ a ∈ areps, ∑ l ∈ orbitPieceL a, ψ l := by
          simpa [orbitPieceL] using
            (Finset.sum_biUnion horbit_pair (f := fun l : L => ψ l))
        _ = ∑ a ∈ areps,
            ∑ l : MulAction.orbit (ConjAct L) (repL a), ψ (l : L) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simpa [orbitPieceL] using
            (Finset.sum_subtype
              (s := (MulAction.orbit (ConjAct L) (repL a)).toFinset)
              (p := fun l : L => l ∈ MulAction.orbit (ConjAct L) (repL a))
              (by intro l; simp)
              (fun l : L => ψ l))
    have hright_reps :
        ∑ l : L, α l * star (dadeAveragingFunction L H χ l) =
          ∑ a ∈ areps,
            (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
              (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) := by
      calc
        ∑ l : L, α l * star (dadeAveragingFunction L H χ l) =
            ∑ l : L, ψ l := rfl
        _ = ∑ a ∈ areps,
              ∑ l : MulAction.orbit (ConjAct L) (repL a), ψ (l : L) := hright_sum
        _ = ∑ a ∈ areps,
              (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            have hft :
                (Subtype.fintype
                    (Membership.mem (MulAction.orbit (ConjAct L) (repL a)))) =
                  Fintype.ofFinite (MulAction.orbit (ConjAct L) (repL a)) := by
              exact of_decide_eq_true rfl
            rw [hft]
            simpa [ψ] using
              (sum_orbit_conjAct_eq_card_mul L ψ hψclass (repL a))
    have hcardL : (Nat.card L : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := L)).ne'
    have hGsum :
        (Nat.card G : ℂ)⁻¹ * ∑ a ∈ areps,
          α (repL a) *
            (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
            (Nat.card (H a) : ℂ) *
              star (dadeAveragingFunction L H χ (repL a)) =
          (Nat.card G : ℂ)⁻¹ * ∑ x, dadeTransform H hAL α x * star (χ x) := by
      rw [hsum_total.symm]
    have hterm :
        ∀ a ∈ areps,
          (Nat.card G : ℂ)⁻¹ *
            (α (repL a) *
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) *
                star (dadeAveragingFunction L H χ (repL a))) =
            (Nat.card L : ℂ)⁻¹ *
              (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) := by
      intro a ha
      have haA : a ∈ A := harepsA a ha
      have hrepL : repL a = ⟨a, hAL a haA⟩ := by
        simp [repL, ha]
      have hGcoeff :
          (Nat.card G : ℂ)⁻¹ *
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) =
            (Nat.card (centralizerIn L a) : ℂ)⁻¹ := by
        have hcard :
            (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) *
                (Nat.card (centralizerIn L a) : ℂ) =
              (Nat.card G : ℂ) := by
          exact_mod_cast
            (cosetProduct_orbit_card_mul_h_card_centralizerIn (A := A) (L := L) (H := H) h haA)
        have hGne : (Nat.card G : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := G)).ne'
        have hCne : (Nat.card (centralizerIn L a) : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := centralizerIn L a)).ne'
        apply mul_right_cancel₀ hCne
        calc
          ((Nat.card G : ℂ)⁻¹ *
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ)) *
              (Nat.card (centralizerIn L a) : ℂ) =
              (Nat.card G : ℂ)⁻¹ *
                ((Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                  (Nat.card (H a) : ℂ) *
                  (Nat.card (centralizerIn L a) : ℂ)) := by
                ring
          _ = (Nat.card G : ℂ)⁻¹ * (Nat.card G : ℂ) := by rw [hcard]
          _ = (Nat.card (centralizerIn L a) : ℂ)⁻¹ *
                (Nat.card (centralizerIn L a) : ℂ) := by
                simp
      have hLcoeff :
          (Nat.card (centralizerIn L a) : ℂ)⁻¹ =
            (Nat.card L : ℂ)⁻¹ * (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) := by
        have hcard :
            (Nat.card (centralizerIn L a) : ℂ) *
              (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) =
            (Nat.card L : ℂ) := by
          have hnat := orbit_card_mul_card_centralizerIn L (repL a)
          have hcast :
              (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                  (Nat.card (centralizerIn L ((repL a : L) : G)) : ℂ) =
                (Nat.card L : ℂ) := by
            exact_mod_cast hnat
          simpa [hrepL, mul_comm, mul_left_comm, mul_assoc] using hcast
        have hLne : (Nat.card L : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := L)).ne'
        have hCne : (Nat.card (centralizerIn L a) : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := centralizerIn L a)).ne'
        apply mul_right_cancel₀ hCne
        calc
          (Nat.card (centralizerIn L a) : ℂ)⁻¹ *
              (Nat.card (centralizerIn L a) : ℂ) = 1 := by
                simp
          _ = (Nat.card L : ℂ)⁻¹ *
                (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                (Nat.card (centralizerIn L a) : ℂ) := by
                symm
                calc
                  (Nat.card L : ℂ)⁻¹ *
                      (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                      (Nat.card (centralizerIn L a) : ℂ) =
                      (Nat.card L : ℂ)⁻¹ *
                        ((Nat.card (centralizerIn L a) : ℂ) *
                          (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ)) := by
                        ring
                  _ = (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ) := by
                    rw [hcard]
                  _ = 1 := by simp
      calc
        (Nat.card G : ℂ)⁻¹ *
            (α (repL a) *
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) *
                star (dadeAveragingFunction L H χ (repL a))) =
            α (repL a) * star (dadeAveragingFunction L H χ (repL a)) *
              ((Nat.card G : ℂ)⁻¹ *
                (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                (Nat.card (H a) : ℂ)) := by
              ring
        _ = α (repL a) * star (dadeAveragingFunction L H χ (repL a)) *
              (Nat.card (centralizerIn L a) : ℂ)⁻¹ := by
              rw [hGcoeff]
        _ = (Nat.card L : ℂ)⁻¹ *
              (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) := by
              rw [hLcoeff]
              ring
    have hmid :
        (Nat.card G : ℂ)⁻¹ *
          ∑ a ∈ areps,
            α (repL a) *
              (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
              (Nat.card (H a) : ℂ) *
                star (dadeAveragingFunction L H χ (repL a)) =
        (Nat.card L : ℂ)⁻¹ *
          ∑ a ∈ areps,
            (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
              (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa [mul_assoc] using hterm a ha
    have hLsum :
        (Nat.card L : ℂ)⁻¹ *
          ∑ a ∈ areps,
            (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
              (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) =
        Section1.scalarProduct L α (dadeAveragingFunction L H χ) := by
      unfold Section1.scalarProduct
      rw [hright_reps.symm]
      have huniv :
          (@Finset.univ L inferInstance) =
            (@Finset.univ L (Fintype.ofFinite L)) := by
        ext l
        simp
      rw [huniv]
    calc
      Section1.scalarProduct G (dadeTransform H hAL α) χ =
          (Nat.card G : ℂ)⁻¹ *
            ∑ a ∈ areps,
              α (repL a) *
                (Nat.card (MulAction.orbit (ConjAct G) (cosetProduct a (H a))) : ℂ) *
                (Nat.card (H a) : ℂ) *
                  star (dadeAveragingFunction L H χ (repL a)) := by
              unfold Section1.scalarProduct
              exact hGsum.symm
      _ = (Nat.card L : ℂ)⁻¹ *
            ∑ a ∈ areps,
              (Nat.card (MulAction.orbit (ConjAct L) (repL a)) : ℂ) *
                (α (repL a) * star (dadeAveragingFunction L H χ (repL a))) := hmid
      _ = Section1.scalarProduct L α (dadeAveragingFunction L H χ) := hLsum
  exact havg

public theorem theorem_2_6_inner_product_restrict_core
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) (χ : Section1.ClassFunction G)
    (hα : CFOn L A α)
    (hχclass : Section1.IsClassFunction χ)
    (hχ : constantOnDadeCosets A H χ) :
    Section1.scalarProduct G (dadeTransform H hAL α) χ =
      Section1.scalarProduct L α (Section1.subgroupRestriction L χ) := by
  calc
    Section1.scalarProduct G (dadeTransform H hAL α) χ =
        Section1.scalarProduct L α (dadeAveragingFunction L H χ) := by
          exact theorem_2_6_inner_product_core A L H h hAL α χ hα hχclass
    _ = Section1.scalarProduct L α (Section1.subgroupRestriction L χ) := by
          exact scalarProduct_dadeAveraging_eq_restrict_of_constant
            A L H α χ hα hχ

private theorem theorem_2_6_virtual_closure_core
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) :
    virtualCharacterOn L A α →
      virtualCharacterOfG (dadeTransform H hAL α) := by
  intro hα
  classical
  have hinclusion :
      ∃ reps : Finset (Set G),
        ∃ αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B),
          IsRepresentativeSystemForNonemptySubsets A L reps ∧
            (∀ B ∈ reps, alphaBSpec H α B (αB B)) ∧
            (∀ B ∈ reps,
              Theory.Character.IsVirtualCharacter (αB B)) ∧
            dadeTransform H hAL α =
              dadeInclusionExclusionSum L H reps αB := by
    -- PF (2.9): choose representatives and define `α_B` by the semidirect
    -- projection `M(B) → N_L(B) ≤ L`.
    rcases exists_representative_system_for_nonempty_subsets (A := A) L with
      ⟨reps, hreps⟩
    let αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B) := fun B =>
      if hB : B.Nonempty ∧ B ⊆ A then
        alphaBFromProjection A L H h hB.1 hB.2 α
      else
        0
    have hαBspec : ∀ B ∈ reps, alphaBSpec H α B (αB B) := by
      intro B hBmem
      have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
      dsimp [αB]
      rw [dif_pos hBprops]
      exact alphaBFromProjection_spec A L H h hBprops.1 hBprops.2 α
    have hαBvirt :
        ∀ B ∈ reps, Theory.Character.IsVirtualCharacter (αB B) := by
      intro B hBmem
      have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
      dsimp [αB]
      rw [dif_pos hBprops]
      exact alphaBFromProjection_isVirtualCharacter A L H h
        hBprops.1 hBprops.2 α hα.1
    have hformula :
        dadeTransform H hAL α = dadeInclusionExclusionSum L H reps αB := by
      -- PF (2.10): compare pointwise, first off the Dade support by (2.10.3).
      ext g
      by_cases hg : g ∈ dadeSupport A H
      ·
        -- The remaining branch is the inclusion-exclusion cancellation on
        -- `g ∈ (aH(a))^G`, using (2.10.1), (2.10.2), and (2.10.3).
        rcases hg with ⟨a, ha, h₀, hh₀, hconj⟩
        have hgpiece : g ∈ conjugateSet (cosetProduct a (H a)) :=
          dadeSupport_piece_mem_conjugateSet hh₀ hconj
        have hleft :
          dadeTransform H hAL α g =
              α ⟨a, hAL a ha⟩ := by
          exact dadeTransform_eq_on_conjugateSet_cosetProduct
            A L H h hAL α (CFOn_of_virtualCharacterOn L A α hα).1
            ha hgpiece
        have hterm :
            ∀ B ∈ reps,
              Section1.inducedCF (MOfSet H L B) (αB B) g =
                dadeInductionFormulaTerm A L H α g a B hAL ha := by
          intro B hBmem
          have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
          exact inducedCF_alphaB_support_piece_formula
            (A := A) (L := L) (H := H) h hBprops.1 hBprops.2
            (CFOn_of_virtualCharacterOn L A α hα).1 hα.2
            (hαBspec B hBmem) ha hgpiece
        have hsum :
            dadeInclusionExclusionSum L H reps αB g =
              -(reps.sum fun B =>
                ((-1 : ℂ) ^ Nat.card B) *
                  dadeInductionFormulaTerm A L H α g a B hAL ha) := by
          unfold dadeInclusionExclusionSum
          congr 1
          refine Finset.sum_congr rfl ?_
          intro B hBmem
          rw [hterm B hBmem]
        have hcancel :
            (reps.sum fun B =>
              ((-1 : ℂ) ^ Nat.card B) *
                dadeInductionFormulaTerm A L H α g a B hAL ha) =
              -(dadeTransform H hAL α g) := by
          rw [hleft]
          exact dadeInductionFormulaTerm_representative_sum_support_cancel
            A L H h hAL hreps α (CFOn_of_virtualCharacterOn L A α hα)
            ha hgpiece
        calc
          dadeTransform H hAL α g = dadeTransform H hAL α g := rfl
          _ = dadeInclusionExclusionSum L H reps αB g := by
            rw [hsum]
            rw [hcancel]
            ring
      ·
        have hleft : dadeTransform H hAL α g = 0 :=
          dadeTransform_eq_zero_of_not_mem_support H hAL α hg
        have hsum :
            reps.sum (fun B =>
              ((-1 : ℂ) ^ Nat.card B) *
                Section1.inducedCF (MOfSet H L B) (αB B) g) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro B hBmem
          have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
          have hterm :
              Section1.inducedCF (MOfSet H L B) (αB B) g = 0 :=
            inducedCF_alphaB_eq_zero_of_not_mem_dadeSupport
              (A := A) (L := L) (H := H) h hBprops.1 hBprops.2
              hα.2 (hαBspec B hBmem) hg
          rw [hterm, mul_zero]
        calc
          dadeTransform H hAL α g = 0 := hleft
          _ = dadeInclusionExclusionSum L H reps αB g := by
            rw [dadeInclusionExclusionSum, hsum]
            simp
    exact ⟨reps, αB, hreps, hαBspec, hαBvirt, hformula⟩
  rcases hinclusion with ⟨reps, αB, _hreps, _hαBspec, hαBvirt, hformula⟩
  rw [hformula]
  exact dadeInclusionExclusionSum_isVirtualCharacter L H reps αB hαBvirt

public theorem theorem_2_6 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) :
    theorem_2_6_statement A L H h hAL := by
  change
    (∀ α β : Section1.ClassFunction L,
        CFOn L A α → CFOn L A β →
          Section1.scalarProduct G (dadeTransform H hAL α) (dadeTransform H hAL β) =
            Section1.scalarProduct L α β) ∧
      (∀ α : Section1.ClassFunction L,
        virtualCharacterOn L A α →
          virtualCharacterOfG (dadeTransform H hAL α))
  constructor
  · intro α β hα hβ
    calc
      Section1.scalarProduct G (dadeTransform H hAL α) (dadeTransform H hAL β) =
          Section1.scalarProduct L α
            (Section1.subgroupRestriction L (dadeTransform H hAL β)) := by
            exact theorem_2_6_inner_product_restrict_core A L H h hAL α
              (dadeTransform H hAL β) hα
              (dadeTransform_isClassFunction_of_CFOn A L H h hAL β hβ)
              (theorem_2_6_transform_constant_on_dade_cosets A L H h hAL β hβ)
      _ = Section1.scalarProduct L α β := by
            exact scalarProduct_restrict_dadeTransform_eq_of_support
              A L H h hAL α β hα hβ
  · intro α hα
    exact theorem_2_6_virtual_closure_core A L H h hAL α hα

private theorem proposition_2_7 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) :
    proposition_2_7_statement A L H h hAL := by
  have hstmt :
      ∀ (α : Section1.ClassFunction L) (χ : Section1.ClassFunction G),
        CFOn L A α →
          Section1.IsClassFunction χ →
            ∀ ψ : Section1.ClassFunction L,
              Section1.IsClassFunction ψ →
                (∀ ⦃a : G⦄, (ha : a ∈ A) →
                  ψ ⟨a, hAL a ha⟩ = dadeAveragingFunction L H χ ⟨a, hAL a ha⟩) →
                  Section1.scalarProduct G (dadeTransform H hAL α) χ =
                    Section1.scalarProduct L α ψ ∧
                  (constantOnDadeCosets A H χ →
                    Section1.scalarProduct G (dadeTransform H hAL α) χ =
                      Section1.scalarProduct L α (Section1.subgroupRestriction L χ)) := by
    intro α χ hα hχclass ψ _hψclass hψ
    constructor
    · calc
        Section1.scalarProduct G (dadeTransform H hAL α) χ =
            Section1.scalarProduct L α (dadeAveragingFunction L H χ) := by
          exact theorem_2_6_inner_product_core A L H h hAL α χ hα hχclass
        _ = Section1.scalarProduct L α ψ := by
          exact scalarProduct_right_congr_on_left_support
            (A := {l : L | (l : G) ∈ A}) (φ := α)
            (ψ := dadeAveragingFunction L H χ) (χ := ψ)
            (by
              intro l hlA
              exact hα.2 l hlA)
            (by
              intro l hlA
              have hsub : (⟨(l : G), hAL (l : G) hlA⟩ : L) = l := by
                ext
                rfl
              simpa [hsub] using (hψ (a := (l : G)) hlA).symm)
    · intro hχ
      exact theorem_2_6_inner_product_restrict_core A L H h hAL α χ hα hχclass hχ
  simpa [proposition_2_7_statement] using hstmt


private theorem proposition_2_11 {G : Type u} [Group G] [Finite G]
    (A A1 : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G) :
    proposition_2_11_statement A A1 L H := by
  have hstmt :
      A1 ⊆ A →
        L ≤ setNormalizer A1 →
          Hypothesis2 A L H →
            Hypothesis2 A1 L H ∧
              ∀ (hAL : ∀ a ∈ A, a ∈ L) (hA1L : ∀ a ∈ A1, a ∈ L),
                ∀ α : Section1.ClassFunction L,
                  CFOn L A1 α →
                    dadeTransform H hAL α = dadeTransform H hA1L α := by
    intro hsub hnorm h
    let hA1 : Hypothesis2 A1 L H := proposition_2_11_hypothesis h hsub hnorm
    refine ⟨hA1, ?_⟩
    intro hAL hA1L α hα
    have hαA : CFOn L A α := by
      refine ⟨hα.1, ?_⟩
      intro l hlA
      exact hα.2 l (by
        intro hlA1
        exact hlA (hsub hlA1))
    ext g
    by_cases hgA1 : g ∈ dadeSupport A1 H
    · rcases hgA1 with ⟨a, ha1, h₀, hh₀, hconj⟩
      have ha : a ∈ A := hsub ha1
      have hleft :
          dadeTransform H hAL α g = α ⟨a, hAL a ha⟩ :=
        ((definition_2_5 A L H h hAL α hαA).1)
          (g := g) (a := a) (h' := h₀) ha hh₀ hconj
      have hright :
          dadeTransform H hA1L α g = α ⟨a, hA1L a ha1⟩ :=
        ((definition_2_5 A1 L H hA1 hA1L α hα).1)
          (g := g) (a := a) (h' := h₀) ha1 hh₀ hconj
      have hsubeq : (⟨a, hAL a ha⟩ : L) = ⟨a, hA1L a ha1⟩ := by
        ext
        rfl
      have hright' :
          dadeTransform H hA1L α g = α ⟨a, hAL a ha⟩ := by
        simpa [← hsubeq] using hright
      exact hleft.trans hright'.symm
    · have hright : dadeTransform H hA1L α g = 0 :=
        (definition_2_5 A1 L H hA1 hA1L α hα).2 g hgA1
      by_cases hgA : g ∈ dadeSupport A H
      · rcases hgA with ⟨a, ha, h₀, hh₀, hconj⟩
        have ha1not : a ∉ A1 := by
          intro ha1
          exact hgA1 ⟨a, ha1, h₀, hh₀, hconj⟩
        have hleft :
            dadeTransform H hAL α g = α ⟨a, hAL a ha⟩ :=
          ((definition_2_5 A L H h hAL α hαA).1)
            (g := g) (a := a) (h' := h₀) ha hh₀ hconj
        have hzero : α ⟨a, hAL a ha⟩ = 0 :=
          hα.2 ⟨a, hAL a ha⟩ ha1not
        rw [hleft, hzero, hright]
      · have hleft : dadeTransform H hAL α g = 0 :=
          (definition_2_5 A L H h hAL α hαA).2 g hgA
        rw [hleft, hright]
  simpa [proposition_2_11_statement] using hstmt

end CFSG.Section2
