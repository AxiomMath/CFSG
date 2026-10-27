module

public import CFSG.RankThree.PartOne.KE.A1Group
public import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (baseChangeGL_mem_torusGroup mem_torusGroup_of_baseChangeGL_mem)

section Twisted

variable {τ : Tag} {L : Type} [Field L]

@[expose] def twistedTorusOf (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L) :
    Subgroup (ModGL τ L) :=
  torusGroup τ L ⊓ ((MulAut.conj n).toMonoidHom.comp Φ).eqLocus (MonoidHom.id _)

theorem mem_twistedTorusOf {n : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L} {x : ModGL τ L} :
    x ∈ twistedTorusOf n Φ ↔ x ∈ torusGroup τ L ∧ n * Φ x * n⁻¹ = x :=
  Iff.rfl

abbrev twistedTorus (n : ModGL τ L) (Fr : L →+* L) : Subgroup (ModGL τ L) :=
  twistedTorusOf n (Units.map (entrywiseHom Fr))

theorem mem_twistedTorus {n : ModGL τ L} {Fr : L →+* L} {x : ModGL τ L} :
    x ∈ twistedTorus n Fr ↔
      x ∈ torusGroup τ L ∧ n * Units.map (entrywiseHom Fr) x * n⁻¹ = x :=
  Iff.rfl

theorem torusGroup_le_adjointGroup' : torusGroup τ L ≤ adjointGroup τ L :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem twistedTorusOf_le_adjointGroup (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L) :
    twistedTorusOf n Φ ≤ adjointGroup τ L :=
  inf_le_left.trans torusGroup_le_adjointGroup'

end Twisted


theorem natCard_fixSubfield_eq_of_frobenius {K L : Type} [Field K] [Finite K]
    [Field L] [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (E : Subfield L) [Finite E] (hKE : Set.range (algebraMap K L) ⊆ E)
    (σE : E ≃+* E) (hσ : ∀ e : E, (σE e : L) = Fr e) :
    Nat.card (fixSubfield σE) = Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hq : 1 < Nat.card K := Finite.one_lt_card
  refine le_antisymm ?_ ?_
  · let P : Polynomial L := Polynomial.X ^ Nat.card K - Polynomial.X
    have hdeg : P.natDegree = Nat.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq L hq
    have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
    let f : fixSubfield σE → P.roots.toFinset := fun x => ⟨((x : E) : L), by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
      have h1 : σE (x : E) = x := (mem_fixSubfield σE).1 x.2
      have h2 : ((x : E) : L) ^ Nat.card K = ((x : E) : L) := by
        rw [← hFr, ← hσ, h1]
      simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [h2, sub_self]⟩
    have hf : Function.Injective f := fun x y hxy => by
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
    calc Nat.card (fixSubfield σE) ≤ Nat.card P.roots.toFinset :=
          Nat.card_le_card_of_injective f hf
      _ = P.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = Nat.card K := hdeg
  · let g : K → fixSubfield σE := fun a =>
      ⟨⟨algebraMap K L a, hKE ⟨a, rfl⟩⟩, by
        refine (mem_fixSubfield σE).2 (Subtype.ext ?_)
        rw [hσ, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]⟩
    have hg : Function.Injective g := fun a b hab => by
      have := congrArg (fun x : fixSubfield σE => ((x : E) : L)) hab
      exact (algebraMap K L).injective this
    exact Nat.card_le_card_of_injective g hg

section Rational

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

theorem finite_fixed_subgroup_rational_perfect_card_units (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL τ L)) [Finite X]
    (hXC : X ≤ adjointGroup τ L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ d ∧
      (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
        P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) ∧
      (∀ P : Subgroup (ModGL τ L), P ≤ X → ⁅P, P⁆ = P →
        P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) ∧
      ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣
        (Nat.card K - 1) ^ τ.rank := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hdesc : ∀ x : X, ∃ S : Finset L, ∀ E : Subfield L, (S : Set L) ⊆ E →
      ∃ y ∈ adjointGroup τ E, baseChangeGL E.subtype y = (x : ModGL τ L) :=
    fun x => CFSG.LieType.Chevalley.exists_finset_descent (hXC x.2)
  choose Sx hSx using hdesc
  obtain ⟨E, hEf, hSE, hKE⟩ :=
    exists_finite_subfield_of_finset (K := K) (L := L) (Finset.univ.biUnion Sx)
  have : Finite E := hEf
  have hSE' : ∀ x : X, (Sx x : Set L) ⊆ E := fun x a ha =>
    hSE (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Finset.mem_coe.1 ha⟩))
  obtain ⟨σE, hσE, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
  obtain ⟨-, hCart⟩ := ordinary_E_algebraic_torus_and_finite_fixed_group_Cartan_index τ d hτ
  obtain ⟨-, hJn, hidx, hpgrp⟩ := hCart E σE
  have hιE : Function.Injective (baseChangeGL (τ := τ) E.subtype) :=
    baseChangeGL_injective E.subtype
  set A : Subgroup (ModGL τ E) :=
    X.comap (baseChangeGL E.subtype) ⊓ adjointGroup τ E with hA
  have hXA : X = A.map (baseChangeGL E.subtype) := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨y, hy, hyx⟩ := hSx ⟨x, hx⟩ E (hSE' ⟨x, hx⟩)
      refine ⟨y, ⟨?_, hy⟩, hyx⟩
      have h1 : baseChangeGL E.subtype y = x := hyx
      show baseChangeGL E.subtype y ∈ X
      rw [h1]
      exact hx
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
  have hAΓ : A ≤ entrywiseFixedGroup τ σE := fun y hy =>
    hfix y hy.2 (hXF _ hy.1)
  have hrel : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X =
      ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).relIndex
        (A.subgroupOf (entrywiseFixedGroup τ σE)) := by
    rw [← hJ, hXA, Subgroup.relIndex_map_map_of_injective _ _ hιE]
    exact (Subgroup.relIndex_subgroupOf hAΓ).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrel]
    have := hJn
    exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hidx
  · intro p hp hp3 P hPX hP
    have hPA : P.comap (baseChangeGL E.subtype) ≤ A := by
      intro y hy
      have hy' : baseChangeGL E.subtype y ∈ X := hPX hy
      rw [hXA] at hy'
      obtain ⟨y', hy'A, hyy'⟩ := hy'
      have := hιE hyy'
      subst this
      exact hy'A
    have hPE : IsPGroup p (P.comap (baseChangeGL E.subtype)) := hP.comap_of_injective _ hιE
    have hle := hpgrp p hp hp3 _ (hPA.trans hAΓ) hPE
    intro x hx
    have hxX : x ∈ A.map (baseChangeGL E.subtype) := hXA ▸ hPX hx
    obtain ⟨y, -, rfl⟩ := hxX
    rw [← hJ]
    exact ⟨y, hle hx, rfl⟩
  · intro P hPX hPperf
    have hPA : P.comap (baseChangeGL E.subtype) ≤ A := by
      intro y hy
      have hy' : baseChangeGL E.subtype y ∈ X := hPX hy
      rw [hXA] at hy'
      obtain ⟨y', hy'A, hyy'⟩ := hy'
      have := hιE hyy'
      subst this
      exact hy'A
    have hPrange : P ≤ (baseChangeGL (τ := τ) E.subtype).range := fun x hx => by
      have hxX : x ∈ A.map (baseChangeGL E.subtype) := hXA ▸ hPX hx
      obtain ⟨y, -, rfl⟩ := hxX
      exact ⟨y, rfl⟩
    have hPmap : (P.comap (baseChangeGL E.subtype)).map (baseChangeGL E.subtype) = P := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hPrange]
    have hPperf' : ⁅P.comap (baseChangeGL E.subtype), P.comap (baseChangeGL E.subtype)⁆ =
        P.comap (baseChangeGL E.subtype) := by
      apply Subgroup.map_injective hιE
      rw [Subgroup.map_commutator, hPmap, hPperf]
    have hindexpos : 0 < ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).index := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      rw [h0, zero_dvd_iff] at hidx
      rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp at hidx
    have hindexle : ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).index ≤ 3 := by
      refine (Nat.le_of_dvd (by omega) hidx).trans ?_
      rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    have hP'Γ : P.comap (baseChangeGL E.subtype) ≤ entrywiseFixedGroup τ σE := hPA.trans hAΓ
    have hsubperf : ⁅(P.comap (baseChangeGL E.subtype)).subgroupOf (entrywiseFixedGroup τ σE),
        (P.comap (baseChangeGL E.subtype)).subgroupOf (entrywiseFixedGroup τ σE)⁆ =
        (P.comap (baseChangeGL E.subtype)).subgroupOf (entrywiseFixedGroup τ σE) := by
      apply Subgroup.map_injective (entrywiseFixedGroup τ σE).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP'Γ, hPperf']
    have hle := le_of_perfect_of_index_le_three _ hindexpos hindexle _ hsubperf
    intro x hx
    have hxX : x ∈ A.map (baseChangeGL E.subtype) := hXA ▸ hPX hx
    obtain ⟨y, hyA, rfl⟩ := hxX
    have hyP : y ∈ P.comap (baseChangeGL E.subtype) := hx
    have h1 : (⟨y, hP'Γ hyP⟩ : entrywiseFixedGroup τ σE) ∈
        (P.comap (baseChangeGL E.subtype)).subgroupOf (entrywiseFixedGroup τ σE) := hyP
    have h2 := hle h1
    rw [← hJ]
    exact ⟨y, h2, rfl⟩
  · have hfixcard : Nat.card (fixSubfield σE) = Nat.card K :=
      natCard_fixSubfield_eq_of_frobenius Fr hFr E hKE σE hσE
    have hcard := fixedFieldImage_index_dvd_card_units (τ := τ) σE
    rw [hfixcard] at hcard
    rw [hrel]
    have := hJn
    exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hcard


theorem finite_fixed_subgroup_rational_perfect (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL τ L)) [Finite X]
    (hXC : X ≤ adjointGroup τ L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ d ∧
      (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
        P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) ∧
      ∀ P : Subgroup (ModGL τ L), P ≤ X → ⁅P, P⁆ = P →
        P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  let h := finite_fixed_subgroup_rational_perfect_card_units d hτ Fr hFr X hXC hXF
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem finite_fixed_subgroup_rational_perfect_relIndex_card_units (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL τ L)) [Finite X]
    (hXC : X ≤ adjointGroup τ L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣
      (Nat.card K - 1) ^ τ.rank := by
  exact (finite_fixed_subgroup_rational_perfect_card_units d hτ Fr hFr X hXC hXF).2.2.2

theorem finite_fixed_subgroup_rational_card_dvd (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL τ L)) [Finite X]
    (hXC : X ≤ adjointGroup τ L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x)
    {m : ℕ} (hm : Nat.Coprime m (Nat.card K - 1)) (hmX : Nat.card X ∣ m) :
    X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  classical
  obtain ⟨-, -, -, hidxCard⟩ :=
    finite_fixed_subgroup_rational_perfect_card_units d hτ Fr hFr X hXC hXF
  have hidxX : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣
      Nat.card X := Subgroup.relIndex_dvd_card _ _
  have hidxM : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ m :=
    hidxX.trans hmX
  have hcop : Nat.Coprime
      (((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X)
      (Nat.card K - 1) :=
    Nat.Coprime.of_dvd_left hidxM hm
  have hrankpos : 0 < τ.rank := by
    rcases hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hcopPow : Nat.Coprime
      (((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X)
      ((Nat.card K - 1) ^ τ.rank) :=
    (Nat.coprime_pow_right_iff hrankpos _ _).2 hcop
  have hone : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopPow (dvd_refl _) hidxCard
  exact Subgroup.relIndex_eq_one.1 hone

theorem frobenius_fixed_pow_card_add_one_mem_baseChange [CharP K 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {x : ModGL .E6 L}
    (hxC : x ∈ adjointGroup .E6 L) (hxF : Units.map (entrywiseHom Fr) x = x)
    (hxq : x ^ (Nat.card K + 1) = 1) :
    x ∈ (adjointGroup .E6 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  let X : Subgroup (ModGL .E6 L) := Subgroup.zpowers x
  have horder : orderOf x ∣ Nat.card K + 1 := orderOf_dvd_of_pow_eq_one hxq
  have hXcard : Nat.card X = orderOf x := Nat.card_zpowers x
  have hXfin : Finite X := by
    apply Nat.finite_of_card_ne_zero
    rw [hXcard]
    intro h0
    have hzero : Nat.card K + 1 = 0 := by
      have := horder
      rw [h0] at this
      exact zero_dvd_iff.1 this
    omega
  haveI : Finite X := hXfin
  have hXC : X ≤ adjointGroup .E6 L := Subgroup.zpowers_le.2 hxC
  have hXF : ∀ y ∈ X, Units.map (entrywiseHom Fr) y = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow, hxF]
  have hEven : Even (Nat.card K) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hKcard⟩ := FiniteField.card (K := K) 2
    rw [Nat.card_eq_fintype_card, hKcard]
    exact Nat.even_pow.2 ⟨by norm_num, n.pos.ne'⟩
  have hOdd : Odd (Nat.card K + 1) :=
    Nat.not_even_iff_odd.1 fun h => (Nat.even_add_one.1 h) hEven
  have hcop2 : Nat.Coprime (Nat.card K + 1) 2 := by
    rw [Nat.coprime_comm]
    exact Nat.coprime_two_left.2 hOdd
  have hqpos : 0 < Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.2 ⟨(0 : K)⟩
  have hcop : Nat.Coprime (Nat.card K + 1) (Nat.card K - 1) := by
    have h := (Nat.coprime_self_sub_right (m := 2) (n := Nat.card K + 1) (by omega)).2 hcop2
    rwa [show Nat.card K + 1 - 2 = Nat.card K - 1 by omega] at h
  have hmX : Nat.card X ∣ Nat.card K + 1 := by rw [hXcard]; exact horder
  have hXle : X ≤ (adjointGroup .E6 K).map (baseChangeGL (algebraMap K L)) :=
    finite_fixed_subgroup_rational_card_dvd (τ := .E6) 3 (Or.inl ⟨rfl, rfl⟩) Fr hFr X
      hXC hXF (m := Nat.card K + 1) hcop hmX
  exact hXle (Subgroup.mem_zpowers x)

theorem finite_fixed_subgroup_rational (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL τ L)) [Finite X]
    (hXC : X ≤ adjointGroup τ L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ d ∧
      ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
        P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
  let h := finite_fixed_subgroup_rational_perfect d hτ Fr hFr X hXC hXF
  ⟨h.1, h.2.1⟩

end Rational

section Regular

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_map_tuple {τ : Tag} {R S : Type} [Field R] [Field S] (f : R →+* S)
    (b : Fin τ.rank → Rˣ) (α : Fin τ.rank → ℤ) :
    rootChar (fun i => Units.map f.toMonoidHom (b i)) α =
      Units.map f.toMonoidHom (rootChar b α) := by
  simp only [rootChar, map_prod, map_zpow]

theorem torus_of_commuting_regular (K : Type) [Field K] [Finite K] [Algebra K L]
    [Algebra.IsAlgebraic K L] {p : ℕ} (hp : p.Prime)
    (hcent : ∀ (M : Type) [Field M] [Finite M], p ∣ Nat.card Mˣ → ∀ {x : ModGL τ M},
      x ∈ torusGroup τ M → orderOf x = p →
      (∀ a : Fin τ.rank → Mˣ, x = rootDiagUnit τ a →
        ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) →
      adjointGroup τ M ⊓ Subgroup.centralizer {x} = torusGroup τ M)
    {x : ModGL τ L} (hxH : x ∈ torusGroup τ L) (hxp : orderOf x = p)
    (hreg : ∀ a : Fin τ.rank → Lˣ, x = rootDiagUnit τ a →
      ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1)
    {y : ModGL τ L} (hy : y ∈ adjointGroup τ L) (hcomm : y * x = x * y) :
    y ∈ torusGroup τ L := by
  classical
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
  have hxC : rootDiagUnit τ a ∈ adjointGroup τ L :=
    torusGroup_le_adjointGroup' hxH
  obtain ⟨Sy, hSy⟩ := CFSG.LieType.Chevalley.exists_finset_descent hy
  obtain ⟨Sx, hSx⟩ := CFSG.LieType.Chevalley.exists_finset_descent hxC
  obtain ⟨M, hMf, hSM, hKM⟩ := exists_finite_subfield_of_finset (K := K) (L := L)
    (Sy ∪ Sx ∪ Finset.univ.image fun i => ((a i : Lˣ) : L))
  have : Finite M := hMf
  have hSyM : (Sy : Set L) ⊆ M := fun c hc =>
    hSM (Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_coe.1 hc))))
  have hSxM : (Sx : Set L) ⊆ M := fun c hc =>
    hSM (Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_coe.1 hc))))
  have haM : ∀ i, ((a i : Lˣ) : L) ∈ M := fun i =>
    hSM (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)))
  obtain ⟨yM, hyM, hyMe⟩ := hSy M hSyM
  obtain ⟨xM, hxM, hxMe⟩ := hSx M hSxM
  have hMinj : Function.Injective (baseChangeGL (τ := τ) M.subtype) :=
    baseChangeGL_injective M.subtype
  let a' : Fin τ.rank → Mˣ := fun i => Units.mk0 ⟨(a i : L), haM i⟩ fun h =>
    (a i).ne_zero (congrArg Subtype.val h)
  have ha' : (fun i => Units.map M.subtype.toMonoidHom (a' i)) = a := by
    funext i
    exact Units.ext rfl
  have hxMa : xM = rootDiagUnit τ a' := by
    apply hMinj
    rw [hxMe, baseChangeGL_rootDiagUnit, ha']
  have hxMT : xM ∈ torusGroup τ M :=
    CFSG.RankThree.Classical2.mem_torusGroup_of_baseChangeGL_mem M.subtype hxM
      (by rw [hxMe]; exact hxH)
  have hxMp : orderOf xM = p := by
    rw [← hxp, ← orderOf_injective (baseChangeGL (τ := τ) M.subtype) hMinj xM, hxMe]
  have hap : a ^ p = 1 := by
    apply rootDiagUnit_injective (τ := τ)
    have h1 : rootDiagUnit τ a ^ p = 1 := hxp ▸ pow_orderOf_eq_one _
    have h2 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p := (rootDiagUnitHom τ L).map_pow a p
    rw [rootDiagUnit_one, h2, h1]
  have hpM : p ∣ Nat.card Mˣ := by
    have hne : ∃ i, a i ≠ 1 := by
      by_contra hcon
      have h1 : a = 1 := funext fun i => not_not.1 fun hi => hcon ⟨i, hi⟩
      rw [h1, rootDiagUnit_one, orderOf_one] at hxp
      exact hp.one_lt.ne hxp
    obtain ⟨i, hi⟩ := hne
    have hi' : (a i) ^ p = 1 := by simpa using congrFun hap i
    have hord : orderOf (a i) = p := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hi') with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hi
      · exact h
    have hinj : Function.Injective (Units.map M.subtype.toMonoidHom) :=
      Units.map_injective M.subtype.injective
    have hord' : orderOf (a' i) = p := by
      rw [← hord, ← orderOf_injective _ hinj (a' i)]
      exact congrArg orderOf (congrFun ha' i)
    rw [← hord']
    exact orderOf_dvd_natCard _
  have hregM : ∀ b : Fin τ.rank → Mˣ, xM = rootDiagUnit τ b →
      ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar b α ≠ 1 := by
    intro b hb α hα hbα
    have h1 : (fun i => Units.map M.subtype.toMonoidHom (b i)) = a := by
      apply rootDiagUnit_injective (τ := τ)
      rw [← baseChangeGL_rootDiagUnit, ← hb, hxMe]
    refine hreg a rfl α hα ?_
    rw [← h1, rootChar_map_tuple, hbα, map_one]
  have hcent := hcent M hpM hxMT hxMp hregM
  have hyMc : yM ∈ adjointGroup τ M ⊓ Subgroup.centralizer {xM} := by
    refine ⟨hyM, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    apply hMinj
    rw [map_mul, map_mul, hxMe, hyMe]
    exact hcomm
  rw [hcent] at hyMc
  rw [← hyMe]
  exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup M.subtype hyMc

end Regular

end CFSG.RankThree.PartOne.KE
