module

public import CFSG.Walter.Cited.HuppertAlperin
public import CFSG.Walter.ReeOrder.JT.Cited

public section

namespace CFSG.Walter

open scoped Pointwise commutatorElement

namespace Huppert

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem exists_mem_normalizer_conj_eq (hp2 : p ≠ 2) (P : Sylow p X)
    (hmeta : CFSG.IsMetacyclic (P : Subgroup X)) {x g : X} (hx : x ∈ (P : Subgroup X))
    (hg : g⁻¹ * x * g ∈ (P : Subgroup X)) :
    ∃ c ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), c⁻¹ * x * c = g⁻¹ * x * g := by
  have hP : Subgroup.zpowers x ≤ (P : Subgroup X) := Subgroup.zpowers_le.2 hx
  have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup X) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := RankTwoShapes.alperin_centric_radical_fusion P hP hPg
  have hcN : c ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    clear hcg
    induction hc with
    | one => exact Subgroup.one_mem _
    | step _ hQ _ hn ih =>
      rw [eq_of_isAlperinSubgroup hp2 P hmeta hQ] at hn
      exact Subgroup.mul_mem _ ih hn
  exact ⟨c, hcN, hcg x (Subgroup.mem_zpowers x)⟩

theorem exists_cyclic_of_normalizer (hp2 : p ≠ 2) (P : Sylow p X)
    (hmeta : CFSG.IsMetacyclic (P : Subgroup X)) (hnab : ¬ IsMulCommutative (P : Subgroup X)) :
    ∃ D : Subgroup X, D ≤ P ∧ IsCyclic D ∧ ∀ x ∈ (P : Subgroup X),
      ∀ c ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), x⁻¹ * (c⁻¹ * x * c) ∈ D := by
  classical
  set N := Subgroup.normalizer ((P : Subgroup X) : Set X) with hNdef
  have hPp : IsPGroup p (P : Subgroup X) := P.isPGroup'
  set P' : Subgroup N := (P : Subgroup X).subgroupOf N with hP'def
  have hP'n : P'.Normal := Subgroup.normal_in_normalizer
  have hP'card : Nat.card P' = Nat.card (P : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hP'idx : ¬ p ∣ P'.index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  have hcop : (Nat.card P').Coprime P'.index := by
    rw [hP'card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hP'idx)
  obtain ⟨S, hS⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set S' : Subgroup X := S.map N.subtype with hS'def
  have hS'N : S' ≤ N := Subgroup.map_subtype_le _
  let : MulDistribMulAction S' (P : Subgroup X) :=
    MulDistribMulAction.compHom (P : Subgroup X) (Subgroup.inclusion hS'N)
  have hsmul : ∀ (a : S') (x : (P : Subgroup X)), ((a • x : (P : Subgroup X)) : X) =
      (a : X) * x * (a : X)⁻¹ := fun _ _ => rfl
  have hS'cop : Nat.Coprime p (Nat.card S') := by
    have h1 : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective N.subtype_injective
    have h2 := hS.card_mul_card
    have h3 := P'.card_mul_index
    have hpos : 0 < Nat.card P' := Nat.card_pos
    have : Nat.card S = P'.index := Nat.eq_of_mul_eq_mul_left hpos (h2.trans h3.symm)
    rw [h1, this]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hP'idx
  have : Fact (IsPGroup p (P : Subgroup X)) := ⟨hPp⟩
  set D₀ : Subgroup (P : Subgroup X) :=
    CFSG.commutatorAction S' (P : Subgroup X) ⊔ commutator (P : Subgroup X) with hD₀def
  have hD₀cyc : IsCyclic D₀ := by
    by_cases htriv : CFSG.ActsTrivially S' (P : Subgroup X)
    · have hbot : CFSG.commutatorAction S' (P : Subgroup X) = ⊥ := by
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨a, h, -, rfl⟩
        rw [htriv a h, inv_mul_cancel]
        exact Subgroup.one_mem _
      rw [hD₀def, hbot, bot_sup_eq]
      exact isCyclic_commutator hmeta
    · obtain ⟨-, hcyc, -, -, hder⟩ := CFSG.theorem_4_12_c (R := (P : Subgroup X)) (A := S') hp2
        hS'cop hmeta hnab htriv
      have hder' : commutator (P : Subgroup X) ≤ CFSG.commutatorAction S' (P : Subgroup X) := by
        rw [← derivedSeries_one]
        exact hder
      rw [hD₀def, sup_eq_left.mpr hder']
      exact hcyc
  refine ⟨D₀.map (P : Subgroup X).subtype, Subgroup.map_subtype_le _,
    (D₀.equivMapOfInjective _ (P : Subgroup X).subtype_injective).isCyclic.mp hD₀cyc, ?_⟩
  intro x hx c hc
  obtain ⟨⟨⟨q, hq⟩, ⟨s, hs⟩⟩, hqs, -⟩ := (Subgroup.isComplement'_def.mp hS).existsUnique ⟨c, hc⟩
  have hqs' : (c : X) = (q : X) * (s : X) := by
    have := congrArg Subtype.val hqs
    simpa using this.symm
  have hqP : (q : X) ∈ (P : Subgroup X) := Subgroup.mem_subgroupOf.mp hq
  have hsS' : (s : X) ∈ S' := ⟨s, hs, rfl⟩
  set y : X := (q : X)⁻¹ * x * q with hydef
  have hyP : y ∈ (P : Subgroup X) :=
    (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hqP) hx) hqP
  have hsplit : x⁻¹ * (c⁻¹ * x * c) = (x⁻¹ * y) * (y⁻¹ * ((s : X)⁻¹ * y * s)) := by
    rw [hqs', hydef]; group
  rw [hsplit]
  refine Subgroup.mul_mem _ ⟨⁅(⟨x, hx⟩ : (P : Subgroup X))⁻¹, (⟨q, hqP⟩ : (P : Subgroup X))⁻¹⁆,
    Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _)), ?_⟩ ⟨(⟨y, hyP⟩ : (P : Subgroup X))⁻¹ *
      ((⟨s, hsS'⟩ : S')⁻¹ • (⟨y, hyP⟩ : (P : Subgroup X))),
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, _, Subgroup.mem_top _, rfl⟩), ?_⟩
  · rw [Subgroup.coe_subtype, commutatorElement_def]
    simp [hydef, mul_assoc]
  · rw [Subgroup.coe_subtype, Subgroup.coe_mul, hsmul]
    simp

end Huppert

theorem huppertMetacyclicTheorem : JT.HuppertMetacyclicTheorem := by
  intro X _ _ p _ hp2 P hnab hmeta
  have hmeta' : CFSG.IsMetacyclic (P : Subgroup X) := hmeta
  obtain ⟨D, hDP, hDcyc, hD⟩ := Huppert.exists_cyclic_of_normalizer hp2 P hmeta' hnab
  have hfocal : (P : Subgroup X) ⊓ CFSG.derivedSubgroup X ≤ D := by
    rw [CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p P, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    obtain ⟨c, hc, hcx⟩ := Huppert.exists_mem_normalizer_conj_eq hp2 P hmeta' (g := g⁻¹) hx
      (by simpa using hy)
    have := hD x hx c hc
    rw [hcx] at this
    simpa using this
  have hDne : D ≠ P := by
    intro h
    apply hnab
    have : IsCyclic (P : Subgroup X) := h ▸ hDcyc
    exact this.isMulCommutative
  obtain ⟨x, hxP, hxD⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hDP hDne)
  have hxX' : x ∉ commutator X := fun h =>
    hxD (hfocal ⟨hxP, by rw [CFSG.derivedSubgroup, derivedSeries_one]; exact h⟩)
  set m := (P : Subgroup X).index with hmdef
  have hm : ¬ p ∣ m := P.not_dvd_index
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine ⟨(powMonoidHom m : Abelianization X →* Abelianization X).ker.comap Abelianization.of,
    Subgroup.Normal.comap inferInstance _, ?_, ?_⟩
  · intro htop
    apply hxX'
    have h1 : (Abelianization.of x) ^ m = 1 := by
      have : x ∈ (powMonoidHom m : Abelianization X →* Abelianization X).ker.comap
          Abelianization.of := htop ▸ Subgroup.mem_top x
      exact this
    have hx1 : x ^ p ^ k = 1 := by
      rw [← hk]
      exact congrArg Subtype.val (pow_card_eq_one' (G := (P : Subgroup X)) (x := ⟨x, hxP⟩))
    have h2 : (Abelianization.of x) ^ p ^ k = 1 := by rw [← map_pow, hx1, map_one]
    have hcop : Nat.Coprime m (p ^ k) :=
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)).symm
    have h3 : orderOf (Abelianization.of x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h3
  · intro v
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    change (Abelianization.of (g ^ p ^ k)) ^ m = 1
    rw [map_pow, ← pow_mul, ← hk, hmdef, Subgroup.card_mul_index, ← map_pow, pow_card_eq_one',
      map_one]

end CFSG.Walter
