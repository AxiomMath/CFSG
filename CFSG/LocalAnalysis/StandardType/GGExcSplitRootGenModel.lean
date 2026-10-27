module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count

public section

namespace CFSG.StandardType.ExcSplitRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three Multiplicative

variable {τ : Tag} {K : Type} [Field K] {p : ℕ}

private theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h))

private theorem sum_alpha_mul_corootPair
    {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∑ i, α i * corootPair α (Pi.single i 1) = 2 := by
  have hv : α = ∑ i, α i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin := CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum hα Finset.univ α
    (fun i => (Pi.single i 1 : Fin τ.rank → ℤ))
  rw [← hv] at hlin
  rw [← hlin]
  have hpos := iform_self_pos_of_isRoot hα
  refine mul_right_cancel₀ hpos.ne' ?_
  rw [corootPair_mul hα α]

theorem excRefl_apply
    {τ : Tag} {p : ℕ} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (t : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    excRefl α t i = t i -
      (corootPair α (Pi.single i 1) : ZMod p) * ∑ j, (α j : ZMod p) * t j := by
  rw [excRefl, adAct, rootReflection_inv hα, rootReflection_smul hα (Pi.single i 1)]
  have hsplit : (∑ j, ((((Pi.single i 1 : Fin τ.rank → ℤ) -
          corootPair α (Pi.single i 1) • α) j : ℤ) : ZMod p) * t j) =
      (∑ j, (((Pi.single i 1 : Fin τ.rank → ℤ) j : ℤ) : ZMod p) * t j) -
        (∑ j, (((corootPair α (Pi.single i 1) • α) j : ℤ) : ZMod p) * t j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.sub_apply, Int.cast_sub, sub_mul]
  have hfirst :
      (∑ j, (((Pi.single i 1 : Fin τ.rank → ℤ) j : ℤ) : ZMod p) * t j) = t i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hsecond :
      (∑ j, (((corootPair α (Pi.single i 1) • α) j : ℤ) : ZMod p) * t j) =
        (corootPair α (Pi.single i 1) : ZMod p) * (∑ j, (α j : ZMod p) * t j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    ring
  rw [hsplit, hfirst, hsecond]

section Torus


theorem excTorusHom_injective [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    Function.Injective (excTorusHom hfullp hζ) := by
  intro x y hxy
  have h : TableBExc.torusPowEltP hfullp hζ (toAdd x) =
      TableBExc.torusPowEltP hfullp hζ (toAdd y) := by
    apply Subtype.ext
    rw [TableBExc.coe_torusPowEltP, TableBExc.coe_torusPowEltP]
    have hxy' := congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) hxy
    rw [coe_excTorusHom, coe_excTorusHom] at hxy'
    have hfunx : zetaVec ζ hζ (toAdd x) = fun i => ζ ^ ((toAdd x) i).val := by
      funext i
      exact zetaVec_apply ζ hζ (toAdd x) i
    have hfuny : zetaVec ζ hζ (toAdd y) = fun i => ζ ^ ((toAdd y) i).val := by
      funext i
      exact zetaVec_apply ζ hζ (toAdd y) i
    rw [hfunx, hfuny] at hxy'
    exact hxy'
  exact Multiplicative.ofAdd.injective
    ((TableBExc.bijective_torusPowEltP hfullp hζo hζ).2.1 h)

theorem range_excTorusHom [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    (excTorusHom hfullp hζ).range = TableBExc.torusPow τ K p := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    have hmem := (TableBExc.bijective_torusPowEltP hfullp hζo hζ).1 (toAdd x)
    have he : excTorusHom hfullp hζ x = TableBExc.torusPowEltP hfullp hζ (toAdd x) := by
      apply Subtype.ext
      rw [coe_excTorusHom, TableBExc.coe_torusPowEltP]
      rfl
    rwa [he]
  · intro hg
    obtain ⟨x, hx⟩ := (TableBExc.bijective_torusPowEltP hfullp hζo hζ).2.2 g hg
    refine ⟨ofAdd x, ?_⟩
    have he : excTorusHom hfullp hζ (ofAdd x) = TableBExc.torusPowEltP hfullp hζ x := by
      apply Subtype.ext
      rw [coe_excTorusHom, TableBExc.coe_torusPowEltP]
      rfl
    rw [he, hx]

theorem excRefl_excRefl {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (t : Fin τ.rank → ZMod p) :
    excRefl α (excRefl α t) = t := by
  rw [excRefl, ← adAct_mul, rootReflection_mul_self hα, adAct_one]

theorem excRefl_eq_self_iff [Fact p.Prime] (hp2 : p ≠ 2) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (t : Fin τ.rank → ZMod p) :
    excRefl α t = t ↔ ∑ j, (α j : ZMod p) * t j = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hsum : (∑ i, (α i : ZMod p) * (corootPair α (Pi.single i 1) : ZMod p)) = 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) (sum_alpha_mul_corootPair hα)
    simpa using this
  constructor
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, (corootPair α (Pi.single i 1) : ZMod p) ≠ 0 := by
      by_contra hc
      push Not at hc
      have hzero : (∑ i, (α i : ZMod p) *
          (corootPair α (Pi.single i 1) : ZMod p)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hc i, mul_zero]
      rw [hsum] at hzero
      exact h2ne hzero
    have hcS : (corootPair α (Pi.single i 1) : ZMod p) *
        (∑ j, (α j : ZMod p) * t j) = 0 := by
      have hi' := congrFun h i
      rw [excRefl_apply hα t i] at hi'
      exact sub_eq_self.mp hi'
    exact (mul_eq_zero.mp hcS).resolve_left hi
  · intro hS
    funext i
    rw [excRefl_apply hα t i, hS, mul_zero]
    exact sub_zero _

theorem card_fix_excRefl [Fact p.Prime] (hp2 : p ≠ 2) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    Nat.card {t // excRefl (p := p) α t = t} * p = p ^ τ.rank := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hsum : (∑ i, (α i : ZMod p) * (corootPair α (Pi.single i 1) : ZMod p)) = 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) (sum_alpha_mul_corootPair hα)
    simpa using this
  have hαmod : ∃ i, (α i : ZMod p) ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : (∑ i, (α i : ZMod p) *
        (corootPair α (Pi.single i 1) : ZMod p)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [h i, zero_mul]
    rw [hsum] at hzero
    exact h2ne hzero
  let S : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
    { toFun := fun t => ∑ j, (α j : ZMod p) * t j
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hS_apply : ∀ t, S t = ∑ j, (α j : ZMod p) * t j := fun t => rfl
  have hsurj : Function.Surjective S := by
    intro c
    obtain ⟨i, hi⟩ := hαmod
    refine ⟨((α i : ZMod p)⁻¹ * c) • (Pi.single i 1 : Fin τ.rank → ZMod p), ?_⟩
    rw [hS_apply, Finset.sum_eq_single i]
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
      rw [← mul_assoc, mul_inv_cancel₀ hi, one_mul]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  have hfix : Nat.card {t // excRefl (p := p) α t = t} =
      Nat.card ↥S.toAddMonoidHom.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
    exact (excRefl_eq_self_iff hp2 hα t).trans
      (AddMonoidHom.mem_ker (f := S.toAddMonoidHom)).symm
  rw [hfix]
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective
    (f := S.toAddMonoidHom) hsurj
  have hU : Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hU, Nat.card_zmod] at hcard
  exact hcard

end Torus

section Weyl


theorem excWeyl_conj_excTorusHom [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (α : {α : Fin τ.rank → ℤ // IsRoot τ α})
    (t : Fin τ.rank → ZMod p) :
    excWeyl α * excTorusHom hfullp hζ (ofAdd t) * (excWeyl α)⁻¹ =
      excTorusHom hfullp hζ (ofAdd (excRefl α.1 t)) := by
  apply Subtype.ext
  obtain ⟨-, hmono, hmaps⟩ := rootWeylOne_spec (K := K) α.2
  have h := monomial_conj_rootDiagUnit_weylTuple (K := K) hmono hmaps (zetaVec ζ hζ t)
  rw [weylTuple_zetaVec] at h
  simpa only [excWeyl, coe_excTorusHom, Subgroup.coe_mul, Subgroup.coe_inv, excRefl,
    toAdd_ofAdd] using h

theorem excWeyl_mem_excComp (α : {α : Fin τ.rank → ℤ // IsRoot τ α}) :
    excWeyl (K := K) α ∈ excComp α.1 := by
  rw [excComp, Subgroup.mem_subgroupOf]
  change rootWeylOne τ K α.1 ∈ rootSpan τ K {α.1, -α.1}
  exact (sup_le (rootSubgroup_le_rootSpan (Set.mem_insert _ _))
    (rootSubgroup_le_rootSpan (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    (rootWeylOne_spec (K := K) α.2).1

end Weyl

end CFSG.StandardType.ExcSplitRootGen

end
