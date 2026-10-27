module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.B4Models
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsIrrOnRep
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules
import CFSG.Quasithin.EmptyFaithful.LRed2EbA
import CFSG.Quasithin.Background.HSL3Bridge
import TauCeti.FieldTheory.Finite.Four
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour
import CFSG.Quasithin.Background.FFC4Zmod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open
open scoped MatrixGroups Matrix LinearAlgebra.Projectivization
open CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.SL2Modules

private theorem exists_order_three_diag {K : Type} [Field K] [Fintype K]
    (h2 : Nat.card K = 2 ^ 2) :
    ∃ t : SL(2, K), orderOf t = 3 ∧
      t • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K ∧
      t • psl2ProjectiveZero K = psl2ProjectiveZero K := by
  have h4 : Nat.card K = 4 := by rw [h2]; norm_num
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four h4
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω
    simp at hω
  have hω3 : ω ^ 3 = 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [hω, mul_zero] at h
    linear_combination -h
  have h2K : CharP K 2 := CFSG.Quasithin.FFC.charP_two_of_card_pow h2
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have h3 : (3 : K) = 0 := by linear_combination hω
    rw [show (3 : K) = 2 + 1 by norm_num, htwo, zero_add] at h3
    exact zero_ne_one h3.symm
  let z : Kˣ := Units.mk0 ω hω0
  have hz3 : z ^ 3 = 1 := by
    apply Units.ext
    show ω ^ 3 = 1
    exact hω3
  have hz1 : z ≠ 1 := by
    intro h
    exact hω1 (congrArg Units.val h)
  have hzv : ((z : K) ^ 3) = 1 := congrArg Units.val hz3
  have hziv : (((z⁻¹ : Kˣ) : K) ^ 3) = 1 := by
    have h : (z⁻¹ : Kˣ) ^ 3 = 1 := by rw [inv_pow, hz3, inv_one]
    simpa using congrArg Units.val h
  refine ⟨dElt z, ?_, dElt_fixes_infinity z, dElt_fixes_zero z⟩
  apply orderOf_eq_prime
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow]
    simp only [coe_dElt']
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
    · simpa [pow_succ] using hzv
    · simpa [pow_succ] using hziv
  · intro h
    have h00 : ((dElt z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      rw [h]; rfl
    rw [coe_dElt'] at h00
    exact hz1 (Units.ext (by simpa using h00))

private noncomputable def coordWeight (K : Type) [Field K] [Fintype K]
    [Fintype (ℙ K (Fin 2 → K))] [DecidableEq (ℙ K (Fin 2 → K))] :
    ↥(evenWeight (ℙ K (Fin 2 → K))) := by
  classical
  exact ⟨delta (psl2ProjectiveInfinity K) + delta (psl2ProjectiveZero K),
    delta_add_delta_mem _ _⟩

private theorem coordWeight_ne_zero (K : Type) [Field K] [Fintype K]
    [Fintype (ℙ K (Fin 2 → K))] [DecidableEq (ℙ K (Fin 2 → K))] :
    coordWeight K ≠ 0 := by
  classical
  have hne : psl2ProjectiveInfinity K ≠ psl2ProjectiveZero K :=
    infinity_ne_zero (k := K)
  intro h
  have hP := congrArg (fun x : ↥(evenWeight (ℙ K (Fin 2 → K))) =>
    ((x : ℙ K (Fin 2 → K) → ZMod 2) (psl2ProjectiveInfinity K))) h
  simp [coordWeight, delta, hne] at hP

private theorem coordWeight_fixed {K : Type} [Field K] [Fintype K]
    [Fintype (ℙ K (Fin 2 → K))] [DecidableEq (ℙ K (Fin 2 → K))] {t : SL(2, K)}
    (htinf : t • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K)
    (htzero : t • psl2ProjectiveZero K = psl2ProjectiveZero K) :
    (deletedRep (SL(2, K)) (ℙ K (Fin 2 → K)) t) (coordWeight K) = coordWeight K := by
  classical
  apply Subtype.ext
  rw [deletedRep_apply]
  show permAct (MulAction.toPerm t) (delta (psl2ProjectiveInfinity K) +
    delta (psl2ProjectiveZero K)) = _
  rw [permAct_add, permAct_delta, permAct_delta]
  simp only [MulAction.toPerm_apply]
  rw [htinf, htzero]
  rfl

private theorem card_eq_sixteen_of_realizesVia_nat {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {J : Subgroup V} {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ 2) {π' : ↥(StatedSL 2 K') →* ↥L}
    (h' : (FFModel.nat (StatedSL 2 K')).RealizesVia L J ⊥ π') :
    Nat.card ↥J = 16 := by
  obtain ⟨e, -⟩ := CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub
    (Γ := StatedSL 2 K') h'
  rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H.card_stdMod, hK']
  norm_num

private theorem realizesVia_nat_of_isNaturalModule {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {J : Subgroup V} [Module (ZMod 2) (Additive ↥J)] {K : Type}
    [Field K] {π : ↥(StatedSL 2 K) →* ↥L} (hπ : Function.Surjective π)
    (hstable : StableUnder L J) {ρ : Representation (ZMod 2) SL(2, K) (Additive ↥J)}
    (hρ : ∀ (g : SL(2, K)) (x : ↥J), ρ g (Additive.ofMul x) = Additive.ofMul
      ⟨((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g) : ↥L) :
          MulAut V) x, hstable _ (π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
            2 K g)).2 _ x.2⟩)
    (hnat : IsNaturalModule ρ) :
    (FFModel.nat (StatedSL 2 K)).RealizesVia L J ⊥ π := by
  obtain ⟨φ, hφ⟩ := hnat
  let f : ↥J →* Multiplicative (Fin 2 → K) :=
    (AddEquiv.toMultiplicativeRight φ).toMonoidHom
  have hf_apply : ∀ u : ↥J, f u = Multiplicative.ofAdd (φ (Additive.ofMul u)) := fun _ => rfl
  refine CFSG.Quasithin.FFC.realizesVia_nat_of (Γ := StatedSL 2 K) (ι := Fin 2) (K := K)
    hπ bot_le (fun h u hu => hstable h h.2 u hu) ?_ f ?_ ?_ ?_
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    simp [hz]
  · exact (AddEquiv.toMultiplicativeRight φ).surjective
  · intro u
    rw [hf_apply]
    constructor
    · intro h
      have h0 : φ (Additive.ofMul u) = 0 :=
        Multiplicative.ofAdd.injective (by simpa using h)
      have h1 : Additive.ofMul u = 0 := φ.injective (by rw [h0, map_zero])
      have hu1 : u = 1 := Additive.ofMul.injective (by simpa using h1)
      rw [hu1]
      exact Subgroup.one_mem _
    · intro h
      have hu1 : u = 1 := by
        apply Subtype.ext
        exact Subgroup.mem_bot.mp h
      rw [hu1]
      exact f.map_one
  · intro γ u hu
    let g : SL(2, K) := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm γ
    have hσg : CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g = γ :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).apply_symm_apply γ
    have hρg : ρ g (Additive.ofMul u) = Additive.ofMul
        ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ := by
      rw [hρ, hσg]
    have hmain := hφ g (Additive.ofMul u)
    show f ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ =
      natAct (StatedSL 2 K) γ (f u)
    rw [hf_apply]
    change Multiplicative.ofAdd
        (φ (Additive.ofMul ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩)) =
      Multiplicative.ofAdd
        ((((γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          φ (Additive.ofMul u))
    congr 1
    rw [← hρg]
    have hcoe : ((g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        ((((γ : ↥(StatedSL 2 K)) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hσg]
      exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 K g).symm
    rw [hmain, hcoe]

private theorem false_of_isDeletedModule {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {J : Subgroup V} [Module (ZMod 2) (Additive ↥J)]
    {K K' : Type} [Field K] [Fintype K] [Field K'] [Finite K']
    [Fintype (ℙ K (Fin 2 → K))] [DecidableEq (ℙ K (Fin 2 → K))]
    {π : ↥(StatedSL 2 K) →* ↥L} (hπ : Function.Injective π)
    {π' : ↥(StatedSL 2 K') →* ↥L}
    (h' : (FFModel.nat (StatedSL 2 K')).RealizesVia L J ⊥ π')
    (hK : Nat.card K = 2 ^ 2) (hK' : Nat.card K' = 2 ^ 2)
    (hstable : StableUnder L J)
    {ρ : Representation (ZMod 2) SL(2, K) (Additive ↥J)}
    (hρ : ∀ (g : SL(2, K)) (x : ↥J), ρ g (Additive.ofMul x) = Additive.ofMul
      ⟨((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g) : ↥L) :
          MulAut V) x, hstable _ (π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
            2 K g)).2 _ x.2⟩)
    (hdel : IsDeletedModule ρ) : False := by
  classical
  obtain ⟨φ, hφ⟩ := hdel
  obtain ⟨t, ht3, htinf, htzero⟩ := exists_order_three_diag hK
  let w : ↥(evenWeight (ℙ K (Fin 2 → K))) := coordWeight K
  have hwne : w ≠ 0 := coordWeight_ne_zero K
  have hwfix : (deletedRep (SL(2, K)) (ℙ K (Fin 2 → K)) t) w = w :=
    coordWeight_fixed htinf htzero
  let v : Additive ↥J := φ.symm w
  have hvfix : ρ t v = v := by
    apply φ.injective
    apply Subtype.ext
    rw [hφ]
    rw [show φ v = w from AddEquiv.apply_symm_apply φ w]
    exact congrArg Subtype.val hwfix
  let u : ↥J := v.toMul
  have hu_ne : u ≠ 1 := by
    intro hu
    apply hwne
    have hv0 : v = 0 := by
      change Additive.ofMul u = 0
      rw [hu]
      rfl
    calc w = φ v := (AddEquiv.apply_symm_apply φ w).symm
      _ = φ 0 := by rw [hv0]
      _ = 0 := map_zero φ
  have hufix : ((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K t) : ↥L) :
      MulAut V) (u : V) = (u : V) := by
    have h1 : ρ t (Additive.ofMul u) = Additive.ofMul u := by
      change ρ t v = v
      exact hvfix
    have h2 : (⟨((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K t) : ↥L) :
        MulAut V) (u : V),
        hstable _ (π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K t)).2 _
          u.2⟩ : ↥J) = u := by
      apply Additive.ofMul.injective
      rw [← hρ t u]
      exact h1
    exact congrArg Subtype.val h2
  have hπσ : Function.Injective
      (π.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toMonoidHom) :=
    hπ.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).injective
  have hy3 : orderOf (((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K t) :
      ↥L) : MulAut V)) = 3 := by
    rw [Subgroup.orderOf_coe]
    change orderOf ((π.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
      2 K).toMonoidHom) t) = 3
    rw [orderOf_injective _ hπσ t, ht3]
  have hmem := CFSG.Quasithin.lred2_natural_fixed (K := K') (n := 2) hK' h'
    (y := ((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K t) : ↥L) :
      MulAut V)) (π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K t)).2 hy3
    (u := (u : V)) u.2 hufix
  exact absurd (Subtype.ext (Subgroup.mem_bot.mp hmem)) hu_ne

theorem realizesVia_nat_statedSL_two_of_bijective {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {J : Subgroup V} (hJ : IsIrrOn L J ⊥)
    {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    (hK : Nat.card K = 2 ^ 2) (hK' : Nat.card K' = 2 ^ 2)
    {π : ↥(StatedSL 2 K) →* ↥L} (hπ : Function.Bijective π)
    {π' : ↥(StatedSL 2 K') →* ↥L} (h' : (FFModel.nat (StatedSL 2 K')).RealizesVia L J ⊥ π') :
    (FFModel.nat (StatedSL 2 K)).RealizesVia L J ⊥ π := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (ℙ K (Fin 2 → K)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ K (Fin 2 → K)) := Classical.decEq _
  have hK4 : Fintype.card K = 4 := by
    rw [Fintype.card_eq_nat_card, hK]
    norm_num
  have hcardJ : Nat.card ↥J = 16 := card_eq_sixteen_of_realizesVia_nat hK' h'
  have h2J : ∀ x : Additive ↥J, 2 • x = 0 := by
    intro x
    rw [two_nsmul]
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    simpa [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using
      hV ((Additive.toMul x : ↥J) : V)
  let _ : Module (ZMod 2) (Additive ↥J) := AddCommGroup.zmodModule (n := 2) h2J
  let πσ : SL(2, K) →* ↥L :=
    π.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toMonoidHom
  let actV : SL(2, K) →* MulAut V := L.subtype.comp πσ
  have hJinv : ∀ g, ∀ w ∈ J, actV g w ∈ J :=
    fun g w hw => hJ.2.1 _ (πσ g).2 w hw
  let ρ : Representation (ZMod 2) SL(2, K) (Additive ↥J) :=
    CFSG.Quasithin.ASInputs.C10KH.repOf
      (CFSG.Quasithin.ASInputs.C10KH.restrictAut actV J hJinv)
  have hρ_apply : ∀ (g : SL(2, K)) (x : ↥J), ρ g (Additive.ofMul x) = Additive.ofMul
      ⟨((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g) : ↥L) :
        MulAut V) x, hJ.2.1 _ (πσ g).2 _ x.2⟩ := by
    intro g x
    dsimp only [ρ]
    rw [CFSG.Quasithin.ASInputs.C10KH.repOf_apply]
    change Additive.ofMul (((CFSG.Quasithin.ASInputs.C10KH.restrictAut actV J hJinv) g) x) =
      Additive.ofMul ⟨((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g) :
        ↥L) : MulAut V) x, hJ.2.1 _ (πσ g).2 _ x.2⟩
    rw [show ((CFSG.Quasithin.ASInputs.C10KH.restrictAut actV J hJinv) g) x =
        ⟨((π (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g) : ↥L) :
          MulAut V) x, hJ.2.1 _ (πσ g).2 _ x.2⟩ from by
      apply Subtype.ext
      rw [CFSG.Quasithin.ASInputs.C10KH.restrictAut_apply]
      rfl]
  have hsurjAct : ∀ l ∈ L, ∃ g : SL(2, K), actV g = l := by
    intro l hl
    obtain ⟨g, hg⟩ :=
      (hπ.2.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).surjective)
        ⟨l, hl⟩
    exact ⟨g, by simpa [actV, πσ] using congrArg Subtype.val hg⟩
  have hρirr : ρ.IsIrreducible :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.isIrreducible_repOf_restrictAut hJ actV hJinv
      hsurjAct
  obtain ⟨hclass, -, -, -, -, -⟩ :=
    irreducible_binary_SL2_four_module_production hK4 ρ hρirr
  rcases hclass with htriv | hnat | hdel
  · obtain ⟨φ, -⟩ := htriv
    have hc := Nat.card_congr φ.toEquiv
    change Nat.card ↥J = Nat.card (ZMod 2) at hc
    rw [hcardJ, Nat.card_zmod] at hc
    norm_num at hc
  · exact realizesVia_nat_of_isNaturalModule hπ.2 hJ.2.1 hρ_apply hnat
  · exact (false_of_isDeletedModule hπ.1 h' hK hK' hJ.2.1 hρ_apply hdel).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
