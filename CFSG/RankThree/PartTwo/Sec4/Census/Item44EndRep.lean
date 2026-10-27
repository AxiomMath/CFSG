module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Gaps
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndBasic
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.Foundations.HigherElementaryThompson
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartTwo.NotationBlocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped IsMulCommutative Matrix

@[expose] noncomputable def autToEndP (p : ℕ) [Fact p.Prime] (A : Type*) [Group A]
    [IsElementaryAbelian p A] : MulAut A →* Module.End (ZMod p) (Additive A) where
  toFun σ := AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive σ.toMonoidHom)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem autToEndP_apply (p : ℕ) [Fact p.Prime] {A : Type*} [Group A] [IsElementaryAbelian p A]
    (σ : MulAut A) (x : A) : autToEndP p A σ (Additive.ofMul x) = Additive.ofMul (σ x) :=
  rfl

theorem map_eq_one_of_isPerfect_comm {G M : Type*} [Group G] [Group.IsPerfect G] [CommGroup M]
    (f : G →* M) (g : G) : f g = 1 := by
  have h : g ∈ commutator G := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top g
  exact Abelianization.commutator_subset_ker f h

section Action

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D : Subgroup G}

@[expose] noncomputable def frattiniLin (h : CriticalAt p D)
    [IsElementaryAbelian p (D ⧸ frattini D)] :
    G →* Module.End (ZMod p) (Additive (D ⧸ frattini D)) :=
  (autToEndP p (D ⧸ frattini D)).comp h.frattiniAct

omit [Finite G] in
theorem frattiniLin_apply (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)] (y : G)
    (x : D) : frattiniLin h y (Additive.ofMul (x : D ⧸ frattini D)) =
      Additive.ofMul ((h.conjD y x : D) : D ⧸ frattini D) :=
  congrArg Additive.ofMul (quotientAutomorphism_apply _ _ _)

theorem mem_oddCore_of_frattiniLin_eq_one (h : CriticalAt p D) (hp2 : p ≠ 2)
    [IsElementaryAbelian p (D ⧸ frattini D)]
    (hodd : Odd (Nat.card (Subgroup.centralizer (D : Set G)))) {y : G}
    (hy : frattiniLin h y = 1) : y ∈ oddCore G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : h.frattiniKer.Normal := h.frattiniKer_normal
  have hNodd : Odd (Nat.card h.frattiniKer) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := h.frattiniKer) 2 h2
    have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have hcop : Nat.Coprime (orderOf (t : G)) p := by
      rw [ht']
      exact (Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hp2)
    have htD := h.centralizes_D_of_mem_frattiniKer t.2 hcop
    have htC : (t : G) ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      calc d * t = (t : G) * d * (t : G)⁻¹ * t := by rw [htD d hd]
        _ = t * d := by group
    have h1 : orderOf (t : G) ∣ Nat.card (Subgroup.centralizer (D : Set G)) := by
      rw [← Subgroup.orderOf_mk (t : G) htC]
      exact orderOf_dvd_natCard _
    rw [ht'] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
  apply le_oddCore hN hNodd
  rw [CriticalAt.mem_frattiniKer_iff]
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have := congrArg (fun f : Module.End (ZMod p) (Additive (D ⧸ frattini D)) =>
      f (Additive.ofMul (x : D ⧸ frattini D))) hy
    simp only [frattiniLin_apply, Module.End.one_apply] at this
    rw [MulAut.one_apply, CriticalAt.frattiniAct, MonoidHom.comp_apply]
    exact (quotientAutomorphism_apply _ _ _).trans (Additive.ofMul.injective this)

@[expose] noncomputable def frattiniMat (h : CriticalAt p D)
    [IsElementaryAbelian p (D ⧸ frattini D)] {d : ℕ}
    (b : Module.Basis (Fin d) (ZMod p) (Additive (D ⧸ frattini D))) : G →* GL (Fin d) (ZMod p) :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp (frattiniLin h).toHomUnits

variable {d : ℕ}

omit [Finite G] in
theorem frattiniMat_coe (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    (b : Module.Basis (Fin d) (ZMod p) (Additive (D ⧸ frattini D))) (y : G) :
    (frattiniMat h b y : Matrix (Fin d) (Fin d) (ZMod p)) =
      LinearMap.toMatrix b b (frattiniLin h y) :=
  rfl

omit [Finite G] in
theorem frattiniMat_mulVec (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    (b : Module.Basis (Fin d) (ZMod p) (Additive (D ⧸ frattini D))) (y : G)
    (x : Additive (D ⧸ frattini D)) :
    (frattiniMat h b y : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ b.equivFun x =
      b.equivFun (frattiniLin h y x) := by
  rw [frattiniMat_coe, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

omit [Finite G] in
theorem frattiniMat_eq_one_iff (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    (b : Module.Basis (Fin d) (ZMod p) (Additive (D ⧸ frattini D))) (y : G) :
    frattiniMat h b y = 1 ↔ frattiniLin h y = 1 := by
  constructor
  · intro hy
    have h1 := congrArg Units.val hy
    rw [frattiniMat_coe, Units.val_one] at h1
    apply (LinearMap.toMatrix b b).injective
    rw [h1, ← LinearMap.toMatrix_id b]
    rfl
  · intro hy
    apply Units.ext
    rw [frattiniMat_coe, hy, Units.val_one]
    exact LinearMap.toMatrix_id b

omit [Finite G] in
theorem finrank_fixed_mat (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    (b : Module.Basis (Fin d) (ZMod p) (Additive (D ⧸ frattini D))) (y : G) :
    Module.finrank (ZMod p) (Module.End.eigenspace
        (Matrix.toLin' (frattiniMat h b y : Matrix (Fin d) (Fin d) (ZMod p))) 1) =
      Module.finrank (ZMod p) (Module.End.eigenspace (frattiniLin h y) 1) := by
  have heq : Module.End.eigenspace
      (Matrix.toLin' (frattiniMat h b y : Matrix (Fin d) (Fin d) (ZMod p))) 1 =
      (Module.End.eigenspace (frattiniLin h y) 1).map b.equivFun.toLinearMap := by
    ext v
    obtain ⟨x, rfl⟩ := b.equivFun.surjective v
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Module.End.mem_eigenspace_iff,
      Module.End.mem_eigenspace_iff, one_smul, one_smul, Matrix.toLin'_apply, frattiniMat_mulVec]
    exact b.equivFun.injective.eq_iff
  rw [heq, LinearEquiv.finrank_map_eq]

omit [Finite G] in
theorem det_frattiniMat_eq_one [Group.IsPerfect G] (h : CriticalAt p D)
    [IsElementaryAbelian p (D ⧸ frattini D)]
    (b : Module.Basis (Fin d) (ZMod p) (Additive (D ⧸ frattini D))) (y : G) :
    (frattiniMat h b y : Matrix (Fin d) (Fin d) (ZMod p)).det = 1 := by
  rw [frattiniMat_coe, LinearMap.det_toMatrix]
  have := map_eq_one_of_isPerfect_comm ((Units.map LinearMap.det).comp
    (frattiniLin h).toHomUnits) y
  exact congrArg Units.val this

end Action

variable {G : Type} [Group G] [Finite G]

theorem exists_rep {K : Subgroup G} [K.Normal] (hyp : PartTwoRankThreeHyp G K) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ ρ : G →* GL (Fin 4) (ZMod p),
      (∀ y, ρ y = 1 → y ∈ oddCore G) ∧
      (∀ y, (ρ y : Matrix (Fin 4) (Fin 4) (ZMod p)).det = 1) ∧
      ∃ a₀ : G, a₀ * a₀ = 1 ∧ ρ a₀ = -1 := by
  obtain ⟨hG, hperf, -, -, -, -, -, h3, p, hp, hp3, -, D, hD, hodd⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hDp : IsPGroup p D := pCore_isPGroup.to_le hD.le
  have : D.Normal := hD.normal
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) (⊤ : Subgroup G)
  rw [h3] at hEcard
  obtain ⟨eE⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := E)
    (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (hE.2 a a.2)) hEcard
  set ι : Multiplicative (Fin 3 → ZMod 2) →* G := E.subtype.comp eE.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp eE.symm.injective
  have hA2 : ∀ a : Multiplicative (Fin 3 → ZMod 2), a ^ 2 = 1 := by
    intro a
    obtain ⟨e, rfl⟩ := eE.surjective a
    rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hA8 : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
    rw [← Nat.card_congr eE.toEquiv, hEcard]
    norm_num
  set ρA : Multiplicative (Fin 3 → ZMod 2) →* MulAut D := hD.conjD.comp ι with hρAdef
  have hρA : ∀ a (d : D), ((ρA a d : D) : G) = ι a * d * (ι a)⁻¹ := fun a d =>
    hD.conjD_apply (ι a) d
  have hfaith : Function.Injective ρA := by
    intro a₁ a₂ h
    apply hι
    set c := (ι a₁)⁻¹ * ι a₂ with hc
    have hcD : c ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : G)) h
      simp only [hρA] at h1
      calc d * c = (ι a₁)⁻¹ * (ι a₁ * d * (ι a₁)⁻¹) * ι a₂ := by rw [hc]; group
        _ = (ι a₁)⁻¹ * (ι a₂ * d * (ι a₂)⁻¹) * ι a₂ := by rw [h1]
        _ = c * d := by rw [hc]; group
    have hc2 : c ^ 2 = 1 := by
      rw [hc, ← map_inv, ← map_mul, ← map_pow, hA2, map_one]
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have h2 : orderOf c ∣ Nat.card (Subgroup.centralizer (D : Set G)) := by
      rw [← Subgroup.orderOf_mk c hcD]
      exact orderOf_dvd_natCard _
    have h3 : orderOf c = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left).mpr hodd) h1 h2
    rw [orderOf_eq_one_iff, hc, inv_mul_eq_one] at h3
    exact h3
  have hfix : ∀ a : Multiplicative (Fin 3 → ZMod 2), a ≠ 1 →
      CFSG.pRank p (fixedSubgroupOf (ρA a)) ≤ 2 := by
    intro a ha
    set C := fixedSubgroupOf (ρA a) with hC
    have ht : orderOf (ι a) = 2 := orderOf_eq_prime (by rw [← map_pow, hA2, map_one])
      (fun h => ha (hι (by rw [h, map_one])))
    have hCt : ∀ c ∈ C.map D.subtype, c * ι a = ι a * c := by
      rintro _ ⟨c, hc, rfl⟩
      have h1 := congrArg Subtype.val ((mem_fixedSubgroupOf (ρA a) c).mp hc)
      rw [hρA] at h1
      change (c : G) * ι a = ι a * c
      calc (c : G) * ι a = ι a * c * (ι a)⁻¹ * ι a := by rw [h1]
        _ = ι a * c := by group
    have h1 := pRank_le_localRank_of_centralizes hp hp2 ht hCt
    have h2 := hG.localRank_lt p hp hp3
    rw [← pRank_congr_mulEquiv hp.one_lt (C.equivMapOfInjective D.subtype D.subtype_injective)]
      at h1
    omega
  obtain ⟨hd, ⟨a₀, ⟨ha₀1, ha₀⟩, -⟩, -⟩ := class_two_eight_action_inverting_quotient hp2 hDp
    (fun x => Subtype.ext (by simpa using hD.exp x x.2)) hD.commutator_le_center hA2 hA8 ρA
    hfaith hfix
  obtain ⟨-, -, -, hVelem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have := hVelem
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  set R := frattiniLin hD with hRdef
  have hR := frattiniLin_apply hD
  have hdet : ∀ y, LinearMap.det (R y) = 1 := by
    intro y
    have := map_eq_one_of_isPerfect_comm ((Units.map LinearMap.det).comp R.toHomUnits) y
    exact congrArg Units.val this
  have hneg : R (ι a₀) = -1 := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwx : w = Additive.ofMul (x : D ⧸ frattini D) := by rw [hx]; rfl
    rw [hwx, hR, LinearMap.neg_apply, Module.End.one_apply, ← ofMul_inv]
    exact congrArg Additive.ofMul (ha₀ x)
  have hfin4 : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) = 4 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (D ⧸ frattini D))
    rw [Nat.card_zmod] at hpow
    have hrank := pRank_eq_of_card_eq_pow hp.one_lt (A := D ⧸ frattini D) hpow
    have h1 := hdet (ι a₀)
    rw [hneg, ← LinearMap.det_toMatrix (Module.finBasis (ZMod p) (Additive (D ⧸ frattini D))),
      map_neg, LinearMap.toMatrix_one, Matrix.det_neg, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    have hne : (-1 : ZMod p) ≠ 1 := by
      intro h
      have h2 : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 1 - (-1) := by ring
          _ = 0 := by rw [h, sub_self]
      exact two_ne_zero_zmod hp hp2 h2
    rcases hd with h | h
    · rw [hrank] at h
      rw [h, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, neg_one_sq, one_mul] at h1
      exact absurd h1 hne
    · rwa [hrank] at h
  set b := Module.finBasisOfFinrankEq (ZMod p) (Additive (D ⧸ frattini D)) hfin4
  refine ⟨p, hp, hp5, frattiniMat hD b, fun y hy => mem_oddCore_of_frattiniLin_eq_one hD hp2 hodd
    ((frattiniMat_eq_one_iff hD b y).mp hy), det_frattiniMat_eq_one hD b, ι a₀, ?_, ?_⟩
  · rw [← map_mul, ← sq, hA2, map_one]
  · apply Units.ext
    rw [frattiniMat_coe, hneg, Units.val_neg, Units.val_one, map_neg]
    congr 1
    exact LinearMap.toMatrix_id b

end CFSG.RankThree.PartTwo.Sec4.Census
