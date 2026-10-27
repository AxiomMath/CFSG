module

public import CFSG.RankThree.SubgroupLists.CommutatorScalarBound
public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.RankThree.SubgroupLists2.OmegaThree
public import CFSG.Walter.W67.CentralExt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.SubgroupLists.ExtraspecialNormal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank CFSG.RepresentationTheory
open scoped MatrixGroups

section Model

variable {F : Type} [Field F]

@[expose] def rootSL2 (b : F) : SL(2, F) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def torusSL2 (a : Fˣ) : SL(2, F) :=
  ⟨!![(a : F), 0; 0, (a⁻¹ : Fˣ)], by simp [Matrix.det_fin_two]⟩

theorem rootSL2_add (b c : F) : rootSL2 b * rootSL2 c = rootSL2 (b + c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change !![(1 : F), b; 0, 1] * !![(1 : F), c; 0, 1] = !![1, b + c; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem rootSL2_zero : rootSL2 (0 : F) = 1 := by
  apply Subtype.ext
  change !![(1 : F), 0; 0, 1] = 1
  rw [Matrix.one_fin_two]

theorem rootSL2_pow (n : ℕ) : rootSL2 (1 : F) ^ n = rootSL2 (n : F) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, rootSL2_zero]
  | succ n ih => rw [pow_succ, ih, rootSL2_add, Nat.cast_succ]

theorem torusSL2_conj_rootSL2 (a : Fˣ) (b : F) :
    torusSL2 a * rootSL2 b = rootSL2 ((a : F) ^ 2 * b) * torusSL2 a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![1, b; 0, 1] =
    !![1, (a : F) ^ 2 * b; 0, 1] * !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  congr 1
  simp
  field_simp

theorem rootSL2_not_mem_center {b : F} (hb : b ≠ 0) :
    rootSL2 b ∉ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrFun (congrFun hr 0) 1
  simp [rootSL2] at h
  exact hb h.symm

@[expose] noncomputable def rootPSL2 (F : Type) [Field F] :
    ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.mk' (Subgroup.center SL(2, F)) (rootSL2 1)

theorem isConj_rootPSL2_pow {k : ℕ} {a : Fˣ} (ha : (k : F) = (a : F) ^ 2) :
    IsConj (rootPSL2 F) (rootPSL2 F ^ k) := by
  refine isConj_iff.mpr ⟨QuotientGroup.mk' _ (torusSL2 a), ?_⟩
  rw [rootPSL2, ← map_pow, ← map_inv, ← map_mul, ← map_mul, rootSL2_pow,
    torusSL2_conj_rootSL2, mul_one, ← ha, mul_inv_cancel_right]

theorem rootPSL2_ne_one : rootPSL2 F ≠ 1 := by
  intro h
  apply rootSL2_not_mem_center (one_ne_zero (α := F))
  simpa [rootPSL2, QuotientGroup.eq_one_iff] using h

@[expose] noncomputable def rootHomPSL2 (F : Type) [Field F] :
    Multiplicative F →* ProjectiveSpecialLinearGroup (Fin 2) F where
  toFun b := QuotientGroup.mk' (Subgroup.center SL(2, F)) (rootSL2 (Multiplicative.toAdd b))
  map_one' := by rw [toAdd_one, rootSL2_zero, map_one]
  map_mul' a b := by rw [toAdd_mul, ← rootSL2_add, map_mul]

theorem rootHomPSL2_injective : Function.Injective (rootHomPSL2 F) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hmem : rootSL2 (Multiplicative.toAdd b) ∈ Subgroup.center SL(2, F) :=
    (QuotientGroup.eq_one_iff _).mp hb
  by_contra hb1
  exact rootSL2_not_mem_center (fun h0 => hb1 (by rw [← ofAdd_toAdd b, h0, ofAdd_zero])) hmem

@[expose] noncomputable def rootGroupPSL2 (F : Type) [Field F] :
    Subgroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
  (rootHomPSL2 F).range

theorem card_rootGroupPSL2 [Finite F] : Nat.card (rootGroupPSL2 F) = Nat.card F := by
  rw [rootGroupPSL2, ← Nat.card_congr (MonoidHom.ofInjective rootHomPSL2_injective).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem rootGroupPSL2_comm {x y : ProjectiveSpecialLinearGroup (Fin 2) F}
    (hx : x ∈ rootGroupPSL2 F) (hy : y ∈ rootGroupPSL2 F) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem rootGroupPSL2_pow {r : ℕ} [CharP F r] {x : ProjectiveSpecialLinearGroup (Fin 2) F}
    (hx : x ∈ rootGroupPSL2 F) : x ^ r = 1 := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a ^ r = 1 := by
    rw [← ofAdd_toAdd a, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero]
  rw [← map_pow, ha, map_one]

theorem rootPSL2_mem_rootGroupPSL2 : rootPSL2 F ∈ rootGroupPSL2 F :=
  ⟨Multiplicative.ofAdd 1, rfl⟩

end Model

theorem center_eq_bot_of_isCyclic_sylow {G : Type*} [Group G] [Finite G]
    [hperf : Group.IsPerfect G] (hZ : Nat.card (Subgroup.center G) ∣ 3)
    (hcyc : ∀ Q : Sylow 3 (G ⧸ Subgroup.center G), IsCyclic Q) : Subgroup.center G = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  set π := QuotientGroup.mk' (Subgroup.center G) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hQ : IsCyclic ((P : Subgroup G).map π) := by
    have := hcyc (P.mapSurjective hπ)
    rwa [Sylow.coe_mapSurjective] at this
  let φ : (P : Subgroup G) →* (P : Subgroup G).map π :=
    (π.comp (P : Subgroup G).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  have hker : φ.ker ≤ Subgroup.center (P : Subgroup G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    have hxZ : (x : G) ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).mp hx'
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ y)
  have hPab : IsMulCommutative (P : Subgroup G) :=
    φ.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hZp : IsPGroup 3 (Subgroup.center G) := IsPGroup.of_card_dvd_pow (n := 1) (by rwa [pow_one])
  have h := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup P hPab le_rfl hZp
  rwa [hperf.commutator_eq_top, inf_top_eq] at h

theorem isCyclic_sylow_three_of_not_dvd {S : Type*} [Group S] [Finite S]
    (h9 : ¬ 9 ∣ Nat.card S) (Q : Sylow 3 S) : IsCyclic Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hdvd : 3 ^ k ∣ Nat.card S := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    exact h9 ((pow_dvd_pow 3 h).trans hdvd)
  interval_cases k
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
    infer_instance
  · exact isCyclic_of_prime_card (by rw [hk, pow_one])

theorem isCyclic_sylow_of_mulEquiv {S T : Type*} [Group S] [Group T] [Finite S] (e : S ≃* T)
    {r : ℕ} [Fact r.Prime] (h : ∀ R : Sylow r T, IsCyclic R) (Q : Sylow r S) : IsCyclic Q := by
  have hQ := h (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
  change IsCyclic ((Q : Subgroup S).map e.toMonoidHom) at hQ
  exact isCyclic_of_surjective
    ((Q : Subgroup S).equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    ((Q : Subgroup S).equivMapOfInjective e.toMonoidHom e.injective).symm.surjective

theorem coprime_self_pow_sub_one {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) :
    Nat.Coprime p (p ^ k - 1) := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓp hℓq
  have h1 : ℓ ∣ p ^ k := hℓp.trans (dvd_pow_self p (by omega))
  have h2 : ℓ ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub h1 hℓq
  have h3 : p ^ k - (p ^ k - 1) = 1 := by
    have := Nat.one_le_pow k p hp
    omega
  rw [h3] at h2
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

theorem eq_one_of_card_psl2_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1))) : f = 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp2' : 9 ≤ p ^ 2 := by nlinarith
  have hp3' : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have hf3 : f ≤ 3 := by
    have hq2 : 2 ∣ (p ^ f) ^ 2 - 1 := by
      obtain ⟨k, hk⟩ := (hodd.pow (n := f)).pow (n := 2)
      exact ⟨k, by omega⟩
    have hqd : p ^ f ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
      refine dvd_trans ?_ h
      rw [Nat.mul_div_assoc _ hq2]
      exact Dvd.intro _ rfl
    have hcop : Nat.Coprime (p ^ f) ((p ^ 2 - 1) * (p ^ 3 - 1)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.mul_right
        (coprime_self_pow_sub_one (by omega) (by norm_num))
        (coprime_self_pow_sub_one (by omega) (by norm_num)))
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcop.dvd_of_dvd_mul_right hqd)
  interval_cases f
  · rfl
  ·
    exfalso
    obtain ⟨m, hm⟩ : ∃ m, p ^ 2 + 1 = 2 * m := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨2 * k ^ 2 + 2 * k + 1, by rw [hk]; ring⟩
    have hsq : (p ^ 2) ^ 2 - 1 = (p ^ 2 - 1) * (2 * m) := by
      rw [← hm, mul_comm, ← Nat.sq_sub_sq, one_pow]
    have hN : p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2 = p ^ 2 * (p ^ 2 - 1) * m := by
      rw [hsq, show p ^ 2 * ((p ^ 2 - 1) * (2 * m)) = 2 * (p ^ 2 * (p ^ 2 - 1) * m) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hN, show p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) =
      p ^ 2 * (p ^ 2 - 1) * (p * (p ^ 3 - 1)) by ring] at h
    have hpos : 0 < p ^ 2 * (p ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
    have h1 : m ∣ p * (p ^ 3 - 1) := Nat.dvd_of_mul_dvd_mul_left hpos h
    have hcop : Nat.Coprime m p := by
      apply Nat.coprime_of_dvd
      intro ℓ hℓ hℓm hℓp
      have h2 : ℓ ∣ p ^ 2 + 1 := hm ▸ hℓm.mul_left 2
      have h3 : ℓ ∣ p ^ 2 := hℓp.trans (dvd_pow_self p (by norm_num))
      have h4 : ℓ ∣ p ^ 2 + 1 - p ^ 2 := Nat.dvd_sub h2 h3
      rw [show p ^ 2 + 1 - p ^ 2 = 1 by omega] at h4
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h4)
    have h2 : m ∣ p ^ 3 - 1 := hcop.dvd_of_dvd_mul_left h1
    have h3 : m ∣ p ^ 3 + p := ⟨2 * p, by nlinarith [hm]⟩
    have h4 : m ∣ (p ^ 3 + p) - (p ^ 3 - 1) := Nat.dvd_sub h3 h2
    rw [show (p ^ 3 + p) - (p ^ 3 - 1) = p + 1 by omega] at h4
    have h5 := Nat.le_of_dvd (by omega) h4
    nlinarith
  ·
    exfalso
    obtain ⟨k, hk⟩ : ∃ k, p ^ 3 + 1 = 2 * k := by
      obtain ⟨t, ht⟩ := hodd.pow (n := 3)
      exact ⟨t + 1, by omega⟩
    have hsq : (p ^ 3) ^ 2 - 1 = (p ^ 3 - 1) * (2 * k) := by
      rw [← hk, mul_comm, ← Nat.sq_sub_sq, one_pow]
    have hN : p ^ 3 * ((p ^ 3) ^ 2 - 1) / 2 = p ^ 3 * (p ^ 3 - 1) * k := by
      rw [hsq, show p ^ 3 * ((p ^ 3 - 1) * (2 * k)) = 2 * (p ^ 3 * (p ^ 3 - 1) * k) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hN, show p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) = p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) by
      ring] at h
    have hpos : 0 < p ^ 3 * (p ^ 3 - 1) := Nat.mul_pos (by positivity) (by omega)
    have h1 : k ∣ p ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left hpos h
    have h2 := Nat.le_of_dvd (by omega) h1
    have h3 : 3 * p ^ 2 ≤ p ^ 3 :=
      calc 3 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp3
        _ = p ^ 3 := by ring
    omega

section Cases

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def toPSL2 {H : Type*} [Group H] {F : Type} [Field F]
    (e : H ≃* StatedProj (StatedSL 2 F)) : H ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm

theorem card_dvd_of_det_eq_one {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) :
    Nat.card H ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  have hle : H ≤ (Matrix.SpecialLinearGroup.toGL : SL(3, ZMod p) →* GL (Fin 3) (ZMod p)).range :=
    fun x hx => (mem_range_toGL_iff x).mpr (hdet x hx)
  have h1 := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h1
  simpa using h1

theorem linear_two_defining (hp2 : p ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod p))}
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {f : ℕ} (hf : 1 ≤ f) (hq3 : p ^ f ≠ 3)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    f = 1 ∧ Subgroup.center H = ⊥ ∧
      ∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hS : Nat.card (H ⧸ Subgroup.center H) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two hodd.pow hF]
  have hf1 : f = 1 := eq_one_of_card_psl2_dvd hp hp2 hf
    (hS ▸ (Subgroup.card_quotient_dvd_card _).trans (card_dvd_of_det_eq_one hdet))
  subst hf1
  rw [pow_one] at hF hq3
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hZ1 : Subgroup.center H = ⊥ := by
    apply center_eq_bot_of_isCyclic_sylow hZ
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    by_cases hp7 : 7 ≤ p
    · apply isCyclic_sylow_of_mulEquiv (toPSL2 e)
      exact CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
        (p := p) (f := 1) (by rw [hF, pow_one]) (by rw [hF]; exact hp7) 3 (by norm_num)
        (by
          rw [hF]
          exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega))
    · have hp5' : p = 5 := by
        rcases hodd with ⟨k, rfl⟩
        omega
      intro Q
      apply isCyclic_sylow_three_of_not_dvd
      rw [hS, hp5']
      norm_num
  refine ⟨rfl, hZ1, ?_⟩
  exact eq_omegaGL_of_mulEquiv_psl2 hp5 hirr hdet hF
    (((QuotientGroup.quotientBot (G := H)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ1.symm)).trans e)

theorem linear_two_cross {H : Subgroup (GL (Fin 3) (ZMod p))} [Group.IsPerfect H]
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrp : r ≠ p) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = r ^ f) (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    (r = 5 ∨ r = 7) ∧ f = 1 ∧ Subgroup.center H = ⊥ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : CharP F r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hF
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hr3' : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr hr3
  have hrK : (r : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff r p).mp h
    exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hr).mp this).symm
  have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
  set e' := toPSL2 e with he'
  set u := e'.symm (rootPSL2 F) with hudef
  have hu1 : u ≠ 1 := fun h =>
    rootPSL2_ne_one (e'.symm.injective (by rw [← hudef, h, map_one]))
  have hur : u ^ r = 1 := by
    rw [hudef, ← map_pow, rootGroupPSL2_pow rootPSL2_mem_rootGroupPSL2, map_one]
  obtain ⟨x, hxu, hxr⟩ := exists_lift_pow_eq_one le_rfl hZ3 hr3' u hur
  set X : GL (Fin 3) (ZMod p) := (x : GL (Fin 3) (ZMod p)) with hXdef
  have hX1 : X ≠ 1 := fun h => hu1 (by
    rw [← hxu, show x = 1 from Subtype.ext h, QuotientGroup.mk_one])
  have hXr : X ^ r = 1 := by rw [hXdef, ← Subgroup.coe_pow, hxr, Subgroup.coe_one]
  have hconj : ∀ k : ℕ, (∃ a : Fˣ, (k : F) = (a : F) ^ 2) →
      IsConj X (X ^ (k : ZMod r).val) := by
    rintro k ⟨a, ha⟩
    have hS : IsConj u (u ^ k) := by
      obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_rootPSL2_pow (F := F) ha)
      exact isConj_iff.mpr ⟨e'.symm c, by
        rw [hudef, ← map_pow, ← map_inv, ← map_mul, ← map_mul, hc]⟩
    have hH : IsConj x (x ^ k) := isConj_of_isConj_mk le_rfl hZ3 hr3' hxr
      (by rw [← pow_mul, mul_comm, pow_mul, hxr, one_pow])
      (by rw [QuotientGroup.mk_pow, hxu]; exact hS)
    have hval : X ^ (k : ZMod r).val = X ^ k := by
      rw [ZMod.val_natCast]
      conv_rhs => rw [← Nat.div_add_mod k r, pow_add, pow_mul, hXr, one_pow, one_mul]
    rw [hval, hXdef, ← Subgroup.coe_pow]
    exact H.subtype.map_isConj hH
  have hr7 : r ≤ 7 := by
    by_contra hr7
    push Not at hr7
    have hr11 : 11 ≤ r := by
      by_contra h
      push Not at h
      interval_cases r <;> norm_num at hr
    set Q := (Finset.Icc 1 4).image (fun m : ℕ => ((m ^ 2 : ℕ) : ZMod r)) with hQdef
    have hQcard : Q.card = 4 := by
      rw [hQdef, Finset.card_image_of_injOn]
      · simp
      · intro m₁ hm₁ m₂ hm₂ h
        simp only [Finset.coe_Icc, Set.mem_Icc] at hm₁ hm₂
        have h' : ((m₁ : ZMod r) - m₂) * ((m₁ : ZMod r) + m₂) = 0 := by
          have h'' : ((m₁ ^ 2 : ℕ) : ZMod r) = ((m₂ ^ 2 : ℕ) : ZMod r) := h
          push_cast at h''
          linear_combination h''
        rcases mul_eq_zero.mp h' with h1 | h1
        · have h1' : (m₁ : ZMod r) = m₂ := sub_eq_zero.mp h1
          rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)] at h1'
        · exfalso
          have h1' : ((m₁ + m₂ : ℕ) : ZMod r) = 0 := by push_cast; exact h1
          rw [ZMod.natCast_eq_zero_iff] at h1'
          have := Nat.le_of_dvd (by omega) h1'
          omega
    have hQ : ∀ k ∈ Q, k ≠ 0 ∧ IsConj X (X ^ k.val) := by
      intro k hk
      rw [hQdef, Finset.mem_image] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      simp only [Finset.mem_Icc] at hm
      have hmF : (m : F) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff F r]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      refine ⟨?_, hconj (m ^ 2) ⟨Units.mk0 (m : F) hmF, by rw [Units.val_mk0, Nat.cast_pow]⟩⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) (hr.dvd_of_dvd_pow hd)
      omega
    have := card_le_three_of_isConj_pow hrK hXr hX1 Q hQ
    omega
  have hr57 : r = 5 ∨ r = 7 := by
    interval_cases r
    all_goals first | (left; rfl) | (right; rfl) | (exfalso; norm_num at hr)
  set π := QuotientGroup.mk' (Subgroup.center H) with hπ
  set U := (rootGroupPSL2 F).map e'.symm.toMonoidHom with hUdef
  have hUcomm : ∀ y ∈ U, ∀ z ∈ U, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, rootGroupPSL2_comm hy hz]
  have hUexp : ∀ y ∈ U, y ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, rootGroupPSL2_pow hy, map_one]
  have hUp : IsPGroup r U := fun y =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hUexp _ y.2, Subgroup.coe_one])⟩
  have hcen : π.ker ≤ Subgroup.center H := by rw [hπ, QuotientGroup.ker_mk']
  have hC : ¬ r ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (h.trans hZ))
  let eU := CFSG.LieType.CentralExt.liftSubgroupEquiv (QuotientGroup.mk'_surjective _) hcen hC hUp
  set E := (CFSG.LieType.CentralExt.liftSubgroup r π U).map H.subtype with hE
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : eU (⟨a, ha⟩ * ⟨b, hb⟩) = eU (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext (hUcomm _ (eU ⟨a, ha⟩).2 _ (eU ⟨b, hb⟩).2)
    have h3 : a * b = b * a := congrArg Subtype.val (eU.injective h1)
    exact congrArg Subtype.val h3
  have hEexp : ∀ a ∈ E, a ^ r = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : eU (⟨a, ha⟩ ^ r) = eU 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hUexp _ (eU ⟨a, ha⟩).2, Subgroup.coe_one])
    have h3 : a ^ r = 1 := congrArg Subtype.val (eU.injective h1)
    change (a : GL (Fin 3) (ZMod p)) ^ r = 1
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  have hEdet : ∀ a ∈ E, (a : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact hdet _ a.2
  have hEcard : Nat.card E = r ^ f := by
    rw [hE, Subgroup.card_map_of_injective H.subtype_injective, Nat.card_congr eU.toEquiv, hUdef,
      Subgroup.card_map_of_injective e'.symm.injective, card_rootGroupPSL2, hF]
  have hf2 : f ≤ 2 := by
    have := card_le_sq_of_elementary hrK E hEcomm hEexp hEdet
    rw [hEcard] at this
    exact (Nat.pow_le_pow_iff_right hr.one_lt).mp this
  have hf1 : f = 1 := by
    rcases (by omega : f = 1 ∨ f = 2) with h | h
    · exact h
    exfalso
    subst h
    have : Fintype F := Fintype.ofFinite F
    have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F r]; exact hr2
    have hcard : Fintype.card F = r ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
    have hsq : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∃ a : Fˣ, (k : F) = (a : F) ^ 2 := by
      intro k hk1 hk4
      have hk0 : (k : F) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff F r]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      have hpow : (k : F) ^ (Fintype.card F / 2) = 1 := by
        rw [hcard]
        rcases hr57 with rfl | rfl
        · have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
          have h4 : (k : F) ^ 4 = 1 := by
            interval_cases k
            · norm_num
            · norm_num; linear_combination 3 * h5
            · norm_num; linear_combination 16 * h5
            · norm_num; linear_combination 51 * h5
          rw [show 5 ^ 2 / 2 = 4 * 3 by norm_num, pow_mul, h4, one_pow]
        · have h7 : (7 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 7
          have h6 : (k : F) ^ 6 = 1 := by
            interval_cases k
            · norm_num
            · norm_num; linear_combination 9 * h7
            · norm_num; linear_combination 104 * h7
            · norm_num; linear_combination 585 * h7
          rw [show 7 ^ 2 / 2 = 6 * 4 by norm_num, pow_mul, h6, one_pow]
      obtain ⟨b, hb⟩ := (FiniteField.isSquare_iff hchar hk0).mpr hpow
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hb
        exact hk0 hb
      exact ⟨Units.mk0 b hb0, by rw [Units.val_mk0, hb, sq]⟩
    set Q := (Finset.Icc 1 4).image (fun m : ℕ => ((m : ℕ) : ZMod r)) with hQdef
    have hQcard : Q.card = 4 := by
      rw [hQdef, Finset.card_image_of_injOn]
      · simp
      · intro m₁ hm₁ m₂ hm₂ h
        simp only [Finset.coe_Icc, Set.mem_Icc] at hm₁ hm₂
        have h' : (m₁ : ZMod r) = m₂ := h
        rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at h'
    have hQ : ∀ k ∈ Q, k ≠ 0 ∧ IsConj X (X ^ k.val) := by
      intro k hk
      rw [hQdef, Finset.mem_image] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      simp only [Finset.mem_Icc] at hm
      refine ⟨?_, hconj m (hsq m hm.1 hm.2)⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have := card_le_three_of_isConj_pow hrK hXr hX1 Q hQ
    omega
  subst hf1
  refine ⟨hr57, rfl, ?_⟩
  have hS : Nat.card (H ⧸ Subgroup.center H) = r ^ 1 * ((r ^ 1) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two (hr.odd_of_ne_two hr2).pow hF]
  apply center_eq_bot_of_isCyclic_sylow hZ
  intro Q
  apply isCyclic_sylow_three_of_not_dvd
  rw [hS]
  rcases hr57 with rfl | rfl <;> norm_num

theorem linear_two_three (hp3 : p ≠ 3) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * x) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {f : ℕ} (hf : 1 ≤ f) (hq3 : 3 ^ f ≠ 3)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3 ^ f)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    f = 2 ∧ Nat.card (Subgroup.center H) = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_three hF
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp this)
  have hf2 : 2 ≤ f := by
    by_contra h
    push Not at h
    interval_cases f
    exact hq3 rfl
  set e' := toPSL2 e with he'
  set π := QuotientGroup.mk' (Subgroup.center H) with hπ
  set U := (rootGroupPSL2 F).map e'.symm.toMonoidHom with hUdef
  have hUcomm : ∀ y ∈ U, ∀ z ∈ U, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, rootGroupPSL2_comm hy hz]
  have hUexp : ∀ y ∈ U, y ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, rootGroupPSL2_pow hy, map_one]
  have hUcard : Nat.card U = 3 ^ f := by
    rw [hUdef, Subgroup.card_map_of_injective e'.symm.injective, card_rootGroupPSL2, hF]
  set Ũ := U.comap π with hŨ
  have hŨcard : Nat.card Ũ = 3 ^ f * Nat.card (Subgroup.center H) := by
    have h1 := Subgroup.card_mul_index Ũ
    have h2 := Subgroup.card_mul_index U
    have h3 : Ũ.index = U.index :=
      Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective _)
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
    have hi : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [h3, h4, ← h2] at h1
    rw [← hUcard]
    apply Nat.eq_of_mul_eq_mul_right hi
    rw [h1]
    ring
  set R := Ũ.map H.subtype with hR
  have hRcard : Nat.card R = Nat.card Ũ := Subgroup.card_map_of_injective H.subtype_injective
  have hcenscal : ∀ z ∈ Subgroup.center H, ∃ c : ZMod p,
      ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.scalar (Fin 3) c := by
    intro z hz
    apply hscal
    intro y hy
    have := congrArg (fun g : H => ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)))
      (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
    simpa using this
  have hcomm_mem : ∀ y ∈ Ũ, ∀ z ∈ Ũ, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.center H := by
    intro y hy z hz
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    have hc := hUcomm _ (Subgroup.mem_comap.mp hy) _ (Subgroup.mem_comap.mp hz)
    change (y : H ⧸ Subgroup.center H) * z = z * y at hc
    rw [hc]
    group
  have hcube_mem : ∀ y ∈ Ũ, y ^ 3 ∈ Subgroup.center H := by
    intro y hy
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]
    exact hUexp _ (Subgroup.mem_comap.mp hy)
  have hRdet : ∀ a ∈ R, (a : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact hdet _ a.2
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, ∃ c : ZMod p,
      ((a * b * a⁻¹ * b⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        Matrix.scalar (Fin 3) c := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact hcenscal _ (hcomm_mem y hy z hz)
  have hRcube : ∀ a ∈ R, ∃ c : ZMod p,
      ((a ^ 3 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        Matrix.scalar (Fin 3) c := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcenscal _ (hcube_mem y hy)
  have hRle := card_le_twentyseven_of_scalar_commutators h3 R hRdet hRcomm hRcube
  rw [hRcard, hŨcard] at hRle
  rcases (Nat.dvd_prime Nat.prime_three).mp hZ with hZ1 | hZ3
  ·
    exfalso
    have hZbot : Subgroup.center H = ⊥ := Subgroup.card_eq_one.mp hZ1
    have hRcomm' : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      have h1 := hcomm_mem y hy z hz
      rw [hZbot, Subgroup.mem_bot] at h1
      have h2 : y * z = z * y := by
        calc y * z = y * z * y⁻¹ * z⁻¹ * (z * y) := by group
          _ = z * y := by rw [h1, one_mul]
      exact congrArg Subtype.val h2
    have hRexp : ∀ a ∈ R, a ^ 3 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hcube_mem y hy
      rw [hZbot, Subgroup.mem_bot] at h1
      change (y : GL (Fin 3) (ZMod p)) ^ 3 = 1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hR9 := card_le_sq_of_elementary (r := 3) (by exact_mod_cast h3) R hRcomm' hRexp hRdet
    rw [hRcard, hŨcard, hZ1, mul_one] at hR9
    have hf2' : f = 2 := le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp hR9) hf2
    obtain ⟨a, haR, ha1, c, hac⟩ := exists_scalar_of_card_eq_nine h3 R hRcomm' hRexp hRdet
      (by rw [hRcard, hŨcard, hZ1, mul_one, hf2']; norm_num)
    obtain ⟨y, -, rfl⟩ := haR
    have hyc : y ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact commute_of_coe_eq_scalar hac (g : GL (Fin 3) (ZMod p))
    rw [hZbot, Subgroup.mem_bot] at hyc
    exact ha1 (by rw [hyc]; rfl)
  ·
    rw [hZ3] at hRle
    have h9 : 3 ^ f ≤ 3 ^ 2 := by omega
    exact ⟨le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp h9) hf2, hZ3⟩

theorem linear_two_cases (hp2 : p ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod p))}
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * x) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hq3 : r ^ f ≠ 3) {F : Type} [Field F] [Finite F] (hF : Nat.card F = r ^ f)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    (r = p ∧ f = 1 ∧ Subgroup.center H = ⊥ ∧
        ∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M) ∨
      (r ≠ p ∧ (r = 5 ∨ r = 7) ∧ f = 1 ∧ Subgroup.center H = ⊥) ∨
      (r = 3 ∧ r ≠ p ∧ f = 2 ∧ Nat.card (Subgroup.center H) = 3) := by
  by_cases hrp : r = p
  · subst hrp
    exact Or.inl ⟨rfl, linear_two_defining hp2 hirr hdet hZ hf hq3 hF e⟩
  · by_cases hr3 : r = 3
    · subst hr3
      exact Or.inr (Or.inr ⟨rfl, hrp, linear_two_three (Ne.symm hrp) hscal hdet hZ hf hq3 hF e⟩)
    · exact Or.inr (Or.inl ⟨hrp, linear_two_cross hdet hZ hr hr2 hr3 hrp hf hF e⟩)

end Cases

end CFSG.RankThree.SubgroupLists
