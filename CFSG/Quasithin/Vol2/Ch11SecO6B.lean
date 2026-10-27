module

public import CFSG.Quasithin.Vol2.Ch11SecO6A
public import CFSG.Quasithin.Vol2.Ch11SecO6C
public import CFSG.Quasithin.Vol2.Ch11SecGTShape
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative MatrixGroups commutatorElement

theorem card_frattiniQuot_le_of_gen {P : Type*} [Group P] [Finite P] {r : ℕ} [Fact r.Prime]
    [Fact (IsPGroup r P)] (g₁ g₂ : P) (hg : ∀ x : P, ∃ a b : ℕ, x = g₁ ^ a * g₂ ^ b) :
    Nat.card (P ⧸ frattini P) ≤ r ^ 2 := by
  have : IsElementaryAbelian r (P ⧸ frattini P) := CFSG.isElementaryAbelian_quotient_frattini
  have hpow : ∀ v : P ⧸ frattini P, v ^ r = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p r _)
  have hmod : ∀ (v : P ⧸ frattini P) (a : ℕ), v ^ a = v ^ (a % r) := fun v a => by
    conv_lhs => rw [← Nat.div_add_mod a r, pow_add, pow_mul, hpow, one_pow, one_mul]
  let f : Fin r × Fin r → P ⧸ frattini P := fun ij =>
    ((g₁ : P) : P ⧸ frattini P) ^ (ij.1 : ℕ) * ((g₂ : P) : P ⧸ frattini P) ^ (ij.2 : ℕ)
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨a, b, rfl⟩ := hg x
    have hr := (Fact.out : r.Prime).pos
    refine ⟨(⟨a % r, Nat.mod_lt _ hr⟩, ⟨b % r, Nat.mod_lt _ hr⟩), ?_⟩
    simp only [f, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    rw [← hmod, ← hmod]
  calc Nat.card (P ⧸ frattini P) ≤ Nat.card (Fin r × Fin r) := Nat.card_le_card_of_surjective f hf
    _ = r ^ 2 := by simp [sq]

theorem card_frattiniQuot_le_of_pOnePlusTwo {P : Type*} [Group P] [Finite P] {r : ℕ}
    [Fact r.Prime] (h : IsPOnePlusTwo r P) : Nat.card (P ⧸ frattini P) ≤ r ^ 2 := by
  obtain ⟨hE, hcard, -⟩ := h
  have : Fact (IsPGroup r P) := ⟨IsExtraspecial.isPGroup r P⟩
  have hne : commutator P ≠ ⊥ := by
    intro hb
    have hc : Subgroup.center P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have hm : ⁅y, x⁆ ∈ commutator P :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    have hnt := IsExtraspecial.quotient_nontrivial r P
    obtain ⟨a, b, hab⟩ := exists_pair_ne (P ⧸ Subgroup.center P)
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [QuotientGroup.eq, hc]
    exact Subgroup.mem_top _
  have hr : r ≤ Nat.card (commutator P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((Fact.out : IsPGroup r P).to_subgroup (commutator P))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hne (Subgroup.eq_bot_of_card_eq _ hk)
    rw [hk]
    exact Nat.le_self_pow hk0 r
  have hle : Nat.card (commutator P) ≤ Nat.card (frattini P) :=
    Subgroup.card_le_of_le (CFSG.commutator_le_frattini_of_isPGroup (p := r))
  have hmul := (frattini P).card_eq_card_quotient_mul_card_subgroup
  rw [hcard] at hmul
  by_contra hlt
  push Not at hlt
  have h1 : (r ^ 2 + 1) * r ≤ Nat.card (P ⧸ frattini P) * Nat.card (frattini P) :=
    Nat.mul_le_mul hlt (hr.trans hle)
  rw [← hmul] at h1
  nlinarith [h1, (Fact.out : r.Prime).pos]

structure Case1Data (X : Type) [Group X] [Finite X] : Prop where
  struct : SecG.Case1Struct X
  rank : ∀ r : ℕ, r.Prime → r ∣ Nat.card (CFSG.fittingSubgroup X) →
    Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) ≤ r ^ 2

theorem case1Data_of_shape {X : Type} [Group X] [Finite X]
    (h : A36Case4 X ∨ ∃ q : ℕ, q.Prime ∧ (q % 5 = 1 ∨ q % 5 = 4) ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧
      CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
      IsElemAbelianOfRank q 2 ↥(CFSG.fittingSubgroup X) ∧
      NaturalSL2Action q X (CFSG.fittingSubgroup X)) : Case1Data X := by
  rcases h with h4 | ⟨q, hq, hq5, -, hFF, hE, hN⟩
  · refine ⟨SecG.case1Struct_of_a36Case4 h4, fun r hr hrF => ?_⟩
    have : Fact r.Prime := ⟨hr⟩
    have : Fact (IsPGroup r ↥(CFSG.pCore r X)) := ⟨CFSG.pCore_isPGroup⟩
    rcases (h4.2.2.2 r hr hrF).2 with h1 | ⟨n, -, ⟨e⟩⟩
    · exact card_frattiniQuot_le_of_pOnePlusTwo h1
    · have : NeZero (r ^ n) := ⟨pow_ne_zero _ (Fact.out : r.Prime).ne_zero⟩
      refine card_frattiniQuot_le_of_gen (e.symm (Multiplicative.ofAdd 1, 1))
        (e.symm (1, Multiplicative.ofAdd 1)) fun x => ?_
      refine ⟨(Multiplicative.toAdd (e x).1).val, (Multiplicative.toAdd (e x).2).val, ?_⟩
      apply e.injective
      rw [map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, Prod.pow_fst, one_pow, mul_one]
        rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      · simp only [Prod.snd_mul, Prod.pow_snd, one_pow, one_mul]
        rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  · refine ⟨SecG.case1Struct_of_natural hq hq5 hFF hE hN, fun r hr hrF => ?_⟩
    obtain ⟨eF⟩ := hE
    have hcard : Nat.card (CFSG.fittingSubgroup X) = q ^ 2 := by
      rw [Nat.card_congr eF.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow (hcard ▸ hrF))
    subst hrq
    have : Fact r.Prime := ⟨hr⟩
    calc Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))
        ≤ Nat.card ↥(CFSG.pCore r X) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      _ ≤ Nat.card (CFSG.fittingSubgroup X) := Subgroup.card_le_of_le (CFSG.pCore_le_fitting X r)
      _ = r ^ 2 := hcard

theorem mem_center_of_sq_eq_one {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {g : SL(2, k)}
    (hg : g ^ 2 = 1) : g ∈ Subgroup.center SL(2, k) := by
  have hm : (g : Matrix (Fin 2) (Fin 2) k) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hg, Matrix.SpecialLinearGroup.coe_one]
  have hdet : (g : Matrix (Fin 2) (Fin 2) k).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) k => A 0 0) hm
  have e01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) k => A 0 1) hm
  have e10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) k => A 1 0) hm
  have e11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) k => A 1 1) hm
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  set a := (g : Matrix (Fin 2) (Fin 2) k) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) k) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) k) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) k) 1 1
  have hsum : a + d ≠ 0 := by
    intro h
    apply h2
    have : d = -a := by linear_combination h
    rw [this] at hdet
    linear_combination -(hdet + e00)
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hsum
  have had : a = d := by
    have h1 : a * a = 1 := by rw [hb] at e00; linear_combination e00
    have h3 : a * d = 1 := by rw [hb] at hdet; linear_combination hdet
    have ha : a ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
    exact mul_left_cancel₀ ha (h1.trans h3.symm)
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨a, ?_, ?_⟩
  · have h1 : a * a = 1 := by rw [hb] at e00; linear_combination e00
    simp [Fintype.card_fin, sq, h1]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, had, Matrix.scalar_apply]

variable {X : Type} [Group X] [Finite X]

theorem oddCore_eq (hD : Case1Data X) : CFSG.oddCore X = CFSG.fittingSubgroup X := by
  obtain ⟨-, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hD.struct
  have : Fact q.Prime := ⟨hq⟩
  have hFodd : Odd (Nat.card (CFSG.fittingSubgroup X)) := by
    rw [Nat.odd_iff]
    by_contra h
    have := hprimes 2 Nat.prime_two (Nat.dvd_of_mod_eq_zero (by omega))
    omega
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hFodd⟩)
  have hO : Odd (Nat.card (CFSG.oddCore X)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := X)
  have hb : (CFSG.oddCore X).map ψ = ⊥ := by
    refine SecG.SL2.eq_bot_of_normal_of_odd (by rw [Nat.card_zmod]; omega) _
      (Subgroup.Normal.map inferInstance ψ hψ) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Nat.card (CFSG.oddCore X), hO, ?_⟩
    rw [← map_pow]
    have h1 := pow_card_eq_one' (G := CFSG.oddCore X) (x := ⟨x, hx⟩)
    rw [show x ^ Nat.card (CFSG.oddCore X) = 1 from congrArg Subtype.val h1, map_one]
  intro x hx
  rw [← hker, MonoidHom.mem_ker]
  have : ψ x ∈ (CFSG.oddCore X).map ψ := ⟨x, hx, rfl⟩
  rwa [hb, Subgroup.mem_bot] at this

section Act

variable (r : ℕ) [Fact r.Prime]

@[expose] noncomputable def linConj :
    X →* Module.End (ZMod r) (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) where
  toFun x := linV r (MulAut.conj x)
  map_one' := by rw [map_one, linV_one]
  map_mul' x y := by rw [map_mul, linV_mul]

theorem mem_ker_linConj {x : X} :
    x ∈ (linConj r).ker ↔ ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) x := by
  rw [MonoidHom.mem_ker, actsTrivially_iff, actsScalar_iff_linV, Nat.cast_one, one_smul]
  rfl

theorem fitting_acts_triv {f : X} (hf : f ∈ CFSG.fittingSubgroup X) :
    ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) f := by
  rw [← mem_ker_linConj]
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hf
  refine (iSup_le fun s => ?_ : _ ≤ (linConj r).ker) hf
  have hs : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
  have : Fact (s : ℕ).Prime := ⟨hs⟩
  intro d hd
  rw [mem_ker_linConj]
  intro c hc
  by_cases hsr : (s : ℕ) = r
  · have : Fact (IsPGroup r ↥(CFSG.pCore r X)) := ⟨CFSG.pCore_isPGroup⟩
    have hdr : d ∈ CFSG.pCore r X := hsr ▸ hd
    have hm : ⁅(⟨c, hc⟩ : ↥(CFSG.pCore r X))⁻¹, ⟨d, hdr⟩⁆ ∈ frattini ↥(CFSG.pCore r X) :=
      CFSG.commutator_le_frattini_of_isPGroup (p := r)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    refine ⟨_, hm, ?_⟩
    simp only [commutatorElement_def, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      inv_inv]
    group
  · have hdis : Disjoint (CFSG.pCore (s : ℕ) X) (CFSG.pCore r X) :=
      IsPGroup.disjoint_of_ne (s : ℕ) r hsr _ _ CFSG.pCore_isPGroup CFSG.pCore_isPGroup
    have hcomm : ⁅d, c⁆ = 1 := by
      have h1 : ⁅d, c⁆ ∈ ⁅CFSG.pCore (s : ℕ) X, CFSG.pCore r X⁆ :=
        Subgroup.commutator_mem_commutator hd hc
      have h2 := Subgroup.commutator_le_inf (CFSG.pCore (s : ℕ) X) (CFSG.pCore r X) h1
      rw [hdis.eq_bot, Subgroup.mem_bot] at h2
      exact h2
    have e : c⁻¹ * (d * c * d⁻¹) = 1 := by
      rw [commutatorElement_def] at hcomm
      calc c⁻¹ * (d * c * d⁻¹) = c⁻¹ * (d * c * d⁻¹ * c⁻¹) * c := by group
        _ = 1 := by rw [hcomm, mul_one, inv_mul_cancel]
    rw [e]
    exact Subgroup.one_mem _

theorem isPGroup_range_conjNormal (hT : ∀ x : X, x ∈ (linConj r).ker) :
    IsPGroup r (MulAut.conjNormal (H := CFSG.pCore r X)).range := by
  set A := (MulAut.conjNormal (H := CFSG.pCore r X)).range
  have hA : A ≤ CFSG.SignalizerFunctor.Helpers.frattiniAutomorphismKernel ↥(CFSG.pCore r X) := by
    rintro _ ⟨x, rfl⟩ d
    obtain ⟨y, hy, hyd⟩ := (mem_ker_linConj r).mp (hT x) d d.2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    have e : d⁻¹ * MulAut.conjNormal x d = y := by
      apply Subtype.ext
      have hyd' : (y : X) = (d : X)⁻¹ * (x * d * x⁻¹) := hyd
      rw [hyd', Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    rw [e]
    exact hy
  refine IsPGroup.of_card (n := (Nat.card A).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {s} hs hsA => ?_)
  by_contra hsr
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' s hsA
  have hs1 : (a : MulAut ↥(CFSG.pCore r X)) ^ s = 1 := by
    rw [← ha, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have hz : IsPGroup s (Subgroup.zpowers (a : MulAut ↥(CFSG.pCore r X))) := by
    rintro ⟨b, hb⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    refine ⟨1, Subtype.ext ?_⟩
    change ((a : MulAut ↥(CFSG.pCore r X)) ^ n) ^ s ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs1, one_zpow]
  have hbot := CFSG.SignalizerFunctor.Helpers.frattini_automorphism_kernel_coprime_subgroup_trivial
    r s (Fact.out) hs (Ne.symm hsr) CFSG.pCore_isPGroup _
    ((Subgroup.zpowers_le).mpr (hA a.2)) hz
  have ha1 : (a : MulAut ↥(CFSG.pCore r X)) = 1 := by
    have h3 : (a : MulAut ↥(CFSG.pCore r X)) ∈ Subgroup.zpowers (a : MulAut _) :=
      Subgroup.mem_zpowers _
    rwa [hbot, Subgroup.mem_bot] at h3
  have h1 : orderOf a = 1 := by
    rw [← Subgroup.orderOf_coe, ha1, orderOf_one]
  rw [h1] at ha
  exact hs.one_lt.ne ha

theorem exists_not_triv (hD : Case1Data X) (hrF : r ∣ Nat.card (CFSG.fittingSubgroup X))
    (h : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ ∨ IsPGroup r (CFSG.fittingSubgroup X)) :
    ∃ x y : X, ¬ ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) (x * y * x⁻¹ * y⁻¹) := by
  by_contra hall
  push Not at hall
  obtain ⟨hCF, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hD.struct
  have : Fact q.Prime := ⟨hq⟩
  have hr5 : 5 ≤ r := hprimes r Fact.out hrF
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ (linConj r).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [mem_ker_linConj, commutatorElement_def]
    exact hall a b
  have hT : ∀ x : X, x ∈ (linConj r).ker := by
    intro x
    have : Group.IsPerfect SL(2, ZMod q) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (ZMod q)
        (by rw [Nat.card_zmod]; omega)
    have hmap : (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map ψ = ⊤ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]
      exact Group.IsPerfect.commutator_eq_top
    obtain ⟨c, hc, hcx⟩ : ψ x ∈ (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map ψ :=
      hmap ▸ Subgroup.mem_top _
    have hf : c⁻¹ * x ∈ CFSG.fittingSubgroup X := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    have := (linConj r).ker.mul_mem (hcomm hc) ((mem_ker_linConj r).mpr (fitting_acts_triv r hf))
    rwa [mul_inv_cancel_left] at this
  have hAr := isPGroup_range_conjNormal r hT
  rcases h with hperf | hF
  ·
    have : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
    have hA1 : ∀ x : X, MulAut.conjNormal (H := CFSG.pCore r X) x = 1 := by
      have : Group.IsPerfect (MulAut.conjNormal (H := CFSG.pCore r X)).range :=
        Group.IsPerfect.range _
      have hbot : (MulAut.conjNormal (H := CFSG.pCore r X)).range = ⊥ := by
        by_contra hne
        have : Nontrivial (MulAut.conjNormal (H := CFSG.pCore r X)).range :=
          (Subgroup.nontrivial_iff_ne_bot _).mpr hne
        exact Group.IsPerfect.not_isNilpotent _ hAr.isNilpotent
      intro x
      have h1 : MulAut.conjNormal (H := CFSG.pCore r X) x ∈
          (MulAut.conjNormal (H := CFSG.pCore r X)).range := ⟨x, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at h1
    have hcent : ∀ x : X, ∀ d ∈ CFSG.pCore r X, x * d * x⁻¹ = d := fun x d hd => by
      have h1 := congrArg (fun α : MulAut ↥(CFSG.pCore r X) => ((α ⟨d, hd⟩ : _) : X)) (hA1 x)
      simpa [MulAut.conjNormal_apply] using h1
    have hFle : CFSG.fittingSubgroup X ≤ CFSG.pCore r X ⊔ CFSG.pPrimeCore r X := by
      rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
      refine iSup_le fun s => ?_
      have hs : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
      by_cases hsr : (s : ℕ) = r
      · rw [hsr]
        exact le_sup_left
      · refine le_sup_of_le_right (le_sSup ⟨CFSG.pCore_normal, ?_⟩)
        have : Fact (s : ℕ).Prime := ⟨hs⟩
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := (s : ℕ)) (G := X))
        rw [hk]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out hs).mpr (Ne.symm hsr))
    set Q := CFSG.fittingSubgroup X ⊓ CFSG.pPrimeCore r X with hQ
    have hQn : Q.Normal := Subgroup.normal_inf_normal _ _
    have hcomm' : ⁅CFSG.fittingSubgroup X, ⊤⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro f hf x _
      have hfx : ⁅f, x⁆ ∈ CFSG.fittingSubgroup X := by
        rw [commutatorElement_def, show f * x * f⁻¹ * x⁻¹ = f * (x * f⁻¹ * x⁻¹) by group]
        exact Subgroup.mul_mem _ hf
          (Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hf) x)
      refine ⟨hfx, ?_⟩
      have hf' := hFle hf
      rw [← SetLike.mem_coe, Subgroup.mul_normal] at hf'
      obtain ⟨a, ha, b, hb, rfl⟩ := hf'
      have ha' : ∀ y : X, a * y = y * a := fun y => by
        have h1 := hcent y a ha
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      have e : ⁅a * b, x⁆ = b * (x * b⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        calc a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x * b⁻¹) * a⁻¹ * x⁻¹ := by group
          _ = b * x * b⁻¹ * a * a⁻¹ * x⁻¹ := by rw [ha' (b * x * b⁻¹)]
          _ = b * (x * b⁻¹ * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hb (Subgroup.Normal.conj_mem CFSG.pPrimeCore_normal _
        (Subgroup.inv_mem _ hb) x)
    have hFQ := SecD.sl2pMultFact_holds X ⊤ (CFSG.fittingSubgroup X) Q q hq (by omega) hperf
      inf_le_left le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
      (Subgroup.normalizer_eq_top_iff.mpr hQn).ge hcomm'
      ⟨ψ.comp (⊤ : Subgroup X).subtype, fun y => by
        obtain ⟨x, hx⟩ := hψ y
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx⟩, by
        ext x
        simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker]⟩
    have hle : CFSG.fittingSubgroup X ≤ CFSG.pPrimeCore r X := by
      rw [hFQ]
      exact inf_le_right
    have h1 := (Subgroup.card_dvd_of_le hle)
    have h2 : Nat.Coprime r (Nat.card (CFSG.pPrimeCore r X)) := CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp h2 (hrF.trans h1)
  ·
    have hFP : CFSG.fittingSubgroup X ≤ CFSG.pCore r X := le_sSup ⟨inferInstance, hF⟩
    obtain ⟨x, hx⟩ := hψ (SecG.SL2.wElt ^ 2)
    obtain ⟨k, hk⟩ := hAr ⟨_, ⟨x, rfl⟩⟩
    have hk' : MulAut.conjNormal (H := CFSG.pCore r X) (x ^ r ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hxF : x ^ r ^ k ∈ CFSG.fittingSubgroup X := by
      apply hCF
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := congrArg (fun α : MulAut ↥(CFSG.pCore r X) => ((α ⟨f, hFP hf⟩ : _) : X)) hk'
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc f * x ^ r ^ k = x ^ r ^ k * f * (x ^ r ^ k)⁻¹ * x ^ r ^ k := by rw [h1]
        _ = x ^ r ^ k * f := by group
    have h1 : (SecG.SL2.wElt ^ 2 : SL(2, ZMod q)) ^ r ^ k = 1 := by
      rw [← hx, ← map_pow, ← MonoidHom.mem_ker, hker]
      exact hxF
    have hw2 := SecG.SL2.sq_eq_one_of_mem_center (SecG.SL2.wElt_sq_mem_center (k := ZMod q))
    have hodd : Nat.Coprime (r ^ k) 2 := Nat.Coprime.pow_left _
      ((Nat.coprime_primes Fact.out Nat.prime_two).mpr (by omega))
    have h3 := pow_gcd_eq_one.mpr ⟨h1, hw2⟩
    rw [Nat.Coprime.gcd_eq_one hodd, pow_one] at h3
    exact wElt_sq_ne_one (p := q) (by omega) h3

theorem card_frattiniQuot_eq (hD : Case1Data X) (hrF : r ∣ Nat.card (CFSG.fittingSubgroup X))
    (hna : ∃ x y : X, ¬ ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) (x * y * x⁻¹ * y⁻¹)) :
    Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) = r ^ 2 := by
  have h2 := finrank_le_two r (hD.rank r Fact.out hrF)
  rw [show Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) =
    Nat.card (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) from rfl,
    ← FiniteField.pow_finrank_eq_natCard r]
  congr 1
  refine le_antisymm h2 ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨x, y, hxy⟩ := hna
  have hsc : ∀ T : Module.End (ZMod r)
      (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))), ∃ c : ZMod r, T = c • 1 := by
    intro T
    refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun v hv => ?_
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have hcomm2 : ∀ A B : Module.End (ZMod r)
      (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))), A * B = B * A := by
    intro A B
    obtain ⟨a, rfl⟩ := hsc A
    obtain ⟨b, rfl⟩ := hsc B
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm a b]
  apply hxy
  rw [← mem_ker_linConj, MonoidHom.mem_ker, map_mul, map_mul, map_mul]
  calc linConj r x * linConj r y * linConj r x⁻¹ * linConj r y⁻¹
      = linConj r x * (linConj r y * linConj r x⁻¹) * linConj r y⁻¹ := by
        rw [mul_assoc (linConj r x)]
    _ = linConj r x * (linConj r x⁻¹ * linConj r y) * linConj r y⁻¹ := by
        rw [hcomm2 (linConj r y)]
    _ = (linConj r x * linConj r x⁻¹) * (linConj r y * linConj r y⁻¹) := by
        simp only [mul_assoc]
    _ = 1 := by rw [← map_mul, ← map_mul, mul_inv_cancel, mul_inv_cancel, map_one, mul_one]

theorem inverts_of_pGroup (hD : Case1Data X) (hrF : r ∣ Nat.card (CFSG.fittingSubgroup X))
    (hF : IsPGroup r (CFSG.fittingSubgroup X)) {s : X} (hs : s ∉ CFSG.fittingSubgroup X)
    (hs2 : s ^ 2 ∈ CFSG.fittingSubgroup X) (h2 : IsPGroup 2 (Subgroup.zpowers s)) :
    ActsScalar r (MulAut.conj s) (r - 1) := by
  obtain ⟨hCF, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hD.struct
  have : Fact q.Prime := ⟨hq⟩
  have hr5 : 5 ≤ r := hprimes r Fact.out hrF
  have hFP : CFSG.fittingSubgroup X ≤ CFSG.pCore r X := le_sSup ⟨inferInstance, hF⟩
  have hna := exists_not_triv r hD hrF (Or.inr hF)
  have hψs : ψ s ∈ Subgroup.center SL(2, ZMod q) := by
    refine mem_center_of_sq_eq_one ?_ ?_
    · intro h
      have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · rw [← map_pow, ← MonoidHom.mem_ker, hker]
      exact hs2
  have hcent : ∀ x : X, x⁻¹ * MulAut.conj s x ∈ CFSG.fittingSubgroup X := by
    intro x
    rw [← hker, MonoidHom.mem_ker, MulAut.conj_apply, map_mul, map_inv, map_mul, map_mul,
      map_inv, ← Subgroup.mem_center_iff.mp hψs (ψ x)]
    group
  obtain ⟨k, hk⟩ := actsScalar_of_comm r (hD.rank r Fact.out hrF)
    (fun f hf => fitting_acts_triv r hf) hna hcent
  have hsq : ActsScalar r (MulAut.conj s ^ 2) 1 := by
    rw [← map_pow, ← actsTrivially_iff]
    exact fitting_acts_triv r hs2
  rcases actsScalar_sign r hk hsq with h1 | h1
  · exfalso
    obtain ⟨e, he⟩ := h2 ⟨s, Subgroup.mem_zpowers s⟩
    have he' : MulAut.conj s ^ 2 ^ e = 1 := by
      rw [← map_pow]
      have : s ^ 2 ^ e = 1 := congrArg Subtype.val he
      rw [this, map_one]
    have hfix := fix_of_actsScalar_one r (by omega) he' h1
    apply hs
    apply hCF
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h3 := hfix f (hFP hf)
    rw [MulAut.conj_apply] at h3
    calc f * s = s * f * s⁻¹ * s := by rw [h3]
      _ = s * f := by group
  · exact h1

end Act


theorem case1Data_kBar {G : Type} [Group G] [Finite G] {K : Subgroup G} {n : ℕ}
    (hl : List11_1_1Two (SecG.Bar.KBar K) n ∨ (n = 2 ∧ List11_1_1Three (SecG.Bar.KBar K)))
    (h1 : Case11_1_2One K) : Case1Data (SecG.Bar.KBar K) := by
  obtain ⟨p, hp, hp5, φ, hφ, -⟩ := SecG.exists_oddCore_of_case11_1_2One h1
  have : Fact p.Prime := ⟨hp⟩
  exact case1Data_of_shape (shape_of_lists hl (by omega) hφ)

end CFSG.Quasithin.Vol2.Ch11.O6
