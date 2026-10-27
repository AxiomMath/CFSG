module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.LemmaSDegree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

structure RankOneLocal (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) : Prop where
  root : ∀ ω : Ω, ∃ R : Subgroup X, R ≤ MulAction.stabilizer X ω ∧
    (R.subgroupOf (MulAction.stabilizer X ω)).Normal ∧ IsPGroup 2 R ∧
    ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β
  torus_odd : ∀ ω ω' : Ω, ω ≠ ω' →
    Odd (Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'))
  torus_fix : ∀ ω ω' ω'' : Ω, ω ≠ ω' →
    (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', t • ω'' = ω'') →
      ω'' = ω ∨ ω'' = ω'
  torus_cyclic : ∀ ω ω' : Ω, ω ≠ ω' →
    IsCyclic ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω')
  odd_closure : ∀ ω ω' : Ω, ω ≠ ω' → ∀ S : Set X,
    S ⊆ ↑(MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') →
    (∀ s ∈ S, Odd (orderOf s)) → Odd (Nat.card ↥(Subgroup.closure S))
  perfectResidual_eq : CFSG.perfectResidual X = N

structure RankOneZassenhaus (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) : Prop where
  fix_two : ∀ ω ω' : Ω, ω ≠ ω' →
    ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
      t ≠ 1 → ∀ ω'', t • ω'' = ω'' → ω'' = ω ∨ ω'' = ω'
  centralizer_le : ∀ ω ω' : Ω, ω ≠ ω' →
    ∀ g ∈ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
      (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', g * t = t * g) → g ∈ N

theorem centralizer_eq_bot_of_isMultiplyPretransitive
    {X Ω : Type*} [Group X] [MulAction X Ω] [Finite X] [FaithfulSMul X Ω]
    {N : Subgroup X} [N.Normal] (hN : ¬ IsMulCommutative N)
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) :
    Subgroup.centralizer (N : Set X) = ⊥ := by
  classical
  have hNbot : N ≠ ⊥ := by
    intro hbot
    apply hN
    rw [hbot]
    exact IsMulCommutative.of_comm fun a b => Subsingleton.elim (a * b) (b * a)
  have hNnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
  have hXnt : Nontrivial X := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne N
    exact ⟨(a : X), (b : X), fun h => hab (Subtype.ext h)⟩
  haveI hΩnt : Nontrivial Ω := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact (not_subsingleton_iff_nontrivial.mpr hXnt)
      ⟨fun a b => FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
        fun x => Subsingleton.elim (a • x) (b • x)⟩
  haveI : Nonempty Ω := inferInstance
  let C : Subgroup X := Subgroup.centralizer (N : Set X)
  haveI hCnormal : C.Normal := Subgroup.normal_centralizer
  haveI : MulAction.IsPreprimitive X Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive X Ω := inferInstance
  have hfixedN : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    apply hNbot
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
    intro x
    have hx : x ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ x
    simpa using hx ⟨n, hn⟩
  haveI : MulAction.IsPretransitive N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfixedN
  have hCsem : ∀ (c : C) (ω : Ω), c • ω = ω → c = 1 := by
    intro c ω hcω
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
    intro α
    obtain ⟨n, rfl⟩ := MulAction.exists_smul_eq N ω α
    have hcωX : (c : X) • ω = ω := by simpa only [Subgroup.smul_def] using hcω
    have hcomm : (c : X) * (n : X) = (n : X) * (c : X) :=
      (Subgroup.mem_centralizer_iff.mp c.2 (n : X) n.2).symm
    calc
      (c : X) • ((n : X) • ω) = ((c : X) * (n : X)) • ω := by rw [mul_smul]
      _ = ((n : X) * (c : X)) • ω := by rw [hcomm]
      _ = (n : X) • ((c : X) • ω) := by rw [mul_smul]
      _ = (n : X) • ω := by rw [hcωX]
      _ = (1 : X) • ((n : X) • ω) := by rw [one_smul]
  by_cases hC : C = ⊥
  · exact hC
  · exfalso
    have hCne : C ≠ ⊥ := hC
    haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
    have hfixedC : MulAction.fixedPoints C Ω ≠ ⊤ := by
      intro htop
      apply hCne
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_bot]
      apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
      intro x
      have hx : x ∈ MulAction.fixedPoints C Ω := by rw [htop]; exact Set.mem_univ x
      simpa using hx ⟨c, hc⟩
    haveI : MulAction.IsPretransitive C Ω :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := C) hfixedC
    let ω : Ω := Classical.arbitrary Ω
    have hCreg : ∀ (c c' : C), c • ω = c' • ω → c = c' := by
      intro c c' h
      have hfix : (c⁻¹ * c') • ω = ω := by
        rw [mul_smul]
        rw [← h]
        rw [← mul_smul, inv_mul_cancel, one_smul]
      have h1 := hCsem (c⁻¹ * c') ω hfix
      have h2' : c' = c := by
        calc
          c' = c * (c⁻¹ * c') := by group
          _ = c * 1 := by rw [h1]
          _ = c := mul_one c
      exact h2'.symm
    have hconj : ∀ c c' : C, c ≠ 1 → c' ≠ 1 →
        ∃ x : X, x • ω = ω ∧ x * (c : X) * x⁻¹ = (c' : X) := by
      intro c c' hc hc'
      have hcω : c • ω ≠ ω := fun h => hc (hCsem c ω h)
      have hc'ω : c' • ω ≠ ω := fun h => hc' (hCsem c' ω h)
      rw [MulAction.is_two_pretransitive_iff] at h2
      obtain ⟨x, hx1, hx2⟩ :=
        h2 (a := ω) (b := c • ω) (c := ω) (d := c' • ω) hcω.symm hc'ω.symm
      refine ⟨x, hx1, ?_⟩
      have hmem : x * (c : X) * x⁻¹ ∈ C := hCnormal.conj_mem (c : X) c.2 x
      have hxinv : x⁻¹ • ω = ω := by
        rw [← hx1, inv_smul_smul]
        exact hx1.symm
      have hact : (⟨x * (c : X) * x⁻¹, hmem⟩ : C) • ω = c' • ω := by
        change (x * (c : X) * x⁻¹) • ω = (c' : X) • ω
        calc
          (x * (c : X) * x⁻¹) • ω = x • ((c : X) • (x⁻¹ • ω)) := by
            rw [mul_smul, mul_smul]
          _ = x • ((c : X) • ω) := by rw [hxinv]
          _ = x • (c • ω) := rfl
          _ = (c' : X) • ω := hx2
      have hCeq : (⟨x * (c : X) * x⁻¹, hmem⟩ : C) = c' := hCreg _ _ hact
      exact congrArg Subtype.val hCeq
    have hord : ∀ c c' : C, c ≠ 1 → c' ≠ 1 → orderOf c = orderOf c' := by
      intro c c' hc hc'
      obtain ⟨x, -, hxconj⟩ := hconj c c' hc hc'
      have h := MulEquiv.orderOf_eq (MulAut.conj x) (c : X)
      rw [MulAut.conj_apply] at h
      rw [hxconj] at h
      rw [← Subgroup.orderOf_coe c, ← Subgroup.orderOf_coe c']
      exact h.symm
    obtain ⟨c0, hc0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
    set p : ℕ := orderOf c0 with hp_def
    have hp_ne_one : p ≠ 1 := by
      intro h
      apply hc0
      exact orderOf_eq_one_iff.mp h
    have hp_pos : 0 < p := orderOf_pos c0
    obtain ⟨q, hqprime, hq_dvd⟩ := Nat.exists_prime_and_dvd hp_ne_one
    have hq_le_p : q ≤ p := Nat.le_of_dvd hp_pos hq_dvd
    have hpdiv_pos : 0 < p / q := Nat.div_pos hq_le_p hqprime.pos
    have hlt : p / q < p := Nat.div_lt_self hp_pos hqprime.one_lt
    have hneq : c0 ^ (p / q) ≠ 1 := by
      intro h
      have hd : p ∣ p / q := by
        simpa [hp_def] using (orderOf_dvd_iff_pow_eq_one (x := c0) (n := p / q)).mpr h
      have hle : p ≤ p / q := Nat.le_of_dvd hpdiv_pos hd
      omega
    have hdvd : orderOf (c0 ^ (p / q)) ∣ q := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [← pow_mul, Nat.div_mul_cancel hq_dvd, pow_orderOf_eq_one]
    have horder_q : orderOf (c0 ^ (p / q)) = q := by
      rcases (Nat.dvd_prime hqprime).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hneq
      · exact h1
    have hpq : p = q := by
      have h := hord (c0 ^ (p / q)) c0 hneq hc0
      rw [horder_q] at h
      exact h.symm
    have hp_prime : p.Prime := hpq ▸ hqprime
    have hCpg : IsPGroup p C := by
      intro g
      refine ⟨1, ?_⟩
      rw [pow_one, ← orderOf_dvd_iff_pow_eq_one]
      by_cases hg : g = 1
      · rw [hg, orderOf_one]
        exact one_dvd p
      · rw [hord g c0 hg hc0]
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have hZnt : Nontrivial (Subgroup.center C) := IsPGroup.center_nontrivial hCpg
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center C)
    have hzC1 : (z : C) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hconj_center : ∀ (x : X) (z : C), z ∈ Subgroup.center C →
        (⟨x * (z : X) * x⁻¹, hCnormal.conj_mem (z : X) z.2 x⟩ : C) ∈
          Subgroup.center C := by
      intro x z hz
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro c
      have hmemc : x⁻¹ * (c : X) * x ∈ C := by
        simpa using hCnormal.conj_mem (c : X) c.2 x⁻¹
      have hcz := hz ⟨x⁻¹ * (c : X) * x, hmemc⟩
      have hczX : (x⁻¹ * (c : X) * x) * (z : X) = (z : X) * (x⁻¹ * (c : X) * x) :=
        congrArg Subtype.val hcz
      apply Subtype.ext
      calc
        (c : X) * (x * (z : X) * x⁻¹)
            = x * ((x⁻¹ * (c : X) * x) * (z : X)) * x⁻¹ := by group
        _ = x * ((z : X) * (x⁻¹ * (c : X) * x)) * x⁻¹ := by rw [hczX]
        _ = (x * (z : X) * x⁻¹) * (c : X) := by group
    have hcenter_top : Subgroup.center C = ⊤ := by
      rw [eq_top_iff]
      intro c _
      rw [Subgroup.mem_center_iff]
      intro d
      by_cases hc1 : c = 1
      · rw [hc1, one_mul, mul_one]
      · obtain ⟨x, -, hxconj⟩ := hconj (z : C) c hzC1 hc1
        have hmemd : x⁻¹ * (d : X) * x ∈ C := by
          simpa using hCnormal.conj_mem (d : X) d.2 x⁻¹
        have hzdC := Subgroup.mem_center_iff.mp z.2 ⟨x⁻¹ * (d : X) * x, hmemd⟩
        have hzd : (x⁻¹ * (d : X) * x) * (z : X) = (z : X) * (x⁻¹ * (d : X) * x) :=
          congrArg Subtype.val hzdC
        have hconj_eq :
            (d : X) * (x * (z : X) * x⁻¹) = (x * (z : X) * x⁻¹) * (d : X) := by
          calc
            (d : X) * (x * (z : X) * x⁻¹)
                = x * ((x⁻¹ * (d : X) * x) * (z : X)) * x⁻¹ := by group
            _ = x * ((z : X) * (x⁻¹ * (d : X) * x)) * x⁻¹ := by rw [hzd]
            _ = (x * (z : X) * x⁻¹) * (d : X) := by group
        apply Subtype.ext
        change (d : X) * (c : X) = (c : X) * (d : X)
        rw [← hxconj]
        exact hconj_eq
    have hcommC : IsMulCommutative C := by
      rw [isMulCommutative_iff]
      intro a b
      have ha : a ∈ Subgroup.center C := by rw [hcenter_top]; trivial
      exact (Subgroup.mem_center_iff.mp ha b).symm
    letI : IsMulCommutative C := hcommC
    have hCcent_sem : ∀ (g : X), g ∈ Subgroup.centralizer (C : Set X) → ∀ ω : Ω,
        g • ω = ω → g = 1 := by
      intro g hg ω hω
      apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
      intro α
      obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq C ω α
      have hcomm : (c : X) * g = g * (c : X) :=
        Subgroup.mem_centralizer_iff.mp hg (c : X) c.2
      calc
        g • ((c : X) • ω) = (g * (c : X)) • ω := by rw [mul_smul]
        _ = ((c : X) * g) • ω := by rw [← hcomm]
        _ = (c : X) • (g • ω) := by rw [mul_smul]
        _ = (c : X) • ω := by rw [hω]
        _ = (1 : X) • ((c : X) • ω) := by rw [one_smul]
    have hCcent_le : Subgroup.centralizer (C : Set X) ≤ C := by
      intro g hg
      let ω : Ω := Classical.arbitrary Ω
      obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C ω (g • ω)
      have hfix : ((c : X)⁻¹ * g) • ω = ω := by
        have hcX : (c : X) • ω = g • ω := hc
        calc
          ((c : X)⁻¹ * g) • ω = (c : X)⁻¹ • (g • ω) := by rw [mul_smul]
          _ = (c : X)⁻¹ • ((c : X) • ω) := by rw [← hcX]
          _ = ω := by rw [← mul_smul, inv_mul_cancel, one_smul]
      have hc_cent : (c : X)⁻¹ ∈ Subgroup.centralizer (C : Set X) := by
        simpa using Subgroup.le_centralizer C (C.inv_mem c.2)
      have hprod : (c : X)⁻¹ * g ∈ Subgroup.centralizer (C : Set X) :=
        (Subgroup.centralizer (C : Set X)).mul_mem hc_cent hg
      have h1 : (c : X)⁻¹ * g = 1 := hCcent_sem ((c : X)⁻¹ * g) hprod ω hfix
      have hg_eq : g = (c : X) := by
        calc
          g = (c : X) * ((c : X)⁻¹ * g) := by group
          _ = (c : X) * 1 := by rw [h1]
          _ = (c : X) := mul_one _
      rw [hg_eq]
      exact c.2
    have hCcent_eq : Subgroup.centralizer (C : Set X) = C :=
      le_antisymm hCcent_le (Subgroup.le_centralizer C)
    have hNleCentC : N ≤ Subgroup.centralizer (C : Set X) := by
      rw [Subgroup.le_centralizer_iff]
    have hNleC : N ≤ C := by
      simpa [hCcent_eq] using hNleCentC
    have hNcomm : IsMulCommutative N := by
      rw [isMulCommutative_iff]
      intro a b
      have haC : (a : X) ∈ C := hNleC a.2
      have hbC : (b : X) ∈ C := hNleC b.2
      letI : IsMulCommutative C := hcommC
      have hcab := hcommC.is_comm.comm (⟨(a : X), haC⟩ : C) ⟨(b : X), hbC⟩
      have hcabX : (a : X) * (b : X) = (b : X) * (a : X) := congrArg Subtype.val hcab
      exact Subtype.ext hcabX
    exact hN hNcomm

theorem exists_stabilizer_eq_conj_of_rankOneData {Y Ω : Type*} [Group Y] [Finite Y]
    [Fintype Ω] [MulAction Y Ω] [FaithfulSMul Y Ω] (N : Subgroup Y) [N.Normal]
    (hNbot : N ≠ ⊥) (h2 : MulAction.IsMultiplyPretransitive Y Ω 2)
    {U B : Subgroup N} (hd : RankOneData N U B)
    (hcard : Fintype.card Ω = 1 + Nat.card U) (ω : Ω) :
    ∃ x : N, (MulAction.stabilizer Y ω).subgroupOf N = B.map (MulAut.conj x).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixed : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    apply hNbot
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply FaithfulSMul.eq_of_smul_eq_smul (M := Y) (α := Ω)
    intro x
    have hx : x ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ x
    simpa using hx ⟨n, hn⟩
  haveI : MulAction.IsPreprimitive Y Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive Y Ω := inferInstance
  haveI : MulAction.IsPretransitive N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfixed
  let M : Subgroup N := MulAction.stabilizer N ω
  have hMindex : M.index = Fintype.card Ω := by
    rw [MulAction.index_stabilizer_of_transitive N ω, Nat.card_eq_fintype_card]
  have hMtop : M < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hfixed
    change MulAction.fixedPoints N Ω = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [MulAction.mem_fixedPoints]
    intro m
    obtain ⟨n, rfl⟩ := MulAction.exists_smul_eq N ω x
    have hnfix : n • ω = ω := by
      have : n ∈ M := htop ▸ Subgroup.mem_top n
      simpa [M] using this
    calc
      m • (n • ω) = (m * n) • ω := (mul_smul m n ω).symm
      _ = ω := by
        have hmn : m * n ∈ M := htop ▸ Subgroup.mem_top (m * n)
        simpa [M] using hmn
      _ = n • ω := hnfix.symm
  have hodd : Odd M.index := by
    rw [hMindex, hcard]
    obtain ⟨k, hk⟩ := hd.isPGroup.exists_card_eq
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
      apply hd.ne_bot
      rw [Subgroup.eq_bot_iff_card, hk, hk0']
      simp
    rw [hk]
    obtain ⟨j, hj⟩ := Nat.even_pow.mpr ⟨even_two, Nat.pos_iff_ne_zero.mp hkpos⟩
    exact ⟨j, by omega⟩
  have hnotdvd : ¬ 2 ∣ M.index :=
    fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨x, hx⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index
      Nat.prime_two M hnotdvd U hd.isPGroup
  let e1 : N ≃* N := MulAut.conj x
  let U' : Subgroup N := U.map e1.toMonoidHom
  let B' : Subgroup N := B.map e1.toMonoidHom
  have hU'data : RankOneData N U' B' := hd.map e1
  have hU'le : U' ≤ M := by
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact hx u hu
  have hMleB : M ≤ B' :=
    hU'data.overgroup_le_B M hU'le (lt_top_iff_ne_top.mpr hMtop.ne)
  have hMindexB' : M.index = B'.index := by
    rw [hMindex, hcard, hU'data.index_B, Subgroup.card_map_of_injective e1.injective]
  have hB'ne : B'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel1 : M.relIndex B' = 1 := by
    have h := Subgroup.relIndex_mul_index hMleB
    rw [hMindexB'] at h
    have h' : M.relIndex B' * B'.index = 1 * B'.index := by
      rw [one_mul]
      exact h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hB'ne) h'
  have hB'leM : B' ≤ M := Subgroup.relIndex_eq_one.mp hrel1
  have hMB' : M = B' := le_antisymm hMleB hB'leM
  refine ⟨x, ?_⟩
  change MulAction.stabilizer N ω = B.map (MulAut.conj x).toMonoidHom
  exact hMB'

namespace RankOneLocal

theorem oddFix {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} (h : RankOneLocal X Ω N) (ω : Ω) (K : Subgroup X)
    (hK : K ≤ MulAction.stabilizer X ω) (hKodd : Odd (Nat.card K))
    (hω : ∃ ω₀ : Ω, ω₀ ≠ ω) :
    ∃ ω' : Ω, ω' ≠ ω ∧ ∀ k ∈ K, k • ω' = ω' := by
  classical
  obtain ⟨ω₀, hω₀ne⟩ := hω
  obtain ⟨R, hRstab, hRnorm, hR2, hRreg⟩ := h.root ω
  let H : Subgroup X := R ⊔ K
  have hRH : R ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hHstab : H ≤ MulAction.stabilizer X ω := sup_le hRstab hK
  have hRnormH : (R.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRH]
    intro r k hr hk
    exact (Subgroup.normal_subgroupOf_iff hRstab).mp hRnorm r k hr (hHstab hk)
  have hcopRK : Nat.Coprime (Nat.card R) (Nat.card K) := by
    obtain ⟨m, hm⟩ := hR2.exists_card_eq
    rw [hm]
    exact (Nat.coprime_two_left.mpr hKodd).pow_left m
  have hdisjRK : Disjoint R K := Subgroup.disjoint_of_coprime_natCard hcopRK
  have hdisj : Disjoint (R.subgroupOf H) (K.subgroupOf H) := by
    rw [disjoint_iff]
    ext x
    constructor
    · rintro ⟨hxR, hxK⟩
      have hx : (x : X) ∈ R ⊓ K := ⟨hxR, hxK⟩
      rw [disjoint_iff.mp hdisjRK] at hx
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subgroup.mem_bot.mp hx)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact ⟨(R.subgroupOf H).one_mem, (K.subgroupOf H).one_mem⟩
  have hsupRH : R.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hRH hKH]
    change (R ⊔ K).subgroupOf (R ⊔ K) = ⊤
    rw [Subgroup.subgroupOf_self]
  have hmul : (R.subgroupOf H : Set H) * (K.subgroupOf H : Set H) = (Set.univ : Set H) := by
    rw [← Subgroup.normal_mul (R.subgroupOf H) (K.subgroupOf H), hsupRH]
    rfl
  have hcompRK : (R.subgroupOf H).IsComplement' (K.subgroupOf H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hcompRL : (R.subgroupOf H).IsComplement' (MulAction.stabilizer H ω₀) := by
    refine Subgroup.isComplement'_stabilizer (H := R.subgroupOf H) ω₀ ?_ ?_
    · intro r hr
      obtain ⟨r₀, hr₀, huniq⟩ := hRreg ω₀ ω₀ hω₀ne hω₀ne
      have hr₀1 : r₀ = 1 := (huniq 1 (by simp)).symm
      have hrr : (⟨((r : H) : X), r.2⟩ : R) = r₀ := by
        apply huniq
        simpa [Subgroup.smul_def] using hr
      apply Subtype.ext
      apply Subtype.ext
      rw [congrArg Subtype.val hrr, hr₀1]
      rfl
    · intro g
      have hgX : (g : X) • ω₀ ≠ ω := by
        intro hgω
        have hgfix : (g : X) • ω = ω := hHstab g.2
        have h : (g : X)⁻¹ • ((g : X) • ω₀) = (g : X)⁻¹ • ((g : X) • ω) := by
          rw [hgω, hgfix]
        rw [inv_smul_smul, inv_smul_smul] at h
        exact hω₀ne h
      obtain ⟨r₀, hr₀, -⟩ := hRreg ((g : X) • ω₀) ω₀ hgX hω₀ne
      refine ⟨⟨⟨(r₀ : X), hRH r₀.2⟩, r₀.2⟩, ?_⟩
      change (r₀ : X) • ((g : X) • ω₀) = ω₀
      exact hr₀
  have hcop : Nat.Coprime (Nat.card (R.subgroupOf H)) (R.subgroupOf H).index := by
    have hcardR : Nat.card (R.subgroupOf H) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
    have hcardK : Nat.card (K.subgroupOf H) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
    rw [hcompRK.symm.index_eq_card, hcardR, hcardK]
    exact hcopRK
  obtain ⟨n, hn⟩ :=
    CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      (R.subgroupOf H) (K.subgroupOf H) (MulAction.stabilizer H ω₀)
      hRnormH hcompRK hcompRL hcop
  let ω' : Ω := ((n : H) : X)⁻¹ • ω₀
  have hnω : ((n : H) : X) • ω = ω := hHstab (n : H).2
  have hnω' : ((n : H) : X) • ω' = ω₀ := by
    rw [show ω' = ((n : H) : X)⁻¹ • ω₀ from rfl, ← mul_smul, mul_inv_cancel, one_smul]
  have hω'ne : ω' ≠ ω := by
    intro h
    have h1 : ((n : H) : X) • ω' = ((n : H) : X) • ω := by rw [h]
    rw [hnω', hnω] at h1
    exact hω₀ne h1
  have hfixK : ∀ k : K, (k : X) • ω' = ω' := by
    intro k
    let kH : K.subgroupOf H := ⟨⟨(k : X), hKH k.2⟩, k.2⟩
    have hmem : ((n : H) * (kH : H) * (n : H)⁻¹) ∈ MulAction.stabilizer H ω₀ := by
      rw [hn]
      exact Subgroup.mem_map_of_mem (MulAut.conj (n : H)).toMonoidHom kH.2
    have hfix0 : (((n : H) : X) * (k : X) * ((n : H) : X)⁻¹) • ω₀ = ω₀ := by
      simpa [Subgroup.smul_def] using hmem
    calc
      (k : X) • ω' = (k : X) • (((n : H) : X)⁻¹ • ω₀) := rfl
      _ = ((k : X) * ((n : H) : X)⁻¹) • ω₀ := by rw [mul_smul]
      _ = (((n : H) : X)⁻¹ * (((n : H) : X) * (k : X) * ((n : H) : X)⁻¹)) • ω₀ := by
        congr 1
        group
      _ = ((n : H) : X)⁻¹ •
          ((((n : H) : X) * (k : X) * ((n : H) : X)⁻¹) • ω₀) := by
        rw [mul_smul]
      _ = ((n : H) : X)⁻¹ • ω₀ := by rw [hfix0]
      _ = ω' := rfl
  refine ⟨ω', hω'ne, ?_⟩
  intro k hk
  have hkX : (k : X) • ω' = ω' := hfixK ⟨k, hk⟩
  simpa [Subgroup.smul_def] using hkX

theorem oddFix_unique {X Ω : Type*} [Group X] [MulAction X Ω]
    {N : Subgroup X} (h : RankOneLocal X Ω N) {ω ω' : Ω} (hω : ω ≠ ω')
    {K : Subgroup X}
    (hNK : N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω' ≤ K) :
    ∀ ω'' : Ω, ω'' ≠ ω → (∀ k ∈ K, k • ω'' = ω'') → ω'' = ω' := by
  intro ω'' hω'' hfix
  have hfixS : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
      t • ω'' = ω'' := fun t ht => hfix t (hNK ht)
  rcases h.torus_fix ω ω' ω'' hω hfixS with h | h
  · exact absurd h hω''
  · exact h

end RankOneLocal

end CFSG.Quasithin.Stroth.WeissDelta
