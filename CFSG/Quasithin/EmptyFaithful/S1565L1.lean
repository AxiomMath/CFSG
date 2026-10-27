module

public import CFSG.Quasithin.EmptyFaithful.S1565B
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

theorem three_dvd_borel_of_model {Y : Type} [Group Y] [Finite Y] {Ks MKs : Subgroup Y}
    {P : Type} [Group P] (e : ↥Ks ≃* P) (Q : Sylow 2 P) (x : P)
    (hx : x ∈ Subgroup.normalizer ((Q : Subgroup P) : Set P)) (hx3 : orderOf x = 3)
    (hB : E2.IsBorelIn Ks MKs) : 3 ∣ Nat.card MKs := by
  obtain ⟨S, hS, rfl⟩ := hB
  obtain ⟨hSK, hS2, hSi⟩ := hS
  have hS' : IsPGroup 2 (S.subgroupOf Ks) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  let S' : Sylow 2 ↥Ks := hS'.toSylow hSi
  let Q' : Sylow 2 ↥Ks :=
    Q.comapOfInjective e.toMonoidHom e.injective
      (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  have : Finite (Sylow 2 ↥Ks) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Ks) Q' S'
  set xK : ↥Ks := e.symm x with hxK
  have hQ'mem : ∀ h : ↥Ks, h ∈ (Q' : Subgroup ↥Ks) ↔ e h ∈ (Q : Subgroup P) := fun h => Iff.rfl
  have hxQ' : xK ∈ Subgroup.normalizer ((Q' : Subgroup ↥Ks) : Set ↥Ks) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQ'mem, hQ'mem, map_mul, map_mul, map_inv, hxK, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hx (e h)
  have hxs : xK • Q' = Q' := Sylow.smul_eq_iff_mem_normalizer.mpr hxQ'
  set y : ↥Ks := g * xK * g⁻¹ with hy
  have hys : y • S' = S' := by
    rw [hy, ← hg, mul_smul, mul_smul, inv_smul_smul, hxs]
  have hyN : y ∈ Subgroup.normalizer ((S' : Subgroup ↥Ks) : Set ↥Ks) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hys
  have hS'mem : ∀ h : ↥Ks, h ∈ (S' : Subgroup ↥Ks) ↔ (h : Y) ∈ S := fun h => Iff.rfl
  have hyY : (y : Y) ∈ Subgroup.normalizer (S : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hhS
      have hhK : h ∈ Ks := hSK hhS
      have := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhK⟩).mp ((hS'mem _).mpr hhS)
      exact (hS'mem _).mp this
    · intro hS2'
      have hhK : h ∈ Ks := by
        have h1 : (y : Y)⁻¹ * ((y : Y) * h * (y : Y)⁻¹) * (y : Y) = h := by group
        rw [← h1]
        exact Ks.mul_mem (Ks.mul_mem (Ks.inv_mem y.2) (hSK hS2')) y.2
      have := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhK⟩).mpr ((hS'mem _).mpr hS2')
      exact (hS'mem _).mp this
  have hmem : (y : Y) ∈ Ks ⊓ Subgroup.normalizer (S : Set Y) := ⟨y.2, hyY⟩
  have hord : orderOf (y : Y) = 3 := by
    rw [Subgroup.orderOf_coe, hy]
    have h1 : orderOf xK = 3 :=
      (orderOf_injective e.symm.toMonoidHom e.symm.injective x).trans hx3
    rw [← h1]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective xK)
  have := orderOf_dvd_natCard (⟨(y : Y), hmem⟩ : ↥(Ks ⊓ Subgroup.normalizer (S : Set Y)))
  rw [Subgroup.orderOf_mk, hord] at this
  exact this

theorem exists_unit_orderOf_three {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h)

theorem three_dvd_two_pow_sub_one_of_even {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h := Nat.sub_dvd_pow_sub_pow 4 1 m
  rw [one_pow] at h
  have e : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
  rw [e]
  simpa using h

section Linear

variable {K : Type} [Field K]

private noncomputable def omegaDiagSL (n : ℕ) (hn : n = 2 ∨ n = 3) (ω : Kˣ) :
    SpecialLinearGroup (Fin n) K :=
  ⟨Matrix.diagonal (fun i : Fin n =>
    if (i : ℕ) = 0 then (ω : K) else if (i : ℕ) = 1 then (ω⁻¹ : Kˣ) else 1), by
    rcases hn with rfl | rfl <;>
    simp [Matrix.det_diagonal, Fin.prod_univ_succ]⟩

private theorem coe_omegaDiagSL (n : ℕ) (hn : n = 2 ∨ n = 3) (ω : Kˣ) :
    (omegaDiagSL n hn ω : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i : Fin n =>
        if (i : ℕ) = 0 then (ω : K) else if (i : ℕ) = 1 then (ω⁻¹ : Kˣ) else 1) := rfl

private theorem omegaDiagSL_mem_upperTriangular (n : ℕ) (hn : n = 2 ∨ n = 3) (ω : Kˣ) :
    omegaDiagSL n hn ω ∈ LinearFlag.upperTriangular n K := by
  rw [LinearFlag.mem_upperTriangular]
  intro i j hji
  rw [coe_omegaDiagSL, Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

private theorem omegaDiagSL_pow_three (n : ℕ) (hn : n = 2 ∨ n = 3) (ω : Kˣ)
    (hω : orderOf ω = 3) : (omegaDiagSL n hn ω) ^ 3 = 1 := by
  have h3 : ((ω : K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have key : ((omegaDiagSL n hn ω ^ 3 : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_omegaDiagSL, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h0 : (i : ℕ) = 0
    · simp [h0, h3]
    · by_cases h1 : (i : ℕ) = 1
      · simp [h1, h3]
      · simp [h0, h1]
  exact Subtype.ext key

private theorem omegaDiagSL_not_mem_scalars (n : ℕ) (hn : n = 2 ∨ n = 3) (ω : Kˣ)
    (hω : orderOf ω = 3) : omegaDiagSL n hn ω ∉ LinearFlag.scalars n K := by
  intro hmem
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hmem
  have h0 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
  have h1 := congrFun (congrFun hc ⟨1, by omega⟩) ⟨1, by omega⟩
  rw [coe_omegaDiagSL] at h0 h1
  simp at h0 h1
  have h2 : (ω : K) = (ω : K)⁻¹ := h0.trans h1.symm
  have h3 : ω = ω⁻¹ := Units.ext (by simpa using h2)
  have h4 : ω ^ 2 = 1 := by
    rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h3
  have h5 : orderOf ω ∣ 2 := orderOf_dvd_of_pow_eq_one h4
  rw [hω] at h5
  omega

theorem exists_order_three_normalizer_projSL [Finite K] [CharP K 2] (n : ℕ)
    (hn : n = 2 ∨ n = 3) (ω : Kˣ) (hω : orderOf ω = 3) :
    ∃ Q : Sylow 2 (LinearFlag.projectiveSL n K), ∃ x : LinearFlag.projectiveSL n K,
      x ∈ Subgroup.normalizer ((Q : Subgroup (LinearFlag.projectiveSL n K)) :
        Set (LinearFlag.projectiveSL n K)) ∧ orderOf x = 3 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨Q, hQ⟩ := LinearFlag.exists_sylow_projUnitriangular (K := K) 2 hn1
  refine ⟨Q, LinearFlag.proj n K (omegaDiagSL n hn ω), ?_, ?_⟩
  · rw [hQ, LinearFlag.normalizer_projUnitriangular 2]
    exact Subgroup.mem_map_of_mem _ (omegaDiagSL_mem_upperTriangular n hn ω)
  · apply orderOf_eq_prime (p := 3)
    · rw [← map_pow, omegaDiagSL_pow_three n hn ω hω, map_one]
    · rw [Ne, LinearFlag.proj_eq_one_iff]
      exact omegaDiagSL_not_mem_scalars n hn ω hω

theorem three_dvd_borel_of_psl {Y : Type} [Group Y] [Finite Y] {Ks MKs : Subgroup Y}
    [Finite K] [CharP K 2] (N : ℕ) (hN : N = 2 ∨ N = 3)
    (e : ↥Ks ≃* StatedProj (StatedSL N K)) (ω : Kˣ) (hω : orderOf ω = 3)
    (hB : E2.IsBorelIn Ks MKs) : 3 ∣ Nat.card MKs := by
  obtain ⟨Q, x, hx, hx3⟩ := exists_order_three_normalizer_projSL (K := K) N hN ω hω
  exact three_dvd_borel_of_model
    ((e.trans (projectiveSpecialLinearGroupEquivStatedProj N K).symm).trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center N K)).symm) Q x hx hx3 hB

end Linear

section Symplectic

variable {K : Type} [Field K]

private theorem torusHom_pow_three (ω : Kˣ) (hω : orderOf ω = 3) :
    (SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![ω, 1]) ^ 3 = 1 := by
  rw [← map_pow]
  have : (![ω, 1] : Fin 2 → Kˣ) ^ 3 = 1 := by
    funext i
    fin_cases i
    · simp [← hω, pow_orderOf_eq_one]
    · simp
  rw [this, map_one]

private theorem torusHom_not_mem_scalars (ω : Kˣ) (hω : orderOf ω = 3) :
    SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![ω, 1] ∉
      (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) := by
  intro hmem
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hm := congrArg
    (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at hm
  rw [SymplecticTorusWeyl.coe_torusHom] at hm
  have h0 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 0)
  have h1 := congrFun (congrFun hm (Sum.inl 1)) (Sum.inl 1)
  simp at h0 h1
  have h2 : ω = 1 := by
    subst h1
    exact Units.ext (by simpa using h0.symm)
  have := hω
  rw [h2, orderOf_one] at this
  omega

theorem exists_order_three_normalizer_projSp [Finite K] [CharP K 2] (ω : Kˣ)
    (hω : orderOf ω = 3) :
    ∃ Q : Sylow 2 (StatedProj (StatedSp 2 K)), ∃ x : StatedProj (StatedSp 2 K),
      x ∈ Subgroup.normalizer ((Q : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K))) ∧ orderOf x = 3 := by
  obtain ⟨Q, hQ⟩ := SymplecticFlag.exists_sylow_projUnipotent (K := K) (r := 2) 2 (by norm_num)
  refine ⟨Q, SymplecticFlag.proj 2 K (SymplecticTorusWeyl.torusHom ![ω, 1]), ?_, ?_⟩
  · rw [hQ, SymplecticHigher.normalizer_projUnipotent 2 (by norm_num)]
    exact Subgroup.mem_map_of_mem _
      (SymplecticFlag.torus_le_borelSubgroup (SymplecticTorusWeyl.torusHom_mem_torus _))
  · apply orderOf_eq_prime (p := 3)
    · rw [← map_pow, torusHom_pow_three ω hω, map_one]
    · intro h
      rw [SymplecticFlag.proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact torusHom_not_mem_scalars ω hω h

end Symplectic

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

theorem exists_order_three_normalizer_hypPSU (n : ℕ) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (ω : Kˣ) (hω : orderOf ω = 3)
    (hωq : (ω : K) ^ 2 ^ n = ω) :
    ∃ (h : UnitaryFieldData 2 n K), ∃ Q : Sylow 2 (hypPSU h 1 1), ∃ x : hypPSU h 1 1,
      x ∈ Subgroup.normalizer ((Q : Subgroup (hypPSU h 1 1)) : Set (hypPSU h 1 1)) ∧
        orderOf x = 3 := by
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  refine ⟨h, ?_⟩
  obtain ⟨-, -, -, -, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hbar : h.bar (ω : K) = ω := by rw [UnitaryFieldData.bar_apply]; exact hωq
  let a : Fin 1 → Kˣ := fun _ => ω
  let d : Fin 1 → Kˣ := fun _ => 1
  have hd : ∀ k, h.norm (d k : K) = 1 := fun k => by simp [d, UnitaryFieldData.norm]
  have hp : torusRatio h a d = 1 := by
    simp [torusRatio, a, d, hbar]
  obtain ⟨g, hgT, hg⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨Q, hypProj h 1 1 g, ?_, ?_⟩
  · rw [hQ, UnitaryHigher.normalizer_hypProjUnitriangular h le_rfl le_rfl]
    exact Subgroup.mem_map_of_mem _ (hypTorus_le_hypBorel h hgT)
  · have h3 : (ω : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
    have hcube : g ^ 3 = 1 := by
      have hm : (((g ^ 3 : hypSU h 1 1) : GL (HypIndex 1 1) K) :
          Matrix (HypIndex 1 1) (HypIndex 1 1) K) = 1 := by
        rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow,
          ← Matrix.diagonal_one]
        congr 1
        funext x
        rcases x with i | k | i
        · simp [torusEntries, a, h3]
        · simp [torusEntries, d]
        · simp [torusEntries, a, hbar, h3]
      exact Subtype.ext (Units.ext (by simpa using hm))
    apply orderOf_eq_prime (p := 3)
    · rw [← map_pow, hcube, map_one]
    · intro h1
      rw [hypProj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      obtain ⟨c, -, -, hc⟩ := h1
      have hm := congrArg (fun g : GL (HypIndex 1 1) K =>
        (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at hm
      rw [hg] at hm
      have h0 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 0)
      have h1' := congrFun (congrFun hm (Sum.inr (Sum.inl 0))) (Sum.inr (Sum.inl 0))
      simp [torusEntries, a, d] at h0 h1'
      have h2 : ω = 1 := Units.ext (h0.trans h1'.symm)
      rw [h2, orderOf_one] at hω
      omega

end Unitary

theorem input15365Odd_of : Input15365Odd := by
  intro Y _ _ Ks MKs n hn2 hev hShape hB
  have h3n : 3 ∣ 2 ^ n - 1 := three_dvd_two_pow_sub_one_of_even hev
  rcases hShape with hL2 | hSz | hU3 | hL3 | hSp
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨ω, hω⟩ := exists_unit_orderOf_three (K := K) (by rw [hK]; exact h3n)
    exact three_dvd_borel_of_psl 2 (Or.inl rfl) e ω hω hB
  · obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := hSz
    obtain ⟨m, hm⟩ := hev
    omega
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hU3
    have hKq : Nat.card K = (2 ^ n) ^ 2 := hK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := 2 * n)
        (by rw [← Nat.card_eq_fintype_card, hKq, ← pow_mul, mul_comm])
    have h3sq : 3 ∣ Nat.card K - 1 := by
      rw [hKq]
      have h := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
      rw [one_pow] at h
      exact (h3n.trans h)
    obtain ⟨ω, hω⟩ := exists_unit_orderOf_three (K := K) h3sq
    have hωq : (ω : K) ^ 2 ^ n = ω := by
      obtain ⟨t, ht⟩ := h3n
      have h2n : 2 ^ n = 3 * t + 1 := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      have h3 : (ω : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
      rw [h2n, pow_succ, pow_mul, h3, one_pow, one_mul]
    obtain ⟨h, Q, x, hx, hx3⟩ := exists_order_three_normalizer_hypPSU (K := K) n (by omega) hKq
      ω hω hωq
    obtain ⟨R, hR⟩ :=
      CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport h (r := 1) (ε := 1)
    exact three_dvd_borel_of_model
      (e.trans (CFSG.ClassicalGroups.UnitaryFlag.hypPSUEquivStatedProj h hR (by omega)).symm)
      Q x hx hx3 hB
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL3
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨ω, hω⟩ := exists_unit_orderOf_three (K := K) (by rw [hK]; exact h3n)
    exact three_dvd_borel_of_psl 3 (Or.inr rfl) e ω hω hB
  · have hn1 : ¬ n = 1 := by omega
    have hSp' : IsPSp4 2 n ↥Ks := by
      simpa [E2.IsSp4Prime, hn1] using hSp
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hSp'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨ω, hω⟩ := exists_unit_orderOf_three (K := K) (by rw [hK]; exact h3n)
    obtain ⟨Q, x, hx, hx3⟩ := exists_order_three_normalizer_projSp (K := K) ω hω
    exact three_dvd_borel_of_model e Q x hx hx3 hB

end CFSG.Quasithin
