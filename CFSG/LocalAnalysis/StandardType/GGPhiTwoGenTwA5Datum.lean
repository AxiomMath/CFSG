module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Cover
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoTorus
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.CTP.SeitzFineU5
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.Assembly CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

private theorem mem_largeEvenGUSet_of_mem_largeEvenSUGroup {K : Type} [Field K] [CharP K 2]
    {d n : ℕ} {g : GL (Fin d) K} (hg : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    g ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  have hmap : ∀ M : Matrix (Fin d) (Fin d) K,
      M.map (fun x => x ^ 2 ^ n) = M.map (iterateFrobenius K 2 n) := by
    intro M
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, iterateFrobenius_def]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, hid⟩ := hx
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    rw [one_smul]
    exact hid
  | one =>
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    simp
  | mul x y _ _ hx hy =>
    obtain ⟨μx, hμx0, hμx1, hμx⟩ := hx
    obtain ⟨μy, hμy0, hμy1, hμy⟩ := hy
    refine ⟨μx * μy, mul_ne_zero hμx0 hμy0, by rw [mul_pow, hμx1, hμy1], ?_⟩
    rw [hmap] at hμx hμy ⊢
    simp only [Units.val_mul]
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          (Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((x : Matrix (Fin d) (Fin d) K) * (y : Matrix (Fin d) (Fin d) K))
        = (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
            (x : Matrix (Fin d) (Fin d) K)) * (y : Matrix (Fin d) (Fin d) K) := by
          simp only [Matrix.mul_assoc]
      _ = (μx * μy) • (1 : Matrix (Fin d) (Fin d) K) := by
          rw [hμx, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hμy, smul_smul]
  | inv x _ hx =>
    obtain ⟨μ, hμ0, hμ1, hX⟩ := hx
    rw [hmap] at hX
    have hXZ : (x : Matrix (Fin d) (Fin d) K) *
        ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hXfZf : Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n) *
        Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          (iterateFrobenius K 2 n) = 1 := by
      rw [← Matrix.map_mul, hXZ, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = 1 := by
      rw [← Matrix.transpose_mul, hXfZf, Matrix.transpose_one]
    have h2 : μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = (x : Matrix (Fin d) (Fin d) K) := by
      calc μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose
          = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (μ • (1 : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * ((Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (x : Matrix (Fin d) (Fin d) K)) := by rw [hX]
        _ = ((Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose) * (x : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc]
        _ = (x : Matrix (Fin d) (Fin d) K) := by rw [h1, Matrix.one_mul]
    have h3 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = μ⁻¹ • (x : Matrix (Fin d) (Fin d) K) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμ1], ?_⟩
    rw [hmap]
    rw [h3, Matrix.smul_mul, hXZ]

private theorem unitarySLEquivStated_mk_eq_one_iff {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (B : unitarySL σ) :
    LargeEvenProjMk (StatedSU 6 (2 ^ n) K)
        (unitarySLEquivStated (p := 2) (f := n) hK hσ B) = 1 ↔
      B ∈ Subgroup.center (unitarySL σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := unitarySLEquivStated (p := 2) (f := n) hK hσ
  have hnq : (6, 2 ^ n) ≠ (3, 2) := fun h =>
    absurd (congrArg Prod.fst h) (by norm_num)
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := n) (F := K) (n := 6) hK (by norm_num) hnq).2
  constructor
  · intro h
    have h1 : (QuotientGroup.mk (e B) : LargeEvenProj (StatedSU 6 (2 ^ n) K)) = 1 := by
      simpa [e, LargeEvenProjMk, MonoidHom.comp_apply] using h
    have h2 : e B ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ n) K) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : e B ∈ Subgroup.center (StatedSU 6 (2 ^ n) K) := by
      rw [hZ]
      exact h2
    have h4 : e B ∈ (Subgroup.center (unitarySL σ)).map e.toMonoidHom := by
      rw [CFSG.LieType.Universal.Unitary.map_center_mulEquiv e]
      exact h3
    obtain ⟨B', hB', hBB'⟩ := Subgroup.mem_map.1 h4
    rwa [← e.injective hBB']
  · intro hB
    have h3 : e B ∈ Subgroup.center (StatedSU 6 (2 ^ n) K) := by
      rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv e]
      exact ⟨B, hB, rfl⟩
    have h2 : e B ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ n) K) := by
      rw [hZ] at h3
      exact h3
    have h1 : (QuotientGroup.mk (e B) : LargeEvenProj (StatedSU 6 (2 ^ n) K)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h2
    simpa [e, LargeEvenProjMk, MonoidHom.comp_apply] using h1

private theorem pow_six_eq_one_of_mem_center {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {B : unitarySL σ} (hB : B ∈ Subgroup.center (unitarySL σ)) :
    B ^ 6 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl⟩ := (mem_center_unitarySL_iff hK hσ B).1 hB
  have hdet : l ^ 6 = 1 := by
    have h := (B : Matrix.SpecialLinearGroup (Fin 6) K).2
    rw [hl, Matrix.scalar_apply, Matrix.det_diagonal] at h
    simpa using h
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_one, hl, Matrix.scalar_apply, Matrix.diagonal_pow]
  have hone : ((fun _ => l : Fin 6 → K) ^ 6) = 1 := by
    funext i
    simpa using hdet
  rw [hone]
  simp

section E6


private theorem mk_eq_one_of_psi_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {ε : K} {Ψ : Matrix.SpecialLinearGroup (Fin 6) K →* ModGL TwistTag.E6.tag K}
    (hΨ : IsPsiTw σ ε Ψ) (B : unitarySL σ)
    (hB : Ψ (B : Matrix.SpecialLinearGroup (Fin 6) K) = 1) :
    LargeEvenProjMk (StatedSU 6 (2 ^ n) K)
        (unitarySLEquivStated (p := 2) (f := n) hK hσ B) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, _, hrB⟩ := hΨ.scalar_of_eq_one (B : Matrix.SpecialLinearGroup (Fin 6) K) hB
  refine (unitarySLEquivStated_mk_eq_one_iff hK σ hσ B).2 ?_
  exact (mem_center_unitarySL_iff hK hσ B).2 ⟨r, hrB⟩

private structure A5Core {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) where
  Ψ : Matrix.SpecialLinearGroup (Fin 6) K →* ModGL TwistTag.E6.tag K
  ε : K
  hΨ : IsPsiTw σ.toRingHom ε Ψ
  ΨU : unitarySL σ.toRingHom →* ↥(twistedE6RootGroup K σ)
  hΨU_coe : ∀ B, ((ΨU B : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
    Ψ (B : Matrix.SpecialLinearGroup (Fin 6) K)
  Y : Subgroup ↥(twistedE6RootGroup K σ)
  hY : Y = ΨU.range
  hM : ∀ a : Fin TwistTag.E6.foldedTag.rank, a.val ≤ 2 →
    orbitRankOneGroup TwistTag.E6 K σ.toRingHom a ≤ (unitarySL σ.toRingHom).map Ψ
  e : unitarySL σ.toRingHom ≃* StatedSU 6 (2 ^ n) K
  φ : unitarySL σ.toRingHom →* LargeEvenProj (StatedSU 6 (2 ^ n) K)
  hφ_apply : ∀ B, φ B = LargeEvenProjMk (StatedSU 6 (2 ^ n) K) (e B)
  hφsurj : Function.Surjective φ
  hkerφ : φ.ker ≤ Subgroup.center (unitarySL σ.toRingHom)
  ΨY : unitarySL σ.toRingHom →* ↥Y
  hΨYsurj : Function.Surjective ΨY
  θ : ↥Y →* LargeEvenProj (StatedSU 6 (2 ^ n) K)
  hθfac : ∀ B, θ (ΨY B) = φ B
  hθsurj : Function.Surjective θ
  hkerθ : θ.ker ≤ Subgroup.center ↥Y
  hcommY : commutator ↥Y = ⊤

private theorem a5Core_center_exp {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (D : A5Core hK σ hσ) :
    ∀ z ∈ Subgroup.center ↥D.Y, z ^ p = 1 → z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (unitarySL σ.toRingHom) :=
    isPerfect_unitarySL_gen (p := 2) (f := n) hK hσ
  intro z hz hzp
  rw [Subgroup.mem_center_iff] at hz
  obtain ⟨B, rfl⟩ := D.hΨYsurj z
  have hφBcenter : D.φ B ∈ Subgroup.center (LargeEvenProj (StatedSU 6 (2 ^ n) K)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := D.hθsurj q
    rw [← D.hθfac B, ← map_mul, ← map_mul]
    rw [hz y]
  have hBcenter : B ∈ Subgroup.center (unitarySL σ.toRingHom) := by
    have hcom := CFSG.LocalCores.comap_center_eq_of_perfect hperf D.φ D.hφsurj D.hkerφ
    have hmem : B ∈ (Subgroup.center (LargeEvenProj (StatedSU 6 (2 ^ n) K))).comap D.φ := by
      rw [Subgroup.mem_comap]
      exact hφBcenter
    rwa [hcom] at hmem
  have hz6 : (D.ΨY B) ^ 6 = 1 := by
    rw [← map_pow, pow_six_eq_one_of_mem_center hK σ.toRingHom hσ hBcenter, map_one]
  have hcop : Nat.Coprime 6 p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    intro hd
    have hp6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hp56 : p = 5 ∨ p = 6 := by omega
    rcases hp56 with rfl | rfl
    · norm_num at hd
    · exact absurd (Fact.out : Nat.Prime 6) (by norm_num)
  have := pow_gcd_eq_one.2 ⟨hz6, hzp⟩
  rwa [hcop, pow_one] at this

private theorem a5Core_gu {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (D : A5Core hK σ hσ) :
    ∀ x : ↥D.Y, MulAut.conj (D.θ x) ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (StatedSU 6 (2 ^ n) K))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
  intro x
  obtain ⟨B, rfl⟩ := D.hΨYsurj x
  let A : GL (Fin 6) K := (D.e B : ↥(StatedSU 6 (2 ^ n) K))
  let AH : ↥(StatedSU 6 (2 ^ n) K) := ⟨A, (D.e B).2⟩
  have hAgu : A ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) :=
    mem_largeEvenGUSet_of_mem_largeEvenSUGroup AH.2
  have hφA : D.φ B = LargeEvenProjMk (StatedSU 6 (2 ^ n) K) AH := by
    rw [D.hφ_apply B]
  refine ⟨A, hAgu, ?_⟩
  intro h h' hrel
  have hrel' : h' = AH * h * AH⁻¹ := Subtype.ext hrel
  calc MulAut.conj (D.θ (D.ΨY B)) (LargeEvenProjMk (StatedSU 6 (2 ^ n) K) h)
      = MulAut.conj (D.φ B) (LargeEvenProjMk (StatedSU 6 (2 ^ n) K) h) := by
        rw [D.hθfac B]
    _ = LargeEvenProjMk (StatedSU 6 (2 ^ n) K) AH *
          LargeEvenProjMk (StatedSU 6 (2 ^ n) K) h *
          (LargeEvenProjMk (StatedSU 6 (2 ^ n) K) AH)⁻¹ := by
        rw [hφA, MulAut.conj_apply]
    _ = LargeEvenProjMk (StatedSU 6 (2 ^ n) K) (AH * h * AH⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = LargeEvenProjMk (StatedSU 6 (2 ^ n) K) h' := by rw [hrel']

section Certificates


private theorem a5Core_exists {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nonempty (A5Core hK σ hσ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, hK'⟩
  have : CharP K 2 := hU.charP
  set σ' : K →+* K := σ.toRingHom with hσ'def
  have hσ' : ∀ c, σ' c = c ^ 2 ^ n := hσ
  have hσσ : ∀ c, σ' (σ' c) = c := fun c => by
    rw [hσ', hσ']
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  obtain ⟨c0, hc0⟩ := hU.exists_bar_ne
  have hbar : hU.bar c0 = σ' c0 := by rw [hU.bar_apply, hσ']
  have hε0 : c0 - σ' c0 ≠ 0 := sub_ne_zero.2 (fun h => hc0 (by rw [hbar]; exact h.symm))
  have hε : σ' (c0 - σ' c0) = -(c0 - σ' c0) := by rw [map_sub, hσσ]; ring
  obtain ⟨Ψ, hΨ⟩ := exists_isPsiTw σ' hσσ hε0 hε Nat.prime_two (by omega : 1 ≤ 2 * n) hK'
  have hperf : Group.IsPerfect (unitarySL σ') := isPerfect_unitarySL_gen (p := 2) (f := n) hK hσ'
  have hC0 : (unitarySL σ').map Ψ ≤ graphFixedRootGroup TwistTag.E6 K σ' :=
    map_unitarySL_le_graphFixedRootGroup hΨ σ.surjective hperf
  have hM := orbitRankOneGroup_le_map hΨ hσσ hε0 hε
  let ΨU : unitarySL σ' →* ↥(twistedE6RootGroup K σ) :=
    (Ψ.comp (unitarySL σ').subtype).codRestrict _ fun B => hC0 ⟨B, B.2, rfl⟩
  let Y : Subgroup ↥(twistedE6RootGroup K σ) := ΨU.range
  let ΨY : unitarySL σ' →* ↥Y := ΨU.rangeRestrict
  have hΨYsurj : Function.Surjective ΨY := MonoidHom.rangeRestrict_surjective ΨU
  let H : Subgroup (GL (Fin 6) K) := StatedSU 6 (2 ^ n) K
  let e : unitarySL σ' ≃* StatedSU 6 (2 ^ n) K :=
    unitarySLEquivStated (p := 2) (f := n) hK hσ'
  let φ : unitarySL σ' →* LargeEvenProj H := (LargeEvenProjMk H).comp e.toMonoidHom
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin 6) K).subgroupOf H) y
    refine ⟨e.symm h, ?_⟩
    show LargeEvenProjMk H (e (e.symm h)) = LargeEvenProjMk H h
    rw [MulEquiv.apply_symm_apply]
  have hkerφ : φ.ker ≤ Subgroup.center (unitarySL σ') := by
    intro B hB
    rw [MonoidHom.mem_ker] at hB
    exact (unitarySLEquivStated_mk_eq_one_iff hK σ' hσ' B).1 hB
  have hkerφΨ : ΨY.ker ≤ φ.ker := by
    intro B hB
    rw [MonoidHom.mem_ker] at hB ⊢
    have hΨB : Ψ (B : Matrix.SpecialLinearGroup (Fin 6) K) = 1 := by
      have h := congrArg Subtype.val (congrArg Subtype.val hB)
      exact h
    exact mk_eq_one_of_psi_eq_one hK σ' hσ' hΨ B hΨB
  let θ : ↥Y →* LargeEvenProj H := ΨY.liftOfSurjective hΨYsurj ⟨φ, hkerφΨ⟩
  have hθfac : ∀ B, θ (ΨY B) = φ B := fun B =>
    ΨY.liftOfRightInverse_comp_apply _ _ ⟨φ, hkerφΨ⟩ B
  have hθsurj : Function.Surjective θ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin 6) K).subgroupOf H) y
    obtain ⟨B, rfl⟩ := e.surjective h
    exact ⟨ΨY B, hθfac B⟩
  have hkerθ : θ.ker ≤ Subgroup.center ↥Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨B, rfl⟩ := hΨYsurj y
    have hφB : φ B = 1 := by rw [← hθfac B]; exact hy
    have hBcenter : B ∈ Subgroup.center (unitarySL σ') :=
      (unitarySLEquivStated_mk_eq_one_iff hK σ' hσ' B).1 hφB
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨C, rfl⟩ := hΨYsurj y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hBcenter C]
  have hYperf : Group.IsPerfect ↥Y := Group.IsPerfect.ofSurjective (f := ΨY) hΨYsurj
  have hcommY : commutator ↥Y = ⊤ := Group.IsPerfect.commutator_eq_top
  exact ⟨A5Core.mk Ψ (c0 - σ' c0) hΨ ΨU (fun B => rfl) Y rfl hM e φ (fun B => rfl)
    hφsurj hkerφ ΨY hΨYsurj θ hθfac hθsurj hkerθ hcommY⟩

private theorem a5Core_contain {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (D : A5Core hK σ hσ) :
    (∀ a : Fin TwistTag.E6.foldedTag.rank, a.val ≤ 2 →
      orbitRankOneGroup TwistTag.E6 K σ.toRingHom a ≤
        D.Y.map (twistedE6RootGroup K σ).subtype) ∧
    ((frameHom σ.toRingHom 0).range ⊔ (frameHom σ.toRingHom 1).range ⊔
      (frameHom σ.toRingHom 2).range ⊔ (torusG σ.toRingHom).range ≤ D.Y) ∧
    (∀ y ∈ D.Y, ∀ z ∈ (frameHom σ.toRingHom 3).range, y * z = z * y) := by
  have hM0 := D.hM orb0 (by decide)
  have hM1 := D.hM orb1 (by decide)
  have hM2 := D.hM orbLeaf (by decide)
  have hYmem : ∀ y : ↥(twistedE6RootGroup K σ),
      (y : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ.toRingHom).map D.Ψ → y ∈ D.Y := by
    rw [D.hY]
    rintro y ⟨B, hB, hBy⟩
    refine ⟨⟨B, hB⟩, ?_⟩
    apply Subtype.ext
    rw [D.hΨU_coe]
    exact hBy
  have hYmap : D.Y.map (twistedE6RootGroup K σ).subtype =
      (unitarySL σ.toRingHom).map D.Ψ := by
    rw [D.hY]
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨B, rfl⟩ := hy
      exact ⟨B, B.2, (D.hΨU_coe B).symm⟩
    · rintro _ ⟨B, hB, rfl⟩
      refine ⟨D.ΨU ⟨B, hB⟩, ⟨⟨B, hB⟩, rfl⟩, ?_⟩
      exact D.hΨU_coe ⟨B, hB⟩
  have hframe : ((frameHom σ.toRingHom 0).range ⊔ (frameHom σ.toRingHom 1).range ⊔
      (frameHom σ.toRingHom 2).range ⊔ (torusG σ.toRingHom).range ≤ D.Y) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · rintro _ ⟨A, rfl⟩
      exact hYmem _ (frameHom_mem_of_orbit hM0 hM1 hM2 0 (by decide) A)
    · rintro _ ⟨A, rfl⟩
      exact hYmem _ (frameHom_mem_of_orbit hM0 hM1 hM2 1 (by decide) A)
    · rintro _ ⟨A, rfl⟩
      exact hYmem _ (frameHom_mem_of_orbit hM0 hM1 hM2 2 (by decide) A)
    · rintro _ ⟨pr, rfl⟩
      exact hYmem _ (by rw [coe_torusG]; exact torusAB_mem_of_orbit hM0 hM1 pr.1.2 pr.2.2)
  have hcentral : ∀ y ∈ D.Y, ∀ z ∈ (frameHom σ.toRingHom 3).range, y * z = z * y := by
    intro y hy z hz
    rw [D.hY] at hy
    obtain ⟨B, rfl⟩ := hy
    obtain ⟨A, rfl⟩ := hz
    have hB5 : D.Ψ (B : Matrix.SpecialLinearGroup (Fin 6) K) ∈ D.Ψ.range := ⟨B, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [D.hΨU_coe B]
    exact (commute_frameHom_three σ.toRingHom A (D.hΨ.range_le hB5)).symm
  refine ⟨?_, hframe, hcentral⟩
  intro a ha
  rw [hYmap]
  exact D.hM a ha

end Certificates

end E6

theorem exists_a5Datum_twE6
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ (Y : Subgroup ↥(twistedE6RootGroup K σ))
      (θ : ↥Y →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))),
      Function.Surjective θ ∧ θ.ker ≤ Subgroup.center ↥Y ∧ commutator ↥Y = ⊤ ∧
      (∀ z ∈ Subgroup.center ↥Y, z ^ p = 1 → z = 1) ∧
      (∀ x : ↥Y, MulAut.conj (θ x) ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n))) (LargeEvenGUSet (Fin 6) K (2 ^ n))) ∧
      (∀ a : Fin TwistTag.E6.foldedTag.rank, a.val ≤ 2 →
        orbitRankOneGroup TwistTag.E6 K σ.toRingHom a ≤ Y.map (twistedE6RootGroup K σ).subtype) ∧
      ((frameHom σ.toRingHom 0).range ⊔ (frameHom σ.toRingHom 1).range ⊔
        (frameHom σ.toRingHom 2).range ⊔ (torusG σ.toRingHom).range ≤ Y) ∧
      (∀ y ∈ Y, ∀ z ∈ (frameHom σ.toRingHom 3).range, y * z = z * y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, hK'⟩
  have : CharP K 2 := hU.charP
  obtain ⟨D⟩ := a5Core_exists hn hK σ hσ
  obtain ⟨hcontain, hframe, hcentral⟩ := a5Core_contain hK σ hσ D
  refine ⟨D.Y, D.θ, D.hθsurj, D.hkerθ, D.hcommY,
    a5Core_center_exp hp5 hK σ hσ D, ?_, hcontain, hframe, hcentral⟩
  exact a5Core_gu hK σ hσ D

end CFSG.StandardType.PhiTwoRootGen

end
