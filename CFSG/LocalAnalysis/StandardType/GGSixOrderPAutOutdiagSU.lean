module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUTorus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace OrdPOutSU

section Block

variable {f : ℕ} {K : Type} [Field K]

theorem IsUnitaryPPD.not_dvd_card_gramSU {r n : ℕ} (hU : IsUnitaryPPD r f n)
    (h : UnitaryFieldData 2 f K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hk : 1 ≤ Fintype.card ι) (hkn : Fintype.card ι < n) :
    ¬ r ∣ Nat.card (gramSU h (1 : Matrix ι ι K)) := by
  have : CharP K 2 := h.charP
  have hU' := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix ι ι K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fintype_fun_eq_card K) hk).2.1
  rw [card_gramSU]
  intro hd
  have hd' := hU' ▸ Int.natCast_dvd_natCast.mpr hd
  have hrp : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hU.prime
  rcases hrp.dvd_or_dvd hd' with h1 | h1
  · have h2 : r ∣ 2 ^ f := Int.natCast_dvd_natCast.mp (hrp.dvd_of_dvd_pow h1)
    exact hU.ne_two h.one_le ((Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).mp
      (hU.prime.dvd_of_dvd_pow h2))
  · obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hrp _).mp h1
    rw [Finset.mem_Icc] at hi
    exact hU.not_dvd i (by omega) (by omega) hdi

theorem false_of_commute_diagonal (h : UnitaryFieldData 2 f K) {n r : ℕ}
    (hU : IsUnitaryPPD r f n) {W : GL (Fin n) K} (hWU : W ∈ primeFormUnitary h (idGram K n))
    (hWr : W ^ r = 1) (hW1 : W ≠ 1) {t : Fin n → K}
    (hcomm : (W : Matrix (Fin n) (Fin n) K) * diagonal t = diagonal t * W)
    (ht : ∀ c, ∃ i, t i ≠ c) : False := by
  classical
  have hrp := hU.prime
  have : Fact r.Prime := ⟨hrp⟩
  set M : Matrix (Fin n) (Fin n) K := (W : Matrix (Fin n) (Fin n) K) with hMdef
  have hM1 : M ≠ 1 := fun h' => hW1 (Units.ext h')
  have hMr : M ^ r = 1 := by rw [hMdef, ← Units.val_pow_eq_pow_val, hWr, Units.val_one]
  have hMU : (M.map h.bar)ᵀ * M = 1 := by
    have h1 := mem_primeFormUnitary.mp hWU
    rwa [idGram, Units.val_one, Matrix.mul_one] at h1
  have hbd := TypeA.PGLTor.isBlockDiag_of_commute_diagonal hcomm
  have hbd' : TypeA.PGLTor.IsBlockDiag t (M.map h.bar)ᵀ := fun i j hij => by
    rw [transpose_apply, map_apply, hbd j i (Ne.symm hij), map_zero]
  obtain ⟨c, hc⟩ : ∃ c, M.toSquareBlock t c ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hM1
    ext i j
    by_cases hij : t i = t j
    · have h := congrFun (congrFun (hall (t j)) ⟨i, hij⟩) ⟨j, rfl⟩
      simpa only [toSquareBlock_def, of_apply, one_apply, Subtype.mk.injEq] using h
    · rw [hbd i j hij, one_apply_ne (fun h => hij (by rw [h]))]
  set Mc := M.toSquareBlock t c with hMc
  have hcard : Fintype.card {i // t i = c} < n := by
    obtain ⟨i, hi⟩ := ht c
    calc Fintype.card {i // t i = c} < Fintype.card (Fin n) :=
          Fintype.card_subtype_lt (p := fun i => t i = c) (x := i) hi
      _ = n := Fintype.card_fin n
  have hcard1 : 1 ≤ Fintype.card {i // t i = c} := by
    by_contra h0
    have h0' : Fintype.card {i // t i = c} = 0 := by omega
    have : IsEmpty {i // t i = c} := Fintype.card_eq_zero_iff.mp h0'
    exact hc (Subsingleton.elim _ _)
  have hMcr : Mc ^ r = 1 := by
    rw [hMc, ← TypeA.PGLTor.toSquareBlock_pow_of_isBlockDiag hbd, hMr,
      TypeA.PGLTor.toSquareBlock_one]
  have hMcU : (Mc.map h.bar)ᵀ * Mc = 1 := by
    have h1 : ((M.map h.bar)ᵀ * M).toSquareBlock t c =
        (1 : Matrix (Fin n) (Fin n) K).toSquareBlock t c := by rw [hMU]
    rw [TypeA.PGLTor.toSquareBlock_mul_of_isBlockDiag hbd', TypeA.PGLTor.toSquareBlock_one] at h1
    have h2 : (M.map h.bar)ᵀ.toSquareBlock t c = (Mc.map h.bar)ᵀ := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [hMc, toSquareBlock_def, of_apply, transpose_apply, map_apply]
    rw [← h2, hMc]
    exact h1
  have hdet : Mc.det = 1 := by
    have h1 : Mc.det ^ r = 1 := by rw [← det_pow, hMcr, det_one]
    have h2 : Mc.det ^ (2 ^ f + 1) = 1 := by
      have h3 := congrArg Matrix.det hMcU
      have h4 : (Mc.map h.bar).det = h.bar Mc.det := (RingHom.map_det h.bar _).symm
      rw [det_mul, det_transpose, h4, det_one, UnitaryFieldData.bar_apply] at h3
      rw [pow_succ]
      exact h3
    have hcop : Nat.Coprime r (2 ^ f + 1) :=
      (Nat.Prime.coprime_iff_not_dvd hrp).mpr (hU.not_dvd_two_pow_add_one (by omega))
    have h4 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h4
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel hrp.one_lt.le
  let g : GL {i // t i = c} K := ⟨Mc, Mc ^ (r - 1),
    by rw [← pow_succ', hr1, hMcr], by rw [← pow_succ, hr1, hMcr]⟩
  have hg : g ∈ gramSU h (1 : Matrix {i // t i = c} {i // t i = c} K) :=
    mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact hMcU, hdet⟩
  have hgo : orderOf (⟨g, hg⟩ : gramSU h (1 : Matrix {i // t i = c} {i // t i = c} K)) = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      apply Units.ext
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
      exact hMcr
    · intro h1
      exact hc (congrArg (fun x : gramSU h (1 : Matrix {i // t i = c} {i // t i = c} K) =>
        ((x : GL {i // t i = c} K) : Matrix {i // t i = c} {i // t i = c} K)) h1)
  exact hU.not_dvd_card_gramSU h hcard1 hcard (hgo ▸ orderOf_dvd_natCard _)

end Block

section Frame

variable {G : Type} [Group G] {n f : ℕ}

theorem unitaryFieldData_galois (f : ℕ) :
    UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
  ⟨Nat.prime_two, by omega, by
    rw [card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f), ← pow_mul, mul_comm]⟩

theorem false_of_commute_frame {p r : ℕ} (hU : IsUnitaryPPD r (f + 1) n) (hn4 : 4 ≤ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ (f + 1) + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n →* G}
    (hker : ψ.ker ≤
      Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    {P : GL (Fin n) (GaloisField 2 (2 * (f + 1)))}
    (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
        (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n)
    {b : G} (hbD : SURep.GGFrameDiagU (SURep.ggFrameU
        (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b)
    (hbp : b ^ p = 1) (hb1 : b ≠ 1) {z : G} (hzM : z ∈ Subgroup.normalizer (ψ.range : Set G))
    (hzr : orderOf z = r) (hzb : z * b = b * z) : False := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h := unitaryFieldData_galois f
  have : Fact r.Prime := ⟨hU.prime⟩
  have : NeZero n := ⟨by omega⟩
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  set φ := SURep.ggFrameU hF ψ P hP with hφ
  have hφr : φ.range = ψ.range := SURep.range_ggFrameU hF ψ P hP
  have hcent : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hφr]; exact hC
  have hkerφ := SURep.ker_ggFrameU_le hF ψ P hP hker
  have hσ : ∀ φ' : GaloisField 2 (2 * (f + 1)) ≃+* GaloisField 2 (2 * (f + 1)),
      φ' ^ r = 1 → φ' = 1 := fun φ' h' =>
    LinModel.eq_one_of_pow_eq_one_of_not_dvd (by omega) hU.prime (fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      have := hU.lt
      omega) h'
  have hzr1 : z ^ r = 1 := hzr ▸ pow_orderOf_eq_one z
  obtain ⟨A, hAJ, hAc⟩ :=
    UnitModel.exists_mem_suInducedPairs_of_pow_eq_one h hn4 hker hC hσ hzM hzr1
  have hZ : (z, P * A * P⁻¹) ∈ SUTorus.suPairs φ :=
    SUTorus.mem_suPairs_transfer P hP
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n) hAJ hAc
  have hZU : P * A * P⁻¹ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) :=
    SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP hAJ)
  obtain ⟨μ, hμ⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hp hpq hkerφ (by
    have := (SUTorus.suPairs φ).pow_mem hZ r
    rwa [Prod.pow_mk, hzr1] at this)
  have hμN : μ ^ (2 ^ (f + 1) + 1) = 1 := by
    have hcU : GeneralLinearGroup.scalar (Fin n) μ ∈
        primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
      rw [← hμ]
      exact (primeFormUnitary h _).pow_mem hZU r
    have h1 := (SUTorus.scalar_mem_primeFormUnitary_iff h μ).mp hcU
    rw [UnitaryFieldData.bar_apply] at h1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, h1, Units.val_one]
  obtain ⟨W, hW⟩ : ∃ W, W = (P * A * P⁻¹) ^ (2 ^ (f + 1) + 1) := ⟨_, rfl⟩
  have hWr : W ^ r = 1 := by
    rw [hW, ← pow_mul, mul_comm (2 ^ (f + 1) + 1) r, pow_mul, hμ, ← map_pow, hμN, map_one]
  have hWU : W ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
    rw [hW]
    exact (primeFormUnitary h _).pow_mem hZU _
  obtain ⟨z', hz'⟩ : ∃ z', z' = z ^ (2 ^ (f + 1) + 1) := ⟨_, rfl⟩
  have hz'W : (z', W) ∈ SUTorus.suPairs φ := by
    have := (SUTorus.suPairs φ).pow_mem hZ (2 ^ (f + 1) + 1)
    rwa [Prod.pow_mk, ← hW, ← hz'] at this
  have hz'1 : z' ≠ 1 := by
    intro h1
    rw [hz'] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hzr] at h2
    exact hU.not_dvd_two_pow_add_one (by omega) h2
  have hW1 : W ≠ 1 := by
    intro h1
    rw [h1] at hz'W
    have := SUTorus.mem_centralizer_of_mem_suPairs_one hz'W
    rw [hcent, Subgroup.mem_bot] at this
    exact hz'1 this
  obtain ⟨τ, hτ⟩ := hbD
  have hDU : diagHom n τ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
    rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
    exact CFSG.RankThree.Classical2.diagHom_unitary h hτ.1
  have hbD' : (b, diagHom n τ) ∈ SUTorus.suPairs φ :=
    ⟨SUTorus.mem_normalizer_of_mem_primeFormUnitary h hDU, fun s s' hs' => hτ.2 s s' hs'⟩
  have hz'b : z' * b = b * z' := by
    rw [hz']
    exact (Commute.pow_left hzb _).eq
  have h1 : (z' * b, W * diagHom n τ) ∈ SUTorus.suPairs φ := by
    have := (SUTorus.suPairs φ).mul_mem hz'W hbD'
    rwa [Prod.mk_mul_mk] at this
  have h2 : (z' * b, diagHom n τ * W) ∈ SUTorus.suPairs φ := by
    have := (SUTorus.suPairs φ).mul_mem hbD' hz'W
    rw [Prod.mk_mul_mk, ← hz'b] at this
    exact this
  obtain ⟨l, hl⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn3 hnq hp hpq hkerφ h1 h2
  obtain ⟨S, hS⟩ : ∃ S, S = GeneralLinearGroup.scalar (Fin n) l := ⟨_, rfl⟩
  rw [← hS] at hl
  have hSW : Commute S W := by
    rw [hS]
    exact TypeA.PGLTor.commute_scalar l W
  have hSr : S ^ r = 1 := by
    have h3 := TypeA.PGLTor.mul_pow_eq_of_mul_eq hSW hl r
    rw [hWr, mul_one, one_mul] at h3
    exact mul_right_cancel (h3.symm.trans (one_mul (diagHom n τ)).symm)
  obtain ⟨ν, hν⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hp hpq hkerφ (by
    have := (SUTorus.suPairs φ).pow_mem hbD' p
    rwa [Prod.pow_mk, hbp] at this)
  have hSp : S ^ p = 1 := by
    have hl' : W * diagHom n τ = S⁻¹ * (diagHom n τ * W) := by rw [hl]; group
    have hSD : Commute S⁻¹ (diagHom n τ) := by
      rw [hS]
      exact (TypeA.PGLTor.commute_scalar l (diagHom n τ)).inv_left
    have h3 := TypeA.PGLTor.mul_pow_eq_of_mul_eq hSD hl' p
    rw [hν, ← mul_assoc, (TypeA.PGLTor.commute_scalar ν W).eq.symm] at h3
    have h4 := mul_right_cancel h3
    have h5 : (S⁻¹) ^ p = 1 := mul_right_cancel
      (h4.symm.trans (one_mul (GeneralLinearGroup.scalar (Fin n) ν)).symm)
    rw [inv_pow, inv_eq_one] at h5
    exact h5
  have hpr : p.Coprime r := (Nat.coprime_primes hp hU.prime).mpr fun he =>
    hU.not_dvd_two_pow_add_one (by omega) (he ▸ hpq)
  have hS1 : S = 1 := by
    have h3 := pow_gcd_eq_one.mpr ⟨hSp, hSr⟩
    rwa [hpr.gcd_eq_one, pow_one] at h3
  rw [hS1, one_mul] at hl
  have ht : ∀ c : GaloisField 2 (2 * (f + 1)), ∃ i, ((τ i : (GaloisField 2 (2 * (f + 1)))ˣ) :
      GaloisField 2 (2 * (f + 1))) ≠ c := by
    intro c
    by_contra hall
    push Not at hall
    apply hb1
    have i0 : Fin n := ⟨0, by omega⟩
    have hsc : diagHom n τ * GeneralLinearGroup.scalar (Fin n) (τ i0)⁻¹ = 1 := by
      apply Units.ext
      rw [Units.val_mul, coe_diagHom, GeneralLinearGroup.coe_scalar, scalar_apply,
        diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
      congr 1
      funext i
      rw [hall i, ← hall i0, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _)]
    have h3 := (SUTorus.suPairs φ).mul_mem hbD' (SUTorus.one_scalar_mem_suPairs φ (τ i0)⁻¹)
    rw [Prod.mk_mul_mk, mul_one, hsc] at h3
    have h4 := SUTorus.mem_centralizer_of_mem_suPairs_one h3
    rwa [hcent, Subgroup.mem_bot] at h4
  refine false_of_commute_diagonal h hU hWU hWr hW1
    (t := fun i => ((τ i : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1)))) ?_ ht
  have h3 := congrArg (fun X : GL (Fin n) (GaloisField 2 (2 * (f + 1))) =>
    (X : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) hl
  simp only [Units.val_mul, coe_diagHom] at h3
  exact h3.symm

theorem frame_ne_one {r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ 2 ^ (f + 1) + 1)
    (hn3 : 3 ≤ n) {φ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) →* G}
    (hkerφ : SURep.GGFrameKer φ) (g : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n))
    (hgo : orderOf (g : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = r) : φ g ≠ 1 := by
  have h := unitaryFieldData_galois f
  intro h1
  obtain ⟨c, hc⟩ := hkerφ g h1
  have i0 : Fin n := ⟨0, by omega⟩
  have hgr : (g : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) ^ r = 1 :=
    hgo ▸ pow_orderOf_eq_one _
  have hcr : c ^ r = 1 := by
    have h2 := congrArg (fun X : GL (Fin n) (GaloisField 2 (2 * (f + 1))) =>
      (X : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) i0 i0) hgr
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hc, scalar_apply, diagonal_pow,
      diagonal_apply_eq, Pi.pow_apply, one_apply_eq] at h2
    exact h2
  have hcN : c ^ (2 ^ (f + 1) + 1) = 1 := by
    have h2 := ((mem_unitarySU_iff h).mp g.2).2
    rw [hc] at h2
    have h3 := congrFun (congrFun h2 i0) i0
    simp only [scalar_apply, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq, UnitaryFieldData.bar_apply] at h3
    rw [pow_succ]
    exact h3
  have hcop : Nat.Coprime r (2 ^ (f + 1) + 1) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrq
  have hc1 : c = 1 := by
    have h4 := pow_gcd_eq_one.mpr ⟨hcr, hcN⟩
    rwa [hcop.gcd_eq_one, pow_one] at h4
  have hg1 : (g : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = 1 :=
    Units.ext (by rw [hc, hc1, Units.val_one, scalar_apply, diagonal_one])
  rw [hg1, orderOf_one] at hgo
  exact hr.one_lt.ne hgo

theorem false_of_outdiag [Finite G] {p r : ℕ} {Bs : Subgroup G} (hU : IsUnitaryPPD r (f + 1) n)
    (hn4 : 4 ≤ n) (hpn : p ∣ n) (hpq : p ∣ 2 ^ (f + 1) + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n →* G}
    (hS : GGSixFusionSetting p Bs ψ.range
      (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) n) .PSU n
        (f + 1) ψ)
    {b : G} (hb : b ∈ Bs) {y : G} (hyM : y ∈ Subgroup.normalizer (ψ.range : Set G))
    (hyo : orderOf y = p)
    (hy : GGPsiInnerDiag
      (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) n) ψ y)
    (hnc : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), m⁻¹ * y * m ∉ Bs)
    (hemb : GGCentralizerEmbeds (Subgroup.normalizer (ψ.range : Set G)) y b) : False := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h := unitaryFieldData_galois f
  have hp := hS.prime
  have hp2 := hS.ne_two
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero n := ⟨by omega⟩
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨-, ⟨-, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := hS.centralizer_eq_bot
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨P, hP, hBsD⟩ := UnitModel.exists_frame_of_su_gen hp hp2 hn4
    (div_add_one_lt_sub_two hp hp2 hpn hn4) hpq hker hC hS.bstar_le hS.elem hS.innerDiag
    hS.unique
  set φ := SURep.ggFrameU hF ψ P hP with hφ
  have hφr : φ.range = ψ.range := SURep.range_ggFrameU hF ψ P hP
  have hcent : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hφr]; exact hC
  have hkerφ := SURep.ker_ggFrameU_le hF ψ P hP hker
  obtain ⟨A, hAJ, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker y hy
  have hmem : (y⁻¹, A) ∈ UFusion.suInducedPairs ψ := ⟨hAJ, fun u => by rw [inv_inv]; exact hAc u⟩
  have hmem' : (y, A⁻¹) ∈ UFusion.suInducedPairs ψ := by
    have := (UFusion.suInducedPairs ψ).inv_mem hmem
    rwa [Prod.inv_mk, inv_inv] at this
  obtain ⟨hAJ', hAc'⟩ := hmem'
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = P * A⁻¹ * P⁻¹ := ⟨_, rfl⟩
  have hY : (y, Y) ∈ SUTorus.suPairs φ := by
    rw [hYdef]
    exact SUTorus.mem_suPairs_transfer P hP
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n) hAJ' hAc'
  have hYU : Y ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
    rw [hYdef]
    exact SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP hAJ')
  obtain ⟨c₀, hc₀⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hp hpq hkerφ (by
    have := (SUTorus.suPairs φ).pow_mem hY p
    rwa [Prod.pow_mk, hyp] at this)
  have hc₀N : c₀ ^ (2 ^ (f + 1) + 1) = 1 := by
    have hcU : GeneralLinearGroup.scalar (Fin n) c₀ ∈
        primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
      rw [← hc₀]
      exact (primeFormUnitary h _).pow_mem hYU p
    have h1 := (SUTorus.scalar_mem_primeFormUnitary_iff h c₀).mp hcU
    rw [UnitaryFieldData.bar_apply] at h1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, h1, Units.val_one]
  by_cases hroot : ∃ μ : (GaloisField 2 (2 * (f + 1)))ˣ, μ ^ p = c₀
  ·
    obtain ⟨μ, hμ⟩ := hroot
    have hμN : μ ^ (2 ^ (f + 1) + 1) = 1 :=
      SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hμ hc₀N
    obtain ⟨Y₂, hY₂⟩ : ∃ Y₂, Y₂ = GeneralLinearGroup.scalar (Fin n) μ⁻¹ * Y := ⟨_, rfl⟩
    have hY₂U : Y₂ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
      rw [hY₂]
      exact (primeFormUnitary h _).mul_mem
        (SUModel.scalar_mem_unitary h (by rw [inv_pow, hμN, inv_one])) hYU
    have hY₂p : Y₂ ^ p = 1 := by
      rw [hY₂, (TypeA.PGLTor.commute_scalar μ⁻¹ Y).mul_pow, hc₀, ← map_pow, ← map_mul, inv_pow,
        hμ, inv_mul_cancel, map_one]
    have hY₂pair : (y, Y₂) ∈ SUTorus.suPairs φ := by
      have h1 := (SUTorus.suPairs φ).mul_mem (SUTorus.one_scalar_mem_suPairs φ μ⁻¹) hY
      rwa [Prod.mk_mul_mk, one_mul, ← hY₂] at h1
    obtain ⟨s₀, τ, hτ⟩ := UnitModel.exists_det_one_conj_diag h hp hpq hY₂U hY₂p
    have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem
      ((SUTorus.suPairs φ).inv_mem (UnitModel.mem_suPairs_coe φ s₀)) hY₂pair)
      (UnitModel.mem_suPairs_coe φ s₀)
    rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, hτ] at h1
    have hτp : ∀ i, τ i ^ p = 1 := by
      have h2 : diagHom n (τ ^ p) = 1 := by
        rw [map_pow, ← hτ, show ((s₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))))⁻¹ * Y₂ * s₀ =
          MulAut.conj ((s₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))))⁻¹ Y₂ by
            rw [MulAut.conj_apply, inv_inv], ← map_pow, hY₂p, map_one]
      intro i
      have h3 := congrFun (diagHom_injective n (h2.trans (map_one _).symm)) i
      simpa using h3
    have hτN : ∀ i, ((τ i : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
        (2 ^ (f + 1) + 1) = 1 := fun i => by
      rw [← Units.val_pow_eq_pow_val, SUModel.pow_add_one_of_pow_eq_one hpq (hτp i),
        Units.val_one]
    have hact : SURep.GGFrameActs φ ((φ s₀)⁻¹ * y * φ s₀) τ :=
      ⟨hτN, fun s s' hs' => h1.2 s s' hs'⟩
    have hcen : (φ s₀)⁻¹ * y * φ s₀ ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      obtain ⟨τ', hb''⟩ := hBsD b' hb'
      exact (SURep.commute_of_frameActs h hcent hact hb'').symm
    have hsM : φ s₀ ∈ Subgroup.normalizer (ψ.range : Set G) := by
      rw [← hφr]
      exact Subgroup.le_normalizer ⟨s₀, rfl⟩
    exact hS.not_conj_mem_centralizer hyp hnc hsM hcen
  ·
    push Not at hroot
    obtain ⟨g, hgSU, hgo, hgY⟩ := exists_su_comm_of_twisted h (by omega) hp hp2 hpq hYU hc₀ hroot
      hU.prime (fun m hm => hU.dvd_pow_sub hodd hm) (hU.not_dvd_two_pow_add_one (by omega))
    obtain ⟨g', hg'⟩ : ∃ g' : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
        (g' : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = g := ⟨⟨g, hgSU⟩, rfl⟩
    have hgy : y * φ g' * y⁻¹ = φ g' := hY.2 g' g' (by rw [hg', ← hgY, mul_inv_cancel_right])
    have hgC : φ g' ∈ Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {y} := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← hφr]
        exact Subgroup.le_normalizer ⟨g', rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        calc x * φ g' = x * φ g' * x⁻¹ * x := by group
          _ = φ g' * x := by rw [hgy]
    have hgr : orderOf (φ g') = r := by
      have : Fact r.Prime := ⟨hU.prime⟩
      refine orderOf_eq_prime ?_ (frame_ne_one hU.prime (hU.not_dvd_two_pow_add_one (by omega))
        hn3 (SURep.ggFrameKer_ggFrameU hF ψ P hP hn3 hnq hker) g' (by rw [hg', hgo]))
      have hg'r : g' ^ r = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hg', ← hgo, pow_orderOf_eq_one])
      rw [← map_pow, hg'r, map_one]
    obtain ⟨θ, hθinj, hθC, hθy⟩ := hemb
    have hb1 : b ≠ 1 := by
      intro hb1
      have hyy : y ∈ Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {y} := by
        refine Subgroup.mem_inf.mpr ⟨hyM, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
      have h1 := hθy hyy
      rw [hb1, ← map_one θ] at h1
      have h3 : y = 1 := congrArg Subtype.val (hθinj h1)
      rw [h3, orderOf_one] at hyo
      exact hp.one_lt.ne hyo
    have hθr : orderOf (θ ⟨φ g', hgC⟩) = r := by
      rw [orderOf_injective θ hθinj, ← Subgroup.orderOf_coe]
      exact hgr
    obtain ⟨hθM, hθb⟩ := Subgroup.mem_inf.mp (hθC ⟨φ g', hgC⟩)
    have hcomm : θ ⟨φ g', hgC⟩ * b = b * θ ⟨φ g', hgC⟩ :=
      (Subgroup.mem_centralizer_iff.mp hθb b (Set.mem_singleton b)).symm
    exact false_of_commute_frame hU hn4 hp hpq hker hC hP (hBsD b hb) (hS.elem.2 b hb) hb1 hθM
      hθr hcomm

end Frame

end OrdPOutSU

section Family

theorem ggOrdPOutdiag_PSU_false :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
      (ψ : (ggU .PSU n f).K →* G),
      GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ →
      GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → GGOutdiagPrimeConfig p .PSU n f →
      ∀ b ∈ Bs, ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
        GGPsiInnerDiag (ggU .PSU n f).D ψ y →
        (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
        GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b → False := by
  intro G _ _ p Bs G₀ n f ψ hS _ hcfg b hb y hyM hyo hy hnc hemb
  obtain ⟨hpn, hpq⟩ : p ∣ n ∧ p ∣ 2 ^ f + 1 := by
    rcases hcfg with ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact ⟨h1, h2⟩
    all_goals exact absurd h (by decide)
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, -⟩, -, -⟩ := hS.presents
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hn4 : 4 ≤ n := by
    have : 2 ≤ n / 2 := hrank
    omega
  subst hrange
  have hp := hS.prime
  obtain ⟨r, hU⟩ := OrdPOutSU.exists_isUnitaryPPD (f := f + 1) (n := n) (by omega) (by omega)
    (by omega) (fun ⟨h6, hf2⟩ => by
      rw [hf2] at hpq
      rw [h6] at hpn
      have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (by simpa using hpq)
      rw [h5] at hpn
      omega)
  exact OrdPOutSU.false_of_outdiag hU hn4 hpn hpq hS hb hyM hyo hy hnc hemb

theorem ggOrdPOutdiagAt_PSU : GGOrdPOutdiagAt .PSU := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hcfg b hb y hyM hyo hy hnc hemb
  exact (ggOrdPOutdiag_PSU_false G p Bs G₀ n f ψ hS h24 hcfg b hb y hyM hyo hy hnc hemb).elim

end Family

end CFSG.StandardType
