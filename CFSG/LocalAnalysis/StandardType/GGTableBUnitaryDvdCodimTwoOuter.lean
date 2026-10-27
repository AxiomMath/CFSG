module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestOuter

public section

namespace CFSG.StandardType

namespace TableBUDT

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover TableBUD TableBUE
  TableBUR

variable {K : Type} [Field K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

section Transport

@[expose] noncomputable def projE (hd : 1 ≤ d) :
    LargeEvenProj (unitarySU 2 n K d) ≃*
      primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  InndiagSU.projEquiv h hd

theorem projE_mk (hd : 1 ≤ d) (x : ↥(unitarySU 2 n K d)) :
    projE h hd (LargeEvenProjMk _ x) =
      ((⟨x, InndiagSU.largeEvenSUGroup_eq_gramSU (d := d) h ▸ x.2⟩ :
        gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
          primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
  InndiagSU.projEquiv_mk h hd x

theorem mem_unitarySU_of_gram (s : gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    (s : GL (Fin d) K) ∈ unitarySU 2 n K d := by
  have h1 : (s : GL (Fin d) K) ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    rw [InndiagSU.largeEvenSUGroup_eq_gramSU h]
    exact s.2
  exact h1

theorem projE_symm_mk (hd : 1 ≤ d)
    (s : gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    (projE h hd).symm (s : primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      LargeEvenProjMk (unitarySU 2 n K d) ⟨s, mem_unitarySU_of_gram h s⟩ :=
  InndiagSU.projEquiv_symm_mk h hd s

theorem congr_projConj_eq (hd : 1 ≤ d) {D : GL (Fin d) K}
    (hN : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hU : D ∈ primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    MulAut.congr (projE h hd) (TableB.projConj (unitarySU 2 n K d) ⟨D, hN⟩) =
      primeFormConjHom h _ ⟨D, hU⟩ := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_
  rw [primeFormConjHom_mk, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    projE_symm_mk, projConj_mk_coe, projE_mk]
  rfl

end Transport

section Inner

variable [Finite K]

include h in
theorem exists_eq_of_inn (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hpq : p ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} {ν : Ab →* (Fin d → Kˣ)}
    (hνp : ∀ a k, ν a k ∈ rootsOfUnity p K)
    (hνN : ∀ a : Ab, ∃ hN : diagHom d (ν a) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
          (a : MulAut _) = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d (ν a), hN⟩)
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hU2 : IsPGroup 2 U)
    (hAU : Ab ≤ Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))))
    (hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range ≠ ⊥) :
    ∃ s t : Fin d, s ≠ t ∧ ∀ a : Ab, ν a s = ν a t := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  set φ : ↥(unitarySU 2 n K d) →* MulAut (LargeEvenProj (unitarySU 2 n K d)) :=
    (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).comp π with hφ
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    center_proj_eq_bot hK hd hdq
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
    intro x hx
    apply ker_projMk_le_center
    rw [MonoidHom.mem_ker] at hx ⊢
    exact conj_injective_of_center hZ (by rw [map_one]; exact hx)
  set V := U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range with hV
  have hV2 : IsPGroup 2 V := hU2.to_le inf_le_left
  have hVφ : V ≤ φ.range := by
    rintro _ ⟨-, ⟨r, rfl⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ r
    exact ⟨x, rfl⟩
  have hBV : Ab ≤ Subgroup.normalizer (V : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hUa := (Subgroup.mem_normalizer_iff.mp (hAU ha)) v
    constructor
    · rintro ⟨hvU, ⟨r, rfl⟩⟩
      exact ⟨hUa.mp hvU, ⟨a r, (mul_conj_mul_inv_eq a r).symm⟩⟩
    · rintro ⟨hvU, ⟨r, hr⟩⟩
      refine ⟨hUa.mpr hvU, ⟨a⁻¹ r, ?_⟩⟩
      have e := mul_conj_mul_inv_eq a⁻¹ r
      rw [hr, inv_inv] at e
      rw [← e]
      group
  obtain ⟨s, t, hst, hpair⟩ := SURepair.exists_framePair_of_twoSubgroup h hker hUI hV2 hVφ hBV
  refine ⟨s, t, hst, fun a => hpair a a.2 (ν a) ⟨fun i => ?_, fun x x' hxx' => ?_⟩⟩
  · have h1 : ν a i ^ p = 1 := (mem_rootsOfUnity _ _).mp (hνp a i)
    obtain ⟨k, hk⟩ := hpq
    rw [← Units.val_pow_eq_pow_val, hk, pow_mul, h1, one_pow, Units.val_one]
  · obtain ⟨hN, hνa⟩ := hνN a
    change (a : MulAut _) * MulAut.conj (π x) * (a : MulAut _)⁻¹ = MulAut.conj (π x')
    rw [mul_conj_mul_inv_eq, hνa, projConj_mk_coe]
    congr 2
    exact Subtype.ext hxx'.symm

end Inner

section Outer

variable [Finite K]

include h in
theorem exists_sigma_of_outer (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) {p : ℕ} (hpq : p ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} {ν : Ab →* (Fin d → Kˣ)}
    (hνp : ∀ a k, ν a k ∈ rootsOfUnity p K)
    (hνN : ∀ a : Ab, ∃ hN : diagHom d (ν a) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
          (a : MulAut _) = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d (ν a), hN⟩)
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U)
    (hAU : Ab ≤ Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))))
    (hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range = ⊥) :
    ∃ σ : Fin d → Fin d, ∀ a : Ab, ∃ z : Kˣ, ∀ i, ν a (σ i) * ν a i = z := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hC := isPrimeFormGram_one (K := K) (n := d)
  set e := projE h hd1 with he
  set E := MulAut.congr e with hE
  obtain ⟨-, -, hPsi1, -, hreal, hFF, -, -, hD, -, hcardD⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hd hq
  have hnorm : ∀ a : Ab, ∀ i, (ν a i : K) ^ (2 ^ n + 1) = 1 := by
    intro a i
    have h1 : ν a i ^ p = 1 := (mem_rootsOfUnity _ _).mp (hνp a i)
    obtain ⟨k, hk⟩ := hpq
    rw [← Units.val_pow_eq_pow_val, hk, pow_mul, h1, one_pow, Units.val_one]
  have hDU : ∀ a : Ab, diagHom d (ν a) ∈
      primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro a
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact CFSG.RankThree.Classical2.diagHom_unitary h (hnorm a)
  have hEa : ∀ a : Ab, E a = primeFormConjHom h _ ⟨diagHom d (ν a), hDU a⟩ := fun a => by
    obtain ⟨hN, hνa⟩ := hνN a
    rw [hE, hνa]
    exact congr_projConj_eq h hd1 hN (hDU a)
  have htriv : ∀ c ∈ U, E c ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
      c = 1 := by
    intro c hcU hcD
    obtain ⟨k, hk⟩ := hU2 ⟨c, hcU⟩
    have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    set Dd := primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hDd
    set N := (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))).subgroupOf Dd with hN
    set y : Dd := ⟨E c, hcD⟩ with hy
    have hy2 : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hy]
      change (E c) ^ 2 ^ k = 1
      rw [← map_pow, hk', map_one]
    have hord : orderOf (y : Dd ⧸ N) = 1 := by
      have h1 : orderOf (y : Dd ⧸ N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        rw [← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one])
      have h2 : orderOf (y : Dd ⧸ N) ∣ 2 ^ n + 1 := (orderOf_dvd_natCard _).trans hcardD
      have hodd : Nat.Coprime (2 ^ k) (2 ^ n + 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_two_left]
        exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩)
      exact Nat.eq_one_of_dvd_coprimes hodd h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hord
    obtain ⟨y', hy'⟩ := hord
    have hc : c = MulAut.conj (e.symm y') := by
      apply E.injective
      rw [hE, congr_conj, MulEquiv.apply_symm_apply]
      exact hy'.symm
    have hmem : c ∈ U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range :=
      ⟨hcU, ⟨e.symm y', hc.symm⟩⟩
    rw [hUI, Subgroup.mem_bot] at hmem
    exact hmem
  have hcomm : ∀ a : Ab, ∀ u ∈ U, (a : MulAut _) * u = u * (a : MulAut _) := by
    intro a u hu
    have hcU : (a : MulAut _) * u * (a : MulAut _)⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAU a.2) u).mp hu) (U.inv_mem hu)
    have h1 : E a ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      ⟨_, (hEa a).symm⟩
    have hcD : E ((a : MulAut _) * u * (a : MulAut _)⁻¹ * u⁻¹) ∈
        primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        show E a * E u * (E a)⁻¹ * (E u)⁻¹ = E a * (E u * (E a)⁻¹ * (E u)⁻¹) by group]
      exact Subgroup.mul_mem _ h1 (hD.conj_mem _ (Subgroup.inv_mem _ h1) (E u))
    have h2 := htriv _ hcU hcD
    calc (a : MulAut _) * u = (a : MulAut _) * u * (a : MulAut _)⁻¹ * u⁻¹ * (u * (a : MulAut _)) :=
          by group
      _ = u * (a : MulAut _) := by rw [h2, one_mul]
  have : Finite (MulAut (LargeEvenProj (unitarySU 2 n K d))) := inferInstance
  have h2U : 2 ∣ Nat.card U := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hU1 hk
    · exact dvd_pow_self 2 hk0.ne'
  have := Fact.mk Nat.prime_two
  obtain ⟨⟨u, huU⟩, hu2⟩ := exists_prime_orderOf_dvd_card' 2 h2U
  rw [Subgroup.orderOf_mk] at hu2
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    norm_num at hu2
  obtain ⟨φ, ⟨B, hB⟩, -⟩ := hreal (E u)
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    have hmem : E u ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      ⟨B, by rw [hB, map_one, mul_one]⟩
    exact hu1 (htriv u huU hmem)
  have hφ2 : φ ^ 2 = 1 := by
    have h1 : primeFormFieldFactor h hC hd hq (E u) = φ := by
      rw [hB]
      exact hFF B φ
    have hu2' : u ^ 2 = 1 := by
      have h3 := pow_orderOf_eq_one u
      rwa [hu2] at h3
    rw [← h1, ← map_pow, ← map_pow, hu2', map_one, map_one]
  have hφbar : ∀ x : K, φ x = x ^ 2 ^ n := by
    have hn1 := h.one_le
    obtain ⟨s, hs, hφs, hφm⟩ := exists_frobenius_pow_eq (n := 2 * n) (by omega)
      (by rw [hK, ← pow_mul, mul_comm]) φ
    have h2 := (hφm 2).mp hφ2
    have h1 : ¬ 2 * n ∣ 1 * s := fun hdvd => hφ1 (by simpa using (hφm 1).mpr hdvd)
    obtain ⟨k, hk⟩ := h2
    have hsn : s = n := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · exfalso
          apply h1
          have : s = 0 := by omega
          rw [this]
          exact dvd_zero _
        · omega
      · have : 2 * n * 2 ≤ 2 * n * k := Nat.mul_le_mul_left _ hk2
        omega
    intro x
    rw [hφs x, hsn]
  have hrow : ∀ i, ∃ j, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j ≠ 0 := by
    intro i
    by_contra hcon
    push Not at hcon
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (B : GL (Fin d) K).isUnit).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero i hcon)
  choose σ hσ using hrow
  refine ⟨σ, fun a => ?_⟩
  set Dg : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    ⟨diagHom d (ν a), hDU a⟩ with hDg
  have hEc : E u * E a = E a * E u := by rw [← map_mul, ← map_mul, hcomm a u huU]
  rw [hEa a, hB] at hEc
  have key : primeFormConjHom h _ (B * primeFormFieldU h hC φ Dg) =
      primeFormConjHom h _ (Dg * B) := by
    rw [map_mul, map_mul, ← primeFormField_conj_eq h hC φ Dg]
    calc primeFormConjHom h _ B * (primeFormFieldHom h hC φ * primeFormConjHom h _ Dg *
          (primeFormFieldHom h hC φ)⁻¹)
        = primeFormConjHom h _ B * primeFormFieldHom h hC φ * primeFormConjHom h _ Dg *
          (primeFormFieldHom h hC φ)⁻¹ := by group
      _ = primeFormConjHom h _ Dg * (primeFormConjHom h _ B * primeFormFieldHom h hC φ) *
          (primeFormFieldHom h hC φ)⁻¹ := by rw [hEc]
      _ = primeFormConjHom h _ Dg * primeFormConjHom h _ B := by group
  have hM1 : primeFormPsi h hC ⟨(Dg * B)⁻¹ * (B * primeFormFieldU h hC φ Dg),
      RingEquiv.refl K⟩ = 1 := by
    rw [primeFormPsi_apply, map_mul, map_inv, key, inv_mul_cancel, one_mul]
    exact map_one _
  obtain ⟨-, c, -, hcM⟩ := (hPsi1 _).mp hM1
  have hmat : ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((glAut φ (diagHom d (ν a)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (c : K) • (((diagHom d (ν a)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h1 : (B : GL (Fin d) K) * glAut φ (diagHom d (ν a)) =
        Matrix.GeneralLinearGroup.scalar (Fin d) c * (diagHom d (ν a) * (B : GL (Fin d) K)) := by
      have h2 : (((Dg * B)⁻¹ * (B * primeFormFieldU h hC φ Dg) :
          primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) : GL (Fin d) K) =
            (diagHom d (ν a) * (B : GL (Fin d) K))⁻¹ *
              ((B : GL (Fin d) K) * glAut φ (diagHom d (ν a))) := rfl
      rw [h2] at hcM
      rw [TypeA.PGLTor.scalar_mul_comm]
      calc (B : GL (Fin d) K) * glAut φ (diagHom d (ν a)) =
          diagHom d (ν a) * (B : GL (Fin d) K) * ((diagHom d (ν a) * (B : GL (Fin d) K))⁻¹ *
            ((B : GL (Fin d) K) * glAut φ (diagHom d (ν a)))) := by group
        _ = _ := by rw [hcM]
    have h3 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) h1
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h3
    rw [h3, scalar_mul_eq_smul, Matrix.smul_mul]
  refine ⟨c⁻¹, fun i => ?_⟩
  have he := congrFun (congrFun hmat i) (σ i)
  rw [coe_glAut, coe_diagHom, Matrix.diagonal_map (map_zero φ), Matrix.mul_diagonal,
    Matrix.smul_mul, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul] at he
  have he' : φ (ν a (σ i) : K) = (c : K) * (ν a i : K) := by
    have h4 := hσ i
    have h5 : ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i (σ i) *
        (φ (ν a (σ i) : K) - (c : K) * (ν a i : K)) = 0 := by
      rw [mul_sub, he]
      ring
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 h4
    · exact sub_eq_zero.mp h6
  rw [hφbar] at he'
  have hinv : (ν a (σ i) : K) ^ 2 ^ n * (ν a (σ i) : K) = 1 := by
    rw [← pow_succ]
    exact hnorm a (σ i)
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hν0 : (ν a i : K) ≠ 0 := (ν a i).ne_zero
  field_simp
  calc (ν a (σ i) : K) * (ν a i : K) * (c : K) =
      (ν a (σ i) : K) * ((c : K) * (ν a i : K)) := by ring
    _ = (ν a (σ i) : K) * (ν a (σ i) : K) ^ 2 ^ n := by rw [he']
    _ = 1 := by rw [mul_comm]; exact hinv

end Outer

section Main

variable [Finite K]

include h in
theorem endNode_codimTwo (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 6 ≤ d)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hdiag : ∀ a ∈ Ab, ∃ (τ : Fin d → Kˣ) (hτ : diagHom d τ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
        a = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hτ⟩)
    (hcard : p ^ (d - 3) ≤ Nat.card Ab)
    (hU : ∃ U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d))), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      Ab ≤ Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d))))) :
    ∃ a ∈ Ab, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ Ab, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  classical
  have hp2 := ne_two_of_dvd h hpq
  have hpK := dvd_card_sub_one' h hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun h' => by omega
  set k₀ : Fin d := ⟨0, by omega⟩ with hk₀
  obtain ⟨ν, hνinj, hν0, hνp, hνN⟩ := exists_ratio h hK hp hpq (by omega) hdq hAb hdiag k₀
  by_cases hE : ∃ s t : Fin d, s ≠ t ∧ ∀ a : Ab, ν a s = ν a t
  · obtain ⟨s, t, hst, heq⟩ := hE
    exact endNode_of_eq h hK hp hpq hd hAb hdiag hcard hst (ν₀ := fun a => ν a)
      fun a => ⟨hνN a, heq a⟩
  push Not at hE
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  by_cases hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range = ⊥
  · obtain ⟨σ, hσ⟩ := exists_sigma_of_outer h hK (by omega) hq hpq hνp hνN hU1 hU2 hAU hUI
    have hcardY : Nat.card ν.range = Nat.card Ab := Nat.card_range_of_injective hνinj
    obtain ⟨-, hnode⟩ := outer_comb (Y := ν.range) (σ := σ) hp hp2 hpK hd (k₀ := k₀)
      (by rintro _ ⟨a, rfl⟩; exact hν0 a) (by rintro _ ⟨a, rfl⟩ k; exact hνp a k)
      (hcardY ▸ hcard)
      (fun i j hij => by
        obtain ⟨a, ha⟩ := hE i j hij
        exact ⟨ν a, ⟨a, rfl⟩, ha⟩)
      (by rintro _ ⟨a, rfl⟩; exact hσ a)
    exact endNode_of_ratio h hK (by omega) (Or.inr hd) hνinj hνN hnode
  · exfalso
    obtain ⟨s, t, hst, heq⟩ := exists_eq_of_inn h hK (by omega) hdq hpq hνp hνN hU2 hAU hUI
    obtain ⟨a, ha⟩ := hE s t hst
    exact ha (heq a)

end Main

end TableBUDT

end CFSG.StandardType
