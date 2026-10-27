module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniHeld
import CFSG.LocalAnalysis.StandardType.GGCentralExtTwoSubgroup
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSU
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section UniSplitAux

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits

private theorem mem_primeFormUnitary_of_isHermIsometry {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    [Finite K] [CharP K 2] (hcard : Nat.card K = (2 ^ f) ^ 2) {g : GL (Fin n) K}
    (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  have hpres : ∀ u v, (unitaryForm 2 f hcard n).β
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ u) ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (unitaryForm 2 f hcard n).β u v := by
    intro u v
    simpa only [unitaryForm_β, unitaryInvolution_apply] using hg u v
  have hmap := (unitaryForm_preserves_iff hcard (g : Matrix (Fin n) (Fin n) K)).mp hpres
  have hbar : (g : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K 2 f) =
      (g : Matrix (Fin n) (Fin n) K).map h.bar := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply, h.bar_apply]
  simpa only [hbar] using hmap

private noncomputable def conjHomPSU {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n) :
    primeFormUnitary h (idGram K n) →* MulAut (PSUg n K (2 ^ f)) :=
  (MulAut.congr (InndiagSU.projEquiv h hn).symm).toMonoidHom.comp
    (primeFormConjHom h (idGram K n))

private theorem isHermIsometry_of_mem_primeFormUnitary {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    [Finite K] [CharP K 2] (hcard : Nat.card K = (2 ^ f) ^ 2) {g : GL (Fin n) K}
    (hg : g ∈ primeFormUnitary h (idGram K n)) :
    IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K) := by
  have hB := mem_primeFormUnitary.mp hg
  rw [idGram, Units.val_one, Matrix.mul_one] at hB
  have hmap : (g : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K 2 f) =
      (g : Matrix (Fin n) (Fin n) K).map h.bar := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply, h.bar_apply]
  rw [← hmap] at hB
  have hpres := (unitaryForm_preserves_iff hcard (g : Matrix (Fin n) (Fin n) K)).mpr hB
  intro u v
  simpa only [unitaryForm_β, unitaryInvolution_apply] using hpres u v

private theorem conjHomPSU_mk {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n))
    (y : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) :
    conjHomPSU h hn ⟨g, hg⟩ (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) y) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))
        ⟨g * (y : GL (Fin n) K) * g⁻¹,
          (le_of_eq (InndiagSU.largeEvenSUGroup_eq_gramSU (d := n) h).symm)
            (conj_mem_gramSU h (idGram K n) hg
              ((le_of_eq (InndiagSU.largeEvenSUGroup_eq_gramSU (d := n) h)) y.2))⟩ := by
  have hcast : (le_of_eq (InndiagSU.largeEvenSUGroup_eq_gramSU (d := n) h)) y.2 =
      (InndiagSU.largeEvenSUGroup_eq_gramSU (d := n) h) ▸ y.2 := rfl
  have he : InndiagSU.projEquiv (n := f) (d := n) h hn
      (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) y) =
      ((⟨y, (InndiagSU.largeEvenSUGroup_eq_gramSU (d := n) h) ▸ y.2⟩ :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    InndiagSU.projEquiv_mk h hn y
  show (InndiagSU.projEquiv h hn).symm (primeFormConjHom h (idGram K n) ⟨g, hg⟩
      ((InndiagSU.projEquiv h hn) (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) y))) = _
  rw [he, primeFormConjHom_mk, InndiagSU.projEquiv_symm_mk]
  congr 1

private theorem conjHomPSU_eq_of_isConjBy {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n))
    {a : MulAut (PSUg n K (2 ^ f))} (ha : IsConjBy g a) :
    conjHomPSU h hn ⟨g, hg⟩ = a := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K (2 ^ f))) x
  rw [conjHomPSU_mk]
  exact (ha y _ rfl).symm

private theorem ker_conjHomPSU_le_center {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    (hn3 : 3 ≤ n) :
    (conjHomPSU h hn).ker ≤ Subgroup.center (primeFormUnitary h (idGram K n)) := by
  intro A hA
  rw [Subgroup.mem_center_iff]
  intro B
  have hA1 : primeFormConjHom h (idGram K n) A = 1 := by
    apply MulEquiv.ext
    intro x
    have hpt := DFunLike.congr_fun hA ((InndiagSU.projEquiv h hn).symm x)
    show primeFormConjHom h (idGram K n) A x = x
    exact (InndiagSU.projEquiv h hn).symm.injective (by simpa [conjHomPSU, MonoidHom.comp_apply]
      using hpt)
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h (isPrimeFormGram_idGram (K := K) (n := n))
    hn3 (SemidirectProduct.mk A 1)).mp (by
      rw [primeFormPsi_apply, hA1, map_one, mul_one])
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (commute_scalar c (B : GL (Fin n) K)).eq

private theorem conjHomPSU_range_normal {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) [Finite K] [CharP K 2]
    (hn : 1 ≤ n) (hn3 : 3 ≤ n) (hqne : ¬(n = 3 ∧ 2 ^ f = 2))
    (hcard : Nat.card K = (2 ^ f) ^ 2) :
    (conjHomPSU h hn).range.Normal := by
  have hD : (primeFormD h (idGram K n)).Normal := by
    have hreal := unitary_prime_form_full_semilinear_realization h
      (C := (1 : GL (Fin n) K)) isPrimeFormGram_idGram hn3 hqne
    simpa only [idGram] using hreal.2.2.2.2.2.2.2.2.1
  have hrange : (conjHomPSU h hn).range =
      (primeFormD h (idGram K n)).map
        (MulAut.congr (InndiagSU.projEquiv h hn).symm).toMonoidHom := by
    rw [conjHomPSU, MonoidHom.range_comp]
    rfl
  rw [hrange]
  exact hD.map _ (MulAut.congr (InndiagSU.projEquiv h hn).symm).surjective

private theorem mem_range_conjHomPSU_of_mem_conjImage {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    [Finite K] [CharP K 2] (hn : 1 ≤ n) (hcard : Nat.card K = (2 ^ f) ^ 2)
    {a : MulAut (PSUg n K (2 ^ f))}
    (ha : a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)))
      (LargeEvenGUSet (Fin n) K (2 ^ f))) :
    a ∈ (conjHomPSU h hn).range := by
  obtain ⟨A, hA⟩ := InndiagSU.congr_mem_primeFormD h hn hcard ha
  refine ⟨A, ?_⟩
  apply MulEquiv.ext
  intro x
  show (InndiagSU.projEquiv h hn).symm
      (primeFormConjHom h (idGram K n) A ((InndiagSU.projEquiv h hn) x)) = a x
  rw [hA]
  have hcongr : (MulAut.congr (InndiagSU.projEquiv h hn) a)
      ((InndiagSU.projEquiv h hn) x) =
      (InndiagSU.projEquiv h hn) (a x) := by
    rw [show (MulAut.congr (InndiagSU.projEquiv h hn) a)
        ((InndiagSU.projEquiv h hn) x) =
        (InndiagSU.projEquiv h hn) (a ((InndiagSU.projEquiv h hn).symm
          ((InndiagSU.projEquiv h hn) x))) from rfl]
    rw [MulEquiv.symm_apply_apply]
  rw [hcongr, MulEquiv.symm_apply_apply]

private theorem mulAut_congr_comp_symm {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (φ : MulAut H) : MulAut.congr e (MulAut.congr e.symm φ) = φ := by
  apply MulEquiv.ext
  intro x
  show e (e.symm (φ (e (e.symm x)))) = φ x
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem primeFormConjHom_ker {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn3 : 3 ≤ n)
    {A : primeFormUnitary h (idGram K n)}
    (hA : primeFormConjHom h (idGram K n) A = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨-, c, hcn, hcA⟩ := (primeFormPsi_eq_one_iff h (isPrimeFormGram_idGram (K := K) (n := n))
    hn3 (SemidirectProduct.mk A 1)).mp (by rw [primeFormPsi_apply, hA, map_one, mul_one])
  exact ⟨c, hcn, hcA⟩

end UniSplitAux

section UniSplitProof

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits

theorem uni_split {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ} (hK : Nat.card K = q ^ 2)
    (hn : 4 ≤ n) (φ : K →+* K) (hφ : ∀ x, φ x = x ^ q)
    {Ā : Subgroup (MulAut (PSUg n K q))}
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q))
      (LargeEvenGUSet (Fin n) K q))
    {Ahat : Subgroup (GL (Fin n) K)} (hL : UniLift n q K Ā Ahat)
    {U : Subgroup (MulAut (PSUg n K q))} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hnorm : ∀ a ∈ Ā, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    (∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      ∀ g ∈ Ahat, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) ∨
    (∃ B : GL (Fin n) K, IsHermIsometry q (B : Matrix (Fin n) (Fin n) K) ∧
      ∀ g ∈ Ahat, ∃ c : Kˣ, c ^ (q + 1) = 1 ∧
        B * Matrix.GeneralLinearGroup.map φ g * B⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin n) c * g) := by
  obtain ⟨f, hf, hq⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  have hcard : Nat.card K = (2 ^ f) ^ 2 := hK
  have hd1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hqne : ¬(n = 3 ∧ 2 ^ f = 2) := by omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  have hAhatX : ∀ g ∈ Ahat, g ∈ primeFormUnitary h (idGram K n) :=
    fun g hg => mem_primeFormUnitary_of_isHermIsometry h hcard (hL.iso g hg)
  have hmemĀ : ∀ (g : primeFormUnitary h (idGram K n)),
      (g : GL (Fin n) K) ∈ Ahat → conjHomPSU h hd1 g ∈ Ā := by
    intro g hg
    obtain ⟨a, haĀ, ha⟩ := hL.induces (g : GL (Fin n) K) hg
    rwa [conjHomPSU_eq_of_isConjBy h hd1 g.2 ha]
  have hrange_normal : (conjHomPSU h hd1).range.Normal :=
    conjHomPSU_range_normal h hd1 hn3 hqne hcard
  have hĀrange : Ā ≤ (conjHomPSU h hd1).range :=
    fun a ha => mem_range_conjHomPSU_of_mem_conjImage h hd1 hcard (hĀI a ha)
  let X : Subgroup (GL (Fin n) K) := primeFormUnitary h (idGram K n)
  let Z : Subgroup X := (conjHomPSU h hd1).ker
  let R : Subgroup X := U.comap (conjHomPSU h hd1)
  let AhatX : Subgroup X := Ahat.subgroupOf X
  let N : Subgroup X := AhatX ⊔ R
  haveI : Finite X := inferInstance
  have hRnorm : ∀ n ∈ N, ∀ x ∈ R, n * x * n⁻¹ ∈ R := by
    have hAhatN : AhatX ≤ Subgroup.normalizer (R : Set X) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hgĀ : conjHomPSU h hd1 g ∈ Ā :=
          hmemĀ g (by simpa [AhatX, Subgroup.mem_subgroupOf] using hg)
        show conjHomPSU h hd1 (g * x * g⁻¹) ∈ U
        simpa only [map_mul, map_inv] using
          hnorm (conjHomPSU h hd1 g) hgĀ (conjHomPSU h hd1 x)
            (show conjHomPSU h hd1 x ∈ U from hx)
      · intro hx
        have hgĀ : conjHomPSU h hd1 g⁻¹ ∈ Ā :=
          hmemĀ g⁻¹ (by
            simpa [AhatX, Subgroup.mem_subgroupOf] using Subgroup.inv_mem _ hg)
        have h1 : conjHomPSU h hd1 (g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹) ∈ U := by
          simpa only [map_mul, map_inv] using
            hnorm (conjHomPSU h hd1 g⁻¹) hgĀ (conjHomPSU h hd1 (g * x * g⁻¹))
              (show conjHomPSU h hd1 (g * x * g⁻¹) ∈ U from hx)
        have e : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
        rw [e] at h1
        show conjHomPSU h hd1 x ∈ U
        exact h1
    have hNnorm : N ≤ Subgroup.normalizer (R : Set X) :=
      sup_le hAhatN Subgroup.le_normalizer
    intro n hn x hx
    have := hNnorm hn
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this x).mp hx
  have hcent : ∀ x ∈ R ⊓ Z, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_center_iff.mp (ker_conjHomPSU_le_center h hd1 hn3 hx.2) y).symm
  have h2 : ∀ y ∈ R, ∃ k : ℕ, y ^ (2 ^ k) ∈ Z := by
    intro y hy
    obtain ⟨k, hk⟩ := hU2 ⟨conjHomPSU h hd1 y, by simpa [R, Subgroup.mem_comap] using hy⟩
    refine ⟨k, ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val hk
  obtain ⟨P, hPR, hP2, hPN, hRlePZ⟩ :=
    exists_normal_two_subgroup_of_central_ext (N := N) (R := R) (U := Z)
      le_sup_right hRnorm hcent h2
  by_cases hPbot : P = ⊥
  ·
    have hRleZ : R ≤ Z := by
      intro x hx
      have := hRlePZ hx
      rwa [hPbot, bot_sup_eq] at this
    have hUdisj : U ⊓ (conjHomPSU h hd1).range = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨x, hx⟩ := hu.2
      have hxR : x ∈ R := by
        show conjHomPSU h hd1 x ∈ U
        rw [hx]; exact hu.1
      have hx1 : conjHomPSU h hd1 x = 1 := MonoidHom.mem_ker.mp (hRleZ hxR)
      rw [← hx, hx1]
      exact Subgroup.mem_bot.mpr rfl
    have hUne : ∃ y : U, y ≠ 1 := by
      by_contra h
      apply hU
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      exact h ⟨⟨x, hx⟩, fun hxy => hx1 (Subtype.ext_iff.mp hxy)⟩
    obtain ⟨y, hy1⟩ := hUne
    have h2dvd : 2 ∣ orderOf y := IsPGroup.dvd_orderOf hU2 hy1
    refine Or.inr ?_
    let u : MulAut (PSUg n K (2 ^ f)) := (y : MulAut _) ^ (orderOf y / 2)
    have huU : u ∈ U := U.pow_mem y.2 _
    have hu2 : u ^ 2 = 1 := by
      show ((y : MulAut (PSUg n K (2 ^ f))) ^ (orderOf y / 2)) ^ 2 = 1
      rw [← pow_mul, mul_comm, Nat.mul_div_cancel' h2dvd]
      simpa only [Subgroup.orderOf_coe] using pow_orderOf_eq_one (y : MulAut (PSUg n K (2 ^ f)))
    have hu1 : u ≠ 1 := by
      intro h1
      have h1' : (y : MulAut (PSUg n K (2 ^ f))) ^ (orderOf y / 2) = 1 := by
        rw [show u = (y : MulAut (PSUg n K (2 ^ f))) ^ (orderOf y / 2) from rfl] at h1
        exact h1
      have hdvd : orderOf (y : MulAut (PSUg n K (2 ^ f))) ∣ orderOf y / 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr h1'
      rw [Subgroup.orderOf_coe] at hdvd
      have hlt : orderOf y / 2 < orderOf y := by
        have hpos : 0 < orderOf y := orderOf_pos y
        omega
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.mpr hlt)
    have huOut : u ∉ (conjHomPSU h hd1).range := by
      intro hu
      have : u ∈ U ⊓ (conjHomPSU h hd1).range := ⟨huU, hu⟩
      rw [hUdisj] at this
      exact hu1 (Subgroup.mem_bot.mp this)
    let e := InndiagSU.projEquiv (n := f) (d := n) h hd1
    let u' : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      MulAut.congr e u
    have hu'2 : u' ^ 2 = 1 := by
      show ((MulAut.congr e) u) ^ 2 = 1
      rw [← map_pow, hu2, map_one]
    have hu'Out : u' ∉ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      intro hu'
      apply huOut
      obtain ⟨A, hA⟩ := hu'
      refine ⟨A, ?_⟩
      apply MulEquiv.ext
      intro x
      show conjHomPSU h hd1 A x = u x
      rw [show conjHomPSU h hd1 A =
          (MulAut.congr e.symm) (primeFormConjHom h (idGram K n) A) from rfl, hA]
      show e.symm (e (u (e.symm (e x)))) = u x
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    have hreal := unitary_prime_form_full_semilinear_realization h hC hn3 hqne
    obtain ⟨σ, hAdecomp, -⟩ := hreal.2.2.2.2.1 u'
    obtain ⟨A, hA'⟩ := hAdecomp
    have hσne : σ ≠ 1 := by
      intro hσ1
      apply hu'Out
      rw [hA', hσ1, map_one, mul_one]
      exact ⟨A, rfl⟩
    have hσ2 : σ * σ = 1 := by
      have hFF := hreal.2.2.2.2.2.1 A σ
      have h1 : primeFormFieldFactor h hC hn3 hqne u' = σ := by
        rw [hA', hFF]
      have h2' := congrArg (primeFormFieldFactor h hC hn3 hqne) hu'2
      rw [map_pow, map_one, h1] at h2'
      simpa [pow_two] using h2'
    have hσφ : σ = unitaryInvolution K 2 f := AutPSU.eq_sigma_of_mul_self_eq_one h hσ2 hσne
    have hunit : ∀ x : K, unitaryInvolution K 2 f x = φ x := by
      intro x
      rw [unitaryInvolution_apply]
      exact (hφ x).symm
    have hσφ' : (σ : K →+* K) = φ := by
      rw [hσφ]
      ext x
      exact hunit x
    refine ⟨(A : GL (Fin n) K), ?_, ?_⟩
    · exact isHermIsometry_of_mem_primeFormUnitary h hcard A.2
    · intro g hg
      let gX : X := ⟨g, hAhatX g hg⟩
      have hg' : (gX : GL (Fin n) K) = g := rfl
      have hcomm : conjHomPSU h hd1 gX ∈ Ā ∧ conjHomPSU h hd1 gX * u = u * conjHomPSU h hd1 gX := by
        refine ⟨hmemĀ gX (by simpa [gX] using hg), ?_⟩
        have hdisj : (conjHomPSU h hd1 gX * u) * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹ = 1 := by
          have hmemU : (conjHomPSU h hd1 gX * u) * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹ ∈ U :=
            U.mul_mem (hnorm _ (hmemĀ gX (by simpa [gX] using hg)) u huU) (U.inv_mem huU)
          have hmemR : (conjHomPSU h hd1 gX * u) * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹ ∈
              (conjHomPSU h hd1).range := by
            have haR : conjHomPSU h hd1 gX ∈ (conjHomPSU h hd1).range :=
              ⟨gX, rfl⟩
            have huaR : u * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹ ∈ (conjHomPSU h hd1).range :=
              hrange_normal.conj_mem _ (Subgroup.inv_mem _ haR) u
            have hprod : conjHomPSU h hd1 gX * (u * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹) ∈
                (conjHomPSU h hd1).range := Subgroup.mul_mem _ haR huaR
            rwa [show conjHomPSU h hd1 gX * (u * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹) =
              (conjHomPSU h hd1 gX * u) * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹ from by group] at hprod
          have hmem : (conjHomPSU h hd1 gX * u) * (conjHomPSU h hd1 gX)⁻¹ * u⁻¹ ∈
              U ⊓ (conjHomPSU h hd1).range := ⟨hmemU, hmemR⟩
          rw [hUdisj] at hmem
          exact Subgroup.mem_bot.mp hmem
        rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
        exact hdisj
      have hcomm' : primeFormConjHom h (idGram K n) gX * u' = u' * primeFormConjHom h (idGram K n) gX := by
        have hs : (MulAut.congr e) (conjHomPSU h hd1 gX) = primeFormConjHom h (idGram K n) gX := by
          rw [show conjHomPSU h hd1 gX =
              MulAut.congr e.symm (primeFormConjHom h (idGram K n) gX) from rfl,
            mulAut_congr_comp_symm]
        have := congrArg (MulAut.congr e) hcomm.2
        rwa [map_mul, map_mul, hs] at this
      have hXeq : primeFormConjHom h (idGram K n) (gX * A) =
          primeFormConjHom h (idGram K n) (A * primeFormFieldU h hC σ gX) := by
        have h1 : primeFormConjHom h (idGram K n) gX * primeFormConjHom h (idGram K n) A =
            primeFormConjHom h (idGram K n) A *
              (primeFormFieldHom h hC σ * primeFormConjHom h (idGram K n) gX *
                (primeFormFieldHom h hC σ)⁻¹) := by
          have := hcomm'
          rw [hA'] at this
          calc primeFormConjHom h (idGram K n) gX * primeFormConjHom h (idGram K n) A =
                primeFormConjHom h (idGram K n) gX *
                  (primeFormConjHom h (idGram K n) A * primeFormFieldHom h hC σ) *
                    (primeFormFieldHom h hC σ)⁻¹ := by group
            _ = (primeFormConjHom h (idGram K n) gX *
                  (primeFormConjHom h (idGram K n) A * primeFormFieldHom h hC σ)) *
                    (primeFormFieldHom h hC σ)⁻¹ := by group
            _ = ((primeFormConjHom h (idGram K n) A * primeFormFieldHom h hC σ) *
                  primeFormConjHom h (idGram K n) gX) * (primeFormFieldHom h hC σ)⁻¹ := by
                  rw [← this]
            _ = primeFormConjHom h (idGram K n) A *
                  (primeFormFieldHom h hC σ * primeFormConjHom h (idGram K n) gX *
                    (primeFormFieldHom h hC σ)⁻¹) := by group
        rw [primeFormField_conj_eq h hC σ gX] at h1
        rw [← map_mul, ← map_mul] at h1
        exact h1
      have hmemker : (gX * A) * (A * primeFormFieldU h hC σ gX)⁻¹ ∈
          (primeFormConjHom h (idGram K n)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hXeq, mul_inv_cancel]
      obtain ⟨c, hcnorm, hceq⟩ := primeFormConjHom_ker h hn3 hmemker
      refine ⟨c⁻¹, ?_, ?_⟩
      ·
        rw [inv_pow]
        rw [show (c : Kˣ) ^ (2 ^ f + 1) = 1 from by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow]
          exact hcnorm]
        rw [inv_one]
      ·
        have hgl : (primeFormFieldU h hC σ gX : GL (Fin n) K) =
            Matrix.GeneralLinearGroup.map φ (gX : GL (Fin n) K) := by
          rw [coe_primeFormFieldU, ← hσφ']
          rfl
        have hkey : (A : GL (Fin n) K) * primeFormFieldU h hC σ gX * (A : GL (Fin n) K)⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * (gX : GL (Fin n) K) := by
          have h1 : ((gX : GL (Fin n) K) * (A : GL (Fin n) K)) *
              ((A : GL (Fin n) K) * primeFormFieldU h hC σ gX)⁻¹ =
              Matrix.GeneralLinearGroup.scalar (Fin n) c := hceq
          have h2 : (Matrix.GeneralLinearGroup.scalar (Fin n) c)⁻¹ =
              Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ := by rw [map_inv]
          have hgroup : (A : GL (Fin n) K) * primeFormFieldU h hC σ gX * (A : GL (Fin n) K)⁻¹ =
              (((gX : GL (Fin n) K) * (A : GL (Fin n) K)) *
                ((A : GL (Fin n) K) * primeFormFieldU h hC σ gX)⁻¹)⁻¹ * (gX : GL (Fin n) K) := by
            group
          rw [hgroup, h1, h2]
        rw [hgl, hg'] at hkey
        exact hkey
  ·
    have hPne : P ≠ ⊥ := hPbot
    refine Or.inl ?_
    let G : Subgroup (GL (Fin n) K) := N.map X.subtype
    let T : Subgroup (GL (Fin n) K) := P.map X.subtype
    have hpoint : ∀ a ∈ N, ∀ x : X, x ∈ P ↔ a * x * a⁻¹ ∈ P := by
      intro a ha x
      refine ⟨fun hx => hPN a ha x hx, fun hx => ?_⟩
      have h1 := hPN a⁻¹ (N.inv_mem ha) (a * x * a⁻¹) hx
      rwa [show a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x from by group] at h1
    have hG : ∀ g ∈ G, IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K) := by
      intro g hg
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hg
      exact isHermIsometry_of_mem_primeFormUnitary h hcard x.2
    have hTG : T ≤ G := Subgroup.map_mono (le_trans hPR le_sup_right)
    have hT : T ≠ ⊥ := by
      intro hTbot
      apply hPne
      rw [eq_bot_iff]
      intro x hx
      have hxT : (x : GL (Fin n) K) ∈ T := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hTbot] at hxT
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxT))
    have hT2 : IsPGroup 2 T := hP2.map X.subtype
    obtain ⟨W, hWne, hWiso, hWstab⟩ := heldFlagGU hcard G T hG hTG hT hT2
    refine ⟨W, hWne, hWiso, ?_⟩
    intro g hg w hw
    let gX : X := ⟨g, hAhatX g hg⟩
    have hgN : gX ∈ N := Subgroup.mem_sup_left (by
      show gX ∈ AhatX
      change (gX : GL (Fin n) K) ∈ Ahat
      exact hg)
    have hgnorm : g ∈ Subgroup.normalizer (T : Set (GL (Fin n) K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨p, hpP, hpv⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_map.mpr ⟨gX * p * gX⁻¹, (hpoint gX hgN p).mp hpP, ?_⟩
        show ((gX * p * gX⁻¹ : X) : GL (Fin n) K) = g * y * g⁻¹
        rw [← hpv]
        rfl
      · intro hy
        obtain ⟨p, hpP, hpv⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_map.mpr ⟨gX⁻¹ * p * (gX⁻¹)⁻¹,
          (hpoint gX⁻¹ (N.inv_mem hgN) p).mp hpP, ?_⟩
        show ((gX⁻¹ * p * (gX⁻¹)⁻¹ : X) : GL (Fin n) K) = y
        change (gX⁻¹ : GL (Fin n) K) * (p : GL (Fin n) K) *
          ((gX⁻¹ : GL (Fin n) K))⁻¹ = y
        rw [show (p : GL (Fin n) K) = g * y * g⁻¹ from hpv]
        rw [show (gX : GL (Fin n) K) = g from rfl]
        group
    have hgG : g ∈ G := Subgroup.mem_map.mpr ⟨gX, hgN, rfl⟩
    exact hWstab g hgG hgnorm w hw

end UniSplitProof

end CFSG.StandardType.TablePThreeKG

end
