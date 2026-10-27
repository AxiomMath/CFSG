module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInnTorus
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public section

namespace CFSG.StandardType

namespace TableBUI

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] [Finite K] {d n p : ℕ}

omit [Finite K] in
theorem norm_eq_one_of_diagHom_mem (h : UnitaryFieldData 2 n K) {β : Fin d → Kˣ}
    (hβ : diagHom d β ∈ primeFormUnitary h (idGram K d)) (k : Fin d) :
    ((β k : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
  have h1 := congrFun (congrFun (mem_primeFormUnitary.mp hβ) k) k
  rw [idGram, Units.val_one, Matrix.mul_one, coe_diagHom, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    Matrix.one_apply_eq, UnitaryFieldData.bar_apply] at h1
  rw [pow_succ]
  exact h1

theorem exists_diag_of_commute (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (hp : p.Prime)
    (hpd : ¬ p ∣ d)
    {E₀ : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    {P : GL (Fin d) K}
    (hP : P ∈ primeFormUnitary (TableBU.unitaryFieldData_of_card hK hn) (idGram K d))
    {W : Subgroup (Fin d → Kˣ)} (hW : ∀ σ ∈ W, (∀ k, σ k ^ p = 1) ∧ ∏ k, σ k = 1)
    (hWx : ∀ σ ∈ W, ∃ x : ↥(unitarySU 2 n K d),
      (TableBUE.conjSU (TableBU.unitaryFieldData_of_card hK hn) P hP x : GL (Fin d) K) =
        diagHom d σ ∧ MulAut.conj (projU n d K x) ∈ E₀)
    (hsep : ∀ k l : Fin d, k ≠ l → ∃ σ ∈ W, σ k ≠ σ l)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hfc : ∀ e ∈ E₀, f * e = e * f) (hfp : f ^ p = 1) :
    ∃ β : Fin d → Kˣ,
      diagHom d β ∈ primeFormUnitary (TableBU.unitaryFieldData_of_card hK hn) (idGram K d) ∧
      IsSemilin (frameMk (TableBU.unitaryFieldData_of_card hK hn) P hP) f (diagHom d β)
        (fieldFactorU (TableBU.unitaryFieldData_of_card hK hn) hd hq f) := by
  classical
  set h := TableBU.unitaryFieldData_of_card hK hn with hh
  have := Fact.mk hp
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hcinj := mulAut_conj_injective (TableBUE.center_proj_eq_bot hK hd hdq)
  obtain ⟨B, hB, hsl⟩ := exists_isSemilin h hd hq f
  set φ := fieldFactorU h hd hq f with hφ
  have hφp : φ ^ p = 1 := by rw [hφ, ← map_pow, hfp, map_one]
  have hsl' := hsl.frame h P hP
  set B' := P⁻¹ * B * glAut φ P with hB'
  have hB'u : B' ∈ primeFormUnitary h (idGram K d) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) hB)
      (glAut_mem_primeFormUnitary h (isPrimeFormGram_one (K := K) (n := d)) φ hP)
  have hcomm : ∀ σ ∈ W, B' * diagHom d σ = diagHom d σ * B' := by
    intro σ hσ
    obtain ⟨x, hx, hxE⟩ := hWx σ hσ
    set t : ↥(unitarySU 2 n K d) := TableBUE.conjSU h P hP x with ht_def
    have ht : frameMk h P hP t = projU n d K x := by
      rw [frameMk_apply, ht_def, MulEquiv.symm_apply_apply]
    have hfix : f (projU n d K x) = projU n d K x := by
      apply hcinj
      have h1 := hfc _ hxE
      have h2 : MulAut.conj (f (projU n d K x)) = f * MulAut.conj (projU n d K x) * f⁻¹ := by
        ext y
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
          MulEquiv.apply_symm_apply]
      rw [h2, h1, mul_inv_cancel_right]
    set v : ↥(unitarySU 2 n K d) := ⟨B' * glAut φ (t : GL (Fin d) K) * B'⁻¹,
      semilin_mem h hB'u φ t⟩ with hv
    have hfv := hsl' t v rfl
    rw [ht, hfix, ← ht] at hfv
    obtain ⟨c, hc⟩ := exists_scalar_of_frameMk_eq h P hP hfv
    have hvσ : (v : GL (Fin d) K) = B' * diagHom d σ * B'⁻¹ := by
      change B' * glAut φ (t : GL (Fin d) K) * B'⁻¹ = _
      rw [show (t : GL (Fin d) K) = diagHom d σ from hx,
        glAut_diagHom_of_pow hp hφp (hW σ hσ).1]
    have htσ : (t : GL (Fin d) K) = diagHom d σ := hx
    have hcd : c ^ d = 1 := by
      have hdetv := ((mem_unitarySU_iff h).mp v.2).1
      have hdett := ((mem_unitarySU_iff h).mp t.2).1
      rw [hc, Units.val_mul, Matrix.det_mul, det_coe_scalar, hdett, mul_one] at hdetv
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdetv, Units.val_one])
    have hcp : c ^ p = 1 := by
      have hσp : (diagHom d σ) ^ p = 1 := by
        rw [← map_pow]
        have : σ ^ p = 1 := funext fun k => (hW σ hσ).1 k
        rw [this, map_one]
      have h1 : (v : GL (Fin d) K) ^ p = 1 := by
        rw [hvσ, conj_pow, hσp, mul_one, mul_inv_cancel]
      have hcomm' : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) c) (t : GL (Fin d) K) :=
        TypeA.PGLTor.commute_scalar c _
      rw [hc, hcomm'.mul_pow, htσ, hσp, mul_one, ← map_pow] at h1
      exact TypeA.PGLTor.scalar_injective (h1.trans (map_one _).symm)
    have hc1 : c = 1 := by
      have hcop : Nat.gcd d p = 1 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
      have h1 := pow_gcd_eq_one.mpr ⟨hcd, hcp⟩
      rwa [hcop, pow_one] at h1
    rw [hc1, map_one, one_mul, hvσ, htσ] at hc
    calc B' * diagHom d σ = B' * diagHom d σ * B'⁻¹ * B' := by group
      _ = diagHom d σ * B' := by rw [hc]
  obtain ⟨β, hβ⟩ := TableBUM.exists_diagHom_of_commute (W := (W : Set (Fin d → Kˣ))) hsep
    fun σ hσ => hcomm σ hσ
  exact ⟨β, hβ ▸ hB'u, hβ ▸ hsl'⟩

theorem prod_eq_of_semilin (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {P : GL (Fin d) K}
    (hP : P ∈ primeFormUnitary (TableBU.unitaryFieldData_of_card hK hn) (idGram K d))
    {β : Fin d → Kˣ}
    (hβu : diagHom d β ∈ primeFormUnitary (TableBU.unitaryFieldData_of_card hK hn) (idGram K d))
    {φ : K ≃+* K} (hφp : φ ^ p = 1)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} (hfp : f ^ p = 1)
    (hsl : IsSemilin (frameMk (TableBU.unitaryFieldData_of_card hK hn) P hP) f (diagHom d β) φ)
    (i j : Fin d) :
    ∏ l ∈ Finset.range p, Units.map ((φ ^ l : K ≃+* K) : K →* K) (β i) =
      ∏ l ∈ Finset.range p, Units.map ((φ ^ l : K ≃+* K) : K →* K) (β j) := by
  set h := TableBU.unitaryFieldData_of_card hK hn with hh
  have hpow := hsl.pow h hβu p
  have hNu := semilinNorm_mem h hβu φ p
  rw [hfp, hφp] at hpow
  rw [semilinNorm_diagHom] at hpow hNu
  obtain ⟨c, hc⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq P hP hNu hpow
  have hent : ∀ k, ∏ l ∈ Finset.range p, Units.map ((φ ^ l : K ≃+* K) : K →* K) (β k) = c := by
    intro k
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K =>
      (g : Matrix (Fin d) (Fin d) K)) hc) k) k
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, coe_diagHom] at h1
    exact Units.ext h1.symm
  rw [hent i, hent j]

@[expose] def fixerSub {R : Type*} [Group R] (m : R) : Subgroup (MulAut R) where
  carrier := {α | α m = m}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    have ha' : a m = m := ha
    have hb' : b m = m := hb
    change (a * b) m = m
    rw [MulAut.mul_apply, hb', ha']
  inv_mem' {a} ha := by
    have ha' : a m = m := ha
    change a⁻¹ m = m
    rw [MulAut.inv_apply]
    conv_lhs => rw [← ha']
    exact a.symm_apply_apply m

theorem ggBstarBoundInnR_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGBstarBoundInnR p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  intro Eb Eh hEbI hEb hr h3 hV hle hEh hcard
  set h := TableBU.unitaryFieldData_of_card hK hn with hh
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun ⟨h1, h2⟩ => hdq (by rw [h1, h2])
  have hd1 : 1 ≤ d := by omega
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : CharP K 2 := h.charP
  have hEbD : Eb ≤ inndiagU h hd1 := fun e he => congr_mem_primeFormD h hd1 hK (hEbI he)
  set E₀ := Eh ⊓ inndiagU h hd1 with hE₀
  have hE₀ab : IsElemAbelian p E₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hEh a.2.1 b.2.1)⟩⟩,
      fun a ha => hEh.2 a ha.1⟩
  have hEhE₀ := card_le_mul_card_inf_inndiagU h hd hq hp hEh
  obtain ⟨P, hP, W, hWcard, hWprop, hWx, hWe⟩ :=
    exists_frame_torus hK hn hd hdq hp hpq hpd hE₀ab inf_le_right
  have hWle : Nat.card W ≤ p ^ (d - 1) := TableBUM.card_le_pow_sub_one hd1 W
    (fun σ hσ => (hWprop σ hσ).1) (fun σ hσ => (hWprop σ hσ).2)
  have hpd2 : p ^ d = p ^ 2 * p ^ (d - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hpd1 : p ^ d = p * p ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hEh_ge : p ^ d ≤ Nat.card Eh := by
    rw [hpd2]
    exact (Nat.mul_le_mul_left _ hr).trans hcard
  have hW_ge : p ^ (d - 1) ≤ Nat.card W := by
    have h1 : p * p ^ (d - 1) ≤ p * Nat.card W := by
      rw [← hpd1, hWcard]
      exact hEh_ge.trans hEhE₀
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hlt : p ^ (d - 1) < p ^ d := by
    rw [hpd1]
    have : 0 < p ^ (d - 1) := pow_pos hp.pos _
    nlinarith [hp.two_le]
  have hsep : ∀ k l : Fin d, k ≠ l → ∃ σ ∈ W, σ k ≠ σ l := by
    intro k l hkl
    by_contra hcon
    push Not at hcon
    have h1 := TableBUM.card_le_pow_sub_two hd W (fun σ hσ => (hWprop σ hσ).1)
      (fun σ hσ => (hWprop σ hσ).2) hkl hcon
    have h2 : p ^ (d - 2) < p ^ (d - 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  obtain ⟨f, hfEh, hfD⟩ : ∃ f ∈ Eh, f ∉ inndiagU h hd1 := by
    by_contra hcon
    push Not at hcon
    have hEE : E₀ = Eh := inf_eq_left.mpr fun e he => hcon e he
    have h1 : Nat.card Eh ≤ p ^ (d - 1) := by
      rw [← hEE, ← hWcard]
      exact hWle
    omega
  have hfp : f ^ p = 1 := hEh.2 f hfEh
  have hfc : ∀ e ∈ E₀, f * e = e * f := fun e he => TableB.IsElemAbelian.comm hEh hfEh he.1
  obtain ⟨β, hβu, hsl⟩ := exists_diag_of_commute hK hn hd hdq hq hp hpd hP hWprop hWx hsep hfc hfp
  set φ := fieldFactorU h hd hq f with hφ
  have hφp : φ ^ p = 1 := by rw [hφ, ← map_pow, hfp, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hfD
    rw [← ker_fieldFactorU h hd hq]
    exact h1
  obtain ⟨V, hV1, hV2, hEbV⟩ := hV
  set Bb : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    Eb.comap MulAut.conj with hBb
  have hBV : Bb ≤ Subgroup.normalizer (V : Set (LargeEvenProj (LargeEvenSUGroup (Fin d) K
      (2 ^ n)))) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have := hEbV _ hb v hv
      rwa [MulAut.conj_apply] at this
    · intro hv
      have hb' : MulAut.conj b⁻¹ ∈ Eb := by
        rw [map_inv]
        exact Eb.inv_mem hb
      have := hEbV _ hb' _ hv
      rwa [MulAut.conj_apply, show b⁻¹ * (b * v * b⁻¹) * b⁻¹⁻¹ = v by group] at this
  obtain ⟨i, j, hij, hpair⟩ := SURepair.exists_framePair_of_twoSubgroup h
    (ker_frameMk_le_center h P hP) hV1 hV2 (fun v _ => frameMk_surjective h P hP v) hBV
  have hσnorm : ∀ σ ∈ W, ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
    intro σ hσ k
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, ← Units.val_pow_eq_pow_val, (hWprop σ hσ).1 k, Units.val_one, one_pow]
  have hEbσ : ∀ e ∈ Eb, ∃ σ ∈ W, ∃ x : ↥(unitarySU 2 n K d),
      (TableBUE.conjSU h P hP x : GL (Fin d) K) = diagHom d σ ∧
        e = MulAut.conj (projU n d K x) ∧ σ i = σ j := by
    intro e he
    obtain ⟨σ, hσ, x, hx, rfl⟩ := hWe e ⟨hle he, hEbD he⟩
    exact ⟨σ, hσ, x, hx, rfl, hpair _ he σ (frameActs_of_eq h P hP hx (hσnorm σ hσ))⟩
  have hN := prod_eq_of_semilin hK hn hd hdq hp hpq hP hβu hφp hfp hsl i j
  set γ : K := ((β j : Kˣ) : K) * ((β i : Kˣ) : K)⁻¹ with hγ
  have hγq : γ ^ (2 ^ n + 1) = 1 := by
    rw [hγ, mul_pow, inv_pow, norm_eq_one_of_diagHom_mem h hβu j,
      norm_eq_one_of_diagHom_mem h hβu i, inv_one, one_mul]
  have hγN : TableBUF.partNorm φ γ p = 1 := by
    have e1 : ∀ k, ∏ l ∈ Finset.range p, (φ ^ l) ((β k : Kˣ) : K) =
        ((∏ l ∈ Finset.range p, Units.map ((φ ^ l : K ≃+* K) : K →* K) (β k) : Kˣ) : K) := by
      intro k
      rw [Units.coe_prod]
      rfl
    rw [TableBUF.partNorm, hγ]
    simp only [map_mul, map_inv₀, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [e1 j, e1 i, hN]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  obtain ⟨c₀, hc₀q, hc₀φ⟩ := TableBUF.exists_hilbert90_unitary (q := 2 ^ n) hK
    ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow hp hφp hφ1 hγq hγN
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hc₀q
    exact zero_ne_one hc₀q
  set c : Kˣ := Units.mk0 c₀ hc₀0 with hc
  have hcq : c ^ (2 ^ n + 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc₀q, Units.val_one])
  have hcφ : Units.map (φ : K →* K) c = β j * (β i)⁻¹ * c := by
    apply Units.ext
    rw [Units.coe_map, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact hc₀φ
  have hMmem := TableBUM.monoSwap_mem (d := d) h hij hcq
  set M : ↥(unitarySU 2 n K d) := ⟨TableBUM.monoSwap i j c, hMmem⟩ with hM
  set m := frameMk h P hP M with hm
  have hm1 : m ≠ 1 := by
    intro h1
    have h2 : frameMk h P hP 1 = frameMk h P hP M := by rw [map_one, ← hm, h1]
    obtain ⟨a, ha⟩ := exists_scalar_of_frameMk_eq h P hP h2
    apply TableBUM.monoSwap_not_mem_scalars hij c
    refine ⟨a, ?_⟩
    have ha' : TableBUM.monoSwap i j c = Matrix.GeneralLinearGroup.scalar (Fin d) a * 1 := ha
    rw [ha', mul_one]
  have hm2 : m ^ 2 = 1 := by
    have hM2 : M ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq]
      exact TableBUM.monoSwap_mul_self hij c)
    rw [hm, ← map_pow, hM2, map_one]
  have hEbm : ∀ e ∈ Eb, e m = m := by
    intro e he
    obtain ⟨σ, hσ, x, hx, rfl, hσij⟩ := hEbσ e he
    have hacts := frameActs_of_eq h P hP hx (hσnorm σ hσ)
    rw [MulAut.conj_apply, hm]
    refine hacts.2 M M ?_
    change TableBUM.monoSwap i j c = diagHom d σ * TableBUM.monoSwap i j c * (diagHom d σ)⁻¹
    rw [TableBUM.commute_monoSwap hσij c, mul_inv_cancel_right]
  have hfm : f m = m := by
    rw [hm]
    refine hsl M M ?_
    change TableBUM.monoSwap i j c =
      diagHom d β * glAut φ (TableBUM.monoSwap i j c) * (diagHom d β)⁻¹
    rw [TableBUM.diagHom_conj_glAut_monoSwap hij φ β hcφ]
  have hEbF : Eb ≤ fixerSub m := fun e he => hEbm e he
  have hfF : f ∈ fixerSub m := hfm
  have hE'F : Eb ⊔ Subgroup.zpowers f ≤ fixerSub m :=
    sup_le hEbF ((Subgroup.zpowers_le).mpr hfF)
  refine ⟨Eb ⊔ Subgroup.zpowers f, lt_of_le_of_ne le_sup_left fun he => ?_,
    sup_le hle ((Subgroup.zpowers_le).mpr hfEh), Subgroup.zpowers m, ?_,
    isPGroup_zpowers_of_pow Nat.prime_two (k := 1) (by rw [pow_one]; exact hm2), ?_⟩
  · have h1 : f ∈ Eb ⊔ Subgroup.zpowers f :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
    rw [← he] at h1
    exact hfD (hEbD h1)
  · intro h1
    apply hm1
    have h2 := Subgroup.mem_zpowers m
    rw [h1, Subgroup.mem_bot] at h2
    exact h2
  · intro α hα v hv
    have hαF : α m = m := hE'F hα
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [map_zpow, hαF]
    exact Subgroup.zpow_mem_zpowers m k

theorem ggBstarBoundInn_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGBstarBoundInn p (ggUnitaryTorusRank p d) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  exact ggBstarBoundInn_of_R hp (TableBUE.center_proj_eq_bot hK hd hdq)
    (ggBstarBoundInnR_unitary hK hn hd hdq hp hpq hpd)

end TableBUI

end CFSG.StandardType
