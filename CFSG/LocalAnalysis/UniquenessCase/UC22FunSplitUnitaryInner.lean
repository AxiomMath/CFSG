module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitBlockTrace
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTraceInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSmallInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open CFSG.ClassicalInvolution.Models.Transfer
open CFSG.LieType.Steinberg CFSG.LieType.Universal
open scoped MatrixGroups

private theorem exists_inner_normalizer_aut_of_trace_subfield
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (φ : SL(2, fixedSubfield K p f) →* Su K p f n)
    (hφ : Function.Injective φ)
    (htrace : ∀ A : SL(2, fixedSubfield K p f),
      (suMat (φ A)).trace =
        (((A : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
          fixedSubfield K p f) : K) + (n - 2 : ℕ))
    {g : Su K p f n} (hg : g ∈ normalizer (φ.range : Set (Su K p f n)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ φ.range, ∀ x ∈ φ.range, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  by_cases h3 : 3 < Nat.card (fixedSubfield K p f)
  ·
    let e : SL(2, fixedSubfield K p f) ≃* φ.range := MonoidHom.ofInjective hφ
    let act : MulAut φ.range := φ.range.normalizerMonoidHom ⟨g, hg⟩
    let α : MulAut (SL(2, fixedSubfield K p f)) := e.trans (act.trans e.symm)
    have hact_dvd : orderOf act ∣ orderOf g := by
      have h := orderOf_map_dvd φ.range.normalizerMonoidHom
        (⟨g, hg⟩ : normalizer (φ.range : Set (Su K p f n)))
      rw [Subgroup.orderOf_mk] at h
      simpa [act] using h
    have hact_odd : Odd (orderOf act) := Odd.of_dvd_nat hgo hact_dvd
    have hα_eq : α = (MulAut.congr e).symm act :=
      (MulAut.congr_symm_apply e act).symm
    have hα_order : orderOf α = orderOf act := by
      rw [hα_eq]
      exact MulEquiv.orderOf_eq ((MulAut.congr e).symm) act
    have hα_odd : Odd (orderOf α) := by
      rw [hα_order]
      exact hact_odd
    have hα_apply : ∀ x : SL(2, fixedSubfield K p f), e (α x) = act (e x) := by
      intro x
      simp [α]
    have hφ_alpha : ∀ x : SL(2, fixedSubfield K p f),
        φ (α x) = g * φ x * g⁻¹ := by
      intro x
      have h := congrArg Subtype.val (hα_apply x)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      have h1 : ((e (α x) : φ.range) : Su K p f n) = φ (α x) :=
        MonoidHom.ofInjective_apply hφ
      have h2 : ((e x : φ.range) : Su K p f n) = φ x :=
        MonoidHom.ofInjective_apply hφ
      rw [h1, h2] at h
      exact h
    have hconj_trace : ∀ x : SL(2, fixedSubfield K p f),
        (suMat (g * φ x * g⁻¹)).trace = (suMat (φ x)).trace := by
      intro x
      let M : (Matrix (Fin n) (Fin n) K)ˣ :=
        ⟨suMat g, suMat g⁻¹, suMat_mul_suMat_inv g, suMat_inv_mul_suMat g⟩
      calc
        (suMat (g * φ x * g⁻¹)).trace
            = (suMat g * suMat (φ x) * suMat g⁻¹).trace := by
                rw [suMat_mul, suMat_mul]
        _ = (suMat (φ x)).trace := Matrix.trace_units_conj M (suMat (φ x))
    have hα_trace : ∀ x : SL(2, fixedSubfield K p f),
        ((α x : SL(2, fixedSubfield K p f)) :
            Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace =
          ((x : SL(2, fixedSubfield K p f)) :
            Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace := by
      intro x
      have h1 := htrace (α x)
      have h2 := htrace x
      have h3 : (((α x : SL(2, fixedSubfield K p f)) :
            Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
              fixedSubfield K p f) + ((n - 2 : ℕ) : K) =
          (((x : SL(2, fixedSubfield K p f)) :
            Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
              fixedSubfield K p f) + ((n - 2 : ℕ) : K) := by
        calc
          ((((α x : SL(2, fixedSubfield K p f)) :
              Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
                fixedSubfield K p f) : K) + ((n - 2 : ℕ) : K)
              = (suMat (φ (α x))).trace := h1.symm
          _ = (suMat (g * φ x * g⁻¹)).trace := by rw [hφ_alpha x]
          _ = (suMat (φ x)).trace := hconj_trace x
          _ = ((((x : SL(2, fixedSubfield K p f)) :
                Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
                  fixedSubfield K p f) : K) + ((n - 2 : ℕ) : K) := h2
      exact (fixedSubfield K p f).subtype.injective (add_right_cancel h3)
    obtain ⟨r, hr⟩ :=
      mem_range_conj_of_odd_of_trace (odd_natCard_fixedSubfield hK hp2) h3 α hα_odd
        hα_trace
    refine ⟨φ r, ⟨r, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    calc
      g * φ x * g⁻¹ = φ (α x) := (hφ_alpha x).symm
      _ = φ ((MulAut.conj r) x) := by rw [hr]
      _ = φ r * φ x * (φ r)⁻¹ := by
            simp only [MulAut.conj_apply, map_mul, map_inv]
  ·
    have hF0card : Nat.card (fixedSubfield K p f) = p ^ f := card_fixedSubfield hK
    have hF0odd : Odd (Nat.card (fixedSubfield K p f)) := odd_natCard_fixedSubfield hK hp2
    have hcard3 : Nat.card (fixedSubfield K p f) = 3 := by
      have h1 : 1 < Nat.card (fixedSubfield K p f) := Finite.one_lt_card
      obtain ⟨k, hk⟩ := hF0odd
      omega
    obtain ⟨y, hy⟩ := exists_inner_normalizer_aut_of_card_three hcard3 φ hφ hg hgo
    refine ⟨φ y, ⟨y, rfl⟩, ?_⟩
    intro x hx
    rcases hx with ⟨z, -, rfl⟩
    exact hy z

private theorem exists_inner_normalizer_aut_of_trace_rootSU2
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    {g : Su K p f n}
    (hg : g ∈ normalizer (rootSU2 K p f hn : Set (Su K p f n)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ rootSU2 K p f hn,
      ∀ x ∈ rootSU2 K p f hn, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  obtain ⟨e0, he0⟩ := exists_su2Equiv (K := K) (p := p) (f := f) hK
  let φ : SL(2, fixedSubfield K p f) →* Su K p f n :=
    (CFSG.ClassicalInvolution.Phan.blockEmb K p f n 2 0 (by omega)).comp e0.toMonoidHom
  have hφ : Function.Injective φ :=
    (CFSG.ClassicalInvolution.Phan.blockEmb_injective (by omega)).comp e0.injective
  have hφrange : φ.range = rootSU2 K p f hn := by
    rw [show φ = (CFSG.ClassicalInvolution.Phan.blockEmb K p f n 2 0 (by omega)).comp
        e0.toMonoidHom from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e0.surjective, Subgroup.map_top]
    rfl
  have htrace : ∀ A : SL(2, fixedSubfield K p f),
      (suMat (φ A)).trace =
        (((A : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
          fixedSubfield K p f) : K) + (n - 2 : ℕ) := by
    intro A
    have hblock : suMat (φ A) =
        blockMat n 0 (suMat (e0 A)) := by
      rw [show φ A = CFSG.ClassicalInvolution.Phan.blockEmb K p f n 2 0 (by omega)
          (e0 A) from rfl]
      exact suMat_blockEmb (by omega) (e0 A)
    have he0A : (suMat (e0 A)).trace =
        (((A : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace :
          fixedSubfield K p f) : K) := by
      simpa [suMat] using he0 A
    rw [hblock, trace_blockMat (by omega) (suMat (e0 A)), he0A]
  obtain ⟨r, hr, hconj⟩ :=
    exists_inner_normalizer_aut_of_trace_subfield hK hp2 φ hφ htrace
      (by rwa [hφrange]) hgo
  exact ⟨r, hφrange ▸ hr, fun x hx => hconj x (hφrange.symm ▸ hx)⟩

private theorem exists_inner_normalizer_of_isLongRootSU2
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (hL : IsLongRootSU2 K p f hn L i)
    {g : Su K p f n} (hg : g ∈ normalizer (L : Set (Su K p f n)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ L, ∀ x ∈ L, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  obtain ⟨c, hLc, -⟩ := hL
  rw [hLc] at hg ⊢
  have hg' : c⁻¹ * g * c ∈
      normalizer (rootSU2 K p f hn : Set (Su K p f n)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change CFSG.ClassicalInvolution.Generic.conjSub (c⁻¹ * g * c)
      (rootSU2 K p f hn) = rootSU2 K p f hn
    have hconj : CFSG.ClassicalInvolution.Generic.conjSub g
        (CFSG.ClassicalInvolution.Generic.conjSub c (rootSU2 K p f hn)) =
        CFSG.ClassicalInvolution.Generic.conjSub c (rootSU2 K p f hn) := by
      simpa [CFSG.ClassicalInvolution.Generic.conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)
    rw [CFSG.ClassicalInvolution.Generic.conjSub_mul,
      CFSG.ClassicalInvolution.Generic.conjSub_mul, hconj,
      CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub]
  have hg'odd : Odd (orderOf (c⁻¹ * g * c)) := by
    have h : orderOf (c⁻¹ * g * c) = orderOf g := by
      rw [show c⁻¹ * g * c = (MulAut.conj c⁻¹) g by simp]
      exact MulEquiv.orderOf_eq (MulAut.conj c⁻¹) g
    rwa [h]
  obtain ⟨r0, hr0mem, hr0conj⟩ :=
    exists_inner_normalizer_aut_of_trace_rootSU2 hK hp2 hn hg' hg'odd
  refine ⟨c * r0 * c⁻¹, ?_, ?_⟩
  · exact ⟨r0, hr0mem, rfl⟩
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    calc
      g * (c * y * c⁻¹) * g⁻¹ =
          c * ((c⁻¹ * g * c) * y * (c⁻¹ * g * c)⁻¹) * c⁻¹ := by group
      _ = c * (r0 * y * r0⁻¹) * c⁻¹ := by rw [hr0conj y hy]
      _ = (c * r0 * c⁻¹) * (c * y * c⁻¹) * (c * r0 * c⁻¹)⁻¹ := by group

theorem odd_normalizer_inner_fundamental_psu_model
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e)
    (R : Subgroup (modelUniv .PSU n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p e Fact.out).D)
    (g : (modelUniv .PSU n p e Fact.out).K)
    (hg : g ∈ normalizer (R : Set (modelUniv .PSU n p e Fact.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  have hf : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := by
    have := hadm.2.2.1
    omega
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hEqFund : (R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p e Fact.out).D) =
      (R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
        (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e Fact.out).D) := rfl
  have hRgeneric : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
      (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e Fact.out).D := by
    rw [← hEqFund]
    exact hR
  let R' : Subgroup (Su (GaloisField p (2 * e)) p e n) :=
    Subgroup.map φ.toMonoidHom R
  have hR' : R' ∈ longRootSetU (K := GaloisField p (2 * e)) (p := p) (f := e) hn := by
    have h := (hφ R).mp hRgeneric
    simpa [R'] using h
  obtain ⟨i, hi⟩ := hR'
  let gG : (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e Fact.out).K := g
  have hg' : φ gG ∈ normalizer (R' : Set (Su (GaloisField p (2 * e)) p e n)) := by
    simpa [R', gG] using map_mem_normalizer φ.toMonoidHom hg
  have hgo' : Odd (orderOf (φ gG)) := by
    rw [MulEquiv.orderOf_eq φ gG]
    exact hgo
  obtain ⟨r', hr'mem, hr'conj⟩ :=
    exists_inner_normalizer_of_isLongRootSU2 hK hp2 hn hi hg' hgo'
  rcases hr'mem with ⟨r, hrR, hrEq⟩
  let rM : (modelUniv .PSU n p e Fact.out).K := r
  refine ⟨rM, ?_, ?_⟩
  · exact hrR
  · intro x hx
    let xG : (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e Fact.out).K := x
    let rG : (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e Fact.out).K := r
    have hx' : φ xG ∈ R' := ⟨xG, hx, rfl⟩
    have h := hr'conj (φ xG) hx'
    apply φ.injective
    change φ.toMonoidHom (gG * xG * gG⁻¹) = φ.toMonoidHom (rG * xG * rG⁻¹)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rw [← hrEq] at h
    simpa [rG] using h
end CFSG.LocalAnalysis.UniquenessCase.UC22
