module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.RankOne
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1Index

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.AGLEmbedding

theorem fixedFreeFive_psl2GF {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 2 ≤ n) :
    FixedFreeFive p (PSL2GF p n) := by
  have hp2 : p ≠ 2 := by omega
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have h25 : 25 ≤ p ^ n := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ p ^ n := Nat.pow_le_pow_left hp5 n
  obtain ⟨T⟩ := Sylow.nonempty (p := p) (G := PSL2GF p n)
  obtain ⟨hTabel, hTcard⟩ := psl2GF_sylow p n hn1 T
  obtain ⟨ψ, hψinj, hψrange, hψconj⟩ :=
    exists_torus_param_of_mulEquiv_psl2GF (Y := PSL2GF p n) hp2 hn1
      (K := ⊤) Subgroup.topEquiv (T : Subgroup (PSL2GF p n)) le_top hTcard
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField p n)ˣ)
  obtain ⟨c, -, hc⟩ := hψconj μ
  have hμne : ∀ k : ℕ, 0 < k → k < 5 → (μ : GaloisField p n) ^ (2 * k) ≠ 1 := by
    intro k hk0 hk5 h
    have h' : μ ^ (2 * k) = 1 := Units.ext h
    have hdvd : orderOf μ ∣ 2 * k := orderOf_dvd_iff_pow_eq_one.mpr h'
    have hpos : 0 < 2 * k := by omega
    have hle : orderOf μ ≤ 2 * k := Nat.le_of_dvd hpos hdvd
    have hlt : 2 * k < orderOf μ := by
      rw [hμ, Nat.card_units, GaloisField.card p n hn0]
      omega
    omega
  have hpow : ∀ k : ℕ, ∀ a : Multiplicative (GaloisField p n),
      c ^ k * ψ a * (c ^ k)⁻¹ =
        ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ (2 * k) *
          Multiplicative.toAdd a)) := by
    intro k
    induction k with
    | zero =>
        intro a
        simp
    | succ k ih =>
        intro a
        have hstep : c ^ (k + 1) * ψ a * (c ^ (k + 1))⁻¹ =
            c * (c ^ k * ψ a * (c ^ k)⁻¹) * c⁻¹ := by
          rw [pow_succ']
          group
        rw [hstep, ih, hc, toAdd_ofAdd]
        have harg : (μ : GaloisField p n) ^ 2 *
            ((μ : GaloisField p n) ^ (2 * k) * Multiplicative.toAdd a) =
            (μ : GaloisField p n) ^ (2 * (k + 1)) * Multiplicative.toAdd a := by
          rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_two]
          ring
        rw [harg]
  have hcN : c ∈ Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) := by
    have hmap : (T : Subgroup (PSL2GF p n)).map (MulAut.conj c).toMonoidHom =
        (T : Subgroup (PSL2GF p n)) := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [← hψrange] at hx ⊢
        obtain ⟨a, rfl⟩ := hx
        refine ⟨Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a), ?_⟩
        simpa [MulAut.conj_apply] using (hc a).symm
      · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (MulAut.conj c) x ∈
          (T : Subgroup (PSL2GF p n)).map (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmap] at hx'
      simpa [MulAut.conj_apply] using hx'
    · intro hx
      have hx' : (MulAut.conj c) x ∈
          (T : Subgroup (PSL2GF p n)).map (MulAut.conj c).toMonoidHom := by
        rw [hmap]
        simpa [MulAut.conj_apply] using hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
      have hyx : y = x := (MulAut.conj c).injective hxy
      simpa [hyx] using hy
  refine ⟨(T : Subgroup (PSL2GF p n)), T.isPGroup', ?_, ?_, c, hcN, ?_⟩
  ·
    intro hbot
    rw [hbot, Subgroup.card_bot] at hTcard
    omega
  · intro a ha b hb
    simpa using hTabel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  · intro k hk0 hk5 s hs hfix
    rw [← hψrange] at hs
    obtain ⟨a, rfl⟩ := hs
    have hψeq : ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ (2 * k) *
        Multiplicative.toAdd a)) = ψ a := by
      rw [← hpow k a]
      exact hfix
    have hXa : (μ : GaloisField p n) ^ (2 * k) * Multiplicative.toAdd a =
        Multiplicative.toAdd a := by
      simpa using congrArg Multiplicative.toAdd (hψinj hψeq)
    have ha0 : Multiplicative.toAdd a = 0 := by
      by_contra h
      have hsub : (μ : GaloisField p n) ^ (2 * k) - 1 = 0 := by
        have hmul : ((μ : GaloisField p n) ^ (2 * k) - 1) * Multiplicative.toAdd a = 0 := by
          rw [sub_mul, one_mul, hXa, sub_self]
        exact (mul_eq_zero.mp hmul).resolve_right h
      exact hμne k hk0 hk5 (sub_eq_zero.mp hsub)
    have ha1 : a = 1 := by
      rw [← ofAdd_toAdd a, ha0]
      rfl
    rw [ha1, map_one]


section Transport

theorem isCoatom_normalizer_of_mulEquiv_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {K : Type} [Group K] [Finite K] (e : K ≃* PSL2GF p n) (T : Sylow p K) :
    IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K)) := by
  let U : Sylow p (PSL2GF p n) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hU : (U : Subgroup (PSL2GF p n)) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective T
  have h := psl2GF_borelCoatom p n hp2 hn U
  rw [hU, ← Subgroup.map_equiv_normalizer_eq (T : Subgroup K) e] at h
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) _).mp h

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (index_normalizer_of_equiv) in
theorem card_sylow_of_mulEquiv_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {K : Type} [Group K] [Finite K] (e : K ≃* PSL2GF p n) (T : Sylow p K) :
    Nat.card (Sylow p K) = Nat.card (T : Subgroup K) + 1 := by
  let U : Sylow p (PSL2GF p n) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcardT : Nat.card (T : Subgroup K) = p ^ n := by
    have h := (psl2GF_sylow p n hn U).2
    rwa [Sylow.coe_mapSurjective e.surjective T,
      Subgroup.card_map_of_injective e.injective] at h
  rw [Sylow.card_eq_index_normalizer T, hcardT]
  exact index_normalizer_of_equiv hp2 hn e T

theorem exists_eq_conj_of_mulEquiv_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {K : Type} [Group K] [Finite K] (e : K ≃* PSL2GF p n) (T : Sylow p K) (α : MulAut K)
    (hα : ∀ u ∈ (T : Subgroup K), α u = u) :
    ∃ u ∈ (T : Subgroup K), α = MulAut.conj u := by
  let U : Sylow p (PSL2GF p n) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hU : (U : Subgroup (PSL2GF p n)) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective T
  let β : MulAut (PSL2GF p n) := MulAut.congr e α
  have hβ : ∀ u ∈ (U : Subgroup (PSL2GF p n)), β u = u := by
    intro u hu
    rw [hU] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    simp [β, MulAut.congr_apply, hα v hv]
  obtain ⟨u, hu, hβu⟩ :=
    CFSG.AGLEmbedding.kFactL2UnipotentCentralizer p n hp2 hn U β hβ
  rw [hU] at hu
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  refine ⟨v, hv, ?_⟩
  ext x
  apply e.injective
  have h := DFunLike.congr_fun hβu (e x)
  simp only [β, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h
  simpa [MulAut.conj_apply] using h

end Transport

theorem good_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) {X : Type} [Group X]
    [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* PSL2GF p n) : Good p N := by
  refine good_of_rankOne hO hN ?_ ?_ ?_
  · intro T
    exact isCoatom_normalizer_of_mulEquiv_psl2GF hp2 hn e T
  · intro T
    exact card_sylow_of_mulEquiv_psl2GF hp2 hn e T
  · intro T α hα
    exact exists_eq_conj_of_mulEquiv_psl2GF hp2 hn e T α hα

theorem pElements_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) {X : Type}
    [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* PSL2GF p n) :
    (∀ x y : X, x ∈ N → y ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) →
      (orderOf y).Prime → orderOf y ≠ p → x * y = y * x →
      ∃ c ∈ CFSG.generalizedFitting X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧
        c ∉ N) ∧
    ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ CFSG.generalizedFitting X :=
  pElements_of_rankOne hO hN (fun T => isCoatom_normalizer_of_mulEquiv_psl2GF hp2 hn e T)
    (fun T => card_sylow_of_mulEquiv_psl2GF hp2 hn e T)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
