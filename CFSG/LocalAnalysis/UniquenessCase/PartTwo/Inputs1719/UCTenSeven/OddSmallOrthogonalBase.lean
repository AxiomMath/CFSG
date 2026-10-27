module

public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Module QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Orthogonal.Small

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

private lemma smallOrth_two_ne_zero (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 :=
  CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd

omit [Finite K] in
private lemma smallOrth_neg_one_ne_one_units (h2 : (2 : K) ≠ 0) : (-1 : Kˣ) ≠ 1 := by
  intro h
  apply h2
  have := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

omit [Finite K] in
private lemma smallOrth_mul_self_eq_one_of_det_eq_neg_one
    (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K W ≤ 2) {g : W ≃ₗ[K] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hdet : LinearEquiv.det g = -1) : g * g = 1 := by
  classical
  have : NeZero (2 : K) := ⟨h2⟩
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨l, hl, hlen, hprod⟩ :=
    TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq Q hQ' ⟨g, hg⟩
  have hdetl : LinearEquiv.det (l.prod : W ≃ₗ[K] W) = (-1 : Kˣ) ^ l.length :=
    TauCeti.QuadraticMap.det_list_prod_of_reflectionOrthogonal Q l hl
  have hg_eq : (l.prod : W ≃ₗ[K] W) = g := congrArg Subtype.val hprod
  rw [hg_eq, hdet] at hdetl
  have hlen3 : l.length = 0 ∨ l.length = 1 ∨ l.length = 2 := by omega
  rcases hlen3 with h0 | h1 | h2'
  · rw [h0, pow_zero] at hdetl
    exact absurd hdetl (smallOrth_neg_one_ne_one_units h2)
  · obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨v, hv, hrv⟩ := hl r (by simp)
    have hrr : (r * r : TauCeti.QuadraticMap.orthogonalGroup Q) = 1 := by
      rw [← hrv]
      exact TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q v
    rw [List.prod_singleton] at hprod
    have hr : (r : W ≃ₗ[K] W) = g := by
      simpa using congrArg Subtype.val hprod
    rw [← hr]
    exact congrArg Subtype.val hrr
  · rw [h2', neg_one_sq] at hdetl
    exact absurd hdetl (smallOrth_neg_one_ne_one_units h2)

theorem eq_one_of_mem_normalizer_sylow_of_finrank_le_two (hodd : Odd (Nat.card K))
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W ≤ 2)
    (T : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q))
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} (hg : Odd (orderOf g))
    (hgT : g ∈ normalizer
      ((T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q))) :
    g = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := smallOrth_two_ne_zero hodd
  have : NeZero (2 : K) := ⟨h2⟩
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun f : W ≃ₗ[K] W => (f : W → W))
      (fun f g h => LinearEquiv.ext (congrFun h))
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := Subtype.finite
  by_cases hsub : Subsingleton W
  · exact Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)
  · have : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
    have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
    have hrange : (QuadraticMap.orthogonalDet Q).range = rootsOfUnity 2 K :=
      TauCeti.QuadraticMap.range_orthogonalDet hQ'
    let f : TauCeti.QuadraticMap.orthogonalGroup Q →*
        (QuadraticMap.orthogonalDet Q).range :=
      (QuadraticMap.orthogonalDet Q).codRestrict _
        (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
      exact ⟨x, Subtype.ext hx⟩
    have hpow : ∀ x : (QuadraticMap.orthogonalDet Q).range, (x : Kˣ) ^ 2 = 1 := by
      intro x
      have hx : (x : Kˣ) ∈ rootsOfUnity 2 K := by
        rw [← hrange]
        exact x.2
      rwa [mem_rootsOfUnity] at hx
    have hgroup : IsPGroup 2 (QuadraticMap.orthogonalDet Q).range := by
      rw [isPGroup_iff_exists_pow_pow_eq_one]
      refine ⟨1, fun x => ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      norm_num
      exact hpow x
    have htopgroup : IsPGroup 2 (⊤ : Subgroup (QuadraticMap.orthogonalDet Q).range) :=
      hgroup.of_equiv Subgroup.topEquiv.symm
    let T' : Sylow 2 (QuadraticMap.orthogonalDet Q).range := Sylow.mapSurjective hf T
    have htop : (T' : Subgroup (QuadraticMap.orthogonalDet Q).range) = ⊤ := by
      exact (T'.is_maximal' (Q := ⊤) htopgroup le_top).symm
    have hneg : (-1 : Kˣ) ∈ (QuadraticMap.orthogonalDet Q).range := by
      rw [hrange, mem_rootsOfUnity]
      simp
    have hnegT : (⟨(-1 : Kˣ), hneg⟩ : (QuadraticMap.orthogonalDet Q).range) ∈
        (T' : Subgroup (QuadraticMap.orthogonalDet Q).range) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hnegtop : (⟨(-1 : Kˣ), hneg⟩ : (QuadraticMap.orthogonalDet Q).range) ∈
        (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map f := by
      rw [← Sylow.coe_mapSurjective hf T]
      exact hnegT
    obtain ⟨r, hrT, hfr⟩ := Subgroup.mem_map.mp hnegtop
    have hdetr : LinearEquiv.det (r : W ≃ₗ[K] W) = -1 := by
      have hval := congrArg Subtype.val hfr
      change QuadraticMap.orthogonalDet Q r = (-1 : Kˣ) at hval
      rw [QuadraticMap.orthogonalDet_apply] at hval
      exact hval
    have hsqg : (QuadraticMap.orthogonalDet Q g) ^ 2 = 1 := by
      have hmem : (QuadraticMap.orthogonalDet Q g) ∈ rootsOfUnity 2 K := by
        rw [← hrange]
        exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
      rwa [mem_rootsOfUnity] at hmem
    have hodd_det : Odd (orderOf (QuadraticMap.orthogonalDet Q g)) :=
      hg.of_dvd_nat (orderOf_map_dvd (QuadraticMap.orthogonalDet Q) g)
    have hdetg_unit : QuadraticMap.orthogonalDet Q g = 1 := by
      exact (pow_eq_one_iff_of_coprime (Odd.coprime_two_right hodd_det)).mp
        ⟨pow_orderOf_eq_one _, hsqg⟩
    have hdetg : LinearEquiv.det (g : W ≃ₗ[K] W) = 1 := by
      rw [← QuadraticMap.orthogonalDet_apply]
      exact hdetg_unit
    have hrr : (r : W ≃ₗ[K] W) * r = 1 :=
      smallOrth_mul_self_eq_one_of_det_eq_neg_one h2 hQ hdim r.2 hdetr
    have hdetrg : LinearEquiv.det (((r * g) : TauCeti.QuadraticMap.orthogonalGroup Q) :
        W ≃ₗ[K] W) = -1 := by
      rw [Subgroup.coe_mul, map_mul, hdetr, hdetg, neg_one_mul]
    set gl : W ≃ₗ[K] W := (g : W ≃ₗ[K] W) with hgl
    set rl : W ≃ₗ[K] W := (r : W ≃ₗ[K] W) with hrl
    have hrr' : rl * rl = 1 := by simpa [hrl] using hrr
    have hdetrg' : LinearEquiv.det (rl * gl) = -1 := by
      simpa [hrl, hgl, Subgroup.coe_mul] using hdetrg
    have hmem_rg : rl * gl ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [hrl, hgl]
      exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem r.2 g.2
    have hrg2 : rl * gl * rl = gl⁻¹ := by
      have h := smallOrth_mul_self_eq_one_of_det_eq_neg_one h2 hQ hdim hmem_rg hdetrg'
      have hassoc : (rl * gl * rl) * gl = 1 := by
        calc (rl * gl * rl) * gl = (rl * gl) * (rl * gl) := by group
          _ = 1 := h
      calc rl * gl * rl = ((rl * gl * rl) * gl) * gl⁻¹ := by group
        _ = 1 * gl⁻¹ := by rw [hassoc]
        _ = gl⁻¹ := one_mul _
    have hrg'_inv : rl * gl⁻¹ * rl = gl := by
      calc rl * gl⁻¹ * rl = rl * (rl * gl * rl) * rl := by rw [hrg2]
        _ = (rl * rl) * gl * (rl * rl) := by group
        _ = gl := by rw [hrr']; group
    have hprod : gl * rl * gl⁻¹ * rl = gl ^ 2 := by
      have e1 : gl * rl = rl * gl⁻¹ := by
        calc gl * rl = (rl * rl) * (gl * rl) := by rw [hrr']; group
          _ = rl * (rl * gl * rl) := by group
          _ = rl * gl⁻¹ := by rw [hrg2]
      have e2 : gl⁻¹ * rl = rl * gl := by
        calc gl⁻¹ * rl = (rl * rl) * (gl⁻¹ * rl) := by rw [hrr']; group
          _ = rl * (rl * gl⁻¹ * rl) := by group
          _ = rl * gl := by rw [hrg'_inv]
      calc gl * rl * gl⁻¹ * rl = (rl * gl⁻¹) * (rl * gl) := by
            rw [show gl * rl * gl⁻¹ * rl = (gl * rl) * (gl⁻¹ * rl) by group, e1, e2]
        _ = rl * (gl⁻¹ * rl) * gl := by group
        _ = rl * (rl * gl) * gl := by rw [e2]
        _ = (rl * rl) * (gl * gl) := by group
        _ = gl * gl := by rw [hrr', one_mul]
        _ = gl ^ 2 := by rw [pow_two]
    have hmemT : g ^ 2 ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      have h1 : g * r * g⁻¹ ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
        (Subgroup.mem_normalizer_iff.mp hgT r).mp hrT
      have h2' : r⁻¹ ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
        (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).inv_mem hrT
      have h3 := (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).mul_mem h1 h2'
      have h3' : g * r * g⁻¹ * r⁻¹ = g ^ 2 := by
        apply Subtype.ext
        change (g : W ≃ₗ[K] W) * (r : W ≃ₗ[K] W) * (g : W ≃ₗ[K] W)⁻¹ *
          (r : W ≃ₗ[K] W)⁻¹ = (g : W ≃ₗ[K] W) ^ 2
        rw [← hgl, ← hrl, inv_eq_of_mul_eq_one_right hrr']
        exact hprod
      rwa [h3'] at h3
    have hodd_g2 : Odd (orderOf (g ^ 2)) := hg.of_dvd_nat (orderOf_pow_dvd (x := g) 2)
    have hg2 : g ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := (T.isPGroup').exists_orderOf_dvd_pow ⟨g ^ 2, hmemT⟩
      rw [orderOf_mk] at hk
      have hcop : Nat.Coprime (orderOf (g ^ 2)) (2 ^ k) :=
        hodd_g2.coprime_two_right.pow_right k
      have h1 : orderOf (g ^ 2) = 1 := hcop.eq_one_of_dvd hk
      exact orderOf_eq_one_iff.mp h1
    have hdvd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    have hcop : Nat.Coprime (orderOf g) 2 := hg.coprime_two_right
    have h1 : orderOf g = 1 := hcop.eq_one_of_dvd hdvd2
    exact orderOf_eq_one_iff.mp h1

omit [Finite K] [FiniteDimensional K W] in
private lemma smallOrth_reflection_apply_eq_neg_smul (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K W}
    (u : W) [Invertible (Q u)] {y : W}
    (h : (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W) y = -y) :
    ∃ c : K, y = c • u := by
  have hformula := TauCeti.QuadraticMap.reflection_apply_eq_sub_div Q u y
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, hformula] at h
  set t : K := polar Q u y / Q u with ht
  have h2y : (2 : K) • y = t • u := by
    calc (2 : K) • y = y + y := two_smul K y
      _ = (y - t • u) + t • u + y := by abel
      _ = -y + t • u + y := by rw [h]
      _ = t • u := by abel
  refine ⟨(2 : K)⁻¹ * t, ?_⟩
  calc y = (2 : K)⁻¹ • ((2 : K) • y) := by
        rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = (2 : K)⁻¹ • (t • u) := by rw [h2y]
    _ = ((2 : K)⁻¹ * t) • u := by rw [smul_smul]

omit [Finite K] [FiniteDimensional K W] in
private lemma smallOrth_reflection_comm_orth_or_smul (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K W}
    {a b : W} [Invertible (Q a)] [Invertible (Q b)]
    (hcomm : TauCeti.QuadraticMap.reflectionOrthogonal Q a *
        TauCeti.QuadraticMap.reflectionOrthogonal Q b =
      TauCeti.QuadraticMap.reflectionOrthogonal Q b *
        TauCeti.QuadraticMap.reflectionOrthogonal Q a) :
    polar Q a b = 0 ∨ ∃ c : K, b = c • a := by
  have hQa : Q a ≠ 0 := (isUnit_of_invertible (Q a)).ne_zero
  have hQb : Q b ≠ 0 := (isUnit_of_invertible (Q b)).ne_zero
  have hQrab : Q ((TauCeti.QuadraticMap.reflectionOrthogonal Q a : W ≃ₗ[K] W) b) = Q b :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (TauCeti.QuadraticMap.reflectionOrthogonal Q a).2 b
  have : Invertible (Q ((TauCeti.QuadraticMap.reflectionOrthogonal Q a : W ≃ₗ[K] W) b)) :=
    invertibleOfNonzero (by rw [hQrab]; exact hQb)
  have hra : TauCeti.QuadraticMap.reflectionOrthogonal Q a *
      TauCeti.QuadraticMap.reflectionOrthogonal Q a = 1 :=
    TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q a
  have hconj := TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q
    (TauCeti.QuadraticMap.reflectionOrthogonal Q a) b
  have hcomm' : TauCeti.QuadraticMap.reflectionOrthogonal Q
      ((TauCeti.QuadraticMap.reflectionOrthogonal Q a : W ≃ₗ[K] W) b) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q b := by
    rw [← hconj]
    calc TauCeti.QuadraticMap.reflectionOrthogonal Q a *
          TauCeti.QuadraticMap.reflectionOrthogonal Q b *
          (TauCeti.QuadraticMap.reflectionOrthogonal Q a)⁻¹ =
        (TauCeti.QuadraticMap.reflectionOrthogonal Q b *
          TauCeti.QuadraticMap.reflectionOrthogonal Q a) *
          (TauCeti.QuadraticMap.reflectionOrthogonal Q a)⁻¹ := by rw [hcomm]
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q b := by group
  have happ : (TauCeti.QuadraticMap.reflectionOrthogonal Q
      ((TauCeti.QuadraticMap.reflectionOrthogonal Q a : W ≃ₗ[K] W) b) : W ≃ₗ[K] W) b = -b := by
    have := congrArg (fun e : TauCeti.QuadraticMap.orthogonalGroup Q =>
      (e : W ≃ₗ[K] W) b) hcomm'
    simpa [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.reflection_apply_self] using this
  obtain ⟨c, hc⟩ := smallOrth_reflection_apply_eq_neg_smul h2
    ((TauCeti.QuadraticMap.reflectionOrthogonal Q a : W ≃ₗ[K] W) b) happ
  by_cases hab : polar Q a b = 0
  · exact Or.inl hab
  · right
    set t : K := polar Q a b / Q a with ht
    have ht0 : t ≠ 0 := by
      rw [ht]
      exact div_ne_zero hab hQa
    have hra_apply : (TauCeti.QuadraticMap.reflectionOrthogonal Q a : W ≃ₗ[K] W) b =
        b - t • a := by
      rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
      rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
    have hb_eq : b = c • (b - t • a) := by rw [← hra_apply]; exact hc
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hQb
      rw [hb_eq, hc0, zero_smul]
      simp
    have hct : c * t ≠ 0 := mul_ne_zero hc0 ht0
    have hb_expand : b = c • b - (c * t) • a := by
      conv_lhs => rw [hb_eq]
      rw [smul_sub, smul_smul]
    have hlin : (c * t) • a = (c - 1) • b := by
      calc (c * t) • a = c • b - (c • b - (c * t) • a) := by abel
        _ = c • b - b := by rw [← hb_expand]
        _ = (c - 1) • b := by rw [sub_smul, one_smul]
    have hc1 : c - 1 ≠ 0 := by
      intro hc1
      have hzero : (c * t) • a = 0 := by rw [hlin, hc1, zero_smul]
      exact hct (smul_eq_zero.mp hzero |>.resolve_right (by
        intro ha
        exact hQa (by rw [ha, map_zero])))
    refine ⟨(c - 1)⁻¹ * (c * t), ?_⟩
    calc b = (c - 1)⁻¹ • ((c - 1) • b) := by
          rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
      _ = (c - 1)⁻¹ • ((c * t) • a) := by rw [← hlin]
      _ = ((c - 1)⁻¹ * (c * t)) • a := by rw [smul_smul]

omit [Finite K] [FiniteDimensional K W] in
private lemma smallOrth_pow_apply_smul {f : W ≃ₗ[K] W} {u : W} {c : K}
    (h : f u = c • u) (n : ℕ) : (f ^ n) u = c ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.map_smul, h, smul_smul, pow_succ]

theorem apply_eq_self_of_central_reflection (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hdim : finrank K W ≤ 4) (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) (u : W)
    [Invertible (Q u)] (hu : TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈ T)
    (huc : ∀ t ∈ T, t * TauCeti.QuadraticMap.reflectionOrthogonal Q u =
      TauCeti.QuadraticMap.reflectionOrthogonal Q u * t)
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : g ^ p ^ j = 1)
    (hgT : g ∈ normalizer (T : Set (TauCeti.QuadraticMap.orthogonalGroup Q))) :
    (g : W ≃ₗ[K] W) u = u := by
  classical
  have h2 : (2 : K) ≠ 0 := smallOrth_two_ne_zero hodd
  have hQu : Q u ≠ 0 := (isUnit_of_invertible (Q u)).ne_zero
  have hune : u ≠ 0 := by
    intro h
    exact hQu (by rw [h, map_zero])
  let ru : TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflectionOrthogonal Q u
  let r : ℕ → TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun i => g ^ i * ru * (g ^ i)⁻¹
  let v : Fin 5 → W := fun i =>
    ((g ^ (i : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) u
  have hu' : ru ∈ T := by simpa [ru] using hu
  have huc' : ∀ t ∈ T, t * ru = ru * t := by simpa [ru] using huc
  have hmemcentral : ∀ i : ℕ, r i ∈ T ∧ ∀ t ∈ T, t * r i = r i * t := by
    intro i
    constructor
    · have hgi : g ^ i ∈ normalizer (T : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
        Subgroup.pow_mem _ hgT i
      exact (Subgroup.mem_normalizer_iff.mp hgi ru).mp hu'
    · intro t ht
      have hgi : g ^ i ∈ normalizer (T : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
        Subgroup.pow_mem _ hgT i
      have hgi' : (g ^ i)⁻¹ ∈
          normalizer (T : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
        Subgroup.inv_mem _ hgi
      have ht' : (g ^ i)⁻¹ * t * (g ^ i) ∈ T :=
        (Subgroup.mem_normalizer_iff.mp hgi' t).mp ht
      have hcomm := huc' _ ht'
      calc t * (g ^ i * ru * (g ^ i)⁻¹)
          = g ^ i * (((g ^ i)⁻¹ * t * (g ^ i)) * ru) * (g ^ i)⁻¹ := by group
        _ = g ^ i * (ru * ((g ^ i)⁻¹ * t * (g ^ i))) * (g ^ i)⁻¹ := by rw [hcomm]
        _ = (g ^ i * ru * (g ^ i)⁻¹) * t := by group
  have hrT : ∀ i : ℕ, r i ∈ T := fun i => (hmemcentral i).1
  have hrCentral : ∀ i : ℕ, ∀ t ∈ T, t * r i = r i * t := fun i => (hmemcentral i).2
  have hrComm : ∀ i j : ℕ, r i * r j = r j * r i := by
    intro i j
    exact (hrCentral i (r j) (hrT j)).symm
  have hQpow : ∀ i : ℕ, Q (((g ^ i : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W) u) = Q u := by
    intro i
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (g ^ i).2 u
  by_cases hmem : ∃ c : K, ((g : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W) u = c • u
  · obtain ⟨c, hc⟩ := hmem
    have huQ : Q (((g : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) u) = Q u :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 u
    have hc2 : c ^ 2 = 1 := by
      have hq := congrArg Q hc
      rw [huQ, QuadraticMap.map_smul, smul_eq_mul] at hq
      have hq' : (c * c) * Q u = 1 * Q u := by rw [one_mul]; exact hq.symm
      have hcc : c * c = 1 := mul_right_cancel₀ hQu hq'
      simpa [pow_two] using hcc
    have hcP : c ^ (p ^ j) = 1 := by
      have h1 : ((g ^ (p ^ j) : TauCeti.QuadraticMap.orthogonalGroup Q) :
          W ≃ₗ[K] W) u = u := by rw [hg]; rfl
      have h2 : (((g : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) ^
          (p ^ j)) u = c ^ (p ^ j) • u := smallOrth_pow_apply_smul hc (p ^ j)
      have h3 : ((g ^ (p ^ j) : TauCeti.QuadraticMap.orthogonalGroup Q) :
          W ≃ₗ[K] W) u = (((g : TauCeti.QuadraticMap.orthogonalGroup Q) :
            W ≃ₗ[K] W) ^ (p ^ j)) u := by rw [Subgroup.coe_pow]
      rw [h3, h2] at h1
      have h1' : c ^ (p ^ j) • u = (1 : K) • u := by simpa using h1
      have := smul_left_injective K hune h1'
      simpa using this
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hcop : Nat.Coprime 2 (p ^ j) := hpodd.coprime_two_left.pow_right j
    have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hc2, hcP⟩
    rw [hc, hc1, one_smul]
  · have hnot : ¬ ∃ c : K, ((g : TauCeti.QuadraticMap.orthogonalGroup Q) :
        W ≃ₗ[K] W) u = c • u := hmem
    have hnotprop : ∀ d : ℕ, 0 < d → d < 5 →
        ¬ ∃ c : K, ((g ^ d : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) u =
          c • u := by
      intro d hd0 hd5 hc
      obtain ⟨c, hc⟩ := hc
      have hdvd : orderOf g ∣ p ^ j := orderOf_dvd_of_pow_eq_one hg
      have hpd : ¬ p ∣ d := Nat.not_dvd_of_pos_of_lt hd0 (by omega)
      have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
      have hcop : Nat.Coprime d (p ^ j) := hpd'.symm.pow_right j
      have hcop' : Nat.Coprime d (orderOf g) := hcop.coprime_dvd_right hdvd
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop'
      have hm' : ((((g ^ d : TauCeti.QuadraticMap.orthogonalGroup Q) :
          W ≃ₗ[K] W)) ^ m) u =
          ((g : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) u := by
        have := congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup Q =>
          (x : W ≃ₗ[K] W) u) hm
        simpa [Subgroup.coe_pow] using this
      rw [smallOrth_pow_apply_smul hc m] at hm'
      exact hnot ⟨c ^ m, hm'.symm⟩
    have key : ∀ {i j : Fin 5} {c : K}, (i : ℕ) < (j : ℕ) →
        v j = c • v i → False := by
      intro i j c hij hc
      have hd0 : 0 < (j : ℕ) - (i : ℕ) := by omega
      have hd5 : (j : ℕ) - (i : ℕ) < 5 := by omega
      have hsplit : (g ^ (j : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) =
          g ^ (i : ℕ) * g ^ ((j : ℕ) - (i : ℕ)) := by
        rw [← pow_add]
        congr 1
        omega
      have h1 : ((g ^ (i : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W)
          (((g ^ ((j : ℕ) - (i : ℕ)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
            W ≃ₗ[K] W) u) =
          c • (((g ^ (i : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) :
            W ≃ₗ[K] W) u) := by
        calc ((g ^ (i : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W)
              (((g ^ ((j : ℕ) - (i : ℕ)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
                W ≃ₗ[K] W) u)
            = ((g ^ (j : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) :
                W ≃ₗ[K] W) u := by
                rw [hsplit, Subgroup.coe_mul, LinearEquiv.mul_apply]
          _ = c • (((g ^ (i : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) :
                W ≃ₗ[K] W) u) := by simpa [v] using hc
      have h2 : ((g ^ ((j : ℕ) - (i : ℕ)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
          W ≃ₗ[K] W) u = c • u := by
        apply ((g ^ (i : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q) :
          W ≃ₗ[K] W).injective
        simpa [LinearEquiv.map_smul] using h1
      exact hnotprop ((j : ℕ) - (i : ℕ)) hd0 hd5 ⟨c, h2⟩
    have horth : ∀ i j : Fin 5, i ≠ j → polar Q (v i) (v j) = 0 := by
      intro i j hij
      have hQvi : Invertible (Q (v i)) :=
        invertibleOfNonzero (by rw [show v i = _ from rfl, hQpow (i : ℕ)]; exact hQu)
      have hQvj : Invertible (Q (v j)) :=
        invertibleOfNonzero (by rw [show v j = _ from rfl, hQpow (j : ℕ)]; exact hQu)
      let : Invertible (Q (v i)) := hQvi
      let : Invertible (Q (v j)) := hQvj
      have hri : r (i : ℕ) = TauCeti.QuadraticMap.reflectionOrthogonal Q (v i) := by
        dsimp [r, v, ru]
        exact TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q
          (g ^ (i : ℕ)) u
      have hrj : r (j : ℕ) = TauCeti.QuadraticMap.reflectionOrthogonal Q (v j) := by
        dsimp [r, v, ru]
        exact TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q
          (g ^ (j : ℕ)) u
      have hcomm : TauCeti.QuadraticMap.reflectionOrthogonal Q (v i) *
          TauCeti.QuadraticMap.reflectionOrthogonal Q (v j) =
          TauCeti.QuadraticMap.reflectionOrthogonal Q (v j) *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (v i) := by
        rw [← hri, ← hrj]
        exact hrComm (i : ℕ) (j : ℕ)
      rcases smallOrth_reflection_comm_orth_or_smul h2 hcomm with h | ⟨c, hc⟩
      · exact h
      · exfalso
        have hvalne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        rcases lt_or_gt_of_ne hvalne with hlt | hgt
        · exact key hlt hc
        · have hcne : c ≠ 0 := by
            intro hc0
            have hvj0 : v j = 0 := by rw [hc, hc0, zero_smul]
            have hQvj0 : Q (v j) = 0 := by rw [hvj0, map_zero]
            rw [show v j = _ from rfl, hQpow (j : ℕ)] at hQvj0
            exact hQu hQvj0
          have hc' : v i = c⁻¹ • v j := by
            rw [hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
          exact key hgt hc'
    have hvQ : ∀ i : Fin 5, Q (v i) = Q u := fun i => hQpow (i : ℕ)
    have hdiag : ∀ i : Fin 5, ((polarBilin Q) (v i)) (v i) ≠ 0 := by
      intro i
      rw [polarBilin_apply_apply, polar_self, hvQ i, nsmul_eq_mul]
      exact mul_ne_zero h2 hQu
    have hli : LinearIndependent K v :=
      LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := polarBilin Q) (v := v)
        (fun i j hij => horth i j hij) hdiag
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    omega

omit [Finite K] [FiniteDimensional K W] in
private lemma smallOrth_stab_ker_polar_of_central (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K W}
    (u : W) [Invertible (Q u)]
    {c : TauCeti.QuadraticMap.orthogonalGroup Q}
    (hcC : c ∈ Subgroup.centralizer
      ({TauCeti.QuadraticMap.reflectionOrthogonal Q u} :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q))) :
    (c : W ≃ₗ[K] W) ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub
      (LinearMap.ker (polarBilin Q u)) := by
  classical
  set ru : TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflectionOrthogonal Q u with hru
  have hQu : Q u ≠ 0 := (isUnit_of_invertible (Q u)).ne_zero
  have hune : u ≠ 0 := by
    intro h
    exact hQu (by rw [h, map_zero])
  have hcC' : c ∈ Subgroup.centralizer ({ru} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by simpa [hru] using hcC
  have hforward : ∀ (d : TauCeti.QuadraticMap.orthogonalGroup Q),
      d ∈ Subgroup.centralizer ({ru} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) →
      ∀ x : W, x ∈ LinearMap.ker (polarBilin Q u) →
        (d : W ≃ₗ[K] W) x ∈ LinearMap.ker (polarBilin Q u) := by
    intro d hdC x hx
    have hdcomm : ru * d = d * ru :=
      (Subgroup.mem_centralizer_iff.mp hdC) ru (by simp)
    have hdcomm_lin : (ru : W ≃ₗ[K] W) * (d : W ≃ₗ[K] W) =
        (d : W ≃ₗ[K] W) * (ru : W ≃ₗ[K] W) := congrArg Subtype.val hdcomm
    have hdu_neg : (ru : W ≃ₗ[K] W) ((d : W ≃ₗ[K] W) u) =
        -((d : W ≃ₗ[K] W) u) := by
      calc (ru : W ≃ₗ[K] W) ((d : W ≃ₗ[K] W) u)
          = ((ru : W ≃ₗ[K] W) * (d : W ≃ₗ[K] W)) u := by rw [LinearEquiv.mul_apply]
        _ = ((d : W ≃ₗ[K] W) * (ru : W ≃ₗ[K] W)) u := by rw [hdcomm_lin]
        _ = (d : W ≃ₗ[K] W) ((ru : W ≃ₗ[K] W) u) := by rw [LinearEquiv.mul_apply]
        _ = (d : W ≃ₗ[K] W) (-u) := by
              rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
                TauCeti.QuadraticMap.reflection_apply_self]
        _ = -((d : W ≃ₗ[K] W) u) := map_neg (d : W ≃ₗ[K] W) u
    obtain ⟨lam, hlam⟩ := smallOrth_reflection_apply_eq_neg_smul h2 u hdu_neg
    have hlam0 : lam ≠ 0 := by
      intro h0
      apply hune
      have hdu0 : (d : W ≃ₗ[K] W) u = 0 := by rw [hlam, h0, zero_smul]
      exact (d : W ≃ₗ[K] W).injective (by rw [hdu0, map_zero])
    have hx0 : polar Q u x = 0 := LinearMap.mem_ker.mp hx
    have hp := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem d.2 u x
    rw [hlam, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hx0] at hp
    have hdx0 : polar Q u ((d : W ≃ₗ[K] W) x) = 0 :=
      (mul_eq_zero.mp hp).resolve_left hlam0
    exact LinearMap.mem_ker.mpr hdx0
  rw [CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub]
  intro x
  constructor
  · intro hx
    exact hforward c hcC' x hx
  · intro hx
    have hcx : (c : W ≃ₗ[K] W) x ∈ LinearMap.ker (polarBilin Q u) := hx
    have hx' : (c⁻¹ : W ≃ₗ[K] W) ((c : W ≃ₗ[K] W) x) ∈
        LinearMap.ker (polarBilin Q u) :=
      hforward c⁻¹ ((Subgroup.centralizer ({ru} :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q))).inv_mem hcC')
        ((c : W ≃ₗ[K] W) x) hcx
    simpa using hx'

omit [Finite K] [FiniteDimensional K W] in
private lemma smallOrth_orthExtend_comm_reflection {Q : QuadraticForm K W}
    (u : W) [Invertible (Q u)] {U L : Submodule K W} (hc : IsCompl U L)
    (hU : ∀ x ∈ U, polar Q u x = 0)
    (hL : ∀ y ∈ L, ∃ c : K, y = c • u)
    (φ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) :
    (orthExtend hc (φ : U ≃ₗ[K] U) : W ≃ₗ[K] W) *
        (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W) =
      (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W) *
        (orthExtend hc (φ : U ≃ₗ[K] U) : W ≃ₗ[K] W) := by
  classical
  apply LinearEquiv.ext
  intro x
  obtain ⟨xU, xL, rfl⟩ := exists_add_of_isCompl hc x
  have hUfix : (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W) (xU : W) =
      (xU : W) := by
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q u (hU xU xU.2)
  have hUfix_phi : (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W)
      (((φ : U ≃ₗ[K] U) xU : U) : W) = (((φ : U ≃ₗ[K] U) xU : U) : W) := by
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q u
      (hU _ ((φ : U ≃ₗ[K] U) xU).2)
  have hLneg : (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W) (xL : W) =
      -(xL : W) := by
    obtain ⟨c, hcL⟩ := hL xL xL.2
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, hcL, map_smul,
      TauCeti.QuadraticMap.reflection_apply_self, smul_neg]
  have harg : (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W)
      ((xU : W) + xL) = (xU : W) + ((-xL : L) : W) := by
    rw [map_add, hUfix, hLneg]
    simp
  have hleft : (orthExtend hc (φ : U ≃ₗ[K] U))
      ((TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W) ((xU : W) + xL)) =
      ((φ : U ≃ₗ[K] U) xU : W) - (xL : W) := by
    rw [harg, orthExtend_apply hc (φ : U ≃ₗ[K] U) xU (-xL)]
    rw [sub_eq_add_neg]
    simp
  have hright : (TauCeti.QuadraticMap.reflectionOrthogonal Q u : W ≃ₗ[K] W)
      ((orthExtend hc (φ : U ≃ₗ[K] U)) ((xU : W) + xL)) =
      ((φ : U ≃ₗ[K] U) xU : W) - (xL : W) := by
    rw [orthExtend_apply hc (φ : U ≃ₗ[K] U) xU xL]
    rw [map_add, hUfix_phi, hLneg]
    rw [sub_eq_add_neg]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hleft, hright]

theorem eq_one_of_central_reflection (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) (T : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q))
    (u : W) [Invertible (Q u)]
    (hu : TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈
      (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)))
    (huc : ∀ t ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
      t * TauCeti.QuadraticMap.reflectionOrthogonal Q u =
        TauCeti.QuadraticMap.reflectionOrthogonal Q u * t)
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} {N : ℕ} (hg : g ^ N = 1)
    (hgT : g ∈ normalizer
      ((T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)))
    (hgu : (g : W ≃ₗ[K] W) u = u)
    (H : ∀ (T' : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (LinearMap.ker (polarBilin Q u)).subtype)))
      (g' : TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (LinearMap.ker (polarBilin Q u)).subtype)),
      g' ^ N = 1 → g' ∈ normalizer
        ((T' : Subgroup (TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (LinearMap.ker (polarBilin Q u)).subtype))) :
          Set (TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (LinearMap.ker (polarBilin Q u)).subtype))) → g' = 1) :
    g = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := smallOrth_two_ne_zero hodd
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun f : W ≃ₗ[K] W => (f : W → W))
      (fun f g h => LinearEquiv.ext (congrFun h))
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := Subtype.finite
  have hQu : Q u ≠ 0 := (isUnit_of_invertible (Q u)).ne_zero
  have hune : u ≠ 0 := by
    intro h
    exact hQu (by rw [h, map_zero])
  let U : Submodule K W := LinearMap.ker (polarBilin Q u)
  let L : Submodule K W := K ∙ u
  let ru : TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflectionOrthogonal Q u
  have hB : (polarBilin Q u) u ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self, nsmul_eq_mul]
    exact mul_ne_zero h2 hQu
  have hU_mem : ∀ x ∈ U, polar Q u x = 0 := fun x hx => LinearMap.mem_ker.mp hx
  have hL_mem : ∀ y ∈ L, ∃ c : K, y = c • u := by
    intro y hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, hc.symm⟩
  have hcompl : IsCompl L U := by
    have h0 : IsCompl L ((K ∙ u).orthogonalBilin (polarBilin Q)) :=
      LinearMap.isCompl_span_singleton_orthogonal (B := polarBilin Q) (x := u) hB
    have hUeq : (K ∙ u).orthogonalBilin (polarBilin Q) = U := by
      rw [Submodule.orthogonalBilin_span_singleton]
    rwa [hUeq] at h0
  have hcomplUL : IsCompl U L := hcompl.symm
  have horth : ∀ x ∈ U, ∀ y ∈ L, polar Q x y = 0 := by
    intro x hx y hy
    obtain ⟨c, rfl⟩ := hL_mem y hy
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      polar_comm, hU_mem x hx, mul_zero]
  have hQU : (polarBilin (Q.comp U.subtype)).Nondegenerate :=
    CFSG.ClassicalGroups.Orthogonal.Small.nondegenerate_comp_subtype hQ hcomplUL horth
  let C : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.centralizer ({ru} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))
  have hruT : ru ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    simpa [ru] using hu
  have hTC : (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ C := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact (huc t ht).symm
  have hgC : g ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    have : Invertible (Q ((g : W ≃ₗ[K] W) u)) :=
      invertibleOfNonzero (by rw [hgu]; exact hQu)
    have hconjO : g * ru * g⁻¹ = ru := by
      dsimp [ru]
      rw [TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv]
      apply Subtype.ext
      rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal]
      rw [← CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection (Q := Q) (v := (g : W ≃ₗ[K] W) u),
        ← CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection (Q := Q) (v := u)]
      rw [hgu]
    have h1O : g * ru = ru * g := by
      calc g * ru = (g * ru * g⁻¹) * g := by group
        _ = ru * g := by rw [hconjO]
    exact h1O.symm
  have hstab : ∀ c : C, ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) ∈
      CFSG.ClassicalGroups.Orthogonal.Small.stabSub U := by
    intro c
    have hcC : (c : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        Subgroup.centralizer ({TauCeti.QuadraticMap.reflectionOrthogonal Q u} :
          Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      show (c : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        Subgroup.centralizer ({ru} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))
      exact c.2
    simpa [U] using smallOrth_stab_ker_polar_of_central h2 (Q := Q) u hcC
  let toStab : C →* CFSG.ClassicalGroups.Orthogonal.Small.stabSub U :=
  { toFun := fun c => ⟨((c : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W), hstab c⟩
    map_one' := Subtype.ext rfl
    map_mul' := fun c d => Subtype.ext rfl }
  let ρ : C →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) :=
  { toFun := fun c => ⟨(CFSG.ClassicalGroups.Orthogonal.Small.resHom U) (toStab c),
      CFSG.ClassicalGroups.Orthogonal.Small.resHom_mem_orthogonalGroup
        (c : TauCeti.QuadraticMap.orthogonalGroup Q).2 (hstab c)⟩
    map_one' := Subtype.ext (map_one (CFSG.ClassicalGroups.Orthogonal.Small.resHom U))
    map_mul' := fun c d => Subtype.ext
      (map_mul (CFSG.ClassicalGroups.Orthogonal.Small.resHom U) (toStab c) (toStab d)) }
  have hρsurj : Function.Surjective ρ := by
    intro φ
    let ψ : W ≃ₗ[K] W := orthExtend hcomplUL (φ : U ≃ₗ[K] U)
    have hψO : ψ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      exact (CFSG.LocalAnalysis.ComponentInitial.orthogonal_complement_elementary_embedding
        Q hcomplUL horth).2.1 φ φ.2
    have hψcomm : ψ * (ru : W ≃ₗ[K] W) = (ru : W ≃ₗ[K] W) * ψ := by
      simpa [ψ, ru] using smallOrth_orthExtend_comm_reflection (Q := Q) u hcomplUL hU_mem hL_mem φ
    have hψC : (⟨ψ, hψO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact Subtype.ext hψcomm.symm
    let c : C := ⟨⟨ψ, hψO⟩, hψC⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ((CFSG.ClassicalGroups.Orthogonal.Small.resHom U) (toStab c) x : W) =
      (((φ : U ≃ₗ[K] U) x : U) : W)
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply]
    change ψ (x : W) = (((φ : U ≃ₗ[K] U) x : U) : W)
    have hx' := orthExtend_apply hcomplUL (φ : U ≃ₗ[K] U) x 0
    simpa [ψ] using hx'
  have : Finite C := Subtype.finite
  let TC : Sylow 2 C := T.subtype hTC
  let T' : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) :=
    Sylow.mapSurjective hρsurj TC
  let gC : C := ⟨g, hgC⟩
  have hgN : (ρ gC) ^ N = 1 := by
    have h1 : gC ^ N = 1 := Subtype.ext (by simpa [gC] using hg)
    calc (ρ gC) ^ N = ρ (gC ^ N) := (map_pow ρ gC N).symm
      _ = ρ 1 := by rw [h1]
      _ = 1 := map_one ρ
  have hgTC : gC ∈ Subgroup.normalizer ((TC : Subgroup C) : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Sylow.coe_subtype]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hx := (Subgroup.mem_normalizer_iff.mp hgT) (x : TauCeti.QuadraticMap.orthogonalGroup Q)
    convert hx using 2
  have hgT' : ρ gC ∈ Subgroup.normalizer ((T' : Subgroup
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))) : Set _) := by
    have hle := Subgroup.le_normalizer_map (H := (TC : Subgroup C)) ρ
    have hmem := hle (Subgroup.mem_map.mpr ⟨gC, hgTC, rfl⟩)
    have hT'eq : (T' : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))) =
        (TC : Subgroup C).map ρ := Sylow.coe_mapSurjective hρsurj TC
    simpa [hT'eq] using hmem
  have hg'1 : ρ gC = 1 := H T' (ρ gC) hgN hgT'
  have hfixU : ∀ x : U, (g : W ≃ₗ[K] W) (x : W) = (x : W) := by
    intro x
    have h := congrArg (fun e : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) =>
      (e : U ≃ₗ[K] U) x) hg'1
    change ((CFSG.ClassicalGroups.Orthogonal.Small.resHom U) (toStab gC) : U ≃ₗ[K] U) x =
      (1 : U ≃ₗ[K] U) x at h
    have hW := congrArg (fun z : U => (z : W)) h
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply] at hW
    change (g : W ≃ₗ[K] W) (x : W) = (x : W)
    simpa [gC, toStab] using hW
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨xU, xL, rfl⟩ := exists_add_of_isCompl hcomplUL x
  have hxU : (g : W ≃ₗ[K] W) (xU : W) = (xU : W) := hfixU xU
  have hxL : (g : W ≃ₗ[K] W) (xL : W) = (xL : W) := by
    obtain ⟨c, hc⟩ := hL_mem xL xL.2
    rw [hc, map_smul, hgu]
  rw [map_add, hxU, hxL]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
