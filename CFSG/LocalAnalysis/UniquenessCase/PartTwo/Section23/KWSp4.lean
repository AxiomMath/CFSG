module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4
public import CFSG.Milestones.ASVolI.A3Aut.SBSp4
public import CFSG.Milestones.ASVolI.A3Aut.Core2
public import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  Subgroup

private theorem torus_two_mul_comm {K : Type} [Field K] {x y : StatedSp 2 K}
    (hx : x ∈ torus 2 K) (hy : y ∈ torus 2 K) : x * y = y * x := by
  have h : (⟨x, hx⟩ : torus 2 K) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    apply (torusEquiv (r := 2) (k := K)).symm.injective
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val h

private theorem card_torus_two {K : Type} [Field K] [Finite K] :
    Nat.card (torus 2 K) = (Nat.card K - 1) ^ 2 := by
  rw [← Nat.card_congr (torusEquiv (r := 2) (k := K)).toEquiv,
    Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]

private theorem factorization_card_statedSp_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card K - 1) :
    (Nat.card (StatedSp 2 K)).factorization r = 2 * (Nat.card K - 1).factorization r := by
  rw [Nat.card_congr (CFSG.RankThree.PartOne.KFU.spRevEquiv K).toEquiv]
  rw [CFSG.RankThree.PartOne.KFU.factorization_card_spRev (p := r) hr hr2 hrd,
    Nat.card_units]

private theorem factorization_card_torus_two {K : Type} [Field K] [Finite K]
    {r : ℕ} (hrd : r ∣ Nat.card K - 1) :
    (Nat.card (torus 2 K)).factorization r = 2 * (Nat.card K - 1).factorization r := by
  rw [card_torus_two, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

private theorem exists_conj_mem_torus_of_mem_borel {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : StatedSp 2 K} (hodd : Odd (orderOf h)) (hhB : h ∈ borelSubgroup 2 K) :
    ∃ e ∈ unipotent 2 K, e⁻¹ * h * e ∈ torus 2 K := by
  have hBor := uc22pwI2_sp4_borel (K := K)
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU2 : IsPGroup 2 (unipotent 2 K) := by
    rw [← hP₀]
    exact P₀.isPGroup'
  obtain ⟨e, heU, hXle⟩ :=
    CFSG.ASVolI.burnsideAut_le_conj_complement
      (E := unipotent 2 K) (Y := borelSubgroup 2 K) (C := torus 2 K)
      (X := Subgroup.zpowers h)
      (CFSG.ASVolI.burnsideAut_sp_borel_le_normalizer (r := 2) (K := K))
      hU2 (torus_le_borelSubgroup (r := 2) (K := K)) hBor.2.eq_bot hBor.1.symm
      (Subgroup.zpowers_le.mpr hhB) (by rw [Nat.card_zpowers]; exact hodd)
  refine ⟨e, heU, ?_⟩
  obtain ⟨c, hcT, hce⟩ := Subgroup.mem_map.mp (hXle (Subgroup.mem_zpowers h))
  have hce' : e * c * e⁻¹ = h := by
    simpa [MulAut.conj_apply] using hce
  have hceq : e⁻¹ * h * e = c := by
    calc e⁻¹ * h * e = e⁻¹ * (e * c * e⁻¹) * e := by rw [hce']
      _ = c := by group
  rwa [hceq]

private theorem exists_sylow_r_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card K - 1) :
    ∃ P : Sylow r (StatedSp 2 K), (P : Subgroup (StatedSp 2 K)) ≤ torus 2 K := by
  haveI : Fact r.Prime := ⟨hr⟩
  let RT : Sylow r (torus 2 K) := default
  let R : Subgroup (StatedSp 2 K) := (RT : Subgroup (torus 2 K)).map (torus 2 K).subtype
  have hRcard : Nat.card R = r ^ (Nat.card (StatedSp 2 K)).factorization r := by
    rw [show Nat.card R = Nat.card RT from
      Subgroup.card_map_of_injective (torus 2 K).subtype_injective]
    rw [Sylow.card_eq_multiplicity, factorization_card_torus_two hrd,
      factorization_card_statedSp_two hr hr2 hrd]
  let P : Sylow r (StatedSp 2 K) := Sylow.ofCard R hRcard
  refine ⟨P, ?_⟩
  rw [show (P : Subgroup (StatedSp 2 K)) = R from Sylow.coe_ofCard _ _]
  rintro x ⟨y, -, rfl⟩
  exact y.2

private theorem exists_sylow_r_fixed_of_mem_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : StatedSp 2 K} (htT : t ∈ torus 2 K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card K - 1) :
    ∃ P : Sylow r (StatedSp 2 K),
      ∀ x ∈ (P : Subgroup (StatedSp 2 K)), t * x * t⁻¹ = x := by
  obtain ⟨P, hPT⟩ := exists_sylow_r_torus (K := K) hr hr2 hrd
  refine ⟨P, fun x hx => ?_⟩
  have hcomm := torus_two_mul_comm htT (hPT hx)
  calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hcomm]
    _ = x := by group

private theorem conj_smul_fixed {K : Type} [Field K] {g h : StatedSp 2 K}
    {r : ℕ} [Fact r.Prime] {P : Sylow r (StatedSp 2 K)}
    (hP : ∀ x ∈ (P : Subgroup (StatedSp 2 K)),
      (g⁻¹ * h * g) * x * (g⁻¹ * h * g)⁻¹ = x) :
    ∀ x ∈ ((g • P : Sylow r (StatedSp 2 K)) : Subgroup (StatedSp 2 K)),
      h * x * h⁻¹ = x := by
  intro x hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply] at hx
  have hx' : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [← hx']
  have hform : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
  calc h * (g * (g⁻¹ * x * g) * g⁻¹) * h⁻¹
      = g * ((g⁻¹ * h * g) * (g⁻¹ * x * g) * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by
        rw [hform]; group
    _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hP (g⁻¹ * x * g) hx]

private theorem exists_sylow_r_fixed_of_mem_borel {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : StatedSp 2 K} (hodd : Odd (orderOf h)) (hhB : h ∈ borelSubgroup 2 K)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card K - 1) :
    ∃ P : Sylow r (StatedSp 2 K),
      ∀ x ∈ (P : Subgroup (StatedSp 2 K)), h * x * h⁻¹ = x := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e, -, htT⟩ := exists_conj_mem_torus_of_mem_borel hodd hhB
  obtain ⟨P, hP⟩ := exists_sylow_r_fixed_of_mem_torus htT hr hr2 hrd
  exact ⟨e • P, conj_smul_fixed (r := r) (g := e) (h := h) (P := P) hP⟩

private theorem exists_conj_mem_borel_of_mem_normalizer_sylow_two {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : StatedSp 2 K} (S : Sylow 2 (StatedSp 2 K))
    (hnorm : h ∈ Subgroup.normalizer ((S : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K))) :
    ∃ g : StatedSp 2 K, g⁻¹ * h * g ∈ borelSubgroup 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := K) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 K) P₀ S
  have hSmap : (S : Subgroup (StatedSp 2 K)) =
      P₀.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hP₀]
    rfl
  have hBnorm : g⁻¹ * h * g ∈ Subgroup.normalizer
      ((P₀ : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) := by
    have hmapN := Subgroup.map_equiv_normalizer_eq
      (P₀ : Subgroup (StatedSp 2 K)) (MulAut.conj g)
    have h1 : h ∈ (Subgroup.normalizer
        ((P₀ : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K))).map
        (MulAut.conj g).toMonoidHom := by
      rw [hmapN, ← hSmap]
      exact hnorm
    rw [Subgroup.mem_map_equiv] at h1
    simpa [MulAut.conj_symm_apply] using h1
  refine ⟨g, ?_⟩
  rw [hP₀] at hBnorm
  rwa [← normalizer_unipotent (r := 2) (K := K)]

private theorem exists_sylow_r_fixed_of_mem_normalizer_sylow_two {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : StatedSp 2 K} (hodd : Odd (orderOf h))
    (S : Sylow 2 (StatedSp 2 K))
    (hnorm : h ∈ Subgroup.normalizer ((S : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card K - 1) :
    ∃ P : Sylow r (StatedSp 2 K),
      ∀ x ∈ (P : Subgroup (StatedSp 2 K)), h * x * h⁻¹ = x := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hB⟩ := exists_conj_mem_borel_of_mem_normalizer_sylow_two S hnorm
  have hoddB : Odd (orderOf (g⁻¹ * h * g)) := by
    rw [← MulAut.conj_symm_apply g h, MulEquiv.orderOf_eq]
    exact hodd
  obtain ⟨P, hP⟩ := exists_sylow_r_fixed_of_mem_borel hoddB hB hr hr2 hrd
  exact ⟨g • P, conj_smul_fixed (r := r) (g := g) (h := h) (P := P) hP⟩

private theorem mem_conj_range_of_not_W2111 {X : Type} [Group X] {a : ℕ} (hX : IsSp4 X a)
    {θ : MulAut X} (hW : ¬ W2111 X θ) :
    θ ∈ (MulAut.conj : X →* MulAut X).range := by
  by_contra hnot
  exact hW (Or.inl ⟨⟨a, hX⟩, hnot⟩)

private theorem odd_orderOf_of_inner {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : X ≃* StatedSp 2 K) {θ : MulAut X} {h : X}
    (hhθ : MulAut.conj h = θ) (hodd : Odd (orderOf θ)) : Odd (orderOf (e h)) := by
  let h' : StatedSp 2 K := e h
  have hconj : MulAut.congr e θ = MulAut.conj h' := by
    ext x i j
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply, map_mul, map_inv]
    rw [← hhθ, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hord : orderOf (MulAut.conj h') = orderOf θ := by
    rw [← hconj, MulEquiv.orderOf_eq]
  have hZ : Subgroup.center (StatedSp 2 K) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (n := 2) (by norm_num)
  have hinj := CFSG.LieType.Automorphisms.conj_injective_of_center_eq_bot hZ
  rw [(orderOf_injective (MulAut.conj : StatedSp 2 K →* MulAut (StatedSp 2 K))
    hinj h').symm, hord]
  exact hodd

private theorem exists_sylow_r_fixed_of_inner {X : Type} [Group X] [Finite X] {K : Type}
    [Field K] [Finite K] [CharP K 2] (e : X ≃* StatedSp 2 K) {θ : MulAut X} {h : X}
    (hhθ : MulAut.conj h = θ) (hodd : Odd (orderOf θ)) (S : Sylow 2 X)
    (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card K - 1) :
    ∃ P : Sylow r X, ∀ x ∈ (P : Subgroup X), θ x = x := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hnorm : h ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
    Subgroup.mem_normalizer_fintype fun x hx => by
      have := hS x hx
      rwa [← hhθ, MulAut.conj_apply] at this
  have hoddh : Odd (orderOf (e h)) := odd_orderOf_of_inner e hhθ hodd
  let h' : StatedSp 2 K := e h
  let S' : Sylow 2 (StatedSp 2 K) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hnorm' : h' ∈ Subgroup.normalizer
      ((S' : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) := by
    rw [show (S' : Subgroup (StatedSp 2 K)) = (S : Subgroup X).map e.toMonoidHom from
      Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S]
    rw [← Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hnorm
  obtain ⟨P', hP'⟩ :=
    exists_sylow_r_fixed_of_mem_normalizer_sylow_two hoddh S' hnorm' hr hr2 hrd
  have hrange : P' ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  let P : Sylow r X := P'.comapOfInjective e.toMonoidHom e.injective hrange
  refine ⟨P, fun x hx => ?_⟩
  have hx' : e x ∈ (P' : Subgroup (StatedSp 2 K)) := by
    rw [show (P : Subgroup X) = P'.comap e.toMonoidHom from
      Sylow.coe_comapOfInjective P' e.toMonoidHom e.injective hrange] at hx
    exact Subgroup.mem_comap.mp hx
  apply e.injective
  rw [← hhθ, MulAut.conj_apply, map_mul, map_mul, map_inv]
  exact hP' (e x) hx'

theorem kWSp4_holds : KWSp4 W2111 := by
  intro X _ _ a hX θ hodd hW S hS r hr hrd
  obtain ⟨hcl, ha⟩ := uc22p2214_bor_sp4_model hX
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eP⟩⟩ := hcl
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := a)
      (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  let e : X ≃* StatedSp 2 K := eP.trans (projSpEquiv K).symm
  obtain ⟨h, hhθ⟩ := mem_conj_range_of_not_W2111 hX hW
  have hr2 : r ≠ 2 := by
    have h1 : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rintro rfl
    exact Nat.two_not_dvd_two_mul_sub_one (Nat.two_pow_pos (a - 1))
      (by simpa [h1] using hrd)
  obtain ⟨P, hP⟩ := exists_sylow_r_fixed_of_inner e hhθ hodd S hS hr hr2 (by rwa [hKcard])
  exact ⟨P, hP⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
