module

public import CFSG.LocalAnalysis.StandardType.GGK1ACenterTorsion

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary

private lemma cenLS_card_adjoinRoot {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} {a : K[X]} (ha : a ∈ primaryFactors x) :
    Nat.card (AdjoinRoot a) = Nat.card K ^ a.natDegree := by
  have : Module.Finite K (AdjoinRoot a) := (monic_of_mem_primaryFactors ha).finite_adjoinRoot
  have hdim : Module.finrank K (AdjoinRoot a) = a.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (monic_of_mem_primaryFactors ha).ne_zero),
      AdjoinRoot.powerBasis_dim]
  have hcard : Nat.card (AdjoinRoot a) = Nat.card K ^ Module.finrank K (AdjoinRoot a) :=
    Module.natCard_eq_pow_finrank
  rw [hcard, hdim]

private lemma cenLS_gcd_eq_p {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1) {x : GL (Fin N) K} {a : K[X]}
    (ha : a ∈ primaryFactors (ggK1A_glEnd x)) :
    Nat.gcd p (Nat.card (AdjoinRoot a) - 1) = p := by
  rw [cenLS_card_adjoinRoot ha, hK]
  exact (Nat.gcd_eq_left_iff_dvd).mpr
    (hdvd.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ nf) a.natDegree))

private lemma cenLS_card_torsGL {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : 0 < p) (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1)
    {x : GL (Fin N) K} (hsq : Squarefree (minpoly K (ggK1A_glEnd x))) :
    Nat.card (ggK1A_torsGL x p) = p ^ (primaryFactors (ggK1A_glEnd x)).card := by
  rw [card_ggK1A_torsGL hp hsq]
  trans ∏ _ : primaryFactors (ggK1A_glEnd x), p
  · exact Finset.prod_congr rfl fun a _ => cenLS_gcd_eq_p hK hdvd a.2
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

private lemma cenLS_p_ne_two {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1) : p ≠ 2 := by
  have hK2 : 1 < Nat.card K := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hnf : nf ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    omega
  have hodd : Odd (2 ^ nf - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnf
    refine ⟨2 ^ m - 1, ?_⟩
    rw [pow_succ]
    omega
  rintro rfl
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨j, hj⟩ := hdvd
  omega

private lemma cenLS_cast_p_ne_zero {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1) : (p : K) ≠ 0 := by
  have hp2 : p ≠ 2 := cenLS_p_ne_two hp hK hdvd
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := nf) (by rwa [← Nat.card_eq_fintype_card])
  intro h
  have hd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
  exact hp2 (Or.resolve_left (hp.eq_one_or_self_of_dvd 2 hd) (by norm_num)).symm

private lemma cenLS_N_pos {p N : ℕ} (hN : ¬ p ∣ N) : 0 < N :=
  Nat.pos_of_ne_zero fun h => hN (h ▸ dvd_zero p)

private lemma cenLS_scalar_eq_one {N : ℕ} {K : Type} [Field K] (hN : 0 < N) {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin N) c = 1) : c = 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h2 : Matrix.scalar (Fin N) (c : K) = Matrix.scalar (Fin N) (1 : K) := by
    simpa using congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) h
  exact Units.ext (Matrix.scalar_inj.mp h2)

private lemma cenLS_exists_pow_eq {p N : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hN : ¬ p ∣ N) {ζ : Kˣ} (hζ : ζ ^ p = 1) : ∃ c : Kˣ, c ^ p = 1 ∧ c ^ N = ζ := by
  have hcop : Nat.gcd p N = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hN
  have hmem : ∀ x : ↥(rootsOfUnity p K), (x : Kˣ) ^ N ∈ rootsOfUnity p K := by
    intro x
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, (mem_rootsOfUnity p (x : Kˣ)).mp x.2,
      one_pow]
  have hinj : Function.Injective (fun x : ↥(rootsOfUnity p K) =>
      (⟨(x : Kˣ) ^ N, hmem x⟩ : ↥(rootsOfUnity p K))) := by
    intro a b hab
    have hab' : (a : Kˣ) ^ N = (b : Kˣ) ^ N := congrArg Subtype.val hab
    have h1 : ((a : Kˣ) / b) ^ N = 1 := by rw [div_pow, hab', div_self']
    have h2 : ((a : Kˣ) / b) ^ p = 1 := by
      rw [div_pow, (mem_rootsOfUnity p (a : Kˣ)).mp a.2,
        (mem_rootsOfUnity p (b : Kˣ)).mp b.2, div_one]
    have hord : orderOf ((a : Kˣ) / b) ∣ Nat.gcd p N :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h2) (orderOf_dvd_iff_pow_eq_one.mpr h1)
    rw [hcop] at hord
    exact Subtype.ext (div_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)))
  obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.mp hinj ⟨ζ, hζ⟩
  exact ⟨c, (mem_rootsOfUnity p (c : Kˣ)).mp c.2, congrArg Subtype.val hc⟩

private lemma cenLS_det_range {p N : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hN : ¬ p ∣ N) {x : GL (Fin N) K} :
    ((Matrix.GeneralLinearGroup.det).comp (ggK1A_torsGL x p).subtype).range =
      rootsOfUnity p K := by
  ext c
  rw [MonoidHom.mem_range, mem_rootsOfUnity]
  constructor
  · rintro ⟨t, rfl⟩
    have h1 : t ^ p = 1 := by
      apply Subtype.ext
      exact (mem_ggK1A_torsGL_iff.mp t.2).1
    rw [← map_pow, h1, map_one]
  · intro hc
    obtain ⟨c', hcp, hcN⟩ := cenLS_exists_pow_eq hp hN hc
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin N) c', scalar_mem_ggK1A_torsGL x hcp⟩, ?_⟩
    show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin N) c') = c
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hcN]

private lemma cenLS_inf_scalars_bot {p N : ℕ} {K : Type} [Field K] (hp : p.Prime)
    (hN : ¬ p ∣ N) {x : GL (Fin N) K} :
    ggK1A_torsGL x p ⊓ LargeEvenSLGroup (Fin N) K ⊓ LargeEvenScalars (Fin N) K = ⊥ := by
  have hNpos : 0 < N := cenLS_N_pos hN
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at ht
  obtain ⟨⟨htP, htSL⟩, htSc⟩ := ht
  rw [largeEvenScalars_def, MonoidHom.mem_range] at htSc
  obtain ⟨c, rfl⟩ := htSc
  have hcp : c ^ p = 1 := by
    refine cenLS_scalar_eq_one hNpos ?_
    have h := (mem_ggK1A_torsGL_iff.mp htP).1
    rwa [← map_pow] at h
  have hcN : c ^ N = 1 := by
    change Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin N) c) = 1 at htSL
    rwa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at htSL
  have hgcd : Nat.gcd p N = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hN
  have hord : orderOf c ∣ Nat.gcd p N :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hcp) (orderOf_dvd_iff_pow_eq_one.mpr hcN)
  rw [hgcd] at hord
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  rw [hc1, map_one]
  exact Subgroup.mem_bot.mpr rfl

private lemma cenLS_card_inf {p nf N : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1) (hN : ¬ p ∣ N) {x : GL (Fin N) K}
    (hxp : x ^ p = 1) :
    Nat.card ↥(ggK1A_torsGL x p ⊓ LargeEvenSLGroup (Fin N) K) =
      p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) := by
  have hpK : (p : K) ≠ 0 := cenLS_cast_p_ne_zero hp hK hdvd
  have hsq : Squarefree (minpoly K (ggK1A_glEnd x)) := squarefree_minpoly_ggK1A_glEnd hpK hxp
  have hcardP : Nat.card ↥(ggK1A_torsGL x p) = p ^ (primaryFactors (ggK1A_glEnd x)).card :=
    cenLS_card_torsGL hp.pos hK hdvd hsq
  set T : Subgroup (GL (Fin N) K) := ggK1A_torsGL x p ⊓ LargeEvenSLGroup (Fin N) K with hT
  set φ : ↥(ggK1A_torsGL x p) →* Kˣ :=
    (Matrix.GeneralLinearGroup.det).comp (ggK1A_torsGL x p).subtype with hφ
  have hmaps : (T.subgroupOf (ggK1A_torsGL x p)).map (ggK1A_torsGL x p).subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr inf_le_left
  have hker : φ.ker = T.subgroupOf (ggK1A_torsGL x p) := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hT, Subgroup.mem_inf]
    exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥T := by
    rw [hker]
    have h1 := Subgroup.card_map_of_injective (f := (ggK1A_torsGL x p).subtype)
      (ggK1A_torsGL x p).subtype_injective (K := T.subgroupOf (ggK1A_torsGL x p))
    rw [hmaps] at h1
    exact h1.symm
  have hrange : Nat.card ↥φ.range = p := by
    have h1 : φ.range = rootsOfUnity p K := by
      rw [hφ]
      exact cenLS_det_range hp hN
    rw [h1, CFSG.RankThree.PartOne.card_rootsOfUnity_finite_field hp.pos]
    exact (Nat.gcd_eq_left_iff_dvd).mpr (by rw [hK]; exact hdvd)
  have hmul : Nat.card T * p = p ^ (primaryFactors (ggK1A_glEnd x)).card := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hcardker, hrange, hcardP] at h1
    exact h1
  have hs : (primaryFactors (ggK1A_glEnd x)).card ≠ 0 := by
    intro hs0
    have h1 : Nat.card T * p = 1 := by rw [hmul, hs0, pow_zero]
    have h2 : p ≤ Nat.card T * p := Nat.le_mul_of_pos_left p Nat.card_pos
    have h3 : 2 ≤ p := hp.two_le
    omega
  have hs1 : 1 ≤ (primaryFactors (ggK1A_glEnd x)).card := Nat.one_le_iff_ne_zero.mpr hs
  refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
  rw [hmul]
  rw [show p ^ (primaryFactors (ggK1A_glEnd x)).card =
      p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) * p by
    rw [← pow_succ, Nat.sub_add_cancel hs1]]

theorem ggK1A_exists_torsion_sl_of_dvd_sub_one {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1) (hN : ¬ p ∣ N)
    {x : GL (Fin N) K} (hxp : x ^ p = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSLGroup (Fin N) K ∧ T ≤ ggK1A_torsGL x p ∧
      T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) :=
  ⟨ggK1A_torsGL x p ⊓ LargeEvenSLGroup (Fin N) K, inf_le_right, inf_le_left,
    cenLS_inf_scalars_bot hp hN, cenLS_card_inf hp hK hdvd hN hxp⟩

end CFSG.StandardType

end
