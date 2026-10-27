module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowSL8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.Quasithin.Background.SimsE214NatCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix
open scoped LinearAlgebra.Projectivization Matrix

theorem s16h_H5_natNorm_statedSL_two_eight_elemAbelian_le_q
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hq7 : q ≠ 7) {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (StatedSL 2 K)) (hD : IsElemAbelian q D) :
    Nat.card D ≤ q := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact q.Prime := ⟨hq⟩
  have hΓ : HasScalarCommutant (StatedSL 2 K) := hasScalarCommutant_statedSL (by norm_num)
  have hAut : Nat.card (K ≃+* K) = 3 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 3) Nat.prime_two K (by rw [hK]; norm_num)).1
    simpa using h
  let φ : ↥D →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hDN)
  have hφrange : Nat.card φ.range = 1 := by
    obtain ⟨k, hk⟩ := hD.isPGroup.exists_card_eq
    have hdiv3 : Nat.card φ.range ∣ 3 := by
      have h := Subgroup.card_subgroup_dvd_card φ.range
      rwa [hAut] at h
    have hdivD : Nat.card φ.range ∣ Nat.card D := by
      have h := Subgroup.card_ker_mul_card_range φ
      exact ⟨Nat.card φ.ker, by rw [← h, mul_comm]⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h1 | h3
    · exact h1
    · exfalso
      have h3dvd : (3 : ℕ) ∣ q ^ k := by
        rw [hk] at hdivD
        rwa [h3] at hdivD
      have h3q : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow h3dvd
      exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3q).symm
  have hφ1 : φ = 1 := by
    have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp hφrange
    refine MonoidHom.ext fun d => ?_
    have hmem : φ d ∈ φ.range := MonoidHom.mem_range.mpr ⟨d, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hDlin : D ≤ linSub (ι := Fin 2) (K := K) := by
    intro d hd
    have hφd : fieldHom hΓ ⟨d, hDN hd⟩ = 1 := by
      have h : φ ⟨d, hd⟩ = 1 := by rw [hφ1]; rfl
      exact h
    exact (fieldHom_eq_one_iff hΓ ⟨d, hDN hd⟩).mp hφd
  let E₀ : Subgroup (GL (Fin 2) K) :=
    D.comap (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))
  have hDle : D ≤ (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range := by
    intro d hd
    obtain ⟨A, hA⟩ := exists_matAut_of_mem_linSub (hDlin hd)
    exact ⟨A, by rw [matHom_apply, hA]⟩
  have hcardE₀ : Nat.card E₀ = Nat.card D := by
    have hmap : E₀.map (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) = D :=
      Subgroup.map_comap_eq_self hDle
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (K := E₀) matHom_injective).symm
  have hGL : Nat.card (GL (Fin 2) K) = 3528 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hK]
    norm_num
  have hdvd : Nat.card D ∣ 3528 := by
    obtain ⟨c, hc⟩ := Subgroup.card_subgroup_dvd_card E₀
    refine ⟨c, ?_⟩
    rw [← hcardE₀]
    rw [hGL] at hc
    exact hc
  obtain ⟨k, hk⟩ := hD.isPGroup.exists_card_eq
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk, hk0, pow_zero]
    exact hq.one_le
  · exfalso
    have hq_dvd_D : q ∣ Nat.card D := by
      rw [hk]
      exact dvd_pow_self q hkpos.ne'
    have hq_dvd : q ∣ 3528 := hq_dvd_D.trans hdvd
    have h2357 : q = 2 ∨ q = 3 ∨ q = 7 := by
      have h3528 : (3528 : ℕ) = 2 ^ 3 * (3 ^ 2 * 7 ^ 2) := by norm_num
      rw [h3528] at hq_dvd
      rcases hq.dvd_mul.mp hq_dvd with h2 | h'
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
      · rcases hq.dvd_mul.mp h' with h3 | h7
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3)))
        · exact Or.inr (Or.inr
            ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp (hq.dvd_of_dvd_pow h7)))
    rcases h2357 with h | h | h
    · exact hq2 h
    · exact hq3 h
    · exact hq7 h

private theorem s16h_E3_stab_commSub {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {g : MulAut W} (hg : g ∈ normalizer (L : Set (MulAut W))) :
    g ∈ stabSub (commSub (⊤ : Subgroup W) L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

theorem s16h_H5_row_SL2_eight_one_aux {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :
    s16h_BlockBound A L q 1 := by
  intro E hE hEab
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub (commSub (⊤ : Subgroup W) L) := fun e he =>
    s16h_E3_stab_commSub (hEN he)
  have hcard := card_autSub_mul (A := E) (U := commSub (⊤ : Subgroup W) L) hEU
  obtain ⟨K, hKf, hKfin, hKcard, D, hDN, hD, hDcard⟩ :=
    s16h_H5_row_SL2_eight_bridge hc h hq hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hle : Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q := by
    rw [← hDcard]
    exact s16h_H5_natNorm_statedSL_two_eight_elemAbelian_le_q hKcard hq hq2 hq3 hq7 hDN hD
  calc Nat.card ↥E
      = Nat.card ↥(autSub E (commSub (⊤ : Subgroup W) L)) *
          Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) := hcard.symm
    _ ≤ q * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) :=
        Nat.mul_le_mul_right _ hle
    _ = q ^ 1 * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) := by rw [pow_one]

theorem s16h_H5_semilinear_three_fix {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {g : MulAut (StdMod (Fin 2) K)} {σ : K ≃+* K}
    (hg : IsSemilinear g σ) (hσ : σ ≠ 1) (hg3 : g ^ 3 = 1) :
    ∃ v : StdMod (Fin 2) K, v ≠ 1 ∧ g v = v := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hAut : Nat.card (K ≃+* K) = 3 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 3) Nat.prime_two K (by rw [hK]; norm_num)).1
    simpa using h
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_card_eq_one' (x := σ)
    rwa [hAut] at this
  have hord : orderOf σ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσ3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ
    · exact h
  obtain ⟨b, hb⟩ := exists_basis_fixed_of_semilinear (ι := Fin 2) (n := 3)
    (by norm_num) hK hg hord hg3
  refine ⟨Multiplicative.ofAdd (b 0), ?_, ?_⟩
  · intro h
    have h0 : b 0 = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    exact b.ne_zero 0 h0
  · have h := hb 0
    change Multiplicative.toAdd (g (Multiplicative.ofAdd (b 0))) = b 0 at h
    calc g (Multiplicative.ofAdd (b 0))
        = Multiplicative.ofAdd
            (Multiplicative.toAdd (g (Multiplicative.ofAdd (b 0)))) :=
          (ofAdd_toAdd _).symm
      _ = Multiplicative.ofAdd (b 0) := by rw [h]

private theorem s16h_H5E8_finite_mulAut {W : Type} [CommGroup W] [Finite W] :
    Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_H5E8_normalizer_le_stabSub_commSub {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private theorem s16h_H5E8_le_stabSub_commSub {W : Type} [CommGroup W]
    (L : Subgroup (MulAut W)) : L ≤ stabSub (commSub ⊤ L) := fun l hl =>
  s16h_H5E8_normalizer_le_stabSub_commSub (Subgroup.le_normalizer hl)

private theorem s16h_H5E8_le_stabSub_fixV {W : Type} [CommGroup W]
    (L : Subgroup (MulAut W)) : L ≤ stabSub (fixV L) := by
  intro l hl
  rw [mem_stabSub]
  intro z
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    have h1 : (l * x * l⁻¹) (l z) = l z := hz _ hx'
    have h2 : (l * x * l⁻¹) (l z) = l (x z) := by simp [MulAut.mul_apply]
    have h3 : l (x z) = l z := by rw [← h2, h1]
    exact l.injective h3
  · intro hz
    rw [mem_fixV] at hz
    rwa [hz l hl]

private theorem s16h_H5E8_normalizer_le_stabSub_fixV {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (fixV L) := by
  rw [mem_stabSub]
  intro z
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g * x * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h1 : (g * x * g⁻¹) (g z) = g z := hz _ hx'
    have h2 : (g * x * g⁻¹) (g z) = g (x z) := by simp [MulAut.mul_apply]
    have h3 : g (x z) = g z := by rw [← h2, h1]
    exact g.injective h3
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hg) x).mp hx
    have h1 : (g⁻¹ * x * g) z = z := hz _ hx'
    have h2 : g ((g⁻¹ * x * g) z) = g z := by rw [h1]
    have h3 : x (g z) = g ((g⁻¹ * x * g) z) := by simp [MulAut.mul_apply]
    rw [h3, h2]

private theorem s16h_H5E8_stabSub_inf {W : Type} [CommGroup W] {U Z : Subgroup W}
    {g : MulAut W} (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) := by
  rw [mem_stabSub] at hU hZ ⊢
  intro x
  exact ⟨fun hx => ⟨(hU x).mp hx.1, (hZ x).mp hx.2⟩,
    fun hx => ⟨(hU x).mpr hx.1, (hZ x).mpr hx.2⟩⟩

private theorem s16h_H5E8_autSec_le_normalizer {W : Type} [CommGroup W]
    {L Y : Subgroup (MulAut W)} {V C : Subgroup W}
    (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C) (hYV : Y ≤ stabSub V) (hYC : Y ≤ stabSub C)
    (hYL : Y ≤ normalizer (L : Set (MulAut W))) :
    autSec Y V C ≤ normalizer ((autSec L V C : Subgroup (MulAut (Sec V C))) :
      Set (MulAut (Sec V C))) := by
  set X' : Subgroup (MulAut W) := stabSub V ⊓ stabSub C with hX'def
  have hX'V : X' ≤ stabSub V := inf_le_left
  have hX'C : X' ≤ stabSub C := inf_le_right
  rw [← CFSG.Quasithin.B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hYV hYC),
    ← CFSG.Quasithin.B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hLV hLC)]
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp (hYL (Subgroup.mem_subgroupOf.mp hy)) (g : MulAut W)

private theorem s16h_H5E8_isPerfect_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : Group.IsPerfect X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : Group.IsPerfect ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_H5E8_isSimpleGroup_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : IsSimpleGroup X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 2) (by norm_num)
      (Or.inr hK2) (Or.inr hK3)
  haveI : IsSimpleGroup ↥(StatedSL 2 K) := q.symm.isSimpleGroup
  exact e.isSimpleGroup

private theorem s16h_H5E8_center_eq_bot_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := s16h_H5E8_isSimpleGroup_of_isSLn_two hm h
  haveI : Group.IsPerfect X := s16h_H5E8_isPerfect_of_isSLn_two hm h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative X) inferInstance

private theorem s16h_H5E8_matHom_range {K : Type} [Field K] :
    (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range =
      linSub (ι := Fin 2) (K := K) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    exact isSemilinear_matAut A
  · intro hg
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg
    exact ⟨A, rfl⟩

theorem s16h_H5_row_SL2_eight_bridge_strong {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = 8)
      (e : Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≃* StdMod (Fin 2) K)
      (D : Subgroup (MulAut (StdMod (Fin 2) K))),
      D = (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ∧
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) =
        natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧
      D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧
      IsElemAbelian q D ∧
      Nat.card D = Nat.card ↥(autSub E (commSub ⊤ L)) := by
  classical
  haveI : Finite (MulAut W) := s16h_H5E8_finite_mulAut
  obtain ⟨hSL, hNat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard3, hreal⟩ := hNat
  have hKcard : Nat.card K = 8 := by rw [hKcard3]; norm_num
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hcenter : Subgroup.center ↥L = ⊥ := s16h_H5E8_center_eq_bot_of_isSLn_two (by norm_num) hSL
  have hfaith : L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ :=
    s16h_H5_faithful_on_quotient hc hcenter
  have hLU : L ≤ stabSub (commSub ⊤ L) := s16h_H5E8_le_stabSub_commSub L
  have hLfix : L ≤ stabSub (fixV L) := s16h_H5E8_le_stabSub_fixV L
  have hLZ : L ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun l hl => s16h_H5E8_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_H5E8_normalizer_le_stabSub_commSub (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_H5E8_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun e he => s16h_H5E8_stabSub_inf (hEU he) (hEfix he)
  have hrealAuto : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K)).Realizes
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
      (⊤ : Subgroup (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))) ⊥ :=
    s16h_realizes_autSec_of_realizes inf_le_left hLU hLZ hfaith hreal
  obtain ⟨π, hπ⟩ := hrealAuto
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia
    (Γ := CFSG.Assembly.LowTwoRank.StatedSL 2 K) hπ
  have hπsurj : Function.Surjective π := hπ.1
  have hmapL : (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) =
      natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    map_congrHom_eq_natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) hπsurj e he
  set X₀ : Subgroup (MulAut W) :=
    stabSub (commSub ⊤ L) ⊓ stabSub (commSub ⊤ L ⊓ fixV L) with hX₀def
  have hX₀U : X₀ ≤ stabSub (commSub ⊤ L) := inf_le_left
  have hX₀Z : X₀ ≤ stabSub (commSub ⊤ L ⊓ fixV L) := inf_le_right
  have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
  have hEsec : IsElemAbelian q (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) := by
    have hmap := IsElemAbelian.map (hEab.subgroupOf X₀)
      (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z)
    rwa [CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀] at hmap
  have hEnorm : autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≤
      normalizer ((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
        Subgroup (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :
          Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :=
    s16h_H5E8_autSec_le_normalizer hLU hLZ hEU hEZ hEN
  have hDnorm : (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ≤
      natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
    have h1 : (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ≤
        (normalizer ((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
          Subgroup (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :
            Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))))).map (congrHom e) :=
      Subgroup.map_mono hEnorm
    have h2 : (normalizer ((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
          Subgroup (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :
            Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))))).map (congrHom e) =
        normalizer (((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2) K))) : Set (MulAut (StdMod (Fin 2) K))) := by
      simpa [congrHom] using Subgroup.map_equiv_normalizer_eq
        (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) (MulAut.congr e)
    rw [h2, hmapL] at h1
    simpa [natNorm] using h1
  refine ⟨K, hKf, hKfin, hKcard, e,
    (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e), rfl, hmapL,
    hDnorm, IsElemAbelian.map hEsec (congrHom e), ?_⟩
  rw [Subgroup.card_map_of_injective (congrHom_injective e)]
  exact (s16h_H5_card_autSub_eq_autSec hc hE).symm

theorem s16h_H5_natNorm_statedSL_two_eight_not_lin {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 9) : ¬ D ≤ linSub (ι := Fin 2) (K := K) := by
  intro hDlin
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hrange : D ≤ (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range := by
    rw [s16h_H5E8_matHom_range]
    exact hDlin
  let E₀ : Subgroup (GL (Fin 2) K) := D.comap (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))
  have hmapE₀ : E₀.map (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) = D :=
    Subgroup.map_comap_eq_self hrange
  have hcardE₀ : Nat.card E₀ = 9 := by
    rw [← Subgroup.card_map_of_injective (K := E₀) matHom_injective, hmapE₀, hcard]
  have hE₀el : IsElemAbelian 3 E₀ := IsElemAbelian.comap hD matHom_injective
  have hdvd7 : Nat.card (E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ)) ∣ 7 := by
    have h := Subgroup.card_subgroup_dvd_card
      (E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ))
    rwa [Nat.card_units, hK] at h
  have hmapdet_bot : E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) = ⊥ := by
    obtain ⟨k, hk⟩ :=
      (hE₀el.isPGroup.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ)).exists_card_eq
    have h3k : 3 ^ k ∣ 7 := hk ▸ hdvd7
    have hk0 : k = 0 := by
      by_contra hk0
      have h3dvd : 3 ∣ 7 := (dvd_pow_self 3 hk0).trans h3k
      norm_num at h3dvd
    exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
  have hE₀SL : E₀ ≤ StatedSL 2 K := by
    intro A hA
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    have hmem : GeneralLinearGroup.det A ∈
        E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) := ⟨A, hA, rfl⟩
    rw [hmapdet_bot] at hmem
    have h1 : GeneralLinearGroup.det A = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (GeneralLinearGroup.det A).val = 1 := congrArg Units.val h1
    rwa [GeneralLinearGroup.val_det_apply] at h2
  have hE₀pow : Nat.card E₀ = 3 ^ 2 := by rw [hcardE₀]; norm_num
  have h2le : 2 ≤ CFSG.Open.pRank 3 (StatedSL 2 K) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE₀SL hE₀el hE₀pow
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hK]
  have hring : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hring ▸ ringChar.charP K
  have hmodel : StatedClassicalModel (StatedSL 2 K) .PSL 2 2 3 := by
    refine ⟨by norm_num [StatedLieAdmissible], K, inferInstance, inferInstance,
      by rw [hK]; norm_num, ?_⟩
    refine ⟨?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K))).trans
        QuotientGroup.quotientBot).symm
  have hbound : CFSG.Open.pRank 3 (StatedSL 2 K) ≤ 1 := by
    have h := CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
      (X := StatedSL 2 K) hmodel Nat.prime_three (by norm_num)
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
  omega

theorem s16h_H5_eigenvector_seven_of_lin {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDlin : D ≤ linSub (ι := Fin 2) (K := K)) (hD : IsElemAbelian 7 D)
    (hcard : Nat.card D = 49) :
    ∃ (A : GL (Fin 2) K) (v : Fin 2 → K),
      v ≠ 0 ∧ A ≠ 1 ∧ matHom A ∈ D ∧ A • v = v := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let Dlin : Subgroup (GL (Fin 2) K) :=
    D.comap (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))
  have hrange : D ≤ (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range := by
    rw [s16h_H5E8_matHom_range]
    exact hDlin
  have hmap : Dlin.map (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) = D :=
    Subgroup.map_comap_eq_self hrange
  have hcardDlin : Nat.card Dlin = 49 := by
    rw [← Subgroup.card_map_of_injective
      (f := (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))) matHom_injective, hmap, hcard]
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hpgD : IsPGroup 7 D := CFSG.Open.IsElemAbelian.isPGroup hD
  have hpg : IsPGroup 7 Dlin :=
    hpgD.of_equiv ((Subgroup.equivMapOfInjective Dlin
      (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) matHom_injective).trans
        (MulEquiv.subgroupCongr hmap)).symm
  letI : Fintype Dlin := Fintype.ofFinite Dlin
  have hcardK : Fintype.card K = 8 := by rwa [Fintype.card_eq_nat_card]
  have hnot : ¬ 7 ∣ Nat.card (ℙ K (Fin 2 → K)) := by
    rw [Projectivization.card_of_finrank_two (k := K) (V := Fin 2 → K) (by simp)]
    rw [hK]
    norm_num
  obtain ⟨P, hP⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (ℙ K (Fin 2 → K)) hnot
  let x : Fin 2 → K := P.rep
  have hx : x ≠ 0 := P.rep_nonzero
  have hPx : Projectivization.mk K x hx = P := Projectivization.mk_rep P
  have hfix (d : Dlin) : ∃ c : K, ((d : GL (Fin 2) K)) • x = c • x := by
    have hsm : d • P = P := hP d
    have hdxne : ((d : GL (Fin 2) K)) • x ≠ 0 := by
      intro hzero
      have h1 : x = ((d : GL (Fin 2) K))⁻¹ • (((d : GL (Fin 2) K)) • x) := by
        calc x = (((d : GL (Fin 2) K))⁻¹ * ((d : GL (Fin 2) K))) • x := by
              rw [inv_mul_cancel, one_smul]
          _ = ((d : GL (Fin 2) K))⁻¹ • (((d : GL (Fin 2) K)) • x) := by rw [mul_smul]
      rw [h1, hzero, smul_zero] at hx
      exact hx rfl
    have hclass : Projectivization.mk K (((d : GL (Fin 2) K)) • x) hdxne =
        Projectivization.mk K x hx := by
      calc Projectivization.mk K (((d : GL (Fin 2) K)) • x) hdxne
          = d • Projectivization.mk K x hx := (Projectivization.smul_mk d hx).symm
        _ = d • P := by rw [hPx]
        _ = P := hsm
        _ = Projectivization.mk K x hx := hPx.symm
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hdxne hx).1 hclass
    refine ⟨(a : K), ?_⟩
    simpa only [Units.smul_def] using ha.symm
  let c : Dlin → K := fun d => Classical.choose (hfix d)
  have hc (d : Dlin) : ((d : GL (Fin 2) K)) • x = c d • x :=
    Classical.choose_spec (hfix d)
  have hlt : Fintype.card K < Fintype.card Dlin := by
    rw [hcardK, show Fintype.card Dlin = 49 by rw [Fintype.card_eq_nat_card]; exact hcardDlin]
    norm_num
  obtain ⟨d₁, d₂, hne, hceq⟩ := Fintype.exists_ne_map_eq_of_card_lt c hlt
  let A : Dlin := d₁ * d₂⁻¹
  have hAne : A ≠ 1 := by
    intro h
    apply hne
    have h1 : ((d₁ : Dlin) : GL (Fin 2) K) = ((d₂ : Dlin) : GL (Fin 2) K) := by
      have h3 : ((d₁ : Dlin) : GL (Fin 2) K) * ((d₂ : Dlin) : GL (Fin 2) K)⁻¹ = 1 := by
        simpa [A] using congrArg (fun z : Dlin => (z : GL (Fin 2) K)) h
      calc ((d₁ : Dlin) : GL (Fin 2) K)
          = ((d₁ : Dlin) : GL (Fin 2) K) *
              (((d₂ : Dlin) : GL (Fin 2) K)⁻¹ * ((d₂ : Dlin) : GL (Fin 2) K)) := by
            rw [inv_mul_cancel, mul_one]
        _ = (((d₁ : Dlin) : GL (Fin 2) K) * ((d₂ : Dlin) : GL (Fin 2) K)⁻¹) *
              ((d₂ : Dlin) : GL (Fin 2) K) := by group
        _ = ((d₂ : Dlin) : GL (Fin 2) K) := by rw [h3, one_mul]
    exact Subtype.ext h1
  have hd₂ne : c d₂ ≠ 0 := by
    intro h0
    have h := hc d₂
    rw [h0, zero_smul] at h
    have hx0 : x = 0 := by
      calc x = (((d₂ : Dlin) : GL (Fin 2) K))⁻¹ • (((d₂ : Dlin) : GL (Fin 2) K) • x) := by
            rw [← mul_smul, inv_mul_cancel, one_smul]
        _ = 0 := by rw [h, smul_zero]
    exact hx hx0
  have hd₂inv : ((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x = (c d₂)⁻¹ • x := by
    have h1 : x = c d₂ • (((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x) := by
      calc x = (((d₂ : Dlin) : GL (Fin 2) K)⁻¹ * ((d₂ : Dlin) : GL (Fin 2) K)) • x := by
            rw [inv_mul_cancel, one_smul]
        _ = (((d₂ : Dlin) : GL (Fin 2) K)⁻¹) • (((d₂ : Dlin) : GL (Fin 2) K) • x) := by
            rw [mul_smul]
        _ = (((d₂⁻¹ : Dlin) : GL (Fin 2) K)) • (((d₂ : Dlin) : GL (Fin 2) K) • x) := rfl
        _ = (((d₂⁻¹ : Dlin) : GL (Fin 2) K)) • (c d₂ • x) := by rw [hc d₂]
        _ = c d₂ • (((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x) := by rw [smul_comm]
    have h3 : (c d₂)⁻¹ • x = (((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x) := by
      calc (c d₂)⁻¹ • x
          = (c d₂)⁻¹ • (c d₂ • (((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x)) := by
              conv_lhs => rw [h1]
        _ = (((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x) := inv_smul_smul₀ hd₂ne _
    exact h3.symm
  have hAfix : ((A : Dlin) : GL (Fin 2) K) • x = x := by
    calc ((A : Dlin) : GL (Fin 2) K) • x
        = ((d₁ : Dlin) : GL (Fin 2) K) • (((d₂⁻¹ : Dlin) : GL (Fin 2) K) • x) := by
          simp [A, mul_smul]
      _ = ((d₁ : Dlin) : GL (Fin 2) K) • ((c d₂)⁻¹ • x) := by rw [hd₂inv]
      _ = (c d₂)⁻¹ • (((d₁ : Dlin) : GL (Fin 2) K) • x) := by rw [smul_comm]
      _ = (c d₂)⁻¹ • (c d₁ • x) := by rw [hc d₁]
      _ = x := by
        rw [hceq, inv_smul_smul₀ hd₂ne]
  refine ⟨(A : Dlin), x, hx, ?_, ?_, hAfix⟩
  · intro h
    apply hAne
    exact Subtype.ext h
  · have hAcomap : ((A : Dlin) : GL (Fin 2) K) ∈ Dlin := (A : Dlin).2
    exact (Subgroup.mem_comap).1 hAcomap

private theorem s16h_H5E8_sq_eq_one_of_mem_of_card_le_two {W : Type} [Group W] [Finite W]
    {Z : Subgroup W} (hZ : Nat.card Z ≤ 2) {z : W} (hz : z ∈ Z) : z ^ 2 = 1 := by
  haveI : Nonempty Z := ⟨⟨z, hz⟩⟩
  have hpos : 1 ≤ Nat.card Z := Nat.card_pos
  have hcases : Nat.card Z = 1 ∨ Nat.card Z = 2 := by omega
  rcases hcases with h1 | h2
  · have hbot : Z = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot] at hz
    rw [Subgroup.mem_bot.mp hz, one_pow]
  · have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z))
    rw [h2] at h
    exact congrArg Subtype.val h

private theorem s16h_H5E8_mulAut_apply_eq_of_mem_of_card_le_two {W : Type} [CommGroup W] [Finite W]
    {Z : Subgroup W} (hZ : Nat.card Z ≤ 2) {b : MulAut W} (hbZ : b ∈ stabSub Z) {z : W}
    (hz : z ∈ Z) : b z = z :=
  s15_Core_map_eq_self_of_card_le_two Z b hZ
    (fun u hu => (mem_stabSub.mp hbZ u).mpr hu) z hz

private theorem s16h_H5E8_apply_eq_of_apply_sq_eq {W : Type} [Group W] {g : MulAut W} {x : W}
    {n : ℕ} (hn : Odd n) (hg : g ^ n = 1) (h2 : g (g x) = x) : g x = x := by
  have hsq : ∀ m : ℕ, ((g ^ 2) ^ m) x = x := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih]
        exact h2
  obtain ⟨m, hm⟩ := hn
  have hpow : g ^ (2 * m + 1) = g * (g ^ 2) ^ m := by rw [pow_succ', pow_mul]
  calc g x = g (((g ^ 2) ^ m) x) := by rw [hsq m]
    _ = (g * (g ^ 2) ^ m) x := rfl
    _ = (g ^ (2 * m + 1)) x := by rw [hpow]
    _ = (g ^ n) x := by rw [hm]
    _ = (1 : MulAut W) x := by rw [hg]
    _ = x := rfl

theorem s16h_H5_row_SL2_eight_fix_aux {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) {q : ℕ} (hq : q = 3 ∨ q = 7) :
    s16h_H5Fix A L q := by
  intro E hE hEab hEcard w hw hwne
  classical
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZdef
  have hqprime : q.Prime := by
    rcases hq with hq3 | hq7
    · rw [hq3]; norm_num
    · rw [hq7]; norm_num
  have hq2 : q ≠ 2 := by
    rcases hq with hq3 | hq7
    · rw [hq3]; norm_num
    · rw [hq7]; norm_num
  obtain ⟨K, hKf, hKfin, hKcard, e, D, hDeq, hmapL, hDnorm, hDab, hDcard⟩ :=
    s16h_H5_row_SL2_eight_bridge_strong hc h hqprime hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun x hx => (mem_inf.mp (hE hx)).2
  have hEU : E ≤ stabSub U := fun x hx =>
    s16h_H5E8_normalizer_le_stabSub_commSub (hEN hx)
  have hEfix : E ≤ stabSub (fixV L) := fun x hx =>
    s16h_H5E8_normalizer_le_stabSub_fixV (hEN hx)
  have hEZ : E ≤ stabSub Z := fun x hx =>
    s16h_H5E8_stabSub_inf (hEU hx) (hEfix hx)
  have hpre : q ^ 2 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card ↥E := hEcard
  have hq2aut : q ^ 2 ≤ Nat.card ↥(autSub E U) := by
    have hcardE := card_autSub_mul (A := E) (U := U) hEU
    rw [← hcardE] at hpre
    exact Nat.le_of_mul_le_mul_right hpre Nat.card_pos
  have hq2D : q ^ 2 ≤ Nat.card D := by rw [hDcard]; exact hq2aut
  have hDle : Nat.card D ≤ q ^ 2 :=
    s16h_natNorm_elemAbelian_le_sl2 (K := K) (a := 3) ⟨by norm_num, by norm_num⟩
      (by rw [hKcard]; norm_num) hqprime hq2 hDnorm hDab
  have hDcard_eq : Nat.card D = q ^ 2 := le_antisymm hDle hq2D
  have hbvex : ∃ b ∈ D, b ≠ 1 ∧ ∃ v : StdMod (Fin 2) K, v ≠ 1 ∧ b v = v := by
    rcases hq with hq3 | hq7
    · subst hq3
      have hnotlin : ¬ D ≤ linSub (ι := Fin 2) (K := K) :=
        s16h_H5_natNorm_statedSL_two_eight_not_lin hKcard hDnorm hDab hDcard_eq
      obtain ⟨b, hbD, hbnotlin⟩ := Set.not_subset.mp hnotlin
      have hb3 : b ^ 3 = 1 := hDab.2 b hbD
      have hΓ : HasScalarCommutant (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
        hasScalarCommutant_statedSL (by norm_num)
      have hsem : IsSemilinear b (fieldAut hΓ ⟨b, hDnorm hbD⟩) :=
        isSemilinear_fieldAut hΓ ⟨b, hDnorm hbD⟩
      have hσne : fieldAut hΓ ⟨b, hDnorm hbD⟩ ≠ 1 := by
        intro h1
        exact hbnotlin ((fieldHom_eq_one_iff hΓ ⟨b, hDnorm hbD⟩).mp h1)
      obtain ⟨v, hvne, hbfix⟩ := s16h_H5_semilinear_three_fix hKcard hsem hσne hb3
      exact ⟨b, hbD, fun h => hbnotlin (h ▸ linSub.one_mem), v, hvne, hbfix⟩
    · subst hq7
      have hDlin : D ≤ linSub (ι := Fin 2) (K := K) := by
        have hΓ : HasScalarCommutant (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
          hasScalarCommutant_statedSL (by norm_num)
        let φ : ↥D →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hDnorm)
        have hAut3 : Nat.card (K ≃+* K) = 3 := by
          have hh := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
            (p := 2) (n := 3) Nat.prime_two K (by rw [hKcard]; norm_num)).1
          simpa using hh
        have hφ1 : φ = 1 := by
          refine MonoidHom.ext fun d => ?_
          have hdt : d ^ 7 = 1 := Subtype.ext (hDab.2 d d.2)
          have hdvd : orderOf (φ d) ∣ 7 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hdt, map_one])
          have h3 : (φ d) ^ 3 = 1 := by
            have := pow_card_eq_one' (x := φ d)
            rwa [hAut3] at this
          have h3dvd : orderOf (φ d) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
          rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
          · exact orderOf_eq_one_iff.mp h1
          · exfalso
            rw [h7] at h3dvd
            exact (by norm_num : ¬ (7 : ℕ) ∣ 3) h3dvd
        intro d hd
        exact (fieldHom_eq_one_iff hΓ ⟨d, hDnorm hd⟩).mp
          (by
            have := congrFun (congrArg DFunLike.coe hφ1) ⟨d, hd⟩
            exact this)
      obtain ⟨A, v, hvne, hAne, hAmem, hAfix⟩ :=
        s16h_H5_eigenvector_seven_of_lin hKcard hDlin hDab (by rw [hDcard_eq]; norm_num)
      refine ⟨matHom A, hAmem, fun h => hAne (matHom_injective (by rw [h, map_one])),
        Multiplicative.ofAdd v, ?_, ?_⟩
      · intro h1
        exact hvne (by
          have := congrArg Multiplicative.toAdd h1
          simpa using this)
      · change CFSG.Quasithin.H.matAut A (Multiplicative.ofAdd v) = Multiplicative.ofAdd v
        rw [← ofAdd_toAdd (CFSG.Quasithin.H.matAut A (Multiplicative.ofAdd v))]
        change Multiplicative.ofAdd (CFSG.Quasithin.H.toAddMap
          (CFSG.Quasithin.H.matAut A) v) = Multiplicative.ofAdd v
        rw [CFSG.Quasithin.H.toAddMap_matAut]
        have h : A *ᵥ v = v := by simpa using hAfix
        rw [h]
  obtain ⟨bm, hbmD, hbmne, v, hvne, hbmv⟩ := hbvex
  by_cases hwZ : w ∈ Z
  ·
    have hEcent : ¬ E ≤ centSub U := by
      intro hle
      have hinf : E ⊓ centSub U = E := inf_eq_left.mpr hle
      have hcardE := card_autSub_mul (A := E) (U := U) hEU
      rw [hinf] at hcardE
      have h1 : Nat.card ↥(autSub E U) * Nat.card ↥E = 1 * Nat.card ↥E := by
        rw [one_mul]; exact hcardE
      have h2 : Nat.card ↥(autSub E U) = 1 :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
      have h3 : q ^ 2 ≤ 1 := by rw [h2] at hq2aut; exact hq2aut
      nlinarith [hqprime.two_le]
    obtain ⟨b0, hb0E, hb0cent⟩ := Set.not_subset.mp hEcent
    have hb0fix : b0 w = w :=
      s16h_H5E8_mulAut_apply_eq_of_mem_of_card_le_two hZ (hEZ hb0E) hwZ
    exact ⟨1, L.one_mem, b0, hb0E, hb0cent, by simpa using hb0fix⟩
  ·
    let wU : U := ⟨w, hw⟩
    let wbar : Sec U Z := QuotientGroup.mk wU
    have hwbarne : wbar ≠ 1 := by
      intro h1
      have hmem : wU ∈ Z.subgroupOf U := (QuotientGroup.eq_one_iff wU).1 h1
      exact hwZ (Subgroup.mem_subgroupOf.mp hmem)
    let y : Fin 2 → K := Multiplicative.toAdd (e wbar)
    have hy : y ≠ 0 := by
      intro hy0
      apply hwbarne
      have h1 : e wbar = 1 := by
        have h2 : Multiplicative.ofAdd y = e wbar := ofAdd_toAdd (e wbar)
        have h3 : Multiplicative.ofAdd y = 1 := by rw [hy0, ofAdd_zero]
        rwa [h2] at h3
      exact e.injective (by simpa using h1)
    obtain ⟨g, hgStated, hgv⟩ :=
      CFSG.Quasithin.SimsE2.E214N.statedSL_exists_mulVec_eq (F := K) (u := y) (w := v) hy hvne
    let Γ : Subgroup (GL (Fin 2) K) := CFSG.Assembly.LowTwoRank.StatedSL 2 K
    let γ : ↥Γ := ⟨g, hgStated⟩
    have hnatmem : CFSG.Quasithin.H.natAut Γ γ ∈ CFSG.Quasithin.H.natImage Γ := ⟨γ, rfl⟩
    rw [← hmapL] at hnatmem
    obtain ⟨lsec, hlsecmem, hlseceq⟩ := hnatmem
    set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀def
    have hX₀U : X₀ ≤ stabSub U := inf_le_left
    have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
    have hLU : L ≤ stabSub U := fun l hl => s16h_H5E8_le_stabSub_commSub L hl
    have hLZ : L ≤ stabSub Z := fun l hl =>
      s16h_H5E8_stabSub_inf (s16h_H5E8_le_stabSub_commSub L hl)
        (s16h_H5E8_le_stabSub_fixV L hl)
    have hLsecEq : (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
        autSec L U Z :=
      CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z (le_inf hLU hLZ)
    rw [← hLsecEq] at hlsecmem
    obtain ⟨l0, hl0L, hl0sec⟩ := Subgroup.mem_map.mp hlsecmem
    let lL : L := ⟨(l0 : MulAut W), Subgroup.mem_subgroupOf.mp hl0L⟩
    have hlsec_toAdd : Multiplicative.toAdd (e (lsec wbar)) = v := by
      have h1 : CFSG.Quasithin.H.congrHom e lsec (e wbar) = e (lsec wbar) := by
        rw [CFSG.Quasithin.H.congrHom_apply, e.symm_apply_apply]
      rw [← h1, hlseceq]
      have h2 : Multiplicative.toAdd
          (CFSG.Quasithin.H.natAut Γ γ (e wbar)) = g *ᵥ y := by
        change CFSG.Quasithin.H.toAddMap (CFSG.Quasithin.H.natAut Γ γ) y = g *ᵥ y
        rw [CFSG.Quasithin.H.toAddMap_natAut]
      rw [h2, hgv]
    have hlsec_eq : e (lsec wbar) = Multiplicative.ofAdd v :=
      (ofAdd_toAdd (e (lsec wbar))).symm.trans (congrArg Multiplicative.ofAdd hlsec_toAdd)
    have hEsecEq : (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
        autSec E U Z :=
      CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z (le_inf hEU hEZ)
    have hbm_mem : bm ∈ (autSec E U Z).map (CFSG.Quasithin.H.congrHom e) := by
      rwa [← hDeq]
    obtain ⟨aE, haEmem, haEeq⟩ := Subgroup.mem_map.mp hbm_mem
    rw [← hEsecEq] at haEmem
    obtain ⟨b0, hb0E, hb0sec⟩ := Subgroup.mem_map.mp haEmem
    let b : MulAut W := b0
    have hbE : b ∈ E := Subgroup.mem_subgroupOf.mp hb0E
    have hbsec : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 = aE := hb0sec
    have hcongr_fix : CFSG.Quasithin.H.congrHom e aE (e (lsec wbar)) = e (lsec wbar) := by
      rw [haEeq, hlsec_eq]
      exact hbmv
    have hfix_class : aE (lsec wbar) = lsec wbar := by
      apply e.injective
      have h1 : CFSG.Quasithin.H.congrHom e aE (e (lsec wbar)) = e (aE (lsec wbar)) := by
        rw [CFSG.Quasithin.H.congrHom_apply, e.symm_apply_apply]
      rw [← h1]
      exact hcongr_fix
    have hfix_wbar : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 (lsec wbar) = lsec wbar := by
      rw [hbsec]
      exact hfix_class
    have hq' : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z (b0 * l0) wbar =
        CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0 wbar := by
      rw [map_mul]
      calc CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0
            (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0 wbar)
          = CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 (lsec wbar) := by rw [hl0sec]
        _ = lsec wbar := hfix_wbar
        _ = CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0 wbar := by rw [hl0sec]
    have hl0L' : (l0 : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hl0L
    have hl0wU : (l0 : MulAut W) w ∈ U :=
      ((hX₀U (le_inf hLU hLZ hl0L')) w).2 hw
    have hbwU : b ((l0 : MulAut W) w) ∈ U := (hEU hbE ((l0 : MulAut W) w)).2 hl0wU
    have hmk : (QuotientGroup.mk (⟨b ((l0 : MulAut W) w), hbwU⟩ : U) : Sec U Z) =
        (QuotientGroup.mk (⟨(l0 : MulAut W) w, hl0wU⟩ : U) : Sec U Z) := by
      simpa [CFSG.Quasithin.B5.secHom_mk, b, wbar, wU, MulAut.mul_apply] using hq'
    have hmem := (CFSG.Quasithin.mk_eq_mk_iff (U := Z.subgroupOf U) _ _).1 hmk
    have hz : b ((l0 : MulAut W) w) * ((l0 : MulAut W) w)⁻¹ ∈ Z := by
      have h2 := Subgroup.mem_subgroupOf.mp hmem
      simpa using h2
    set z : W := b ((l0 : MulAut W) w) * ((l0 : MulAut W) w)⁻¹ with hzdef
    have hz_mem : z ∈ Z := by rw [hzdef]; exact hz
    have hbz : b z = z :=
      s16h_H5E8_mulAut_apply_eq_of_mem_of_card_le_two hZ (hEZ hbE) hz_mem
    have hz2 : z ^ 2 = 1 := s16h_H5E8_sq_eq_one_of_mem_of_card_le_two hZ hz_mem
    have hxeq : b ((l0 : MulAut W) w) = z * ((l0 : MulAut W) w) := by rw [hzdef]; group
    have h2x : b (b ((l0 : MulAut W) w)) = (l0 : MulAut W) w := by
      have h1 : b (b ((l0 : MulAut W) w)) = z * (z * ((l0 : MulAut W) w)) := by
        calc b (b ((l0 : MulAut W) w))
            = b (z * ((l0 : MulAut W) w)) := by rw [hxeq]
          _ = b z * b ((l0 : MulAut W) w) := by rw [map_mul]
          _ = z * b ((l0 : MulAut W) w) := by rw [hbz]
          _ = z * (z * ((l0 : MulAut W) w)) := congrArg (fun y => z * y) hxeq
      rw [h1, ← mul_assoc, ← pow_two, hz2, one_mul]
    have hqodd : Odd q := by
      rcases hq with hq3 | hq7
      · rw [hq3]; exact ⟨1, by norm_num⟩
      · rw [hq7]; exact ⟨3, by norm_num⟩
    have hfix_wU : b ((l0 : MulAut W) w) = (l0 : MulAut W) w :=
      s16h_H5E8_apply_eq_of_apply_sq_eq hqodd (hEab.2 b hbE) h2x
    refine ⟨lL⁻¹, L.inv_mem hl0L, b, hbE, ?_, ?_⟩
    · intro hbcent
      have hbcentsec : b ∈ centSec U Z := centSub_le_centSec U Z hbcent
      have hker : b0 ∈ (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z).ker :=
        (CFSG.Quasithin.B5.mem_ker_secHom X₀ hX₀U hX₀Z b0).2 (by simpa [b] using hbcentsec)
      have hbsec1 : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 = 1 :=
        MonoidHom.mem_ker.mp hker
      have haE1 : aE = 1 := by rw [← hbsec, hbsec1]
      have hbm1 : bm = 1 := by rw [← haEeq, haE1, map_one]
      exact hbmne hbm1
    · simp only [inv_inv]
      calc ((lL : MulAut W)⁻¹ * b * (lL : MulAut W)) w
          = (lL : MulAut W)⁻¹ (b ((lL : MulAut W) w)) := by simp [MulAut.mul_apply]
        _ = (lL : MulAut W)⁻¹ ((lL : MulAut W) w) := by rw [hfix_wU]
        _ = w := by simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
