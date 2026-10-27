module

public import CFSG.Quasithin.Background.HSL
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec41iii

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] [Finite K]

theorem s16h_H5_natNorm_statedSL_two_four_lin_dvd
    (hK : Nat.card K = 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hD : IsElemAbelian q D) :
    D ≤ linSub (ι := Fin 2) (K := K) ∧ Nat.card D ∣ 180 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hΓ : HasScalarCommutant (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    hasScalarCommutant_statedSL (K := K) (by norm_num)
  have hAut : Nat.card (K ≃+* K) = 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 2) Nat.prime_two K (by rw [hK]; norm_num)).1
    simpa using h
  let φ : ↥D →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hDN)
  have hφ1 : φ = 1 := by
    refine MonoidHom.ext fun d => ?_
    have hdq : d ^ q = 1 := Subtype.ext (hD.2 d d.2)
    have hq_dvd : orderOf (φ d) ∣ q :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hdq, map_one])
    have h2_eq : (φ d) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := φ d)
      rwa [hAut] at this
    have h2_dvd : orderOf (φ d) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2_eq
    rcases (Nat.dvd_prime hq).mp hq_dvd with h1 | hq_eq
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [hq_eq] at h2_dvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2_dvd)
  have hDlin : D ≤ linSub (ι := Fin 2) (K := K) := by
    intro d hd
    have hφd : (fieldHom hΓ) ((Subgroup.inclusion hDN) ⟨d, hd⟩) = 1 := by
      have h := congrFun (congrArg DFunLike.coe hφ1) ⟨d, hd⟩
      exact h
    have hφd' : (fieldHom hΓ) (⟨d, hDN hd⟩ :
        ↥(natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))) = 1 := by
      rwa [show (Subgroup.inclusion hDN) ⟨d, hd⟩ = ⟨d, hDN hd⟩ from rfl] at hφd
    exact (fieldHom_eq_one_iff hΓ ⟨d, hDN hd⟩).mp hφd'
  have hdiv : Nat.card D ∣ 180 := by
    have h1 : Nat.card D ∣ Nat.card (linSub (ι := Fin 2) (K := K)) :=
      Subgroup.card_dvd_of_le hDlin
    have hlin : Nat.card (linSub (ι := Fin 2) (K := K)) = 180 := by
      have hrange : (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range =
          linSub (ι := Fin 2) (K := K) := by
        ext g
        constructor
        · rintro ⟨A, rfl⟩
          exact isSemilinear_matAut A
        · intro hg
          obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg
          exact ⟨A, rfl⟩
      rw [← hrange]
      rw [← Nat.card_congr (MonoidHom.ofInjective
        (f := (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))) matHom_injective).toEquiv]
      rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hK]
      norm_num
    rwa [hlin] at h1
  exact ⟨hDlin, hdiv⟩

theorem s16h_H5_natNorm_statedSL_two_four_elemAbelian_one
    (hK : Nat.card K = 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hD : IsElemAbelian q D) :
    Nat.card D ≤ q := by
  obtain ⟨-, hdiv⟩ := s16h_H5_natNorm_statedSL_two_four_lin_dvd hK hq hq2 hDN hD
  haveI : Fact q.Prime := ⟨hq⟩
  have hpg : IsPGroup q D := CFSG.Open.IsElemAbelian.isPGroup hD
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  rw [hk] at hdiv ⊢
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero]
    exact hq.one_le
  · have hdvd : q ∣ 180 := dvd_trans (dvd_pow_self q hkpos.ne') hdiv
    have hq5 : q = 5 := by
      have h180 : (180 : ℕ) = 2 ^ 2 * (3 ^ 2 * 5) := by norm_num
      rw [h180] at hdvd
      rcases hq.dvd_mul.mp hdvd with h2 | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
          (hq.dvd_of_dvd_pow h2)) hq2
      · rcases hq.dvd_mul.mp h' with h3 | h5
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
            (hq.dvd_of_dvd_pow h3)) hq3
        · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5
    have hk1 : k = 1 := by
      by_contra hk1
      have hk2 : 2 ≤ k := by omega
      have h25 : 25 ∣ 180 := by
        rw [hq5] at hdiv
        exact dvd_trans (pow_dvd_pow 5 hk2) hdiv
      norm_num at h25
    rw [hq5, hk1, pow_one]


theorem s16h_H5_row_SL2_four_stab_commSub {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {g : MulAut W} (hg : g ∈ normalizer (L : Set (MulAut W))) :
    g ∈ stabSub (commSub ⊤ L) := by
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


theorem s16h_H5_natNorm_statedSL_two_four_three_card
    (hK : Nat.card K = 4) {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hD : IsElemAbelian 3 D) (h9 : 9 ≤ Nat.card D) :
    Nat.card D = 9 ∧ D ≤ linSub (ι := Fin 2) (K := K) := by
  obtain ⟨hDlin, hdiv⟩ :=
    s16h_H5_natNorm_statedSL_two_four_lin_dvd hK Nat.prime_three (by norm_num) hDN hD
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 D := CFSG.Open.IsElemAbelian.isPGroup hD
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hkdiv : 3 ^ k ∣ 180 := hk ▸ hdiv
  have hk2 : k = 2 := by
    have hle : k ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ k := by omega
      have h27 : 27 ∣ 180 := dvd_trans (pow_dvd_pow 3 h3) hkdiv
      norm_num at h27
    have hge : 2 ≤ k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      have hpow : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      rw [hk] at h9
      omega
    omega
  exact ⟨by rw [hk, hk2]; norm_num, hDlin⟩

private theorem s16h_E3RowSL4_finite_mulAut {W : Type} [CommGroup W] [Finite W] :
    Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_E3RowSL4_le_stabSub_commSub {W : Type} [CommGroup W]
    (L : Subgroup (MulAut W)) : L ≤ stabSub (commSub ⊤ L) := fun l hl =>
  s16h_H5_row_SL2_four_stab_commSub (Subgroup.le_normalizer hl)

private theorem s16h_E3RowSL4_le_stabSub_fixV {W : Type} [CommGroup W]
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

private theorem s16h_E3RowSL4_normalizer_le_stabSub_fixV {W : Type} [CommGroup W]
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

private theorem s16h_E3RowSL4_stabSub_inf {W : Type} [CommGroup W] {U Z : Subgroup W}
    {g : MulAut W} (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) := by
  rw [mem_stabSub] at hU hZ ⊢
  intro x
  exact ⟨fun hx => ⟨(hU x).mp hx.1, (hZ x).mp hx.2⟩,
    fun hx => ⟨(hU x).mpr hx.1, (hZ x).mpr hx.2⟩⟩

private theorem s16h_E3RowSL4_autSec_le_normalizer {W : Type} [CommGroup W]
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

private theorem s16h_E3RowSL4_center_eq_bot_of_isSLn_two {X : Type} [Group X] [Finite X]
    {a : ℕ} (h : IsSLn X 2 a) : Subgroup.center X = ⊥ := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have h2le : 2 ≤ Nat.card K := Finite.one_lt_card
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · exfalso
      rw [h0] at hKcard
      rw [pow_zero] at hKcard
      omega
    · exact hpos
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hKcenter : Subgroup.center ↥(StatedSL 2 K) = ⊥ :=
    CFSG.RankThree.GF2n.Stroth80.center_statedSL_two_eq_bot
  have hcard : Nat.card ↥(Subgroup.center X) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hKcenter]
    simp
  exact Subgroup.card_eq_one.mp hcard

theorem s16h_H5_row_SL2_four_bridge_strong {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = 4)
      (e : Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≃* StdMod (Fin 2) K)
      (D : Subgroup (MulAut (StdMod (Fin 2) K))),
      D = (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ∧
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) =
        natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧
      D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧
      IsElemAbelian q D ∧
      Nat.card D = Nat.card ↥(autSub E (commSub ⊤ L)) := by
  classical
  haveI : Finite (MulAut W) := s16h_E3RowSL4_finite_mulAut
  obtain ⟨hSL, hNat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hNat
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hcenter : Subgroup.center ↥L = ⊥ := s16h_E3RowSL4_center_eq_bot_of_isSLn_two hSL
  have hfaith : L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ :=
    s16h_H5_faithful_on_quotient hc hcenter
  have hLU : L ≤ stabSub (commSub ⊤ L) := s16h_E3RowSL4_le_stabSub_commSub L
  have hLfix : L ≤ stabSub (fixV L) := s16h_E3RowSL4_le_stabSub_fixV L
  have hLZ : L ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun l hl => s16h_E3RowSL4_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_H5_row_SL2_four_stab_commSub (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_E3RowSL4_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun e he => s16h_E3RowSL4_stabSub_inf (hEU he) (hEfix he)
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
    s16h_E3RowSL4_autSec_le_normalizer hLU hLZ hEU hEZ hEN
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

theorem s16h_H5_matHom_range {K : Type} [Field K] :
    (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range =
      linSub (ι := Fin 2) (K := K) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    exact isSemilinear_matAut A
  · intro hg
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg
    exact ⟨A, rfl⟩

theorem s16h_H5_eigenvector_one_of_three_subgroup {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDlin : D ≤ linSub (ι := Fin 2) (K := K)) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 9) :
    ∃ (A : GL (Fin 2) K) (v : Fin 2 → K),
      v ≠ 0 ∧ A ≠ 1 ∧ matHom A ∈ D ∧ A • v = v := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let Dlin : Subgroup (GL (Fin 2) K) := D.comap (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))
  have hrange : D ≤ (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range := by
    rw [s16h_H5_matHom_range]
    exact hDlin
  have hmap : Dlin.map (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) = D :=
    Subgroup.map_comap_eq_self hrange
  have hcardDlin : Nat.card Dlin = 9 := by
    rw [← Subgroup.card_map_of_injective
      (f := (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))) matHom_injective, hmap, hcard]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpgD : IsPGroup 3 D := CFSG.Open.IsElemAbelian.isPGroup hD
  have hpg : IsPGroup 3 Dlin :=
    hpgD.of_equiv ((Subgroup.equivMapOfInjective Dlin
      (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) matHom_injective).trans
        (MulEquiv.subgroupCongr hmap)).symm
  letI : Fintype Dlin := Fintype.ofFinite Dlin
  have hcardK : Fintype.card K = 4 := by rwa [Fintype.card_eq_nat_card]
  have hnot : ¬ 3 ∣ Nat.card (ℙ K (Fin 2 → K)) := by
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
    rw [hcardK, show Fintype.card Dlin = 9 by rw [Fintype.card_eq_nat_card]; exact hcardDlin]
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

theorem s16h_H5_row_SL2_four_le_stabSub_commSub_fixV {W : Type} [CommGroup W]
    (L : Subgroup (MulAut W)) : L ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
  fun l hl => s16h_E3RowSL4_stabSub_inf
    (s16h_H5_row_SL2_four_stab_commSub (Subgroup.le_normalizer hl))
    (s16h_E3RowSL4_le_stabSub_fixV L hl)


theorem s16h_H5_row_SL2_four_stab_fixV {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {g : MulAut W} (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (fixV L) :=
  s16h_E3RowSL4_normalizer_le_stabSub_fixV hg

theorem s16h_H5_row_SL2_four_stab_inf {W : Type} [CommGroup W] {U Z : Subgroup W}
    {g : MulAut W} (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) :=
  s16h_E3RowSL4_stabSub_inf hU hZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
