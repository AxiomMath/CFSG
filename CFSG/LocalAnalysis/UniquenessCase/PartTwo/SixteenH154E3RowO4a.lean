module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowO4a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

private abbrev s16h_iota : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem s16h_e3_o4a_centralizer_natImage_le_statedScalars {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) : Set (MulAut (StdMod s16h_iota K))) ≤
      natImage (StatedScalars s16h_iota K) := by
  intro g hg
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) :=
    S18.hasScalarCommutant_statedOmegaMinus2 hirr
  let f : (s16h_iota → K) →+ (s16h_iota → K) :=
    AddMonoidHom.mk' (toAddMap g) (fun v w => toAddMap_add g v w)
  have hcomm : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v : s16h_iota → K,
      f ((γ : Matrix s16h_iota s16h_iota K) *ᵥ v) =
        (γ : Matrix s16h_iota s16h_iota K) *ᵥ f v := by
    intro γ hγ v
    have hmem : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ ∈
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) := ⟨_, rfl⟩
    have hc : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g =
        g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    change toAddMap g ((γ : Matrix s16h_iota s16h_iota K) *ᵥ v) =
        (γ : Matrix s16h_iota s16h_iota K) *ᵥ toAddMap g v
    calc toAddMap g ((γ : Matrix s16h_iota s16h_iota K) *ᵥ v)
        = toAddMap (g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩) v := by
          rw [toAddMap_mul, toAddMap_natAut]
      _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g) v := by
          rw [← hc]
      _ = (γ : Matrix s16h_iota s16h_iota K) *ᵥ toAddMap g v := by
          rw [toAddMap_mul, toAddMap_natAut]
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hsingle : (Pi.single (Sum.inl (0 : Fin 1)) (1 : K) : s16h_iota → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 1))
      simpa using this
    refine hsingle ((toAddMap_eq_zero_iff g).mp ?_)
    have h1 : f (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0 := by
      rw [hμ, h0, zero_smul]
    change toAddMap g (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0
    exact h1
  let u : Kˣ := Units.mk0 μ hμ0
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar s16h_iota u, ⟨u, rfl⟩⟩, ?_⟩
  apply toAddMap_injective
  intro v
  rw [toAddMap_natAut]
  change ((Matrix.GeneralLinearGroup.scalar s16h_iota u : GL s16h_iota K) :
      Matrix s16h_iota s16h_iota K) *ᵥ v = toAddMap g v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  rw [Matrix.mulVec_diagonal]
  exact congrFun (hμ v).symm x

private theorem s16h_e3_o4a_card_statedScalars_natImage {K : Type} [Field K] [Finite K] :
    Nat.card (natImage (StatedScalars s16h_iota K)) = Nat.card K - 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16h_iota K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16h_iota K))
  calc Nat.card (natImage (StatedScalars s16h_iota K))
      = Nat.card ↥(StatedScalars s16h_iota K) :=
        (Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv).symm
    _ = Nat.card Kˣ :=
        (Nat.card_congr (MonoidHom.ofInjective
          (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := s16h_iota)
            (R := K))).toEquiv).symm
    _ = Nat.card K - 1 := Nat.card_units K

private theorem s16h_natNorm_elemAbelian_le_omegaMinus4_one {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hK : Nat.card K = 2 ^ 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) {A' : Subgroup (MulAut (StdMod s16h_iota K))}
    (hA : A' ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hE : IsElemAbelian q A') : Nat.card ↥A' ≤ q := by
  let Γ : Subgroup (GL s16h_iota K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_iota K)) := natImage Γ
  have hAleN : A' ≤ Subgroup.normalizer (Ω : Set (MulAut (StdMod s16h_iota K))) := hA
  let ψ : ↥A' →* MulAut ↥Ω :=
    (Subgroup.normalizerMonoidHom Ω).comp (Subgroup.inclusion hAleN)
  have hInjNatAut : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInjNatAut
  have hL2 : IsL2 ↥Ω 4 :=
    uc22p22d_isL2_of_omegaMinus4 (X := ↥Ω) (k := 2) (by norm_num) hK b c hirr eImg.symm
  have hAutRank := uc22p2121d_pRank_mulAut_l2 hL2 hq hq2
  have hEtop : IsElemAbelian q (⊤ : Subgroup ↥A') := by
    rw [← Subgroup.subgroupOf_self]
    exact hE.subgroupOf A'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    (show IsPGroup q ↥A' from fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩)
  have hrank := CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank
    q hq ψ hEtop k (by rw [Subgroup.card_top]; exact hk)
  have hker_map_le : ψ.ker.map (Subgroup.subtype A') ≤
      A' ⊓ Subgroup.centralizer (Ω : Set (MulAut (StdMod s16h_iota K))) := by
    rintro x ⟨y, hy, rfl⟩
    have hyker : ψ y = 1 := (MonoidHom.mem_ker).mp hy
    have hmem : Subgroup.inclusion hAleN y ∈ (Subgroup.normalizerMonoidHom Ω).ker := by
      rw [MonoidHom.mem_ker]
      exact hyker
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact ⟨y.2, (Subgroup.mem_subgroupOf.mp hmem)⟩
  have hker_le_scal : CFSG.Open.pRank q ψ.ker ≤
      CFSG.Open.pRank q (natImage (StatedScalars s16h_iota K)) :=
    (CFSG.SectionRank.pRank_le_map hq.one_lt (Subgroup.subtype A')
        (Subgroup.subtype_injective A') ψ.ker).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt
        (hker_map_le.trans (inf_le_right.trans
          (s16h_e3_o4a_centralizer_natImage_le_statedScalars (K := K) hirr))))
  have hscal0 : CFSG.Open.pRank q (natImage (StatedScalars s16h_iota K)) ≤ 0 := by
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hq ?_
    rw [pow_one, s16h_e3_o4a_card_statedScalars_natImage (K := K), hK,
      show 2 ^ 2 - 1 = 3 by norm_num]
    exact fun hd => hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hd)
  have himg_le : CFSG.Open.pRank q ψ.range ≤
      CFSG.Open.pRank q (⊤ : Subgroup (MulAut ↥Ω)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  have hrank' : k ≤ CFSG.Open.pRank q ψ.ker + CFSG.Open.pRank q ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact hrank
  have hk1 : k ≤ 1 := by
    have hna2 : ¬ q ∣ 4 := by
      intro hd
      have hd' : q ∣ 2 ^ 2 := by rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at hd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd'))
    have h1 := hAutRank.2 hna2
    omega
  calc Nat.card ↥A' = q ^ k := hk
    _ ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hk1
    _ = q := pow_one q

private theorem s16h_e3_o4a_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
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

theorem s16h_H5_row_O4_two_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) : s16h_BlockBound A L q 1 := by
  intro E hE hEab
  obtain ⟨K, hKf, hKfin, hKchar, b, c, hKcard, hirr, D, hDN, hDab, hDcard⟩ :=
    s16h_H5_bridge_omegaMinus4 hc h hq hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hU : E ≤ stabSub (commSub ⊤ L) := fun g hg =>
    s16h_e3_o4a_commSub_stab (L := L) (g := g) (Subgroup.mem_inf.mp (hE hg)).2
  have hcard := card_autSub_mul (A := E) (U := commSub ⊤ L) hU
  have hle : Nat.card ↥D ≤ q :=
    s16h_natNorm_elemAbelian_le_omegaMinus4_one (K := K) (b := b) (c := c)
      hKcard hirr hq hq2 hq3 hDN hDab
  rw [hDcard] at hle
  rw [← hcard]
  simpa [pow_one] using
    Nat.mul_le_mul_right (Nat.card ↥(E ⊓ centSub (commSub ⊤ L))) hle

theorem s16h_H5_row_O4_two_fix {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ : commSub ⊤ L ⊓ fixV L = ⊥) : s16h_H5Fix A L 3 := by
  intro E hE hEab hEcard w hw hwne
  classical
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZdef
  have hZbot : Z = ⊥ := by simpa [U, Z] using hZ
  obtain ⟨K, hKf, hKfin, b, c, hKcard, hirr, e, D, hDeq, hmapL, hDnorm, hDab, hDcard⟩ :=
    s16h_H5_row_O4_two_bridge_strong hc h (q := 3) Nat.prime_three (by norm_num) hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by norm_num) hKcard
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := fun e he => s16h_e3_o4a_commSub_stab (L := L) (g := e) (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_H5O4a_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub Z := fun e he =>
    s16h_H5O4a_stabSub_inf (hEU he) (hEfix he)
  have hLU : L ≤ stabSub U := fun l hl =>
    s16h_e3_o4a_commSub_stab (Subgroup.le_normalizer hl)
  have hLfix : L ≤ stabSub (fixV L) := s16h_H5O4a_le_stabSub_fixV L
  have hLZ : L ≤ stabSub Z := fun l hl =>
    s16h_H5O4a_stabSub_inf (hLU hl) (hLfix hl)
  set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀def
  have hX₀U : X₀ ≤ stabSub U := inf_le_left
  have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
  have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
  have hLX₀ : L ≤ X₀ := le_inf hLU hLZ
  have hDsize : Nat.card ↥D = 3 ^ 2 := by
    have hcardE := card_autSub_mul (A := E) (U := U) hEU
    have hb : Nat.card ↥(autSub E U) ≤ 3 ^ 2 :=
      s16h_H5_row_O4_two_rank hc h 3 Nat.prime_three (by norm_num) E hE hEab
    have hge : 3 ^ 2 ≤ Nat.card ↥(autSub E U) := by
      have hpre : 3 ^ 2 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card E := hEcard
      rw [← hcardE] at hpre
      exact Nat.le_of_mul_le_mul_right hpre Nat.card_pos
    rw [show Nat.card ↥D = Nat.card ↥(autSub E U) from by simpa using hDcard]
    exact le_antisymm hb hge
  let wU : U := ⟨w, hw⟩
  let wbar : Sec U Z := QuotientGroup.mk wU
  have hwbarne : wbar ≠ 1 := by
    intro h1
    have hmem : wU ∈ Z.subgroupOf U := (QuotientGroup.eq_one_iff wU).1 h1
    have hwZ : w ∈ Z := Subgroup.mem_subgroupOf.mp hmem
    exact hwne (by simpa [hZbot, wU] using hwZ)
  let v : StdMod s16h_H5O4aIota K := e wbar
  have hv : v ≠ 1 := by
    change e wbar ≠ 1
    intro h1
    exact hwbarne (e.injective (by rw [h1, map_one]))
  obtain ⟨g, hg, d, hd, hdne, hgfixv⟩ :=
    s16h_H5_omegaMinusFour_two_q_sq_fix hKcard hirr hDnorm hDab hDsize v hv
  have hd_mem : d ∈ (autSec E U Z).map (congrHom e) := by rw [← hDeq]; exact hd
  obtain ⟨d₀, hd₀mem, hd₀eq⟩ := Subgroup.mem_map.mp hd_mem
  have hg_mem : g ∈ (autSec L U Z).map (congrHom e) := by rw [hmapL]; exact hg
  obtain ⟨g₀, hg₀mem, hg₀eq⟩ := Subgroup.mem_map.mp hg_mem
  have hEsecEq : (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
      autSec E U Z :=
    CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀
  have hd₀mem' : d₀ ∈ (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) := by
    rw [hEsecEq]; exact hd₀mem
  obtain ⟨b0, hb0E, hb0sec⟩ := Subgroup.mem_map.mp hd₀mem'
  have hLsecEq : (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
      autSec L U Z :=
    CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hLX₀
  have hg₀mem' : g₀ ∈ (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) := by
    rw [hLsecEq]; exact hg₀mem
  obtain ⟨l0, hl0L, hl0sec⟩ := Subgroup.mem_map.mp hg₀mem'
  have hfix_g0d0 : (g₀ * d₀ * g₀⁻¹) wbar = wbar := by
    have h1 : g = congrHom e g₀ := hg₀eq.symm
    have h2 : d = congrHom e d₀ := hd₀eq.symm
    rw [h1, h2] at hgfixv
    have hmap : congrHom e g₀ * congrHom e d₀ * (congrHom e g₀)⁻¹ =
        congrHom e (g₀ * d₀ * g₀⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [hmap] at hgfixv
    exact e.injective (by simpa [congrHom_apply, v, MulAut.mul_apply] using hgfixv)
  have hfix_sec : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z (l0 * b0 * l0⁻¹) wbar = wbar := by
    have h1 : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z (l0 * b0 * l0⁻¹) =
        g₀ * d₀ * g₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, hl0sec, hb0sec]
    rw [h1]
    exact hfix_g0d0
  have hmemU : (((l0 * b0 * l0⁻¹) : X₀) : MulAut W) w ∈ U :=
    (hX₀U (l0 * b0 * l0⁻¹).2 w).2 hw
  have hfix_wU : (((l0 * b0 * l0⁻¹) : X₀) : MulAut W) w = w := by
    have hstep : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z (l0 * b0 * l0⁻¹) wbar =
        QuotientGroup.mk (⟨(((l0 * b0 * l0⁻¹) : X₀) : MulAut W) w, hmemU⟩ : U) := by
      rw [show wbar = (QuotientGroup.mk wU : Sec U Z) from rfl]
      rw [CFSG.Quasithin.B5.secHom_mk]
    have hmk : (QuotientGroup.mk (⟨(((l0 * b0 * l0⁻¹) : X₀) : MulAut W) w, hmemU⟩ : U) :
        Sec U Z) = wbar := hstep ▸ hfix_sec
    have hmem := (CFSG.Quasithin.mk_eq_mk_iff (U := Z.subgroupOf U) _ _).1 hmk
    have h1 : (⟨(((l0 * b0 * l0⁻¹) : X₀) : MulAut W) w, hmemU⟩ : U) *
        (⟨w, hw⟩ : U)⁻¹ = 1 := by
      have h2 : (⟨(((l0 * b0 * l0⁻¹) : X₀) : MulAut W) w, hmemU⟩ : U) *
          (⟨w, hw⟩ : U)⁻¹ ∈ (⊥ : Subgroup U) := by
        simpa [hZbot] using hmem
      exact Subgroup.mem_bot.mp h2
    exact Subtype.ext_iff.mp (mul_inv_eq_one.mp h1)
  have hbcent : (((b0 : X₀) : MulAut W)) ∉ centSub U := by
    intro hbc
    have hcentsec : (((b0 : X₀) : MulAut W)) ∈ centSec U Z := centSub_le_centSec U Z hbc
    have hker : (b0 : X₀) ∈ (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z).ker :=
      (CFSG.Quasithin.B5.mem_ker_secHom X₀ hX₀U hX₀Z (b0 : X₀)).2 hcentsec
    have hb0one : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z (b0 : X₀) = 1 :=
      MonoidHom.mem_ker.mp hker
    have hd₀one : d₀ = 1 := by rw [← hb0sec]; exact hb0one
    exact hdne (by rw [← hd₀eq, hd₀one, map_one])
  have hbE : (((b0 : X₀) : MulAut W)) ∈ E := Subgroup.mem_subgroupOf.mp hb0E
  have hl0L' : (((l0 : X₀) : MulAut W)) ∈ L := Subgroup.mem_subgroupOf.mp hl0L
  exact ⟨((l0 : X₀) : MulAut W), hl0L', ((b0 : X₀) : MulAut W), hbE, hbcent, hfix_wU⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
