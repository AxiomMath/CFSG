module

public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAA3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
public import CFSG.GroupTheory.PRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5BridgeO4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2121d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix Pointwise

variable {W : Type} [CommGroup W]

abbrev s16h_H5E3Rkι : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem s16h_H5E3Rk_centralizer_natImage_le_statedScalars {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) : Set (MulAut (StdMod s16h_H5E3Rkι K))) ≤
      natImage (StatedScalars s16h_H5E3Rkι K) := by
  intro g hg
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) :=
    S18.hasScalarCommutant_statedOmegaMinus2 hirr
  let f : (s16h_H5E3Rkι → K) →+ (s16h_H5E3Rkι → K) :=
    AddMonoidHom.mk' (toAddMap g) (fun v w => toAddMap_add g v w)
  have hcomm : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v : s16h_H5E3Rkι → K,
      f ((γ : Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ v) =
        (γ : Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ f v := by
    intro γ hγ v
    have hmem : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ ∈
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) := ⟨_, rfl⟩
    have hc : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g =
        g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    change toAddMap g ((γ : Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ v) =
        (γ : Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ toAddMap g v
    calc toAddMap g ((γ : Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ v)
        = toAddMap (g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩) v := by
          rw [toAddMap_mul, toAddMap_natAut]
      _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g) v := by
          rw [← hc]
      _ = (γ : Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ toAddMap g v := by
          rw [toAddMap_mul, toAddMap_natAut]
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hsingle : (Pi.single (Sum.inl (0 : Fin 1)) (1 : K) : s16h_H5E3Rkι → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 1))
      simpa using this
    refine hsingle ((toAddMap_eq_zero_iff g).mp ?_)
    have h1 : f (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0 := by
      rw [hμ, h0, zero_smul]
    change toAddMap g (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0
    exact h1
  let u : Kˣ := Units.mk0 μ hμ0
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar s16h_H5E3Rkι u, ⟨u, rfl⟩⟩, ?_⟩
  apply toAddMap_injective
  intro v
  rw [toAddMap_natAut]
  change ((Matrix.GeneralLinearGroup.scalar s16h_H5E3Rkι u : GL s16h_H5E3Rkι K) :
      Matrix s16h_H5E3Rkι s16h_H5E3Rkι K) *ᵥ v = toAddMap g v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  rw [Matrix.mulVec_diagonal]
  exact congrFun (hμ v).symm x

private theorem s16h_H5E3Rk_card_statedScalars_natImage {K : Type} [Field K] [Finite K] :
    Nat.card (natImage (StatedScalars s16h_H5E3Rkι K)) = Nat.card K - 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16h_H5E3Rkι K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16h_H5E3Rkι K))
  calc Nat.card (natImage (StatedScalars s16h_H5E3Rkι K))
      = Nat.card ↥(StatedScalars s16h_H5E3Rkι K) :=
        (Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv).symm
    _ = Nat.card Kˣ :=
        (Nat.card_congr (MonoidHom.ofInjective
          (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective
            (ι := s16h_H5E3Rkι) (R := K))).toEquiv).symm
    _ = Nat.card K - 1 := Nat.card_units K

theorem s16h_natNorm_elemAbelian_le_omegaMinus4_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hq7 : q ≠ 7)
    {A' : Subgroup (MulAut (StdMod _ K))}
    (hA : A' ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hE : IsElemAbelian q A') : Nat.card ↥A' ≤ q := by
  let Γ : Subgroup (GL s16h_H5E3Rkι K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3Rkι K)) := natImage Γ
  have hAleN : A' ≤ Subgroup.normalizer (Ω : Set (MulAut (StdMod s16h_H5E3Rkι K))) := hA
  let ψ : ↥A' →* MulAut ↥Ω :=
    (Subgroup.normalizerMonoidHom Ω).comp (Subgroup.inclusion hAleN)
  have hInjNatAut : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInjNatAut
  have hL2 : IsL2 ↥Ω (2 * 3) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
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
      A' ⊓ Subgroup.centralizer (Ω : Set (MulAut (StdMod s16h_H5E3Rkι K))) := by
    rintro x ⟨y, hy, rfl⟩
    have hyker : ψ y = 1 := (MonoidHom.mem_ker).mp hy
    have hmem : Subgroup.inclusion hAleN y ∈ (Subgroup.normalizerMonoidHom Ω).ker := by
      rw [MonoidHom.mem_ker]
      exact hyker
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact ⟨y.2, (Subgroup.mem_subgroupOf.mp hmem)⟩
  have hker_le_scal : CFSG.Open.pRank q ψ.ker ≤
      CFSG.Open.pRank q (natImage (StatedScalars s16h_H5E3Rkι K)) :=
    (CFSG.SectionRank.pRank_le_map hq.one_lt (Subgroup.subtype A')
        (Subgroup.subtype_injective A') ψ.ker).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt
        (hker_map_le.trans (inf_le_right.trans
          (s16h_H5E3Rk_centralizer_natImage_le_statedScalars (K := K) hirr))))
  have hker0 : CFSG.Open.pRank q ψ.ker ≤ 0 := by
    refine hker_le_scal.trans ?_
    have hcard : Nat.card (natImage (StatedScalars s16h_H5E3Rkι K)) = 2 ^ 3 - 1 := by
      rw [s16h_H5E3Rk_card_statedScalars_natImage (K := K), hK]
    refine (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hq (H :=
      natImage (StatedScalars s16h_H5E3Rkι K)) (k := 0) ?_)
    rw [pow_one, hcard]
    norm_num
    exact fun h => hq7 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).1 h)
  have himg_le : CFSG.Open.pRank q ψ.range ≤
      CFSG.Open.pRank q (⊤ : Subgroup (MulAut ↥Ω)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  have hrank' : k ≤ CFSG.Open.pRank q ψ.ker + CFSG.Open.pRank q ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact hrank
  have hna6 : ¬ q ∣ 2 * 3 := by
    intro hd
    rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)
  have hk1 : k ≤ 1 := by
    have h1 := himg_le.trans (hAutRank.2 hna6)
    omega
  calc Nat.card ↥A' = q ^ k := hk
    _ ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hk1
    _ = q := pow_one q

theorem s16h_H5E3_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
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

theorem s16h_H5_row_O4_three_block_one [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :
    s16h_BlockBound A L q 1 := by
  intro E hE hEab
  have hU : E ≤ stabSub (commSub ⊤ L) := by
    intro g hg
    exact s16h_H5E3_commSub_stab (L := L) (g := g) (Subgroup.mem_inf.mp (hE hg)).2
  have hcard := card_autSub_mul (A := E) (U := commSub ⊤ L) hU
  have hb : Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q := by
    obtain ⟨K, hKf, hKfin, hKchar, b, c, hKcard, hirr, D, hDN, hDab, hDcard⟩ :=
      s16h_H5_bridge_omegaMinus4 hc h hq hq2 hE hEab
    letI : Field K := hKf
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    rw [← hDcard]
    exact s16h_natNorm_elemAbelian_le_omegaMinus4_three hKcard hirr hq hq2 hq3 hq7 hDN hDab
  rw [← hcard]
  exact Nat.mul_le_mul_right _ (by simpa using hb)

private theorem s16h_H5E3RowO4b_finite_mulAut [Finite W] : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

theorem s16h_H5E3RowO4b_le_stabSub_fixV (L : Subgroup (MulAut W)) :
    L ≤ stabSub (fixV L) := by
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

theorem s16h_H5E3RowO4b_normalizer_le_stabSub_fixV {L : Subgroup (MulAut W)}
    {g : MulAut W} (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (fixV L) := by
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

theorem s16h_H5E3RowO4b_stabSub_inf {U Z : Subgroup W} {g : MulAut W}
    (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) := by
  rw [mem_stabSub] at hU hZ ⊢
  intro x
  exact ⟨fun hx => ⟨(hU x).mp hx.1, (hZ x).mp hx.2⟩,
    fun hx => ⟨(hU x).mpr hx.1, (hZ x).mpr hx.2⟩⟩

private theorem s16h_H5E3RowO4b_autSec_le_normalizer {L Y : Subgroup (MulAut W)}
    {V C : Subgroup W} (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C) (hYV : Y ≤ stabSub V)
    (hYC : Y ≤ stabSub C) (hYL : Y ≤ normalizer (L : Set (MulAut W))) :
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

theorem s16h_H5_row_O4_three_bridge_strong [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K) (_ : Nat.card K = 2 ^ 3)
      (_ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (e : Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≃* StdMod s16h_H5E3Rkι K)
      (D : Subgroup (MulAut (StdMod s16h_H5E3Rkι K))),
      D = (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ∧
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) =
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) ∧
      D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)) ∧
      IsElemAbelian q D ∧
      Nat.card D = Nat.card ↥(autSub E (commSub ⊤ L)) := by
  classical
  haveI : Finite (MulAut W) := s16h_H5E3RowO4b_finite_mulAut
  obtain ⟨hOm, hNat⟩ := h
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hbc, hreal⟩ := hNat
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have hL2 : IsL2 ↥L (2 * 3) := S18.isL2_of_isOmegaMinus_four (by norm_num) hOm
    exact P22y.center_eq_bot_of_isL2Ev (P22fin.isL2Ev_of_isL2 hL2).1
  have hfaith : L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ :=
    s16h_H5_faithful_on_quotient hc hcenter
  have hLU : L ≤ stabSub (commSub ⊤ L) := fun l hl =>
    s16h_H5E3_commSub_stab (Subgroup.le_normalizer hl)
  have hLfix : L ≤ stabSub (fixV L) := s16h_H5E3RowO4b_le_stabSub_fixV L
  have hLZ : L ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun l hl => s16h_H5E3RowO4b_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_H5E3_commSub_stab (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_H5E3RowO4b_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun e he => s16h_H5E3RowO4b_stabSub_inf (hEU he) (hEfix he)
  have hrealAuto : (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))).Realizes
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
      (⊤ : Subgroup (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))) ⊥ :=
    s16h_realizes_autSec_of_realizes inf_le_left hLU hLZ hfaith hreal
  obtain ⟨π, hπ⟩ := hrealAuto
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia
    (Γ := StatedOmega (StatedQuadMinus 2 K b c)) hπ
  have hπsurj : Function.Surjective π := hπ.1
  have hmapL : (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) =
      natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
    map_congrHom_eq_natImage (StatedOmega (StatedQuadMinus 2 K b c)) hπsurj e he
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
    s16h_H5E3RowO4b_autSec_le_normalizer hLU hLZ hEU hEZ hEN
  have hDnorm : (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ≤
      natNorm (StatedOmega (StatedQuadMinus 2 K b c)) := by
    have h1 : (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ≤
        (normalizer ((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
          Subgroup (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :
            Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))))).map (congrHom e) :=
      Subgroup.map_mono hEnorm
    have h2 : (normalizer ((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
          Subgroup (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :
            Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))))).map (congrHom e) =
        normalizer (((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) :
          Subgroup (MulAut (StdMod s16h_H5E3Rkι K))) : Set (MulAut (StdMod s16h_H5E3Rkι K))) := by
      simpa [congrHom] using Subgroup.map_equiv_normalizer_eq
        (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) (MulAut.congr e)
    rw [h2, hmapL] at h1
    simpa [natNorm] using h1
  refine ⟨K, hKf, hKfin, b, c, hKcard, hbc, e,
    (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e), rfl, hmapL,
    hDnorm, IsElemAbelian.map hEsec (congrHom e), ?_⟩
  rw [Subgroup.card_map_of_injective (congrHom_injective e)]
  exact (s16h_H5_card_autSub_eq_autSec hc hE).symm

theorem s16h_H5_omegaMinusFour_q_sq_order {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {q : ℕ} (hq : q = 3 ∨ q = 7)
    {D : Subgroup (MulAut (StdMod s16h_H5E3Rkι K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian q D) (hDcard : Nat.card ↥D = q ^ 2) :
    ∃ y ∈ D, y ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) ∧ orderOf y = q := by
  classical
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3Rkι K)) :=
    natImage (StatedOmega (StatedQuadMinus 2 K b c))
  have hqprime : q.Prime := by rcases hq with h | h <;> subst h <;> norm_num
  have hmeet : Nat.card ↥(D ⊓ Ω) = q :=
    s16h_H5_omegaMinusFour_q_sq_order_meet hK hirr hq hDN hDab hDcard
  have hnt : Nontrivial ↥(D ⊓ Ω) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hmeet]
    rcases hq with h | h <;> omega
  obtain ⟨y, hyne⟩ := exists_ne (1 : ↥(D ⊓ Ω))
  have hdvd : orderOf y ∣ q := by
    have h := orderOf_dvd_natCard y
    rwa [hmeet] at h
  have hne1 : orderOf y ≠ 1 := fun h => hyne (orderOf_eq_one_iff.mp h)
  have hyord : orderOf y = q := by
    rcases hqprime.eq_one_or_self_of_dvd (orderOf y) hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  refine ⟨y.1, (Subgroup.mem_inf.mp y.2).1, (Subgroup.mem_inf.mp y.2).2, ?_⟩
  show orderOf y.1 = q
  rw [← Subgroup.orderOf_mk y.1 y.2]
  exact hyord

theorem s16h_H5_omegaMinusFour_q_sq_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {q : ℕ} (hq : q = 3 ∨ q = 7)
    {y z : MulAut (StdMod s16h_H5E3Rkι K)}
    (hy : y ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)))
    (hz : z ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)))
    (hyq : orderOf y = q) (hzq : orderOf z = q) :
    ∃ g ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), ∃ j : ℕ, g * y * g⁻¹ = z ^ j := by
  classical
  let Γ : Subgroup (GL s16h_H5E3Rkι K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3Rkι K)) := natImage Γ
  have hqprime : q.Prime := by rcases hq with h | h <;> subst h <;> norm_num
  have hq2 : q ≠ 2 := by rcases hq with h | h <;> omega
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : IsL2 ↥Ω (2 * 3) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  have hm : CFSG.Open.StatedClassicalModel ↥Ω .PSL 2 2 (2 * 3) :=
    hL2.statedClassicalModel (by decide)
  have hprank : CFSG.Open.pRank q (⊤ : Subgroup ↥Ω) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hm hqprime hq2
  let yΩ : ↥Ω := ⟨y, hy⟩
  let zΩ : ↥Ω := ⟨z, hz⟩
  have hyΩord : orderOf yΩ = q := by
    change orderOf (⟨y, hy⟩ : ↥Ω) = q
    rw [Subgroup.orderOf_mk]
    exact hyq
  have hzΩord : orderOf zΩ = q := by
    change orderOf (⟨z, hz⟩ : ↥Ω) = q
    rw [Subgroup.orderOf_mk]
    exact hzq
  have hPy : IsPGroup q (Subgroup.zpowers yΩ) :=
    IsPGroup.of_card (p := q) (n := 1) (by rw [Nat.card_zpowers, hyΩord, pow_one])
  obtain ⟨Py, hyPy⟩ := hPy.exists_le_sylow
  have hPz : IsPGroup q (Subgroup.zpowers zΩ) :=
    IsPGroup.of_card (p := q) (n := 1) (by rw [Nat.card_zpowers, hzΩord, pow_one])
  obtain ⟨Pz, hzPz⟩ := hPz.exists_le_sylow
  have hPzcyc : IsCyclic ↥Pz := by
    refine CFSG.isCyclic_of_pRank_le_one hqprime hq2 Pz.isPGroup' ?_
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Pz : Subgroup ↥Ω)]
    exact (CFSG.SectionRank.pRank_mono hqprime.one_lt le_top).trans hprank
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := ↥Ω) Py Pz
  have hyPymem : yΩ ∈ (Py : Subgroup ↥Ω) := hyPy (Subgroup.mem_zpowers yΩ)
  have hzPzmem : zΩ ∈ (Pz : Subgroup ↥Ω) := hzPz (Subgroup.mem_zpowers zΩ)
  have hconjPz : (MulAut.conj g) yΩ ∈ (Pz : Subgroup ↥Ω) := by
    have h2 : (MulAut.conj g) • (Py : Subgroup ↥Ω) = (Pz : Subgroup ↥Ω) := by
      have h := congrArg (fun P : Sylow q ↥Ω => (P : Subgroup ↥Ω)) hg
      rwa [Sylow.coe_subgroup_smul] at h
    have h1 : (MulAut.conj g) yΩ ∈ (MulAut.conj g) • (Py : Subgroup ↥Ω) :=
      Subgroup.smul_mem_pointwise_smul_iff.mpr hyPymem
    rwa [h2] at h1
  let wPz : ↥Pz := ⟨(MulAut.conj g) yΩ, hconjPz⟩
  let zPz : ↥Pz := ⟨zΩ, hzPzmem⟩
  have hzPzord : orderOf zPz = q := by
    change orderOf (⟨zΩ, hzPzmem⟩ : ↥Pz) = q
    rw [Subgroup.orderOf_mk]
    exact hzΩord
  have hwPzord : orderOf wPz = q := by
    change orderOf (⟨(MulAut.conj g) yΩ, hconjPz⟩ : ↥Pz) = q
    rw [Subgroup.orderOf_mk]
    have hconjord : orderOf ((MulAut.conj g) yΩ) = orderOf yΩ := by
      rw [MulAut.conj_apply]
      have hsc : g * yΩ = (g * yΩ * g⁻¹) * g := by group
      exact (SemiconjBy.orderOf_eq g hsc).symm
    rw [hconjord, hyΩord]
  have hsub : Subgroup.zpowers wPz = Subgroup.zpowers zPz := by
    rw [IsCyclic.subgroup_eq_iff_card_eq (G := ↥Pz)]
    rw [Nat.card_zpowers, Nat.card_zpowers, hwPzord, hzPzord]
  have hsubΩ : Subgroup.zpowers ((MulAut.conj g) yΩ) = Subgroup.zpowers zΩ := by
    have h1 : (Subgroup.zpowers wPz).map (Subgroup.subtype Pz) =
        Subgroup.zpowers ((MulAut.conj g) yΩ) := by
      rw [MonoidHom.map_zpowers]
      rfl
    have h2 : (Subgroup.zpowers zPz).map (Subgroup.subtype Pz) =
        Subgroup.zpowers zΩ := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← h1, ← h2, hsub]
  have hwmemΩ : (MulAut.conj g) yΩ ∈ Subgroup.zpowers zΩ := by
    rw [← hsubΩ]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp
    ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (isOfFinOrder_of_finite zΩ)).mp hwmemΩ)
  refine ⟨g, g.2, j, ?_⟩
  have h2 := congrArg (Subgroup.subtype Ω) hj
  rw [map_pow] at h2
  have h3 : Subgroup.subtype Ω zΩ = z := rfl
  have h4 : Subgroup.subtype Ω ((MulAut.conj g) yΩ) = g * y * g⁻¹ := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl
  rw [h3, h4] at h2
  exact h2.symm

theorem s16h_H5_omegaMinusFour_q_sq_stab {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {q : ℕ} (hq : q = 3 ∨ q = 7) (v : StdMod s16h_H5E3Rkι K) (hv : v ≠ 1)
    (hcase : q = 3 ∨ StatedQuadMinus 2 K b c (Multiplicative.toAdd v) ≠ 0) :
    ∃ z ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), orderOf z = q ∧ z v = v := by
  classical
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3Rkι K)) :=
    natImage (StatedOmega (StatedQuadMinus 2 K b c))
  have hqprime : q.Prime := by rcases hq with h | h <;> subst h <;> norm_num
  haveI : Fact q.Prime := ⟨hqprime⟩
  let S : Subgroup (MulAut (StdMod s16h_H5E3Rkι K)) :=
    Ω ⊓ MulAction.stabilizer (MulAut (StdMod s16h_H5E3Rkι K)) v
  have hdvd : q ∣ Nat.card ↥S :=
    s16h_H5_omegaMinusFour_stab_card hK hirr hq v hv hcase
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hdvd
  refine ⟨z.1, (Subgroup.mem_inf.mp z.2).1, ?_, ?_⟩
  · show orderOf z.1 = q
    rw [← Subgroup.orderOf_mk z.1 z.2]
    exact hz
  · have hzv : z.1 ∈ MulAction.stabilizer (MulAut (StdMod s16h_H5E3Rkι K)) v :=
      (Subgroup.mem_inf.mp z.2).2
    rwa [MulAction.mem_stabilizer_iff] at hzv

theorem s16h_H5_omegaMinusFour_q_sq_sing {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5E3Rkι K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 7 D) (hDcard : Nat.card ↥D = 7 ^ 2)
    (v : StdMod s16h_H5E3Rkι K) (hv : v ≠ 1)
    (hQv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0) :
    ∃ g ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), ∃ d ∈ D, d ≠ 1 ∧
      (g * d * g⁻¹) v = v := by
  classical
  let Γ : Subgroup (GL s16h_H5E3Rkι K) := StatedOmega (StatedQuadMinus 2 K b c)
  obtain ⟨u, hu, hQu, d, hd, hdne, hdu⟩ :=
    s16h_H5_omegaMinusFour_singular_common_fix hK hirr hDN hDab hDcard
  have hu0 : Multiplicative.toAdd u ≠ 0 := fun h =>
    hu (by simpa using congrArg Multiplicative.ofAdd h)
  have hv0 : Multiplicative.toAdd v ≠ 0 := fun h =>
    hv (by simpa using congrArg Multiplicative.ofAdd h)
  have hQu' : CFSG.LieType.Universal.Spin.quadMinus 2 K b c (Multiplicative.toAdd u) = 0 := by
    rw [congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) (Multiplicative.toAdd u)]
    exact hQu
  have hQv' : CFSG.LieType.Universal.Spin.quadMinus 2 K b c (Multiplicative.toAdd v) = 0 := by
    rw [congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) (Multiplicative.toAdd v)]
    exact hQv
  obtain ⟨A, hA, hAu⟩ :=
    CFSG.RankThree.GF2n.Stroth80.omegaMinusFourSingularTrans_holds K b c hirr
      (Multiplicative.toAdd u) (Multiplicative.toAdd v) hu0 hv0 hQu' hQv'
  refine ⟨natAut Γ ⟨A, hA⟩, ⟨⟨A, hA⟩, rfl⟩, d, hd, hdne, ?_⟩
  have hgu : natAut Γ ⟨A, hA⟩ u = v := by
    have h2 := toAddMap_natAut Γ ⟨A, hA⟩ (Multiplicative.toAdd u)
    rw [hAu] at h2
    simpa using h2
  have hginv : (natAut Γ ⟨A, hA⟩)⁻¹ v = u := by
    rw [← hgu, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  rw [MulAut.mul_apply, MulAut.mul_apply, hginv, hdu, hgu]

theorem s16h_H5_omegaMinusFour_q_sq_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {q : ℕ} (hq : q = 3 ∨ q = 7)
    {D : Subgroup (MulAut (StdMod s16h_H5E3Rkι K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian q D) (hDcard : Nat.card ↥D = q ^ 2) :
    ∀ v : StdMod s16h_H5E3Rkι K, v ≠ 1 →
      ∃ g ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), ∃ d ∈ D, d ≠ 1 ∧
        (g * d * g⁻¹) v = v := by
  intro v hv
  have hpow : ∀ (z : MulAut (StdMod s16h_H5E3Rkι K)) (j : ℕ), z v = v → (z ^ j) v = v := by
    intro z j hz
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hz, ih]
  rcases hq with rfl | rfl
  · obtain ⟨y, hyD, hyΩ, hyord⟩ :=
      s16h_H5_omegaMinusFour_q_sq_order hK hirr (q := 3) (Or.inl rfl) hDN hDab hDcard
    obtain ⟨z, hzΩ, hzord, hzfix⟩ :=
      s16h_H5_omegaMinusFour_q_sq_stab hK hirr (q := 3) (Or.inl rfl) v hv (Or.inl rfl)
    obtain ⟨g, hgΩ, j, hgj⟩ :=
      s16h_H5_omegaMinusFour_q_sq_conj hK hirr (q := 3) (Or.inl rfl) hyΩ hzΩ hyord hzord
    refine ⟨g, hgΩ, y, hyD, ?_, ?_⟩
    · intro h1
      rw [h1, orderOf_one] at hyord
      exact absurd hyord (by norm_num)
    · rw [hgj]
      exact hpow z j hzfix
  · obtain ⟨y, hyD, hyΩ, hyord⟩ :=
      s16h_H5_omegaMinusFour_q_sq_order hK hirr (q := 7) (Or.inr rfl) hDN hDab hDcard
    by_cases hQv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0
    · exact s16h_H5_omegaMinusFour_q_sq_sing hK hirr hDN hDab hDcard v hv hQv
    · obtain ⟨z, hzΩ, hzord, hzfix⟩ :=
        s16h_H5_omegaMinusFour_q_sq_stab hK hirr (q := 7) (Or.inr rfl) v hv (Or.inr hQv)
      obtain ⟨g, hgΩ, j, hgj⟩ :=
        s16h_H5_omegaMinusFour_q_sq_conj hK hirr (q := 7) (Or.inr rfl) hyΩ hzΩ hyord hzord
      refine ⟨g, hgΩ, y, hyD, ?_, ?_⟩
      · intro h1
        rw [h1, orderOf_one] at hyord
        exact absurd hyord (by norm_num)
      · rw [hgj]
        exact hpow z j hzfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
