module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aTW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aI
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2121d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix Pointwise

variable {W : Type} [CommGroup W]

abbrev s16h_H5O4aIota : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem s16h_H5O4a_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
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

private theorem s16h_H5O4a_finite_mulAut [Finite W] : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

theorem s16h_H5O4a_le_stabSub_fixV (L : Subgroup (MulAut W)) :
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

theorem s16h_H5O4a_normalizer_le_stabSub_fixV {L : Subgroup (MulAut W)}
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

theorem s16h_H5O4a_stabSub_inf {U Z : Subgroup W} {g : MulAut W}
    (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) := by
  rw [mem_stabSub] at hU hZ ⊢
  intro x
  exact ⟨fun hx => ⟨(hU x).mp hx.1, (hZ x).mp hx.2⟩,
    fun hx => ⟨(hU x).mpr hx.1, (hZ x).mpr hx.2⟩⟩

private theorem s16h_H5O4a_autSec_le_normalizer {L Y : Subgroup (MulAut W)}
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

theorem s16h_H5_row_O4_two_bridge_strong [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K) (_ : Nat.card K = 2 ^ 2)
      (_ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (e : Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≃* StdMod s16h_H5O4aIota K)
      (D : Subgroup (MulAut (StdMod s16h_H5O4aIota K))),
      D = (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) ∧
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e) =
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) ∧
      D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)) ∧
      IsElemAbelian q D ∧
      Nat.card D = Nat.card ↥(autSub E (commSub ⊤ L)) := by
  classical
  haveI : Finite (MulAut W) := s16h_H5O4a_finite_mulAut
  obtain ⟨hOm, hNat⟩ := h
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hbc, hreal⟩ := hNat
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have hL2 : IsL2 ↥L (2 * 2) := S18.isL2_of_isOmegaMinus_four (by norm_num) hOm
    exact P22y.center_eq_bot_of_isL2Ev (P22fin.isL2Ev_of_isL2 hL2).1
  have hfaith : L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ :=
    s16h_H5_faithful_on_quotient hc hcenter
  have hLU : L ≤ stabSub (commSub ⊤ L) := fun l hl =>
    s16h_H5O4a_commSub_stab (Subgroup.le_normalizer hl)
  have hLfix : L ≤ stabSub (fixV L) := s16h_H5O4a_le_stabSub_fixV L
  have hLZ : L ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun l hl => s16h_H5O4a_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_H5O4a_commSub_stab (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_H5O4a_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun e he => s16h_H5O4a_stabSub_inf (hEU he) (hEfix he)
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
    s16h_H5O4a_autSec_le_normalizer hLU hLZ hEU hEZ hEN
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
          Subgroup (MulAut (StdMod s16h_H5O4aIota K))) :
          Set (MulAut (StdMod s16h_H5O4aIota K))) := by
      simpa [congrHom] using Subgroup.map_equiv_normalizer_eq
        (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) (MulAut.congr e)
    rw [h2, hmapL] at h1
    simpa [natNorm] using h1
  refine ⟨K, hKf, hKfin, b, c, hKcard, hbc, e,
    (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e), rfl, hmapL,
    hDnorm, IsElemAbelian.map hEsec (congrHom e), ?_⟩
  rw [Subgroup.card_map_of_injective (congrHom_injective e)]
  exact (s16h_H5_card_autSub_eq_autSec hc hE).symm


private theorem s16h_H5O4a_centralizer_natImage_le_statedScalars {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
          Set (MulAut (StdMod s16h_H5O4aIota K))) ≤
      natImage (StatedScalars s16h_H5O4aIota K) := by
  intro g hg
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) :=
    S18.hasScalarCommutant_statedOmegaMinus2 hirr
  let f : (s16h_H5O4aIota → K) →+ (s16h_H5O4aIota → K) :=
    AddMonoidHom.mk' (toAddMap g) (fun v w => toAddMap_add g v w)
  have hcomm : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v : s16h_H5O4aIota → K,
      f ((γ : Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ v) =
        (γ : Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ f v := by
    intro γ hγ v
    have hmem : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ ∈
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) := ⟨_, rfl⟩
    have hc : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g =
        g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    change toAddMap g ((γ : Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ v) =
        (γ : Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ toAddMap g v
    calc toAddMap g ((γ : Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ v)
        = toAddMap (g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩) v := by
          rw [toAddMap_mul, toAddMap_natAut]
      _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g) v := by
          rw [← hc]
      _ = (γ : Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ toAddMap g v := by
          rw [toAddMap_mul, toAddMap_natAut]
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hsingle : (Pi.single (Sum.inl (0 : Fin 1)) (1 : K) : s16h_H5O4aIota → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 1))
      simpa using this
    refine hsingle ((toAddMap_eq_zero_iff g).mp ?_)
    have h1 : f (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0 := by
      rw [hμ, h0, zero_smul]
    change toAddMap g (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0
    exact h1
  let u : Kˣ := Units.mk0 μ hμ0
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar s16h_H5O4aIota u, ⟨u, rfl⟩⟩, ?_⟩
  apply toAddMap_injective
  intro v
  rw [toAddMap_natAut]
  change ((Matrix.GeneralLinearGroup.scalar s16h_H5O4aIota u : GL s16h_H5O4aIota K) :
      Matrix s16h_H5O4aIota s16h_H5O4aIota K) *ᵥ v = toAddMap g v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  rw [Matrix.mulVec_diagonal]
  exact congrFun (hμ v).symm x

private theorem s16h_H5O4a_card_statedScalars_natImage {K : Type} [Field K] [Finite K] :
    Nat.card (natImage (StatedScalars s16h_H5O4aIota K)) = Nat.card K - 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16h_H5O4aIota K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16h_H5O4aIota K))
  calc Nat.card (natImage (StatedScalars s16h_H5O4aIota K))
      = Nat.card ↥(StatedScalars s16h_H5O4aIota K) :=
        (Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv).symm
    _ = Nat.card Kˣ :=
        (Nat.card_congr (MonoidHom.ofInjective
          (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := s16h_H5O4aIota)
            (R := K))).toEquiv).symm
    _ = Nat.card K - 1 := Nat.card_units K

private theorem s16h_H5O4a_scalars_commute_natImage {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {mu g : MulAut (StdMod ι K)}
    (hmu : mu ∈ natImage (StatedScalars ι K)) (hg : g ∈ natImage Γ) : mu * g = g * mu := by
  obtain ⟨u, rfl⟩ := hmu
  obtain ⟨γ, rfl⟩ := hg
  obtain ⟨s, hs⟩ := u.2
  change matHom u.1 * matHom γ.1 = matHom γ.1 * matHom u.1
  rw [← map_mul, ← map_mul]
  congr 1
  rw [← hs]
  exact Matrix.GeneralLinearGroup.scalar_commute s γ.1

private theorem s16h_H5_omegaMinusFour_two_scalars_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5O4aIota K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 3 D) (hDcard : Nat.card ↥D = 3 ^ 2) :
    natImage (StatedScalars s16h_H5O4aIota K) ≤ D := by
  classical
  let Γ : Subgroup (GL s16h_H5O4aIota K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5O4aIota K)) := natImage Γ
  let C : Subgroup (MulAut (StdMod s16h_H5O4aIota K)) :=
    natImage (StatedScalars s16h_H5O4aIota K)
  have hcent : Subgroup.centralizer (Ω : Set (MulAut (StdMod s16h_H5O4aIota K))) = C := by
    apply le_antisymm
    · exact s16h_H5O4a_centralizer_natImage_le_statedScalars (K := K) hirr
    · rintro g ⟨u, rfl⟩ x hx
      exact (s16h_H5O4a_scalars_commute_natImage (Γ := Γ) ⟨u, rfl⟩ hx).symm
  have hCcard : Nat.card C = 3 := by
    show Nat.card (natImage (StatedScalars s16h_H5O4aIota K)) = 3
    rw [s16h_H5O4a_card_statedScalars_natImage (K := K), hK]
    norm_num
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : IsL2 ↥Ω (2 * 2) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  have hprank : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥Ω)) ≤ 1 :=
    (uc22p2121d_pRank_mulAut_l2 hL2 (by norm_num) (by norm_num)).2 (by norm_num)
  let φ : ↥D →* MulAut ↥Ω :=
    (Subgroup.normalizerMonoidHom Ω).comp (Subgroup.inclusion hDN)
  have hker : (φ.ker).map (Subgroup.subtype D) = D ⊓ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyker : φ y = 1 := MonoidHom.mem_ker.mp hy
      have hmem : Subgroup.inclusion hDN y ∈ (Subgroup.normalizerMonoidHom Ω).ker := by
        rw [MonoidHom.mem_ker]
        exact hyker
      rw [Subgroup.normalizerMonoidHom_ker] at hmem
      refine ⟨y.2, ?_⟩
      show y.1 ∈ C
      rw [← hcent]
      simpa using Subgroup.mem_subgroupOf.mp hmem
    · rintro ⟨hxD, hxC⟩
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      change φ ⟨x, hxD⟩ = 1
      have hmem : Subgroup.inclusion hDN (⟨x, hxD⟩ : ↥D) ∈
          (Subgroup.centralizer (Ω : Set (MulAut (StdMod s16h_H5O4aIota K)))).subgroupOf
            (Subgroup.normalizer (Ω : Set (MulAut (StdMod s16h_H5O4aIota K)))) := by
        rw [Subgroup.mem_subgroupOf, hcent]
        exact hxC
      rwa [← Subgroup.normalizerMonoidHom_ker] at hmem
  by_contra hCnotle
  have hDinfC_ne : D ⊓ C ≠ ⊥ := by
    intro hbot
    have hkerbot : φ.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hmem : x.1 ∈ (φ.ker).map (Subgroup.subtype D) := ⟨x, hx, rfl⟩
      rw [show (φ.ker).map (Subgroup.subtype D) = ⊥ from by rw [hker, hbot]] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥D) := by
      rw [← Subgroup.subgroupOf_self (H := D)]
      exact hDab.subgroupOf D
    have hea : IsElemAbelian 3 φ.range := by
      have h := IsElemAbelian.map htop φ
      simpa [MonoidHom.range_eq_map] using h
    have hrangecard : Nat.card φ.range = 3 ^ 2 := by
      have h1 : Nat.card φ.range = Nat.card ↥D :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
      rw [h1, hDcard]
    have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥Ω)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hea hrangecard
    omega
  have hcard : Nat.card ↥(D ⊓ C) = Nat.card C := by
    have hdiv : Nat.card ↥(D ⊓ C) ∣ Nat.card C := Subgroup.card_dvd_of_le inf_le_right
    rw [hCcard] at hdiv
    have hne : Nat.card ↥(D ⊓ C) ≠ 1 := by
      intro h1
      exact hDinfC_ne ((Subgroup.card_eq_one).mp h1)
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (Nat.card ↥(D ⊓ C)) hdiv) with h | h
    · exact absurd h hne
    · rw [h, hCcard]
  have hCle : C ≤ D := by
    have hrel : (D ⊓ C).relIndex C = 1 := by
      have hmul := Subgroup.relIndex_mul_card (H := D ⊓ C) (K := C)
      have hinf : (D ⊓ C) ⊓ C = D ⊓ C := inf_eq_left.mpr inf_le_right
      rw [hinf] at hmul
      have hpos : 0 < Nat.card ↥(D ⊓ C) := Nat.card_pos
      nlinarith [hmul, hcard]
    exact (Subgroup.relIndex_eq_one.mp hrel).trans inf_le_left
  exact hCnotle hCle

public theorem s16h_H5_omegaMinusFour_two_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {y z : MulAut (StdMod s16h_H5O4aIota K)}
    (hy : y ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)))
    (hz : z ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)))
    (hyne : y ≠ 1) (hzne : z ≠ 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) :
    ∃ g ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), ∃ j : ℕ, g * y * g⁻¹ = z ^ j := by
  classical
  let Γ : Subgroup (GL s16h_H5O4aIota K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5O4aIota K)) := natImage Γ
  have hqprime : (3 : ℕ).Prime := by norm_num
  have hq2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (3 : ℕ).Prime := ⟨hqprime⟩
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : IsL2 ↥Ω (2 * 2) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  have hm : CFSG.Open.StatedClassicalModel ↥Ω .PSL 2 2 (2 * 2) :=
    hL2.statedClassicalModel (by decide)
  have hprank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Ω) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hm hqprime hq2
  let yΩ : ↥Ω := ⟨y, hy⟩
  let zΩ : ↥Ω := ⟨z, hz⟩
  have hyΩord : orderOf yΩ = 3 := by
    change orderOf (⟨y, hy⟩ : ↥Ω) = 3
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hy3 hyne
  have hzΩord : orderOf zΩ = 3 := by
    change orderOf (⟨z, hz⟩ : ↥Ω) = 3
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hz3 hzne
  have hPy : IsPGroup 3 (Subgroup.zpowers yΩ) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [Nat.card_zpowers, hyΩord, pow_one])
  obtain ⟨Py, hyPy⟩ := hPy.exists_le_sylow
  have hPz : IsPGroup 3 (Subgroup.zpowers zΩ) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [Nat.card_zpowers, hzΩord, pow_one])
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
      have h := congrArg (fun P : Sylow 3 ↥Ω => (P : Subgroup ↥Ω)) hg
      rwa [Sylow.coe_subgroup_smul] at h
    have h1 : (MulAut.conj g) yΩ ∈ (MulAut.conj g) • (Py : Subgroup ↥Ω) :=
      Subgroup.smul_mem_pointwise_smul_iff.mpr hyPymem
    rwa [h2] at h1
  let wPz : ↥Pz := ⟨(MulAut.conj g) yΩ, hconjPz⟩
  let zPz : ↥Pz := ⟨zΩ, hzPzmem⟩
  have hzPzord : orderOf zPz = 3 := by
    change orderOf (⟨zΩ, hzPzmem⟩ : ↥Pz) = 3
    rw [Subgroup.orderOf_mk]
    exact hzΩord
  have hwPzord : orderOf wPz = 3 := by
    change orderOf (⟨(MulAut.conj g) yΩ, hconjPz⟩ : ↥Pz) = 3
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

public theorem s16h_H5_omegaMinusFour_two_cover {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5O4aIota K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 3 D) (hDcard : Nat.card ↥D = 3 ^ 2) :
    ∀ v : StdMod s16h_H5O4aIota K, v ≠ 1 →
      ∃ y ∈ D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c)), y ≠ 1 ∧
        ∃ h ∈ natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)),
          ∃ mu ∈ natImage (StatedScalars s16h_H5O4aIota K), (h * y * h⁻¹) v = mu v := by
  intro v hv
  have hC3 : Nat.card (natImage (StatedScalars s16h_H5O4aIota K)) = 3 := by
    rw [s16h_H5O4a_card_statedScalars_natImage (K := K), hK]
    norm_num
  have hCD := s16h_H5_omegaMinusFour_two_scalars_le hK hirr hDN hDab hDcard
  have hcent : Subgroup.centralizer (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
      Set (MulAut (StdMod s16h_H5O4aIota K))) ≤ natImage (StatedScalars s16h_H5O4aIota K) :=
    s16h_H5O4a_centralizer_natImage_le_statedScalars (K := K) hirr
  obtain ⟨y, hy, hyne⟩ :=
    s16h_H5_omegaMinusFour_two_inf_ne_bot hK hirr hDN hDab hDcard hCD hC3 hcent
  obtain ⟨z, hzΩ, hz1, hz3, hzv⟩ := s16h_H5O4a_cover_torus hK hirr
  have hy3 : y ^ 3 = 1 := hDab.2 y hy.1
  obtain ⟨g, hg, j, hgy⟩ := s16h_H5_omegaMinusFour_two_conj hK hirr hy.2 hzΩ hyne hz1 hy3 hz3
  obtain ⟨h, hh, mu, hmu, hmuv⟩ := hzv v hv
  have hΩO : natImage (StatedOmega (StatedQuadMinus 2 K b c)) ≤
      natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) := by
    have h1 : StatedOmega (StatedQuadMinus 2 K b c) ≤
        CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c) :=
      Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
        Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂) (Subgroup.inv_mem _ hg₁))
          (Subgroup.inv_mem _ hg₂)
    rw [natImage_eq_map, natImage_eq_map]
    exact Subgroup.map_mono h1
  have hzO := hΩO hzΩ
  have hzconj : h * z * h⁻¹ ∈ natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hzO) (Subgroup.inv_mem _ hh)
  have hmuz : mu * (h * z * h⁻¹) = (h * z * h⁻¹) * mu :=
    s16h_H5O4a_scalars_commute_natImage hmu hzconj
  have hcommmuz : Commute mu (h * z * h⁻¹) := hmuz
  have hzj : ∀ k : ℕ, ((h * z * h⁻¹) ^ k) v = (mu ^ k) v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, hmuv]
      have hc : (h * z * h⁻¹) ^ k * mu = mu * (h * z * h⁻¹) ^ k :=
        (hcommmuz.pow_right k).eq.symm
      rw [← MulAut.mul_apply, hc, MulAut.mul_apply, ih, ← MulAut.mul_apply, ← pow_succ']
  refine ⟨y, hy, hyne, h * g, Subgroup.mul_mem _ hh (hΩO hg), mu ^ j,
    Subgroup.pow_mem _ hmu j, ?_⟩
  have e1 : h * g * y * (h * g)⁻¹ = (h * z * h⁻¹) ^ j := by
    rw [conj_pow, ← hgy]
    group
  rw [e1, hzj j]

theorem s16h_H5_omegaMinusFour_two_q_sq_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5O4aIota K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 3 D) (hDcard : Nat.card ↥D = 3 ^ 2) :
    ∀ v : StdMod s16h_H5O4aIota K, v ≠ 1 →
      ∃ g ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), ∃ d ∈ D, d ≠ 1 ∧
        (g * d * g⁻¹) v = v := by
  intro v hv
  obtain ⟨y, hy, hyne, h, hh, mu, hmu, hmuv⟩ :=
    s16h_H5_omegaMinusFour_two_cover hK hirr hDN hDab hDcard v hv
  have hyΩ : y ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) := hy.2
  have hy3 : y ^ 3 = 1 := hDab.2 y hy.1
  have hnorm : natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) ≤
      normalizer (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
        Set (MulAut (StdMod s16h_H5O4aIota K))) := by
    have h1 : (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) ≤
        normalizer (StatedOmega (StatedQuadMinus 2 K b c)) :=
      Subgroup.normalizer_commutator_ge_left _ _
    have h2 : (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)).map matHom ≤
        normalizer ((StatedOmega (StatedQuadMinus 2 K b c)).map matHom) :=
      (Subgroup.map_mono (f := matHom) h1).trans
        (Subgroup.le_normalizer_map (f := matHom)
          (H := StatedOmega (StatedQuadMinus 2 K b c)))
    rw [← natImage_eq_map (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)),
      ← natImage_eq_map (StatedOmega (StatedQuadMinus 2 K b c))] at h2
    exact h2
  have hzΩ : h * y * h⁻¹ ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hh) y).mp hyΩ
  have hz3 : (h * y * h⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hzne : h * y * h⁻¹ ≠ 1 := by
    intro h1
    apply hyne
    calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨g, hg, j, hgy⟩ :=
    s16h_H5_omegaMinusFour_two_conj hK hirr hyΩ hzΩ hyne hzne hy3 hz3
  have hmuD : mu ∈ D :=
    s16h_H5_omegaMinusFour_two_scalars_le hK hirr hDN hDab hDcard hmu
  have hmuz : mu * (h * y * h⁻¹) = (h * y * h⁻¹) * mu :=
    s16h_H5O4a_scalars_commute_natImage hmu hzΩ
  have hmug : mu * g = g * mu := s16h_H5O4a_scalars_commute_natImage hmu hg
  have hcommmuz : Commute mu (h * y * h⁻¹) := hmuz
  have hzj : ∀ k : ℕ, ((h * y * h⁻¹) ^ k) v = (mu ^ k) v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, hmuv]
      have hc : (h * y * h⁻¹) ^ k * mu = mu * (h * y * h⁻¹) ^ k :=
        (hcommmuz.pow_right k).eq.symm
      rw [← MulAut.mul_apply, hc, MulAut.mul_apply, ih, ← MulAut.mul_apply, ← pow_succ']
  have hmuginv : (mu ^ j)⁻¹ * g = g * (mu ^ j)⁻¹ := by
    have : Commute mu g := hmug
    exact ((this.pow_left j).inv_left).eq
  have hCO : natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊓
      natImage (StatedScalars s16h_H5O4aIota K) = ⊥ := by
    let Γ₀ : Subgroup (GL s16h_H5O4aIota K) := StatedOmega (StatedQuadMinus 2 K b c)
    let Ω₀ : Subgroup (MulAut (StdMod s16h_H5O4aIota K)) := natImage Γ₀
    have hInj₀ : Function.Injective (natAut Γ₀) :=
      matHom_injective.comp (Subgroup.subtype_injective Γ₀)
    let e₀ : ↥Γ₀ ≃* ↥Ω₀ := MonoidHom.ofInjective hInj₀
    have hL2₀ : IsL2 ↥Ω₀ (2 * 2) :=
      uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr e₀.symm
    obtain ⟨hsimple₀, hnonab₀⟩ :=
      CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel hL2₀
    haveI : IsSimpleGroup ↥Ω₀ := hsimple₀
    have hcenter₀ : Subgroup.center ↥Ω₀ = ⊥ :=
      GL83.I713.center_eq_bot_of_simple hnonab₀
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxcenter : (⟨x, hx.1⟩ : ↥Ω₀) ∈ Subgroup.center ↥Ω₀ := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (s16h_H5O4a_scalars_commute_natImage
        (Γ := Γ₀) (mu := x) (g := z.1) hx.2 z.2).symm
    rw [hcenter₀] at hxcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter)
  refine ⟨g, hg, (mu ^ j)⁻¹ * y,
    D.mul_mem (D.inv_mem (D.pow_mem hmuD j)) hy.1, ?_, ?_⟩
  · intro h1
    have hyC : y ∈ natImage (StatedScalars s16h_H5O4aIota K) := by
      have hyeq : y = mu ^ j := by
        have h2 := congrArg (fun t => mu ^ j * t) h1
        simpa [mul_assoc] using h2
      rw [hyeq]
      exact (natImage (StatedScalars s16h_H5O4aIota K)).pow_mem hmu j
    exact hyne (Subgroup.mem_bot.mp (by
      have : y ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊓
          natImage (StatedScalars s16h_H5O4aIota K) := ⟨hyΩ, hyC⟩
      rwa [hCO] at this))
  · have hgd : g * ((mu ^ j)⁻¹ * y) * g⁻¹ = (mu ^ j)⁻¹ * (g * y * g⁻¹) := by
      calc g * ((mu ^ j)⁻¹ * y) * g⁻¹
          = (g * (mu ^ j)⁻¹) * y * g⁻¹ := by rw [mul_assoc g (mu ^ j)⁻¹ y]
        _ = ((mu ^ j)⁻¹ * g) * y * g⁻¹ := by rw [← hmuginv]
        _ = (mu ^ j)⁻¹ * (g * y * g⁻¹) := by group
    rw [hgd, hgy, MulAut.mul_apply, hzj j, ← MulAut.mul_apply]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
