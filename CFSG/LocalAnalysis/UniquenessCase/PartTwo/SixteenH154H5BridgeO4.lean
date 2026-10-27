module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.Quasithin.Background.HStandard
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_finite_mulAut [Finite W] : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_H5_normalizer_le_stabSub_commSub {L : Subgroup (MulAut W)} {g : MulAut W}
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

private theorem s16h_H5_le_stabSub_commSub (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub ⊤ L) := fun l hl =>
  s16h_H5_normalizer_le_stabSub_commSub (Subgroup.le_normalizer hl)

private theorem s16h_le_stabSub_fixV (L : Subgroup (MulAut W)) : L ≤ stabSub (fixV L) := by
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

private theorem s16h_normalizer_le_stabSub_fixV {L : Subgroup (MulAut W)} {g : MulAut W}
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

private theorem s16h_stabSub_inf {U Z : Subgroup W} {g : MulAut W}
    (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) := by
  rw [mem_stabSub] at hU hZ ⊢
  intro x
  exact ⟨fun hx => ⟨(hU x).mp hx.1, (hZ x).mp hx.2⟩,
    fun hx => ⟨(hU x).mpr hx.1, (hZ x).mpr hx.2⟩⟩

private theorem s16h_autSec_le_normalizer {L Y : Subgroup (MulAut W)} {V C : Subgroup W}
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

private theorem s16h_one_le_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {m : ℕ}
    (h : Nat.card K = 2 ^ m) : 1 ≤ m := by
  by_contra hlt
  have hm : m = 0 := Nat.lt_one_iff.mp (not_le.mp hlt)
  rw [hm, pow_zero] at h
  have h1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
  omega

theorem s16h_H5_bridge_omegaMinus4 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {m : ℕ}
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) m)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K) (_ : Nat.card K = 2 ^ m)
      (_ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (D : Subgroup (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))),
      D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)) ∧ IsElemAbelian q D ∧
      Nat.card D = Nat.card ↥(autSub E (commSub ⊤ L)) := by
  classical
  haveI : Finite (MulAut W) := s16h_finite_mulAut
  obtain ⟨hO4, hNat⟩ := h
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hbc, hreal⟩ := hNat
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hm1 : 1 ≤ m := s16h_one_le_of_card_eq_two_pow hKcard
  have hchar : CharP K 2 := uc22p22d_charP_two hm1 hKcard
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have hL2 : IsL2 ↥L (2 * m) := S18.isL2_of_isOmegaMinus_four hm1 hO4
    exact P22y.center_eq_bot_of_isL2Ev (P22fin.isL2Ev_of_isL2 hL2).1
  have hfaith : L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ :=
    s16h_H5_faithful_on_quotient hc hcenter
  have hLU : L ≤ stabSub (commSub ⊤ L) := s16h_H5_le_stabSub_commSub L
  have hLfix : L ≤ stabSub (fixV L) := s16h_le_stabSub_fixV L
  have hLZ : L ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun l hl => s16h_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_H5_normalizer_le_stabSub_commSub (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub (commSub ⊤ L ⊓ fixV L) :=
    fun e he => s16h_stabSub_inf (hEU he) (hEfix he)
  have hrealAuto : (FFModel.nat (StatedOmega (StatedQuadMinus (4 / 2) K b c))).Realizes
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
      (⊤ : Subgroup (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))) ⊥ :=
    s16h_realizes_autSec_of_realizes inf_le_left hLU hLZ hfaith hreal
  have hLX : autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≤
      autSec (E ⊔ L) (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :=
    autSec_mono le_sup_right _ _
  have hXN : autSec (E ⊔ L) (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ≤
      normalizer ((autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
        Subgroup (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :
          Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) :=
    s16h_autSec_le_normalizer hLU hLZ (sup_le hEU hLU) (sup_le hEZ hLZ)
      (sup_le hEN Subgroup.le_normalizer)
  obtain ⟨e, -, hXeN⟩ := exists_transport_natural hrealAuto hLX hXN
  set X₀ : Subgroup (MulAut W) := stabSub (commSub ⊤ L) ⊓ stabSub (commSub ⊤ L ⊓ fixV L)
    with hX₀def
  have hX₀U : X₀ ≤ stabSub (commSub ⊤ L) := inf_le_left
  have hX₀Z : X₀ ≤ stabSub (commSub ⊤ L ⊓ fixV L) := inf_le_right
  have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
  have hEsec : IsElemAbelian q (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) := by
    have hmap := IsElemAbelian.map (hEab.subgroupOf X₀)
      (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z)
    rwa [CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀] at hmap
  refine ⟨K, hKf, hKfin, hchar, b, c, hKcard, hbc,
    (autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)).map (congrHom e), ?_, ?_, ?_⟩
  · exact le_trans (Subgroup.map_mono (autSec_mono le_sup_left _ _)) hXeN
  · exact IsElemAbelian.map hEsec (congrHom e)
  · rw [Subgroup.card_map_of_injective (congrHom_injective e)]
    exact (s16h_H5_card_autSub_eq_autSec hc hE).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
