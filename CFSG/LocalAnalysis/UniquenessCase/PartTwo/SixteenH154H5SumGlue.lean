module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_finite_mulAut_of_finite (X : Type) [Group X] [Finite X] :
    Finite (MulAut X) := by
  classical
  exact Finite.of_injective (fun f : MulAut X => (f : X → X))
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

theorem s16h_H5_sum_glue [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hN : ∀ I : Subgroup W, N L I (commSub ⊤ L ⊓ fixV L) →
      s16h_SimpleScalar L I (commSub ⊤ L ⊓ fixV L))
    {k : ℕ} (hk : k ≤ 3) (hS : SumOfNat N L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    (hcenter : Subgroup.center ↥L = ⊥) {M : ℕ} (hM : Nat.card (MulAut ↥L) ∣ M)
    (hMq : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ^ 2 ∣ M) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  intro q hq hq2 E hE hEab
  classical
  haveI : Finite (MulAut W) := s16h_finite_mulAut_of_finite W
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hLU : L ≤ stabSub U := by
    rw [hU]
    exact s16h_H5_le_stabSub_commSub L
  have hLfix : L ≤ stabSub (fixV L) := s16h_le_stabSub_fixV L
  have hLZ : L ≤ stabSub Z := by
    rw [hZ]
    exact fun l hl => s16h_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := by
    rw [hU]
    exact fun e he => s16h_H5_normalizer_le_stabSub_commSub (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub Z := by
    rw [hZ]
    exact fun e he => s16h_stabSub_inf (hEU he) (hEfix he)
  have hfaith : L ⊓ centSec U Z = ⊥ := by
    rw [hU, hZ]
    exact s16h_H5_faithful_on_quotient hc hcenter
  set Λ : Subgroup (MulAut (Sec U Z)) := autSec L U Z with hΛ
  set E' : Subgroup (MulAut (Sec U Z)) := autSec E U Z with hE'
  have hE'ea : IsElemAbelian q E' := by
    set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀
    have hX₀U : X₀ ≤ stabSub U := inf_le_left
    have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
    have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
    have hmap := IsElemAbelian.map (hEab.subgroupOf X₀)
      (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z)
    rw [CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀] at hmap
    simpa [hE'] using hmap
  have hE'N : E' ≤ normalizer (Λ : Set (MulAut (Sec U Z))) := by
    rw [hE', hΛ]
    exact s16h_autSec_le_normalizer hLU hLZ hEU hEZ hEN
  let ρ : E' →* MulAut Λ :=
    (Subgroup.normalizerMonoidHom Λ).comp (Subgroup.inclusion hE'N)
  set F : Subgroup (MulAut (Sec U Z)) :=
    E' ⊓ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) with hF
  have hker : ρ.ker = F.subgroupOf E' := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, ?_⟩
      change (Subgroup.normalizerMonoidHom Λ) (Subgroup.inclusion hE'N x) = 1 at hx
      have hx' : (Subgroup.inclusion hE'N x) ∈
          (Subgroup.normalizerMonoidHom Λ).ker := hx
      rw [Subgroup.normalizerMonoidHom_ker] at hx'
      rw [Subgroup.mem_subgroupOf] at hx'
      simpa using hx'
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      change (Subgroup.normalizerMonoidHom Λ) (Subgroup.inclusion hE'N x) = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa using hx.2
  have hkerCard : Nat.card ρ.ker = Nat.card F := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hFle : F ≤ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) := inf_le_right
  have hFea : IsElemAbelian q F := hE'ea.mono inf_le_left
  have hFcard : Nat.card F ≤ q :=
    s16h_sum_cent_sec hc.elem hN hk hS hLU hLZ hq hq2 hFle hFea
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (MulAut (Sec U Z)) := s16h_finite_mulAut_of_finite (Sec U Z)
  have hrangeEA : IsElemAbelian q ρ.range := by
    have hmap := IsElemAbelian.map (hE'ea.subgroupOf E') ρ
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map ρ] at hmap
    exact hmap
  obtain ⟨j, hj⟩ :=
    (IsPGroup.iff_card (p := q) (G := ↥ρ.range)).mp hrangeEA.isPGroup
  have hcardAut : Nat.card (MulAut ↥Λ) = Nat.card (MulAut ↥L) := by
    have e : ↥L ≃* ↥Λ := by
      rw [hΛ]
      exact CFSG.Quasithin.B5.secEquiv L hLU hLZ hfaith
    exact (Nat.card_congr (MulAut.congr e).toEquiv).symm
  have hdvdRange : Nat.card ρ.range ∣ Nat.card (MulAut ↥Λ) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  have hdvdM : Nat.card ρ.range ∣ M := by
    exact hdvdRange.trans (hcardAut ▸ hM)
  have hjM : q ^ j ∣ M := by
    rw [← hj]
    exact hdvdM
  have hjle : j ≤ 1 := by
    rcases Nat.lt_or_ge j 2 with h | h
    · omega
    · exfalso
      exact hMq q hq hq2 (dvd_trans (pow_dvd_pow q h) hjM)
  have hRangeLe : Nat.card ρ.range ≤ q := by
    rw [hj]
    calc q ^ j ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hjle
      _ = q := pow_one q
  have hcardE' : Nat.card ↥(autSub E U) = Nat.card E' := by
    simpa [hU, hZ, hE'] using s16h_H5_card_autSub_eq_autSec hc hE
  calc
    Nat.card ↥(autSub E U) = Nat.card E' := hcardE'
    _ = Nat.card ρ.ker * Nat.card ρ.range := (card_ker_mul_card_range ρ).symm
    _ = Nat.card F * Nat.card ρ.range := by rw [hkerCard]
    _ ≤ q * q := Nat.mul_le_mul hFcard hRangeLe
    _ = q ^ 2 := (pow_two q).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
