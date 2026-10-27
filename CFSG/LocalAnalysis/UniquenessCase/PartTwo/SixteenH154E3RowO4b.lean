module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowO4b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_O4_three_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) : s16h_BlockBound A L q 1 :=
  s16h_H5_row_O4_three_block_one hc h hq hq2 hq3 hq7

theorem s16h_H5_row_O4_three_fix {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L = ⊥) {q : ℕ} (hq : q = 3 ∨ q = 7) : s16h_H5Fix A L q := by
  intro E hE hEab hEcard w hw hwne
  classical
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZdef
  have hZbot : Z = ⊥ := by simpa [U, Z] using hZ
  have hqprime : q.Prime := by rcases hq with h | h <;> subst h <;> norm_num
  have hq2 : q ≠ 2 := by rcases hq with h | h <;> omega
  obtain ⟨K, hKf, hKfin, b, c, hKcard, hirr, e, D, hDeq, hmapL, hDnorm, hDab, hDcard⟩ :=
    s16h_H5_row_O4_three_bridge_strong hc h hqprime hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by norm_num) hKcard
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := fun e he => s16h_H5E3_commSub_stab (L := L) (g := e) (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_H5E3RowO4b_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub Z := fun e he =>
    s16h_H5E3RowO4b_stabSub_inf (hEU he) (hEfix he)
  have hLU : L ≤ stabSub U := fun l hl =>
    s16h_H5E3_commSub_stab (Subgroup.le_normalizer hl)
  have hLfix : L ≤ stabSub (fixV L) := s16h_H5E3RowO4b_le_stabSub_fixV L
  have hLZ : L ≤ stabSub Z := fun l hl =>
    s16h_H5E3RowO4b_stabSub_inf (hLU hl) (hLfix hl)
  set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀def
  have hX₀U : X₀ ≤ stabSub U := inf_le_left
  have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
  have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
  have hLX₀ : L ≤ X₀ := le_inf hLU hLZ
  have hDsize : Nat.card ↥D = q ^ 2 := by
    have hcardE := card_autSub_mul (A := E) (U := U) hEU
    have hb : Nat.card ↥(autSub E U) ≤ q ^ 2 :=
      s16h_H5_row_O4_b_bound hc h q hqprime hq2 E hE hEab
    have hge : q ^ 2 ≤ Nat.card ↥(autSub E U) := by
      have hpre : q ^ 2 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card E := hEcard
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
  let v : StdMod s16h_H5E3Rkι K := e wbar
  have hv : v ≠ 1 := by
    change e wbar ≠ 1
    intro h1
    exact hwbarne (e.injective (by rw [h1, map_one]))
  obtain ⟨g, hg, d, hd, hdne, hgfixv⟩ :=
    s16h_H5_omegaMinusFour_q_sq_fix hKcard hirr hq hDnorm hDab hDsize v hv
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
