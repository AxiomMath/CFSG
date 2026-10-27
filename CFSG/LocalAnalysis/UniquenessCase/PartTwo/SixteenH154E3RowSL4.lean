module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL4A
public import CFSG.Quasithin.Background.SimsE214NatCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_four_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) : s16h_BlockBound A L q 1 := by
  intro E hE hEab
  obtain ⟨K, hKf, hKfin, hKcard, D, hDN, hDab, hcard⟩ :=
    s16h_H5_row_SL2_four_bridge hc h hq hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hDle : Nat.card D ≤ q :=
    s16h_H5_natNorm_statedSL_two_four_elemAbelian_one hKcard hq hq2 hq3 hDN hDab
  rw [hcard] at hDle
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_H5_row_SL2_four_stab_commSub (Subgroup.mem_inf.mp (hE he)).2
  rw [← card_autSub_mul (A := E) (U := commSub ⊤ L) hEU]
  exact Nat.mul_le_mul_right _ (by simpa using hDle)

theorem s16h_H5_row_SL2_four_fix {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) : s16h_H5Fix A L 3 := by
  intro E hE hEab hEcard w hw hwne
  classical
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZdef
  have hZcard : Nat.card ↥Z ≤ 2 := by simpa [hZdef] using hZ
  have hEcardU : 3 ^ 2 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card ↥E := by
    simpa [hU] using hEcard
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun x hx => (mem_inf.mp (hE hx)).2
  have hEU : E ≤ stabSub U := fun x hx =>
    s16h_H5_row_SL2_four_stab_commSub (hEN hx)
  have hEfix : E ≤ stabSub (fixV L) := fun x hx =>
    s16h_H5_row_SL2_four_stab_fixV (hEN hx)
  have hEZ : E ≤ stabSub Z := fun x hx =>
    s16h_H5_row_SL2_four_stab_inf (hEU hx) (hEfix hx)
  by_cases hwZ : w ∈ Z
  · have hbex : ∃ b ∈ E, b ∉ centSub U := by
      by_contra hcon
      have hall : ∀ b ∈ E, b ∈ centSub U := by
        intro b hb
        by_contra hbc
        exact hcon ⟨b, hb, hbc⟩
      have hEq : E ⊓ centSub U = E :=
        le_antisymm inf_le_left fun b hb => ⟨hb, hall b hb⟩
      rw [hEq] at hEcardU
      have hle : 9 * Nat.card ↥E ≤ Nat.card ↥E := by simpa using hEcardU
      have hpos : 0 < Nat.card ↥E := Nat.card_pos
      omega
    obtain ⟨b, hbE, hbcent⟩ := hbex
    have hfixw : b w = w :=
      s15_Core_map_eq_self_of_card_le_two Z b hZcard
        (fun u hu => ((mem_stabSub.mp (hEZ hbE)) u).mpr hu) w hwZ
    refine ⟨1, L.one_mem, b, hbE, hbcent, ?_⟩
    show ((1 : MulAut W) * b * (1 : MulAut W)⁻¹) w = w
    simpa using hfixw
  · obtain ⟨K, hKf, hKfin, hKcard, e, D, hDeq, hmapL, hDnorm, hDab, hDcard⟩ :=
      s16h_H5_row_SL2_four_bridge_strong hc h (q := 3) Nat.prime_three (by norm_num) hE hEab
    letI : Field K := hKf
    letI : Finite K := hKfin
    have h9aut : 9 ≤ Nat.card ↥(autSub E U) := by
      have hpre : 9 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card E := by
        simpa only [show (3 : ℕ) ^ 2 = 9 by norm_num] using hEcardU
      have hcardE := card_autSub_mul (A := E) (U := U) hEU
      rw [← hcardE] at hpre
      exact Nat.le_of_mul_le_mul_right hpre Nat.card_pos
    have hD9le : 9 ≤ Nat.card D := by
      rw [hDcard]
      exact h9aut
    obtain ⟨hD9, hDlin⟩ :=
      s16h_H5_natNorm_statedSL_two_four_three_card hKcard hDnorm hDab hD9le
    obtain ⟨Amat, v, hvne, hAne, hAvmem, hAfixv⟩ :=
      s16h_H5_eigenvector_one_of_three_subgroup hKcard hDlin hDab hD9
    let wU : U := ⟨w, by simpa [hU] using hw⟩
    let wbar : Sec U Z := QuotientGroup.mk wU
    have hwbarne : wbar ≠ 1 := by
      intro h1
      have hmem : wU ∈ Z.subgroupOf U := (QuotientGroup.eq_one_iff wU).1 h1
      have hwZmem : w ∈ Z := Subgroup.mem_subgroupOf.mp hmem
      exact hwZ (by simpa [wU] using hwZmem)
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
    have hLU : L ≤ stabSub U := fun l hl =>
      s16h_H5_row_SL2_four_stab_commSub (Subgroup.le_normalizer hl)
    have hLZ : L ≤ stabSub Z := fun l hl =>
      s16h_H5_row_SL2_four_le_stabSub_commSub_fixV L hl
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
    have hlsec_eq : e (lsec wbar) = Multiplicative.ofAdd v := by
      rw [← ofAdd_toAdd (e (lsec wbar)), hlsec_toAdd]
    have hEsecEq : (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
        autSec E U Z :=
      CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z (le_inf hEU hEZ)
    have hAvmem' : CFSG.Quasithin.H.matHom Amat ∈
        (autSec E U Z).map (CFSG.Quasithin.H.congrHom e) := by
      rwa [← hDeq]
    obtain ⟨aE, haEmem, haEeq⟩ := Subgroup.mem_map.mp hAvmem'
    rw [← hEsecEq] at haEmem
    obtain ⟨b0, hb0E, hb0sec⟩ := Subgroup.mem_map.mp haEmem
    let b : MulAut W := b0
    have hbE : b ∈ E := Subgroup.mem_subgroupOf.mp hb0E
    have hbsec : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 = aE := hb0sec
    have hAmat_fix_v : CFSG.Quasithin.H.matHom Amat (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd v := by
      change CFSG.Quasithin.H.matAut Amat (Multiplicative.ofAdd v) = Multiplicative.ofAdd v
      rw [← ofAdd_toAdd
        (CFSG.Quasithin.H.matAut Amat (Multiplicative.ofAdd v))]
      change Multiplicative.ofAdd (CFSG.Quasithin.H.toAddMap
        (CFSG.Quasithin.H.matAut Amat) v) = Multiplicative.ofAdd v
      rw [CFSG.Quasithin.H.toAddMap_matAut]
      have h : Amat *ᵥ v = v := by simpa using hAfixv
      rw [h]
    have hcongr_fix : CFSG.Quasithin.H.congrHom e aE (e (lsec wbar)) = e (lsec wbar) := by
      rw [haEeq, hlsec_eq, hAmat_fix_v]
    have hfix_class : aE (lsec wbar) = lsec wbar := by
      apply e.injective
      have h1 : CFSG.Quasithin.H.congrHom e aE (e (lsec wbar)) = e (aE (lsec wbar)) := by
        rw [CFSG.Quasithin.H.congrHom_apply, e.symm_apply_apply]
      rw [← h1]
      exact hcongr_fix
    have hfix_wbar : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 (lsec wbar) = lsec wbar := by
      rw [hbsec]
      exact hfix_class
    have hfix_wU : b ((l0 : MulAut W) w) = (l0 : MulAut W) w := by
      have hq' : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z (b0 * l0) wbar =
          CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0 wbar := by
        rw [map_mul]
        calc CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0
              (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0 wbar)
            = CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 (lsec wbar) := by rw [hl0sec]
          _ = lsec wbar := hfix_wbar
          _ = CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0 wbar := by rw [hl0sec]
      have hb0E' : (b0 : MulAut W) ∈ E := Subgroup.mem_subgroupOf.mp hb0E
      have hl0L' : (l0 : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hl0L
      have hl0wU : (l0 : MulAut W) w ∈ U :=
        ((hX₀U ((le_inf hLU hLZ) hl0L')) w).2 hw
      have hmk : (QuotientGroup.mk (⟨b ((l0 : MulAut W) w),
          ((hX₀U ((le_inf hEU hEZ) hb0E')) ((l0 : MulAut W) w)).2 hl0wU⟩ : U) : Sec U Z) =
          (QuotientGroup.mk (⟨(l0 : MulAut W) w, hl0wU⟩ : U) : Sec U Z) := by
        simpa [CFSG.Quasithin.B5.secHom_mk, b, wbar, wU, MulAut.mul_apply] using hq'
      have hmem := (CFSG.Quasithin.mk_eq_mk_iff (U := Z.subgroupOf U) _ _).1 hmk
      have hZmem : b ((l0 : MulAut W) w) * ((l0 : MulAut W) w)⁻¹ ∈ Z := by
        have h := Subgroup.mem_subgroupOf.mp hmem
        simpa using h
      set x : W := (l0 : MulAut W) w with hxdef
      have hZmem' : b x * x⁻¹ ∈ Z := by
        rw [hxdef]
        exact hZmem
      set z : W := b x * x⁻¹ with hzdef
      have hzZ : z ∈ Z := by
        rw [hzdef]
        exact hZmem'
      have hbfixZ : ∀ u ∈ Z, b u = u := fun u hu =>
        s15_Core_map_eq_self_of_card_le_two Z b hZcard
          (fun v hv => ((mem_stabSub.mp (hEZ hbE)) v).mpr hv) u hu
      have hbx : b x = z * x := by
        rw [hzdef]
        group
      have hb2 : b (b x) = z * (z * x) := by
        rw [hbx, map_mul, hbfixZ z hzZ, hbx]
      have hb3 : b ^ 3 = 1 := hEab.2 b hbE
      have hb3x : (b ^ 3) x = x := by rw [hb3]; rfl
      have hb3x' : (b ^ 3) x = b (b (b x)) := by
        rw [pow_succ, MulAut.mul_apply, pow_two, MulAut.mul_apply]
      have h3 : b (b (b x)) = z * (z * (z * x)) := by
        rw [hb2, map_mul, hbfixZ z hzZ, map_mul, hbfixZ z hzZ, hbx]
      have hx2 : z * (z * (z * x)) = x := by
        rw [← h3, ← hb3x', hb3x]
      have hx3 : z ^ 3 * x = 1 * x := by
        rw [one_mul]
        calc z ^ 3 * x = (z * z * z) * x := by rw [pow_succ, pow_two]
          _ = z * (z * (z * x)) := by simp [mul_assoc]
          _ = x := hx2
      have hz3 : z ^ 3 = 1 := mul_right_cancel hx3
      have hz2 : z ^ 2 = 1 := by
        have hzpow : z ^ Nat.card Z = 1 := by
          have hdvd : orderOf z ∣ Nat.card Z := by
            have h := orderOf_dvd_natCard (⟨z, hzZ⟩ : Z)
            rwa [← Subgroup.orderOf_coe] at h
          exact orderOf_dvd_iff_pow_eq_one.mp hdvd
        rcases lt_or_eq_of_le hZcard with hlt | heq
        · have h1 : Nat.card Z = 1 := by
            have hpos : 0 < Nat.card Z := Nat.card_pos
            omega
          have hbot : Z = ⊥ := Subgroup.card_eq_one.mp h1
          have hz1 : z = 1 := by
            have hz' : z ∈ (⊥ : Subgroup W) := by rwa [← hbot]
            simpa using hz'
          rw [hz1]
          simp
        · rw [← heq]
          exact hzpow
      have hz1 : z = 1 := by
        have h : z * z ^ 2 = 1 := by rw [← pow_succ', hz3]
        rwa [hz2, mul_one] at h
      have hfix_eq : b ((l0 : MulAut W) w) = (l0 : MulAut W) w := by
        have h := hbx
        rw [hz1, one_mul] at h
        simpa [hxdef] using h
      exact hfix_eq
    refine ⟨lL⁻¹, L.inv_mem hl0L, b, hbE, ?_, ?_⟩
    · intro hbcent
      have hbcentsec : b ∈ centSec U Z := centSub_le_centSec U Z hbcent
      have hker : b0 ∈ (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z).ker :=
        (CFSG.Quasithin.B5.mem_ker_secHom X₀ hX₀U hX₀Z b0).2 (by simpa [b] using hbcentsec)
      have hbsec1 : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 = 1 :=
        MonoidHom.mem_ker.mp hker
      have haE1 : aE = 1 := by rw [← hbsec, hbsec1]
      have hmat1 : CFSG.Quasithin.H.matHom Amat = 1 := by rw [← haEeq, haE1, map_one]
      exact hAne ((CFSG.Quasithin.H.matHom_injective) (by simpa using hmat1))
    · simp only [inv_inv]
      calc ((lL : MulAut W)⁻¹ * b * (lL : MulAut W)) w
          = (lL : MulAut W)⁻¹ (b ((lL : MulAut W) w)) := by simp [MulAut.mul_apply]
        _ = (lL : MulAut W)⁻¹ ((lL : MulAut W) w) := by rw [hfix_wU]
        _ = w := by simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
