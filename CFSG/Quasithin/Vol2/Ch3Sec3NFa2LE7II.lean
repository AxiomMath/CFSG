module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7Base
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem e7_caseII {Z U TC G2 R : Subgroup G} {g : G} (h : E7Pair Z U TC G2 R g)
    (hWR : ∃ c ∈ G2, conjSub c (conjSub g U) ≤ R)
    (hlt : centralizerMod Z (conjSub g U) U < conjSub g U)
    (hle : mIdx U (centralizerMod (conjSub g Z) U (conjSub g U)) ≤
      mIdx (conjSub g U) (centralizerMod Z (conjSub g U) U)) :
    ∃ B : Subgroup G, B ≤ R ∧ ¬ B ≤ TC ∧
      mIdx U (centralizerMod Z U B) ≤ 2 * mIdx (B ⊔ TC) TC := by
  obtain ⟨c, hcG2, hcR⟩ := hWR
  set W := conjSub g U with hWdef
  set A := conjSub g Z with hAdef
  set D := centralizerMod A U W with hDdef
  set D' := centralizerMod Z W U with hD'def
  set cM := centralizerMod Z U W with hcMdef
  have hpU : IsPGroup 2 U := CFSG.Quasithin.F7.isPGroup_of_isElemAbelian h.U_ab
  have hY : IsElemAbelian 2 W := CFSG.Quasithin.F7.isElemAbelian_conjSub (g := g) h.U_ab
  have hpW : IsPGroup 2 W := CFSG.Quasithin.F7.isPGroup_of_isElemAbelian hY
  have hcardA : Nat.card A = 2 :=
    (CFSG.Quasithin.CosetGeom.card_conjSub g Z).trans h.card_Z
  have hWN : W ≤ Subgroup.normalizer (TC : Set G) := h.W_le.trans h.G2_normTC
  have hUN : U ≤ Subgroup.normalizer (Z : Set G) := by
    intro u hu
    exact Subgroup.centralizer_le_normalizer _ (h.G2_cent (h.U_le hu))
  have hDU : D ≤ U := centralizerMod_le_left A U W
  have hD'le : D' ≤ W := centralizerMod_le_left Z W U
  have hZA : Z ⊓ A = ⊥ := by
    by_contra hne
    apply h.ne_A
    have hle' : Z ≤ A := CFSG.Quasithin.le_of_card_eq_two_of_inf_ne_bot h.card_Z hne
    exact (Subgroup.eq_of_le_of_card_ge hle' (hcardA.trans h.card_Z.symm).le).symm
  have hAW : A ≤ Subgroup.centralizer (W : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hz : g⁻¹ * a * g ∈ Z := CFSG.Quasithin.mem_conjSub.mp ha
    have hu : g⁻¹ * w * g ∈ U := CFSG.Quasithin.mem_conjSub.mp hw
    have e := Subgroup.mem_centralizer_iff.mp (h.U_le.trans h.G2_cent hu) _ hz
    calc w * a = g * (g⁻¹ * w * g * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * (g⁻¹ * w * g)) * g⁻¹ := by rw [e]
      _ = a * w := by group
  have hAU : A ≤ Subgroup.centralizer (U : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hz : g⁻¹ * a * g ∈ Z := CFSG.Quasithin.mem_conjSub.mp ha
    have hb : g⁻¹ * u * g ∈ conjSub g⁻¹ U := by
      have := CFSG.Quasithin.mul_mem_conjSub (g := g⁻¹) hu
      rwa [inv_inv] at this
    have e := Subgroup.mem_centralizer_iff.mp (h.G2_cent (h.R_le (h.B_le hb))) _ hz
    calc u * a = g * (g⁻¹ * u * g * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * (g⁻¹ * u * g)) * g⁻¹ := by rw [e]
      _ = a * u := by group
  have hCX : A ≤ Subgroup.centralizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_iff.mp (hAU ha) d (hDU hd)
  have hDcomm : ⁅D, W⁆ ≤ A := Subgroup.commutator_le.mpr fun d hd w hw => hd.2.2 w hw
  have hpair := CFSG.Quasithin.relIndex_eq_of_commutator_le (X := D) (Y := W) (C := A)
    hY hcardA hDcomm hCX hAW
  have hD'eq : D' = W ⊓ TC := by
    rw [← h.e5b]
    ext x
    constructor
    · rintro ⟨hxW, hxN, hx⟩
      exact ⟨hxW, h.W_le hxW, hxN, hx⟩
    · rintro ⟨hxW, -, hxN, hx⟩
      exact ⟨hxW, hxN, hx⟩
  have hD'C : D' ≤ W ⊓ Subgroup.centralizer (D : Set G) := by
    intro x hx
    refine ⟨hD'le hx, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hcA : d * x * d⁻¹ * x⁻¹ ∈ A := hd.2.2 x (hD'le hx)
    have hcZ : x * d * x⁻¹ * d⁻¹ ∈ Z := hx.2.2 d (hDU hd)
    have hmem : d * x * d⁻¹ * x⁻¹ ∈ Z ⊓ A := by
      refine ⟨?_, hcA⟩
      have e : (x * d * x⁻¹ * d⁻¹)⁻¹ = d * x * d⁻¹ * x⁻¹ := by group
      rw [← e]
      exact Z.inv_mem hcZ
    rw [hZA, Subgroup.mem_bot] at hmem
    calc d * x = (d * x * d⁻¹ * x⁻¹) * (x * d) := by group
      _ = x * d := by rw [hmem, one_mul]
  have hCDcM : D ⊓ Subgroup.centralizer (W : Set G) ≤ cM := by
    intro x hx
    refine ⟨hDU hx.1, hUN (hDU hx.1), fun y hy => ?_⟩
    have hyx := Subgroup.mem_centralizer_iff.mp hx.2 y hy
    have e : x * y * x⁻¹ * y⁻¹ = 1 := by rw [← hyx]; group
    rw [e]
    exact Z.one_mem
  have hrp : ∀ X Y : Subgroup G, 0 < Y.relIndex X := fun X Y =>
    Nat.pos_of_ne_zero (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
  have iD' : D'.relIndex W = 2 ^ mIdx W D' := CFSG.Quasithin.HypF98.relIndex_eq_two_pow_mIdx hpW
  have iD : D.relIndex U = 2 ^ mIdx U D := CFSG.Quasithin.HypF98.relIndex_eq_two_pow_mIdx hpU
  have icM : cM.relIndex U = 2 ^ mIdx U cM := CFSG.Quasithin.HypF98.relIndex_eq_two_pow_mIdx hpU
  have t1 := Subgroup.relIndex_mul_relIndex D' (W ⊓ Subgroup.centralizer (D : Set G)) W hD'C
    inf_le_left
  have t2 := Subgroup.relIndex_mul_relIndex (D ⊓ Subgroup.centralizer (W : Set G)) D U
    inf_le_left hDU
  have t3 := Subgroup.relIndex_mul_relIndex (D ⊓ Subgroup.centralizer (W : Set G)) cM U hCDcM
    (centralizerMod_le_left Z U W)
  have hfle : (W ⊓ Subgroup.centralizer (D : Set G)).relIndex W ≤ D'.relIndex W := by
    rw [← t1]
    exact Nat.le_mul_of_pos_left _ (hrp _ _)
  have hdle : D.relIndex U ≤ D'.relIndex W := by
    rw [iD, iD']
    exact Nat.pow_le_pow_right (by norm_num) hle
  have hcle : cM.relIndex U ≤
      (D ⊓ Subgroup.centralizer (W : Set G)).relIndex D * D.relIndex U := by
    rw [t2, ← t3]
    exact Nat.le_mul_of_pos_left _ (hrp _ _)
  have hcle2 : cM.relIndex U ≤ D'.relIndex W * D'.relIndex W := by
    refine hcle.trans ?_
    rw [hpair]
    exact Nat.mul_le_mul hfle hdle
  rw [icM, iD', ← pow_add, ← two_mul] at hcle2
  have hmain : mIdx U cM ≤ 2 * mIdx W D' := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcle2
  have hWidx : mIdx W D' = mIdx (W ⊔ TC) TC := by
    rw [hD'eq]
    exact mIdx_inf_eq_mIdx_sup hWN
  have hcTC : conjSub c TC = TC :=
    CFSG.Quasithin.F7.conjSub_eq_of_mem_normalizer (h.G2_normTC hcG2)
  have hc'TC : conjSub c⁻¹ TC = TC :=
    CFSG.Quasithin.F7.conjSub_eq_of_mem_normalizer (h.G2_normTC (G2.inv_mem hcG2))
  have hcZ : conjSub c Z = Z :=
    CFSG.Quasithin.F7.conjSub_eq_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (h.G2_cent hcG2))
  have hcU : conjSub c U = U :=
    CFSG.Quasithin.F7.conjSub_eq_of_mem_normalizer (h.G2_normU hcG2)
  refine ⟨conjSub c W, hcR, ?_, ?_⟩
  · intro hBT
    have hWT : W ≤ TC := by
      have h1 : conjSub c⁻¹ (conjSub c W) ≤ conjSub c⁻¹ TC :=
        CFSG.Quasithin.conjSub_mono _ hBT
      rw [CFSG.Quasithin.conjSub_conjSub_inv, hc'TC] at h1
      exact h1
    have hlt' : W ⊓ TC < W := by
      rw [← hD'eq]
      exact hlt
    rw [inf_eq_left.mpr hWT] at hlt'
    exact lt_irrefl _ hlt'
  · have hconj : conjSub c cM = centralizerMod Z U (conjSub c W) := by
      rw [hcMdef, CFSG.Quasithin.conjSub_centralizerMod, hcZ, hcU]
    have hm1 : mIdx U (centralizerMod Z U (conjSub c W)) = mIdx U cM := by
      have := CFSG.Quasithin.F9.mIdx_conjSub c U cM
      rw [hcU, hconj] at this
      exact this
    have hm2 : mIdx (conjSub c W ⊔ TC) TC = mIdx (W ⊔ TC) TC := by
      have := CFSG.Quasithin.F9.mIdx_conjSub c (W ⊔ TC) TC
      rw [CFSG.Quasithin.conjSub_sup, hcTC] at this
      exact this
    rw [hm1, hm2, ← hWidx]
    exact hmain

end CFSG.Quasithin.H13.NFa2
