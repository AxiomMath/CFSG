module

public import CFSG.Quasithin.Background.RonanH45A
public import CFSG.Quasithin.Background.RonanH45C
public import CFSG.Quasithin.Background.RonanH44Fix

public section

namespace CFSG.Quasithin.RonanH45

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
private theorem transv02_mul_transv12_entries (b b' : K) :
    ((SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) b *
        SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) b' :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = b ∧
      ((SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) b *
        SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) b' :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = b' := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.single_apply]

omit [Finite K] in
private theorem rhoQ2_mem_Q2_comm {x y : SpecialLinearGroup (Fin 3) K} (hx : x ∈ Q2 K)
    (hy : y ∈ Q2 K) : x * y = y * x := by
  apply uni3_ext (mul_mem hx.1 hy.1) (mul_mem hy.1 hx.1)
  · rw [uni3_mul_01 hx.1 hy.1, uni3_mul_01 hy.1 hx.1, add_comm]
  · rw [uni3_mul_02 hx.1 hy.1, uni3_mul_02 hy.1 hx.1, hx.2, hy.2]
    ring
  · rw [uni3_mul_12 hx.1 hy.1, uni3_mul_12 hy.1 hx.1, add_comm]

omit [Finite K] in
private theorem rhoQ2_mem_Q2_sq {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ Q2 K) :
    x ^ 2 = 1 := by
  rw [sq]
  apply uni3_ext (mul_mem hx.1 hx.1) (one_mem _)
  · rw [uni3_mul_01 hx.1 hx.1, hx.2]
    simp
  · rw [uni3_mul_02 hx.1 hx.1, hx.2, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    simp
  · rw [uni3_mul_12 hx.1 hx.1, CharTwo.add_self_eq_zero]
    simp

theorem card_Q2_eq (hK : Nat.card K = (2 ^ n) ^ 2) : Nat.card (Q2 K) = Nat.card K ^ 2 := by
  refine le_antisymm card_Q2_le ?_
  have hf : Function.Injective (fun p : K × K =>
      (⟨SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) p.1 *
        SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) p.2,
        mul_mem (transvection02_mem_Q2 p.1) (transvection12_mem_Q2 p.2)⟩ : ↥(Q2 K))) := by
    rintro ⟨b, b'⟩ ⟨c, c'⟩ h
    have h' : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) b *
        SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) b' =
        SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c *
        SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c' :=
      congrArg Subtype.val h
    have e1 : b = c := by
      have hb := (transv02_mul_transv12_entries b b').1
      rw [h'] at hb
      exact hb.symm.trans (transv02_mul_transv12_entries c c').1
    have e2 : b' = c' := by
      have hb := (transv02_mul_transv12_entries b b').2
      rw [h'] at hb
      exact hb.symm.trans (transv02_mul_transv12_entries c c').2
    rw [e1, e2]
  calc Nat.card K ^ 2 = Nat.card (K × K) := by rw [Nat.card_prod, sq]
    _ ≤ Nat.card (Q2 K) := Nat.card_le_card_of_injective _ hf

theorem card_rhoQ2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥((Q2 K).map (rho hK)) = 2 ^ (4 * n) := by
  rw [card_map_rho_of_inj (P := Q2 K) hK (fun x hx h => eq_one_of_rho_uni3 hK hx.1 h),
    card_Q2_eq hK, hK]
  ring

theorem rhoQ2_mem_aSet (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hLM : img hK ≤ M) :
    (Q2 K).map (rho hK) ∈ E3.aSet (3 * n) M := by
  have : Finite (HMod n K) := Finite.of_injective _ (mat_injective (n := n) (K := K))
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hcard := card_rhoQ2 hn hK
  have hAL : (Q2 K).map (rho hK) ≤ img hK := Subgroup.map_le_range _ _
  have hA1 : (Q2 K).map (rho hK) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have h1 : 1 < 2 ^ (4 * n) := Nat.one_lt_two_pow (by omega)
    exact (ne_of_lt h1) hcard
  have hAe : IsElemAbelian2 ((Q2 K).map (rho hK)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, rhoQ2_mem_Q2_comm hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, rhoQ2_mem_Q2_sq hx, map_one]
  refine ⟨hAL.trans hLM, hA1, hAe, fun B hB hm => ?_⟩
  have hA2 : IsPGroup 2 ((Q2 K).map (rho hK)) := E3.isPGroup_of_isElemAbelian2 hAe
  have hsize := E3.card_eq_two_pow_mul hA2 hB
  rw [hcard] at hsize
  have hBn : 2 ^ n < Nat.card B := by
    by_contra hle
    have hle' : Nat.card B ≤ 2 ^ n := not_lt.1 hle
    have h1 := Nat.mul_le_mul (le_refl (2 ^ E3.mQuot ((Q2 K).map (rho hK)) B)) hle'
    rw [← hsize, ← pow_add] at h1
    have h2 : 2 ^ (E3.mQuot ((Q2 K).map (rho hK)) B + n) < 2 ^ (4 * n) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd h1 (not_le.2 h2)
  have hPB : (B.comap (rho hK) ⊓ Q2 K).map (rho hK) = B := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hb
      obtain ⟨x, hxQ, rfl⟩ := hB hb
      exact ⟨x, ⟨hb, hxQ⟩, rfl⟩
  have hinj : ∀ x ∈ B.comap (rho hK) ⊓ Q2 K, rho hK x = 1 → x = 1 :=
    fun x hx h => eq_one_of_rho_uni3 hK hx.2.1 h
  have hcardP : Nat.card ↥(B.comap (rho hK) ⊓ Q2 K) = Nat.card ↥B := by
    rw [← card_map_rho_of_inj hK hinj, hPB]
  have hP01 : ∀ x ∈ B.comap (rho hK) ⊓ Q2 K, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 :=
    fun x hx => hx.2.2
  have hfix := fixV_eq_blkW_of_Q2 hn hK (P := B.comap (rho hK) ⊓ Q2 K)
    (fun x hx => hx.2.1) hP01 (by rw [hcardP]; exact hBn)
  rw [hPB] at hfix
  rw [hfix, fixV_rhoQ2 hn hK]

private theorem rhoQ2_mem_fixV_conj {W : Type*} [CommGroup W] (B : Subgroup (MulAut W))
    (g : MulAut W) (v : W) : v ∈ fixV (conjSubgroup B g) ↔ g v ∈ fixV B := by
  have hinv : ∀ z : W, g (g⁻¹ z) = z := fun z => by
    rw [← MulAut.mul_apply, mul_inv_cancel] <;> rfl
  have hinv' : ∀ z : W, g⁻¹ (g z) = z := fun z => by
    rw [← MulAut.mul_apply, inv_mul_cancel] <;> rfl
  constructor
  · intro hv y hy
    have hmem : g⁻¹ * y * g ∈ conjSubgroup B g := by
      rw [mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hy
    have h : g⁻¹ (y (g v)) = v := hv _ hmem
    calc y (g v) = g (g⁻¹ (y (g v))) := (hinv _).symm
      _ = g v := by rw [h]
  · intro hg x hx
    have hmem : g * x * g⁻¹ ∈ B := mem_conjSubgroup_iff.1 hx
    have h : g (x (g⁻¹ (g v))) = g v := hg _ hmem
    rw [hinv'] at h
    exact g.injective h

private theorem rhoQ2_conj_mem_aSet {W : Type*} [CommGroup W] {k : ℕ}
    {X A Y : Subgroup (MulAut W)} (g : MulAut W) (hA : A ∈ E3.aSet k X)
    (hY : conjSubgroup A g ≤ Y) : conjSubgroup A g ∈ E3.aSet k Y := by
  obtain ⟨-, hA1, ⟨hcomm, hsq⟩, hfix⟩ := hA
  refine ⟨hY, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro h0
    apply hA1
    rw [← E3.conjSubgroup_conj_inv A g, h0, E3.conjSubgroup_bot]
  · intro a ha b hb
    have hc := hcomm _ (mem_conjSubgroup_iff.1 ha) _ (mem_conjSubgroup_iff.1 hb)
    calc a * b = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹)) * g := by rw [hc]
      _ = b * a := by group
  · intro a ha
    have hs := hsq _ (mem_conjSubgroup_iff.1 ha)
    have e : g⁻¹ * (g * a * g⁻¹) ^ 2 * g = a ^ 2 := by
      rw [pow_two, pow_two]
      group
    calc a ^ 2 = g⁻¹ * (g * a * g⁻¹) ^ 2 * g := e.symm
      _ = g⁻¹ * 1 * g := by rw [hs]
      _ = 1 := by group
  · intro B hB hm
    obtain ⟨B0, rfl⟩ : ∃ B0, conjSubgroup B0 g = B :=
      ⟨conjSubgroup B g⁻¹, E3.conjSubgroup_inv_conj B g⟩
    have hB0 : B0 ≤ A := (E3.conjSubgroup_le_conjSubgroup_iff g).1 hB
    rw [E3.mQuot_conjSubgroup] at hm
    have hf : fixV B0 = fixV A := hfix B0 hB0 hm
    ext v
    rw [rhoQ2_mem_fixV_conj, rhoQ2_mem_fixV_conj, hf]

private theorem rhoQ2_false_of_mem_aSet_lt (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK)
    (hC : ∀ i ∈ M, i ∉ img hK → orderOf i = 2 →
      M ⊓ centSub (fixV (Subgroup.zpowers i)) = Subgroup.zpowers i)
    {T : Subgroup (MulAut (HMod n K))} (hTM : T ≤ M)
    (hTL : T ⊓ img hK ≤ (stabZ K ⊓ stabW K).map (rho hK))
    {k : ℕ} (hk : 3 * n < k) {Y : Subgroup (MulAut (HMod n K))} (hY : Y ∈ E3.aSet k T) :
    False := by
  have : Finite (HMod n K) := Finite.of_injective _ (mat_injective (n := n) (K := K))
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hY2 : Y ∈ E3.aSet (2 * n + 1) T := E3.aSet_anti (show 2 * n + 1 ≤ k by omega) T hY
  have hYQ : Y ≤ (Q2 K).map (rho hK) := part1 hn hK hMN hC hTM hTL Y hY2
  have hYP : IsPGroup 2 Y := E3.isPGroup_of_isElemAbelian2 hY.2.2.1
  have hm : 3 * n + 1 ≤ E3.mQuot Y ⊥ :=
    (show 3 * n + 1 ≤ k by omega).trans (E3.le_mQuot_bot_of_mem_aSet hY)
  have hcardY : 2 ^ (3 * n) < Nat.card Y := by
    have h := E3.card_eq_two_pow_mul hYP (bot_le : (⊥ : Subgroup (MulAut (HMod n K))) ≤ Y)
    rw [Subgroup.card_bot, mul_one] at h
    rw [h]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hGam : E3.gammaCheck (3 * n) Y = Hhyp n K := gammaCheck_eq hn hK hYQ hcardY
  have hGamFix : E3.gammaCheck (3 * n) Y = fixV Y := by
    apply le_antisymm
    · unfold E3.gammaCheck
      refine iSup_le fun X => iSup_le fun hXY => iSup_le fun hX => ?_
      exact le_of_eq (hY.2.2.2 X hXY (by omega))
    · exact fixV_le_gammaCheck le_rfl (by rw [E3.mQuot_self]; exact Nat.zero_le _)
  have hHle : Hhyp n K ≤ fixV Y := le_of_eq (hGam.symm.trans hGamFix)
  exact hY.2.1 (eq_bot_of_Hhyp_le_fixV hn hK hYQ hHle)

theorem part3 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hLM : img hK ≤ M) (hMN : M ≤ norm hK)
    (hC : ∀ i ∈ M, i ∉ img hK → orderOf i = 2 →
      M ⊓ centSub (fixV (Subgroup.zpowers i)) = Subgroup.zpowers i)
    {T : Subgroup (MulAut (HMod n K))} (hT : IsSylowIn 2 T M)
    (hTL : T ⊓ img hK ≤ (stabZ K ⊓ stabW K).map (rho hK)) :
    E3.aParam M = 3 * n := by
  have : Finite (HMod n K) := Finite.of_injective _ (mat_injective (n := n) (K := K))
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hA := rhoQ2_mem_aSet hn hK hLM
  have hTM : T ≤ M := hT.1
  have hev : Even (Nat.card M) :=
    E3.even_card_of_isPGroup hA.1 (E3.isPGroup_of_isElemAbelian2 hA.2.2.1) hA.2.1
  rw [E3.aParam, if_pos hev]
  apply le_antisymm
  · refine csSup_le ⟨3 * n, by omega, _, hA⟩ ?_
    rintro k ⟨-, A', hA'⟩
    by_contra! hlt
    obtain ⟨g, -, hle⟩ := E3.exists_le_conj_of_isSylowIn hT hA'.1
      (E3.isPGroup_of_isElemAbelian2 hA'.2.2.1)
    have hY : conjSubgroup A' g⁻¹ ≤ T := by
      intro x hx
      have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ A' := mem_conjSubgroup_iff.1 hx
      have hz : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ ∈ T := mem_conjSubgroup_iff.1 (hle hx')
      have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
      rwa [e] at hz
    exact rhoQ2_false_of_mem_aSet_lt hn hK hMN hC hTM hTL hlt (rhoQ2_conj_mem_aSet g⁻¹ hA' hY)
  · exact le_csSup (E3.aSet_bddAbove M) ⟨by omega, _, hA⟩

end CFSG.Quasithin.RonanH45
