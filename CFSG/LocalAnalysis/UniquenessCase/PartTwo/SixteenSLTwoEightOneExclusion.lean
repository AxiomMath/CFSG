module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoEightFixedSpace
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
import CFSG.Quasithin.Background.SimsE214NatCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_exists_conj_of_ne_one
    {W : Type} [Group W] {K : Type} [Field K]
    {H : Subgroup (MulAut W)}
    (π : StatedSL 2 K →* ↥H) {β : W →* Multiplicative (Fin 2 → K)}
    (hβinj : Function.Injective β)
    (hβe : ∀ (γ : StatedSL 2 K) (w : W),
      β ((π γ : MulAut W) w) = CFSG.Quasithin.natAct (StatedSL 2 K) γ (β w)) :
    ∀ u x : W, u ≠ 1 → x ≠ 1 → ∃ g ∈ H, g u = x := by
  intro u x hu hx
  have hβu1 : β u ≠ 1 := by
    intro h
    exact hu (hβinj (by rw [h, map_one]))
  have hβx1 : β x ≠ 1 := by
    intro h
    exact hx (hβinj (by rw [h, map_one]))
  have hua : Multiplicative.toAdd (β u) ≠ 0 := by
    intro h
    apply hβu1
    simpa using congrArg Multiplicative.ofAdd h
  have hxa : Multiplicative.toAdd (β x) ≠ 0 := by
    intro h
    apply hβx1
    simpa using congrArg Multiplicative.ofAdd h
  obtain ⟨γ, hγ, hγmul⟩ :=
    CFSG.Quasithin.SimsE2.E214N.statedSL_exists_mulVec_eq hua hxa
  let γH : ↥H := π ⟨γ, hγ⟩
  have hout : β ((γH : MulAut W) u) = β x := by
    calc β ((γH : MulAut W) u) =
        CFSG.Quasithin.natAct (StatedSL 2 K) ⟨γ, hγ⟩ (β u) := hβe ⟨γ, hγ⟩ u
      _ = Multiplicative.ofAdd
          (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
            Multiplicative.toAdd (β u)) := rfl
      _ = Multiplicative.ofAdd (Multiplicative.toAdd (β x)) := by rw [hγmul]
      _ = β x := ofAdd_toAdd (β x)
  have hmap : (γH : MulAut W) u = x := hβinj hout
  exact ⟨(γH : MulAut W), (γH).2, hmap⟩

private theorem s168e3_false_of_sl2_eight_realization
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [fieldK : Field K]
    (hK8 : Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (h7 : 7 ∈ D.sig) (hfix : fixV (lBar V₀ V hV L) = ⊥) : False := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  have hHA : H ≤ A := by
    show lBar V₀ V hV L ≤ Mbar D.M V₀ V hV
    simpa only [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hrealTop := s16g_realizes_top c.conc hs (StatedSL 2 K) hreal
  rw [hfix] at hrealTop
  obtain ⟨π, hπ⟩ := hrealTop
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL 2 K)) rfl rfl hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    apply Subtype.ext
    exact Subgroup.mem_bot.mp ((hβk u).mp hu)
  let βW : W →* Multiplicative (Fin 2 → K) :=
    β.comp (Subgroup.topEquiv (G := W)).symm.toMonoidHom
  have hβW_apply : ∀ w : W, βW w = β ⟨w, Subgroup.mem_top w⟩ := fun w => rfl
  have hβWe : ∀ (γ : StatedSL 2 K) (w : W),
      βW ((π γ : MulAut W) w) =
        CFSG.Quasithin.natAct (StatedSL 2 K) γ (βW w) := by
    intro γ w
    rw [hβW_apply, hβW_apply]
    exact hβe γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)
  have hβWinj : Function.Injective βW := by
    intro w w' h
    rw [hβW_apply, hβW_apply] at h
    exact congrArg Subtype.val (hβinj h)
  have hβWsurj : Function.Surjective βW := by
    intro y
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨(u : W), by rw [hβW_apply]; exact hu⟩
  let e : W ≃* Multiplicative (Fin 2 → K) :=
    MulEquiv.ofBijective βW ⟨hβWinj, hβWsurj⟩
  have hWcard : Nat.card W = 64 := by
    rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd)]
    simp [Nat.card_fun, hK8]
  have hWnt : Nontrivial W :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; norm_num)
  have htrans := s168e3_exists_conj_of_ne_one (W := W) (K := K) (H := H)
    π (β := βW) hβWinj hβWe
  have hcube : ¬ 7 ^ 3 ∣ Nat.card A := by
    have h1 : Nat.card A ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card A
    have h2 : Nat.card (MulAut W) ∣ Nat.card (GL (Fin 6) (ZMod 2)) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
        (q := 2) (d := 6) (V := W) (fun a b => mul_comm a b)
        (s15_Infra_vtil_sq_eq_one V₀ V hV) (by rw [hWcard]; norm_num)
    have hGL : Nat.card (GL (Fin 6) (ZMod 2)) = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by
      rw [Matrix.card_GL_field, ZMod.card]
      simp [Fin.prod_univ_succ]
    have hnot : ¬ 7 ^ 3 ∣ Nat.card (GL (Fin 6) (ZMod 2)) := by
      rw [hGL]
      norm_num
    intro h
    exact hnot (h.trans (h1.trans h2))
  have h2le : 2 ≤ CFSG.Open.pRank 7 A := by
    simpa only [A] using c.two_le_pRank_mbar h7
  obtain ⟨E, hEA, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (G := MulAut W) (p := 7) (hp := ⟨Nat.prime_seven⟩) (H := A) (k := 2) h2le
  have hEcard49 : 7 ^ 2 ≤ Nat.card ↥E := by rw [hEcard]
  have hcop : ¬ 7 ∣ Nat.card W := by rw [hWcard]; norm_num
  let : CFSG.IsElementaryAbelian 7 ↥E := CFSG.Open.IsElemAbelian.isElementaryAbelian hEab
  let : MulDistribMulAction ↥E W := MulDistribMulAction.compHom (A := W) E.subtype
  have hgen : (⨆ (a : ↥E) (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) W) = ⊤ :=
    CFSG.SolvableHall.coprime_centralizer_generation
      (p := 7) (A := ↥E) (H := W) hEcard49 hcop
  have hsome : ∃ a : ↥E, a ≠ 1 ∧
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) W ≠ ⊥ := by
    by_contra h
    have hbotall : ∀ a : ↥E, a ≠ 1 →
        CFSG.fixedPointSubgroup (Subgroup.zpowers a) W = ⊥ := by
      intro a ha
      by_contra hne
      exact h ⟨a, ha, hne⟩
    have hbot : (⨆ (a : ↥E) (_ : a ≠ 1),
        CFSG.fixedPointSubgroup (Subgroup.zpowers a) W) = ⊥ :=
      iSup₂_eq_bot.mpr hbotall
    rw [hgen] at hbot
    exact top_ne_bot hbot
  obtain ⟨a, ha1, hane⟩ := hsome
  obtain ⟨u, hu1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hane
  have hu : (u : W) ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) W := u.2
  have hu1 : (u : W) ≠ 1 := fun h => hu1sub (Subtype.ext h)
  have hau : a • (u : W) = (u : W) :=
    (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a (u : W)).mp hu
  let b0 : MulAut W := (a : MulAut W)
  have hb0E : b0 ∈ E := a.2
  have hb0A : b0 ∈ A := hEA hb0E
  have hb01 : b0 ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb0u : b0 (u : W) = (u : W) := by
    simpa [MulDistribMulAction.compHom, Subgroup.smul_def, MulAut.smul_def] using hau
  have hb07 : b0 ^ 7 = 1 := hEab.2 b0 hb0E
  have hordb0 : orderOf b0 = 7 :=
    (orderOf_eq_prime_iff (hp := ⟨Nat.prime_seven⟩)).mpr ⟨hb07, hb01⟩
  have hpoint : ∀ x : W, x ≠ 1 → ∃ b ∈ A, orderOf b = 7 ∧ b x = x := by
    intro x hx
    obtain ⟨g, hgH, hgu⟩ := htrans (u : W) x hu1 hx
    let b : MulAut W := g * b0 * g⁻¹
    have hbA : b ∈ A :=
      A.mul_mem (A.mul_mem (hHA hgH) hb0A) (A.inv_mem (hHA hgH))
    have hb7 : b ^ 7 = 1 := by
      show (g * b0 * g⁻¹) ^ 7 = 1
      rw [conj_pow, hb07, mul_one, mul_inv_cancel]
    have hb1 : b ≠ 1 := by
      have hbconj : b = (MulAut.conj g) b0 := by
        simp [b, MulAut.conj_apply, mul_assoc]
      intro h
      apply hb01
      apply (MulAut.conj g).injective
      rw [← hbconj, h, map_one]
    have hordb : orderOf b = 7 :=
      (orderOf_eq_prime_iff (hp := ⟨Nat.prime_seven⟩)).mpr ⟨hb7, hb1⟩
    have hgu' : g⁻¹ x = (u : W) := by
      simpa using (congrArg (fun y : W => g⁻¹ y) hgu).symm
    have hbx : b x = x := by
      calc b x = g (b0 (g⁻¹ x)) := rfl
        _ = g (u : W) := by rw [hgu', hb0u]
        _ = x := hgu
    exact ⟨b, hbA, hordb, hbx⟩
  have hk : S168e3Kernel A 7 :=
    s168e3_kernel_of_cube Nat.prime_seven A hcube hpoint
  exact s168e3_false_of_kernel c Nat.prime_seven h7 hk

theorem s168e3_false_of_sl2_eight_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    False := by
  have hfacts := s168e3_seven_mem_and_fixV_eq_bot_of_sl2_eight_of_s_eq_one
    c hcomp hthin hs hrow
  obtain ⟨_hSL, K, hKf, _hKfin, hKcard, hreal⟩ := hrow
  have hK8 : Nat.card K = 8 := by
    rw [hKcard]
    norm_num
  exact s168e3_false_of_sl2_eight_realization
    (K := K) (fieldK := hKf) c hs hK8 hreal hfacts.1 hfacts.2

theorem s168e3_concl163F_of_sl2_eight_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    Concl163F D V₀ V hV L :=
  (s168e3_false_of_sl2_eight_of_s_eq_one c hcomp hthin hs hrow).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
