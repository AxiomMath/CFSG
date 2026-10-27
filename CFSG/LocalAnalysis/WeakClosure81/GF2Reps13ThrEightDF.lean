module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightDE
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}
  {z k a : MulAut W} {N : Subgroup (MulAut W)}

@[expose] def s13Comp8 (N R : Subgroup (MulAut W)) : Subgroup W :=
  commSub ⊤ N ⊓ fixV R

private theorem w16g_z_pow_three (hD : Data8 A t z N) : z ^ 3 = 1 := by
  simpa [hD.hz3] using pow_orderOf_eq_one z

private theorem w16g_a_z (hD : Data8 A t z N) (hG : Gen8 A t z N k a) :
    a * z * a⁻¹ = z := by
  rw [hD.hzc a hG.haP]
  group

private theorem w16g_N_map_conj_a (hD : Data8 A t z N) (hG : Gen8 A t z N k a) :
    N.map (MulAut.conj a).toMonoidHom = N := by
  have hz : (MulAut.conj a).toMonoidHom z = z := by
    change MulAut.conj a z = z
    rw [MulAut.conj_apply]
    exact w16g_a_z hD hG
  have hk : (MulAut.conj a).toMonoidHom k = k * z := by
    change MulAut.conj a k = k * z
    rw [MulAut.conj_apply]
    exact hG.hak
  rw [hG.hNeq, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hz, hk]
  have h1 : Subgroup.zpowers (k * z) ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers k := by
    rw [sup_comm]
    exact Subgroup.zpowers_mul_le_sup k z
  have h2 : Subgroup.zpowers k ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers (k * z) := by
    rw [Subgroup.zpowers_le]
    have hmem := Subgroup.mul_mem (Subgroup.zpowers z ⊔ Subgroup.zpowers (k * z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (k * z)))
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers z)))
    simpa using hmem
  exact le_antisymm (sup_le le_sup_left h1) (sup_le le_sup_left h2)

private theorem w16g_N_map_conj_t (hD : Data8 A t z N) (hG : Gen8 A t z N k a) :
    N.map (MulAut.conj t).toMonoidHom = N := by
  have hz : (MulAut.conj t).toMonoidHom z = z := by
    change MulAut.conj t z = z
    rw [MulAut.conj_apply]
    exact hD.htz
  have hk : (MulAut.conj t).toMonoidHom k = k⁻¹ := by
    change MulAut.conj t k = k⁻¹
    rw [MulAut.conj_apply]
    exact hG.htk
  rw [hG.hNeq, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hz, hk,
    Subgroup.zpowers_inv]

private theorem w16g_commSub_N_map_a (hD : Data8 A t z N) (hG : Gen8 A t z N k a) :
    (commSub ⊤ N).map a.toMonoidHom = commSub ⊤ N := by
  rw [← CFSG.Quasithin.Asc81c.commSub_map_conj N a, w16g_N_map_conj_a hD hG]

private theorem w16g_commSub_N_map_t (hD : Data8 A t z N) (hG : Gen8 A t z N k a) :
    (commSub ⊤ N).map t.toMonoidHom = commSub ⊤ N := by
  rw [← CFSG.Quasithin.Asc81c.commSub_map_conj N t, w16g_N_map_conj_t hD hG]

private theorem w16g_zpow_mod (hD : Data8 A t z N) (n : ℕ) :
    z ^ n = z ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, w16g_z_pow_three hD, one_pow, mul_one]

private theorem w16g_zpow_fin_succ (hD : Data8 A t z N) (i : Fin 3) :
    z ^ ((i : ℕ) + 1) = z ^ (((i + 1 : Fin 3) : ℕ)) := by
  have hval : ((i + 1 : Fin 3) : ℕ) = ((i : ℕ) + 1) % 3 := by
    rw [Fin.val_add]
    norm_num
  rw [hval]
  exact w16g_zpow_mod hD ((i : ℕ) + 1)

private theorem w16g_zpow_neg_fin (hD : Data8 A t z N) (i : Fin 3) :
    (z ^ (i : ℕ))⁻¹ = z ^ ((-i : Fin 3) : ℕ) := by
  have hz3 := w16g_z_pow_three hD
  have hsum : (i : ℕ) + (3 - (i : ℕ)) = 3 := by omega
  have hmul : z ^ (i : ℕ) * z ^ (3 - (i : ℕ)) = 1 := by
    rw [← pow_add, hsum, hz3]
  have hinv : z ^ (3 - (i : ℕ)) = (z ^ (i : ℕ))⁻¹ :=
    eq_inv_of_mul_eq_one_right hmul
  rw [Fin.val_neg', ← w16g_zpow_mod hD (3 - (i : ℕ))]
  exact hinv.symm

private theorem w16g_conj_R_a (hD : Data8 A t z N) (hG : Gen8 A t z N k a) (i : Fin 3) :
    (Subgroup.zpowers (k * z ^ (i : ℕ))).map (MulAut.conj a).toMonoidHom =
      Subgroup.zpowers (k * z ^ ((i + 1 : Fin 3) : ℕ)) := by
  rw [MonoidHom.map_zpowers]
  congr 1
  have hz : (MulAut.conj a).toMonoidHom z = z := by
    change MulAut.conj a z = z
    rw [MulAut.conj_apply]
    exact w16g_a_z hD hG
  have hk : (MulAut.conj a).toMonoidHom k = k * z := by
    change MulAut.conj a k = k * z
    rw [MulAut.conj_apply]
    exact hG.hak
  have hval : (MulAut.conj a).toMonoidHom (k * z ^ (i : ℕ)) = (k * z) * z ^ (i : ℕ) := by
    rw [map_mul, map_pow, hk, hz]
  rw [hval, mul_assoc, ← pow_succ']
  rw [w16g_zpow_fin_succ hD i]

private theorem w16g_conj_R_t (hD : Data8 A t z N) (hG : Gen8 A t z N k a) (i : Fin 3) :
    (Subgroup.zpowers (k * z ^ (i : ℕ))).map (MulAut.conj t).toMonoidHom =
      Subgroup.zpowers (k * z ^ ((-i : Fin 3) : ℕ)) := by
  rw [MonoidHom.map_zpowers]
  have hz : (MulAut.conj t).toMonoidHom z = z := by
    change MulAut.conj t z = z
    rw [MulAut.conj_apply]
    exact hD.htz
  have hk : (MulAut.conj t).toMonoidHom k = k⁻¹ := by
    change MulAut.conj t k = k⁻¹
    rw [MulAut.conj_apply]
    exact hG.htk
  have hval : (MulAut.conj t).toMonoidHom (k * z ^ (i : ℕ)) = k⁻¹ * z ^ (i : ℕ) := by
    rw [map_mul, map_pow, hk, hz]
  rw [hval, ← Subgroup.zpowers_inv]
  congr 1
  rw [mul_inv_rev, inv_inv, w16g_zpow_neg_fin hD i]
  exact ((show Commute k z from hG.hkc).pow_right _).symm

private theorem w16g_comp_map_a (hD : Data8 A t z N) (hG : Gen8 A t z N k a) (i : Fin 3) :
    (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))).map a.toMonoidHom =
      s13Comp8 N (Subgroup.zpowers (k * z ^ ((i + 1 : Fin 3) : ℕ))) := by
  have hU := w16g_commSub_N_map_a hD hG
  have hR := w16g_conj_R_a hD hG i
  simp only [s13Comp8]
  rw [Subgroup.map_inf _ _ _ a.injective, hU]
  congr 1
  rw [← CFSG.Quasithin.Asc81c.fixV_map_conj (Subgroup.zpowers (k * z ^ (i : ℕ))) a, hR]

private theorem w16g_comp_map_t (hD : Data8 A t z N) (hG : Gen8 A t z N k a) (i : Fin 3) :
    (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))).map t.toMonoidHom =
      s13Comp8 N (Subgroup.zpowers (k * z ^ ((-i : Fin 3) : ℕ))) := by
  have hU := w16g_commSub_N_map_t hD hG
  have hR := w16g_conj_R_t hD hG i
  simp only [s13Comp8]
  rw [Subgroup.map_inf _ _ _ t.injective, hU]
  congr 1
  rw [← CFSG.Quasithin.Asc81c.fixV_map_conj (Subgroup.zpowers (k * z ^ (i : ℕ))) t, hR]

private theorem w16g_rk_map (g : MulAut W) (S : Subgroup W) :
    rk ↥(S.map g.toMonoidHom) = rk S := by
  unfold rk
  rw [Subgroup.card_map_of_injective g.injective]

theorem s13_eight_decomp (h : Cfg133 A t 3) (hD : Data8 A t z N) (hG : Gen8 A t z N k a) :
    iSupIndep (fun i : Fin 3 => s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) ∧
      (⨆ i : Fin 3, s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) = commSub ⊤ N ∧
      ∀ i : Fin 3, rk ↥(s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) = 2 := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have hNcard : Nat.card ↥N = 9 := by
    have h9 := w16g_card_of_isElemAbelianOfRank (p := 3) (n := 2) hD.hN
    norm_num at h9
    exact h9
  have hNodd : Odd (Nat.card ↥N) := by rw [hNcard]; norm_num
  have hZodd : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hD.hz3]; norm_num
  have hEelem : CFSG.Open.IsElemAbelian 3 N :=
    w16g_isElemAbelian_of_isElemAbelianOfRank (p := 3) (n := 2) (X := N) hD.hN
  have hUstab : StableUnder N (commSub ⊤ N) :=
    fun x hx u hu => CFSG.Quasithin.Asc81c.commSub_stable' hx hu
  have hUU : commSub (commSub ⊤ N) N = commSub ⊤ N :=
    CFSG.Quasithin.Asc81c.commSub_commSub_eq' hW2 hNodd
  have hdecomp := inf_fixV_hyperplane_decomposition hW2 (p := 3) Nat.prime_three (by norm_num)
    N hEelem hUstab hUU
  have hzk : Commute z k := hG.hkc.symm
  have hhyper : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N =
      {Subgroup.zpowers z} ∪ Set.range (fun i : Fin 3 => Subgroup.zpowers (k * z ^ (i : ℕ))) := by
    rw [hG.hNeq]
    exact w16g_hyperplanes_sup_zpowers Nat.prime_three hD.hz3 hG.hk3 hzk hG.hkz
  let D : Fin 3 → CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N :=
    fun i => ⟨Subgroup.zpowers (k * z ^ (i : ℕ)),
      by rw [hhyper]; exact Or.inr ⟨i, rfl⟩⟩
  have hD_inj : Function.Injective D := by
    intro i j hij
    have h1 : Subgroup.zpowers (k * z ^ (i : ℕ)) = Subgroup.zpowers (k * z ^ (j : ℕ)) :=
      congrArg (fun x : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N =>
        (x : Subgroup (MulAut W))) hij
    exact (w16g_zpowers_mul_pow_injective Nat.prime_three hD.hz3 hG.hk3 hzk hG.hkz).1 h1
  let F : Fin 3 → Subgroup W := fun i => commSub ⊤ N ⊓ fixV ((D i : Subgroup (MulAut W)))
  have hFind : iSupIndep F := hdecomp.1.comp hD_inj
  let Zhyp : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N :=
    ⟨Subgroup.zpowers z, by rw [hhyper]; exact Or.inl rfl⟩
  have hsup_eq : (⨆ D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N,
        commSub ⊤ N ⊓ fixV (D' : Subgroup (MulAut W))) =
      (commSub ⊤ N ⊓ fixV (Subgroup.zpowers z)) ⊔ ⨆ i : Fin 3, F i := by
    apply le_antisymm
    · refine iSup_le fun D' => ?_
      have hD' : (D' : Subgroup (MulAut W)) ∈ {Subgroup.zpowers z} ∪
          Set.range (fun i : Fin 3 => Subgroup.zpowers (k * z ^ (i : ℕ))) := by
        rw [← hhyper]; exact D'.2
      rcases hD' with hD' | ⟨i, hDi⟩
      · have hDZ : D' = Zhyp := Subtype.ext hD'
        rw [hDZ]
        exact le_sup_left
      · have hDD : D' = D i := Subtype.ext hDi.symm
        rw [hDD]
        exact le_sup_of_le_right (le_iSup F i)
    · refine sup_le ?_ ?_
      · exact le_iSup
          (fun D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N =>
            commSub ⊤ N ⊓ fixV (D' : Subgroup (MulAut W))) Zhyp
      · refine iSup_le fun i => ?_
        exact le_iSup
          (fun D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 N =>
            commSub ⊤ N ⊓ fixV (D' : Subgroup (MulAut W))) (D i)
  have hZbot : commSub ⊤ N ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    rw [hD.hNV, inf_comm]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hZodd
  have hU_eq : commSub ⊤ N = (commSub ⊤ N ⊓ fixV (Subgroup.zpowers z)) ⊔ ⨆ i : Fin 3, F i := by
    nth_rewrite 1 [← hdecomp.2]
    exact hsup_eq
  have hsup : (⨆ i : Fin 3, F i) = commSub ⊤ N := by
    have hh := hU_eq
    rw [hZbot, bot_sup_eq] at hh
    exact hh.symm
  have hstep : ∀ i : Fin 3, rk (F i) = rk (F (i + 1)) := by
    intro i
    have hh := w16g_comp_map_a hD hG i
    change (F i).map a.toMonoidHom = F (i + 1) at hh
    rw [← hh, w16g_rk_map]
  have hrk_eq : ∀ i : Fin 3, rk (F i) = rk (F 0) := by
    intro i
    have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases h3 with rfl | rfl | rfl
    · rfl
    · simpa using (hstep 0).symm
    · have h21 : rk (F 2) = rk (F 1) := by simpa using (hstep 1).symm
      rw [h21]
      simpa using (hstep 0).symm
  have hsum : rk ↥(⨆ i : Fin 3, F i) = ∑ i : Fin 3, rk (F i) :=
    w16g_rk_iSup_eq_sum hW2 F hFind
  have hrkU : rk ↥(commSub ⊤ N) = 6 := by rw [hD.hNV]; exact hD.hrkz
  have hthree : ∑ i : Fin 3, rk (F i) = 3 * rk (F 0) := by
    rw [Finset.sum_congr rfl fun i _ => hrk_eq i]
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : rk (F 0) = 2 := by
    have h6 : rk ↥(commSub ⊤ N) = ∑ i : Fin 3, rk (F i) := by
      rw [← hsup]; exact hsum
    rw [hrkU, hthree] at h6
    omega
  refine ⟨hFind, hsup, fun i => ?_⟩
  change rk ↥(F i) = 2
  rw [hrk_eq i, h2]

theorem s13_eight_comp_map_a (hD : Data8 A t z N) (hG : Gen8 A t z N k a) (i : Fin 3) :
    (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))).map a.toMonoidHom =
      s13Comp8 N (Subgroup.zpowers (k * z ^ ((i + 1 : Fin 3) : ℕ))) :=
  w16g_comp_map_a hD hG i

theorem s13_eight_comp_map_t (hD : Data8 A t z N) (hG : Gen8 A t z N k a) (i : Fin 3) :
    (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))).map t.toMonoidHom =
      s13Comp8 N (Subgroup.zpowers (k * z ^ ((-i : Fin 3) : ℕ))) :=
  w16g_comp_map_t hD hG i

end CFSG.LocalAnalysis.WeakClosure81
