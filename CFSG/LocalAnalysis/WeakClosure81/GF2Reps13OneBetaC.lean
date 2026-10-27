module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Hyp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_heisenberg_seven (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W} (ht : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {x z y : MulAut W}
    (hx : orderOf x = 7) (hz : orderOf z = 7) (htx : t * x * t⁻¹ = x⁻¹)
    (htz : t * z * t⁻¹ = z) (hxz : x * z = z * x) (hyx : y * x * y⁻¹ = x * z)
    (hyz : y * z = z * y) : False := by
  classical
  have hx7 : x ^ 7 = 1 := by simpa [hx] using pow_orderOf_eq_one x
  have hz7 : z ^ 7 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have hx_notin : x ∉ Subgroup.zpowers z := by
    intro hxZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    have htz' : MulAut.conj t z = z := by rw [MulAut.conj_apply, htz]
    have hzpow : t * z ^ k * t⁻¹ = z ^ k := by
      calc t * z ^ k * t⁻¹ = MulAut.conj t (z ^ k) := (MulAut.conj_apply t _).symm
        _ = (MulAut.conj t z) ^ k := map_zpow (MulAut.conj t) z k
        _ = z ^ k := by rw [htz']
    have htx' : t * x * t⁻¹ = x := by rw [← hk]; exact hzpow
    have hxinv : x⁻¹ = x := by rw [← htx, htx']
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hxinv.symm]
      exact inv_mul_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rw [hx] at hdvd
    norm_num at hdvd
  set X : Subgroup (MulAut W) := Subgroup.zpowers x with hX
  set Zs : Subgroup (MulAut W) := Subgroup.zpowers z with hZs
  set E : Subgroup (MulAut W) := Zs ⊔ X with hE
  set M : Subgroup W := commSub ⊤ E with hM
  have hEelem : IsElemAbelian 7 E := by
    rw [hE, hX, hZs]
    exact w16g_isElemAbelian_sup_zpowers hz7 hx7 hxz.symm
  have hEcard : Nat.card ↥E = 49 := by
    rw [hE, hX, hZs]
    have h := w16g_card_sup_zpowers Nat.prime_seven hz hx hxz.symm hx_notin
    norm_num at h ⊢
    exact h
  have hEodd : Odd (Nat.card E) := by rw [hEcard]; norm_num
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hMstab : StableUnder E M := fun e he u hu =>
    CFSG.Quasithin.Asc81c.commSub_stable' he hu
  have hME : commSub M E = M := by
    rw [hM]
    exact CFSG.Quasithin.Asc81c.commSub_commSub_eq' hW hEodd
  have hMfix : M ⊓ fixV E = ⊥ := by
    rw [hM, inf_comm]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hEodd
  have hdecomp :=
    inf_fixV_hyperplane_decomposition (W := W) hW Nat.prime_seven (by norm_num) E hEelem hMstab hME
  have hhyper : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E
      = {Zs} ∪ Set.range (fun j : Fin 7 => Subgroup.zpowers (x * z ^ (j : ℕ))) := by
    rw [hE, hX, hZs]
    exact w16g_hyperplanes_sup_zpowers Nat.prime_seven hz hx hxz.symm hx_notin
  let Dj : Fin 7 → CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := fun j =>
    ⟨Subgroup.zpowers (x * z ^ (j : ℕ)), by rw [hhyper]; exact Or.inr ⟨j, rfl⟩⟩
  have hDj_inj : Function.Injective Dj := by
    intro i j hij
    have h1 : Subgroup.zpowers (x * z ^ (i : ℕ)) = Subgroup.zpowers (x * z ^ (j : ℕ)) :=
      congrArg Subtype.val hij
    exact (w16g_zpowers_mul_pow_injective Nat.prime_seven hz hx hxz.symm hx_notin).1 h1
  have hDj0 : (Dj 0 : Subgroup (MulAut W)) = X := by
    show Subgroup.zpowers (x * z ^ ((0 : Fin 7) : ℕ)) = X
    rw [hX]
    simp
  have hDjE : ∀ j : Fin 7, (Dj j : Subgroup (MulAut W)) ≤ E := by
    intro j
    refine Subgroup.zpowers_le.mpr ?_
    have hxE : x ∈ E := by
      rw [hE, hX]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hzE : z ^ (j : ℕ) ∈ E := by
      rw [hE, hZs]
      exact Subgroup.mem_sup_left (by simpa using Subgroup.zpow_mem_zpowers z (j : ℤ))
    exact E.mul_mem hxE hzE
  let G : Fin 7 → Subgroup W := fun j => M ⊓ fixV (Dj j : Subgroup (MulAut W))
  have hGind : iSupIndep G := hdecomp.1.comp hDj_inj
  let Zhyp : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E :=
    ⟨Zs, by rw [hhyper]; exact Or.inl rfl⟩
  have hsup_eq : (⨆ D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E,
        M ⊓ fixV (D : Subgroup (MulAut W))) = (M ⊓ fixV Zs) ⊔ ⨆ j : Fin 7, G j := by
    apply le_antisymm
    · refine iSup_le fun D => ?_
      have hD : D.1 ∈ {Zs} ∪ Set.range (fun j : Fin 7 => Subgroup.zpowers (x * z ^ (j : ℕ))) := by
        rw [← hhyper]
        exact D.2
      rcases hD with hD | ⟨j, hDj⟩
      · have hDZ : D = Zhyp := Subtype.ext hD
        rw [hDZ]
        exact le_sup_left
      · have hDD : D = Dj j := Subtype.ext hDj.symm
        rw [hDD]
        exact le_sup_of_le_right (le_iSup G j)
    · refine sup_le ?_ ?_
      · exact le_iSup
          (fun D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E =>
            M ⊓ fixV (D : Subgroup (MulAut W))) Zhyp
      · refine iSup_le fun j => ?_
        exact le_iSup
          (fun D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E =>
            M ⊓ fixV (D : Subgroup (MulAut W))) (Dj j)
  have hM_eq : M = (M ⊓ fixV Zs) ⊔ ⨆ j : Fin 7, G j := by
    nth_rewrite 1 [← hdecomp.2]
    exact hsup_eq
  have hconjz : ∀ n : ℕ, (MulAut.conj (y ^ n)).toMonoidHom z = z := by
    intro n
    show MulAut.conj (y ^ n) z = z
    rw [MulAut.conj_apply]
    exact w16g_conj_zpow_self hyz n
  have hconjx : ∀ n : ℕ, (MulAut.conj (y ^ n)).toMonoidHom x = x * z ^ n := by
    intro n
    show MulAut.conj (y ^ n) x = x * z ^ n
    rw [MulAut.conj_apply]
    exact w16g_conj_zpow_x hyx hyz n
  have hEnorm : ∀ n : ℕ, E.map (MulAut.conj (y ^ n)).toMonoidHom = E := by
    intro n
    have hmap : E.map (MulAut.conj (y ^ n)).toMonoidHom
        = Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z ^ n) := by
      rw [hE, hX, hZs, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
        hconjz n, hconjx n]
    rw [hmap, hE, hX, hZs]
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      exact Subgroup.zpowers_le.mpr (Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
        (Subgroup.mem_sup_left (by simpa using Subgroup.zpow_mem_zpowers z (n : ℤ))))
    · refine sup_le le_sup_left ?_
      refine Subgroup.zpowers_le.mpr ?_
      have h1 : x * z ^ n ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z ^ n) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers (x * z ^ n))
      have h2 : (z ^ n)⁻¹ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z ^ n) :=
        Subgroup.mem_sup_left (by simpa using Subgroup.zpow_mem_zpowers z (-(n : ℤ)))
      have hxeq : x = (x * z ^ n) * (z ^ n)⁻¹ := by group
      have hmem := Subgroup.mul_mem (Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z ^ n)) h1 h2
      rwa [← hxeq] at hmem
  have hMnorm : ∀ n : ℕ, M.map (y ^ n).toMonoidHom = M := by
    intro n
    have h := CFSG.Quasithin.Asc81c.commSub_map_conj E (y ^ n)
    rw [hEnorm n] at h
    rw [hM]
    exact h.symm
  have hDjmap : ∀ j : Fin 7,
      (Dj 0 : Subgroup (MulAut W)).map (MulAut.conj (y ^ (j : ℕ))).toMonoidHom = Dj j := by
    intro j
    rw [hDj0, hX, MonoidHom.map_zpowers, hconjx (j : ℕ)]
  have hfixmap : ∀ j : Fin 7,
      (fixV (Dj 0 : Subgroup (MulAut W))).map (y ^ (j : ℕ)).toMonoidHom = fixV (Dj j) := by
    intro j
    rw [← CFSG.Quasithin.Asc81c.fixV_map_conj (Dj 0) (y ^ (j : ℕ)), hDjmap j]
  have hGrank : ∀ j : Fin 7, rk (G j) = rk (G 0) := by
    intro j
    have hmap : (G 0).map (y ^ (j : ℕ)).toMonoidHom = G j := by
      change (M ⊓ fixV (Dj 0 : Subgroup (MulAut W))).map (y ^ (j : ℕ)).toMonoidHom
        = M ⊓ fixV (Dj j : Subgroup (MulAut W))
      rw [Subgroup.map_inf _ _ _ (MulEquiv.injective (y ^ (j : ℕ))), hMnorm (j : ℕ), hfixmap j]
    have hcard := Subgroup.card_map_of_injective (K := G 0)
      (f := (y ^ (j : ℕ)).toMonoidHom) (MulEquiv.injective (y ^ (j : ℕ)))
    rw [hmap] at hcard
    unfold rk
    rw [hcard]
  have hXodd : Odd (Nat.card X) := by rw [hX, Nat.card_zpowers, hx]; norm_num
  have hZsStab : StableUnder Zs (G 0) := by
    change StableUnder Zs (M ⊓ fixV (Dj 0 : Subgroup (MulAut W)))
    rw [hDj0]
    have hMZs : StableUnder Zs M := fun z' hz' u hu =>
      hMstab z' (by rw [hE]; exact Subgroup.mem_sup_left hz') u hu
    have hfixZs : StableUnder Zs (fixV X) := by
      refine stableUnder_fixV ?_
      intro z' hz' x' hx'
      have hcomm : z' * x' = x' * z' :=
        hEcomm z' (by rw [hE]; exact Subgroup.mem_sup_left hz')
          x' (by rw [hE]; exact Subgroup.mem_sup_right hx')
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hx'
    exact stableUnder_inf hMZs hfixZs
  have hG0fix : G 0 ⊓ fixV Zs = ⊥ := by
    change (M ⊓ fixV (Dj 0 : Subgroup (MulAut W))) ⊓ fixV Zs = ⊥
    rw [hDj0, inf_assoc, ← w16g_fixV_sup X Zs]
    rw [show X ⊔ Zs = E by rw [hE]; exact sup_comm X Zs, hMfix]
  have hZsP : IsPGroup 7 ↥Zs := by
    apply IsPGroup.of_card (n := 1)
    rw [hZs, Nat.card_zpowers, hz, pow_one]
  have h3dvd : 3 ∣ rk (G 0) := by
    have h := CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hW hZsP hZsStab hG0fix
    have hd : orderOf (2 : ZMod 7) = 3 :=
      orderOf_eq_prime (by decide) (by decide)
    rwa [hd] at h
  have hGj_le : ∀ j : Fin 7, j ≠ 0 → G j ≤ commSub ⊤ X := by
    intro j hj
    have hXstab : StableUnder X (G j) := by
      change StableUnder X (M ⊓ fixV (Dj j : Subgroup (MulAut W)))
      have hMX : StableUnder X M := fun x' hx' u hu =>
        hMstab x' (by rw [hE]; exact Subgroup.mem_sup_right hx') u hu
      have hfixX : StableUnder X (fixV (Dj j : Subgroup (MulAut W))) := by
        refine stableUnder_fixV ?_
        intro x' hx' d hd
        have hcomm : x' * d = d * x' :=
          hEcomm x' (by rw [hE]; exact Subgroup.mem_sup_right hx') d (hDjE j hd)
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hd
      exact stableUnder_inf hMX hfixX
    have hGjfix : G j ⊓ fixV X = ⊥ := by
      change (M ⊓ fixV (Dj j : Subgroup (MulAut W))) ⊓ fixV X = ⊥
      have hsup : (Dj j : Subgroup (MulAut W)) ⊔ (Dj 0 : Subgroup (MulAut W)) = E :=
        CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.sup_eq_of_hyperplanes
          (Dj j).2 (Dj 0).2 (fun h => hj (hDj_inj (Subtype.ext h)))
      have hsup' : (Dj j : Subgroup (MulAut W)) ⊔ X = E := by rw [← hDj0]; exact hsup
      rw [inf_assoc, ← w16g_fixV_sup (Dj j) X, hsup', hMfix]
    have hdec := CFSG.Quasithin.B1.coprime_decomp hW hXodd hXstab
    have hcomm_eq : commSub (G j) X = G j := by
      have h := hdec.1
      rw [hGjfix, bot_sup_eq] at h
      exact h
    calc G j = commSub (G j) X := hcomm_eq.symm
      _ ≤ commSub ⊤ X := commSub_mono le_top le_rfl
  have hsum6 : rk ↥(⨆ j : {j : Fin 7 // j ≠ 0}, G j.1) = 6 * rk (G 0) := by
    rw [w16g_rk_iSup_eq_sum hW (fun j : {j : Fin 7 // j ≠ 0} => G j.1)
      (hGind.comp Subtype.val_injective)]
    have hcard : Fintype.card {j : Fin 7 // j ≠ 0} = 6 := by decide
    calc ∑ j : {j : Fin 7 // j ≠ 0}, rk (G j.1)
        = ∑ _j : {j : Fin 7 // j ≠ 0}, rk (G 0) := by
          refine Finset.sum_congr rfl fun j _ => hGrank j.1
      _ = 6 * rk (G 0) := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          norm_num
  have h6k_le : 6 * rk (G 0) ≤ rk ↥(commSub ⊤ X) := by
    rw [← hsum6]
    refine rk_mono ?_
    exact iSup_le fun j => hGj_le j.1 j.2
  have hrkX_le : rk ↥(commSub ⊤ X) ≤ 6 := by
    have hXrank : IsElemAbelianOfRank 7 1 ↥X := by
      rw [hX]
      exact w16g_isElemAbelianOfRank_one_of_card Nat.prime_seven (by rw [Nat.card_zpowers, hx])
    have hinvX : ∀ a ∈ X, t * a * t⁻¹ = a⁻¹ := by
      intro a ha
      rw [hX] at ha
      exact w16g_conj_inv_of_mem_zpowers htx ha
    have hbridge := rk_commSub_eq_two_mul_of_inverted hW ht Nat.prime_seven (by norm_num)
      (by norm_num) hXrank hinvX
    have hle : rk ↥(commSub (commSub ⊤ X) (Subgroup.zpowers t)) ≤ 3 :=
      le_trans (rk_mono (commSub_mono le_top le_rfl)) hrk
    calc rk ↥(commSub ⊤ X)
        = 2 * rk ↥(commSub (commSub ⊤ X) (Subgroup.zpowers t)) := hbridge
      _ ≤ 2 * 3 := by gcongr
      _ = 6 := by norm_num
  have hk0 : rk (G 0) = 0 := by
    have hle := le_trans h6k_le hrkX_le
    rcases Nat.eq_zero_or_pos (rk (G 0)) with h | h
    · exact h
    · have h3 := Nat.le_of_dvd h h3dvd
      omega
  have hGbot : ∀ j : Fin 7, G j = ⊥ := fun j =>
    (rk_eq_zero_iff hW).mp (by rw [hGrank j, hk0])
  have hM_le_fix : M ≤ fixV Zs := by
    have h1 : M = M ⊓ fixV Zs := by
      nth_rewrite 1 [hM_eq]
      rw [iSup_eq_bot.mpr hGbot, sup_bot_eq]
    rw [h1]
    exact inf_le_right
  have hcomm_bot : commSub ⊤ Zs = ⊥ := by
    have hle : commSub ⊤ Zs ≤ fixV Zs :=
      le_trans (commSub_mono le_top (by rw [hE]; exact le_sup_left)) hM_le_fix
    have hodd : Odd (Nat.card Zs) := by rw [hZs, Nat.card_zpowers, hz]; norm_num
    have hbot : commSub ⊤ Zs ⊓ fixV Zs = ⊥ := by
      rw [inf_comm]
      exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hodd
    exact le_antisymm (by rw [← hbot]; exact le_inf le_rfl hle) bot_le
  have hz1 : z = 1 := by
    have hle : (⊤ : Subgroup W) ≤ fixV Zs := commSub_eq_bot_iff.mp hcomm_bot
    ext w
    rw [MulAut.one_apply]
    exact mem_fixV.mp (hle (Subgroup.mem_top w)) z (Subgroup.mem_zpowers z)
  rw [hz1] at hz
  simp at hz

end CFSG.LocalAnalysis.WeakClosure81
