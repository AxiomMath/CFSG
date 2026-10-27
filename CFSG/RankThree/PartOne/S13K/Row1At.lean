module

public import CFSG.RankThree.PartOne.N143.JKt1
public import CFSG.RankThree.PartOne.S13K.BlockAt
public import CFSG.RankThree.PartOne.KF.R1Final
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL permSL permSL_inv mem_Tor_iff ent ent_ext)
open scoped commutatorElement

theorem admissible_psl_two {f : ℕ} (hf : 2 ≤ f) : StatedLieAdmissible .PSL 2 2 f := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨Nat.prime_two, by omega, le_refl 2, ?_, ?_⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

theorem statedModel_of_sl2_equiv {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {X : Type} [Group X]
    (e : Matrix.SpecialLinearGroup (Fin 2) K ≃* X) : StatedClassicalModel X .PSL 2 2 f := by
  obtain ⟨e0⟩ := CFSG.RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := K)
  exact ⟨admissible_psl_two hf, K, inferInstance, inferInstance, hK, ⟨e.symm.trans e0⟩⟩

theorem permSL_swap01_mem_range_blkSL {K : Type} [Field K] [CharP K 2] :
    (permSL (Equiv.swap (0 : Fin 3) 1) : SL3 K) ∈
      (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range := by
  obtain ⟨w, hw⟩ : ∃ w : Matrix.SpecialLinearGroup (Fin 2) K,
      (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
    ⟨⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩, rfl⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  rw [coe_blkSL, KFOUT3.coe_permSL, hw]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blkMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem ent_permSL' {K : Type} [Field K] [CharP K 2] (σ : Equiv.Perm (Fin 3)) (a b : Fin 3) :
    ent (permSL σ : SL3 K) a b = if σ⁻¹ a = b then 1 else 0 := by
  simp [ent, KFOUT3.coe_permSL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem permSL_conj_swap {K : Type} [Field K] [CharP K 2] (τ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    permSL τ * permSL (Equiv.swap i j) * (permSL τ)⁻¹ = (permSL (Equiv.swap (τ i) (τ j)) : SL3 K) := by
  refine ent_ext fun a b => ?_
  rw [KFOUT3.ent_permSL_conj, ent_permSL', ent_permSL']
  have key : (Equiv.swap i j) (τ⁻¹ a) = τ⁻¹ b ↔ Equiv.swap (τ i) (τ j) a = b := by
    rw [← Equiv.apply_eq_iff_eq τ, Equiv.swap_apply_apply]
    simp
  simp only [Equiv.swap_inv]
  exact if_congr key rfl rfl

section JGood

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem jGood_of_row1 (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E = A)
    (hrow : RowModel p L 1) : JGood p A c L := by
  subst hEA
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hG : Sec12TwoGeneric p c L E := by
    rcases hF.two with hG | hS
    · exact hG
    · exfalso
      obtain ⟨f', -, hmod5⟩ := hS.model
      obtain ⟨f, -, -, hmod1⟩ := hrow
      exact Sec141Row.not_psl_three_and_psu_five hmod1 hmod5
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  have hcore : Table123Core p L (E ⊓ L) (E ⊓ L) :=
    { prime := hp
      five_le := h5
      quasisimple := hG.quasisimple
      center_pPrime := hG.center_pPrime
      A₀_le := inf_le_right
      A₀_elem := Planes.isElementaryAbelian_of_le inf_le_left h.A_elem
      A₀_card := Sec12Three.card_A_inf_L h hG hcL
      A₀_invariant := Sec12Three.invariant_A_inf_L h hG
      F_le := inf_le_right
      F_elem := Planes.isElementaryAbelian_of_le inf_le_left h.E_elem
      A₀_le_F := inf_le_inf_right L h.A_le_E
      F_le_centralizer := fun f hf a ha => by
        have hfE := (Subgroup.mem_inf.1 hf).1
        have haA := (Subgroup.mem_inf.1 ha).1
        exact (Subgroup.mem_centralizer_iff.1 (h.E_le hfE) a haA)
      F_max := fun F' hF'L hF'el hF'c hFF' =>
        Sec12Three.F_max_generic h hG F' hF'L hF'el hF'c hFF' }
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r1ctx hcore hrow
  have hweyl : RowWeylIso E (torusImage E L) 1 := R.rowWeylIso ⟨S.weylEquiv hp hp2 hζ⟩
  have hEcard : Nat.card E = p ^ 3 := h.A_card
  have hEadm : E ∈ admissibleTriples p E := by
    refine ⟨le_rfl, h.E_elem, hEcard, ?_⟩
    exact h.setup.2.2.2.2.2.2.2.2.1
  have hBE : ∀ B ∈ admissibleTriples p E, B = E := fun B hB =>
    Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hB.2.2.1, hEcard])
  have hmem : L ∈ thetaCompZeroStarE p E := by
    have hM := Sec12Three.L_mem_zeroStar h
    refine ⟨⟨E, hEadm, hM.1⟩, ⟨E, hEadm, hM.2.1⟩, fun J hJ hMJ => ?_⟩
    obtain ⟨B, hB, hJB⟩ := hJ
    rw [hBE B hB] at hJB
    exact hM.2.2 J hJB hMJ
  exact ⟨h, hF, hG, hweyl, hrow, cent_of_generic h hG, hmem⟩

end JGood

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G}

theorem kfAt_of_cover {K : Type} [Field K] [Finite K] [CharP K 2] {ρ : SL3 K →* G}
    (h : JGood p A c J)
    (hρ : IsPSL3Cover p A J ρ) {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (hf : p ∣ 2 ^ f - 1) {t : MulAut A} (ht : t ∈ reflectionSet p A) (htJ : t ∈ torusImage A J) :
    ∃ τ : Equiv.Perm (Fin 3), KFAt p A f t ∧
      kZero p A t = (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)).range ∧
      ∃ hk : ρ (permSL (Equiv.swap (τ 0) (τ 1))) ∈ Subgroup.normalizer (A : Set G),
        A.normalizerMonoidHom ⟨ρ (permSL (Equiv.swap (τ 0) (τ 1))), hk⟩ = t := by
  classical
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hf3 := three_le_of_dvd_pred h5 hf1 hf
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hf)
  obtain ⟨x, hxJ, hxN, rfl⟩ := Sec12Three.mem_torusImage_iff.1 htJ
  obtain ⟨m, hmN, hxm⟩ := (hρ.mem_inf_normalizer_iff hp h).1 ⟨hxJ, hxN⟩
  subst hxm
  obtain ⟨σ, hσ⟩ := exists_perm_conj_Tor hζ hmN
  have hord : orderOf (A.normalizerMonoidHom ⟨ρ m, hxN⟩) = 2 := ht.1.1
  have h2 : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (A.normalizerMonoidHom ⟨ρ m, hxN⟩)
    rwa [hord] at this
  have ht1 : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have ht3 : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ^ 3 ≠ 1 := by
    intro h3
    apply ht1
    have : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ^ 3 = A.normalizerMonoidHom ⟨ρ m, hxN⟩ := by
      rw [pow_succ, h2, one_mul]
    rw [← this]
    exact h3
  have hact : ∀ n : ℕ, σ ^ n = 1 → ∀ a ∈ A, (ρ m) ^ n * a * ((ρ m) ^ n)⁻¹ = a := by
    intro n hn a ha
    obtain ⟨i, d, hd, rfl⟩ := hρ.exists_decomp h ha
    rw [← map_pow, hρ.conj_decomp h (m ^ n) i d]
    obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
    rw [conj_pow_diagSL hσ n v hv hv1]
    have : diagSL (permVec (σ ^ n) v) (prod_permVec (σ ^ n) hv) = diagSL v hv :=
      diagSL_congr (by rw [hn, permVec_one]) _ _
    rw [this]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply ht1
    have := normalizerMonoidHom_pow_eq_one hxN 1 (hact 1 (by rw [pow_one]; exact h1))
    simpa using this
  have hσ3 : σ ^ 3 ≠ 1 := fun h3 => ht3 (normalizerMonoidHom_pow_eq_one hxN 3 (hact 3 h3))
  obtain ⟨τ, hτ⟩ := exists_conj_swap σ hσ1 hσ3
  have hρ' := hρ.conjPerm τ
  have hP : permSL τ ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) := permSL_mem_normalizer_Tor τ
  have hmN' : (permSL τ)⁻¹ * m * permSL τ ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) hmN) hP
  have hxm' : (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom) ((permSL τ)⁻¹ * m * permSL τ) = ρ m := by
    show ρ (permSL τ * ((permSL τ)⁻¹ * m * permSL τ) * (permSL τ)⁻¹) = ρ m
    congr 1
    group
  have hσ' : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      ((permSL τ)⁻¹ * m * permSL τ) * diagSL v hv * ((permSL τ)⁻¹ * m * permSL τ)⁻¹ =
        diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv) := by
    intro v hv hv1
    have e1 : (permSL τ)⁻¹ * m * permSL τ * diagSL v hv * ((permSL τ)⁻¹ * m * permSL τ)⁻¹ =
        (permSL τ)⁻¹ * (m * (permSL τ * diagSL v hv * (permSL τ)⁻¹) * m⁻¹) * ((permSL τ)⁻¹)⁻¹ := by
      group
    rw [e1, permSL_conj_diagSL τ v hv, hσ (permVec τ v) (prod_permVec τ hv) (fun i => hv1 _),
      permSL_inv]
    rw [permSL_conj_diagSL τ⁻¹]
    exact diagSL_congr (by rw [permVec_permVec, permVec_permVec, mul_assoc, hτ]) _ _
  have hrange := Kof_eq_swap h hp hρ' hζ h4 hxN hxm' hσ'
  have hle := autMoved_le_swap h hρ' hζ hxN hxm' hmN' hσ'
  set ρ' : SL3 K →* G := ρ.comp (MulAut.conj (permSL τ)).toMonoidHom with hρ'def
  set m' : SL3 K := (permSL τ)⁻¹ * m * permSL τ with hm'def
  set t₀ : MulAut A := A.normalizerMonoidHom ⟨ρ m, hxN⟩ with ht₀def
  have hf2 : 2 ≤ f := by omega
  have hmodelB : StatedClassicalModel ↥(blkφ ρ').range .PSL 2 2 f :=
    statedModel_of_sl2_equiv hf2 hK (MonoidHom.ofInjective (blkφ_injective hρ'))
  have hmJ : ρ m ∈ J := hρ.range_eq ▸ ⟨m, rfl⟩
  have hct : c ∈ autFixedInG A t₀ := by
    rw [ht₀def, mem_autFixedInG_normalizerMonoidHom hxN]
    refine ⟨h.hyp.c_mem, ?_⟩
    have hc : c * ρ m = ρ m * c := Sec12Three.comm_c_L h.hyp (ρ m) hmJ
    rw [mul_inv_eq_iff_eq_mul]
    exact hc.symm
  have hBL : (blkφ ρ').range ≤ J := by
    rintro _ ⟨M, rfl⟩
    exact hρ'.range_eq ▸ ⟨blkSL M, rfl⟩
  have hNt_le : Kof A J t₀ ≤ Nt A J t₀ := by
    unfold Kof
    exact Subgroup.commutator_le.2 fun a ha b hb =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)
  have hBX : (blkφ ρ').range ≤ Subgroup.centralizer (autFixedInG A t₀ : Set G) := by
    rw [← hrange]
    exact hNt_le.trans inf_le_right
  have hBnorm : ∀ y ∈ J ⊓ Subgroup.centralizer (autFixedInG A t₀ : Set G),
      ∀ b ∈ (blkφ ρ').range, y * b * y⁻¹ ∈ (blkφ ρ').range := by
    intro y hy b hb
    rw [← hrange] at hb ⊢
    have hbN : b ∈ Nt A J t₀ := hNt_le hb
    have e : y * b * y⁻¹ = ⁅y, b⁆ * b := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hy hbN) hb
  have hM : Nat.card (autMovedInG A t₀) = p := (node121a_of_hyp G p A c J A h.hyp t₀ ht).2.2
  have hMne : autMovedInG A t₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hM
    exact hp.one_lt.ne' hM.symm
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hMne
  have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hzord : orderOf (z : G) = p := by
    have hdvd : orderOf (z : G) ∣ Nat.card (autMovedInG A t₀) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard z
    rw [hM] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hz1'
    · exact h1
  have hMz : autMovedInG A t₀ = Subgroup.zpowers (z : G) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 z.2) ?_).symm
    rw [hM, Nat.card_zpowers, hzord]
  have hzB : (z : G) ∈ (blkφ ρ').range := hle z.2
  have hzE : (z : G) ∈ A := Subgroup.map_subtype_le _ z.2
  have hE : ∀ e ∈ A, ∃ u ∈ autFixedInG A t₀, ∃ i : ℤ, e = u * (z : G) ^ i := by
    intro e he
    have hsup := (node121a_of_hyp G p A c J A h.hyp t₀ ht).1
    rw [hsup] at he
    obtain ⟨u, hu, w, hw, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun k hk l hl => Sec12Three.mul_comm_of_mem_A h.hyp (Subgroup.map_subtype_le _ hk)
        (Subgroup.map_subtype_le _ hl)) he
    have hw' : w ∈ autMovedInG A t₀ := hw
    rw [hMz] at hw'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw'
    exact ⟨u, hu, i, rfl⟩
  have hlift : ∃ hk : ρ' (permSL (Equiv.swap (0 : Fin 3) 1)) ∈ Subgroup.normalizer (A : Set G),
      ρ' (permSL (Equiv.swap (0 : Fin 3) 1)) ∈ (blkφ ρ').range ∧
      A.normalizerMonoidHom ⟨ρ' (permSL (Equiv.swap (0 : Fin 3) 1)), hk⟩ = t₀ := by
    have hPN : permSL (Equiv.swap (0 : Fin 3) 1) ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) :=
      permSL_mem_normalizer_Tor _
    have hkJN : ρ' (permSL (Equiv.swap (0 : Fin 3) 1)) ∈ J ⊓ torusNormalizer A :=
      (hρ'.mem_inf_normalizer_iff hp h).2 ⟨_, hPN, rfl⟩
    obtain ⟨M, hM'⟩ := permSL_swap01_mem_range_blkSL (K := K)
    refine ⟨hkJN.2, ⟨M, ?_⟩, ?_⟩
    · rw [blkφ_apply, hM']
    · refine MulEquiv.ext fun a => Subtype.ext ?_
      rw [ht₀def]
      show ρ' (permSL (Equiv.swap (0 : Fin 3) 1)) * (a : G) *
          (ρ' (permSL (Equiv.swap (0 : Fin 3) 1)))⁻¹ = ρ m * (a : G) * (ρ m)⁻¹
      obtain ⟨i, d, hd, ha⟩ := hρ'.exists_decomp h a.2
      rw [ha, ← hxm', hρ'.conj_decomp h _ i d, hρ'.conj_decomp h m' i d]
      congr 2
      obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
      rw [permSL_conj_diagSL _ v hv, hσ' v hv hv1]
  obtain ⟨hkN, hkB, hkt⟩ := hlift
  have hkf := kfAt_of_block_gen h.hyp t₀ hct hBL hBX hBnorm hmodelB hzB hzE hz1' hE hle
    ⟨_, hkN, hkB, hkt⟩
  have hkeq : ρ' (permSL (Equiv.swap (0 : Fin 3) 1)) = ρ (permSL (Equiv.swap (τ 0) (τ 1))) := by
    show ρ (permSL τ * permSL (Equiv.swap (0 : Fin 3) 1) * (permSL τ)⁻¹) = _
    rw [permSL_conj_swap]
  obtain ⟨hkN', hkt'⟩ : ∃ hk : ρ (permSL (Equiv.swap (τ 0) (τ 1))) ∈ Subgroup.normalizer (A : Set G),
      A.normalizerMonoidHom ⟨ρ (permSL (Equiv.swap (τ 0) (τ 1))), hk⟩ = t₀ := by
    rw [← hkeq]
    exact ⟨hkN, hkt⟩
  exact ⟨τ, hkf.1, hkf.2, hkN', hkt'⟩

theorem kfAt_of_jgood (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : JGood p A c J) {t : MulAut A} (ht : t ∈ reflectionSet p A) (htJ : t ∈ torusImage A J)
    {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) : KFAt p A f t := by
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA h hf hm
  have hchar : CharP K 2 := charP_two_of_card hK
  obtain ⟨-, hkf, -⟩ := kfAt_of_cover h hρ hK hm.1.2.1 hf ht htJ
  exact hkf

theorem kfAt_row1 (hGA : CFSG.Open.GriessAllModelsStatement)
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E = A)
    {f : ℕ} (hf : p ∣ 2 ^ f - 1) (hf1 : 1 ≤ f)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) :
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E f t := by
  subst hEA
  have hJ : JGood p E c L := jGood_of_row1 h hF rfl ⟨f, hf1, hf, hm⟩
  intro t ht htL
  exact kfAt_of_jgood hGA hJ ht htL hf hm

end Main

end CFSG.RankThree.PartOne.S13K
