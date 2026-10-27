module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR3S

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU
  CFSG.Quasithin.H.LU24 CFSG.Quasithin.E3 CFSG.Quasithin.H13 CFSG.Quasithin.B42Alt6
  CFSG.Quasithin.S143
open scoped commutatorElement

@[expose] def mb4TArr : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 17, 16, 19, 18, 21, 20, 23, 22, 9, 8, 11, 10, 13, 12, 15, 14]

theorem mb4T_ok : InvPairOK 24 mb4TArr mb4TArr = true ∧ autArrOK mb4TArr mb4TArr = true := by
  decide +kernel

@[expose] def mb4T : Equiv.Perm (Fin 24) := permOfArr 24 mb4TArr mb4TArr mb4T_ok.1

theorem hasArr_mb4T : HasArr mb4T mb4TArr := hasArr_permOfArr _

theorem hasArr_mb4Tinv : HasArr mb4T⁻¹ mb4TArr := hasArr_permOfArr_inv _

theorem mb4T_mem : mb4T ∈ AutPerm := mem_AutPerm_of_arr _ mb4T_ok.2

theorem mb4T_sq : mb4T * mb4T = 1 := by
  have h : cArr mb4TArr mb4TArr = idArr := by decide +kernel
  exact perm_eq_of_hasArr (h ▸ hasArr_mul hasArr_mb4T hasArr_mb4T) hasArr_one

theorem mb4T_pres : ∀ m ∈ uSMasks, actC11 mb4TArr m ∈ uSMasks := by decide +kernel

theorem mb4T_stab : rhoCd mb4T_mem ∈ stabSub US :=
  rhoCd_mem_stabSub mb4T_mem hasArr_mb4T hasArr_mb4Tinv mb4T_pres mb4T_pres

@[expose] def mb4TC : List ℕ := [514, 513, 531, 540, 519, 1580, 599, 1164, 1819, 512, 1027]

theorem mb4TCols_eq : matOf 11 (actC11 mb4TArr) = mb4TC := by decide +kernel

theorem mb4TCols_lt : ∀ x ∈ mb4TC, x < 2 ^ 11 := by decide +kernel

theorem actsBy_mb4T : ActsBy (rhoCd mb4T_mem) mb4TC := by
  rw [← mb4TCols_eq]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW mb4T_mem hasArr_mb4T)

@[expose] def mb4Tau : Equiv.Perm (Fin 6) :=
  perm6 ![0, 1, 2, 3, 5, 4] ![0, 1, 2, 3, 5, 4] (by decide)

theorem mb4Tau_odd : Equiv.Perm.sign mb4Tau ≠ 1 := by decide

theorem mb4Tau_act : ∀ m ∈ combos uSBasis, ∀ i : Fin 6,
    bvec 6 (actM thC (actM mb4TC m)) i =
      bvec 6 (actM thC m) (mb4Tau⁻¹ i) + bvec 6 (actM thC m) (mb4Tau⁻¹ 5) := by
  decide +kernel

theorem rhoOf_mb4T :
    B42Alt6.rhoOf usTheta mb4Tau = resHom US ⟨rhoCd mb4T_mem, mb4T_stab⟩ :=
  rhoOf_eq mb4T_stab actsBy_mb4T mb4TCols_lt mb4Tau_act

private theorem mb4T_resHom_ne {p : MulAut W11} (hp : p ∈ stabSub US) (hpP : p ∈ imgCd sxP0) :
    resHom US ⟨p, hp⟩ ≠ resHom US ⟨rhoCd mb4T_mem, mb4T_stab⟩ := by
  intro heq
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1
    (autSub_le_alt6 (mem_autSub.2 ⟨⟨p, hp⟩, hpP, rfl⟩))
  have h : a = mb4Tau := rhoOf_injective usTheta (hae.trans (heq.trans rhoOf_mb4T.symm))
  exact mb4Tau_odd (Equiv.Perm.mem_alternatingGroup.1 (h ▸ ha))

private theorem mem_KS_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (h : HasArr σ a) {S : ℕ}
    (hS : a = wArr ((List.range 6).map ks6Arr) (subW S)) : σ ∈ sxKS := by
  subst hS
  rw [perm_eq_of_hasArr h (hasArr_wPerm hasArr_ksList (subW S))]
  exact wPerm_ksList_mem _

theorem mb4Inv_arr : cArr (cArr (cArr mb4TArr sxZArr) mb4TArr) sxZArr =
    wArr ((List.range 6).map ks6Arr) (subW 3) := by
  decide +kernel

theorem mb4T_inv_sxZ : mb4T * sxZ * mb4T⁻¹ * sxZ ∈ sxKS :=
  mem_KS_of_arr (hasArr_mul (hasArr_mul (hasArr_mul hasArr_mb4T hasArr_sxZ) hasArr_mb4Tinv)
    hasArr_sxZ) mb4Inv_arr

@[expose] def mb4GArr : Array ℕ :=
  #[18, 23, 12, 13, 17, 1, 21, 0, 19, 8, 9, 22, 6, 15, 3, 11, 20, 4, 5, 16, 7, 2, 14, 10]

@[expose] def mb4GInv : Array ℕ :=
  #[7, 5, 21, 14, 17, 18, 12, 20, 9, 10, 23, 15, 2, 3, 22, 13, 19, 4, 0, 8, 16, 6, 11, 1]

theorem mb4G_ok : InvPairOK 24 mb4GArr mb4GInv = true ∧ autArrOK mb4GArr mb4GInv = true := by
  decide +kernel

theorem mb4G_conj : cArr (cArr mb4GArr mb4TArr) mb4GInv =
    wArr ((List.range 6).map ks6Arr) (subW 9) := by
  decide +kernel

theorem mb4_conj_into_KS :
    ∃ g : Equiv.Perm (Fin 24), ∃ hg : g ∈ AutPerm, g * mb4T * g⁻¹ ∈ sxKS :=
  ⟨permOfArr 24 mb4GArr mb4GInv mb4G_ok.1, mem_AutPerm_of_arr _ mb4G_ok.2,
    mem_KS_of_arr (hasArr_mul (hasArr_mul (hasArr_permOfArr _) hasArr_mb4T)
      (hasArr_permOfArr_inv _)) mb4G_conj⟩

private theorem inv_mul_mem_of_card_le {G : Type*} [Group G] [Finite G] {N P : Subgroup G}
    (hPN : P ≤ N) (hcard : Nat.card ↥N ≤ 2 * Nat.card ↥P) {t : G} (htN : t ∈ N) (htP : t ∉ P)
    {x : G} (hxN : x ∈ N) (hxP : x ∉ P) : x⁻¹ * t ∈ P := by
  have hQ : Nat.card ↥(P.subgroupOf N) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have h1 := Subgroup.card_mul_index (P.subgroupOf N)
  rw [hQ] at h1
  have h0 : (P.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (P.subgroupOf N).index ≠ 1 := by
    intro h
    have h3 := Subgroup.index_eq_one.1 h
    have h4 : (⟨t, htN⟩ : ↥N) ∈ P.subgroupOf N := by
      rw [h3]
      exact Subgroup.mem_top _
    exact htP (Subgroup.mem_subgroupOf.1 h4)
  have hPpos : 0 < Nat.card ↥P := Nat.card_pos
  have h5 : (P.subgroupOf N).index ≤ 2 :=
    Nat.le_of_mul_le_mul_left (h1.trans_le (hcard.trans_eq (mul_comm _ _))) hPpos
  have hidx : (P.subgroupOf N).index = 2 := by omega
  have hx' : (⟨x, hxN⟩ : ↥N) ∉ P.subgroupOf N := fun h => hxP (Subgroup.mem_subgroupOf.1 h)
  have ht' : (⟨t, htN⟩ : ↥N) ∉ P.subgroupOf N := fun h => htP (Subgroup.mem_subgroupOf.1 h)
  have h6 : (⟨x, hxN⟩ : ↥N)⁻¹ * ⟨t, htN⟩ ∈ P.subgroupOf N := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false (fun h => hx' (inv_mem_iff.1 h)) ht'
  exact Subgroup.mem_subgroupOf.1 h6

theorem centH_le_P0_of_card
    (hS : Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 138240) :
    (rhoC11 AutPerm le_rfl).range ⊓ centSub US ≤ imgCd sxP0 := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have hPN : imgCd sxP0 ≤ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US :=
    le_inf (Subgroup.map_le_range _ _) imgCd_P0_le_stab
  have hP : 69120 ≤ Nat.card ↥(imgCd sxP0) := by
    have h1 := card_centUS_mul_le
    have h2 := le_card_centUS
    omega
  have htN : rhoCd mb4T_mem ∈ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US :=
    ⟨⟨⟨mb4T, mb4T_mem⟩, rfl⟩, mb4T_stab⟩
  have htP : rhoCd mb4T_mem ∉ imgCd sxP0 := fun h => mb4T_resHom_ne mb4T_stab h rfl
  rintro x ⟨hxR, hxC⟩
  by_contra hxP
  have hxS : x ∈ stabSub US := centSub_le_stabSub US hxC
  have hp : x⁻¹ * rhoCd mb4T_mem ∈ imgCd sxP0 :=
    inv_mul_mem_of_card_le hPN (by omega) htN htP ⟨hxR, hxS⟩ hxP
  have hpS : x⁻¹ * rhoCd mb4T_mem ∈ stabSub US :=
    (stabSub US).mul_mem ((stabSub US).inv_mem hxS) mb4T_stab
  refine mb4T_resHom_ne hpS hp ?_
  have h1 : resHom US ⟨x, hxS⟩ = 1 := MulEquiv.ext fun u => Subtype.ext (hxC u.1 u.2)
  have h2 : (⟨x⁻¹ * rhoCd mb4T_mem, hpS⟩ : ↥(stabSub US)) =
      (⟨x, hxS⟩ : ↥(stabSub US))⁻¹ * ⟨rhoCd mb4T_mem, mb4T_stab⟩ := rfl
  rw [h2, map_mul, map_inv, h1, inv_one, one_mul]

theorem centH_le_P0 :
    (rhoC11 AutPerm le_rfl).range ⊓ centSub US ≤ imgCd sxP0 :=
  centH_le_P0_of_card card_stab_US_le

theorem mb4_b4 : ∃ b ∈ maskSub 11 mb3L10, rhoCd sxZ_autPerm b * b⁻¹ ∉ US := by
  refine ⟨toW 11 948, toW_mem_maskSub (by decide +kernel), ?_⟩
  have hx : (actC11 sxZArr 948 ^^^ 948) < 2 ^ 11 :=
    Nat.xor_lt_two_pow (actC11_lt _ _) (by norm_num)
  rw [rhoCd_toW sxZ_autPerm hasArr_sxZ, toW_inv_self, ← toW_xor, toW_mem_US_iff hx]
  decide +kernel

theorem hasArr_sxZinv_mb4 : HasArr sxZ⁻¹ (cArr sxZArr sxZArr) := by
  have h3 : sxZ * (sxZ * sxZ) = 1 := by
    have h := sxZ_cube
    rw [pow_succ, pow_two, mul_assoc] at h
    exact h
  rw [inv_eq_of_mul_eq_one_right h3]
  exact hasArr_mul hasArr_sxZ hasArr_sxZ

theorem mb4_comm_arr : cArr (cArr (cArr sxZArr sxG1Arr) (cArr sxZArr sxZArr)) sxG1Inv =
    wArr ((List.range 6).map ks6Arr) (subW 44) := by
  decide +kernel

theorem mb4_comm_sxZ_sxG1 : ⁅sxZ, sxG1⁆ ∈ sxKS := by
  rw [commutatorElement_def]
  exact mem_KS_of_arr (hasArr_mul (hasArr_mul (hasArr_mul hasArr_sxZ hasArr_sxG1)
    hasArr_sxZinv_mb4) hasArr_sxG1inv) mb4_comm_arr

end CFSG.Quasithin.H13.Mat
