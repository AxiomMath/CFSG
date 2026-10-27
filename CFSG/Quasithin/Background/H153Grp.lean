module

public import CFSG.Quasithin.Background.H153Sext
public import CFSG.Quasithin.Background.H153Defs

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans

theorem smul_colF_of_cols {σ : S24} {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, colOf (σ i) = π (colOf i)) (j : Fin 6) : σ • colF j = colF (π j) := by
  ext x
  obtain ⟨y, rfl⟩ := σ.surjective x
  have h1 : σ • y ∈ σ • colF j ↔ y ∈ colF j := Finset.smul_mem_smul_finset_iff (s := colF j) σ
  have h2 : (σ • y : Fin 24) = σ y := rfl
  rw [h2] at h1
  rw [h1, mem_colF, mem_colF, h y, π.apply_eq_iff_eq]

theorem mem_stabilizer_S0_iff (σ : S24) : σ ∈ MulAction.stabilizer S24 S0 ↔ σ ∈ BP := by
  constructor
  · intro hσ
    have hS : σ • S0 = S0 := MulAction.mem_stabilizer_iff.1 hσ
    have hex : ∀ j : Fin 6, ∃ j' : Fin 6, σ • colF j = colF j' := by
      intro j
      have h1 : σ • colF j ∈ σ • S0 := Finset.smul_mem_smul_finset (mem_S0 j)
      rw [hS] at h1
      obtain ⟨j', -, hj'⟩ := Finset.mem_image.1 h1
      exact ⟨j', hj'.symm⟩
    choose f hf using hex
    have hinj : Function.Injective f := by
      intro a b hab
      have : σ • colF a = σ • colF b := by rw [hf a, hf b, hab]
      exact colF_injective (MulAction.injective σ this)
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => ?_⟩
    have h1 : σ i ∈ σ • colF (colOf i) := by
      have : σ • i ∈ σ • colF (colOf i) := Finset.smul_mem_smul_finset (mem_colF.2 rfl)
      exact this
    rw [hf] at h1
    exact mem_colF.1 h1
  · rintro ⟨π, hπ⟩
    refine MulAction.mem_stabilizer_iff.2 ?_
    ext B
    constructor
    · intro hB
      obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_smul_finset.1 hB
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB₀
      rw [smul_colF_of_cols hπ]
      exact mem_S0 _
    · intro hB
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB
      refine Finset.mem_smul_finset.2 ⟨colF (π⁻¹ j), mem_S0 _, ?_⟩
      rw [smul_colF_of_cols hπ]
      simp

theorem mem_MY0 {σ : S24} : σ ∈ MY M24g S0 ↔ σ ∈ AutPerm ∧ σ ∈ BP := by
  show σ ∈ AutPerm ⊓ MulAction.stabilizer S24 S0 ↔ _
  rw [Subgroup.mem_inf, mem_stabilizer_S0_iff]

theorem MY0_le_BP : MY M24g S0 ≤ BP := fun _ h => (mem_MY0.1 h).2

theorem MY0_le_autPerm : MY M24g S0 ≤ AutPerm := fun _ h => (mem_MY0.1 h).1

theorem Lz_le_MY0 : Lz ≤ MY M24g S0 := fun _ h => mem_MY0.2 ⟨Lz_le h, Lz_le_BP h⟩

theorem KSp_le_MY0 : KSp ≤ MY M24g S0 := fun _ h => Lz_le_MY0 (KSp_le_Lz h)

theorem ksP_cols : ∀ c < 64, ∀ i < 24, (ksC c)[i]! / 4 = i / 4 := by decide +kernel

theorem colOf_ksP (c : Fin 64) (i : Fin 24) : colOf (ksP c i) = colOf i :=
  Fin.ext (by
    show (ksP c i : ℕ) / 4 = (i : ℕ) / 4
    rw [ksP, permOfArr_val]
    exact ksP_cols c c.2 i i.2)

@[expose] noncomputable def piM : ↥(MY M24g S0) →* Equiv.Perm (Fin 6) :=
  colHom.comp (Subgroup.inclusion MY0_le_BP)

theorem piM_eq {σ : ↥(MY M24g S0)} {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, colOf ((σ : S24) i) = π (colOf i)) : piM σ = π := colHom_eq h

theorem piM_ksP (c : Fin 64) : piM ⟨ksP c, KSp_le_MY0 (ksP_mem_KSp c)⟩ = 1 :=
  piM_eq fun i => colOf_ksP c i

theorem piM_lz {σ : S24} (h : σ ∈ Lz) : piM ⟨σ, Lz_le_MY0 h⟩ = colLz ⟨σ, h⟩ := rfl

@[expose] def oddArr : Array ℕ :=
  #[0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 15, 14, 20, 21, 23, 22, 16, 17, 19, 18]

theorem odd_ok : InvPairOK 24 oddArr oddArr = true ∧ autArrOK oddArr oddArr = true := by
  decide +kernel

@[expose] def oddP : S24 := permOfArr 24 oddArr oddArr odd_ok.1

theorem hasArr_oddP : HasArr oddP oddArr := hasArr_permOfArr odd_ok.1

theorem hasArr_oddP_inv : HasArr oddP⁻¹ oddArr := hasArr_permOfArr_inv odd_ok.1

theorem oddP_mem : oddP ∈ AutPerm := mem_AutPerm_of_arr _ odd_ok.2

@[expose] def oddColArr : Array ℕ := #[0, 1, 2, 3, 5, 4]

theorem oddCol_ok : InvPairOK 6 oddColArr oddColArr = true := by decide +kernel

@[expose] def oddCol : Equiv.Perm (Fin 6) := permOfArr 6 oddColArr oddColArr oddCol_ok

theorem oddP_cols : ∀ i < 24, oddArr[i]! / 4 = oddColArr[i / 4]! := by decide +kernel

theorem colOf_oddP (i : Fin 24) : colOf (oddP i) = oddCol (colOf i) :=
  Fin.ext (by
    show (oddP i : ℕ) / 4 = (oddCol (colOf i) : ℕ)
    rw [hasArr_oddP i, oddCol, permOfArr_val]
    exact oddP_cols i i.2)

theorem oddP_mem_MY0 : oddP ∈ MY M24g S0 := mem_MY0.2 ⟨oddP_mem, ⟨oddCol, colOf_oddP⟩⟩

theorem piM_oddP : piM ⟨oddP, oddP_mem_MY0⟩ = oddCol := piM_eq colOf_oddP

theorem sign_oddCol : Equiv.Perm.sign oddCol = -1 := by decide

theorem oddCol_not_mem_alt : oddCol ∉ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_oddCol]
  decide

theorem oddP_not_mem_Lz : oddP ∉ Lz := by
  intro h
  have h1 := colLz_mem oddP h
  rw [A6c_eq] at h1
  have h2 : colLz ⟨oddP, h⟩ = oddCol := piM_oddP
  rw [h2] at h1
  exact oddCol_not_mem_alt h1

theorem kappa_colF (j : Fin 6) : cocodeCoords.κ (eY (colF j)) = z0 := by
  have hbits : ∀ j < 6, ∀ i < 24, (i / 4 = j ↔ (15 <<< (4 * j)).testBit i = true) := by
    decide +kernel
  have hval : ∀ j < 6, actM ccECols (15 <<< (4 * j)) = 31 := by decide +kernel
  have h : Multiplicative.toAdd (eY (colF j)) = bvec 24 (15 <<< (4 * (j : ℕ))) := by
    funext i
    rw [toAdd_eY, bvec_apply]
    have hb := hbits (j : ℕ) j.2 i i.2
    have hi : i ∈ colF j ↔ (i : ℕ) / 4 = (j : ℕ) := by
      rw [mem_colF]
      simp only [colOf, Fin.ext_iff]
    by_cases hc : i ∈ colF j
    · have := hb.1 (hi.1 hc)
      simp [hc, this]
    · have : ¬ (15 <<< (4 * (j : ℕ))).testBit i = true := fun h' => hc (hi.2 (hb.2 h'))
      simp [hc, this]
  change Multiplicative.ofAdd (ccE (Multiplicative.toAdd (eY (colF j)))) = _
  rw [h, ccE_bvec, hval (j : ℕ) j.2]
  rfl

theorem eY_colF_mem_coreMod (j : Fin 6) : eY (colF j) ∈ G6.coreMod 24 := by
  rw [G6.mem_coreMod, sum_toAdd_eY, card_colF]
  decide

theorem rho11_z0_of_mem {σ : ↥AutPerm} (h : (σ : S24) ∈ MulAction.stabilizer S24 S0) :
    rho11 AutPerm le_rfl σ z0 = z0 := by
  have hσ : (σ : S24) • S0 = S0 := MulAction.mem_stabilizer_iff.1 h
  have h1 : (σ : S24) • colF 0 ∈ S0 := by
    have : (σ : S24) • colF 0 ∈ (σ : S24) • S0 := Finset.smul_mem_smul_finset (mem_S0 0)
    rwa [hσ] at this
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h1
  rw [← kappa_colF 0]
  have h2 := SecCoords.κ_permAct_rho cocodeCoords AutPerm (fun _ hσ => preserves_cocode hσ) σ
    (eY_colF_mem_coreMod 0)
  have h3 : rho11 AutPerm le_rfl σ (cocodeCoords.κ (eY (colF 0))) =
      cocodeCoords.κ (G6.permAct 24 (σ : S24) (eY (colF 0))) := h2.symm
  rw [h3, ← eY_smul, ← hj, kappa_colF]
  exact (kappa_colF 0).symm

theorem img11_MY0_le : img11 (MY M24g S0) ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) := by
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨⟨σ, Subgroup.mem_subgroupOf.2 σ.2, rfl⟩, ?_⟩
  exact mem_centSub_zpowers.2 (rho11_z0_of_mem (Subgroup.mem_subgroupOf.1 hσ).2)

theorem card_img11' {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : Γ ≤ AutPerm) : Nat.card ↥(img11 Γ) = Nat.card ↥Γ := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv]

theorem card_MY0 :
    Nat.card ↥(MY M24g S0) = 138240 := by
  have h1 : Nat.card ↥(MY M24g S0) ≤ 138240 := by
    rw [← card_img11' MY0_le_autPerm]
    exact (Subgroup.card_le_of_le img11_MY0_le).trans card_stab_le
  have h2 : Nat.card ↥Lz ∣ Nat.card ↥(MY M24g S0) := Subgroup.card_dvd_of_le Lz_le_MY0
  rw [card_Lz] at h2
  have h3 : Nat.card ↥(MY M24g S0) ≠ 69120 := by
    intro h
    have : Lz = MY M24g S0 :=
      Subgroup.eq_of_le_of_card_ge Lz_le_MY0 (by rw [card_Lz, h])
    exact oddP_not_mem_Lz (this ▸ oddP_mem_MY0)
  obtain ⟨k, hk⟩ := h2
  have hpos : 0 < Nat.card ↥(MY M24g S0) := Nat.card_pos
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · omega

theorem index_LzM :
    (Lz.subgroupOf (MY M24g S0)).index = 2 := by
  have h1 := Subgroup.card_mul_index (Lz.subgroupOf (MY M24g S0))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lz_le_MY0).toEquiv, card_Lz, card_MY0] at h1
  omega

theorem MY0_cases
    {σ : S24} (hσ : σ ∈ MY M24g S0) :
    σ ∈ Lz ∨ oddP⁻¹ * σ ∈ Lz := by
  by_cases h : σ ∈ Lz
  · exact Or.inl h
  · right
    have hi := index_LzM
    have h1 : (⟨oddP⁻¹ * σ, MY M24g S0 |>.mul_mem (MY M24g S0 |>.inv_mem oddP_mem_MY0) hσ⟩ :
        ↥(MY M24g S0)) ∈ Lz.subgroupOf (MY M24g S0) := by
      have hm : (⟨oddP⁻¹, (MY M24g S0).inv_mem oddP_mem_MY0⟩ * ⟨σ, hσ⟩ : ↥(MY M24g S0)) ∈
          Lz.subgroupOf (MY M24g S0) := by
        rw [Subgroup.mul_mem_iff_of_index_two hi]
        constructor
        · intro h'
          exact absurd (by simpa using Subgroup.mem_subgroupOf.1 h') (by
            intro hh
            exact oddP_not_mem_Lz (by simpa using Lz.inv_mem hh))
        · intro h'
          exact absurd (Subgroup.mem_subgroupOf.1 h') h
      exact hm
    exact Subgroup.mem_subgroupOf.1 h1

theorem sign_piM_one {σ : S24} (hσ : σ ∈ MY M24g S0) (h : σ ∈ Lz) :
    Equiv.Perm.sign (piM ⟨σ, hσ⟩) = 1 := by
  have h1 := colLz_mem σ h
  rw [A6c_eq] at h1
  exact Equiv.Perm.mem_alternatingGroup.1 h1

theorem sign_piM_neg
    {σ : S24} (hσ : σ ∈ MY M24g S0) (h : σ ∉ Lz) :
    Equiv.Perm.sign (piM ⟨σ, hσ⟩) = -1 := by
  rcases MY0_cases hσ with h1 | h1
  · exact absurd h1 h
  · have hm : oddP⁻¹ * σ ∈ MY M24g S0 :=
      (MY M24g S0).mul_mem ((MY M24g S0).inv_mem oddP_mem_MY0) hσ
    have h2 := sign_piM_one hm h1
    have h3 : piM ⟨oddP⁻¹ * σ, hm⟩ = (piM ⟨oddP, oddP_mem_MY0⟩)⁻¹ * piM ⟨σ, hσ⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [h3, piM_oddP, map_mul, map_inv, sign_oddCol] at h2
    rcases Int.units_eq_one_or (Equiv.Perm.sign (piM ⟨σ, hσ⟩)) with h4 | h4
    · rw [h4] at h2
      exact absurd h2 (by decide)
    · exact h4

theorem range_piM :
    piM.range = ⊤ := by
  refine eq_top_iff.2 fun τ _ => ?_
  by_cases hτ : τ ∈ alternatingGroup (Fin 6)
  · rw [← A6c_eq, ← range_colLz] at hτ
    obtain ⟨σ, hσ⟩ := hτ
    exact ⟨⟨σ.1, Lz_le_MY0 σ.2⟩, by rw [piM_lz σ.2]; exact hσ⟩
  · have hs : Equiv.Perm.sign τ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
      · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hτ
      · exact h
    have h2 : τ * oddCol⁻¹ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, sign_oddCol]
      decide
    rw [← A6c_eq, ← range_colLz] at h2
    obtain ⟨σ, hσ⟩ := h2
    refine ⟨⟨σ.1, Lz_le_MY0 σ.2⟩ * ⟨oddP, oddP_mem_MY0⟩, ?_⟩
    rw [map_mul, piM_lz σ.2, piM_oddP]
    have : colLz σ = τ * oddCol⁻¹ := hσ
    rw [this, inv_mul_cancel_right]

theorem piM_surjective :
    Function.Surjective piM :=
  MonoidHom.range_eq_top.1 range_piM

theorem card_perm_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_ker_piM :
    Nat.card piM.ker = 192 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup piM.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange piM).toEquiv, range_piM,
    Subgroup.card_top, card_perm_six, card_MY0] at h
  omega

@[expose] def moCols : List ℕ := [1, 3, 4, 12, 16, 48]

theorem ksConj_odd : ∀ c < 64, cArr oddArr (cArr (ksC c) oddArr) = ksC (actM moCols c) := by
  decide +kernel

theorem moCols_lt : ∀ c < 64, actM moCols c < 64 := by decide +kernel

theorem conj_ksP_odd (c : Fin 64) :
    oddP * ksP c * oddP⁻¹ = ksP ⟨actM moCols c, moCols_lt c c.2⟩ := by
  have h : HasArr (oddP * ksP c * oddP⁻¹) (cArr oddArr (cArr (ksC c) oddArr)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_oddP (hasArr_mul (hasArr_ksP c) hasArr_oddP_inv)
  rw [ksConj_odd c c.2] at h
  exact perm_eq_of_hasArr h (hasArr_ksP _)

theorem oddP_conj_KSp {k : S24} (hk : k ∈ KSp) : oddP * k * oddP⁻¹ ∈ KSp := by
  obtain ⟨c, rfl⟩ := mem_KSp_iff.1 hk
  rw [conj_ksP_odd]
  exact ksP_mem_KSp _

theorem MY0_conj_KSp
    {σ k : S24} (hσ : σ ∈ MY M24g S0) (hk : k ∈ KSp) :
    σ * k * σ⁻¹ ∈ KSp := by
  rcases MY0_cases hσ with h | h
  · exact (Subgroup.mem_normalizer_iff.1 (Lz_le_normalizer_KSp h) k).1 hk
  · have h1 : (oddP⁻¹ * σ) * k * (oddP⁻¹ * σ)⁻¹ ∈ KSp :=
      (Subgroup.mem_normalizer_iff.1 (Lz_le_normalizer_KSp h) k).1 hk
    have h2 := oddP_conj_KSp h1
    have e : oddP * ((oddP⁻¹ * σ) * k * (oddP⁻¹ * σ)⁻¹) * oddP⁻¹ = σ * k * σ⁻¹ := by group
    rw [e] at h2
    exact h2

theorem MY0_le_normalizer_KSp :
    MY M24g S0 ≤ Subgroup.normalizer (KSp : Set S24) := by
  intro σ hσ
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  exact MY0_conj_KSp hσ hk

theorem KSp_le_pCoreOf_MY0 :
    KSp ≤ pCoreOf 2 (MY M24g S0) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 KSp_le_MY0 MY0_le_normalizer_KSp
    isPGroup_KSp

theorem pCoreOf_MY0 :
    pCoreOf 2 (MY M24g S0) = KSp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Open.pCore 2 ↥(MY M24g S0) with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hker : N ≤ piM.ker := by
    by_contra hnk
    have hM : IsPGroup 2 (N.map piM) := hNp.map piM
    have hMn : (N.map piM).Normal := hNn.map piM piM_surjective
    have hnt : Nontrivial (N.map piM) := by
      refine (Subgroup.nontrivial_iff_ne_bot _).2 ?_
      intro h
      exact hnk ((Subgroup.map_eq_bot_iff N).1 h)
    have hle : alternatingGroup (Fin 6) ≤ N.map piM :=
      Equiv.Perm.alternatingGroup_le_of_normal
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
    have hAp : IsPGroup 2 (alternatingGroup (Fin 6)) := hM.to_le hle
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hk
    have h3 : 3 ∣ 2 ^ k := by
      rw [← hk]
      decide
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)
  have hcard : Nat.card N ≤ 64 := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    have h1 : Nat.card N ∣ 192 := card_ker_piM ▸ Subgroup.card_dvd_of_le hker
    rw [hk] at h1 ⊢
    have h2 : 2 ^ k ∣ 64 :=
      (Nat.Coprime.pow_left k (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_right
        (by simpa using h1)
    exact Nat.le_of_dvd (by norm_num) h2
  have hK : KSp.subgroupOf (MY M24g S0) ≤ N := by
    intro k hk
    have := KSp_le_pCoreOf_MY0 (Subgroup.mem_subgroupOf.1 hk)
    obtain ⟨n, hn, hnk⟩ := this
    rwa [show n = k from Subtype.ext hnk] at hn
  have hKc : Nat.card (KSp.subgroupOf (MY M24g S0)) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe KSp_le_MY0).toEquiv, card_KSp]
  have hEq : KSp.subgroupOf (MY M24g S0) = N :=
    Subgroup.eq_of_le_of_card_ge hK (by rw [hKc]; exact hcard)
  rw [pCoreOf, ← hN, ← hEq, Subgroup.map_subgroupOf_eq_of_le KSp_le_MY0]

@[expose] noncomputable def N0 : Subgroup S24 := piM.ker.map (MY M24g S0).subtype

theorem N0_subgroupOf : N0.subgroupOf (MY M24g S0) = piM.ker :=
  Subgroup.comap_map_eq_self_of_injective (MY M24g S0).subtype_injective _

theorem mem_N0 {σ : S24} : σ ∈ N0 ↔ ∃ h : σ ∈ MY M24g S0, piM ⟨σ, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨σ, h⟩, hx, rfl⟩

theorem N0_le_MY0 : N0 ≤ MY M24g S0 := fun _ h => (mem_N0.1 h).1

theorem KSp_le_N0 : KSp ≤ N0 := fun σ h => by
  obtain ⟨c, rfl⟩ := mem_KSp_iff.1 h
  exact mem_N0.2 ⟨KSp_le_MY0 (ksP_mem_KSp c), piM_ksP c⟩

theorem card_N0 :
    Nat.card ↥N0 = 192 := by
  rw [N0, Subgroup.card_map_of_injective (MY M24g S0).subtype_injective, card_ker_piM]

theorem cube_mem_KSp
    {σ : S24} (hσ : σ ∈ N0) : σ ^ 3 ∈ KSp := by
  obtain ⟨hMY, hπ⟩ := mem_N0.1 hσ
  set Kk : Subgroup ↥(MY M24g S0) := KSp.subgroupOf (MY M24g S0) with hKk
  have hKn : Kk.Normal := ⟨fun k hk g => by
    have := MY0_conj_KSp g.2 (Subgroup.mem_subgroupOf.1 hk)
    exact Subgroup.mem_subgroupOf.2 this⟩
  have hKN : Kk ≤ piM.ker := fun k hk => by
    obtain ⟨c, hc⟩ := mem_KSp_iff.1 (Subgroup.mem_subgroupOf.1 hk)
    have : k = ⟨ksP c, KSp_le_MY0 (ksP_mem_KSp c)⟩ := Subtype.ext hc.symm
    rw [this]
    exact piM_ksP c
  have hcardK : Nat.card Kk = 64 := by
    rw [hKk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe KSp_le_MY0).toEquiv, card_KSp]
  have hQ : Nat.card (↥piM.ker ⧸ Kk.subgroupOf piM.ker) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Kk.subgroupOf piM.ker)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv, hcardK, card_ker_piM] at h
    omega
  have h1 := pow_card_eq_one' (G := ↥piM.ker ⧸ Kk.subgroupOf piM.ker)
    (x := QuotientGroup.mk (⟨⟨σ, hMY⟩, hπ⟩ : ↥piM.ker))
  rw [hQ, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  have h2 := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 h1)
  simpa using h2

theorem isO23_MY0 :
    IsO23' (MY M24g S0) N0 := by
  refine ⟨N0_le_MY0, ?_, ?_, ?_, ?_⟩
  · intro g hg n hn
    obtain ⟨hnM, hπ⟩ := mem_N0.1 hn
    refine mem_N0.2 ⟨(MY M24g S0).mul_mem ((MY M24g S0).mul_mem hg hnM)
      ((MY M24g S0).inv_mem hg), ?_⟩
    have : (⟨g * n * g⁻¹, _⟩ : ↥(MY M24g S0)) = ⟨g, hg⟩ * ⟨n, hnM⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, hπ, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · rw [pCoreOf_MY0]
    exact KSp_le_N0
  · intro n hn
    exact ⟨1, by rw [pCoreOf_MY0, pow_one]; exact cube_mem_KSp hn⟩
  · intro N' hN'le hN'norm hN'core hN'3 σ hσ
    have hσM : σ ∈ MY M24g S0 := hN'le hσ
    have hN'' : (N'.subgroupOf (MY M24g S0)).Normal := ⟨fun n hn g => by
      have := hN'norm g g.2 n (Subgroup.mem_subgroupOf.1 hn)
      exact Subgroup.mem_subgroupOf.2 (by simpa using this)⟩
    have hQn : ((N'.subgroupOf (MY M24g S0)).map piM).Normal := hN''.map piM piM_surjective
    by_cases hbot : (N'.subgroupOf (MY M24g S0)).map piM = ⊥
    · have h1 : piM ⟨σ, hσM⟩ ∈ (N'.subgroupOf (MY M24g S0)).map piM :=
        ⟨⟨σ, hσM⟩, Subgroup.mem_subgroupOf.2 hσ, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact mem_N0.2 ⟨hσM, h1⟩
    · exfalso
      have hnt : Nontrivial ((N'.subgroupOf (MY M24g S0)).map piM) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hbot
      have hle := Equiv.Perm.alternatingGroup_le_of_normal
        (N := (N'.subgroupOf (MY M24g S0)).map piM)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
      have hxA : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) :=
        Equiv.Perm.mem_alternatingGroup.2 (by decide)
      obtain ⟨n, hn, hnx⟩ := hle hxA
      obtain ⟨k, hk⟩ := hN'3 (n : S24) (Subgroup.mem_subgroupOf.1 hn)
      rw [pCoreOf_MY0] at hk
      obtain ⟨c, hc⟩ := mem_KSp_iff.1 hk
      have h1 : piM (n ^ 3 ^ k) = 1 := by
        have : n ^ 3 ^ k = ⟨ksP c, KSp_le_MY0 (ksP_mem_KSp c)⟩ := Subtype.ext (by
          rw [Subgroup.coe_pow]; exact hc.symm)
        rw [this]
        exact piM_ksP c
      rw [map_pow, hnx] at h1
      have hx2 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ^ 2 = 1 := by decide
      obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
      rw [hm, pow_succ, pow_mul, hx2, one_pow, one_mul] at h1
      exact absurd h1 (by decide)

@[expose] def tArr : Array ℕ :=
  #[3, 1, 0, 2, 7, 5, 4, 6, 10, 8, 9, 11, 14, 12, 13, 15, 17, 19, 18, 16, 21, 23, 22, 20]

@[expose] def tInv : Array ℕ :=
  #[2, 1, 3, 0, 6, 5, 7, 4, 9, 10, 8, 11, 13, 14, 12, 15, 19, 16, 18, 17, 23, 20, 22, 21]

theorem t_ok : InvPairOK 24 tArr tInv = true ∧ autArrOK tArr tInv = true := by decide +kernel

@[expose] def tP : S24 := permOfArr 24 tArr tInv t_ok.1

theorem hasArr_tP : HasArr tP tArr := hasArr_permOfArr t_ok.1

theorem tP_mem : tP ∈ AutPerm := mem_AutPerm_of_arr _ t_ok.2

theorem tP_cols : ∀ i < 24, tArr[i]! / 4 = i / 4 := by decide +kernel

theorem colOf_tP (i : Fin 24) : colOf (tP i) = colOf i :=
  Fin.ext (by
    show (tP i : ℕ) / 4 = (i : ℕ) / 4
    rw [hasArr_tP i]
    exact tP_cols i i.2)

theorem tP_mem_MY0 : tP ∈ MY M24g S0 := mem_MY0.2 ⟨tP_mem, ⟨1, colOf_tP⟩⟩

theorem piM_tP : piM ⟨tP, tP_mem_MY0⟩ = 1 := piM_eq colOf_tP

theorem tP_mem_N0 : tP ∈ N0 := mem_N0.2 ⟨tP_mem_MY0, piM_tP⟩

theorem tArr_cube : cArr tArr (cArr tArr tArr) = idArr := by decide +kernel

theorem tP_pow_three : tP ^ 3 = 1 := by
  have h : HasArr (tP * (tP * tP)) (cArr tArr (cArr tArr tArr)) :=
    hasArr_mul hasArr_tP (hasArr_mul hasArr_tP hasArr_tP)
  rw [tArr_cube] at h
  rw [show tP ^ 3 = tP * (tP * tP) by rw [pow_succ, pow_two, mul_assoc]]
  exact perm_eq_of_hasArr h hasArr_one

theorem tP_ne_one : tP ≠ 1 := by
  intro h
  have h1 := hasArr_tP 0
  rw [h] at h1
  exact absurd h1 (by decide)

theorem orderOf_tP : orderOf tP = 3 := orderOf_eq_prime tP_pow_three tP_ne_one

theorem N0_eq_sup :
    N0 = KSp ⊔ Subgroup.zpowers tP := by
  refine (Subgroup.eq_of_le_of_card_ge (sup_le KSp_le_N0 ((Subgroup.zpowers_le).2 tP_mem_N0))
    ?_).symm
  have h64 : 64 ∣ Nat.card ↥(KSp ⊔ Subgroup.zpowers tP) := by
    rw [← card_KSp]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card ↥(KSp ⊔ Subgroup.zpowers tP) := by
    rw [← orderOf_tP, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h192 : 192 ∣ Nat.card ↥(KSp ⊔ Subgroup.zpowers tP) := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 64 3) h64 h3
    simpa using this
  rw [card_N0]
  exact Nat.le_of_dvd Nat.card_pos h192

end CFSG.Quasithin.H153
