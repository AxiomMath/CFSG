module

public import CFSG.Monster.B.Fischer.InducedOrbits
public import CFSG.Monster.B.Fischer.CanonicalChecks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu
  CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def coordImg (x : X₀) : W₀ := K₀.mkQ (e x)

theorem coordImg_eq (x : X₀) : coordImg x = K₀.mkQ (vecOf (2 ^ (pos x : ℕ))) := by
  rw [coordImg, e_eq_vecOf]

theorem coordImg_mem (x : X₀) : coordImg x ∈ Lw 1 := by
  show cosetWt (coordImg x) = 1
  refine cosetWt_eq_iff.2 ⟨⟨e x, rfl, ?_⟩, fun v hv => ?_⟩
  · rw [e_eq_vecOf, hammingNorm_vecOf]
    exact popc_coord (pos x)
  · by_contra h
    push Not at h
    have hv0 : v = 0 := by
      rw [Nat.lt_one_iff, hammingNorm_eq_zero] at h
      exact h
    rw [hv0, map_zero, coordImg_eq, eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      vecOf_mem_K₀_iff (two_pow_lt_22 (pos x))] at hv
    exact red_coord (pos x) hv

theorem coordImg_injective : Function.Injective coordImg := by
  intro x y h
  by_contra hne
  have hpos : pos x ≠ pos y := fun h' => hne (by rw [← coordAt_pos x, h', coordAt_pos])
  rw [coordImg_eq, coordImg_eq, mkQ_eq_iff_mem, ← vecOf_xor,
    vecOf_mem_K₀_iff (Nat.xor_lt_two_pow (two_pow_lt_22 _) (two_pow_lt_22 _))] at h
  exact red_coord_pair _ _ hpos h

theorem ncard_L1 :
    (Lw 1).ncard = 22 := by
  rw [L1_eq, ncard_orbitW (by simp), wCert_size.2.1]

theorem range_coordImg :
    Set.range coordImg = Lw 1 := by
  have : Finite W₀ := Finite.of_equiv _ wEquiv
  refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 coordImg_mem) ?_ (Set.toFinite _)
  rw [Set.ncard_range_of_injective coordImg_injective, ncard_L1, Nat.card_eq_fintype_card,
    Fintype.card_coe, card_X₀]

@[expose] noncomputable def l1Equiv :
    X₀ ≃ Lw 1 :=
  Equiv.ofBijective (fun x => ⟨coordImg x, coordImg_mem x⟩)
    ⟨fun x y h => coordImg_injective (congrArg Subtype.val h), fun w => by
      have hw : (w : W₀) ∈ Set.range coordImg := by
        rw [range_coordImg]
        exact w.2
      obtain ⟨x, hx⟩ := hw
      exact ⟨x, Subtype.ext hx⟩⟩

theorem l1Equiv_symm_coordImg
    (x : X₀) : l1Equiv.symm ⟨coordImg x, coordImg_mem x⟩ = x :=
  l1Equiv.symm_apply_eq.2 rfl

theorem coordImg_l1Equiv_symm
    (w : Lw 1) : coordImg (l1Equiv.symm w) = w :=
  congrArg Subtype.val (l1Equiv.apply_symm_apply w)

theorem not_mem_Lw {i j : ℕ} {w : W₀} (hi : w ∈ Lw i) (hij : i ≠ j) : w ∉ Lw j :=
  fun hj => hij ((show cosetWt w = i from hi).symm.trans hj)

theorem zero_mem_L0 : (0 : W₀) ∈ Lw 0 := by
  show cosetWt 0 = 0
  rw [← wv_zero]
  exact cosetWt_seed.1

theorem ncard_Z462 :

    Z462.ncard = 462 := by rw [Z462, ncard_orbitZ (by simp), zCert_size.1]

theorem ncard_Z770 :

    Z770.ncard = 770 := by rw [Z770, ncard_orbitZ (by simp), zCert_size.2.1]

theorem ncard_Z1232 :
    Z1232.ncard = 1232 := by
  rw [Z1232, ncard_orbitZ (by simp), zCert_size.2.2]

theorem orbitZ_eq_of_mem_both
    {z z₁ z₂ : Z} (h1 : z ∈ orbitZ z₁) (h2 : z ∈ orbitZ z₂) :
    orbitZ z₁ = orbitZ z₂ :=
  (orbitZ_eq_of_mem h1).symm.trans (orbitZ_eq_of_mem h2)

theorem not_mem_Z770_of_mem_Z1232
    {z : Z} (h : z ∈ Z1232) : z ∉ Z770 := fun h' => by
  have e : Z770 = Z1232 := orbitZ_eq_of_mem_both h' h
  have := ncard_Z770
  rw [e, ncard_Z1232] at this
  omega

theorem not_mem_Z770_of_mem_Z462
    {z : Z} (h : z ∈ Z462) : z ∉ Z770 := fun h' => by
  have e : Z462 = Z770 := orbitZ_eq_of_mem_both h h'
  have := ncard_Z462
  rw [e, ncard_Z770] at this
  omega

theorem not_mem_Z1232_of_mem_Z462
    {z : Z} (h : z ∈ Z462) : z ∉ Z1232 := fun h' => by
  have e : Z462 = Z1232 := orbitZ_eq_of_mem_both h h'
  have := ncard_Z462
  rw [e, ncard_Z1232] at this
  omega

open scoped _root_.Classical in
@[expose] noncomputable def tFun :
    Y → Y
  | .inl x => .inr (.inl (coordImg x))
  | .inr (.inl w) =>
    if h1 : w ∈ Lw 1 then .inl (l1Equiv.symm ⟨w, h1⟩)
    else if h3 : w ∈ Lw 3 then .inr (.inr (sigmaEquiv ⟨w, h3⟩ : Z))
    else .inr (.inl w)
  | .inr (.inr z) =>
    if h7 : z ∈ Z770 then .inr (.inl (sigmaEquiv.symm ⟨z, h7⟩ : W₀))
    else if h12 : z ∈ Z1232 then .inr (.inr (tauPerm ⟨z, h12⟩ : Z))
    else .inr (.inr z)

theorem tFun_inl
    (x : X₀) : tFun (.inl x) = .inr (.inl (coordImg x)) := rfl

theorem tFun_L1
    {w : W₀} (h : w ∈ Lw 1) : tFun (.inr (.inl w)) = .inl (l1Equiv.symm ⟨w, h⟩) := by
  simp only [tFun, h, ↓reduceDIte]

theorem tFun_L3
    {w : W₀} (h : w ∈ Lw 3) :
    tFun (.inr (.inl w)) = .inr (.inr (sigmaEquiv ⟨w, h⟩ : Z)) := by
  simp only [tFun, not_mem_Lw h (by norm_num : (3 : ℕ) ≠ 1), h, ↓reduceDIte]

theorem tFun_fixW
    {w : W₀} (h1 : w ∉ Lw 1) (h3 : w ∉ Lw 3) :
    tFun (.inr (.inl w)) = .inr (.inl w) := by
  simp only [tFun, h1, h3, ↓reduceDIte]

theorem tFun_Z770
    {z : Z} (h : z ∈ Z770) :
    tFun (.inr (.inr z)) = .inr (.inl (sigmaEquiv.symm ⟨z, h⟩ : W₀)) := by
  simp only [tFun, h, ↓reduceDIte]

theorem tFun_Z1232
    {z : Z} (h : z ∈ Z1232) :
    tFun (.inr (.inr z)) = .inr (.inr (tauPerm ⟨z, h⟩ : Z)) := by
  simp only [tFun, not_mem_Z770_of_mem_Z1232 h, h, ↓reduceDIte]

theorem tFun_fixZ
    {z : Z} (h7 : z ∉ Z770) (h12 : z ∉ Z1232) :
    tFun (.inr (.inr z)) = .inr (.inr z) := by
  simp only [tFun, h7, h12, ↓reduceDIte]

theorem tFun_involutive :
    Function.Involutive tFun := by
  rintro (x | w | z)
  · rw [tFun_inl, tFun_L1 (coordImg_mem x), l1Equiv_symm_coordImg]
  · by_cases h1 : w ∈ Lw 1
    · rw [tFun_L1 h1, tFun_inl, coordImg_l1Equiv_symm]
    · by_cases h3 : w ∈ Lw 3
      · rw [tFun_L3 h3, tFun_Z770 (sigmaEquiv ⟨w, h3⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply]
      · rw [tFun_fixW h1 h3, tFun_fixW h1 h3]
  · by_cases h7 : z ∈ Z770
    · rw [tFun_Z770 h7, tFun_L3 (sigmaEquiv.symm ⟨z, h7⟩).2, Subtype.coe_eta,
        Equiv.apply_symm_apply]
    · by_cases h12 : z ∈ Z1232
      · rw [tFun_Z1232 h12, tFun_Z1232 (tauPerm ⟨z, h12⟩).2, Subtype.coe_eta, tauPerm_apply,
          tauPerm_apply, tauL_tauL]
      · rw [tFun_fixZ h7 h12, tFun_fixZ h7 h12]

@[expose] noncomputable def tPerm :

    Equiv.Perm Y := Function.Involutive.toPerm tFun tFun_involutive

theorem tPerm_apply
    (y : Y) : tPerm y = tFun y := rfl

@[expose] noncomputable def J :
    Subgroup (Equiv.Perm Y) :=
  Subgroup.closure (Set.range (MulAction.toPermHom F₀ Y) ∪ {tPerm})

@[expose] noncomputable def jGen
    (k : ℕ) : Equiv.Perm Y :=
  if k < 2 then MulAction.toPerm (kF (genAB k))
  else if k < 12 then MulAction.toPerm (wBasis (k - 2)) else tPerm

theorem jGen_zero :
    jGen 0 = MulAction.toPerm (kF m22a) := by
  simp only [jGen, Nat.ofNat_pos, ↓reduceIte, genAB]

theorem jGen_one :
    jGen 1 = MulAction.toPerm (kF m22b) := by
  simp only [jGen, Nat.one_lt_ofNat, ↓reduceIte, genAB, one_ne_zero]

theorem jGen_trans
    (t : Fin 10) : jGen (t + 2) = MulAction.toPerm (wF (bW t)) := by
  have h1 : ¬((t : ℕ) + 2 < 2) := by omega
  have h2 : (t : ℕ) + 2 < 12 := by omega
  simp only [jGen, h1, h2, ↓reduceIte, Nat.add_sub_cancel, bW_eq]
  rfl

theorem jGen_twelve :
    jGen 12 = tPerm := by
  simp only [jGen, Nat.not_lt.2 (by norm_num : 2 ≤ 12), Nat.lt_irrefl, ↓reduceIte]

theorem kF_mem
    {H : Subgroup F₀} (ha : kF m22a ∈ H) (hb : kF m22b ∈ H)
    (k : CFSG.Blueprint.NativeSporadic.M22) : kF k ∈ H :=
  m22_induction (P := fun k => kF k ∈ H) ha hb
    (fun x y hx hy => by rw [kF_mul]; exact H.mul_mem hx hy)
    (fun x hx => by
      rw [show kF x⁻¹ = (kF x)⁻¹ from map_inv SemidirectProduct.inr x]
      exact H.inv_mem hx)
    (by rw [show kF 1 = 1 from map_one SemidirectProduct.inr]; exact H.one_mem) k

theorem wF_add
    (r s : W₀) : wF (r + s) = wF r * wF s := by
  rw [wF, wF, wF, ofAdd_add, map_mul]

theorem wF_zero :
    wF 0 = 1 := by rw [wF, ofAdd_zero, map_one]

theorem wF_mem
    {H : Subgroup F₀} (hb : ∀ t : Fin 10, wF (bW t) ∈ H) (r : W₀) : wF r ∈ H := by
  have hr : r ∈ Submodule.span (ZMod 2) (Set.range bW) := by
    rw [bW.span_eq]
    trivial
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact hb t
  | zero => rw [wF_zero]; exact H.one_mem
  | add x y _ _ hx hy => rw [wF_add]; exact H.mul_mem hx hy
  | smul c x _ hx =>
    obtain rfl | rfl := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    · rw [zero_smul, wF_zero]
      exact H.one_mem
    · rw [one_smul]
      exact hx

theorem F₀_mem
    {H : Subgroup F₀} (ha : kF m22a ∈ H) (hb : kF m22b ∈ H)
    (ht : ∀ t : Fin 10, wF (bW t) ∈ H) (f : F₀) : f ∈ H := by
  rw [← SemidirectProduct.inl_left_mul_inr_right f]
  exact H.mul_mem (wF_mem ht (Multiplicative.toAdd f.left)) (kF_mem ha hb f.right)

theorem J_eq_closure_jGen :

    J = Subgroup.closure (Set.range fun k : Fin 13 => jGen k) := by
  apply le_antisymm
  · rw [J, Subgroup.closure_le]
    rintro g (⟨f, rfl⟩ | hg)
    · refine F₀_mem (H := (Subgroup.closure (Set.range fun k : Fin 13 => jGen k)).comap
        (MulAction.toPermHom F₀ Y)) ?_ ?_ ?_ f
      · exact Subgroup.subset_closure ⟨0, jGen_zero⟩
      · exact Subgroup.subset_closure ⟨1, jGen_one⟩
      · intro t
        exact Subgroup.subset_closure ⟨⟨t + 2, by omega⟩, jGen_trans t⟩
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Subgroup.subset_closure ⟨12, jGen_twelve⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    show jGen k ∈ J
    unfold jGen
    split_ifs
    · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr rfl)

theorem sigmaEquiv_val
    (w : L3) : (sigmaEquiv w : Z) = decZn (sigmaFun (idxW w)) := rfl

theorem sigmaEquiv_wv
    {u : ℕ} (hu : u < 1024) (hw : wv u ∈ Lw 3) :
    (sigmaEquiv ⟨wv u, hw⟩ : Z) = decZn (sigmaFun u) := by
  rw [sigmaEquiv_val, show ((⟨wv u, hw⟩ : L3) : W₀) = wv u from rfl, idxW_wv hu]

theorem tauPerm_decZn
    {n : ℕ} (hn : n < 2464) (hz : decZn n ∈ Z1232) :
    (tauPerm ⟨decZn n, hz⟩ : Z) = decZn (tauFun n) := by
  rw [tauPerm_apply, tauL_val, show ((⟨decZn n, hz⟩ : Z1232T) : Z) = decZn n from rfl,
    idxZ_decZn hn]

theorem coordImg_of_red {x : X₀} {m : ℕ}
    (h : red 12 pivK rowK (spreadW m ^^^ 2 ^ (pos x : ℕ)) = 0) : coordImg x = wv m := by
  rw [coordImg_eq, wv, mkQ_eq_iff_mem, ← vecOf_xor, Nat.xor_comm,
    vecOf_mem_K₀_iff (Nat.xor_lt_two_pow (spreadW_lt _) (two_pow_lt_22 _))]
  exact h

theorem ι_tPerm
    (y : Y) : (ι (tPerm y) : ℕ) = indCentral[(ι y : ℕ)]! := by
  obtain ⟨hX, hL1, h0, h3, hL3, hZ0, hZ7, hZ12⟩ := central_check
  rw [tPerm_apply]
  rcases y with x | w | z
  · obtain ⟨h22, hlt, hred⟩ := hX (pos x) (pos x).2
    rw [tFun_inl, coordImg_of_red hred, ι_wv (by omega), ι_inl]
    omega
  · obtain ⟨u, hu, rfl⟩ := wv_surj w
    rw [ι_wv hu]
    rcases wCert_cover u hu with h | h | h | h
    · have hw : wv u ∈ Lw 0 := by
        have := mem_orbitW (s := 0) (by simp) h
        rw [wv_zero, orbitW_zero, Set.mem_singleton_iff] at this
        rw [this]
        exact zero_mem_L0
      rw [tFun_fixW (not_mem_Lw hw (by norm_num)) (not_mem_Lw hw (by norm_num)), ι_wv hu, h0 u h]
    · have hw : wv u ∈ Lw 1 := L1_eq ▸ mem_orbitW (by simp) h
      obtain ⟨hlt, hred⟩ := hL1 u h
      have e1 : coordImg (coordAt ⟨_, hlt⟩) = wv u := by
        apply coordImg_of_red
        rw [pos_coordAt]
        exact hred
      have e2 : l1Equiv.symm ⟨wv u, hw⟩ = coordAt ⟨_, hlt⟩ :=
        l1Equiv.symm_apply_eq.2 (Subtype.ext e1.symm)
      rw [tFun_L1 hw, e2, ι_inl, pos_coordAt]
    · have hw : wv u ∈ Lw 2 := L2_eq ▸ mem_orbitW (by simp) h
      rw [tFun_fixW (not_mem_Lw hw (by norm_num)) (not_mem_Lw hw (by norm_num)), ι_wv hu, h3 u h]
    · have hw : wv u ∈ Lw 3 := L3_eq ▸ mem_orbitW (by simp) h
      rw [tFun_L3 hw, hL3 u h, sigmaEquiv_wv hu, ι_decZn (sigma_lt h)]
  · obtain ⟨n, hn, rfl⟩ := decZn_surj z
    rw [ι_decZn hn]
    rcases zCert_cover n hn with h | h | h
    · have hz : decZn n ∈ Z462 := mem_orbitZ (by simp) h
      rw [tFun_fixZ (not_mem_Z770_of_mem_Z462 hz) (not_mem_Z1232_of_mem_Z462 hz), ι_decZn hn,
        hZ0 n h]
    · have hz : decZn n ∈ Z770 := mem_orbitZ (by simp) h
      obtain ⟨h22, hmem, hsig⟩ := hZ7 n h
      have hmlt := wCert7_lt hmem
      have hwm : wv (indCentral[1046 + n]! - 22) ∈ Lw 3 := L3_eq ▸ mem_orbitW (by simp) hmem
      have e1 : sigmaEquiv ⟨_, hwm⟩ = ⟨decZn n, hz⟩ :=
        Subtype.ext (by rw [sigmaEquiv_wv hmlt, hsig])
      rw [tFun_Z770 hz, sigmaEquiv.symm_apply_eq.2 e1.symm,
        show ((⟨_, hwm⟩ : L3) : W₀) = wv (indCentral[1046 + n]! - 22) from rfl, ι_wv hmlt]
      omega
    · have hz : decZn n ∈ Z1232 := mem_orbitZ (by simp) h
      rw [tFun_Z1232 hz, hZ12 n h, tauPerm_decZn hn hz, ι_decZn (tau_lt h)]

theorem ι_jGen
    {k : ℕ} (hk : k < 13) (y : Y) :
    (ι (jGen k y) : ℕ) = (indCandidate k)[(ι y : ℕ)]! := by
  unfold jGen indCandidate
  split_ifs with h2 h12
  · exact (repArr_gen h2).ι_smul y
  · exact (repArr_trans (by omega)).ι_smul y
  · exact ι_tPerm y

theorem Fischer_canonical_permutation_group :
    Function.Injective (fun x : X₀ => K₀.mkQ (e x)) ∧
    Set.range (fun x : X₀ => K₀.mkQ (e x)) = Lw 1 ∧
    (∀ x : X₀, tPerm (.inl x) = .inr (.inl (K₀.mkQ (e x)))) ∧
    (∀ x : X₀, tPerm (.inr (.inl (K₀.mkQ (e x)))) = .inl x) ∧
    tPerm o = o ∧
    (∀ w ∈ Lw 2, tPerm (.inr (.inl w)) = .inr (.inl w)) ∧
    (∀ z ∈ Z462, tPerm (.inr (.inr z)) = .inr (.inr z)) ∧
    (∀ u : L3, tPerm (.inr (.inl (u : W₀))) = .inr (.inr (sigmaEquiv u : Z))) ∧
    (∀ u : L3, tPerm (.inr (.inr (sigmaEquiv u : Z))) = .inr (.inl (u : W₀))) ∧
    (∀ z : Z1232T, tPerm (.inr (.inr (z : Z))) = .inr (.inr (tauPerm z : Z))) ∧
    tPerm * tPerm = 1 ∧ tPerm ≠ 1 ∧
    J = Subgroup.closure (Set.range (MulAction.toPermHom F₀ Y) ∪ {tPerm}) ∧
    jGen 0 = MulAction.toPerm (kF m22a) ∧ jGen 1 = MulAction.toPerm (kF m22b) ∧
    (∀ t : Fin 10, jGen (t + 2) = MulAction.toPerm (wF (bW t))) ∧ jGen 12 = tPerm ∧
    J = Subgroup.closure (Set.range fun k : Fin 13 => jGen k) ∧
    (∀ k < 13, ∀ y : Y, (ι (jGen k y) : ℕ) = (indCandidate k)[(ι y : ℕ)]!) := by
  refine ⟨coordImg_injective, range_coordImg, tFun_inl, fun x => ?_, ?_, fun w hw => ?_,
    fun z hz => ?_, fun u => tFun_L3 u.2, fun u => ?_, fun z => ?_, ?_, ?_, rfl, jGen_zero,
    jGen_one, jGen_trans, jGen_twelve, J_eq_closure_jGen, fun k hk => ι_jGen hk⟩
  · exact (tFun_L1 (coordImg_mem x)).trans (congrArg Sum.inl (l1Equiv_symm_coordImg x))
  · have h := zero_mem_L0
    exact tFun_fixW (not_mem_Lw h (by norm_num)) (not_mem_Lw h (by norm_num))
  · exact tFun_fixW (not_mem_Lw hw (by norm_num)) (not_mem_Lw hw (by norm_num))
  · exact tFun_fixZ (not_mem_Z770_of_mem_Z462 hz) (not_mem_Z1232_of_mem_Z462 hz)
  · rw [tPerm_apply, tFun_Z770 (sigmaEquiv u).2, Subtype.coe_eta, Equiv.symm_apply_apply]
  · exact tFun_Z1232 z.2
  · exact Equiv.ext tFun_involutive
  · intro h
    have := congrArg (fun p : Equiv.Perm Y => p (.inl (coordAt 0))) h
    simp only [Equiv.Perm.coe_one, id_eq, tPerm_apply, tFun_inl] at this
    exact Sum.inr_ne_inl this

end CFSG.Monster.B.Fischer
