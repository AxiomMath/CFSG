module

public import CFSG.Quasithin.Background.HZCoc24Gen
public import CFSG.Quasithin.Background.HZ82Base
public import Certificates.Certificate7227
public import CFSG.Quasithin.Background.HMathieuO2Cert

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans
open scoped commutatorElement

@[expose] def lzX : Equiv.Perm (Fin 24) := permOfArr 24 lzXArr lzXInv lz_ok.1

@[expose] def lzY : Equiv.Perm (Fin 24) := permOfArr 24 lzYArr lzYInv lz_ok.2.1

theorem hasArr_lzX : HasArr lzX lzXArr := hasArr_permOfArr _

theorem hasArr_lzXinv : HasArr lzX⁻¹ lzXInv := hasArr_permOfArr_inv _

theorem hasArr_lzY : HasArr lzY lzYArr := hasArr_permOfArr _

theorem hasArr_lzYinv : HasArr lzY⁻¹ lzYInv := hasArr_permOfArr_inv _

theorem lzX_mem : lzX ∈ AutPerm := mem_AutPerm_of_arr _ lz_ok.2.2.1

theorem lzY_mem : lzY ∈ AutPerm := mem_AutPerm_of_arr _ lz_ok.2.2.2

@[expose] def Lz : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {lzX, lzY}

theorem lzX_mem_Lz : lzX ∈ Lz := Subgroup.subset_closure (Set.mem_insert _ _)

theorem lzY_mem_Lz : lzY ∈ Lz := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem Lz_le : Lz ≤ AutPerm := by
  rw [Lz, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact lzX_mem
  · exact lzY_mem

theorem hasArr_getD₂ {p q : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hp : HasArr p a)
    (hq : HasArr q b) : ∀ i, HasArr ([p, q].getD i 1) ([a, b].getD i idArr)
  | 0 => hp
  | 1 => hq
  | _ + 2 => hasArr_one

section Order

open CFSG.Sporadic.Th CFSG.Sporadic.Mathieu

theorem rep_lzX : CFSG.Sporadic.Th.Rep 24 Native.lzData.tA (⟨lzX, lzX_mem_Lz⟩ : Lz) := by
  have h : (List.range 24).all (fun i => CFSG.Sporadic.Th.Native.ap Native.lzData.tA i ==
      lzXArr[i]!) = true := by decide +kernel
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]
  exact (hasArr_lzX ⟨i, hi⟩).symm

theorem rep_lzY : CFSG.Sporadic.Th.Rep 24 Native.lzData.tB (⟨lzY, lzY_mem_Lz⟩ : Lz) := by
  have h : (List.range 24).all (fun i => CFSG.Sporadic.Th.Native.ap Native.lzData.tB i ==
      lzYArr[i]!) = true := by decide +kernel
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]
  exact (hasArr_lzY ⟨i, hi⟩).symm

theorem card_Lz : Nat.card Lz = 69120 := by
  have H : Hyp Lz Native.lzData ⟨lzX, lzX_mem_Lz⟩ ⟨lzY, lzY_mem_Lz⟩ :=
    ⟨by norm_num, closure_pair_eq_top rfl _ _, rep_lzX, rep_lzY,
      Certificates.certificate7227.1⟩
  rw [card_eq H]
  rfl

end Order

theorem hasArr_c0 : HasArr ⁅lzX, lzY⁆ c0Arr := by
  rw [commutatorElement_def, mul_assoc (lzX * lzY)]
  exact hasArr_mul (hasArr_mul hasArr_lzX hasArr_lzY) (hasArr_mul hasArr_lzXinv hasArr_lzYinv)

theorem hasArr_c2 : HasArr ⁅lzX * lzX, lzY⁆ c2Arr := by
  rw [commutatorElement_def, mul_assoc (lzX * lzX * lzY), mul_inv_rev]
  exact hasArr_mul (hasArr_mul (hasArr_mul hasArr_lzX hasArr_lzX) hasArr_lzY)
    (hasArr_mul (hasArr_mul hasArr_lzXinv hasArr_lzXinv) hasArr_lzYinv)

theorem commutator_Lz : ⁅Lz, Lz⁆ = Lz := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact Lz.mul_mem (Lz.mul_mem (Lz.mul_mem ha hb) (Lz.inv_mem ha)) (Lz.inv_mem hb)) ?_
  have hc : ∀ p ∈ [⁅lzX, lzY⁆, ⁅lzX * lzX, lzY⁆], p ∈ ⁅Lz, Lz⁆ := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Subgroup.commutator_mem_commutator lzX_mem_Lz lzY_mem_Lz
    · exact Subgroup.commutator_mem_commutator (Lz.mul_mem lzX_mem_Lz lzX_mem_Lz) lzY_mem_Lz
  have hw := hasArr_wPerm (hasArr_getD₂ hasArr_c0 hasArr_c2)
  show Subgroup.closure ({lzX, lzY} : Set (Equiv.Perm (Fin 24))) ≤ ⁅Lz, Lz⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h := hw xWord
    rw [perfect_words.1] at h
    have hx := perm_eq_of_hasArr hasArr_lzX h
    exact hx ▸ wPerm_mem hc _
  · have h := hw yWord
    rw [perfect_words.2] at h
    have hy := perm_eq_of_hasArr hasArr_lzY h
    exact hy ▸ wPerm_mem hc _

@[expose] def ksP (c : Fin 64) : Equiv.Perm (Fin 24) :=
  permOfArr 24 (ksC c) (ksC c) (ksC_ok c c.2).1

theorem hasArr_ksP (c : Fin 64) : HasArr (ksP c) (ksC c) := hasArr_permOfArr _

theorem ksP_mul_self (c : Fin 64) : ksP c * ksP c = 1 := permOfArr_mul_self _

theorem ksP_injective : Function.Injective ksP := by
  intro c d h
  have hc := hasArr_ksP c
  have hd := hasArr_ksP d
  rw [h] at hc
  have e : ∀ i (hi : i < 24), (ksC c)[i]! = (ksC d)[i]! := fun i hi =>
    (hc ⟨i, hi⟩).symm.trans (hd ⟨i, hi⟩)
  have h1 : ksCoeff (ksC c) = ksCoeff (ksC d) := by
    unfold ksCoeff
    rw [e 8 (by norm_num), e 4 (by norm_num), e 0 (by norm_num)]
  rw [ksCoeff_ksC c c.2, ksCoeff_ksC d d.2] at h1
  exact Fin.ext h1

theorem ksPerm_eq (i : Fin 6) : ksPerm i = ksP ⟨2 ^ (i : ℕ), by
    have := i.2
    interval_cases (i : ℕ) <;> norm_num⟩ := by
  refine perm_eq_of_hasArr (hasArr_permOfArr (ksArr_ok i).1) ?_
  have h := hasArr_ksP ⟨2 ^ (i : ℕ), by have := i.2; interval_cases (i : ℕ) <;> norm_num⟩
  rwa [show ksC (2 ^ (i : ℕ)) = ksArr i from ksC_basis i i.2] at h

theorem ksPerm_mul_ksP (i : Fin 6) (c : Fin 64) :
    ksPerm i * ksP c = ksP ⟨c ^^^ 2 ^ (i : ℕ), Nat.xor_lt_two_pow (n := 6) c.2 (by
      have := i.2
      interval_cases (i : ℕ) <;> norm_num)⟩ := by
  refine perm_eq_of_hasArr (hasArr_mul (hasArr_permOfArr (ksArr_ok i).1) (hasArr_ksP c)) ?_
  rw [ksC_mul c c.2 i i.2]
  exact hasArr_ksP _

theorem ksP_zero : ksP 0 = 1 := by
  have h := ksPerm_mul_ksP 0 1
  have h1 : ksP 1 = ksPerm 0 := by
    rw [ksPerm_eq 0]
    rfl
  rw [h1, show ksPerm 0 * ksPerm 0 = 1 from permOfArr_mul_self _] at h
  rw [h]
  rfl

@[expose] def KSp : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure (Set.range ksPerm)

theorem ksPerm_mem_KSp (i : Fin 6) : ksPerm i ∈ KSp := Subgroup.subset_closure ⟨i, rfl⟩

theorem ksP_mem_KSp (c : Fin 64) : ksP c ∈ KSp := by
  have h := hasArr_wPerm (ps := (List.range 6).map fun i => if h : i < 6 then ksPerm ⟨i, h⟩ else 1)
    (gs := (List.range 6).map ksArr) (fun i => by
      by_cases hi : i < 6
      · rw [List.getD_eq_getElem _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_map, List.getElem_range, hi, ↓reduceDIte]
        exact hasArr_permOfArr _
      · rw [List.getD_eq_default _ _ (by simpa using hi),
          List.getD_eq_default _ _ (by simpa using hi)]
        exact hasArr_one) ((List.range 6).filter fun i => c.val.testBit i)
  rw [ksC_word c c.2] at h
  rw [perm_eq_of_hasArr (hasArr_ksP c) h]
  refine wPerm_mem (fun p hp => ?_) _
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  have hi' : i < 6 := List.mem_range.1 hi
  simp only [hi', ↓reduceDIte]
  exact ksPerm_mem_KSp _

theorem mem_KSp_iff {σ : Equiv.Perm (Fin 24)} : σ ∈ KSp ↔ ∃ c, ksP c = σ := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc ▸ ksP_mem_KSp c⟩
  induction h using Subgroup.closure_induction_left with
  | one => exact ⟨0, ksP_zero⟩
  | mul_left x hx y hy ih =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := ih
    exact ⟨_, (ksPerm_mul_ksP i c).symm⟩
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := ih
    rw [show (ksPerm i)⁻¹ = ksPerm i from inv_eq_of_mul_eq_one_right (permOfArr_mul_self _)]
    exact ⟨_, (ksPerm_mul_ksP i c).symm⟩

theorem card_KSp : Nat.card KSp = 64 := by
  have h : (KSp : Set (Equiv.Perm (Fin 24))) = Set.range ksP := by
    ext σ
    simp only [SetLike.mem_coe, mem_KSp_iff, Set.mem_range]
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective ksP_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ksP_mem_Lz (c : Fin 64) : ksP c ∈ Lz := by
  have h := hasArr_wPerm (hasArr_getD₂ hasArr_lzX hasArr_lzY) (ksWordC c)
  rw [ksWordC_ok c c.2] at h
  rw [perm_eq_of_hasArr (hasArr_ksP c) h]
  refine wPerm_mem (fun p hp => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact lzX_mem_Lz
  · exact lzY_mem_Lz

theorem KSp_le_Lz : KSp ≤ Lz := fun σ h => by
  obtain ⟨c, rfl⟩ := mem_KSp_iff.1 h
  exact ksP_mem_Lz c

theorem conj_ksP_x (c : Fin 64) :
    lzX * ksP c * lzX⁻¹ = ksP ⟨actM mxCols c, (actM_ks_lt c c.2).1⟩ := by
  have h : HasArr (lzX * ksP c * lzX⁻¹) (cArr lzXArr (cArr (ksC c) lzXInv)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_lzX (hasArr_mul (hasArr_ksP c) hasArr_lzXinv)
  rw [(ksC_conj c c.2).1] at h
  exact perm_eq_of_hasArr h (hasArr_ksP _)

theorem conj_ksP_y (c : Fin 64) :
    lzY * ksP c * lzY⁻¹ = ksP ⟨actM myCols c, (actM_ks_lt c c.2).2⟩ := by
  have h : HasArr (lzY * ksP c * lzY⁻¹) (cArr lzYArr (cArr (ksC c) lzYInv)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_lzY (hasArr_mul (hasArr_ksP c) hasArr_lzYinv)
  rw [(ksC_conj c c.2).2] at h
  exact perm_eq_of_hasArr h (hasArr_ksP _)

theorem Lz_le_normalizer_KSp : Lz ≤ Subgroup.normalizer (KSp : Set (Equiv.Perm (Fin 24))) := by
  rw [Lz, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> refine Subgroup.mem_normalizer_fintype fun k hk => ?_ <;>
    obtain ⟨c, rfl⟩ := mem_KSp_iff.1 hk
  · rw [conj_ksP_x]
    exact ksP_mem_KSp _
  · rw [conj_ksP_y]
    exact ksP_mem_KSp _

theorem isPGroup_KSp : IsPGroup 2 KSp := fun g => ⟨1, by
  obtain ⟨c, hc⟩ := mem_KSp_iff.1 g.2
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, ← hc, pow_two, ksP_mul_self, Subgroup.coe_one]⟩

theorem KSp_le_pCoreOf : KSp ≤ pCoreOf 2 Lz :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 KSp_le_Lz Lz_le_normalizer_KSp isPGroup_KSp

@[expose] def colOf (i : Fin 24) : Fin 6 := ⟨i / 4, by omega⟩

theorem colOf_surjective : Function.Surjective colOf := fun j =>
  ⟨⟨4 * j, by omega⟩, Fin.ext (by simp only [colOf]; omega)⟩

@[expose] def BP : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | ∃ π : Equiv.Perm (Fin 6), ∀ i, colOf (σ i) = π (colOf i)}
  mul_mem' := by
    rintro σ τ ⟨π, hπ⟩ ⟨π', hπ'⟩
    exact ⟨π * π', fun i => by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπ, hπ']⟩
  one_mem' := ⟨1, fun _ => rfl⟩
  inv_mem' := by
    rintro σ ⟨π, hπ⟩
    refine ⟨π⁻¹, fun i => ?_⟩
    have h := hπ (σ⁻¹ i)
    have e1 : σ (σ⁻¹ i) = i := by simp
    rw [e1] at h
    rw [h]
    simp

theorem col_unique {σ : Equiv.Perm (Fin 24)} {π π' : Equiv.Perm (Fin 6)}
    (h : ∀ i, colOf (σ i) = π (colOf i)) (h' : ∀ i, colOf (σ i) = π' (colOf i)) : π = π' :=
  Equiv.ext fun j => by
    obtain ⟨i, rfl⟩ := colOf_surjective j
    rw [← h, ← h']

@[expose] noncomputable def colHom : ↥BP →* Equiv.Perm (Fin 6) where
  toFun σ := Classical.choose σ.2
  map_one' := col_unique (Classical.choose_spec (1 : BP).2) fun _ => rfl
  map_mul' σ τ := col_unique (Classical.choose_spec (σ * τ).2) fun i => by
    show colOf ((σ : Equiv.Perm (Fin 24)) ((τ : Equiv.Perm (Fin 24)) i)) = _
    rw [Classical.choose_spec σ.2, Classical.choose_spec τ.2]
    rfl

theorem colHom_spec (σ : BP) (i : Fin 24) :
    colOf ((σ : Equiv.Perm (Fin 24)) i) = colHom σ (colOf i) :=
  Classical.choose_spec σ.2 i

theorem colHom_eq {σ : BP} {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, colOf ((σ : Equiv.Perm (Fin 24)) i) = π (colOf i)) : colHom σ = π :=
  col_unique (colHom_spec σ) h

@[expose] def colX : Equiv.Perm (Fin 6) := permOfArr 6 colXArr colXInv col_ok.1

@[expose] def colY : Equiv.Perm (Fin 6) := permOfArr 6 colYArr colYInv col_ok.2

theorem colOf_lzX (i : Fin 24) : colOf (lzX i) = colX (colOf i) := Fin.ext (by
  show (lzX i : ℕ) / 4 = (colX (colOf i) : ℕ)
  rw [hasArr_lzX i, colX, permOfArr_val]
  exact (lz_cols i i.2).1)

theorem colOf_lzY (i : Fin 24) : colOf (lzY i) = colY (colOf i) := Fin.ext (by
  show (lzY i : ℕ) / 4 = (colY (colOf i) : ℕ)
  rw [hasArr_lzY i, colY, permOfArr_val]
  exact (lz_cols i i.2).2)

theorem Lz_le_BP : Lz ≤ BP := by
  rw [Lz, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨colX, colOf_lzX⟩
  · exact ⟨colY, colOf_lzY⟩

@[expose] noncomputable def colLz : ↥Lz →* Equiv.Perm (Fin 6) :=
  colHom.comp (Subgroup.inclusion Lz_le_BP)

@[expose] def A6c : Subgroup (Equiv.Perm (Fin 6)) := Subgroup.closure {colX, colY}

theorem colLz_mem (σ : Equiv.Perm (Fin 24)) (hσ : σ ∈ Lz) : colLz ⟨σ, hσ⟩ ∈ A6c := by
  have hQ : Lz ≤ (A6c.comap colHom).map BP.subtype := by
    rw [Lz, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨⟨lzX, ⟨colX, colOf_lzX⟩⟩, ?_, rfl⟩
      show colHom _ ∈ A6c
      rw [colHom_eq colOf_lzX]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · refine ⟨⟨lzY, ⟨colY, colOf_lzY⟩⟩, ?_, rfl⟩
      show colHom _ ∈ A6c
      rw [colHom_eq colOf_lzY]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨τ, hτ, hτσ⟩ := hQ hσ
  have : (Subgroup.inclusion Lz_le_BP ⟨σ, hσ⟩ : BP) = τ := Subtype.ext hτσ.symm
  show colHom (Subgroup.inclusion Lz_le_BP ⟨σ, hσ⟩) ∈ A6c
  rw [this]
  exact hτ

theorem range_colLz : colLz.range = A6c := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    exact colLz_mem σ σ.2
  · rw [A6c, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨lzX, lzX_mem_Lz⟩, colHom_eq colOf_lzX⟩
    · exact ⟨⟨lzY, lzY_mem_Lz⟩, colHom_eq colOf_lzY⟩

section Order6

open CFSG.Sporadic.Th CFSG.Sporadic.Mathieu

theorem colX_mem_A6c : colX ∈ A6c := Subgroup.subset_closure (Set.mem_insert _ _)

theorem colY_mem_A6c : colY ∈ A6c := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem rep_colX : CFSG.Sporadic.Th.Rep 6 Native.a6colData.tA (⟨colX, colX_mem_A6c⟩ : A6c) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_colY : CFSG.Sporadic.Th.Rep 6 Native.a6colData.tB (⟨colY, colY_mem_A6c⟩ : A6c) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem card_A6c : Nat.card A6c = 360 := by
  have H : Hyp A6c Native.a6colData ⟨colX, colX_mem_A6c⟩ ⟨colY, colY_mem_A6c⟩ :=
    ⟨by norm_num, closure_pair_eq_top rfl _ _, rep_colX, rep_colY,
      Certificates.certificate7227.2⟩
  rw [card_eq H]
  rfl

end Order6

theorem A6c_eq : A6c = alternatingGroup (Fin 6) := by
  have hle : A6c ≤ alternatingGroup (Fin 6) := by
    rw [A6c, Subgroup.closure_le]
    rintro _ (rfl | rfl) <;> exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_A6c, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_ker_colLz : Nat.card colLz.ker = 192 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup colLz.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange colLz).toEquiv, range_colLz, card_A6c,
    card_Lz] at h
  omega

theorem pCoreOf_Lz : pCoreOf 2 Lz = KSp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Open.pCore 2 ↥Lz with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hker : N ≤ colLz.ker := by
    have hM : IsPGroup 2 (N.map colLz) := hNp.map colLz
    have hMA : N.map colLz ≤ alternatingGroup (Fin 6) := by
      rw [← A6c_eq, ← range_colLz]
      exact Subgroup.map_le_range _ _
    have hMn : ((N.map colLz).subgroupOf (alternatingGroup (Fin 6))).Normal := by
      constructor
      intro m hm a
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      obtain ⟨n, hn, hnm⟩ := hm
      have ha : (a : Equiv.Perm (Fin 6)) ∈ colLz.range := by
        rw [range_colLz, A6c_eq]
        exact a.2
      obtain ⟨l, hl⟩ := ha
      refine ⟨l * n * l⁻¹, hNn.conj_mem n hn l, ?_⟩
      rw [map_mul, map_mul, map_inv, hl, hnm]
      rfl
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N.map colLz).subgroupOf (alternatingGroup (Fin 6))) with h | h
    · intro n hn
      rw [MonoidHom.mem_ker]
      have hm : colLz n ∈ N.map colLz := ⟨n, hn, rfl⟩
      have hm' : (⟨colLz n, hMA hm⟩ : ↥(alternatingGroup (Fin 6))) ∈
          (N.map colLz).subgroupOf (alternatingGroup (Fin 6)) := Subgroup.mem_subgroupOf.2 hm
      rw [h, Subgroup.mem_bot] at hm'
      exact congrArg Subtype.val hm'
    · exfalso
      have hle : alternatingGroup (Fin 6) ≤ N.map colLz := by
        intro a ha
        have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin 6))) ∈
            (N.map colLz).subgroupOf (alternatingGroup (Fin 6)) := by rw [h]; trivial
        exact Subgroup.mem_subgroupOf.1 this
      have hAp : IsPGroup 2 (alternatingGroup (Fin 6)) := hM.to_le hle
      obtain ⟨k, hk⟩ := hAp.exists_card_eq
      rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hk
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk]
        decide
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)
  have hcard : Nat.card N ≤ 64 := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    have h1 : Nat.card N ∣ 192 := card_ker_colLz ▸ Subgroup.card_dvd_of_le hker
    rw [hk] at h1 ⊢
    have h2 : 2 ^ k ∣ 64 :=
      (Nat.Coprime.pow_left k (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_right
        (by simpa using h1)
    exact Nat.le_of_dvd (by norm_num) h2
  have hK : KSp.subgroupOf Lz ≤ N := by
    intro k hk
    have := KSp_le_pCoreOf (Subgroup.mem_subgroupOf.1 hk)
    obtain ⟨n, hn, hnk⟩ := this
    rwa [show n = k from Subtype.ext hnk] at hn
  have hKc : Nat.card (KSp.subgroupOf Lz) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe KSp_le_Lz).toEquiv, card_KSp]
  have hEq : KSp.subgroupOf Lz = N :=
    Subgroup.eq_of_le_of_card_ge hK (by rw [hKc]; exact hcard)
  rw [pCoreOf, ← hN, ← hEq, Subgroup.map_subgroupOf_eq_of_le KSp_le_Lz]

abbrev z0 : W11 := toW 11 31

theorem mem_centSub_zpowers {V : Type*} [CommGroup V] {g : MulAut V} {z : V} :
    g ∈ centSub (Subgroup.zpowers z) ↔ g z = z := by
  refine ⟨fun h => h z (Subgroup.mem_zpowers z), fun h u hu => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  rw [map_zpow, h]

theorem rho11_mem_img11 (σ : ↥AutPerm) : rho11 AutPerm le_rfl σ ∈ img11 AutPerm :=
  ⟨⟨σ, Subgroup.mem_subgroupOf.2 σ.2⟩, Subgroup.mem_subgroupOf.2 σ.2, rfl⟩

theorem orbTree_mem : ∀ e ∈ orbTree, ∃ h ∈ img11 AutPerm, h z0 = toW 11 e.1 := by
  have hP : ∀ g m, (∃ h ∈ img11 AutPerm, h z0 = toW 11 m) →
      ∃ h ∈ img11 AutPerm, h z0 = toW 11 (orbAct g m) := by
    rintro g m ⟨h, hh, hhz⟩
    by_cases hg : g = 0
    · refine ⟨rho11 AutPerm le_rfl ⟨bridgePA, bridgePA_mem⟩ * h,
        (img11 AutPerm).mul_mem (rho11_mem_img11 _) hh, ?_⟩
      rw [MulAut.mul_apply, hhz, rho11_toW AutPerm le_rfl ⟨bridgePA, bridgePA_mem⟩ hasArr_pA m,
        orbAct, ite_eq_left hg]
    · refine ⟨rho11 AutPerm le_rfl ⟨bridgePB, bridgePB_mem⟩ * h,
        (img11 AutPerm).mul_mem (rho11_mem_img11 _) hh, ?_⟩
      rw [MulAut.mul_apply, hhz, rho11_toW AutPerm le_rfl ⟨bridgePB, bridgePB_mem⟩ hasArr_pB m,
        orbAct, ite_eq_right hg]
  have hs : ∀ m, (1 <<< 31 : ℕ).testBit m = true → ∃ h ∈ img11 AutPerm, h z0 = toW 11 m := by
    intro m hm
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hm
    rw [← of_decide_eq_true hm]
    exact ⟨1, (img11 AutPerm).one_mem, rfl⟩
  exact (treeB_spec orbAct _ hP orbTree _ hs orbTree_ok).1

theorem le_card_orbit :
    1771 ≤ (MulAction.orbit ↥(img11 AutPerm) z0).ncard := by
  classical
  obtain ⟨-, hnd, hnot⟩ := treeB_spec orbAct (fun _ => True) (fun _ _ _ => trivial) orbTree _
    (fun _ _ => trivial) orbTree_ok
  set l : List ℕ := 31 :: orbTree.map Prod.fst with hl
  have hlnd : l.Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, hnd⟩
    obtain ⟨e, he, he31⟩ := List.mem_map.1 h
    have := hnot e he
    rw [he31, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    exact Bool.noConfusion this
  have hlt : ∀ m ∈ l, m < 2 ^ 11 := by
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · norm_num
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      exact orbTree_lt e he
  have hsub : ((l.map (toW 11)).toFinset : Set W11) ⊆ MulAction.orbit ↥(img11 AutPerm) z0 := by
    intro v hv
    simp only [List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    rcases List.mem_cons.1 hm with rfl | hm
    · exact MulAction.mem_orbit_self _
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      obtain ⟨h, hh, hhz⟩ := orbTree_mem e he
      exact ⟨⟨h, hh⟩, hhz⟩
  have hinj : (l.map (toW 11)).Nodup := by
    refine hlnd.map_on fun a ha b hb hab => toW_inj (hlt a ha) (hlt b hb) hab
  have hlen : (l.map (toW 11)).length = 1771 := by
    rw [List.length_map, hl, List.length_cons, List.length_map, orbTree_length]
  calc 1771 = ((l.map (toW 11)).toFinset : Set W11).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, hlen]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_img11_autPerm :
    Nat.card ↥(img11 AutPerm) = 244823040 := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_rfl).toEquiv, card_AutPerm]

theorem card_stab_le :
    Nat.card ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ≤ 138240 := by
  have e : ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ≃
      ↥(MulAction.stabilizer ↥(img11 AutPerm) z0) :=
    { toFun := fun y => ⟨⟨y, y.2.1⟩, mem_centSub_zpowers.1 y.2.2⟩
      invFun := fun y => ⟨y.1, y.1.2, mem_centSub_zpowers.2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(img11 AutPerm) z0)
  rw [MulAction.index_stabilizer, card_img11_autPerm, ← Nat.card_congr e] at h1
  have h2 := le_card_orbit
  by_contra hc
  push Not at hc
  have : 138241 * 1771 ≤ Nat.card ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) *
      (MulAction.orbit ↥(img11 AutPerm) z0).ncard := Nat.mul_le_mul hc h2
  omega

theorem img11_Lz_le_centSub : img11 Lz ≤ centSub (Subgroup.zpowers z0) := by
  have hQ : Lz ≤ ((centSub (Subgroup.zpowers z0)).comap (rho11 AutPerm le_rfl)).map
      AutPerm.subtype := by
    rw [Lz, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨⟨lzX, lzX_mem⟩, mem_centSub_zpowers.2 ?_, rfl⟩
      exact (rho11_toW AutPerm le_rfl ⟨lzX, lzX_mem⟩ hasArr_lzX 31).trans
        (congrArg (toW 11) lz_fix.1)
    · refine ⟨⟨lzY, lzY_mem⟩, mem_centSub_zpowers.2 ?_, rfl⟩
      exact (rho11_toW AutPerm le_rfl ⟨lzY, lzY_mem⟩ hasArr_lzY 31).trans
        (congrArg (toW 11) lz_fix.2)
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hτσ⟩ := hQ (Subgroup.mem_subgroupOf.1 hσ)
  rw [show σ = τ from Subtype.ext hτσ.symm]
  exact hτ

theorem img11_Lz_le_stab : img11 Lz ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) :=
  le_inf (Subgroup.map_mono fun σ _ => Subgroup.mem_subgroupOf.2 σ.2) img11_Lz_le_centSub

theorem card_img11_Lz :
    Nat.card ↥(img11 Lz) = 69120 := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lz_le).toEquiv, card_Lz]

theorem commutator_img11_Lz : ⁅img11 Lz, img11 Lz⁆ = img11 Lz := by
  have h : ⁅Lz.subgroupOf AutPerm, Lz.subgroupOf AutPerm⁆ = Lz.subgroupOf AutPerm := by
    apply Subgroup.map_injective AutPerm.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le Lz_le, commutator_Lz]
  rw [img11, ← Subgroup.map_commutator, h]

theorem commutator_le_of_card_two_mul {G : Type*} [Group G] [Finite G] {A Y : Subgroup G}
    (hAY : A ≤ Y) (hc : Nat.card Y = 2 * Nat.card A) : ⁅Y, Y⁆ ≤ A := by
  have hi : (A.subgroupOf Y).index = 2 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hc] at h1
    have hA : 0 < Nat.card A := Nat.card_pos
    nlinarith
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have key : ⁅(⟨a, ha⟩ : Y), ⟨b, hb⟩⁆ ∈ A.subgroupOf Y := by
    rw [commutatorElement_def, mul_assoc, Subgroup.mul_mem_iff_of_index_two hi,
      Subgroup.mul_mem_iff_of_index_two hi, Subgroup.mul_mem_iff_of_index_two hi,
      Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  exact Subgroup.mem_subgroupOf.1 key

theorem perfectCore_stab :
    perfectCore (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) = img11 Lz := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  set Y := img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) with hY
  have hdvd : Nat.card ↥(img11 Lz) ∣ Nat.card Y := Subgroup.card_dvd_of_le img11_Lz_le_stab
  have hle : Nat.card Y ≤ 138240 := card_stab_le
  rw [card_img11_Lz] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k = 1 ∨ k = 2 := by
    have hpos : 0 < Nat.card Y := Nat.card_pos
    rcases k with _ | _ | _ | k
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  refine le_antisymm ?_ (le_perfectCore_of_perfect img11_Lz_le_stab commutator_img11_Lz)
  rcases hk2 with rfl | rfl
  · have hEq : img11 Lz = Y :=
      Subgroup.eq_of_le_of_card_ge img11_Lz_le_stab (by rw [card_img11_Lz, hk])
    rw [← hEq, perfectCore_eq_self_of_perfect commutator_img11_Lz]
  · refine (perfectCore_le_derivedSeriesOf Y 1).trans ?_
    rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
    exact commutator_le_of_card_two_mul img11_Lz_le_stab (by rw [hk, card_img11_Lz])

end CFSG.Quasithin.H.Coc24
