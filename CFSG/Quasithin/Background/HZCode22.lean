module

public import CFSG.Quasithin.Background.HZCode22Gen
public import CFSG.Quasithin.Background.HZCoc24
public import CFSG.Quasithin.Background.H16TwoM22PfA
public import Certificates.Certificate7228

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.Mathieu.H16Pf
open scoped commutatorElement

@[expose] def lX : Equiv.Perm (Fin 24) := permOfArr 24 lxArr lxInv l_ok.1

@[expose] def lY : Equiv.Perm (Fin 24) := permOfArr 24 lyArr lyInv l_ok.2.1

theorem hasArr_lX : HasArr lX lxArr := hasArr_permOfArr _

theorem hasArr_lXinv : HasArr lX⁻¹ lxInv := hasArr_permOfArr_inv _

theorem hasArr_lY : HasArr lY lyArr := hasArr_permOfArr _

theorem hasArr_lYinv : HasArr lY⁻¹ lyInv := hasArr_permOfArr_inv _

theorem lX_mem : lX ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ l_ok.2.2.1) hasArr_lX l_ok.2.2.2.2.1
    l_ok.2.2.2.2.2.1

theorem lY_mem : lY ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ l_ok.2.2.2.1) hasArr_lY l_ok.2.2.2.2.2.2.1
    l_ok.2.2.2.2.2.2.2

@[expose] def L22 : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {lX, lY}

theorem lX_mem_L22 : lX ∈ L22 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem lY_mem_L22 : lY ∈ L22 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem L22_le : L22 ≤ mog22 := by
  rw [L22, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact lX_mem
  · exact lY_mem

section Order

open CFSG.Sporadic.Th CFSG.Sporadic.Mathieu

theorem rep_lX : CFSG.Sporadic.Th.Rep 24 Native.l22Data.tA (⟨lX, lX_mem_L22⟩ : L22) := by
  have h : (List.range 24).all (fun i => CFSG.Sporadic.Th.Native.ap Native.l22Data.tA i ==
      lxArr[i]!) = true := by decide +kernel
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]
  exact (hasArr_lX ⟨i, hi⟩).symm

theorem rep_lY : CFSG.Sporadic.Th.Rep 24 Native.l22Data.tB (⟨lY, lY_mem_L22⟩ : L22) := by
  have h : (List.range 24).all (fun i => CFSG.Sporadic.Th.Native.ap Native.l22Data.tB i ==
      lyArr[i]!) = true := by decide +kernel
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]
  exact (hasArr_lY ⟨i, hi⟩).symm

theorem card_L22 : Nat.card L22 = 5760 := by
  have H : Hyp L22 Native.l22Data ⟨lX, lX_mem_L22⟩ ⟨lY, lY_mem_L22⟩ :=
    ⟨by norm_num, closure_pair_eq_top rfl _ _, rep_lX, rep_lY,
      Certificates.certificate7228⟩
  rw [card_eq H]
  rfl

end Order

theorem hasArr_c0 : HasArr ⁅lX, lY⁆ c0Arr := by
  rw [commutatorElement_def, mul_assoc (lX * lY)]
  exact hasArr_mul (hasArr_mul hasArr_lX hasArr_lY) (hasArr_mul hasArr_lXinv hasArr_lYinv)

theorem hasArr_c2 : HasArr ⁅lX * lX, lY⁆ c2Arr := by
  rw [commutatorElement_def, mul_assoc (lX * lX * lY), mul_inv_rev]
  exact hasArr_mul (hasArr_mul (hasArr_mul hasArr_lX hasArr_lX) hasArr_lY)
    (hasArr_mul (hasArr_mul hasArr_lXinv hasArr_lXinv) hasArr_lYinv)

theorem commutator_L22 : ⁅L22, L22⁆ = L22 := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact L22.mul_mem (L22.mul_mem (L22.mul_mem ha hb) (L22.inv_mem ha)) (L22.inv_mem hb)) ?_
  have hc : ∀ p ∈ [⁅lX, lY⁆, ⁅lX * lX, lY⁆], p ∈ ⁅L22, L22⁆ := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Subgroup.commutator_mem_commutator lX_mem_L22 lY_mem_L22
    · exact Subgroup.commutator_mem_commutator (L22.mul_mem lX_mem_L22 lX_mem_L22) lY_mem_L22
  have hw := hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_c0 hasArr_c2)
  show Subgroup.closure ({lX, lY} : Set (Equiv.Perm (Fin 24))) ≤ ⁅L22, L22⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h := hw xWord
    rw [perfect_words.1] at h
    have hx := perm_eq_of_hasArr hasArr_lX h
    exact hx ▸ wPerm_mem hc _
  · have h := hw yWord
    rw [perfect_words.2] at h
    have hy := perm_eq_of_hasArr hasArr_lY h
    exact hy ▸ wPerm_mem hc _

theorem hasArr_koPerm (t : Fin 16) : HasArr (koPerm t) (koArr t) := hasArr_permOfArr _

theorem koPerm_injective : Function.Injective koPerm := fun s t h => by
  have hs := koPerm_eight s
  rw [h, koPerm_eight t] at hs
  exact Fin.ext (by omega)

theorem card_fixO : Nat.card fixO = 16 := by
  have h : (fixO : Set (Equiv.Perm (Fin 24))) = Set.range koPerm := by
    ext σ
    simp only [SetLike.mem_coe, mem_fixO_iff, Set.mem_range]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective koPerm_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem koPerm_mem_L22 (t : Fin 16) : koPerm t ∈ L22 := by
  have h := hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_lX hasArr_lY) (koWord t)
  rw [koWord_ok t t.2] at h
  rw [perm_eq_of_hasArr (hasArr_koPerm t) h]
  refine wPerm_mem (fun p hp => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact lX_mem_L22
  · exact lY_mem_L22

theorem fixO_le_L22 : fixO ≤ L22 := fun σ h => by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff σ).1 h
  exact koPerm_mem_L22 t

theorem lX_oct (i : Fin 24) : ((lX i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
  rw [hasArr_lX i]
  exact (l_oct i i.2).1

theorem lY_oct (i : Fin 24) : ((lY i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
  rw [hasArr_lY i]
  exact (l_oct i i.2).2

theorem L22_le_normalizer_fixO :
    L22 ≤ Subgroup.normalizer (fixO : Set (Equiv.Perm (Fin 24))) := by
  rw [L22, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact mem_normalizer_fixO lX_mem.1.1 lX_oct
  · exact mem_normalizer_fixO lY_mem.1.1 lY_oct

theorem fixO_le_pCoreOf : fixO ≤ pCoreOf 2 L22 :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 fixO_le_L22 L22_le_normalizer_fixO
    isPGroup_fixO

@[expose] def hx (i : Fin 6) : Fin 24 := ⟨i + 2, by omega⟩

theorem hx_injective : Function.Injective hx := fun i j h => Fin.ext (by
  have := congrArg Fin.val h
  simp only [hx] at this
  omega)

@[expose] def HXP : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | ∃ π : Equiv.Perm (Fin 6), ∀ i, σ (hx i) = hx (π i)}
  mul_mem' := by
    rintro σ τ ⟨π, hπ⟩ ⟨π', hπ'⟩
    exact ⟨π * π', fun i => by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπ', hπ]⟩
  one_mem' := ⟨1, fun _ => rfl⟩
  inv_mem' := by
    rintro σ ⟨π, hπ⟩
    refine ⟨π⁻¹, fun i => ?_⟩
    have h := hπ (π⁻¹ i)
    have e1 : π (π⁻¹ i) = i := by simp
    rw [e1] at h
    rw [← h]
    simp

theorem hex_unique {σ : Equiv.Perm (Fin 24)} {π π' : Equiv.Perm (Fin 6)}
    (h : ∀ i, σ (hx i) = hx (π i)) (h' : ∀ i, σ (hx i) = hx (π' i)) : π = π' :=
  Equiv.ext fun i => hx_injective ((h i).symm.trans (h' i))

@[expose] noncomputable def hexHom : ↥HXP →* Equiv.Perm (Fin 6) where
  toFun σ := Classical.choose σ.2
  map_one' := hex_unique (Classical.choose_spec (1 : HXP).2) fun _ => rfl
  map_mul' σ τ := hex_unique (Classical.choose_spec (σ * τ).2) fun i => by
    show (σ : Equiv.Perm (Fin 24)) ((τ : Equiv.Perm (Fin 24)) (hx i)) = _
    rw [Classical.choose_spec τ.2, Classical.choose_spec σ.2]
    rfl

theorem hexHom_spec (σ : HXP) (i : Fin 6) :
    (σ : Equiv.Perm (Fin 24)) (hx i) = hx (hexHom σ i) :=
  Classical.choose_spec σ.2 i

theorem hexHom_eq {σ : HXP} {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, (σ : Equiv.Perm (Fin 24)) (hx i) = hx (π i)) : hexHom σ = π :=
  hex_unique (hexHom_spec σ) h

theorem hx_lX (i : Fin 6) : lX (hx i) = hx (Coc24.colX i) := Fin.ext (by
  show (lX (hx i) : ℕ) = (Coc24.colX i : ℕ) + 2
  rw [hasArr_lX (hx i), Coc24.colX, permOfArr_val]
  exact (l_hex i i.2).1)

theorem hx_lY (i : Fin 6) : lY (hx i) = hx (Coc24.colY i) := Fin.ext (by
  show (lY (hx i) : ℕ) = (Coc24.colY i : ℕ) + 2
  rw [hasArr_lY (hx i), Coc24.colY, permOfArr_val]
  exact (l_hex i i.2).2)

theorem L22_le_HXP : L22 ≤ HXP := by
  rw [L22, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨Coc24.colX, hx_lX⟩
  · exact ⟨Coc24.colY, hx_lY⟩

@[expose] noncomputable def hexL22 : ↥L22 →* Equiv.Perm (Fin 6) :=
  hexHom.comp (Subgroup.inclusion L22_le_HXP)

theorem hexL22_mem (σ : Equiv.Perm (Fin 24)) (hσ : σ ∈ L22) : hexL22 ⟨σ, hσ⟩ ∈ Coc24.A6c := by
  have hQ : L22 ≤ (Coc24.A6c.comap hexHom).map HXP.subtype := by
    rw [L22, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨⟨lX, ⟨Coc24.colX, hx_lX⟩⟩, ?_, rfl⟩
      show hexHom _ ∈ Coc24.A6c
      rw [hexHom_eq hx_lX]
      exact Coc24.colX_mem_A6c
    · refine ⟨⟨lY, ⟨Coc24.colY, hx_lY⟩⟩, ?_, rfl⟩
      show hexHom _ ∈ Coc24.A6c
      rw [hexHom_eq hx_lY]
      exact Coc24.colY_mem_A6c
  obtain ⟨τ, hτ, hτσ⟩ := hQ hσ
  have : (Subgroup.inclusion L22_le_HXP ⟨σ, hσ⟩ : HXP) = τ := Subtype.ext hτσ.symm
  show hexHom (Subgroup.inclusion L22_le_HXP ⟨σ, hσ⟩) ∈ Coc24.A6c
  rw [this]
  exact hτ

theorem range_hexL22 : hexL22.range = Coc24.A6c := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    exact hexL22_mem σ σ.2
  · rw [Coc24.A6c, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨lX, lX_mem_L22⟩, hexHom_eq hx_lX⟩
    · exact ⟨⟨lY, lY_mem_L22⟩, hexHom_eq hx_lY⟩

theorem card_ker_hexL22 :
    Nat.card hexL22.ker = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup hexL22.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange hexL22).toEquiv, range_hexL22,
    Coc24.card_A6c, card_L22] at h
  omega

theorem fixO_subgroupOf_le_ker : fixO.subgroupOf L22 ≤ hexL22.ker := by
  intro σ hσ
  obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hσ)
  rw [MonoidHom.mem_ker]
  show hexHom (Subgroup.inclusion L22_le_HXP σ) = 1
  refine hexHom_eq fun i => ?_
  show (σ : Equiv.Perm (Fin 24)) (hx i) = hx i
  rw [ht]
  exact koPerm_apply_of_lt t (hx i) (by simp only [hx]; omega)

theorem ker_hexL22 :
    hexL22.ker = fixO.subgroupOf L22 := by
  refine (Subgroup.eq_of_le_of_card_ge fixO_subgroupOf_le_ker ?_).symm
  rw [card_ker_hexL22, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_L22).toEquiv,
    card_fixO]

theorem pCore_le_ker_of_range_eq {G : Type*} [Group G] [Finite G] (f : G →* Equiv.Perm (Fin 6))
    (hf : f.range = alternatingGroup (Fin 6)) : CFSG.Open.pCore 2 G ≤ f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Open.pCore 2 G with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hM : IsPGroup 2 (N.map f) := hNp.map f
  have hMA : N.map f ≤ alternatingGroup (Fin 6) := by
    rw [← hf]
    exact Subgroup.map_le_range _ _
  have hMn : ((N.map f).subgroupOf (alternatingGroup (Fin 6))).Normal := by
    constructor
    intro m hm a
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨n, hn, hnm⟩ := hm
    have ha : (a : Equiv.Perm (Fin 6)) ∈ f.range := by
      rw [hf]
      exact a.2
    obtain ⟨l, hl⟩ := ha
    refine ⟨l * n * l⁻¹, hNn.conj_mem n hn l, ?_⟩
    rw [map_mul, map_mul, map_inv, hl, hnm]
    rfl
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N.map f).subgroupOf (alternatingGroup (Fin 6))) with h | h
  · intro n hn
    rw [MonoidHom.mem_ker]
    have hm : f n ∈ N.map f := ⟨n, hn, rfl⟩
    have hm' : (⟨f n, hMA hm⟩ : ↥(alternatingGroup (Fin 6))) ∈
        (N.map f).subgroupOf (alternatingGroup (Fin 6)) := Subgroup.mem_subgroupOf.2 hm
    rw [h, Subgroup.mem_bot] at hm'
    exact congrArg Subtype.val hm'
  · exfalso
    have hle : alternatingGroup (Fin 6) ≤ N.map f := by
      intro a ha
      have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin 6))) ∈
          (N.map f).subgroupOf (alternatingGroup (Fin 6)) := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    have hAp : IsPGroup 2 (alternatingGroup (Fin 6)) := hM.to_le hle
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hk
    have h3 : 3 ∣ 2 ^ k := by
      rw [← hk]
      decide
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)

theorem pCoreOf_L22 :
    pCoreOf 2 L22 = fixO := by
  set N := CFSG.Open.pCore 2 ↥L22 with hN
  have hker : N ≤ fixO.subgroupOf L22 := by
    rw [← ker_hexL22]
    exact pCore_le_ker_of_range_eq hexL22 (range_hexL22.trans Coc24.A6c_eq)
  have hK : fixO.subgroupOf L22 ≤ N := by
    intro k hk
    obtain ⟨n, hn, hnk⟩ := fixO_le_pCoreOf (Subgroup.mem_subgroupOf.1 hk)
    rwa [show n = k from Subtype.ext hnk] at hn
  rw [pCoreOf, ← hN, le_antisymm hker hK, Subgroup.map_subgroupOf_eq_of_le fixO_le_L22]

end CFSG.Quasithin.H.Code22
