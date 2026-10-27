module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsRee
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits CFSG.LieType.Simplicity.TitsBits.Letter

namespace TableBF4TwoInputs

section Bits

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [CharP K 2]

theorem hasBits_pinnedX {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) {a : ℕ}
    (ha : a < ReeTag.F4.tag.rootCertificate.roots.length)
    (hroot : ReeTag.F4.tag.rootCertificate.root a = β) :
    HasBits K ⟨pinnedX ReeTag.F4.tag K β 1, pinnedX_mem_adjointGroup β 1⟩ (pack (eltBits a)) := by
  have h1 := hasBits_eltElement (K := K) ⟨β, hβ⟩
  rw [RootOps.rootPos_eq ha hroot] at h1
  have hs : ((rootOperatorFamily ReeTag.F4.tag).pinnedFamilySign β : K) * 1 = 1 := by
    rw [mul_one]
    rcases (rootOperatorFamily ReeTag.F4.tag).pinnedFamilySign_eq β with h | h <;> rw [h]
    · simp
    · simp [CharTwo.neg_eq]
  have h2 : (rootOperatorFamily ReeTag.F4.tag).eltElement ⟨β, hβ⟩ 1 =
      ⟨pinnedX ReeTag.F4.tag K β 1, pinnedX_mem_adjointGroup β 1⟩ := by
    apply Subtype.ext
    change (rootOperatorFamily ReeTag.F4.tag).eltUnit K ⟨β, hβ⟩ 1 = pinnedX ReeTag.F4.tag K β 1
    rw [(rootOperatorFamily ReeTag.F4.tag).pinnedX_eq_eltUnit K hβ, hs]
  rwa [h2] at h1

omit [CharP K 2] in
theorem isRoot_orthRoot' (i : Fin 4) : IsRoot ReeTag.F4.tag (TableBF4Two.orthRoot i) :=
  TableBF4Two.isRoot_orthRoot i

@[expose] def posP : Fin 4 → ℕ := ![1, 7, 15, 43]

@[expose] def posN : Fin 4 → ℕ := ![6, 14, 23, 46]

omit [CharP K 2] in
theorem posP_spec : ∀ i : Fin 4, posP i < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (posP i) = TableBF4Two.orthRoot i := by
  decide +kernel

omit [CharP K 2] in
theorem posN_spec : ∀ i : Fin 4, posN i < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (posN i) = -TableBF4Two.orthRoot i := by
  decide +kernel

theorem hasBits_rho (i : Fin 4) :
    HasBits K (TableBF4Two.rho K i (uSL 1 * vSL 1))
      (mul (pack (eltBits (posP i))) (pack (eltBits (posN i)))) := by
  have hβ := isRoot_orthRoot' i
  have hβ' : IsRoot ReeTag.F4.tag (-TableBF4Two.orthRoot i) := CFSG.LieType.Chevalley.IsRoot.neg hβ
  obtain ⟨-, -, -, hx, -⟩ := CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .F4 K hβ
  have e : TableBF4Two.rho K i (uSL 1 * vSL 1) =
      ⟨pinnedX ReeTag.F4.tag K (TableBF4Two.orthRoot i) 1, pinnedX_mem_adjointGroup _ 1⟩ *
        ⟨pinnedX ReeTag.F4.tag K (-TableBF4Two.orthRoot i) 1, pinnedX_mem_adjointGroup _ 1⟩ := by
    apply Subtype.ext
    rw [TableBF4Two.coe_rho, map_mul, (hx 1).1, (hx 1).2]
    rfl
  rw [e]
  exact (hasBits_pinnedX hβ (posP_spec i).1 (posP_spec i).2).mul
    (hasBits_pinnedX hβ' (posN_spec i).1 (posN_spec i).2)

@[expose] def cWord : List Letter := [n 3, n 2]

@[expose] def nWord : List Letter := [n 0, n 1, n 2, n 3, n 1, n 2, n 0]

theorem conj_eq_of_bits {x y : adjointGroup ReeTag.F4.tag K} (w : List Letter) {A B : ℕ}
    (hx : HasBits K x A) (hy : HasBits K y B)
    (h : mul (mul (evalB w) A) (evalB w.reverse) % 2 ^ 2704 = B % 2 ^ 2704) :
    evalG K w * x * (evalG K w)⁻¹ = y := by
  rw [evalG_inv]
  exact ((((hasBits_evalG w).mul hx).mul (hasBits_evalG w.reverse)).eq_iff hy).2 h

variable (K) in
@[expose] noncomputable def cElt : adjointGroup .F4 K := evalG K cWord

variable (K) in
@[expose] noncomputable def nElt : adjointGroup .F4 K := evalG K nWord

theorem cElt_pow_three : cElt K ^ 3 = 1 := by
  have h : evalG K cWord ^ 3 = 1 := by
    rw [evalG_pow_three]
    exact evalG_eq_one_of_evalB (by decide +kernel)
  exact h

theorem cWord_conj_rho_zero :
    cElt K * TableBF4Two.rho K 0 (uSL 1 * vSL 1) * (cElt K)⁻¹ =
      TableBF4Two.rho K 2 (uSL 1 * vSL 1) :=
  conj_eq_of_bits cWord (hasBits_rho 0) (hasBits_rho 2) (by decide +kernel)

theorem cWord_conj_rho_two :
    cElt K * TableBF4Two.rho K 2 (uSL 1 * vSL 1) * (cElt K)⁻¹ =
      TableBF4Two.rho K 1 (uSL 1 * vSL 1) :=
  conj_eq_of_bits cWord (hasBits_rho 2) (hasBits_rho 1) (by decide +kernel)

theorem cWord_conj_rho_one :
    cElt K * TableBF4Two.rho K 1 (uSL 1 * vSL 1) * (cElt K)⁻¹ =
      TableBF4Two.rho K 0 (uSL 1 * vSL 1) :=
  conj_eq_of_bits cWord (hasBits_rho 1) (hasBits_rho 0) (by decide +kernel)

theorem nWord_conj_rho_zero :
    nElt K * TableBF4Two.rho K 0 (uSL 1 * vSL 1) * (nElt K)⁻¹ =
      TableBF4Two.rho K 3 (uSL 1 * vSL 1) :=
  conj_eq_of_bits nWord (hasBits_rho 0) (hasBits_rho 3) (by decide +kernel)

end Bits

section Levi

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem orthRoot_mem_c3LeviRoots (i : Fin 3) :
    TableBF4Two.orthRoot i.castSucc ∈ c3LeviRoots ∧
      -TableBF4Two.orthRoot i.castSucc ∈ c3LeviRoots := by
  have h1 := TableBF4Two.isRoot_orthRoot i.castSucc
  refine ⟨⟨h1, ?_⟩, ⟨CFSG.LieType.Chevalley.IsRoot.neg h1, ?_⟩⟩ <;> fin_cases i <;> decide

theorem rho_mem_C3Levi (i : Fin 3) (A : SL2 K) : TableBF4Two.rho K i.castSucc A ∈ C3Levi K := by
  rw [mem_C3Levi_iff, TableBF4Two.coe_rho]
  have hβ := TableBF4Two.isRoot_orthRoot i.castSucc
  have hA : rootSL2 .F4 K (TableBF4Two.orthRoot i.castSucc) A ∈
      (rootSL2 .F4 K (TableBF4Two.orthRoot i.castSucc)).range := ⟨A, rfl⟩
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ] at hA
  have hle : rootSubgroup .F4 K (TableBF4Two.orthRoot i.castSucc) ⊔
      rootSubgroup .F4 K (-TableBF4Two.orthRoot i.castSucc) ≤ rootSpan .F4 K c3LeviRoots :=
    sup_le (le_iSup₂_of_le (f := fun α (_ : α ∈ c3LeviRoots) => rootSubgroup .F4 K α) _
      (orthRoot_mem_c3LeviRoots i).1 le_rfl)
      (le_iSup₂_of_le (f := fun α (_ : α ∈ c3LeviRoots) => rootSubgroup .F4 K α) _
        (orthRoot_mem_c3LeviRoots i).2 le_rfl)
  exact hle hA

theorem weylElement_mem_C3Levi (i : Fin (Tag.rank .F4)) (hi : i.val ≠ 0) :
    weylElement .F4 K i ∈ C3Levi K := by
  rw [mem_C3Levi_iff]
  change weylElt .F4 K i 1 ∈ rootSpan .F4 K c3LeviRoots
  have h1 : (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ c3LeviRoots := by
    refine ⟨IsRoot.basis _, ?_⟩
    fin_cases i
    · exact absurd rfl hi
    all_goals decide
  have h2 : -(Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ c3LeviRoots :=
    ⟨CFSG.LieType.Chevalley.IsRoot.neg h1.1, by rw [Pi.neg_apply, h1.2, neg_zero]⟩
  have hx : ∀ c : K, xUnit .F4 K i c ∈ rootSpan .F4 K c3LeviRoots := fun c => by
    rw [← pinnedX_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ c3LeviRoots) => rootSubgroup .F4 K α) _ h1 le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  have hy : ∀ c : K, yUnit .F4 K i c ∈ rootSpan .F4 K c3LeviRoots := fun c => by
    rw [← pinnedX_neg_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ c3LeviRoots) => rootSubgroup .F4 K α) _ h2 le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem cElt_mem_C3Levi : cElt K ∈ C3Levi K := by
  have h3 := weylElement_mem_C3Levi (K := K) ⟨3, by decide⟩ (by decide)
  have h2 := weylElement_mem_C3Levi (K := K) ⟨2, by decide⟩ (by decide)
  have e : cElt K = weylElement .F4 K ⟨3, by decide⟩ * weylElement .F4 K ⟨2, by decide⟩ := by
    change evalG K [n 3, n 2] = _
    rw [evalG_cons, evalG_cons, evalG_nil, mul_one]
    rfl
  rw [e]
  exact mul_mem h3 h2

theorem range_torus3_le_C3Levi : (TableBF4Two.torus3 K).range ≤ C3Levi K := by
  rw [TableBF4Two.torus3, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun i => ?_
  rintro _ ⟨a, rfl⟩
  rw [TableBF4Two.torusCoord_apply]
  exact rho_mem_C3Levi i _

theorem card_range_torus3 : Nat.card (TableBF4Two.torus3 K).range = 3 ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective TableBF4Two.torus3_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_multiplicative, ZMod.card,
    Fintype.card_fin]

theorem card_C3Levi_two [Finite K] (hK : Nat.card K = 2) : Nat.card (C3Levi K) = 1451520 := by
  rw [← Nat.card_congr (c3LeviEquiv K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
  decide

end Levi

@[expose] def shift : (Fin 3 → Multiplicative (ZMod 3)) →* (Fin 3 → Multiplicative (ZMod 3)) where
  toFun f := fun k => f (![1, 2, 0] k)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem shift_mulSingle (j : Fin 3) (a : Multiplicative (ZMod 3)) :
    shift (Pi.mulSingle j a) = Pi.mulSingle (![2, 0, 1] j) a := by
  funext k
  fin_cases j <;> fin_cases k <;> simp [shift]

theorem shift_iterate_three (f : Fin 3 → Multiplicative (ZMod 3)) : shift^[3] f = f := by
  funext k
  fin_cases k <;> rfl

theorem const_eq_pow (a : Multiplicative (ZMod 3)) :
    (fun _ : Fin 3 => a) =
      (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd a).val := by
  revert a
  decide

theorem const_pow_three : (fun _ : Fin 3 => Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by
  decide

theorem eq_const_of_shift (f : Fin 3 → Multiplicative (ZMod 3))
    (h : shift f = f ∨ shift (shift f) = f) :
    f = fun _ => f 0 := by
  revert f
  decide

section Sylow

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [CharP K 2]

theorem cElt_conj_torusGen (j : Fin 3) :
    cElt K * TableBF4Two.torusGen K j * (cElt K)⁻¹ = TableBF4Two.torusGen K (![2, 0, 1] j) := by
  fin_cases j
  · exact cWord_conj_rho_zero
  · exact cWord_conj_rho_one
  · exact cWord_conj_rho_two

theorem cElt_conj_torus3 (f : Fin 3 → Multiplicative (ZMod 3)) :
    cElt K * TableBF4Two.torus3 K f * (cElt K)⁻¹ = TableBF4Two.torus3 K (shift f) := by
  have h : (MulAut.conj (cElt K)).toMonoidHom.comp (TableBF4Two.torus3 K) =
      (TableBF4Two.torus3 K).comp shift := MonoidHom.pi_ext fun j a => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      TableBF4Two.torus3, MonoidHom.noncommPiCoprod_mulSingle, shift_mulSingle]
    rw [TableBF4Two.torusCoord, TableBF4Two.torusCoord, TableBSymp.zmodPowHom_apply,
      TableBSymp.zmodPowHom_apply, ← conj_pow, cElt_conj_torusGen]
  have h1 := congrArg (fun φ => φ f) h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1

theorem cElt_pow_conj_torus3 (k : ℕ) (f : Fin 3 → Multiplicative (ZMod 3)) :
    cElt K ^ k * TableBF4Two.torus3 K f * (cElt K ^ k)⁻¹ = TableBF4Two.torus3 K (shift^[k] f) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← cElt_conj_torus3, ← ih, pow_succ', mul_inv_rev]
    group

theorem cElt_mem_normalizer :
    cElt K ∈ Subgroup.normalizer ((TableBF4Two.torus3 K).range : Set (adjointGroup .F4 K)) := by
  have hc2 : (cElt K)⁻¹ = cElt K ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', cElt_pow_three])
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨shift f, (cElt_conj_torus3 f).symm⟩
  · rintro ⟨f, hf⟩
    refine ⟨shift^[2] f, ?_⟩
    rw [← cElt_pow_conj_torus3, ← hc2, hf, inv_inv]
    group

theorem torusGen_eq_torus3 (j : Fin 3) :
    TableBF4Two.torusGen K j = TableBF4Two.torus3 K (Pi.mulSingle j (Multiplicative.ofAdd 1)) := by
  rw [TableBF4Two.torus3, MonoidHom.noncommPiCoprod_mulSingle, TableBF4Two.torusCoord,
    TableBSymp.zmodPowHom_apply, toAdd_ofAdd, show (1 : ZMod 3).val = 1 from rfl, pow_one]

theorem cElt_not_mem_range : cElt K ∉ (TableBF4Two.torus3 K).range := by
  rintro ⟨f, hf⟩
  have h1 := cElt_conj_torusGen (K := K) 0
  rw [← hf, torusGen_eq_torus3, torusGen_eq_torus3, ← map_mul, ← map_inv, ← map_mul,
    mul_comm f, mul_assoc, mul_inv_cancel, mul_one] at h1
  exact absurd (TableBF4Two.torus3_injective h1) (by decide)

variable (K) in
@[expose] noncomputable def sylT : Subgroup (adjointGroup .F4 K) :=
  (TableBF4Two.torus3 K).range ⊔ Subgroup.zpowers (cElt K)

theorem isPGroup_range_torus3 : IsPGroup 3 (TableBF4Two.torus3 K).range :=
  IsPGroup.of_card card_range_torus3

theorem isPGroup_sylT : IsPGroup 3 (sylT K) :=
  IsPGroup.to_sup_of_normal_left' isPGroup_range_torus3
    (isPGroup_zpowers_of_pow_three cElt_pow_three) (Subgroup.zpowers_le.2 cElt_mem_normalizer)

theorem sylT_le_C3Levi : sylT K ≤ C3Levi K :=
  sup_le range_torus3_le_C3Levi (Subgroup.zpowers_le.2 cElt_mem_C3Levi)

theorem card_sylT [Finite K] (hK : Nat.card K = 2) : Nat.card (sylT K) = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (isPGroup_sylT (K := K)).exists_card_eq
  have hET : (TableBF4Two.torus3 K).range ≤ sylT K := le_sup_left
  have h27 : 3 ^ 3 ∣ 3 ^ k := by
    rw [← card_range_torus3 (K := K), ← hk]
    exact Subgroup.card_dvd_of_le hET
  have hne : k ≠ 3 := by
    rintro rfl
    have hEq : (TableBF4Two.torus3 K).range = sylT K :=
      Subgroup.eq_of_le_of_card_ge hET (by rw [hk, card_range_torus3])
    apply cElt_not_mem_range (K := K)
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hle : 3 ^ k ≤ 3 ^ 4 := by
    have hG : ¬ 3 ^ (4 + 1) ∣ Nat.card (C3Levi K) := by
      rw [card_C3Levi_two hK]
      norm_num
    have hp : IsPGroup 3 ((sylT K).subgroupOf (C3Levi K)) :=
      isPGroup_sylT.of_equiv (Subgroup.subgroupOfEquivOfLe sylT_le_C3Levi).symm
    have h := card_le_of_isPGroup_of_not_dvd hG hp
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylT_le_C3Levi).toEquiv, hk] at h
  have h3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h27
  have h4 : k ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  rw [hk, show k = 4 by omega]

theorem exists_conj_le_sylT [Finite K] (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .F4 K)}
    (hAD : A ≤ C3Levi K) (hA : IsPGroup 3 A) :
    ∃ d ∈ C3Levi K, ∀ a ∈ A, d⁻¹ * a * d ∈ sylT K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL .F4 K) := finite_modGL
  set G := C3Levi K
  set T' : Subgroup G := (sylT K).subgroupOf G with hT'
  have hT'card : Nat.card T' = 3 ^ 4 := by
    rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylT_le_C3Levi).toEquiv, card_sylT hK]
  have hT'p : IsPGroup 3 T' := IsPGroup.of_card hT'card
  have hidx : ¬ 3 ∣ T'.index := by
    have h := T'.card_mul_index
    rw [hT'card, card_C3Levi_two hK] at h
    have hi : T'.index = 17920 := by omega
    rw [hi]
    norm_num
  set S := hT'p.toSylow hidx with hS
  set A' : Subgroup G := A.subgroupOf G
  have hA' : IsPGroup 3 A' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAD).symm
  obtain ⟨S', hAS'⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  refine ⟨(g : adjointGroup .F4 K), g.2, fun a ha => ?_⟩
  have h1 : (⟨a, hAD ha⟩ : G) ∈ (S' : Subgroup G) := hAS' (Subgroup.mem_subgroupOf.2 ha)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : g⁻¹ * ⟨a, hAD ha⟩ * g ∈ T' := by
    simpa [MulAut.conj_symm_apply, hS] using h1
  exact h2

theorem sylT_eq_closure :
    sylT K = Subgroup.closure (((TableBF4Two.torus3 K).range : Set (adjointGroup .F4 K)) ∪
      {cElt K}) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  rfl

theorem cElt_inv_eq : (cElt K)⁻¹ = cElt K ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', cElt_pow_three])

theorem sylT_normal_form {t : adjointGroup .F4 K} (ht : t ∈ sylT K) :
    ∃ f : Fin 3 → Multiplicative (ZMod 3), ∃ k : ℕ, t = TableBF4Two.torus3 K f * cElt K ^ k := by
  rw [sylT_eq_closure] at ht
  induction ht using Subgroup.closure_induction_left with
  | one => exact ⟨1, 0, by simp⟩
  | mul_left x hx y _ ih =>
    obtain ⟨f, k, rfl⟩ := ih
    rcases hx with ⟨g, rfl⟩ | hx
    · exact ⟨g * f, k, by rw [map_mul, mul_assoc]⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨shift f, k + 1, ?_⟩
      rw [← cElt_conj_torus3, pow_succ']
      group
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨f, k, rfl⟩ := ih
    rcases hx with ⟨g, rfl⟩ | hx
    · refine ⟨g⁻¹ * f, k, ?_⟩
      rw [map_mul, mul_assoc]
      congr 1
      exact (map_inv (TableBF4Two.torus3 K) g).symm
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨shift^[2] f, k + 2, ?_⟩
      rw [← cElt_pow_conj_torus3, cElt_inv_eq]
      group

theorem cElt_pow_mod (k : ℕ) : cElt K ^ k = cElt K ^ (k % 3) := by
  conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, cElt_pow_three, one_pow, one_mul]

theorem torusGen_zero_mem_of_le_sylT [Finite K] (hK : Nat.card K = 2)
    {B : Subgroup (adjointGroup .F4 K)} (hBT : B ≤ sylT K)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB : 3 ^ 3 ≤ Nat.card B) :
    TableBF4Two.torusGen K 0 ∈ B := by
  set E := (TableBF4Two.torus3 K).range with hE
  by_cases hBE : B ≤ E
  · have hEq : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [card_range_torus3]; exact hB)
    rw [hEq, torusGen_eq_torus3]
    exact ⟨_, rfl⟩
  exfalso
  obtain ⟨b, hb, hbE⟩ : ∃ b ∈ B, b ∉ E := by
    by_contra hne
    push Not at hne
    exact hBE fun x hx => hne x hx
  obtain ⟨f, k, hbk⟩ := sylT_normal_form (hBT hb)
  rw [cElt_pow_mod] at hbk
  have hk : k % 3 = 1 ∨ k % 3 = 2 := by
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
    · exfalso
      apply hbE
      rw [hbk, h, pow_zero, mul_one]
      exact ⟨f, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
  set δ := TableBF4Two.torus3 K (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) with hδ
  have hΔ : ∀ e ∈ B, e ∈ E → e ∈ Subgroup.zpowers δ := by
    intro e heB heE
    obtain ⟨g, rfl⟩ := heE
    have hcomm := hBc _ hb _ heB
    have h1 : b * TableBF4Two.torus3 K g * b⁻¹ = TableBF4Two.torus3 K g := by
      rw [hcomm, mul_inv_cancel_right]
    have h2 : b * TableBF4Two.torus3 K g * b⁻¹ = TableBF4Two.torus3 K (shift^[k % 3] g) := by
      rw [hbk]
      calc TableBF4Two.torus3 K f * cElt K ^ (k % 3) * TableBF4Two.torus3 K g *
            (TableBF4Two.torus3 K f * cElt K ^ (k % 3))⁻¹ =
          TableBF4Two.torus3 K f * (cElt K ^ (k % 3) * TableBF4Two.torus3 K g *
            (cElt K ^ (k % 3))⁻¹) * (TableBF4Two.torus3 K f)⁻¹ := by group
        _ = TableBF4Two.torus3 K f * TableBF4Two.torus3 K (shift^[k % 3] g) *
            (TableBF4Two.torus3 K f)⁻¹ := by rw [cElt_pow_conj_torus3]
        _ = TableBF4Two.torus3 K (shift^[k % 3] g) := by
          rw [← map_inv, ← map_mul, ← map_mul, mul_comm f, mul_assoc, mul_inv_cancel, mul_one]
    have hfix : shift^[k % 3] g = g := TableBF4Two.torus3_injective (h2.symm.trans h1)
    have hfix' : shift g = g ∨ shift (shift g) = g := by
      rcases hk with h | h
      · rw [h] at hfix
        exact Or.inl hfix
      · rw [h] at hfix
        exact Or.inr hfix
    rw [eq_const_of_shift g hfix', const_eq_pow, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) _
  have hδ3 : δ ^ 3 = 1 := by rw [hδ, ← map_pow, const_pow_three, map_one]
  have hcardΔ : Nat.card (Subgroup.zpowers δ) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hδ3)
  have hEB : Nat.card (E.subgroupOf B) ≤ 3 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun e : E.subgroupOf B => (⟨((e : B) : adjointGroup .F4 K),
        hΔ _ (e : B).2 (Subgroup.mem_subgroupOf.1 e.2)⟩ : Subgroup.zpowers δ)) ?_) hcardΔ
    intro e₁ e₂ h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have hET : E ≤ sylT K := le_sup_left
  have hrelT : E.relIndex (sylT K) = 3 := by
    have h := (E.subgroupOf (sylT K)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv, card_range_torus3,
      card_sylT hK] at h
    change 3 ^ 3 * E.relIndex (sylT K) = 3 ^ 4 at h
    omega
  have hrel : E.relIndex B ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hBT (by rw [hrelT]; norm_num)).trans (le_of_eq hrelT)
  have hcardB : Nat.card (E.subgroupOf B) * E.relIndex B = Nat.card B :=
    (E.subgroupOf B).card_mul_index
  have : Nat.card B ≤ 9 := by
    rw [← hcardB]
    calc Nat.card (E.subgroupOf B) * E.relIndex B ≤ 3 * 3 := Nat.mul_le_mul hEB hrel
      _ = 9 := by norm_num
  have h27 : (27 : ℕ) ≤ Nat.card B := by simpa using hB
  omega

theorem exists_conj_nodeElt_mem_of_le_C3Levi [Finite K] (hK : Nat.card K = 2)
    {A : Subgroup (adjointGroup .F4 K)} (hAD : A ≤ C3Levi K) (hA : IsElemAbelian 3 A)
    (h27 : 3 ^ 3 ≤ Nat.card A) : ∃ g : adjointGroup .F4 K, g * nodeElt K * g⁻¹ ∈ A := by
  have hAp : IsPGroup 3 A := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA.2 _ x.2
  obtain ⟨d, -, hd⟩ := exists_conj_le_sylT hK hAD hAp
  set B := A.map (MulAut.conj d⁻¹).toMonoidHom with hB
  have hBT : B ≤ sylT K := by
    rintro _ ⟨a, ha, rfl⟩
    have h := hd a ha
    simpa [MulAut.conj_apply] using h
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hab]
  have hBcard : 3 ^ 3 ≤ Nat.card B := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective]
    exact h27
  obtain ⟨a, ha, hae⟩ := torusGen_zero_mem_of_le_sylT hK hBT hBc hBcard
  have hae' : d⁻¹ * a * d = TableBF4Two.torusGen K 0 := by
    simpa [MulAut.conj_apply] using hae
  have hn : (nElt K)⁻¹ * nodeElt K * nElt K = TableBF4Two.torusGen K 0 := by
    have h := nWord_conj_rho_zero (K := K)
    change nElt K * TableBF4Two.torusGen K 0 * (nElt K)⁻¹ = nodeElt K at h
    rw [← h]
    group
  refine ⟨d * (nElt K)⁻¹, ?_⟩
  have e : d * (nElt K)⁻¹ * nodeElt K * (d * (nElt K)⁻¹)⁻¹ =
      d * ((nElt K)⁻¹ * nodeElt K * nElt K) * d⁻¹ := by group
  rw [e, hn, ← hae']
  have e' : d * (d⁻¹ * a * d) * d⁻¹ = a := by group
  rw [e']
  exact ha

end Sylow

end TableBF4TwoInputs

end CFSG.StandardType
