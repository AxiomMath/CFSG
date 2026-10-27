module

public import CFSG.Quasithin.Recognition.L34AmalgamHom
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22PointStabilizer
public import CFSG.Quasithin.Recognition.L34AmalgamCases
public import CFSG.Quasithin.Recognition.L34AmalgamCert

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.CosetTable

@[expose] noncomputable def homOf {X : Type*} [Group X] (f : Fin 5 → X)
    {ws : List (List (Fin 5 × Bool))} (hws : ∀ w ∈ ws, evalW f w = 1) : PG 5 ws →* X :=
  PresentedGroup.toGroup (f := f) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [← evalW_eq_lift]
    exact hws w hw

theorem homOf_of {X : Type*} [Group X] (f : Fin 5 → X) {ws : List (List (Fin 5 × Bool))}
    (hws : ∀ w ∈ ws, evalW f w = 1) (j : Fin 5) : homOf f hws (PresentedGroup.of j) = f j :=
  PresentedGroup.toGroup.of _

theorem evalW_genK_good
    {i : Fin 12} (hi : IsGood i) : ∀ w ∈ relsOf i 3, evalW genK w = 1 := by
  intro w hw
  apply Subtype.ext
  rw [Subgroup.coe_one, show ((evalW genK w : ↥(stabilizer M22 (0 : Fin 22))) : M22) =
    evalW gen w from (evalW_map (stabilizer M22 (0 : Fin 22)).subtype genK gen w
      (fun x _ => rfl)).symm]
  rcases List.mem_append.mp hw with hw | hw
  · exact evalW_amalRels w hw
  · rw [List.mem_singleton.mp hw]
    exact evalW_extra_good i hi

instance isSimpleGroup_stab0
    : IsSimpleGroup (stabilizer M22 (0 : Fin 22)) :=
  isSimpleGroup_stabilizer 0

section Amalgam

variable {L : Type*} [Group L] {L₁ L₂ : Subgroup L}
  {φ₁ : ↥m22TwoStab ≃* ↥L₁} {φ₂ : ↥m22PtHexStab ≃* ↥L₂}
  (hB : ∀ (b : M22) (h₁ : b ∈ m22TwoStab) (h₂ : b ∈ m22PtHexStab),
    (φ₁ ⟨b, h₁⟩ : L) = φ₂ ⟨b, h₂⟩)
include hB

theorem mem_two_of_phi2_mem (hB' : ∀ p : ↥m22TwoStab, (φ₁ p : L) ∈ L₂ ↔ (p : M22) ∈ m22PtHexStab)
    (p : ↥m22PtHexStab) (hp : (φ₂ p : L) ∈ L₁) : (p : M22) ∈ m22TwoStab := by
  set q : ↥m22TwoStab := φ₁.symm ⟨φ₂ p, hp⟩ with hq
  have hq1 : (φ₁ q : L) = φ₂ p := by rw [hq, MulEquiv.apply_symm_apply]
  have hq2 : (q : M22) ∈ m22PtHexStab := (hB' q).mp (by rw [hq1]; exact (φ₂ p).2)
  have h3 := hB q q.2 hq2
  rw [Subtype.coe_eta, hq1] at h3
  have h4 : p = ⟨q, hq2⟩ := φ₂.injective (Subtype.ext h3)
  rw [h4]
  exact q.2

theorem false_of_bad
    (hB' : ∀ p : ↥m22TwoStab, (φ₁ p : L) ∈ L₂ ↔ (p : M22) ∈ m22PtHexStab)
    {ws : List (List (Fin 5 × Bool))} (hws : ∀ w ∈ ws, evalW (genL φ₁ φ₂) w = 1)
    (hcert : subsetCheck ws [0, 1, 2, 3] 100000 1 = true) : False := by
  obtain ⟨hfi, hidx⟩ := index_genSub_le hcert
  have hH : genSub {r : FreeGroup (Fin 5) | r ∈ ws.map FreeGroup.mk} (subsetOf 5 [0, 1, 2, 3])
      = ⊤ := by
    have h0 := hfi.index_ne_zero
    exact Subgroup.index_eq_one.mp (by omega)
  have h4 : (PresentedGroup.of (4 : Fin 5) : PG 5 ws) ∈
      genSub {r : FreeGroup (Fin 5) | r ∈ ws.map FreeGroup.mk} (subsetOf 5 [0, 1, 2, 3]) := by
    rw [hH]
    exact Subgroup.mem_top _
  have hle : (genSub {r : FreeGroup (Fin 5) | r ∈ ws.map FreeGroup.mk}
      (subsetOf 5 [0, 1, 2, 3])).map (homL hws) ≤ L₁ := by
    rw [genSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have hj4 : j ≠ 4 := (mem_subsetOf_iff j).mp hj
    rw [homL_of, genL_eq₁ hj4]
    exact (φ₁ (gen₁ j)).2
  have h5 := hle ⟨_, h4, rfl⟩
  rw [homL_of, genL_eq₂ hB (by decide)] at h5
  have h6 := mem_two_of_phi2_mem hB hB' _ h5
  rw [coe_gen₂ (by decide), gen_four] at h6
  exact bT2_not_mem h6

theorem exists_iso_of_good
    (hgen : L₁ ⊔ L₂ = ⊤) {i : Fin 12} (hi : IsGood i)
    (hws : ∀ w ∈ relsOf i 3, evalW (genL φ₁ φ₂) w = 1) :
    ∃ Φ : L ≃* stabilizer M22 (0 : Fin 22),
      (∀ p : ↥m22TwoStab, (Φ (φ₁ p) : M22) = p) ∧ (∀ p : ↥m22PtHexStab, (Φ (φ₂ p) : M22) = p) := by
  obtain ⟨hfinR, hcardR⟩ := card_le_of_subsetCheck_nil _ (cert_P1 i hi)
  obtain ⟨hfinP, hcardP⟩ := card_le_of_subsetCheck (relsOf i 3) [0, 1, 2, 3] (cert_good i hi)
  have hP : Nat.card (PG 5 (relsOf i 3)) ≤ 20160 := hcardP.trans (by omega)
  set ψK := homOf genK (evalW_genK_good hi) with hψK
  have hrangeK : ψK.range = Subgroup.closure (Set.range genK) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 1
  have hsurjK : Function.Surjective ψK := by
    rw [← MonoidHom.range_eq_top, hrangeK]
    apply Subgroup.map_injective (stabilizer M22 (0 : Fin 22)).subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact closure_range_gen
  have hbijK : Function.Bijective ψK :=
    hsurjK.bijective_of_nat_card_le (by rw [card_stabilizer_point]; exact hP)
  set eK := MulEquiv.ofBijective ψK hbijK with heK
  have : Nontrivial (PG 5 (relsOf i 3)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr eK.toEquiv, card_stabilizer_point]
    norm_num
  have : IsSimpleGroup (PG 5 (relsOf i 3)) :=
    IsSimpleGroup.isSimpleGroup_of_surjective eK.symm.toMonoidHom eK.symm.surjective
  set ψL := homL hws with hψL
  have hsurjL : Function.Surjective ψL := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨p, rfl⟩ : ∃ p, (φ₁ p : L) = y := ⟨φ₁.symm ⟨y, hy⟩, by rw [MulEquiv.apply_symm_apply]⟩
      have hp : p ∈ Subgroup.closure (gen₁ '' {0, 1, 2, 3}) := by
        rw [closure_gen₁]; exact Subgroup.mem_top p
      have := Subgroup.mem_map_of_mem (L₁.subtype.comp φ₁.toMonoidHom) hp
      rw [MonoidHom.map_closure] at this
      refine (Subgroup.closure_le _).mpr ?_ this
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      have hj4 : j ≠ 4 := by rintro rfl; simp at hj
      exact ⟨PresentedGroup.of j, by rw [hψL, homL_of, genL_eq₁ hj4]; rfl⟩
    · obtain ⟨p, rfl⟩ : ∃ p, (φ₂ p : L) = y := ⟨φ₂.symm ⟨y, hy⟩, by rw [MulEquiv.apply_symm_apply]⟩
      have hp : p ∈ Subgroup.closure (gen₂ '' {0, 1, 2, 4}) := by
        rw [closure_gen₂]; exact Subgroup.mem_top p
      have := Subgroup.mem_map_of_mem (L₂.subtype.comp φ₂.toMonoidHom) hp
      rw [MonoidHom.map_closure] at this
      refine (Subgroup.closure_le _).mpr ?_ this
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      have hj3 : j ≠ 3 := by rintro rfl; simp at hj
      exact ⟨PresentedGroup.of j, by rw [hψL, homL_of, genL_eq₂ hB hj3]; rfl⟩
  have hinjL : Function.Injective ψL := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MonoidHom.normal_ker ψL).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hall : ∀ y : L, y = 1 := fun y => by
        obtain ⟨x, rfl⟩ := hsurjL y
        exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x)
      have h2 : φ₁ ⟨bT1, bT1_mem_two⟩ = 1 := Subtype.ext (hall _)
      have h3 : (⟨bT1, bT1_mem_two⟩ : ↥m22TwoStab) = 1 :=
        φ₁.injective (h2.trans (map_one φ₁).symm)
      have h4 : bT1 = 1 := congrArg Subtype.val h3
      exact bT1_not_mem (by rw [h4]; exact m22PtHexStab.one_mem)
  set eL := MulEquiv.ofBijective ψL ⟨hinjL, hsurjL⟩ with heL
  have hsymm : ∀ j : Fin 5, eL.symm (genL φ₁ φ₂ j) = PresentedGroup.of j := by
    intro j
    apply eL.injective
    rw [MulEquiv.apply_symm_apply]
    show genL φ₁ φ₂ j = ψL (PresentedGroup.of j)
    rw [hψL, homL_of]
  have hK : ∀ j : Fin 5, ((eL.symm.trans eK) (genL φ₁ φ₂ j) : M22) = gen j := by
    intro j
    rw [MulEquiv.trans_apply, hsymm]
    show ((ψK (PresentedGroup.of j) : ↥(stabilizer M22 (0 : Fin 22))) : M22) = gen j
    rw [hψK, homOf_of]
    rfl
  refine ⟨eL.symm.trans eK, fun p => ?_, fun p => ?_⟩
  · have hF : ((stabilizer M22 (0 : Fin 22)).subtype.comp (eL.symm.trans eK).toMonoidHom).comp
        (L₁.subtype.comp φ₁.toMonoidHom) = m22TwoStab.subtype := by
      refine MonoidHom.eq_of_eqOn_dense closure_gen₁ ?_
      rintro _ ⟨j, hj, rfl⟩
      have hj4 : j ≠ 4 := by rintro rfl; simp at hj
      have := hK j
      rw [genL_eq₁ hj4] at this
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom]
      rw [this, coe_gen₁ hj4]
    exact DFunLike.congr_fun hF p
  · have hF : ((stabilizer M22 (0 : Fin 22)).subtype.comp (eL.symm.trans eK).toMonoidHom).comp
        (L₂.subtype.comp φ₂.toMonoidHom) = m22PtHexStab.subtype := by
      refine MonoidHom.eq_of_eqOn_dense closure_gen₂ ?_
      rintro _ ⟨j, hj, rfl⟩
      have hj3 : j ≠ 3 := by rintro rfl; simp at hj
      have := hK j
      rw [genL_eq₂ hB hj3] at this
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom]
      rw [this, coe_gen₂ hj3]
    exact DFunLike.congr_fun hF p

end Amalgam

theorem nonempty_mulEquiv_m22Stab_of_amalgam
    {L : Type*} [Group L] [Finite L]
    {L₁ L₂ : Subgroup L} (hgen : L₁ ⊔ L₂ = ⊤)
    (φ₁ : ↥m22TwoStab ≃* ↥L₁) (φ₂ : ↥m22PtHexStab ≃* ↥L₂)
    (hB : ∀ (b : M22) (h₁ : b ∈ m22TwoStab) (h₂ : b ∈ m22PtHexStab),
      (φ₁ ⟨b, h₁⟩ : L) = φ₂ ⟨b, h₂⟩)
    (hB' : ∀ p : ↥m22TwoStab, (φ₁ p : L) ∈ L₂ ↔ (p : M22) ∈ m22PtHexStab)
    {t₁ t₂ : L} (ht₁ : t₁ ∈ L₁) (ht₁' : t₁ ∉ L₂) (ht₂ : t₂ ∈ L₂) (ht₂' : t₂ ∉ L₁)
    (h₁ : t₁ * t₁ = 1) (h₂ : t₂ * t₂ = 1) (h₃ : orderOf (t₁ * t₂) ≤ 3) :
    ∃ Φ : L ≃* stabilizer M22 (0 : Fin 22),
      (∀ p : ↥m22TwoStab, (Φ (φ₁ p) : M22) = p) ∧ (∀ p : ↥m22PtHexStab, (Φ (φ₂ p) : M22) = p) := by
  set σ₁ : ↥m22TwoStab := φ₁.symm ⟨t₁, ht₁⟩ with hσ₁
  set σ₂ : ↥m22PtHexStab := φ₂.symm ⟨t₂, ht₂⟩ with hσ₂
  have hφσ₁ : (φ₁ σ₁ : L) = t₁ := by rw [hσ₁, MulEquiv.apply_symm_apply]
  have hφσ₂ : (φ₂ σ₂ : L) = t₂ := by rw [hσ₂, MulEquiv.apply_symm_apply]
  have hσ₁' : (σ₁ : M22) ∉ m22PtHexStab := fun h => ht₁' (by rw [← hφσ₁]; exact (hB' σ₁).mpr h)
  have hσ₂' : (σ₂ : M22) ∉ m22TwoStab := by
    intro h
    apply ht₂'
    have e := hB (σ₂ : M22) h σ₂.2
    rw [Subtype.coe_eta, hφσ₂] at e
    rw [← e]
    exact (φ₁ _).2
  have hsq₁ : (σ₁ : M22) * σ₁ = 1 := by
    have : σ₁ * σ₁ = 1 := φ₁.injective (by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hφσ₁, h₁, map_one]
      rfl)
    exact congrArg Subtype.val this
  have hsq₂ : (σ₂ : M22) * σ₂ = 1 := by
    have : σ₂ * σ₂ = 1 := φ₂.injective (by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hφσ₂, h₂, map_one]
      rfl)
    exact congrArg Subtype.val this
  obtain ⟨b, hb, i, hb1, hb2⟩ := exists_conj_rep σ₁.2 hσ₁' hsq₁ σ₂.2 hσ₂' hsq₂
  have hℓ : (φ₁ ⟨b, hb.1⟩ : L) = φ₂ ⟨b, hb.2⟩ := hB b hb.1 hb.2
  have hc1 : (φ₁ ⟨b, hb.1⟩ : L) * t₁ * (φ₁ ⟨b, hb.1⟩ : L)⁻¹ = genL φ₁ φ₂ 3 := by
    rw [genL_eq₁ (by decide)]
    have e : (⟨b, hb.1⟩ : ↥m22TwoStab) * σ₁ * (⟨b, hb.1⟩ : ↥m22TwoStab)⁻¹ = gen₁ 3 := by
      apply Subtype.ext
      rw [coe_gen₁ (by decide), gen_three, ← hb1]
      rfl
    rw [← e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφσ₁]
  have hc2 : (φ₁ ⟨b, hb.1⟩ : L) * t₂ * (φ₁ ⟨b, hb.1⟩ : L)⁻¹ =
      evalW (genL φ₁ φ₂) (word (repStr i)) := by
    rw [evalW_genL_rep hB i, hℓ]
    have e : (⟨b, hb.2⟩ : ↥m22PtHexStab) * σ₂ * (⟨b, hb.2⟩ : ↥m22PtHexStab)⁻¹ =
        ⟨rep i, rep_mem i⟩ := by
      apply Subtype.ext
      exact hb2
    rw [← e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφσ₂]
  have hk0 : 0 < orderOf (t₁ * t₂) := orderOf_pos _
  have hk1 : orderOf (t₁ * t₂) ≠ 1 := by
    intro h
    have h12 : t₁ * t₂ = 1 := orderOf_eq_one_iff.mp h
    have ht : t₁ = t₂ := by
      have : t₁ = t₂⁻¹ := eq_inv_of_mul_eq_one_left h12
      rw [this, inv_eq_of_mul_eq_one_right h₂]
    exact ht₁' (ht ▸ ht₂)
  have hrel : evalW (genL φ₁ φ₂) (extra i (orderOf (t₁ * t₂))) = 1 := by
    rw [evalW_extra, ← hc1, ← hc2,
      show (φ₁ ⟨b, hb.1⟩ : L) * t₁ * (φ₁ ⟨b, hb.1⟩ : L)⁻¹ *
          ((φ₁ ⟨b, hb.1⟩ : L) * t₂ * (φ₁ ⟨b, hb.1⟩ : L)⁻¹) =
        (φ₁ ⟨b, hb.1⟩ : L) * (t₁ * t₂) * (φ₁ ⟨b, hb.1⟩ : L)⁻¹ by group,
      conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hws : ∀ w ∈ relsOf i (orderOf (t₁ * t₂)), evalW (genL φ₁ φ₂) w = 1 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact evalW_genL_amalRels hB w hw
    · rw [List.mem_singleton.mp hw]
      exact hrel
  by_cases hg : IsGood i ∧ orderOf (t₁ * t₂) = 3
  · obtain ⟨hgi, hk3⟩ := hg
    rw [hk3] at hws
    exact exists_iso_of_good hB hgen hgi hws
  · exfalso
    have hk : orderOf (t₁ * t₂) ∈ [2, 3] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact false_of_bad hB hB' hws (cert_bad i _ hk hg)

end CFSG.Quasithin.L34Amalgam
