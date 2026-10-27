module

public import CFSG.LieType.SteinbergBRBlockParabolicDInfSolvable
public import CFSG.Quasithin.EmptyFaithful.S153LComp
public import CFSG.Quasithin.Background.HSL3S77Blk
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.LieType.SteinbergBR.BlockPar

namespace S125Pb

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem det_GL (A : GL a (ZMod 2)) : (A : Matrix a a (ZMod 2)).det = 1 := by
  have h : (A : Matrix a a (ZMod 2)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  generalize (A : Matrix a a (ZMod 2)).det = x at h ⊢
  fin_cases x
  · exact absurd rfl h
  · rfl

theorem toGL_bijective :
    Function.Bijective (SpecialLinearGroup.toGL : SpecialLinearGroup a (ZMod 2) →* GL a (ZMod 2)) :=
  ⟨SpecialLinearGroup.toGL_injective, fun A =>
    ⟨⟨A, det_GL A⟩, Units.ext (SpecialLinearGroup.coe_GL_coe_matrix _)⟩⟩

@[expose] noncomputable def glEquivSL : GL a (ZMod 2) ≃* SpecialLinearGroup a (ZMod 2) :=
  (MulEquiv.ofBijective _ toGL_bijective).symm

theorem coe_glEquivSL (A : GL a (ZMod 2)) :
    ((glEquivSL A : SpecialLinearGroup a (ZMod 2)) : Matrix a a (ZMod 2)) =
      (A : Matrix a a (ZMod 2)) := by
  have h : SpecialLinearGroup.toGL (glEquivSL A) = A :=
    (MulEquiv.ofBijective _ toGL_bijective).apply_symm_apply A
  rw [← SpecialLinearGroup.coe_GL_coe_matrix, h]

variable (a b) in
@[expose] noncomputable def chi :
    (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))) →* GL b (ZMod 2) × GL a (ZMod 2) :=
  (chiR (ZMod 2) a b).prod (chiL (ZMod 2) a b)

theorem chi_surjective : Function.Surjective (chi a b) := by
  rintro ⟨D, A⟩
  let g : SpecialLinearGroup (a ⊕ b) (ZMod 2) := ⟨fromBlocks A.val 0 0 D.val, by
    rw [det_fromBlocks_zero₂₁, det_GL A, det_GL D, mul_one]⟩
  refine ⟨⟨g, toBlocks_fromBlocks₂₁ _ _ _ _⟩, ?_⟩
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · exact toBlocks_fromBlocks₂₂ _ _ _ _
  · exact toBlocks_fromBlocks₁₁ _ _ _ _

variable (a b) in
@[expose] noncomputable def uniRad : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2)) :=
  (uniHom (ZMod 2) a b).range

theorem mem_uniRad {g : SpecialLinearGroup (a ⊕ b) (ZMod 2)} :
    g ∈ uniRad a b ↔ g ∈ parQ ∧ g.val.toBlocks₁₁ = 1 ∧ g.val.toBlocks₂₂ = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨uniHom_mem_parQ x, ?_, ?_⟩
    · change (fromBlocks 1 (Multiplicative.toAdd x) 0 1).toBlocks₁₁ = 1
      exact toBlocks_fromBlocks₁₁ _ _ _ _
    · change (fromBlocks 1 (Multiplicative.toAdd x) 0 1).toBlocks₂₂ = 1
      exact toBlocks_fromBlocks₂₂ _ _ _ _
  · rintro ⟨hQ, h11, h22⟩
    refine ⟨Multiplicative.ofAdd g.val.toBlocks₁₂, Subtype.ext ?_⟩
    rw [uniHom_val]
    conv_rhs => rw [eq_fromBlocks_of_mem_parQ hQ]
    rw [h11, h22]

theorem uniRad_le_parQ : uniRad a b ≤ parQ := fun _ h => (mem_uniRad.1 h).1

theorem ker_chi : (chi a b).ker = (uniRad a b).subgroupOf parQ := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_uniRad]
  simp only [chi, MonoidHom.prod_apply, Prod.mk_eq_one, Units.ext_iff]
  exact ⟨fun ⟨h2, h1⟩ => ⟨g.2, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩⟩

theorem isPGroup_uniRad : IsPGroup 2 (uniRad a b) := by
  rintro ⟨_, ⟨x, rfl⟩⟩
  refine ⟨1, Subtype.ext ?_⟩
  change uniHom (ZMod 2) a b x ^ 2 = 1
  have hx2 : x ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    generalize Multiplicative.toAdd x i j = y
    fin_cases y <;> rfl
  rw [← map_pow, hx2, map_one]

@[expose] def NoO2 (H : Type*) [Group H] : Prop :=
  ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N = ⊥

theorem noO2_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] (h₁ : NoO2 H₁) (h₂ : NoO2 H₂) :
    NoO2 (H₁ × H₂) := by
  intro N hN hp
  have hf : N.map (MonoidHom.fst H₁ H₂) = ⊥ :=
    h₁ _ (hN.map _ Prod.fst_surjective) (hp.map _)
  have hs : N.map (MonoidHom.snd H₁ H₂) = ⊥ :=
    h₂ _ (hN.map _ Prod.snd_surjective) (hp.map _)
  rw [eq_bot_iff]
  intro x hx
  have h1 : x.1 = 1 := by
    have : (MonoidHom.fst H₁ H₂) x ∈ N.map (MonoidHom.fst H₁ H₂) := Subgroup.mem_map_of_mem _ hx
    rw [hf, Subgroup.mem_bot] at this
    exact this
  have h2 : x.2 = 1 := by
    have : (MonoidHom.snd H₁ H₂) x ∈ N.map (MonoidHom.snd H₁ H₂) := Subgroup.mem_map_of_mem _ hx
    rw [hs, Subgroup.mem_bot] at this
    exact this
  rw [Subgroup.mem_bot]
  exact Prod.ext h1 h2

theorem noO2_of_mulEquiv {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂) (h : NoO2 H₂) :
    NoO2 H₁ := by
  intro N hN hp
  have := h (N.map e.toMonoidHom) (hN.map _ e.surjective) (hp.map _)
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 this

theorem noO2_of_simple {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (hcard : ¬ ∃ k : ℕ, Nat.card H = 2 ^ k) : NoO2 H := by
  intro N hN hp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [h, Subgroup.card_top] at hk
    exact hcard ⟨k, hk⟩

theorem noO2_SL3 : NoO2 (SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
  refine noO2_of_simple ?_
  rintro ⟨k, hk⟩
  rw [card_sl_three_zmod_two] at hk
  have h1 : k ≤ 7 := by
    by_contra h
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> norm_num at hk

theorem noO2_SL4 : NoO2 (SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  have := (isSimpleGroup_sl_zmod_two (m := 4) (by norm_num)).1
  refine noO2_of_simple ?_
  rintro ⟨k, hk⟩
  rw [card_sl_four_zmod_two] at hk
  have h1 : k ≤ 15 := by
    by_contra h
    have : 2 ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> norm_num at hk

theorem noO2_SL2 : NoO2 (SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  intro N hN hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_congr (glEquivSL (a := Fin 2)).symm.toEquiv]
    exact CFSG.Quasithin.H.S77.card_GL2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : 2 ^ k ∣ 6 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := this.trans hdvd
    norm_num at this
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Subgroup.eq_bot_of_card_eq N (by simpa using hk)
  · exfalso
    obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
      by_contra h
      push Not at h
      have : N = ⊥ := (Subgroup.eq_bot_iff_forall N).2 h
      rw [this, Subgroup.card_bot] at hk
      norm_num at hk
    have hcen : ∀ g : SpecialLinearGroup (Fin 2) (ZMod 2), g * x * g⁻¹ = x := by
      intro g
      have hgx : g * x * g⁻¹ ∈ N := hN.conj_mem x hxN g
      have hgx1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this)
      have hN2 : ∀ y ∈ N, y = 1 ∨ y = x := by
        intro y hy
        have : Fintype N := Fintype.ofFinite N
        by_contra hne
        push Not at hne
        have h3 : 3 ≤ Nat.card N := by
          have : ({⟨1, N.one_mem⟩, ⟨x, hxN⟩, ⟨y, hy⟩} : Finset N).card = 3 := by
            rw [Finset.card_eq_three]
            refine ⟨⟨1, N.one_mem⟩, ⟨x, hxN⟩, ⟨y, hy⟩, ?_, ?_, ?_, rfl⟩
            · exact fun h => hx1 (congrArg Subtype.val h).symm
            · exact fun h => hne.1 (congrArg Subtype.val h).symm
            · exact fun h => hne.2 (congrArg Subtype.val h).symm
          rw [Nat.card_eq_fintype_card, ← this]
          exact Finset.card_le_univ _
        rw [hk] at h3
        norm_num at h3
      rcases hN2 _ hgx with h | h
      · exact absurd h hgx1
      · exact h
    have key : ∀ x : SpecialLinearGroup (Fin 2) (ZMod 2), x ≠ 1 →
        ∃ g : SpecialLinearGroup (Fin 2) (ZMod 2), g * x * g⁻¹ ≠ x := by
      decide
    obtain ⟨g, hg⟩ := key x hx1
    exact hg (hcen g)

theorem noO2_GL (n : ℕ) (h : NoO2 (SpecialLinearGroup (Fin n) (ZMod 2))) :
    NoO2 (GL (Fin n) (ZMod 2)) :=
  noO2_of_mulEquiv glEquivSL h

theorem pCore_parQ (hO : NoO2 (GL b (ZMod 2) × GL a (ZMod 2))) :
    CFSG.pCore 2 (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))) = (chi a b).ker := by
  apply le_antisymm
  · have h1 := hO ((CFSG.pCore 2 _).map (chi a b))
      ((CFSG.pCore_normal (p := 2)).map _ chi_surjective) ((CFSG.pCore_isPGroup (p := 2)).map _)
    intro x hx
    have : chi a b x ∈ (CFSG.pCore 2 _).map (chi a b) := Subgroup.mem_map_of_mem _ hx
    rw [h1, Subgroup.mem_bot] at this
    exact this
  · rw [ker_chi]
    unfold CFSG.pCore
    refine le_sSup ⟨?_, ?_⟩
    · rw [← ker_chi]
      exact MonoidHom.normal_ker _
    · exact isPGroup_uniRad.of_equiv (Subgroup.subgroupOfEquivOfLe uniRad_le_parQ).symm

theorem quotient_pCore_parQ (hO : NoO2 (GL b (ZMod 2) × GL a (ZMod 2))) :
    Nonempty (↥(parQ : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))) ⧸
      CFSG.pCore 2 ↥(parQ : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))) ≃*
      SpecialLinearGroup b (ZMod 2) × SpecialLinearGroup a (ZMod 2)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (pCore_parQ hO)).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ chi_surjective).trans
      (MulEquiv.prodCongr glEquivSL glEquivSL))⟩

variable (a b) in
@[expose] noncomputable def chiRJ :
    (parJR (ZMod 2) a b : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))) →* GL b (ZMod 2) :=
  (chiR (ZMod 2) a b).comp (Subgroup.inclusion parJR_le_parQ)

variable (a b) in
@[expose] noncomputable def chiLJ :
    (parJL (ZMod 2) a b : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))) →* GL a (ZMod 2) :=
  (chiL (ZMod 2) a b).comp (Subgroup.inclusion parJL_le_parQ)

theorem chiRJ_surjective : Function.Surjective (chiRJ a b) := by
  intro D
  refine ⟨⟨levR (ZMod 2) a (glEquivSL D), levR_mem_parJR _⟩, Units.ext ?_⟩
  change (levR (ZMod 2) a (glEquivSL D)).val.toBlocks₂₂ = D.val
  rw [levR_val, toBlocks_fromBlocks₂₂]
  exact coe_glEquivSL D

theorem chiLJ_surjective : Function.Surjective (chiLJ a b) := by
  intro A
  refine ⟨⟨levL (ZMod 2) b (glEquivSL A), levL_mem_parJL _⟩, Units.ext ?_⟩
  change (levL (ZMod 2) b (glEquivSL A)).val.toBlocks₁₁ = A.val
  rw [levL_val, toBlocks_fromBlocks₁₁]
  exact coe_glEquivSL A

theorem ker_chiRJ : (chiRJ a b).ker = (uniRad a b).subgroupOf (parJR (ZMod 2) a b) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_uniRad, Units.ext_iff]
  have hJ := mem_parJR.1 g.2
  exact ⟨fun h => ⟨hJ.1, hJ.2, h⟩, fun h => h.2.2⟩

theorem ker_chiLJ : (chiLJ a b).ker = (uniRad a b).subgroupOf (parJL (ZMod 2) a b) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_uniRad, Units.ext_iff]
  have hJ := mem_parJL.1 g.2
  exact ⟨fun h => ⟨hJ.1, h, hJ.2⟩, fun h => h.2.1⟩

instance normal_uniRad_parJR : ((uniRad a b).subgroupOf (parJR (ZMod 2) a b)).Normal := by
  rw [← ker_chiRJ]
  exact MonoidHom.normal_ker _

instance normal_uniRad_parJL : ((uniRad a b).subgroupOf (parJL (ZMod 2) a b)).Normal := by
  rw [← ker_chiLJ]
  exact MonoidHom.normal_ker _

theorem quotient_parJR :
    Nonempty (↥(parJR (ZMod 2) a b) ⧸ (uniRad a b).subgroupOf (parJR (ZMod 2) a b) ≃*
      SpecialLinearGroup b (ZMod 2)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq ker_chiRJ.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ chiRJ_surjective).trans glEquivSL)⟩

theorem quotient_parJL :
    Nonempty (↥(parJL (ZMod 2) a b) ⧸ (uniRad a b).subgroupOf (parJL (ZMod 2) a b) ≃*
      SpecialLinearGroup a (ZMod 2)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq ker_chiLJ.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ chiLJ_surjective).trans glEquivSL)⟩

theorem le_uniRad_of_parJR (hO : NoO2 (GL b (ZMod 2)))
    {N : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))} (hN : N ≤ parJR (ZMod 2) a b)
    (hnorm : (N.subgroupOf (parJR (ZMod 2) a b)).Normal) (hp : IsPGroup 2 N) :
    N ≤ uniRad a b := by
  have h1 := hO ((N.subgroupOf (parJR (ZMod 2) a b)).map (chiRJ a b))
    (hnorm.map _ chiRJ_surjective)
    ((hp.of_equiv (Subgroup.subgroupOfEquivOfLe hN).symm).map _)
  intro x hx
  have hmem : chiRJ a b ⟨x, hN hx⟩ ∈ (N.subgroupOf (parJR (ZMod 2) a b)).map (chiRJ a b) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
  rw [h1, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_chiRJ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem le_uniRad_of_parJL (hO : NoO2 (GL a (ZMod 2)))
    {N : Subgroup (SpecialLinearGroup (a ⊕ b) (ZMod 2))} (hN : N ≤ parJL (ZMod 2) a b)
    (hnorm : (N.subgroupOf (parJL (ZMod 2) a b)).Normal) (hp : IsPGroup 2 N) :
    N ≤ uniRad a b := by
  have h1 := hO ((N.subgroupOf (parJL (ZMod 2) a b)).map (chiLJ a b))
    (hnorm.map _ chiLJ_surjective)
    ((hp.of_equiv (Subgroup.subgroupOfEquivOfLe hN).symm).map _)
  intro x hx
  have hmem : chiLJ a b ⟨x, hN hx⟩ ∈ (N.subgroupOf (parJL (ZMod 2) a b)).map (chiLJ a b) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
  rw [h1, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_chiLJ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem uniRad_le_parJR : uniRad a b ≤ parJR (ZMod 2) a b := by
  rintro _ ⟨x, rfl⟩
  exact uniHom_mem_parJR x

theorem uniRad_le_parJL : uniRad a b ≤ parJL (ZMod 2) a b := by
  rintro _ ⟨x, rfl⟩
  exact uniHom_mem_parJL x

theorem isSolvable_GL2 : Group.IsSolvable (GL (Fin 2) (ZMod 2)) :=
  CFSG.Quasithin.S153L.comp_solvable_of_card_six CFSG.Quasithin.H.S77.card_GL2

theorem isSolvable_GL1 : Group.IsSolvable (GL (Fin 1) (ZMod 2)) := by
  have : Subsingleton (GL (Fin 1) (ZMod 2)) := by
    refine ⟨fun x y => ?_⟩
    rw [← (MulEquiv.ofBijective _ (toGL_bijective (a := Fin 1))).apply_symm_apply x,
      ← (MulEquiv.ofBijective _ (toGL_bijective (a := Fin 1))).apply_symm_apply y]
    congr 1
    exact Subsingleton.elim _ _
  infer_instance

theorem perfectResidual_parQ23 :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin 2 ⊕ Fin 3) (ZMod 2))) =
      (parJR (ZMod 2) (Fin 2) (Fin 3)).subgroupOf parQ :=
  perfectResidual_parQ_eq_parJR_of_isSolvable isSolvable_GL2
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by norm_num))

theorem perfectResidual_parQ32 :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ Fin 2) (ZMod 2))) =
      (parJL (ZMod 2) (Fin 3) (Fin 2)).subgroupOf parQ :=
  perfectResidual_parQ_eq_parJL_of_isSolvable isSolvable_GL2
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by norm_num))

theorem perfectResidual_parQ14 :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin 1 ⊕ Fin 4) (ZMod 2))) =
      (parJR (ZMod 2) (Fin 1) (Fin 4)).subgroupOf parQ :=
  perfectResidual_parQ_eq_parJR_of_isSolvable isSolvable_GL1
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by norm_num))

theorem perfectResidual_parQ41 :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin 4 ⊕ Fin 1) (ZMod 2))) =
      (parJL (ZMod 2) (Fin 4) (Fin 1)).subgroupOf parQ :=
  perfectResidual_parQ_eq_parJL_of_isSolvable isSolvable_GL1
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by norm_num))

theorem parJR_eq_parQ_of_fin_one :
    parJR (ZMod 2) (Fin 1) b = parQ := by
  refine le_antisymm parJR_le_parQ fun g hg => mem_parJR.2 ⟨hg, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  have hdet := det_eq_of_mem_parQ hg
  have h1 : (g.val.toBlocks₁₁).det = 1 := by
    have h := left_ne_zero_of_mul_eq_one hdet
    generalize (g.val.toBlocks₁₁).det = x at h ⊢
    fin_cases x
    · exact absurd rfl h
    · rfl
  rw [Matrix.det_unique] at h1
  simpa using h1

theorem parJL_eq_parQ_of_fin_one :
    parJL (ZMod 2) a (Fin 1) = parQ := by
  refine le_antisymm parJL_le_parQ fun g hg => mem_parJL.2 ⟨hg, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  have hdet := det_eq_of_mem_parQ hg
  have h1 : (g.val.toBlocks₂₂).det = 1 := by
    have h := right_ne_zero_of_mul_eq_one hdet
    generalize (g.val.toBlocks₂₂).det = x at h ⊢
    fin_cases x
    · exact absurd rfl h
    · rfl
  rw [Matrix.det_unique] at h1
  simpa using h1

end S125Pb

end CFSG.Quasithin.H13
