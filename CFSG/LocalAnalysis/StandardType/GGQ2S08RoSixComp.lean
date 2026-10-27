module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixMat
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixQuasi
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

namespace GGQ2S08RoSix

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

@[expose] noncomputable def piL (c : GGQ2S08RoSix Bs L x) :
    ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) c.K (2 ^ 1)) :=
  c.θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem piL_surjective (c : GGQ2S08RoSix Bs L x) : Function.Surjective c.piL :=
  c.θ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piL_ker (c : GGQ2S08RoSix Bs L x) : c.piL.ker = Subgroup.center ↥L := by
  ext l
  rw [MonoidHom.mem_ker]
  change c.θ (QuotientGroup.mk' (Subgroup.center ↥L) l) = 1 ↔ _
  rw [← map_one c.θ, c.θ.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite G]
  in
theorem su6_eq (K : Type) [Field K] :
    LargeEvenSUGroup (Fin 6) K 2 = ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 := by
  rw [largeEvenSUGroup_eq_statedSU, ClassicalGroups.UnitaryFlag.unitarySU, pow_one]

noncomputable abbrev suCongr (K : Type) [Field K] :
    ↥(LargeEvenSUGroup (Fin 6) K 2) ≃* ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
  MulEquiv.subgroupCongr (su6_eq K)

@[expose] noncomputable def fr (c : GGQ2S08RoSix Bs L x) :
    ↥(LargeEvenSUGroup (Fin 6) c.K 2) →* LargeEvenProj (LargeEvenSUGroup (Fin 6) c.K (2 ^ 1)) :=
  (InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ).comp (suCongr c.K).toMonoidHom

theorem fr_apply (c : GGQ2S08RoSix Bs L x) (u : ↥(LargeEvenSUGroup (Fin 6) c.K 2)) :
    c.fr u = InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ (suCongr c.K u) := rfl

theorem fr_surjective (c : GGQ2S08RoSix Bs L x) : Function.Surjective c.fr :=
  (InndiagSU.frameMk_surjective _ c.Q c.hQ).comp (suCongr c.K).surjective

@[expose] noncomputable def stabImg (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) c.K (2 ^ 1))) :=
  (ggQ2s08r6Stab c.K w).map c.fr

@[expose] noncomputable def stabPre (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : Subgroup ↥L :=
  (c.stabImg w).comap c.piL

@[expose] noncomputable def comp (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : Subgroup G :=
  (⁅c.stabPre w, c.stabPre w⁆).map L.subtype

theorem stabImg_perfect (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    ⁅c.stabImg w, c.stabImg w⁆ = c.stabImg w := by
  rw [stabImg, ← Subgroup.map_commutator, ggQ2s08r6_stab_perfect c.hK w]

theorem stabImg_sup (c : GGQ2S08RoSix Bs L x) {w w' : Fin 6} (h : w ≠ w') :
    c.stabImg w ⊔ c.stabImg w' = ⊤ := by
  rw [stabImg, stabImg, ← Subgroup.map_sup, ggQ2s08r6_stab_sup c.hK h, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr c.fr_surjective]

theorem fr_injOn (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {u : ↥(LargeEvenSUGroup (Fin 6) c.K 2)}
    (hu : u ∈ ggQ2s08r6Stab c.K w) (h1 : c.fr u = 1) : u = 1 := by
  rw [fr_apply, InndiagSU.frameMk_apply] at h1
  have hmem := (QuotientGroup.eq_one_iff _).mp h1
  have hmem' : (((TableBUE.conjSU (USixTwo.fieldDataFour c.hK) c.Q c.hQ).symm (suCongr c.K u) :
      ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6)) : GL (Fin 6) c.K) ∈
        LargeEvenScalars (Fin 6) c.K := hmem
  obtain ⟨μ, hμ⟩ := hmem'
  rw [InndiagSU.coe_conjSU_symm] at hμ
  have hu' : ((u : GL (Fin 6) c.K)) = Matrix.GeneralLinearGroup.scalar (Fin 6) μ := by
    have h2 : ((suCongr c.K u : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6)) :
        GL (Fin 6) c.K) = (u : GL (Fin 6) c.K) := rfl
    rw [h2] at hμ
    have h3 : (u : GL (Fin 6) c.K) = c.Q⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) μ * c.Q := by
      rw [hμ]
      group
    rw [h3, ← TypeA.PGLTor.scalar_mul_comm μ c.Q⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hww := hu w
  rw [if_pos rfl, hu', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at hww
  have hμ1 : μ = 1 := Units.ext hww
  apply Subtype.ext
  rw [hu', hμ1, map_one]
  rfl

theorem fr_comp_injective (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    Function.Injective (c.fr.comp (ggQ2s08r6Stab c.K w).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
  have := c.fr_injOn w u.2 hu
  rw [Subgroup.mem_bot]
  exact Subtype.ext this

theorem range_fr_comp (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    (c.fr.comp (ggQ2s08r6Stab c.K w).subtype).range = c.stabImg w := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, stabImg]

noncomputable def stabEquiv (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    ↥(ggQ2s08r6Stab c.K w) ≃* ↥(c.stabImg w) :=
  (MonoidHom.ofInjective (c.fr_comp_injective w)).trans (MulEquiv.subgroupCongr (c.range_fr_comp w))

theorem stabImg_simple (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : IsSimpleGroup ↥(c.stabImg w) := by
  haveI := ggQ2s08r6_stab_simple c.hK w
  exact (c.stabEquiv w).symm.isSimpleGroup

noncomputable abbrev compL (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : Subgroup ↥L :=
  ⁅c.stabPre w, c.stabPre w⁆

theorem piL_ker_le (c : GGQ2S08RoSix Bs L x) : c.piL.ker ≤ Subgroup.center ↥L := by
  rw [c.piL_ker]

theorem compL_quasisimple (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    CFSG.Assembly.IsQuasisimple ↥(c.compL w) :=
  ggQ2s08r6_comm_comap_quasisimple c.piL_surjective c.piL_ker_le (c.stabImg w)
    (c.stabImg_perfect w) (c.stabImg_simple w)

theorem comp_quasisimple (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    CFSG.Assembly.IsQuasisimple ↥(c.comp w) :=
  ggQ2s08r6_isQuasisimple_map_subtype (c.compL_quasisimple w)

theorem comp_le (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : c.comp w ≤ L :=
  Subgroup.map_subtype_le _

theorem comp_sup (c : GGQ2S08RoSix Bs L x) {w w' : Fin 6} (h : w ≠ w') :
    c.comp w ⊔ c.comp w' = L := by
  rw [comp, comp, stabPre, stabPre, ← Subgroup.map_sup,
    ggQ2s08r6_comm_comap_sup c.piL_surjective c.piL_ker_le
    c.hperf (c.stabImg w) (c.stabImg w') (c.stabImg_perfect w) (c.stabImg_perfect w')
    (c.stabImg_sup h), ← MonoidHom.range_eq_map, Subgroup.range_subtype]

noncomputable abbrev conjB (c : GGQ2S08RoSix Bs L x) (b : Bs) : MulAut ↥L :=
  e6QTwoBstarConjAction c.hNL b

theorem piL_conjB (c : GGQ2S08RoSix Bs L x) (b : Bs) (l : ↥L) :
    c.piL (c.conjB b l) = c.act b (c.piL l) := by
  have h := e6QTwoSixFrameAction_apply c.hNL c.θ b l
  have hl : c.conjB b l = ⟨(b : G) * (l : G) * (b : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (c.hNL b.2) (l : G)).mp l.2⟩ :=
    Subtype.ext (e6QTwoBstarConjAction_apply c.hNL b l)
  rw [hl]
  exact h.symm

theorem exists_scalar_of_fr_eq_one (c : GGQ2S08RoSix Bs L x)
    {a : ↥(LargeEvenSUGroup (Fin 6) c.K 2)} (h1 : c.fr a = 1) :
    ∃ μ : c.Kˣ, (a : GL (Fin 6) c.K) = Matrix.GeneralLinearGroup.scalar (Fin 6) μ := by
  rw [fr_apply, InndiagSU.frameMk_apply] at h1
  have hmem := (QuotientGroup.eq_one_iff _).mp h1
  have hmem' : (((TableBUE.conjSU (USixTwo.fieldDataFour c.hK) c.Q c.hQ).symm (suCongr c.K a) :
      ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6)) : GL (Fin 6) c.K) ∈
        LargeEvenScalars (Fin 6) c.K := hmem
  obtain ⟨μ, hμ⟩ := hmem'
  rw [InndiagSU.coe_conjSU_symm] at hμ
  refine ⟨μ, ?_⟩
  have h2 : ((suCongr c.K a : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6)) :
      GL (Fin 6) c.K) = (a : GL (Fin 6) c.K) := rfl
  rw [h2] at hμ
  have h3 : (a : GL (Fin 6) c.K) = c.Q⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) μ * c.Q := by
    rw [hμ]
    group
  rw [h3, ← TypeA.PGLTor.scalar_mul_comm μ c.Q⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_scalar_of_fr_eq (c : GGQ2S08RoSix Bs L x)
    {a a' : ↥(LargeEvenSUGroup (Fin 6) c.K 2)} (h : c.fr a = c.fr a') :
    ∃ μ : c.Kˣ, (a' : GL (Fin 6) c.K) = Matrix.GeneralLinearGroup.scalar (Fin 6) μ * a := by
  have h1 : c.fr (a' * a⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := c.exists_scalar_of_fr_eq_one h1
  refine ⟨μ, ?_⟩
  rw [← hμ, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

@[expose] noncomputable def diagConj (c : GGQ2S08RoSix Bs L x) (σ : Fin 6 → c.Kˣ)
    (u : ↥(LargeEvenSUGroup (Fin 6) c.K 2)) : ↥(LargeEvenSUGroup (Fin 6) c.K 2) :=
  ⟨diagHom 6 σ * u * (diagHom 6 σ)⁻¹, by
    have h := InndiagSU.semilin_mem (USixTwo.fieldDataFour c.hK)
      (TableBUD.diagHom_mem_primeFormUnitary (USixTwo.fieldDataFour c.hK) (c.norm_one σ)) 1
      (suCongr c.K u)
    rw [map_one, MulAut.one_apply] at h
    have h' : diagHom 6 σ * (u : GL (Fin 6) c.K) * (diagHom 6 σ)⁻¹ ∈
        ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6 := h
    exact (SetLike.ext_iff.mp (su6_eq c.K) _).mpr h'⟩

theorem coe_diagConj (c : GGQ2S08RoSix Bs L x) (σ : Fin 6 → c.Kˣ)
    (u : ↥(LargeEvenSUGroup (Fin 6) c.K 2)) :
    ((c.diagConj σ u : ↥(LargeEvenSUGroup (Fin 6) c.K 2)) : GL (Fin 6) c.K) =
      diagHom 6 σ * u * (diagHom 6 σ)⁻¹ := rfl

theorem act_fr (c : GGQ2S08RoSix Bs L x) (b : Bs) (u : ↥(LargeEvenSUGroup (Fin 6) c.K 2)) :
    c.act b (c.fr u) = c.fr (c.diagConj (c.diag b) u) := by
  rw [fr_apply, fr_apply]
  exact (c.frameDiag_diag b).apply (suCongr c.K u) (suCongr c.K (c.diagConj (c.diag b) u)) rfl

theorem conjB_mem_stabPre (c : GGQ2S08RoSix Bs L x) (w : Fin 6) (b : Bs) {l : ↥L}
    (hl : l ∈ c.stabPre w) : c.conjB b l ∈ c.stabPre w := by
  change c.piL (c.conjB b l) ∈ c.stabImg w
  obtain ⟨u, hu, hul⟩ := (show c.piL l ∈ c.stabImg w from hl)
  rw [piL_conjB, ← hul, act_fr]
  exact ⟨_, ggQ2s08r6_diag_conj_mem_stab (c.diag b) hu (c.coe_diagConj _ u), rfl⟩

theorem stabPre_map_conjB (c : GGQ2S08RoSix Bs L x) (w : Fin 6) (b : Bs) :
    (c.stabPre w).map (c.conjB b).toMonoidHom = c.stabPre w := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨l, hl, rfl⟩
    exact c.conjB_mem_stabPre w b hl
  · intro l hl
    refine ⟨c.conjB b⁻¹ l, c.conjB_mem_stabPre w b⁻¹ hl, ?_⟩
    change (c.conjB b * c.conjB b⁻¹) l = l
    rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem conjB_mem_compL (c : GGQ2S08RoSix Bs L x) (w : Fin 6) (b : Bs) {q : ↥L}
    (hq : q ∈ c.compL w) : c.conjB b q ∈ c.compL w := by
  have h : (c.compL w).map (c.conjB b).toMonoidHom = c.compL w := by
    rw [compL, Subgroup.map_commutator, stabPre_map_conjB]
  rw [← h]
  exact ⟨q, hq, rfl⟩

theorem le_normalizer_comp (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    Bs ≤ Subgroup.normalizer (c.comp w : Set G) := by
  have key : ∀ b : Bs, ∀ g : G, g ∈ c.comp w → (b : G) * g * (b : G)⁻¹ ∈ c.comp w := by
    rintro b _ ⟨q, hq, rfl⟩
    refine ⟨c.conjB b q, c.conjB_mem_compL w b hq, ?_⟩
    exact e6QTwoBstarConjAction_apply c.hNL b q
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key ⟨b, hb⟩ g, fun hg => ?_⟩
  have h := key ⟨b, hb⟩⁻¹ _ hg
  simp only [Subgroup.coe_inv, inv_inv] at h
  rwa [show b⁻¹ * (b * g * b⁻¹) * b = g by group] at h

theorem compL_le_stabPre (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : c.compL w ≤ c.stabPre w :=
  Subgroup.commutator_le.mpr fun a ha b hb =>
    (c.stabPre w).mul_mem ((c.stabPre w).mul_mem ((c.stabPre w).mul_mem ha hb)
      ((c.stabPre w).inv_mem ha)) ((c.stabPre w).inv_mem hb)

theorem conjB_eq_of_const (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {b : Bs}
    (hb : ∀ i i', i ≠ w → i' ≠ w → c.diag b i = c.diag b i') (q : ↥(c.compL w)) :
    c.conjB b q = q := by
  have hH : commutator ↥(c.compL w) = ⊤ := (c.compL_quasisimple w).1
  have heq := NbrLangTypeA.eq_of_mul_mem_center hH
    (f₁ := (c.compL w).subtype) (f₂ := (c.conjB b).toMonoidHom.comp (c.compL w).subtype)
    (fun q => by
      rw [← c.piL_ker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
      change c.piL q = c.piL (c.conjB b q)
      rw [piL_conjB]
      obtain ⟨u, hu, hul⟩ := (show c.piL q ∈ c.stabImg w from c.compL_le_stabPre w q.2)
      rw [← hul, act_fr]
      congr 1
      apply Subtype.ext
      rw [coe_diagConj]
      have hcomm := ggQ2s08r6_stab_commute c.hK hu (t := c.diag b) hb
      rw [← hcomm, mul_inv_cancel_right])
  have h := congrArg (fun f => f q) heq
  exact h.symm

theorem comp_le_centralizer_of_const (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {b : Bs}
    (hb : ∀ i i', i ≠ w → i' ≠ w → c.diag b i = c.diag b i') :
    c.comp w ≤ Subgroup.centralizer ({x, (b : G)} : Set G) := by
  rintro _ ⟨q, hq, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro h (rfl | rfl)
  · exact Subgroup.mem_centralizer_iff.mp (c.hLx q.2) h rfl
  · have h1 := c.conjB_eq_of_const w hb ⟨q, hq⟩
    have h2 := e6QTwoBstarConjAction_apply c.hNL b q
    have h3 : (b : G) * (q : G) * (b : G)⁻¹ = q := by
      rw [← h2]
      exact congrArg Subtype.val h1
    calc (b : G) * (q : G) = (b : G) * (q : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (q : G) * (b : G) := by rw [h3]

theorem conj_mem_stabPre_of_commute (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {b : Bs}
    (hb2 : ∀ i i', i ≠ w → i' ≠ w → c.diag b i = c.diag b i')
    (hb3 : ∀ i, i ≠ w → c.diag b i ≠ c.diag b w) {n : ↥L} (hn : c.conjB b n = n) {l : ↥L}
    (hl : l ∈ c.stabPre w) : n * l * n⁻¹ ∈ c.stabPre w := by
  obtain ⟨v, hv⟩ := c.fr_surjective (c.piL n)
  have hfix : c.fr v = c.fr (c.diagConj (c.diag b) v) := by
    rw [← act_fr, hv, ← piL_conjB, hn]
  obtain ⟨μ, hμ⟩ := c.exists_scalar_of_fr_eq hfix
  rw [coe_diagConj] at hμ
  have hDv : diagHom 6 (c.diag b) * (v : GL (Fin 6) c.K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) μ * (v : GL (Fin 6) c.K) * diagHom 6 (c.diag b) := by
    rw [← hμ]
    group
  obtain ⟨-, hcol⟩ := ggQ2s08r6_col_of_conj_eq_smul hb2 hb3 hDv
  obtain ⟨u, hu, hul⟩ := (show c.piL l ∈ c.stabImg w from hl)
  change c.piL (n * l * n⁻¹) ∈ c.stabImg w
  rw [map_mul, map_mul, map_inv, ← hv, ← hul, ← map_inv, ← map_mul, ← map_mul]
  exact ⟨_, ggQ2s08r6_conj_mem_stab_of_col hcol hu, rfl⟩

theorem conj_mem_compL_of_commute (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {b : Bs}
    (hb2 : ∀ i i', i ≠ w → i' ≠ w → c.diag b i = c.diag b i')
    (hb3 : ∀ i, i ≠ w → c.diag b i ≠ c.diag b w) {n : ↥L} (hn : c.conjB b n = n) {q : ↥L}
    (hq : q ∈ c.compL w) : n * q * n⁻¹ ∈ c.compL w := by
  have hle : (c.stabPre w).map (MulAut.conj n).toMonoidHom ≤ c.stabPre w := by
    rintro _ ⟨l, hl, rfl⟩
    exact c.conj_mem_stabPre_of_commute w hb2 hb3 hn hl
  have h : (c.compL w).map (MulAut.conj n).toMonoidHom ≤ c.compL w := by
    rw [compL, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h ⟨q, hq, rfl⟩

theorem comp_subnormal (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {b : Bs}
    (hb2 : ∀ i i', i ≠ w → i' ≠ w → c.diag b i = c.diag b i')
    (hb3 : ∀ i, i ≠ w → c.diag b i ≠ c.diag b w) :
    IsSubnormal (c.comp w) (Subgroup.centralizer ({x, (b : G)} : Set G)) := by
  set C := Subgroup.centralizer ({x, (b : G)} : Set G) with hC
  have hCx : C ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (by simp)
  have hle : c.comp w ≤ L ⊓ C := le_inf (c.comp_le w) (c.comp_le_centralizer_of_const w hb2)
  refine IsSubnormal.step hle ⟨fun a ha g => ?_⟩ (IsSubnormal.inf_of_le c.hLsn hCx)
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  obtain ⟨q, hq, hqa⟩ := ha
  have hgL : (g : G) ∈ L := g.2.1
  have hgb : (b : G) * g = g * b := by
    have := Subgroup.mem_centralizer_iff.mp g.2.2 (b : G) (by simp)
    exact this
  have hn : c.conjB b ⟨g, hgL⟩ = ⟨g, hgL⟩ := by
    apply Subtype.ext
    rw [e6QTwoBstarConjAction_apply]
    change (b : G) * g * (b : G)⁻¹ = g
    rw [hgb, mul_inv_cancel_right]
  have h := c.conj_mem_compL_of_commute w hb2 hb3 hn hq
  refine ⟨_, h, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, MulMemClass.coe_mul,
    InvMemClass.coe_inv]
  rw [← hqa]
  rfl

theorem three_dvd_card_comp (c : GGQ2S08RoSix Bs L x) (w : Fin 6) : 3 ∣ Nat.card ↥(c.comp w) := by
  have h1 : Nat.card ↥(c.comp w) = Nat.card ↥(c.compL w) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have h2 : Nat.card ↥(c.stabImg w) ∣ Nat.card ↥(c.compL w) := by
    have hmap := ggQ2s08r6_map_comm_comap c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
    rw [← hmap]
    exact Subgroup.card_map_dvd _ _
  have h3 : Nat.card ↥(c.stabImg w) = Nat.card ↥(ggQ2s08r6Stab c.K w) :=
    (Nat.card_congr (c.stabEquiv w).toEquiv).symm
  rw [h1]
  exact (ggQ2s08r6_three_dvd_card_stab c.hK w).trans (h3 ▸ h2)

theorem comp_pComponent (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {b : Bs}
    (hb2 : ∀ i i', i ≠ w → i' ≠ w → c.diag b i = c.diag b i')
    (hb3 : ∀ i, i ≠ w → c.diag b i ≠ c.diag b w) :
    LargeEvenPComponent 3 (Subgroup.centralizer ({x, (b : G)} : Set G)) (c.comp w) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := c.comp_le_centralizer_of_const w hb2
  exact (ggLargeEvenPComponent_iff 3 _ _).mpr ⟨hle,
    isPComponent_subgroupOf_of_isComponentOf_of_dvd
      ⟨hle, c.comp_subnormal w hb2 hb3, c.comp_quasisimple w⟩ (c.three_dvd_card_comp w)⟩

end GGQ2S08RoSix

end CFSG.StandardType

end
