module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimAction
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover
open CFSG.StandardType.TableBUE CFSG.StandardType.UnitTB CFSG.StandardType.LineU

variable {F : Type} [Field F] {f d : ℕ}

theorem blockExt_injective (S : Finset (Fin d)) :
    Function.Injective (blockExt (K := F) S) := by
  intro M N h
  have := congrArg (blockRes (K := F) S) h
  simpa only [blockRes_blockExt] using this

theorem mem_unitarySU_of_blockExt_mem (h : UnitaryFieldData 2 f F)
    {S : Finset (Fin d)} {A : GL (Fin S.card) F}
    (hA : Units.map (blockExtHom (K := F) S) A ∈ unitarySU 2 f F d) :
    A ∈ unitarySU 2 f F S.card := by
  rw [mem_unitarySU_iff h] at hA ⊢
  obtain ⟨hdet, huni⟩ := hA
  have hcoe : ((Units.map (blockExtHom (K := F) S) A : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) =
      blockExt S (A : Matrix (Fin S.card) (Fin S.card) F) := rfl
  constructor
  · rw [hcoe, det_eq_det_blockRes (isBlockOn_blockExt (S := S) (K := F)
      (N := (A : Matrix (Fin S.card) (Fin S.card) F))), blockRes_blockExt] at hdet
    exact hdet
  · rw [hcoe, ← blockExt_map_transpose (S := S)
      (N := (A : Matrix (Fin S.card) (Fin S.card) F)) h.bar, ← blockExt_mul,
      ← blockExt_one (S := S) (K := F)] at huni
    have h1 : ((A : Matrix (Fin S.card) (Fin S.card) F).map h.bar)ᵀ *
        (A : Matrix (Fin S.card) (Fin S.card) F) = 1 :=
      blockExt_injective S huni
    simpa only [Matrix.map_apply] using h1

theorem blockExt_conj_diagonal {S : Finset (Fin d)} {D : GL (Fin d) F}
    {t : Fin d → F}
    (hD : (D : Matrix (Fin d) (Fin d) F) = diagonal t)
    (M : Matrix (Fin S.card) (Fin S.card) F) :
    (D : Matrix (Fin d) (Fin d) F) * blockExt S M *
      ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
    blockExt S (diagonal (fun a => t (S.equivFin.symm a)) * M *
      diagonal (fun a => (t (S.equivFin.symm a))⁻¹)) := by
  rw [hD, LineU.coe_inv_diag hD]
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [blockExt, dif_pos hi, dif_pos hj, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Equiv.symm_apply_apply, Subtype.coe_mk]
    · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [blockExt, dif_pos hi, dif_neg hj, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [blockExt, dif_neg hi, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, mul_one]
      exact mul_inv_cancel₀ (LineU.diag_ne_zero_of_eq hD i)
    · simp [hij]

theorem exists_diagHom_mem_normalizer_block (h : UnitaryFieldData 2 f F)
    {S : Finset (Fin d)} {D : GL (Fin d) F} {t : Fin d → F}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 f F d : Set (GL (Fin d) F)))
    (hDt : (D : Matrix (Fin d) (Fin d) F) = diagonal t) :
    ∃ D' : GL (Fin S.card) F,
      D' ∈ Subgroup.normalizer (unitarySU 2 f F S.card : Set (GL (Fin S.card) F)) ∧
      (D' : Matrix (Fin S.card) (Fin S.card) F) =
        diagonal (fun a => t (S.equivFin.symm a)) := by
  classical
  have hne : ∀ k, t k ≠ 0 := fun k => LineU.diag_ne_zero_of_eq hDt k
  let τ : Fin S.card → Fˣ := fun a => Units.mk0 (t (S.equivFin.symm a)) (hne _)
  let D' : GL (Fin S.card) F := diagHom (S.card) τ
  have hD'mat : (D' : Matrix (Fin S.card) (Fin S.card) F) =
      diagonal (fun a => t (S.equivFin.symm a)) := by
    rw [show D' = diagHom (S.card) τ from rfl, coe_diagHom]
    rfl
  refine ⟨D', ?_, hD'mat⟩
  have hconj : ∀ M : Matrix (Fin S.card) (Fin S.card) F,
      (D : Matrix (Fin d) (Fin d) F) * blockExt S M *
        ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      blockExt S (diagonal (fun a => t (S.equivFin.symm a)) * M *
        diagonal (fun a => (t (S.equivFin.symm a))⁻¹)) := fun M =>
    blockExt_conj_diagonal hDt M
  have hblockExt_conj : ∀ y : ↥(unitarySU 2 f F S.card),
      blockExt S (((D' * y * D'⁻¹ : GL (Fin S.card) F) :
        Matrix (Fin S.card) (Fin S.card) F)) =
      (D : Matrix (Fin d) (Fin d) F) *
        blockExt S ((y : GL (Fin S.card) F) : Matrix (Fin S.card) (Fin S.card) F) *
        ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    intro y
    have hy : ((D' * y * D'⁻¹ : GL (Fin S.card) F) :
        Matrix (Fin S.card) (Fin S.card) F) =
        diagonal (fun a => t (S.equivFin.symm a)) *
          ((y : GL (Fin S.card) F) : Matrix (Fin S.card) (Fin S.card) F) *
          diagonal (fun a => (t (S.equivFin.symm a))⁻¹) := by
      rw [Units.val_mul, Units.val_mul, hD'mat, LineU.coe_inv_diag hD'mat]
    rw [hy, ← hconj]
  have hfwd : ∀ y : GL (Fin S.card) F, y ∈ unitarySU 2 f F S.card →
      D' * y * D'⁻¹ ∈ unitarySU 2 f F S.card := by
    intro y hy
    apply mem_unitarySU_of_blockExt_mem h
    have hmemd : Units.map (blockExtHom (K := F) S) y ∈ unitarySU 2 f F d :=
      blockExt_mem S h ⟨y, hy⟩
    have hval : Units.map (blockExtHom (K := F) S) (D' * y * D'⁻¹) =
        D * Units.map (blockExtHom (K := F) S) y * D⁻¹ := by
      apply Units.ext
      change blockExt S (((D' * y * D'⁻¹ : GL (Fin S.card) F) :
          Matrix (Fin S.card) (Fin S.card) F)) =
        ((D * Units.map (blockExtHom (K := F) S) y * D⁻¹ : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F)
      rw [Units.val_mul, Units.val_mul]
      change blockExt S (((D' * y * D'⁻¹ : GL (Fin S.card) F) :
          Matrix (Fin S.card) (Fin S.card) F)) =
        (D : Matrix (Fin d) (Fin d) F) *
          blockExt S (y : Matrix (Fin S.card) (Fin S.card) F) *
          ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
      rw [hblockExt_conj ⟨y, hy⟩]
    rw [hval]
    exact (Subgroup.mem_normalizer_iff.mp hD
      (Units.map (blockExtHom (K := F) S) y)).mp hmemd
  have hbwd : ∀ z : GL (Fin S.card) F,
      D' * z * D'⁻¹ ∈ unitarySU 2 f F S.card → z ∈ unitarySU 2 f F S.card := by
    intro z hz
    apply mem_unitarySU_of_blockExt_mem h
    have hmemd : Units.map (blockExtHom (K := F) S) (D' * z * D'⁻¹) ∈ unitarySU 2 f F d :=
      blockExt_mem S h ⟨D' * z * D'⁻¹, hz⟩
    have hDinv : D⁻¹ ∈ Subgroup.normalizer (unitarySU 2 f F d : Set (GL (Fin d) F)) :=
      Subgroup.inv_mem _ hD
    have hval : Units.map (blockExtHom (K := F) S) z =
        D⁻¹ * Units.map (blockExtHom (K := F) S) (D' * z * D'⁻¹) * D := by
      apply Units.ext
      change blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) =
        ((D⁻¹ * Units.map (blockExtHom (K := F) S) (D' * z * D'⁻¹) * D :
          GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
      rw [Units.val_mul, Units.val_mul]
      change blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) =
        ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          blockExt S (((D' * z * D'⁻¹ : GL (Fin S.card) F) :
            Matrix (Fin S.card) (Fin S.card) F)) *
          (D : Matrix (Fin d) (Fin d) F)
      have hz' : ((D' * z * D'⁻¹ : GL (Fin S.card) F) :
          Matrix (Fin S.card) (Fin S.card) F) =
          diagonal (fun a => t (S.equivFin.symm a)) *
            (z : Matrix (Fin S.card) (Fin S.card) F) *
            diagonal (fun a => (t (S.equivFin.symm a))⁻¹) := by
        rw [Units.val_mul, Units.val_mul, hD'mat, LineU.coe_inv_diag hD'mat]
      rw [hz', ← hconj (z : Matrix (Fin S.card) (Fin S.card) F)]
      have hDD : ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          (D : Matrix (Fin d) (Fin d) F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hcalc : ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
            ((D : Matrix (Fin d) (Fin d) F) *
              blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) *
              ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) *
            (D : Matrix (Fin d) (Fin d) F) =
          blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) := by
        calc ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
              ((D : Matrix (Fin d) (Fin d) F) *
                blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) *
                ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) *
              (D : Matrix (Fin d) (Fin d) F)
            = (((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
                (D : Matrix (Fin d) (Fin d) F)) *
                blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) *
                (((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
                  (D : Matrix (Fin d) (Fin d) F)) := by noncomm_ring
          _ = blockExt S (z : Matrix (Fin S.card) (Fin S.card) F) := by
              rw [hDD, one_mul, mul_one]
      exact hcalc.symm
    rw [hval]
    exact (Subgroup.mem_normalizer_iff.mp hDinv
      (Units.map (blockExtHom (K := F) S) (D' * z * D'⁻¹))).mp hmemd
  rw [Subgroup.mem_normalizer_iff]
  intro z
  exact ⟨hfwd z, hbwd z⟩

theorem exists_diagCover_blockSU
    {G : Type} [Group G] {X J Bs B : Subgroup G}
    {φ : ↥(unitarySU 2 f F d) →* X} (hM : UnitTB.Model φ)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t)
    (hBBs : B ≤ Bs) (S : Finset (Fin d))
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp φ))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) :
    ∃ χ : ↥(unitarySU 2 f F S.card) →* ↥J,
      Function.Surjective χ ∧
      (∀ g : ↥(unitarySU 2 f F S.card), χ g = 1 → ∃ c : F,
        ((g : GL (Fin S.card) F) : Matrix (Fin S.card) (Fin S.card) F) =
          diagonal (fun _ => c)) ∧
      (∀ b : B, ∃ t : Fin S.card → F, LineU.ActsDiagU χ (ggGamma J hBJ b) t) := by
  classical
  let U : Subgroup ↥(unitarySU 2 f F d) := TableBUE.blockSU (K := F) (n := f) S
  let φb : ↥(unitarySU 2 f F S.card) →* ↥X := φ.comp (TableBUE.blockExtSU S hM.field)
  let A : Subgroup ↥X := U.map φ
  have hr : φb.range = A := by
    change (φ.comp (TableBUE.blockExtSU S hM.field)).range = U.map φ
    rw [MonoidHom.range_comp, TableBUE.range_blockExtSU]
  have hJ' : J = A.map X.subtype := by
    rw [hJ, ← Subgroup.map_map]
  let χ : ↥(unitarySU 2 f F S.card) →* ↥J :=
    (MulEquiv.subgroupCongr hJ').symm.toMonoidHom.comp
      ((Subgroup.equivMapOfInjective A X.subtype X.subtype_injective).toMonoidHom.comp
        ((MulEquiv.subgroupCongr hr).toMonoidHom.comp φb.rangeRestrict))
  have hχcoe : ∀ s : ↥(unitarySU 2 f F S.card),
      ((χ s : ↥J) : G) = ((φ (TableBUE.blockExtSU S hM.field s) : ↥X) : G) := by
    intro s
    dsimp only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.subgroupCongr_symm_apply]
    change ((Subgroup.equivMapOfInjective A X.subtype X.subtype_injective)
        ((MulEquiv.subgroupCongr hr) (φb.rangeRestrict s)) : ↥(A.map X.subtype)) =
      (X.subtype (φ (TableBUE.blockExtSU S hM.field s)) : G)
    rfl
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨a, rfl⟩ := (MulEquiv.subgroupCongr hJ').symm.surjective j
    obtain ⟨b, rfl⟩ :=
      (Subgroup.equivMapOfInjective A X.subtype X.subtype_injective).surjective a
    obtain ⟨c, rfl⟩ := (MulEquiv.subgroupCongr hr).surjective b
    obtain ⟨s, rfl⟩ := MonoidHom.rangeRestrict_surjective φb c
    exact ⟨s, rfl⟩
  · intro g hg
    have h1 := congrArg (fun x : ↥J => ((x : J) : G)) hg
    rw [hχcoe g] at h1
    have hφg : φ (TableBUE.blockExtSU S hM.field g) = 1 := by
      apply X.subtype_injective
      simpa using h1
    obtain ⟨c, hc⟩ := hM.ker _ hφg
    refine ⟨c, ?_⟩
    have hc' : blockExt S ((g : GL (Fin S.card) F) :
        Matrix (Fin S.card) (Fin S.card) F) = diagonal (fun _ => c) := by
      simpa only [TableBUE.coe_blockExtSU] using hc
    have hres : ((g : GL (Fin S.card) F) : Matrix (Fin S.card) (Fin S.card) F) =
        blockRes S (diagonal (fun _ => c)) := by
      simpa only [TableBUE.blockRes_blockExt] using congrArg (blockRes (K := F) S) hc'
    have hbr : blockRes S (diagonal (fun _ => c)) = diagonal (fun _ => c) := by
      ext a b
      simp only [TableBUE.blockRes, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · have hne : S.equivFin.symm a ≠ S.equivFin.symm b :=
          fun h => hab (S.equivFin.symm.injective h)
        simp [hab, hne]
    rwa [hbr] at hres
  · intro b
    have hbBs : (b : G) ∈ Bs := hBBs b.2
    obtain ⟨t, D, hD, hDt, hact⟩ :=
      hdiag (ggGamma X hN ⟨b, hbBs⟩) ⟨⟨b, hbBs⟩, rfl⟩
    obtain ⟨D', hD', hD'mat⟩ := exists_diagHom_mem_normalizer_block hM.field hD hDt
    refine ⟨fun a => t (S.equivFin.symm a), D', hD', hD'mat, fun s => ?_⟩
    apply Subtype.ext
    rw [ggGamma_coe]
    rw [hχcoe, hχcoe]
    have hbX : b * ((φ (TableBUE.blockExtSU S hM.field s) : ↥X) : G) * (b : G)⁻¹ =
        ((ggGamma X hN ⟨b, hbBs⟩
          (φ (TableBUE.blockExtSU S hM.field s)) : ↥X) : G) := by
      rw [ggGamma_coe]
    rw [hbX, hact]
    have heq : LineU.conjN D hD (TableBUE.blockExtSU S hM.field s) =
        TableBUE.blockExtSU S hM.field (LineU.conjN D' hD' s) := by
      apply Subtype.ext
      apply Units.ext
      rw [LineU.coe_conjN]
      simp only [Units.val_mul, TableBUE.coe_blockExtSU]
      rw [LineU.coe_conjN]
      have hs : ((D' * s * D'⁻¹ : GL (Fin S.card) F) :
          Matrix (Fin S.card) (Fin S.card) F) =
          diagonal (fun a => t (S.equivFin.symm a)) *
            ((s : GL (Fin S.card) F) : Matrix (Fin S.card) (Fin S.card) F) *
            diagonal (fun a => (t (S.equivFin.symm a))⁻¹) := by
        rw [Units.val_mul, Units.val_mul, hD'mat, LineU.coe_inv_diag hD'mat]
      rw [hs]
      exact blockExt_conj_diagonal hDt
        ((s : GL (Fin S.card) F) : Matrix (Fin S.card) (Fin S.card) F)
    rw [heq]

theorem card_range_ggGamma_le
    {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    {f d : ℕ} {X J Bs B : Subgroup G}
    {φ : ↥(unitarySU 2 f F d) →* X} (hM : UnitTB.Model φ)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t)
    (hBBs : B ≤ Bs) (S : Finset (Fin d)) (hS : 3 ≤ S.card)
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp φ))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    {p : ℕ} (hp : p.Prime) (hBp : ∀ b ∈ B, b ^ p = 1) :
    Nat.card (ggGamma J hBJ).range ≤ p ^ (S.card - 1) := by
  obtain ⟨χ, hχs, hχker, hχact⟩ :=
    exists_diagCover_blockSU hM hN hdiag hBBs S hJ hBJ
  have : NeZero p := ⟨hp.ne_zero⟩
  refine LineU.card_le_of_actsDiagU (f := f) hM.field hS hχs hχker
    (ggGamma J hBJ).range ?_ ?_
  · intro a ha
    obtain ⟨b, rfl⟩ := ha
    have hbp : b ^ p = 1 := Subtype.ext (hBp (b : G) b.2)
    rw [← map_pow, hbp, map_one]
  · intro a ha
    obtain ⟨b, rfl⟩ := ha
    exact hχact b

end CFSG.StandardType

end
