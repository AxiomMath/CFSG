module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem isXSectionIso₂_refl {X J C : Subgroup G} (hn : (C.subgroupOf J).Normal)
    (hXC : X ≤ Subgroup.normalizer (C : Set G)) : IsXSectionIso₂ X J C J C := by
  refine ⟨hn, hn, MulEquiv.refl _, ?_⟩
  intro x hx j k hj hk hjk
  rw [MulEquiv.refl_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hjk ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hjk ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hXC hx) _).mp hjk
  convert this using 1
  group

theorem isXSectionIso₂_of_equiv {X A B : Subgroup G} (e : ↥A ≃* ↥B)
    (he : ∀ x ∈ X, ∀ (a : ↥A) (ha : x * (a : G) * x⁻¹ ∈ A),
      ((e ⟨x * (a : G) * x⁻¹, ha⟩ : ↥B) : G) = x * (e a : G) * x⁻¹) :
    IsXSectionIso₂ X A ⊥ B ⊥ := by
  have hnA : ((⊥ : Subgroup G).subgroupOf A).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  have hnB : ((⊥ : Subgroup G).subgroupOf B).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  obtain ⟨qA, hqA⟩ : ∃ q : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A ≃* ↥A,
      ∀ a : ↥A, q (a : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A) = a :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf A)).trans
      QuotientGroup.quotientBot, fun _ => rfl⟩
  obtain ⟨qB, hqB⟩ : ∃ q : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B ≃* ↥B,
      ∀ b : ↥B, q (b : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B) = b :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf B)).trans
      QuotientGroup.quotientBot, fun _ => rfl⟩
  refine ⟨hnA, hnB, (qA.trans e).trans qB.symm, ?_⟩
  intro x hx j k hj hk hjk
  have h1 : e j = k := by
    have := congrArg qB hjk
    rwa [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hqA, hqB] at this
  apply qB.injective
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hqA, hqB]
  apply Subtype.ext
  rw [he x hx j hj, h1]

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem stmt11_0_3_one (h322 : Ch10.TmpL6_3_2_2_two) (h : Hyp11 G T L I n) :
    VM T L I ≤ Subgroup.normalizer (L : Set G) ∧
      IsPrimeReduced 2 ((VM T L I).subgroupOf (Subgroup.normalizer (L : Set G))) := by
  have := h322 G T L I h.fsu
  rwa [fsuVM_eq h, fsuM_eq h] at this

theorem fsuV_eq_VM_or_tiSet (h325 : Stmt3_2_5) (h : Hyp11 G T L I n) :
    fsuV T I = VM T L I ∨
      (fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        IsTISetIn (fsuV T I) (Subgroup.normalizer (L : Set G))) := by
  obtain ⟨-, -, hcases⟩ := h325 G T L I h.fsu (fsuL0_eq h).symm
  rcases hcases with ⟨-, h1⟩ | ⟨h0, -, -, hCL, hTI⟩ | ⟨-, -, ⟨t, ht, htN⟩, hall⟩
  · exact Or.inl h1
  · right
    have hV : fsuV T I = I := h0.symm
    have hVM := fsuV_le_normalizer_L h
    rw [hV] at hVM ⊢
    exact ⟨hCL, hVM, fun g hg hgN => hTI g hg hgN⟩
  · exact Or.inl (hall t ht htN).1.symm

theorem isTISetIn_fsuV (h325 : Stmt3_2_5) (h : Hyp11 G T L I n) :
    IsTISetIn (fsuV T I) (Subgroup.normalizer (L : Set G)) := by
  rcases fsuV_eq_VM_or_tiSet h325 h with hV | ⟨-, hTI⟩
  · refine ⟨fsuV_le_normalizer_L h, fun g hg hgN => absurd ?_ hgN⟩
    rw [hV]
    exact le_normalizer_conjClosure _ _ hg
  · exact hTI

theorem fsuV_eq_VM_of_ne_bot (h325 : Stmt3_2_5) (h : Hyp11 G T L I n)
    (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : fsuV T I = VM T L I := by
  rcases fsuV_eq_VM_or_tiSet h325 h with hV | ⟨hC', -⟩
  · exact hV
  · exact absurd hC' hC

end CFSG.Quasithin.Vol2.Ch11.SecA
