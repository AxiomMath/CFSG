module

public import CFSG.Milestones.ASVolI.C61.Glue3
public import CFSG.Milestones.ASVolI.C61.HypBlk
public import CFSG.Milestones.ASVolI.C61.Glue1
public import CFSG.Milestones.ASVolI.C61.PAppDA5C61
public import CFSG.Milestones.ASVolI.C61.PAppDK6
public import CFSG.Milestones.ASVolI.C61.PBasic245C61

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

theorem burnsideC56_glue_conjJoin_ne {G : Type} [Group G] [Finite G] {S K : Subgroup G} {t : G}
    (ht : t ∈ S) (hne : conjByElt t K ≠ K) : conjJoin S K ≠ K := by
  intro h
  apply hne
  have hle : conjByElt t K ≤ K := by
    have h1 : conjByElt t K ≤ conjJoin S K := by
      rw [burnsideC56_glue_conjJoin]
      exact le_iSup₂_of_le t ht le_rfl
    rwa [h] at h1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  unfold conjByElt
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]

theorem burnsideC56_glue_case_of {G : Type} [Group G] [Finite G] {H S K₁ : Subgroup G}
    (hjoin : conjJoin S K₁ = oTwoUpper H)
    (h : ((∀ t ∈ S, conjByElt t K₁ = K₁) ∧ oTwoUpper H = K₁ ∧
        ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 5) ∧
        ¬ IsA3Product H (oTwoUpper H) 1 ∧ ¬ IsA3Product H (oTwoUpper H) 2) ∨
      ((∀ t ∈ S, conjByElt t K₁ = K₁) ∧ oTwoUpper H = K₁ ∧ IsAltType K₁ 3 ∧
        ¬ IsA3Product H (oTwoUpper H) 2) ∨
      ((∃ t ∈ S, conjByElt t K₁ ≠ K₁) ∧ IsAltType K₁ 3 ∧ ¬ IsBlock2 H (oTwoUpper H))) :
    burnsideC56_glue_Case H S K₁ := by
  rcases h with ⟨-, hL, h1, h2, h3⟩ | ⟨-, hL, h1, h2⟩ | ⟨⟨t, ht, hne⟩, h1, h2⟩
  · exact Or.inl ⟨hjoin.trans hL, h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨hjoin.trans hL, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨burnsideC56_glue_conjJoin_ne ht hne, h1, h2⟩)

section

theorem burnsideC56_C61_fin_of
    (hA3 : ∀ {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G},
      burnsideC56_CS G T M H S L → IsAltType L 3 → conjJoin S L = L → C61Six T H S L) :
    ∀ (G : Type) [Group G] [Finite G] (H Λ : Subgroup G) [Finite H] [Finite Λ],
      CharTwo H →
      ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))) →
      IsPGroup 2 Λ → IsSylowTwoOf (Λ ⊓ H) H →
      Λ ⊓ H < Λ →
      (∀ T₀ : Subgroup G, T₀ ≠ ⊥ → T₀ ≤ Λ ⊓ H → H ≤ Subgroup.normalizer (T₀ : Set G) →
        Λ ⊓ Subgroup.normalizer (T₀ : Set G) = Λ ⊓ H) →
      ((Λ ⊓ H).relIndex (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) = 2 ∧
        thompsonJ (Λ ⊓ H) = baum (Λ ⊓ H) ∧
        ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
          (baum (Λ ⊓ H) : Set G) = (pCoreOf 2 H : Set G) * (rconj x (pCoreOf 2 H) : Set G)) ∧
      ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
          IsAltType (oTwoUpper H) 5)) ∨
        IsA3Product H (oTwoUpper H) 1 ∨ IsA3Product H (oTwoUpper H) 2) ∧
      (∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
            IsAltType (oTwoUpper H) 3)) →
          AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H)}) ∧
        (∀ n : ℕ, 1 < n → IsBlock2 H (oTwoUpper H) → IsLin2Type (oTwoUpper H) n →
          ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
            IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n) ∧
        (IsBlock2 H (oTwoUpper H) → IsAltType (oTwoUpper H) 3 →
          ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
            IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ 1)) ∧
      (∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) →
        ∃ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H ∧ r ∉ thompsonJ (Λ ⊓ H) ∧
          (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
          AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H), A₁, rconj r A₁}) ∧
      ((pCoreOf 2 H : Set G) =
        (((Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) *
          (pCoreOf 2 (oTwoUpper H) : Set G)) ∧
      (((Λ ⊓ H).relIndex Λ = 2 ∧ thompsonJ (Λ ⊓ H) = thompsonJ Λ ∧
        ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3) →
          Nonempty (↥H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
      (IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3 ∧
        Nonempty (↥H ≃* Equiv.Perm (Fin 4)) ∧ IsDihedralOrSemidihedral Λ) ∨
      (((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) ∧
        thompsonJ (Λ ⊓ H) = thompsonJ (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) ∧
        QuotHas (Λ ⊓ Subgroup.normalizer ((Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G) :
            Subgroup G) : Set G)) (thompsonJ (Λ ⊓ H))
          (fun Y _ => Nonempty (Y ≃* DihedralGroup 4)) ∧
        ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
          ∀ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H → r ∉ thompsonJ (Λ ⊓ H) →
            (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 →
            AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H), A₁, rconj r A₁} →
            Nat.card ↥(Λ ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) : Set G)) ≥
              Nat.card ↥(Λ ⊓ H))) := by
  intro G _ _ H Λ _ _ hc hi hΛ2 hsyl hlt hiv
  obtain ⟨M₀, K₁, -, -, -, hset, hcs, hjoin⟩ := burnsideC56_glue_setup
    (fun hc hi => burnsideC56_hypI_sqtk hc hi) (fun hc hi hT => burnsideC56_hypI_minParabolic hc hi hT)
    (fun hc hi hT => burnsideC56_hypI_uniqueMax hc hi hT) hc hi hΛ2 hsyl hlt hiv
  have hcase : burnsideC56_glue_Case H (Λ ⊓ H) K₁ :=
    burnsideC56_glue_case_of hjoin (burnsideC56_hypI_blocks hc hi hsyl hset.config)
  have hLsh : IsShort2 K₁ := hcs.block.1.1
  have hC : C61Concl Λ H (Λ ⊓ H) K₁ := by
    rcases hcase with ⟨hj, ⟨n, hn, hlin⟩ | h5, -, -⟩ | ⟨hj, h3, -⟩ | ⟨hne, h3, -⟩
    · exact burnsideC56_P.C56.c61_lin2 hcs hj hn hlin
        (fun h5 => CFSG.QuasithinUnique.AppC.not_lin2_of_alt5 hLsh h5 hn hlin)
    · exact burnsideC56_P.AppD.c61_a5 hcs h5 hj
    · have h5 : ¬ IsAltType K₁ 5 := fun h5 => CFSG.QuasithinUnique.AppC.not_alt3_of_alt5 h5 h3
      exact burnsideC56_P.C56.c61_single
        (fun _ hSM hMT h2 => burnsideC56_P.C56.c56_7_single naturalModuleStructure hcs hj
          (Or.inr h3) h5 hSM hMT h2)
        ⟨burnsideC56_P.C56.c61_single_bound naturalModuleStructure hcs hj (Or.inr h3),
          hA3 hcs h3 hj⟩ hcs hj (Or.inr h3) h5
    · exact burnsideC56_P.AppD.c61A3Double hcs h3 hne
  have hr : ((IsAltType K₁ 5 ∧ conjJoin (Λ ⊓ H) K₁ = K₁) ∨
      (IsAltType K₁ 3 ∧ conjJoin (Λ ⊓ H) K₁ ≠ K₁)) → ∃ r ∈ Λ ⊓ H, r ∉ baum (Λ ⊓ H) := by
    rintro (⟨h5, hj⟩ | ⟨h3, hne⟩)
    · obtain ⟨Cf⟩ := burnsideC56_P.AppC.nonempty_cfg hcs hj h5
      exact (burnsideC56_P.AppD.GCfg.ofCfg Cf).exists_r
    · obtain ⟨s, h⟩ := burnsideC56_P.DoubleA3.exists_A3A3 hcs h3 hne
      obtain ⟨C⟩ := burnsideC56_P.AppD.exists_gcfg h
      exact C.exists_r
  exact ⟨burnsideC56_glue_c1 hC, burnsideC56_glue_c2 hcs hjoin hcase,
    burnsideC56_glue_c3 hjoin hcase hC, burnsideC56_glue_c4 hcs hjoin hcase hC hr,
    burnsideC56_glue_c5 hjoin hC, burnsideC56_glue_c6 hcs hjoin hcase hC⟩

end

end CFSG.ASVolI
