module

public import CFSG.Quasithin.Vol2.Ch11SecD557G
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecD557A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem almostSpecialL3Hyp_of_kindSL3 (hG2 : SecA.FactG2DerivedOrder) (hNat : NatV3Fact)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hSL3 : KindSL3 L (fsuV T I) n)
    (hU : ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))) :
    AlmostSpecialL3Hyp n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := by
  obtain ⟨hcomm, -, -, -, hc⟩ := h1102 G T L I n h
  rcases hc with ⟨K, _, _, hK, he, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
  · exact almostSpecialL3Hyp_of hNat h1102 h1110 h1141 h hV₁ hK he π hπ hU
  · exact (SecA.kind_not_SL3_Sp4 (by have := h.one_lt; omega) hSL3
      ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact (SecA.kind_not_SL3_G2 hG2 h.one_lt hSL3 ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem pCoreOf_le_S₂ {V₁ : Subgroup G}
    (hyp : AlmostSpecialL3Hyp n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)))
    (hTor : TorusFixSL3Fact) (hComm : CommLOneSL3Fact) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hSL3 : KindSL3 L (fsuV T I) n) {x y : G} (hx : x ∈ L) (hy : y ∈ L)
    (hV : fsuV T I = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y) :
    pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      TripleGrp.S₂ (tripleU (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) x y) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := ⟨hyp, D⟩
  refine le_S₂_of_comm St hx hy hV fun u hu z hz => ?_
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  have hH₁ : InH (LOf L V₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G)) :=
    ⟨sup_le (lOf_le_normalizer L V₁) hTG₁, hO2ne⟩
  have hH₁M : ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := fun hle =>
    (h1154 G T L I n V₁ h hV₁).1 ((Subgroup.centralizer_le_normalizer _).trans hle)
  obtain ⟨V₃, hV₃, -⟩ := (h1110 G T L I n h).1 3 (by norm_num) le_rfl
  have hV₃eq : V₃ = fsuV T I := ((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).1 hSL3
  obtain ⟨h5one, h5two, -, -⟩ := h1155 G T L I n V₁ V₃ _ h hV₁ hV₃ hH₁ hH₁M le_rfl
  rw [hV₃eq] at h5one h5two
  have hSO := pCoreOf_le_pCoreOf_normalizer St hTor hComm h1102 h1141 h1143 h1156 h hV₁ hSL3 hx
    hy hV hTG₁ hH₁ hH₁M h5one
  exact h5two (Subgroup.commutator_mem_commutator hu (hSO hz))

end CFSG.Quasithin.Vol2.Ch11.SecD
