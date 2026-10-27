module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem19Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem19A5
public import CFSG.Quasithin.H13.A7EscapeLocal
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem19S

variable {G : Type} [Group G] [Finite G]

theorem exists_solvable_of_A7 {T L V H Y : Subgroup G} (hH : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hKY : oTwoUpper H ≤ Y)
    (hYmax : quasithinIsMaximalLocal T Y)
    (hA7 : Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      alternatingGroup (Fin 7)))
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ X : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) X ∧ Group.IsSolvable ↥X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hYM : ¬ Y ≤ M := fun h => hHs.2.1 (by
    rw [← A7.eq_oTwoUpper_sup_sylow S hHs.1.1]
    exact sup_le (hKY.trans h) hH.normalizes)
  obtain ⟨f⟩ := hA7
  set R := pCoreOf 2 Y with hR
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hRsub : R.subgroupOf Y = CFSG.pCore 2 ↥Y := by
    rw [hR, A7.pCoreOf_eq_map_cfsgPCore]
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have hR2 : IsPGroup 2 R := by
    rw [hR, A7.pCoreOf_eq_map_cfsgPCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := Y)).map Y.subtype
  have hRn : (R.subgroupOf (Y ⊔ (S : Subgroup G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hRY.trans le_sup_left)).2
      ((sup_le Subgroup.le_normalizer hTY).trans A7.normalizer_le_normalizer_pCoreOf_two)
  have : (R.subgroupOf Y).Normal := by
    rw [hRsub]
    infer_instance
  let e : ↥Y ⧸ R.subgroupOf Y ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.quotientMulEquivOfEq hRsub
  let θ : ↥Y ⧸ R.subgroupOf Y →* alternatingGroup (Fin 7) :=
    f.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))).comp
      e.toMonoidHom)
  have hθ : Function.Surjective θ :=
    f.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)
  have hθc : θ.ker ≤ Subgroup.center (↥Y ⧸ R.subgroupOf Y) := by
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) (e x) = 1 := by
      apply f.injective
      rw [map_one]
      exact hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact h1 (e g)
  obtain ⟨H₁, H₂, hT1, h1Y, hT2, h2Y, hs1, hs2, hsup⟩ :=
    (A7.A7_every_normalized_central_cover_has_solvable_Sylow_generators S hTY hRY hR2 hRn θ hθ
      hθc).1
  obtain ⟨X₀, hTX₀, hX₀Y, hX₀s, hX₀M⟩ : ∃ X₀ : Subgroup G, (S : Subgroup G) ≤ X₀ ∧
      X₀ ≤ Y ⊔ (S : Subgroup G) ∧ Group.IsSolvable ↥X₀ ∧ ¬ X₀ ≤ M := by
    by_contra hno
    push Not at hno
    apply hYM
    have h := sup_le (hno H₁ hT1 h1Y hs1) (hno H₂ hT2 h2Y hs2)
    rw [hsup] at h
    exact le_sup_left.trans h
  have hYT : InH (S : Subgroup G) (Y ⊔ (S : Subgroup G)) := ⟨le_sup_right, hYmax.1.2.2.2⟩
  obtain ⟨X, ⟨hXin, hXle, hXM⟩, hXmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup G))
    {X : Subgroup G | InH (S : Subgroup G) X ∧ X ≤ X₀ ∧ ¬ X ≤ M}
    ⟨X₀, inH_of_le S hTX₀ hX₀Y hYT, le_rfl, hX₀M⟩
  refine ⟨X, ⟨hXin, hXM, fun Y' hY' hY'X hY'M => ?_⟩, ?_⟩
  · by_contra hne
    exact hXmin Y' ⟨hY', hY'X.trans hXle, hY'M⟩ (lt_of_le_of_ne hY'X hne)
  · have : Group.IsSolvable ↥X₀ := hX₀s
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXle)

end Lem19S

open Lem19S

theorem lem12219Solvable_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1216 : Stmt12_2_16) (h12218 : Stmt12_2_18) (h1227 : Stmt12_2_7) : Lem12219Solvable := by
  intro G _ _ T L V hH hNE
  obtain ⟨-, -, ⟨H, hHs⟩, -, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at hHs
  by_cases hsolv : Group.IsSolvable ↥H
  · exact ⟨H, hHs, hsolv⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hredV, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    have hne := Lem7.omegaOneCenter_inf_ne_bot hH.sylow.1 hVT hTV hH.irrPlus.2.1
      fun v hv => (S125.isElemAbelian_of_hyp1223 hH).2 v hv
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    refine (Subgroup.centralizer_le ?_).trans (hNE z hz.2 fun h => hz1 (Subtype.ext h))
    rw [Set.singleton_subset_iff]
    exact hz.1
  obtain ⟨⟨-, hCT, hO2, hker⟩, h2⟩ := h1227 G T L V H hH hCZ hHs
  obtain ⟨hLie, Y, hKY, hYmax, -, hcase⟩ := h2 hsolv
  rcases hcase with ⟨-, hA5⟩ | ⟨hA7, -, hTY, -⟩
  · exact (false_of_A5Sum hH hHs hTV (Lem18.not_card_le_four hH hredV) (h1216 G T L V hH hNE)
      (h12218 G T L V hH hNE H hHs) hCT hO2 hker (Lem7.not_le_centralizer_VZ hCZ hHs) hLie
      hA5).elim
  · exact exists_solvable_of_A7 hH hHs hKY hYmax hA7 hTY

end CFSG.Quasithin.H13
