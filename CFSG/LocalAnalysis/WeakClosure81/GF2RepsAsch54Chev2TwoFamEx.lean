module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoOrder

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoFamCl
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamEx
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbFamF4
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbFamTwE6
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcTwE6Rank

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Open CFSG.LieType.Universal CFSG.AGLEmbedding.ParabHub
  CFSG.ComponentClassification.CatLeaf CFSG.Blueprint.Chevalley
open CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.Tits.GN516
  CFSG.AGLEmbeddingD2.Tits.GN516.Fam CFSG.Timmesfeld
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
  CFSG.SeitzReduction.F4Pilot CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {X : Type} [Group X] {n : ℕ}

theorem hasBQSmall_f4
    (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .F4 n 2 1) : HasBQSmall X := by
  let k := GaloisField 2 1
  have hk2 : Nat.card k = 2 := by
    dsimp [k]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hk4 : Nat.card k ≤ 4 := by omega
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_f4 (f := 1) hm
  refine ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 k), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.Adjoint.f4Datum k,
    CFSG.LieType.Chevalley.weylElement .F4 k,
    CFSG.LieType.Steinberg.Adjoint.torus (τ := .F4) k, π, e, hbq, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨φ, -, hx, hy⟩ := CFSG.LieType.Steinberg.Adjoint.exists_sl2_hom_xPar (K := k)
        (CFSG.LieType.Steinberg.Adjoint.exists_sl2_hom
          (CFSG.LieType.Chevalley.rootOperatorFamily .F4)
          (CFSG.LieType.Steinberg.Adjoint.neighbour_F4 i).choose_spec.1)
      exact not_hasCompFactor_of_sl2_range hO hk4 φ
        (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2
          (CFSG.LieType.Steinberg.Adjoint.f4_isParametrization k) hx hy)
    · intro _ u v hadj
      obtain ⟨hne, hcart⟩ :=
        (CFSG.LieType.Steinberg.Adjoint.f4Datum k).isFiniteType.diagramGraph_adj_iff.1 hadj
      have h01 : ¬ HasCompFactor (rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 0 ⊔
          rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 1) IsCalL0 := by
        obtain ⟨l, -, hr⟩ := exists_sl3_range (K := k) CFSG.RankThree.Chevalley.F4A2Kind.long
        have hr' : l.range = rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 0 ⊔
            rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 1 := by
          simpa [CFSG.RankThree.Chevalley.F4A2Kind.i,
            CFSG.RankThree.Chevalley.F4A2Kind.j] using hr
        exact not_hasCompFactor_of_sl3_range hO (Or.inl hk2) l hr'
      have h10 : ¬ HasCompFactor (rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 1 ⊔
          rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 0) IsCalL0 := by
        rw [sup_comm]
        exact h01
      have h12 : ¬ HasCompFactor (rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 1 ⊔
          rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 2) IsCalL0 := by
        have hr : (b2LeviHom k).range =
            rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 1 ⊔
            rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 2 := by
          rw [range_b2LeviHom, ← levi_one_two_eq_B2Levi, levi_pair, levi_singleton,
            levi_singleton]
        rw [← hr]
        exact not_hasCompFactor_isCalL0_range_Sp4 hO hk2 (b2LeviHom k)
      have h21 : ¬ HasCompFactor (rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 2 ⊔
          rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 1) IsCalL0 := by
        rw [sup_comm]
        exact h12
      have h23 : ¬ HasCompFactor (rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 2 ⊔
          rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 3) IsCalL0 := by
        obtain ⟨l, -, hr⟩ := exists_sl3_range (K := k) CFSG.RankThree.Chevalley.F4A2Kind.short
        have hr' : l.range = rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 2 ⊔
            rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 3 := by
          simpa [CFSG.RankThree.Chevalley.F4A2Kind.i,
            CFSG.RankThree.Chevalley.F4A2Kind.j] using hr
        exact not_hasCompFactor_of_sl3_range hO (Or.inl hk2) l hr'
      have h32 : ¬ HasCompFactor (rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 3 ⊔
          rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 2) IsCalL0 := by
        rw [sup_comm]
        exact h23
      have hrank : (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rank = 4 := rfl
      let u4 : Fin 4 := ⟨u.val, by have h := u.isLt; omega⟩
      let v4 : Fin 4 := ⟨v.val, by have h := v.isLt; omega⟩
      have hne4 : u4 ≠ v4 := by
        intro h
        exact hne (Fin.ext (by simpa [u4, v4] using congrArg Fin.val h))
      have hcart4 : (CFSG.Blueprint.Chevalley.Tag.cartan .F4 u4 v4 : ℤ) ≠ 0 := by
        change (CFSG.Blueprint.Chevalley.Tag.cartan .F4 u v : ℤ) ≠ 0
        exact hcart
      rcases f4_edge_of_adj u4 v4 hne4 hcart4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hu : u = 0 := by
          refine Fin.ext ?_
          simpa [u4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h1
        have hv : v = 1 := by
          refine Fin.ext ?_
          simpa [v4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h2
        rw [hu, hv]
        exact Or.inl h01
      · have hu : u = 1 := by
          refine Fin.ext ?_
          simpa [u4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h1
        have hv : v = 0 := by
          refine Fin.ext ?_
          simpa [v4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h2
        rw [hu, hv]
        exact Or.inl h10
      · have hu : u = 1 := by
          refine Fin.ext ?_
          simpa [u4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h1
        have hv : v = 2 := by
          refine Fin.ext ?_
          simpa [v4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h2
        rw [hu, hv]
        exact Or.inl h12
      · have hu : u = 2 := by
          refine Fin.ext ?_
          simpa [u4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h1
        have hv : v = 1 := by
          refine Fin.ext ?_
          simpa [v4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h2
        rw [hu, hv]
        exact Or.inl h21
      · have hu : u = 2 := by
          refine Fin.ext ?_
          simpa [u4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h1
        have hv : v = 3 := by
          refine Fin.ext ?_
          simpa [v4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h2
        rw [hu, hv]
        exact Or.inl h23
      · have hu : u = 3 := by
          refine Fin.ext ?_
          simpa [u4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h1
        have hv : v = 2 := by
          refine Fin.ext ?_
          simpa [v4, CFSG.Blueprint.Chevalley.Tag.rank] using congrArg Fin.val h2
        rw [hu, hv]
        exact Or.inl h32
  · exact Or.inl (by have h : (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rank = 4 := rfl; omega)

theorem hasBQSmall_e6
    (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .E6 n 2 1) : HasBQSmall X := by
  let k := GaloisField 2 1
  have hk2 : Nat.card k = 2 := by
    dsimp [k]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hk4 : Nat.card k ≤ 4 := by omega
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_e6 (f := 1) hm
  refine ⟨↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup k), inferInstance,
    inferInstance, CFSG.LieType.Steinberg.Minuscule.e6Datum k,
    CFSG.LieType.Steinberg.Minuscule.e6Data_valid.nm k,
    CFSG.LieType.Steinberg.Minuscule.e6Data_valid.torus k, π, e, hbq, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨φ, -, hx, hy⟩ :=
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid.exists_sl2Hom k i
      exact not_hasCompFactor_of_sl2_range hO hk4 φ
        (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2
          (CFSG.LieType.Steinberg.Minuscule.e6Datum_isParametrization k _
            (CFSG.LieType.Steinberg.Minuscule.roots_eq
              CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6)) hx hy)
    · intro _ u v hadj
      obtain ⟨hne, hcart⟩ :=
        (CFSG.LieType.Steinberg.Minuscule.e6Datum k).isFiniteType.diagramGraph_adj_iff.1
          hadj
      have hcases : adjE u.val v.val ∨ adjE v.val u.val := by
        by_contra hn
        exact hcart ((cartan_E6_iff u v hne).2 hn)
      have h' : edgeE (CFSG.Blueprint.Chevalley.Tag.rank .E6) u v ∨
          edgeE (CFSG.Blueprint.Chevalley.Tag.rank .E6) v u := hcases
      refine Or.inl ?_
      rcases h' with h' | h'
      · exact not_hasCompFactor_edge_of_simplyLacedLevis hO (Or.inl hk2)
          (simplyLacedLevis_e6 k) h'
      · rw [sup_comm]
        exact not_hasCompFactor_edge_of_simplyLacedLevis hO (Or.inl hk2)
          (simplyLacedLevis_e6 k) h'
  · exact Or.inl (by
      have h : (CFSG.LieType.Steinberg.Minuscule.e6Datum k).rank = 6 := rfl
      omega)

theorem hasBQSmall_e7
    (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .E7 n 2 1) : HasBQSmall X := by
  let k := GaloisField 2 1
  have hk2 : Nat.card k = 2 := by
    dsimp [k]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hk4 : Nat.card k ≤ 4 := by omega
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_e7 (f := 1) hm
  refine ⟨↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup k), inferInstance,
    inferInstance, CFSG.LieType.Steinberg.Minuscule.e7Datum k,
    CFSG.LieType.Steinberg.Minuscule.e7Data_valid.nm k,
    CFSG.LieType.Steinberg.Minuscule.e7Data_valid.torus k, π, e, hbq, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨φ, -, hx, hy⟩ :=
        CFSG.LieType.Steinberg.Minuscule.e7Data_valid.exists_sl2Hom k i
      exact not_hasCompFactor_of_sl2_range hO hk4 φ
        (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2
          (CFSG.LieType.Steinberg.Minuscule.e7Datum_isParametrization k _
            (CFSG.LieType.Steinberg.Minuscule.roots_eq
              CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7)) hx hy)
    · intro _ u v hadj
      obtain ⟨hne, hcart⟩ :=
        (CFSG.LieType.Steinberg.Minuscule.e7Datum k).isFiniteType.diagramGraph_adj_iff.1
          hadj
      have hcases : adjE u.val v.val ∨ adjE v.val u.val := by
        by_contra hn
        exact hcart ((cartan_E7_iff u v hne).2 hn)
      have h' : edgeE (CFSG.Blueprint.Chevalley.Tag.rank .E7) u v ∨
          edgeE (CFSG.Blueprint.Chevalley.Tag.rank .E7) v u := hcases
      refine Or.inl ?_
      rcases h' with h' | h'
      · exact not_hasCompFactor_edge_of_simplyLacedLevis hO (Or.inl hk2)
          (simplyLacedLevis_e7 k) h'
      · rw [sup_comm]
        exact not_hasCompFactor_edge_of_simplyLacedLevis hO (Or.inl hk2)
          (simplyLacedLevis_e7 k) h'
  · exact Or.inl (by
      have h : (CFSG.LieType.Steinberg.Minuscule.e7Datum k).rank = 7 := rfl
      omega)

theorem hasBQSmall_e8
    (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .E8 n 2 1) : HasBQSmall X := by
  let k := GaloisField 2 1
  have hk2 : Nat.card k = 2 := by
    dsimp [k]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hk4 : Nat.card k ≤ 4 := by omega
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_e8 (f := 1) hm
  refine ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 k), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.Adjoint.e8Datum k,
    CFSG.LieType.Chevalley.weylElement .E8 k,
    CFSG.LieType.Steinberg.Adjoint.torus (τ := .E8) k, π, e, hbq, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨φ, -, hx, hy⟩ := CFSG.LieType.Steinberg.Adjoint.exists_sl2_hom_xPar (K := k)
        (CFSG.LieType.Steinberg.Adjoint.exists_sl2_hom
          (CFSG.LieType.Chevalley.rootOperatorFamily .E8)
          (CFSG.LieType.Steinberg.Adjoint.neighbour_E8 i).choose_spec.1)
      exact not_hasCompFactor_of_sl2_range hO hk4 φ
        (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2
          (CFSG.LieType.Steinberg.Adjoint.e8_isParametrization k) hx hy)
    · intro _ u v hadj
      obtain ⟨hne, hcart⟩ :=
        (CFSG.LieType.Steinberg.Adjoint.e8Datum k).isFiniteType.diagramGraph_adj_iff.1
          hadj
      have hcases : adjE u.val v.val ∨ adjE v.val u.val := by
        by_contra hn
        exact hcart ((cartan_E8_iff u v hne).2 hn)
      have h' : edgeE (CFSG.Blueprint.Chevalley.Tag.rank .E8) u v ∨
          edgeE (CFSG.Blueprint.Chevalley.Tag.rank .E8) v u := hcases
      refine Or.inl ?_
      rcases h' with h' | h'
      · exact not_hasCompFactor_edge_of_simplyLacedLevis hO (Or.inl hk2)
          (simplyLacedLevis_e8 k) h'
      · rw [sup_comm]
        exact not_hasCompFactor_edge_of_simplyLacedLevis hO (Or.inl hk2)
          (simplyLacedLevis_e8 k) h'
  · exact Or.inl (by
      have h : (CFSG.LieType.Steinberg.Adjoint.e8Datum k).rank = 8 := rfl
      omega)

theorem hasBQSmall_twistedE6
    (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .twistedE6 n 2 1) :
    HasBQSmall X := by
  let k := GaloisField 2 2
  let σ : k →+* k := iterateFrobenius k 2 1
  have hk4 : Nat.card k = 4 := by
    dsimp [k]
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hk4le : Nat.card k ≤ 4 := by omega
  have hk : Nat.card k = 2 ^ 2 := by
    dsimp [k]
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hσ : ∀ c, σ c = c ^ 2 := by
    intro c
    dsimp [σ]
    simpa using iterateFrobenius_def 2 1 c
  have hθ : ∀ c, σ (σ c) = c := involutive_of_card_twE6 (q := 2) hk hσ
  let F := fixedSubfield σ
  have hfix : Nat.card ↥F ≤ 4 :=
    (Nat.card_le_card_of_injective (fun x : ↥F => (x : k))
      Subtype.val_injective).trans hk4le
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_twistedE6 (f := 1) hm
  refine ⟨↥(fixedGroup k σ), inferInstance, inferInstance, twistedDatum k σ,
    nHat σ, hHat k σ, π, e, hbq, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have fixedNode : ∀ (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a)
            (i : Fin (Tag.rank .F4)), orbitMap a = i →
            ¬ HasCompFactor (rankOne (twistedDatum k σ).rootGroup i) IsCalL0 := by
          intro a ha i hi
          subst hi
          let φ := slFixedNodeHom σ ha
          have hle := rankOne_le_range_slFixedNodeHom σ ha rfl
          have hcard : Nat.card ↥(rankOne (twistedDatum k σ).rootGroup (orbitMap a)) ≤
              Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
            calc Nat.card ↥(rankOne (twistedDatum k σ).rootGroup (orbitMap a)) ≤
                  Nat.card ↥(φ.range) :=
                  Nat.card_le_card_of_injective (Subgroup.inclusion hle)
                    (Subgroup.inclusion_injective hle)
              _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
                  rw [← Nat.card_congr (MonoidHom.ofInjective
                    (slFixedNodeHom_injective σ ha)).toEquiv]
          have hq : Nat.card F ≤ 4 := hfix
          have hsl2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ≤ 60 := by
            rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
            have hq2 : Nat.card F ^ 2 - 1 ≤ 15 := by
              have := Nat.pow_le_pow_left hq 2
              omega
            calc Nat.card F * (Nat.card F ^ 2 - 1) ≤ 4 * 15 := Nat.mul_le_mul hq hq2
              _ = 60 := by norm_num
          exact not_hasCompFactor_isCalL0_of_natCard_lt hO
            (lt_of_le_of_lt (hcard.trans hsl2) (by norm_num))
      have orbitNode : ∀ {a b : Fin (Tag.rank .E6)}
            (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5))
            {i : Fin (Tag.rank .F4)}, orbitMap a = i →
            ¬ HasCompFactor (rankOne (twistedDatum k σ).rootGroup i) IsCalL0 := by
          intro a b hab i hi
          subst hi
          let φ := slOrbitHom σ hθ hab
          have hle := rankOne_le_range_slOrbitHom σ hθ hab rfl
          have hcard : Nat.card ↥(rankOne (twistedDatum k σ).rootGroup (orbitMap a)) ≤
              Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
            calc Nat.card ↥(rankOne (twistedDatum k σ).rootGroup (orbitMap a)) ≤
                  Nat.card ↥(φ.range) :=
                  Nat.card_le_card_of_injective (Subgroup.inclusion hle)
                    (Subgroup.inclusion_injective hle)
              _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
                  rw [← Nat.card_congr (MonoidHom.ofInjective
                    (slOrbitHom_injective σ hθ hab)).toEquiv]
          have hsl2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = 60 := by
            rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk4]
            norm_num
          exact not_hasCompFactor_isCalL0_of_natCard_lt hO
            (lt_of_le_of_lt (hcard.trans_eq hsl2) (by norm_num))
      have hnodes : ∀ i : Fin (twistedDatum k σ).rank,
          ¬ HasCompFactor (rankOne (twistedDatum k σ).rootGroup i) IsCalL0 := by
        intro i
        fin_cases i
        · exact fixedNode (nd 1) rfl 0 rfl
        · exact fixedNode (nd 3) rfl 1 rfl
        · exact orbitNode (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) rfl
        · exact orbitNode (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) rfl
      exact hnodes
    · intro _ u v hadj
      obtain ⟨hne, hcart⟩ :=
        (twistedDatum k σ).isFiniteType.diagramGraph_adj_iff.1 hadj
      have hfix2 : Nat.card
          (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField σ) = 2 :=
        CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6.card_fixedField
          (θ := σ) (q := 2) hk hσ
      have hX : Nat.card ↥((twistedDatum k σ).rootGroup (Pi.single (nf 1) 1)) ≠
          Nat.card ↥((twistedDatum k σ).rootGroup (Pi.single (nf 2) 1)) := by
        rw [card_rootGroup_one_twE6, card_rootGroup_two_twE6 hθ]
        exact (card_fixedField_lt_twE6 (q := 2) (by norm_num) hk hσ).ne
      have hrank : (twistedDatum k σ).rank = 4 := rfl
      let u4 : Fin 4 := ⟨u.val, by have h := u.isLt; omega⟩
      let v4 : Fin 4 := ⟨v.val, by have h := v.isLt; omega⟩
      have hne4 : u4 ≠ v4 := by
        intro h
        exact hne (Fin.ext (by simpa [u4, v4] using congrArg Fin.val h))
      have hcart4 : (CFSG.Blueprint.Chevalley.Tag.cartan .F4 u4 v4 : ℤ) ≠ 0 := by
        change (CFSG.Blueprint.Chevalley.Tag.cartan .F4 u v : ℤ) ≠ 0
        exact hcart
      rcases twE6_edge_of_adj u4 v4 hne4 hcart4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hu : u = nf 0 := Fin.ext (by simpa [u4, nf] using congrArg Fin.val h1)
        have hv : v = nf 1 := Fin.ext (by simpa [v4, nf] using congrArg Fin.val h2)
        rw [hu, hv]
        refine Or.inl ?_
        obtain ⟨emb, -, h0, h1⟩ := CFSG.ClassicalInvolution.WeakCT.exists_levi01 σ
        have hr : emb.range = rankOne (twistedDatum k σ).rootGroup (nf 0) ⊔
            rankOne (twistedDatum k σ).rootGroup (nf 1) := by
          rw [range_eq_sup_blk_twE6 emb, h0, h1,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_zero,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_one]
        exact not_hasCompFactor_of_sl3_range hO (Or.inl hfix2) emb hr
      · have hu : u = nf 1 := Fin.ext (by simpa [u4, nf] using congrArg Fin.val h1)
        have hv : v = nf 0 := Fin.ext (by simpa [v4, nf] using congrArg Fin.val h2)
        rw [hu, hv]
        refine Or.inl ?_
        obtain ⟨emb, -, h0, h1⟩ := CFSG.ClassicalInvolution.WeakCT.exists_levi01 σ
        have hr : emb.range = rankOne (twistedDatum k σ).rootGroup (nf 0) ⊔
            rankOne (twistedDatum k σ).rootGroup (nf 1) := by
          rw [range_eq_sup_blk_twE6 emb, h0, h1,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_zero,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_one]
        rw [sup_comm]
        exact not_hasCompFactor_of_sl3_range hO (Or.inl hfix2) emb hr
      · have hu : u = nf 1 := Fin.ext (by simpa [u4, nf] using congrArg Fin.val h1)
        have hv : v = nf 2 := Fin.ext (by simpa [v4, nf] using congrArg Fin.val h2)
        rw [hu, hv]
        exact Or.inr (Or.inr hX)
      · have hu : u = nf 2 := Fin.ext (by simpa [u4, nf] using congrArg Fin.val h1)
        have hv : v = nf 1 := Fin.ext (by simpa [v4, nf] using congrArg Fin.val h2)
        rw [hu, hv]
        exact Or.inr (Or.inr hX.symm)
      · have hu : u = nf 2 := Fin.ext (by simpa [u4, nf] using congrArg Fin.val h1)
        have hv : v = nf 3 := Fin.ext (by simpa [v4, nf] using congrArg Fin.val h2)
        rw [hu, hv]
        refine Or.inl ?_
        obtain ⟨emb, -, h0, h1⟩ := CFSG.ClassicalInvolution.WeakCT.exists_levi23 σ hθ
        have hr : emb.range = rankOne (twistedDatum k σ).rootGroup (nf 2) ⊔
            rankOne (twistedDatum k σ).rootGroup (nf 3) := by
          rw [range_eq_sup_blk_twE6 emb, h0, h1,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two σ hθ,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_three σ hθ]
        exact not_hasCompFactor_of_sl3_range hO (Or.inr hk4) emb hr
      · have hu : u = nf 3 := Fin.ext (by simpa [u4, nf] using congrArg Fin.val h1)
        have hv : v = nf 2 := Fin.ext (by simpa [v4, nf] using congrArg Fin.val h2)
        rw [hu, hv]
        refine Or.inl ?_
        obtain ⟨emb, -, h0, h1⟩ := CFSG.ClassicalInvolution.WeakCT.exists_levi23 σ hθ
        have hr : emb.range = rankOne (twistedDatum k σ).rootGroup (nf 2) ⊔
            rankOne (twistedDatum k σ).rootGroup (nf 3) := by
          rw [range_eq_sup_blk_twE6 emb, h0, h1,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two σ hθ,
            ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_three σ hθ]
        rw [sup_comm]
        exact not_hasCompFactor_of_sl3_range hO (Or.inr hk4) emb hr
  · exact Or.inl (by
      have h : (twistedDatum k σ).rank = 4 := rfl
      omega)

theorem exists_bqSmall_g2
    (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .G2 n 2 2) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (w : Fin D.rank → K)
      (H : Fin D.rank → Subgroup K) (π : K →* X) (e : ℕ),
        BorelQuotient D w H π e ∧ BQSmall D ∧ D.rank = 2 := by
  let k := GaloisField 2 2
  have hk4 : Nat.card k = 4 := by
    dsimp [k]
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_g2 (f := 2) hm
  refine ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 k), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.Adjoint.g2Datum k,
    CFSG.LieType.Chevalley.weylElement .G2 k,
    CFSG.LieType.Steinberg.Adjoint.torus (τ := .G2) k, π, e, hbq, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨eL⟩ :=
        CFSG.AGLEmbedding.LeviBlock.nonempty_sl2_mulEquiv_rankOne_g2 (F := k) i
      exact not_hasCompFactor_of_mulEquiv_sl2 hO (by omega) eL.symm
    · intro h
      have hrank : (CFSG.LieType.Steinberg.Adjoint.g2Datum k).rank = 2 := rfl
      omega
  · rfl

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
