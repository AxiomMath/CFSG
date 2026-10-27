module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapNormalizeBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotBLiftY

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (SwapComponentData oddCoreLift HasBLift centralizerPerfectCore)

section Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C]

theorem perfect_le_map_symm_of_centralizer_eq (e : L ≃* C) {A B D : Subgroup C}
    (hAD : A ≤ centralizer (D : Set C)) (hAA : A ≤ centralizer (A : Set C))
    (hcen : centralizer (B : Set C) = A ⊔ D) {P : Subgroup G} (hPL : P ≤ L)
    (hPX : P ≤ centralizer (((B.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))
    (hPp : ⁅P, P⁆ = P) : P ≤ (D.map e.symm.toMonoidHom).map L.subtype := by
  have hPLX : P ≤ L ⊓ centralizer (((B.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
      Set G) := le_inf hPL hPX
  rw [F4Pilot.inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup] at hPLX
  have hKD : (A.map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (((D.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (F4Pilot.map_map_symm_le_centralizer e hAD)
  have hKK : (A.map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) :=
    F4Pilot.map_map_symm_le_centralizer e hAA
  have hKs : Group.IsSolvable ((A.map e.symm.toMonoidHom).map L.subtype) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (mem_centralizer_iff.1 (hKK b.2) a a.2)
  exact CFSG.SeitzReduction.perfect_le_of_le_sup (hKD.trans (centralizer_le_normalizer _)) hKs hPp
    (by rw [sup_comm]; exact hPLX)

end Generic

section Covers


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem nonempty_swapCover_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hZ : center Kc = ⊥)
    (hφ : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    Nonempty (SwapCover t X D (centralizerPerfectCore X)) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
  obtain ⟨-, -, hDX, -, -, -⟩ := neighbour_data_2E6_X hset hf2 hk hK hσ e htC ht hX hDe
  have hDL : D ≤ L := by rw [hDe]; exact map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hss : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
      Subtype.ext htt, map_one]
  have hτD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩) Kc ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
    ⟨hss, hKc, hne, hcomm, hDKK, hτD, hsyl⟩
  obtain ⟨hBK, hBsup⟩ := hasBLift_neighbour_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe hKc
    ⟨hDKK, Or.inr ⟨hne, hcomm, hZ, hφ⟩⟩
  obtain ⟨hDs, hDperf, hDo⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  have eD := mapSymmEquiv (G := G) e ((su6Levi σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))
  rw [← hDe] at eD
  have hDp : ⁅D, D⁆ = D := isPerfect_iff.mp (Group.IsPerfect.ofSurjective
    (f := eD.toMonoidHom) eD.surjective)
  have hsimple : IsSimpleGroup (D.subgroupOf (centralizer (X : Set G))) :=
    ((subgroupOfEquivOfLe hDX).trans eD.symm).isSimpleGroup
  obtain ⟨eDb⟩ := F4Pilot.nonempty_mulEquiv_map_of_isSimpleGroup
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) hsimple
    (ne_bot_of_isQuasisimple hcomp.2.2)
  obtain ⟨eK⟩ := hφ
  have hOut : Group.IsSolvable (Outer Kc) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (eK.trans (eDb.symm.trans ((subgroupOfEquivOfLe hDX).trans eD.symm)))).2.2 hDo
  obtain ⟨Kc', hperf, hc, hsup, hnorm⟩ :=
    exists_swapFactor_of_swapComponentData htX hdata hOut hBK hBsup
  have hDE : D ≤ centralizerPerfectCore X := F4Pilot.le_centralizerPerfectCore hDp hDX
  obtain ⟨-, -, hWD⟩ := centralizer_thetaTorus_inf_eq hf2 hk hK hσ
  have hPD : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer ({t} : Set G) →
      P ≤ centralizer (X : Set G) → P ≤ D := by
    intro P hPp hPt hPX
    have hOutL := (outer_solvable_and_center_eq_bot_twistedE6 hK σ e).1
    have hPL := std_perfect_le hset.standardSetting hOutL htC ht hPp hPt
    rw [hDe]
    rw [hX] at hPX
    exact perfect_le_map_symm_of_centralizer_eq e
      (subgroupOf_le_centralizer_subgroupOf hWD)
      (subgroupOf_le_centralizer_subgroupOf (thetaTorus_le_centralizer_self _))
      (centralizer_thetaTorus_subgroupOf hf2 hk hK hσ) hPL hPX hPp
  exact nonempty_swapCover_of_decomposition htt hperf hc hsup hnorm hDp hDt hDE hPD

theorem nonempty_swapCover_2E6_Y (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hφ : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    Nonempty (SwapCover t X D (centralizerPerfectCore X)) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe
  obtain ⟨-, -, hDX, -, -, -⟩ := neighbour_data_2E6_Y hset hf2 hk hK hσ e htC ht hX hDe
  have hDL : D ≤ L := by rw [hDe]; exact map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hss : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
      Subtype.ext htt, map_one]
  have hτD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩) Kc ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
    ⟨hss, hKc, hne, hcomm, hDKK, hτD, hsyl⟩
  obtain ⟨hBK, hBsup⟩ := hasBLift_neighbour_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe hKc hDKK
  obtain ⟨hDs, hDperf, hDo⟩ := omegaMinusLevi_subgroupOf_facts hf hK hσ
  have eD := mapSymmEquiv (G := G) e ((omegaMinusLevi σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))
  rw [← hDe] at eD
  have hDp : ⁅D, D⁆ = D := isPerfect_iff.mp (Group.IsPerfect.ofSurjective
    (f := eD.toMonoidHom) eD.surjective)
  have hsimple : IsSimpleGroup (D.subgroupOf (centralizer (X : Set G))) :=
    ((subgroupOfEquivOfLe hDX).trans eD.symm).isSimpleGroup
  obtain ⟨eDb⟩ := F4Pilot.nonempty_mulEquiv_map_of_isSimpleGroup
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) hsimple
    (ne_bot_of_isQuasisimple hcomp.2.2)
  obtain ⟨eK⟩ := hφ
  have hOut : Group.IsSolvable (Outer Kc) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (eK.trans (eDb.symm.trans ((subgroupOfEquivOfLe hDX).trans eD.symm)))).2.2 hDo
  obtain ⟨Kc', hperf, hc, hsup, hnorm⟩ :=
    exists_swapFactor_of_swapComponentData htX hdata hOut hBK hBsup
  have hDE : D ≤ centralizerPerfectCore X := F4Pilot.le_centralizerPerfectCore hDp hDX
  obtain ⟨-, hYD, hYY, -, -⟩ := w1C_centralizer_data hf2 hk hK hσ
  have hPD : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer ({t} : Set G) →
      P ≤ centralizer (X : Set G) → P ≤ D := by
    intro P hPp hPt hPX
    have hOutL := (outer_solvable_and_center_eq_bot_twistedE6 hK σ e).1
    have hPL := std_perfect_le hset.standardSetting hOutL htC ht hPp hPt
    rw [hDe]
    rw [hX] at hPX
    exact perfect_le_map_symm_of_centralizer_eq e hYD hYY
      (centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ) hPL hPX hPp
  exact nonempty_swapCover_of_decomposition htt hperf hc hsup hnorm hDp hDt hDE hPD

theorem false_of_swapRow_2E6_of_components (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (hP : SeitzQ2.SwapPairExclusion (graphFixedRootGroup TwistTag.E6 K σ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hZ : center Kc = ⊥)
    (hφ : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    {Y : Subgroup G} (hY : Y = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htY : t ∈ centralizer (Y : Set G)) {DY : Subgroup G}
    (hDYe : DY = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {KY : Subgroup (centralizer (Y : Set G) ⧸ oddCore (centralizer (Y : Set G)))}
    (hKY : IsComponent KY)
    (hDKY : (DY.subgroupOf (centralizer (Y : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))) ≤
      KY ⊔ KY.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom)
    (hneY : KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom ≠ KY)
    (hcommY : ⁅KY, KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom⁆ = ⊥)
    (hφY : Nonempty (KY ≃* (DY.subgroupOf (centralizer (Y : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))))) :
    False := by
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow
    (show Nat.card K = 2 ^ (2 * f) by rw [hK, ← pow_mul, mul_comm])
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hXc⟩ := nonempty_swapCover_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe hKc hDKK hne
    hcomm hZ hφ
  obtain ⟨hYc⟩ := nonempty_swapCover_2E6_Y hset hf2 hk hK hσ e htC ht hY htY hDYe hKY hDKY hneY
    hcommY hφY
  have hTX : X = modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X) :=
    by rw [hX, (neighbourTorus_X_Y (algebraMap k K)).1]; rfl
  have hTY : Y = modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y) :=
    by rw [hY, (neighbourTorus_X_Y (algebraMap k K)).2]; rfl
  refine false_of_swapRow_2E6 hset hf2 hk hK hσ e hP ht hKt
    (hXc.cast hTX (by rw [hDe]; rfl) (by rw [neighbourCore_def, ← hTX]))
    (hYc.cast hTY (by rw [hDYe]; rfl) (by rw [neighbourCore_def, ← hTY]))

end Covers

end CFSG.SeitzReduction.TwistedE6Pilot
