module

public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

private theorem sbquot_pCore_subgroupOf (N : Subgroup X) [hN : N.Normal] :
    (CFSG.pCore 2 X).subgroupOf N = CFSG.pCore 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_sSup ⟨Subgroup.normal_subgroupOf,
    (CFSG.pCore_isPGroup (G := X) (p := 2)).comap_subtype⟩) ?_
  have hnorm : (CFSG.Open.pCoreOf 2 N).Normal := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N
    rw [Subgroup.normalizer_eq_top_iff.mpr hN] at h1
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  have hle : CFSG.Open.pCoreOf 2 N ≤ CFSG.pCore 2 X :=
    CFSG.LieType.BorelTits.le_pCore 2 hnorm (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  exact hle ((CFSG.mem_openPCoreOf_iff x).mpr hx)

theorem nonempty_oResidual_quot_equiv :
    Nonempty (↥(oResidual 2 X) ⧸ CFSG.pCore 2 ↥(oResidual 2 X) ≃*
      ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) := by
  have hnorm : (oResidual 2 X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  have hmap : (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    Stage1.Thm6.Prod.map_oResidual _ (QuotientGroup.mk'_surjective _) Nat.prime_two
  let φ : ↥(oResidual 2 X) →* X ⧸ CFSG.pCore 2 X :=
    (QuotientGroup.mk' (CFSG.pCore 2 X)).comp (oResidual 2 X).subtype
  have hrange : φ.range = oResidual 2 (X ⧸ CFSG.pCore 2 X) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hker : φ.ker = CFSG.pCore 2 ↥(oResidual 2 X) := by
    rw [← sbquot_pCore_subgroupOf (oResidual 2 X)]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : X)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem nontrivial_of_isQuasisimple
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) : Nontrivial X := by
  set Y := oResidual 2 (X ⧸ CFSG.pCore 2 X)
  have h1 : Nontrivial (↥Y ⧸ Subgroup.center ↥Y) := hq.2.1.toNontrivial
  have h2 : Nontrivial ↥Y := (QuotientGroup.mk_surjective (s := Subgroup.center ↥Y)).nontrivial
  have h3 : Nontrivial (X ⧸ CFSG.pCore 2 X) := Y.subtype_injective.nontrivial
  exact (QuotientGroup.mk_surjective (s := CFSG.pCore 2 X)).nontrivial

private theorem sbquot_isSimpleGroup_alt {m : ℕ} (hm : 5 ≤ m) :
    IsSimpleGroup (alternatingGroup (Fin m)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)

theorem isQuasisimple_of_equiv_alt {m : ℕ} (hm : 5 ≤ m)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* alternatingGroup (Fin m)) :
    CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) := by
  have hs := sbquot_isSimpleGroup_alt hm
  have hY : IsSimpleGroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) := e.isSimpleGroup
  have hnc' : ∃ a b : alternatingGroup (Fin m), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hcomm : IsMulCommutative (alternatingGroup (Fin m)) := ⟨⟨fun a b => hc a b⟩⟩
    have h3 := (alternatingGroup.isMulCommutative_iff_card_le_three).mp hcomm
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    omega
  obtain ⟨a, b, hab⟩ := hnc'
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩).1

private theorem sbquot_mem_center_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : G} :
    e x ∈ Subgroup.center H ↔ x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · exact e.injective (by rw [map_mul, map_mul]; exact h (e y))
  · obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h z]

private theorem sbquot_mem_subgroupOf_oTwoZIn {G : Type*} [Group G] {L : Subgroup G} (x : ↥L) :
    x ∈ (CFSG.Quasithin.oTwoZIn L).subgroupOf L ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  · intro h
    exact ⟨x, h, rfl⟩

private theorem sbquot_isAltQuotient {G : Type*} [Group G] {L : Subgroup G} {Y : Type*}
    [Group Y] {m : ℕ} (ψ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Y) (f : Y →* alternatingGroup (Fin m))
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.center Y) :
    CFSG.Quasithin.IsAltQuotient L (CFSG.Quasithin.oTwoZIn L) m := by
  refine ⟨(f.comp ψ.toMonoidHom).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    (hf.comp ψ.surjective).comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, sbquot_mem_subgroupOf_oTwoZIn, ← sbquot_mem_center_iff ψ,
    ← hker, MonoidHom.mem_ker]
  rfl

theorem isAltQuotient_of_equiv_alt {m : ℕ} (hm : 5 ≤ m)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* alternatingGroup (Fin m)) :
    CFSG.Quasithin.IsAltQuotient (oResidual 2 X)
      (CFSG.Quasithin.oTwoZIn (oResidual 2 X)) m := by
  obtain ⟨ψ⟩ := nonempty_oResidual_quot_equiv (X := X)
  have hc : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  refine sbquot_isAltQuotient ψ e.toMonoidHom e.surjective ?_
  have hZ : Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have h1 : e x ∈ Subgroup.center (alternatingGroup (Fin m)) := (sbquot_mem_center_iff e).mpr hx
    rw [hc, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (e.injective (by rw [h1, map_one]))
  rw [hZ]
  exact (MonoidHom.ker_eq_bot_iff _).mpr e.injective

theorem isAltQuotient_of_isTripleCover
    (h : Sec4.IsTripleCover ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) (alternatingGroup (Fin 6))) :
    CFSG.Quasithin.IsAltQuotient (oResidual 2 X)
      (CFSG.Quasithin.oTwoZIn (oResidual 2 X)) 6 := by
  obtain ⟨-, ⟨e⟩⟩ := h
  obtain ⟨ψ⟩ := nonempty_oResidual_quot_equiv (X := X)
  refine sbquot_isAltQuotient ψ
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center
      ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  change e (QuotientGroup.mk' _ y) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff y

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
