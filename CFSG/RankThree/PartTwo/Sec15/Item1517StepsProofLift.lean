module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTorus
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec16.Item163Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1517

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_card_aBar {A : Subgroup G} {c : G} {L Y : Subgroup G}
    (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) :
    CFSG.Assembly.IsElemAbelian 3
        ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) ∧
      Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 := by
  obtain ⟨-, h9, -⟩ := point_facts h hctx
  exact ⟨CFSG.SectionRank.isElemAbelian_map
      (isElemAbelian_subgroupOf h.toSec13Data.isElemAbelian L) _,
    by rw [card_map_mk_subgroupOf h.toSec13Data.isElemAbelian, h9]⟩

theorem le_normalizer_map_comap {A : Subgroup G} {c : G} {L Y : Subgroup G}
    (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y)
    {Qb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hQb : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.normalizer (Qb : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    A ≤ Subgroup.normalizer
      (((Qb.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map L.subtype :
        Subgroup G) : Set G) := by
  obtain ⟨-, -, hAeq⟩ := point_facts h hctx
  have hKL : (Qb.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map L.subtype ≤ L :=
    Subgroup.map_subtype_le _
  rw [hAeq]
  refine sup_le ?_ ?_
  · refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.toSec13Data.le_centralizer (hKL hx))
  · intro b hb
    obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.mp hb
    have hbAb : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩ ∈
        (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbA)
    have hbN : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.normalizer
        ((Qb.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) : Subgroup ↥L) : Set ↥L) :=
      Subgroup.le_normalizer_comap _ (show _ ∈ _ from hQb hbAb)
    exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hbN)

theorem mem_scriptQ_of_le_L (h142 : Concl142R) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {Q : Subgroup G} (hQL : Q ≤ L) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) : Q ∈ scriptQ A (lB A) :=
  Sec16.mem_scriptQ_of_concl142 (h142 G A c L h) h.toSec13Data.zpowers_mem_omegaA
    ⟨hQL.trans (h.toSec13Data.le_centralizer.trans
      (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩

theorem le_sSup_of_gen {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y)
    (hgen : sSup (invariantPiSubgroups ⊤ ((A.subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) (piCompl 3)) = ⊤) :
    L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  set Ab := (A.subgroupOf L).map π with hAb
  set S := sSup (invariantPiSubgroups L A (piCompl 3)) with hS
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hlift : ∀ Qb ∈ invariantPiSubgroups ⊤ Ab (piCompl 3),
      (Qb.comap π).map L.subtype ∈ invariantPiSubgroups L A (piCompl 3) := by
    intro Qb hQb
    refine ⟨Subgroup.map_subtype_le _, ?_, le_normalizer_map_comap h hctx hQb.2.2⟩
    rw [isPiSubgroup_piCompl_iff Nat.prime_three,
      Subgroup.card_map_of_injective L.subtype_injective]
    refine not_three_dvd_card_comap π
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQb.2.1) ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact hθ3
  set S' := S.subgroupOf L with hS'
  have hθS : θ ≤ S' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine le_sSup (hlift ⊥ (bot_mem_invariantPiSubgroups ⊤ Ab (piCompl 3))) ⟨x, ?_, rfl⟩
    change π x ∈ (⊥ : Subgroup (↥L ⧸ θ))
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hmap : S'.map π = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sSup_le fun Qb hQb => ?_
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ y
    refine ⟨x, ?_, rfl⟩
    change (x : G) ∈ S
    exact le_sSup (hlift Qb hQb) ⟨x, hy, rfl⟩
  have hS'top : S' = ⊤ := by
    have h1 := Subgroup.comap_map_eq π S'
    rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hθS] at h1
    exact h1.symm
  intro l hl
  have hl' : (⟨l, hl⟩ : ↥L) ∈ S' := hS'top ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hl'

theorem le_delta_of_le_sSup (h142 : Concl142R) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hgen : L ≤ sSup (invariantPiSubgroups L A (piCompl 3))) :
    L ≤ delta A (lB A) L := by
  refine hgen.trans (sSup_le fun Q hQ => ?_)
  exact le_delta (mem_scriptQ_of_le_L h142 h hQ.1
    ((isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.2.1) hQ.2.2) hQ.1

end Proof1517

end CFSG.RankThree.PartTwo.Sec15
