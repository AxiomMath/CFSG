module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Defs
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem kS1613Fus : KS1613Fus := by
  intro G _ _ A c L h ⟨φ⟩ h9 y hy hy1 z hz hz1
  have hA := h.isElemAbelian
  have hS3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hA.2 _ (Subgroup.mem_inf.mp g.2).1))⟩
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  have hyS : (⟨y, (Subgroup.mem_inf.mp hy).2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := hy
  have hzS : (⟨z, (Subgroup.mem_inf.mp hz).2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := hz
  set χ := φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hχ
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hE : Nat.card (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) |>.map χ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective χ.injective, Sec13.card_map_eq_of_injOn _ hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hne : ∀ x : ↥L, x ∈ (A ⊓ L).subgroupOf L → (x : G) ≠ 1 →
      χ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) x) ≠ 1 := by
    intro x hxS hx1 hχx
    rw [MulEquiv.map_eq_one_iff] at hχx
    apply hx1
    have hx := hinj hxS (one_mem _) (hχx.trans (map_one _).symm)
    rw [hx]
    rfl
  obtain ⟨n', hn', hn'e⟩ := KFacts.L34.exists_mem_normalizer_conj_eq_of_card_eq_nine hk hE
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hyS)) (hne _ hyS hy1)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzS)) (hne _ hzS hz1)
  have hn'' : χ.symm n' ∈ Subgroup.normalizer
      ((((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
        Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    have h1 : n' ∈ (Subgroup.normalizer
        ((((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
          Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
            Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))).map χ.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq]
      exact hn'
    obtain ⟨m, hm, hmn⟩ := h1
    rw [← hmn]
    simpa using hm
  obtain ⟨n, hnS, hnn⟩ := (Sec13.normalizer_map_mk_eq hS3).le hn''
  refine ⟨(n : G), n.2, ?_⟩
  have hmem : n * ⟨y, (Subgroup.mem_inf.mp hy).2⟩ * n⁻¹ ∈ (A ⊓ L).subgroupOf L :=
    (Subgroup.mem_normalizer_iff.mp hnS _).mp hyS
  have heq : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
        (n * ⟨y, (Subgroup.mem_inf.mp hy).2⟩ * n⁻¹) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨z, (Subgroup.mem_inf.mp hz).2⟩ := by
    apply χ.injective
    simp only [map_mul, map_inv]
    rw [hnn, MulEquiv.apply_symm_apply]
    exact hn'e
  exact congrArg Subtype.val (hinj hmem hzS heq)

end CFSG.RankThree.PartTwo.Sec16.Proof1613
