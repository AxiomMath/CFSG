module

public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem map_barCentralizer_eq {M : Type*} [Group M] {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (S : Subgroup M) (hS : ∀ z, z ∈ S ↔ inducedAutHom L e ⟨a, ha⟩ z = z) :
    (Sec8.barCentralizer (Subgroup.zpowers a) L).map e.toMonoidHom = S := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_barCentralizer_zpowers_iff ha] at hy
    rw [hS]
    change e (thetaQuotMulAut L (compAction L ⟨a, ha⟩) (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply, hy]
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [SetLike.mem_coe, mem_barCentralizer_zpowers_iff ha]
    have h1 : e (thetaQuotMulAut L (compAction L ⟨a, ha⟩) (e.symm z)) = z := (hS z).mp hz
    calc thetaQuotMulAut L (compAction L ⟨a, ha⟩) (e.symm z) =
        e.symm (e (thetaQuotMulAut L (compAction L ⟨a, ha⟩) (e.symm z))) :=
          (e.symm_apply_apply _).symm
      _ = e.symm z := by rw [h1]

theorem nonempty_barCentralizer_mulEquiv {M M' : Type*} [Group M] [Group M'] {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (ι : M' →* M) (hι : Function.Injective ι)
    (hrange : ∀ z, z ∈ ι.range ↔ inducedAutHom L e ⟨a, ha⟩ z = z) :
    Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃* M') :=
  ⟨(e.subgroupMap _).trans ((MulEquiv.subgroupCongr (map_barCentralizer_eq ha e _ hrange)).trans
    (MonoidHom.ofInjective hι).symm)⟩

theorem mem_range_conj_comp_iff {M M' : Type*} [Group M] [Group M'] (c φ : MulAut M)
    (ι : M' →* M) (hι : ∀ y, y ∈ ι.range ↔ φ y = y) (z : M) :
    z ∈ ((c : M ≃* M).toMonoidHom.comp ι).range ↔ (c * φ * c⁻¹) z = z := by
  have hz : z = c (c⁻¹ z) := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · rintro ⟨x, rfl⟩
    have hx : φ (ι x) = ι x := (hι (ι x)).mp ⟨x, rfl⟩
    have hcc : c⁻¹ (c (ι x)) = ι x := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    change c (φ (c⁻¹ (c (ι x)))) = c (ι x)
    rw [hcc, hx]
  · intro hfix
    have h1 : φ (c⁻¹ z) = c⁻¹ z := by
      apply c.injective
      rw [hfix, ← hz]
    obtain ⟨x, hx⟩ := (hι _).mpr h1
    refine ⟨x, ?_⟩
    change c (ι x) = z
    rw [hx, ← hz]

end CFSG.RankThree.PartTwo.KFacts
