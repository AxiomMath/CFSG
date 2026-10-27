module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] {K1 : Subgroup G}

theorem exists_benderData {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1)) :
    ∃ (K : Type) (_ : Group K) (ψ : OTwoQuot K1 →* K) (e i : ℕ),
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (OTwoQuot K1) ∧ BenderType K n i e ∧
      ((i = 1 ∧ IsL2Quot n (OTwoQuot K1)) ∨ 2 ≤ i) := by
  rcases hX with hL | ⟨a, rfl, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · obtain ⟨e⟩ := hL
    exact ⟨OTwoQuot K1, inferInstance, MonoidHom.id _, 1, 1, Function.surjective_id, by simp,
      BenderType.linear n hn e, Or.inl ⟨rfl, ⟨e⟩⟩⟩
  · exact ⟨OTwoQuot K1, inferInstance, MonoidHom.id _, 1, 2, Function.surjective_id, by simp,
      BenderType.suzuki a (by omega)
        (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)), Or.inr le_rfl⟩
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    refine ⟨StatedProj (StatedSU 3 (2 ^ n) F), inferInstance,
      (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))).comp
        e.toMonoidHom, e', 3, (QuotientGroup.mk'_surjective _).comp e.surjective, ?_, hB,
      Or.inr (by omega)⟩
    intro x hx
    have hx' : e x ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) :=
      (QuotientGroup.eq_one_iff (e x)).mp (MonoidHom.mem_ker.mp hx)
    have hc : e x ∈ Subgroup.center (StatedSU 3 (2 ^ n) F) := statedSU_scalars_le_center hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e g)
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    refine ⟨_, inferInstance, e.toMonoidHom, e', 3, e.surjective, ?_, hB, Or.inr (by omega)⟩
    intro x hx
    have : x = 1 := e.injective (by simpa using hx)
    rw [this]
    exact Subgroup.one_mem _

end CFSG.Quasithin.SzVB
