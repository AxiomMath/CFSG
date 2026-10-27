module

public import CFSG.Quasithin.MS93.S5A55X

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512F

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem finrank_fixSp_le_two_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {Q' : Subgroup G} (hQM : Q' ≤ M)
    (hlarge : 2 ^ k < (Subgroup.centralizer (Q' : Set G)).relIndex (Uq M T L)) :
    Module.finrank F (MSP.fixSp ((Q'.subgroupOf M).map a)) ≤ 2 := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have h1 := S5B.relIndex_centralizer_mul_card h hlift c hQM
  rw [MSP.card_V4, hFq, Module.natCard_eq_pow_finrank (K := F), hFq] at h1
  by_contra hlt
  push Not at hlt
  have hq : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  have h3 : (2 ^ k) ^ 3 ≤ (2 ^ k) ^ Module.finrank F (MSP.fixSp ((Q'.subgroupOf M).map a)) :=
    Nat.pow_le_pow_right (by omega) hlt
  have h4 : 2 ^ k * (2 ^ k) ^ 3 < (Subgroup.centralizer (Q' : Set G)).relIndex (Uq M T L) *
      (2 ^ k) ^ Module.finrank F (MSP.fixSp ((Q'.subgroupOf M).map a)) :=
    Nat.mul_lt_mul_of_lt_of_le hlarge h3 (by positivity)
  rw [h1] at h4
  have : 2 ^ k * (2 ^ k) ^ 3 = (2 ^ k) ^ 4 := by ring
  omega

theorem card_uq_inf_centralizer_le_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {Q' : Subgroup G} (hQM : Q' ≤ M)
    (hlarge : 2 ^ k < (Subgroup.centralizer (Q' : Set G)).relIndex (Uq M T L)) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (Q' : Set G)) ≤ (2 ^ k) ^ 3 := by
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  rw [S5.card_uq_inf_centralizer h hd hQM]
  have hdim := finrank_fixSp_le_two_M h hd hQM hlarge
  have h1 : Nat.card (MSP.fixSp (S5.imSp a Q')) ≤ (2 ^ k) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hFq]
    exact Nat.pow_le_pow_right (Nat.two_pow_pos k) hdim
  have h2 := (sp4Lift_holds G M T L h k F _ _ a hd).1
  calc Nat.card (MSP.fixSp (S5.imSp a Q')) *
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ (2 ^ k) ^ 2 * 2 ^ k :=
        Nat.mul_le_mul h1 h2
    _ = (2 ^ k) ^ 3 := by ring

theorem isPGroup_of_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M)
    (hE2 : IsPGroup 2 ((imM h.le E₀).map (MulAut.conj g).toMonoidHom)) : IsPGroup 2 E₀ := by
  have e1 : ↥E₀ ≃* ↥(imM h.le E₀) := by
    refine (Subgroup.subgroupOfEquivOfLe hE₀M).symm.trans ?_
    exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
  have e2 : ↥(imM h.le E₀) ≃* ↥((imM h.le E₀).map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
  exact hE2.of_equiv (e1.trans e2).symm

theorem card_uSub_inf_centralizer_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {Q' : Subgroup (puAmalgam h.le).Universal}
    (hQ : Q' ≤ stab _ δ)
    (hlarge : 2 ^ k < (Subgroup.centralizer (Q' : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ)) :
    Nat.card ↥(S5.uSub h.le L δ ⊓
      Subgroup.centralizer (Q' : Set (puAmalgam h.le).Universal)) ≤ (2 ^ k) ^ 3 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨Q₀, hQ₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hQ
  rw [S5B.relIndex_centralizer_smul h g hQ₀M] at hlarge
  rw [S5B.uSub_inf_centralizer_smul h g hQ₀M,
    Subgroup.card_map_of_injective (MulAut.conj g).injective,
    S5B.card_imM h.le (inf_le_left.trans (Uq_le h.L_le))]
  exact card_uq_inf_centralizer_le_M h hd hQ₀M hlarge

end S512F

end CFSG.Quasithin.MS93
