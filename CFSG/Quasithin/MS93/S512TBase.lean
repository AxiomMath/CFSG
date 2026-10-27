module

public import CFSG.Quasithin.MS93.S510Tv
public import CFSG.Quasithin.MS93.S5B58Sp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512T

theorem relIndex_sup_of_le_of_comm {Γ : Type*} [Group Γ] {A B H K : Subgroup Γ}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hH : H ≤ A) (hK : K ≤ A)
    (hKB : K ≤ B) : B.relIndex (H ⊔ K) = B.relIndex H := by
  have hn : (B.subgroupOf A).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm g g.2 n n.2, mul_inv_cancel_right]
    rw [e]
    exact hn⟩
  rw [← Subgroup.relIndex_subgroupOf (sup_le hH hK), ← Subgroup.relIndex_subgroupOf hH,
    Subgroup.subgroupOf_sup hH hK,
    ← Subgroup.relIndex_sup_right (H := H.subgroupOf A ⊔ K.subgroupOf A) (K := B.subgroupOf A),
    ← Subgroup.relIndex_sup_right (H := H.subgroupOf A) (K := B.subgroupOf A)]
  congr 1
  rw [sup_assoc, sup_eq_right.mpr (show K.subgroupOf A ≤ B.subgroupOf A from fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hKB (Subgroup.mem_subgroupOf.mp hx)))]

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section NatM

theorem relIndex_eq_pow_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) =
      (2 ^ k) ^ Module.finrank F (MSP.commSp ((E.subgroupOf M).map a)) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hrel := S5B.relIndex_centralizer_mul_card h hlift c hEM
  rw [MSP.card_V4, hFq, Module.natCard_eq_pow_finrank (K := F), hFq,
    S5B.fixSp_eq_perp_commSp] at hrel
  have hperp := MSP.finrank_perp (MSP.commSp ((E.subgroupOf M).map a))
  have hpos : 0 < (2 ^ k) ^ Module.finrank F ↥(MSP.perp (MSP.commSp ((E.subgroupOf M).map a))) :=
    by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hrel, ← pow_add, add_comm, hperp]

theorem commSp_le_fixSp_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) (hRE : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (E : Set G)) :
    MSP.commSp ((E.subgroupOf M).map a) ≤ MSP.fixSp ((E.subgroupOf M).map a) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  intro w hw
  obtain ⟨u, hu, rfl⟩ := S5B.exists_mem_commutator_vec_eq h c hw
  exact (S5B.mem_centralizer_iff_vec h hlift c hEM u).1 (hRE hu)

omit [Fintype F] in
theorem finrank_le_two_of_le_perp {W : Submodule F (MSP.V4 F)} (hW : W ≤ MSP.perp W) :
    Module.finrank F W ≤ 2 := by
  have h1 := Submodule.finrank_mono hW
  have h2 := MSP.finrank_perp W
  omega

theorem relIndex_le_sq_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) (hRE : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (E : Set G)) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ (2 ^ k) ^ 2 := by
  rw [relIndex_eq_pow_M h hd hEM]
  refine Nat.pow_le_pow_right (by positivity) (finrank_le_two_of_le_perp ?_)
  rw [← S5B.fixSp_eq_perp_commSp]
  exact commSp_le_fixSp_M h hd hEM hRE

theorem relIndex_pCoreOf_le_card_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) :
    (pCoreOf 2 M).relIndex E ≤ Nat.card ((E.subgroupOf M).map a) := by
  rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_subgroupOf hEM,
    ← Subgroup.inf_relIndex_right a.ker]
  refine Subgroup.relIndex_le_of_le_left ?_ ?_
  · rintro m ⟨hmk, hmE⟩
    obtain ⟨n, hn⟩ := hE2 ⟨m, Subgroup.mem_subgroupOf.1 hmE⟩
    exact Subgroup.mem_subgroupOf.2 (S5B.mem_pCoreOf_of_ker h hd hmk
      ⟨n, by simpa using congrArg Subtype.val hn⟩)
  · rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite

theorem relIndex_pCoreOf_le_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hEO : ¬ E ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ 2 ^ k) :
    (pCoreOf 2 M).relIndex E ≤ 2 ^ k := by
  have heq : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k :=
    le_antisymm hrel (S5B.relIndex_centralizer_M h hd hEM hE2 hEO).1
  obtain ⟨p, hp, -, -, hxP⟩ := S510.exists_point_of_relIndex h hd hEM heq
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  calc (pCoreOf 2 M).relIndex E ≤ Nat.card ((E.subgroupOf M).map a) :=
        relIndex_pCoreOf_le_card_M h hd hEM hE2
    _ ≤ Nat.card (MSP.xPoint p) := Subgroup.card_le_of_le hxP
    _ = 2 ^ k := by rw [MSP.card_xPoint hp, hFq]

end NatM

section Vertex

theorem relIndex_le_sq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hRE : ⁅S5.uSub h.le L δ, E⁆ ≤ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) :
    (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L δ) ≤
      (2 ^ k) ^ 2 := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M]
  refine relIndex_le_sq_M h hd hE₀M ?_
  have hU : S5.uSub h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj g).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h]
  rw [hU, ← Subgroup.map_commutator, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
    ← imM_commutator h.le (Uq_le h.L_le) hE₀M] at hRE
  have hcomm : ⁅Uq M T L, E₀⁆ ≤ M := commutator_le_of_le (Uq_le h.L_le) hE₀M
  have h1 : imM h.le ⁅Uq M T L, E₀⁆ ≤ imM h.le (⁅Uq M T L, E₀⁆ ⊓
      Subgroup.centralizer (E₀ : Set G)) := by
    rw [imM_inf_centralizer h.le _ hE₀M]
    exact le_inf le_rfl hRE
  exact ((imM_le_imM_iff h.le hcomm).1 h1).trans inf_le_right

theorem relIndex_qv_le_of_relIndex_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) ≤ 2 ^ k) :
    (Qv _ δ).relIndex E ≤ 2 ^ k := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hE₀M]
  exact relIndex_pCoreOf_le_M h hd hE₀M hE₀2 hE₀O hrel

end Vertex

end S512T

end CFSG.Quasithin.MS93
