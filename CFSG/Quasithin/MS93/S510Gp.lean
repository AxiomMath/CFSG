module

public import CFSG.Quasithin.MS93.S510Loc

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem critR_smul (g : X.Universal) (α α' : Vtx X) :
    critR X (g • α) (g • α') = (critR X α α').map (MulAut.conj g).toMonoidHom := by
  rw [critR, critR, zm_smul, zm_smul, Subgroup.map_commutator]

theorem critA_smul (g : X.Universal) (α α' : Vtx X) :
    critA X (g • α) (g • α') = (critA X α α').map (MulAut.conj g).toMonoidHom := by
  rw [critA, critA, xm_smul, qv_smul, Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem le_normalizer_sup {Γ : Type*} [Group Γ] {K H₁ H₂ : Subgroup Γ}
    (h₁ : K ≤ Subgroup.normalizer (H₁ : Set Γ)) (h₂ : K ≤ Subgroup.normalizer (H₂ : Set Γ)) :
    K ≤ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup Γ) : Set Γ) := by
  refine le_normalizer_of_map_conj_le fun x hx => ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (h₁ hx),
    map_conj_eq_of_mem_normalizer (h₂ hx)]

end General

section PU

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem s33ii2_gp (hX2 : S33.S33X52) (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') {Y : Subgroup (puAmalgam h.le).Universal}
    (hYT : Y ≤ Qv _ (geo _ γ' γ 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ γ γ' : Set (puAmalgam h.le).Universal))
    (hYX : Y ≤ Subgroup.centralizer (XM _ γ : Set (puAmalgam h.le).Universal))
    (hY : ¬ ⁅ZM (puAmalgam h.le) γ', Y⁆ ≤
      ⁅XM (puAmalgam h.le) γ, XM (puAmalgam h.le) γ'⁆ ⊔ ⁅critA (puAmalgam h.le) γ γ', Y⁆)
    (hYZ : ¬ ⁅Y, S5.zHat _ γ γ'⁆ ≤ critR _ γ γ') :
    (Qv _ γ').relIndex (ZM _ γ) = 2 ^ k ∧ Xq M = Uq M T L ⊔ Zq M L ∧
      (⁅⁅critA _ γ γ', Y⁆, Y⁆ = ⊥ →
        Nat.card ↥⁅Y, critA _ γ γ'⁆ = 2 ^ k ∧
          ⁅Y, critA _ γ γ'⁆ ≤ critR _ γ γ' ⊔ stabCenter _ γ') := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  have hc₀ : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') := by
    have := (isCritical_smul _ g⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  have eγ' : γ' = g • (g⁻¹ • γ') := (smul_inv_smul g γ').symm
  have hYY : Y = (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv Y g).symm
  set Y₀ := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY₀
  rw [hYY] at hYT hYR hYX hY hYZ ⊢
  rw [eγ'] at hYT hYR hY hYZ ⊢
  rw [geo_smul, qv_smul, map_conj_le_map_conj_iff] at hYT
  rw [critR_smul, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hYR
  rw [xm_smul, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hYX
  rw [zm_smul, ← Subgroup.map_commutator, xm_smul, xm_smul, ← Subgroup.map_commutator, critA_smul,
    ← Subgroup.map_commutator, ← Subgroup.map_sup, map_conj_le_map_conj_iff] at hY
  rw [S5B.zHat_smul, ← Subgroup.map_commutator, critR_smul, map_conj_le_map_conj_iff] at hYZ
  obtain ⟨h1, h3, h4⟩ := S5B.s33ii2_of' hX2 h hd hXL hc₀ hYT hYR hYX hY hYZ
  refine ⟨?_, h3, fun h5 => ?_⟩
  · rw [qv_smul, zm_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact h1
  · rw [critA_smul, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at h5
    obtain ⟨h6, h7⟩ := h4 h5
    refine ⟨?_, ?_⟩
    · rw [critA_smul, ← Subgroup.map_commutator, S5B.card_map_conj]
      exact h6
    · rw [critA_smul, ← Subgroup.map_commutator, critR_smul, S510.stabCenter_smul,
        ← Subgroup.map_sup, map_conj_le_map_conj_iff]
      exact h7

omit [Fintype F] in
theorem xm_eq_gp_of (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) {γ : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) :
    XM _ γ = S5.uSub h.le L γ ⊔ XM _ γ ⊓ stabCenter _ γ ∧ XM _ γ = ZM _ γ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  have e1 := S5B.xm_eq_uSub_sup h hXU hZc
  have e2 := S5B.xm_eq_zm h hXU hZc
  refine ⟨?_, ?_⟩
  · rw [xm_smul, S5B.uSub_smul h.le hLn, S510.stabCenter_smul,
      ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← Subgroup.map_sup, ← e1]
  · rw [xm_smul, zm_smul, e2]

omit [Fintype F] in
theorem relIndex_bSub_uSub_conj (h : PUHyp M T L) {γ δ : Vtx (puAmalgam h.le)}
    {c : (puAmalgam h.le).Universal} (hc : c ∈ stab _ γ) :
    (S5.bSub h.le L γ).relIndex (S5.uSub h.le L (c • δ)) =
      (S5.bSub h.le L γ).relIndex (S5.uSub h.le L δ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  calc (S5.bSub h.le L γ).relIndex (S5.uSub h.le L (c • δ)) =
      (S5.bSub h.le L (c • γ)).relIndex (S5.uSub h.le L (c • δ)) := by rw [(mem_stab _).1 hc]
    _ = _ := by
      rw [S5B.bSub_smul h.le hLn, S5B.uSub_smul h.le hLn,
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

end PU

end S510

end CFSG.Quasithin.MS93
