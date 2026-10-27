module

public import CFSG.Quasithin.MS93.S511SBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_zm_jOff_le_zm_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hc56 : S5.Case56 h (2 ^ k) a δ l)
    (hJ : ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le))) :
    ⁅ZM _ δ, S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)⁆ ≤
      ZM _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hJδ, hl, -, hJl⟩ := hc56
  set J := S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) with hJdef
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδ : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ J := S5B.qv_le_jOff h Nat.one_le_two_pow hα hαβ
  have hJT : J ≤ Qv _ (baseB (puAmalgam h.le)) := S5B.jOff_le_qv h.le L _ _ _
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ hαβ.symm hβδ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  have hJg : J.map (MulAut.conj g).toMonoidHom = J := by
    have := S5B.jOff_smul h.le hLn (2 ^ k) g (baseA (puAmalgam h.le)) (baseB _)
    rw [hgα, hgβ, hJδ] at this
    exact this.symm
  have hquadδ : ⁅S5.uSub h.le L δ, J⁆ ≤ Subgroup.centralizer (J : Set _) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      (S5B.commutator_uSub_le_centralizer_baseA h hd hl hJl)
    rw [Subgroup.map_commutator, ← PU.centralizer_map_mulEquiv, ← S5B.uSub_smul h.le hLn, hgα,
      hJg] at h1
    exact h1
  have hZδ := S5B.zm_eq_zh_sup_uSub h hδ hβδ.symm
  have hδst : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ δ := qv_le_stab_of_adj _ hβδ
  have hUδT : S5.uSub h.le L δ ≤ Qv _ (baseB (puAmalgam h.le)) :=
    (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L δ).trans
      (stab_le_normalizer_zm _ _))).trans ((zm_le_qv_self _ hδ hb0).trans
        (qv_le_qv _ hyp hδ hβδ.symm))
  have hZβc : ZH _ (baseB (puAmalgam h.le)) ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set _) :=
    (PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right
  have hZJ : ⁅ZM _ δ, J⁆ ≤ ⁅S5.uSub h.le L δ, J⁆ := by
    rw [Subgroup.commutator_le]
    intro z hz j hj
    rw [hZδ] at hz
    have hn : ZH _ (baseB (puAmalgam h.le)) ≤
        Subgroup.normalizer (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal) :=
      ((PU.omegaOneCenterOf_le _).trans hδst).trans
        (le_normalizer_commutator (stab_le_normalizer_zm _ _)
          (stab_le_normalizer_puTrans h.le hLn δ))
    have hz' : z ∈ ((ZH _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) *
        (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hz
    obtain ⟨z₀, hz₀, u, hu, rfl⟩ := hz'
    have hc₀ : ∀ t ∈ Qv _ (baseB (puAmalgam h.le)), z₀ * t = t * z₀ := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 (hZβc hz₀) t ht).symm
    have e : ⁅z₀ * u, j⁆ = ⁅u, j⁆ := by
      simp only [commutatorElement_def]
      have h1 := hc₀ (u * j * u⁻¹) (mul_mem (mul_mem (hUδT hu) (hJT hj)) (inv_mem (hUδT hu)))
      calc z₀ * u * j * (z₀ * u)⁻¹ * j⁻¹ = z₀ * (u * j * u⁻¹) * z₀⁻¹ * j⁻¹ := by group
        _ = u * j * u⁻¹ * j⁻¹ := by rw [h1]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu hj
  have hdα : (puAmalgam h.le).treeGraph.dist δ (baseA _) < critDist (puAmalgam h.le) := by
    have := dist_triangle _ δ (baseB (puAmalgam h.le)) (baseA _)
    rw [dist_eq_one_of_adj _ hβδ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    omega
  have hZQ : ZM _ δ ≤ Qv _ (baseA (puAmalgam h.le)) := zm_le_qv_of_dist_lt _ hδ hdα
  have hcomm : ⁅ZM _ δ, J⁆ ≤ Subgroup.centralizer (J : Set _) := hZJ.trans hquadδ
  have hcommZ : ⁅ZM _ δ, J⁆ ≤ ZM _ δ :=
    commutator_le_left_of_le_normalizer (hJT.trans (hδst.trans (stab_le_normalizer_zm _ _)))
  have hX : ⁅ZM _ δ, J⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hZQ (hcommZ hx), ?_⟩, ?_⟩
    · exact Subgroup.centralizer_le hQJ (hcomm hx)
    · exact (isElemAbelian_zm _ hyp hb0 hδ).2 x (hcommZ hx)
  exact (le_inf (le_inf hcommZ hX) hcomm).trans hJ

theorem commutator_le_zm_of_le_sup {A B C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {δ : Vtx X} {Y K₁ K₂ K₃ K : Subgroup X.Universal}
    (h₁ : K₁ ≤ stab X δ) (h₂ : K₂ ≤ stab X δ) (h₃ : K₃ ≤ stab X δ)
    (hY₁ : ⁅Y, K₁⁆ ≤ ZM X δ) (hY₂ : ⁅Y, K₂⁆ ≤ ZM X δ) (hY₃ : ⁅Y, K₃⁆ ≤ ZM X δ)
    (hK : K ≤ K₁ ⊔ K₂ ⊔ K₃) : ⁅Y, K⁆ ≤ ZM X δ := by
  have hn := stab_le_normalizer_zm X δ
  let N : Subgroup X.Universal :=
    { carrier := {t | t ∈ stab X δ ∧ ∀ y ∈ Y, ⁅y, t⁆ ∈ ZM X δ}
      mul_mem' := by
        rintro t₁ t₂ ⟨ht₁, H₁⟩ ⟨ht₂, H₂⟩
        refine ⟨mul_mem ht₁ ht₂, fun y hy => ?_⟩
        have e : ⁅y, t₁ * t₂⁆ = ⁅y, t₁⁆ * (t₁ * ⁅y, t₂⁆ * t₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (H₁ y hy) ((Subgroup.mem_normalizer_iff.1 (hn ht₁) _).1 (H₂ y hy))
      one_mem' := ⟨one_mem _, fun y _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      inv_mem' := by
        rintro t ⟨ht, H⟩
        refine ⟨inv_mem ht, fun y hy => ?_⟩
        have e : ⁅y, t⁻¹⁆ = t⁻¹ * ⁅y, t⁆⁻¹ * t⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hn (inv_mem ht)) _).1 (inv_mem (H y hy)) }
  have hKN : ∀ K' : Subgroup X.Universal, K' ≤ stab X δ → ⁅Y, K'⁆ ≤ ZM X δ → K' ≤ N :=
    fun K' hK' hYK t ht => ⟨hK' ht, fun y hy => hYK (Subgroup.commutator_mem_commutator hy ht)⟩
  have hle : K ≤ N := hK.trans (sup_le (sup_le (hKN _ h₁ hY₁) (hKN _ h₂ hY₂)) (hKN _ h₃ hY₃))
  rw [Subgroup.commutator_le]
  intro y hy t ht
  exact (hle ht).2 y hy

theorem commutator_sup_le_left {H : Type*} [Group H] {A B Q : Subgroup H}
    (hAB : A ≤ Subgroup.normalizer (B : Set H)) (hBQ : B ≤ Subgroup.centralizer (Q : Set H)) :
    ⁅A ⊔ B, Q⁆ ≤ ⁅A, Q⁆ := by
  rw [Subgroup.commutator_le]
  intro y hy q hq
  have hy' : y ∈ ((A ⊔ B : Subgroup H) : Set H) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hy'
  obtain ⟨u, hu, v, hv, huv⟩ := hy'
  have huv' : u * v = y := huv
  rw [← huv', commutatorElement_mul_left_eq_conj_mul]
  have hvq : ⁅v, q⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hBQ hv) q hq).symm
  rw [hvq, mul_one, mul_inv_cancel, one_mul]
  exact Subgroup.commutator_mem_commutator hu hq

theorem commutator_zm_eq_uSub (h32 : S32) (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ ρ) : ⁅ZM _ ρ, E⁆ = ⁅S5.uSub h.le L ρ, E⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono (S5B.uSub_le_zm h.le _) le_rfl)
  rw [Subgroup.commutator_le]
  intro z hz e he
  obtain ⟨u, hu, c, hc, rfl⟩ := S510.exists_mul_of_mem_sup h (zm_le_sup' h32 h53 h hmin hb hd hρ hz)
  have hce : e * c = c * e := S510.commute_of_mem_stabCenter hc (hE he)
  have e1 : ⁅u * c, e⁆ = ⁅u, e⁆ := by
    simp only [commutatorElement_def]
    calc u * c * e * (u * c)⁻¹ * e⁻¹ = u * (c * e) * c⁻¹ * u⁻¹ * e⁻¹ := by group
      _ = u * e * u⁻¹ * e⁻¹ := by rw [← hce]; group
  rw [e1]
  exact Subgroup.commutator_mem_commutator hu he

theorem zm_inf_centralizer_eq_of_uSub (h32 : S32) (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {E E' : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ ρ) (hE' : E' ≤ stab _ ρ)
    (hU : S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E : Set _) =
      S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E' : Set _)) :
    ZM _ ρ ⊓ Subgroup.centralizer (E : Set _) = ZM _ ρ ⊓ Subgroup.centralizer (E' : Set _) := by
  have key : ∀ {K K' : Subgroup (puAmalgam h.le).Universal}, K ≤ stab _ ρ → K' ≤ stab _ ρ →
      S5.uSub h.le L ρ ⊓ Subgroup.centralizer (K : Set _) ≤ Subgroup.centralizer (K' : Set _) →
      ZM _ ρ ⊓ Subgroup.centralizer (K : Set _) ≤ Subgroup.centralizer (K' : Set _) := by
    intro K K' hK hK' hle z ⟨hz, hzK⟩
    obtain ⟨u, hu, c, hc, rfl⟩ :=
      S510.exists_mul_of_mem_sup h (zm_le_sup' h32 h53 h hmin hb hd hρ hz)
    have hcK : c ∈ Subgroup.centralizer (K : Set _) := Subgroup.mem_centralizer_iff.2
      fun y hy => S510.commute_of_mem_stabCenter hc (hK hy)
    have hcK' : c ∈ Subgroup.centralizer (K' : Set _) := Subgroup.mem_centralizer_iff.2
      fun y hy => S510.commute_of_mem_stabCenter hc (hK' hy)
    have huK : u ∈ Subgroup.centralizer (K : Set _) := by
      have e : u = u * c * c⁻¹ := by group
      rw [e]
      exact mul_mem hzK (inv_mem hcK)
    exact mul_mem (hle ⟨hu, huK⟩) hcK'
  refine le_antisymm (le_inf inf_le_left (key hE hE' (hU.le.trans inf_le_right)))
    (le_inf inf_le_left (key hE' hE (hU.ge.trans inf_le_right)))

theorem le_relIndex_zm_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    2 ^ k ≤ (Qv _ γ').relIndex (ZM _ γ) := by
  obtain ⟨g, rfl, -, hc', -⟩ := S510.exists_base_crit h hc
  have key := S511.le_relIndex_zm h hd hc'
  have e1 : γ' = g • (g⁻¹ • γ') := (smul_inv_smul g γ').symm
  rw [e1, qv_smul, zm_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact key

theorem isCritical_of_not_le (h : PUHyp M T L) {α μ ρ : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) (hαμ : (puAmalgam h.le).treeGraph.dist α μ = 2)
    (hαρ : (puAmalgam h.le).treeGraph.dist α ρ + 2 = critDist (puAmalgam h.le))
    (hZ : ¬ ZM _ μ ≤ Qv _ ρ) : IsCritical _ μ ρ := by
  refine ⟨hμ, ?_, hZ⟩
  have h1 := dist_triangle _ μ α ρ
  rw [tdist_comm _ μ α, hαμ] at h1
  by_contra hne
  exact hZ (zm_le_qv_of_dist_lt _ hμ (by omega))

end S511S

end CFSG.Quasithin.MS93
