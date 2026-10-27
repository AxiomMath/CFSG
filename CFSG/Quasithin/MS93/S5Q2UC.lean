module

public import CFSG.Quasithin.MS93.S5Q2X52Cent
public import CFSG.Quasithin.MS93.S5Q2V

public section

namespace CFSG.Quasithin.MS93.S5Q2.UC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
private theorem relIndex_le_two_of_forall {H H' : Subgroup G}
    (hH : ∀ g ∈ H', ∀ g' ∈ H', g ∉ H → g' ∉ H → g⁻¹ * g' ∈ H) : H.relIndex H' ≤ 2 := by
  by_cases htop : H.subgroupOf H' = ⊤
  · rw [Subgroup.relIndex, htop, Subgroup.index_top]
    omega
  · have hex : ∃ x : H', x ∉ H.subgroupOf H' := by
      by_contra hcon
      push Not at hcon
      exact htop (eq_top_iff.mpr fun x _ => hcon x)
    obtain ⟨x, hx⟩ := hex
    have h2 : (H.subgroupOf H').index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨x, fun y => ?_⟩
      by_cases hy : y ∈ H.subgroupOf H'
      · refine Or.inr ⟨hy, fun hyx => hx ?_⟩
        have := (H.subgroupOf H').mul_mem ((H.subgroupOf H').inv_mem hy) hyx
        simpa using this
      · refine Or.inl ⟨?_, hy⟩
        rw [Subgroup.mem_subgroupOf] at hy hx ⊢
        have hyinv : (y : G)⁻¹ ∉ H := fun hh => hy (by simpa using H.inv_mem hh)
        have := hH (y : G)⁻¹ (H'.inv_mem y.2) (x : G) x.2 hyinv hx
        simpa using this
    rw [Subgroup.relIndex, h2]

theorem comm_eq_or (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) {c : G}
    (hc : c ∈ Zq M L) {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M) :
    ⁅c, m₁⁆ = 1 ∨ ⁅c, m₂⁆ = 1 ∨ ⁅c, m₁⁆ = ⁅c, m₂⁆ := by
  have key : ∀ {m : G} (hm : m ∈ M), a ⟨m, hm⟩ ∈ commutator (MSP.Sp4 F) → ⁅c, m⁆ = 1 := by
    intro m hm hmc
    have hcm : m * c = c * m := S5Q2.commute_of_mem_commutator h hd hmc hc
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hcm.symm
  by_cases h₁ : a ⟨m₁, hm₁⟩ ∈ commutator (MSP.Sp4 F)
  · exact Or.inl (key hm₁ h₁)
  by_cases h₂ : a ⟨m₂, hm₂⟩ ∈ commutator (MSP.Sp4 F)
  · exact Or.inr (Or.inl (key hm₂ h₂))
  refine Or.inr (Or.inr ?_)
  have e : m₁ * c * m₁⁻¹ = m₂ * c * m₂⁻¹ := S5Q2.conj_eq_of_not_mem h hd h₁ h₂ hc
  have e' : m₁ * c⁻¹ * m₁⁻¹ = m₂ * c⁻¹ * m₂⁻¹ := by
    have := congrArg (·⁻¹) e
    simpa [mul_assoc] using this
  rw [commutatorElement_def, commutatorElement_def]
  calc c * m₁ * c⁻¹ * m₁⁻¹ = c * (m₁ * c⁻¹ * m₁⁻¹) := by group
    _ = c * (m₂ * c⁻¹ * m₂⁻¹) := by rw [e']
    _ = c * m₂ * c⁻¹ * m₂⁻¹ := by group

theorem mem_pCoreOf_of_comm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {c : ↥M}
    (hc2 : ∃ e : ℕ, (c : G) ^ 2 ^ e = 1)
    (hP : ∀ w₁ ∈ Xq M, ∀ w₂ ∈ Xq M,
      ⁅(c : G), w₁⁆ = 1 ∨ ⁅(c : G), w₂⁆ = 1 ∨ ⁅(c : G), w₁⁆ = ⁅(c : G), w₂⁆) :
    (c : G) ∈ pCoreOf 2 M := by
  by_contra hcO
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hZn : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  have hcU : ∀ u ∈ Uq M T L, ⁅(c : G), u⁆ ∈ Uq M T L := fun u hu => by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hUn c.2) u).1 hu) (inv_mem hu)
  have hne : ∀ u, u ∉ Subgroup.centralizer ({(c : G)} : Set G) → ⁅(c : G), u⁆ ≠ 1 := by
    intro u hu h1
    apply hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((commutatorElement_eq_one_iff_mul_comm).1 h1).symm
  have hrel : (Subgroup.centralizer ({(c : G)} : Set G)).relIndex (Uq M T L) ≤ 2 := by
    refine relIndex_le_two_of_forall fun u₁ hu₁ u₂ hu₂ h₁ h₂ => ?_
    have heq : ⁅(c : G), u₁⁆ = ⁅(c : G), u₂⁆ :=
      ((hP u₁ (h.Uq_le_Xq hu₁) u₂ (h.Uq_le_Xq hu₂)).resolve_left (hne u₁ h₁)).resolve_left
        (hne u₂ h₂)
    have hinv : ⁅(c : G), u₁⁻¹⁆ = ⁅(c : G), u₁⁆⁻¹ := by
      have e := X52.comm_mul_eq (m := (c : G)) ((Xq M).inv_mem (h.Uq_le_Xq hu₁))
        (h.Uq_le_Xq (hcU u₁ hu₁))
      rw [inv_mul_cancel, commutatorElement_one_right] at e
      exact eq_inv_of_mul_eq_one_left e.symm
    have e := X52.comm_mul_eq (m := (c : G)) ((Xq M).inv_mem (h.Uq_le_Xq hu₁))
      (h.Uq_le_Xq (hcU u₂ hu₂))
    rw [hinv, heq, inv_mul_cancel] at e
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((commutatorElement_eq_one_iff_mul_comm).1 e).symm
  have hodd := S5Q2.not_mem_commutator_of_relIndex_le_two h hd hc2 hcO hrel
  obtain ⟨z, hz, hzC⟩ := Set.not_subset.1 hC
  have hzc : ⁅(c : G), z⁆ ≠ 1 := by
    intro h1
    exact hzC (S5Q2.mem_centralizer_of_commute h hd hodd hz
      ((commutatorElement_eq_one_iff_mul_comm).1 h1))
  have hdZ : ⁅(c : G), z⁆ ∈ Zq M L := by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hZn c.2) z).1 hz) (inv_mem hz)
  have hlift := (sp4Lift_holds G M T L h 1 F _ _ a hd).2.2
  have hUc : Uq M T L ≤ Subgroup.centralizer ({(c : G)} : Set G) := by
    intro u hu
    have h1 : ⁅(c : G), u⁆ ∈ Subgroup.centralizer (L : Set G) := by
      rcases hP u (h.Uq_le_Xq hu) z hz.1 with h1 | h1 | h1
      · rw [h1]
        exact one_mem _
      · exact absurd h1 hzc
      · rw [h1]
        exact hdZ.2
    have h2 : (c : G) * u * (c : G)⁻¹ = u :=
      hlift _ c.2 u hu (by rwa [commutatorElement_def] at h1)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * c = ((c : G) * u * (c : G)⁻¹) * c := by rw [h2]
      _ = c * u := by group
  set E : Subgroup G := Subgroup.closure {(c : G)} with hE
  have hEM : E ≤ M := (Subgroup.closure_le M).2 (Set.singleton_subset_iff.2 c.2)
  have hE2 : IsPGroup 2 E := by
    obtain ⟨e, he⟩ := hc2
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hg
    refine ⟨e, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have hEO : ¬ E ≤ pCoreOf 2 M := fun hle => hcO (hle (Subgroup.subset_closure rfl))
  have h2 := (S5B.relIndex_centralizer_M h hd hEM hE2 hEO).1
  rw [hE, Subgroup.centralizer_closure, Subgroup.relIndex_eq_one.2 hUc] at h2
  norm_num at h2

section Vertex

variable (h : PUHyp M T L)

theorem cX_baseA :
    XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) =
      imM h.le (Zq M L) := by
  rw [S5B.xm_baseA_eq h, S5B.puTrans_L_baseA h, ← imM_inf_centralizer h.le _ h.L_le]

theorem cX_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    XM _ (g • δ) ⊓ Subgroup.centralizer (puTrans h.le L (g • δ) : Set (puAmalgam h.le).Universal) =
      (XM _ δ ⊓ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal)).map
        (MulAut.conj g).toMonoidHom := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← PU.centralizer_map_mulEquiv, ← puTrans_smul h.le hLn]

theorem comm_eq_or_vtx (hd : S5.IsSp4Data M T L 1 F a) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ XM _ α ⊓
      Subgroup.centralizer (puTrans h.le L α : Set (puAmalgam h.le).Universal))
    {y₁ y₂ : (puAmalgam h.le).Universal} (hy₁ : y₁ ∈ stab _ α) (hy₂ : y₂ ∈ stab _ α) :
    ⁅x, y₁⁆ = 1 ∨ ⁅x, y₂⁆ = 1 ∨ ⁅x, y₁⁆ = ⁅x, y₂⁆ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hα
  rw [cX_smul h, cX_baseA h] at hx
  obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hx
  rw [stab_smul, puAmalgam.stab_baseA] at hy₁ hy₂
  obtain ⟨_, ⟨m₁, -, rfl⟩, rfl⟩ := hy₁
  obtain ⟨_, ⟨m₂, -, rfl⟩, rfl⟩ := hy₂
  set φ : ↥M →* (puAmalgam h.le).Universal :=
    (MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA with hφ
  have hφi : Function.Injective φ :=
    (MulAut.conj g).injective.comp (puAmalgam h.le).ofA_injective
  have e : ∀ m₁ m₂ : ↥M, ⁅(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA m₁),
      (MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA m₂)⁆ = φ ⁅m₁, m₂⁆ := fun m₁ m₂ => by
    rw [map_commutatorElement]
    rfl
  have hcoe : ∀ m₁ m₂ : ↥M, ((⁅m₁, m₂⁆ : ↥M) : G) = ⁅(m₁ : G), (m₂ : G)⁆ := fun m₁ m₂ =>
    map_commutatorElement M.subtype m₁ m₂
  rw [e, e, (map_eq_one_iff φ hφi), (map_eq_one_iff φ hφi), hφi.eq_iff, ← Subtype.coe_inj,
    ← Subtype.coe_inj, ← Subtype.coe_inj, hcoe, hcoe, Subgroup.coe_one]
  exact comm_eq_or h hd (Subgroup.mem_subgroupOf.1 hc) m₁.2 m₂.2

theorem le_qv_of_le_stab (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {α ρ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hρ : IsMVtx _ ρ) (hX : XM _ ρ ≤ stab _ α)
    (hCs : XM _ α ⊓
      Subgroup.centralizer (puTrans h.le L α : Set (puAmalgam h.le).Universal) ≤ stab _ ρ) :
    XM _ α ⊓ Subgroup.centralizer (puTrans h.le L α : Set (puAmalgam h.le).Universal) ≤
      Qv _ ρ := by
  intro x hx
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  have hxs := hCs hx
  rw [stab_smul, puAmalgam.stab_baseA] at hxs
  obtain ⟨_, ⟨c₀, -, rfl⟩, hxe⟩ := hxs
  rw [qv_smul, S5B.qv_baseA_eq h]
  refine ⟨_, ⟨c₀, Subgroup.mem_subgroupOf.2 ?_, rfl⟩, hxe⟩
  set φ : ↥M →* (puAmalgam h.le).Universal :=
    (MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA with hφ
  have hφi : Function.Injective φ :=
    (MulAut.conj g).injective.comp (puAmalgam h.le).ofA_injective
  have hxφ : φ c₀ = x := hxe
  have hcoe : ∀ m₁ m₂ : ↥M, ((⁅m₁, m₂⁆ : ↥M) : G) = ⁅(m₁ : G), (m₂ : G)⁆ := fun m₁ m₂ =>
    map_commutatorElement M.subtype m₁ m₂
  refine mem_pCoreOf_of_comm h hd hC ⟨1, ?_⟩ fun w₁ hw₁ w₂ hw₂ => ?_
  · have hx2 : x ^ 2 = 1 := (isElemAbelian_xm _ α).2 x hx.1
    rw [← hxφ, ← map_pow, map_eq_one_iff φ hφi] at hx2
    rw [pow_one, ← Subgroup.coe_pow, hx2, Subgroup.coe_one]
  · have hy : ∀ w (hw : w ∈ Xq M), φ ⟨w, Xq_le M hw⟩ ∈ stab _ α := by
      intro w hw
      apply hX
      rw [xm_smul, S5B.xm_baseA_eq h]
      exact ⟨_, ⟨⟨w, Xq_le M hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩, rfl⟩
    have key := comm_eq_or_vtx h hd hα hx (hy w₁ hw₁) (hy w₂ hw₂)
    rw [← hxφ, ← map_commutatorElement, ← map_commutatorElement, map_eq_one_iff φ hφi,
      map_eq_one_iff φ hφi, hφi.eq_iff, ← Subtype.coe_inj, ← Subtype.coe_inj,
      ← Subtype.coe_inj, hcoe, hcoe, Subgroup.coe_one] at key
    exact key

theorem xm_le_stab_of_dist_le {α ρ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hρ : IsMVtx _ ρ)
    (hdist : (puAmalgam h.le).treeGraph.dist α ρ ≤ critDist (puAmalgam h.le)) :
    XM _ ρ ≤ stab _ α := by
  have h20 := h.hyp20
  have hC := h.centHyp
  have hev : Even ((puAmalgam h.le).treeGraph.dist α ρ) :=
    (even_dist_iff _ α ρ).2 (iff_of_true hα hρ)
  rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist α ρ) 2 with hlt | hge
  · have h0 : (puAmalgam h.le).treeGraph.dist α ρ = 0 := by
      obtain ⟨r, hr⟩ := hev
      omega
    rw [(dist_eq_zero_iff _).1 h0]
    exact (xm_le_qv _ ρ).trans (qv_le_stab _ ρ)
  · have h1 : (puAmalgam h.le).treeGraph.Adj (geo _ α ρ 1) (geo _ α ρ 2) :=
      adj_geo _ (i := 1) (by omega)
    have h0 : (puAmalgam h.le).treeGraph.Adj (geo _ α ρ 0) (geo _ α ρ 1) :=
      adj_geo _ (i := 0) (by omega)
    rw [geo_zero] at h0
    have hμ : IsMVtx _ (geo _ α ρ 2) := (isMVtx_geo _ (by omega)).2 (iff_of_true hα even_two)
    have hdρμ : (puAmalgam h.le).treeGraph.dist ρ (geo _ α ρ 2) < critDist (puAmalgam h.le) := by
      rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega)]
      omega
    exact (ms22_i _ h20 hC hρ hμ hdρμ).trans
      ((qv_le_qv _ h20 hμ h1.symm).trans (qv_le_stab_of_adj _ h0.symm))

theorem le_qv_of_dist_le (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {α ρ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hρ : IsMVtx _ ρ)
    (hdist : (puAmalgam h.le).treeGraph.dist α ρ ≤ critDist (puAmalgam h.le)) :
    XM _ α ⊓ Subgroup.centralizer (puTrans h.le L α : Set (puAmalgam h.le).Universal) ≤
      Qv _ ρ :=
  le_qv_of_le_stab h hd hC hα hρ (xm_le_stab_of_dist_le h hα hρ hdist)
    (inf_le_left.trans (xm_le_stab_of_dist_le h hρ hα (by rwa [SimpleGraph.dist_comm])))

theorem vIm_xm_le_commutator (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) α') :
    S5.vIm h.le a (XM _ α') ≤ commutator (MSP.Sp4 F) := by
  have hle := le_qv_of_dist_le h hd hC (isMVtx_baseA _) (hc.isMVtx_right _ h.hyp20) hc.2.1.le
  rw [cX_baseA h] at hle
  rintro _ ⟨m, hm, rfl⟩
  by_contra hodd
  refine hC fun c hc' => S5Q2.mem_centralizer_of_commute h hd hodd hc' ?_
  have h1 : (puAmalgam h.le).ofA ⟨c, Xq_le M hc'.1⟩ ∈ Qv _ α' :=
    hle ⟨⟨c, Xq_le M hc'.1⟩, Subgroup.mem_subgroupOf.2 hc', rfl⟩
  have h2 := Subgroup.mem_centralizer_iff.1 (qv_le_centralizer_xm _ α' h1) _ hm
  have h3 : m * ⟨c, Xq_le M hc'.1⟩ = ⟨c, Xq_le M hc'.1⟩ * m :=
    (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact h2)
  exact congrArg Subtype.val h3

theorem shape_of_not_le (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) α') :
    (Qv _ α').relIndex (XM (puAmalgam h.le) (baseA _)) = Nat.card (S5.vIm h.le a (XM _ α')) ∧
      ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
        S5.vIm h.le a (XM _ α') = MSP.qLine l ⊓ commutator (MSP.Sp4 F) ∧
        S5.vIm h.le a (ZM _ α') = S5.vIm h.le a (XM _ α') := by
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  obtain ⟨hidx, l, hl, hsh⟩ := X52.shape_of_not_le h hd hC hc
  refine ⟨hidx, l, hl, ?_⟩
  rcases hsh with ⟨hT, hZ⟩ | ⟨hT, -⟩
  · exact ⟨hT, hZ⟩
  · exact absurd (hT ▸ vIm_xm_le_commutator h hd hC hc) (MSP.qLine_not_le_commutator hNF hl)

end Vertex

section Zm

open scoped Pointwise

theorem z0q_inf_zq_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) :
    Z0q M T ⊓ Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  obtain ⟨t, htT, hto⟩ := S5Q2.exists_mem_T_not_mem_commutator h hd
  have hlift := (sp4Lift_holds G M T L h 1 F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hZn : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  rintro x ⟨hxZ, hxC⟩
  have hΩn : omegaOneCenterOf T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    ((PU.omegaOneCenterOf_le T).trans h.le).trans hUn
  have hx' : x ∈ ((omegaOneCenterOf T : Set G) * (Uq M T L : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hΩn, ← h.Z0q_eq_sup]
    exact hxZ
  obtain ⟨b, hb, u, hu, rfl⟩ := hx'
  have hbT : b ∈ Xq M ⊓ Subgroup.centralizer (T : Set G) := by
    rw [← h.omegaOneCenterOf_eq]
    exact hb
  have hbt : (t : G) * b = b * t := Subgroup.mem_centralizer_iff.1 hbT.2 _ htT
  have huX : u ∈ Xq M := h.Uq_le_Xq hu
  have htu : (t : G) * u * (t : G)⁻¹ * u⁻¹ ∈ Uq M T L :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 (hUn t.2) u).1 hu) (inv_mem hu)
  have hcomm : (t : G) * (b * u) * (t : G)⁻¹ * (b * u)⁻¹ = (t : G) * u * (t : G)⁻¹ * u⁻¹ := by
    have h1 : b * ((t : G) * u * (t : G)⁻¹ * u⁻¹) = ((t : G) * u * (t : G)⁻¹ * u⁻¹) * b :=
      S5Q2.mul_comm_of_mem_Xq hbT.1 (h.Uq_le_Xq htu)
    calc (t : G) * (b * u) * (t : G)⁻¹ * (b * u)⁻¹
        = ((t : G) * b) * u * (t : G)⁻¹ * u⁻¹ * b⁻¹ := by group
      _ = b * ((t : G) * u * (t : G)⁻¹ * u⁻¹) * b⁻¹ := by rw [hbt]; group
      _ = (t : G) * u * (t : G)⁻¹ * u⁻¹ := by rw [h1]; group
  have hxZq : (t : G) * (b * u) * (t : G)⁻¹ * (b * u)⁻¹ ∈ Zq M L :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 (hZn t.2) (b * u)).1 hxC) (inv_mem hxC)
  have htu1 : (t : G) * u * (t : G)⁻¹ = u := hlift _ t.2 u hu (by rw [← hcomm]; exact hxZq.2)
  refine S5Q2.mem_centralizer_of_commute h hd hto hxC ?_
  have h2 : (t : G) * (b * u) * (t : G)⁻¹ * (b * u)⁻¹ = 1 := by
    rw [hcomm, htu1, mul_inv_cancel]
  calc (t : G) * (b * u) = (t : G) * (b * u) * (t : G)⁻¹ * (b * u)⁻¹ * ((b * u) * t) := by group
    _ = b * u * t := by rw [h2, one_mul]

theorem z0q_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) :
    Z0q M T ≤ Uq M T L ⊔ (Zq M L ⊓ Subgroup.centralizer (M : Set G)) := by
  obtain ⟨t, htT, hto⟩ := S5Q2.exists_mem_T_not_mem_commutator h hd
  rw [h.Z0q_eq_sup]
  refine sup_le ?_ le_sup_left
  refine le_trans ?_ (S5Q2.xq_inf_centralizer_le h hd hXU hto)
  rw [h.omegaOneCenterOf_eq]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 htT))

variable (h : PUHyp M T L)

private theorem map_stabCenter_le' (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    (stabCenter _ δ).map (MulAut.conj g).toMonoidHom ≤ stabCenter _ (g • δ) := by
  rintro _ ⟨z, hz, rfl⟩
  have hzs := (S5B.stabCenter_le_inf δ hz).1
  have hzc := (S5B.stabCenter_le_inf δ hz).2
  have hgz : (MulAut.conj g).toMonoidHom z ∈ stab _ (g • δ) := by
    rw [stab_smul]
    exact ⟨z, hzs, rfl⟩
  refine ⟨⟨_, hgz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
  have hy : g⁻¹ * (y : (puAmalgam h.le).Universal) * g ∈ stab _ δ := (mem_stab_smul _).1 y.2
  have hyz := Subgroup.mem_centralizer_iff.1 hzc _ hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul]
  calc (y : (puAmalgam h.le).Universal) * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by
        group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hyz]
    _ = g * z * g⁻¹ * y := by group

theorem zm_inf_centralizer_le_stabCenter (hd : S5.IsSp4Data M T L 1 F a)
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    ZM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ γ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  have h1 : ZM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
    rw [puAmalgam.zm_baseA h.le, S5B.puTrans_L_baseA h, ← imM_inf_centralizer h.le _ h.L_le,
      S5B.stabCenter_baseA]
    refine imM_mono h.le (le_inf (inf_le_left.trans (Z0q_le M T)) ?_)
    exact (le_inf inf_le_left (le_inf (inf_le_left.trans h.Z0q_le_Xq) inf_le_right)).trans
      (z0q_inf_zq_le h hd)
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← zm_smul,
    ← PU.centralizer_map_mulEquiv, ← puTrans_smul h.le hLn] at h2
  exact h2.trans (map_stabCenter_le' h g _)

theorem zm_le_uSub_sup (hd : S5.IsSp4Data M T L 1 F a) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    ZM _ γ ≤ S5.uSub h.le L γ ⊔ (XM _ γ ⊓ stabCenter _ γ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  have hle1 : Uq M T L ≤ M := Uq_le h.L_le
  have hle2 : Zq M L ⊓ Subgroup.centralizer (M : Set G) ≤ M :=
    inf_le_left.trans (inf_le_left.trans (Xq_le M))
  have h1 : ZM _ (baseA (puAmalgam h.le)) ≤
      S5.uSub h.le L (baseA _) ⊔ (XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _)) := by
    rw [puAmalgam.zm_baseA h.le]
    refine (imM_mono h.le (z0q_le h hd hXU)).trans ?_
    rw [S5B.imM_sup_of_le h.le hle1 hle2, ← S5B.uSub_baseA h]
    refine sup_le_sup_left ?_ _
    rw [S5B.xm_baseA_eq h, S5B.stabCenter_baseA, ← imM_inf]
    exact imM_mono h.le (le_inf (inf_le_left.trans inf_le_left) (le_inf hle2 inf_le_right))
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← zm_smul, ← xm_smul,
    ← S5B.uSub_smul h.le hLn] at h2
  exact h2.trans (sup_le_sup_left (inf_le_inf_left _ (map_stabCenter_le' h g _)) _)

end Zm

section NotCent

theorem exists_not_mem_commutator_of_not_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E : Subgroup G} (hEM : E ≤ M) (hE : ¬ Zq M L ≤ Subgroup.centralizer (E : Set G)) :
    ∃ e : ↥M, (e : G) ∈ E ∧ a e ∉ commutator (MSP.Sp4 F) := by
  by_contra hne
  push Not at hne
  exact hE (S5Q2.le_centralizer_of_mem_commutator h hd hEM fun j hj => hne ⟨j, hEM hj⟩ hj)

theorem zq_inf_centralizer_le_of_not_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E : Subgroup G} (hEM : E ≤ M) (hE : ¬ Zq M L ≤ Subgroup.centralizer (E : Set G)) :
    Zq M L ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (M : Set G) := by
  obtain ⟨e, he, heo⟩ := exists_not_mem_commutator_of_not_le h hd hEM hE
  rw [S5Q2.inf_centralizer_eq_of_not_mem h hd hEM he heo]
  exact inf_le_right

theorem xq_inf_centralizer_le_of_not_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {E : Subgroup G} (hEM : E ≤ M)
    (hE : ¬ Zq M L ≤ Subgroup.centralizer (E : Set G)) :
    Xq M ⊓ Subgroup.centralizer (E : Set G) ≤
      Uq M T L ⊔ (Zq M L ⊓ Subgroup.centralizer (M : Set G)) := by
  obtain ⟨e, he, heo⟩ := exists_not_mem_commutator_of_not_le h hd hEM hE
  exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 he))).trans
    (S5Q2.xq_inf_centralizer_le h hd hXU heo)

variable (h : PUHyp M T L)

theorem cX_inf_centralizer_le_stabCenter (hd : S5.IsSp4Data M T L 1 F a)
    {ν : Vtx (puAmalgam h.le)} (hν : IsMVtx _ ν) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ ν)
    (hEC : ¬ XM _ ν ⊓ Subgroup.centralizer (puTrans h.le L ν : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) :
    XM _ ν ⊓ Subgroup.centralizer (puTrans h.le L ν : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤ stabCenter _ ν := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hν
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  have hZM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  rw [cX_smul h, cX_baseA h, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hEC
  replace hEC : ¬ Zq M L ≤ Subgroup.centralizer (E₀ : Set G) := fun hle => hEC (by
    rw [← inf_of_le_left hle, imM_inf_centralizer h.le _ hE₀M]
    exact inf_le_right)
  rw [cX_smul h, cX_baseA h, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← imM_inf_centralizer h.le _ hE₀M]
  refine (Subgroup.map_mono ?_).trans (map_stabCenter_le' h g _)
  rw [S5B.stabCenter_baseA]
  exact imM_mono h.le (le_inf (inf_le_left.trans hZM)
    (zq_inf_centralizer_le_of_not_le h hd hE₀M hEC))

theorem xm_inf_centralizer_le_of_not_le (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {ν : Vtx (puAmalgam h.le)} (hν : IsMVtx _ ν)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ ν)
    (hEC : ¬ XM _ ν ⊓ Subgroup.centralizer (puTrans h.le L ν : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) :
    XM _ ν ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      S5.uSub h.le L ν ⊔ (XM _ ν ⊓ stabCenter _ ν) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hν
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  have hZM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  rw [cX_smul h, cX_baseA h, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hEC
  replace hEC : ¬ Zq M L ≤ Subgroup.centralizer (E₀ : Set G) := fun hle => hEC (by
    rw [← inf_of_le_left hle, imM_inf_centralizer h.le _ hE₀M]
    exact inf_le_right)
  have key := xq_inf_centralizer_le_of_not_le h hd hXU hE₀M hEC
  have hle1 : Uq M T L ≤ M := Uq_le h.L_le
  have hle2 : Zq M L ⊓ Subgroup.centralizer (M : Set G) ≤ M := inf_le_left.trans hZM
  have h1 : imM h.le (Xq M ⊓ Subgroup.centralizer (E₀ : Set G)) ≤
      imM h.le (Uq M T L) ⊔ (XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _)) := by
    refine (imM_mono h.le key).trans ?_
    rw [S5B.imM_sup_of_le h.le hle1 hle2]
    refine sup_le_sup_left ?_ _
    rw [S5B.xm_baseA_eq h, S5B.stabCenter_baseA, ← imM_inf]
    exact imM_mono h.le (le_inf (inf_le_left.trans inf_le_left) (le_inf hle2 inf_le_right))
  rw [imM_inf_centralizer h.le _ hE₀M, ← S5B.xm_baseA_eq h, ← S5B.uSub_baseA h] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← PU.centralizer_map_mulEquiv, Subgroup.map_sup,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← S5B.uSub_smul h.le hLn] at h2
  exact h2.trans (sup_le_sup_left (inf_le_inf_left _ (map_stabCenter_le' h g _)) _)

end NotCent

end CFSG.Quasithin.MS93.S5Q2.UC

