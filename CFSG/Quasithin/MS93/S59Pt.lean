module

public import CFSG.Quasithin.MS93.S59C1

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise Matrix

namespace S59

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Sp4

theorem fixSp_le_of_le_qLine {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    {A : Subgroup (MSP.Sp4 F)} (hA : A ≤ MSP.qLine l) (hcard : Nat.card F < Nat.card A) :
    MSP.fixSp A ≤ l := by
  intro v hv
  by_contra hvl
  have hv0 : v ≠ 0 := fun h0 => hvl (h0 ▸ zero_mem l)
  set W : Submodule F (MSP.V4 F) := l ⊔ F ∙ v with hWdef
  have hWA : W ≤ MSP.fixSp A :=
    sup_le (MSP.le_fixer_iff.1 hA) ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
  have hdis : l ⊓ (F ∙ v) = ⊥ := by
    rw [← disjoint_iff]
    exact (Submodule.disjoint_span_singleton' hv0).2 hvl
  have hWr : Module.finrank F W = 3 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq l (F ∙ v)
    rw [hdis, finrank_bot, finrank_span_singleton hv0, hl.1] at this
    omega
  have hp : MSP.IsPoint (MSP.perp W) := by
    have := MSP.finrank_perp W
    show Module.finrank F (MSP.perp W) = 1
    omega
  have hAX : A ≤ MSP.xPoint (MSP.perp W) := by
    show A ≤ MSP.fixer (MSP.perp (MSP.perp W))
    rw [MSP.perp_perp]
    exact MSP.le_fixer_iff.2 hWA
  have hle := Subgroup.card_le_of_le hAX
  rw [MSP.card_xPoint hp] at hle
  omega

end Sp4

section Point

theorem comm_of_comm_of_fixSp_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hfix : Module.finrank F (MSP.fixSp ((T.subgroupOf M).map a)) ≤ 1)
    {u₁ u : G} (hu₁ : u₁ ∈ Uq M T L) (hu : u ∈ Uq M T L)
    (hu₁L : u₁ ∉ Subgroup.centralizer (L : Set G))
    (hTu₁ : ∀ t ∈ T, t * u₁ = u₁ * t) (hTu : ∀ t ∈ T, t * u = u * t)
    {m : G} (hm : m ∈ M) (hmu₁ : m * u₁ = u₁ * m) : m * u = u * m := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  set u₁' : ↥(Uq M T L) := ⟨u₁, hu₁⟩
  set u' : ↥(Uq M T L) := ⟨u, hu⟩
  have hv₁ : c.vec u₁' ≠ 0 := fun h0 => hu₁L ((c.vec_eq_zero_iff u₁').1 h0).2
  have hfixT : ∀ w : ↥(Uq M T L), (∀ t ∈ T, t * (w : G) = w * t) →
      c.vec w ∈ MSP.fixSp ((T.subgroupOf M).map a) := by
    intro w hw
    rw [MSP.mem_fixSp]
    rintro _ ⟨t, ht, rfl⟩
    exact fix_of_comm h c t.2 w (hw t (Subgroup.mem_subgroupOf.1 ht))
  have hspan : (F ∙ c.vec u₁') = MSP.fixSp ((T.subgroupOf M).map a) :=
    Submodule.eq_of_le_of_finrank_le
      ((Submodule.span_singleton_le_iff_mem _ _).2 (hfixT u₁' hTu₁))
      (by rw [finrank_span_singleton hv₁]; exact hfix)
  have h3 : c.vec u' ∈ F ∙ c.vec u₁' := hspan ▸ hfixT u' hTu
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h3
  have hmv := fix_of_comm h c hm u₁' hmu₁
  have hfx : MSP.mat (a ⟨m, hm⟩) *ᵥ c.vec u' = c.vec u' := by
    rw [← hr, Matrix.mulVec_smul, hmv]
  exact comm_of_fix h hlift c hm u' hfx

theorem comm_of_comm_of_fixSp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hfix : Module.finrank F (MSP.fixSp (S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))))) ≤ 1)
    {u₁ u : (puAmalgam h.le).Universal} (hu₁ : u₁ ∈ S5.uSub h.le L (baseA _))
    (hu : u ∈ S5.uSub h.le L (baseA _))
    (hu₁L : u₁ ∉
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal))
    (hTu₁ : u₁ ∈
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal))
    (hTu : u ∈
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal))
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hgu₁ : g * u₁ = u₁ * g) : g * u = u * g := by
  rw [puAmalgam.qv_baseB, S5B.vIm_imM] at hfix
  rw [puAmalgam.qv_baseB] at hTu₁ hTu
  rw [S5B.uSub_baseA h] at hu₁ hu
  rw [S5B.puTrans_L_baseA h] at hu₁L
  rw [puAmalgam.stab_baseA] at hg
  obtain ⟨w₁, hw₁, rfl⟩ := hu₁
  obtain ⟨w, hw, rfl⟩ := hu
  obtain ⟨m₀, -, rfl⟩ := hg
  have hcomm : ∀ x y : ↥M, (puAmalgam h.le).ofA x * (puAmalgam h.le).ofA y =
      (puAmalgam h.le).ofA y * (puAmalgam h.le).ofA x ↔ (x : G) * y = y * x := by
    intro x y
    rw [← map_mul, ← map_mul]
    constructor
    · intro he
      have := congrArg Subtype.val ((puAmalgam h.le).ofA_injective he)
      simpa using this
    · intro he
      rw [show x * y = y * x from Subtype.ext (by simpa using he)]
  have hT : ∀ y : ↥M, (puAmalgam h.le).ofA y ∈
      Subgroup.centralizer (imM h.le T : Set (puAmalgam h.le).Universal) →
      ∀ t ∈ T, t * (y : G) = y * t := by
    intro y hy t ht
    exact (hcomm ⟨t, h.le ht⟩ y).1
      (Subgroup.mem_centralizer_iff.1 hy _ ⟨⟨t, h.le ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩)
  have hL : (w₁ : G) ∉ Subgroup.centralizer (L : Set G) := by
    intro hwL
    apply hu₁L
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    exact (hcomm l w₁).2 (Subgroup.mem_centralizer_iff.1 hwL l (Subgroup.mem_subgroupOf.1 hl))
  exact (hcomm m₀ w).2 (comm_of_comm_of_fixSp_M h hd hfix (Subgroup.mem_subgroupOf.1 hw₁)
    (Subgroup.mem_subgroupOf.1 hw) hL (hT w₁ hTu₁) (hT w hTu) m₀.2 ((hcomm m₀ w₁).1 hgu₁))

theorem exists_centralizer_le_of_fixSp (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    (hfix : Module.finrank F (MSP.fixSp (S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))))) ≤ 1)
    (hnc : ¬ hSub h.le L γ ≤ stabCenter _ (baseA (puAmalgam h.le))) :
    ∃ h₁ ∈ hSub h.le L γ, stab _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer ({h₁} : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨-, hQβ, -, -, -⟩ := hSub_facts h hb hd hβγ hγα hξ hξα hP
  have hTpart : ∀ u d : (puAmalgam h.le).Universal, u * d ∈ hSub h.le L γ →
      d ∈ stabCenter _ (baseA (puAmalgam h.le)) →
      u ∈ Subgroup.centralizer
        (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) := by
    intro u d hx hdd
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htα : t ∈ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_adj _ hαβ.symm ht
    have htx := Subgroup.mem_centralizer_iff.1 (hQβ ht) (u * d) hx
    have htd := (S510.mem_stabCenter_iff.1 hdd).2 t htα
    calc t * u = t * (u * d) * d⁻¹ := by group
      _ = u * d * t * d⁻¹ := by rw [htx]
      _ = u * (d * t) * d⁻¹ := by group
      _ = u * (t * d) * d⁻¹ := by rw [htd]
      _ = u * t := by group
  obtain ⟨h₁, hh₁, hh₁c⟩ := Set.not_subset.1 hnc
  refine ⟨h₁, hh₁, fun g hg => ?_⟩
  obtain ⟨hgα, hgh⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ :=
    exists_mul_of_mem_hSub h53 h hmin hb hd hβγ hγα hξ hξα hP hh₁
  have hu₁L : u₁ ∉
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    fun hL => hh₁c (mul_mem (uSub_inf_le_stabCenter h hd hα ⟨hu₁, hL⟩) hd₁)
  have hgd₁ := (S510.mem_stabCenter_iff.1 hd₁).2 g hgα
  have hgh' := Subgroup.mem_centralizer_singleton_iff.1 hgh
  have hgu₁ : g * u₁ = u₁ * g := by
    calc g * u₁ = g * (u₁ * d₁) * d₁⁻¹ := by group
      _ = u₁ * d₁ * g * d₁⁻¹ := by rw [hgh']
      _ = u₁ * (d₁ * g) * d₁⁻¹ := by group
      _ = u₁ * (g * d₁) * d₁⁻¹ := by rw [hgd₁]
      _ = u₁ * g := by group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨u, hu, d, hdd, rfl⟩ := exists_mul_of_mem_hSub h53 h hmin hb hd hβγ hγα hξ hξα hP hx
  have hgu := comm_of_comm_of_fixSp h hd hfix hu₁ hu hu₁L (hTpart u₁ d₁ hh₁ hd₁)
    (hTpart u d hx hdd) hgα hgu₁
  have hgd := (S510.mem_stabCenter_iff.1 hdd).2 g hgα
  calc u * d * g = u * (d * g) := by group
    _ = u * (g * d) := by rw [hgd]
    _ = u * g * d := by group
    _ = g * u * d := by rw [hgu]
    _ = g * (u * d) := by group

theorem finrank_fixSp_le_one (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (hl : ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
      ¬ S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≤ MSP.qLine l) :
    Module.finrank F (MSP.fixSp (S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))))) ≤ 1 := by
  rcases h54 G M T L h hmin hb k F _ _ a hd with
      ⟨-, ⟨l, hline, -, hJl⟩, hJq⟩ | ⟨-, -, p, hp, hTp⟩
  · have hJQ : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ Qv _ (baseB (puAmalgam h.le)) :=
      S5B.jOff_le_qv h.le L _ _ _
    have hcard : (2 ^ k) ^ 2 ≤
        Nat.card (S5.vIm h.le a (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))) := by
      obtain ⟨J₀, hJ₀T, hJ₀M, hJeq⟩ :=
        S5B.exists_eq_imM h.le (hJQ.trans (puAmalgam.qv_baseB h.le).le)
      rw [hJeq, S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hJ₀M] at hJq
      rw [hJeq, S5B.vIm_imM]
      refine hJq.trans ?_
      have hJ₀2 : IsPGroup 2 J₀ := h.isPGroup.to_le hJ₀T
      rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_subgroupOf hJ₀M,
        ← Subgroup.inf_relIndex_right a.ker]
      refine Subgroup.relIndex_le_of_le_left ?_ Subgroup.FiniteIndex.index_ne_zero
      rintro m ⟨hm1, hmJ⟩
      obtain ⟨n, hn⟩ := hJ₀2 ⟨(m : G), Subgroup.mem_subgroupOf.1 hmJ⟩
      exact Subgroup.mem_subgroupOf.2
        (S5B.mem_pCoreOf_of_ker h hd hm1 ⟨n, by simpa using congrArg Subtype.val hn⟩)
    have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
    have hlt : Nat.card F <
        Nat.card (S5.vIm h.le a (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))) := by
      have h2 : 2 ≤ 2 ^ k := by
        have := hd.1
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
      have h4 : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
      omega
    have hfixJ := fixSp_le_of_le_qLine hline (S5B.vIm_le_of_le_vPre h.le hJl) hlt
    have hfixT : MSP.fixSp (S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le)))) ≤ l :=
      (MSP.fixSp_antitone (Subgroup.map_mono (Subgroup.comap_mono hJQ))).trans hfixJ
    by_contra hcon
    have heq : MSP.fixSp (S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le)))) = l :=
      Submodule.eq_of_le_of_finrank_le hfixT (by rw [hline.1]; omega)
    exact hl l hline (MSP.le_fixer_iff.2 heq.ge)
  · rw [hTp, MSP.fixSp_qPoint hp]
    exact hp.le

end Point

section Natural

theorem exists_eq_commutator_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hnat : Uq M T L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    {t : G} (htE : t ∈ E) (htU : ∃ u ∈ Uq M T L, t * u ≠ u * t)
    {x : G} (hx : x ∈ ⁅Uq M T L, E⁆) : ∃ u ∈ Uq M T L, x = ⁅u, t⁆ := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  obtain ⟨p, hp, hcomm, -, hEX⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  have hUE : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hEM.trans (le_normalizer_Uq h.le_normalizer))
  have hcommU : ∀ y ∈ Uq M T L, ∀ z ∈ Uq M T L, y * z = z * y :=
    (isMulCommutative_subgroup_iff).1 h.isElemAbelian_Uq.1
  set t' : ↥M := ⟨t, hEM htE⟩ with ht'
  have htX : a t' ∈ MSP.xPoint p := hEX ⟨t', Subgroup.mem_subgroupOf.2 htE, rfl⟩
  set f : MSP.V4 F →ₗ[F] MSP.V4 F := Matrix.toLin' (MSP.mat (a t')) - LinearMap.id with hf
  have hfv : ∀ v, f v = MSP.mat (a t') *ᵥ v - v := fun v => by
    rw [hf, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply]
  have hfp : LinearMap.range f ≤ p := by
    rintro _ ⟨v, rfl⟩
    rw [hfv]
    exact MSP.sub_mem_of_mem_fixer_perp htX v
  have hf0 : LinearMap.range f ≠ ⊥ := by
    intro hbot
    obtain ⟨u₀, hu₀, hne⟩ := htU
    apply hne
    refine comm_of_fix h hlift c (hEM htE) ⟨u₀, hu₀⟩ ?_
    have h0 : f (c.vec ⟨u₀, hu₀⟩) = 0 := by
      rw [LinearMap.range_eq_bot.1 hbot, LinearMap.zero_apply]
    rw [hfv, sub_eq_zero] at h0
    exact h0
  have hfeq : LinearMap.range f = p := by
    refine Submodule.eq_of_le_of_finrank_le hfp ?_
    have h1 : Module.finrank F p = 1 := hp
    have h2 : Module.finrank F (LinearMap.range f) ≠ 0 :=
      fun h0 => hf0 (Submodule.finrank_eq_zero.1 h0)
    omega
  have hinj : ∀ y z : ↥(Uq M T L), c.vec y = c.vec z → y = z := by
    intro y z hyz
    have h0 : c.vec (y * z⁻¹) = 0 := by rw [c.vec_mul, c.vec_inv, hyz, add_neg_cancel]
    have h1 := (c.vec_eq_zero_iff _).1 h0
    rw [hnat, Subgroup.mem_bot] at h1
    have h2 : y * z⁻¹ = 1 := Subtype.ext h1
    exact mul_inv_eq_one.1 h2
  have hxp : c.vec ⟨x, hUE hx⟩ ∈ LinearMap.range f := by
    rw [hfeq, ← hcomm]
    exact S5B.vec_mem_commSp h c hEM ⟨x, hUE hx⟩ hx
  obtain ⟨w, hw⟩ := hxp
  obtain ⟨u, rfl⟩ := c.exists_vec_eq w
  have hconj : t * u * t⁻¹ ∈ Uq M T L := conj_mem_uq h (hEM htE) u.2
  have hv := c.vec_commutator t' u hconj
  have hxe : (⟨t * u * t⁻¹ * (u : G)⁻¹, mul_mem hconj (inv_mem u.2)⟩ : ↥(Uq M T L)) =
      ⟨x, hUE hx⟩ := hinj _ _ (by rw [hv, ← hfv]; exact hw)
  refine ⟨(u : G)⁻¹, inv_mem u.2, ?_⟩
  have hx' : x = t * u * t⁻¹ * (u : G)⁻¹ := (congrArg Subtype.val hxe).symm
  rw [hx', commutatorElement_def, inv_inv]
  have e := hcommU _ (inv_mem u.2) _ hconj
  calc t * u * t⁻¹ * (u : G)⁻¹ = (u : G)⁻¹ * (t * u * t⁻¹) := e.symm
    _ = (u : G)⁻¹ * t * u * t⁻¹ := by group

theorem exists_eq_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hnat : Uq M T L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    {t : (puAmalgam h.le).Universal} (htE : t ∈ E)
    (htU : ∃ u ∈ S5.uSub h.le L δ, t * u ≠ u * t)
    {x : (puAmalgam h.le).Universal} (hx : x ∈ ⁅S5.uSub h.le L δ, E⁆) :
    ∃ u ∈ S5.uSub h.le L δ, x = ⁅u, t⁆ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [commutator_uSub_conj_eq h g hE₀M] at hx
  rw [uSub_conj_eq h g] at htU ⊢
  obtain ⟨x₀, hx₀, rfl⟩ := (mem_map_conj_imM h.le).1 hx
  obtain ⟨t₀, ht₀, rfl⟩ := (mem_map_conj_imM h.le).1 htE
  obtain ⟨u₁, hu₁, hne⟩ := htU
  obtain ⟨w₁, hw₁, rfl⟩ := (mem_map_conj_imM h.le).1 hu₁
  have htU₀ : ∃ u ∈ Uq M T L, (t₀ : G) * u ≠ u * t₀ := by
    refine ⟨w₁, hw₁, fun he => hne ((conj_ofA_comm_iff h.le).2 ?_)⟩
    exact he
  obtain ⟨u₀, hu₀, he⟩ := exists_eq_commutator_M h hd hnat hE₀M hrel ht₀ htU₀ hx₀
  have hu₀M : u₀ ∈ M := Uq_le h.L_le hu₀
  refine ⟨g * (puAmalgam h.le).ofA ⟨u₀, hu₀M⟩ * g⁻¹,
    (mem_map_conj_imM h.le).2 ⟨⟨u₀, hu₀M⟩, hu₀, rfl⟩, ?_⟩
  have hx₀e : x₀ = ⁅(⟨u₀, hu₀M⟩ : ↥M), t₀⁆ :=
    Subtype.ext (by simp [he, commutatorElement_def])
  rw [hx₀e]
  simp only [commutatorElement_def, map_mul, map_inv]
  group

theorem bss_of_natural (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) (hnat : Uq M T L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    (hnc : ¬ hSub h.le L γ ≤ stabCenter _ (baseA (puAmalgam h.le)))
    {t : (puAmalgam h.le).Universal} (ht : t ∈ tZero h.le L γ)
    (htH : ∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) :
    ∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ γ := by
  by_cases htU : ∃ u ∈ S5.uSub h.le L γ, t * u ≠ u * t
  · exfalso
    apply hnc
    intro x hx
    obtain ⟨hγ, -, -⟩ := gamma_facts h hβγ hγα
    obtain ⟨-, hTst, -, -, hrel⟩ := tZero_facts h hb hd hβγ hγα hξ hξα hP
    obtain ⟨u, hu, rfl⟩ := exists_eq_commutator h hd hnat hγ hTst hrel ht htU hx
    exact htH u hu
  · intro u hu
    have htu : t * u = u * t := by
      by_contra hne
      exact htU ⟨u, hu, hne⟩
    have e : ⁅u, t⁆ = 1 := by
      calc ⁅u, t⁆ = u * t * u⁻¹ * t⁻¹ := commutatorElement_def u t
        _ = t * u * u⁻¹ * t⁻¹ := by rw [htu]
        _ = 1 := by group
    rw [e]
    exact one_mem _

theorem bss_of_b (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)}
    (hbb : hSub h.le L γ ⊓ stabCenter _ (baseA (puAmalgam h.le)) ≤ stabCenter _ γ)
    {t : (puAmalgam h.le).Universal} (ht : t ∈ tZero h.le L γ)
    (htH : ∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) :
    ∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ γ :=
  fun u hu => hbb ⟨Subgroup.commutator_mem_commutator hu ht, htH u hu⟩

end Natural

end S59

end CFSG.Quasithin.MS93
