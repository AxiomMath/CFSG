module

public import CFSG.Milestones.ASVolI.F4N.L21
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_f2_smul_xv_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) (b : α.G2) :
    f2 (c := c) b • c.xv = c.xv ↔ b ∈ α.α2.range := by
  constructor
  · intro h
    have h1 : ((f2 (c := c) b : c.G0) : Y) ∈ c.φ1.range :=
      (burnsideF4b_mem_stv_xv c _).mp (MulAction.mem_stabilizer_iff.mpr h)
    have h2 : c.φ2 b ∈ c.φ1.range ⊓ c.φ2.range := ⟨h1, ⟨b, rfl⟩⟩
    rw [c.inter] at h2
    obtain ⟨d, hd⟩ := h2
    exact ⟨d, hc.2.2 (by rw [c.comm2]; exact hd)⟩
  · intro hb
    exact MulAction.mem_stabilizer_iff.mp (burnsideF4b_f2_mem_stv_xv c hb)

theorem burnsideF4n_orderOf_mul_comm {G : Type*} [Group G] (a b : G) :
    orderOf (a * b) = orderOf (b * a) :=
  SemiconjBy.orderOf_eq b (by simp [SemiconjBy, mul_assoc])

theorem burnsideF4n_phi1_not_mem_inf {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {a : α.G1} (ha : a ∉ α.α1.range) :
    c.φ1 a ∉ c.φ1.range ⊓ c.φ2.range := by
  rw [c.inter]
  rintro ⟨d, hd⟩
  exact ha ⟨d, hc.1 (by rw [c.comm1]; exact hd)⟩

theorem burnsideF4n_phi2_not_mem_inf {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {b : α.G2} (hb : b ∉ α.α2.range) :
    c.φ2 b ∉ c.φ1.range ⊓ c.φ2.range := by
  rw [c.inter]
  rintro ⟨d, hd⟩
  exact hb ⟨d, hc.2.2 (by rw [c.comm2]; exact hd)⟩

noncomputable def burnsideF4n_quotCpl {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (ρ : α.Completion Y) (hρ : ρ.IsFaithful) (N : Subgroup α.Ghat) [N.Normal]
    (hN : N ≤ ρ.theta.ker) : α.Completion (α.Ghat ⧸ N) where
  φ1 := (QuotientGroup.mk' N).comp (Amalgam.ξ α.toAmalgam RankTwoIndex.one)
  φ12 := (QuotientGroup.mk' N).comp (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo)
  φ2 := (QuotientGroup.mk' N).comp (Amalgam.ξ α.toAmalgam RankTwoIndex.two)
  comm1 g := congrArg (QuotientGroup.mk' N)
    (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.one) trivial g)
  comm2 g := congrArg (QuotientGroup.mk' N)
    (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.two) trivial g)
  inter := by
    apply le_antisymm
    · rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      let π := QuotientGroup.lift N ρ.theta hN
      have h1 : π (QuotientGroup.mk' N (Amalgam.ξ α.toAmalgam RankTwoIndex.one a)) = ρ.φ1 a :=
        theta_ξ1 ρ a
      have h2 : π (QuotientGroup.mk' N (Amalgam.ξ α.toAmalgam RankTwoIndex.two b)) = ρ.φ2 b :=
        theta_ξ2 ρ b
      have hb' : QuotientGroup.mk' N (Amalgam.ξ α.toAmalgam RankTwoIndex.two b) =
          QuotientGroup.mk' N (Amalgam.ξ α.toAmalgam RankTwoIndex.one a) := hb
      have hab : ρ.φ1 a = ρ.φ2 b := by rw [← h1, ← h2, hb']
      have hint : ρ.φ1 a ∈ ρ.φ1.range ⊓ ρ.φ2.range := ⟨⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
      rw [ρ.inter] at hint
      obtain ⟨d, hd⟩ := hint
      have hd1 : α.α1 d = a := hρ.1 (by rw [ρ.comm1]; exact hd)
      refine ⟨d, ?_⟩
      show QuotientGroup.mk' N (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo d) =
        QuotientGroup.mk' N (Amalgam.ξ α.toAmalgam RankTwoIndex.one a)
      rw [← hd1]
      exact (congrArg (QuotientGroup.mk' N) (Amalgam.ξ_map (α := α.toAmalgam)
        (d := RankTwoIndex.onetwo) (e := RankTwoIndex.one) trivial d)).symm
    · rintro x ⟨d, rfl⟩
      refine ⟨⟨α.α1 d, congrArg (QuotientGroup.mk' N) (Amalgam.ξ_map (α := α.toAmalgam)
        (d := RankTwoIndex.onetwo) (e := RankTwoIndex.one) trivial d)⟩,
        ⟨α.α2 d, congrArg (QuotientGroup.mk' N) (Amalgam.ξ_map (α := α.toAmalgam)
        (d := RankTwoIndex.onetwo) (e := RankTwoIndex.two) trivial d)⟩⟩
  gen := by
    refine eq_top_iff.mpr ?_
    have hle : (α.Ghat1 ⊔ α.Ghat2).map (QuotientGroup.mk' N) ≤
        ((QuotientGroup.mk' N).comp (Amalgam.ξ α.toAmalgam RankTwoIndex.one)).range ⊔
          ((QuotientGroup.mk' N).comp (Amalgam.ξ α.toAmalgam RankTwoIndex.two)).range := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, rfl⟩
    rw [α.Ghat1_sup_Ghat2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hle
    exact hle

theorem burnsideF4n_quotCpl_isFaithful {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (ρ : α.Completion Y) (hρ : ρ.IsFaithful) (N : Subgroup α.Ghat) [N.Normal]
    (hN : N ≤ ρ.theta.ker) : (burnsideF4n_quotCpl ρ hρ N hN).IsFaithful := by
  let π := QuotientGroup.lift N ρ.theta hN
  refine ⟨fun a b h => hρ.1 ?_, fun a b h => hρ.2.1 ?_, fun a b h => hρ.2.2 ?_⟩
  · have := congrArg π h
    rwa [show π ((burnsideF4n_quotCpl ρ hρ N hN).φ1 a) = ρ.φ1 a from theta_ξ1 ρ a,
      show π ((burnsideF4n_quotCpl ρ hρ N hN).φ1 b) = ρ.φ1 b from theta_ξ1 ρ b] at this
  · have := congrArg π h
    rwa [show π ((burnsideF4n_quotCpl ρ hρ N hN).φ12 a) = ρ.φ12 a from theta_ξ12 ρ a,
      show π ((burnsideF4n_quotCpl ρ hρ N hN).φ12 b) = ρ.φ12 b from theta_ξ12 ρ b] at this
  · have := congrArg π h
    rwa [show π ((burnsideF4n_quotCpl ρ hρ N hN).φ2 a) = ρ.φ2 a from theta_ξ2 ρ a,
      show π ((burnsideF4n_quotCpl ρ hρ N hN).φ2 b) = ρ.φ2 b from theta_ξ2 ρ b] at this

theorem burnsideF4n_quotCpl_theta {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (ρ : α.Completion Y) (hρ : ρ.IsFaithful) (N : Subgroup α.Ghat) [N.Normal]
    (hN : N ≤ ρ.theta.ker) : (burnsideF4n_quotCpl ρ hρ N hN).theta = QuotientGroup.mk' N := by
  symm
  refine Amalgam.Completion.hat_unique _ _ fun d x => ?_
  cases d <;> rfl

theorem burnsideF4n_theta_xi1 {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Z : Type} [Group Z]
    (c : Cpl M₁ M₂ Z) (a : ↥M₁) : c.theta (xi1 M₁ M₂ a) = c.φ1 a :=
  theta_ξ1 c a

theorem burnsideF4n_theta_xi2 {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Z : Type} [Group Z]
    (c : Cpl M₁ M₂ Z) (b : ↥M₂) : c.theta (xi2 M₁ M₂ b) = c.φ2 b :=
  theta_ξ2 c b

theorem burnsideF4n_N1hat_tits {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {cc y : β.Γ} {w : GHat M₁ M₂} (hw : w ∈ N1hat GLKind.Tits β cc y) :
    ∃ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1, w = xi1 M₁ M₂ a ∧
      f1 (c := β) a ∈ N1set β GLKind.Tits cc y := by
  obtain ⟨hdom, g, hg, hgw⟩ := hw
  rw [liftDom1, if_pos rfl] at hdom
  obtain ⟨a, rfl⟩ := hdom
  refine ⟨a, rfl, ?_⟩
  have : g = f1 (c := β) a := Subtype.ext (hgw.trans (theta_ξ1 β a))
  rwa [this] at hg

theorem burnsideF4n_N2hat_tits {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {cc y y' : β.Γ} {w : GHat M₁ M₂}
    (hw : w ∈ N2hat GLKind.Tits β cc y y') :
    ∃ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, w = xi2 M₁ M₂ b ∧
      f2 (c := β) b ∈ N2set β GLKind.Tits cc y y' := by
  obtain ⟨hdom, g, hg, hgw⟩ := hw
  rw [liftDom2, if_pos rfl] at hdom
  obtain ⟨b, rfl⟩ := hdom
  refine ⟨b, rfl, ?_⟩
  have : g = f2 (c := β) b := Subtype.ext (hgw.trans (theta_ξ2 β b))
  rwa [this] at hg

theorem burnsideF4n_N1hat_g2d {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {cc y : β.Γ} {w : GHat M₁ M₂} (hw : w ∈ N1hat GLKind.G2d β cc y) :
    ∃ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, w = xi2 M₁ M₂ b ∧
      f2 (c := β) b ∈ N1set β GLKind.G2d cc y := by
  obtain ⟨hdom, g, hg, hgw⟩ := hw
  rw [liftDom1, if_neg (by decide)] at hdom
  obtain ⟨b, rfl⟩ := hdom
  refine ⟨b, rfl, ?_⟩
  have : g = f2 (c := β) b := Subtype.ext (hgw.trans (theta_ξ2 β b))
  rwa [this] at hg

theorem burnsideF4n_N2hat_g2d {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {cc y y' : β.Γ} {w : GHat M₁ M₂}
    (hw : w ∈ N2hat GLKind.G2d β cc y y') :
    ∃ (h : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) (b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2),
      f1 (c := β) h • β.lv = cc ∧ w = xi1 M₁ M₂ h * xi2 M₁ M₂ b * (xi1 M₁ M₂ h)⁻¹ ∧
      f1 (c := β) h * f2 (c := β) b * (f1 (c := β) h)⁻¹ ∈ N2set β GLKind.G2d cc y y' := by
  obtain ⟨hdom, g, hg, hgw⟩ := hw
  rw [liftDom2, if_neg (by decide)] at hdom
  obtain ⟨h, hh, b, rfl⟩ := hdom
  refine ⟨h, b, hh, rfl, ?_⟩
  have : g = f1 (c := β) h * f2 (c := β) b * (f1 (c := β) h)⁻¹ := by
    apply Subtype.ext
    rw [hgw]
    show β.theta (xi1 M₁ M₂ h * xi2 M₁ M₂ b * (xi1 M₁ M₂ h)⁻¹) = _
    rw [map_mul, map_mul, map_inv, burnsideF4n_theta_xi1, burnsideF4n_theta_xi2]
    rfl
  rwa [this] at hg

theorem burnsideF4n_inv_of_hasCycle1 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {a : α.G1} {u v : c.Γ}
    (h : HasCycle c (f1 (c := c) a) u v) (hu : u = c.lv) : a * a = 1 ∧ a ∉ α.α1.range := by
  obtain ⟨hss, hne, hsu, -⟩ := h
  refine ⟨f1_injective c hc (by rw [map_mul, hss, map_one]), fun ha => ?_⟩
  have := (burnsideF4n_f1_smul_lv_iff c hc a).mpr ha
  subst hu
  exact hne (this.symm.trans hsu)

theorem burnsideF4n_inv_of_hasCycle2 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {b : α.G2} {u v : c.Γ}
    (h : HasCycle c (f2 (c := c) b) u v) (hu : u = c.xv) : b * b = 1 ∧ b ∉ α.α2.range := by
  obtain ⟨hss, hne, hsu, -⟩ := h
  refine ⟨f2_injective c hc (by rw [map_mul, hss, map_one]), fun hb => ?_⟩
  have := (burnsideF4n_f2_smul_xv_iff c hc b).mpr hb
  subst hu
  exact hne (this.symm.trans hsu)

theorem burnsideF4n_small_of_order {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {m : ℕ} (F : c.Facts46 m) (hm : 1 < m)
    {a : α.G1} {b : α.G2} (ha : a * a = 1) (ha' : a ∉ α.α1.range) (hb : b * b = 1)
    (hb' : b ∉ α.α2.range) (hord : orderOf (c.φ1 a * c.φ2 b) = m) : c.IsSmall m := by
  have hs : f1 (c := c) a * f1 (c := c) a = 1 := by rw [← map_mul, ha, map_one]
  have ht : f2 (c := c) b * f2 (c := c) b = 1 := by rw [← map_mul, hb, map_one]
  have hord' : orderOf (f1 (c := c) a * f2 (c := c) b) = m := by
    rw [← Subgroup.orderOf_coe]
    exact hord
  have hpow : (f1 (c := c) a * f2 (c := c) b) ^ m = 1 := by
    rw [← hord']; exact pow_orderOf_eq_one _
  obtain ⟨-, hpoly, -⟩ := CosetGeom.lemma_F36 (G₁ := c.φ1.range) (G₂ := c.φ2.range) hm
    F.uniqueGeod hs ht ⟨a, rfl⟩ (burnsideF4n_phi1_not_mem_inf c hc ha') ⟨b, rfl⟩
    (burnsideF4n_phi2_not_mem_inf c hc hb') (by omega) le_rfl
    (by rw [hpow]; exact Subgroup.one_mem _)
  exact F.isSmall_of_polygon hpoly

theorem burnsideF4n_small_of_order' {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {m : ℕ} (F : c.Facts46 m) (hm4 : 4 ≤ m)
    (hmev : Even m) {h : α.G1} (hh : h ∉ α.α1.range) {b b₁ : α.G2} (hb : b * b = 1)
    (hb' : b ∉ α.α2.range) (hb₁ : b₁ * b₁ = 1) (hb₁' : b₁ ∉ α.α2.range)
    (hord : orderOf (c.φ2 b₁ * (c.φ1 h * c.φ2 b * (c.φ1 h)⁻¹)) = m / 2) : c.IsSmall m := by
  set g := f1 (c := c) h
  set s := g * f2 (c := c) b * g⁻¹
  set t := f2 (c := c) b₁
  have hgx : g • c.xv = c.xv := f1_smul_xv h
  have hcc : c.graph.Adj c.xv (g • c.lv) := by
    rw [← hgx] at *
    exact (CosetGeom.smul_adj g).mpr CosetGeom.adj_γ₀_γ₁
  have hcl : g • c.lv ≠ c.lv := fun e => hh ((burnsideF4n_f1_smul_lv_iff c hc h).mp e)
  have hs : s * s = 1 := by
    simp only [s]
    rw [show g * f2 (c := c) b * g⁻¹ * (g * f2 (c := c) b * g⁻¹) =
      g * (f2 (c := c) b * f2 (c := c) b) * g⁻¹ by group, ← map_mul, hb, map_one]
    group
  have ht : t * t = 1 := by simp only [t]; rw [← map_mul, hb₁, map_one]
  have hsc : s • (g • c.lv) = g • c.lv := by
    simp only [s]
    rw [mul_smul, mul_smul, inv_smul_smul, f2_smul_lv]
  have hsx : s • c.xv ≠ c.xv := by
    intro e
    simp only [s] at e
    rw [mul_smul, mul_smul, show g⁻¹ • c.xv = c.xv by rw [inv_smul_eq_iff, hgx]] at e
    have e2 : f2 (c := c) b • c.xv = c.xv := by
      have := congrArg (fun v => g⁻¹ • v) e
      simpa [hgx, show g⁻¹ • c.xv = c.xv by rw [inv_smul_eq_iff, hgx]] using this
    exact hb' ((burnsideF4n_f2_smul_xv_iff c hc b).mp e2)
  have hord' : orderOf (s * t) = m / 2 := by
    rw [burnsideF4n_orderOf_mul_comm, ← Subgroup.orderOf_coe]
    exact hord
  have hpow : (s * t) ^ (m / 2) = 1 := by rw [← hord']; exact pow_orderOf_eq_one _
  have hsc' : (s : Y) ∈ CosetGeom.stab (g • c.lv) := CosetGeom.mem_stab_of_smul_eq hsc
  have hsxc : (s : Y) ∉ c.φ1.range ⊓ CosetGeom.stab (g • c.lv) := by
    rintro ⟨h1, -⟩
    exact hsx (MulAction.mem_stabilizer_iff.mp ((burnsideF4b_mem_stv_xv c s).mpr h1))
  obtain ⟨-, hpoly, -⟩ := CosetGeom.lemma_F37 (G₁ := c.φ1.range) (G₂ := c.φ2.range) hm4 hmev
    F.uniqueGeod hcc hcl hs ht hsc' hsxc ⟨b₁, rfl⟩ (burnsideF4n_phi2_not_mem_inf c hc hb₁')
    (by omega) le_rfl (by rw [hpow]; exact Subgroup.one_mem _)
  exact F.isSmall_of_polygon hpoly

theorem burnsideF4n_small_of_phat
    (h46 : F_4_6)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {cc y y' : β.Γ} (hccl : cc ≠ β.lv)
    {Y' : Type} [Group Y'] (ρ : Cpl M₁ M₂ Y') (hρ : ρ.IsFaithful)
    (hne : (PhatFor κ β cc y y' ρ).Nonempty) : ρ.IsSmall κ.m := by
  have F := burnsideF4n_facts46_at h46 hyp ρ hρ
  obtain ⟨⟨w₁, w₂⟩, h1, h2, hord⟩ := hne
  rcases hκ with rfl | rfl
  ·
    obtain ⟨b₁, rfl, hb₁⟩ := burnsideF4n_N1hat_g2d β h1
    obtain ⟨h, b, hh, rfl, hg⟩ := burnsideF4n_N2hat_g2d β h2
    obtain ⟨hb₁i, hb₁r⟩ := burnsideF4n_inv_of_hasCycle2 β hβ hb₁.2 rfl
    have hhr : h ∉ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := fun e =>
      hccl (hh.symm.trans ((burnsideF4n_f1_smul_lv_iff β hβ h).mpr e))
    obtain ⟨hgg, hgne, hgx, -⟩ := hg.2
    have hbi : b * b = 1 := by
      apply f2_injective β hβ
      have : f1 (c := β) h * (f2 (c := β) b * f2 (c := β) b) * (f1 (c := β) h)⁻¹ = 1 := by
        rw [← hgg]; group
      rw [map_mul, map_one]
      have h3 := congrArg (fun z => (f1 (c := β) h)⁻¹ * z * f1 (c := β) h) this
      simpa [mul_assoc] using h3
    have hbr : b ∉ (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range := by
      intro e
      apply hgne
      rw [← hgx, mul_smul, mul_smul,
        show (f1 (c := β) h)⁻¹ • β.xv = β.xv by rw [inv_smul_eq_iff, f1_smul_xv],
        (burnsideF4n_f2_smul_xv_iff β hβ b).mpr e, f1_smul_xv]
    have hord' : orderOf (ρ.φ2 b₁ * (ρ.φ1 h * ρ.φ2 b * (ρ.φ1 h)⁻¹)) = GLKind.G2d.m / 2 := by
      have e1 : ρ.toCompletion.hat (xi2 M₁ M₂ b₁) = ρ.φ2 b₁ := theta_ξ2 ρ b₁
      have e2 : ρ.toCompletion.hat (xi1 M₁ M₂ h) = ρ.φ1 h := theta_ξ1 ρ h
      have e3 : ρ.toCompletion.hat (xi2 M₁ M₂ b) = ρ.φ2 b := theta_ξ2 ρ b
      have h' : orderOf (ρ.toCompletion.hat (xi2 M₁ M₂ b₁) * ρ.toCompletion.hat
          (xi1 M₁ M₂ h * xi2 M₁ M₂ b * (xi1 M₁ M₂ h)⁻¹)) = 3 := hord
      rw [map_mul, map_mul, map_inv, e1, e2, e3] at h'
      exact h'
    exact burnsideF4n_small_of_order' ρ hρ F (by decide) (by decide) hhr hbi hbr hb₁i hb₁r hord'
  ·
    obtain ⟨a, rfl, ha⟩ := burnsideF4n_N1hat_tits β h1
    obtain ⟨b, rfl, hb⟩ := burnsideF4n_N2hat_tits β h2
    obtain ⟨hai, har⟩ := burnsideF4n_inv_of_hasCycle1 β hβ ha.2.1 rfl
    obtain ⟨hbi, hbr⟩ := burnsideF4n_inv_of_hasCycle2 β hβ hb.2 rfl
    have hord' : orderOf (ρ.φ1 a * ρ.φ2 b) = GLKind.Tits.m := by
      have e1 : ρ.toCompletion.hat (xi1 M₁ M₂ a) = ρ.φ1 a := theta_ξ1 ρ a
      have e2 : ρ.toCompletion.hat (xi2 M₁ M₂ b) = ρ.φ2 b := theta_ξ2 ρ b
      have h' : orderOf (ρ.toCompletion.hat (xi1 M₁ M₂ a) * ρ.toCompletion.hat (xi2 M₁ M₂ b)) =
          8 := hord
      rw [e1, e2] at h'
      exact h'
    exact burnsideF4n_small_of_order ρ hρ F (by decide) hai har hbi hbr hord'

theorem burnsideF4n_ker_eq
    (h45 : F_4_5) (h46 : F_4_6)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {cc y y' : β.Γ} (hccl : cc ≠ β.lv)
    {Y' : Type} [Group Y'] (ρ : Cpl M₁ M₂ Y') (hρ : ρ.IsFaithful)
    {st : GHat M₁ M₂ × GHat M₁ M₂} (hst : st ∈ PhatFor κ β cc y y' ρ) :
    ρ.toCompletion.hat.ker = Subgroup.normalClosure {(st.1 * st.2) ^ m0Of κ} := by
  haveI : Finite E := hyp.finite
  set N := Subgroup.normalClosure ({(st.1 * st.2) ^ m0Of κ} : Set (GHat M₁ M₂)) with hNdef
  have hpow : ρ.theta ((st.1 * st.2) ^ m0Of κ) = 1 := by
    rw [map_pow, map_mul]
    have h1 : orderOf (ρ.theta st.1 * ρ.theta st.2) = m0Of κ := hst.2.2
    rw [← h1]
    exact pow_orderOf_eq_one _
  have hN : N ≤ ρ.theta.ker := Subgroup.normalClosure_le_normal (by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hpow)
  have hρs : (burnsideF4n_quotCpl ρ hρ N hN).IsFaithful := burnsideF4n_quotCpl_isFaithful ρ hρ N hN
  have hth : (burnsideF4n_quotCpl ρ hρ N hN).theta = QuotientGroup.mk' N :=
    burnsideF4n_quotCpl_theta ρ hρ N hN
  let π := QuotientGroup.lift N ρ.theta hN
  have hord : orderOf (QuotientGroup.mk' N (st.1 * st.2)) = m0Of κ := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.subset_normalClosure (Set.mem_singleton _)
    · have h1 : orderOf (π (QuotientGroup.mk' N (st.1 * st.2))) = m0Of κ := by
        show orderOf (ρ.theta (st.1 * st.2)) = m0Of κ
        rw [map_mul]
        exact hst.2.2
      have h2 := orderOf_map_dvd π (QuotientGroup.mk' N (st.1 * st.2))
      rwa [h1] at h2
  have hsts : st ∈ PhatFor κ β cc y y' (burnsideF4n_quotCpl ρ hρ N hN) := by
    refine ⟨hst.1, hst.2.1, ?_⟩
    show orderOf ((burnsideF4n_quotCpl ρ hρ N hN).theta st.1 *
      (burnsideF4n_quotCpl ρ hρ N hN).theta st.2) = m0Of κ
    rw [hth, ← map_mul]
    exact hord
  have hsm := burnsideF4n_small_of_phat h46 hyp hκ β hβ hccl ρ hρ ⟨st, hst⟩
  have hsms := burnsideF4n_small_of_phat h46 hyp hκ β hβ hccl _ hρs ⟨st, hsts⟩
  have hF := burnsideF4n_facts46All h46
  have h413 := burnsideF4b_F413 hF (burnsideF4b_IotaSmall_of hF h45)
  have c1 := (h413 κ p f E Gp M₁ M₂ hyp _ _ hρs hsms).2
  have c2 := (h413 κ p f E Gp M₁ M₂ hyp _ ρ hρ hsm).2
  rw [card_G0] at c1 c2
  haveI : Finite (GHat M₁ M₂ ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨x, rfl⟩ := Amalgam.Completion.hat_surjective ρ.toCompletion z
    exact ⟨QuotientGroup.mk' N x, rfl⟩
  have hbij := hsurj.bijective_of_nat_card_le (by rw [c1, c2])
  refine le_antisymm (fun x hx => ?_) hN
  have h1 : π (QuotientGroup.mk' N x) = π 1 := by
    rw [map_one]
    exact hx
  have h2 := hbij.1 h1
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2

theorem burnsideF4n_F423_two
    (h45 : F_4_5) (h46 : F_4_6)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {cc y y' : β.Γ} (hccl : cc ≠ β.lv)
    {Y' : Type} [Group Y'] (ρ : Cpl M₁ M₂ Y') (hρ : ρ.IsFaithful) :
    ∀ st ∈ PhatFor κ β cc y y' β, st ∈ PhatFor κ β cc y y' ρ →
      β.toCompletion.hat.ker = Subgroup.normalClosure {(st.1 * st.2) ^ m0Of κ} ∧
      Subgroup.normalClosure {(st.1 * st.2) ^ m0Of κ} = ρ.toCompletion.hat.ker ∧
      Amalgam.Completion.IsEquivalent β.toCompletion ρ.toCompletion := by
  intro st h1 h2
  have k1 := burnsideF4n_ker_eq h45 h46 hyp hκ β hβ hccl β hβ h1
  have k2 := burnsideF4n_ker_eq h45 h46 hyp hκ β hβ hccl ρ hρ h2
  exact ⟨k1, k2.symm, (Amalgam.Completion.isEquivalent_iff_ker_hat_eq _ _).mpr (k1.trans k2.symm)⟩

theorem burnsideF4n_isEquivalent_of_phat
    (h45 : F_4_5)
    (h46 : F_4_6) {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {cc y y' : β.Γ} (hccl : cc ≠ β.lv)
    {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] (ρ₁ : Cpl M₁ M₂ Y₁) (hρ₁ : ρ₁.IsFaithful)
    (ρ₂ : Cpl M₁ M₂ Y₂) (hρ₂ : ρ₂.IsFaithful)
    (hne : (PhatFor κ β cc y y' ρ₁ ∩ PhatFor κ β cc y y' ρ₂).Nonempty) :
    Amalgam.Completion.IsEquivalent ρ₁.toCompletion ρ₂.toCompletion := by
  obtain ⟨st, h1, h2⟩ := hne
  have k1 := burnsideF4n_ker_eq h45 h46 hyp hκ β hβ hccl ρ₁ hρ₁ h1
  have k2 := burnsideF4n_ker_eq h45 h46 hyp hκ β hβ hccl ρ₂ hρ₂ h2
  exact (Amalgam.Completion.isEquivalent_iff_ker_hat_eq _ _).mpr (k1.trans k2.symm)

end CFSG.ASVolI
