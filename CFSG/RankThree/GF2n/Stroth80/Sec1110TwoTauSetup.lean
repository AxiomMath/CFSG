module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoQB
public import CFSG.RankThree.GF2n.Stroth80.Sec37Action
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Bar
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem exists_mem_LB_mk_mem_centralizer_Xbar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hZ : Nat.card Z = 2 ^ x) (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    ∃ u : G, ∃ hu : u ∈ LB M Q B, u ∉ Q ∧
      (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (bar_LB_inf_centralizer_Xbar_ne_bot_two_of_lieModel hc hw hn hLm2 hcenter hZ)
  obtain ⟨haLB, haC⟩ := Subgroup.mem_inf.mp a.2
  obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp haLB
  rw [Subgroup.mem_subgroupOf] at hm
  refine ⟨(m : G), hm, ?_, ?_⟩
  · intro huQ
    apply ha1
    refine Subtype.ext ?_
    rw [← hmk]
    exact (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr huQ)
  · have h1 : (QuotientGroup.mk (⟨(m : G), hc.LB_le_M hm⟩ : ↥M) : Mbar M Q) =
        (a : Mbar M Q) := by
      rw [← hmk]
      rfl
    rw [h1]
    exact haC

theorem Ctx.Xbar_le_bar_H0 [Finite G] [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) : Xbar M Q Z B ≤ bar M Q (H0 M Z) := by
  rw [Xbar]
  exact (Subgroup.closure_le (K := bar M Q (H0 M Z))).mpr fun d hd => hc.Ebar_subset_H hd

theorem isSimpleGroup_Xbar_of_lieModel [(Q.subgroupOf M).Normal] {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) : IsSimpleGroup ↥(Xbar M Q Z B) := by
  have h1 : IsSimpleGroup (XbarMod M Q Z B) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hLm2
  have e : ↥(Xbar M Q Z B) ≃* XbarMod M Q Z B :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot (G := ↥(Xbar M Q Z B)))).symm
  exact e.isSimpleGroup

private theorem mem_Xbar_ne_one_of_isA2 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA2 : IsA2 Q Z a) :
    (⟨(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q),
      Subgroup.subset_closure (hc.mk_mem_Ebar ha hA2)⟩ : ↥(Xbar M Q Z B)) ≠ 1 := by
  intro h
  have h' : (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q) = 1 := by
    simpa using congrArg Subtype.val h
  exact hA2.2.1
    (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨a, hc.LB_le_M ha⟩).mp h'))

private theorem xbar_le_bar_LB_of_le_normalizer [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ} (hx : 1 ≤ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥)
    (hX : Xbar M Q Z B ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q))) :
    Xbar M Q Z B ≤ bar M Q (LB M Q B) := by
  obtain ⟨a, haLB, hA2⟩ := exists_isA2_of_lieModel hc hx hLm2 hcenter
  have hXa : (QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q) ∈
      Xbar M Q Z B := Subgroup.subset_closure (hc.mk_mem_Ebar haLB hA2)
  have hLa : (QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q) ∈
      bar M Q (LB M Q B) :=
    Subgroup.mem_map.mpr ⟨⟨a, hc.LB_le_M haLB⟩, Subgroup.mem_subgroupOf.mpr haLB, rfl⟩
  let S : Subgroup ↥(Xbar M Q Z B) :=
    (bar M Q (LB M Q B)).subgroupOf (Xbar M Q Z B)
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hmem : (⟨(QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q), hXa⟩ :
        ↥(Xbar M Q Z B)) ∈ S := by
      rw [Subgroup.mem_subgroupOf]
      exact hLa
    rw [hbot] at hmem
    exact mem_Xbar_ne_one_of_isA2 hc haLB hA2 (Subgroup.mem_bot.mp hmem)
  haveI hSn : S.Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := (Subgroup.mem_normalizer_iff.mp (hX g.2) (n : Mbar M Q)).mp hn
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  have hStop : S = ⊤ := by
    rcases (isSimpleGroup_Xbar_of_lieModel hLm2 hcenter).eq_bot_or_eq_top_of_normal S with
      h | h
    · exact absurd h hSne
    · exact h
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥(Xbar M Q Z B)) ∈ S := by
    rw [hStop]
    exact Subgroup.mem_top _
  exact hmem

private theorem isPGroup_Xbar_of_le_bar_LB [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hle : Xbar M Q Z B ≤ bar M Q (LB M Q B)) : IsPGroup 2 ↥(Xbar M Q Z B) :=
  (hc.isPGroup_bar_LB).of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem Ctx.not_Xbar_le_normalizer_bar_LB [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ} (hx : 1 ≤ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    ¬ Xbar M Q Z B ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  intro hX
  have hle := xbar_le_bar_LB_of_le_normalizer hc hx hLm2 hcenter hX
  have hbot : Xbar M Q Z B = ⊥ :=
    hc.normal_isPGroup_two_Mbar_eq_bot (Xbar M Q Z B) hc.Xbar_normal
      (isPGroup_Xbar_of_le_bar_LB hc hle)
  obtain ⟨a, haLB, hA2⟩ := exists_isA2_of_lieModel hc hx hLm2 hcenter
  have hXa : (QuotientGroup.mk (⟨a, hc.LB_le_M haLB⟩ : ↥M) : Mbar M Q) ∈
      Xbar M Q Z B := Subgroup.subset_closure (hc.mk_mem_Ebar haLB hA2)
  exact mem_Xbar_ne_one_of_isA2 hc haLB hA2
    (Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ hXa)))

theorem Ctx.mk_mem_normalizer_bar_LB_of_fix_line [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {g : G} (hgM : g ∈ M)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ y ∈ Q, M₀.π (g * y * g⁻¹) = T (M₀.π y)) {μ : K}
    (hTb : T b = μ • b) :
    (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  have h := HS6.piM_mem_normalizer (Q := Q) hc.hyp.Q_normal.1 hgM
    (Gl37.conj_LB_eq_of_fix_line hc hB hgM hT hTb)
  simpa only [HS6.piM_of_mem hgM] using h

theorem Ctx.exists_Xbar_act_not_mem_line [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ} (hx : 1 ≤ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    ∃ g : ↥(H0 M Z), (QuotientGroup.mk (⟨(g : G), g.2.1⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B ∧
      ∀ c : K, φ g b ≠ c • b := by
  by_contra hcon
  push Not at hcon
  have hXle : Xbar M Q Z B ≤
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    intro y hy
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp (hc.Xbar_le_bar_H0 hy)
    rw [Subgroup.mem_subgroupOf] at hm
    let g : ↥(H0 M Z) := ⟨(m : G), hm⟩
    have hgM : (g : G) ∈ M := g.2.1
    have hgm : (QuotientGroup.mk (⟨(g : G), hgM⟩ : ↥M) : Mbar M Q) = y := by
      rw [← hmk]
      rfl
    rw [← hgm]
    obtain ⟨c, hc'⟩ := hcon g (hgm ▸ hy)
    exact Ctx.mk_mem_normalizer_bar_LB_of_fix_line hc hB hgM
      (T := (φ g : M₀.E →ₗ[K] M₀.E)) (hφπ g) (μ := c) hc'
  exact Ctx.not_Xbar_le_normalizer_bar_LB hc hx hLm2 hcenter hXle

theorem charP_two_of_globalModelData {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {x : ℕ}
    (hZ : Nat.card Z = 2 ^ x) : CharP K 2 :=
  CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hD.card.trans hZ)

theorem exists_lagrangian_img_inf_QB_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) :
    ∃ W : Submodule K M₀.E, (∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W) ∧
      Module.finrank K W = 3 ∧ (∀ w ∈ W, M₀.Qf w = 0) ∧
      ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W := by
  have hn3 : n = 3 := width_eq_three hc hw hn hx hZ hLm2 hcenter
  have hKgt1 : 1 < Nat.card K := by
    rw [hD.card]
    have := hc.hyp.q4
    omega
  have hdim : Module.finrank K M₀.E = 2 * 3 := by
    have h := hD.finrank_E hw hKgt1
    omega
  have hK2 : (2 : K) = 0 := by
    haveI : CharP K 2 := charP_two_of_globalModelData hD hZ
    exact CharP.cast_eq_zero K 2
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (3 + 1) := by
    rw [card_inf_QB_eq_of_two hc hw hn hx hZ hLm2 hcenter, hn3, hD.card]
  have hVD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hc.inf_QB_elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨W, hW, hdimW, horth⟩ :=
    Stroth57D.lagrangian_img M₀ hD.reg hK2 hD.card hdim (n := 3)
      (inf_le_left : Q ⊓ QB B ≤ Q) hVD hDc hDcard
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · rw [hdimW]
  · intro w hw
    exact (Tim79.QuadModel.isElemAbelian_iff (M₀ := M₀) hD.reg
      (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian w ((hW w).mpr hw)
  · intro v hv
    rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [M₀.B_comm w v, hv w hw, neg_zero]

theorem Ctx.act_sq_eq_of_mem_LB [Finite G] (hc : Ctx M Q Z B)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {u : G} (hu : u ∈ LB M Q B) (e : M₀.E) :
    φ ⟨u, hc.LB_le_H0 hu⟩ (φ ⟨u, hc.LB_le_H0 hu⟩ e) = e := by
  let g : ↥(H0 M Z) := ⟨u, hc.LB_le_H0 hu⟩
  have h2 : (g : G) ^ 2 ∈ Q := by
    simpa only [g] using hc.sq_mem_Q_of_mem_LB hu
  have hφ2 : φ g * φ g = 1 := by
    have h1 : φ (g * g) = 1 := (hφker (g * g)).mpr (by simpa [pow_two] using h2)
    rwa [map_mul] at h1
  calc φ g (φ g e) = (φ g * φ g) e := rfl
    _ = e := by rw [hφ2]; rfl

theorem act_comm_of_mk_comm [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {m₁ m₂ : H0 M Z}
    (hcomm : (QuotientGroup.mk (⟨(m₁ : G), m₁.2.1⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨(m₂ : G), m₂.2.1⟩ : ↥M) =
      QuotientGroup.mk (⟨(m₂ : G), m₂.2.1⟩ : ↥M) * QuotientGroup.mk (⟨(m₁ : G), m₁.2.1⟩ : ↥M))
    (e : M₀.E) : φ m₁ (φ m₂ e) = φ m₂ (φ m₁ e) := by
  let a : ↥M := ⟨(m₁ : G), m₁.2.1⟩
  let b : ↥M := ⟨(m₂ : G), m₂.2.1⟩
  have hab : (QuotientGroup.mk a : Mbar M Q) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := by
    simpa only [a, b] using hcomm
  let w : ↥M := a * b * a⁻¹ * b⁻¹
  have hw : (QuotientGroup.mk w : Mbar M Q) = 1 := by
    have h1 : (QuotientGroup.mk w : Mbar M Q) =
        QuotientGroup.mk a * QuotientGroup.mk b *
          (QuotientGroup.mk a)⁻¹ * (QuotientGroup.mk b)⁻¹ := by
      simp only [w, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, hab]
    group
  have hwQ : (w : G) ∈ Q :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff w).mp hw)
  let h : ↥(H0 M Z) := m₁ * m₂ * m₁⁻¹ * m₂⁻¹
  have hhQ : (h : G) ∈ Q := by
    have e1 : (h : G) = (w : G) := by
      simp only [h, w, a, b, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e1]
    exact hwQ
  have hφh : φ m₁ * φ m₂ * (φ m₁)⁻¹ * (φ m₂)⁻¹ = 1 := by
    have h1 : φ h = 1 := (hφker h).mpr hhQ
    simpa only [h, map_mul, map_inv] using h1
  have hcommφ : φ m₁ * φ m₂ = φ m₂ * φ m₁ := by
    calc φ m₁ * φ m₂ =
        (φ m₁ * φ m₂ * (φ m₁)⁻¹ * (φ m₂)⁻¹) * (φ m₂ * φ m₁) := by group
      _ = 1 * (φ m₂ * φ m₁) := by rw [hφh]
      _ = φ m₂ * φ m₁ := by rw [one_mul]
  calc φ m₁ (φ m₂ e) = (φ m₁ * φ m₂) e := rfl
    _ = (φ m₂ * φ m₁) e := by rw [hcommφ]
    _ = φ m₂ (φ m₁ e) := rfl

theorem Ctx.act_flag_of_mem_LB [Finite G] (hc : Ctx M Q Z B)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {W : Submodule K M₀.E} (hW : ∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W)
    {u : G} (hu : u ∈ LB M Q B) :
    b ∈ W ∧ φ ⟨u, hc.LB_le_H0 hu⟩ b = b ∧
      ∀ w ∈ W, ∃ c : K, φ ⟨u, hc.LB_le_H0 hu⟩ w - w = c • b := by
  have hfix := hc.LB_act_fix_line hD hB hu
    (T := (φ ⟨u, hc.LB_le_H0 hu⟩ : M₀.E →ₗ[K] M₀.E)) (hφπ ⟨u, hc.LB_le_H0 hu⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact (hW b).mp (M₀.img_mono (le_inf hc.le hc.B_le_QB)
      ((hB b).mpr ⟨1, (one_smul K b).symm⟩))
  · simpa using hfix.1
  · intro w hw
    simpa using hfix.2 w ((hW w).mpr hw)

end CFSG.RankThree.GF2n.Stroth80
