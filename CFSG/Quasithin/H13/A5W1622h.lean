module

public import CFSG.Quasithin.H13.A5W1622e
public import CFSG.LinearAlgebra.SL2MinimalFaithful

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section BlockQuot

variable {G : Type} [Group G]

theorem blockU_le_block (K₀ : Subgroup G) : blockU K₀ ≤ K₀ := by
  rw [blockU, Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ K₀ := C1.blockQ_le K₀ ha
  rw [commutatorElement_def]
  exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem ha' hb) (K₀.inv_mem ha')) (K₀.inv_mem hb)

instance normal_blockZ_subgroupOf (K₀ : Subgroup G) :
    ((blockZ K₀).subgroupOf (blockU K₀)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * n = n * g :=
      Subgroup.mem_centralizer_iff.mp hn.2 (g : G) (blockU_le_block K₀ g.2)
    have e : ((g * n * g⁻¹ : ↥(blockU K₀)) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc, mul_inv_cancel_right]
    rw [e]
    exact hn

abbrev blockQuot (K₀ : Subgroup G) : Type :=
  ↥(blockU K₀) ⧸ (blockZ K₀).subgroupOf (blockU K₀)

theorem blockQuot_sq {K₀ : Subgroup G} (hshort : IsShort2 K₀) (n : blockQuot K₀) : n ^ 2 = 1 := by
  induction n using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow]
    have hu : u ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact C1.blockU_sq hshort _ u.2)
    rw [hu, QuotientGroup.mk_one]

theorem blockQuot_comm {K₀ : Subgroup G} (hshort : IsShort2 K₀) (a b : blockQuot K₀) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H u =>
    induction b using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (C1.blockU_comm hshort _ u.2 _ (C1.blockU_le_blockQ hshort w.2))

variable [Finite G]

theorem actionOn_blockZ (K₀ : Subgroup G) (j : ↥K₀) :
    ((blockZ K₀).subgroupOf (blockU K₀)).map
        ((A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀) j :
          MulAut ↥(blockU K₀)) : ↥(blockU K₀) →* ↥(blockU K₀)) =
      (blockZ K₀).subgroupOf (blockU K₀) := by
  have hfix : ∀ w ∈ (blockZ K₀).subgroupOf (blockU K₀),
      A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀) j w = w := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw
    apply Subtype.ext
    rw [A4.actionOn_apply_coe, Subgroup.mem_centralizer_iff.mp hw.2 (j : G) j.2,
      mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have e : ((A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀) j :
        MulAut ↥(blockU K₀)) : ↥(blockU K₀) →* ↥(blockU K₀)) w = w := hfix w hw
    rw [e]
    exact hw
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

@[expose] noncomputable def blockQuotAct (K₀ : Subgroup G) : ↥K₀ →* MulAut (blockQuot K₀) :=
  CFSG.SL2MinimalFaithful.quotientAction (A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀))
    ((blockZ K₀).subgroupOf (blockU K₀)) (actionOn_blockZ K₀)

theorem blockQuotAct_mk (K₀ : Subgroup G) (ℓ : ↥K₀) (u v : ↥(blockU K₀))
    (h : (v : G) = ℓ * u * (ℓ : G)⁻¹) :
    blockQuotAct K₀ ℓ (u : blockQuot K₀) = (v : blockQuot K₀) := by
  rw [blockQuotAct, CFSG.SL2MinimalFaithful.quotientAction_mk]
  congr 1
  exact Subtype.ext h.symm

theorem actionOn_eq_one_of_mem_pCore {K₀ : Subgroup G} (hshort : IsShort2 K₀) {q : ↥K₀}
    (hq : q ∈ CFSG.pCore 2 ↥K₀) :
    A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀) q = 1 := by
  ext w
  have hq' : q ∈ CFSG.Open.pCore 2 ↥K₀ := by exact hq
  have hqmem : (q : G) ∈ pCoreOf 2 K₀ := ⟨q, hq', rfl⟩
  have hwc : (w : G) ∈ Subgroup.centralizer (blockQ K₀ : Set G) := (hshort.2.2.1.1 w.2).2
  have h1 := Subgroup.mem_centralizer_iff.1 hwc (q : G) hqmem
  rw [A4.actionOn_apply_coe, h1, mul_inv_cancel_right]
  try rfl

@[expose] noncomputable def blockLiftAct {K₀ : Subgroup G} (hshort : IsShort2 K₀) {X : Type}
    [Group X] (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀) :
    X →* MulAut (blockQuot K₀) :=
  α.liftOfSurjective hα ⟨blockQuotAct K₀, fun q hq => by
    rw [hker] at hq
    rw [MonoidHom.mem_ker]
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [blockQuotAct, CFSG.SL2MinimalFaithful.quotientAction_mk,
        actionOn_eq_one_of_mem_pCore hshort hq]
      rfl⟩

theorem blockLiftAct_apply {K₀ : Subgroup G} (hshort : IsShort2 K₀) {X : Type} [Group X]
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀) (ℓ : ↥K₀) :
    blockLiftAct hshort α hα hker (α ℓ) = blockQuotAct K₀ ℓ := by
  rw [blockLiftAct, MonoidHom.liftOfRightInverse_comp_apply]

@[expose] noncomputable def blockLiftConj {K₀ : Subgroup G} (hshort : IsShort2 K₀) {X : Type}
    [Group X] (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀) :
    X →* MulAut ↥(blockU K₀) :=
  α.liftOfSurjective hα ⟨A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀), fun q hq => by
    rw [hker] at hq
    exact actionOn_eq_one_of_mem_pCore hshort hq⟩

theorem blockLiftConj_apply {K₀ : Subgroup G} (hshort : IsShort2 K₀) {X : Type} [Group X]
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀) (ℓ : ↥K₀) :
    blockLiftConj hshort α hα hker (α ℓ) =
      A4.actionOn (blockU K₀) K₀ (C1.le_normalizer_blockU K₀) ℓ := by
  rw [blockLiftConj, MonoidHom.liftOfRightInverse_comp_apply]

theorem fixed_eq_one_of_short {K₀ : Subgroup G} (hshort : IsShort2 K₀)
    (hN : 2 < Nat.card (blockQuot K₀)) {n : blockQuot K₀}
    (hn : ∀ ℓ : ↥K₀, blockQuotAct K₀ ℓ n = n) : n = 1 := by
  classical
  let q := QuotientGroup.mk' ((blockZ K₀).subgroupOf (blockU K₀))
  let P : Subgroup ↥(blockU K₀) := (Subgroup.zpowers n).comap q
  let W : Subgroup G := P.map (blockU K₀).subtype
  have hmemW : ∀ x : G, x ∈ W ↔ ∃ hx : x ∈ blockU K₀, q ⟨x, hx⟩ ∈ Subgroup.zpowers n := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hZW : blockZ K₀ ≤ W := by
    intro x hx
    refine (hmemW x).mpr ⟨hx.1, ?_⟩
    have : q ⟨x, hx.1⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hx)
    rw [this]
    exact Subgroup.one_mem _
  have hWU : W ≤ blockU K₀ := fun x hx => ((hmemW x).mp hx).1
  have hconj : ∀ ℓ ∈ K₀, ∀ x ∈ W, ℓ * x * ℓ⁻¹ ∈ W := by
    intro ℓ hℓ x hx
    obtain ⟨hxU, hxn⟩ := (hmemW x).mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxn
    have hyU : ℓ * x * ℓ⁻¹ ∈ blockU K₀ :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K₀ hℓ) x).mp hxU
    refine (hmemW _).mpr ⟨hyU, Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩⟩
    have h1 := blockQuotAct_mk K₀ ⟨ℓ, hℓ⟩ ⟨x, hxU⟩ ⟨_, hyU⟩ rfl
    have h2 : q ⟨_, hyU⟩ = blockQuotAct K₀ ⟨ℓ, hℓ⟩ (q ⟨x, hxU⟩) := h1.symm
    rw [h2, ← hk, map_zpow, hn]
  have hK₀W : K₀ ≤ Subgroup.normalizer (W : Set G) := fun ℓ hℓ =>
    B6.mem_normalizer_of_forall_mem (hconj ℓ hℓ) fun x hx => by
      have := hconj ℓ⁻¹ (K₀.inv_mem hℓ) x hx
      rwa [inv_inv] at this
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective n
  rcases hshort.2.2.2.2.2 W hZW hWU hK₀W with h | h
  · have hu : (u : G) ∈ W := (hmemW u).mpr ⟨u.2, Subgroup.mem_zpowers _⟩
    rw [h] at hu
    exact (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hu)
  · exfalso
    have htop : Subgroup.zpowers (u : blockQuot K₀) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective m
      have hw : (w : G) ∈ W := by rw [h]; exact w.2
      obtain ⟨_, hmem⟩ := (hmemW w).mp hw
      exact hmem
    have h2 : Nat.card (blockQuot K₀) ≤ 2 := by
      rw [← Subgroup.card_top (G := blockQuot K₀), ← htop, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (blockQuot_sq hshort _)
    omega

end BlockQuot

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem closing_data_blockU (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hshort : IsShort2 K₀) :
    (∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ blockU K₀) ∧ S.e2 ∈ blockU K₀ ∧
      (∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ blockU K₀) ∧
      (∀ x ∈ blockU K₀, x ^ 2 = 1) ∧ (∀ x ∈ blockU K₀, ∀ x' ∈ blockU K₀, x * x' = x' * x) := by
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hKU : K₀ ≤ Subgroup.normalizer (blockU K₀ : Set G) := C1.le_normalizer_blockU K₀
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  refine ⟨hcommA, he2U, fun y hy => (Subgroup.mem_normalizer_iff.mp (hKU (hLvK₀ hy)) _).mp he2U,
    C1.blockU_sq hshort, fun x hx x' hx' => C1.blockU_comm hshort x hx x'
      (C1.blockU_le_blockQ hshort hx')⟩

theorem false_of_blockModel (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hshort : IsShort2 K₀) {X : Type} [Group X] [Finite X]
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀)
    {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hFix : ModelFix (blockLiftAct hshort α hα hker) S₀) : False := by
  obtain ⟨hcommA, he2U, hlA, hU2, hUc⟩ :=
    S.closing_data_blockU h1222 h517 hK₀G hK₀ hTK₀ hLvK₀ hchar hshort
  have hβe : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      QuotientGroup.mk' ((blockZ K₀).subgroupOf (blockU K₀)) v =
        blockLiftAct hshort α hα hker (α ℓ)
          (QuotientGroup.mk' ((blockZ K₀).subgroupOf (blockU K₀)) u) := by
    intro ℓ u v h
    rw [blockLiftAct_apply]
    exact (blockQuotAct_mk K₀ ℓ u v h).symm
  exact S.false_of_closing_model h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ (C1.le_normalizer_blockU K₀) (Zc := blockZ K₀) inf_le_right hU2 hUc hcommA he2U
    hlA (blockQuot_sq hshort) (blockLiftAct hshort α hα hker) hS₀ hFix α hα
    (QuotientGroup.mk' _) (QuotientGroup.ker_mk' _) hβe

theorem false_of_blockModelU (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hshort : IsShort2 K₀) {X : Type} [Group X] [Finite X]
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀)
    {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hFix : ModelFix (blockLiftConj hshort α hα hker) S₀) : False := by
  obtain ⟨hcommA, he2U, hlA, hU2, hUc⟩ :=
    S.closing_data_blockU h1222 h517 hK₀G hK₀ hTK₀ hLvK₀ hchar hshort
  have hβe : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      MonoidHom.id ↥(blockU K₀) v =
        blockLiftConj hshort α hα hker (α ℓ) (MonoidHom.id ↥(blockU K₀) u) := by
    intro ℓ u v h
    rw [blockLiftConj_apply]
    exact Subtype.ext h
  have hN2 : ∀ n : ↥(blockU K₀), n ^ 2 = 1 := fun n =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hU2 _ n.2)
  have hβk : (MonoidHom.id ↥(blockU K₀)).ker = (⊥ : Subgroup G).subgroupOf (blockU K₀) := by
    rw [Subgroup.bot_subgroupOf]
    exact MonoidHom.ker_id
  exact S.false_of_closing_model h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ (C1.le_normalizer_blockU K₀) (Zc := ⊥) bot_le hU2 hUc hcommA he2U hlA hN2
    (blockLiftConj hshort α hα hker) hS₀ hFix α hα (MonoidHom.id _) hβk hβe

end Setting

end CFSG.Quasithin.H13.A5
