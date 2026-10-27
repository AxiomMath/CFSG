module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem21
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem comm_of_mem_inf_centralizer (_h : Hyp6116 G T M L V n) {W C : Subgroup G}
    (hU : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) = V ⊔ W ⊔ C)
    (hC : C ≤ Subgroup.centralizer ((V ⊔ W : Subgroup G) : Set G))
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) {c : G} (hc : c ∈ C) {u : G}
    (hu : u ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) :
    u * c = c * u := by
  have hle : V ⊔ W ⊔ C ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hC hc) y hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hCab y hy c hc)
  rw [hU] at hu
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

theorem le_or_le_of_isElemAbelian_U (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (h : Hyp6116 G T M L V n) {x : G} (hx : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hne : ⁅V, conjSub x V⁆ ≠ ⊥)
    (hRab : IsElemAbelian 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
      Subgroup.centralizer (V : Set G)))
    {A : Subgroup G} (hAU : A ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))
    (hA : IsElemAbelian 2 A) :
    A ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        Subgroup.centralizer (V : Set G) ∨
      A ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        Subgroup.centralizer (conjSub x V : Set G) := by
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hUdef
  have hxi : x⁻¹ ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := Subgroup.inv_mem _ hx
  have heq : conjSubgroup V x⁻¹ = conjSub x V := by
    unfold conjSubgroup conjSub
    rw [inv_inv]
  have hne' : ⁅V, conjSubgroup V x⁻¹⁆ ≠ ⊥ := by rwa [heq]
  have hU := h.eq_sup_of_commutator_ne h432 h6110 hxi hne'
  rw [heq] at hU
  set W := conjSub x V with hW
  set C := U ⊓ Subgroup.centralizer ((V ⊔ W : Subgroup G) : Set G) with hC
  have hCR : C ≤ U ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (le_sup_left : V ≤ V ⊔ W))))
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hRab (hCR ha) (hCR hb)
  have hcomm : ∀ c ∈ C, ∀ u ∈ U, u * c = c * u := fun c hc u hu =>
    h.comm_of_mem_inf_centralizer hU inf_le_right hCab hc hu
  have hAC : IsElemAbelian 2 (A ⊔ C) := by
    have hAC' : A ≤ Subgroup.centralizer (C : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun c hc => (hcomm c hc a (hAU ha)).symm
    refine ⟨⟨⟨fun p q => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · have hcomm' : ∀ a ∈ A ⊔ C, ∀ b ∈ A ⊔ C, a * b = b * a := by
        intro a ha b hb
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (hAC'.trans (Subgroup.centralizer_le_normalizer _))] at ha hb
        obtain ⟨a₁, ha₁, c₁, hc₁, rfl⟩ := ha
        obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := hb
        have e1 := B2F.isElemAbelian_comm hA ha₁ ha₂
        have e2 := hCab c₁ hc₁ c₂ hc₂
        have e3 := hcomm c₂ hc₂ a₁ (hAU ha₁)
        have e4 := hcomm c₁ hc₁ a₂ (hAU ha₂)
        calc a₁ * c₁ * (a₂ * c₂) = a₁ * (c₁ * a₂) * c₂ := by group
          _ = a₁ * (a₂ * c₁) * c₂ := by rw [e4]
          _ = (a₁ * a₂) * (c₁ * c₂) := by group
          _ = (a₂ * a₁) * (c₂ * c₁) := by rw [e1, e2]
          _ = a₂ * (a₁ * c₂) * c₁ := by group
          _ = a₂ * (c₂ * a₁) * c₁ := by rw [e3]
          _ = a₂ * c₂ * (a₁ * c₁) := by group
      exact hcomm' _ p.2 _ q.2
    · rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hAC'.trans (Subgroup.centralizer_le_normalizer _))] at hy
      obtain ⟨a, ha, c, hc, rfl⟩ := hy
      have e := hcomm c hc a (hAU ha)
      rw [pow_two, show a * c * (a * c) = (a * a) * (c * c) by
        calc a * c * (a * c) = a * (c * a) * c := by group
          _ = a * (a * c) * c := by rw [e]
          _ = (a * a) * (c * c) := by group]
      rw [← pow_two, ← pow_two, hA.2 a ha, (hRab.2 c (hCR hc)), one_mul]
  have hVW2 : (A ⊔ C) ⊓ (V ⊔ W) ≤ V ∨ (A ⊔ C) ⊓ (V ⊔ W) ≤ W := by
    have := h.le_or_le_of_isElemAbelian h432 h6110 hxi hne' ((A ⊔ C) ⊓ (V ⊔ W))
      (by rw [heq]; exact inf_le_right) (B2F.isElemAbelian_mono inf_le_left hAC)
    rwa [heq] at this
  have hdec : A ≤ ((A ⊔ C) ⊓ (V ⊔ W)) ⊔ C := by
    intro a ha
    have haU : a ∈ V ⊔ W ⊔ C := hU ▸ hAU ha
    have hCN : C ≤ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
      intro c hc
      exact Subgroup.centralizer_le_normalizer _ (hC ▸ hc).2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN] at haU
    obtain ⟨y, hy, c, hc, rfl⟩ := haU
    have hyAC : y ∈ A ⊔ C := by
      have e : y = y * c * c⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hyAC, hy⟩) (Subgroup.mem_sup_right hc)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.toHyp611.isElemAbelian ha hb
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm (F7.isElemAbelian_conjSub h.toHyp611.isElemAbelian) ha hb
  rcases hVW2 with hle | hle
  · left
    refine hdec.trans (sup_le (hle.trans ?_) hCR)
    exact le_inf (le_conjClosure V _) fun v hv =>
      Subgroup.mem_centralizer_iff.mpr fun w hw => hVab w hw v hv
  · right
    refine hdec.trans (sup_le (hle.trans ?_) ?_)
    · exact le_inf (Hyp6116.conjSub_le_conjClosure hx) fun w hw =>
        Subgroup.mem_centralizer_iff.mpr fun w' hw' => hWab w' hw' w hw
    · exact le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (le_sup_right : W ≤ V ⊔ W))))

theorem mem_normalizer_of_odd {U R R' : Subgroup G} (hRU : R ≤ U) (hR'U : R' ≤ U)
    (hR : IsElemAbelian 2 R) (hR' : IsElemAbelian 2 R') (hcard : Nat.card R' = Nat.card R)
    (hmax : ∀ A : Subgroup G, A ≤ U → IsElemAbelian 2 A → A ≤ R ∨ A ≤ R') {y : G}
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) (hy : Odd (orderOf y)) :
    y ∈ Subgroup.normalizer (R : Set G) := by
  have hconjU : ∀ X : Subgroup G, X ≤ U → conjSub y X ≤ U := fun X hX => by
    have := conjSub_mono y hX
    rwa [conjSub_eq_of_mem_normalizer' hyU] at this
  have hel : ∀ X : Subgroup G, IsElemAbelian 2 X → IsElemAbelian 2 (conjSub y X) :=
    fun X hX => F7.isElemAbelian_conjSub hX
  have hsq : y ^ 2 ∈ Subgroup.normalizer (R : Set G) := by
    rcases hmax _ (hconjU R hRU) (hel R hR) with h1 | h1
    · exact Subgroup.pow_mem _ (mem_normalizer_of_conjSub_le' h1) 2
    · have e1 : conjSub y R = R' :=
        Subgroup.eq_of_le_of_card_ge h1 (by rw [card_conjSub', hcard])
      rcases hmax _ (hconjU R' hR'U) (hel R' hR') with h2 | h2
      · have e2 : conjSub y R' = R :=
          Subgroup.eq_of_le_of_card_ge h2 (by rw [card_conjSub', hcard])
        refine mem_normalizer_of_conjSub_le' ?_
        rw [pow_two, conjSub_mul, e1, e2]
      · have e2 : conjSub y R' = R' :=
          Subgroup.eq_of_le_of_card_ge h2 (by rw [card_conjSub'])
        have hRR' : R = R' := by
          have := congrArg (conjSub y⁻¹) (e1.trans e2.symm)
          rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
        refine Subgroup.pow_mem _ (mem_normalizer_of_conjSub_le' ?_) 2
        rw [e1, ← hRR']
  obtain ⟨k, hk⟩ := hy
  have hy1 : y ^ (orderOf y) = 1 := pow_orderOf_eq_one y
  have e : y = (y ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    calc y = y * y ^ (orderOf y) := by rw [hy1, mul_one]
      _ = y ^ (2 * (k + 1)) := by rw [hk, ← pow_succ']; ring_nf
  rw [e]
  exact Subgroup.pow_mem _ hsq _

end Hyp6116

theorem stmt6_1_22 (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
      ∀ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) →
        let U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))
        U ⊓ conjSubgroup U l < pCoreOf 2 (U ⊔ conjSubgroup U l) := by
  intro G _ _ T M L V n h l hl hlN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hL1 := h21.1.2.2
  rw [hL1] at h21 ⊢
  obtain ⟨-, ⟨hR, -⟩, ⟨hEel, -, -, -⟩, ⟨-, hCE, -⟩, hRN, -⟩ := h21
  have hER : U ⊓ conjSubgroup U l ≤ pCoreOf 2 (L ⊔ U) := by
    rw [← hCE, hR]
    exact inf_le_left.trans le_sup_left
  refine lt_of_le_of_ne hER fun heq => ?_
  have hRU : pCoreOf 2 (L ⊔ U) ≤ U := heq ▸ inf_le_left
  have hRC : pCoreOf 2 (L ⊔ U) = U ⊓ Subgroup.centralizer (V : Set G) := by
    rw [← h.inf_pCoreOf_L1_eq h432]
    exact (inf_eq_right.mpr hRU).symm
  have hRel : IsElemAbelian 2 (U ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hRC, ← heq]
    exact hEel
  obtain ⟨x, hx, hne⟩ := h.exists_commutator_ne h432 h6111 h6119
  have hRx : conjSub x (U ⊓ Subgroup.centralizer (V : Set G)) =
      U ⊓ Subgroup.centralizer (conjSub x V : Set G) := by
    rw [conjSub_inf, conjSub_centralizer',
      conjSub_eq_of_mem_normalizer' (le_normalizer_conjClosure V _ hx)]
  have hmax : ∀ A : Subgroup G, A ≤ U → IsElemAbelian 2 A →
      A ≤ U ⊓ Subgroup.centralizer (V : Set G) ∨
        A ≤ U ⊓ Subgroup.centralizer (conjSub x V : Set G) :=
    fun A hAU hA => h.le_or_le_of_isElemAbelian_U h432 h6110 hx hne hRel hAU hA
  have hRxel : IsElemAbelian 2 (U ⊓ Subgroup.centralizer (conjSub x V : Set G)) := by
    rw [← hRx]
    exact F7.isElemAbelian_conjSub hRel
  have hcard : Nat.card ↥(U ⊓ Subgroup.centralizer (conjSub x V : Set G)) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hRx, card_conjSub']
  have hIU : Subgroup.centralizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure V _
  have hO2 : oTwoUpper (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      Subgroup.normalizer ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    exact Hyp6116.mem_normalizer_of_odd inf_le_left inf_le_left hRel hRxel hcard hmax
      (hIU hy.1) hy.2
  have hTMV : T ≤ ch6MV M V := le_inf h.T_le h.toHyp611.T_le_normalizer
  have hSR : ch6S T L V ≤
      Subgroup.normalizer ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← hRC]
    exact (inf_le_left.trans hTMV).trans hRN
  have hIN : Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' h.toHyp611Nat.isSylowIn_S]
    exact sup_le hO2 hSR
  apply h.not_le
  have hRne : U ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ := by
    intro h0
    apply h.toHyp611.ne_bot
    rw [eq_bot_iff, ← h0]
    exact le_inf (le_conjClosure V _) fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hw hv
  have hLTN : L ⊔ T ≤
      Subgroup.normalizer ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← hRC]
    exact (sup_le (le_inf h.L_le h.toHyp611.L_le_normalizer) hTMV).trans hRN
  refine hIN.trans (le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM h432) hLTN ?_)
  exact ⟨_, hRne, B2F.isPGroup_of_isElemAbelian hRel, rfl⟩

theorem stmt6_1_23 (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
      ∀ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) →
        let U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))
        ∀ S₀ : Subgroup G, S₀ ≤ ch6S T L V → pCoreOf 2 (U ⊔ conjSubgroup U l) ⊔ U ≤ S₀ →
          Subgroup.normalizer (S₀ : Set G) ≤ M := by
  intro G _ _ T M L V n h l hl hlN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  intro S₀ hS₀ hRU
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hL1 := h21.1.2.2
  have hsyl0 := h21.2.1.2
  rw [hL1] at hsyl0 hRU
  have hsyl : IsSylowTwoOf (U ⊔ pCoreOf 2 (L ⊔ U)) (L ⊔ U) := hsyl0
  have hUT := h.U_le_T h432
  have hRT : pCoreOf 2 (L ⊔ U) ≤ T := by
    rw [h.pCoreOf_L1_eq h432]
    exact inf_le_right.trans (F7.isSylowTwoOf_pCoreOf_le h.toHyp611.isSylowIn_T)
  have hNL : U ⊔ pCoreOf 2 (L ⊔ U) ≤ Subgroup.normalizer (L : Set G) :=
    (sup_le hUT hRT).trans h.toHyp611Nat.T_le_normalizer_L
  have hsylL := F7.isSylowTwoOf_inf_normal hsyl le_sup_left hNL
  have hle : (U ⊔ pCoreOf 2 (L ⊔ U)) ⊓ L ≤ S₀ ⊓ L :=
    inf_le_inf_right L (sup_le (le_sup_right.trans hRU) (le_sup_left.trans hRU))
  have hS0L : IsSylowTwoOf (S₀ ⊓ L) L := by
    refine F7.isSylowTwoOf_of_relIndex inf_le_right
      (h.sylow.1.to_le (inf_le_left.trans (hS₀.trans inf_le_left))) fun hd => ?_
    exact F7.isSylowTwoOf_odd_relIndex hsylL
      (hd.trans (Subgroup.relIndex_dvd_of_le_left L hle))
  exact (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).2 S₀ (hS₀.trans inf_le_left) hS0L

end CFSG.Quasithin.H13
