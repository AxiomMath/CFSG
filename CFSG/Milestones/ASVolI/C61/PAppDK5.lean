module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK5
public import CFSG.Milestones.ASVolI.C61.PAppDK3
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.burnsideC56_P.DoubleA3
open CFSG.QuasithinUnique.DoubleA3 hiding A3A3 A3A3.V_isPGroup A3A3.blockU0_eq A3A3.center_L0
  A3A3.comm_elem A3A3.conjJoin_ne A3A3.conj_cases A3A3.inf_Ls A3A3.inf_S_L0 A3A3.isA4 A3A3.isA4s
  A3A3.isShort A3A3.isSylowTwoOf_V A3A3.le_normalizer_V A3A3.normalizer_conjR exists_A3A3

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

namespace A3x
open CFSG.QuasithinUnique.AppD.A3x

variable (h : A3A3 T M H S L s)
include h

theorem hQ_cent :
    H ⊓ Subgroup.centralizer ((blockU L ⊔ blockU2 L s : Subgroup G) : Set G) = pCoreOf 2 H := by
  have hLb : IsBlock2 H L := h.cs.block.1
  have hL : ∀ i : Fin 2, IsBlock2 H (![L, conjR L s] i) := by
    intro i
    fin_cases i
    · exact hLb
    · exact CFSG.Quasithin.IsBlock2.conjByElt_of_mem hLb (H.inv_mem (h.cs.sylow.le h.s_mem))
  have hcomm : ∀ i j : Fin 2, i ≠ j → ⁅(![L, conjR L s] i), (![L, conjR L s] j)⁆ = ⊥ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h.comm
    · rw [Subgroup.commutator_comm]; exact h.comm
    · exact absurd rfl hij
  have hperm : ∀ t ∈ S, ∀ i : Fin 2, ∃ j : Fin 2,
      conjSubgroup (![L, conjR L s] i) t = ![L, conjR L s] j := by
    intro t ht i
    fin_cases i
    · rcases h.conj_cases (hU0 h) ht with ⟨-, a⟩ | ⟨-, a⟩
      · exact ⟨0, a⟩
      · exact ⟨1, a⟩
    · have hst : s * t ∈ S := S.mul_mem h.s_mem ht
      have e : conjSubgroup (conjR L s) t = conjR L (s * t) := conjSubgroup_conjSubgroup L s t
      rcases h.conj_cases (hU0 h) hst with ⟨-, a⟩ | ⟨-, a⟩
      · exact ⟨0, by show conjSubgroup (conjR L s) t = L; rw [e]; exact a⟩
      · exact ⟨1, by show conjSubgroup (conjR L s) t = conjR L s; rw [e]; exact a⟩
  have hKT : (⨆ i : Fin 2, ![L, conjR L s] i) ⊔ S = H := by
    rw [iSup_fin_two_eq]
    show L ⊔ conjR L s ⊔ S = H
    rw [← h.join, ← h.cs.eq_join]
  have := Setup.Campbell.commuting_short_product_core_centralizer h.cs.sylow (s := 2) (by norm_num)
    ![L, conjR L s] hL hcomm hperm hKT
  have hU : (⨆ i : Fin 2, blockU (![L, conjR L s] i)) = blockU L ⊔ blockU2 L s := by
    rw [iSup_fin_two_eq]
    show blockU L ⊔ blockU (conjR L s) = blockU L ⊔ blockU2 L s
    rw [blockU_conjR]
    rfl
  have h4 := this.2.2.2.1
  rw [hU] at h4
  exact h4

theorem U_inf_D : (blockU L ⊔ blockU2 L s) ⊓ blockD S L = ⊥ := by
  rw [← hUeq h]
  refine eq_bot_iff.2 fun x hx => ?_
  have hxK : x ∈ conjJoin S L := by
    have : blockU0 S L ≤ conjJoin S L := by
      rw [hUeq h, h.join]
      exact sup_le (h.isA4.le.trans le_sup_left) (h.isA4s.le.trans le_sup_right)
    exact this hx.1
  have := h.center_L0 x hxK fun l hl => (Subgroup.mem_centralizer_iff.1 hx.2.2 l hl).symm
  exact Subgroup.mem_bot.2 this

theorem card_K : Nat.card ↥(conjJoin S L) = 144 := by
  have hA := h.isA4
  have hAs := h.isA4s
  have := C5.card_sup_mul_card_inf_of_le_normalizer (C5.le_normalizer_of_commute h.comm_elem)
  rw [h.inf_Ls, Subgroup.card_bot, mul_one, hA.card_L, hAs.card_L] at this
  rw [h.join]
  omega

theorem U_le_K : blockU L ⊔ blockU2 L s ≤ conjJoin S L := by
  rw [h.join]
  exact sup_le (h.isA4.le.trans le_sup_left) (h.isA4s.le.trans le_sup_right)

variable {h}

include h in
theorem U_le_Q : blockU L ⊔ blockU2 L s ≤ pCoreOf 2 H := by
  rw [← hUeq h, hU0 h]
  exact C56.pCoreOf_conjJoin_le h.cs

theorem Q_le_sup_D (sp : Spec h) :
    pCoreOf 2 H ≤ (blockU L ⊔ blockU2 L s) ⊔ blockD S L := by
  intro q hq
  set K := conjJoin S L with hK
  set U := blockU L ⊔ blockU2 L s with hU
  have hqH : q ∈ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H hq
  have hqS : q ∈ S := C56.pCoreOf_le_S h.cs hq
  have hqN : q ∈ Subgroup.normalizer (K : Set G) := C56.H_le_normalizer_conjJoin h.cs hqH
  have hqC : ∀ u ∈ U, u * q = q * u := by
    intro u hu
    have : q ∈ H ⊓ Subgroup.centralizer (U : Set G) := by rw [hQ_cent h]; exact hq
    exact Subgroup.mem_centralizer_iff.1 this.2 u hu
  have hUK : U ≤ K := U_le_K h
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := h.le_normalizer_V
  have hNnormal : (U.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).2 hKU
  have hNab : ∀ a ∈ U.subgroupOf K, ∀ b ∈ U.subgroupOf K, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext ((C5.isElemAbelian_two_iff.1 sp.kp.elemAbelian_sup).1 _
      (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have hN : Nat.card ↥(U.subgroupOf K) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv).trans sp.kp.card_sup
  have h1 : ∀ n ∈ U.subgroupOf K, conjK hqN n = n := by
    intro n hn
    have hu : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn
    refine Subtype.ext ?_
    show q * (n : G) * q⁻¹ = n
    rw [← hqC _ hu]
    group
  have hU0S : blockU0 S L ≤ S := by rw [hUeq h]; exact U_le_S (h := h)
  have h2 : ∀ x : ↥K, conjK hqN x * x⁻¹ ∈ U.subgroupOf K := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    set e : G := q * (x : G) * q⁻¹ * (x : G)⁻¹ with he
    have hxH : (x : G) ∈ H := by
      have : K ≤ H := by rw [h.cs.eq_join]; exact le_sup_left
      exact this x.2
    have heK : e ∈ K := (conjK hqN x * x⁻¹).2
    have heQ : e ∈ pCoreOf 2 H := by
      have : (x : G) * q⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.1
          (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H hxH) q⁻¹).1
          (inv_mem hq)
      have e2 : e = q * ((x : G) * q⁻¹ * (x : G)⁻¹) := by rw [he]; group
      rw [e2]
      exact mul_mem hq this
    have heS : e ∈ S ⊓ conjJoin S L := ⟨C56.pCoreOf_le_S h.cs heQ, heK⟩
    rw [h.inf_S_L0 (hU0 h) hU0S, hUeq h] at heS
    exact heS
  obtain ⟨n, hn, hφ⟩ := exists_conj_of_trivial_on_quotient (U.subgroupOf K) hNab hN
    (card_K h) (conjK hqN) h1 h2
  have hu : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn
  have hconj : ∀ k ∈ K, q * k * q⁻¹ = (n : G) * k * (n : G)⁻¹ := by
    intro k hk
    exact congrArg Subtype.val (hφ ⟨k, hk⟩)
  set q' := (n : G)⁻¹ * q with hq'
  have hq'S : q' ∈ S := mul_mem (inv_mem (U_le_S (h := h) hu)) hqS
  have hq'C : q' ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := hconj k hk
    calc k * ((n : G)⁻¹ * q) = (n : G)⁻¹ * ((n : G) * k * (n : G)⁻¹) * q := by group
      _ = (n : G)⁻¹ * (q * k * q⁻¹) * q := by rw [this]
      _ = ((n : G)⁻¹ * q) * k := by group
  have hq'D : q' ∈ blockD S L := ⟨hq'S, hq'C⟩
  have hqe : q = (n : G) * q' := by rw [hq']; group
  rw [hqe]
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hq'D)

include h in
theorem D_le_Q : blockD S L ≤ pCoreOf 2 H := by
  intro d hd
  rw [← hQ_cent h]
  exact ⟨h.cs.sylow.le hd.1, Subgroup.centralizer_le
    (SetLike.coe_subset_coe.2 (U_le_K h)) hd.2⟩

theorem Q_eq (sp : Spec h) : pCoreOf 2 H = (blockU L ⊔ blockU2 L s) ⊔ blockD S L :=
  le_antisymm (Q_le_sup_D sp) (sup_le (U_le_Q (h := h)) (D_le_Q (h := h)))

end A3x

end CFSG.QuasithinUnique.burnsideC56_P.AppD
