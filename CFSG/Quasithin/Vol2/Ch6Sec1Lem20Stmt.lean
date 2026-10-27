module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20Four
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19W

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_centralizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.centralizer (A : Set G))
    (hB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hA a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hB b hb)
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

namespace Hyp6116

theorem ZS_le_conjSub (_h : Hyp6116 G T M L V n) {x : G}
    (hx : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) : ch6ZS T L V ≤ conjSub x V := by
  have h1 := conjSub_mono x (inf_le_left : ch6ZS T L V ≤ V)
  rwa [conjSub_eq_of_mem_normalizer' (Subgroup.centralizer_le_normalizer _ hx)] at h1

theorem commutator_conjSub_le (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) {x : G}
    (hx : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) :
    ⁅V, conjSub x V⁆ ≤ ch6ZS T L V := by
  obtain ⟨hUO, hUOZ⟩ := h.lemma_6_1_20_one h432
  exact (Subgroup.commutator_mono (le_conjClosure V _)
    ((Hyp6116.conjSub_le_conjClosure hx).trans hUO)).trans hUOZ

theorem le_normalizer_conjSub (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) {x : G}
    (hx : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) :
    V ≤ Subgroup.normalizer (conjSub x V : Set G) := by
  intro v hv
  refine mem_normalizer_of_forall_conj_mem_of_le fun w hw => ?_
  have hc : v * w * v⁻¹ * w⁻¹ ∈ conjSub x V :=
    h.ZS_le_conjSub hx (h.commutator_conjSub_le h432 hx
      (Subgroup.commutator_mem_commutator hv hw))
  have e : v * w * v⁻¹ = (v * w * v⁻¹ * w⁻¹) * w := by group
  rw [e]
  exact Subgroup.mul_mem _ hc hw

theorem eq_sup_of_commutator_ne (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (h : Hyp6116 G T M L V n) {g : G} (hg : g ∈ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) =
      V ⊔ conjSubgroup V g ⊔
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          Subgroup.centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G)) := by
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have heq : conjSubgroup V g = conjSub g⁻¹ V := rfl
  rw [heq] at hne ⊢
  have hgi : g⁻¹ ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := Subgroup.inv_mem _ hg
  have hUN : U ≤ Subgroup.normalizer (V : Set G) :=
    (h.conjClosure_le_S h432).trans (inf_le_left.trans h.toHyp611.T_le_normalizer)
  have hU1 := (h.le_sup_inf_centralizer h432 h6110 hgi hne).1
  have hne2 : ⁅V, conjSub g V⁆ ≠ ⊥ := by
    intro h0
    apply hne
    have h1 := congrArg (conjSub g⁻¹) h0
    rw [conjSub_commutator', conjSub_conjSub_inv, Subgroup.commutator_comm] at h1
    rw [h1]
    unfold conjSub
    exact Subgroup.map_bot _
  have hU2' := (h.le_sup_inf_centralizer h432 h6110 hg hne2).1
  have hU2 : U ≤ V ⊔ (U ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G)) := by
    have h1 := conjSub_mono g⁻¹ hU2'
    have hUg : conjSub g⁻¹ U = U := conjSub_eq_of_mem_normalizer'
      (le_normalizer_conjClosure V _ hgi)
    have e : conjSub g⁻¹ (conjSub g V ⊔ (U ⊓ Subgroup.centralizer (V : Set G))) =
        V ⊔ (U ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G)) := by
      have hsup : ∀ (y : G) (A B : Subgroup G), conjSub y (A ⊔ B) = conjSub y A ⊔ conjSub y B :=
        fun y A B => Subgroup.map_sup A B _
      rw [hsup, conjSub_conjSub_inv, conjSub_inf, hUg, conjSub_centralizer']
    rwa [hUg, e] at h1
  have hle1 : conjSub g⁻¹ V ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro a ha
    have haU := (Hyp6116.conjSub_le_conjClosure hgi) ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer haU, F7.normalizer_le_normalizer_centralizer _ (hUN haU)⟩
  have hle2 : V ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G) : Subgroup G) : Set G) := by
    intro b hb
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (le_conjClosure V _ hb),
        F7.normalizer_le_normalizer_centralizer _ (h.le_normalizer_conjSub h432 hgi hb)⟩
  apply le_antisymm
  · intro u hu
    have hu1 := hU1 hu
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle1] at hu1
    obtain ⟨a, ha, c, hc, rfl⟩ := hu1
    have hc2 := hU2 hc.1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle2] at hc2
    obtain ⟨b, hb, d, hd, rfl⟩ := hc2
    have hdV : d ∈ Subgroup.centralizer (V : Set G) := by
      have e : d = b⁻¹ * (b * d) := by group
      rw [e]
      refine Subgroup.mul_mem _ ?_ hc.2
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hy (V.inv_mem hb)
    have hdC : d ∈ U ⊓ Subgroup.centralizer ((V ⊔ conjSub g⁻¹ V : Subgroup G) : Set G) :=
      ⟨hd.1, mem_centralizer_sup hdV hd.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ha))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hb))
        (Subgroup.mem_sup_right hdC))
  · exact sup_le (sup_le (le_conjClosure V _) (Hyp6116.conjSub_le_conjClosure hgi)) inf_le_left

theorem le_or_le_of_isElemAbelian (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (h : Hyp6116 G T M L V n) {g : G} (hg : g ∈ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    ∀ A : Subgroup G, A ≤ V ⊔ conjSubgroup V g → IsElemAbelian 2 A →
      A ≤ V ∨ A ≤ conjSubgroup V g := by
  have heq : conjSubgroup V g = conjSub g⁻¹ V := rfl
  rw [heq] at hne ⊢
  have hgi : g⁻¹ ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := Subgroup.inv_mem _ hg
  set W := conjSub g⁻¹ V with hW
  have hWU : W ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
    Hyp6116.conjSub_le_conjClosure hgi
  have hWS : W ≤ ch6S T L V := hWU.trans (h.conjClosure_le_S h432)
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := hWS.trans (inf_le_left.trans
    h.toHyp611.T_le_normalizer)
  have hZW : ch6ZS T L V ≤ W := h.ZS_le_conjSub hgi
  have hcZ : ⁅V, W⁆ ≤ ch6ZS T L V := h.commutator_conjSub_le h432 hgi
  have hidx := (h.le_sup_inf_centralizer h432 h6110 hgi hne).2
  have hCW : W ⊓ Subgroup.centralizer (V : Set G) = ch6ZS T L V := by
    have hZle : ch6ZS T L V ≤ W ⊓ Subgroup.centralizer (V : Set G) :=
      le_inf hZW fun z hz => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hy hz.1
    have h1 := card_mul_relIndex_of_le (inf_le_left : W ⊓ Subgroup.centralizer (V : Set G) ≤ W)
    rw [hidx, card_conjSub', h.toHyp611Nat.natural.card_eq] at h1
    have h2 : Nat.card ↥(W ⊓ Subgroup.centralizer (V : Set G)) = 2 ^ n :=
      Nat.eq_of_mul_eq_mul_right (by positivity) h1
    exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [h2, h.toHyp611Nat.card_ZS])).symm
  have hinv : ∀ x ∈ V ⊔ W, x ^ 2 = 1 → x ∈ V ∨ x ∈ W := by
    intro x hx hx2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWN] at hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hx
    by_cases hwZ : w ∈ ch6ZS T L V
    · exact Or.inl (V.mul_mem hv hwZ.1)
    by_cases hvZ : v ∈ ch6ZS T L V
    · exact Or.inr (W.mul_mem (hZW hvZ) hw)
    exfalso
    have hwV : w ∉ Subgroup.centralizer (V : Set G) := fun hwc => hwZ (hCW ▸ ⟨hw, hwc⟩)
    have hCV := h.toHyp611Nat.centralizer_singleton_eq_ZS (hWS hw) hwV
    have hvw : v * w ≠ w * v := by
      intro e
      apply hvZ
      rw [← hCV]
      exact ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr e⟩
    have hc : w * v * w⁻¹ * v⁻¹ ∈ ch6ZS T L V := by
      have := Subgroup.commutator_mem_commutator hw hv
      rw [Subgroup.commutator_comm] at this
      exact hcZ this
    have hcv : (w * v * w⁻¹ * v⁻¹) * v = v * (w * v * w⁻¹ * v⁻¹) :=
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hc.1 hv
    have hv2 : v * v = 1 := by rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 v hv
    have hw2 : w * w = 1 := by
      have := h.toHyp611.isElemAbelian.2 _ (mem_conjSub.mp hw)
      have e : (g⁻¹⁻¹ * w * g⁻¹) ^ 2 = g⁻¹⁻¹ * (w * w) * g⁻¹ := by rw [pow_two]; group
      rw [e] at this
      have e2 : w * w = g⁻¹ * (g⁻¹⁻¹ * (w * w) * g⁻¹) * g⁻¹⁻¹ := by group
      rw [e2, this]
      group
    apply hvw
    have hsq : (v * w) ^ 2 = w * v * w⁻¹ * v⁻¹ := by
      calc (v * w) ^ 2 = v * (w * v * w⁻¹ * v⁻¹ * v * w) * w := by rw [pow_two]; group
        _ = v * (v * (w * v * w⁻¹ * v⁻¹) * w) * w := by rw [hcv]
        _ = (v * v) * (w * v * w⁻¹ * v⁻¹) * (w * w) := by group
        _ = w * v * w⁻¹ * v⁻¹ := by rw [hv2, hw2]; group
    rw [hsq] at hx2
    calc v * w = (w * v * w⁻¹ * v⁻¹)⁻¹ * (w * v) := by group
      _ = w * v := by rw [hx2, inv_one, one_mul]
  intro A hA hAel
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haA, haV⟩ := Set.not_subset.mp hcon.1
  obtain ⟨b, hbA, hbW⟩ := Set.not_subset.mp hcon.2
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have hb2 : b ^ 2 = 1 := hAel.2 b hbA
  have haW : a ∈ W := (hinv a (hA haA) ha2).resolve_left haV
  have hbV : b ∈ V := (hinv b (hA hbA) hb2).resolve_right hbW
  rcases hinv (a * b) (hA (A.mul_mem haA hbA)) (hAel.2 _ (A.mul_mem haA hbA)) with hab | hab
  · apply haV
    have e : a = (a * b) * b⁻¹ := by group
    rw [e]
    exact V.mul_mem hab (V.inv_mem hbV)
  · apply hbW
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact W.mul_mem (W.inv_mem haW) hab

theorem lemma_6_1_20_four (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h : Hyp6116 G T M L V n) :
    IsElemAbelianMod (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          Subgroup.centralizer (V : Set G)) ∧
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          Subgroup.centralizer (V : Set G)).relIndex
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) = 2 ^ n ∧
      ∀ g ∈ Subgroup.centralizer (ch6ZS T L V : Set G), ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
        conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) =
          V ⊔ conjSubgroup V g ⊔
            (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
              Subgroup.centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G)) ∧
        ∀ A : Subgroup G, A ≤ V ⊔ conjSubgroup V g → IsElemAbelian 2 A →
          A ≤ V ∨ A ≤ conjSubgroup V g := by
  have hUS := h.conjClosure_le_S h432
  refine ⟨h.toHyp611Nat.isElemAbelianMod_of_le_S hUS, ?_, fun g hg hne =>
    ⟨h.eq_sup_of_commutator_ne h432 h6110 hg hne, h.le_or_le_of_isElemAbelian h432 h6110 hg hne⟩⟩
  obtain ⟨x, hx, hne⟩ := h.exists_commutator_ne h432 h6111 h6119
  have hidx := (h.le_sup_inf_centralizer h432 h6110 hx hne).2
  refine le_antisymm (h.toHyp611Nat.relIndex_le_of_le_S hUS) ?_
  rw [Subgroup.inf_relIndex_left]
  rw [Subgroup.inf_relIndex_left] at hidx
  rw [← hidx]
  exact Subgroup.relIndex_le_of_le_right (Hyp6116.conjSub_le_conjClosure hx)
    (relIndex_ne_zero' _ _)

end Hyp6116

end CFSG.Quasithin.H13
