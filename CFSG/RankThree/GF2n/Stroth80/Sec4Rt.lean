module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec4Quasi

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_bar_LB_le_bar_Rt [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : M}
    (ht : (t : G) ∈ LB M Q B) {y : Mbar M Q}
    (hy : y * QuotientGroup.mk t = QuotientGroup.mk t * y) :
    conjSubgroup y (bar M Q (LB M Q B)) ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hLRt : LB M Q B ≤ Rt M (LB M Q B) (t : G) := by
    have h1 : (t : G) ∈ conjSubgroup (1 : G) (LB M Q B) := by
      rw [conjSubgroup_one]
      exact ht
    have h2 : conjSubgroup (1 : G) (LB M Q B) ≤ Rt M (LB M Q B) (t : G) :=
      le_iSup₂_of_le (1 : G) M.one_mem (le_iSup_of_le h1 le_rfl)
    rwa [conjSubgroup_one] at h2
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  intro z hz
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  have hz' : (w : G) ∈ conjSubgroup (m : G) (LB M Q B) :=
    (mk_mem_conj_bar_iff_sec4 hQL m w).mp hz
  have htm : (t : G) ∈ conjSubgroup (m : G) (LB M Q B) := by
    rw [mem_conjSubgroup]
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (m⁻¹ * t * m) =
        QuotientGroup.mk' (Q.subgroupOf M) t := by
      rw [map_mul, map_mul, map_inv]
      have h0 : (QuotientGroup.mk m : Mbar M Q)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk m =
          QuotientGroup.mk t := by
        calc (QuotientGroup.mk m : Mbar M Q)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk m
            = (QuotientGroup.mk m)⁻¹ * (QuotientGroup.mk m * QuotientGroup.mk t) := by
              rw [mul_assoc, hy]
          _ = QuotientGroup.mk t := by group
      exact h0
    have h2 : t⁻¹ * (m⁻¹ * t * m) ∈ Q.subgroupOf M := QuotientGroup.eq.mp h1.symm
    have e : ((m⁻¹ * t * m : M) : G) = (t : G) * (((t⁻¹ * (m⁻¹ * t * m)) : M) : G) := by
      simp [mul_assoc]
    rw [show (m : G)⁻¹ * (t : G) * (m : G) = ((m⁻¹ * t * m : M) : G) by simp, e]
    exact (LB M Q B).mul_mem ht (hQL (Subgroup.mem_subgroupOf.mp h2))
  have hle : conjSubgroup (m : G) (LB M Q B) ≤ Rt M (LB M Q B) (t : G) :=
    le_iSup₂_of_le (m : G) m.2 (le_iSup_of_le htm le_rfl)
  exact (mk_mem_bar_iff_sec4 (hQL.trans hLRt) w).mpr (hle hz')

theorem Ctx.le_bar_Rt_of_normalClosure [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : M}
    (ht : (t : G) ∈ LB M Q B) {X S : Subgroup (Mbar M Q)} (hSΛ : S ≤ bar M Q (LB M Q B))
    (hSX : S ≤ X)
    (hcl : Subgroup.normalClosure ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) = ⊤)
    (hcent : ∀ x ∈ X, x * QuotientGroup.mk t = QuotientGroup.mk t * x) :
    X ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
  have key : Subgroup.normalClosure ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤
      (bar M Q (Rt M (LB M Q B) (t : G))).subgroupOf X := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le _).mpr fun c hc' => ?_
    obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hc'
    obtain ⟨u, hu⟩ := isConj_iff.mp hac
    have haS : (a : Mbar M Q) ∈ S := ha
    have hmem : (c : Mbar M Q) ∈ conjSubgroup (u : Mbar M Q) (bar M Q (LB M Q B)) := by
      rw [mem_conjSubgroup, ← hu]
      have : (u : Mbar M Q)⁻¹ * (((u * a * u⁻¹ : ↥X)) : Mbar M Q) * (u : Mbar M Q) =
          (a : Mbar M Q) := by simp [mul_assoc]
      rw [this]
      exact hSΛ haS
    exact hc.conj_bar_LB_le_bar_Rt ht (hcent u u.2) hmem
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalClosure ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [hcl]
    exact Subgroup.mem_top _
  exact key h1

theorem Ctx.normal_bar_Lgen [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    (bar M Q (Lgen M (LB M Q B))).Normal :=
  bar_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer (Lgen_le hc.LB_le_M)).mpr
    (Lgen_normalizes M (LB M Q B)))

theorem Ctx.bar_LB_le_bar_Lgen [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    bar M Q (LB M Q B) ≤ bar M Q (Lgen M (LB M Q B)) :=
  Subgroup.map_mono fun x hx => le_Lgen_self M (LB M Q B) hx

theorem Ctx.bar_LB_le_normalizer_of_normal [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {X : Subgroup (Mbar M Q)} (hX : X ≤ bar M Q (Lgen M (LB M Q B)))
    (hXn : (X.subgroupOf (bar M Q (Lgen M (LB M Q B)))).Normal) :
    bar M Q (LB M Q B) ≤ Subgroup.normalizer (X : Set (Mbar M Q)) :=
  hc.bar_LB_le_bar_Lgen.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hX).mp hXn)

theorem Ctx.le_bar_Rt_of_normal_centralizes [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) {Y : Subgroup (Mbar M Q)}
    (hYM : Y ≤ bar M Q (Lgen M (LB M Q B)))
    (hYn : (Y.subgroupOf (bar M Q (Lgen M (LB M Q B)))).Normal) (hYq : CFSG.IsQuasisimple Y)
    {t : M} (ht : (t : G) ∈ LB M Q B)
    (hcent : ∀ x ∈ Y, x * QuotientGroup.mk t = QuotientGroup.mk t * x) :
    Y ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
  have hne : bar M Q (LB M Q B) ⊓ Y ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hYq (hc.bar_LB_le_normalizer_of_normal hYM hYn)
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    odd_card_center_of_normal_normal hc.pCore_two_Mbar hc.normal_bar_Lgen hYM hYn
  have hΛab := hc.isElemAbelian_bar_LB
  have hS2 : IsPGroup 2 ↥((bar M Q (LB M Q B) ⊓ Y).subgroupOf Y) := by
    intro g
    refine ⟨1, ?_⟩
    have hg : ((g : Y) : Mbar M Q) ∈ bar M Q (LB M Q B) := (Subgroup.mem_subgroupOf.mp g.2).1
    apply Subtype.ext
    apply Subtype.ext
    simpa using hΛab.2 _ hg
  have hS1 : (bar M Q (LB M Q B) ⊓ Y).subgroupOf Y ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right)
  exact hc.le_bar_Rt_of_normalClosure ht inf_le_left inf_le_right
    (normalClosure_eq_top_of_quasisimple hYq hodd hS2 hS1) hcent

theorem Rt_le_Lgen' (M L : Subgroup G) (t : G) : Rt M L t ≤ Lgen M L := by
  unfold Rt Lgen
  exact iSup₂_mono fun m hm => iSup_le fun _ => le_rfl

end CFSG.RankThree.GF2n.Stroth80
