module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_iSup_conj_frame {L B' : Subgroup G} {h : G} (hh : h ∈ M) (s : G) :
    (⨆ (m : G) (_ : m ∈ M) (_ : s ∈ conjSubgroup m (conjSubgroup h L)),
        conjSubgroup m (conjSubgroup h B')) =
      ⨆ (m : G) (_ : m ∈ M) (_ : s ∈ conjSubgroup m L), conjSubgroup m B' := by
  refine le_antisymm (iSup_le fun m => iSup_le fun hm => iSup_le fun hs => ?_)
    (iSup_le fun m => iSup_le fun hm => iSup_le fun hs => ?_)
  · have e : conjSubgroup m (conjSubgroup h B') = conjSubgroup (m * h) B' :=
      (conjSubgroup_mul m h B').symm
    have hs' : s ∈ conjSubgroup (m * h) L := by
      rw [conjSubgroup_mul]
      exact hs
    rw [e]
    exact le_iSup₂_of_le (m * h) (M.mul_mem hm hh) (le_iSup_of_le hs' le_rfl)
  · have hmh : m * h⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hh)
    have e : conjSubgroup (m * h⁻¹) (conjSubgroup h B') = conjSubgroup m B' := by
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
    have e' : conjSubgroup (m * h⁻¹) (conjSubgroup h L) = conjSubgroup m L := by
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
    have hs' : s ∈ conjSubgroup (m * h⁻¹) (conjSubgroup h L) := by
      rw [e']
      exact hs
    rw [← e]
    exact le_iSup₂_of_le (m * h⁻¹) hmh (le_iSup_of_le hs' le_rfl)

theorem sec7ctr_Rt_conj_frame {L : Subgroup G} {h : G} (hh : h ∈ M) (s : G) :
    Rt M (conjSubgroup h L) s = Rt M L s := by
  unfold Rt
  exact sec7ctr_iSup_conj_frame (B' := L) hh s

theorem sec7ctr_Vt_conj_frame {L B' : Subgroup G} {h : G} (hh : h ∈ M) (s : G) :
    Vt M (conjSubgroup h L) (conjSubgroup h B') Z s = Vt M L B' Z s := by
  unfold Vt
  rw [sec7ctr_iSup_conj_frame hh s]

theorem sec7ctr_CN_conj_frame (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) (s : G) :
    (hc.conj_of_mem hh).CN s = hc.CN s := by
  ext x
  rw [Ctx.mem_CN, Ctx.mem_CN, hc.LB_conj hh, sec7ctr_Rt_conj_frame hh s,
    sec7ctr_Vt_conj_frame hh s]

theorem sec7ctr_OmegaPlusNat_conj_frame (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) (s : G)
    (m : ℕ) : OmegaPlusNat (hc.conj_of_mem hh) s m ↔ OmegaPlusNat hc s m := by
  unfold OmegaPlusNat
  rw [sec7ctr_CN_conj_frame hc hh s, hc.LB_conj hh, sec7ctr_Rt_conj_frame hh s,
    sec7ctr_Vt_conj_frame hh s]

theorem sec7ctr_OmegaMinusNat_conj_frame (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) (s : G)
    (m : ℕ) : OmegaMinusNat (hc.conj_of_mem hh) s m ↔ OmegaMinusNat hc s m := by
  unfold OmegaMinusNat
  rw [sec7ctr_CN_conj_frame hc hh s, hc.LB_conj hh, sec7ctr_Rt_conj_frame hh s,
    sec7ctr_Vt_conj_frame hh s]

theorem sec7ctr_IsA2_conj {g : G} (hgQ : conjSubgroup g Q = Q) (hgZ : conjSubgroup g Z = Z)
    {a : G} (ha : IsA2 Q Z a) : IsA2 Q Z (g * a * g⁻¹) := by
  unfold IsA2 at ha ⊢
  obtain ⟨hN, hQa, hsq, hcard, hab⟩ := ha
  have hgN : g ∈ Subgroup.normalizer (Q : Set G) := conjSubgroup_eq_self_iff.mp hgQ
  have hmemQ : ∀ x : G, g * x * g⁻¹ ∈ Q ↔ x ∈ Q := by
    intro x
    have h1 := mem_conjSubgroup (g := g) (T := Q) (x := g * x * g⁻¹)
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [hgQ, e] at h1
    exact h1
  have hzp : conjSubgroup g (Subgroup.zpowers a) = Subgroup.zpowers (g * a * g⁻¹) := by
    have h : (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := rfl
    rw [← h]
    exact MonoidHom.map_zpowers _ _
  have hU : ⁅Q, Subgroup.zpowers (g * a * g⁻¹)⁆ ⊔ Z =
      conjSubgroup g (⁅Q, Subgroup.zpowers a⁆ ⊔ Z) :=
    Ut_conj_of_normalizes hgQ hgZ a
  have hC : ⁅Q, Subgroup.zpowers (g * a * g⁻¹)⁆ = conjSubgroup g ⁅Q, Subgroup.zpowers a⁆ := by
    rw [conjSubgroup_commutator, hgQ, hzp]
  refine ⟨?_, fun h => hQa ((hmemQ a).mp h), ?_, ?_, ?_⟩
  · exact (Subgroup.normalizer (Q : Set G)).mul_mem
      ((Subgroup.normalizer (Q : Set G)).mul_mem hgN hN)
      ((Subgroup.normalizer (Q : Set G)).inv_mem hgN)
  · rw [conj_pow]
    exact (hmemQ _).mpr hsq
  · rw [hU, CFSG.CGT.Timmesfeld75.card_conjSubgroup]
    exact hcard
  · rw [hC]
    exact CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup hab g

theorem sec7ctr_NoA2_conj (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) {L : Subgroup G}
    (hL : NoA2 Q Z L) : NoA2 Q Z (conjSubgroup h L) := by
  unfold NoA2 at hL ⊢
  intro a ha hA
  rw [mem_conjSubgroup] at ha
  have hA' := sec7ctr_IsA2_conj (hc.conj_Q_eq (M.inv_mem hh)) (hc.conj_Z_eq (M.inv_mem hh)) hA
  rw [inv_inv] at hA'
  exact hL _ ha hA'

end CFSG.RankThree.GF2n.Stroth80
