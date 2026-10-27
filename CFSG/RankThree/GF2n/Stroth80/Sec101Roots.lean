module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem IsRootB.LB_eq_iff {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {D E : Subgroup G}
    (hD : IsRootB M B D) (hE : IsRootB M B E) : LB M Q D = LB M Q E ↔ D ⊔ Z = E ⊔ Z := by
  constructor
  · intro h
    obtain ⟨g, hgM, rfl⟩ := hD.exists_conj hE
    have hcE := hE.ctx hc
    rw [hcE.LB_conj hgM] at h
    have hgN : g ∈ Subgroup.normalizer (LB M Q E : Set G) :=
      conjSubgroup_eq_self_iff.mp h
    have hgV : g ∈ Subgroup.normalizer ((E ⊔ Z : Subgroup G) : Set G) :=
      (hcE.mem_normalizer_LB_iff' (hE.sec10 H).width (hE.sec10 H).n_gt
        (hE.sec10 H).noA2 hgM).mp hgN
    have hconj := conjSubgroup_eq_self_iff.mpr hgV
    rwa [conjSubgroup_sup', hc.conj_Z_eq hgM] at hconj
  · intro h
    have hEctx : Ctx M Q Z E := hE.ctx hc
    have hEsec : Sec10Hyp hEctx n := hE.sec10 H
    obtain ⟨d, hdM, rfl⟩ := hD
    obtain ⟨e, heM, rfl⟩ := hE
    let m : G := d * e⁻¹
    have hmM : m ∈ M := M.mul_mem hdM (M.inv_mem heM)
    have hDm : conjSubgroup d B = conjSubgroup m (conjSubgroup e B) := by
      rw [← conjSubgroup_mul]
      congr 1
      dsimp only [m]
      group
    have hV : conjSubgroup m (conjSubgroup e B ⊔ Z) = conjSubgroup e B ⊔ Z := by
      rw [conjSubgroup_sup', hc.conj_Z_eq hmM, ← hDm]
      exact h
    have hmN : m ∈ Subgroup.normalizer (LB M Q (conjSubgroup e B) : Set G) :=
      (hEctx.mem_normalizer_LB_iff' hEsec.width hEsec.n_gt hEsec.noA2 hmM).mpr
        (conjSubgroup_eq_self_iff.mp hV)
    rw [hDm, hEctx.LB_conj hmM, conjSubgroup_eq_self_iff.mpr hmN]

theorem IsRootB.Rt_ne {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {D E : Subgroup G}
    (hD : IsRootB M B D) (hE : IsRootB M B E) {t : G}
    (htE : t ∈ LB M Q E) (hne : D ⊔ Z ≠ E ⊔ Z) : Rt M (LB M Q D) t ≠ LB M Q D := by
  intro hRt
  obtain ⟨g, hgM, rfl⟩ := hE.exists_conj hD
  have hcD := hD.ctx hc
  have ht : t ∈ conjSubgroup g (LB M Q D) := by
    rwa [← hcD.LB_conj hgM]
  have hle : LB M Q (conjSubgroup g D) ≤ LB M Q D := by
    have := hcD.LB_conj_le_Rt hgM ht
    rwa [hRt] at this
  have hcard : Nat.card (LB M Q (conjSubgroup g D)) = Nat.card (LB M Q D) := by
    rw [hcD.LB_conj hgM, card_conjSubgroup]
  have heq : LB M Q (conjSubgroup g D) = LB M Q D :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  exact hne ((IsRootB.LB_eq_iff H hD (IsRootB.conj hD hgM)).mp heq.symm)

theorem IsRootB.exists_good101 (hc : Ctx M Q Z B) {E : Subgroup G} (hE : IsRootB M B E) {t : G}
    (ht : Good101 M Q Z E t) : ∃ s : G, Good101 M Q Z B s := by
  obtain ⟨m, hmM, rfl⟩ := hE
  refine ⟨m⁻¹ * t * (m⁻¹)⁻¹, ?_⟩
  have h := Good101.conjG (hc := hc.conj_of_mem hmM) ht m⁻¹
  simpa only [hc.conj_M_eq (M.inv_mem hmM), hc.conj_Q_eq (M.inv_mem hmM),
    hc.conj_Z_eq (M.inv_mem hmM), conjSubgroup_conjSubgroup, inv_inv,
    inv_mul_cancel, conjSubgroup_one] using h

end CFSG.RankThree.GF2n.Stroth80
