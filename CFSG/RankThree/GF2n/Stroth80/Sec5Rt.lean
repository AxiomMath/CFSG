module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs
import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_LB_inf_QB_mem_sup (hc : Ctx M Q Z B) {l : G} (hl : l ∈ LB M Q B) {a : G}
    (ha : a ∈ Q ⊓ QB B) : ⁅l, a⁆ ∈ (Z ⊔ B : Subgroup G) := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hsZ : s * ⁅y, a⁆ * s⁻¹ ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) _).mp
      (hc.hyp.toHyp79.comm_mem_V hy ha.1)
    simpa using this
  have e : ⁅s * y, a⁆ = (s * ⁅y, a⁆ * s⁻¹) * ⁅s, a⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Z ⊔ B : Subgroup G).mul_mem (Subgroup.mem_sup_left hsZ)
    (Subgroup.mem_sup_right (hc.comm_QB_le_B hs.1 ha.2))

omit [Finite G] in
theorem conjSubgroup_le_Rt {L : Subgroup G} {t m : G} (hm : m ∈ M) (htm : t ∈ conjSubgroup m L) :
    conjSubgroup m L ≤ Rt M L t := by
  unfold Rt
  exact le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl)

theorem Ctx.Tt_comm_le_inf_QB (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {m : G} (hm : m ∈ M)
    (htm : t ∈ conjSubgroup m (LB M Q B)) :
    ⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers t⁆ ≤ Q ⊓ QB (conjSubgroup m B) := by
  have hcC := hc.conj_of_mem hm
  have htC : t ∈ LB M Q (conjSubgroup m B) := by rw [hc.LB_conj hm]; exact htm
  refine Subgroup.commutator_le.mpr fun x hx u hu => ?_
  have hx' : x ∈ Q ⊓ Subgroup.centralizer (Vt M (LB M Q B) B Z t : Set G) := hx
  have hxC : x ∈ Q ⊓ Subgroup.centralizer ((conjSubgroup m B : Subgroup G) : Set G) :=
    ⟨hx'.1, Subgroup.centralizer_le (fun b hb => sec39_conjB_le_Vt hm htm hb) hx'.2⟩
  have huC : u ∈ LB M Q (conjSubgroup m B) := Subgroup.zpowers_le.mpr htC hu
  rw [← commutatorElement_inv]
  exact (Q ⊓ QB (conjSubgroup m B)).inv_mem (hcC.comm_mem_inf_of_mem_LB huC hxC)

theorem Ctx.comm_Rt_Tt_le_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ Tt Q Z (Vt M (LB M Q B) B Z t) t,
      ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  set V := Vt M (LB M Q B) B Z t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  let S : Subgroup G :=
    { carrier := {s | s ∈ Subgroup.normalizer (V : Set G) ∧ ∀ x ∈ Tt Q Z V t, ⁅s, x⁆ ∈ V}
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨(Subgroup.normalizer (V : Set G)).mul_mem haN hbN, fun x hx => ?_⟩
        have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine V.mul_mem ?_ (ha x hx)
        simpa using (Subgroup.mem_normalizer_iff.mp haN _).mp (hb x hx)
      one_mem' := ⟨(Subgroup.normalizer (V : Set G)).one_mem, fun x _ => by
        simpa [commutatorElement_def] using V.one_mem⟩
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨(Subgroup.normalizer (V : Set G)).inv_mem haN, fun x hx => ?_⟩
        have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem haN)
          _).mp (V.inv_mem (ha x hx))
        simpa using this }
  have hle : Rt M (LB M Q B) t ≤ S := by
    unfold Rt
    refine iSup₂_le fun m hm => iSup_le fun htm l hl => ?_
    have hlR : l ∈ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm htm hl
    refine ⟨hc.Rt_normalizes_Vt ht hlR, fun x hx => ?_⟩
    have hcC := hc.conj_of_mem hm
    have hlC : l ∈ LB M Q (conjSubgroup m B) := by rw [hc.LB_conj hm]; exact hl
    have hZCV : (Z ⊔ conjSubgroup m B : Subgroup G) ≤ V := sup_le hZV (sec39_conjB_le_Vt hm htm)
    have hH := hc.Tt_comm_le_inf_QB ht hm htm
    have hHN : ⁅Wt Q V, Subgroup.zpowers t⁆ ≤ Subgroup.normalizer (Z : Set G) :=
      (hH.trans inf_le_left).trans (hc.hyp.Q_normal.1.trans hc.hyp.Z_normal.2)
    obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hHN hx
    have h1 : ⁅l, z⁆ = 1 := by
      rw [commutatorElement_def, hcC.LB_centralizes_Z hlC z hz]; group
    have e : ⁅l, a * z⁆ = ⁅l, a⁆ * (a * ⁅l, z⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, h1]
    simpa using hZCV (hcC.comm_LB_inf_QB_mem_sup hlC (hH ha))
  intro s hs x hx
  exact (hle hs).2 x hx

end CFSG.RankThree.GF2n.Stroth80
