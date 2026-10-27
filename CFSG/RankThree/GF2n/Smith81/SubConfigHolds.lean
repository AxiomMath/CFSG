module

public import CFSG.RankThree.GF2n.Smith81.SubConfigNorm
import CFSG.RankThree.GF2n.Smith81.OrthE1Small
import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Rt_mul_eq {M Q L : Subgroup G} (hQ : ∀ m ∈ M, Q ≤ conjSubgroup m L) {q t : G}
    (hq : q ∈ Q) : Rt M L (q * t) = Rt M L t := by
  unfold Rt
  refine iSup_congr fun m => iSup_congr fun hm => ?_
  have h : q * t ∈ conjSubgroup m L ↔ t ∈ conjSubgroup m L := by
    constructor
    · intro h
      have := (conjSubgroup m L).mul_mem ((conjSubgroup m L).inv_mem (hQ m hm hq)) h
      simpa using this
    · exact fun h => (conjSubgroup m L).mul_mem (hQ m hm hq) h
  exact iSup_congr_Prop h fun _ => rfl

section Holds

variable [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem Q_le_conj_LB (H : StrothHyp M Q Z) {m : G} (hm : m ∈ M) :
    Q ≤ conjSubgroup m (LB M Q B) := by
  intro x hx
  rw [mem_conjSubgroup]
  refine le_sup_left (a := Q) (b := QB B ⊓ M) ?_
  have := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (inv_mem hm)) x).mp hx
  simpa using this

theorem mem_Nt_of_mem_conj (hc : Ctx M Q Z B) {m₀ : G} (hm₀ : m₀ ∈ M)
    (ht : t ∈ conjSubgroup m₀ (LB M Q B)) : t ∈ Nt M (LB M Q B) t := by
  have htR : t ∈ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm₀ ht ht
  haveI : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M t hx)
  have hp : IsPGroup 2 (Q.subgroupOf (Rt M (LB M Q B) t)) :=
    (isPGroup_Q' hc.hyp).comap_of_injective _ (Subgroup.subtype_injective _)
  have ht2 : t ^ 2 ∈ Q := by
    have h1 := hc.sq_mem_Q_of_mem_LB (mem_conjSubgroup.mp ht)
    have h2 : m₀⁻¹ * t ^ 2 * m₀ ∈ Q := by
      have e : (m₀⁻¹ * t * m₀) ^ 2 = m₀⁻¹ * t ^ 2 * m₀ := by
        rw [pow_two, pow_two]
        group
      rwa [e] at h1
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm₀) _).mp h2
    simpa [mul_assoc] using this
  have hx2 : (⟨t, htR⟩ : ↥(Rt M (LB M Q B) t)) ^ 2 ∈ Q.subgroupOf (Rt M (LB M Q B) t) := by
    rw [Subgroup.mem_subgroupOf]
    simpa using ht2
  have hcore : (⟨t, htR⟩ : ↥(Rt M (LB M Q B) t)) ∈ pCore 2 ↥(Rt M (LB M Q B) t) := by
    apply Smith23E1.mem_pCore_two_of_comm hp hx2
    intro g
    rw [Subgroup.mem_subgroupOf]
    have h := hc.Rt_comm_mem_Q g.2
    simpa [commutatorElement_def] using h
  exact Subgroup.mem_map.mpr ⟨⟨t, htR⟩, hcore, rfl⟩

variable [(Q.subgroupOf (H0 M Z)).Normal]

theorem bar_t_mem_subCfgZ (hc : Ctx M Q Z B) {m₀ : G} (hm₀ : m₀ ∈ M)
    (ht : t ∈ conjSubgroup m₀ (LB M Q B)) (htH : t ∈ H0 M Z) :
    (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨t, htH⟩ : SubCfgGroup M Q Z) ∈
      SubCfgZ M Q Z (Nt M (LB M Q B) t) := by
  rw [SubCfgZ, cen_eq]
  refine ⟨Subgroup.mem_map.mpr ⟨⟨t, htH⟩, mem_Nt_of_mem_conj hc hm₀ ht, rfl⟩, ?_⟩
  show _ ∈ Subgroup.centralizer _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
  have hnR : (n : G) ∈ Rt M (LB M Q B) t := Nt_le_Rt _ _ _ (Subgroup.mem_subgroupOf.mp hn)
  have hcomm := hc.Rt_comm_mem_Q hnR
  rw [← map_mul, ← map_mul]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf]
  have e : (((n * ⟨t, htH⟩)⁻¹ * (⟨t, htH⟩ * n) : ↥(H0 M Z)) : G) =
      (t : G)⁻¹ * (n : G)⁻¹ * ⁅(n : G), t⁆⁻¹ * (n : G) * t := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [e]
  have h1 : (t : G)⁻¹ * ((n : G)⁻¹ * ⁅(n : G), t⁆⁻¹ * (n : G)) * t ∈ Q := by
    have hnM : (n : G) ∈ M := (n.2 : (n : G) ∈ H0 M Z).1
    have htM : t ∈ M := htH.1
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (inv_mem hnM)) _).mp
      (Q.inv_mem hcomm)
    have h3 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (inv_mem htM)) _).mp h2
    simpa [mul_assoc] using h3
  simpa [mul_assoc] using h1

theorem subConfigNorm_of (hc : Ctx M Q Z B) (h1 : 1 < Nat.card (Nt M (LB M Q B) t))
    {B' : Subgroup (SubCfgGroup M Q Z)}
    (hctx' : Ctx (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B') : SubConfigNorm M Q Z B t B' := by
  obtain ⟨m₀, hm₀, ht⟩ := exists_mem_conj_of_one_lt h1
  have htR : t ∈ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm₀ ht ht
  have htH : t ∈ H0 M Z := Rt_le_H0 hc t htR
  have htZ := bar_t_mem_subCfgZ hc hm₀ ht htH
  have hnorm : ∀ h : ↥(H0 M Z), (h : G) * t * (h : G)⁻¹ * t⁻¹ ∈ Q →
      (h : G) ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) := by
    intro h hq
    rw [← conjSubgroup_eq_self_iff, conjSubgroup_Rt_eq (h.2 : (h : G) ∈ H0 M Z).1]
    have e : (h : G) * t * (h : G)⁻¹ = ((h : G) * t * (h : G)⁻¹ * t⁻¹) * t := by group
    rw [e, Rt_mul_eq (fun m hm => Q_le_conj_LB hc.hyp hm) hq]
  have hle : bar (H0 M Z) Q (Subgroup.normalizer (Rt M (LB M Q B) t : Set G)) ≤
      Subgroup.normalizer (bar (H0 M Z) Q (Rt M (LB M Q B) t) : Set (SubCfgGroup M Q Z)) :=
    bar_le_normalizer le_rfl
  intro y hy
  have hyC : y ∈ Subgroup.centralizer (SubCfgZ M Q Z (Nt M (LB M Q B) t) : Set _) :=
    ((Lgen_le_H0 hctx') hy).2
  have hyt := Subgroup.mem_centralizer_iff.mp hyC _ htZ
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf (H0 M Z)) y
  refine hle (Subgroup.mem_map.mpr ⟨h, hnorm h ?_, rfl⟩)
  rw [← map_mul, ← map_mul] at hyt
  have h2 := QuotientGroup.eq.mp hyt
  rw [Subgroup.mem_subgroupOf] at h2
  have e : (((⟨t, htH⟩ : ↥(H0 M Z)) * h)⁻¹ * (h * ⟨t, htH⟩) : ↥(H0 M Z)) =
      (h⁻¹ * ⟨t, htH⟩⁻¹ * (h * ⟨t, htH⟩ * h⁻¹ * ⟨t, htH⟩⁻¹) * ⟨t, htH⟩ * h :
        ↥(H0 M Z)) := by group
  rw [e] at h2
  have hhM : (h : G) ∈ M := (h.2 : (h : G) ∈ H0 M Z).1
  have htM : t ∈ M := htH.1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have h3 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) _).mp
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hhM) _).mp h2)
  simpa [mul_assoc] using h3

theorem one_lt_card_Nt (hc : Ctx M Q Z B) {w : ℕ}
    (hN : Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ^ w) :
    1 < Nat.card (Nt M (LB M Q B) t) := by
  rw [hN]
  have hQ : 4 ≤ Nat.card Q := hc.hyp.q4.trans (Subgroup.card_le_of_le hc.hyp.Z_normal.1)
  have hZ : 1 ≤ Nat.card Z ^ w := Nat.one_le_pow _ _ Nat.card_pos
  nlinarith

end Holds

theorem subConfigE4NormStatement_holds :
    SubConfigE4NormStatement := by
  intro G _ _ M Q Z B t _ hE h4 _ hH' B' hB'c hB'le hB'ne _
  exact subConfigNorm_of hE.ctx (one_lt_card_Nt hE.ctx h4.2.1) ⟨hH', hB'c, hB'le, hB'ne⟩

theorem subConfigE5NormStatement_holds :
    SubConfigE5NormStatement := by
  intro G _ _ M Q Z B t _ hE h5 _ hH' B' hB'c hB'le hB'ne _
  exact subConfigNorm_of hE.ctx (one_lt_card_Nt hE.ctx h5.2.1) ⟨hH', hB'c, hB'le, hB'ne⟩

theorem subConfigE4Statement_holds : SubConfigE4Statement :=
  subConfigE4_of_norm subConfigE4NormStatement_holds

theorem subConfigE5Statement_holds : SubConfigE5Statement :=
  subConfigE5_of_norm subConfigE5NormStatement_holds

end CFSG.RankThree.GF2n.Smith81.SubCfg
