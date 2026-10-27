module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
import CFSG.RankThree.GF2n.Stroth80.Sec7TailSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem mem_normalizer_bar_iff [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {y : G}
    (hy : y ∈ M) :
    QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy⟩ ∈
        Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ↔
      y ∈ Subgroup.normalizer (LB M Q B : Set G) :=
  ⟨fun h => mem_normalizer_of_mk_mem_normalizer_bar sec39_Q_le_LB hc.LB_le_M ⟨y, hy⟩ h,
    fun h => mk_mem_normalizer_bar_of_normalizer sec39_Q_le_LB ⟨y, hy⟩ h⟩

private theorem exists_normalizing_conj_LB [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} {Z0 : Subgroup G} (cfg : HS9.Cfg95 hc n t Z0) {s g : G}
    (hsZ0 : s ∈ Z0) (hgM : g ∈ M) (hgs : g * s * g⁻¹ ∈ LB M Q B) :
    ∃ z : M, QuotientGroup.mk' (Q.subgroupOf M) z ∈
        Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ∧
      ((z : G) * s * (z : G)⁻¹)⁻¹ * (g * s * g⁻¹) ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsLB : s ∈ LB M Q B := (Subgroup.mem_inf.mp (cfg.centre.1 hsZ0)).1
  have hsM : s ∈ M := hc.LB_le_M hsLB
  have hgsM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hsM) (M.inv_mem hgM)
  have hcomm : bar M Q (LB M Q B) ≤
      Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hss : QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M) ∈ bar M Q (LB M Q B) :=
    (mk_mem_bar_iff_sec4 sec39_Q_le_LB _).mpr hsLB
  have hgg : QuotientGroup.mk' (Q.subgroupOf M) (⟨g * s * g⁻¹, hgsM⟩ : M) ∈
      bar M Q (LB M Q B) :=
    (mk_mem_bar_iff_sec4 sec39_Q_le_LB _).mpr hgs
  have hB : ({(QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M))} : Set (Mbar M Q)) ⊆
      Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hcomm hss
  have hBg : (fun b => QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M) * b *
        (QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M))⁻¹) ''
      ({(QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M))} : Set (Mbar M Q)) ⊆
      Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    show QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M) *
        QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M) *
        (QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M))⁻¹ ∈
      Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q))
    have hconj : QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M) *
          QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M) *
          (QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M))⁻¹ =
        QuotientGroup.mk' (Q.subgroupOf M) (⟨g * s * g⁻¹, hgsM⟩ : M) := by
      simp only [← map_mul, ← map_inv]
      rfl
    rw [hconj]
    exact hcomm hgg
  obtain ⟨nn, hnn, hneq⟩ := CFSG.LargeExtraspecial.lemma_3_12
    (B := ({(QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M))} : Set (Mbar M Q)))
    (g := QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M))
    hc.isElemAbelian_bar_LB.isPGroup
    (fun x hx => hc.weaklyClosed_bar_LB cfg.hs.toSec5.width cfg.hs.toSec5.n_gt
      cfg.hs.toSec5.noA2 x hx) hB hBg
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) nn
  refine ⟨z, hnn, ?_⟩
  have hz := hneq (QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hsM⟩ : M)) (Set.mem_singleton _)
  simp only [← map_mul, ← map_inv] at hz
  have hq := QuotientGroup.eq.mp hz
  rw [Subgroup.mem_subgroupOf] at hq
  simpa using hq

theorem step95Choice_holds : Step95ChoiceStatement := by
  intro G _ _ M Q Z B hc n t Z0 cfg
  haveI hQN : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨s, hsZ0, g, hgM, hgs, hgsZ⟩ := cfg.hnsc
  obtain ⟨z, hzNbar, hq⟩ := exists_normalizing_conj_LB hc cfg hsZ0 hgM hgs
  have hzN : (z : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (mem_normalizer_bar_iff hc z.2).mp hzNbar
  have hzLB : conjSubgroup (z : G) (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr hzN
  have htoN1 : ∀ c ∈ Z0, (z : G) * c * (z : G)⁻¹ ∈ LB M Q B ⊓ hc.CN t := by
    intro c hcZ0
    have hcLB : c ∈ LB M Q B := (Subgroup.mem_inf.mp (cfg.centre.1 hcZ0)).1
    have hzc : (z : G) * c * (z : G)⁻¹ ∈ LB M Q B :=
      (Subgroup.mem_normalizer_iff.mp hzN c).mp hcLB
    exact ⟨hzc, cfg.hbad c hcZ0 (z : G) z.2 hzc⟩
  have hnotN : ∃ c ∈ Z0, (z : G) * c * (z : G)⁻¹ ∉ Z0 := by
    refine ⟨s, hsZ0, fun hcontra => hgsZ ?_⟩
    have hQZ0 : Q ≤ Z0 := hc.Q_le_centre cfg.hs.toSec5.mem cfg.hZ0
    have h2 : ((z : G) * s * (z : G)⁻¹)⁻¹ * (g * s * g⁻¹) ∈ Z0 := hQZ0 hq
    have e : g * s * g⁻¹ = ((z : G) * s * (z : G)⁻¹) *
        (((z : G) * s * (z : G)⁻¹)⁻¹ * (g * s * g⁻¹)) := by
      group
    rw [e]
    exact Z0.mul_mem hcontra h2
  exact ⟨(z : G), { mem := z.2, normL := hzLB, toN1 := htoN1, notN := hnotN }⟩

end CFSG.RankThree.GF2n.Stroth80
