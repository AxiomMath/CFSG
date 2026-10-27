module

public import CFSG.RankThree.GF2n.Stroth80.Sec117KAut
import CFSG.RankThree.GF2n.Stroth80.Sec117U3
import CFSG.RankThree.GF2n.Stroth80.Sec117U3Line
import CFSG.RankThree.GF2n.Stroth80.Sec117U3Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

private theorem Ctx.exists_mem_LB_mk_mem_centralizer_Xbar_of_card_lt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hw : Width Q Z 3)
    (hlt : Nat.card ((bar M Q (LB M Q B)).map hc.xbarModConj) < Nat.card Z ^ 2) :
    ∃ u : G, ∃ hu : u ∈ LB M Q B, u ∉ Q ∧
      (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  have hne : bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≠ ⊥ := by
    intro hbot
    have hge := hc.card_bar_LB_ge_two hw (by norm_num)
    rw [hc.card_bar_LB_eq_card_map_mul, hbot, Subgroup.card_bot, mul_one] at hge
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨haLB, haC⟩ := Subgroup.mem_inf.mp a.2
  obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp haLB
  rw [Subgroup.mem_subgroupOf] at hm
  refine ⟨(m : G), hm, ?_, ?_⟩
  · intro huQ
    apply ha1
    refine Subtype.ext ?_
    rw [← hmk]
    exact (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr huQ)
  · have h1 : (QuotientGroup.mk (⟨(m : G), hc.LB_le_M hm⟩ : ↥M) : Mbar M Q) =
        (a : Mbar M Q) := by
      rw [← hmk]
      rfl
    rw [h1]
    exact haC

private theorem Ctx.act_eq_self_of_mem_range_of_forall_hom_eq_one [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hw : Width Q Z 3)
    (hρ : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z → ∀ k ≤ 3,
      ∀ ρ : ↥(Xbar M Q Z B) →* GL (Fin k) K, ρ = 1)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {i : G} (hi : i ∈ LB M Q B)
    (hiX : (QuotientGroup.mk (⟨i, hc.LB_le_M hi⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {g : G} (hg : g ∈ XbarPre M Q Z B) {v : M₀.E}
    (hv : v ∈ LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1)) :
    φ ⟨g, XbarPre_le_H0 hc hg⟩ v = v := by
  set W := LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1) with hWdef
  obtain ⟨ρ, hρW⟩ := exists_Xbar_hom_of_invariant hc φ (fun m hm => (hφker m).mpr hm) W
    fun g' hg' w hw => hc.act_mem_range_of_mem_centralizer hφker hi hiX hg' hw
  obtain ⟨x, -, hZ, -⟩ := hc.hyp.cp
  have hdim := hc.finrank_range_act_le_three hD hw hZ hφker hi
  let e : LinearMap.GeneralLinearGroup K W ≃* GL (Fin (Module.finrank K W)) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K W)).toRingEquiv.toMulEquiv
  have h1 : e.toMonoidHom.comp ρ = 1 := hρ K hD.card _ hdim _
  have hρ1 : ρ = 1 := by
    refine MonoidHom.ext fun y => ?_
    have h3 := DFunLike.congr_fun h1 y
    rw [MonoidHom.comp_apply, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom] at h3
    rw [MonoidHom.one_apply]
    exact e.injective (h3.trans (map_one e).symm)
  have h2 := hρW g hg ⟨v, hv⟩
  rw [hρ1] at h2
  simpa using h2.symm

theorem Ctx.false_of_width_three [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hE : ∀ E : Subgroup (MulAut (XbarMod M Q Z B)), (∀ e ∈ E, e ^ 2 = 1) →
      Nat.card E < Nat.card Z ^ 2)
    (hρ : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z → ∀ k ≤ 3,
      ∀ ρ : ↥(Xbar M Q Z B) →* GL (Fin k) K, ρ = 1) : False := by
  obtain ⟨i, hi, hiQ, hiX⟩ := hc.exists_mem_LB_mk_mem_centralizer_Xbar_of_card_lt hw
    (hE _ fun e he => hc.sq_eq_one_of_mem_map_xbarModConj he)
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, -, -, hB, hcent, -⟩ := hc.dictB hD
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  have hbW := hc.mem_range_act_sub_one_of_mem_LB hD hφπ hφker hφiso hB hcent hi hiQ
  exact hc.false_of_Xbar_act_fix_line ha2 hφπ hB fun g hg =>
    hc.act_eq_self_of_mem_range_of_forall_hom_eq_one hw hρ hD hφker hi hiX hg hbW

end CFSG.RankThree.GF2n.Stroth80
