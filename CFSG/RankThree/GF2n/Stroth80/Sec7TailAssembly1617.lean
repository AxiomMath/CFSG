module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step716_mk_mul_comm [(Q.subgroupOf M).Normal] {a b : M}
    (h : ⁅(a : G), (b : G)⁆ ∈ Q) :
    QuotientGroup.mk' (Q.subgroupOf M) a * QuotientGroup.mk' (Q.subgroupOf M) b =
      QuotientGroup.mk' (Q.subgroupOf M) b * QuotientGroup.mk' (Q.subgroupOf M) a := by
  have hmem : ⁅a, b⁆ ∈ Q.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h)
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

theorem step716_le_of_fstar [(Q.subgroupOf M).Normal] {K A N : Subgroup G}
    (hKM : K ≤ M) (hQN : Q ≤ N) (hAK : A ≤ K) (hAn : ∀ k ∈ K, conjSubgroup k A = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ Q)
    (hF : generalizedFitting ↥(bar M Q K) = (bar M Q N).subgroupOf (bar M Q K)) :
    A ≤ N := by
  have hconj : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A := fun k hk a ha =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp (hAn k hk)) a).mp ha
  obtain ⟨Ab, hAb⟩ : ∃ Ab : Subgroup ↥(bar M Q K), Ab = (bar M Q A).subgroupOf (bar M Q K) :=
    ⟨_, rfl⟩
  have hmemAb : ∀ x : ↥(bar M Q K), x ∈ Ab ↔ (x : Mbar M Q) ∈ bar M Q A := fun x => by
    rw [hAb, Subgroup.mem_subgroupOf]
  have hAbN : Ab.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, ha, hna⟩ := Subgroup.mem_map.mp ((hmemAb n).mp hn)
    obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.mp g.2
    rw [hmemAb, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hna, ← hgy,
      ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (hconj _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp ha)))
  have hcomm : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp ((hmemAb x).mp hx)
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp ((hmemAb y).mp hy)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby]
    exact step716_mk_mul_comm (hAab _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb))
  haveI : IsMulCommutative ↥Ab := ⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩
  have hAbNil : Group.IsNilpotent ↥Ab := inferInstance
  have hAbF : Ab ≤ generalizedFitting ↥(bar M Q K) := by
    rw [generalizedFitting.eq_sup]
    exact le_sup_of_le_left (le_sSup ⟨hAbN, hAbNil⟩)
  intro a ha
  have haM : a ∈ M := hKM (hAK ha)
  have haK : (⟨a, haM⟩ : M) ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr (hAK ha)
  have haA : (⟨a, haM⟩ : M) ∈ A.subgroupOf M := Subgroup.mem_subgroupOf.mpr ha
  have hmemK : QuotientGroup.mk' (Q.subgroupOf M) ⟨a, haM⟩ ∈ bar M Q K :=
    Subgroup.mem_map_of_mem _ haK
  have heAb : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨a, haM⟩, hmemK⟩ : ↥(bar M Q K)) ∈ Ab :=
    (hmemAb _).mpr (Subgroup.mem_map_of_mem _ haA)
  have heF := hAbF heAb
  rw [hF, Subgroup.mem_subgroupOf] at heF
  exact (mk_mem_bar_iff_sec4 hQN ⟨a, haM⟩).mp heF

theorem step716MaxAb_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
      (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 → ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q →
      generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
      IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0 hirr hN' hF
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hZK : Z0 ≤ NormH0 M Z Z0 := fun z hz => hRK (hZ0.le hz)
  have hKM : NormH0 M Z Z0 ≤ M := fun x hx => hx.1.1
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx,
      fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  refine ⟨hZK, fun x hx y hy => hZ0.comm_mem hx (hZ0.le hy),
    fun k hk => conjSubgroup_eq_self_iff.mpr hk.2, ?_⟩
  intro A hZA hAK hAn hAab
  have hAN : A ≤ hc.CN t := step716_le_of_fstar hKM hQN hAK hAn hAab hF
  have hRA : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A := fun r hr => hAn r (hRK hr)
  rcases hirr.2.2.2 A hZA hAN hRA with h | h
  · exact h
  · exfalso
    apply hN'
    refine Subgroup.commutator_le.mpr fun x hx y hy => hAab x ?_ y ?_
    · rw [h]; exact hx
    · rw [h]; exact hy

end CFSG.RankThree.GF2n.Stroth80
