module

public import CFSG.RankThree.GF2n.Stroth80.Sec117KAut
public import CFSG.RankThree.GF2n.Stroth80.Sec117KKernel
import CFSG.RankThree.GF2n.Stroth80.Sec117KInv
import CFSG.RankThree.GF2n.Stroth80.Sec117KLB
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

private theorem Ctx.mul_comm_of_mem_subgroupOf [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {x y : ↥(Xbar M Q Z B)} (hx : x ∈ (bar M Q (LB M Q B)).subgroupOf (Xbar M Q Z B))
    (hy : y ∈ (bar M Q (LB M Q B)).subgroupOf (Xbar M Q Z B)) : x * y = y * x := by
  have h := hc.isElemAbelian_bar_LB.1.is_comm.comm
    (⟨(x : Mbar M Q), Subgroup.mem_subgroupOf.mp hx⟩ : ↥(bar M Q (LB M Q B)))
    ⟨(y : Mbar M Q), Subgroup.mem_subgroupOf.mp hy⟩
  have h2 : (x : Mbar M Q) * y = y * x := congrArg Subtype.val h
  exact Subtype.ext h2

private theorem odd_orderOf_of_odd_orderOf_mk {X : Type*} [Group X]
    (hZ : Odd (Nat.card (Subgroup.center X))) {g : X}
    (hg : Odd (orderOf (g : X ⧸ Subgroup.center X))) : Odd (orderOf g) := by
  have h1 : g ^ orderOf (g : X ⧸ Subgroup.center X) ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  have h2 := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ h1)
  rw [← pow_mul] at h2
  exact (hg.mul hZ).of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)

private theorem Ctx.mk_mem_bar_LB [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {a₀ : G} (ha₀ : a₀ ∈ LB M Q B) :
    (QuotientGroup.mk (⟨a₀, hc.LB_le_M ha₀⟩ : ↥M) : Mbar M Q) ∈ bar M Q (LB M Q B) := by
  rw [bar, Subgroup.mem_map]
  exact ⟨⟨a₀, hc.LB_le_M ha₀⟩, Subgroup.mem_subgroupOf.mpr ha₀, rfl⟩

theorem Ctx.isKLConfig_mk [Finite G] [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n a : ℕ} (hw : Width Q Z n) (hn : 2 < n) (ha : Nat.card Z = 2 ^ a)
    {a₀ : G} (ha₀ : a₀ ∈ LB M Q B) (hA : IsA2 Q Z a₀) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a₀, hc.LB_le_M ha₀⟩ : ↥M)) :
    IsKLConfig (t : XbarMod M Q Z B) a
      ((hc.a2PlaneKernel a₀).map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))))
      (((bar M Q (LB M Q B)).subgroupOf (Xbar M Q Z B)).map
        (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)))) where
  involution := hc.isStrothInvolution_mk hw hn ⟨a₀, ha₀, hA⟩ ha (by
    rw [ht]
    exact hc.mk_mem_Ebar ha₀ hA)
  kernel := hc.isA2PlaneKernel_mk ha ha₀ hA ht
  isPGroup := hc.isPGroup_bar_LB.comap_subtype.map _
  comm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc.mul_comm_of_mem_subgroupOf hx hy]
  mem := by
    have hmem : (t : Mbar M Q) ∈ bar M Q (LB M Q B) := by
      rw [ht]
      exact hc.mk_mem_bar_LB ha₀
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hmem)
  conj_mem := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨l, hl, rfl⟩
    refine ⟨h * l * h⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
    have hN := hc.mem_normalizer_bar_LB_of_mem_a2PlaneKernel ha₀ hA hh
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp (Subgroup.mem_subgroupOf.mp hl)
  eq_one := by
    rintro _ ⟨h, hh, rfl⟩ hodd hcen
    rw [hc.eq_one_of_mem_a2PlaneKernel hw hn ha₀ hA hh
      (odd_orderOf_of_odd_orderOf_mk (g := h) hc.odd_card_center_Xbar hodd)
      (fun l hl => hcen _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl))),
      map_one]

theorem Ctx.isLBImage_map [Finite G] [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n a : ℕ} (hw : Width Q Z n) (hn : 2 < n) (ha : Nat.card Z = 2 ^ a)
    {a₀ : G} (ha₀ : a₀ ∈ LB M Q B) (hA : IsA2 Q Z a₀) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a₀, hc.LB_le_M ha₀⟩ : ↥M)) :
    IsLBImage (t : XbarMod M Q Z B) a n
      ((hc.a2PlaneKernel a₀).map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))))
      ((bar M Q (LB M Q B)).map hc.xbarModConj) where
  sq_eq_one _ he := hc.sq_eq_one_of_mem_map_xbarModConj he
  conj_mem := by
    refine ⟨(t : Mbar M Q), ?_, hc.xbarModConj_coe t⟩
    rw [ht]
    exact hc.mk_mem_bar_LB ha₀
  conj_conj_mem := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨l, hl, rfl⟩
    have hN := hc.mem_normalizer_bar_LB_of_mem_a2PlaneKernel ha₀ hA hh
    refine ⟨(h : Mbar M Q) * l * (h : Mbar M Q)⁻¹, (Subgroup.mem_normalizer_iff.mp hN l).mp hl,
      ?_⟩
    rw [map_mul, map_mul, map_inv, QuotientGroup.mk'_apply, ← hc.xbarModConj_coe]
  card_le := hc.card_map_xbarModConj_ge hw hn ⟨a₀, ha₀, hA⟩ ha

theorem Ctx.exists_isKLConfig [Finite G] [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n a : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (ha : Nat.card Z = 2 ^ a) :
    ∃ (t : XbarMod M Q Z B) (N A : Subgroup (XbarMod M Q Z B))
      (E : Subgroup (MulAut (XbarMod M Q Z B))), IsKLConfig t a N A ∧ IsLBImage t a n N E := by
  obtain ⟨a₀, ha₀, hA⟩ := ha2
  let t : ↥(Xbar M Q Z B) :=
    ⟨QuotientGroup.mk ⟨a₀, hc.LB_le_M ha₀⟩, Subgroup.subset_closure (hc.mk_mem_Ebar ha₀ hA)⟩
  exact ⟨(t : XbarMod M Q Z B), _, _, _, hc.isKLConfig_mk hw hn ha ha₀ hA rfl,
    hc.isLBImage_map hw hn ha ha₀ hA rfl⟩

end CFSG.RankThree.GF2n.Stroth80
