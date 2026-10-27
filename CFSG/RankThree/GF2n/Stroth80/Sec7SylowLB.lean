module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


theorem sec7SylowLB_of_34 (h34 : Stroth34Statement) : Sec7SylowLBStatement := by
  intro G _ _ M Q Z B _ hc n t hs
  classical
  have h5 := hs.toSec5
  have hWC := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).1
  set L : Subgroup (Mbar M Q) := bar M Q (LB M Q B) with hL
  set NL : Subgroup (Mbar M Q) := Subgroup.normalizer (L : Set (Mbar M Q)) with hNL
  have wc : ∀ g : Mbar M Q, conjSubgroup g⁻¹ L ≤ NL → conjSubgroup g⁻¹ L = L :=
    fun g hg => weaklyClosed_bar_of_weaklyClosed sec39_Q_le_LB hc.LB_le_M hWC g hg
  have hLp : IsPGroup 2 L := CFSG.Open.IsElemAbelian.isPGroup (Ctx.isElemAbelian_bar_LB hc)
  obtain ⟨S⟩ : Nonempty (Sylow 2 NL) := inferInstance
  set S' : Subgroup (Mbar M Q) := S.toSubgroup.map NL.subtype with hS'
  have hS'p : IsPGroup 2 S' := S.isPGroup'.map _
  have hS'NL : S' ≤ NL := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hLS' : L ≤ S' := by
    intro l hl
    have hLn : (L.subgroupOf NL).Normal := Subgroup.normal_in_normalizer
    have hLpn : IsPGroup 2 (L.subgroupOf NL) :=
      hLp.comap_of_injective NL.subtype Subtype.val_injective
    have := hLpn.le_sylow_of_normal S
    exact ⟨⟨l, Subgroup.le_normalizer hl⟩, this hl, rfl⟩
  obtain ⟨P, hSP⟩ := hS'p.exists_le_sylow
  refine ⟨P, ?_⟩
  have hmax : P.toSubgroup ⊓ NL ≤ S' := by
    intro x hx
    have hp : IsPGroup 2 ((P.toSubgroup ⊓ NL).subgroupOf NL) :=
      (P.isPGroup'.to_le inf_le_left).comap_of_injective NL.subtype Subtype.val_injective
    have hle : S.toSubgroup ≤ (P.toSubgroup ⊓ NL).subgroupOf NL := by
      intro y hy
      exact Subgroup.mem_subgroupOf.mpr ⟨hSP ⟨y, hy, rfl⟩, y.2⟩
    have heq := S.is_maximal' hp hle
    have hxs : (⟨x, hx.2⟩ : NL) ∈ (P.toSubgroup ⊓ NL).subgroupOf NL :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at hxs
    exact ⟨_, hxs, rfl⟩
  haveI : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  set H : Subgroup P := S'.subgroupOf P.toSubgroup with hH
  have hNH : Subgroup.normalizer (H : Set P) ≤ H := by
    intro y hy
    have hyNL : (y : Mbar M Q) ∈ NL := by
      have hconj : conjSubgroup (y : Mbar M Q)⁻¹ L ≤ NL := by
        intro z hz
        rw [mem_conjSubgroup, inv_inv] at hz
        have hl : (y : Mbar M Q) * z * (y : Mbar M Q)⁻¹ ∈ S' := hLS' hz
        have hlP : (y : Mbar M Q) * z * (y : Mbar M Q)⁻¹ ∈ P.toSubgroup := hSP hl
        have hzP : z ∈ P.toSubgroup := by
          have : z = (y : Mbar M Q)⁻¹ * ((y : Mbar M Q) * z * (y : Mbar M Q)⁻¹) *
              (y : Mbar M Q) := by
            group
          rw [this]
          exact P.toSubgroup.mul_mem (P.toSubgroup.mul_mem (P.toSubgroup.inv_mem y.2) hlP) y.2
        have hmem : (⟨z, hzP⟩ : P) ∈ H := by
          have hy' : y⁻¹ ∈ Subgroup.normalizer (H : Set P) := Subgroup.inv_mem _ hy
          have h1 : y * ⟨z, hzP⟩ * y⁻¹ ∈ H := Subgroup.mem_subgroupOf.mpr hl
          have := (Subgroup.mem_normalizer_iff.mp hy' (y * ⟨z, hzP⟩ * y⁻¹)).mp h1
          simpa [mul_assoc] using this
        exact hS'NL (Subgroup.mem_subgroupOf.mp hmem)
      have h := wc (y : Mbar M Q) hconj
      have := mem_normalizer_of_conjSubgroup_eq h
      simpa using NL.inv_mem this
    exact Subgroup.mem_subgroupOf.mpr (hmax ⟨y.2, hyNL⟩)
  have hHtop : H = ⊤ := by
    by_contra hne
    have hlt := normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr hne)
    exact (lt_irrefl H) (lt_of_lt_of_le hlt hNH)
  intro x hx
  have : (⟨x, hx⟩ : P) ∈ H := hHtop ▸ Subgroup.mem_top _
  exact hS'NL (Subgroup.mem_subgroupOf.mp this)

end CFSG.RankThree.GF2n.Stroth80
