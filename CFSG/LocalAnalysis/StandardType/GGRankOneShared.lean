module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSharedInvolution
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

theorem ggRankOneIn_isComponentOf_centralizer [Finite G] {X Bs : Subgroup G} {r : MulAut ↥Bs}
    {z : G} (hz : z ∈ ggHyperplane Bs r) (hX : IsSubnormal X (Subgroup.centralizer ({z} : Set G)))
    (hq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r)) :
    IsComponentOf (ggRankOneIn X Bs r) (Subgroup.centralizer (ggHyperplane Bs r : Set G)) := by
  set H := Subgroup.centralizer (ggHyperplane Bs r : Set G)
  have hSle : ggRankOneIn X Bs r ≤ X ⊓ H := ggOTwoPrime_le _
  have hHz : H ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hXH : IsSubnormal (X ⊓ H) H := hX.inf_of_le hHz
  have hnorm : ((ggOTwoPrime (X ⊓ H)).subgroupOf (X ⊓ H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (ggOTwoPrime_le (X ⊓ H))]
    intro h g hh hg
    have hY : (X ⊓ H).map (MulAut.conj g).toMonoidHom = X ⊓ H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh
    rw [ggOTwoPrime_map_conj, hY] at hmem
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  exact ⟨hSle.trans inf_le_right, IsSubnormal.step hSle hnorm hXH, hq⟩

theorem mem_ggAutomizer_ggRankOneIn [Finite G] {X Bs : Subgroup G} {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer X Bs) (hr2 : r ^ 2 = 1) :
    r ∈ ggAutomizer (ggRankOneIn X Bs r) Bs := by
  obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp hr
  have hgC : g ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hrb : r b = b := hb
    have h := hg b
    rw [hrb] at h
    change (b : G) * g = g * b
    calc (b : G) * g = g * b * g⁻¹ * g := by rw [← h]
      _ = g * b := by group
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have h2 : (g ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hrm : r ^ m = r := by
    obtain ⟨t, rfl⟩ := hm
    rw [pow_succ, pow_mul, hr2, one_pow, one_mul]
  have hind : ∀ n : ℕ, ∀ b : ↥Bs, (((r ^ n) b : ↥Bs) : G) = g ^ n * b * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [pow_succ, MulAut.mul_apply, ih, hg b, pow_succ, mul_inv_rev]
      group
  refine mem_ggAutomizer_iff.mpr ⟨g ^ m, ?_, Subgroup.pow_mem _ hgN m, fun b => ?_⟩
  · exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hgX m, Subgroup.pow_mem _ hgC m⟩, k, h2⟩
  · rw [← hind m b, hrm]

theorem normalizer_ggRankOneIn [Finite G] {X Bs : Subgroup G}
    (hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hBX : Bs ≤ Subgroup.normalizer (X : Set G))
    (r : MulAut ↥Bs) :
    Bs ≤ Subgroup.normalizer (ggRankOneIn X Bs r : Set G) := by
  intro b hb
  have hbC : b ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, -, rfl⟩
    exact hcomm _ c.2 b hb
  have hX : X.map (MulAut.conj b).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBX hb)
  have hC : (Subgroup.centralizer (ggHyperplane Bs r : Set G)).map (MulAut.conj b).toMonoidHom =
      Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hbC)
  have key : (ggRankOneIn X Bs r).map (MulAut.conj b).toMonoidHom = ggRankOneIn X Bs r := by
    rw [ggRankOneIn, ggOTwoPrime_map_conj, Subgroup.map_inf _ _ _ (MulAut.conj b).injective, hX,
      hC]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key

theorem ggRankOneIn_eq_of_mem_ggAutomizer [Finite G] {p : ℕ} (hp : Odd p) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {X Z : Subgroup G} {x z : G} (hxB : x ∈ Bs) (hzB : z ∈ Bs)
    (hX : IsSubnormal X (Subgroup.centralizer ({x} : Set G)))
    (hZ : IsSubnormal Z (Subgroup.centralizer ({z} : Set G)))
    (hBZ : Bs ≤ Subgroup.normalizer (Z : Set G)) {r : MulAut ↥Bs}
    (hrX : r ∈ ggAutomizer X Bs) (hrZ : r ∈ ggAutomizer Z Bs)
    (hqX : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r))
    (hqZ : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn Z Bs r))
    (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1) : ggRankOneIn X Bs r = ggRankOneIn Z Bs r := by
  have hH : ∀ {Y : Subgroup G} {v : G}, v ∈ Bs → Y ≤ Subgroup.centralizer ({v} : Set G) →
      r ∈ ggAutomizer Y Bs → v ∈ ggHyperplane Bs r := by
    intro Y v hvB hY hrY
    obtain ⟨g, hgY, -, hg⟩ := mem_ggAutomizer_iff.mp hrY
    have hgv : g * v * g⁻¹ = v := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hY hgY), mul_inv_cancel_right]
    refine Subgroup.mem_map.mpr ⟨⟨v, hvB⟩, ?_, rfl⟩
    change r ⟨v, hvB⟩ = ⟨v, hvB⟩
    exact Subtype.ext ((hg ⟨v, hvB⟩).trans hgv)
  exact (eq_of_isComponentOf_of_mem_ggAutomizer
    (ggRankOneIn_isComponentOf_centralizer (hH hzB hZ.le hrZ) hZ hqZ)
    (ggRankOneIn_isComponentOf_centralizer (hH hxB hX.le hrX) hX hqX)
    (fun b hb h => eq_one_of_mul_self_eq_one_of_isElemAbelian hp hBs hb h)
    (normalizer_ggRankOneIn (fun c hc d hd => hBs.comm hc hd) hBZ r)
    (mem_ggAutomizer_ggRankOneIn hrZ hr2) (mem_ggAutomizer_ggRankOneIn hrX hr2) hr2 hr1).symm

end CFSG.StandardType

end
