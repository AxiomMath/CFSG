module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem step93L2AltXH_CN_inv (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hsc : StronglyClosedMod M Z0 (LB M Q B))
    (hVt : ∀ s ∈ Z0, s ∉ Q →
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t)
    {g : G} (hgM : g ∈ M) (hgL : conjSubgroup g (LB M Q B) = LB M Q B) :
    conjSubgroup g (LB M Q B ⊓ hc.CN t) = LB M Q B ⊓ hc.CN t := by
  classical
  set L : Subgroup G := LB M Q B with hL
  set N : Subgroup G := hc.CN t with hN
  have htL : t ∈ L := hs.mem
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) htL hZ0
  have htQ : t ∉ Q := hs.notQ
  have hgLinv : conjSubgroup g⁻¹ L = L := by
    calc conjSubgroup g⁻¹ L = conjSubgroup g⁻¹ (conjSubgroup g L) := by rw [hgL]
      _ = conjSubgroup (g⁻¹ * g) L := by rw [← CFSG.RankThree.GF2n.conjSubgroup_mul]
      _ = L := by rw [inv_mul_cancel, CFSG.RankThree.GF2n.conjSubgroup_one]
  have htLg : g * t * g⁻¹ ∈ L := by
    have hx : t ∈ conjSubgroup g⁻¹ L := by rw [hgLinv]; exact htL
    simpa [inv_inv] using (mem_conjSubgroup.mp hx)
  have htZg : g * t * g⁻¹ ∈ Z0 := hsc t htZ g hgM htLg
  have hQginv : conjSubgroup g⁻¹ Q = Q := by
    calc conjSubgroup g⁻¹ Q = conjSubgroup g⁻¹ (conjSubgroup g Q) := by rw [hc.conj_Q_eq hgM]
      _ = conjSubgroup (g⁻¹ * g) Q := by rw [← CFSG.RankThree.GF2n.conjSubgroup_mul]
      _ = Q := by rw [inv_mul_cancel, CFSG.RankThree.GF2n.conjSubgroup_one]
  have htQg : g * t * g⁻¹ ∉ Q := by
    intro hq
    apply htQ
    have hx : t ∈ conjSubgroup g⁻¹ Q := by
      rw [mem_conjSubgroup]
      simpa [inv_inv] using hq
    rwa [hQginv] at hx
  have hR : Rt M L (g * t * g⁻¹) = Rt M L t :=
    Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 htZg htQg
  have hV : Vt M L B Z (g * t * g⁻¹) = Vt M L B Z t := hVt _ htZg htQg
  have hCN : hc.CN (g * t * g⁻¹) = N := by
    ext x
    change x ∈ CNt M L B Z (g * t * g⁻¹) ↔ x ∈ CNt M L B Z t
    unfold CNt
    rw [hR, hV]
  have hCNg : conjSubgroup g N = N := by
    rw [← Ctx.CN_conjM hc hgM t]
    exact hCN
  change conjSubgroup g (L ⊓ N) = L ⊓ N
  rw [conjSubgroup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) L = L from hgL,
    show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) N = N from hCNg]

end HS9

end CFSG.RankThree.GF2n.Stroth80
