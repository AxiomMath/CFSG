module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerForms

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80.S714
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem mem_NormH0_of_fixes (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {z : G} (hzH : z ∈ H0 M Z)
    (hzV : ∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk (⟨z, hzH.1⟩ : ↥M))).toAdd e = e) :
    z ∈ NormH0 M Z Z0 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hzM : z ∈ M := hzH.1
  set zb : Mbar M Q := QuotientGroup.mk (⟨z, hzM⟩ : ↥M) with hzb
  have hzbH : zb ∈ bar M Q (H0 M Z) := mk_mem_bar _ hzH
  have hzbH' : zb⁻¹ ∈ bar M Q (H0 M Z) := Subgroup.inv_mem _ hzbH
  have hzz : ∀ e : M₀.E, (ρ zb).toAdd ((ρ zb⁻¹).toAdd e) = e := fun e => by
    rw [← act_mul_apply, mul_inv_cancel]
    exact act_one_apply e
  obtain ⟨act, hactρ, hinj, -⟩ := endg_act_data hc hS.model ρ hS.conj
  obtain ⟨hψV, -, hψW⟩ := psi_facts_tbar h310chi hS hs
  have hW : ∀ e, (ρ zb⁻¹).toAdd e - e ∈ wsub hS t := by
    intro e
    rw [wsub_eq_orthogonal hS t, LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    have h1 := hS.iso zb⁻¹ hzbH' ((ρ zb).toAdd v) e
    have hzv : (ρ zb).toAdd v = v := hzV v hv
    have e1 : (ρ zb⁻¹).toAdd ((ρ zb).toAdd v) = v := by
      rw [← act_mul_apply, inv_mul_cancel]
      exact act_one_apply v
    rw [e1, hzv] at h1
    show M₀.B v ((ρ zb⁻¹).toAdd e - e) = 0
    rw [map_sub, h1, sub_self]
  have hψ : ∀ e, dmap ρ (tbar hc ht) ((ρ zb⁻¹).toAdd e) = dmap ρ (tbar hc ht) e := by
    intro e
    have h0 := (hψW _).mpr (hW e)
    have e1 : (ρ zb⁻¹).toAdd e = ((ρ zb⁻¹).toAdd e - e) + e := by abel
    rw [e1, dmap_add, h0, zero_add]
  have hkey : ∀ a ∈ bar M Q Z0, zb * a * zb⁻¹ = a := by
    intro a ha
    apply hinj
    refine Equiv.ext fun e => ?_
    rw [hactρ, hactρ]
    have e1 : (ρ (zb * a * zb⁻¹)).toAdd e = (ρ zb).toAdd ((ρ a).toAdd ((ρ zb⁻¹).toAdd e)) := by
      rw [act_mul_apply, act_mul_apply]
    rw [e1, act_eq_cscal h310chi h52a hMp hS hs hr hZ0 ha ((ρ zb⁻¹).toAdd e),
      act_eq_cscal h310chi h52a hMp hS hs hr hZ0 ha e, map_add, hS.lin zb hzbH, hzz,
      hzV _ (hψV _), hψ]
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  refine ⟨hzH, Subgroup.mem_normalizer_fintype fun a ha => ?_⟩
  have haM : a ∈ M := hc.centre_le_M t hZ0 ha
  have hm : z * a * z⁻¹ ∈ M := M.mul_mem (M.mul_mem hzM haM) (M.inv_mem hzM)
  have hmk : QuotientGroup.mk' (Q.subgroupOf M) (⟨z * a * z⁻¹, hm⟩ : ↥M) =
      zb * (QuotientGroup.mk (⟨a, haM⟩ : ↥M) : Mbar M Q) * zb⁻¹ := by
    rw [QuotientGroup.mk'_apply, hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl
  have hmem := (mk_mem_bar_iff_sec4 hQZ0 (⟨z * a * z⁻¹, hm⟩ : ↥M)).mp (by
    rw [hmk, hkey _ (mk_mem_bar _ ha)]
    exact mk_mem_bar _ ha)
  exact hmem

end CFSG.RankThree.GF2n.Stroth80.S715L
