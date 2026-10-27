module

public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelDelta
import CFSG.RankThree.GF2n.Stroth80.Sec7EndModel
import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80.S714

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

omit [Finite G] [Finite K] in
theorem dmap_act_comm {g x : Mbar M Q} (hgx : g * x = x * g) (e : M₀.E) :
    dmap ρ g ((ρ x).toAdd e) = (ρ x).toAdd (dmap ρ g e) := by
  have h1 : (ρ g).toAdd ((ρ x).toAdd e) = (ρ x).toAdd ((ρ g).toAdd e) := by
    have e1 : (ρ (g * x)).toAdd e = (ρ g).toAdd ((ρ x).toAdd e) := by
      rw [map_mul]
      rfl
    have e2 : (ρ (x * g)).toAdd e = (ρ x).toAdd ((ρ g).toAdd e) := by
      rw [map_mul]
      rfl
    rw [← e1, ← e2, hgx]
  simp only [dmap, map_sub, h1]

theorem exists_scalar_of_nat (h310chi : Stroth310ChiStatement) (hZV : Sec7ZVStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (hs : Sec7Hyp hc n t)
    {K' : Type} [Field K'] [Finite K'] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Xcl : Subgroup (GL ι K')} (hK' : Nat.card K' = Nat.card Z) (hcomm : AddCommutantScalar Xcl)
    (hnat : NaturalRep K' Xcl (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t))
    (tm : ↥M) (htm : (tm : G) = t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {z : Mbar M Q} (hz : z ∈ bar M Q Z0) :
    ∃ c : K, ∀ e, dmap ρ z e = c • dmap ρ (QuotientGroup.mk tm) e := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  obtain ⟨θ, Ψ, π, hπr, -, hΨc, hΨx⟩ := hc.natural_transport hS ht hK' hcomm hnat
  obtain ⟨hψV, hψsurj, hψW⟩ := psi_facts h310chi hS hs.toSec5 (Or.inr hs.omegaNat) tm htm
  obtain ⟨zm, hzZ0, rfl⟩ := exists_of_mem_bar hz
  by_cases hzQ : (zm : G) ∈ Q
  · have h1 : (QuotientGroup.mk zm : Mbar M Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
    refine ⟨0, fun e => ?_⟩
    rw [h1, dmap_one, zero_smul]
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have htH : (QuotientGroup.mk tm : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    mem_bar_H0_of_Rt hc (mk_mem_bar tm (htm ▸ hZ0.le htZ0))
  have hzH : (QuotientGroup.mk zm : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    mem_bar_H0_of_Rt hc (mk_mem_bar zm (hZ0.le hzZ0))
  let ψ : M₀.E →ₗ[K] M₀.E := dlin hS (QuotientGroup.mk tm) htH
  let φ : M₀.E →ₗ[K] M₀.E := dlin hS (QuotientGroup.mk zm) hzH
  have hrange : LinearMap.range ψ = hc.VtSub hS.model t := by
    ext v
    constructor
    · rintro ⟨e, rfl⟩
      exact hψV e
    · intro hv
      obtain ⟨e, he⟩ := hψsurj v hv
      exact ⟨e, he⟩
  have hcQ : ∀ x ∈ Q, ⁅(zm : G), x⁆ ∈ Q := fun x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 zm.2) x).mp hx)
      (Q.inv_mem hx)
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro e he
    have heW := (hψW e).mp he
    obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp heW)
    show dmap ρ (QuotientGroup.mk zm) (M₀.π x) = 0
    rw [dmap_pi hS zm hxQ]
    exact (M₀.π_ker _ (hcQ x hxQ)).mpr ((hMp G M Q Z B hc n t hs Z0 hZ0 zm hzZ0).2 x hxW)
  have hφP : LinearMap.range φ ≤ hc.VtSub hS.model t := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    show dmap ρ (QuotientGroup.mk zm) (M₀.π x) ∈ _
    rw [dmap_pi hS zm hxQ, hc.mem_VtSub hS.model t, ← hZV G M Q Z B hc n t hs Z0 hZ0 zm hzZ0 hzQ]
    have h1 : ⁅x, (zm : G)⁆ ∈ Ut Q Z (zm : G) := comm_mem_Ut hxQ
    have h2 : ⁅(zm : G), x⁆ ∈ Ut Q Z (zm : G) := by
      rw [← commutatorElement_inv]
      exact (Ut Q Z (zm : G)).inv_mem h1
    exact M₀.pi_mem_img h2 (hcQ x hxQ)
  have hψS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
      ψ ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (ψ e) := fun x e =>
    dmap_act_comm (endg_comm_centre hZ0 hRM (z := tm) (htm ▸ htZ0) x.2) e
  have hφS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
      φ ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (φ e) := fun x e =>
    dmap_act_comm (endg_comm_centre hZ0 hRM (z := zm) hzZ0 x.2) e
  obtain ⟨c, hc'⟩ := endg_schur hcomm (hc.VtSub hS.model t) θ Ψ hΨc π hπr
    (fun (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : M₀.E) => (ρ (x : Mbar M Q)).toAdd w)
    (fun x w hw => hc.act_mem_VtSub hS ht x x.2 w hw) hΨx ψ φ hrange hker hφP hψS hφS
  exact ⟨c, fun e => hc' e⟩

theorem exists_scalar_of_mem_Z0 (h310chi : Stroth310ChiStatement) (hZV : Sec7ZVStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (hs : Sec7Hyp hc n t)
    (tm : ↥M) (htm : (tm : G) = t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {z : Mbar M Q} (hz : z ∈ bar M Q Z0) :
    ∃ c : K, ∀ e, dmap ρ z e = c • dmap ρ (QuotientGroup.mk tm) e := by
  obtain ⟨K', hF, hFin, hK', hplus | hminus⟩ := hs.omegaNat
  · obtain ⟨m, hm, hnat⟩ := hplus
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    exact exists_scalar_of_nat h310chi hZV hMp hS hs hK'
      (addCommutantScalar_statedOmegaPlus hm) hnat tm htm hZ0 hz
  · obtain ⟨m, b', c', hm, hirr, hnat⟩ := hminus
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    exact exists_scalar_of_nat h310chi hZV hMp hS hs hK'
      (addCommutantScalar_statedOmegaMinus hm hirr) hnat tm htm hZ0 hz

end CFSG.RankThree.GF2n.Stroth80.S714
