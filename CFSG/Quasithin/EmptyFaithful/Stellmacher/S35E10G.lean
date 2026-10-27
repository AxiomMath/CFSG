module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_transvec_of_mem (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false)
    (hZ : IsOrthSec (stab β) (Zv β) (Vn β)) {g : G} (hg : g ∈ Lr β ⊔ Qv β) :
    secIdx (Subgroup.zpowers g) (Zv β) (Vn β) ≠ 2 := by
  intro h2
  have hLs : Lr β ≤ stab β := oTwoRes_le _
  have hQs : Qv β ≤ stab β := pCoreOf_le 2 _
  have hgs : g ∈ stab β := (sup_le hLs hQs) hg
  have hLN : Zv β ≤ Vn β := Zv_le_Vn_S5 hS hβ
  have hnorm : stab β ≤ Subgroup.normalizer (Zv β : Set G) :=
    stab_le_normalizer_Zv hS.glob.amalg β
  have hNL : Vn β ≤ Subgroup.normalizer (Zv β : Set G) := fun v hv =>
    hnorm (hQs (Vn_le_Qv_self hS β hv))
  obtain ⟨θ, -, hker, hiff⟩ := S43.IsOrthSec.exists_swap_iff hZ hLN
  have hnc : g ∉ cSecIn (stab β) (Zv β) (Vn β) := by
    intro hc
    have h1 := (S43.secIdx_eq_one_iff hNL (hnorm hgs)).mpr ((mem_cSecIn_iff hnorm).mp hc).2
    omega
  have hswap : (θ ⟨g, hgs⟩).IsSwap := (hiff g hgs hnc).mp h2
  let σ : ↥(stab β) →* ℤˣ := Equiv.Perm.sign.comp θ
  have hLP : Lr β ≤ (σ.ker).map (stab β).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, k, hk, hxk⟩
    refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have h1 : σ ⟨x, hx⟩ ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : ↥(stab β)) ^ k = 1 := Subtype.ext (by simpa using hxk)
      rw [this, map_one]
    rcases Int.units_eq_one_or (σ ⟨x, hx⟩) with h | h
    · exact h
    · rw [h, hk.neg_one_pow] at h1
      exact absurd h1 (by decide)
  have hQP : Qv β ≤ (σ.ker).map (stab β).subtype := by
    intro q hq
    refine ⟨⟨q, hQs hq⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have hqc : q ∈ cSecIn (stab β) (Zv β) (Vn β) := by
      refine (mem_cSecIn_iff hnorm).mpr ⟨hQs hq, fun y hy => ?_⟩
      have h : ⁅y, q⁆ ∈ Zv β := by
        rw [← comm_Vn_Qv hS hβ]
        exact Subgroup.commutator_mem_commutator hy hq
      have e : q * y * q⁻¹ * y⁻¹ = ⁅y, q⁆⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact (Zv β).inv_mem h
    show Equiv.Perm.sign (θ ⟨q, hQs hq⟩) = 1
    rw [(mem_cSecIn_iff_of_ker hker (hQs hq)).mpr hqc, map_one]
  obtain ⟨y, hy, hyg⟩ := (sup_le hLP hQP) hg
  have hyg' : y = ⟨g, hgs⟩ := Subtype.ext hyg
  rw [hyg'] at hy
  have h1 : Equiv.Perm.sign (θ ⟨g, hgs⟩) = 1 := hy
  obtain ⟨a, b, hab, hs⟩ := hswap
  rw [hs, Equiv.Perm.sign_swap hab] at h1
  exact absurd h1 (by decide)

theorem claim11 (hS : Sit H M S) (hI : CaseI H M) (h10 : Claim10 H M) (h16 : Claim16a H M) :
    Claim11 H M := by
  intro β α' hl hle
  have hl' : Lam α' β := h10.2 β α' hl
  obtain ⟨v, hv, -, hsec⟩ := h16 α' β hl'
  exact not_transvec_of_mem hS hl.1.vδ (C1.caseI_orthSec hS hI hl.1.vδ).2 (hle hv) hsec

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
