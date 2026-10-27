module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7K1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.K

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Wl_smul (g : ↥(H ⊔ M)) (l : Geo H M) : Wl (g • l) = conjSub (g : G) (Wl l) := by
  unfold Wl
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs l := (Std.smul_mem_nbrs_iff' g).mp hδ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs l) => Vn δ)
      δ' hδ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs (g • l)) => Vn δ)
      (g • δ) ((Std.smul_mem_nbrs_iff' g).mpr hδ) le_rfl

@[expose] def toHM (β : Geo H M) {g : G} (hg : g ∈ stab β) : ↥(H ⊔ M) := ⟨g, stab_le β hg⟩

omit [Finite G] in
theorem coe_toHM (β : Geo H M) {g : G} (hg : g ∈ stab β) : (toHM β hg : G) = g := rfl

theorem Wl_le_Wb (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) :
    Wl l ≤ Wb β := by
  rw [Std.Wb_eq_iSup_Wl hS hβ]
  exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl le_rfl

theorem Qv_comm_mem (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {E : Subgroup G}
    (hEn : stab β ≤ Subgroup.normalizer (E : Set G)) (ho : IsOrthSec (stab β) E (Wb β)) :
    ∀ q ∈ Qv β, ∀ x ∈ Wb β, q * x * q⁻¹ * x⁻¹ ∈ E := by
  have hcs : cSecIn (stab β) E (Wb β) = Qv β :=
    IsModelSec.cSecIn_eq_pCoreOf ho (C56.quot_five hS hβ)
  intro q hq x hx
  rw [← hcs] at hq
  exact ((F53Mod.mem_cSecIn_iff hEn).mp hq).2 x hx

omit [Finite G] in
theorem inf_smul_eq_of_cen {β l : Geo H M} (hl : l ∈ nbrs β) {E : Subgroup G}
    (hEn : stab β ≤ Subgroup.normalizer (E : Set G)) (hVE : Vn β ≤ E) {c : G}
    (hc : c ∈ cenSec (stab β) (Vn β) E (Std.Vn_normal β)) :
    Wl (toHM β hc.1 • l) ⊓ E = Wl l ⊓ E := by
  have hVA : Vn β ≤ Wl l ⊓ E := le_inf (Std.Vn_le_Wl (Std.mem_nbrs_symm.mp hl)) hVE
  have key : ∀ c ∈ cenSec (stab β) (Vn β) E (Std.Vn_normal β), ∀ a ∈ Wl l ⊓ E,
      c * a * c⁻¹ ∈ Wl l ⊓ E := by
    intro c hc a ha
    have h1 : c * a * c⁻¹ * a⁻¹ ∈ Wl l ⊓ E := hVA (hc.2 a ha.2)
    have := mul_mem h1 ha
    simpa [mul_assoc] using this
  have hle : ∀ c ∈ cenSec (stab β) (Vn β) E (Std.Vn_normal β),
      conjSub c (Wl l ⊓ E) ≤ Wl l ⊓ E := by
    intro c hc x hx
    rw [mem_conjSub] at hx
    have := key c hc _ hx
    simpa [mul_assoc] using this
  have hconj : conjSub c (Wl l ⊓ E) = Wl l ⊓ E :=
    le_antisymm (hle c hc) (le_conjSub_iff c |>.mpr (hle c⁻¹ (inv_mem hc)))
  have hE : conjSub c E = E := conjSub_eq_of_mem_normalizer (hEn hc.1)
  rw [Wl_smul, coe_toHM, ← hconj, conjSub_inf, hE]

theorem inf_smul_eq (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {E : Subgroup G}
    (hEn : stab β ≤ Subgroup.normalizer (E : Set G)) (hVE : Vn β ≤ E) (hEW : E ≤ Wb β)
    (ho : IsOrthSec (stab β) E (Wb β)) {y : G} (hy : y ∈ stab β) (hyQ : y ∉ Qv β)
    (h1 : secIdx (Subgroup.zpowers y) (Vn β) E = 1)
    (h2 : secIdx (Subgroup.zpowers y) E (Wb β) = 2) :
    ∀ (g : G) (hg : g ∈ stab β), ∀ l ∈ nbrs β, Wl (toHM β hg • l) ⊓ E = Wl l ⊓ E := by
  obtain ⟨θ, hθs, hθk, hsw⟩ := S43.IsOrthSec.exists_swap_iff ho hEW
  have hcs : cSecIn (stab β) E (Wb β) = Qv β :=
    IsModelSec.cSecIn_eq_pCoreOf ho (C56.quot_five hS hβ)
  rw [hcs] at hθk hsw
  have hVn := Std.Vn_normal (H := H) (M := M) β
  have hNL : E ≤ Subgroup.normalizer (Vn β : Set G) := fun e he =>
    hVn (pCoreOf_le 2 (stab β) (Std.Wb_le_Qv hS β (hEW he)))
  have hyC : y ∈ cenSec (stab β) (Vn β) E hVn :=
    ⟨hy, (S43.secIdx_eq_one_iff hNL (hVn hy)).mp h1⟩
  have hsw' : (θ ⟨y, hy⟩).IsSwap := (hsw y hy hyQ).mp h2
  have hCX : cenSec (stab β) (Vn β) E hVn ≤ stab β := fun x hx => hx.1
  obtain hmul := exists_mul_of_swap θ hθs hθk hCX
    (fun g hg t ht => cenSec_conj hVn hEn hg ht) hyC hsw'
  intro g hg l hl
  obtain ⟨q, hq, c, hc, rfl⟩ := hmul g hg
  have hl' : toHM β hc.1 • l ∈ nbrs β := Std.smul_mem_nbrs_of_stab hc.1 hl
  have hqs : (toHM β (pCoreOf_le 2 (stab β) hq) : G) ∈ stab (toHM β hc.1 • l) :=
    Std.Qv_le_stab hS hl' hq
  have e : toHM β hg = toHM β (pCoreOf_le 2 (stab β) hq) * toHM β hc.1 := rfl
  rw [e, mul_smul, smul_eq_of_mem_stab hqs]
  exact inf_smul_eq_of_cen hl hEn hVE hc

end S35.G7.K

end F53.Stellmacher

end CFSG.Quasithin
