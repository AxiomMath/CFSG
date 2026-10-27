module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Basic
public import CFSG.Quasithin.EmptyFaithful.SzF53MDict
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolSec

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem map_zpowers_subgroupOf {K : Subgroup G} {x : G} (hx : x ∈ K) {Γ : Type*} [Group Γ]
    (θ : ↥K →* Γ) :
    ((Subgroup.zpowers x).subgroupOf K).map θ = Subgroup.zpowers (θ ⟨x, hx⟩) := by
  have e : (Subgroup.zpowers x).subgroupOf K = Subgroup.zpowers (⟨x, hx⟩ : ↥K) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; simp⟩
  rw [e, MonoidHom.map_zpowers]

theorem isInvSub_zpowers_top {n : ℕ} (Mo : Model n) (σ : Equiv.Perm (Fin n)) :
    IsInvSub Mo (Subgroup.zpowers σ) ⊤ := fun _ _ _ _ => Subgroup.mem_top _

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem exists_secData {δ : Geo H M} (hδ : vtype δ = false) :
    ∃ (_ : ((F53B3.Cv δ).subgroupOf (Vn δ)).Normal) (θ : ↥(stab δ) →* Equiv.Perm (Fin 5))
      (βm : nat.W →* ↥(Vn δ) ⧸ (F53B3.Cv δ).subgroupOf (Vn δ)),
      Function.Surjective θ ∧ θ.ker = (Qv δ).subgroupOf (stab δ) ∧
        SecData nat (stab δ) (F53B3.Cv δ) (Vn δ) θ βm := by
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.isNatSec hδ
  refine ⟨hN, θ, βm, hθs, ?_, hsd⟩
  rw [hθk, C.cSecIn_eq_Qv hδ]

theorem four_le_relIndex_commSec {δ : Geo H M} (hδ : vtype δ = false) {x : G}
    (hx : x ∈ stab δ) (hxQ : x ∉ Qv δ) :
    4 ≤ (F53B3.Cv δ).relIndex (commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)) := by
  obtain ⟨hN, θ, βm, -, hθk, hsd⟩ := C.exists_secData hδ
  have hle : Subgroup.zpowers x ≤ stab δ := (Subgroup.zpowers_le).mpr hx
  rw [hsd.card_commSec inf_le_left hle, map_zpowers_subgroupOf hx,
    card_commW_zpowers_eq_relIndex (isInvSub_zpowers_top nat _), Subgroup.relIndex_top_right]
  have hne : θ ⟨x, hx⟩ ≠ 1 := by
    intro h1
    have : (⟨x, hx⟩ : ↥(stab δ)) ∈ θ.ker := h1
    rw [hθk, Subgroup.mem_subgroupOf] at this
    exact hxQ this
  have h4 : 4 ≤ idx nat (θ ⟨x, hx⟩) := by
    rw [idx_nat]
    simp only [hne, ↓reduceIte]
    split_ifs <;> norm_num
  exact h4

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
