module

public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure ISec (U Y L Cg : Subgroup G) : Prop where
  elem : ∀ u ∈ U, u ^ 2 = 1
  normU : Y ≤ Subgroup.normalizer (U : Set G)
  le : L ≤ Y
  normL : Y ≤ Subgroup.normalizer (L : Set G)
  two : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (U : Set G)
  normC : Y ≤ Subgroup.normalizer ((U ⊓ Cg : Subgroup G) : Set G)
  centC : U ⊓ Cg ≤ Subgroup.centralizer (L : Set G)
  comm : ⁅U, L⁆ = U
  lt : ¬ U ≤ Cg
  irr : ∀ J : Subgroup G, U ⊓ Cg ≤ J → J ≤ U → L ≤ Subgroup.normalizer (J : Set G) →
    J = U ⊓ Cg ∨ J = U
  o2 : pCoreOf 2 (autOn L U) = ⊥
  quasi : CFSG.IsQuasisimple ↥(autOn L U)

namespace ISec

variable {U Y L Cg : Subgroup G} (h : ISec U Y L Cg)

include h

theorem normUL : L ≤ Subgroup.normalizer (U : Set G) := h.le.trans h.normU

theorem autOn_le : autOn L U ≤ autOn Y U := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hx
  exact Setup.mem_autOn_iff.2 ⟨g, h.le hg, rfl⟩

theorem autOn_normal : ∀ x ∈ autOn Y U, ∀ k ∈ autOn L U, x * k * x⁻¹ ∈ autOn L U := by
  intro x hx k hk
  obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hx
  obtain ⟨l, hlL, rfl⟩ := Setup.mem_autOn_iff.1 hk
  rw [← map_inv, ← map_mul, ← map_mul]
  refine Setup.mem_autOn_iff.2 ⟨g * l * g⁻¹, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (h.normL hgY) l).1 hlL

theorem autOn_two : ∀ x ∈ autOn Y U, ∃ e : ℕ, x ^ 2 ^ e ∈ autOn L U := by
  intro x hx
  obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hx
  obtain ⟨e, he⟩ := h.two _ hgY
  refine ⟨e, ?_⟩
  rw [← map_pow]
  exact conjAct_mem_autOn_of_mem_sup h.normUL _ he

theorem lt_top [IsMulCommutative ↥U] : Cg.subgroupOf U < ⊤ := by
  refine lt_top_iff_ne_top.2 fun htop => h.lt fun u hu => ?_
  have : (⟨u, hu⟩ : ↥U) ∈ Cg.subgroupOf U := by rw [htop]; trivial
  exact this

theorem qsec [Finite G] [IsMulCommutative ↥U] :
    QSec (autOn Y U) (autOn L U) (Cg.subgroupOf U) := by
  have hstab := autOn_le_stabSub (U := U) h.normC
  have hfix := le_fixV_autOn (U := U) (L := L) h.centC
  have hV : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using h.elem v v.2)
  exact ⟨h.autOn_le, h.autOn_normal, h.autOn_two, hstab,
    hfix, commV_autOn_eq_top h.normUL h.comm, h.lt_top, irr_autOn h.normUL h.irr,
    inf_centSec_eq_bot_of_pCoreOf hV (h.autOn_le.trans hstab) hfix h.o2, h.quasi⟩

theorem b4Hyp [Finite G] [IsMulCommutative ↥U] (hS : SQTKGroup ↥(autOn L U)) :
    B4Hyp (autSec (autOn Y U) ⊤ (Cg.subgroupOf U)) (autSec (autOn L U) ⊤ (Cg.subgroupOf U)) :=
  h.qsec.b4Hyp (fun v => Subtype.ext (by simpa using h.elem v v.2)) hS

end ISec

end CFSG.Quasithin.InternalSec
