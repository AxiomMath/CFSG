module

public import CFSG.Quasithin.Background.Harris.R1.QbetaTb

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert
open scoped commutatorElement

namespace QD

variable {G : Type*} [Group G] [Finite G] {P S Q W Z M D : Subgroup G} {g y z : G}
variable (h : QD P S Q W Z M D g y z)
include h

theorem sq_mem_conjSub {r : G} (hr : r ∈ conjSub g W) : r * r ∈ conjSub g Z := by
  have h1 : g⁻¹ * r * g ∈ W := mem_conjSub.mp hr
  have h2 := h.hsqW _ h1
  have := mul_mem_conjSub (g := g) h2
  have e : g * ((g⁻¹ * r * g) * (g⁻¹ * r * g)) * g⁻¹ = r * r := by group
  rwa [e] at this

theorem comm_A_A' {a a' : G} (ha : a ∈ W ⊓ Q) (ha' : a' ∈ conjSub g W ⊓ Q) :
    ⁅a, a'⁆ ∈ W ∧ ⁅a, a'⁆ ∈ Q ∧ ⁅a, a'⁆ * ⁅a, a'⁆ = 1 := by
  have hmem : ⁅a, a'⁆ ∈ W ⊓ conjSub g M :=
    Vert.Hyp.D_le_T h.vh h.hg (Subgroup.commutator_mem_commutator ha ha')
  have hTN := Vert.Hyp.le_normalizer_T h.vh h.hg h.hyg h.hyS
  have hTg : conjSub g (W ⊓ conjSub g M) = W ⊓ conjSub g M :=
    conjSub_eq_of_mem_normalizer (hTN h.hg)
  have hTWg : W ⊓ conjSub g M ≤ conjSub g W := Vert.Hyp.T_le_conjSub h.vh h.hgg hTg
  have hrW : ⁅a, a'⁆ ∈ W := hmem.1
  have hrWg : ⁅a, a'⁆ ∈ conjSub g W := hTWg hmem
  have hrQ : ⁅a, a'⁆ ∈ Q :=
    h.Tb_le_Q ⟨h.vh.wm hrW, hmem.2⟩
  refine ⟨hrW, hrQ, ?_⟩
  have hZ1 : ⁅a, a'⁆ * ⁅a, a'⁆ ∈ Z := h.hsqW _ hrW
  have hZ2 : ⁅a, a'⁆ * ⁅a, a'⁆ ∈ conjSub g Z := h.sq_mem_conjSub hrWg
  have : ⁅a, a'⁆ * ⁅a, a'⁆ ∈ Z ⊓ conjSub g Z := ⟨hZ1, hZ2⟩
  rw [h.hZZ, Subgroup.mem_bot] at this
  exact this

end QD

end CFSG.Quasithin.Background.Harris.R1
