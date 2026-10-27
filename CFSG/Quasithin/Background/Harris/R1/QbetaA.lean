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

theorem b1_conj {s : G} (hs : s ∈ Q)
    (hfix : ∀ w ∈ conjSub g W ⊓ Q, s * w * s⁻¹ * w⁻¹ ∈ conjSub g Z) : s ∈ conjSub g M := by
  have hQg : conjSub g Q = Q := conjSub_eq_of_mem_normalizer (h.vh.qn h.hg)
  have hgi : g⁻¹ ∈ P := P.inv_mem h.hg
  have hs' : g⁻¹ * s * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (h.vh.qn hgi) s).mp hs
    simpa using this
  have hM : g⁻¹ * s * g ∈ M := by
    refine h.vh.b1 _ hs' (fun w hw => ?_)
    obtain ⟨hwW, hwQ⟩ := Subgroup.mem_inf.mp hw
    have hgw : g * w * g⁻¹ ∈ conjSub g W ⊓ Q :=
      ⟨mul_mem_conjSub hwW, (Subgroup.mem_normalizer_iff.mp (h.vh.qn h.hg) w).mp hwQ⟩
    have h1 := hfix _ hgw
    have h2 := mem_conjSub.mp h1
    have e : g⁻¹ * (s * (g * w * g⁻¹) * s⁻¹ * (g * w * g⁻¹)⁻¹) * g =
        (g⁻¹ * s * g) * w * (g⁻¹ * s * g)⁻¹ * w⁻¹ := by group
    rw [e] at h2
    exact h2
  have e : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
  rw [mem_conjSub]
  exact hM

theorem D_le_Q : D ≤ Q := fun x hx =>
  h.hQV x (h.hMS (h.hD hx)) (fun v hv => h.hDc x hx v (h.V_le_W hv))

theorem comm_D_A' {x a : G} (hx : x ∈ D) (ha : a ∈ conjSub g W ⊓ Q) :
    x * a * x⁻¹ * a⁻¹ ∈ Z := by
  obtain ⟨haW, haQ⟩ := Subgroup.mem_inf.mp ha
  have hxQ : x ∈ Q := h.D_le_Q hx
  have haS : a ∈ S := h.vh.qs haQ
  have hD : x * a * x⁻¹ * a⁻¹ ∈ D := by
    have h1 : a * x⁻¹ * a⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (h.hDS haS) x⁻¹).mp (D.inv_mem hx)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact D.mul_mem hx h1
  have hW : x * a * x⁻¹ * a⁻¹ ∈ conjSub g W := by
    have hN : x ∈ Subgroup.normalizer ((conjSub g W : Subgroup G) : Set G) := by
      have : Q ≤ Subgroup.normalizer ((conjSub g W : Subgroup G) : Set G) :=
        calc Q = conjSub g Q := (conjSub_eq_of_mem_normalizer (h.vh.qn h.hg)).symm
          _ ≤ conjSub g S := conjSub_mono g h.vh.qs
          _ ≤ Subgroup.normalizer ((conjSub g W : Subgroup G) : Set G) :=
            conjSub_le_normalizer h.vh.sw
      exact this hxQ
    exact (conjSub g W).mul_mem ((Subgroup.mem_normalizer_iff.mp hN a).mp haW)
      ((conjSub g W).inv_mem haW)
  have hM : x * a * x⁻¹ * a⁻¹ ∈ conjSub g M := conjSub_mono g h.vh.wm hW
  exact h.D_inf_conjSub_M_le_Z ⟨hD, hM⟩

theorem mem_Z_of_comm {x : G} (hx : x ∈ D) (hc : ∀ a ∈ conjSub g W ⊓ Q, x * a = a * x) :
    x ∈ Z := by
  have hxQ : x ∈ Q := h.D_le_Q hx
  have hM : x ∈ conjSub g M := by
    refine h.b1_conj hxQ (fun w hw => ?_)
    have : x * w * x⁻¹ * w⁻¹ = 1 := by rw [hc w hw]; group
    rw [this]
    exact (conjSub g Z).one_mem
  exact h.D_inf_conjSub_M_le_Z ⟨hx, hM⟩

end QD

end CFSG.Quasithin.Background.Harris.R1
