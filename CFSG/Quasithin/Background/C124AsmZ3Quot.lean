module

public import CFSG.Quasithin.Background.C124BlockLift

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure XBar (X V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (Γ : Type) [Group Γ] where
  π : ↥X →* Γ
  ρ : Γ →* MulAut (IntMod V hV)
  ker : ∀ g : ↥X, π g = 1 ↔ (g : G) ∈ pCoreOf 2 X
  act : ∀ g : ↥X, ρ (π g) = convI hV ⟨g, hXN g.2⟩

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV) {Γ : Type} [Group Γ] (B : XBar X V hV E.hXN Γ)

include E

theorem pi_conj {g s : G} (hs : s ∈ X) (hg : g ∈ X) :
    B.π ⟨s, hs⟩ * B.π ⟨g, hg⟩ * (B.π ⟨s, hs⟩)⁻¹ =
      B.π ⟨s * g * s⁻¹, X.mul_mem (X.mul_mem hs hg) (X.inv_mem hs)⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem pi_comm {k l : G} (hk : k ∈ L) (hkC : k ∈ Subgroup.centralizer (V : Set G))
    (hl : l ∈ L) : B.π ⟨k, E.hLX hk⟩ * B.π ⟨l, E.hLX hl⟩ =
      B.π ⟨l, E.hLX hl⟩ * B.π ⟨k, E.hLX hk⟩ := by
  have h2 : k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 X :=
    E.pCoreOf_L_le_Q (E.comm_C_L k ⟨E.hLX hk, hkC⟩ l hl)
  have h3 : B.π (⟨k, E.hLX hk⟩ * ⟨l, E.hLX hl⟩ * ⟨k, E.hLX hk⟩⁻¹ * ⟨l, E.hLX hl⟩⁻¹) = 1 :=
    (B.ker _).2 h2
  simp only [map_mul, map_inv] at h3
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)

end EntryPlus

end CFSG.Quasithin.C124
