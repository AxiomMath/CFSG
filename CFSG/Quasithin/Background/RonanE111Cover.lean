module

public import CFSG.Quasithin.Background.RonanE111WrAct
public import CFSG.Quasithin.Background.RonanE111LSG

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X T A J C : Subgroup G} [Fintype ↥C]

theorem cover_diag {n : ℕ} (hn : 1 ≤ n) (h : DiagSetting X T A J C) {D Y : Subgroup G}
    {𝒟 : Set (Subgroup G)} (hJD : JData (actE T A J) J D Y 𝒟) (hSylD : IsSylowIn 2 (T ⊓ D) D)
    (hmove : (∃ S ∈ 𝒟, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ S,
        v * s * v⁻¹ * s⁻¹ ∉ Y) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ S ∈ 𝒟, (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    dimg h.diagComm D ≤ T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K := by
  obtain ⟨S₀, hS₀⟩ := hJD.nonempty
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := wreath_struct h hJD hS₀ hSylD
  have hT : IsSylowIn 2 T ⊤ := h.red.2.2.2.2.2.1
  have hT₀A : ∀ t ∈ actT T A, ∀ a ∈ A, t * a = a * t := fun t ht a ha =>
    (Subgroup.mem_centralizer_iff.mp ht.2 a ha).symm
  have hAT₀ : A ≤ actT T A := fun a ha =>
    ⟨h.AT ha, Subgroup.mem_centralizer_iff.mpr fun b hb => h.comm hb ha⟩
  have hτ : E1.tauOf ⊤ T A ≤ actT T A := E111R.tauOf_le (E111R.pCoreOf_two_eq_bot h.red) T A
  exact h1.trans (lift_semisimple_sub hn hT inf_le_left hAT₀ h.elem hT₀A h4 h5 h6 h3 h7 h8 h9 h11 hτ
    (wreath_move h hJD hS₀ hmove) (wreath_rank h hJD hS₀ n hrank))

end CFSG.Quasithin.RonanE111
