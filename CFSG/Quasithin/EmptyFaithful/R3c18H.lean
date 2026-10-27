module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.QuasithinUnique.Fin257

theorem exists_sq_of_pair {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (φ : MulAut G) {u v : G}
    (hu : φ u = u) (hv : φ v = v) (hc : u * v = v * u) (hup : u ^ p = 1) (hvp : v ^ p = 1)
    (hind : ∀ i j : ℕ, u ^ i * v ^ j = 1 → p ∣ i ∧ p ∣ j) :
    ∃ E : Subgroup G, Nat.card E = p ^ 2 ∧ CFSG.Open.IsElemAbelian p E ∧ ∀ y ∈ E, φ y = y := by
  set H : Subgroup G := (φ : MulAut G).toMonoidHom.eqLocus (MonoidHom.id G) with hH
  have hu' : u ∈ H := hu
  have hv' : v ∈ H := hv
  set u' : H := ⟨u, hu'⟩ with hu'def
  set v' : H := ⟨v, hv'⟩ with hv'def
  have hc' : u' * v' = v' * u' := Subtype.ext hc
  have hup' : u' ^ p = 1 := Subtype.ext hup
  have hvp' : v' ^ p = 1 := Subtype.ext hvp
  have hind' : ∀ i j : ℕ, u' ^ i * v' ^ j = 1 → p ∣ i ∧ p ∣ j := fun i j h =>
    hind i j (congrArg Subtype.val h)
  obtain ⟨P₀, hel, hcard, -, -⟩ := exists_elemAbelian_pair hp hc' hup' hvp' hind'
  refine ⟨P₀.map H.subtype, ?_, CFSG.SectionRank.isElemAbelian_map hel H.subtype, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
  · rintro _ ⟨w, -, rfl⟩
    exact w.2

end R3c18

end CFSG.Quasithin
