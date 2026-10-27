module

public import CFSG.Quasithin.Background.E1ElevenIso

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

@[expose] def innAutInduced {G : Type} [Group G] (T M N : Subgroup G)
    [(N.subgroupOf M).Normal] : Subgroup (MulAut (↥M ⧸ N.subgroupOf M)) :=
  Subgroup.closure
    {α | ∃ g ∈ M ⊔ (T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (N : Set G)),
      ∀ m : ↥M, ∃ m' : ↥M, (m' : G) = g * (m : G) * g⁻¹ ∧
        α (QuotientGroup.mk m) = QuotientGroup.mk m'}

section Induces

variable {G : Type} [Group G] (M N : Subgroup G) [(N.subgroupOf M).Normal]

@[expose] def Induces (g : G) (α : MulAut (↥M ⧸ N.subgroupOf M)) : Prop :=
  ∀ m : ↥M, ∃ m' : ↥M, (m' : G) = g * (m : G) * g⁻¹ ∧
    α (QuotientGroup.mk m) = QuotientGroup.mk m'

@[expose] def indSet (U : Subgroup G) : Set (MulAut (↥M ⧸ N.subgroupOf M)) :=
  {α | ∃ g ∈ U, Induces M N g α}

variable {M N}

theorem innAutInduced_eq (T : Subgroup G) :
    innAutInduced T M N =
      Subgroup.closure (indSet M N
        (M ⊔ (T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (N : Set G)))) :=
  rfl

end Induces

section Congr

variable {G G' : Type} [Group G] [Group G'] {M N : Subgroup G} {M' N' : Subgroup G'}
  [(N.subgroupOf M).Normal] [(N'.subgroupOf M').Normal]

theorem closure_indSet_congr (e : (↥M ⧸ N.subgroupOf M) ≃* (↥M' ⧸ N'.subgroupOf M'))
    {U : Subgroup G} {U' : Subgroup G'}
    (h1 : ∀ g ∈ U, ∃ g' ∈ U', ∀ α, Induces M N g α → Induces M' N' g' (MulAut.congr e α))
    (h2 : ∀ g' ∈ U', ∃ g ∈ U, ∀ α', Induces M' N' g' α' →
      Induces M N g ((MulAut.congr e).symm α')) :
    Subgroup.closure (indSet M' N' U') =
      (Subgroup.closure (indSet M N U)).map (MulAut.congr e).toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext α'
  constructor
  · rintro ⟨g', hg', hα'⟩
    obtain ⟨g, hg, hind⟩ := h2 g' hg'
    exact ⟨(MulAut.congr e).symm α', ⟨g, hg, hind α' hα'⟩,
      (MulAut.congr e).apply_symm_apply α'⟩
  · rintro ⟨α, ⟨g, hg, hα⟩, rfl⟩
    obtain ⟨g', hg', hind⟩ := h1 g hg
    exact ⟨g', hg', hind α hα⟩

theorem nParam_closure_indSet_congr [Finite G'] [Finite (MulAut (↥M ⧸ N.subgroupOf M))]
    (e : (↥M ⧸ N.subgroupOf M) ≃* (↥M' ⧸ N'.subgroupOf M'))
    {U : Subgroup G} {U' : Subgroup G'}
    (h1 : ∀ g ∈ U, ∃ g' ∈ U', ∀ α, Induces M N g α → Induces M' N' g' (MulAut.congr e α))
    (h2 : ∀ g' ∈ U', ∃ g ∈ U, ∀ α', Induces M' N' g' α' →
      Induces M N g ((MulAut.congr e).symm α')) [Finite (MulAut (↥M' ⧸ N'.subgroupOf M'))] :
    E1.nParam (Subgroup.closure (indSet M' N' U')) =
      E1.nParam (Subgroup.closure (indSet M N U)) := by
  rw [closure_indSet_congr e h1 h2]
  exact E1.Eleven.nParam_map_mulEquiv (MulAut.congr e) _

end Congr

@[expose] def HypT (n : ℕ) (G : Type) [Group G] (T : Subgroup G) : Prop :=
  ∀ (M N : Subgroup G) [(N.subgroupOf M).Normal], N ≤ M → M.IsSubnormal →
    T ≤ Subgroup.normalizer (N : Set G) → IsSimpleGroup (↥M ⧸ N.subgroupOf M) →
    (∃ a b : ↥M ⧸ N.subgroupOf M, a * b ≠ b * a) →
      E1.nParam (innAutInduced T M N) ≤ (n : ℕ∞)

end CFSG.Quasithin.RonanE111
