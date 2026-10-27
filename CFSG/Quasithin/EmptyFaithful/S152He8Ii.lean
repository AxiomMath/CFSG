module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S152He8Aut

public section

namespace CFSG.Quasithin.He8

open CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem quot_equiv_of_isAut {Kc T : Subgroup G} (hperf : ⁅Kc, Kc⁆ = Kc) (hne : Kc ≠ ⊥)
    (hT : T ≤ Subgroup.normalizer (Kc : Set G)) {Λ : Type} [Group Λ] [Finite Λ]
    (hs : IsSimpleGroup Λ) (hZ : Subgroup.center Λ = ⊥) [Group.IsSolvable (Outer Λ)]
    (e : OTwoQuot (Kc ⊔ T) ≃* MulAut Λ) : Nonempty ((↥Kc ⧸ CFSG.pCore 2 ↥Kc) ≃* Λ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := Kc ⊔ T with hX
  have hKX : Kc ≤ X := le_sup_left
  have hXn : X ≤ Subgroup.normalizer (Kc : Set G) :=
    sup_le Subgroup.le_normalizer hT
  let π : ↥X →* MulAut Λ := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : ∀ x : ↥X, π x = 1 → x ∈ CFSG.Open.pCore 2 ↥X := by
    intro x hx
    have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)) x = 1 := by
      have : e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) x) = 1 := hx
      exact e.map_eq_one_iff.mp this
    exact (QuotientGroup.eq_one_iff x).mp h1
  let ι : ↥Kc →* ↥X := Subgroup.inclusion hKX
  let α : ↥Kc →* MulAut Λ := π.comp ι
  have hnorm : α.range.Normal := by
    refine ⟨fun a ha φ => ?_⟩
    obtain ⟨r, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hπs φ
    have hmem : (y : G) * (r : G) * (y : G)⁻¹ ∈ Kc :=
      (Subgroup.mem_normalizer_iff.mp (hXn y.2) r).mp r.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    have h1 : ι ⟨_, hmem⟩ = y * ι r * y⁻¹ := Subtype.ext rfl
    simp only [α, MonoidHom.comp_apply]
    rw [h1, map_mul, map_mul, map_inv]
  have h2 : IsPGroup 2 α.ker := by
    have hP := CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥X)
    intro g
    have hg : π (ι g.1) = 1 := g.2
    obtain ⟨k, hk⟩ := hP ⟨ι g.1, hπk _ hg⟩
    refine ⟨k, ?_⟩
    have h3 : (ι g.1) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h4 : ι (g.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h3
    have h5 : g.1 ^ 2 ^ k = 1 := Subgroup.inclusion_injective hKX (by rw [h4, map_one])
    exact Subtype.ext (by simpa using h5)
  have : Group.IsPerfect ↥Kc := Subgroup.isPerfect_iff.mpr hperf
  have : Nontrivial ↥Kc := (Subgroup.nontrivial_iff_ne_bot Kc).mpr hne
  exact quot_equiv_of_normal_image hs hZ α hnorm h2

end CFSG.Quasithin.He8
