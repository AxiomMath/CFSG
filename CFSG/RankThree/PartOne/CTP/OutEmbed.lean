module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {H : Type*} [Group H]

theorem conjNormal_injective_of_centralizer (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := S)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.centralizer (S : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut S => ((φ ⟨x, hx⟩ : S) : H)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [hSc] at hc
  exact hc

noncomputable def outerHom (S : Subgroup H) [S.Normal] : H →* Outer ↥S :=
  (QuotientGroup.mk' (inner ↥S)).comp (MulAut.conjNormal (H := S))

theorem ker_outerHom (S : Subgroup H) [S.Normal] (hSc : Subgroup.centralizer (S : Set H) = ⊥) :
    (outerHom S).ker = S := by
  ext g
  constructor
  · intro hg
    have hg' : MulAut.conjNormal (H := S) g ∈ inner ↥S :=
      (QuotientGroup.eq_one_iff _).mp hg
    obtain ⟨s, hs⟩ := hg'
    have hc : (s : H)⁻¹ * g ∈ Subgroup.centralizer (S : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut S => ((φ ⟨x, hx⟩ : S) : H)) hs
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
      have h2 : (s : H) * x * (s : H)⁻¹ = g * x * g⁻¹ := by simpa using h1
      calc x * ((s : H)⁻¹ * g) = (s : H)⁻¹ * ((s : H) * x * (s : H)⁻¹) * g := by group
        _ = (s : H)⁻¹ * (g * x * g⁻¹) * g := by rw [h2]
        _ = (s : H)⁻¹ * g * x := by group
    rw [hSc, Subgroup.mem_bot] at hc
    have : g = (s : H) := (inv_mul_eq_one.mp hc).symm
    rw [this]
    exact s.2
  · intro hg
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (inner ↥S) (MulAut.conjNormal (H := S) g) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨g, hg⟩, ?_⟩
    ext x
    simp [MulAut.conj_apply, MulAut.conjNormal_apply]

theorem quotientOuterHom_injective (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) :
    Function.Injective (QuotientGroup.lift S (outerHom S)
      (fun _ hg => (MonoidHom.mem_ker (f := outerHom S)).mp
        ((ker_outerHom S hSc).symm ▸ hg))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ (outerHom S).ker := hx
  rw [ker_outerHom S hSc] at hg
  exact (QuotientGroup.eq_one_iff g).mpr hg

theorem solvable_quotient_of_outer (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) [h : Group.IsSolvable (Outer ↥S)] :
    Group.IsSolvable (H ⧸ S) :=
  Group.isSolvable_of_isSolvable_injective (quotientOuterHom_injective S hSc)

theorem card_quotient_le_outer [Finite H] (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) :
    Nat.card (H ⧸ S) ≤ Nat.card (Outer ↥S) := by
  have hfin : Finite (MulAut ↥S) :=
    Finite.of_injective (fun f : MulAut ↥S => (f : ↥S → ↥S)) DFunLike.coe_injective
  have hfin2 : Finite (Outer ↥S) :=
    Finite.of_surjective (QuotientGroup.mk' (inner ↥S)) (QuotientGroup.mk'_surjective _)
  exact Nat.card_le_card_of_injective _ (quotientOuterHom_injective S hSc)

theorem le_of_isPGroup_of_not_dvd_card_quotient [Finite H] {p : ℕ} [Fact p.Prime]
    {E S : Subgroup H} [S.Normal] (hE : IsPGroup p E) (hp : ¬ p ∣ Nat.card (H ⧸ S)) :
    E ≤ S := by
  intro x hx
  obtain ⟨k, hk⟩ := hE ⟨x, hx⟩
  have hxk : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk x : H ⧸ S) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hxk]; rfl)
  have h2 : orderOf (QuotientGroup.mk x : H ⧸ S) ∣ Nat.card (H ⧸ S) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (Nat.card (H ⧸ S)) (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp).symm
  have := Nat.eq_one_of_dvd_coprimes hcop h2 h1
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp this)

end CFSG.RankThree.PartOne.CTP
