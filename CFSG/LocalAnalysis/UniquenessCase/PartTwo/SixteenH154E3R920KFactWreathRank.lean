module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Abs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_map_le_four_of_pRank_two_le_two {Q : Type} [Group Q] [Finite Q]
    (hrk : CFSG.Open.pRank 2 (⊤ : Subgroup Q) ≤ 2) {T : Subgroup Q} {E : Type} [Group E] [Finite E]
    (π : ↥T →* E) (hE : ∀ e : E, e * e = 1) {A : Subgroup ↥T}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card (A.map π) ≤ 4 := by
  classical
  have hcommA : ∀ a b : ↥A, a * b = b * a :=
    fun a b => Subtype.ext (hA a.1 a.2 b.1 b.2)
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hcommA }
  haveI : IsMulCommutative ↥A := IsMulCommutative.of_comm hcommA
  let ι : ↥A →* Q := T.subtype.comp A.subtype
  have hι : Function.Injective ι := by
    intro a b h
    exact A.subtype_injective (T.subtype_injective (by simpa [ι] using h))
  let f : ↥A →* E := π.comp A.subtype
  let Ω : Subgroup ↥A := (powMonoidHom 2 : ↥A →* ↥A).ker
  let Ω₁ : Subgroup Q := Ω.map ι
  have hΩcard : Nat.card Ω = Nat.card {a : ↥A // a * a = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => by simp [Ω, pow_two])
  have hΩel : IsElemAbelian 2 Ω := by
    refine ⟨inferInstance, ?_⟩
    intro x hx
    simpa [Ω, pow_two] using hx
  have hΩ₁el : IsElemAbelian 2 Ω₁ := by
    simpa [Ω₁] using CFSG.SectionRank.isElemAbelian_map hΩel ι
  have hcardmap : Nat.card Ω₁ = Nat.card Ω := by
    simpa [Ω₁] using Subgroup.card_map_of_injective (K := Ω) hι
  have hP : IsPGroup 2 Ω₁ := fun y => ⟨1, by
    apply Subtype.ext
    simpa using hΩ₁el.2 (y : Q) y.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) (le_top : Ω₁ ≤ ⊤) hΩ₁el hk).trans hrk
  have hcardle : Nat.card Ω₁ ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk2
      _ = 4 := by norm_num
  have hmap : A.map π = f.range := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
  have hF : ∀ x : ↥f.range, x * x = 1 := fun x => Subtype.ext (by simpa using hE (x : E))
  have hbound : Nat.card f.range ≤ Nat.card {a : ↥A // a * a = 1} :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2.card_le_card_sq_eq_one
      hcommA f.rangeRestrict f.rangeRestrict_surjective hF
  calc Nat.card (A.map π) = Nat.card f.range := by rw [hmap]
    _ ≤ Nat.card {a : ↥A // a * a = 1} := hbound
    _ = Nat.card Ω := hΩcard.symm
    _ = Nat.card Ω₁ := hcardmap.symm
    _ ≤ 4 := hcardle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
