module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isElemAbelian2_of_sq_eq_one {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
    (hA : ∀ a ∈ A, a ^ 2 = 1) : IsElemAbelian2 A := by
  refine ⟨fun a ha b hb => ?_, hA⟩
  have h1 : a * a = 1 := by rw [← sq]; exact hA a ha
  have h2 : b * b = 1 := by rw [← sq]; exact hA b hb
  have h3 : b * a * (b * a) = 1 := by rw [← sq]; exact hA _ (A.mul_mem hb ha)
  calc a * b = a * b * (b * a * (b * a)) := by rw [h3, mul_one]
    _ = a * (b * b) * a * (b * a) := by simp only [mul_assoc]
    _ = b * a := by rw [h2, mul_one, h1, one_mul]

theorem subgroupOf_inf_center_eq_bot_of_o2Trivial {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} (hO2 : O2Trivial L) (hA : IsElemAbelian2 A) :
    A.subgroupOf L ⊓ Subgroup.center ↥L = ⊥ := by
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let A' : Subgroup ↥L := A.subgroupOf L
  let P : Subgroup (MulAut W) := (A' ⊓ Z).map L.subtype
  have hPle : P ≤ L := Subgroup.map_subtype_le _
  have hPbot : P = ⊥ := by
    refine hO2 P hPle ?_ ?_
    · have hsub : P.subgroupOf L = A' ⊓ Z := by
        apply Subgroup.map_injective L.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hPle]
      rw [hsub]
      exact Subgroup.normal_of_le_center inf_le_right
    · have hPel : IsElemAbelian2 P := by
        constructor
        · intro x hx y hy
          obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
          obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
          simpa using hA.1 x'.1 (Subgroup.mem_subgroupOf.1 hx'.1)
            y'.1 (Subgroup.mem_subgroupOf.1 hy'.1)
        · intro x hx
          obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
          simpa using hA.2 x'.1 (Subgroup.mem_subgroupOf.1 hx'.1)
      exact E3.isPGroup_of_isElemAbelian2 hPel
  have hP'bot : A' ⊓ Z = ⊥ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_bot]
    exact hPbot
  simpa [A', Z] using hP'bot

theorem card_le_of_sq_eq_one_of_o2Trivial {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} (hO2 : O2Trivial L) (hAL : A ≤ L) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {S : Type*} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    Nat.card A ≤ 2 ^ r := by
  have hA : IsElemAbelian2 A := isElemAbelian2_of_sq_eq_one hA2
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let A' : Subgroup ↥L := A.subgroupOf L
  have hP'bot : A' ⊓ Z = ⊥ := subgroupOf_inf_center_eq_bot_of_o2Trivial hO2 hA
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπinj : ∀ a b : ↥L, a ∈ A' → b ∈ A' → π a = π b → a = b := by
    intro a b ha hb hab
    have hker : a⁻¹ * b ∈ Z := QuotientGroup.eq.1 (e.injective hab)
    have hmem : a⁻¹ * b ∈ A' ⊓ Z := ⟨A'.mul_mem (A'.inv_mem ha) hb, hker⟩
    rw [hP'bot] at hmem
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 hmem)
  let B : Subgroup S := A'.map π
  have hfinj : Function.Injective (π.comp A'.subtype) := by
    intro a b hab
    exact Subtype.ext (hπinj a.1 b.1 a.2 b.2 hab)
  have hcardB : Nat.card B = Nat.card A' := by
    have hrange : (π.comp A'.subtype).range = B := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hcardA' : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    calc π a * π b = π (a * b) := (map_mul π a b).symm
      _ = π (b * a) := by
          congr 1
          exact Subtype.ext (hA.1 a.1 (Subgroup.mem_subgroupOf.1 ha) b.1
            (Subgroup.mem_subgroupOf.1 hb))
      _ = π b * π a := map_mul π b a
  have hsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    calc π a * π a = π (a * a) := (map_mul π a a).symm
      _ = π 1 := by
          congr 1
          apply Subtype.ext
          simpa [pow_two] using hA.2 a.1 (Subgroup.mem_subgroupOf.1 ha)
      _ = 1 := map_one π
  rw [← hcardA', ← hcardB]
  exact hr B hcomm hsq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
