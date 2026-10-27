module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModDefs
import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open

variable {V : Type} [CommGroup V]

theorem c23a_rk_le_two_of_le [Finite V] {L : Subgroup (MulAut V)} {E Z : Subgroup V}
    (h : C23ABlock L E Z) {A : Subgroup (MulAut V)} (hA : A ≤ L) (hel : IsElemAbelian 2 A) :
    rk ↥A ≤ 2 := by
  obtain ⟨D⟩ := h.nat
  let φ : ↥L ≃* GL (Fin 3) (ZMod 2) :=
    (MulEquiv.ofBijective D.ρ ⟨D.inj, D.surj⟩).symm.trans
      (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : SL3F2 →* GL (Fin 3) (ZMod 2))
        c23a_toGL_bijective)
  let A₀ : Subgroup ↥L := A.subgroupOf L
  let A₁ : Subgroup (GL (Fin 3) (ZMod 2)) := A₀.map φ.toMonoidHom
  have hsq : ∀ B ∈ A₁, B * B = 1 := by
    rintro B hB
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hB
    have hx2 : x * x = 1 := Subtype.ext (by
      have h1 := hel.2 (x : MulAut V) (Subgroup.mem_subgroupOf.mp hx)
      simpa [pow_two] using h1)
    rw [← map_mul, hx2, map_one]
  have hcomm : ∀ B ∈ A₁, ∀ B' ∈ A₁, B * B' = B' * B := by
    rintro B hB B' hB'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hB
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hB'
    have hxy : x * y = y * x := Subtype.ext (by
      have hc := (hel.1.is_comm).comm
        (⟨(x : MulAut V), Subgroup.mem_subgroupOf.mp hx⟩ : ↥A)
        (⟨(y : MulAut V), Subgroup.mem_subgroupOf.mp hy⟩ : ↥A)
      simpa using congrArg Subtype.val hc)
    rw [← map_mul, ← map_mul, hxy]
  have hcard_le : Nat.card ↥A₁ ≤ Nat.card (ZMod 2) ^ 2 :=
    CFSG.Quasithin.H.card_le_of_elemAbelian_GL3 A₁ hsq hcomm
  have hcard_map : Nat.card ↥A₁ = Nat.card ↥A₀ :=
    Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective
  have hcard_sub : Nat.card ↥A₀ = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have heq : Nat.card ↥A = Nat.card ↥A₁ := hcard_sub.symm.trans hcard_map.symm
  have hcard : Nat.card ↥A ≤ 2 ^ 2 := by
    rw [heq]
    calc Nat.card ↥A₁ ≤ Nat.card (ZMod 2) ^ 2 := hcard_le
      _ = 2 ^ 2 := by rw [Nat.card_zmod]
  have hcardA : Nat.card ↥A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun v : ↥A =>
      Subtype.ext (by simpa using hel.2 (v : MulAut V) v.2))
  have hpow : 2 ^ rk ↥A ≤ 2 ^ 2 := by
    rw [← hcardA]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
