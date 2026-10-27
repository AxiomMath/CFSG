module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43RedA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s16ku43_exists_embedding {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {S : Type} [Group S] [Finite S] (hHat : IsHat ↥H S)
    (hirr : IsIrrOn H ⊤ ⊥) (hcard : Nat.card W = 2 ^ 12) {w : W} (hw : w ≠ 1) :
    ∃ ψ : ↥(ptCent H w) →* S, Function.Injective ψ ∧ ψ.range.index ≤ 1365 := by
  classical
  obtain ⟨e⟩ := hHat.2.2
  let inc : ↥(ptCent H w) →* ↥H := Subgroup.inclusion inf_le_left
  let φ : ↥(ptCent H w) →* ↥H ⧸ Subgroup.center ↥H :=
    (QuotientGroup.mk' (Subgroup.center ↥H)).comp inc
  let ψ : ↥(ptCent H w) →* S := e.toMonoidHom.comp φ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
    have hxZ : inc x ∈ Subgroup.center ↥H := by
      have h : (inc x : ↥H ⧸ Subgroup.center ↥H) = 1 := by simpa [φ] using hx1
      exact (QuotientGroup.eq_one_iff (inc x)).mp h
    have hfix : ((inc x : ↥H) : MulAut W) w = w := by
      have hxfix : (x : MulAut W) w = w := by
        have h := MulAction.mem_stabilizer_iff.mp x.2.2
        simpa [MulAut.smul_def] using h
      change (x : MulAut W) w = w
      exact hxfix
    by_contra hxne
    have hincne : inc x ≠ 1 := fun h => hxne (Subgroup.inclusion_injective inf_le_left h)
    have hzc : ∀ h ∈ H, h * ((inc x : ↥H) : MulAut W) =
        ((inc x : ↥H) : MulAut W) * h := by
      intro h hh
      have hcomm := (Subgroup.mem_center_iff.mp hxZ) (⟨h, hh⟩ : ↥H)
      simpa using congrArg (fun t : ↥H => (t : MulAut W)) hcomm
    exact hw (s16ku43_center_fixes_only_one hirr (inc x).2 hzc
      (fun h => hincne (Subtype.ext h)) hfix)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact hφinj (e.injective hxy)
  refine ⟨ψ, hψinj, ?_⟩
  have hmn : Nat.card ↥ψ.range = Nat.card ↥(ptCent H w) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hHcard : Nat.card ↥H = Nat.card S * 3 := by
    have h1 : Nat.card ↥H =
        Nat.card (↥H ⧸ Subgroup.center ↥H) * Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥H)
    have h2 : Nat.card (↥H ⧸ Subgroup.center ↥H) = Nat.card S := Nat.card_congr e.toEquiv
    rw [h2, hHat.2.1] at h1
    exact h1
  have hle : Nat.card ↥H ≤ (Nat.card W - 1) * Nat.card ↥(ptCent H w) :=
    s16ku43_card_le_orbit_mul H hw
  have hW : Nat.card W - 1 = 4095 := by rw [hcard]; norm_num
  have hbound : Nat.card S * 3 ≤ 4095 * Nat.card ↥(ptCent H w) := by
    rw [hHcard, hW] at hle
    exact hle
  have hSle : Nat.card S ≤ 1365 * Nat.card ↥(ptCent H w) := by
    have h3 : (4095 : ℕ) = 3 * 1365 := by norm_num
    rw [h3, mul_assoc] at hbound
    rw [mul_comm (Nat.card S) 3] at hbound
    exact Nat.le_of_mul_le_mul_left hbound (by norm_num)
  have hSle' : Nat.card S ≤ 1365 * Nat.card ↥ψ.range := by
    rw [hmn]
    exact hSle
  have hcardmul : Nat.card ↥ψ.range * ψ.range.index = Nat.card S :=
    Subgroup.card_mul_index ψ.range
  have hpos : 0 < Nat.card ↥ψ.range :=
    Nat.card_pos_iff.2 ⟨⟨1, ψ.range.one_mem⟩, inferInstance⟩
  have hle' : Nat.card ↥ψ.range * ψ.range.index ≤ Nat.card ↥ψ.range * 1365 := by
    rw [hcardmul, mul_comm (Nat.card ↥ψ.range) 1365]
    exact hSle'
  exact Nat.le_of_mul_le_mul_left hle' hpos

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
