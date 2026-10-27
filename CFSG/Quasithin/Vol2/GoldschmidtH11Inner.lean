module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Conj
public import CFSG.Quasithin.Vol2.GoldschmidtH11TauL
public import CFSG.Quasithin.Vol2.GoldschmidtH11Vec

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

theorem inner_bound (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) {A : Subgroup (MulAut (HV F a))}
    (hAL : A ≤ Lh a h) (hA1 : A ≠ ⊥) (hel : IsElemAbelian2 A) :
    rk A + a ≤ rkIdx (fixV A) := by
  set P : Subgroup SL(2, F) := A.comap (actHom a h) with hP
  have hPp : IsPGroup 2 P := fun x => ⟨1, by
    apply Subtype.ext
    apply actHom_injective a h
    have := hel.2 _ x.2
    simpa [pow_two] using this⟩
  obtain ⟨g, hg⟩ := exists_conj_unitriangular P hPp
  have hconj : conjSub (actHom a h g⁻¹) A ≠ ⊥ := conjSub_ne_bot hA1
  have hU : UType a h (conjSub (actHom a h g⁻¹) A) := by
    intro y hy
    rw [mem_conjSub] at hy
    obtain ⟨x, hx⟩ := hAL hy
    have hxP : x ∈ P := by
      show actHom a h x ∈ A
      rw [hx]; simpa using hy
    obtain ⟨d, hd⟩ := hg x hxP
    refine ⟨d, ?_⟩
    rw [← hd]
    have : y = actHom a h g⁻¹ * actHom a h x * actHom a h g := by
      rw [hx, map_inv]; group
    rw [this, ← map_mul, ← map_mul]
  have key := inner_rank hU hconj (isElemAbelian2_conjSub hel) ha
  rwa [rk_conjSub, rkIdx_fixV_conjSub] at key

theorem concl_of_le_Lh (ha : 1 < a) (h : Nat.card F = 2 ^ (2 * a))
    {A : Subgroup (MulAut (HV F a))} (hAL : A ≤ Lh a h) (hA1 : A ≠ ⊥) (hel : IsElemAbelian2 A) :
    H11Concl a (Lh a h) A := by
  have := inner_bound (by omega) h hAL hA1 hel
  exact ⟨by omega, Or.inl (by omega), fun _ => this⟩

end CFSG.Quasithin.H11
