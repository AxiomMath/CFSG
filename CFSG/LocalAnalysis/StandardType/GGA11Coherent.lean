module

public import CFSG.LocalAnalysis.StandardType.GGA11CohOvlEq
public import CFSG.LocalAnalysis.StandardType.GGA11CohOvlAut
public import CFSG.LocalAnalysis.StandardType.GGA11CohCocycle

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

private lemma a11co_f_eq_T9' {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (hGlue : A11GlueHyp φ₃ f n) (j : Fin 4) (hj : j ≠ 3) : f j = φ₃ (T9' j) := by
  have hjlt : j.val < 3 := by have := j.isLt; omega
  have h := hGlue.2.1 ⟨j.val, hjlt⟩
  rw [show (⟨j.val, hjlt⟩ : Fin 3).castSucc = j from Fin.ext rfl] at h
  rw [T9', dif_pos hjlt]
  exact h

private lemma a11co_commute_closure {G : Type} [Group G] {f : Fin 4 → G}
    (hcomm : ∀ i j, f i * f j = f j * f i) (k : Fin 4) {x : G}
    (hx : x ∈ Subgroup.closure (Set.range f)) : x * f k = f k * x := by
  have hle : Subgroup.closure (Set.range f) ≤ Subgroup.centralizer ({f k} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm i k)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem a11CoherentInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G),
      A11GlueHyp φ₃ f n → ∃ Φ : Fin 4 → SL 9 →* G, A11CohSpec φ₃ f n Φ := by
  intro G _ _ φ₃ f n hGlue
  have hφ : Function.Injective φ₃ := hGlue.1
  have hcomm : ∀ i j, f i * f j = f j * f i := hGlue.2.2.1
  have hn3 : n 3 = 1 := hGlue.2.2.2.2.2.1
  have hnf : ∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i) := hGlue.2.2.2.2.2.2.1
  have hcomp : φ₃.range ≤ Subgroup.centralizer ({f 3} : Set G) := hGlue.2.2.2.2.2.2.2.1
  have hEq : ∀ l m : Fin 4, l ≠ m → Ovl φ₃ n l m = Ovl φ₃ n m l :=
    fun l m h => a11OverlapEqInput_holds G φ₃ f n hGlue l m h
  have hAut : ∀ l m : Fin 4, l ≠ m → ∃ u ∈ OvlTorus f l m,
      ∀ a b : Fin 12, a ≠ b → blk a ≠ l → blk b ≠ l → blk a ≠ m → blk b ≠ m →
        Xe φ₃ n l a b = u * Xe φ₃ n m a b * u⁻¹ :=
    fun l m h => a11OverlapAutInput_holds G φ₃ f n hGlue l m h (hEq l m h)
  obtain ⟨τ, hτmem, hτ3, hτXe⟩ := a11CocycleInput_holds G φ₃ f n hGlue hAut
  let Φ : Fin 4 → SL 9 →* G := fun l => (MulAut.conj (τ l * n l)).toMonoidHom.comp φ₃
  have hΦeval : ∀ (l : Fin 4) (x : SL 9),
      Φ l x = τ l * (n l * φ₃ x * (n l)⁻¹) * (τ l)⁻¹ := by
    intro l x
    simp only [Φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [Φ, hτ3, hn3]
  · intro l
    simpa only [Φ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] using
      (MulAut.conj (τ l * n l)).injective.comp hφ
  · intro l
    change ((MulAut.conj (τ l * n l)).toMonoidHom.comp φ₃).range =
      φ₃.range.map (MulAut.conj (n l)).toMonoidHom
    rw [← MonoidHom.map_range]
    have hfl_cent : f l ∈ Subgroup.centralizer
        ((φ₃.range.map (MulAut.conj (n l)).toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      change h ∈ Subgroup.map (MulAut.conj (n l)).toMonoidHom φ₃.range at hh
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
      have ha_comm : a * f 3 = f 3 * a := Subgroup.mem_centralizer_singleton_iff.mp (hcomp ha)
      have hfl : f l = n l * f 3 * (n l)⁻¹ := by
        have h := hnf l 3
        rw [Equiv.swap_apply_right] at h
        exact h.symm
      rw [hfl]
      calc n l * a * (n l)⁻¹ * (n l * f 3 * (n l)⁻¹)
          = n l * (a * f 3) * (n l)⁻¹ := by group
        _ = n l * (f 3 * a) * (n l)⁻¹ := by rw [ha_comm]
        _ = (n l * f 3 * (n l)⁻¹) * (n l * a * (n l)⁻¹) := by group
    have hclosure : Subgroup.closure (Set.range f) ≤ Subgroup.normalizer
        (φ₃.range.map (MulAut.conj (n l)).toMonoidHom) := by
      rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      by_cases hil : i = l
      · subst hil
        exact Subgroup.centralizer_le_normalizer _ hfl_cent
      · have hjk : Equiv.swap l 3 i ≠ 3 := by
          intro hcon
          apply hil
          have hh := congrArg (Equiv.swap l 3) hcon
          rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at hh
        have hfi : f i = n l * φ₃ (T9' (Equiv.swap l 3 i)) * (n l)⁻¹ := by
          have h := hnf l (Equiv.swap l 3 i)
          rw [Equiv.swap_apply_self] at h
          rw [a11co_f_eq_T9' hGlue (Equiv.swap l 3 i) hjk] at h
          exact h.symm
        have hmem : f i ∈ φ₃.range.map (MulAut.conj (n l)).toMonoidHom :=
          Subgroup.mem_map.mpr
            ⟨φ₃ (T9' (Equiv.swap l 3 i)), ⟨_, rfl⟩,
              by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hfi.symm⟩
        exact Subgroup.le_normalizer hmem
    have htau_norm : τ l ∈ Subgroup.normalizer
        (φ₃.range.map (MulAut.conj (n l)).toMonoidHom) := hclosure (hτmem l)
    have hKmap : (φ₃.range.map (MulAut.conj (n l)).toMonoidHom).map
        (MulAut.conj (τ l)).toMonoidHom =
        φ₃.range.map (MulAut.conj (n l)).toMonoidHom :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htau_norm
    have hconj : (MulAut.conj (τ l * n l)).toMonoidHom =
        (MulAut.conj (τ l)).toMonoidHom.comp (MulAut.conj (n l)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hconj, ← Subgroup.map_map]
    exact hKmap
  · intro l k hkl
    have hjk : Equiv.swap l 3 k ≠ 3 := by
      intro hcon
      apply hkl
      have hh := congrArg (Equiv.swap l 3) hcon
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at hh
    have hfi : φ₃ (T9' (Equiv.swap l 3 k)) = f (Equiv.swap l 3 k) :=
      (a11co_f_eq_T9' hGlue (Equiv.swap l 3 k) hjk).symm
    have hnf' : n l * f (Equiv.swap l 3 k) * (n l)⁻¹ = f k := by
      have h := hnf l (Equiv.swap l 3 k)
      rwa [Equiv.swap_apply_self] at h
    have hcommτ : τ l * f k * (τ l)⁻¹ = f k := by
      have h := a11co_commute_closure hcomm k (hτmem l)
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hΦeval, hfi, hnf', hcommτ]
  · intro l m a b hab hla hlb hma hmb
    rw [hΦeval, hΦeval]
    change τ l * Xe φ₃ n l a b * (τ l)⁻¹ = τ m * Xe φ₃ n m a b * (τ m)⁻¹
    exact hτXe l m a b hab hla hlb hma hmb

end CFSG.StandardType.A11

end
