module

public import CFSG.Quasithin.Background.ShultG53CoverFinite

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv


@[expose] def Hx (k : Fin 2) : Set ↥(alternatingGroup (Fin 6)) := {h | ρk k h (x0 k) = x0 k}

@[expose] def Hl (k : Fin 2) : Set ↥(alternatingGroup (Fin 6)) :=
  {h | ∀ y, inLine k y → inLine k (ρk k h y)}

@[expose] def a6El (σ : Perm (Fin 6)) (h : Perm.sign σ = 1) : ↥(alternatingGroup (Fin 6)) :=
  ⟨σ, Perm.mem_alternatingGroup.mpr h⟩

@[expose] def L3E (k : Fin 2) (a : Fin 9) : ↥(alternatingGroup (Fin 6)) :=
  a6El (L3P k a) (L3_ok k a).1

@[expose] def tE (k : Fin 2) : ↥(alternatingGroup (Fin 6)) := a6El (tP k) (t_ok k).1

@[expose] def SE (k : Fin 2) (j : Fin 24) : ↥(alternatingGroup (Fin 6)) :=
  a6El (SP k j) (SP_sign k j)

@[expose] def GE (k : Fin 2) (i : Fin 15) : ↥(alternatingGroup (Fin 6)) :=
  a6El (RS0 k i) (RS0_act k i).1

@[expose] def h0E (k : Fin 2) : ↥(alternatingGroup (Fin 6)) := a6El (h0P k) (h0_sign k)

theorem ρk_L3E (k : Fin 2) (a : Fin 9) : ρk k (L3E k a) (x0 k) = x0 k := by
  rw [ρk_apply]
  exact (L3_ok k a).2.1

theorem L3E_cube (k : Fin 2) (a : Fin 9) : L3E k a * L3E k a * L3E k a = 1 := by
  apply Subtype.ext
  apply Perm.ext
  intro i
  exact (L3_ok k a).2.2 i

theorem ρk_tE (k : Fin 2) : ρk k (tE k) (x0 k) = x0 k := by
  rw [ρk_apply]
  exact (t_ok k).2.1

theorem tE_sq (k : Fin 2) : tE k * tE k = 1 := by
  apply Subtype.ext
  apply Perm.ext
  intro i
  exact (t_ok k).2.2.1 i

theorem ρk_tE_y0 (k : Fin 2) : ρk k (tE k) (y0P k) + y0P k = x0 k := by
  rw [ρk_apply]
  exact (t_ok k).2.2.2

theorem ρk_GE (k : Fin 2) (i : Fin 15) : ρk k (GE k i) (x0 k) = ymap i := by
  rw [ρk_apply]
  exact (RS0_act k i).2

theorem SE_decomp (k : Fin 2) (j : Fin 24) : ∃ a b : Fin 9,
    SE k j = L3E k a * L3E k b ∨ SE k j = tE k * (L3E k a * L3E k b) := by
  obtain ⟨a, b, h | h⟩ := SP_decomp k j
  · exact ⟨a, b, Or.inl (Subtype.ext (Perm.ext fun i => h i))⟩
  · exact ⟨a, b, Or.inr (Subtype.ext (Perm.ext fun i => h i))⟩

theorem ρk_SE (k : Fin 2) (j : Fin 24) : ρk k (SE k j) (x0 k) = x0 k := by
  obtain ⟨a, b, h | h⟩ := SE_decomp k j
  · rw [h, map_mul, Module.End.mul_apply, ρk_L3E, ρk_L3E]
  · rw [h, map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, ρk_L3E, ρk_L3E, ρk_tE]

theorem exists_ρ_eq (k : Fin 2) (y : V4) (hy : y ≠ 0) :
    ∃ g : ↥(alternatingGroup (Fin 6)), ρk k g (x0 k) = y := by
  obtain ⟨i, rfl⟩ := ymap_cover y hy
  exact ⟨GE k i, ρk_GE k i⟩

theorem card_nonzero_V4 : Nat.card {y : V4 // y ≠ 0} = 15 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem Hx_decomp (k : Fin 2) {h : ↥(alternatingGroup (Fin 6))} (hh : h ∈ Hx k) :
    ∃ a b : Fin 9, h = L3E k a * L3E k b ∨ h = tE k * (L3E k a * L3E k b) := by
  classical
  let gm : V4 → ↥(alternatingGroup (Fin 6)) := fun y =>
    if hy : y = x0 k then 1 else if hex : ∃ g : ↥(alternatingGroup (Fin 6)), ρk k g (x0 k) = y
      then hex.choose else 1
  have hgm : ∀ y : V4, y ≠ 0 → ρk k (gm y) (x0 k) = y := by
    intro y hy
    by_cases hyx : y = x0 k
    · simp only [gm, dif_pos hyx, map_one, Module.End.one_apply]
      exact hyx.symm
    · have hex := exists_ρ_eq k y hy
      simp only [gm, dif_neg hyx, dif_pos hex]
      exact hex.choose_spec
  have hgm1 : gm (x0 k) = 1 := by simp [gm]
  let Φ : {y : V4 // y ≠ 0} × Fin 24 → ↥(alternatingGroup (Fin 6)) :=
    fun p => gm p.1 * SE k p.2
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨y, hy⟩, j⟩ ⟨⟨y', hy'⟩, j'⟩ hΦ
    have h1 : y = y' := by
      have := congrArg (fun g : ↥(alternatingGroup (Fin 6)) => ρk k g (x0 k)) hΦ
      simp only [Φ, map_mul, Module.End.mul_apply, ρk_SE, hgm y hy, hgm y' hy'] at this
      exact this
    subst h1
    have h2 : SE k j = SE k j' := mul_left_cancel hΦ
    have h3 : j = j' := SP_inj k j j' (fun i => by
      have := congrArg (fun g : ↥(alternatingGroup (Fin 6)) => (g : Perm (Fin 6)) i) h2
      exact this)
    subst h3
    rfl
  have hcard : Nat.card ↥(alternatingGroup (Fin 6)) ≤
      Nat.card ({y : V4 // y ≠ 0} × Fin 24) := by
    rw [Nat.card_prod, nat_card_alternatingGroup, card_nonzero_V4]
    simp [Nat.factorial]
  obtain ⟨⟨⟨y, hy⟩, j⟩, hΦ⟩ := (hinj.bijective_of_nat_card_le hcard).2 h
  have hyx : y = x0 k := by
    have := congrArg (fun g : ↥(alternatingGroup (Fin 6)) => ρk k g (x0 k)) hΦ
    simp only [Φ, map_mul, Module.End.mul_apply, ρk_SE, hgm y hy] at this
    exact this.trans hh
  have hgy : gm y = 1 := by rw [hyx, hgm1]
  have hhj : h = SE k j := by
    rw [← hΦ]
    simp only [Φ, hgy, one_mul]
  obtain ⟨a, b, h'⟩ := SE_decomp k j
  exact ⟨a, b, hhj ▸ h'⟩

end CFSG.Quasithin.ShultG53
