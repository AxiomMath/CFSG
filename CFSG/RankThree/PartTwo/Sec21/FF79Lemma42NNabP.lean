module

public import CFSG.Holt.General.AltRecPrimitiveONanScott
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.Holt.General.AltRecPrim

variable {Γ : Type} [Group Γ] {N : Subgroup Γ}

@[expose] def Cj (F : SimpleFactors N) (g : Γ) (i j : Fin F.r) : Prop :=
  ∀ x : Γ, x ∈ F.S i ↔ g * x * g⁻¹ ∈ F.S j

variable (F : SimpleFactors N)

theorem S_ne {i j : Fin F.r} (hij : i ≠ j) : F.S i ≠ F.S j := by
  intro h
  obtain ⟨a, ha, c, hc, hac⟩ := F.not_commute i
  have hc' : c ∈ F.S j := h ▸ hc
  exact hac (F.commute_of_ne hij ha hc').eq

theorem Cj.symm_mem {F : SimpleFactors N} {g : Γ} {i j : Fin F.r} (h : Cj F g i j) {y : Γ}
    (hy : y ∈ F.S j) : g⁻¹ * y * g ∈ F.S i := by
  refine (h _).mpr ?_
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [e]
  exact hy

theorem Cj.unique {F : SimpleFactors N} {g : Γ} {i j j' : Fin F.r} (h : Cj F g i j)
    (h' : Cj F g i j') : j = j' := by
  by_contra hne
  apply S_ne F hne
  ext y
  constructor
  · intro hy
    have h2 := (h' _).mp (h.symm_mem hy)
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at h2
  · intro hy
    have h2 := (h _).mp (h'.symm_mem hy)
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at h2

theorem Cj.comp {F : SimpleFactors N} {g h : Γ} {i j k : Fin F.r} (hg : Cj F g i j)
    (hh : Cj F h j k) : Cj F (h * g) i k := by
  intro x
  rw [hg x, hh (g * x * g⁻¹)]
  simp only [mul_inv_rev, mul_assoc]

theorem Cj.inv {F : SimpleFactors N} {g : Γ} {i j : Fin F.r} (hg : Cj F g i j) :
    Cj F g⁻¹ j i := by
  intro x
  rw [inv_inv]
  constructor
  · exact fun hx => hg.symm_mem hx
  · intro hx
    have h2 := (hg _).mp hx
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h2

theorem Cj.one (F : SimpleFactors N) (i : Fin F.r) : Cj F 1 i i := by
  intro x
  simp

theorem Cj.of_map {F : SimpleFactors N} {g : Γ} {i j : Fin F.r}
    (h : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j) : Cj F g i j := by
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h2
    exact this ▸ hy

theorem Cj.map_eq {F : SimpleFactors N} {g : Γ} {i j : Fin F.r} (h : Cj F g i j) :
    (F.S i).map (MulAut.conj g).toMonoidHom = F.S j := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mp hx
  · intro hy
    exact ⟨g⁻¹ * y * g, h.symm_mem hy, by simp [mul_assoc]⟩

theorem exists_Cj (hN : N.Normal) (g : Γ) (i : Fin F.r) : ∃ j, Cj F g i j := by
  obtain ⟨j, hj⟩ := F.exists_map_conj_eq hN g i
  exact ⟨j, Cj.of_map hj⟩

theorem Cj_self_iff (g : Γ) (i : Fin F.r) :
    Cj F g i i ↔ g ∈ Subgroup.normalizer (F.S i : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  exact Iff.rfl

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
