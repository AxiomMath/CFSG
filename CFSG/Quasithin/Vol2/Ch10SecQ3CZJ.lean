module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZI

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem exists_mul_of_mem_L0 {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {y : G} (hyL0 : y ∈ fsuL0 T L) :
    ∃ l ∈ L, ∃ l' ∈ CFSG.conjugate L t, l * l' = y := by
  have hLN : L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
    SecA.le_normalizer_conjugate c.hyp.fsu.maximal.1 (SecA.le_fsuM T L ht)
  rw [SecA.fsuL0_eq_sup c.h37 c.h38 c.hyp ht htn] at hyL0
  have hy' : y ∈ ((L ⊔ CFSG.conjugate L t : Subgroup G) : Set G) := hyL0
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN] at hy'
  obtain ⟨l, hl, l', hl', rfl⟩ := hy'
  exact ⟨l, hl, l', hl', rfl⟩

theorem mem_pCoreOf_of_centralizes {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G} (hxL0 : x ∈ fsuL0 T L)
    (h₁ : ∀ v ∈ fsuUL T L I, v * x = x * v)
    (h₂ : ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, v * x = x * v) :
    x ∈ pCoreOf 2 (fsuL0 T L) := by
  have hV : fsuVM T L I ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [SecA.fsuVM_eq_sup c.h37 c.h38 c.hyp ht htn,
      ← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
    exact sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (h₁ v hv))
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (h₂ v hv))
  refine SecA.fsuL0_inf_centralizer_le c.h37 c.h38 c.hyp ⟨hxL0, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV hv)

theorem mem_L_of_centralizes {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyo : Odd (orderOf y)) (hy : ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, y * v * y⁻¹ = v) :
    y ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, l', hl', rfl⟩ := c.exists_mul_of_mem_L0 ht htn hyL0
  obtain ⟨_, -, -, ha, -⟩ := c.hyp.three
  have hV₁ : fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) := (ha t ht htn).2.2
  have hV₂ := SecA.conjugate_fsuUL_le_centralizer c.h37 c.h38 c.hyp ht htn
  have hl'O : l' ∈ pCoreOf 2 (fsuL0 T L) := by
    refine c.mem_pCoreOf_of_centralizes ht htn (SecA.conjugate_le_fsuL0 ht hl')
      (fun v hv => (Subgroup.mem_centralizer_iff.mp (hV₁ hv) l' hl').symm) (fun v hv => ?_)
    have h2 : l * v = v * l := Subgroup.mem_centralizer_iff.mp (hV₂ hv) l hl
    have e : l' * v * l'⁻¹ = v := by
      calc l' * v * l'⁻¹ = l⁻¹ * (l * l' * v * (l * l')⁻¹) * l := by group
        _ = l⁻¹ * (v * l) := by rw [hy v hv]; group
        _ = v := by rw [← h2]; group
    calc v * l' = l' * v * l'⁻¹ * l' := by rw [e]
      _ = l' * v := by group
  have hON : pCoreOf 2 (fsuL0 T L) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.map_subtype_le _).trans (SecA.fsuL0_le_normalizer c.hyp.fsu.maximal.1)
  exact mul_mem_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hON hl hl'O hyo

theorem mem_Lt_of_centralizes {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyo : Odd (orderOf y)) (hy : ∀ v ∈ fsuUL T L I, y * v * y⁻¹ = v) :
    y ∈ CFSG.conjugate L t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, l', hl', rfl⟩ := c.exists_mul_of_mem_L0 ht htn hyL0
  obtain ⟨_, -, -, ha, -⟩ := c.hyp.three
  have hV₁ : fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) := (ha t ht htn).2.2
  have hV₂ := SecA.conjugate_fsuUL_le_centralizer c.h37 c.h38 c.hyp ht htn
  have hlO : l ∈ pCoreOf 2 (fsuL0 T L) := by
    refine c.mem_pCoreOf_of_centralizes ht htn (SecA.le_fsuL0 T L hl) (fun v hv => ?_)
      (fun v hv => (Subgroup.mem_centralizer_iff.mp (hV₂ hv) l hl).symm)
    have h2 : l' * v = v * l' := Subgroup.mem_centralizer_iff.mp (hV₁ hv) l' hl'
    have e : l * v * l⁻¹ = v := by
      calc l * v * l⁻¹ = l * l' * (l'⁻¹ * v * l') * (l * l')⁻¹ := by group
        _ = l * l' * v * (l * l')⁻¹ := by
          rw [show l'⁻¹ * v * l' = v by rw [mul_assoc, ← h2]; group]
        _ = v := hy v hv
    calc v * l = l * v * l⁻¹ * l := by rw [e]
      _ = l * v := by group
  have hl'L0 : l' ∈ fsuL0 T L := SecA.conjugate_le_fsuL0 ht hl'
  have hO : l'⁻¹ * l * l' ∈ pCoreOf 2 (fsuL0 T L) := by
    have h := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      ((fsuL0 T L).inv_mem hl'L0)) l).mp hlO
    simpa using h
  have hON : pCoreOf 2 (fsuL0 T L) ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
    (Subgroup.map_subtype_le _).trans
      (SecA.fsuL0_le_normalizer_conjugate c.hyp.fsu.maximal.1 (SecA.le_fsuM T L ht))
  have he : l * l' = l' * (l'⁻¹ * l * l') := by group
  rw [he] at hyo ⊢
  exact mul_mem_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hON hl' hO hyo

theorem s7 : k = n ∧ ∀ t ∈ T,
    t ∉ Subgroup.normalizer (L : Set G) →
      (b ∈ L ∧ ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, b * v * b⁻¹ = v) ∨
        (b ∈ CFSG.conjugate L t ∧ ∀ v ∈ fsuUL T L I, b * v * b⁻¹ = v) := by
  refine ⟨le_antisymm c.k_le_n c.n_le_k, fun t ht htn => ?_⟩
  obtain ⟨e, he, he1, hbe⟩ := c.exists_fix
  have hbL0 := (oTwoUpper_le _ c.hbB0).1
  rcases c.centralizes_of_fix ht htn hbL0 (oTwoUpper_le _ c.hbB0).2 c.hbo (c.E_le_V he) he1
      hbe with h₁ | h₂
  · exact Or.inr ⟨c.mem_Lt_of_centralizes ht htn hbL0 c.hbo h₁, h₁⟩
  · exact Or.inl ⟨c.mem_L_of_centralizes ht htn hbL0 c.hbo h₂, h₂⟩

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
