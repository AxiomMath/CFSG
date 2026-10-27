module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZH
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZG

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

theorem exists_fix :
    ∃ e ∈ omegaOneCenterOf (thompsonJ T), e ≠ 1 ∧ b * e * b⁻¹ = e := by
  by_contra hcon
  push Not at hcon
  have h1 := c.card_le_of_fix le_rfl fun a ha hba => by_contra fun h => hcon a ha h hba
  have h2 := c.card_E
  have hkn := c.k_le_n
  have hn := c.h1.1
  have h3 : 2 ^ k < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem fix_components {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {y : G} (hyL0 : y ∈ fsuL0 T L) {e : G}
    (he : e ∈ fsuVM T L I) (hye : y * e * y⁻¹ = e) :
    ∃ e₁ ∈ fsuUL T L I, ∃ e₂ ∈ CFSG.conjugate (fsuUL T L I) t, e₁ * e₂ = e ∧
      y * e₁ * y⁻¹ = e₁ ∧ y * e₂ * y⁻¹ = e₂ := by
  have hloc := c.hyp.fsu.maximal.1
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  obtain ⟨e₁, he₁, e₂, he₂, hw⟩ := SecA.exists_mul_of_mem_fsuVM c.h37 c.h38 c.hyp ht htn he
  have h12 : ∀ v, v ∈ fsuUL T L I → v ∈ CFSG.conjugate (fsuUL T L I) t → v = 1 := by
    intro v hv1 hv2
    have := SecA.inf_conjugate_le_fsuCVM c.hyp ht htn ⟨hv1, hv2⟩
    rwa [c.fsuCVM_eq_bot, Subgroup.mem_bot] at this
  have hN₁ : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer hloc)
  have hN₂ : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I) t : Set G) := by
    rw [SecA.conjugate_commutator_fsuVM htM]
    exact SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer_conjugate hloc htM)
  have hyw₁ : y * e₁ * y⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp (hN₁ hyL0) _).mp he₁
  have hyw₂ : y * e₂ * y⁻¹ ∈ CFSG.conjugate (fsuUL T L I) t :=
    (Subgroup.mem_normalizer_iff.mp (hN₂ hyL0) _).mp he₂
  have hkey : e₁⁻¹ * (y * e₁ * y⁻¹) = e₂ * (y * e₂ * y⁻¹)⁻¹ := by
    have e : y * e₁ * y⁻¹ * (y * e₂ * y⁻¹) = e₁ * e₂ := by
      calc y * e₁ * y⁻¹ * (y * e₂ * y⁻¹) = y * (e₁ * e₂) * y⁻¹ := by group
        _ = e₁ * e₂ := by rw [hw, hye]
    rw [eq_mul_inv_of_mul_eq e]
    group
  have ha1 := h12 _ ((fsuUL T L I).mul_mem ((fsuUL T L I).inv_mem he₁) hyw₁)
    (hkey ▸ (CFSG.conjugate (fsuUL T L I) t).mul_mem he₂
      ((CFSG.conjugate (fsuUL T L I) t).inv_mem hyw₂))
  refine ⟨e₁, he₁, e₂, he₂, hw, ?_, ?_⟩
  · rw [inv_mul_eq_one] at ha1
    exact ha1.symm
  · rw [hkey, mul_inv_eq_one] at ha1
    exact ha1.symm

theorem centralizes_of_fix {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) (hyo : Odd (orderOf y)) {e : G}
    (he : e ∈ fsuVM T L I) (he1 : e ≠ 1) (hye : y * e * y⁻¹ = e) :
    (∀ v ∈ fsuUL T L I, y * v * y⁻¹ = v) ∨
      ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, y * v * y⁻¹ = v := by
  obtain ⟨e₁, he₁, e₂, he₂, he12, hy₁, hy₂⟩ := c.fix_components ht htn hyL0 he hye
  by_cases h₁ : e₁ = 1
  · right
    have he₂1 : e₂ ≠ 1 := by
      rintro rfl
      rw [h₁, one_mul] at he12
      exact he1 he12.symm
    exact c.fix_V₂ ht hyL0 hyN hyo he₂ he₂1 hy₂
  · exact Or.inl (c.fix_V₁ hyL0 hyN hyo he₁ h₁ hy₁)

theorem not_both {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    (h₁ : ∀ v ∈ fsuUL T L I, b * v * b⁻¹ = v)
    (h₂ : ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, b * v * b⁻¹ = v) : False := by
  have hc : ∀ v : G, b * v * b⁻¹ = v → v ∈ Subgroup.centralizer ({b} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc v * b = b * v * b⁻¹ * b := by rw [hv]
        _ = b * v := by group)
  have hV : fsuVM T L I ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [SecA.fsuVM_eq_sup c.h37 c.h38 c.hyp ht htn,
      ← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
    exact sup_le (fun v hv => hc v (h₁ v hv)) (fun v hv => hc v (h₂ v hv))
  exact c.hbZ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV (c.Z_le_V hz)))

theorem E₂_facts {t : G} (ht : t ∈ T) :
    CFSG.conjugate (fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) t ≤
        omegaOneCenterOf (thompsonJ T) ∧
      CFSG.conjugate (fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) t ≤
        CFSG.conjugate (fsuUL T L I) t ∧
      Nat.card ↥(CFSG.conjugate (fsuUL T L I ⊓
        Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) t) = 2 ^ n := by
  refine ⟨fun x hx => ?_, fun x hx => SecA.mem_conjugate_iff.mpr
    (SecA.mem_conjugate_iff.mp hx).1, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_E T (T.inv_mem ht)) _).mp
      (c.E₁_le_E (SecA.mem_conjugate_iff.mp hx))
    simpa [mul_assoc] using h
  · rw [← c.card_E₁]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem n_le_k : n ≤ k := by
  obtain ⟨t, ht, htn⟩ := c.exists_t
  obtain ⟨e, he, he1, hbe⟩ := c.exists_fix
  have hbL0 := (oTwoUpper_le _ c.hbB0).1
  have hbN := (oTwoUpper_le _ c.hbB0).2
  have hle : 2 ^ n ≤ 2 ^ k := by
    rcases c.centralizes_of_fix ht htn hbL0 hbN c.hbo (c.E_le_V he) he1 hbe with h₁ | h₂
    · obtain ⟨hE₂E, hE₂V, hE₂c⟩ := c.E₂_facts ht
      rw [← hE₂c]
      refine c.card_le_of_fix hE₂E fun a ha hba => by_contra fun ha1 => ?_
      exact c.not_both ht htn h₁ (c.fix_V₂ ht hbL0 hbN c.hbo (hE₂V ha) ha1 hba)
    · rw [← c.card_E₁]
      refine c.card_le_of_fix c.E₁_le_E fun a ha hba => by_contra fun ha1 => ?_
      exact c.not_both ht htn (c.fix_V₁ hbL0 hbN c.hbo ha.1 ha1 hba) h₂
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
