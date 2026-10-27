module

public import CFSG.Quasithin.Background.HFL3Q
public import CFSG.Quasithin.Background.HL3NineW9

public section

namespace CFSG.Quasithin.H.L3W9

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H13.Ch9.Herm9

theorem card_F4' : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]
  norm_num

theorem exists_conj_eq_QW9 {X : Subgroup (MulAut W9)}
    (hXN : X ≤ Subgroup.normalizer (img9 : Set (MulAut W9))) (hXe : IsElemAbelian 2 X)
    (hX : Nat.card ↥X = 2 ^ 4) (hfX : Nat.card ↥(fixV X) = 2 ^ 4) :
    ∃ c ∈ Subgroup.normalizer (img9 : Set (MulAut W9)),
      X.map (MulAut.conj c).toMonoidHom =
        (Q2 F4).map (rho9.comp Matrix.SpecialLinearGroup.toGL) := by
  have hK := card_F4'
  set E := hmodEquiv (RingEquiv.refl F4) with hE
  set Φ := (MulAut.congr E).toMonoidHom with hΦ
  set Ψ := (MulAut.congr E.symm).toMonoidHom with hΨ
  have himg : (img hK).map Φ = img9 := map_img (RingEquiv.refl F4) hK
  have hrho : ∀ A : GL (Fin 3) F4, Φ (rhoT hK A) = rho9 A := by
    intro A
    refine (congrHom_hmodEquiv_rhoT (RingEquiv.refl F4) hK A).trans ?_
    congr 1
  have hΦΨ : Φ.comp Ψ = MonoidHom.id _ := by
    ext x w
    simp [hΦ, hΨ, MulAut.congr_apply]
  have hΨΦ : Ψ.comp Φ = MonoidHom.id _ := by
    ext x w
    simp [hΦ, hΨ, MulAut.congr_apply]
  set X₀ := X.map Ψ with hX₀
  have hXX₀ : X₀.map Φ = X := by
    rw [hX₀, Subgroup.map_map, hΦΨ, Subgroup.map_id]
  have hnorm : (L3Nine.norm hK).map Φ = Subgroup.normalizer (img9 : Set (MulAut W9)) := by
    rw [L3Nine.norm, ← himg]
    exact Subgroup.map_equiv_normalizer_eq _ (MulAut.congr E)
  have hX₀N : X₀ ≤ L3Nine.norm hK := by
    have h1 : X₀ ≤ ((L3Nine.norm hK).map Φ).map Ψ := by
      rw [hnorm]
      exact Subgroup.map_mono hXN
    rwa [Subgroup.map_map, hΨΦ, Subgroup.map_id] at h1
  have hX₀e : IsElemAbelian2 X₀ := by
    have hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hXe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hs : ∀ x ∈ X, x ^ 2 = 1 := hXe.2
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hc x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hs x hx, map_one]
  have hcX₀ : Nat.card ↥X₀ = Nat.card F4 ^ 2 := by
    rw [hX₀, Subgroup.card_map_of_injective (MulAut.congr E.symm).injective, hX,
      Nat.card_eq_fintype_card, F4.card]
    norm_num
  have hΨapp : ∀ (x : MulAut W9) (v : L3Nine.HMod 1 F4), Ψ x v = E.symm (x (E v)) :=
    fun x v => rfl
  have hfixcard : Nat.card ↥(fixV X₀) = Nat.card ↥(fixV X) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨E v, fun x hx => ?_⟩
        invFun := fun w => ⟨E.symm w, ?_⟩
        left_inv := fun v => Subtype.ext (E.symm_apply_apply _)
        right_inv := fun w => Subtype.ext (E.apply_symm_apply _) }
    · have h1 : E.symm (x (E v)) = v := v.2 (Ψ x) ⟨x, hx, rfl⟩
      calc x (E v) = E (E.symm (x (E v))) := (E.apply_symm_apply _).symm
        _ = E v := congrArg E h1
    · rintro _ ⟨x, hx, rfl⟩
      show E.symm (x (E (E.symm w))) = E.symm w
      calc E.symm (x (E (E.symm w))) = E.symm (x w) := by rw [E.apply_symm_apply]
        _ = E.symm w := congrArg E.symm (w.2 x hx)
  have hfX₀ : 2 ^ 1 < Nat.card ↥(fixV X₀) := by
    rw [hfixcard, hfX]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_eq_Q2 (le_refl 1) hK hX₀N hX₀e hcX₀.ge hfX₀
  set c := Φ (rho hK g) with hc
  have hc9 : c = rho9 (Matrix.SpecialLinearGroup.toGL g) := hrho _
  refine ⟨c, ?_, ?_⟩
  · rw [hc9]
    exact Subgroup.le_normalizer ⟨g, rfl⟩
  · have h1 : (MulAut.conj c).toMonoidHom.comp Φ =
        Φ.comp (MulAut.conj (rho hK g)).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      show c * Φ x * c⁻¹ = Φ (rho hK g * x * (rho hK g)⁻¹)
      rw [hc, map_mul, map_mul, map_inv]
    have h2 : Φ.comp (rho hK) = rho9.comp Matrix.SpecialLinearGroup.toGL :=
      MonoidHom.ext fun x => hrho _
    rw [← hXX₀, Subgroup.map_map, h1, ← Subgroup.map_map, hg, Subgroup.map_map, h2]

end CFSG.Quasithin.H.L3W9
