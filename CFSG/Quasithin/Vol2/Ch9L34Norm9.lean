module

public import CFSG.Quasithin.Vol2.Ch9L34NormGen
public import CFSG.Quasithin.Vol2.Ch9L34M9
public import CFSG.Quasithin.Background.HL3NineW9

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.L3W9

theorem card_F4_eq : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]
  norm_num

theorem congrHom_hmodEquiv_fldAut :
    congrHom (hmodEquiv (RingEquiv.refl F4)) (L3Nine.fldAut (n := 1) cjRing) = fld9 := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, rfl⟩ := toW9.surjective w
  refine (?_ : _ = toW9 (fld m)).trans (fld9_toW9 m).symm
  have h1 : L3Nine.mat ((hmodEquiv (RingEquiv.refl F4)).symm (toW9 m)) = herm m := by
    change (herm (toW9.symm (toW9 m))).map (RingEquiv.refl F4).symm = herm m
    rw [Equiv.symm_apply_apply]
    ext i j
    rfl
  change toW9 (code ((L3Nine.mat (L3Nine.fldAut cjRing
    ((hmodEquiv (RingEquiv.refl F4)).symm (toW9 m)))).map (RingEquiv.refl F4))) = toW9 (fld m)
  rw [L3Nine.mat_fldAut, h1]
  rfl

theorem normalizer_img9_le : Subgroup.normalizer (img9 : Set (MulAut W9)) ≤ rho9G.range := by
  intro x hx
  have hmap : (L3Nine.img card_F4_eq).map
      (MulAut.congr (hmodEquiv (RingEquiv.refl F4))).toMonoidHom = img9 :=
    map_img (RingEquiv.refl F4) card_F4_eq
  have hx' : x ∈ (Subgroup.normalizer (L3Nine.img card_F4_eq :
      Set (MulAut (L3Nine.HMod 1 F4)))).map
      (MulAut.congr (hmodEquiv (RingEquiv.refl F4))).toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq, hmap]
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  obtain ⟨A, σ, rfl⟩ := L3Nine.exists_eq_rhoT_mul_fldAut le_rfl card_F4_eq hy
  have hA : (MulAut.congr (hmodEquiv (RingEquiv.refl F4))).toMonoidHom
      (L3Nine.rhoT card_F4_eq A) = rho9 (mapGLF (RingEquiv.refl F4) A) :=
    congrHom_hmodEquiv_rhoT _ _ A
  rw [map_mul, hA]
  refine mul_mem ⟨SemidirectProduct.inl (mapGLF (RingEquiv.refl F4) A), ?_⟩ ?_
  · rw [rho9G, SemidirectProduct.lift_inl]
  rcases ringEquiv_eq_refl_or_cj σ with rfl | rfl
  · have h1 : L3Nine.fldAut (n := 1) (RingEquiv.refl F4) = 1 :=
      MulEquiv.ext fun X => L3Nine.mat_injective (by rw [L3Nine.mat_fldAut]; ext i j; rfl)
    rw [h1, map_one]
    exact one_mem _
  · have h2 : (MulAut.congr (hmodEquiv (RingEquiv.refl F4))).toMonoidHom
        (L3Nine.fldAut (n := 1) cjRing) = fld9 := congrHom_hmodEquiv_fldAut
    rw [h2]
    refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩
    rw [rho9G, SemidirectProduct.lift_inr, fldHom, c2Hom_apply]
    rfl

end CFSG.Quasithin.H13.Ch9.L34N
