module

public import CFSG.Quasithin.Background.F918K1
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Blueprint

variable {X : Type} [Group X]

private theorem ns4_false_of_simple {Γ : Type} [Group Γ] (hX : NSGroup X) (hΓ : IsSimpleGroup Γ)
    (hc : ¬ NSCard (Nat.card Γ)) (π : Γ →* X) (hπ : Function.Surjective π) : False := by
  have := hX.isSimple.toNontrivial
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hΓ π hπ
  exact hc (by rw [Nat.card_congr e.toEquiv]; exact hX.card)

theorem NSGroup.false_of_surjective_m12
    (hX : NSGroup X)
    {eY : G6.PermMod 24} (hY : eY ∈ golayC) (hw : hammingNorm (Multiplicative.toAdd eY) = 12)
    (π : ↥(m24Fix eY) →* X) (hπ : Function.Surjective π) : False := by
  obtain ⟨p, hp, hpe⟩ := C10P01.exists_permAct_eq hY hw
  have hmap : (m24Fix C10P01.dodecadE).map (MulAut.conj p).toMonoidHom = m24Fix eY := by
    rw [← hpe, C10P01.m24Fix_permAct hp]
  let e1 : ↥(m24Fix C10P01.dodecadE) ≃* ↥(m24Fix eY) :=
    ((m24Fix C10P01.dodecadE).equivMapOfInjective _ (MulAut.conj p).injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨⟨e2⟩, -⟩ := C10P01.m24Fix_dodecadE_props
  have hs : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  let e : ↥(m24Fix eY) ≃* NativeSporadic.M12 := e1.symm.trans e2
  exact ns4_false_of_simple hX hs
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; exact not_nsCard_95040)
    (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective)

theorem NSGroup.false_of_surjective_m22
    (hX : NSGroup X)
    {x y : Fin 24} (hxy : x ≠ y)
    (π : ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) →* X) (hπ : Function.Surjective π) : False := by
  obtain ⟨hs, hc⟩ := C10P01.stab_props_m22 hxy
  exact ns4_false_of_simple hX hs (by rw [hc]; exact not_nsCard_443520) π hπ

theorem NSGroup.false_of_surjective_m23
    (hX : NSGroup X) (x : Fin 24)
    (π : ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x) →* X)
    (hπ : Function.Surjective π) : False := by
  obtain ⟨hs, hc⟩ := C10P01.stab_props_m23 x
  exact ns4_false_of_simple hX hs (by rw [hc]; exact not_nsCard_10200960) π hπ

theorem NSGroup.false_of_surjective_m24 (hX : NSGroup X)
    (π : ↥CFSG.Monster.Code.AutPerm →* X) (hπ : Function.Surjective π) : False :=
  ns4_false_of_simple hX CFSG.Monster.Code.AutPerm_isSimpleGroup
    (by rw [CFSG.Monster.Code.card_AutPerm]; exact not_nsCard_244823040) π hπ

theorem NSGroup.false_of_surjective_g2derived
    (hX : NSGroup X)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* X) (hπ : Function.Surjective π) : False := by
  have hd : Nat.card X ∣ 6048 :=
    (C10P01.card_g2Two_commutator hK) ▸ Subgroup.card_dvd_of_surjective hπ
  exact not_nsCard_of_dvd_smooth (a := 5) (b := 3) (c := 0) (d := 1)
    (by rw [show 2 ^ 5 * 3 ^ 3 * 5 ^ 0 * 7 ^ 1 = 6048 by norm_num]; exact hd) hX.card

theorem NSGroup.false_of_equiv_j2 (hX : NSGroup X)
    (e : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2) : False := by
  have hc : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine not_nsCard_of_dvd_smooth (N := Nat.card X) (a := 7) (b := 3) (c := 2) (d := 1) ?_ hX.card
  rw [hc, show 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 ^ 1 = 604800 by norm_num]

end CFSG.Quasithin
