module

public import CFSG.Quasithin.Vol2.Ch10SecKIe
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Monster.Code

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)}

theorem false_of_row_m12
    (h : M12Ten L ⊤ ⊥) (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨eY, heY, hw, π, hR⟩ := h
  obtain ⟨p, hp, hpe⟩ := SecA.C10P01.exists_permAct_eq heY hw
  have hmap : (m24Fix SecA.C10P01.dodecadE).map (MulAut.conj p).toMonoidHom = m24Fix eY := by
    rw [← hpe, SecA.C10P01.m24Fix_permAct hp]
  let e1 : ↥(m24Fix SecA.C10P01.dodecadE) ≃* ↥(m24Fix eY) :=
    ((m24Fix SecA.C10P01.dodecadE).equivMapOfInjective _ (MulAut.conj p).injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨⟨e2⟩, -⟩ := SecA.C10P01.m24Fix_dodecadE_props
  have hs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  let f := (e1.symm.trans e2).symm
  refine false_of_simple_surj hs ?_ hT (π.comp f.toMonoidHom) (hR.1.comp f.surjective)
  rw [CFSG.Sporadic.Mathieu.card_M12]
  exact not_targetCard_of_dvd (by norm_num)

theorem false_of_row_mhat22 (h : Mhat22Twelve L ⊤ ⊥)
    (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩ := h
  have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
    ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
  obtain ⟨-, hc3, ⟨e2⟩⟩ := hhat
  have hM : Nat.card ↥CFSG.Open.quasithinM22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  refine not_sixteen_dvd hT ?_
  rw [← Nat.card_congr e.toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Γ₀), hc3,
    Nat.card_congr e2.toEquiv, hM]
  norm_num

theorem false_of_row_m22
    (h : MathieuCocode22 L ⊤ ⊥ ∨ MathieuCode22 L ⊤ ⊥) (hT : TargetCard (Nat.card ↥L)) :
    False := by
  rcases h with ⟨x, y, hxy, π, hR⟩ | ⟨x, y, hxy, π, hR⟩
  all_goals
    obtain ⟨hs, hc⟩ := SecA.C10P01.stab_props_m22 hxy
    refine false_of_simple_surj hs ?_ hT π hR.1
    rw [hc]
    exact not_targetCard_of_dvd (by norm_num)

theorem false_of_row_m2324
    (h : MathieuCocode23 L ⊤ ⊥ ∨ MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥ ∨
      MathieuCode24 L ⊤ ⊥) (hT : TargetCard (Nat.card ↥L)) : False := by
  rcases h with ⟨x, π, hR⟩ | ⟨x, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩
  · obtain ⟨hs, hc⟩ := SecA.C10P01.stab_props_m23 x
    refine false_of_simple_surj hs ?_ hT π hR.1
    rw [hc]
    exact not_targetCard_of_dvd (by norm_num)
  · obtain ⟨hs, hc⟩ := SecA.C10P01.stab_props_m23 x
    refine false_of_simple_surj hs ?_ hT π hR.1
    rw [hc]
    exact not_targetCard_of_dvd (by norm_num)
  all_goals
    refine false_of_simple_surj AutPerm_isSimpleGroup ?_ hT π hR.1
    rw [card_AutPerm]
    exact not_targetCard_of_dvd (by norm_num)

theorem false_of_table
    [Finite V] (ht : AsB45Table G L) (hT : TargetCard (Nat.card ↥L))
    (hZ : Nat.card (Subgroup.center ↥L) ≤ 3) : False := by
  rcases ht with ⟨h, -⟩ | ⟨m, hm, h, -⟩ | ⟨m, h, -⟩ | ⟨f, h, -⟩ | ⟨m, hm, h, -⟩ | ⟨h, -⟩ |
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact false_of_row_alt7 h hT
  · exact false_of_row_orth hm h hT
  · exact false_of_row_su3 h hT hZ
  · exact false_of_row_sz h hT
  · exact false_of_row_nine hm h hT
  · exact false_of_row_g2d h hT
  · exact false_of_row_m12 h hT
  · exact false_of_row_mhat22 h hT
  · exact false_of_row_m22 (Or.inl h) hT
  · exact false_of_row_m22 (Or.inr h) hT
  · exact false_of_row_m2324 h hT

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
