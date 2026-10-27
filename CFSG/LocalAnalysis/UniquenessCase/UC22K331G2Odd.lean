module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331A8Shape
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.RankThree.PartOne.S11c.G2Plane
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331A8Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti CFSG.SignalizerFunctorTheorem CFSG.Blueprint.Chevalley

section Certified


theorem k331Idx_G2_odd (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hq : q.p ≠ 2) :
    K331Idx (.lie ⟨.G2 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩ T _ K hK _
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hodd : Odd (q.p ^ q.exponent) := (q.prime_p.odd_of_ne_two hq).pow
  have hKc : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv (GaloisField q.p q.exponent)
    (by rw [hKc, PrimePower.card_def])
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, PrimePower.card_def q ▸ hr⟩,
      ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hKc, ⟨e.trans b.symm⟩⟩⟩
  have hM : CFSG.Blueprint.LieModel L .G2 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hm⟩)
  have h8 : ∀ E : Subgroup L, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 8 := by
    intro E hEsq
    obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm.2
    let ψ : L →* ModGL .G2 F := (adjointGroup .G2 F).subtype.comp φ.toMonoidHom
    have hψ : Function.Injective ψ := fun a b h => φ.injective (Subtype.ext h)
    have hR : E.map ψ ≤ adjointGroup .G2 F := by
      rintro _ ⟨x, -, rfl⟩
      exact (φ x).2
    have hRsq : ∀ y ∈ E.map ψ, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hEsq x hx, map_one]
    have : Finite (E.map ψ) := Finite.of_equiv E (E.equivMapOfInjective ψ hψ).toEquiv
    have : IsElementaryAbelian 2 (E.map ψ) :=
      { is_comm := ⟨fun a b => Subtype.ext (by
          have ha : (a : ModGL .G2 F)⁻¹ = a := inv_eq_of_mul_eq_one_right (hRsq a a.2)
          have hb : (b : ModGL .G2 F)⁻¹ = b := inv_eq_of_mul_eq_one_right (hRsq b b.2)
          have hab : ((a : ModGL .G2 F) * b)⁻¹ = a * b :=
            inv_eq_of_mul_eq_one_right (hRsq _ (a * b).2)
          rw [mul_inv_rev, ha, hb] at hab
          exact hab.symm)⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (by rw [sq]; exact hRsq x x.2) }
    rw [← Subgroup.card_map_of_injective hψ]
    exact (CFSG.RankThree.PartOne.g2_elementary_two (by rw [hF]; exact hodd) hR).1
  obtain ⟨z, hz, hsec⟩ := k331_isSectionOf_centralizer h8 hK
  obtain ⟨F, _, _, S, hF, -⟩ := CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 q.prime_p hq hM z hz
  have h2 : (2 : F) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F (by rw [hF]; exact hodd)
  exact k331_not_isSectionOf_shape h2 h2 S hsec

theorem k331_g2Odd : K331Fam K331G2Odd := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · cases d with
    | G2 q => exact k331Idx_G2_odd q hv hi
    | _ => exact False.elim hi
  · exact False.elim hi

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
