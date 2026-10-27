module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndNormal

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

private theorem fsEnds_not_isCyclic_of_card {R : Type} [Group R] {E : Subgroup R} {k : ℕ}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ k) (hk : 2 ≤ k) :
    ¬ IsCyclic E := by
  intro hcyc
  haveI : IsCyclic E := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (g : R) g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
  have hle : Nat.card E ≤ 3 := by
    rw [← hg]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have h9 : 9 ≤ Nat.card E := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem isPGroup_of_isElemAbelian_three {R : Type} [Group R] {E : Subgroup R}
    (hE : IsElemAbelian 3 E) : IsPGroup 3 E := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  exact ⟨1, Subtype.ext (by simpa using hE.2 (x : R) x.2)⟩

private theorem fsEnds_noncyclic_three_of_surjective {L R : Type} [Group L] [Group R] [Finite L]
    (π : L →* R) (hπ : Function.Surjective π)
    (hE : ∃ E : Subgroup R, IsPGroup 3 E ∧ ¬ IsCyclic E) :
    ∃ S : Subgroup L, IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨E, hEp, hEnc⟩ := hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup L := E.comap π
  have hPmap : P.map π = E := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπ, top_inf_eq]
  haveI : Finite ↥P := Subtype.finite
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥P))
  let φ : ↥P →* ↥E := (π.comp P.subtype).codRestrict E (by
    intro x
    show π (P.subtype x) ∈ E
    rw [← hPmap]
    exact ⟨(x : L), x.2, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp
      (show (e : R) ∈ P.map π by rw [hPmap]; exact e.2)
    exact ⟨⟨p, hp⟩, Subtype.ext hpe⟩
  have hQtop : ((Sylow.mapSurjective (f := φ) hφsurj Q : Sylow 3 ↥E) : Subgroup ↥E) = ⊤ := by
    refine ((Sylow.mapSurjective (f := φ) hφsurj Q).is_maximal' (Q := ⊤) ?_ le_top).symm
    haveI : IsPGroup 3 ↥E := hEp
    exact IsPGroup.to_subgroup hEp ⊤
  have hQmap : (Q : Subgroup ↥P).map φ = ⊤ := by
    rw [← Sylow.coe_mapSurjective (f := φ) hφsurj Q]
    exact hQtop
  refine ⟨(Q : Subgroup ↥P).map P.subtype, Q.isPGroup'.map P.subtype, ?_⟩
  intro hScyc
  haveI : IsCyclic ((Q : Subgroup ↥P).map P.subtype) := hScyc
  have hQcyc : IsCyclic ↥Q :=
    isCyclic_of_injective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥P) P.subtype
        (Subgroup.subtype_injective P)).toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥P) P.subtype
        (Subgroup.subtype_injective P)).injective
  haveI : IsCyclic ↥Q := hQcyc
  let ψ : ↥Q →* ↥E := φ.comp (Q : Subgroup ↥P).subtype
  have hψsurj : Function.Surjective ψ := by
    intro e
    have he : e ∈ (Q : Subgroup ↥P).map φ := by rw [hQmap]; exact Subgroup.mem_top e
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp he
    exact ⟨⟨q, hq⟩, hqe⟩
  exact hEnc (isCyclic_of_surjective ψ hψsurj)

private theorem isElemAbelian_top_multiplicative_pi_zmod3 (d : ℕ) :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin d → ZMod 3))) := by
  refine ⟨inferInstance, ?_⟩
  intro x _
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  show (3 : ℕ) • Multiplicative.toAdd x = 0
  ext i
  show (3 : ℕ) • (Multiplicative.toAdd x i) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem not_isCyclic_multiplicative_pi_zmod3 (d : ℕ) (hd : 2 ≤ d) :
    ¬ IsCyclic (Multiplicative (Fin d → ZMod 3)) := by
  intro hcyc
  haveI : IsCyclic (Multiplicative (Fin d → ZMod 3)) := hcyc
  have hE := isElemAbelian_top_multiplicative_pi_zmod3 d
  have hcard : Nat.card (⊤ : Subgroup (Multiplicative (Fin d → ZMod 3))) = 3 ^ d := by
    rw [Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd), Nat.card_fun,
      Nat.card_zmod]
    simp [Nat.card_eq_fintype_card]
  exact (fsEnds_not_isCyclic_of_card hE hcard hd) (Subgroup.isCyclic ⊤)

private theorem e7_model_noncyclic_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ E : Subgroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)),
      IsPGroup 3 E ∧ ¬ IsCyclic E := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl (by rw [pow_one]; exact hK)
  let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false) ≃*
      ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K) := recipeChevEquiv .E7 K
  let T : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K) :=
    (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range
  have hTp : IsPGroup 3 T := by
    have hdom : IsPGroup 3 (⊤ : Subgroup (Multiplicative (Fin 7 → ZMod 3))) :=
      isPGroup_of_isElemAbelian_three (isElemAbelian_top_multiplicative_pi_zmod3 7)
    have h := hdom.map (TableBExcTwoTB.tE K TableBExcTwo.frameE7)
    rw [← MonoidHom.range_eq_map] at h
    simpa [T] using h
  have hTnc : ¬ IsCyclic T := by
    intro hcyc
    haveI : IsCyclic T := hcyc
    exact not_isCyclic_multiplicative_pi_zmod3 7 (by norm_num)
      (isCyclic_of_injective
        (MonoidHom.ofInjective (TableBExcTwoTB.tE_injective (K := K) TableBExcTwo.frameE7)).toMonoidHom
        (MonoidHom.ofInjective (TableBExcTwoTB.tE_injective (K := K) TableBExcTwo.frameE7)).injective)
  refine ⟨T.map e.symm.toMonoidHom, hTp.map e.symm.toMonoidHom, ?_⟩
  intro hEcyc
  haveI : IsCyclic (T.map e.symm.toMonoidHom) := hEcyc
  exact hTnc (isCyclic_of_injective
    (Subgroup.equivMapOfInjective T e.symm.toMonoidHom e.symm.injective).toMonoidHom
    (Subgroup.equivMapOfInjective T e.symm.toMonoidHom e.symm.injective).injective)

private theorem exists_noncyclic_three_of_fsLab_marking
    {L : Type} [Group L] [Finite L]
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => FSLab lab)) :
    ∃ S : Subgroup L, IsPGroup 3 S ∧ ¬ IsCyclic S := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at hmark
  obtain ⟨-, lab, _hlab, hraw⟩ := hmark
  have hFS : FSLab lab := by
    obtain ⟨R, _hRg, _I, _F, hQ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, hFS⟩ := hQ.2.2
    exact hFS
  obtain ⟨t, l, n⟩ := lab
  dsimp only [FSLab] at hFS
  obtain ⟨hn, hcase⟩ := hFS
  rcases hcase with ⟨ht, hl⟩ | ⟨ht, hl⟩ | ⟨ht, hl⟩
  ·
    subst ht; subst hl; subst hn
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, hK, hKfin, hcard, hQ⟩ := hraw
    obtain ⟨θ, -⟩ := hQ.2.2
    have hK2 : Nat.card K = 2 := by rw [hcard]; norm_num
    obtain ⟨-, E, -, -, -, hEab, hEcard⟩ :=
      OrthRestTail.torus_plus (K := K) (m := 6) hK2 (by norm_num)
    refine fsEnds_noncyclic_three_of_surjective
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      (θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))) ⟨E, isPGroup_of_isElemAbelian_three hEab, ?_⟩
    exact fsEnds_not_isCyclic_of_card hEab hEcard (by norm_num)
  ·
    subst ht; subst hl; subst hn
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, hK, hKfin, hcard, b, c, hirr, hQ⟩ := hraw
    obtain ⟨θ, -⟩ := hQ.2.2
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two le_rfl hcard
    obtain ⟨-, E, -, -, -, hEab, hEcard⟩ :=
      OrthRestTail.torus_minus (K := K) (m := 6) (n := 1) (p := 3) b c hcard
        (by norm_num) Nat.prime_three (by norm_num) (by norm_num) hirr
    refine fsEnds_noncyclic_three_of_surjective
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      (θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))) ⟨E, isPGroup_of_isElemAbelian_three hEab, ?_⟩
    exact fsEnds_not_isCyclic_of_card hEab hEcard (by norm_num)
  ·
    subst ht; subst hl; subst hn
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, hK, hKfin, hcard, hQ⟩ := hraw
    obtain ⟨θ, -⟩ := hQ.2.2
    have hK2 : Nat.card K = 2 := by rw [hcard]; norm_num
    refine fsEnds_noncyclic_three_of_surjective
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      (θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))) (e7_model_noncyclic_three hK2)

theorem sStar_of_restHyp {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) :
    x ∈ B ∧ LargeEvenSStar 3 B x L :=
  ⟨hR.1.1.2.2.2.2.2.2.1.2.1, hR.1.1.2.2.2.2.2.2.1⟩

theorem fsEnds_normal
    {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hmark : LargeEvenMarking L fun lab _ _ _ _ _ => FSLab lab) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
  obtain ⟨S, hSp, hSnc⟩ := exists_noncyclic_three_of_fsLab_marking hmark
  refine subgroupOf_centralizer_normal_of_noncyclic hR
    ⟨S.map L.subtype, ?_, hSp.map L.subtype, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact s.2
  · intro hcyc
    exact hSnc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).injective)

end CFSG.StandardType.FrameRoute
