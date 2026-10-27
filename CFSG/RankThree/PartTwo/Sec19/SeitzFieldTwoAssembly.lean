module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrow
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofOuter
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL7
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL8
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU10

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts

@[expose] def U38FieldPlaneGen : Prop :=
  ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 3 K) (E : Subgroup (MulAut (unitaryPSU h 3))),
    CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → ¬ NarrowScope 3 E → PlaneGen E

theorem prime_pow_eq_eight_u38 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : p ^ f = 8) :
    p = 2 ∧ f = 3 := by
  have h2 : p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
    exact dvd_pow_self p (by omega)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 3 by norm_num [h])⟩

theorem planeGen_of_u38_data {p f : ℕ} {K : Type} [Field K] (hU8 : U38FieldPlaneGen)
    (h : UnitaryFieldData p f K) (hp : p = 2) (hf : f = 3)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 9) (hN : ¬ NarrowScope 3 E) : PlaneGen E := by
  subst hp
  subst hf
  exact hU8 K h E hE hc hN

theorem map_congr_symm_map_congr_u38 {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (E : Subgroup (MulAut K)) :
    (E.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = E := by
  have hid : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id (MulAut K) := by
    refine MonoidHom.ext fun α => ?_
    ext x
    simp [MulAut.congr_apply]
  rw [Subgroup.map_map, hid, Subgroup.map_id]

theorem narrowScope_of_map_congr_u38 {K L : Type*} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    {E : Subgroup (MulAut K)} (h : NarrowScope p (E.map (MulAut.congr e).toMonoidHom)) :
    NarrowScope p E := by
  have h' := NarrowScope.map_congr e.symm h
  rwa [map_congr_symm_map_congr_u38] at h'

theorem planeGen_A2_wide {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hpq : 3 ≠ q.p)
    {E : Subgroup (MulAut (Cat ⟨.A 2 q, hv⟩))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hN : ¬ NarrowScope 3 E) : PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A 2 q, hv⟩ ≃* LinearFlag.projectiveSL 3 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (2 + 1) _)
  have hE' := isElemAbelian_map_congr e hE
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 9 :=
    (card_map_congr e E).trans hc
  have hN' : ¬ NarrowScope 3 (E.map (MulAut.congr e).toMonoidHom) :=
    fun h => hN (narrowScope_of_map_congr_u38 e h)
  apply planeGen_of_outer_model e
  by_cases h8 : Nat.card (GaloisField q.p q.exponent) = 8
  ·
    exact absurd (narrowScope_of_map_congr_u38 e (narrowScope_projectiveSL_eight h8 _ hE')) hN
  ·
    have h3 : (3 : GaloisField q.p q.exponent) ≠ 0 := by
      intro h0
      have h0' : ((3 : ℕ) : GaloisField q.p q.exponent) = 0 := by exact_mod_cast h0
      rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p] at h0'
      exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h0').symm
    exact planeGen_projectiveSL_field h3 h8 hE' hc' hN'

theorem planeGen_twistedA2_wide (hU8 : U38FieldPlaneGen)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hpq : 3 ≠ q.p)
    {E : Subgroup (MulAut (Cat ⟨.twistedA 2 q, hv⟩))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hout : ¬ InnerPlane ⟨.twistedA 2 q, hv⟩ 3 E)
    (hN : ¬ NarrowScope 3 E) : PlaneGen E := by
  by_cases hlift : 3 ∣ q.card + 1
  ·
    obtain ⟨-, hf, -, hne, K, _, hU, ⟨θ⟩⟩ :=
      CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
          (MulEquiv.refl (Cat ⟨.twistedA 2 q, hv⟩)))
    have hQ : q.p ^ q.exponent % 3 = 2 := by
      rw [TauCeti.PrimePower.card_def] at hlift
      omega
    have h2le : 2 ≤ q.p ^ q.exponent :=
      calc 2 ≤ q.p := q.prime_p.two_le
        _ = q.p ^ 1 := (pow_one _).symm
        _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos hf
    have hq : 2 < q.p ^ q.exponent :=
      lt_of_le_of_ne h2le (fun h => hne ⟨rfl, h.symm⟩)
    let e : Cat ⟨.twistedA 2 q, hv⟩ ≃* unitaryPSU hU 3 :=
      θ.trans (psuPrimeFormEquiv hU).symm
    have hE' := isElemAbelian_map_congr e hE
    have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 9 :=
      (card_map_congr e E).trans hc
    have hN' : ¬ NarrowScope 3 (E.map (MulAut.congr e).toMonoidHom) :=
      fun h => hN (narrowScope_of_map_congr_u38 e h)
    apply planeGen_of_outer_model e
    by_cases h8 : q.p ^ q.exponent = 8
    ·
      obtain ⟨hp2, hf3⟩ := prime_pow_eq_eight_u38 q.prime_p hf h8
      exact planeGen_of_u38_data hU8 hU hp2 hf3 hE' hc' hN'
    · exact planeGen_unitaryPSU_field hU hQ hq h8 hE' hc' hN'
  ·
    exact SeitzScopeProof.planeGen_outer_twistedA_three hv hpq hlift hE hc hout

theorem seitzThreeLThreePiField_of_u38 (hU8 : U38FieldPlaneGen) :
    SeitzThreeLThreePiField := by
  rintro ⟨d, hv⟩ p _hp _hp2 hpd _hex E hE hc ⟨hout, hN, rfl, q, hd | hd⟩
  ·
    subst hd
    exact planeGen_A2_wide hv (by simpa using hpd) hE hc hN
  ·
    subst hd
    exact planeGen_twistedA2_wide hU8 hv (by simpa using hpd) hE hc hout hN

theorem seitzThreeLThreePiFieldTwo_of_u38 (hU8 : U38FieldPlaneGen) :
    SeitzThreeLThreePiFieldTwo :=
  seitzThreeLThreePiFieldTwo_of_wide (seitzThreeLThreePiField_of_u38 hU8)

end CFSG.RankThree.PartTwo.Sec19
