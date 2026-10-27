module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecWeyl
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Geom
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Second
public import CFSG.LieType.AlgebraicGroups.ToralRootCoverWords
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv

open scoped CFSG.ConvolutionPoints


variable {L : Type} [Field L]

theorem graphCentralizer_secElt_eq (h2 : (2 : L) = 0) {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) :
    graphCentralizer TwistTag.D4.tag L (secElt μ) = secM μ := by
  have hμ3 := pow_three_of_sq_add hμ
  refine le_antisymm (fun g hg => ?_) (secM_le h2 hμ3)
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  have hfix : secElt μ * g * (secElt μ)⁻¹ = g := by rw [← hgc, mul_inv_cancel_right]
  obtain ⟨w, hw, v, hv, h, hh, u, hu, hvf, hhf, huf, rfl⟩ :=
    exists_sec_fixed_factor hμ3 hgG hfix
  obtain ⟨a₀, a₁, a₂, rfl⟩ := exists_eq_secOrbitX_of_fixed h2 hμ hv hvf
  obtain ⟨b₀, b₁, b₂, rfl⟩ := exists_eq_secOrbitX_of_fixed h2 hμ hu huf
  have hX := secOrbitX_mem_secM (L := L) μ
  exact mul_mem (mul_mem (mul_mem (mul_mem (hX 0 a₀) (hX 1 a₁)) (hX 2 a₂))
    (mem_secM_of_fixed_monomial h2 hμ hw hh hhf)) (mul_mem (mul_mem (hX 0 b₀) (hX 1 b₁))
      (hX 2 b₂))

@[expose] def secOrbitWord (R : Type) [CommRing R] (j : Fin 3) (ε : Bool) (κ c : R) :
    List (Letter TwistTag.D4.tag × R) :=
  canonicalWord TwistTag.D4.tag R (secW j) ++
    (if ε then [((0, true), c), ((1, true), κ * c), ((3, true), κ ^ 2 * c)]
      else [((0, false), c), ((1, false), κ ^ 2 * c), ((3, false), κ * c)]) ++
    invWord (canonicalWord TwistTag.D4.tag R (secW j))

theorem mapWord_secOrbitWord {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (j : Fin 3)
    (ε : Bool) (κ c : R) :
    mapWord f (secOrbitWord R j ε κ c) = secOrbitWord S j ε (f κ) (f c) := by
  unfold secOrbitWord
  rw [mapWord_append, mapWord_append, mapWord_invWord, mapWord_canonicalWord]
  cases ε <;> simp [mapWord]

theorem wordUnit_secOrbitWord (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3) (ε : Bool) (c : L) :
    wordUnit TwistTag.D4.tag L (secOrbitWord L j ε (secKappa μ j) c) =
      if ε then secOrbitX μ j c else secOrbitY μ j c := by
  have hv0 : secW j • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j 0 := secW_smul j 0
  have hv1 : secW j • (Pi.single 1 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j 1 := secW_smul j 1
  have hv3 : secW j • (Pi.single 3 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j 2 := secW_smul j 2
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) with hn
  have e : ∀ a b c : ModGL TwistTag.D4.tag L,
      n * a * (b * c) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) * (n * c * n⁻¹) := fun a b c => by
    group
  have hx : ∀ (i : Fin TwistTag.D4.tag.rank) (x : L), n * xUnit TwistTag.D4.tag L i x * n⁻¹ =
      pinnedX TwistTag.D4.tag L (secW j • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) x :=
    fun i x => by
      rw [← pinnedX_single, hn, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single _ i)]
  have hy : ∀ (i : Fin TwistTag.D4.tag.rank) (x : L), n * yUnit TwistTag.D4.tag L i x * n⁻¹ =
      pinnedX TwistTag.D4.tag L (-(secW j • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ))) x :=
    fun i x => by
      rw [← pinnedX_neg_single, hn,
        canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (IsRoot.neg (isRoot_single _ i)), smul_neg]
  unfold secOrbitWord
  rw [wordUnit_append, wordUnit_append, wordUnit_invWord, wordUnit_canonicalWord, ← hn]
  cases ε
  · simp only [Bool.false_eq_true, ite_false, wordUnit_cons, wordUnit_nil, letterUnit, mul_one]
    rw [← mul_assoc, e, hy, hy, hy, hv0, hv1, hv3, secOrbitY]
  · simp only [ite_true, wordUnit_cons, wordUnit_nil, letterUnit, mul_one]
    rw [← mul_assoc, e, hx, hx, hx, hv0, hv1, hv3, secOrbitX]

variable [IsAlgClosed L]

variable (L) in
@[expose] def secOrbitCurve (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3) (ε : Bool) :
    WordCurve TwistTag.D4.tag L :=
  WordCurve.ofWord (Polynomial L)
    (secOrbitWord (Polynomial L) j ε (Polynomial.C (secKappa μ j)) Polynomial.X)
    (Polynomial.aeval 0) (by
      rw [mapWord_secOrbitWord]
      simp only [AlgHom.coe_toRingHom, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [wordUnit_secOrbitWord h2]
      cases ε
      · simp [secOrbitY, pinnedX_zero]
      · simp [secOrbitX, pinnedX_zero])

theorem values_secOrbitCurve (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3) (ε : Bool) :
    (secOrbitCurve L h2 μ j ε).values =
      ((secH μ (some (j, ε)) : Subgroup (ModGL TwistTag.D4.tag L)) :
        Set (ModGL TwistTag.D4.tag L)) := by
  rw [secOrbitCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    beta_reduce
    rw [mapWord_secOrbitWord]
    simp only [AlgHom.coe_toRingHom]
    rw [← Polynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      wordUnit_secOrbitWord h2]
    cases ε
    · exact ⟨Multiplicative.ofAdd (z Polynomial.X), rfl⟩
    · exact ⟨Multiplicative.ofAdd (z Polynomial.X), rfl⟩
  · intro hg
    have hg' : ∃ c : L, g = if ε then secOrbitX μ j c else secOrbitY μ j c := by
      cases ε
      · obtain ⟨c, rfl⟩ := hg
        exact ⟨c.toAdd, rfl⟩
      · obtain ⟨c, rfl⟩ := hg
        exact ⟨c.toAdd, rfl⟩
    obtain ⟨c, rfl⟩ := hg'
    refine ⟨Polynomial.aeval c, ?_⟩
    beta_reduce
    rw [mapWord_secOrbitWord]
    simp only [AlgHom.coe_toRingHom, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact wordUnit_secOrbitWord h2 μ j ε c

@[expose] def secConjCurve (F : WordCurve TwistTag.D4.tag L)
    (zw : List (Letter TwistTag.D4.tag × L)) : WordCurve TwistTag.D4.tag L where
  D := F.D
  word := mapWord (algebraMap L F.D) zw ++ F.word ++ invWord (mapWord (algebraMap L F.D) zw)
  base := F.base
  base_eq := by
    have hid : (F.base : F.D →+* L).comp (algebraMap L F.D) = RingHom.id L := by
      ext c
      exact F.base.commutes c
    rw [mapWord_append, mapWord_append, mapWord_invWord, mapWord_mapWord, hid, wordUnit_append,
      wordUnit_append, wordUnit_invWord, F.base_eq, mul_one]
    have hmap : mapWord (RingHom.id L) zw = zw := by simp [mapWord]
    rw [hmap, mul_inv_cancel]

theorem values_secConjCurve (F : WordCurve TwistTag.D4.tag L)
    (zw : List (Letter TwistTag.D4.tag × L)) :
    (secConjCurve F zw).values = (fun g => wordUnit TwistTag.D4.tag L zw * g *
      (wordUnit TwistTag.D4.tag L zw)⁻¹) '' F.values := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    let x' : F.D →ₐ[L] L := x
    have hid : (x' : F.D →+* L).comp (algebraMap L F.D) = RingHom.id L := by
      ext c
      exact x'.commutes c
    have hmap : mapWord (RingHom.id L) zw = zw := by simp [mapWord]
    refine ⟨_, ⟨x', rfl⟩, ?_⟩
    change _ = wordUnit TwistTag.D4.tag L (mapWord (x' : F.D →+* L)
      (mapWord (algebraMap L F.D) zw ++ F.word ++ invWord (mapWord (algebraMap L F.D) zw)))
    rw [mapWord_append, mapWord_append, mapWord_invWord, mapWord_mapWord, hid, hmap,
      wordUnit_append, wordUnit_append, wordUnit_invWord]
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    have hid : (x : F.D →+* L).comp (algebraMap L F.D) = RingHom.id L := by
      ext c
      exact x.commutes c
    have hmap : mapWord (RingHom.id L) zw = zw := by simp [mapWord]
    refine ⟨x, ?_⟩
    change wordUnit TwistTag.D4.tag L (mapWord (x : F.D →+* L)
      (mapWord (algebraMap L F.D) zw ++ F.word ++ invWord (mapWord (algebraMap L F.D) zw))) = _
    rw [mapWord_append, mapWord_append, mapWord_invWord, mapWord_mapWord, hid, hmap,
      wordUnit_append, wordUnit_append, wordUnit_invWord]

@[expose] def secCurve (h2 : (2 : L) = 0) (μ : Lˣ) :
    Option (Fin 3 × Bool) → WordCurve TwistTag.D4.tag L
  | none => d4FixedTorusCurve L
  | some (j, ε) => secOrbitCurve L h2 μ j ε

theorem values_secCurve (h2 : (2 : L) = 0) (μ : Lˣ) (o : Option (Fin 3 × Bool)) :
    (secCurve h2 μ o).values = (secH μ o : Set (ModGL TwistTag.D4.tag L)) := by
  rcases o with _ | ⟨j, ε⟩
  · exact values_d4FixedTorusCurve
  · exact values_secOrbitCurve h2 μ j ε

@[expose] def secZWord (μ : Lˣ) : List (Letter TwistTag.D4.tag × L) :=
  [((2, false), (μ : L)), ((2, true), 1)]

theorem wordUnit_secZWord (μ : Lˣ) :
    wordUnit TwistTag.D4.tag L (secZWord μ) =
      yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 := by
  simp [secZWord, wordUnit_cons, wordUnit_nil, letterUnit]

theorem graphCentralizer_conj {z : ModGL TwistTag.D4.tag L}
    (hz : z ∈ adjointGroup TwistTag.D4.tag L) (X : ModGL TwistTag.D4.tag L) :
    graphCentralizer TwistTag.D4.tag L (z * X * z⁻¹) =
      (graphCentralizer TwistTag.D4.tag L X).map (MulAut.conj z).toMonoidHom := by
  ext g
  simp only [graphCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, hgc⟩
    refine ⟨z⁻¹ * g * z, ⟨mul_mem (mul_mem (inv_mem hz) hg) hz, ?_⟩, by group⟩
    calc z⁻¹ * g * z * X = z⁻¹ * (g * (z * X * z⁻¹)) * z := by group
      _ = z⁻¹ * ((z * X * z⁻¹) * g) * z := by rw [hgc]
      _ = X * (z⁻¹ * g * z) := by group
  · rintro ⟨g', ⟨hg', hg'c⟩, rfl⟩
    refine ⟨mul_mem (mul_mem hz hg') (inv_mem hz), ?_⟩
    calc z * g' * z⁻¹ * (z * X * z⁻¹) = z * (g' * X) * z⁻¹ := by group
      _ = z * (X * g') * z⁻¹ := by rw [hg'c]
      _ = z * X * z⁻¹ * (z * g' * z⁻¹) := by group

theorem isPointIrreducible_secM (h2 : (2 : L) = 0) (μ : Lˣ) :
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (secM μ : Set (ModGL TwistTag.D4.tag L))) :=
  isPointIrreducible_iSup_wordCurves (secCurve h2 μ) (secH μ) (values_secCurve h2 μ)

theorem isPointIrreducible_conj_secM (h2 : (2 : L) = 0) (μ : Lˣ)
    (zw : List (Letter TwistTag.D4.tag × L)) :
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      ((secM μ).map (MulAut.conj (wordUnit TwistTag.D4.tag L zw)).toMonoidHom :
        Set (ModGL TwistTag.D4.tag L))) := by
  rw [secM, Subgroup.map_iSup]
  refine isPointIrreducible_iSup_wordCurves (fun o => secConjCurve (secCurve h2 μ o) zw)
    (fun o => (secH μ o).map (MulAut.conj (wordUnit TwistTag.D4.tag L zw)).toMonoidHom)
    fun o => ?_
  rw [values_secConjCurve, values_secCurve, Subgroup.coe_map]
  rfl

theorem twoTuple_eq_secTuple_inv {μ : Lˣ} (hμ3 : μ ^ 3 = 1) : twoTuple μ = (secTuple μ)⁻¹ := by
  have h1 : μ⁻¹ = μ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hμ3]
  funext i
  fin_cases i <;> simp [twoTuple, secTuple, h1] <;> rfl

theorem d4TrialityY0_mul_eq_conj (h2 : (2 : L) = 0) {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) :
    d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹ =
      wordUnit TwistTag.D4.tag L (secZWord μ) * (secElt μ)⁻¹ *
        (wordUnit TwistTag.D4.tag L (secZWord μ))⁻¹ := by
  have hμ3 := pow_three_of_sq_add hμ
  set P := diagramMap TwistTag.D4 L with hP
  set z := wordUnit TwistTag.D4.tag L (secZWord μ) with hz
  have hz' : z = yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 := wordUnit_secZWord μ
  have hAinv : (secElt μ)⁻¹ = torusElt TwistTag.D4.tag L 2 μ * P⁻¹ := by
    rw [torusElt_two_eq, twoTuple_eq_secTuple_inv hμ3, ← rootDiagUnit_inv, secElt, mul_inv_rev]
    have hc := diagramMap_commute_secTuple (L := L) μ
    rw [← hP] at hc
    calc P⁻¹ * (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ =
        (rootDiagUnit TwistTag.D4.tag (secTuple μ) * P)⁻¹ := by group
      _ = (P * rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ := by rw [hc]
      _ = (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ * P⁻¹ := by group
  have hzP : z * P⁻¹ = P⁻¹ * z := by
    obtain ⟨hx, -⟩ := diagramMap_inv_commute_two (L := L) (1 : L)
    obtain ⟨-, hy⟩ := diagramMap_inv_commute_two (L := L) (μ : L)
    rw [← hP] at hx hy
    rw [hz', mul_assoc, ← hx, ← mul_assoc, ← hy, mul_assoc]
  have hy0 := conj_torusElt_two_eq_y0 h2 μ hμ
  rw [← hz'] at hy0
  rw [hAinv, ← hy0]
  calc z * torusElt TwistTag.D4.tag L 2 μ * z⁻¹ * P⁻¹ =
      z * torusElt TwistTag.D4.tag L 2 μ * (z⁻¹ * P⁻¹) := by group
    _ = z * torusElt TwistTag.D4.tag L 2 μ * (P⁻¹ * z⁻¹) := by
        congr 1
        calc z⁻¹ * P⁻¹ = z⁻¹ * (P⁻¹ * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * P⁻¹) * z⁻¹ := by rw [hzP]
          _ = P⁻¹ * z⁻¹ := by group
    _ = z * (torusElt TwistTag.D4.tag L 2 μ * P⁻¹) * z⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  LangTwistedProof

theorem d4SecondCentIrred_holds :
    D4SecondCentIrred := by
  intro L _ _ _
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  obtain ⟨μ, hμ⟩ := exists_sq_add_self_add_one (L := L)
  have hzG : wordUnit TwistTag.D4.tag L (secZWord μ) ∈ adjointGroup TwistTag.D4.tag L := by
    rw [wordUnit_secZWord]
    exact mul_mem (yUnit_mem_adjointGroup 2 _) (xUnit_mem_adjointGroup 2 _)
  rw [d4TrialityY0_mul_eq_conj h2 hμ, graphCentralizer_conj hzG, graphCentralizer_inv,
    graphCentralizer_secElt_eq h2 hμ]
  exact isPointIrreducible_conj_secM h2 μ (secZWord μ)

theorem kF82D4LangCoset_holds :
    KF82D4LangCoset :=
  kF82D4LangCoset_of_secondCentIrred d4SecondCentIrred_holds

theorem kF82D4SecondCent_of_secondCentY0
    (hY0 : KF82D4SecondCentY0) :
    KF82D4SecondCent :=
  kF82D4SecondCent_of_y0 d4SecondCentIrred_holds hY0

end CFSG.RankThree.PartTwo.Sec8
