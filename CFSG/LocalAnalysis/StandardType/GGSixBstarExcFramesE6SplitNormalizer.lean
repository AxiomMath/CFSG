module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.LieType.Chevalley.WeylRoots
import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality

namespace CFSG.StandardType.ExcFrames

private def foldE6 (v : Fin Tag.E6.rank → ℤ) : Fin 4 → ℤ :=
  ![v ⟨0, by decide⟩ + v ⟨5, by decide⟩, v ⟨1, by decide⟩, v ⟨2, by decide⟩ + v ⟨4, by decide⟩,
    v ⟨3, by decide⟩]

private def foldE6L (l : List ℤ) : List ℤ :=
  [l.getD 0 0 + l.getD 5 0, l.getD 1 0, l.getD 2 0 + l.getD 4 0, l.getD 3 0]

private def simpleE6L (j : Fin Tag.E6.rank) : List ℤ := List.ofFn (Pi.single j (1 : ℤ))

private theorem foldE6L_check :
    ∀ l ∈ Tag.E6.artifactRoots, ∃ k : Fin 4, (foldE6L l).getD k 0 ≠ 0 ∧
      -4 ≤ (foldE6L l).getD k 0 ∧ (foldE6L l).getD k 0 ≤ 4 := by
  decide +kernel

private theorem foldE6L_neg_check :
    ∀ l ∈ Tag.E6.artifactRoots, l.sum < 0 → ∀ j : Fin Tag.E6.rank, ∃ k : Fin 4,
      1 ≤ (foldE6L (simpleE6L j)).getD k 0 - (foldE6L l).getD k 0 ∧
        (foldE6L (simpleE6L j)).getD k 0 - (foldE6L l).getD k 0 ≤ 4 := by
  decide +kernel

private theorem foldE6L_ofFn (v : Fin Tag.E6.rank → ℤ) (k : Fin 4) :
    (foldE6L (List.ofFn v)).getD k 0 = foldE6 v k := by
  fin_cases k <;> rfl

private def splitGenE6 {L : Type} [Field L] (ζ : Lˣ) : Fin 4 → Fin Tag.E6.rank → Lˣ :=
  ![Pi.mulSingle ⟨0, by decide⟩ ζ * Pi.mulSingle ⟨5, by decide⟩ ζ, Pi.mulSingle ⟨1, by decide⟩ ζ,
    Pi.mulSingle ⟨2, by decide⟩ ζ * Pi.mulSingle ⟨4, by decide⟩ ζ, Pi.mulSingle ⟨3, by decide⟩ ζ]

private theorem rootChar_mul_E6 {L : Type} [Field L] (a b : Fin Tag.E6.rank → Lˣ)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem rootChar_splitGenE6 {L : Type} [Field L] (ζ : Lˣ) (k : Fin 4)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (splitGenE6 ζ k) v = ζ ^ foldE6 v k := by
  fin_cases k <;>
    simp [splitGenE6, foldE6, rootChar_mul_E6,
      CFSG.RankThree.Chevalley.rootChar_mulSingle_eq_zpow, zpow_add]

private theorem familyKernel_splitGenE6_eq_empty {L : Type}
    [Field L] {p : ℕ}
    (hp5 : 5 ≤ p) {ζ : Lˣ} (hζ : orderOf ζ = p) : familyKernel (splitGenE6 ζ) = ∅ := by
  ext α
  simp only [familyKernel, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
    not_forall]
  intro hα
  obtain ⟨k, hk0, hkl, hku⟩ := foldE6L_check _ (isRoot_iff_mem_artifactRoots.1 hα)
  rw [foldE6L_ofFn] at hk0 hkl hku
  refine ⟨k, fun h => hk0 ?_⟩
  rw [rootChar_splitGenE6, ← orderOf_dvd_iff_zpow_eq_one, hζ] at h
  refine Int.eq_zero_of_abs_lt_dvd h ?_
  have : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  rw [abs_lt]
  constructor <;> omega

private theorem eq_one_of_mem_familyStabilizer_splitGenE6
    {L : Type} [Field L] {p : ℕ} (hp5 : 5 ≤ p) {ζ : Lˣ}
    (hζ : orderOf ζ = p) {w : WeylGroup Tag.E6} (hw : w ∈ familyStabilizer (splitGenE6 ζ)) :
    w = 1 := by
  refine eq_one_of_forall_nonneg fun j => ?_
  have hroot := IsRoot.smul (isRoot_single Tag.E6 j) w
  rcases IsRoot.height_pos_or_neg hroot with hpos | hneg
  · exact fun i => (IsRoot.height_pos_iff hroot).1 hpos i
  · exfalso
    have hsum : (List.ofFn (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))).sum < 0 := by
      rw [List.sum_ofFn]
      exact hneg
    obtain ⟨k, hk1, hk4⟩ :=
      foldE6L_neg_check _ (isRoot_iff_mem_artifactRoots.1 hroot) hsum j
    rw [foldE6L_ofFn, simpleE6L, foldE6L_ofFn] at hk1 hk4
    have h1 := hw k (Pi.single j 1)
    rw [rootChar_splitGenE6, rootChar_splitGenE6] at h1
    have h2 : ζ ^ (foldE6 (Pi.single j 1) k -
        foldE6 (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k) = 1 := by
      rw [zpow_sub, h1, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hζ] at h2
    have h3 := Int.eq_zero_of_abs_lt_dvd h2 (by
      have : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      rw [abs_lt]
      constructor <;> omega)
    omega

@[expose] def e6SplitTorsion (L : Type) [Field L] (p : ℕ) : Set (ModGL .E6 L) :=
  {x | ∃ c : Fin Tag.E6.rank → Lˣ, (∀ i, c i ^ p = 1) ∧ c ⟨0, by decide⟩ = c ⟨5, by decide⟩ ∧
    c ⟨2, by decide⟩ = c ⟨4, by decide⟩ ∧ x = rootDiagUnit .E6 c}

private theorem rootDiagUnit_splitGenE6_mem {L : Type} [Field L] {p : ℕ} {ζ : Lˣ}
    (hζ : orderOf ζ = p) (k : Fin 4) :
    rootDiagUnit .E6 (splitGenE6 ζ k) ∈ e6SplitTorsion L p := by
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  refine ⟨splitGenE6 ζ k, fun i => ?_, ?_, ?_, rfl⟩
  · have hg : splitGenE6 ζ k ^ p = 1 := by
      fin_cases k <;> simp [splitGenE6, mul_pow, ← Pi.mulSingle_pow, hζp]
    simpa using congrFun hg i
  · fin_cases k <;> simp [splitGenE6, Pi.mulSingle_apply]
  · fin_cases k <;> simp [splitGenE6, Pi.mulSingle_apply]

theorem mem_torusGroup_of_commute_e6SplitTorsion
    {L : Type} [Field L] {p : ℕ} (hp5 : 5 ≤ p) {ζ : Lˣ} (hζ : orderOf ζ = p) {z : ModGL .E6 L}
    (hzC : z ∈ adjointGroup .E6 L) (hz : ∀ x ∈ e6SplitTorsion L p, z * x = x * z) :
    z ∈ torusGroup .E6 L := by
  have hzcent : z ∈ familyCentralizer Tag.E6 L (splitGenE6 ζ) := by
    rw [mem_familyCentralizer]
    refine ⟨hzC, fun k => ?_⟩
    rw [← hz _ (rootDiagUnit_splitGenE6_mem hζ k)]
    group
  obtain ⟨w, hw, m, hm, hzm⟩ := familyCentralizer_le_mul Tag.E6 L (splitGenE6 ζ) hzcent
  have hw1 : w = 1 := eq_one_of_mem_familyStabilizer_splitGenE6 hp5 hζ hw
  have hmT : m ∈ torusGroup Tag.E6 L := by
    rw [familyGroup, familyKernel_splitGenE6_eq_empty hp5 hζ] at hm
    have hbot : rootSpan Tag.E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm
  rw [hzm, hw1, canonicalRep_one, mul_one]
  exact hmT

theorem mem_monomialSubgroup_of_conj_e6SplitTorsion
    {L : Type} [Field L] {p : ℕ} (hp5 : 5 ≤ p) {ζ : Lˣ} (hζ : orderOf ζ = p) {z : ModGL .E6 L}
    (hzC : z ∈ adjointGroup .E6 L)
    (hz : ∀ x ∈ e6SplitTorsion L p, z * x * z⁻¹ ∈ e6SplitTorsion L p) :
    z ∈ monomialSubgroup .E6 L := by
  have hVD : ∀ x ∈ e6SplitTorsion L p, ∃ b : Fin Tag.E6.rank → Lˣ, x = rootDiagUnit .E6 b := by
    rintro x ⟨c, -, -, -, rfl⟩
    exact ⟨c, rfl⟩
  obtain ⟨w, hwconj⟩ :=
    CFSG.StandardType.NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := Tag.E6) (k := L) hVD hzC hz
  set n : ModGL .E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hn
  have hyC : n⁻¹ * z ∈ adjointGroup .E6 L :=
    mul_mem (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) L w)) hzC
  have hycent : ∀ x ∈ e6SplitTorsion L p, n⁻¹ * z * x = x * (n⁻¹ * z) := by
    intro x hx
    have h := hwconj x hx
    calc n⁻¹ * z * x = n⁻¹ * (z * x * z⁻¹) * z := by group
      _ = n⁻¹ * (n * x * n⁻¹) * z := by rw [h]
      _ = x * (n⁻¹ * z) := by group
  have hyT := mem_torusGroup_of_commute_e6SplitTorsion hp5 hζ hyC hycent
  have hz_eq : z = n * (n⁻¹ * z) := by group
  rw [hz_eq]
  exact mul_mem (Subgroup.mem_sup_right (canonicalRep_mem_closure (coxeterSystem Tag.E6) L w))
    (Subgroup.mem_sup_left hyT)

theorem mem_relWeylTwist_of_normalizes_e6SplitTorsion
    {L : Type} [Field L] {p : ℕ} (hp5 : 5 ≤ p)
    {ζ : Lˣ} (hζ : orderOf ζ = p) {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ x ∈ e6SplitTorsion L p,
      canonicalRep (coxeterSystem Tag.E6) L v * x *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ ∈ e6SplitTorsion L p) :
    v ∈ relWeylTwist TwistTag.E6 := by
  let P : ModGL Tag.E6 L := diagramMap TwistTag.E6 L
  let n : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L v
  have hfix : ∀ x ∈ e6SplitTorsion L p, P * x * P⁻¹ = x := by
    rintro x ⟨a, -, h05, h24, rfl⟩
    have ha : (fun i : Fin Tag.E6.rank => a (TwistTag.E6.perm.symm i)) = a := by
      funext i
      fin_cases i
      · exact h05.symm
      · rfl
      · exact h24.symm
      · rfl
      · exact h24
      · exact h05
    have hPd : P * rootDiagUnit Tag.E6 a =
        rootDiagUnit Tag.E6 (fun i => a (TwistTag.E6.perm.symm i)) * P :=
      diagramMap_mul_rootDiagUnit (t := TwistTag.E6) a
    rw [hPd, ha, mul_assoc, mul_inv_cancel, mul_one]
  have htw : P * n * P⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) L (weylTwist TwistTag.E6 v) := by
    have hh := twistHom_canonicalRep TwistTag.E6 L (RingHom.id L) v
    rw [twistHom_apply] at hh
    have hi : Units.map (entrywiseHom (RingHom.id L)) n = n := by
      ext1
      simp only [Units.coe_map]
      exact CFSG.LieType.Chevalley.entrywise_id _
    change P * Units.map (entrywiseHom (RingHom.id L)) n * P⁻¹ = _ at hh
    rwa [hi] at hh
  let k : ModGL Tag.E6 L := n⁻¹ * (P * n * P⁻¹)
  have hkC : k ∈ adjointGroup Tag.E6 L := by
    dsimp only [k]
    rw [htw]
    exact mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ _ v))
      (canonicalRep_mem_adjointGroup _ _ _)
  have hkc : ∀ x ∈ e6SplitTorsion L p, k * x = x * k := by
    intro x hx
    have hxP : P * x * P⁻¹ = x := hfix x hx
    have hnP := hfix (n * x * n⁻¹) (hv x hx)
    have hconj : k * x * k⁻¹ = x := by
      dsimp only [k]
      calc
        _ = n⁻¹ * P * (n * (P⁻¹ * x * P) * n⁻¹) * P⁻¹ * n := by group
        _ = n⁻¹ * (P * (n * x * n⁻¹) * P⁻¹) * n := by
          have hi : P⁻¹ * x * P = x := by
            calc _ = P⁻¹ * (P * x * P⁻¹) * P := by rw [hxP]
              _ = x := by group
          rw [hi]
          group
        _ = x := by rw [hnP]; group
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hkT := mem_torusGroup_of_commute_e6SplitTorsion hp5 hζ hkC hkc
  have hkW : MapsRootLines k (v⁻¹ * weylTwist TwistTag.E6 v) := by
    dsimp only [k]
    rw [htw]
    exact (mapsRootLines_canonicalRep v).inv.mul
      (mapsRootLines_canonicalRep (weylTwist TwistTag.E6 v))
  have h1 : v⁻¹ * weylTwist TwistTag.E6 v = 1 :=
    hkW.unique (mapsRootLines_of_mem_torusGroup hkT)
  rw [mem_relWeylTwist]
  exact (inv_mul_eq_one.mp h1).symm

theorem exists_foldedWeyl_of_normalizes_e6SplitTorsion
    {L : Type} [Field L] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {z : ModGL Tag.E6 L}
    (hzC : z ∈ adjointGroup Tag.E6 L)
    (hz : ∀ x ∈ e6SplitTorsion L p, z * x * z⁻¹ ∈ e6SplitTorsion L p) :
    ∃ u : WeylGroup Tag.F4, ∀ s : Fin Tag.F4.rank → ZMod p,
      z * frameDiag (τ := Tag.E6) ζ hζ (twE6SplitTheta p s) * z⁻¹ =
        frameDiag (τ := Tag.E6) ζ hζ
          (twE6SplitTheta p (TableBExc.torusAct Tag.F4 p u s)) := by
  have hVD : ∀ x ∈ e6SplitTorsion L p,
      ∃ b : Fin Tag.E6.rank → Lˣ, x = rootDiagUnit Tag.E6 b := by
    rintro x ⟨b, -, -, -, rfl⟩
    exact ⟨b, rfl⟩
  obtain ⟨w, hconj⟩ :=
    CFSG.StandardType.NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := Tag.E6) hVD hzC hz
  have hw : w ∈ relWeylTwist TwistTag.E6 :=
    mem_relWeylTwist_of_normalizes_e6SplitTorsion hp5 hζo fun x hx => by
      rw [← hconj x hx]
      exact hz x hx
  let u : WeylGroup Tag.F4 := foldedWeylEquiv TwistTag.E6 ⟨w, hw⟩
  refine ⟨u, fun s => ?_⟩
  have hd : frameDiag (τ := Tag.E6) ζ hζ (twE6SplitTheta p s) ∈
      e6SplitTorsion L p := by
    obtain ⟨b, hb, h05, h24, hframe⟩ := frameDiag_twE6SplitTheta_eq_rootDiagUnit hζ s
    exact ⟨b, hb, h05, h24, hframe⟩
  have hfold : TableBExc.torusAct Tag.E6 p w (twE6SplitTheta p s) =
      twE6SplitTheta p (TableBExc.torusAct Tag.F4 p u s) :=
    torusAct_twE6SplitTheta ⟨w, hw⟩ s
  exact (hconj _ hd).trans
    ((canonicalRep_conj_frameDiag (τ := Tag.E6) ζ hζ w (twE6SplitTheta p s)).trans
      (congrArg (frameDiag (τ := Tag.E6) ζ hζ) hfold))

end CFSG.StandardType.ExcFrames
