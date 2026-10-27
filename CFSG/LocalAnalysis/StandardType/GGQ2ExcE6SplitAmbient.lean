module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitTorus
import CFSG.LieType.Chevalley.FoldedWeylIdentification
import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
import CFSG.LieType.Chevalley.WeylNormalizerQuotient
import CFSG.LieType.Steinberg.BruhatTwist
import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeNormalizer
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitWeyl

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
  CFSG.StandardType.ExcFrames.E6QPlusThree

noncomputable section

namespace E6SplitDatum

private def e6SimpleIdx : Fin 6 → Fin Tag.E6.rank :=
  Fin.cast (by decide : 6 = Tag.E6.rank)

private def e6RootIdx : Fin 24 → ExcRaw.Root 1 :=
  Fin.cast (by decide : 24 = ExcRaw.nroots 1)

private def e6TagIdx : Fin 6 → Fin TwistTag.E6.tag.rank :=
  Fin.cast (by decide : 6 = TwistTag.E6.tag.rank)

private def e6Perm : Equiv.Perm (Fin Tag.E6.rank) :=
  TwistTag.E6.perm

private def orbitRefl (a : Fin 4) : WeylGroup .E6 :=
  TwistTag.E6.orbitReflection a

private def toRelE6 (w : WeylGroup .E6) : WeylGroup TwistTag.E6.tag :=
  w

private def e6OrbitRootIndex : Fin 4 → ExcRaw.Root 1 :=
  ![e6RootIdx 0, e6RootIdx 8, e6RootIdx 1, e6RootIdx 12]

private theorem orbitWord_e6_zero :
    TwistTag.E6.orbitWord (0 : Fin 4) = [e6TagIdx 0, e6TagIdx 5] := by
  decide

private theorem orbitWord_e6_one :
    TwistTag.E6.orbitWord (1 : Fin 4) = [e6TagIdx 2, e6TagIdx 4] := by
  decide

private theorem orbitWord_e6_two :
    TwistTag.E6.orbitWord (2 : Fin 4) = [e6TagIdx 3] := by
  decide

private theorem orbitWord_e6_three :
    TwistTag.E6.orbitWord (3 : Fin 4) = [e6TagIdx 1] := by
  decide

private theorem orbitReflection_e6_zero_tag :
    TwistTag.E6.orbitReflection (0 : Fin 4) =
      (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 0) *
        (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 5) := by
  change (coxeterSystem TwistTag.E6.tag).wordProd (TwistTag.E6.orbitWord (0 : Fin 4)) =
    (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 0) *
      (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 5)
  rw [orbitWord_e6_zero, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_singleton]

private theorem orbitReflection_e6_one_tag :
    TwistTag.E6.orbitReflection (1 : Fin 4) =
      (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 2) *
        (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 4) := by
  change (coxeterSystem TwistTag.E6.tag).wordProd (TwistTag.E6.orbitWord (1 : Fin 4)) =
    (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 2) *
      (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 4)
  rw [orbitWord_e6_one, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_singleton]

private theorem orbitReflection_e6_two_tag :
    TwistTag.E6.orbitReflection (2 : Fin 4) =
      (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 3) := by
  change (coxeterSystem TwistTag.E6.tag).wordProd (TwistTag.E6.orbitWord (2 : Fin 4)) =
    (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 3)
  rw [orbitWord_e6_two, CoxeterSystem.wordProd_singleton]

private theorem orbitReflection_e6_three_tag :
    TwistTag.E6.orbitReflection (3 : Fin 4) =
      (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 1) := by
  change (coxeterSystem TwistTag.E6.tag).wordProd (TwistTag.E6.orbitWord (3 : Fin 4)) =
    (coxeterSystem TwistTag.E6.tag).simple (e6TagIdx 1)
  rw [orbitWord_e6_three, CoxeterSystem.wordProd_singleton]

private theorem orbitReflection_e6_zero :
    TwistTag.E6.orbitReflection (0 : Fin 4) =
      (coxeterSystem .E6).simple (e6SimpleIdx 0) * (coxeterSystem .E6).simple (e6SimpleIdx 5) :=
  orbitReflection_e6_zero_tag

private theorem orbitReflection_e6_one :
    TwistTag.E6.orbitReflection (1 : Fin 4) =
      (coxeterSystem .E6).simple (e6SimpleIdx 2) * (coxeterSystem .E6).simple (e6SimpleIdx 4) :=
  orbitReflection_e6_one_tag

private theorem orbitReflection_e6_two :
    TwistTag.E6.orbitReflection (2 : Fin 4) = (coxeterSystem .E6).simple (e6SimpleIdx 3) :=
  orbitReflection_e6_two_tag

private theorem orbitReflection_e6_three :
    TwistTag.E6.orbitReflection (3 : Fin 4) = (coxeterSystem .E6).simple (e6SimpleIdx 1) :=
  orbitReflection_e6_three_tag

private theorem simple_e6_zero_five :
    (coxeterSystem .E6).simple (e6SimpleIdx 0) * (coxeterSystem .E6).simple (e6SimpleIdx 5) =
      (coxeterSystem .E6).simple (e6SimpleIdx 5) * (coxeterSystem .E6).simple (e6SimpleIdx 0) :=
  CFSG.LieType.Steinberg.simple_mul_simple_comm (hA := isFiniteType_cartan .E6)
    (i := e6SimpleIdx 0) (j := e6SimpleIdx 5) (by decide)

private theorem simple_e6_two_four :
    (coxeterSystem .E6).simple (e6SimpleIdx 2) * (coxeterSystem .E6).simple (e6SimpleIdx 4) =
      (coxeterSystem .E6).simple (e6SimpleIdx 4) * (coxeterSystem .E6).simple (e6SimpleIdx 2) :=
  CFSG.LieType.Steinberg.simple_mul_simple_comm (hA := isFiniteType_cartan .E6)
    (i := e6SimpleIdx 2) (j := e6SimpleIdx 4) (by decide)

private theorem permLattice_e6Perm_single (i : Fin Tag.E6.rank) :
    permLattice (τ := .E6) e6Perm (Pi.single i 1) = Pi.single (e6Perm i) 1 :=
  permLattice_single (τ := .E6) e6Perm i

private theorem e6Perm_five : e6Perm (e6SimpleIdx 5) = e6SimpleIdx 0 := by
  decide +kernel

private theorem e6Perm_four : e6Perm (e6SimpleIdx 4) = e6SimpleIdx 2 := by
  decide +kernel

section Refl


private theorem rootReflection_single_e6 (i : Fin Tag.E6.rank) :
    rootReflection (Pi.single i 1) = (coxeterSystem .E6).simple i := by
  rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]


private theorem diagramMap_mul_rootDiagUnit_e6 {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) :
    diagramMap TwistTag.E6 L * rootDiagUnit TwistTag.E6.tag a =
      rootDiagUnit TwistTag.E6.tag (fun i => a (e6Perm.symm i)) * diagramMap TwistTag.E6 L :=
  diagramMap_mul_rootDiagUnit (t := TwistTag.E6) a

private theorem e6SplitRefl_e6_zero :
    e6SplitRefl (e6RootIdx 0) =
      (coxeterSystem .E6).simple (e6SimpleIdx 5) * (coxeterSystem .E6).simple (e6SimpleIdx 0) := by
  have hroot : e6SplitRoot (e6RootIdx 0) = Pi.single (e6SimpleIdx 5) 1 := by
    decide +kernel
  have hperm' : permLattice (τ := .E6) e6Perm (e6SplitRoot (e6RootIdx 0)) =
      Pi.single (e6SimpleIdx 0) 1 := by
    rw [hroot, permLattice_e6Perm_single, e6Perm_five]
  have hperm : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot (e6RootIdx 0)) =
      Pi.single (e6SimpleIdx 0) 1 := hperm'
  rw [e6SplitRefl, if_neg (by decide), hperm, hroot]
  rw [rootReflection_single_e6, rootReflection_single_e6]

private theorem e6SplitRefl_e6_one :
    e6SplitRefl (e6RootIdx 1) = (coxeterSystem .E6).simple (e6SimpleIdx 3) := by
  have hroot : e6SplitRoot (e6RootIdx 1) = Pi.single (e6SimpleIdx 3) 1 := by
    decide +kernel
  rw [e6SplitRefl, if_pos (by decide), hroot, rootReflection_single_e6]

private theorem e6SplitRefl_e6_eight :
    e6SplitRefl (e6RootIdx 8) =
      (coxeterSystem .E6).simple (e6SimpleIdx 4) * (coxeterSystem .E6).simple (e6SimpleIdx 2) := by
  have hroot : e6SplitRoot (e6RootIdx 8) = Pi.single (e6SimpleIdx 4) 1 := by
    decide +kernel
  have hperm' : permLattice (τ := .E6) e6Perm (e6SplitRoot (e6RootIdx 8)) =
      Pi.single (e6SimpleIdx 2) 1 := by
    rw [hroot, permLattice_e6Perm_single, e6Perm_four]
  have hperm : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot (e6RootIdx 8)) =
      Pi.single (e6SimpleIdx 2) 1 := hperm'
  rw [e6SplitRefl, if_neg (by decide), hperm, hroot]
  rw [rootReflection_single_e6, rootReflection_single_e6]

private theorem e6SplitRefl_e6_twelve :
    e6SplitRefl (e6RootIdx 12) = (coxeterSystem .E6).simple (e6SimpleIdx 1) := by
  have hroot : e6SplitRoot (e6RootIdx 12) = -Pi.single (e6SimpleIdx 1) 1 := by
    decide +kernel
  rw [e6SplitRefl, if_pos (by decide), hroot,
    rootReflection_neg (isRoot_single .E6 (e6SimpleIdx 1))]
  rw [rootReflection_single_e6]

private theorem orbitRefl_eq_e6SplitRefl (a : Fin 4) :
    orbitRefl a = e6SplitRefl (e6OrbitRootIndex a) := by
  fin_cases a
  · exact orbitReflection_e6_zero.trans (simple_e6_zero_five.trans e6SplitRefl_e6_zero.symm)
  · exact orbitReflection_e6_one.trans (simple_e6_two_four.trans e6SplitRefl_e6_eight.symm)
  · exact orbitReflection_e6_two.trans e6SplitRefl_e6_one.symm
  · exact orbitReflection_e6_three.trans e6SplitRefl_e6_twelve.symm

end Refl

section Weyl


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)}

private theorem orbitRefl_mul_self (a : Fin 4) : orbitRefl a * orbitRefl a = 1 :=
  TwistTag.E6.orbitReflection_mul_self a

private theorem exists_map_of_mem_closure (d : E6SplitDatum S T₀) (hS : E6SplitLangTwo S)
    {w : WeylGroup .E6}
    (hw : w ∈ Subgroup.closure (Set.range orbitRefl)) :
    ∃ M ∈ ExcRaw.ambientNormalizer 1,
      ∀ (b : Fin Tag.E6.rank → Lˣ) (hb : rootDiagUnit .E6 b ∈ T₀),
        ∃ h : rootDiagUnit .E6 (weylTuple w b) ∈ T₀,
          d.coord (Additive.ofMul ⟨rootDiagUnit .E6 (weylTuple w b), h⟩) =
            M (d.coord (Additive.ofMul ⟨rootDiagUnit .E6 b, hb⟩)) := by
  let P : WeylGroup .E6 → Prop := fun w =>
    ∃ M ∈ ExcRaw.ambientNormalizer 1,
      ∀ (b : Fin Tag.E6.rank → Lˣ) (hb : rootDiagUnit .E6 b ∈ T₀),
        ∃ h : rootDiagUnit .E6 (weylTuple w b) ∈ T₀,
          d.coord (Additive.ofMul ⟨rootDiagUnit .E6 (weylTuple w b), h⟩) =
            M (d.coord (Additive.ofMul ⟨rootDiagUnit .E6 b, hb⟩))
  have hone : P 1 := by
    refine ⟨1, one_mem _, fun b hb => ?_⟩
    have hmem : rootDiagUnit .E6 (weylTuple (1 : WeylGroup .E6) b) ∈ T₀ := by
      rw [weylTuple_one]; exact hb
    refine ⟨hmem, ?_⟩
    have h1 : (⟨rootDiagUnit .E6 (weylTuple (1 : WeylGroup .E6) b), hmem⟩ : ↥T₀) =
        ⟨rootDiagUnit .E6 b, hb⟩ := by
      refine Subtype.ext ?_
      exact congrArg (rootDiagUnit .E6) (weylTuple_one b)
    rw [h1]
    rfl
  have hgen : ∀ a : Fin 4, P (orbitRefl a) := by
    intro a
    have hji := orbitRefl_eq_e6SplitRefl a
    refine ⟨ExcRaw.reflection 1 (e6OrbitRootIndex a),
      Subgroup.subset_closure (Set.mem_range_self (e6OrbitRootIndex a)), fun b hb => ?_⟩
    obtain ⟨h, he⟩ := d.weylTuple_e6SplitRefl_mem hS (e6OrbitRootIndex a) hb
    have hmem : rootDiagUnit .E6 (weylTuple (orbitRefl a) b) ∈ T₀ := by
      rw [hji]; exact h
    refine ⟨hmem, ?_⟩
    have h1 : (⟨rootDiagUnit .E6 (weylTuple (orbitRefl a) b), hmem⟩ : ↥T₀) =
        ⟨rootDiagUnit .E6 (weylTuple (e6SplitRefl (e6OrbitRootIndex a)) b), h⟩ := by
      refine Subtype.ext ?_
      exact congrArg (rootDiagUnit .E6) (congrArg (fun w' => weylTuple w' b) hji)
    rw [h1]
    exact he
  have hmul : ∀ a ∈ Set.range orbitRefl, ∀ g, P g → P (a * g) := by
    rintro a ⟨a₀, rfl⟩ g ⟨Mg, hMg, hMgp⟩
    obtain ⟨Ma, hMa, hMap⟩ := hgen a₀
    refine ⟨Ma * Mg, mul_mem hMa hMg, fun b hb => ?_⟩
    obtain ⟨hg_mem, hg_eq⟩ := hMgp b hb
    obtain ⟨ha_mem, ha_eq⟩ := hMap (weylTuple g b) hg_mem
    have hmem : rootDiagUnit .E6 (weylTuple (orbitRefl a₀ * g) b) ∈ T₀ := by
      rw [← weylTuple_weylTuple]; exact ha_mem
    refine ⟨hmem, ?_⟩
    have h1 : (⟨rootDiagUnit .E6 (weylTuple (orbitRefl a₀ * g) b), hmem⟩ : ↥T₀) =
        ⟨rootDiagUnit .E6 (weylTuple (orbitRefl a₀) (weylTuple g b)), ha_mem⟩ := by
      refine Subtype.ext ?_
      exact congrArg (rootDiagUnit .E6) (weylTuple_weylTuple _ g b).symm
    rw [h1]
    calc d.coord (Additive.ofMul ⟨rootDiagUnit .E6
          (weylTuple (orbitRefl a₀) (weylTuple g b)), ha_mem⟩)
        = Ma (d.coord (Additive.ofMul ⟨rootDiagUnit .E6 (weylTuple g b), hg_mem⟩)) := ha_eq
      _ = Ma (Mg (d.coord (Additive.ofMul ⟨rootDiagUnit .E6 b, hb⟩))) := by rw [hg_eq]
      _ = (Ma * Mg) (d.coord (Additive.ofMul ⟨rootDiagUnit .E6 b, hb⟩)) := rfl
  have hmain : ∀ w, w ∈ Subgroup.closure (Set.range orbitRefl) → P w := by
    intro w hw
    induction hw using Subgroup.closure_induction_left with
    | one => exact hone
    | mul_left a ha g hg ih => exact hmul a ha g ih
    | inv_mul_cancel a ha g hg ih =>
      obtain ⟨a₀, rfl⟩ := ha
      rw [show (orbitRefl a₀)⁻¹ = orbitRefl a₀ from
        inv_eq_of_mul_eq_one_right (orbitRefl_mul_self a₀)]
      exact hmul _ ⟨a₀, rfl⟩ g ih
  exact hmain w hw

end Weyl

section Main


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀)

theorem map_ggAutomizer_le_ambientNormalizer (hS : E6SplitLangTwo S) :
    (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) ≤ ExcRaw.ambientNormalizer 1 := by
  rw [ggAutomizer, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨z, hzΓ, hznorm, hzact⟩ := hφ
  have hΓC : ∀ y ∈ S.Γ, y ∈ adjointGroup .E6 L := by
    intro y hy
    exact ((S.D.mem_model).1 (S.Γ_le_model hy)).1
  have hzC : z ∈ adjointGroup .E6 L := hΓC z hzΓ
  have hzV : ∀ x ∈ T₀, z * x * z⁻¹ ∈ T₀ := by
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp hznorm x).mp hx
  have hVD : ∀ x ∈ (T₀ : Set (ModGL .E6 L)), ∃ b, x = rootDiagUnit .E6 b := by
    intro x hx
    exact d.exists_rootDiagUnit ⟨x, hx⟩
  obtain ⟨w, hwconj⟩ :=
    CFSG.StandardType.NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := .E6) (k := L) hVD hzC hzV
  let P : ModGL .E6 L := diagramMap TwistTag.E6 L
  let n : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L w
  have hT : T₀ = (e6ThreeDiag d.ζ d.ζ_pow_three).range :=
    (d.eq_fullThreeTorus hS).trans
      (fullThreeTorus_eq_range_e6ThreeDiag hS d.orderOf_ζ d.ζ_pow_three)
  have hfix : ∀ x ∈ T₀, P * x * P⁻¹ = x := by
    intro x hx
    have hxf : x ∈ fullThreeTorus S := by
      rwa [d.eq_fullThreeTorus hS] at hx
    obtain ⟨a, ha⟩ := d.exists_rootDiagUnit ⟨x, hx⟩
    have ha' : x = rootDiagUnit .E6 a := ha
    have h1 := (rootDiagUnit_mem_fullThreeTorus_iff hS a).1 (ha ▸ hxf)
    have hσ : (fun i : Fin Tag.E6.rank => a (e6Perm.symm i)) = a := by
      funext i
      have h1j : a (e6Perm (e6Perm.symm i)) = a (e6Perm.symm i) := h1.2 (e6Perm.symm i)
      rw [Equiv.apply_symm_apply e6Perm i] at h1j
      exact h1j.symm
    have hPd : P * rootDiagUnit .E6 a =
        rootDiagUnit .E6 (fun i => a (e6Perm.symm i)) * P :=
      diagramMap_mul_rootDiagUnit_e6 a
    rw [ha', hPd, hσ, mul_assoc, mul_inv_cancel, mul_one]
  let wt : WeylGroup .E6 := weylTwist TwistTag.E6 w
  have htw : P * n * P⁻¹ = canonicalRep (coxeterSystem .E6) L wt := by
    have hh := twistHom_canonicalRep TwistTag.E6 L (RingHom.id L) w
    rw [twistHom_apply] at hh
    have hi : Units.map (entrywiseHom (RingHom.id L)) n = n := by
      ext1
      simp only [Units.coe_map]
      exact CFSG.LieType.Chevalley.entrywise_id _
    change P * Units.map (entrywiseHom (RingHom.id L)) n * P⁻¹ = _ at hh
    rw [hi] at hh
    exact hh
  let k : ModGL .E6 L := n⁻¹ * (P * n * P⁻¹)
  have hkC : k ∈ adjointGroup .E6 L := by
    dsimp only [k]
    rw [htw]
    exact mul_mem (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem .E6) L w))
      (canonicalRep_mem_adjointGroup (coxeterSystem .E6) L wt)
  have hkc : ∀ x ∈ T₀, k * x = x * k := by
    intro x hx
    have hxP : P * x * P⁻¹ = x := hfix x hx
    have hnx : n * x * n⁻¹ ∈ T₀ := by
      have h' : z * x * z⁻¹ = n * x * n⁻¹ := hwconj x hx
      rw [← h']
      exact hzV x hx
    have hnP := hfix (n * x * n⁻¹) hnx
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
  have hkT : k ∈ torusGroup .E6 L := by
    refine mem_torusGroup_of_commute_e6ThreeDiag d.orderOf_ζ d.ζ_pow_three hkC (fun s => ?_)
    have hmem : e6ThreeDiag d.ζ d.ζ_pow_three s ∈ T₀ :=
      hT.ge (Set.mem_range_self s)
    exact hkc _ hmem
  have hkW : MapsRootLines k (w⁻¹ * wt) := by
    dsimp only [k]
    rw [htw]
    exact (mapsRootLines_canonicalRep w).inv.mul (mapsRootLines_canonicalRep wt)
  have h1 : w⁻¹ * wt = 1 :=
    hkW.unique (mapsRootLines_of_mem_torusGroup hkT)
  have hwrel : toRelE6 w ∈ relWeylTwist TwistTag.E6 := by
    rw [mem_relWeylTwist]
    exact (inv_mul_eq_one.mp h1).symm
  have hwclos : toRelE6 w ∈ Subgroup.closure (Set.range (TwistTag.E6.orbitReflection)) := by
    rw [← relWeylTwist_eq_closure]
    exact hwrel
  have hwclos' : w ∈ Subgroup.closure (Set.range orbitRefl) := hwclos
  obtain ⟨M, hM, hMp⟩ := exists_map_of_mem_closure d hS hwclos'
  have hEq : ggLin (p := 3) d.coord φ = M := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨a, rfl⟩ := d.coord.surjective v
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective a
    obtain ⟨c, hc⟩ := d.exists_rootDiagUnit b
    have hb : rootDiagUnit .E6 c ∈ T₀ := hc ▸ b.2
    have hb_eq : b = ⟨rootDiagUnit .E6 c, hb⟩ := Subtype.ext hc
    obtain ⟨h, he⟩ := hMp c hb
    have hφb : φ ⟨rootDiagUnit .E6 c, hb⟩ = ⟨rootDiagUnit .E6 (weylTuple w c), h⟩ := by
      refine Subtype.ext ?_
      calc ((φ ⟨rootDiagUnit .E6 c, hb⟩ : ↥T₀) : ModGL .E6 L)
          = z * rootDiagUnit .E6 c * z⁻¹ := hzact _
        _ = rootDiagUnit .E6 (weylTuple w c) := by
            rw [hwconj (rootDiagUnit .E6 c) hb]
            exact canonicalRep_conj_rootDiagUnit w c
    rw [ggLin_apply_ofMul, hb_eq, hφb]
    exact he
  rw [hEq]
  exact hM

end Main

end E6SplitDatum

section Ambient


theorem e6SplitCoreAmbient_holds : E6SplitCoreAmbient :=
  fun _ hS _ d => le_antisymm (d.map_ggAutomizer_le_ambientNormalizer hS)
    (d.ambientNormalizer_le_map_ggAutomizer hS)

end Ambient

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
