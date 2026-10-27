module

public import CFSG.LocalAnalysis.StandardType.GGTorusLangCoordinates
public import CFSG.LocalAnalysis.StandardType.GGTorusE6Relative
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.RankThree.PartOne.KE.CTLang

public noncomputable section

namespace CFSG.StandardType.E6RelativeLang

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable {p : ℕ} {E : Subgroup (adjointGroup .E6 K)}
variable (F : ExcFrame .E6 K p E)

noncomputable def frobHom : AlgebraicClosure K →+* AlgebraicClosure K :=
  Classical.choose F.frob

theorem frobHom_eq : ∀ c, frobHom F c = c ^ Nat.card K :=
  (Classical.choose_spec F.frob).1

theorem frobHom_apply : ∀ g, F.D.Φ g = Units.map (entrywiseHom (frobHom F)) g :=
  (Classical.choose_spec F.frob).2

@[expose] def coordTuple
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
  fun i => (a (e6IndexToF4 i) : (AlgebraicClosure K)ˣ)

@[expose] def coordMap :
    (Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      (Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) where
  toFun := coordTuple
  map_one' := by
    funext i
    rfl
  map_mul' := by
    intro a b
    funext i
    rfl

@[simp] theorem coordMap_apply
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K))
    (i : Fin Tag.E6.rank) :
    coordMap (K := K) a i = coordTuple a i := rfl

theorem coordTuple_pow_card_add_one
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) (i : Fin Tag.E6.rank) :
    coordTuple a i ^ (Nat.card K + 1) = 1 := by
  exact (mem_rootsOfUnity _ _).mp (a (e6IndexToF4 i)).2

theorem coordMap_pow_card_add_one
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    a ^ (Nat.card K + 1) = 1 := by
  funext i
  apply Subtype.ext
  simpa using (mem_rootsOfUnity _ _).mp (a i).2

theorem coordMap_injective : Function.Injective (coordMap (K := K)) := by
  intro a b hab
  funext j
  have h := congrFun hab (f4IndexRep (show Fin Tag.F4.rank from j))
  rw [coordMap_apply, coordMap_apply] at h
  simp only [coordTuple] at h
  have hidx : e6IndexToF4 (f4IndexRep (show Fin Tag.F4.rank from j)) = j := by
    simpa using e6IndexToF4_f4IndexRep (show Fin Tag.F4.rank from j)
  rw [hidx] at h
  exact Subtype.ext h

theorem e6IndexToF4_ggKGEp_phi (i : Fin Tag.E6.rank) :
    e6IndexToF4 (ggKGEp_phi i) = e6IndexToF4 i := by
  fin_cases i <;> rfl

theorem ggKGEp_phi_eq_rhoE6 : ggKGEp_phi = rhoE6 := by
  ext i
  fin_cases i <;> rfl

theorem coordTuple_phi
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) (i : Fin Tag.E6.rank) :
    coordTuple a (ggKGEp_phi i) = coordTuple a i := by
  simp only [coordTuple, e6IndexToF4_ggKGEp_phi]

@[expose] def fullTorus : Subgroup (adjointGroup .E6 K) :=
  F.D.torus.comap
    ((MulAut.conj F.D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E6 K).subtype))

theorem mem_fullTorus {x : adjointGroup .E6 K} :
    x ∈ fullTorus F ↔
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) *
        F.D.g0 ∈ F.D.torus := by
  rfl

theorem rootDiagUnit_mem_torus_of_mTorsion_fixed
    (hlong : ExcIsLongest .E6 F.w) {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hbpow : ∀ i, b i ^ (Nat.card K + 1) = 1)
    (hbfix : ∀ i, b (ggKGEp_phi i) = b i) :
    rootDiagUnit .E6 b ∈ F.D.torus := by
  change rootDiagUnit .E6 b ∈ twistedTorusOf F.D.n F.D.Φ
  rw [mem_twistedTorusOf]
  refine ⟨rootDiagUnit_mem_torusGroup b, ?_⟩
  have hΦb : F.D.Φ (rootDiagUnit .E6 b) =
      rootDiagUnit .E6 (fun i => Units.map (frobHom F).toMonoidHom (b i)) := by
    rw [frobHom_apply F]
    exact Units.ext (entrywise_rootDiag (frobHom F) b)
  have hbq : ∀ i, Units.map (frobHom F).toMonoidHom (b i) = (b i)⁻¹ := by
    intro i
    have hq : Nat.card K = (Nat.card K + 1) - 1 := by omega
    have hbq' : b i ^ Nat.card K = (b i)⁻¹ := by
      rw [hq]
      apply eq_inv_of_mul_eq_one_left
      have h := hbpow i
      rw [show Nat.card K + 1 = (Nat.card K + 1 - 1) + 1 by omega, pow_succ] at h
      exact h
    apply Units.ext
    rw [Units.coe_map, Units.val_inv_eq_inv_val]
    change frobHom F (b i : AlgebraicClosure K) = ((b i : AlgebraicClosure K)⁻¹)
    rw [frobHom_eq F]
    simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using
      congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hbq'
  have hwt : weylTuple F.w (fun i => Units.map (frobHom F).toMonoidHom (b i)) = b := by
    rw [ggKGEp_eq_w0_of_longest hlong, ggKGEp_weylTuple_w0_phi]
    funext i
    rw [hbq (ggKGEp_phi i), inv_inv, hbfix i]
  rw [hΦb, F.n_eq, canonicalRep_conj_rootDiagUnit, hwt]

theorem coordTuple_mem_torus
    (hlong : ExcIsLongest .E6 F.w)
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    rootDiagUnit .E6 (coordTuple a) ∈ F.D.torus :=
  rootDiagUnit_mem_torus_of_mTorsion_fixed F hlong
    (fun i => coordTuple_pow_card_add_one a i) (coordTuple_phi a)

theorem hrat_E6 :
    ∀ x : ModGL .E6 (AlgebraicClosure K),
      x ∈ adjointGroup .E6 (AlgebraicClosure K) →
      Units.map (entrywiseHom (frobHom F)) x = x →
      x ^ (Nat.card K + 1) = 1 →
        x ∈ (adjointGroup .E6 K).map
          (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  intro x hxC hxF hxq
  exact frobenius_fixed_pow_card_add_one_mem_baseChange
    (K := K) (L := AlgebraicClosure K) (Fr := frobHom F) (frobHom_eq F) hxC hxF hxq

@[expose] def phi (hlong : ExcIsLongest .E6 F.w) :
    (Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      adjointGroup .E6 K :=
  ScalarLangTorus.coordHomOfFixed F.D (frobHom F) (frobHom_apply F)
    (Nat.succ_pos _) (coordMap (K := K)) (coordTuple_mem_torus F hlong)
    (coordMap_pow_card_add_one (K := K)) (hrat_E6 F)

theorem phi_apply_baseChange (hlong : ExcIsLongest .E6 F.w)
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (phi F hlong a : ModGL .E6 K) =
      F.D.g0 * rootDiagUnit .E6 (coordTuple a) * F.D.g0⁻¹ := by
  exact ScalarLangTorus.baseChange_coordHomOfFixed F.D (frobHom F) (frobHom_apply F)
    (Nat.succ_pos _) (coordMap (K := K)) (coordTuple_mem_torus F hlong)
    (coordMap_pow_card_add_one (K := K)) (hrat_E6 F) a

theorem phi_injective (hlong : ExcIsLongest .E6 F.w) :
    Function.Injective (phi F hlong) := by
  exact ScalarLangTorus.coordHomOfFixed_injective F.D (frobHom F) (frobHom_apply F)
    (Nat.succ_pos _) (coordMap (K := K)) (coordTuple_mem_torus F hlong)
    (coordMap_pow_card_add_one (K := K)) (hrat_E6 F) (coordMap_injective (K := K))

theorem phi_pow_card_add_one (hlong : ExcIsLongest .E6 F.w)
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    phi F hlong a ^ (Nat.card K + 1) = 1 := by
  calc
    phi F hlong a ^ (Nat.card K + 1) = phi F hlong (a ^ (Nat.card K + 1)) :=
      (map_pow (phi F hlong) a (Nat.card K + 1)).symm
    _ = phi F hlong 1 := by rw [coordMap_pow_card_add_one]
    _ = 1 := map_one (phi F hlong)

theorem phi_mem_fullTorus (hlong : ExcIsLongest .E6 F.w)
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    phi F hlong a ∈ fullTorus F := by
  rw [mem_fullTorus, phi_apply_baseChange]
  rw [show F.D.g0⁻¹ * (F.D.g0 * rootDiagUnit .E6 (coordTuple a) * F.D.g0⁻¹) * F.D.g0 =
      rootDiagUnit .E6 (coordTuple a) by group]
  exact coordTuple_mem_torus F hlong a

theorem rootDiagUnit_phi_fixed_of_mem_torus
    (hlong : ExcIsLongest .E6 F.w) {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hbpow : ∀ i, b i ^ (Nat.card K + 1) = 1)
    (hT : rootDiagUnit .E6 b ∈ F.D.torus) :
    ∀ i, b (ggKGEp_phi i) = b i := by
  have hΦb : F.D.Φ (rootDiagUnit .E6 b) =
      rootDiagUnit .E6 (fun i => Units.map (frobHom F).toMonoidHom (b i)) := by
    rw [frobHom_apply F]
    exact Units.ext (entrywise_rootDiag (frobHom F) b)
  have hmem : F.D.n * F.D.Φ (rootDiagUnit .E6 b) * F.D.n⁻¹ = rootDiagUnit .E6 b :=
    (mem_twistedTorusOf.1 hT).2
  rw [hΦb, F.n_eq, canonicalRep_conj_rootDiagUnit] at hmem
  have hwt : weylTuple F.w (fun i => Units.map (frobHom F).toMonoidHom (b i)) = b :=
    rootDiagUnit_injective hmem
  rw [ggKGEp_eq_w0_of_longest hlong, ggKGEp_weylTuple_w0_phi] at hwt
  have hbq : ∀ i, Units.map (frobHom F).toMonoidHom (b i) = (b i)⁻¹ := by
    intro i
    have hq : Nat.card K = (Nat.card K + 1) - 1 := by omega
    have hbq' : b i ^ Nat.card K = (b i)⁻¹ := by
      rw [hq]
      apply eq_inv_of_mul_eq_one_left
      have h := hbpow i
      rw [show Nat.card K + 1 = (Nat.card K + 1 - 1) + 1 by omega, pow_succ] at h
      exact h
    apply Units.ext
    rw [Units.coe_map, Units.val_inv_eq_inv_val]
    change frobHom F (b i : AlgebraicClosure K) = ((b i : AlgebraicClosure K)⁻¹)
    rw [frobHom_eq F]
    simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using
      congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hbq'
  intro i
  have hi := congrFun hwt i
  rw [hbq (ggKGEp_phi i), inv_inv] at hi
  exact hi

theorem b_eq_coordTuple_of_mTorsion
    (hlong : ExcIsLongest .E6 F.w) {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hbpow : ∀ i, b i ^ (Nat.card K + 1) = 1)
    (hT : rootDiagUnit .E6 b ∈ F.D.torus) :
    ∃ a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K),
      coordTuple a = b := by
  have hbfix : ∀ i, b (ggKGEp_phi i) = b i :=
    rootDiagUnit_phi_fixed_of_mem_torus F hlong hbpow hT
  have hbrep : ∀ i, b (f4IndexRep (e6IndexToF4 i)) = b i := by
    intro i
    rcases f4IndexRep_e6IndexToF4 i with h | h
    · rw [h]
    · rw [h, ← ggKGEp_phi_eq_rhoE6]
      exact hbfix i
  let a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) := fun j =>
    ⟨b (f4IndexRep j), (mem_rootsOfUnity _ _).mpr (hbpow (f4IndexRep j))⟩
  refine ⟨a, ?_⟩
  funext i
  change (a (e6IndexToF4 i) : (AlgebraicClosure K)ˣ) = b i
  change b (f4IndexRep (e6IndexToF4 i)) = b i
  exact hbrep i

theorem mem_fullTorus_pow_iff_mem_phi_range
    (hlong : ExcIsLongest .E6 F.w) {x : adjointGroup .E6 K} :
    x ∈ fullTorus F ∧ x ^ (Nat.card K + 1) = 1 ↔
      x ∈ (phi F hlong).range := by
  constructor
  · rintro ⟨hxS, hxm⟩
    have hyT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL .E6 K) * F.D.g0 ∈ F.D.torus := (mem_fullTorus F).mp hxS
    have hyG : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL .E6 K) * F.D.g0 ∈ torusGroup .E6 (AlgebraicClosure K) :=
      (mem_twistedTorusOf.1 hyT).1
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyG
    have hxsub : ((x : ModGL .E6 K) ^ (Nat.card K + 1)) = 1 :=
      congrArg (fun y : adjointGroup .E6 K => (y : ModGL .E6 K)) hxm
    have hxm' : (baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL .E6 K)) ^ (Nat.card K + 1) = 1 := by
      rw [← map_pow, hxsub, map_one]
    have hyPow : (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL .E6 K) * F.D.g0) ^ (Nat.card K + 1) = 1 := by
      have hconj : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL .E6 K) * F.D.g0 =
          (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL .E6 K) * (F.D.g0⁻¹)⁻¹) := by group
      rw [hconj, conj_pow, hxm', mul_one, mul_inv_cancel]
    have hbpow : ∀ i, b i ^ (Nat.card K + 1) = 1 := by
      have h1 : (rootDiagUnit .E6 b) ^ (Nat.card K + 1) = 1 := by
        rw [← hb, hyPow]
      have hb' : b ^ (Nat.card K + 1) = 1 :=
        rootDiagUnit_injective (by rw [← rootDiagUnit_pow, h1, rootDiagUnit_one])
      intro i
      simpa using congrFun hb' i
    obtain ⟨a, ha⟩ := b_eq_coordTuple_of_mTorsion F hlong hbpow (hb ▸ hyT)
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [phi_apply_baseChange, ha]
    calc
      F.D.g0 * rootDiagUnit .E6 b * F.D.g0⁻¹ =
          F.D.g0 * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL .E6 K) * F.D.g0) * F.D.g0⁻¹ := by rw [hb]
      _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) := by group
  · rintro ⟨a, rfl⟩
    exact ⟨phi_mem_fullTorus F hlong a, phi_pow_card_add_one F hlong a⟩

theorem mem_E_iff_pow_p_mem_phi_range
    (hlong : ExcIsLongest .E6 F.w) (hpq : p ∣ Nat.card K + 1)
    {x : adjointGroup .E6 K} :
    x ∈ E ↔ x ^ p = 1 ∧ x ∈ (phi F hlong).range := by
  rw [F.mem_iff]
  constructor
  · rintro ⟨hxp, hxS⟩
    refine ⟨hxp, ?_⟩
    rw [← mem_fullTorus_pow_iff_mem_phi_range F hlong]
    refine ⟨hxS, ?_⟩
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hxp, one_pow]
  · rintro ⟨hxp, hxrange⟩
    have hxS : x ∈ fullTorus F :=
      (mem_fullTorus_pow_iff_mem_phi_range F hlong).mpr hxrange |>.1
    exact ⟨hxp, hxS⟩

theorem fullTorus_commute_phi
    (hlong : ExcIsLongest .E6 F.w)
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K))
    {t : adjointGroup .E6 K} (ht : t ∈ fullTorus F) :
    Commute (phi F hlong a) t := by
  have htT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (t : ModGL .E6 K) * F.D.g0 ∈ F.D.torus := (mem_fullTorus F).mp ht
  have htG : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (t : ModGL .E6 K) * F.D.g0 ∈ torusGroup .E6 (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 htT).1
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htG
  have htbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL .E6 K) =
      F.D.g0 * rootDiagUnit .E6 b * F.D.g0⁻¹ := by
    calc
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL .E6 K) =
          F.D.g0 * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (t : ModGL .E6 K) * F.D.g0) * F.D.g0⁻¹ := by group
      _ = F.D.g0 * rootDiagUnit .E6 b * F.D.g0⁻¹ := by rw [hb]
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  change baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((phi F hlong a : ModGL .E6 K) * (t : ModGL .E6 K)) =
    baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((t : ModGL .E6 K) * (phi F hlong a : ModGL .E6 K))
  rw [map_mul, map_mul, phi_apply_baseChange, htbase]
  calc
    (F.D.g0 * rootDiagUnit .E6 (coordTuple a) * F.D.g0⁻¹) *
        (F.D.g0 * rootDiagUnit .E6 b * F.D.g0⁻¹) =
      F.D.g0 * (rootDiagUnit .E6 (coordTuple a) * rootDiagUnit .E6 b) * F.D.g0⁻¹ := by group
    _ = F.D.g0 * (rootDiagUnit .E6 b * rootDiagUnit .E6 (coordTuple a)) * F.D.g0⁻¹ := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    _ = (F.D.g0 * rootDiagUnit .E6 b * F.D.g0⁻¹) *
        (F.D.g0 * rootDiagUnit .E6 (coordTuple a) * F.D.g0⁻¹) := by group

theorem centralizer_le_fullTorus
    (hlong : ExcIsLongest .E6 F.w) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1)
    {x : adjointGroup .E6 K}
    (hx : x ∈ Subgroup.centralizer (E : Set (adjointGroup .E6 K))) :
    x ∈ fullTorus F := by
  have hp3 : 3 ≤ p := by omega
  have hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨
      (p ∣ Nat.card K + 1 ∧ ExcIsLongest .E6 F.w) := Or.inr ⟨hpq, hlong⟩
  have h := (ggKGExc_centralizer_eq (τ := .E6) (K := K) (p := p) (E := E)
    (Or.inl rfl) hp hp3 (fun _ => hp5) F hw x).mp hx
  exact (mem_fullTorus F).mpr h

theorem conj_phi_of_baseChange_orbitReflection
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} {E : Subgroup (adjointGroup .E6 K)} (F : ExcFrame .E6 K p E)
    (hlong : ExcIsLongest .E6 F.w) (j : Fin 4) {x : adjointGroup .E6 K}
    (hx : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) =
      F.D.g0 * canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection (f4FoldedIndex j)) * F.D.g0⁻¹)
    (a : Fin 4 → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    x * phi F hlong a * x⁻¹ =
      phi F hlong a * (phi F hlong (corTuple CartanMatrix.F₄.transpose j (a j)))⁻¹ := by
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  change baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : ModGL .E6 K) * (phi F hlong a : ModGL .E6 K) * (x : ModGL .E6 K)⁻¹) =
    baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((phi F hlong a : ModGL .E6 K) *
        (phi F hlong (corTuple CartanMatrix.F₄.transpose j (a j)) : ModGL .E6 K)⁻¹)
  rw [map_mul, map_mul, map_inv, map_mul, map_inv, hx,
    phi_apply_baseChange, phi_apply_baseChange]
  have hcor : rootDiagUnit .E6 (coordTuple
      (corTuple CartanMatrix.F₄.transpose j (a j))) =
      rootDiagUnit .E6 (fun i => (a j : (AlgebraicClosure K)ˣ) ^
        CartanMatrix.F₄ (e6IndexToF4 i) j) := by
    rfl
  have hconj : canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection (f4FoldedIndex j)) *
      rootDiagUnit .E6 (coordTuple a) *
      (canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection (f4FoldedIndex j)))⁻¹ =
      rootDiagUnit .E6 (coordTuple a) *
        (rootDiagUnit .E6 (coordTuple
          (corTuple CartanMatrix.F₄.transpose j (a j))))⁻¹ := by
    erw [canonicalRep_orbitReflection (t := TwistTag.E6)
      (K := AlgebraicClosure K) (f4FoldedIndex j)]
    rw [hcor]
    exact E6RelativeTorus.orbitWord_conj_rootDiagUnit j
      (fun i => (a i : (AlgebraicClosure K)ˣ))
  calc
    _ = F.D.g0 * (canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
          (TwistTag.E6.orbitReflection (f4FoldedIndex j)) *
        rootDiagUnit .E6 (coordTuple a) *
        (canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
          (TwistTag.E6.orbitReflection (f4FoldedIndex j)))⁻¹) * F.D.g0⁻¹ := by group
    _ = F.D.g0 * (rootDiagUnit .E6 (coordTuple a) *
        (rootDiagUnit .E6 (coordTuple
          (corTuple CartanMatrix.F₄.transpose j (a j))))⁻¹) * F.D.g0⁻¹ := by rw [hconj]
    _ = _ := by group

end CFSG.StandardType.E6RelativeLang
