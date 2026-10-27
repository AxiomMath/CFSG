module

public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Reconstruction

public noncomputable section

namespace CFSG.UnitaryThreeRecognition.Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped LinearAlgebra.Projectivization Matrix

universe u

variable {K : Type u} [Field K]

instance instFiniteIsoPoint [Finite K] (J : HermitianForm 3 K) : Finite (IsoPoint J) :=
  Subtype.finite

instance instFiniteProjGenLinGroup [Finite K] : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
  inferInstanceAs (Finite (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)))

instance instFinitePSU [Finite K] (J : HermitianForm 3 K) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Subtype.finite

section Action

variable (J : HermitianForm 3 K)

theorem eq_toPermHom_of_apply
    (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (IsoPoint J))
    (hrho : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : IsoPoint J,
      ∀ M : J.specialSubgroup,
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) = (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : IsoPoint J) : ℙ K (Fin 3 → K)) =
            (Matrix.GeneralLinearGroup.toLin (M : GL (Fin 3) K)).toLinearEquiv •
              (z : ℙ K (Fin 3 → K))) :
    rho = MulAction.toPermHom (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) := by
  ext g z
  obtain ⟨M, hM, hMg⟩ := Subgroup.mem_map.mp g.property
  change ((rho g z : IsoPoint J) : ℙ K (Fin 3 → K)) = ((g • z : IsoPoint J) : ℙ K (Fin 3 → K))
  rw [hrho g z ⟨M, hM⟩ hMg, coe_smul_eq_toLin J g z ⟨M, hM⟩ hMg]

theorem comap_toPermHom_stabilizer (x : IsoPoint J) :
    (MulAction.stabilizer (Equiv.Perm (IsoPoint J)) x).comap
        (MulAction.toPermHom (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) x := by
  ext g
  rfl

end Action

section RankOne

variable (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem rootGroup_disjoint_stabilizer_pzero :
    Disjoint (rootGroup J hJ)
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pzero J hJ)) := by
  rw [Subgroup.disjoint_def]
  intro x hxR hxfix
  have hne : pzero J hJ ≠ pinf J hJ := (pinf_ne_pzero J hJ).symm
  obtain ⟨r0, _, huniq⟩ := rootGroup_regular J hJ (pzero J hJ) (pzero J hJ) hne hne
  have h1 := huniq ⟨x, hxR⟩ hxfix
  have h2 := huniq 1 (one_smul _ _)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem isInvolution_weyl : IsInvolution (weyl J hJ) :=
  ⟨weyl_ne_one J hJ, weyl_sq J hJ⟩

theorem rightConjugate_stabilizer_pinf_weyl :
    rightConjugate (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
        (weyl J hJ) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pzero J hJ) := by
  rw [rightConjugate_stabilizer, weyl_inv, weyl_smul_pinf]

theorem torusGroup_le_inf_rightConjugate_weyl :
    torusGroup J hJ ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
        rightConjugate (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
          (weyl J hJ) := by
  rw [rightConjugate_stabilizer_pinf_weyl]
  exact le_inf (torusGroup_le_stabilizer_pinf J hJ) (torusGroup_le_stabilizer_pzero J hJ)

theorem rootGroup_disjoint_inf_rightConjugate_weyl :
    Disjoint (rootGroup J hJ)
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
        rightConjugate (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
          (weyl J hJ)) := by
  rw [rightConjugate_stabilizer_pinf_weyl]
  exact (rootGroup_disjoint_stabilizer_pzero J hJ).mono_right inf_le_right

theorem weyl_smul_rankOneCoordinate (z : Coord J) (hz : z ≠ 1) :
    weyl J hJ • CFSG.BenderSuzuki.PFchapter4section1.rankOneCoordinate (rootGroup J hJ)
        (weyl J hJ) (pinf J hJ) (some (rootCoord J hJ z)) =
      CFSG.BenderSuzuki.PFchapter4section1.rankOneCoordinate (rootGroup J hJ) (weyl J hJ)
        (pinf J hJ) (some (rootCoord J hJ (weylCoordRight J z))) := by
  rw [CFSG.BenderSuzuki.PFchapter4section1.rankOneCoordinate_some,
    CFSG.BenderSuzuki.PFchapter4section1.rankOneCoordinate_some, coe_rootCoord, coe_rootCoord,
    weyl_smul_pinf]
  exact weyl_smul_root_inv_smul_pzero J hJ z hz

@[expose] def rootCoordOf (x : ProjectiveSpecialUnitaryMatrixGroup J) : Coord J := by
  classical
  exact if h : x ∈ rootGroup J hJ then (rootCoord J hJ).symm ⟨x, h⟩ else 1

theorem root_rootCoordOf {x : ProjectiveSpecialUnitaryMatrixGroup J} (hx : x ∈ rootGroup J hJ) :
    root J hJ (rootCoordOf J hJ x) = x := by
  classical
  rw [rootCoordOf, dite_eq_left hx]
  have h := congrArg Subtype.val ((rootCoord J hJ).apply_symm_apply ⟨x, hx⟩)
  rw [coe_rootCoord] at h
  exact h

theorem rootCoordOf_root (z : Coord J) : rootCoordOf J hJ (root J hJ z) = z :=
  root_injective J hJ (root_rootCoordOf J hJ (root_mem_rootGroup J hJ z))

theorem rootCoordOf_ne_one {x : ProjectiveSpecialUnitaryMatrixGroup J} (hx : x ∈ rootGroup J hJ)
    (hx1 : x ≠ 1) : rootCoordOf J hJ x ≠ 1 := by
  intro h
  apply hx1
  rw [← root_rootCoordOf J hJ hx, h, map_one]

@[expose] def bruhatLeft (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveSpecialUnitaryMatrixGroup J :=
  root J hJ (weylCoord J (rootCoordOf J hJ x))

@[expose] def bruhatRight (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveSpecialUnitaryMatrixGroup J :=
  root J hJ (weylCoordRight J (rootCoordOf J hJ x))

@[expose] def bruhatTorus (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveSpecialUnitaryMatrixGroup J := by
  classical
  exact if h : (rootCoordOf J hJ x).1.2 = 0 then 1 else torus J hJ (Units.mk0 _ h)

theorem bruhatLeft_root (z : Coord J) :
    bruhatLeft J hJ (root J hJ z) = root J hJ (weylCoord J z) := by
  rw [bruhatLeft, rootCoordOf_root]

theorem bruhatRight_root (z : Coord J) :
    bruhatRight J hJ (root J hJ z) = root J hJ (weylCoordRight J z) := by
  rw [bruhatRight, rootCoordOf_root]

theorem bruhatTorus_root (z : Coord J) (hz : z ≠ 1) :
    bruhatTorus J hJ (root J hJ z) = torus J hJ (Units.mk0 z.1.2 (coord_snd_ne_zero J hz)) := by
  unfold bruhatTorus
  split_ifs with h
  · rw [rootCoordOf_root] at h
    exact absurd h (coord_snd_ne_zero J hz)
  · congr 1
    ext
    simp [rootCoordOf_root]

theorem bruhatLeft_mem (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : x ∈ rootGroup J hJ)
    (hx1 : x ≠ 1) : bruhatLeft J hJ x ∈ rootGroup J hJ ∧ bruhatLeft J hJ x ≠ 1 := by
  refine ⟨root_mem_rootGroup J hJ _, ?_⟩
  rw [bruhatLeft, Ne, ← map_one (root J hJ), (root_injective J hJ).eq_iff]
  exact weylCoord_ne_one J (rootCoordOf_ne_one J hJ hx hx1)

theorem bruhatRight_mem (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : x ∈ rootGroup J hJ)
    (hx1 : x ≠ 1) : bruhatRight J hJ x ∈ rootGroup J hJ ∧ bruhatRight J hJ x ≠ 1 := by
  refine ⟨root_mem_rootGroup J hJ _, ?_⟩
  rw [bruhatRight, Ne, ← map_one (root J hJ), (root_injective J hJ).eq_iff]
  exact weylCoordRight_ne_one J (rootCoordOf_ne_one J hJ hx hx1)

theorem bruhatTorus_mem (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : x ∈ rootGroup J hJ)
    (hx1 : x ≠ 1) :
    bruhatTorus J hJ x ∈
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
        rightConjugate (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
          (weyl J hJ) := by
  classical
  apply torusGroup_le_inf_rightConjugate_weyl J hJ
  rw [bruhatTorus, dite_eq_right (coord_snd_ne_zero J (rootCoordOf_ne_one J hJ hx hx1))]
  exact torus_mem_torusGroup J hJ _

theorem weyl_mul_mul_weyl_eq_bruhat (x : ProjectiveSpecialUnitaryMatrixGroup J)
    (hx : x ∈ rootGroup J hJ) (hx1 : x ≠ 1) :
    weyl J hJ * x * weyl J hJ =
      bruhatLeft J hJ x * bruhatTorus J hJ x * weyl J hJ * bruhatRight J hJ x := by
  classical
  have hz := rootCoordOf_ne_one J hJ hx hx1
  conv_lhs => rw [← root_rootCoordOf J hJ hx]
  rw [weyl_mul_root_mul_weyl J hJ _ hz, bruhatLeft, bruhatRight, bruhatTorus,
    dite_eq_right (coord_snd_ne_zero J hz)]

end RankOne

section Huppert

variable [Finite K] (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
  (q : ℕ) (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q)

include hK in
theorem one_lt_of_card_eq_sq : 1 < q := by
  have h := Finite.one_lt_card (α := K)
  rw [hK] at h
  by_contra hq
  push Not at hq
  interval_cases q <;> simp at h

include hK hfix in
theorem huppert_explicit :
    Nat.card (IsoPoint J) = q ^ 3 + 1 ∧
      Function.Injective
        (MulAction.toPermHom (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J)) ∧
      Nat.card (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) =
        q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ≤
        Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      rootGroup J hJ ⊓ torusGroup J hJ = ⊥ ∧
      rootGroup J hJ ⊔ torusGroup J hJ =
        MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ∧
      IsCyclic (torusGroup J hJ) ∧
      Nat.card (rootGroup J hJ) = q ^ 3 ∧
      commutator (rootGroup J hJ) = Subgroup.center (rootGroup J hJ) ∧
      Nat.card (commutator (rootGroup J hJ)) = q ∧
      Nat.card (torusGroup J hJ) = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
      (∀ a b c d : IsoPoint J, a ≠ b → c ≠ d →
        ∃ g : ProjectiveSpecialUnitaryMatrixGroup J, g • a = c ∧ g • b = d) ∧
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
        (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
  obtain ⟨hcard, rho, pinf', hinj, hnat, hUcard, ⟨R, H, hRU, _hHU, hUnorm, hRH, hRsupH, hHcyc,
      hRcard, hRcomm, hRcommcard, hHcard, _hreg, ⟨coordR, hcoordR⟩, hHcoord, hHsurj⟩,
      htwo, hGcard, -⟩ := huppert_II_10_12 J q hK hfix hJ
  have hrho := eq_toPermHom_of_apply J rho hnat
  subst hrho
  have hcoordR_eq (z : Coord J) :
      ((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) = root J hJ z := by
    obtain ⟨M, hM, hMproj⟩ := hcoordR z
    have hMroot : M = hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) K) i j =
        (hermitianUnipotentGL J z : Matrix (Fin 3) (Fin 3) K) i j
      rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    rw [hMproj, hMroot]
    rfl
  have hR : R = rootGroup J hJ := by
    apply le_antisymm
    · intro g hg
      obtain ⟨z, hz⟩ := coordR.surjective ⟨g, hg⟩
      exact ⟨z, by rw [← hcoordR_eq z, hz]⟩
    · rintro _ ⟨z, rfl⟩
      rw [← hcoordR_eq z]
      exact (coordR z).2
  subst hR
  have hH : H = torusGroup J hJ := by
    apply le_antisymm
    · intro g hg
      obtain ⟨k, M, hM, hproj⟩ := hHcoord ⟨g, hg⟩
      refine ⟨k, ?_⟩
      have hMtorus : M = hermitianTorusGL J k := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (M : Matrix (Fin 3) (Fin 3) K) i j =
          (hermitianTorusGL J k : Matrix (Fin 3) (Fin 3) K) i j
        rw [hM, hermitianTorusGL_val, hermitianTorusMatrix_eq]
      apply Subtype.ext
      change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = _
      rw [← hMtorus, ← hproj]
    · rintro _ ⟨k, rfl⟩
      obtain ⟨h, M, hM, hproj⟩ := hHsurj k
      have hMtorus : M = hermitianTorusGL J k := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (M : Matrix (Fin 3) (Fin 3) K) i j =
          (hermitianTorusGL J k : Matrix (Fin 3) (Fin 3) K) i j
        rw [hM, hermitianTorusGL_val, hermitianTorusMatrix_eq]
      have hh : (h : ProjectiveSpecialUnitaryMatrixGroup J) = torus J hJ k := by
        apply Subtype.ext
        rw [hproj, hMtorus]
        rfl
      rw [← hh]
      exact h.2
  subst hH
  have hq : 1 < q := one_lt_of_card_eq_sq q hK
  have hpinf : pinf' = pinf J hJ := by
    by_contra hne
    have hRtriv : ∀ r : rootGroup J hJ, r = 1 := by
      intro r
      obtain ⟨r0, _, huniq⟩ := rootGroup_regular J hJ pinf' pinf' hne hne
      have h1 := huniq r (hRU r.2)
      have h2 := huniq 1 (one_smul _ _)
      exact h1.trans h2.symm
    have hcard1 : Nat.card (rootGroup J hJ) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hRtriv a).trans (hRtriv b).symm⟩, ⟨1⟩⟩
    rw [hcard1] at hRcard
    have : 1 < q ^ 3 := one_lt_pow₀ hq (by decide)
    omega
  subst hpinf
  refine ⟨hcard, hinj, hUcard, hUnorm, hRH, hRsupH, hHcyc, hRcard, hRcomm, hRcommcard, hHcard,
    fun a b c d hab hcd => htwo a b c d hab hcd, ?_⟩
  rw [hGcard, Nat.gcd_comm]

include hJ hK hfix

theorem faithfulSMul_isoPoint :
    FaithfulSMul (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
  ⟨fun hgh => (huppert_explicit J hJ q hK hfix).2.1 (Equiv.ext fun x => hgh x)⟩

theorem card_isoPoint : Nat.card (IsoPoint J) = q ^ 3 + 1 :=
  (huppert_explicit J hJ q hK hfix).1

theorem isMultiplyPretransitive_two :
    MulAction.IsMultiplyPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  exact (huppert_explicit J hJ q hK hfix).2.2.2.2.2.2.2.2.2.2.2.1 a b c d hab hcd

theorem card_psu :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 :=
  (huppert_explicit J hJ q hK hfix).2.2.2.2.2.2.2.2.2.2.2.2

theorem card_stabilizer_pinf :
    Nat.card (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) =
      q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 :=
  (huppert_explicit J hJ q hK hfix).2.2.1

theorem stabilizer_pinf_le_normalizer_rootGroup :
    MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ≤
      Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  (huppert_explicit J hJ q hK hfix).2.2.2.1

theorem conj_mem_rootGroup_of_smul_pinf {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g • pinf J hJ = pinf J hJ) {x : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : x ∈ rootGroup J hJ) : g * x * g⁻¹ ∈ rootGroup J hJ :=
  (Subgroup.mem_normalizer_iff.mp (stabilizer_pinf_le_normalizer_rootGroup J hJ q hK hfix hg) x).mp
    hx

theorem rootGroup_sup_torusGroup :
    rootGroup J hJ ⊔ torusGroup J hJ =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) :=
  (huppert_explicit J hJ q hK hfix).2.2.2.2.2.1

theorem isCyclic_torusGroup : IsCyclic (torusGroup J hJ) :=
  (huppert_explicit J hJ q hK hfix).2.2.2.2.2.2.1

theorem card_rootGroup : Nat.card (rootGroup J hJ) = q ^ 3 :=
  (huppert_explicit J hJ q hK hfix).2.2.2.2.2.2.2.1

theorem card_torusGroup : Nat.card (torusGroup J hJ) = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 :=
  (huppert_explicit J hJ q hK hfix).2.2.2.2.2.2.2.2.2.2.1

theorem stabilizer_pinf_inf_stabilizer_pzero :
    MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
        MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pzero J hJ) =
      torusGroup J hJ := by
  apply le_antisymm
  · rintro g ⟨hginf, hg0⟩
    have hgmem : g ∈ ((rootGroup J hJ ⊔ torusGroup J hJ :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
      rw [rootGroup_sup_torusGroup J hJ q hK hfix]
      exact hginf
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (torusGroup_le_normalizer_rootGroup J hJ)] at hgmem
    obtain ⟨r, hr, h, hh, rfl⟩ := hgmem
    have hrfix : r ∈ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pzero J hJ) := by
      have hhfix := torusGroup_le_stabilizer_pzero J hJ hh
      have := (MulAction.stabilizer _ (pzero J hJ)).mul_mem hg0
        ((MulAction.stabilizer _ (pzero J hJ)).inv_mem hhfix)
      simpa using this
    have hr1 : r = 1 :=
      Subgroup.disjoint_def.mp (rootGroup_disjoint_stabilizer_pzero J hJ) hr hrfix
    simpa [hr1] using hh
  · intro g hg
    exact ⟨torusGroup_le_stabilizer_pinf J hJ hg, torusGroup_le_stabilizer_pzero J hJ hg⟩

theorem stabilizer_inf_rightConjugate_weyl :
    MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
        rightConjugate (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
          (weyl J hJ) =
      torusGroup J hJ := by
  rw [rightConjugate_stabilizer_pinf_weyl, stabilizer_pinf_inf_stabilizer_pzero J hJ q hK hfix]

theorem rootGroup_subgroupOf_stabilizer_normal :
    ((rootGroup J hJ).subgroupOf
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (stabilizer_pinf_le_normalizer_rootGroup J hJ q hK hfix)

theorem rootGroup_sup_inf_rightConjugate_weyl :
    rootGroup J hJ ⊔
        (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
          rightConjugate (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
            (weyl J hJ)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  rw [stabilizer_inf_rightConjugate_weyl J hJ q hK hfix, rootGroup_sup_torusGroup J hJ q hK hfix]

theorem exists_rankOneCoordinateEquiv_model :
    ∃ c : Option (rootGroup J hJ) ≃ IsoPoint J, ∀ z : Option (rootGroup J hJ),
      c z = CFSG.BenderSuzuki.PFchapter4section1.rankOneCoordinate (rootGroup J hJ) (weyl J hJ)
        (pinf J hJ) z :=
  CFSG.BenderSuzuki.PFchapter4section1.exists_rankOneCoordinateEquiv
    (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) (rootGroup J hJ) _
    (weyl J hJ) (pinf J hJ) (isMultiplyPretransitive_two J hJ q hK hfix) rfl
    (isInvolution_weyl J hJ) (weyl_not_mem_stabilizer J hJ) rfl
    (rootGroup_subgroupOf_stabilizer_normal J hJ q hK hfix)
    (rootGroup_disjoint_inf_rightConjugate_weyl J hJ)
    (rootGroup_sup_inf_rightConjugate_weyl J hJ q hK hfix)

omit hJ in
theorem isSimpleGroup_psu (hq : 2 < q) : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  huppert_II_10_13 J q hq hK hfix

theorem closure_rootGroup_weyl_eq_top (hq : 2 < q) :
    Subgroup.closure ((rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪
      {weyl J hJ}) = ⊤ := by
  have hle := CFSG.BenderSuzuki.PFchapter4section1.rankOneNormalClosure_le_generated
    (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) (rootGroup J hJ)
    _ (weyl J hJ) (pinf J hJ) (isMultiplyPretransitive_two J hJ q hK hfix) rfl
    (isInvolution_weyl J hJ) (weyl_not_mem_stabilizer J hJ) rfl
    (rootGroup_subgroupOf_stabilizer_normal J hJ q hK hfix)
    (rootGroup_disjoint_inf_rightConjugate_weyl J hJ)
    (rootGroup_sup_inf_rightConjugate_weyl J hJ q hK hfix)
  rw [CFSG.BenderSuzuki.PFchapter4section1.iSup_rightConjugate_eq_normalClosure] at hle
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    isSimpleGroup_psu J q hK hfix hq
  have hR_ne_bot : rootGroup J hJ ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, card_rootGroup J hJ q hK hfix]
    exact one_lt_pow₀ (by omega) (by decide)
  have htop : Subgroup.normalClosure
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊤ := by
    rcases (Subgroup.normalClosure_normal
        (s := (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))).eq_bot_or_eq_top with
      hbot | htop
    · exfalso
      apply hR_ne_bot
      rw [eq_bot_iff]
      intro r hr
      have hr' := Subgroup.le_normalClosure hr
      rw [hbot] at hr'
      exact hr'
    · exact htop
  exact top_unique (htop ▸ hle)

end Huppert

end CFSG.UnitaryThreeRecognition.Model
