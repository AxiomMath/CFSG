module

public import CFSG.RankThree.Lattice.SteinbergBTE6OrderFiveGraph
public import CFSG.RankThree.SteinbergR3ESU4PointwiseRigidity
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveMats
public import CFSG.RankThree.PartOne.KE.E6FourFamily

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index charVal dualMatrix chain134 support134
  IsNegativeTransition e6Rho graph_dual_fixed_iff
  E6_large_prime_character_stabilizers_and_A3_graph_action)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (exists_conj_map_inv_transpose_of_root_permuting unitarySet
  invTransposeHom coe_invTransposeHom)
open scoped Matrix MatrixGroups Pointwise

section Orientation

theorem zmod5_sq_add_one_eq_zero (s : ZMod 5) (h : s ^ 2 + 1 = 0) : s = 2 ∨ s = 3 := by
  revert s
  decide

theorem e6_graph_orientation {p : ℕ} [Fact p.Prime] (hp5 : p = 5 ∨ 7 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0)
    {z : Fin Tag.E6.rank → ZMod p} (hz0 : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) e6F4U).mulVec z = r • z) {v : WeylGroup Tag.E6}
    (hv : (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134) {w : WeylGroup Tag.E6}
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    IsNegativeTransition (fun x => v • (w • permLattice e6Rho (v⁻¹ • x))) chain134 chain134 := by
  rcases hp5 with rfl | hp7
  · obtain ⟨-, -, -, -, h⟩ := E6_order_five_graph_stabilizers_reverse_A3_orientation
      (zmod5_sq_add_one_eq_zero r hr) hz0 hzr
    exact (h w (graph_dual_fixed_iff.2 hb)).2.2 v hv
  · exact (E6_large_prime_character_stabilizers_and_A3_graph_action (by omega) z).2.2 v hv w
      (graph_dual_fixed_iff.2 hb) |>.2.2

end Orientation

section Contra

abbrev diagE6 (L : Type) [Field L] : ModGL Tag.E6 L := diagramMap TwistTag.E6 L

theorem e6_graph_transporter {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {b : Fin Tag.E6.rank → Lˣ} {z : Fin Tag.E6.rank → ZMod p}
    (hcol : ∀ l l' : Fin Tag.E6.rank → ℤ, rootChar b l = rootChar b l' ↔ charVal z l = charVal z l')
    {G₃ : ModGL Tag.E6 L} (hG₃ : G₃ ∈ adjointGroup Tag.E6 L)
    (hfix : (G₃ * diagE6 L) * rootDiagUnit Tag.E6 b * (G₃ * diagE6 L)⁻¹ = rootDiagUnit Tag.E6 b) :
    ∃ w : WeylGroup Tag.E6,
      rootDiagUnit Tag.E6 b = canonicalRep (coxeterSystem Tag.E6) L w *
        rootDiagUnit Tag.E6 (fun i => b (TwistTag.E6.perm.symm i)) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ ∧
      ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x := by
  classical
  set Q : ModGL Tag.E6 L := diagE6 L with hQ
  set bσ : Fin Tag.E6.rank → Lˣ := fun i => b (TwistTag.E6.perm.symm i) with hbσ
  have hQb : Q * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 bσ * Q :=
    E6_diagramMap_mul_rootDiagUnit b
  have h1 : G₃ * rootDiagUnit Tag.E6 bσ * G₃⁻¹ = rootDiagUnit Tag.E6 b := by
    have e : rootDiagUnit Tag.E6 bσ = Q * rootDiagUnit Tag.E6 b * Q⁻¹ := by
      rw [hQb, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    simpa [mul_assoc] using hfix
  have htr := exceptional_root_diagonal_conjugacy_Weyl_transporter Tag.E6 L b bσ
  obtain ⟨w, hw⟩ := htr.1.1 ⟨G₃, hG₃, h1⟩
  refine ⟨w, (htr.2.2.1 w).2 hw, fun x => ?_⟩
  apply (hcol _ _).1
  rw [hw]
  calc rootChar bσ (permLattice e6Rho x)
      = rootChar b (permLattice TwistTag.E6.perm.symm (permLattice e6Rho x)) :=
        (rootChar_permLattice b TwistTag.E6.perm.symm _).symm
    _ = rootChar b x := by
        congr 1
        funext j
        exact congrArg x (Equiv.symm_apply_apply TwistTag.E6.perm j)

theorem e6_graph_conj_shape {L : Type} [Field L] (v : WeylGroup Tag.E6) (w : WeylGroup Tag.E6)
    (π' : Equiv.Perm (Fin 4))
    (hroot : ∀ i j : Fin 4, w • permLattice e6Rho (sigmaRootE6A3 v i j) =
      sigmaRootE6A3 v (π' j) (π' i))
    {t₀ : ModGL Tag.E6 L} (ht₀ : t₀ ∈ torusGroup Tag.E6 L) :
    ∃ (Φ'' : SL(4, L) →* SL(4, L)) (A : GL (Fin 4) L),
      (∀ X, (t₀ * canonicalRep (coxeterSystem Tag.E6) L w * diagE6 L) * rhoSigmaE6A3 L v X *
        (t₀ * canonicalRep (coxeterSystem Tag.E6) L w * diagE6 L)⁻¹ =
          rhoSigmaE6A3 L v (Φ'' X)) ∧
      ∀ X, ((Φ'' X : SL(4, L)) : Matrix (Fin 4) (Fin 4) L) =
        (A : Matrix (Fin 4) (Fin 4) L) * ((X : Matrix (Fin 4) (Fin 4) L)⁻¹)ᵀ *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) L) := by
  classical
  set nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hnwm : nw ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L w
  have hπ : weylQuotientHom Tag.E6 L ⟨nw, hnwm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  obtain ⟨b₀, hb₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀
  set Q : ModGL Tag.E6 L := diagE6 L with hQ
  choose! ε hε using fun (i j : Fin 4) (hij : i ≠ j) =>
    rhoSigmaE6A3_transvection (L := L) v i j hij
  have hconj : ∀ i j : Fin 4, i ≠ j → ∃ β : Lˣ, ∀ c : L,
      (t₀ * nw * Q) * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * (t₀ * nw * Q)⁻¹ =
        pinnedX Tag.E6 L (sigmaRootE6A3 v (π' j) (π' i)) ((β : L) * c) := by
    intro i j hij
    have hα : IsRoot Tag.E6 (sigmaRootE6A3 v i j) := isRoot_sigmaRootE6A3 v hij
    have hγ : IsRoot Tag.E6 (w • permLattice e6Rho (sigmaRootE6A3 v i j)) := by
      rw [hroot i j]
      exact isRoot_sigmaRootE6A3 v (π'.injective.ne hij.symm)
    have hργ : IsRoot Tag.E6 (permLattice e6Rho (sigmaRootE6A3 v i j)) := by
      have := IsRoot.smul hγ w⁻¹
      rwa [inv_smul_smul] at this
    obtain ⟨e, hee, he⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hα
    have he' : ∀ c : L, Q * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * Q⁻¹ =
        pinnedX Tag.E6 L (permLattice e6Rho (sigmaRootE6A3 v i j)) (e * c) := he
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnwm hργ
    rw [hπ] at hμ
    refine ⟨rootChar b₀ (w • permLattice e6Rho (sigmaRootE6A3 v i j)) * μ *
      ⟨e, e, hee, hee⟩, fun c => ?_⟩
    have e1 : (t₀ * nw * Q) * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * (t₀ * nw * Q)⁻¹ =
        t₀ * (nw * (Q * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * Q⁻¹) * nw⁻¹) * t₀⁻¹ := by
      group
    rw [e1, he' c, hμ, hb₀, rootDiagUnit_conj_pinnedX b₀ hγ, hroot i j]
    congr 1
    simp only [Units.val_mul]
    ring
  obtain ⟨Φ', hΦ', b', hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E6) (ν := 4)
    (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v) (sigmaRootE6A3 v) ε
    (fun i j hij t => hε i j hij t)
    (RingHom.id L) Function.bijective_id (t₀ * nw * Q) (fun i j => (π' j, π' i))
    (fun i j hij => π'.injective.ne hij.symm)
    (fun i j hij => ⟨π'.symm j, π'.symm i, π'.symm.injective.ne hij.symm, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin 4) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(4, L)) :
        Matrix (Fin 4) (Fin 4) L) = 1 + single (π' j) (π' i) ((b' i j : L) * (RingHom.id L) t) :=
    fun i j hij t => hshape i j hij t
  obtain ⟨A, hA⟩ := exists_conj_map_inv_transpose_of_root_permuting (n := 4) (by norm_num)
    (RingHom.id L) π' Φ'.toMonoidHom b' hshape'
  refine ⟨Φ'.toMonoidHom, A, fun X => ?_, fun X => ?_⟩
  · have hid : ∀ g : ModGL Tag.E6 L, Units.map (entrywiseHom (RingHom.id L)) g = g :=
      fun g => Units.ext (entrywise_id _)
    have := hΦ' X
    rw [hid] at this
    exact this
  · simpa using hA X

theorem e6_graph_contra {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] {p : ℕ} [Fact p.Prime] (hp5 : p = 5 ∨ 7 < p)
    {b : Fin Tag.E6.rank → Lˣ} {z : Fin Tag.E6.rank → ZMod p} (hz0 : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) e6F4U).mulVec z = ((Nat.card K : ℕ) : ZMod p) • z)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (hcol : ∀ l l' : Fin Tag.E6.rank → ℤ, rootChar b l = rootChar b l' ↔ charVal z l = charVal z l')
    {v : WeylGroup Tag.E6} (hSeq : rootCharKernel b = sigmaSetE6A3 v)
    (hCent : ∀ y ∈ adjointGroup Tag.E6 L, y * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * y →
      y ∈ (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) *
        (rootSpan Tag.E6 L (sigmaSetE6A3 v) : Set (ModGL Tag.E6 L)))
    {G₃ : ModGL Tag.E6 L} (hG₃ : G₃ ∈ adjointGroup Tag.E6 L)
    (hfix : (G₃ * diagE6 L) * rootDiagUnit Tag.E6 b * (G₃ * diagE6 L)⁻¹ = rootDiagUnit Tag.E6 b)
    {H : SL(4, L)}
    (hP : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
        Matrix.SpecialLinearGroup.toGL Z =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) →
      (G₃ * diagE6 L) * rhoSigmaE6A3 L v Z * (G₃ * diagE6 L)⁻¹ = rhoSigmaE6A3 L v Z) :
    False := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Q : ModGL Tag.E6 L := diagE6 L with hQ
  obtain ⟨w, hwd, hwz⟩ := e6_graph_transporter hcol hG₃ hfix
  have hkerz : rootKernel z = rootCharKernel b := by
    ext α
    have h0 := hcol α 0
    rw [rootChar_zero] at h0
    have h00 : charVal z (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [charVal]
    rw [h00] at h0
    exact and_congr_right fun _ => h0.symm
  have hv : ((v⁻¹ • ·) : (Fin Tag.E6.rank → ℤ) → _) '' rootKernel z =
      parabolicRoots Tag.E6 support134 := by
    rw [hkerz, hSeq, sigmaSetE6A3, Set.image_image]
    ext x
    simp
  have hneg := e6_graph_orientation hp5 hΦ hz0 hzr hv hwz
  obtain ⟨π', hπ'⟩ := hneg
  have hπ'' : ∀ i j : Fin 4, v⁻¹ • (w • permLattice e6Rho (v • chainRoot chain134 i j)) =
      chainRoot chain134 (π' j) (π' i) := by
    intro i j
    have := hπ' i j
    simpa using this
  have hroot : ∀ i j : Fin 4, w • permLattice e6Rho (sigmaRootE6A3 v i j) =
      sigmaRootE6A3 v (π' j) (π' i) := by
    intro i j
    rw [sigmaRootE6A3_eq_smul, sigmaRootE6A3_eq_smul]
    have := congrArg (fun x => v • x) (hπ'' i j)
    simpa using this
  set nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hnwA : nw ∈ adjointGroup Tag.E6 L :=
    ((exceptional_root_diagonal_conjugacy_Weyl_transporter Tag.E6 L b b).2.2.2) w
  set bσ : Fin Tag.E6.rank → Lˣ := fun i => b (TwistTag.E6.perm.symm i) with hbσ
  have hQb : Q * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 bσ * Q :=
    E6_diagramMap_mul_rootDiagUnit b
  have h1 : G₃ * rootDiagUnit Tag.E6 bσ * G₃⁻¹ = rootDiagUnit Tag.E6 b := by
    have e : rootDiagUnit Tag.E6 bσ = Q * rootDiagUnit Tag.E6 b * Q⁻¹ := by
      rw [hQb, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    simpa [mul_assoc] using hfix
  have hu : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by
    have e : nw⁻¹ * rootDiagUnit Tag.E6 b * nw = rootDiagUnit Tag.E6 bσ := by
      rw [hwd]
      group
    have : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹ = rootDiagUnit Tag.E6 b := by
      calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹
          = G₃ * (nw⁻¹ * rootDiagUnit Tag.E6 b * nw) * G₃⁻¹ := by group
        _ = rootDiagUnit Tag.E6 b := by rw [e, h1]
    calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b
        = ((G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹) * (G₃ * nw⁻¹) := by group
      _ = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by rw [this]
  obtain ⟨t₀, ht₀, q₀, hq₀, huq⟩ := hCent (G₃ * nw⁻¹) (mul_mem hG₃ (inv_mem hnwA)) hu
  set q'' : ModGL Tag.E6 L := t₀ * q₀ * t₀⁻¹ with hq''
  have hq''mem : q'' ∈ rootSpan Tag.E6 L (sigmaSetE6A3 v) := by
    have hnorm := torusGroup_le_normalizer_rootSpan (τ := Tag.E6) (L := L)
      (S := sigmaSetE6A3 v) (sigmaSetE6A3_isRoot v) ht₀
    exact (Subgroup.mem_normalizer_iff.1 hnorm q₀).1 hq₀
  have hm' : G₃ * Q = q'' * (t₀ * nw * Q) := by
    have huq' : t₀ * q₀ = G₃ * nw⁻¹ := huq
    have : G₃ = t₀ * q₀ * nw := by
      rw [huq']
      group
    rw [this, hq'']
    group
  obtain ⟨Φ'', A, hΦ'', hA⟩ := e6_graph_conj_shape (L := L) v w π'
    (fun i j => hroot i j) ht₀
  obtain ⟨Qt, hQt⟩ : ∃ Qt : SL(4, L), rhoSigmaE6A3 L v Qt = q'' := by
    have : q'' ∈ (rhoSigmaE6A3 L v).range := by
      rw [rhoSigmaE6A3_range]
      exact hq''mem
    exact this
  have hfixZ : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
      Matrix.SpecialLinearGroup.toGL Z =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) →
      Qt * Φ'' Z * Qt⁻¹ = Z := by
    intro Z hZ
    have h := hP Z hZ
    rw [hm'] at h
    have e : (q'' * (t₀ * nw * Q)) * rhoSigmaE6A3 L v Z * (q'' * (t₀ * nw * Q))⁻¹ =
        q'' * ((t₀ * nw * Q) * rhoSigmaE6A3 L v Z * (t₀ * nw * Q)⁻¹) * q''⁻¹ := by group
    rw [e, hΦ'', ← hQt, ← map_inv, ← map_mul, ← map_mul] at h
    exact (rhoSigmaE6A3_injective v h)
  set Hg : GL (Fin 4) L := Matrix.SpecialLinearGroup.toGL H with hHg
  set Qg : GL (Fin 4) L := Matrix.SpecialLinearGroup.toGL Qt with hQg
  set A₁ : GL (Fin 4) L := Qg * A with hA₁def
  have hcoeinv : ∀ g : GL (Fin 4) L, ((g⁻¹ : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) =
      (g : Matrix (Fin 4) (Fin 4) L)⁻¹ := fun g => Matrix.coe_units_inv g
  have hA₁ : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
      Matrix.SpecialLinearGroup.toGL Z = Hg * Y * Hg⁻¹) →
      Matrix.SpecialLinearGroup.toGL Z =
        A₁ * invTransposeHom (Matrix.SpecialLinearGroup.toGL Z) * A₁⁻¹ := by
    intro Z hZ
    have h1 := hfixZ Z hZ
    have h2 : Matrix.SpecialLinearGroup.toGL (Φ'' Z) =
        A * invTransposeHom (Matrix.SpecialLinearGroup.toGL Z) * A⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_invTransposeHom, hcoeinv]
      exact hA Z
    calc Matrix.SpecialLinearGroup.toGL Z
        = Matrix.SpecialLinearGroup.toGL (Qt * Φ'' Z * Qt⁻¹) := by rw [h1]
      _ = Qg * Matrix.SpecialLinearGroup.toGL (Φ'' Z) * Qg⁻¹ := by
          simp [map_mul, map_inv, hQg]
      _ = A₁ * invTransposeHom (Matrix.SpecialLinearGroup.toGL Z) * A₁⁻¹ := by
          rw [h2, hA₁def]
          group
  have hHA : ∀ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
      (Hg⁻¹ * A₁ * invTransposeHom Hg) * invTransposeHom Y * (Hg⁻¹ * A₁ * invTransposeHom Hg)⁻¹ =
        Y := by
    intro Y hY
    obtain ⟨Z, hZ⟩ : ∃ Z : SL(4, L), Matrix.SpecialLinearGroup.toGL Z = Hg * Y * Hg⁻¹ := by
      refine ⟨⟨((Hg * Y * Hg⁻¹ : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L), ?_⟩, ?_⟩
      · have hdet : ((Y : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L).det = 1 := hY.2.1
        have hH : ((Hg : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L).det = 1 := H.2
        simp [Units.val_mul, Matrix.det_mul, hdet, hcoeinv, hH]
      · exact Units.ext rfl
    have e := hA₁ Z ⟨Y, hY, hZ⟩
    rw [hZ, map_mul, map_mul, map_inv] at e
    calc (Hg⁻¹ * A₁ * invTransposeHom Hg) * invTransposeHom Y *
          (Hg⁻¹ * A₁ * invTransposeHom Hg)⁻¹
        = Hg⁻¹ * (A₁ * (invTransposeHom Hg * invTransposeHom Y * (invTransposeHom Hg)⁻¹) *
            A₁⁻¹) * Hg := by group
      _ = Hg⁻¹ * (Hg * Y * Hg⁻¹) * Hg := by rw [← e]
      _ = Y := by group
  obtain ⟨-, hrig, -⟩ :=
    CFSG.RankThree.SU4Rigidity.su4_root_subgroup_and_linear_graph_pointwise_rigidity
      (k := K) (q := Nat.card K) rfl (Ω := L)
  refine hrig ⟨Hg⁻¹ * A₁ * invTransposeHom Hg, fun Y hY => ?_⟩
  have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) (hHA Y hY)
  simpa [Units.val_mul, coe_invTransposeHom, hcoeinv] using this


end Contra

end CFSG.RankThree.PartOne.KE
