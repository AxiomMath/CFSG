module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SL3Restriction
public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularSL3
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus
public import CFSG.RankThree.Classical2.SLnSemilinearRigidity

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix SteinbergBN EvenF4QPlus
  Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem exists_scalar_of_commute_map_SL3 {K : Type} [Field K] (f : K →+* L) (C : GL (Fin 3) L)
    (hC : ∀ X ∈ {X : SL(3, L) | ∃ Y : SL(3, K), X = SpecialLinearGroup.map f Y},
      (C : Matrix (Fin 3) (Fin 3) L) * (X : Matrix (Fin 3) (Fin 3) L) =
        (X : Matrix (Fin 3) (Fin 3) L) * C) :
    ∃ c : L, (C : Matrix (Fin 3) (Fin 3) L) = scalar (Fin 3) c := by
  have hmap : ∀ {a b : Fin 3} (hab : a ≠ b),
      ((SpecialLinearGroup.map f (transvection hab (1 : K)) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single a b 1 := fun hab => by
    ext p q
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  have h := fun {a b : Fin 3} (hab : a ≠ b) => hmap hab ▸ hC _ ⟨transvection hab 1, rfl⟩
  refine ⟨(C : Matrix (Fin 3) (Fin 3) L) 0 0, ?_⟩
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  exact eq_smul_one_of_commute_sl3_gens (h (show (0 : Fin 3) ≠ 1 by decide))
    (h (show (1 : Fin 3) ≠ 0 by decide)) (h (show (1 : Fin 3) ≠ 2 by decide))

theorem exists_scalar_of_commute_unitary {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (C : GL (Fin 3) Ω)
    (hC : ∀ X ∈ {X : SL(3, Ω) | SpecialLinearGroup.toGL X ∈
        Classical2.unitarySet (Nat.card K) 3},
      (C : Matrix (Fin 3) (Fin 3) Ω) * (X : Matrix (Fin 3) (Fin 3) Ω) =
        (X : Matrix (Fin 3) (Fin 3) Ω) * C) :
    ∃ c : Ω, (C : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c := by
  have hmem : C ∈ Subgroup.centralizer (Classical2.unitarySet (Ω := Ω) (Nat.card K) 3) := by
    rw [Subgroup.mem_centralizer_iff]
    intro Y hY
    have hdet : (Y : Matrix (Fin 3) (Fin 3) Ω).det = 1 := hY.2.1
    set Y' : SL(3, Ω) := ⟨(Y : Matrix (Fin 3) (Fin 3) Ω), hdet⟩ with hY'def
    have hY' : SpecialLinearGroup.toGL Y' = Y := Units.ext rfl
    have h1 := hC Y' (by
      change SpecialLinearGroup.toGL Y' ∈ Classical2.unitarySet (Ω := Ω) (Nat.card K) 3
      rw [hY']
      exact hY)
    exact Units.ext h1.symm
  rw [Classical2.centralizer_unitary_eq_range_scalar (k := K) rfl (le_refl 3)] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, by rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]⟩

theorem subsystemGroup_le_centralizer_of_forall_torusRootChar
    {z : ModGL Tag.F4 L}
    (hz : z ∈ torusGroup Tag.F4 L) {J : Set (Fin Tag.F4.rank)}
    (h : ∀ a ∈ J, torusRootChar z (Pi.single a 1) = 1) :
    subsystemGroup Tag.F4 L J ≤ Subgroup.centralizer {z} := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hz
  have hneg : ∀ j, torusRootChar (rootDiagUnit Tag.F4 c) (Pi.single j 1) = 1 →
      torusRootChar (rootDiagUnit Tag.F4 c) (-Pi.single j 1) = 1 := fun j hj => by
    rw [torusRootChar_rootDiagUnit c (isRoot_single Tag.F4 j)] at hj
    rw [torusRootChar_rootDiagUnit c (IsRoot.neg (isRoot_single Tag.F4 j)), rootChar_neg',
      Units.val_inv_eq_inv_val, hj, inv_one]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, a, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_single]
    exact ((commute_pinnedX_iff hz (isRoot_single Tag.F4 j)).2 (h j hj) a).symm
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_neg_single]
    exact ((commute_pinnedX_iff hz (IsRoot.neg (isRoot_single Tag.F4 j))).2
      (hneg j (h j hj)) a).symm

theorem mem_centralizer_conj_A2_iff
    (κ : F4A2Kind) {U : Set (SL(3, L))}
    (hU : ∀ C : GL (Fin 3) L, (∀ X ∈ U, (C : Matrix (Fin 3) (Fin 3) L) *
      (X : Matrix (Fin 3) (Fin 3) L) = (X : Matrix (Fin 3) (Fin 3) L) * C) →
        ∃ c : L, (C : Matrix (Fin 3) (Fin 3) L) = scalar (Fin 3) c)
    {a : ModGL Tag.F4 L} (ha : a ∈ subsystemGroup Tag.F4 L {κ.i, κ.j}) {z : ModGL Tag.F4 L}
    (hz : z ∈ torusGroup Tag.F4 L ⊔ subsystemGroup Tag.F4 L {κ.i, κ.j}) :
    (∀ X ∈ U, z * (a * ((f4A2Equiv L κ).symm X : ModGL Tag.F4 L) * a⁻¹) =
        a * ((f4A2Equiv L κ).symm X : ModGL Tag.F4 L) * a⁻¹ * z) ↔
      z ∈ torusGroup Tag.F4 L ∧ torusRootChar z (Pi.single κ.i 1) = 1 ∧
        torusRootChar z (Pi.single κ.j 1) = 1 := by
  classical
  set Q := subsystemGroup Tag.F4 L {κ.i, κ.j} with hQ
  set r := f4A2Equiv L κ with hrdef
  have hNQ : torusGroup Tag.F4 L ≤ Subgroup.normalizer (Q : Set (ModGL Tag.F4 L)) := by
    rw [hQ, subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  constructor
  · intro hc
    have hz' : a⁻¹ * z * a ∈ torusGroup Tag.F4 L ⊔ Q :=
      mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_right ha)) hz) (Subgroup.mem_sup_right ha)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNQ] at hz'
    obtain ⟨h₀, hh₀, v₀, hv₀, hz'eq⟩ := hz'
    simp only at hz'eq
    obtain ⟨hN, hconj⟩ := f4A2Equiv_torus_mul_conj κ hh₀ hv₀
    obtain ⟨D, hDdef⟩ : ∃ D : Matrix (Fin 3) (Fin 3) L, D =
        diagonal ![torusRootChar h₀ (Pi.single κ.i 1) * torusRootChar h₀ (Pi.single κ.j 1),
          torusRootChar h₀ (Pi.single κ.j 1), 1] := ⟨_, rfl⟩
    obtain ⟨C, hCdef⟩ : ∃ C : Matrix (Fin 3) (Fin 3) L,
        C = D * ((f4A2Equiv L κ ⟨v₀, hv₀⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := ⟨_, rfl⟩
    rw [← hDdef, ← hCdef] at hconj
    have hDdet : IsUnit D.det := by
      have ha0 := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh₀) (Pi.single κ.i 1)
      have hb0 := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh₀) (Pi.single κ.j 1)
      rw [hDdef, Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, mul_one]
      exact (mul_ne_zero (mul_ne_zero ha0 hb0) hb0).isUnit
    have hCdet : IsUnit C.det := by
      have h1 : ((f4A2Equiv L κ ⟨v₀, hv₀⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).det = 1 :=
        Matrix.SpecialLinearGroup.det_coe _
      rw [hCdef, Matrix.det_mul, h1, mul_one]
      exact hDdet
    have hc' : ∀ X ∈ U, h₀ * v₀ * ((r.symm X : Q) : ModGL Tag.F4 L) =
        ((r.symm X : Q) : ModGL Tag.F4 L) * (h₀ * v₀) := fun X hX => by
      rw [hz'eq]
      have h1 := hc X hX
      calc a⁻¹ * z * a * ((r.symm X : Q) : ModGL Tag.F4 L) =
            a⁻¹ * (z * (a * ((r.symm X : Q) : ModGL Tag.F4 L) * a⁻¹)) * a := by group
        _ = a⁻¹ * (a * ((r.symm X : Q) : ModGL Tag.F4 L) * a⁻¹ * z) * a := by rw [h1]
        _ = ((r.symm X : Q) : ModGL Tag.F4 L) * (a⁻¹ * z * a) := by group
    have hCX : ∀ X ∈ U, C * (X : Matrix (Fin 3) (Fin 3) L) = (X : Matrix (Fin 3) (Fin 3) L) * C :=
      fun X hX => by
        have h1 := hconj (r.symm X)
        have e : (⟨h₀ * v₀ * ((r.symm X : Q) : ModGL Tag.F4 L) * (h₀ * v₀)⁻¹,
            hN _ (r.symm X).2⟩ : Q) = r.symm X :=
          Subtype.ext (by
            change h₀ * v₀ * ((r.symm X : Q) : ModGL Tag.F4 L) * (h₀ * v₀)⁻¹ = r.symm X
            rw [hc' X hX, mul_inv_cancel_right])
        rw [e, MulEquiv.apply_symm_apply] at h1
        have h2 : C * (X : Matrix (Fin 3) (Fin 3) L) * C⁻¹ * C =
            C * (X : Matrix (Fin 3) (Fin 3) L) :=
          Matrix.nonsing_inv_mul_cancel_right _ _ hCdet
        rw [← h2, ← h1]
    obtain ⟨c, hc⟩ := hU (Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet.ne_zero) hCX
    change C = scalar (Fin 3) c at hc
    have hcomm : ∀ Y : Matrix (Fin 3) (Fin 3) L, C * Y = Y * C := fun Y => by
      rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have htriv : ∀ y : Q, h₀ * v₀ * (y : ModGL Tag.F4 L) * (h₀ * v₀)⁻¹ = y := fun y => by
      have h1 := hconj y
      rw [hcomm, Matrix.mul_nonsing_inv_cancel_right _ _ hCdet] at h1
      exact congrArg Subtype.val (r.injective (Subtype.ext h1))
    have hdiag : ((r ⟨v₀, hv₀⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).IsDiag := by
      have h1 : ((r ⟨v₀, hv₀⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = D⁻¹ * C := by
        rw [hCdef, Matrix.nonsing_inv_mul_cancel_left _ _ hDdet]
      rw [h1, hc, hDdef, Matrix.inv_diagonal, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
      exact Matrix.isDiag_diagonal _
    obtain ⟨g, hgT, hgv⟩ := (f4A2Equiv_torus_iff κ (r ⟨v₀, hv₀⟩)).2 hdiag
    have hgv' : g = ⟨v₀, hv₀⟩ := r.injective hgv
    have hv₀H : v₀ ∈ torusGroup Tag.F4 L := by
      have h1 := subsystemTorus_le_torusGroup hgT
      rwa [hgv'] at h1
    have hzH : h₀ * v₀ ∈ torusGroup Tag.F4 L := mul_mem hh₀ hv₀H
    have hχ : ∀ k (hk : k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))),
        torusRootChar (h₀ * v₀) (Pi.single k 1) = 1 := fun k hk => by
      have e := conj_pinnedX_of_mem_torusGroup hzH (isRoot_single Tag.F4 k) 1
      rw [pinnedX_single, show h₀ * v₀ * xUnit Tag.F4 L k 1 * (h₀ * v₀)⁻¹ = xUnit Tag.F4 L k 1
        from htriv (qx hk 1), ← pinnedX_single] at e
      have e' := pinnedX_injective Tag.F4 L _ e
      rw [mul_one] at e'
      exact e'.symm
    have hca := Subgroup.mem_centralizer_singleton_iff.1
      (subsystemGroup_le_centralizer_of_forall_torusRootChar hzH hχ ha)
    have hzz : z = h₀ * v₀ := by
      calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
        _ = a * (h₀ * v₀) * a⁻¹ := by rw [hz'eq]
        _ = h₀ * v₀ := by rw [hca, mul_inv_cancel_right]
    rw [hzz]
    exact ⟨hzH, hχ _ (left_mem_pair κ.i κ.j), hχ _ (right_mem_pair κ.i κ.j)⟩
  · rintro ⟨hzH, h1, h2⟩ X _
    have hle := subsystemGroup_le_centralizer_of_forall_torusRootChar hzH
      (J := {κ.i, κ.j}) (by
        rintro k (rfl | hk)
        · exact h1
        · rw [Set.mem_singleton_iff] at hk
          rw [hk]
          exact h2)
    exact (Subgroup.mem_centralizer_singleton_iff.1
      (hle (mul_mem (mul_mem ha (r.symm X).2) (inv_mem ha)))).symm

end CFSG.RankThree.Chevalley
