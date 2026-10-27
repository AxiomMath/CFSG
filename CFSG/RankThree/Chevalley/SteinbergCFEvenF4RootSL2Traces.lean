module

public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.LieType.Ree.LargeReeRootInvolution

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial

variable {L : Type} [Field L]

theorem trace_restrict_conj {V : Type*} [AddCommGroup V] [Module L V] (p : Submodule L V)
    (W : (V →ₗ[L] V)ˣ) (g : V →ₗ[L] V) (hW : ∀ v ∈ p, (W : V →ₗ[L] V) v ∈ p)
    (hW' : ∀ v ∈ p, ((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V) v ∈ p) (hg : ∀ v ∈ p, g v ∈ p)
    (h : ∀ v ∈ p, ((W : V →ₗ[L] V) * g * ((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V)) v ∈ p) :
    LinearMap.trace L p (((W : V →ₗ[L] V) * g * ((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V)).restrict h) =
      LinearMap.trace L p (g.restrict hg) := by
  have e : ((W : V →ₗ[L] V) * g * ((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V)).restrict h =
      (W : V →ₗ[L] V).restrict hW * g.restrict hg *
        (((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V)).restrict hW' := by
    ext v
    rfl
  have e1 : (((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V)).restrict hW' * (W : V →ₗ[L] V).restrict hW =
      1 := by
    ext v
    change (((W⁻¹ : (V →ₗ[L] V)ˣ) : V →ₗ[L] V) * (W : V →ₗ[L] V)) v = v
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  rw [e, LinearMap.trace_mul_comm, ← mul_assoc, e1, one_mul]

theorem shortBasis_repr_apply (t : ReeTag) (R : Type*) [CommRing R] (v : t.shortModule R)
    (b : t.shortLabels) : (t.shortBasis R).repr v b = (v : RootModule t.tag R) b.1 := by
  simp [ReeTag.shortBasis]

theorem trace_restrict_shortModule (t : ReeTag) (g : Module.End L (RootModule t.tag L))
    (h : ∀ v ∈ t.shortModule L, g v ∈ t.shortModule L) :
    LinearMap.trace L (t.shortModule L) (g.restrict h) =
      ∑ b ∈ Finset.univ.filter t.IsShortLabel, g (Finsupp.single b 1) b := by
  classical
  rw [LinearMap.trace_eq_matrix_trace L (t.shortBasis L), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, shortBasis_repr_apply,
    LinearMap.restrict_apply, ReeTag.coe_shortBasis]
  rw [← Finset.sum_subtype (Finset.univ.filter t.IsShortLabel)
    (fun b => by simp [ReeTag.shortLabels]) (fun b => g (Finsupp.single b 1) b)]

@[expose] def shortRootExponentsF4 (j : Fin ReeTag.F4.tag.rank) : List ℤ :=
  ((List.range ReeTag.F4.tag.rootCertificate.roots.length).filter
    (fun k => ReeTag.F4.quadForm (ReeTag.F4.tag.rootCertificate.root k) = 2)).map fun k =>
      ∑ i, ReeTag.F4.tag.cartan j i * ReeTag.F4.tag.rootCertificate.root k i

theorem rootExponents_F4_long (j : Fin ReeTag.F4.tag.rank) (hj : (j : ℕ) < 2) :
    (rootExponents ReeTag.F4.tag j).toFinset ⊆ {-2, -1, 0, 1, 2} ∧
      (rootExponents ReeTag.F4.tag j).count (-2) = 1 ∧
      (rootExponents ReeTag.F4.tag j).count (-1) = 14 ∧
      (rootExponents ReeTag.F4.tag j).count 0 = 18 ∧
      (rootExponents ReeTag.F4.tag j).count 1 = 14 ∧
      (rootExponents ReeTag.F4.tag j).count 2 = 1 := by
  revert j
  decide +kernel

theorem rootExponents_F4_short (j : Fin ReeTag.F4.tag.rank) (hj : 2 ≤ (j : ℕ)) :
    (rootExponents ReeTag.F4.tag j).toFinset ⊆ {-2, -1, 0, 1, 2} ∧
      (rootExponents ReeTag.F4.tag j).count (-2) = 7 ∧
      (rootExponents ReeTag.F4.tag j).count (-1) = 8 ∧
      (rootExponents ReeTag.F4.tag j).count 0 = 18 ∧
      (rootExponents ReeTag.F4.tag j).count 1 = 8 ∧
      (rootExponents ReeTag.F4.tag j).count 2 = 7 := by
  revert j
  decide +kernel

theorem shortRootExponentsF4_long (j : Fin ReeTag.F4.tag.rank) (hj : (j : ℕ) < 2) :
    (shortRootExponentsF4 j).toFinset ⊆ {-2, -1, 0, 1, 2} ∧
      (shortRootExponentsF4 j).count (-2) = 0 ∧ (shortRootExponentsF4 j).count (-1) = 6 ∧
      (shortRootExponentsF4 j).count 0 = 12 ∧ (shortRootExponentsF4 j).count 1 = 6 ∧
      (shortRootExponentsF4 j).count 2 = 0 := by
  revert j
  decide +kernel

theorem shortRootExponentsF4_short (j : Fin ReeTag.F4.tag.rank) (hj : 2 ≤ (j : ℕ)) :
    (shortRootExponentsF4 j).toFinset ⊆ {-2, -1, 0, 1, 2} ∧
      (shortRootExponentsF4 j).count (-2) = 1 ∧ (shortRootExponentsF4 j).count (-1) = 8 ∧
      (shortRootExponentsF4 j).count 0 = 6 ∧ (shortRootExponentsF4 j).count 1 = 8 ∧
      (shortRootExponentsF4 j).count 2 = 1 := by
  revert j
  decide +kernel

theorem list_sum_map_eq_of_toFinset_subset {M : Type*} [AddCommMonoid M] (l : List ℤ) (g : ℤ → M)
    (h : l.toFinset ⊆ {-2, -1, 0, 1, 2}) :
    (l.map g).sum = l.count (-2) • g (-2) + l.count (-1) • g (-1) + l.count 0 • g 0 +
      l.count 1 • g 1 + l.count 2 • g 2 := by
  classical
  rw [Finset.sum_list_map_count, Finset.sum_subset h fun m _ hm => by
    rw [List.count_eq_zero.2 (fun h' => hm (List.mem_toFinset.2 h')), zero_smul],
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

theorem list_sum_map_ite_eq_sum_filter {α M : Type*} [AddCommMonoid M] (l : List α)
    (p : α → Bool) (f : α → M) :
    (l.map fun x => if p x then f x else 0).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases h : p x <;> simp [h, ih]

theorem sum_shortRoots_eq_shortRootExponentsF4 {M : Type*} [AddCommMonoid M]
    (j : Fin ReeTag.F4.tag.rank) (g : ℤ → M) :
    ∑ β : {v : Fin ReeTag.F4.tag.rank → ℤ // IsRoot ReeTag.F4.tag v},
        (if ReeTag.F4.quadForm β.1 = 2 then g (∑ i, ReeTag.F4.tag.cartan j i * β.1 i) else 0) =
      ((shortRootExponentsF4 j).map g).sum := by
  classical
  have hnd : ((List.range ReeTag.F4.tag.rootCertificate.roots.length).map
      ReeTag.F4.tag.rootCertificate.root).Nodup := by
    have h := ReeTag.F4.tag.rootCertificate_checkNodup
    simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
    exact List.Nodup.of_map (fun v => List.ofFn v) (by rw [List.map_map]; exact h)
  rw [← Finset.sum_subtype (rootFinset ReeTag.F4.tag) (fun _ => mem_rootFinset)
    (fun v => if ReeTag.F4.quadForm v = 2 then g (∑ i, ReeTag.F4.tag.cartan j i * v i) else 0)]
  rw [rootFinset, List.sum_toFinset _ hnd, List.map_map, shortRootExponentsF4, List.map_map,
    ← list_sum_map_ite_eq_sum_filter]
  rfl

theorem sum_filter_isShortLabel_F4 {M : Type*} [AddCommMonoid M] (G : Label ReeTag.F4.tag → M) :
    ∑ b ∈ Finset.univ.filter ReeTag.F4.IsShortLabel, G b =
      G (.inl ⟨2, by decide⟩) + G (.inl ⟨3, by decide⟩) +
        ∑ β : {v : Fin ReeTag.F4.tag.rank → ℤ // IsRoot ReeTag.F4.tag v},
          (if ReeTag.F4.quadForm β.1 = 2 then G (.inr β) else 0) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  congr 1
  · change (∑ a : Fin 4, if ReeTag.F4.IsShortLabel (Sum.inl a) then G (Sum.inl a) else 0) = _
    rw [Fin.sum_univ_four]
    simp +decide
    rfl
  · refine Finset.sum_congr rfl fun β _ => ?_
    have : ReeTag.F4.IsShortLabel (.inr β) ↔ ReeTag.F4.quadForm β.1 = 2 := by
      change ReeTag.F4.lengthParam β.1 = 1 ↔ _
      rw [ReeTag.lengthParam]
      rw [div_eq_one_iff_eq (two_ne_zero (α := ℚ))]
      exact_mod_cast Iff.rfl
    simp only [this]

theorem sum_filter_isShortLabel_torusEigen (j : Fin ReeTag.F4.tag.rank) (c : Lˣ) :
    ∑ b ∈ Finset.univ.filter ReeTag.F4.IsShortLabel, torusEigen j c b =
      2 + ((shortRootExponentsF4 j).map fun n => ((c ^ n : Lˣ) : L)).sum := by
  rw [sum_filter_isShortLabel_F4, ← sum_shortRoots_eq_shortRootExponentsF4]
  simp only [torusEigen]
  norm_num

theorem trace_simpleRootSL2_HSL_mul_uSL_F4 [CharP L 2] (j : Fin ReeTag.F4.tag.rank) (c : Lˣ)
    (s : L) :
    LinearMap.trace L (RootModule ReeTag.F4.tag L)
        (simpleRootSL2 ReeTag.F4.tag L j (HSL c * uSL s) :
          Module.End L (RootModule ReeTag.F4.tag L)) = ((c : L) + (c⁻¹ : Lˣ)) ^ 2 ∧
    ∀ h : ∀ v ∈ ReeTag.F4.shortModule L, (simpleRootSL2 ReeTag.F4.tag L j (HSL c * uSL s) :
        Module.End L (RootModule ReeTag.F4.tag L)) v ∈ ReeTag.F4.shortModule L,
      LinearMap.trace L (ReeTag.F4.shortModule L)
          ((simpleRootSL2 ReeTag.F4.tag L j (HSL c * uSL s) :
            Module.End L (RootModule ReeTag.F4.tag L)).restrict h) =
        if (j : ℕ) < 2 then 0 else ((c : L) + (c⁻¹ : Lˣ)) ^ 2 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  set d : L := ((c⁻¹ : Lˣ) : L)
  have hcd : (c : L) * d = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ∀ n : ℤ, ((c ^ n : Lˣ) : L) = (c : L) ^ n := fun n => Units.val_zpow_eq_zpow_val c n
  have hd : d = (c : L)⁻¹ := Units.val_inv_eq_inv_val c
  have hneg2 : (c : L) ^ (-2 : ℤ) = d ^ 2 := by
    rw [zpow_neg, zpow_two, ← pow_two, hd, inv_pow]
  have hneg1 : (c : L) ^ (-1 : ℤ) = d := by rw [zpow_neg_one, hd]
  have hpos2 : (c : L) ^ (2 : ℤ) = (c : L) ^ 2 := zpow_ofNat _ 2
  have hdiag : ∀ b, (simpleRootSL2 ReeTag.F4.tag L j (HSL c * uSL s) :
      Module.End L (RootModule ReeTag.F4.tag L)) (Finsupp.single b 1) b = torusEigen j c b := by
    intro b
    rw [map_mul, simpleRootSL2_HSL, simpleRootSL2_uSL, Units.val_mul, Module.End.mul_apply,
      torusElt_apply_apply, (isUpperUnitriangular_xUnit j s).1 b, mul_one]
  refine ⟨?_, fun h => ?_⟩
  · rw [map_mul, simpleRootSL2_HSL, simpleRootSL2_uSL, Units.val_mul,
      trace_torusElt_mul_of_isUpperUnitriangular j c (isUpperUnitriangular_xUnit j s),
      sum_torusEigen, sum_isRoot_eq_rootExponents j (fun n => ((c ^ n : Lˣ) : L))]
    by_cases hj : (j : ℕ) < 2
    · obtain ⟨hset, e1, e2, e3, e4, e5⟩ := rootExponents_F4_long j hj
      rw [list_sum_map_eq_of_toFinset_subset _ _ hset, e1, e2, e3, e4, e5]
      simp only [hz, hneg2, hneg1, hpos2, nsmul_eq_mul, zpow_zero, zpow_one, Nat.cast_ofNat,
        Nat.cast_one, Units.val_one, one_mul, mul_one]
      change (4 : L) + _ = _
      linear_combination (10 + 7 * (c : L) + 7 * d) * h2 - 2 * hcd
    · obtain ⟨hset, e1, e2, e3, e4, e5⟩ := rootExponents_F4_short j (by omega)
      rw [list_sum_map_eq_of_toFinset_subset _ _ hset, e1, e2, e3, e4, e5]
      simp only [hz, hneg2, hneg1, hpos2, nsmul_eq_mul, zpow_zero, zpow_one, Nat.cast_ofNat,
        Units.val_one, mul_one]
      change (4 : L) + _ = _
      linear_combination (10 + 4 * (c : L) + 4 * d + 3 * (c : L) ^ 2 + 3 * d ^ 2) * h2 -
        2 * hcd
  · rw [trace_restrict_shortModule]
    simp only [hdiag]
    rw [sum_filter_isShortLabel_torusEigen]
    by_cases hj : (j : ℕ) < 2
    · obtain ⟨hset, e1, e2, e3, e4, e5⟩ := shortRootExponentsF4_long j hj
      rw [list_sum_map_eq_of_toFinset_subset _ _ hset, e1, e2, e3, e4, e5, ite_eq_left hj]
      simp only [hz, hneg2, hneg1, hpos2, nsmul_eq_mul, zpow_zero, zpow_one, Nat.cast_ofNat,
        Units.val_one, Nat.cast_zero, zero_mul, mul_one, zero_add, add_zero]
      linear_combination (7 + 3 * (c : L) + 3 * d) * h2
    · obtain ⟨hset, e1, e2, e3, e4, e5⟩ := shortRootExponentsF4_short j (by omega)
      rw [list_sum_map_eq_of_toFinset_subset _ _ hset, e1, e2, e3, e4, e5, ite_eq_right hj]
      simp only [hz, hneg2, hneg1, hpos2, nsmul_eq_mul, zpow_zero, zpow_one, Nat.cast_ofNat,
        Nat.cast_one, Units.val_one, one_mul, mul_one]
      linear_combination (3 + 4 * (c : L) + 4 * d) * h2 - 2 * hcd

theorem sum_diag_baseChangeGL {τ : Tag} {K : Type} [Field K] (f : K →+* L) (g : ModGL τ K)
    (S : Finset (Label τ)) :
    ∑ b ∈ S, (baseChangeGL f g : Module.End L (RootModule τ L)) (Finsupp.single b 1) b =
      f (∑ b ∈ S, (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) b) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [baseChangeGL_apply_single, Finsupp.mapRange_apply]

theorem mapsTo_shortModule_F4 [CharP L 2] {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ adjointGroup ReeTag.F4.tag L) :
    ∀ v ∈ ReeTag.F4.shortModule L,
      (g : Module.End L (RootModule ReeTag.F4.tag L)) v ∈ ReeTag.F4.shortModule L :=
  fun _ hv => ReeTag.mem_shortModule_of_mem (by exact_mod_cast CharTwo.two_eq_zero) hg hv

theorem trace_simpleRootSL2_F4 {M : Type} [Field M] [CharP M 2] (j : Fin ReeTag.F4.tag.rank)
    (A : SL2 M) :
    LinearMap.trace M (RootModule ReeTag.F4.tag M)
        (simpleRootSL2 ReeTag.F4.tag M j A : Module.End M (RootModule ReeTag.F4.tag M)) =
      (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2 ∧
    ∀ h : ∀ v ∈ ReeTag.F4.shortModule M, (simpleRootSL2 ReeTag.F4.tag M j A :
        Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M,
      LinearMap.trace M (ReeTag.F4.shortModule M)
          ((simpleRootSL2 ReeTag.F4.tag M j A :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h) =
        if (j : ℕ) < 2 then 0 else (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2 := by
  set L := AlgebraicClosure M
  set f : M →+* L := algebraMap M L
  have : CharP L 2 := charP_of_injective_ringHom f.injective 2
  set A' := Matrix.SpecialLinearGroup.map f A
  obtain ⟨Q, hQ⟩ := exists_conj_lower_eq_zero_of_isAlgClosed A'
  set B := Q⁻¹ * A' * Q with hB
  have hA' : A' = Q * B * Q⁻¹ := by rw [hB]; group
  have hBe := eq_HSL_mul_uSL hQ
  set u := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hQ)
  set s := (B : Matrix (Fin 2) (Fin 2) L) 0 1 / (B : Matrix (Fin 2) (Fin 2) L) 0 0
  have htr : f (A : Matrix (Fin 2) (Fin 2) M).trace = (u : L) + (u⁻¹ : Lˣ) := by
    have h1 : f (A : Matrix (Fin 2) (Fin 2) M).trace = (A' : Matrix (Fin 2) (Fin 2) L).trace := by
      simp [A', Matrix.trace_fin_two]
    have h2 : (A' : Matrix (Fin 2) (Fin 2) L).trace = (B : Matrix (Fin 2) (Fin 2) L).trace := by
      rw [hA', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, one_mul]
    rw [h1, h2, hBe, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two]
    simp [coe_HSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨hV, hI⟩ := trace_simpleRootSL2_HSL_mul_uSL_F4 j u s
  have hρ : simpleRootSL2 ReeTag.F4.tag L j A' = simpleRootSL2 ReeTag.F4.tag L j Q *
      simpleRootSL2 ReeTag.F4.tag L j B * (simpleRootSL2 ReeTag.F4.tag L j Q)⁻¹ := by
    rw [hA', map_mul, map_mul, map_inv]
  have hC : ∀ X, simpleRootSL2 ReeTag.F4.tag L j X ∈ adjointGroup ReeTag.F4.tag L :=
    fun X => simpleRootSL2_mem_adjointGroup j X
  refine ⟨?_, fun h => ?_⟩
  · apply f.injective
    rw [← trace_baseChangeGL, baseChangeGL_simpleRootSL2, hρ, Units.val_mul, Units.val_mul,
      LinearMap.trace_conj, hBe, hV, map_pow, htr]
  · apply f.injective
    have hmapsA' := mapsTo_shortModule_F4 (hC A')
    have hmapsB := mapsTo_shortModule_F4 (hC B)
    have hEnd : (simpleRootSL2 ReeTag.F4.tag L j A' : Module.End L (RootModule ReeTag.F4.tag L)) =
        (simpleRootSL2 ReeTag.F4.tag L j Q : Module.End L (RootModule ReeTag.F4.tag L)) *
          (simpleRootSL2 ReeTag.F4.tag L j B : Module.End L (RootModule ReeTag.F4.tag L)) *
          (((simpleRootSL2 ReeTag.F4.tag L j Q)⁻¹ : ModGL ReeTag.F4.tag L) :
            Module.End L (RootModule ReeTag.F4.tag L)) := by
      rw [hρ, Units.val_mul, Units.val_mul]
    have hconj : ∀ v ∈ ReeTag.F4.shortModule L,
        ((simpleRootSL2 ReeTag.F4.tag L j Q : Module.End L (RootModule ReeTag.F4.tag L)) *
          (simpleRootSL2 ReeTag.F4.tag L j B : Module.End L (RootModule ReeTag.F4.tag L)) *
          (((simpleRootSL2 ReeTag.F4.tag L j Q)⁻¹ : ModGL ReeTag.F4.tag L) :
            Module.End L (RootModule ReeTag.F4.tag L))) v ∈ ReeTag.F4.shortModule L := by
      rw [← hEnd]
      exact hmapsA'
    have hBu : ∀ v ∈ ReeTag.F4.shortModule L,
        (simpleRootSL2 ReeTag.F4.tag L j (HSL u * uSL s) :
          Module.End L (RootModule ReeTag.F4.tag L)) v ∈ ReeTag.F4.shortModule L := by
      rw [← hBe]
      exact hmapsB
    calc f (LinearMap.trace M (ReeTag.F4.shortModule M)
            ((simpleRootSL2 ReeTag.F4.tag M j A :
              Module.End M (RootModule ReeTag.F4.tag M)).restrict h))
        = ∑ b ∈ Finset.univ.filter ReeTag.F4.IsShortLabel,
            (simpleRootSL2 ReeTag.F4.tag L j A' : Module.End L (RootModule ReeTag.F4.tag L))
              (Finsupp.single b 1) b := by
          rw [trace_restrict_shortModule, ← sum_diag_baseChangeGL, baseChangeGL_simpleRootSL2]
      _ = LinearMap.trace L (ReeTag.F4.shortModule L)
            ((simpleRootSL2 ReeTag.F4.tag L j A' :
              Module.End L (RootModule ReeTag.F4.tag L)).restrict hmapsA') :=
          (trace_restrict_shortModule _ _ _).symm
      _ = LinearMap.trace L (ReeTag.F4.shortModule L)
            (((simpleRootSL2 ReeTag.F4.tag L j Q : Module.End L (RootModule ReeTag.F4.tag L)) *
              (simpleRootSL2 ReeTag.F4.tag L j B : Module.End L (RootModule ReeTag.F4.tag L)) *
              (((simpleRootSL2 ReeTag.F4.tag L j Q)⁻¹ : ModGL ReeTag.F4.tag L) :
                Module.End L (RootModule ReeTag.F4.tag L))).restrict hconj) := by
          congr 1
          exact LinearMap.ext fun v => Subtype.ext (by simp [hEnd])
      _ = LinearMap.trace L (ReeTag.F4.shortModule L)
            ((simpleRootSL2 ReeTag.F4.tag L j B :
              Module.End L (RootModule ReeTag.F4.tag L)).restrict hmapsB) :=
          trace_restrict_conj _ _ _ (mapsTo_shortModule_F4 (hC Q))
            (mapsTo_shortModule_F4 (inv_mem (hC Q))) hmapsB hconj
      _ = LinearMap.trace L (ReeTag.F4.shortModule L)
            ((simpleRootSL2 ReeTag.F4.tag L j (HSL u * uSL s) :
              Module.End L (RootModule ReeTag.F4.tag L)).restrict hBu) := by
          congr 1
          exact LinearMap.ext fun v => Subtype.ext (by simp [hBe])
      _ = if (j : ℕ) < 2 then 0 else ((u : L) + (u⁻¹ : Lˣ)) ^ 2 := hI hBu
      _ = f (if (j : ℕ) < 2 then 0 else (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2) := by
          split_ifs <;> simp [htr]

theorem pinnedData_lt_two_iff {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) :
    ((pinnedData ReeTag.F4.tag α).1 : ℕ) < 2 ↔ ReeTag.F4.quadForm α = 4 := by
  rw [ReeTag.quadForm_pinnedData hα, ReeTag.F4_quadForm_single]
  generalize (pinnedData ReeTag.F4.tag α).1 = j
  revert j
  decide

theorem even_F4_root_SL2_adjoint_and_short_module_traces (M : Type) [Field M] [CharP M 2]
    {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) (A : SL2 M) :
    LinearMap.trace M (RootModule ReeTag.F4.tag M)
        (rootSL2 ReeTag.F4.tag M α A : Module.End M (RootModule ReeTag.F4.tag M)) =
      (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2 ∧
    (∀ v ∈ ReeTag.F4.shortModule M, (rootSL2 ReeTag.F4.tag M α A :
      Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M) ∧
    ∀ h : ∀ v ∈ ReeTag.F4.shortModule M, (rootSL2 ReeTag.F4.tag M α A :
        Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M,
      (α ∈ ReeTag.F4.longRoots → LinearMap.trace M (ReeTag.F4.shortModule M)
          ((rootSL2 ReeTag.F4.tag M α A :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h) = 0) ∧
      (α ∈ ReeTag.F4.shortRoots → LinearMap.trace M (ReeTag.F4.shortModule M)
          ((rootSL2 ReeTag.F4.tag M α A :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h) =
        (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2) := by
  set j := (pinnedData ReeTag.F4.tag α).1
  set W := pinnedWeyl ReeTag.F4.tag M α
  have hW : W ∈ adjointGroup ReeTag.F4.tag M := pinnedWeyl_mem_adjointGroup α
  have hρC : ∀ X, simpleRootSL2 ReeTag.F4.tag M j X ∈ adjointGroup ReeTag.F4.tag M :=
    fun X => simpleRootSL2_mem_adjointGroup j X
  have hEnd : (rootSL2 ReeTag.F4.tag M α A : Module.End M (RootModule ReeTag.F4.tag M)) =
      (W : Module.End M (RootModule ReeTag.F4.tag M)) *
        (simpleRootSL2 ReeTag.F4.tag M j A : Module.End M (RootModule ReeTag.F4.tag M)) *
        ((W⁻¹ : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) := by
    rw [rootSL2_apply, Units.val_mul, Units.val_mul]
  obtain ⟨hV, hI⟩ := trace_simpleRootSL2_F4 j A
  have hmaps : ∀ v ∈ ReeTag.F4.shortModule M, (rootSL2 ReeTag.F4.tag M α A :
      Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M :=
    mapsTo_shortModule_F4 ((exceptional_Lang_root_rank_one_data _ M α).2.2.2.2.1 A)
  have hmapsj := mapsTo_shortModule_F4 (hρC A)
  have hconj : ∀ v ∈ ReeTag.F4.shortModule M,
      ((W : Module.End M (RootModule ReeTag.F4.tag M)) *
        (simpleRootSL2 ReeTag.F4.tag M j A : Module.End M (RootModule ReeTag.F4.tag M)) *
        ((W⁻¹ : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M))) v ∈
        ReeTag.F4.shortModule M := by
    rw [← hEnd]
    exact hmaps
  have htrI : ∀ h : ∀ v ∈ ReeTag.F4.shortModule M, (rootSL2 ReeTag.F4.tag M α A :
      Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M,
      LinearMap.trace M (ReeTag.F4.shortModule M)
          ((rootSL2 ReeTag.F4.tag M α A :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h) =
        if (j : ℕ) < 2 then 0 else (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2 := by
    intro h
    calc LinearMap.trace M (ReeTag.F4.shortModule M)
          ((rootSL2 ReeTag.F4.tag M α A :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h)
        = LinearMap.trace M (ReeTag.F4.shortModule M)
            (((W : Module.End M (RootModule ReeTag.F4.tag M)) *
              (simpleRootSL2 ReeTag.F4.tag M j A : Module.End M (RootModule ReeTag.F4.tag M)) *
              ((W⁻¹ : ModGL ReeTag.F4.tag M) :
                Module.End M (RootModule ReeTag.F4.tag M))).restrict hconj) := by
          congr 1
      _ = LinearMap.trace M (ReeTag.F4.shortModule M)
            ((simpleRootSL2 ReeTag.F4.tag M j A :
              Module.End M (RootModule ReeTag.F4.tag M)).restrict hmapsj) :=
          trace_restrict_conj _ _ _ (mapsTo_shortModule_F4 hW)
            (mapsTo_shortModule_F4 (inv_mem hW)) hmapsj hconj
      _ = _ := hI hmapsj
  refine ⟨by rw [hEnd, LinearMap.trace_conj, hV], hmaps, fun h => ⟨fun hl => ?_, fun hs => ?_⟩⟩
  · have hq : ReeTag.F4.quadForm α = 4 := by
      have h2 := hl.2
      rw [ReeTag.lengthParam] at h2
      have : (ReeTag.F4.quadForm α : ℚ) = 4 := by
        rw [div_eq_iff (two_ne_zero (α := ℚ))] at h2
        rw [h2]
        norm_num [ReeTag.prime]
      exact_mod_cast this
    rw [htrI h, ite_eq_left ((pinnedData_lt_two_iff hα).2 hq)]
  · have hq : ReeTag.F4.quadForm α = 2 := by
      have h2 := hs.2
      rw [ReeTag.lengthParam, div_eq_one_iff_eq (two_ne_zero (α := ℚ))] at h2
      exact_mod_cast h2
    rw [htrI h, ite_eq_right fun hlt => by
      have := (pinnedData_lt_two_iff hα).1 hlt
      omega]

end CFSG.RankThree.Chevalley
