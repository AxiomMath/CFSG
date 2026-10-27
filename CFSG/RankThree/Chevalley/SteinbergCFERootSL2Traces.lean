module

public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open Polynomial

variable {τ : Tag} {L : Type} [Field L]

theorem trace_rootModule_eq_sum (f : Module.End L (RootModule τ L)) :
    LinearMap.trace L (RootModule τ L) f = ∑ b : Label τ, f (Finsupp.single b 1) b := by
  classical
  rw [LinearMap.trace_eq_matrix_trace L Finsupp.basisSingleOne, Matrix.trace]
  simp [LinearMap.toMatrix_apply]

@[expose] def torusEigen (i : Fin τ.rank) (c : Lˣ) : Label τ → L
  | .inl _ => 1
  | .inr β => ((c ^ (∑ j, τ.cartan i j * β.1 j) : Lˣ) : L)

theorem torusElt_single (i : Fin τ.rank) (c : Lˣ) (b : Label τ) :
    (torusElt τ L i c : Module.End L (RootModule τ L)) (Finsupp.single b 1) =
      torusEigen i c b • Finsupp.single b 1 := by
  rcases b with j | ⟨β, hβ⟩
  · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule τ L) = hVec τ L j from rfl,
      torusElt_hVec, torusEigen, one_smul]
  · rw [← rootVec_eq_single_of_isRoot hβ, torusElt_rootVec i c hβ]
    rfl

theorem torusElt_apply_apply (i : Fin τ.rank) (c : Lˣ) (v : RootModule τ L) (b : Label τ) :
    (torusElt τ L i c : Module.End L (RootModule τ L)) v b = torusEigen i c b * v b := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hv, hw, mul_add]
  | single a r =>
    rw [show (Finsupp.single a r : RootModule τ L) = r • Finsupp.single a 1 by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, torusElt_single, smul_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      ring
    · simp [hab]

theorem trace_torusElt_mul_of_isUpperUnitriangular (i : Fin τ.rank) (c : Lˣ)
    {x : Module.End L (RootModule τ L)} (hx : IsUpperUnitriangular x) :
    LinearMap.trace L (RootModule τ L) ((torusElt τ L i c : Module.End L (RootModule τ L)) * x) =
      ∑ b : Label τ, torusEigen i c b := by
  rw [trace_rootModule_eq_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Module.End.mul_apply, torusElt_apply_apply, hx.1 b, mul_one]

theorem sum_torusEigen (i : Fin τ.rank) (c : Lˣ) :
    ∑ b : Label τ, torusEigen i c b =
      τ.rank + ∑ β : {v : Fin τ.rank → ℤ // IsRoot τ v},
        ((c ^ (∑ j, τ.cartan i j * β.1 j) : Lˣ) : L) := by
  rw [Fintype.sum_sum_type]
  simp [torusEigen]

variable (τ) in
@[expose] def rootExponents (i : Fin τ.rank) : List ℤ :=
  (List.range τ.rootCertificate.roots.length).map fun k =>
    ∑ j, τ.cartan i j * τ.rootCertificate.root k j

theorem sum_isRoot_eq_rootExponents {M : Type*} [AddCommMonoid M] (i : Fin τ.rank) (g : ℤ → M) :
    ∑ β : {v : Fin τ.rank → ℤ // IsRoot τ v}, g (∑ j, τ.cartan i j * β.1 j) =
      ((rootExponents τ i).map g).sum := by
  classical
  have hnd : ((List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root).Nodup := by
    have h := τ.rootCertificate_checkNodup
    simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
    exact List.Nodup.of_map (fun v => List.ofFn v) (by rw [List.map_map]; exact h)
  rw [← Finset.sum_subtype (rootFinset τ) (fun _ => mem_rootFinset)
    (fun v => g (∑ j, τ.cartan i j * v j))]
  rw [rootFinset, List.sum_toFinset _ hnd, List.map_map, rootExponents, List.map_map]
  rfl

theorem list_sum_map_eq_of_toFinset {M : Type*} [AddCommMonoid M] (l : List ℤ) (g : ℤ → M)
    (h : l.toFinset = {-2, -1, 0, 1, 2}) :
    (l.map g).sum = l.count (-2) • g (-2) + l.count (-1) • g (-1) + l.count 0 • g 0 +
      l.count 1 • g 1 + l.count 2 • g 2 := by
  rw [Finset.sum_list_map_count, h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

theorem rootExponents_E6 (i : Fin Tag.E6.rank) :
    (rootExponents .E6 i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents .E6 i).count (-2) = 1 ∧
      (rootExponents .E6 i).count (-1) = 20 ∧ (rootExponents .E6 i).count 0 = 30 ∧
      (rootExponents .E6 i).count 1 = 20 ∧ (rootExponents .E6 i).count 2 = 1 := by
  revert i
  decide +kernel

theorem rootExponents_E7 (i : Fin Tag.E7.rank) :
    (rootExponents .E7 i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents .E7 i).count (-2) = 1 ∧
      (rootExponents .E7 i).count (-1) = 32 ∧ (rootExponents .E7 i).count 0 = 60 ∧
      (rootExponents .E7 i).count 1 = 32 ∧ (rootExponents .E7 i).count 2 = 1 := by
  revert i
  decide +kernel

theorem rootExponents_E8 (i : Fin Tag.E8.rank) :
    (rootExponents .E8 i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents .E8 i).count (-2) = 1 ∧
      (rootExponents .E8 i).count (-1) = 56 ∧ (rootExponents .E8 i).count 0 = 126 ∧
      (rootExponents .E8 i).count 1 = 56 ∧ (rootExponents .E8 i).count 2 = 1 := by
  revert i
  decide +kernel

theorem sum_torusEigen_of_counts (i : Fin τ.rank) (c : Lˣ) {b m : ℕ}
    (h : (rootExponents τ i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents τ i).count (-2) = 1 ∧
      (rootExponents τ i).count (-1) = b ∧ (rootExponents τ i).count 0 = m ∧
      (rootExponents τ i).count 1 = b ∧ (rootExponents τ i).count 2 = 1) :
    ∑ b' : Label τ, torusEigen i c b' =
      ((c : L) + (c⁻¹ : Lˣ)) ^ 2 + b * ((c : L) + (c⁻¹ : Lˣ)) + (τ.rank + m - 2) := by
  obtain ⟨hset, h2, h1, h0, h1', h2'⟩ := h
  rw [sum_torusEigen, sum_isRoot_eq_rootExponents i (fun n => ((c ^ n : Lˣ) : L)),
    list_sum_map_eq_of_toFinset _ _ hset, h2, h1, h0, h1', h2']
  simp only [Units.val_zpow_eq_zpow_val, nsmul_eq_mul, Nat.cast_one, one_mul, zpow_zero,
    Units.val_one, mul_one]
  have hc : (c : L) ≠ 0 := c.ne_zero
  rw [Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem isUpperUnitriangular_xUnit (i : Fin τ.rank) (s : L) :
    IsUpperUnitriangular (xUnit τ L i s : Module.End L (RootModule τ L)) :=
  ((positive_root_triangularity.{0, 0} τ).1 L).1 _ (xUnit_mem_posUnipotent i s)

theorem trace_simpleRootSL2_HSL_mul_uSL (i : Fin τ.rank) (c : Lˣ) (s : L) {b m : ℕ}
    (h : (rootExponents τ i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents τ i).count (-2) = 1 ∧
      (rootExponents τ i).count (-1) = b ∧ (rootExponents τ i).count 0 = m ∧
      (rootExponents τ i).count 1 = b ∧ (rootExponents τ i).count 2 = 1) :
    LinearMap.trace L (RootModule τ L)
        (simpleRootSL2 τ L i (HSL c * uSL s) : Module.End L (RootModule τ L)) =
      ((c : L) + (c⁻¹ : Lˣ)) ^ 2 + b * ((c : L) + (c⁻¹ : Lˣ)) + (τ.rank + m - 2) := by
  rw [map_mul, simpleRootSL2_HSL, simpleRootSL2_uSL, Units.val_mul,
    trace_torusElt_mul_of_isUpperUnitriangular i c (isUpperUnitriangular_xUnit i s),
    sum_torusEigen_of_counts i c h]

theorem baseChangeGL_simpleRootSL2 {K : Type} [Field K] (f : K →+* L) (i : Fin τ.rank)
    (A : SL2 K) :
    baseChangeGL f (simpleRootSL2 τ K i A) =
      simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f A) := by
  have h : (baseChangeGL f).comp (simpleRootSL2 τ K i) =
      (simpleRootSL2 τ L i).comp (Matrix.SpecialLinearGroup.map f) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change baseChangeGL f (simpleRootSL2 τ K i (uSL c)) =
          simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f (uSL c))
        rw [simpleRootSL2_uSL, baseChangeGL_xUnit, map_uSL, simpleRootSL2_uSL]
      · change baseChangeGL f (simpleRootSL2 τ K i (vSL c)) =
          simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f (vSL c))
        rw [simpleRootSL2_vSL, baseChangeGL_yUnit, map_vSL, simpleRootSL2_vSL]
  exact DFunLike.congr_fun h A

theorem trace_baseChangeGL {K : Type} [Field K] (f : K →+* L) (g : ModGL τ K) :
    LinearMap.trace L (RootModule τ L) (baseChangeGL f g : Module.End L (RootModule τ L)) =
      f (LinearMap.trace K (RootModule τ K) (g : Module.End K (RootModule τ K))) := by
  rw [trace_rootModule_eq_sum, trace_rootModule_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [baseChangeGL_apply_single, Finsupp.mapRange_apply]

theorem exists_conj_lower_eq_zero (A : SL2 L)
    (hc : ∃ c : L, c ^ 2 - (A : Matrix (Fin 2) (Fin 2) L).trace * c + 1 = 0) :
    ∃ Q : SL2 L, ((Q⁻¹ * A * Q : SL2 L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  obtain ⟨c, hc⟩ := hc
  have hdet := det_SL2 A
  rw [Matrix.trace_fin_two] at hc
  by_cases hb : (A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0
  · refine ⟨WSL, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_WSL, Matrix.mul_apply,
      Fin.sum_univ_two, hb, Matrix.vecMul, dotProduct]
  · set a := (A : Matrix (Fin 2) (Fin 2) L) 0 0
    set b := (A : Matrix (Fin 2) (Fin 2) L) 0 1
    let Q : SL2 L := ⟨!![b, 0; c - a, b⁻¹], by simp [Matrix.det_fin_two, hb]⟩
    have hQ : (Q : Matrix (Fin 2) (Fin 2) L) = !![b, 0; c - a, b⁻¹] := rfl
    refine ⟨Q, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, hQ, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (-b) * hc - b * hdet

theorem exists_conj_lower_eq_zero_of_isAlgClosed [IsAlgClosed L] (A : SL2 L) :
    ∃ Q : SL2 L, ((Q⁻¹ * A * Q : SL2 L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  refine exists_conj_lower_eq_zero A ?_
  set t := (A : Matrix (Fin 2) (Fin 2) L).trace
  have hdeg : (X ^ 2 - C t * X + 1 : L[X]).degree = 2 := by compute_degree!
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (X ^ 2 - C t * X + 1 : L[X])
    (by rw [hdeg]; exact two_ne_zero)
  refine ⟨c, ?_⟩
  simpa using hc

theorem trace_simpleRootSL2_of_counts {k : Type} [Field k] (i : Fin τ.rank) {b m : ℕ}
    (h : (rootExponents τ i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents τ i).count (-2) = 1 ∧
      (rootExponents τ i).count (-1) = b ∧ (rootExponents τ i).count 0 = m ∧
      (rootExponents τ i).count 1 = b ∧ (rootExponents τ i).count 2 = 1) (A : SL2 k) :
    LinearMap.trace k (RootModule τ k) (simpleRootSL2 τ k i A : Module.End k (RootModule τ k)) =
      (A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 + b * (A : Matrix (Fin 2) (Fin 2) k).trace +
        (τ.rank + m - 2) := by
  set L := AlgebraicClosure k
  set f : k →+* L := algebraMap k L
  apply f.injective
  rw [← trace_baseChangeGL, baseChangeGL_simpleRootSL2]
  set A' := Matrix.SpecialLinearGroup.map f A
  obtain ⟨Q, hQ⟩ := exists_conj_lower_eq_zero_of_isAlgClosed A'
  set B := Q⁻¹ * A' * Q with hB
  have hA' : A' = Q * B * Q⁻¹ := by rw [hB]; group
  have hBe := eq_HSL_mul_uSL hQ
  set u := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hQ)
  set s := (B : Matrix (Fin 2) (Fin 2) L) 0 1 / (B : Matrix (Fin 2) (Fin 2) L) 0 0
  have htr : f (A : Matrix (Fin 2) (Fin 2) k).trace = (u : L) + (u⁻¹ : Lˣ) := by
    have h1 : f (A : Matrix (Fin 2) (Fin 2) k).trace = (A' : Matrix (Fin 2) (Fin 2) L).trace := by
      simp [A', Matrix.trace_fin_two]
    have h2 : (A' : Matrix (Fin 2) (Fin 2) L).trace = (B : Matrix (Fin 2) (Fin 2) L).trace := by
      rw [hA', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, one_mul]
    rw [h1, h2, hBe, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two]
    simp [coe_HSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hA', map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
    LinearMap.trace_conj, hBe, trace_simpleRootSL2_HSL_mul_uSL i u s h, map_add, map_add, map_pow,
    map_mul, htr, map_natCast, map_sub, map_add, map_natCast, map_natCast, map_ofNat]

theorem closure_range_quadratic_eq_top {k : Type*} [Field k] [Finite k] (b z : k)
    (hb : ringChar k = 2 → b = 0) :
    Subfield.closure (Set.range fun t : k => t ^ 2 + b * t + z) = ⊤ := by
  classical
  have := Fintype.ofFinite k
  set P := fun t : k => t ^ 2 + b * t + z with hP
  set F := Subfield.closure (Set.range P)
  have hfib : ∀ t₀ t, P t = P t₀ → t = t₀ ∨ t = -t₀ - b := by
    intro t₀ t h
    have h' : (t - t₀) * (t + t₀ + b) = 0 := by
      simp only [hP] at h
      linear_combination h
    rcases mul_eq_zero.1 h' with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  have himage : Fintype.card k < 2 * (Finset.univ.image P).card := by
    have hpos : 0 < Fintype.card k := Fintype.card_pos
    by_cases h2 : ringChar k = 2
    · have : CharP k 2 := ringChar.of_eq h2
      have hinj : Function.Injective P := fun t t' h => by
        rcases hfib t' t h with h | h
        · exact h
        · rw [hb h2, sub_zero, CharTwo.neg_eq] at h
          exact h
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      omega
    · have hodd := FiniteField.odd_card_of_char_ne_two h2
      have hle : (Finset.univ : Finset k).card ≤ 2 * (Finset.univ.image P).card := by
        refine Finset.card_le_mul_card_image _ 2 fun y hy => ?_
        obtain ⟨t₀, -, rfl⟩ := Finset.mem_image.1 hy
        calc (Finset.univ.filter fun t => P t = P t₀).card ≤ ({t₀, -t₀ - b} : Finset k).card :=
              Finset.card_le_card fun t ht => by
                rcases hfib t₀ t (Finset.mem_filter.1 ht).2 with h | h <;> simp [h]
          _ ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at hle
      omega
  have hF : (Finset.univ.image P).card ≤ Nat.card F := by
    have hsub : (↑(Finset.univ.image P) : Set k) ⊆ (F : Set k) := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
      exact Subfield.subset_closure ⟨t, rfl⟩
    calc (Finset.univ.image P).card = (↑(Finset.univ.image P) : Set k).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (F : Set k).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card F := (Nat.card_coe_set_eq _).symm
  obtain ⟨m, hm⟩ := AddSubgroup.card_addSubgroup_dvd_card F.toAddSubgroup
  have hcardF : Nat.card F.toAddSubgroup = Nat.card F := rfl
  rw [hcardF, Nat.card_eq_fintype_card] at hm
  have hm1 : m = 1 := by
    rcases m with _ | _ | m
    · rw [mul_zero] at hm
      exact absurd hm Fintype.card_ne_zero
    · rfl
    · nlinarith
  rw [hm1, mul_one] at hm
  have htop : F.toAddSubgroup = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [hcardF, Nat.card_eq_fintype_card (α := k), hm])
  exact eq_top_iff.2 fun x _ => by
    have hx : x ∈ F.toAddSubgroup := htop ▸ AddSubgroup.mem_top x
    exact hx

@[expose] def conjGL {M : Type*} [Field M] (P : GL (Fin 2) M) (A : SL2 M) : SL2 M :=
  ⟨(P : Matrix (Fin 2) (Fin 2) M) * A * ((P⁻¹ : GL (Fin 2) M) : Matrix (Fin 2) (Fin 2) M), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem trace_conjGL {M : Type*} [Field M] (P : GL (Fin 2) M) (A : SL2 M) :
    ((conjGL P A : SL2 M) : Matrix (Fin 2) (Fin 2) M).trace =
      (A : Matrix (Fin 2) (Fin 2) M).trace := by
  change ((P : Matrix (Fin 2) (Fin 2) M) * A *
    ((P⁻¹ : GL (Fin 2) M) : Matrix (Fin 2) (Fin 2) M)).trace = _
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

@[expose] def companionSL {k : Type*} [Field k] (t : k) : SL2 k :=
  ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩

theorem trace_companionSL {k : Type*} [Field k] (t : k) :
    ((companionSL t : SL2 k) : Matrix (Fin 2) (Fin 2) k).trace = t := by
  simp [companionSL, Matrix.trace_fin_two]

@[expose] def eRootTracePoly : Tag → ℤ[X]
  | .E6 => X ^ 2 + 20 * X + 34
  | .E7 => X ^ 2 + 32 * X + 65
  | .E8 => X ^ 2 + 56 * X + 132
  | _ => 0

theorem trace_simpleRootSL2_eq_aeval {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (k : Type)
    [Field k] (i : Fin τ.rank) (A : SL2 k) :
    LinearMap.trace k (RootModule τ k) (simpleRootSL2 τ k i A : Module.End k (RootModule τ k)) =
      aeval (A : Matrix (Fin 2) (Fin 2) k).trace (eRootTracePoly τ) := by
  rcases hτ with rfl | rfl | rfl
  · rw [trace_simpleRootSL2_of_counts i (rootExponents_E6 i) A]
    simp only [eRootTracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat]
    norm_num [Tag.rank]
  · rw [trace_simpleRootSL2_of_counts i (rootExponents_E7 i) A]
    simp only [eRootTracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat]
    norm_num [Tag.rank]
  · rw [trace_simpleRootSL2_of_counts i (rootExponents_E8 i) A]
    simp only [eRootTracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat]
    norm_num [Tag.rank]

theorem closure_range_eRootTracePoly {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (k : Type)
    [Field k] [Finite k] :
    Subfield.closure (Set.range fun t : k => aeval t (eRootTracePoly τ)) = ⊤ := by
  have h2 : ∀ n : ℕ, ringChar k = 2 → ((2 * n : ℕ) : k) = 0 := fun n h => by
    have : CharP k 2 := ringChar.of_eq h
    rw [Nat.cast_mul, Nat.cast_two, CharTwo.two_eq_zero, zero_mul]
  rcases hτ with rfl | rfl | rfl
  · convert closure_range_quadratic_eq_top (20 : k) 34 fun h => by exact_mod_cast h2 10 h using 3
    funext t
    simp only [eRootTracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat]
  · convert closure_range_quadratic_eq_top (32 : k) 65 fun h => by exact_mod_cast h2 16 h using 3
    funext t
    simp only [eRootTracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat]
  · convert closure_range_quadratic_eq_top (56 : k) 132 fun h => by exact_mod_cast h2 28 h using 3
    funext t
    simp only [eRootTracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat]

theorem ordinary_E_root_SL2_full_module_traces_all_characteristics (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ (k : Type) [Field k] (i : Fin τ.rank) (A : SL2 k),
      LinearMap.trace k (RootModule τ k) (simpleRootSL2 τ k i A : Module.End k (RootModule τ k)) =
        aeval (A : Matrix (Fin 2) (Fin 2) k).trace (eRootTracePoly τ)) ∧
    ∀ (k : Type) [Field k] [Finite k] (M : Type) [Field M] [Algebra k M] (i : Fin τ.rank)
      (P : GL (Fin 2) M) (g : ModGL τ M),
      Subfield.closure {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule τ M)
        ((g * simpleRootSL2 τ M i (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap k M) A)) *
          g⁻¹ : ModGL τ M) : Module.End M (RootModule τ M))} = (algebraMap k M).fieldRange := by
  refine ⟨fun k _ i A => trace_simpleRootSL2_eq_aeval hτ k i A, fun k _ _ M _ _ i P g => ?_⟩
  set f : k →+* M := algebraMap k M
  have hval : ∀ A : SL2 k, LinearMap.trace M (RootModule τ M)
      ((g * simpleRootSL2 τ M i (conjGL P (Matrix.SpecialLinearGroup.map f A)) *
        g⁻¹ : ModGL τ M) : Module.End M (RootModule τ M)) =
      f (aeval (A : Matrix (Fin 2) (Fin 2) k).trace (eRootTracePoly τ)) := by
    intro A
    rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj, trace_simpleRootSL2_eq_aeval hτ M,
      trace_conjGL]
    have htr : ((Matrix.SpecialLinearGroup.map f A : SL2 M) : Matrix (Fin 2) (Fin 2) M).trace =
        f (A : Matrix (Fin 2) (Fin 2) k).trace := by
      simp [Matrix.trace_fin_two]
    rw [htr]
    exact aeval_algebraMap_apply M _ _
  have hS : {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule τ M)
      ((g * simpleRootSL2 τ M i (conjGL P (Matrix.SpecialLinearGroup.map f A)) *
        g⁻¹ : ModGL τ M) : Module.End M (RootModule τ M))} =
      f '' Set.range fun t : k => aeval t (eRootTracePoly τ) := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, (hval A).symm⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      refine ⟨companionSL t, ?_⟩
      rw [hval, trace_companionSL]
  rw [hS, ← RingHom.map_field_closure, closure_range_eRootTracePoly hτ k,
    RingHom.fieldRange_eq_map]

end CFSG.RankThree.Chevalley
