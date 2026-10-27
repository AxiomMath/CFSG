module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryMat
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithField
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryGen

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec14.Item148Rank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)

variable {p f : ℕ} {K : Type} [Field K]

section Map

variable {k : Subfield K}

theorem map_eigen {W P : GL (Fin 3) k} {C : Matrix (Fin 3) (Fin 3) k}
    (hWP : (W : Matrix (Fin 3) (Fin 3) k) * P = P * C) :
    ((GeneralLinearGroup.map k.subtype W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (GeneralLinearGroup.map k.subtype P : GL (Fin 3) K) =
      (GeneralLinearGroup.map k.subtype P : GL (Fin 3) K) * C.map k.subtype := by
  have hmap : ∀ g : GL (Fin 3) k, ((GeneralLinearGroup.map k.subtype g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) k).map k.subtype := fun g => by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [hmap, hmap, ← Matrix.map_mul, hWP, Matrix.map_mul]

theorem diagonal_map_subtype (d : Fin 3 → k) :
    (diagonal d).map k.subtype = diagonal (fun i => (d i : K)) :=
  diagonal_map (map_zero _)

theorem commute_of_eigen {W Q D : GL (Fin 3) K} {Δ : Matrix (Fin 3) (Fin 3) K}
    (hWQ : (W : Matrix (Fin 3) (Fin 3) K) * Q = Q * Δ)
    (hΔD : Δ * (D : Matrix (Fin 3) (Fin 3) K) = D * Δ) :
    W * (Q * D * Q⁻¹) = (Q * D * Q⁻¹) * W := by
  apply Units.ext
  simp only [Units.val_mul]
  exact Item19Res5Proof.commute_of_intertwine hWQ (Units.mul_inv Q) (Units.inv_mul Q) hΔD

theorem cyc_map_subtype (a b c : k) :
    (!![0, 0, a; b, 0, 0; 0, c, 0] : Matrix (Fin 3) (Fin 3) k).map k.subtype =
      !![0, 0, (a : K); (b : K), 0, 0; 0, (c : K), 0] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

end Map

theorem smul_companion_mul_diagonal {F : Type*} [Field F] (c α : F) (s : Fin 3 → F)
    (hs : ∀ i, s i ≠ 0) :
    (c • !![0, 0, α; 1, 0, 0; 0, 1, 0]) * diagonal s =
      diagonal s * !![0, 0, (s 0)⁻¹ * (c * α) * s 2; (s 1)⁻¹ * c * s 0, 0, 0;
        0, (s 2)⁻¹ * c * s 1, 0] := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem psuField_fix_of_mem {h : UnitaryFieldData p f K} {σ : K ≃+* K} {k : Subfield K}
    (hk : ∀ x, x ∈ k ↔ σ x = x) (g : unitarySU p f K 3)
    (hg : ∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) :
    psuField h σ (unitaryProj h 3 g) = unitaryProj h 3 g := by
  change psuField h σ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  apply Units.ext
  rw [coe_glAut]
  ext i j
  exact (hk _).1 (hg i j)

theorem closure_fix_eq_top_toral (h : UnitaryFieldData p f K)
    {e : ℕ} (hfe : f = 3 * e) (hq : p ^ e % 3 = 2) (hqne : p ^ e ≠ 2) {σ : K ≃+* K}
    {k : Subfield K} (hk : ∀ x, x ∈ k ↔ σ x = x) (h₀ : UnitaryFieldData p e k)
    (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))
    {B : Subgroup (MulAut (unitaryPSU h 3))} (hB3 : ∀ z ∈ B, z ^ 3 = 1)
    (x y : unitaryIsom3 h₀)
    (hxB : psuConj h (subIsom h h₀ hbar x) ∈ B) (hyB : psuConj h (subIsom h h₀ hbar y) ∈ B)
    (hxy : psuConj h (subIsom h h₀ hbar x) * psuConj h (subIsom h h₀ hbar y) =
      psuConj h (subIsom h h₀ hbar y) * psuConj h (subIsom h h₀ hbar x))
    (hx1 : psuConj h (subIsom h h₀ hbar x) ≠ 1)
    (hyz : psuConj h (subIsom h h₀ hbar y) ∉
      Subgroup.zpowers (psuConj h (subIsom h h₀ hbar x)))
    {P : GL (Fin 3) k}
    (hP : ∀ i j, i ≠ j →
      ((P * (x : GL (Fin 3) k) * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j = 0 ∧
      ((P * (y : GL (Fin 3) k) * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j = 0)
    {α β : kˣ} (hx3 : (x : GL (Fin 3) k) ^ 3 = GeneralLinearGroup.scalar (Fin 3) α)
    (hy3 : (y : GL (Fin 3) k) ^ 3 = GeneralLinearGroup.scalar (Fin 3) β)
    (hind : ∀ a b : ℕ, (∃ c : kˣ, (x : GL (Fin 3) k) ^ a * (y : GL (Fin 3) k) ^ b =
      GeneralLinearGroup.scalar (Fin 3) c) → 3 ∣ a ∧ 3 ∣ b)
    {u : K} (huN : h.norm u = 1) (huk : u ∉ k) :
    ∃ F₀ : Subgroup (MulAut (unitaryPSU h 3)), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({z | psuField h σ z = z} ∪ {z | ∀ φ ∈ F₀, φ z = z}) = ⊤ := by
  classical
  have := h.finite
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at huN
    exact zero_ne_one huN
  set dx : Fin 3 → k := fun i =>
    ((P * (x : GL (Fin 3) k) * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i with hdxdef
  set dy : Fin 3 → k := fun i =>
    ((P * (y : GL (Fin 3) k) * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i with hdydef
  have hdx : ((P * (x : GL (Fin 3) k) * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      diagonal dx := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp [dx]
    · rw [diagonal_apply_ne _ hij]
      exact (hP i j hij).1
  have hdy : ((P * (y : GL (Fin 3) k) * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      diagonal dy := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp [dy]
    · rw [diagonal_apply_ne _ hij]
      exact (hP i j hij).2
  have heig : ∀ (z : GL (Fin 3) k) (d : Fin 3 → k),
      ((P * z * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d →
      (z : Matrix (Fin 3) (Fin 3) k) * ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
    intro z d hz
    rw [← hz, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hxQ := heig _ dx hdx
  have hyQ := heig _ dy hdy
  have hcube : ∀ (z : GL (Fin 3) k) (d : Fin 3 → k) (c : kˣ),
      ((P * z * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d →
      z ^ 3 = GeneralLinearGroup.scalar (Fin 3) c → ∀ i, d i ^ 3 = c := by
    intro z d c hz hz3 i
    have h1 : ((P * z * P⁻¹ : GL (Fin 3) k) ^ 3 : GL (Fin 3) k) =
        GeneralLinearGroup.scalar (Fin 3) c := by
      rw [conj_pow, hz3, (commute_scalar c P).eq, mul_inv_cancel_right]
    have h2 := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) i i) h1
    simp only [Units.val_pow_eq_pow_val, hz, diagonal_pow, GeneralLinearGroup.coe_scalar,
      scalar_apply, diagonal_apply_eq, Pi.pow_apply] at h2
    exact h2
  have hdx3 := hcube _ dx α hdx hx3
  have hdy3 := hcube _ dy β hdy hy3
  have hαN : h₀.norm (α : k) = 1 := norm_eq_one_of_scalar_mem (hx3 ▸ pow_mem x.2 3)
  have hβN : h₀.norm (β : k) = 1 := norm_eq_one_of_scalar_mem (hy3 ▸ pow_mem y.2 3)
  have hdxN : ∀ i, h₀.norm (dx i) = 1 := fun i => norm_eq_one_of_pow_three h₀ hq hαN (hdx3 i)
  have hdyN : ∀ i, h₀.norm (dy i) = 1 := fun i => norm_eq_one_of_pow_three h₀ hq hβN (hdy3 i)
  have hG : ∀ i j, i ≠ j →
      gram h₀ ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j = 0 := by
    intro i j hij
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have := i.isLt
    have := j.isLt
    obtain ⟨l, hil, hjl⟩ : ∃ l : Fin 3, i ≠ l ∧ j ≠ l :=
      ⟨⟨3 - i - j, by omega⟩, fun h => by
        have := congrArg Fin.val h
        simp only at this
        omega, fun h => by
        have := congrArg Fin.val h
        simp only at this
        omega⟩
    rcases toral_joint_ne hdx hdy hdx3 hdy3 hind hij hil hjl with hne | hne
    · exact gram_eq_zero_of_eigen h₀ x.2 hxQ (bar_mul_ne_one_of_ne h₀ (hdxN i) hne)
    · exact gram_eq_zero_of_eigen h₀ y.2 hyQ (bar_mul_ne_one_of_ne h₀ (hdyN i) hne)
  obtain ⟨Q', s, hs0, hQ's, hQ'U⟩ := exists_unitary_rescale h₀ hG
  have hrescale : ∀ (z : GL (Fin 3) k) (d : Fin 3 → k),
      (z : Matrix (Fin 3) (Fin 3) k) * ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * diagonal d →
      (z : Matrix (Fin 3) (Fin 3) k) * Q' = Q' * diagonal d := by
    intro z d hz
    rw [hQ's, ← Matrix.mul_assoc, hz, Matrix.mul_assoc, Matrix.mul_assoc,
      Item19Res5Proof.diagonal_mul_comm]
  have hxQ' := hrescale _ dx hxQ
  have hyQ' := hrescale _ dy hyQ
  obtain ⟨D, hD⟩ := exists_diag_mem h ![u, 1, u⁻¹]
    (by
      intro i
      fin_cases i
      · exact huN
      · show h.norm 1 = 1
        simp [UnitaryFieldData.norm]
      · show h.norm u⁻¹ = 1
        rw [norm_inv_eq h, huN, inv_one])
    (by
      show u * 1 * u⁻¹ = 1
      field_simp)
  have hQ'K : GeneralLinearGroup.map k.subtype Q' ∈ unitaryIsom3 h :=
    (mem_unitaryIsom3_map_iff h h₀ hbar Q').2 hQ'U
  set t : unitarySU p f K 3 := ⟨GeneralLinearGroup.map k.subtype Q' * D *
    (GeneralLinearGroup.map k.subtype Q')⁻¹, conj_mem_unitarySU hQ'K D.2⟩ with ht
  have hfixt : ∀ (z : unitaryIsom3 h₀) (d : Fin 3 → k),
      ((z : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * Q' = Q' * diagonal d →
      psuConj h (subIsom h h₀ hbar z) (unitaryProj h 3 t) = unitaryProj h 3 t := by
    intro z d hz
    refine psuConj_fix_of_commute _ t ?_
    have h1 := map_eigen hz
    rw [diagonal_map_subtype] at h1
    exact commute_of_eigen h1 (by rw [hD]; exact Item19Res5Proof.diagonal_mul_comm _ _)
  obtain ⟨F₀, hF₀⟩ : ∃ F : Subgroup (MulAut (unitaryPSU h 3)),
      F = Subgroup.closure ({psuConj h (subIsom h h₀ hbar x), psuConj h (subIsom h h₀ hbar y)} :
        Set (MulAut (unitaryPSU h 3))) := ⟨_, rfl⟩
  have hF₀B : F₀ ≤ B := by
    rw [hF₀, Subgroup.closure_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxB
    · rw [Set.mem_singleton_iff.1 hz]
      exact hyB
  refine ⟨F₀, hF₀B, ?_, ?_⟩
  · rw [hF₀]
    exact Item19Res5Proof.card_closure_eq_nine hxy (hB3 _ hxB) (hB3 _ hyB) hx1 hyz
      (fun z hz => hB3 z (hF₀B (hF₀ ▸ hz)))
  have htF : unitaryProj h 3 t ∈ {z | ∀ φ ∈ F₀, φ z = z} := by
    intro φ hφ
    have hle : F₀ ≤ MulAction.stabilizer (MulAut (unitaryPSU h 3)) (unitaryProj h 3 t) := by
      rw [hF₀, Subgroup.closure_le]
      intro z hz
      rcases hz with hz | hz
      · rw [hz, SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hfixt x dx hxQ'
      · rw [Set.mem_singleton_iff.1 hz, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
          MulAut.smul_def]
        exact hfixt y dy hyQ'
    have := hle hφ
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup (unitaryPSU h 3),
      Y = Subgroup.closure ({z | psuField h σ z = z} ∪ {z | ∀ φ ∈ F₀, φ z = z}) := ⟨_, rfl⟩
  have hYk : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        unitaryProj h 3 g ∈ Y :=
    fun g hg => hY ▸ Subgroup.subset_closure (Or.inl (psuField_fix_of_mem hk g hg))
  have htY : unitaryProj h 3 t ∈ Y := hY ▸ Subgroup.subset_closure (Or.inr htF)
  rw [← hY]
  refine eq_top_of_conj_not_mem h h₀ hbar hfe hqne hYk t htY
    (exists_conj_not_mem h h₀ hbar Q' hQ'U D hD ?_)
  show u * (1 : K)⁻¹ ∉ k
  rwa [inv_one, mul_one]

theorem closure_fix_eq_top_heis (h : UnitaryFieldData p f K)
    {e : ℕ} (hfe : f = 3 * e) (hq : p ^ e % 3 = 2) (hqne : p ^ e ≠ 2) {σ : K ≃+* K}
    (hσσσ : ∀ x, σ (σ (σ x)) = x) {k : Subfield K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    (h₀ : UnitaryFieldData p e k) (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))
    {B : Subgroup (MulAut (unitaryPSU h 3))} (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB3 : ∀ z ∈ B, z ^ 3 = 1) (hσB : psuField h σ ∈ B)
    (hσD : psuField h σ ∉ (psuConj h).range)
    (Wx Wy : unitaryIsom3 h₀) (hWxB : psuConj h (subIsom h h₀ hbar Wx) ∈ B)
    (hWyB : psuConj h (subIsom h h₀ hbar Wy) ∈ B)
    {P : GL (Fin 3) k} {μ w α₀ c : k} (hw : IsPrimitiveRoot w 3)
    (hWyP : ((Wy : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * P =
      P * diagonal ![μ, μ * w, μ * w ^ 2])
    (hWxP : ((Wx : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * P =
      P * (c • !![0, 0, α₀; 1, 0, 0; 0, 1, 0]))
    {u : K} (huN : h.norm u = 1) (huσ : u * σ u * σ (σ u) = 1) (huk : u * (σ u)⁻¹ ∉ k) :
    ∃ F₀ : Subgroup (MulAut (unitaryPSU h 3)), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({z | psuField h σ z = z} ∪ {z | ∀ φ ∈ F₀, φ z = z}) = ⊤ := by
  classical
  have := h.finite
  have hw3 : w ^ 3 = 1 := hw.pow_eq_one
  have hμN : h₀.norm μ = 1 := by
    refine norm_eq_one_of_pow_three h₀ hq (norm_det_eq_one Wy.2) ?_
    have h1 := congrArg Matrix.det hWyP
    rw [det_mul, det_mul, det_diagonal, Fin.prod_univ_three] at h1
    have hdetP : (P : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
    have h2 : ((Wy : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det =
        ![μ, μ * w, μ * w ^ 2] 0 * ![μ, μ * w, μ * w ^ 2] 1 * ![μ, μ * w, μ * w ^ 2] 2 :=
      mul_right_cancel₀ hdetP (h1.trans (mul_comm _ _))
    rw [h2]
    show μ ^ 3 = μ * (μ * w) * (μ * w ^ 2)
    linear_combination (-μ ^ 3) * hw3
  have hG : ∀ i j, i ≠ j → gram h₀ (P : Matrix (Fin 3) (Fin 3) k) i j = 0 := fun i j hij =>
    gram_eq_zero_of_eigen h₀ Wy.2 hWyP (heis_bar_mul_ne_one h₀ hq hμN hw hij)
  obtain ⟨Q', s, hs0, hQ's, hQ'U⟩ := exists_unitary_rescale h₀ hG
  have hWyQ' : ((Wy : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * Q' =
      Q' * diagonal ![μ, μ * w, μ * w ^ 2] := by
    rw [hQ's, ← Matrix.mul_assoc, hWyP, Matrix.mul_assoc, Matrix.mul_assoc,
      Item19Res5Proof.diagonal_mul_comm]
  have hWxQ' : ((Wx : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * Q' =
      Q' * !![0, 0, (s 0)⁻¹ * (c * α₀) * s 2; (s 1)⁻¹ * c * s 0, 0, 0;
        0, (s 2)⁻¹ * c * s 1, 0] := by
    rw [hQ's, ← Matrix.mul_assoc, hWxP, Matrix.mul_assoc,
      smul_companion_mul_diagonal _ _ s hs0, ← Matrix.mul_assoc]
  have hNσ : ∀ v : K, h.norm (σ v) = σ (h.norm v) := by
    intro v
    rw [UnitaryFieldData.norm, UnitaryFieldData.norm, map_mul,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ v]
  obtain ⟨D, hD⟩ := exists_diag_mem h ![u, σ u, σ (σ u)]
    (by
      intro i
      fin_cases i
      · exact huN
      · show h.norm (σ u) = 1
        rw [hNσ, huN, map_one]
      · show h.norm (σ (σ u)) = 1
        rw [hNσ, hNσ, huN, map_one, map_one])
    (by
      show u * σ u * σ (σ u) = 1
      exact huσ)
  have hQ'K : GeneralLinearGroup.map k.subtype Q' ∈ unitaryIsom3 h :=
    (mem_unitaryIsom3_map_iff h h₀ hbar Q').2 hQ'U
  set t : unitarySU p f K 3 := ⟨GeneralLinearGroup.map k.subtype Q' * D *
    (GeneralLinearGroup.map k.subtype Q')⁻¹, conj_mem_unitarySU hQ'K D.2⟩ with ht
  have hfix1 : psuConj h (subIsom h h₀ hbar Wy) (unitaryProj h 3 t) = unitaryProj h 3 t := by
    refine psuConj_fix_of_commute _ t ?_
    have h1 := map_eigen hWyQ'
    rw [diagonal_map_subtype] at h1
    exact commute_of_eigen h1 (by rw [hD]; exact Item19Res5Proof.diagonal_mul_comm _ _)
  have hfix2 : (psuField h σ * psuConj h (subIsom h h₀ hbar Wx)) (unitaryProj h 3 t) =
      unitaryProj h 3 t := by
    refine psuField_mul_psuConj_fix σ _ t ?_
    have h1 := map_eigen hWxQ'
    rw [cyc_map_subtype] at h1
    exact glAut_conj_twisted hσσσ (Item19Res5Proof.glAut_map_subtype hk Q')
      (Item19Res5Proof.glAut_map_subtype hk Wx) h1 hD
  have hcxB : psuField h σ * psuConj h (subIsom h h₀ hbar Wx) ∈ B := B.mul_mem hσB hWxB
  have hcy1 : psuConj h (subIsom h h₀ hbar Wy) ≠ 1 := by
    intro h1
    obtain ⟨c₀, hc₀⟩ := exists_scalar_of_psuConj_eq_one h1
    rw [coe_subIsom] at hc₀
    have h2 := map_eigen hWyP
    rw [hc₀, diagonal_map_subtype, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul] at h2
    have hPinv : ((GeneralLinearGroup.map k.subtype P⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (GeneralLinearGroup.map k.subtype P : GL (Fin 3) K) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have h3 : (c₀ : K) • (1 : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i => ((![μ, μ * w, μ * w ^ 2] i : k) : K)) := by
      calc (c₀ : K) • (1 : Matrix (Fin 3) (Fin 3) K)
          = ((GeneralLinearGroup.map k.subtype P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((c₀ : K) • ((GeneralLinearGroup.map k.subtype P : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K)) := by
            rw [Matrix.mul_smul, hPinv]
        _ = _ := by rw [h2, ← Matrix.mul_assoc, hPinv, Matrix.one_mul]
    have h00 := congrFun (congrFun h3 0) 0
    have h11 := congrFun (congrFun h3 1) 1
    simp at h00 h11
    have hμ0 : μ ≠ 0 := by
      rintro h0
      rw [h0, UnitaryFieldData.norm, zero_mul] at hμN
      exact zero_ne_one hμN
    have hw1 : (w : K) = 1 := by
      have h4 : (μ : K) * w = (μ : K) * 1 := by rw [mul_one, ← h11, h00]
      exact mul_left_cancel₀ (fun h0 => hμ0 (Subtype.ext h0)) h4
    exact hw.ne_one (by norm_num) (Subtype.ext hw1)
  have hbz : psuField h σ * psuConj h (subIsom h h₀ hbar Wx) ∉
      Subgroup.zpowers (psuConj h (subIsom h h₀ hbar Wy)) := by
    rintro ⟨m, hm⟩
    apply hσD
    have h1 : psuField h σ = psuConj h (subIsom h h₀ hbar Wy) ^ m *
        (psuConj h (subIsom h h₀ hbar Wx))⁻¹ := by
      simp only at hm
      rw [hm, mul_inv_cancel_right]
    rw [h1, ← map_zpow, ← map_inv, ← map_mul]
    exact ⟨_, rfl⟩
  obtain ⟨F₀, hF₀⟩ : ∃ F : Subgroup (MulAut (unitaryPSU h 3)),
      F = Subgroup.closure ({psuConj h (subIsom h h₀ hbar Wy),
        psuField h σ * psuConj h (subIsom h h₀ hbar Wx)} : Set (MulAut (unitaryPSU h 3))) :=
    ⟨_, rfl⟩
  have hF₀B : F₀ ≤ B := by
    rw [hF₀, Subgroup.closure_le]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      exact hWyB
    · rw [Set.mem_singleton_iff.1 hz]
      exact hcxB
  refine ⟨F₀, hF₀B, ?_, ?_⟩
  · rw [hF₀]
    exact Item19Res5Proof.card_closure_eq_nine (hBab _ hWyB _ hcxB) (hB3 _ hWyB) (hB3 _ hcxB)
      hcy1 hbz (fun z hz => hB3 z (hF₀B (hF₀ ▸ hz)))
  have htF : unitaryProj h 3 t ∈ {z | ∀ φ ∈ F₀, φ z = z} := by
    intro φ hφ
    have hle : F₀ ≤ MulAction.stabilizer (MulAut (unitaryPSU h 3)) (unitaryProj h 3 t) := by
      rw [hF₀, Subgroup.closure_le]
      intro z hz
      rcases hz with hz | hz
      · rw [hz, SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hfix1
      · rw [Set.mem_singleton_iff.1 hz, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
          MulAut.smul_def]
        exact hfix2
    have := hle hφ
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup (unitaryPSU h 3),
      Y = Subgroup.closure ({z | psuField h σ z = z} ∪ {z | ∀ φ ∈ F₀, φ z = z}) := ⟨_, rfl⟩
  have hYk : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        unitaryProj h 3 g ∈ Y :=
    fun g hg => hY ▸ Subgroup.subset_closure (Or.inl (psuField_fix_of_mem hk g hg))
  have htY : unitaryProj h 3 t ∈ Y := hY ▸ Subgroup.subset_closure (Or.inr htF)
  rw [← hY]
  exact eq_top_of_conj_not_mem h h₀ hbar hfe hqne hYk t htY
    (exists_conj_not_mem h h₀ hbar Q' hQ'U D hD huk)

theorem closure_fix_eq_top_field_unitary
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {e : ℕ} (hfe : f = 3 * e)
    (hq2 : 2 < p ^ e) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (B : Subgroup (MulAut (unitaryPSU h 3))) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB3 : ∀ x ∈ B, x ^ 3 = 1) (hB27 : Nat.card B = 27) (hσB : psuField h σ ∈ B) :
    ∃ F₀ : Subgroup (MulAut (unitaryPSU h 3)), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({x | psuField h σ x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) = ⊤ := by
  classical
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by rintro rfl; rw [orderOf_one] at hσ; omega
  have hσσσ : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσ3
    simpa [pow_succ] using this
  have hQ2 : 2 < p ^ f := by
    rw [hfe, pow_mul']
    exact lt_of_lt_of_le hq2 (Nat.le_self_pow (by norm_num) _)
  obtain ⟨e', hfe', he', hkcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  obtain rfl : e' = e := by omega
  have h₀ : UnitaryFieldData p e' (fixedField σ) := ⟨h.prime, he', hkcard⟩
  have hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K) :=
    bar_coe_fixedField h hfe h₀
  have hk : ∀ x, x ∈ fixedField σ ↔ σ x = x := mem_fixedField_iff σ
  have hq : p ^ e' % 3 = 2 := by
    have h1 : (p ^ e') ^ 3 % 3 = p ^ e' % 3 := pow_three_mod_three148 _
    rw [← h1, ← pow_mul, mul_comm, ← hfe]
    exact hQ
  have hqne : p ^ e' ≠ 2 := by omega
  have : Finite (fixedField σ) := Subtype.finite
  have hkF3 : 3 ∣ Nat.card (fixedField σ) - 1 := by
    rw [hkcard]
    have h1 : p ^ (2 * e') % 3 = 1 := by rw [pow_mul', Nat.pow_mod, hq]
    have h2 : 1 ≤ p ^ (2 * e') := Nat.one_le_pow _ _ h.prime.pos
    omega
  have hζ := Item19Res5Proof.exists_isPrimitiveRoot_three hkF3
  have hfσ3 : psuField h σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hfσin : ¬ IsInnerAut (psuField h σ) := not_isInnerAut_psuField hσ1
  have hfσD : psuField h σ ∉ (psuConj h).range := psuField_not_mem_psuConj_range hσ1
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (MulAut (unitaryPSU h 3)),
      A = B ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := ⟨_, rfl⟩
  have hAB : A ≤ B := hA ▸ inf_le_left
  have hcoset : ∀ β ∈ B, ∃ j : ℕ, j < 3 ∧ β * psuField h σ ^ j ∈ A := by
    intro β hβ
    obtain ⟨j, hj⟩ := exists_isInnerAut_mul_pow_unitary148 (h := h) hQ hQ2 hfσ3 (hB3 β hβ)
      (hBab _ hσB _ hβ) hfσin
    refine ⟨j % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [hA]
    refine ⟨B.mul_mem hβ (B.pow_mem hσB _), ?_⟩
    rw [Item19Res5Proof.pow_mod_three_eq hfσ3]
    exact hj
  have hA9 : 9 ≤ Nat.card A := by
    have hsurj : Function.Surjective (fun x : A × Fin 3 =>
        (⟨(x.1 : MulAut (unitaryPSU h 3)) * (psuField h σ ^ (x.2 : ℕ))⁻¹,
          B.mul_mem (hAB x.1.2) (B.inv_mem (B.pow_mem hσB _))⟩ : B)) := by
      rintro ⟨β, hβ⟩
      obtain ⟨j, hj3, hjA⟩ := hcoset β hβ
      refine ⟨(⟨_, hjA⟩, ⟨j, hj3⟩), Subtype.ext ?_⟩
      simp
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hB27, Nat.card_prod, Nat.card_fin] at this
    omega
  obtain ⟨a₁, ha₁A, ha₁1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hcon
    rw [hbot, Subgroup.card_bot] at hA9
    omega
  have ha₁3 : a₁ ^ 3 = 1 := hB3 _ (hAB ha₁A)
  obtain ⟨a₂, ha₂A, ha₂z⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers a₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers a₁ from hcon)
    rw [Nat.card_zpowers] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) ha₁3
    omega
  have ha₂3 : a₂ ^ 3 = 1 := hB3 _ (hAB ha₂A)
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := hBab _ (hAB ha₁A) _ (hAB ha₂A)
  have hrep : ∀ a ∈ A, ∃ g : unitaryIsom3 h, psuConj h g = a ∧
      glAut σ (g : GL (Fin 3) K) = g := by
    intro a haA
    rw [hA] at haA
    obtain ⟨z, hz⟩ := (Subgroup.mem_inf.1 haA).2
    obtain ⟨g₀, rfl⟩ := unitaryProj_surjective h 3 z
    obtain ⟨G₀, hG₀⟩ : ∃ G : unitaryIsom3 h, G = ⟨g₀, unitarySU_le_unitaryIsom3 g₀.2⟩ :=
      ⟨_, rfl⟩
    have ha : psuConj h G₀ = a := by
      rw [← hz, hG₀]
      exact (conj_mk_eq_psuConj g₀).symm
    have hcomm : psuConj h G₀ * psuField h σ = psuField h σ * psuConj h G₀ := by
      rw [ha]
      exact hBab _ (Subgroup.mem_inf.1 haA).1 _ hσB
    obtain ⟨c, hc⟩ := exists_glAut_eq_scalar_mul_psu148 σ G₀ hcomm
    have hdet : GeneralLinearGroup.det (G₀ : GL (Fin 3) K) = 1 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, hG₀]
      exact ((mem_unitarySU_iff h).1 g₀.2).1
    have hc3 : c ^ 3 = 1 := by
      have h1 := congrArg GeneralLinearGroup.det hc
      rw [det_glAut148, map_mul, det_scalar_three148, hdet, map_one, mul_one] at h1
      exact h1.symm
    obtain ⟨μ, hμ0, hμN, hμσ⟩ := exists_norm_one_twist h hQ hσ (c := ((c⁻¹ : Kˣ) : K))
      (by rw [← Units.val_pow_eq_pow_val, inv_pow, hc3, inv_one, Units.val_one])
    have hμmem : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) ∈ unitaryIsom3 h :=
      scalar_mem_unitaryIsom3 (by rw [Units.val_mk0]; exact hμN)
    refine ⟨⟨_, hμmem⟩ * G₀, ?_, ?_⟩
    · rw [map_mul, psuConj_scalar hμmem, one_mul, ha]
    · have hσμ : Units.map (σ : K →* K) (Units.mk0 μ hμ0) = c⁻¹ * Units.mk0 μ hμ0 := by
        apply Units.ext
        rw [Units.coe_map, Units.val_mul, Units.val_mk0]
        exact hμσ
      change glAut σ (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) *
        (G₀ : GL (Fin 3) K)) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) *
          (G₀ : GL (Fin 3) K)
      rw [map_mul, glAut_scalar148, hc, hσμ, ← mul_assoc, ← map_mul]
      congr 2
      rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨g₁, hg₁, hg₁σ⟩ := hrep a₁ ha₁A
  obtain ⟨g₂, hg₂, hg₂σ⟩ := hrep a₂ ha₂A
  obtain ⟨x, hx⟩ := Item19Res5Proof.exists_map_eq_of_mem (fixedField σ)
    (Item19Res5Proof.mem_of_glAut_eq hk hg₁σ)
  obtain ⟨y, hy⟩ := Item19Res5Proof.exists_map_eq_of_mem (fixedField σ)
    (Item19Res5Proof.mem_of_glAut_eq hk hg₂σ)
  have hxU : x ∈ unitaryIsom3 h₀ := (mem_unitaryIsom3_map_iff h h₀ hbar x).1 (hx ▸ g₁.2)
  have hyU : y ∈ unitaryIsom3 h₀ := (mem_unitaryIsom3_map_iff h h₀ hbar y).1 (hy ▸ g₂.2)
  have hsubx : subIsom h h₀ hbar ⟨x, hxU⟩ = g₁ := Subtype.ext hx
  have hsuby : subIsom h h₀ hbar ⟨y, hyU⟩ = g₂ := Subtype.ext hy
  have hlift_scalar : ∀ c : Kˣ, glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) c → ∃ c' : (fixedField σ)ˣ,
        GeneralLinearGroup.map (fixedField σ).subtype (GeneralLinearGroup.scalar (Fin 3) c') =
          GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    obtain ⟨c', hc'⟩ := Item19Res5Proof.exists_units_map_eq_of_mem (fixedField σ)
      ((hk _).2 (Item19Res5Proof.fixed_of_glAut_scalar hc))
    refine ⟨c', ?_⟩
    rw [GeneralLinearGroup.map_scalar]
    congr 1
  have hinj := Item19Res5Proof.map_subtype_injective (fixedField σ)
  obtain ⟨α, hα⟩ := exists_scalar_of_psuConj_eq_one (A := g₁ ^ 3) (by rw [map_pow, hg₁]; exact ha₁3)
  obtain ⟨β, hβ⟩ := exists_scalar_of_psuConj_eq_one (A := g₂ ^ 3) (by rw [map_pow, hg₂]; exact ha₂3)
  obtain ⟨ω, hω⟩ := exists_scalar_of_psuConj_eq_one (A := g₂ * g₁ * (g₁ * g₂)⁻¹)
    (by rw [map_mul, map_mul, map_inv, map_mul, hg₁, hg₂, ha₁₂, mul_inv_cancel])
  rw [Subgroup.coe_pow] at hα hβ
  have hω' : (g₂ : GL (Fin 3) K) * g₁ =
      GeneralLinearGroup.scalar (Fin 3) ω * ((g₁ : GL (Fin 3) K) * g₂) := by
    rw [← hω]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨α', hα'⟩ := hlift_scalar α (by rw [← hα, map_pow, hg₁σ])
  obtain ⟨β', hβ'⟩ := hlift_scalar β (by rw [← hβ, map_pow, hg₂σ])
  obtain ⟨ω', hω''⟩ := hlift_scalar ω (by
    have h1 := congrArg (glAut σ) hω'
    rw [map_mul, map_mul, map_mul, hg₁σ, hg₂σ] at h1
    have h2 : glAut σ (GeneralLinearGroup.scalar (Fin 3) ω) * ((g₁ : GL (Fin 3) K) * g₂) =
        GeneralLinearGroup.scalar (Fin 3) ω * ((g₁ : GL (Fin 3) K) * g₂) := by rw [← h1, ← hω']
    exact mul_right_cancel h2)
  have hx3 : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) α' :=
    hinj (by rw [map_pow, hx, hα, hα'])
  have hy3 : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) β' :=
    hinj (by rw [map_pow, hy, hβ, hβ'])
  have hyx : y * x = GeneralLinearGroup.scalar (Fin 3) ω' * (x * y) :=
    hinj (by rw [map_mul, map_mul, map_mul, hx, hy, hω', hω''])
  have hind : ∀ a b : ℕ, (∃ c : (fixedField σ)ˣ,
      x ^ a * y ^ b = GeneralLinearGroup.scalar (Fin 3) c) → 3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hc⟩
    have h1 := congrArg (GeneralLinearGroup.map (fixedField σ).subtype) hc
    rw [map_mul, map_pow, map_pow, hx, hy, GeneralLinearGroup.map_scalar] at h1
    have hmem : ((g₁ : GL (Fin 3) K) ^ a * (g₂ : GL (Fin 3) K) ^ b : GL (Fin 3) K) ∈
        unitaryIsom3 h := by
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← Subgroup.coe_mul]
      exact (g₁ ^ a * g₂ ^ b).2
    rw [h1] at hmem
    have h2 : a₁ ^ a * a₂ ^ b = 1 := by
      rw [← hg₁, ← hg₂, ← map_pow, ← map_pow, ← map_mul]
      have : g₁ ^ a * g₂ ^ b = ⟨_, hmem⟩ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
        exact h1)
      rw [this]
      exact psuConj_scalar hmem
    exact Item19Res5Proof.three_dvd_of_pow_mul_pow_eq_one ha₁3 ha₂3 ha₁1 ha₂z h2
  have hHs : ∀ c : (fixedField σ)ˣ,
      GeneralLinearGroup.scalar (Fin 3) c ∈ scalarLift h h₀ hbar A :=
    scalar_mem_scalarLift h h₀ hbar A
  have hxH : x ∈ scalarLift h h₀ hbar A :=
    mem_scalarLift_of_mem h h₀ hbar ⟨x, hxU⟩ (by rw [hsubx, hg₁]; exact ha₁A)
  have hyH : y ∈ scalarLift h h₀ hbar A :=
    mem_scalarLift_of_mem h h₀ hbar ⟨y, hyU⟩ (by rw [hsuby, hg₂]; exact ha₂A)
  obtain ⟨u, hu0, huN, huσ, huk⟩ := exists_norm_one_twisted h hσ hfe hkcard hq2
  rcases Item19Res5Proof.toral_or_heis hkF3 hζ (scalarLift h h₀ hbar A) hHs hxH hyH hyx hx3 hy3
    hind with ⟨P, hP⟩ | ⟨x', hx'H, y', hy'H, P, ξ, w, α₀, hw, hPy, hPx⟩
  ·
    exact closure_fix_eq_top_toral h hfe hq hqne hk h₀ hbar hB3 ⟨x, hxU⟩ ⟨y, hyU⟩
      (by rw [hsubx, hg₁]; exact hAB ha₁A) (by rw [hsuby, hg₂]; exact hAB ha₂A)
      (by rw [hsubx, hsuby, hg₁, hg₂]; exact ha₁₂) (by rw [hsubx, hg₁]; exact ha₁1)
      (by rw [hsubx, hsuby, hg₁, hg₂]; exact ha₂z) hP hx3 hy3 hind huN
      (not_mem_of_mul_inv_not_mem hu0 huk)
  ·
    obtain ⟨cx, Wx, hWxA, rfl⟩ := (mem_scalarLift h h₀ hbar).1 hx'H
    obtain ⟨cy, Wy, hWyA, rfl⟩ := (mem_scalarLift h h₀ hbar).1 hy'H
    have hscal_mul : ∀ (c : (fixedField σ)ˣ) (W : GL (Fin 3) (fixedField σ)),
        ((GeneralLinearGroup.scalar (Fin 3) c * W : GL (Fin 3) (fixedField σ)) :
          Matrix (Fin 3) (Fin 3) (fixedField σ)) =
          (c : fixedField σ) • (W : Matrix (Fin 3) (Fin 3) (fixedField σ)) := by
      intro c W
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    have hcancel : ∀ (c : (fixedField σ)ˣ) (M N : Matrix (Fin 3) (Fin 3) (fixedField σ)),
        (c : fixedField σ) • M = N → M = ((c⁻¹ : (fixedField σ)ˣ) : fixedField σ) • N := by
      intro c M N hMN
      rw [← hMN, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    have hWyP : ((Wy : GL (Fin 3) (fixedField σ)) : Matrix (Fin 3) (Fin 3) (fixedField σ)) * P =
        P * diagonal ![((cy⁻¹ : (fixedField σ)ˣ) : fixedField σ) * ξ,
          ((cy⁻¹ : (fixedField σ)ˣ) : fixedField σ) * ξ * w,
          ((cy⁻¹ : (fixedField σ)ˣ) : fixedField σ) * ξ * w ^ 2] := by
      rw [hscal_mul, Matrix.smul_mul] at hPy
      rw [hcancel cy _ _ hPy, ← Matrix.mul_smul]
      congr 1
      rw [Matrix.smul_eq_diagonal_mul, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [mul_assoc]
    have hWxP : ((Wx : GL (Fin 3) (fixedField σ)) : Matrix (Fin 3) (Fin 3) (fixedField σ)) * P =
        P * (((cx⁻¹ : (fixedField σ)ˣ) : fixedField σ) • !![0, 0, α₀; 1, 0, 0; 0, 1, 0]) := by
      rw [hscal_mul, Matrix.smul_mul] at hPx
      rw [hcancel cx _ _ hPx, Matrix.mul_smul]
    exact closure_fix_eq_top_heis h hfe hq hqne hσσσ hk h₀ hbar hBab hB3 hσB hfσD Wx Wy
      (hAB hWxA) (hAB hWyA) hw hWyP hWxP huN huσ huk

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
