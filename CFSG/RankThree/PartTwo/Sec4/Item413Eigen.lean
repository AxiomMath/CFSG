module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.KFacts.K71D4G2Intertwiner

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Polynomial Module Matrix

theorem card_le_three_pow_of_injective {G α K : Type*} [Finite G] [Fintype α] [Field K]
    (φ : G → α → K) (hφ : Function.Injective φ) (h3 : ∀ g a, φ g a ^ 3 = 1) :
    Nat.card G ≤ 3 ^ Fintype.card α := by
  classical
  set S : Finset K := (nthRoots 3 (1 : K)).toFinset
  have hS : S.card ≤ 3 := (Multiset.toFinset_card_le _).trans (card_nthRoots 3 1)
  let ψ : G → (α → S) := fun g a =>
    ⟨φ g a, by rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num)]; exact h3 g a⟩
  have hψ : Function.Injective ψ := fun g g' h =>
    hφ (funext fun a => congrArg Subtype.val (congrFun h a))
  calc Nat.card G ≤ Nat.card (α → S) := Nat.card_le_card_of_injective ψ hψ
    _ = S.card ^ Fintype.card α := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
    _ ≤ 3 ^ Fintype.card α := Nat.pow_le_pow_left hS _

theorem card_le_three_of_pow_three {K : Type*} [Field K] (U : Subgroup Kˣ) [Finite U]
    (hU : ∀ u ∈ U, u ^ 3 = 1) : Nat.card U ≤ 3 := by
  have h := card_le_three_pow_of_injective (α := Unit) (fun (u : U) _ => ((u : Kˣ) : K))
    (fun u v huv => Subtype.ext (Units.ext (congrFun huv ())))
    (fun u _ => by rw [← Units.val_pow_eq_pow_val, hU u u.2, Units.val_one])
  simpa using h

theorem card_sq_le_of_characters {G K : Type*} [Group G] [Finite G] [Field K]
    [DecidableEq (G → K)] (n : ℕ) :
    ∀ (C : Finset (G → K)) (H : Subgroup G), C.card ≤ n →
      (∀ χ ∈ C, ∀ x ∈ H, ∀ y ∈ H, χ (x * y) = χ x * χ y) →
      (∀ χ ∈ C, ∀ x ∈ H, χ x ^ 3 = 1) →
      (∀ χ ∈ C, ∃ ψ ∈ C, ∀ x ∈ H, ψ x = (χ x)⁻¹) →
      (∀ x ∈ H, (∀ χ ∈ C, χ x = 1) → x = 1) →
      Nat.card H ^ 2 ≤ 3 ^ C.card := by
  induction n with
  | zero =>
    intro C H hC _ _ _ hfaith
    have hC0 : C = ∅ := Finset.card_eq_zero.mp (by omega)
    have hH : H = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (hfaith x hx (by simp [hC0]))
    rw [hH, Subgroup.card_bot, one_pow]
    exact Nat.one_le_pow _ _ (by norm_num)
  | succ n ih =>
    intro C H hC hmul h3 hinv hfaith
    by_cases hex : ∃ χ ∈ C, ∃ x₀ ∈ H, χ x₀ ≠ 1
    swap
    · push Not at hex
      have hH : H = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact (Subgroup.mem_bot).mpr (hfaith x hx fun χ hχ => hex χ hχ x hx)
      rw [hH, Subgroup.card_bot, one_pow]
      exact Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨χ, hχ, x₀, hx₀, hχx₀⟩ := hex
    obtain ⟨ψ, hψ, hψχ⟩ := hinv χ hχ
    have hne0 : ∀ x ∈ H, χ x ≠ 0 := fun x hx h0 => by
      have := h3 χ hχ x hx
      rw [h0] at this
      norm_num at this
    have hχ1 : χ 1 = 1 := by
      have h := hmul χ hχ 1 H.one_mem 1 H.one_mem
      rw [mul_one] at h
      have h0 := hne0 1 H.one_mem
      field_simp at h
      exact h.symm
    have hψne : ψ ≠ χ := by
      rintro rfl
      have h := hψχ x₀ hx₀
      have h0 := hne0 x₀ hx₀
      have h33 := h3 ψ hψ x₀ hx₀
      apply hχx₀
      have h2 : ψ x₀ ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [h]
        exact mul_inv_cancel₀ h0
      calc ψ x₀ = ψ x₀ ^ 3 * (ψ x₀ ^ 2)⁻¹ := by
            field_simp
          _ = 1 := by rw [h33, h2]; norm_num
    let H₁ : Subgroup G :=
      { carrier := {x | x ∈ H ∧ χ x = 1}
        one_mem' := ⟨H.one_mem, hχ1⟩
        mul_mem' := fun {x y} hx hy => ⟨H.mul_mem hx.1 hy.1, by
          rw [hmul χ hχ x hx.1 y hy.1, hx.2, hy.2, mul_one]⟩
        inv_mem' := fun {x} hx => ⟨H.inv_mem hx.1, by
          have h := hmul χ hχ x⁻¹ (H.inv_mem hx.1) x hx.1
          rw [inv_mul_cancel, hχ1, hx.2, mul_one] at h
          exact h.symm⟩ }
    have hH₁H : H₁ ≤ H := fun x hx => hx.1
    set C₁ := (C.erase χ).erase ψ
    have hψmem : ψ ∈ C.erase χ := Finset.mem_erase.mpr ⟨hψne, hψ⟩
    have hC₁card : C₁.card + 2 = C.card := by
      rw [Finset.card_erase_of_mem hψmem, Finset.card_erase_of_mem hχ]
      have : 2 ≤ C.card := by
        have h1 : 1 ≤ (C.erase χ).card := Finset.card_pos.mpr ⟨ψ, hψmem⟩
        rw [Finset.card_erase_of_mem hχ] at h1
        omega
      omega
    have hC₁sub : C₁ ⊆ C := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hψ1 : ∀ x ∈ H₁, ψ x = 1 := fun x hx => by rw [hψχ x hx.1, hx.2, inv_one]
    have hIH := ih C₁ H₁ (by omega)
      (fun φ hφ x hx y hy => hmul φ (hC₁sub hφ) x (hH₁H hx) y (hH₁H hy))
      (fun φ hφ x hx => h3 φ (hC₁sub hφ) x (hH₁H hx))
      (fun φ hφ => by
        obtain ⟨φ', hφ', hφφ'⟩ := hinv φ (hC₁sub hφ)
        by_cases hφ'C₁ : φ' ∈ C₁
        · exact ⟨φ', hφ'C₁, fun x hx => hφφ' x (hH₁H hx)⟩
        · refine ⟨φ, hφ, fun x hx => ?_⟩
          have hφ'1 : φ' x = 1 := by
            have : φ' = χ ∨ φ' = ψ := by
              by_contra hc
              push Not at hc
              exact hφ'C₁ (Finset.mem_erase.mpr ⟨hc.2, Finset.mem_erase.mpr ⟨hc.1, hφ'⟩⟩)
            rcases this with rfl | rfl
            · exact hx.2
            · exact hψ1 x hx
          have h := hφφ' x (hH₁H hx)
          rw [hφ'1] at h
          have : φ x = 1 := by
            have h' := congrArg (·⁻¹) h
            simp only [inv_inv, inv_one] at h'
            exact h'.symm
          rw [this, inv_one])
      (fun x hx hall => hfaith x (hH₁H hx) fun φ hφ => by
        by_cases hφC₁ : φ ∈ C₁
        · exact hall φ hφC₁
        · have : φ = χ ∨ φ = ψ := by
            by_contra hc
            push Not at hc
            exact hφC₁ (Finset.mem_erase.mpr ⟨hc.2, Finset.mem_erase.mpr ⟨hc.1, hφ⟩⟩)
          rcases this with rfl | rfl
          · exact hx.2
          · exact hψ1 x hx)
    let μ : H →* Kˣ :=
      { toFun := fun x => ⟨χ x, χ x ^ 2, by rw [← pow_succ', h3 χ hχ x x.2],
          by rw [← pow_succ, h3 χ hχ x x.2]⟩
        map_one' := Units.ext hχ1
        map_mul' := fun x y => Units.ext (hmul χ hχ x x.2 y y.2) }
    have hker : Nat.card μ.ker = Nat.card H₁ := by
      have : μ.ker = H₁.subgroupOf H := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          exact ⟨x.2, congrArg Units.val h⟩
        · intro h
          exact Units.ext h.2
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₁H).toEquiv
    have : Finite μ.range := Finite.of_surjective _ μ.rangeRestrict_surjective
    have hrange : Nat.card μ.range ≤ 3 :=
      card_le_three_of_pow_three μ.range fun u ⟨x, hx⟩ => by
        rw [← hx]
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h3 χ hχ x x.2
    have hcardH : Nat.card H = Nat.card μ.range * Nat.card μ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hker] at hcardH
    calc Nat.card H ^ 2 = Nat.card μ.range ^ 2 * Nat.card H₁ ^ 2 := by rw [hcardH, mul_pow]
      _ ≤ 3 ^ 2 * 3 ^ C₁.card := Nat.mul_le_mul (Nat.pow_le_pow_left hrange 2) hIH
      _ = 3 ^ C.card := by rw [← pow_add, ← hC₁card, add_comm]

section Eigen

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Subgroup (GL ι K)} {b : Module.Basis ι K (ι → K)} {d : GL ι K → ι → K}

theorem eigen_mul (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a) {x y : GL ι K}
    (hx : x ∈ E) (hy : y ∈ E) (a : ι) : d (x * y) a = d x a * d y a := by
  have h1 := hb (x * y) (E.mul_mem hx hy) a
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb y hy a, Matrix.mulVec_smul, hb x hx a,
    smul_smul] at h1
  rw [mul_comm]
  exact (smul_left_injective K (b.ne_zero a) h1).symm

theorem eigen_one (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a) (a : ι) :
    d 1 a = 1 := by
  have h0 := hb 1 E.one_mem a
  rw [Units.val_one, Matrix.one_mulVec] at h0
  exact smul_left_injective K (b.ne_zero a) (show d 1 a • b a = (1 : K) • b a by
    rw [← h0, one_smul])

theorem eigen_pow_three (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a)
    {x : GL ι K} (hx : x ∈ E) (hx3 : x ^ 3 = 1) (a : ι) : d x a ^ 3 = 1 := by
  have h := eigen_mul hb (E.mul_mem hx hx) hx a
  have h1 := eigen_mul hb hx hx a
  have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
  rw [hx3', eigen_one hb a, h1] at h
  rw [h]
  ring

theorem eigen_ext (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a) {x y : GL ι K}
    (hx : x ∈ E) (hy : y ∈ E) (h : ∀ a, d x a = d y a) : x = y := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply b.ext
  intro a
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb x hx a, hb y hy a, h a]

theorem eigen_det (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a) {x : GL ι K}
    (hx : x ∈ E) : (x : Matrix ι ι K).det = ∏ a, d x a := by
  rw [← LinearMap.det_toLin', ← LinearMap.det_toMatrix b,
    show LinearMap.toMatrix b b (Matrix.toLin' (x : Matrix ι ι K)) = Matrix.diagonal (d x) from ?_,
    Matrix.det_diagonal]
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb x hx j, map_smul, b.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

theorem exists_common_eigenbasis_pow_three [IsAlgClosed K] (h3 : (3 : K) ≠ 0)
    (E : Subgroup (GL ι K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ (b : Module.Basis ι K (ι → K)) (d : GL ι K → ι → K),
      ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a := by
  classical
  set f : E → Module.End K (ι → K) :=
    fun x => Matrix.toLinAlgEquiv' ((x : GL ι K) : Matrix ι ι K) with hfdef
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => by
    change Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _ =
      Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hcomm _ i.2 _ j.2]
  have hf3 : ∀ i, f i ^ 3 = 1 := fun i => by
    change (Matrix.toLinAlgEquiv' _) ^ 3 = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hexp _ i.2, Units.val_one, map_one]
  have hsep : (X ^ 3 - C (1 : K)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast h3) one_ne_zero
  have hss : ∀ i, (f i).IsSemisimple := fun i =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hf3 i])
  set W : (E → K) → Submodule K (ι → K) := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hW
  have hind : iSupIndep W :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfcomm j i) φ)
  have htop : ⨆ χ, W χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hfcomm i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  set b₀ := hint.collectedBasis (fun χ => Module.finBasis K (W χ))
  let e := b₀.indexEquiv (Pi.basisFun K ι)
  refine ⟨b₀.reindex e, fun x a => if hx : x ∈ E then (e.symm a).1 ⟨x, hx⟩ else 0, ?_⟩
  intro x hx a
  have hmem : b₀.reindex e a ∈ W (e.symm a).1 := by
    rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem _ _
  have h1 : b₀.reindex e a ∈ (f ⟨x, hx⟩).maxGenEigenspace ((e.symm a).1 ⟨x, hx⟩) :=
    (Submodule.mem_iInf _).mp hmem ⟨x, hx⟩
  rw [(hss ⟨x, hx⟩).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at h1
  simp only [hx, ↓reduceDIte]
  rw [← h1]
  rfl

end Eigen

section Bounds

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_le_of_det_eq_one_of_isAlgClosed [IsAlgClosed K] (h3 : (3 : K) ≠ 0) (a₀ : ι)
    (E : Subgroup (GL ι K)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) [Finite E] :
    Nat.card E ≤ 3 ^ (Fintype.card ι - 1) := by
  classical
  obtain ⟨b, d, hb⟩ := exists_common_eigenbasis_pow_three h3 E hcomm hexp
  have h := card_le_three_pow_of_injective (α := {a : ι // a ≠ a₀})
    (fun (x : E) a => d x a)
    (fun x y hxy => by
      have hxy' : ∀ a, a ≠ a₀ → d x a = d y a := fun a ha => congrFun hxy ⟨a, ha⟩
      apply Subtype.ext
      refine eigen_ext hb x.2 y.2 fun a => ?_
      by_cases ha : a = a₀
      · subst ha
        have hx := (eigen_det hb x.2).symm.trans (hdet x x.2)
        have hy := (eigen_det hb y.2).symm.trans (hdet y y.2)
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)] at hx hy
        have hp : ∏ c ∈ Finset.univ.erase a, d x c = ∏ c ∈ Finset.univ.erase a, d y c :=
          Finset.prod_congr rfl fun c hc => hxy' c (Finset.ne_of_mem_erase hc)
        rw [hp] at hx
        have hne : ∏ c ∈ Finset.univ.erase a, d y c ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hy
          exact zero_ne_one hy
        exact mul_right_cancel₀ hne (hx.trans hy.symm)
      · exact hxy' a ha)
    (fun x a => eigen_pow_three hb x.2 (hexp x x.2) a)
  rwa [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h

omit [DecidableEq ι] in
theorem form_mulVec_mulVec {x M : Matrix ι ι K} (h : xᵀ * M * x = M) (v w : ι → K) :
    (x *ᵥ v) ⬝ᵥ (M *ᵥ (x *ᵥ w)) = v ⬝ᵥ (M *ᵥ w) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

theorem exists_form_ne_zero {M : Matrix ι ι K} (hM : M.det ≠ 0) (b : Module.Basis ι K (ι → K))
    {v : ι → K} (hv : v ≠ 0) : ∃ a', v ⬝ᵥ (M *ᵥ b a') ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hv
  refine Matrix.eq_zero_of_vecMul_eq_zero hM (dotProduct_eq_zero_iff.mp fun w => ?_)
  let L : (ι → K) →ₗ[K] K :=
    { toFun := fun w => v ⬝ᵥ (M *ᵥ w)
      map_add' := fun w w' => by rw [Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c w => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }
  have hL : L = 0 := b.ext fun a' => by rw [LinearMap.zero_apply]; exact hc a'
  rw [← Matrix.dotProduct_mulVec]
  exact LinearMap.congr_fun hL w

theorem card_sq_le_of_form_of_isAlgClosed [IsAlgClosed K] (h3 : (3 : K) ≠ 0)
    (E : Subgroup (GL ι K)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (M : Matrix ι ι K) (hM : M.det ≠ 0)
    (hform : ∀ x ∈ E, (x : Matrix ι ι K)ᵀ * M * (x : Matrix ι ι K) = M) [Finite E] :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  classical
  obtain ⟨b, d, hb⟩ := exists_common_eigenbasis_pow_three h3 E hcomm hexp
  have hpair : ∀ a, ∃ a', ∀ x ∈ E, d x a' = (d x a)⁻¹ := by
    intro a
    obtain ⟨a', ha'⟩ := exists_form_ne_zero hM b (b.ne_zero a)
    refine ⟨a', fun x hx => ?_⟩
    have h1 := form_mulVec_mulVec (hform x hx) (b a) (b a')
    rw [hb x hx a, hb x hx a', Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    have hω : d x a * d x a' = 1 := by
      have : (d x a * d x a' - 1) * (b a ⬝ᵥ (M *ᵥ b a')) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h | h
      · linear_combination h
      · exact absurd h ha'
    exact eq_inv_of_mul_eq_one_right hω
  set C : Finset (E → K) := Finset.univ.image fun a => fun x : E => d x a with hCdef
  have hCcard : C.card ≤ Fintype.card ι := Finset.card_image_le
  have h := card_sq_le_of_characters (G := E) (K := K) C.card C ⊤ le_rfl
    (by
      intro χ hχ x _ y _
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      exact eigen_mul hb x.2 y.2 a)
    (by
      intro χ hχ x _
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      exact eigen_pow_three hb x.2 (hexp x x.2) a)
    (by
      intro χ hχ
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      obtain ⟨a', ha'⟩ := hpair a
      exact ⟨fun x : E => d x a', Finset.mem_image.mpr ⟨a', Finset.mem_univ _, rfl⟩,
        fun x _ => ha' x x.2⟩)
    (by
      intro x _ hx
      apply Subtype.ext
      rw [Subgroup.coe_one]
      refine eigen_ext hb x.2 E.one_mem fun a => ?_
      rw [eigen_one hb a]
      exact hx _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  rw [Subgroup.card_top] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) hCcard)


theorem map_injective_GL {L : Type*} [Field L] (f : K →+* L) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) f) := fun _ _ h =>
  Units.ext (Matrix.map_injective f.injective (congrArg Units.val h))

theorem card_le_of_det_eq_one (h3 : (3 : K) ≠ 0) (a₀ : ι) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) :
    Nat.card E ≤ 3 ^ (Fintype.card ι - 1) := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := map_injective_GL _
  have h3' : (3 : L) ≠ 0 := by
    intro h
    apply h3
    apply (algebraMap K L).injective
    rw [map_ofNat, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := card_le_of_det_eq_one_of_isAlgClosed h3' a₀ (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      change ((x : Matrix ι ι K).map (algebraMap K L)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet x hx, map_one])
  rwa [Subgroup.card_map_of_injective hΦ] at h

theorem card_sq_le_of_form (h3 : (3 : K) ≠ 0) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (M : Matrix ι ι K) (hM : M.det ≠ 0)
    (hform : ∀ x ∈ E, (x : Matrix ι ι K)ᵀ * M * (x : Matrix ι ι K) = M) :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := map_injective_GL _
  have h3' : (3 : L) ≠ 0 := by
    intro h
    apply h3
    apply (algebraMap K L).injective
    rw [map_ofNat, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := card_sq_le_of_form_of_isAlgClosed h3' (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (M.map (algebraMap K L))
    (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (_root_.map_ne_zero _).mpr hM)
    (by
      rintro _ ⟨x, hx, rfl⟩
      change ((x : Matrix ι ι K).map (algebraMap K L))ᵀ * M.map (algebraMap K L) *
        (x : Matrix ι ι K).map (algebraMap K L) = M.map (algebraMap K L)
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hform x hx])
  rwa [Subgroup.card_map_of_injective hΦ] at h

end Bounds

end CFSG.RankThree.PartTwo.Sec4
