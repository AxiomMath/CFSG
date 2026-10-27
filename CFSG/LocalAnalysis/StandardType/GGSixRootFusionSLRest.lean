module

public import CFSG.LocalAnalysis.StandardType.GGSLBstarFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SLRep

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
  {p : ℕ} {B Bs D E G₀ M : Subgroup G} {f : ℕ} {r : G}
  {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) F}

noncomputable def coordBlockSLMapEquiv {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {S : Finset (Fin n)}
    {i₁ : Fin n} (hi₁ : i₁ ∉ S) :
    ((coordBlockSL F S).map φ : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin S.card) F := by
  classical
  have hinj : Function.Injective (φ.comp (coordBlockSL F S).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hj' : (x : Matrix.SpecialLinearGroup (Fin n) F) ∈ coordBlockSL F Sᶜᶜ := by
      rw [compl_compl]
      exact x.2
    exact Subtype.ext (TypeA.coordBlockSL_compl_inf_scalars (T := Sᶜ) (by simpa using hi₁) hj'
      (mem_scalars_of_ker_le_center hker hx))
  have hrange : (φ.comp (coordBlockSL F S).subtype).range = (coordBlockSL F S).map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact (((MonoidHom.ofInjective (blockSLOn_injective (k := F) S)).trans
    (MulEquiv.subgroupCongr (range_blockSLOn S))).trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))).symm

theorem ggRootFusionWitnessAlt_of_inner_seventeen (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {δ : Fin n → F} (hδ : ∏ i, δ i = 1)
    (hδp : ∀ i, δ i ^ p = 1) {S : Finset (Fin n)} (hS : ∀ i ∈ S, δ i = 1)
    (hSc : ∀ i ∉ S, δ i ≠ 1) (hcard : Sᶜ.card < S.card) (hS6 : 6 ≤ S.card)
    (hpell : ∀ k : ℕ, S.card * (S.card - 1) / 2 ≠ k * (k - 1)) {i₁ : Fin n} (hi₁ : i₁ ∉ S)
    {l : ℕ} (hpair : ∀ a c : Fin n, (c : ℕ) < l → (a : ℕ) = c + (n - l) → δ a = δ c) :
    GGRootFusionWitnessAlt p Bs D E G₀ M .PSL f r (ψ (ggInvSL n l F)) := by
  set d := ggDiagSL δ hδ with hd
  have hdδ : (d : Matrix (Fin n) (Fin n) F) = diagonal δ := rfl
  have hkerφ := ker_ggFrame_le hc.ker A₀
  have hrangeφ : (ggFrame ψ A₀).range = G₀ := (range_ggFrame ψ A₀).trans hc.range
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hb := act_map (ggFrame ψ A₀) d
  have hbBs := mem_of_frame_diagonal_inner hc.bstar hc.frame hdδ (ggDiagSL_pow_eq_one hδ hδp)
  have hne : δ i₁ ≠ δ i₀ := by rw [hS i₀ hi₀]; exact hSc i₁ hi₁
  have hb1 := ne_one_of_frame hkerφ hdδ hb hne
  have hcomp := isComponentOf_map_coordBlockSL hc.four hkerφ hdδ hb hS hSc hcard (by omega) hi₁
  rw [hrangeφ] at hcomp
  have hnex := SLRest.not_ggSixSeventeenExcluded (p := p) hF hf hS6 hpell
    (coordBlockSLMapEquiv hkerφ hi₁)
  have hW : GGSixFusionWitness p Bs D E G₀ .PSL f (ggFrame ψ A₀ d) :=
    ⟨hb1, Or.inr (Or.inr ⟨hbBs, _, hcomp, Or.inr hnex⟩)⟩
  have hwG : ψ A₀ ∈ G₀ := hc.range ▸ (⟨A₀, rfl⟩ : ψ A₀ ∈ ψ.range)
  refine ggRootFusionWitnessAlt_of_conj_comm ψ (w := A₀) ?_ (hle hwG) hW
  have hdu : d * ggInvSL n l F = ggInvSL n l F * d := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdδ, coe_ggInvSL]
    exact diagonal_mul_ggInvMatrix_comm δ hpair
  rw [ggFrame_apply, ← map_mul, ← map_mul]
  congr 1
  calc A₀ * d * A₀⁻¹ * (A₀ * ggInvSL n l F * A₀⁻¹) = A₀ * (d * ggInvSL n l F) * A₀⁻¹ := by group
    _ = A₀ * (ggInvSL n l F * d) * A₀⁻¹ := by rw [hdu]
    _ = A₀ * ggInvSL n l F * A₀⁻¹ * (A₀ * d * A₀⁻¹) := by group

omit [Finite F] [CharP F 2] in
theorem prod_eq_prod_of_eq_one_off {δ : Fin n → F} {T : Finset (Fin n)}
    (h : ∀ i ∉ T, δ i = 1) : ∏ i, δ i = ∏ i ∈ T, δ i :=
  (Finset.prod_subset (Finset.subset_univ T) fun i _ hi => h i hi).symm

theorem ggRootFusionWitnessAlt_residual_four (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {l : ℕ}
    (hl5 : 5 ≤ l) (hn : n = 2 * l)
    (hpell : ∀ k : ℕ, (n - 4) * (n - 4 - 1) / 2 ≠ k * (k - 1)) :
    GGRootFusionWitnessAlt p Bs D E G₀ M .PSL f r (ψ (ggInvSL n l F)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hc.prime.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hc.prime.one_lt
  have hζi1 : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hζ1
  set δ : Fin n → F := fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = l then ζ
    else if (i : ℕ) = 1 ∨ (i : ℕ) = l + 1 then ζ⁻¹ else 1 with hδdef
  have ev : ∀ i : Fin n, δ i = if (i : ℕ) = 0 ∨ (i : ℕ) = l then ζ
      else if (i : ℕ) = 1 ∨ (i : ℕ) = l + 1 then ζ⁻¹ else 1 := fun i => rfl
  obtain ⟨i0, h0⟩ : ∃ i : Fin n, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, h1⟩ : ∃ i : Fin n, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, h2⟩ : ∃ i : Fin n, (i : ℕ) = l := ⟨⟨l, by omega⟩, rfl⟩
  obtain ⟨i3, h3⟩ : ∃ i : Fin n, (i : ℕ) = l + 1 := ⟨⟨l + 1, by omega⟩, rfl⟩
  set T : Finset (Fin n) := {i0, i1, i2, i3} with hT
  have hTmem : ∀ i : Fin n, i ∈ T ↔
      ((i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = l ∨ (i : ℕ) = l + 1) := by
    intro i
    simp only [hT, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, h0, h1, h2, h3]
  have n01 : i0 ∉ ({i1, i2, i3} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
    omega
  have n02 : i1 ∉ ({i2, i3} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
    omega
  have n03 : i2 ≠ i3 := by
    simp only [ne_eq, Fin.ext_iff]
    omega
  have hTc : T.card = 4 := by
    rw [hT, Finset.card_insert_of_notMem n01, Finset.card_insert_of_notMem n02,
      Finset.card_pair n03]
  have hoff : ∀ i ∉ T, δ i = 1 := by
    intro i hi
    rw [hTmem] at hi
    rw [ev]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hδ : ∏ i, δ i = 1 := by
    have e0 : δ i0 = ζ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e1 : δ i1 = ζ⁻¹ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e2 : δ i2 = ζ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e3 : δ i3 = ζ⁻¹ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    rw [prod_eq_prod_of_eq_one_off hoff, hT, Finset.prod_insert n01, Finset.prod_insert n02,
      Finset.prod_pair n03, e0, e1, e2, e3]
    field_simp
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    rw [ev]
    split_ifs
    · exact hζ.pow_eq_one
    · rw [inv_pow, hζ.pow_eq_one, inv_one]
    · exact one_pow p
  have hcS : Tᶜ.card = n - 4 := by rw [Finset.card_compl, Fintype.card_fin, hTc]
  refine ggRootFusionWitnessAlt_of_inner_seventeen hc hle hF hf hδ hδp (S := Tᶜ)
    (fun i hi => hoff i (Finset.mem_compl.mp hi)) (fun i hi => ?_) ?_ ?_ ?_
    (i₁ := i0) (by simp [hT]) ?_
  · rw [Finset.mem_compl, not_not, hTmem] at hi
    rw [ev]
    split_ifs
    · exact hζ1
    · exact hζi1
    · exfalso
      omega
  · rw [compl_compl, hTc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [hcS]
    exact hpell
  · intro a c hca hac
    rw [ev, ev]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem ggRootFusionWitnessAlt_residual_six (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {l : ℕ}
    (hl10 : 10 ≤ l) (hleven : l % 2 = 0) (hn : n = 2 * l) :
    GGRootFusionWitnessAlt p Bs D E G₀ M .PSL f r (ψ (ggInvSL n l F)) := by
  have hp3 : 3 ≤ p := by have := hc.prime.two_le; have := hc.odd; omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hc.prime.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hc.prime.one_lt
  have hζ2 : ζ⁻¹ ^ 2 ≠ 1 := by
    rw [inv_pow, inv_ne_one]
    intro h
    have := Nat.le_of_dvd (by norm_num) ((hζ.pow_eq_one_iff_dvd 2).mp h)
    omega
  set δ : Fin n → F := fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = l ∨ (i : ℕ) = l + 1 then ζ
    else if (i : ℕ) = 2 ∨ (i : ℕ) = l + 2 then ζ⁻¹ ^ 2 else 1 with hδdef
  have ev : ∀ i : Fin n, δ i = if (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = l ∨ (i : ℕ) = l + 1 then ζ
      else if (i : ℕ) = 2 ∨ (i : ℕ) = l + 2 then ζ⁻¹ ^ 2 else 1 := fun i => rfl
  obtain ⟨i0, h0⟩ : ∃ i : Fin n, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, h1⟩ : ∃ i : Fin n, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, h2⟩ : ∃ i : Fin n, (i : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨i3, h3⟩ : ∃ i : Fin n, (i : ℕ) = l := ⟨⟨l, by omega⟩, rfl⟩
  obtain ⟨i4, h4⟩ : ∃ i : Fin n, (i : ℕ) = l + 1 := ⟨⟨l + 1, by omega⟩, rfl⟩
  obtain ⟨i5, h5⟩ : ∃ i : Fin n, (i : ℕ) = l + 2 := ⟨⟨l + 2, by omega⟩, rfl⟩
  set T : Finset (Fin n) := {i0, i1, i2, i3, i4, i5} with hT
  have hTmem : ∀ i : Fin n, i ∈ T ↔ ((i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = l ∨
      (i : ℕ) = l + 1 ∨ (i : ℕ) = l + 2) := by
    intro i
    simp only [hT, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, h0, h1, h2, h3, h4, h5]
  have n1 : i0 ∉ ({i1, i2, i3, i4, i5} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
    omega
  have n2 : i1 ∉ ({i2, i3, i4, i5} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
    omega
  have n3 : i2 ∉ ({i3, i4, i5} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
    omega
  have n4 : i3 ∉ ({i4, i5} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
    omega
  have n5 : i4 ≠ i5 := by
    simp only [ne_eq, Fin.ext_iff]
    omega
  have hTc : T.card = 6 := by
    rw [hT, Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_pair n5]
  have hoff : ∀ i ∉ T, δ i = 1 := by
    intro i hi
    rw [hTmem] at hi
    rw [ev]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hδ : ∏ i, δ i = 1 := by
    have e0 : δ i0 = ζ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e1 : δ i1 = ζ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e2 : δ i2 = ζ⁻¹ ^ 2 := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e3 : δ i3 = ζ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e4 : δ i4 = ζ := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    have e5 : δ i5 = ζ⁻¹ ^ 2 := by rw [ev]; split_ifs <;> first | rfl | (exfalso; omega)
    rw [prod_eq_prod_of_eq_one_off hoff, hT, Finset.prod_insert n1, Finset.prod_insert n2,
      Finset.prod_insert n3, Finset.prod_insert n4, Finset.prod_pair n5, e0, e1, e2, e3, e4, e5]
    field_simp
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    rw [ev]
    split_ifs
    · exact hζ.pow_eq_one
    · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
    · exact one_pow p
  have hcS : Tᶜ.card = n - 6 := by rw [Finset.card_compl, Fintype.card_fin, hTc]
  refine ggRootFusionWitnessAlt_of_inner_seventeen hc hle hF hf hδ hδp (S := Tᶜ)
    (fun i hi => hoff i (Finset.mem_compl.mp hi)) (fun i hi => ?_) ?_ ?_ ?_
    (i₁ := i0) (by simp [hT]) ?_
  · rw [Finset.mem_compl, not_not, hTmem] at hi
    rw [ev]
    split_ifs
    · exact hζ1
    · exact hζ2
    · exfalso
      omega
  · rw [compl_compl, hTc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [hcS]
    exact SLRest.half_mul_pred_ne_of_mod_four (by omega)
  · intro a c hca hac
    rw [ev, ev]
    split_ifs <;> first | rfl | (exfalso; omega)

end SLRep

section Alpha

@[expose] def GGSLSixAlphaInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], 4 ≤ Nat.card F → ∀ (G : Type) [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* G),
    ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F) →
      ¬ ∃ φ : ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSL 6 3 F))) →*
          ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSL 6 1 F))), Function.Injective φ

theorem ggRootFusionWitnessAlt_of_alpha (hα : GGSLSixAlphaInput) {G : Type} [Group G] {F : Type}
    [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F)) {p : ℕ}
    {Bs D E M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r c : G} (hc : c ∈ ψ.range)
    (hr : c⁻¹ * r * c = ψ (ggInvSL 6 1 F)) :
    GGRootFusionWitnessAlt p Bs D E ψ.range M t f r (ψ (ggInvSL 6 3 F)) := by
  refine Or.inr (Or.inr ?_)
  rintro ⟨φ, hφ⟩
  have hcN : c ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.le_normalizer hc
  have hmem : ∀ y ∈ ggCentOTwoPrime ψ.range r,
      c⁻¹ * y * c ∈ ggCentOTwoPrime ψ.range (ψ (ggInvSL 6 1 F)) := by
    intro y hy
    have := conj_mem_ggCentOTwoPrime hcN hy
    rwa [hr] at this
  let κ : ↥(ggCentOTwoPrime ψ.range r) →* ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSL 6 1 F))) :=
    { toFun := fun y => ⟨c⁻¹ * y * c, hmem y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hκ : Function.Injective κ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [κ, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  exact hα F h4 G ψ hker ⟨κ.comp φ, hκ.comp hφ⟩

theorem ggRootFusionWitnessAlt_alpha_of_root (hα : GGSLSixAlphaInput) {G : Type} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (ψ : Matrix.SpecialLinearGroup (Fin (5 + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (5 + 1)) F)) {p : ℕ}
    {Bs D E M : Subgroup G} {t : StatedLieTag} {f : ℕ} {γ : Fin 5 → ℤ}
    {v z : Matrix.SpecialLinearGroup (Fin (5 + 1)) F} (hz : z ∈ SpecialLinear.rootGroup 5 F γ)
    (hr2 : orderOf (ψ (v * z * v⁻¹)) = 2) :
    GGRootFusionWitnessAlt p Bs D E ψ.range M t f (ψ (v * z * v⁻¹)) (ψ (ggInvSL (5 + 1) 3 F)) := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨i, j, hij, c, hc0, rfl⟩ := exists_transvection_of_mem_rootGroup hz hz1
  obtain ⟨g, hg⟩ := exists_conj_transvection_eq (F := F) (by norm_num) hij hc0
  refine ggRootFusionWitnessAlt_of_alpha hα h4 ψ hker (c := ψ (v * g⁻¹)) ⟨_, rfl⟩ ?_
  rw [← hg]
  simp only [map_mul, map_inv]
  group

end Alpha

section Inputs

theorem ggSixRootFusionSLRepResidualInput_of_alpha (hα : GGSLSixAlphaInput) :
    GGSixRootFusionSLRepResidualInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx s1 s2 E r hch hC hodd hsplit hpn A₀ hframe hns l hl2 hn
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hcardF]; exact hsplit
  have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcardF]
    have h2 := Nat.le_of_dvd (by omega) hsplit
    have h3 := hp.two_le
    omega
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    rw [hcardF] at h4
    norm_num at h4
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hc : SLRep.FrameCtx p B Bs (ggG0 p B x L D J) ψ A₀ :=
    ⟨hctx.2.1, hker, hrange, s1.1, hframe, hp, hp2, hpF, h4⟩
  have hle : ggG0 p B x L D J ≤ ggM p B x L D J := Subgroup.le_normalizer
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
  have hpl : p ∣ l := by
    rw [hn] at hpn
    rcases (Nat.Prime.dvd_mul hp).mp hpn with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · exact h
  have hnot2 : ∀ k : ℕ, l ≠ 2 ^ k := by
    rintro k rfl
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpl))
  have hl3 : 3 ≤ l := by
    have := Nat.le_of_dvd (by omega) hpl
    have := hp.two_le
    omega
  rcases Nat.lt_or_ge l 4 with hl | hl
  ·
    obtain rfl : l = 3 := by omega
    obtain rfl : m = 5 := by omega
    have hr2 : orderOf r = 2 := hch.2.2.2.2.1
    have hr : ∃ (γ : Fin 5 → ℤ) (v z : Matrix.SpecialLinearGroup (Fin (5 + 1)) (GaloisField 2 f)),
        z ∈ SpecialLinear.rootGroup 5 (GaloisField 2 f) γ ∧ r = ψ (v * z * v⁻¹) := by
      obtain ⟨-, -, -, -, -, γ, -, v, -, hrv⟩ := hch
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hrv
      exact ⟨γ, v, z, hz, rfl⟩
    obtain ⟨γ, v, z, hz, rfl⟩ := hr
    rw [← hrange]
    exact ggRootFusionWitnessAlt_alpha_of_root hα h4 ψ hker hz hr2
  · rcases Nat.lt_or_ge l 5 with hl' | hl5
    · exact absurd (show l = 2 ^ 2 by omega) (hnot2 2)
    rcases Nat.even_or_odd l with hle' | hlo
    · rcases Nat.lt_or_ge l 10 with hl10 | hl10
      ·
        have hl6 : l = 6 := by
          obtain ⟨j, rfl⟩ := hle'
          rcases (show j = 3 ∨ j = 4 by omega) with rfl | rfl
          · rfl
          · exact absurd (show 4 + 4 = 2 ^ 3 by norm_num) (hnot2 3)
        subst hl6
        refine SLRep.ggRootFusionWitnessAlt_residual_four hc hle hcardF hf2 hζ (le_refl _ |>.trans
          (by norm_num)) hn ?_
        rw [hn]
        exact SLRest.eight_half_mul_pred_ne
      · exact SLRep.ggRootFusionWitnessAlt_residual_six hc hle hcardF hf2 hζ hl10
          (Nat.even_iff.mp hle') hn
    · refine SLRep.ggRootFusionWitnessAlt_residual_four hc hle hcardF hf2 hζ hl5 hn ?_
      exact SLRest.half_mul_pred_ne_of_mod_four (by obtain ⟨j, rfl⟩ := hlo; omega)

theorem ggSixRootFusionSLRepInput_of_nonsplit_alpha (hN : GGSixRootFusionSLRepNonsplitInput)
    (hα : GGSLSixAlphaInput) : GGSixRootFusionSLRepInput :=
  ggSixRootFusionSLRepInput_of_nonsplit_residual hN (ggSixRootFusionSLRepResidualInput_of_alpha hα)

end Inputs

end CFSG.StandardType
