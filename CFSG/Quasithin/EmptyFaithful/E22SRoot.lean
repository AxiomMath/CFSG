module

public import CFSG.Quasithin.EmptyFaithful.E22SFrame
public import CFSG.Quasithin.Background.E1Sec6

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.SubgroupLists CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem diag_mul_transvection {d : Fin 3 → K} (hd : ∀ l, d l ≠ 0) {i j : Fin 3} (t : K) :
    Matrix.diagonal d * (1 + Matrix.single i j t) =
      (1 + Matrix.single i j (d i * (d j)⁻¹ * t)) * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    by_cases hab : i = j
    · subst hab
      simp
      field_simp [hd i]
    · simp [hab]
      field_simp [hd j]
  · by_cases hab : a = b
    · subst hab
      simp [h]
    · simp [h, hab]

theorem diag_conj_transvection {M : SL(3, K)} {d : Fin 3 → K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d) {i j : Fin 3} (hij : i ≠ j)
    (t : K) :
    M * Matrix.SpecialLinearGroup.transvection hij t * M⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (d i * (d j)⁻¹ * t) := by
  have hdet : ∏ l, d l = 1 := by
    have h := M.2
    rw [hM, Matrix.det_diagonal] at h
    exact h
  have hd : ∀ l, d l ≠ 0 := fun l h0 => by
    have : ∏ l, d l = 0 := Finset.prod_eq_zero (Finset.mem_univ l) h0
    rw [hdet] at this
    exact one_ne_zero this
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show (M : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single i j t) =
    (1 + Matrix.single i j (d i * (d j)⁻¹ * t)) * (M : Matrix (Fin 3) (Fin 3) K)
  rw [hM]
  exact diag_mul_transvection hd t

@[expose] def rootGrp (g : SL(3, K)) {i j : Fin 3} (hij : i ≠ j) : Subgroup SL(3, K) :=
  (MonoidHom.range (Matrix.SpecialLinearGroup.transvectionHom (n := Fin 3) (A := K) hij)).map
    (MulAut.conj g⁻¹).toMonoidHom

theorem mem_rootGrp {g y : SL(3, K)} {i j : Fin 3} (hij : i ≠ j) :
    y ∈ rootGrp g hij ↔ ∃ t : K,
      y = g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g := by
  unfold rootGrp
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨Multiplicative.toAdd c, ?_⟩
    simp [Matrix.SpecialLinearGroup.transvectionHom_apply]
  · rintro ⟨t, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection hij t,
      ⟨Multiplicative.ofAdd t, by simp [Matrix.SpecialLinearGroup.transvectionHom_apply]⟩, ?_⟩
    simp

theorem rootGrp_mem {g : SL(3, K)} {i j : Fin 3} (hij : i ≠ j) (t : K) :
    g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g ∈ rootGrp g hij :=
  (mem_rootGrp hij).mpr ⟨t, rfl⟩

theorem conj_rootGrp {g x : SL(3, K)} (hx : IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j) (t : K) :
    x * (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g) * x⁻¹ =
      g⁻¹ * Matrix.SpecialLinearGroup.transvection hij (dg g x i * (dg g x j)⁻¹ * t) * g := by
  rw [← diag_conj_transvection (conj_eq_diagonal hx) hij t]
  group

theorem rootGrp_pow {p : ℕ} [CharP K p] {g y : SL(3, K)} {i j : Fin 3} (hij : i ≠ j)
    (hy : y ∈ rootGrp g hij) : y ^ p = 1 := by
  obtain ⟨t, rfl⟩ := (mem_rootGrp hij).mp hy
  have h1 : (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g) ^ p =
      g⁻¹ * (Matrix.SpecialLinearGroup.transvection hij t) ^ p * g := by
    have := map_pow (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.transvection hij t) p
    simpa [MulAut.conj_apply] using this.symm
  have h2 : (Matrix.SpecialLinearGroup.transvection hij t) ^ p = 1 := by
    have e : Matrix.SpecialLinearGroup.transvection hij t =
        Matrix.SpecialLinearGroup.transvectionHom (n := Fin 3) (A := K) hij
          (Multiplicative.ofAdd t) := by
      rw [Matrix.SpecialLinearGroup.transvectionHom_apply]
      rfl
    rw [e, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero,
      map_one]
  rw [h1, h2]
  group

@[expose] def rootImg (g : SL(3, K)) {i j : Fin 3} (hij : i ≠ j) : Subgroup (projectiveSL 3 K) :=
  (rootGrp g hij).map (proj 3 K)

theorem mem_rootImg {g : SL(3, K)} {i j : Fin 3} (hij : i ≠ j) {z : projectiveSL 3 K} :
    z ∈ rootImg g hij ↔ ∃ t : K,
      z = proj 3 K (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g) := by
  unfold rootImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_rootGrp hij).mp hy
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, rootGrp_mem hij t, rfl⟩

theorem isPGroup_rootImg {p : ℕ} [Fact p.Prime] [CharP K p] (g : SL(3, K)) {i j : Fin 3}
    (hij : i ≠ j) : IsPGroup p (rootImg g hij) := by
  intro z
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp z.2
  show (z : projectiveSL 3 K) ^ p ^ 1 = 1
  rw [pow_one, ← hyz, ← map_pow, rootGrp_pow hij hy, map_one]

theorem rootImg_ne_bot {g : SL(3, K)} {i j : Fin 3} (hij : i ≠ j) : rootImg g hij ≠ ⊥ := by
  intro h
  have hmem : proj 3 K (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij 1 * g) ∈
      rootImg g hij := (mem_rootImg hij).mpr ⟨1, rfl⟩
  rw [h, Subgroup.mem_bot, proj_eq_one_iff, scalars_eq_center] at hmem
  have hT : Matrix.SpecialLinearGroup.transvection hij (1 : K) ∈ Subgroup.center SL(3, K) := by
    have h1 := Subgroup.mem_center_iff.mp hmem g
    have e : Matrix.SpecialLinearGroup.transvection hij (1 : K) =
        g⁻¹ * Matrix.SpecialLinearGroup.transvection hij 1 * g :=
      calc Matrix.SpecialLinearGroup.transvection hij (1 : K)
          = g * (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij 1 * g) * g⁻¹ := by group
        _ = (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij 1 * g) * g * g⁻¹ := by rw [h1]
        _ = g⁻¹ * Matrix.SpecialLinearGroup.transvection hij 1 * g := by group
    rw [e]
    exact hmem
  rw [← scalars_eq_center, mem_scalars] at hT
  obtain ⟨c, -, hc'⟩ := hT
  have := congrFun (congrFun hc' i) j
  have h3 : ((Matrix.SpecialLinearGroup.transvection hij (1 : K) : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) i j = 1 := by
    show (1 + Matrix.single i j (1 : K)) i j = 1
    simp [hij]
  rw [h3] at this
  simp [Matrix.scalar_apply, hij] at this

theorem yy_add (g : SL(3, K)) {i j : Fin 3} (hij : i ≠ j) (a b : K) :
    (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij a * g) *
        (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij b * g) =
      g⁻¹ * Matrix.SpecialLinearGroup.transvection hij (a + b) * g := by
  rw [Matrix.SpecialLinearGroup.transvection_add]
  group

theorem yy_inv (g : SL(3, K)) {i j : Fin 3} (hij : i ≠ j) (a : K) :
    (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij a * g)⁻¹ =
      g⁻¹ * Matrix.SpecialLinearGroup.transvection hij (-a) * g := by
  rw [← Matrix.SpecialLinearGroup.transvection_inv]
  group

section Member

variable [Finite K]

theorem proj_mem_normalizer_rootImg {g h : SL(3, K)} (hh : IsDiagIn g h) {i j : Fin 3}
    (hij : i ≠ j) :
    proj 3 K h ∈ Subgroup.normalizer (rootImg g hij : Set (projectiveSL 3 K)) := by
  apply mem_normalizer_of_conj_mem
  intro z hz
  obtain ⟨t, rfl⟩ := (mem_rootImg hij).mp hz
  refine (mem_rootImg hij).mpr ⟨dg g h i * (dg g h j)⁻¹ * t, ?_⟩
  rw [← conj_rootGrp hh hij t]
  simp

theorem le_normalizer_rootImg {A : Subgroup (projectiveSL 3 K)} (hA : IsElemAbelian 2 A)
    {g : SL(3, K)} (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j) :
    A ≤ Subgroup.normalizer (rootImg g hij : Set (projectiveSL 3 K)) := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := exists_invLift hA ha
  exact proj_mem_normalizer_rootImg (hg x hx) hij

theorem mem_normalizer_rootImg_of_centralizes (hK2 : (2 : K) ≠ 0)
    {A : Subgroup (projectiveSL 3 K)} (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    {g : SL(3, K)} (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j)
    {t : projectiveSL 3 K} (ht : ∀ a ∈ A, t * a = a * t) :
    t ∈ Subgroup.normalizer (rootImg g hij : Set (projectiveSL 3 K)) := by
  obtain ⟨h, rfl⟩ := proj_surjective 3 K t
  have hh : ∀ x ∈ invLifts A hA, h * x = x * h := fun x hx =>
    (commute_of_proj_commute_two hx.2 (ht _ hx.1).symm).symm
  exact proj_mem_normalizer_rootImg (isDiagIn_of_commute hK2 hA hA4 hg hh) hij

theorem commutator_rootImg (hK2 : (2 : K) ≠ 0) {A : Subgroup (projectiveSL 3 K)}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {g : SL(3, K)}
    (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j) :
    ⁅rootImg g hij, A⁆ = rootImg g hij := by
  refine le_antisymm (commutator_le_of_le_normalizer (le_normalizer_rootImg hA hg hij)) ?_
  intro z hz
  obtain ⟨s, rfl⟩ := (mem_rootImg hij).mp hz
  obtain ⟨x, hx, hxij⟩ := exists_sign_neg_one hA hA4 hg hij
  have hdj : (dg g x j)⁻¹ = dg g x j := inv_eq_of_mul_eq_one_right (dg_sq (hg x hx) hx.2 j)
  have h2 : (2 : K) ≠ 0 := hK2
  set u : K := s / 2 with hu
  have hyu : ⁅proj 3 K (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g), proj 3 K x⁆ =
      proj 3 K (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij s * g) := by
    have key : (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g) * x *
        (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g)⁻¹ * x⁻¹ =
        g⁻¹ * Matrix.SpecialLinearGroup.transvection hij s * g := by
      have e1 : x * (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g)⁻¹ * x⁻¹ =
          g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g := by
        rw [yy_inv, conj_rootGrp (hg x hx) hij, hdj]
        congr 3
        have : dg g x i * dg g x j = -1 := hxij
        calc dg g x i * dg g x j * -u = -(dg g x i * dg g x j) * u := by ring
          _ = u := by rw [this]; ring
      calc (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g) * x *
          (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g)⁻¹ * x⁻¹
          = (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g) *
            (x * (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g)⁻¹ * x⁻¹) := by group
        _ = (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g) *
            (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * g) := by rw [e1]
        _ = g⁻¹ * Matrix.SpecialLinearGroup.transvection hij (u + u) * g := yy_add g hij u u
        _ = g⁻¹ * Matrix.SpecialLinearGroup.transvection hij s * g := by
          rw [hu]; congr 3; field_simp; ring
    rw [commutatorElement_def]
    simp only [← map_inv, ← map_mul]
    rw [key]
  rw [← hyu]
  exact Subgroup.commutator_mem_commutator ((mem_rootImg hij).mpr ⟨u, rfl⟩) hx.1

theorem relIndex_centralizer_rootImg_le_two {A : Subgroup (projectiveSL 3 K)}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {g : SL(3, K)}
    (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j) :
    (A ⊓ Subgroup.centralizer (rootImg g hij : Set (projectiveSL 3 K))).relIndex A ≤ 2 := by
  obtain ⟨x₀, hx₀, hx₀ij⟩ := exists_sign_neg_one hA hA4 hg hij
  set C : Subgroup (projectiveSL 3 K) :=
    A ⊓ Subgroup.centralizer (rootImg g hij : Set (projectiveSL 3 K)) with hC
  have hsign : ∀ x ∈ invLifts A hA, dg g x i * dg g x j = 1 ∨ dg g x i * dg g x j = -1 := by
    intro x hx
    apply mul_self_eq_one_iff.mp
    calc (dg g x i * dg g x j) * (dg g x i * dg g x j)
        = (dg g x i * dg g x i) * (dg g x j * dg g x j) := by ring
      _ = 1 := by rw [dg_sq (hg x hx) hx.2, dg_sq (hg x hx) hx.2, one_mul]
  have hcent : ∀ x ∈ invLifts A hA, dg g x i * dg g x j = 1 → proj 3 K x ∈ C := by
    intro x hx h1
    refine Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    obtain ⟨t, rfl⟩ := (mem_rootImg hij).mp hz
    have hdj : (dg g x j)⁻¹ = dg g x j := inv_eq_of_mul_eq_one_right (dg_sq (hg x hx) hx.2 j)
    have h2 : x * (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g) * x⁻¹ =
        g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g := by
      rw [conj_rootGrp (hg x hx) hij, hdj, h1, one_mul]
    have h3 : (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g) * x =
        x * (g⁻¹ * Matrix.SpecialLinearGroup.transvection hij t * g) := by
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [← map_mul, ← map_mul, h3]
  unfold Subgroup.relIndex Subgroup.index
  let f : Fin 2 → ↥A ⧸ C.subgroupOf A := fun b =>
    if b = 0 then (QuotientGroup.mk (1 : ↥A) : ↥A ⧸ C.subgroupOf A)
    else ((⟨(proj 3 K x₀)⁻¹, A.inv_mem hx₀.1⟩ : ↥A) : ↥A ⧸ C.subgroupOf A)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, rfl⟩ := exists_invLift hA ha
    rcases hsign x hx with h1 | h1
    · refine ⟨0, ?_⟩
      show (QuotientGroup.mk (1 : ↥A) : ↥A ⧸ C.subgroupOf A) = _
      rw [QuotientGroup.eq]
      refine (Subgroup.mem_subgroupOf).mpr ?_
      have := hcent x hx h1
      simpa using C.inv_mem this
    · refine ⟨1, ?_⟩
      show ((⟨(proj 3 K x₀)⁻¹, A.inv_mem hx₀.1⟩ : ↥A) : ↥A ⧸ C.subgroupOf A) = _
      rw [QuotientGroup.eq]
      refine (Subgroup.mem_subgroupOf).mpr ?_
      have hm : x₀ * x ∈ invLifts A hA := (invLifts A hA).mul_mem hx₀ hx
      have h2 : dg g (x₀ * x) i * dg g (x₀ * x) j = 1 := by
        rw [dg_mul (hg x₀ hx₀) (hg x hx), dg_mul (hg x₀ hx₀) (hg x hx)]
        calc dg g x₀ i * dg g x i * (dg g x₀ j * dg g x j)
            = (dg g x₀ i * dg g x₀ j) * (dg g x i * dg g x j) := by ring
          _ = 1 := by rw [hx₀ij, h1]; ring
      have := hcent _ hm h2
      rw [map_mul] at this
      simpa [mul_inv_rev] using this
  exact (Nat.card_le_card_of_surjective f hf).trans (by simp)

theorem isE_one_root {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {T A : Subgroup (projectiveSL 3 K)} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (hO2 : pCoreOf 2 (⊤ : Subgroup (projectiveSL 3 K)) = ⊥) {g : SL(3, K)}
    (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j) :
    IsE 1 ⊤ T A (rootImg g hij ⊔ tauOf ⊤ T A) := by
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have hτ : tauOf ⊤ T A ≤ Subgroup.normalizer (rootImg g hij : Set (projectiveSL 3 K)) := by
    intro t ht
    obtain ⟨-, -, hc⟩ := mem_tauOf.mp ht
    refine mem_normalizer_rootImg_of_centralizes hK2 hA hA4 hg hij fun a ha => ?_
    have := hc a ha
    rw [hO2, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  exact (isE_one_sup Fact.out hp2 hT hAT hA (isPGroup_rootImg g hij) (rootImg_ne_bot hij) hτ
    (commutator_rootImg hK2 hA hA4 hg hij) (B := A ⊓ Subgroup.centralizer
      (rootImg g hij : Set (projectiveSL 3 K))) inf_le_left inf_le_right
    (relIndex_centralizer_rootImg_le_two hA hA4 hg hij)).1

end Member

theorem iSup_rootGrp_eq_top (g : SL(3, K)) :
    (⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j), rootGrp g hij) = ⊤ := by
  set H : Subgroup SL(3, K) := ⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j), rootGrp g hij with hH
  have hcl : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) K → SL(3, K))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  set H' : Subgroup SL(3, K) := H.comap (MulAut.conj g⁻¹).toMonoidHom with hH'
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) K → SL(3, K))) ≤ H' := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [SetLike.mem_coe, hH', Subgroup.mem_comap, Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (Matrix.SpecialLinearGroup.transvection hij c) =
        g⁻¹ * Matrix.SpecialLinearGroup.transvection hij c * g := by
      simp
    rw [h1]
    have hsub : rootGrp g hij ≤ H := le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hij le_rfl))
    exact hsub (rootGrp_mem hij c)
  rw [hcl] at hle
  refine eq_top_iff.mpr fun y _ => ?_
  have h2 := hle (Subgroup.mem_top (g * y * g⁻¹))
  rw [hH', Subgroup.mem_comap] at h2
  have h3 : (MulAut.conj g⁻¹).toMonoidHom (g * y * g⁻¹) = y := by
    show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
    group
  rwa [h3] at h2

theorem iSup_rootImg_eq_top (g : SL(3, K)) :
    (⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j), rootImg g hij) = ⊤ := by
  have h : (⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j), rootImg g hij) =
      (⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j), rootGrp g hij).map (proj 3 K) := by
    simp only [Subgroup.map_iSup]
    rfl
  rw [h, iSup_rootGrp_eq_top, Subgroup.map_top, MonoidHom.range_eq_top]
  exact proj_surjective 3 K

section Generation

variable [Finite K]

theorem iSup_isE_one_eq_top {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {T A : Subgroup (projectiveSL 3 K)} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (hO2 : pCoreOf 2 (⊤ : Subgroup (projectiveSL 3 K)) = ⊥) :
    T ⊔ ⨆ M ∈ {M : Subgroup (projectiveSL 3 K) | IsE 1 ⊤ T A M}, M = ⊤ := by
  obtain ⟨g, hg⟩ := exists_frame hp2 hA
  have hle : (⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j), rootImg g hij) ≤
      T ⊔ ⨆ M ∈ {M : Subgroup (projectiveSL 3 K) | IsE 1 ⊤ T A M}, M := by
    refine le_sup_of_le_right (iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_)
    exact le_iSup₂_of_le (rootImg g hij ⊔ tauOf ⊤ T A)
      (isE_one_root hp2 hT hAT hA hA4 hO2 hg hij) le_sup_left
  exact eq_top_iff.mpr ((iSup_rootImg_eq_top g).ge.trans hle)

end Generation

end CFSG.Quasithin.E22S
