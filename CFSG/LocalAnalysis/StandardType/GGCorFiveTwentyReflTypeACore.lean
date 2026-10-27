module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

section RankOne

variable {M : Type*} [Group M]

theorem pseudoRefl_rank_one (hp : p.Prime) {A : Subgroup M} [Finite A]
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {β : M} (hN : ∀ a ∈ A, β * a * β⁻¹ ∈ A)
    (hfix : Nat.card {a : A // β * (a : M) * β⁻¹ = a} * p = Nat.card A) {a₁ a₂ : M}
    (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A) :
    β * a₁ * β⁻¹ = a₁ ∨ ∃ e : ℕ, β * (a₁ ^ e * a₂⁻¹) * β⁻¹ = a₁ ^ e * a₂⁻¹ := by
  have := Fact.mk hp
  let δ : A →* A :=
    { toFun := fun a => ⟨β * a * β⁻¹ * (a : M)⁻¹, A.mul_mem (hN _ a.2) (A.inv_mem a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hc := hAc _ (A.mul_mem (hN _ b.2) (A.inv_mem b.2)) _ (A.inv_mem a.2)
        simp only [Subgroup.coe_mul]
        calc β * ((a : M) * b) * β⁻¹ * ((a : M) * b)⁻¹
            = β * a * β⁻¹ * (β * b * β⁻¹ * (b : M)⁻¹ * (a : M)⁻¹) := by group
          _ = β * a * β⁻¹ * ((a : M)⁻¹ * (β * b * β⁻¹ * (b : M)⁻¹)) := by rw [hc]
          _ = β * a * β⁻¹ * (a : M)⁻¹ * (β * b * β⁻¹ * (b : M)⁻¹) := by group) }
  have hδ1 : ∀ a : A, δ a = 1 ↔ β * (a : M) * β⁻¹ = a := by
    intro a
    rw [← Subtype.coe_inj, Subgroup.coe_one]
    exact mul_inv_eq_one
  have hker : Nat.card δ.ker = Nat.card {a : A // β * (a : M) * β⁻¹ = a} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [MonoidHom.mem_ker, hδ1])
  have hrange : Nat.card δ.range = p := by
    have h1 := δ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, ← hfix] at h1
    have hpos : 0 < Nat.card {a : A // β * (a : M) * β⁻¹ = a} := by
      rw [← hker]
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  by_cases ha₁ : δ ⟨a₁, h₁⟩ = 1
  · exact Or.inl ((hδ1 _).mp ha₁)
  right
  have hpow : δ ⟨a₁, h₁⟩ ^ p = 1 := by
    have h1 := pow_card_eq_one' (G := δ.range) (x := ⟨δ ⟨a₁, h₁⟩, ⟨_, rfl⟩⟩)
    rw [hrange] at h1
    simpa using congrArg Subtype.val h1
  have hz : Subgroup.zpowers (δ ⟨a₁, h₁⟩) = δ.range := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := δ.range)).mpr ⟨_, rfl⟩)
    rw [Nat.card_zpowers, orderOf_eq_prime hpow ha₁, hrange]
  have h2 : δ ⟨a₂, h₂⟩ ∈ Submonoid.powers (δ ⟨a₁, h₁⟩) :=
    mem_powers_iff_mem_zpowers.mpr (by rw [hz]; exact ⟨_, rfl⟩)
  obtain ⟨e, he⟩ := h2
  have he' : δ ⟨a₁, h₁⟩ ^ e = δ ⟨a₂, h₂⟩ := he
  refine ⟨e, ?_⟩
  have h3 : δ (⟨a₁, h₁⟩ ^ e * (⟨a₂, h₂⟩ : A)⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, he', mul_inv_cancel]
  simpa using (hδ1 _).mp h3

end RankOne

theorem exists_fin_avoid_four (hd : 5 ≤ d) (a b c e : Fin d) :
    ∃ w : Fin d, w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ e := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {a, b, c, e} := fun w _ => by
    by_cases h1 : w = a
    · simp [h1]
    by_cases h2 : w = b
    · simp [h2]
    by_cases h3 : w = c
    · simp [h3]
    simp [h w h1 h2 h3]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({a, b, c, e} : Finset (Fin d)).card ≤ 4 := Finset.card_le_four
  omega

theorem exists_three_fixed_of_supports (hd : 5 ≤ d) (π : Equiv.Perm (Fin d))
    (h : ∀ i j k : Fin d, i ≠ j → i ≠ k → j ≠ k → ∃ S : Fin d → Prop,
      (∀ l, S l → l = i ∨ l = j ∨ l = k) ∧ (∀ l, S l → S (π l)) ∧ ∃ x y, x ≠ y ∧ S x ∧ S y) :
    ∃ i j k : Fin d, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ π i = i ∧ π j = j ∧ π k = k := by
  have hmoved : ∀ x, π x ≠ x → ∀ y, π y ≠ y → y = x ∨ y = π x := by
    intro x hx y hy
    by_contra hne
    push Not at hne
    obtain ⟨hyx, hyπx⟩ := hne
    obtain ⟨w, hwx, hwπx, hwy, hwπy⟩ := exists_fin_avoid_four hd x (π x) y (π y)
    obtain ⟨S, hS3, hSπ, u, v, huv, hu, hv⟩ := h x y w (Ne.symm hyx) (Ne.symm hwx) (Ne.symm hwy)
    have hxy : S x ∨ S y := by
      by_contra hne
      push Not at hne
      have hu' : u = w := by
        rcases hS3 u hu with h1 | h1 | h1
        · exact absurd (h1 ▸ hu) hne.1
        · exact absurd (h1 ▸ hu) hne.2
        · exact h1
      have hv' : v = w := by
        rcases hS3 v hv with h1 | h1 | h1
        · exact absurd (h1 ▸ hv) hne.1
        · exact absurd (h1 ▸ hv) hne.2
        · exact h1
      exact huv (hu'.trans hv'.symm)
    have hSx : ¬ S x := by
      intro hSx
      rcases hS3 _ (hSπ x hSx) with h1 | h1 | h1
      · exact hx h1
      · exact hyπx h1.symm
      · exact hwπx h1.symm
    rcases hxy with hSx' | hSy
    · exact hSx hSx'
    · rcases hS3 _ (hSπ y hSy) with h1 | h1 | h1
      · exact hSx (h1 ▸ hSπ y hSy)
      · exact hy h1
      · exact hwπy h1.symm
  by_cases hπ : ∃ x, π x ≠ x
  · obtain ⟨x, hx⟩ := hπ
    have hfix : ∀ l, l ≠ x → l ≠ π x → π l = l := by
      intro l hlx hlπx
      by_contra hl
      rcases hmoved x hx l hl with h1 | h1
      · exact hlx h1
      · exact hlπx h1
    obtain ⟨i, hix, hiπx, -, -⟩ := exists_fin_avoid_four hd x (π x) x x
    obtain ⟨j, hjx, hjπx, hji, -⟩ := exists_fin_avoid_four hd x (π x) i i
    obtain ⟨k, hkx, hkπx, hki, hkj⟩ := exists_fin_avoid_four hd x (π x) i j
    exact ⟨i, j, k, Ne.symm hji, Ne.symm hki, Ne.symm hkj, hfix i hix hiπx, hfix j hjx hjπx,
      hfix k hkx hkπx⟩
  · push Not at hπ
    exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], hπ _, hπ _, hπ _⟩

section NormalForm

variable [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
  {X : Subgroup (MulAut (projectiveSL d K))} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)

theorem exists_pow_eq_ringEquiv (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (σ : K ≃+* K) :
    ∃ c : ℕ, ∀ y : K, y ^ p = 1 → σ y = y ^ c := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  obtain ⟨c, -, hc⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨c, fun y hy => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  rw [map_pow, ← hc, ← pow_mul, ← pow_mul, mul_comm]

include hXc in
theorem conjMat_pow_apply {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc) (e : ℕ) (k : Fin d) :
    conjMat A₀ (g ^ e) k k = conjMat A₀ g k k ^ e := by
  have h := (conjMat_diag hg.1 (hdiag g hg)).1
  calc conjMat A₀ (g ^ e) k k = (conjMat A₀ g ^ e) k k := by rw [conjMat_pow]
    _ = (diagonal (fun i => conjMat A₀ g i i) ^ e) k k := by rw [← h]
    _ = conjMat A₀ g k k ^ e := by rw [diagonal_pow, diagonal_apply_eq, Pi.pow_apply]

include hXc in
theorem dualConj_slLift {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc) :
    (conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀ * conjAut d K (SpecialLinearGroup.toGL g) *
        ((conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀)⁻¹ =
      conjAut d K (SpecialLinearGroup.toGL g⁻¹) := by
  have htrans := standard_automorphism_transport (K := K) (n := d)
  have hδ : (dualAut d K)⁻¹ = dualAut d K := inv_eq_of_mul_eq_one_right htrans.2.2.2.1
  have hg' : g⁻¹ ∈ slLift hd hpd X hXc := (slLift hd hpd X hXc).inv_mem hg
  have hIT : GeneralLinearGroup.inverseTranspose (A₀ * SpecialLinearGroup.toGL g * A₀⁻¹) =
      A₀ * SpecialLinearGroup.toGL g⁻¹ * A₀⁻¹ := by
    have e : (A₀ * SpecialLinearGroup.toGL g * A₀⁻¹)⁻¹ =
        A₀ * SpecialLinearGroup.toGL g⁻¹ * A₀⁻¹ := by
      rw [map_inv]
      group
    have hD : ((A₀ * SpecialLinearGroup.toGL g⁻¹ * A₀⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (fun i => conjMat A₀ g⁻¹ i i) := by
      rw [coe_conj_toGL]
      exact (conjMat_diag hg'.1 (hdiag _ hg')).1
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose, e, hD, diagonal_transpose]
  calc (conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀ *
        conjAut d K (SpecialLinearGroup.toGL g) *
        ((conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀)⁻¹
      = (conjAut d K A₀)⁻¹ * (dualAut d K *
          conjAut d K (A₀ * SpecialLinearGroup.toGL g * A₀⁻¹) * dualAut d K) *
          conjAut d K A₀ := by
        rw [conjAut_conj, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hδ]
        group
    _ = conjAut d K (SpecialLinearGroup.toGL g⁻¹) := by
        rw [htrans.2.2.2.2.1, hIT, conjAut_conj]
        group

include hXc in
theorem exists_pow_normal_form (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd3 : 3 ≤ d) (hXp : ∀ x ∈ X, x ^ p = 1)
    (hXI : ∀ x ∈ X, ∃ A : GL (Fin d) K, conjAut d K A = x) {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ g ∈ slLift hd hpd X hXc, conjMat A₀ g = diagonal t)
    {β' : MulAut (projectiveSL d K)} (hN : ∀ x ∈ X, β' * x * β'⁻¹ ∈ X) :
    ∃ (π : Equiv.Perm (Fin d)) (m : ℕ), ∀ g ∈ slLift hd hpd X hXc, ∀ g' ∈ slLift hd hpd X hXc,
      conjAut d K (SpecialLinearGroup.toGL g') =
          β' * conjAut d K (SpecialLinearGroup.toGL g) * β'⁻¹ →
        ∀ k, conjMat A₀ g' k k = conjMat A₀ g (π k) (π k) ^ m := by
  have htrans := standard_automorphism_transport (K := K) (n := d)
  obtain ⟨A, σ, ε, hε, hβ⟩ := (automorphism_generation (K := K) hd3).2 β'
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hβ
    subst hβ
    obtain ⟨π, -, hform⟩ := semilinear_normal_form hd hpd hXc hp hp2 hpK hXp hXI hdiag hfull A σ hN
    obtain ⟨c, hc⟩ := exists_pow_eq_ringEquiv hp hpK σ
    refine ⟨π, c, fun g hg g' hg' hgg' k => ?_⟩
    rw [hform g hg g' hg' hgg' k, hc _ ((conjMat_diag hg.1 (hdiag g hg)).2.1 _)]
  ·
    rw [pow_one] at hβ
    obtain ⟨ι, hι⟩ : ∃ ι : MulAut (projectiveSL d K),
        ι = (conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀ := ⟨_, rfl⟩
    have hιι : ι * ι = 1 := by
      rw [hι]
      calc (conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀ *
            ((conjAut d K A₀)⁻¹ * dualAut d K * conjAut d K A₀)
          = (conjAut d K A₀)⁻¹ * (dualAut d K * dualAut d K) * conjAut d K A₀ := by group
        _ = 1 := by rw [htrans.2.2.2.1, mul_one, inv_mul_cancel]
    have hιg : ∀ g ∈ slLift hd hpd X hXc, ι * conjAut d K (SpecialLinearGroup.toGL g) * ι⁻¹ =
        conjAut d K (SpecialLinearGroup.toGL g⁻¹) := fun g hg => by
      rw [hι]
      exact dualConj_slLift hd hpd hXc hdiag hg
    have hconj : ∀ x : MulAut (projectiveSL d K),
        β' * ι * (ι * x * ι⁻¹) * (β' * ι)⁻¹ = β' * x * β'⁻¹ := by
      intro x
      calc β' * ι * (ι * x * ι⁻¹) * (β' * ι)⁻¹ = β' * (ι * ι) * x * (ι * ι)⁻¹ * β'⁻¹ := by
            group
        _ = β' * x * β'⁻¹ := by rw [hιι, mul_one, inv_one, mul_one]
    have hsemi : β' * ι ∈ semilinearAutGroup d K := by
      have e : β' * ι = conjAut d K A * fieldAut d K σ *
          (dualAut d K * conjAut d K A₀⁻¹ * dualAut d K) * conjAut d K A₀ := by
        rw [hβ, hι, map_inv]
        group
      have hlin : ∀ B : GL (Fin d) K, conjAut d K B ∈ semilinearAutGroup d K := fun B =>
        linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup B)
      rw [e]
      exact mul_mem (mul_mem (mul_mem (hlin A) (fieldAut_mem_semilinearAutGroup σ))
        (dualAut_mul_mul_dualAut_mem (hlin _))) (hlin A₀)
    obtain ⟨A', σ', hA'⟩ := mem_semilinearAutGroup_iff.mp hsemi
    have hN' : ∀ x ∈ X, conjAut d K A' * fieldAut d K σ' * x *
        (conjAut d K A' * fieldAut d K σ')⁻¹ ∈ X := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := exists_mem_slLift_of_mem hd hpd hXc hXp hXI hx
      have hg1 : g⁻¹ ∈ slLift hd hpd X hXc := (slLift hd hpd X hXc).inv_mem hg
      have e1 := hιg g⁻¹ hg1
      rw [inv_inv] at e1
      rw [← hA', ← e1, hconj]
      exact hN _ hg1.2
    obtain ⟨π, -, hform⟩ :=
      semilinear_normal_form hd hpd hXc hp hp2 hpK hXp hXI hdiag hfull A' σ' hN'
    obtain ⟨c, hc⟩ := exists_pow_eq_ringEquiv hp hpK σ'
    refine ⟨π, (p - 1) * c, fun g hg g' hg' hgg' k => ?_⟩
    have hg1 : g⁻¹ ∈ slLift hd hpd X hXc := (slLift hd hpd X hXc).inv_mem hg
    have hgg'' : conjAut d K (SpecialLinearGroup.toGL g') = conjAut d K A' * fieldAut d K σ' *
        conjAut d K (SpecialLinearGroup.toGL g⁻¹) * (conjAut d K A' * fieldAut d K σ')⁻¹ := by
      rw [← hA', ← hιg g hg, hconj, hgg']
    obtain ⟨y, hy⟩ : ∃ y, y = conjMat A₀ g (π k) (π k) := ⟨_, rfl⟩
    have hyp : y ^ p = 1 := hy ▸ (conjMat_diag hg.1 (hdiag g hg)).2.1 _
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hyp
      exact zero_ne_one hyp
    have hyinv : y⁻¹ = y ^ (p - 1) := by
      symm
      rw [← mul_eq_one_iff_eq_inv₀ hy0, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hyp]
    rw [hform g⁻¹ hg1 g' hg' hgg'' k, conjMat_inv_apply hd hpd hXc hdiag hg, ← hy,
      hc _ (by rw [inv_pow, hyp, inv_one]), hyinv, ← pow_mul]

include hXc in
theorem permConj_conj_slLift [CharP K 2] {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ g ∈ slLift hd hpd X hXc, conjMat A₀ g = diagonal t)
    (τ : Equiv.Perm (Fin d)) {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc) :
    permConj A₀ τ * g * (permConj A₀ τ)⁻¹ ∈ slLift hd hpd X hXc ∧
      ∀ l, conjMat A₀ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹) l l = conjMat A₀ g (τ l) (τ l) := by
  obtain ⟨t, ht⟩ : ∃ t : Fin d → K, t = fun l => conjMat A₀ g l l := ⟨_, rfl⟩
  have hgd := conjMat_diag hg.1 (hdiag g hg)
  have hgt : conjMat A₀ g = diagonal t := ht ▸ hgd.1
  have hMN : conjMat A₀ (permConj A₀ τ) * conjMat A₀ (permConj A₀ τ)⁻¹ = 1 := by
    rw [← conjMat_mul, mul_inv_cancel, conjMat_one]
  have hc : conjMat A₀ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹) = diagonal (t ∘ τ) := by
    rw [conjMat_mul, conjMat_mul, hgt, conjMat_permConj, permMatrix_mul_diagonal,
      Matrix.mul_assoc, ← conjMat_permConj A₀ τ, hMN, Matrix.mul_one]
  obtain ⟨g'', hg'', hg''t⟩ := hfull (t ∘ τ) (fun l => by rw [ht]; exact hgd.2.1 (τ l))
    (by simp only [Function.comp_apply]; rw [Equiv.prod_comp τ t, ht]; exact hgd.2.2)
  have heq : permConj A₀ τ * g * (permConj A₀ τ)⁻¹ = g'' :=
    conjMat_injective (A := A₀) (hc.trans hg''t.symm)
  refine ⟨heq ▸ hg'', fun l => ?_⟩
  rw [hc, hgt, diagonal_apply_eq, diagonal_apply_eq]
  rfl

end NormalForm

end CFSG.StandardType.TypeA

end
