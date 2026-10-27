module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode

public section

namespace CFSG.StandardType

namespace TableBUD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag TableBUE
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] {n d : ℕ}

section Frame

variable (h : UnitaryFieldData 2 n K)

include h in
theorem mem_guSet_of_mem_primeFormUnitary {P : GL (Fin d) K}
    (hP : P ∈ primeFormUnitary h (idGram K d)) : P ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  have h1 : ((P : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * ((1 : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) * (P : Matrix (Fin d) (Fin d) K) = ((1 : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) := hP
  rw [Units.val_one, Matrix.mul_one] at h1
  rw [one_smul, ← map_pow_eq_map_bar h] at *
  exact h1

theorem conjProj_projConj (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d))
    (M : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hM' : P⁻¹ * (M : GL (Fin d) K) * P ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (r : LargeEvenProj (unitarySU 2 n K d)) :
    conjProj h P hP (TableB.projConj _ M r) =
      TableB.projConj _ ⟨P⁻¹ * (M : GL (Fin d) K) * P, hM'⟩ (conjProj h P hP r) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ r
  rw [show (QuotientGroup.mk' _ x : LargeEvenProj (unitarySU 2 n K d)) =
    LargeEvenProjMk (unitarySU 2 n K d) x from rfl, projConj_mk_coe, conjProj_mk, conjProj_mk,
    projConj_mk_coe]
  congr 1
  apply Subtype.ext
  show P⁻¹ * ((M : GL (Fin d) K) * x * (M : GL (Fin d) K)⁻¹) * P =
    (P⁻¹ * M * P) * (P⁻¹ * x * P) * (P⁻¹ * M * P)⁻¹
  group

variable [Finite K]

private theorem exists_induced_data [Finite K] (h : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    ∃ (X : Subgroup (MulAut (projectiveSL d K))) (Mf : Ab → GL (Fin d) K)
      (hMf : ∀ a, Mf a ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
      (hXmem : ∀ a, conjAut d K (Mf a) ∈ X),
      IsElemAbelian p X ∧
      (∀ x ∈ X, ∃ (M : GL (Fin d) K) (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
        conjAut d K M = x ∧
        TableB.projConj (unitarySU 2 n K d) ⟨M, gu_subset_normalizer h hM⟩ ∈ Ab) ∧
      (∀ a : Ab, (a : MulAut (LargeEvenProj (unitarySU 2 n K d))) =
        TableB.projConj (unitarySU 2 n K d) ⟨Mf a, gu_subset_normalizer h (hMf a)⟩) ∧
      Nat.card Ab ≤ Nat.card X := by
  classical
  have hN := gu_subset_normalizer (d := d) h
  set ρ := TableB.projConj (unitarySU 2 n K d) with hρ
  set N₀ : Subgroup (Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :=
    Ab.comap ρ with hN₀
  set χ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) →*
      MulAut (projectiveSL d K) :=
    (conjAut d K).comp (Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))).subtype
    with hχ
  set X := N₀.map χ with hX
  have hscal : ∀ M, ρ M = 1 → χ M = 1 := by
    intro M hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hXab : IsElemAbelian p X := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hAb hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (by rw [map_pow]; exact hAb.2 _ hM)
  have hXU : ∀ x ∈ X, ∃ (M : GL (Fin d) K) (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      conjAut d K M = x ∧ ρ ⟨M, hN hM⟩ ∈ Ab := by
    rintro _ ⟨M, hM, rfl⟩
    obtain ⟨M', hM'gu, hM'eq⟩ := TableB.exists_eq_projConj hN (hAbI _ hM)
    have hM'eq' : ρ M = ρ ⟨M', hN hM'gu⟩ := hM'eq
    have h1 : ρ ((⟨M', hN hM'gu⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))⁻¹ * M) = 1 := by
      rw [map_mul, map_inv, hM'eq', inv_mul_cancel]
    have h2 := hscal _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    refine ⟨M', hM'gu, h2, ?_⟩
    rw [← hM'eq']
    exact hM
  have hlift : ∀ a : Ab, ∃ (M : GL (Fin d) K) (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      (a : MulAut (LargeEvenProj (unitarySU 2 n K d))) = ρ ⟨M, hN hM⟩ :=
    fun a => TableB.exists_eq_projConj hN (hAbI a a.2)
  choose Mf hMf hMfeq using hlift
  have hMN : ∀ a : Ab, (⟨Mf a, hN (hMf a)⟩ :
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) ∈ N₀ := fun a => by
    show ρ _ ∈ Ab
    rw [← hMfeq a]
    exact a.2
  have hXmem : ∀ a, conjAut d K (Mf a) ∈ X := fun a => by
    refine ⟨⟨Mf a, hN (hMf a)⟩, hMN a, ?_⟩
    rfl
  let f : Ab → X := fun a => ⟨χ ⟨Mf a, hN (hMf a)⟩, _, hMN a, rfl⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : χ ((⟨Mf a, hN (hMf a)⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))⁻¹ *
          ⟨Mf b, hN (hMf b)⟩) = 1 := by
      have := congrArg Subtype.val hab
      simp only [f] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    have hz := mem_scalars_of_eq_scalar hc
    have h2 : ρ ((⟨Mf a, hN (hMf a)⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))⁻¹ *
          ⟨Mf b, hN (hMf b)⟩) = 1 := by
      have he : (⟨Mf a, hN (hMf a)⟩ :
          Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))⁻¹ *
            ⟨Mf b, hN (hMf b)⟩ = ⟨_, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
      rw [he]
      exact TableB.projConj_of_scalar _ hz
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    apply Subtype.ext
    rw [hMfeq a, hMfeq b, h2]
  have hle := Nat.card_le_card_of_injective f hf
  exact ⟨X, Mf, hMf, hXmem, hXab, hXU, hMfeq, hle⟩

theorem exists_unitary_frame_or_noncomm (h : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hcard : p ^ (d / p) < Nat.card Ab) :
    (∃ P ∈ primeFormUnitary h (idGram K d), ∀ a ∈ Ab, ∃ (M : GL (Fin d) K)
      (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K d) ⟨M, gu_subset_normalizer h hM⟩) ∨
    ∃ (x y : GL (Fin d) K) (hx : x ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
      (hy : y ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      TableB.projConj (unitarySU 2 n K d) ⟨x, gu_subset_normalizer h hx⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 n K d) ⟨y, gu_subset_normalizer h hy⟩ ∈ Ab ∧
      x ∈ primeFormUnitary h (idGram K d) ∧ x ^ p = 1 ∧
      ∃ u : Kˣ, u ≠ 1 ∧ u ^ p = 1 ∧ x * y = GeneralLinearGroup.scalar (Fin d) u * (y * x) := by
  classical
  have hd0 : 0 < d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  obtain ⟨X, Mf, hMf, hXmem, hXab, hXU, hMfeq, hle⟩ :=
    exists_induced_data h hK hd hdq hp hpq hAb hAbI
  have hcardX : p ^ (d / p) < Nat.card X := lt_of_lt_of_le hcard hle
  set G := X.comap (conjAut d K) with hGdef
  have hG : TypeA.PGLTor.IsProjElem p G := TypeA.isProjElem_comap hd0 hXab
  have hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    intro x hx
    obtain ⟨M, -, hconj, -⟩ := hXU x hx
    exact ⟨M, hconj⟩
  have hcardG : Nat.card G = Nat.card X * (Nat.card K - 1) := by
    rw [hGdef, TypeA.card_comap_eq hd0 hXI]
  by_cases hcent : ∀ g ∈ G, g ^ p = 1 → ∀ g' ∈ G, g' * g = g * g'
  · rcases TypeA.PGLTor.toral_or_card_le_of_central_sharp hp (ne_two_of_dvd h hpq)
      (dvd_card_sub_one' h hpq) hG hcent with htor | hbound
    · obtain ⟨P, hP, hPd⟩ := exists_unitary_diag_of_isToral h hp hpq hd0 hXab
        (fun x hx => by obtain ⟨M, hM, hconj, -⟩ := hXU x hx; exact ⟨M, hM, hconj⟩) htor
      exact Or.inl ⟨P, hP, fun a ha =>
        ⟨Mf ⟨a, ha⟩, hMf ⟨a, ha⟩, hPd _ (hXmem ⟨a, ha⟩), hMfeq ⟨a, ha⟩⟩⟩
    · exfalso
      rw [hcardG, Fintype.card_fin] at hbound
      have hK1 : 0 < Nat.card K - 1 := by
        have := Finite.one_lt_card (α := K)
        omega
      exact (not_le.mpr hcardX) (Nat.le_of_mul_le_mul_right hbound hK1)
  · push Not at hcent
    obtain ⟨g, hgG, hgp, g', hg'G, hne⟩ := hcent
    obtain ⟨M, hM, hMconj, hMAb⟩ := hXU (conjAut d K g) hgG
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one (A := g * M⁻¹) (by
      rw [map_mul, map_inv, hMconj, mul_inv_cancel])
    have hsc : g * M⁻¹ ∈ LargeEvenScalars (Fin d) K := mem_scalars_of_eq_scalar hc
    rw [largeEvenScalars_def] at hsc
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hsc
    have hgeq : g = GeneralLinearGroup.scalar (Fin d) s * M := by
      rw [hs]
      group
    have hgU : g ∈ primeFormUnitary h (idGram K d) := by
      refine mem_primeFormUnitary_of_pow_eq_one (c := (s : K)) h hpq hd0 hM ?_ hgp
      rw [hgeq, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul]
    have hx : g ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := mem_guSet_of_mem_primeFormUnitary h hgU
    have hxAb : TableB.projConj (unitarySU 2 n K d) ⟨g, gu_subset_normalizer h hx⟩ ∈ Ab := by
      have hnormM : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
        gu_subset_normalizer h hM
      have hnormg : g ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
        gu_subset_normalizer h hx
      have hsub : (⟨g, hnormg⟩ : Subgroup.normalizer
          (unitarySU 2 n K d : Set (GL (Fin d) K))) =
          ⟨GeneralLinearGroup.scalar (Fin d) s, TableB.scalar_mem_normalizer _
            (show GeneralLinearGroup.scalar (Fin d) s ∈ LargeEvenScalars (Fin d) K from
              ⟨s, rfl⟩)⟩ * ⟨M, hnormM⟩ := by
        apply Subtype.ext
        exact hgeq
      have hz : GeneralLinearGroup.scalar (Fin d) s ∈ LargeEvenScalars (Fin d) K := ⟨s, rfl⟩
      rw [hsub, map_mul, TableB.projConj_of_scalar _ hz, one_mul]
      exact hMAb
    obtain ⟨M', hM', hM'conj, hM'Ab⟩ := hXU (conjAut d K g') hg'G
    obtain ⟨c', hc'⟩ := TypeA.exists_scalar_of_conjAut_eq_one (A := g' * M'⁻¹) (by
      rw [map_mul, map_inv, hM'conj, mul_inv_cancel])
    have hsc' : g' * M'⁻¹ ∈ LargeEvenScalars (Fin d) K := mem_scalars_of_eq_scalar hc'
    rw [largeEvenScalars_def] at hsc'
    obtain ⟨s', hs'⟩ := MonoidHom.mem_range.mp hsc'
    have hg'eq : g' = GeneralLinearGroup.scalar (Fin d) s' * M' := by
      rw [hs']
      group
    let u : Kˣ := TypeA.PGLTor.commChar hG hgG ⟨g', hg'G⟩
    have hcomm : g * g' = GeneralLinearGroup.scalar (Fin d) u * (g' * g) :=
      TypeA.PGLTor.commChar_spec hG hgG ⟨g', hg'G⟩
    have hu1 : u ≠ 1 := by
      intro h1
      apply hne
      rw [hcomm, h1, map_one, one_mul]
    have hup : u ^ p = 1 := TypeA.PGLTor.commChar_pow_eq_one hG hgG ⟨g', hg'G⟩
    have hxy : g * M' = GeneralLinearGroup.scalar (Fin d) u * (M' * g) := by
      have h1 : GeneralLinearGroup.scalar (Fin d) s' * (g * M') =
          GeneralLinearGroup.scalar (Fin d) (u * s') * (M' * g) := by
        calc GeneralLinearGroup.scalar (Fin d) s' * (g * M')
            = g * (GeneralLinearGroup.scalar (Fin d) s' * M') := by
              rw [← mul_assoc, (TypeA.PGLTor.commute_scalar s' g).eq, mul_assoc]
          _ = g * g' := by rw [hg'eq]
          _ = GeneralLinearGroup.scalar (Fin d) u * (g' * g) := hcomm
          _ = GeneralLinearGroup.scalar (Fin d) u *
                (GeneralLinearGroup.scalar (Fin d) s' * M' * g) := by rw [hg'eq]
          _ = GeneralLinearGroup.scalar (Fin d) (u * s') * (M' * g) := by
              rw [mul_assoc, ← mul_assoc (GeneralLinearGroup.scalar (Fin d) u),
                ← map_mul]
      refine mul_left_cancel (a := GeneralLinearGroup.scalar (Fin d) s') ?_
      calc GeneralLinearGroup.scalar (Fin d) s' * (g * M')
          = GeneralLinearGroup.scalar (Fin d) (u * s') * (M' * g) := h1
        _ = GeneralLinearGroup.scalar (Fin d) s' *
              (GeneralLinearGroup.scalar (Fin d) u * (M' * g)) := by
            rw [show u * s' = s' * u from mul_comm u s', map_mul, mul_assoc]
    exact Or.inr ⟨g, M', hx, hM', hxAb, hM'Ab, hgU, hgp, u, hu1, hup, hxy⟩

include h in
theorem exists_unitary_frame (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hcard : p ^ (d / p + 2) ≤ Nat.card Ab) :
    ∃ P ∈ primeFormUnitary h (idGram K d), ∀ a ∈ Ab, ∃ (M : GL (Fin d) K)
      (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K d) ⟨M, gu_subset_normalizer h hM⟩ := by
  classical
  obtain ⟨X, Mf, hMf, hXmem, hXab, hXU, hMfeq, hle⟩ :=
    exists_induced_data h hK hd hdq hp hpq hAb hAbI
  obtain ⟨P, hP, hPd⟩ := ggPGUTorality h hp hpq hXab
    (fun x hx => by obtain ⟨M, hM, hconj, -⟩ := hXU x hx; exact ⟨M, hM, hconj⟩)
    (hcard.trans hle)
  exact ⟨P, hP, fun a ha => ⟨Mf ⟨a, ha⟩, hMf ⟨a, ha⟩,
    hPd _ (hXmem ⟨a, ha⟩), hMfeq ⟨a, ha⟩⟩⟩

end Frame

section EndNode

variable (h : UnitaryFieldData 2 n K) [Finite K]

include h in
theorem ggEndNode_unitary_sub_two (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d) :
    GGEndNode p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  classical
  have hp2 := ne_two_of_dvd h hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hN := gu_subset_normalizer (d := d) h
  set NN := Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) with hNN
  have hind : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (unitarySU 2 n K d)),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hcardAb := TypeA.card_inducedSub hψ hker hperf hind
  have hAbab : IsElemAbelian p Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ φ ∈ Ab, φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    rintro φ ⟨a, ha, hφ⟩
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    rwa [TypeA.induced_unique ψ hψ hφ hφ']
  have hk : d / p + 2 ≤ d - 2 := by
    have h4 : d / p ≤ d / 3 := Nat.div_le_div_left (by have := hp.two_le; omega) (by norm_num)
    omega
  obtain ⟨P, hP, hframe⟩ := exists_unitary_frame h hK (by omega) hdq hp hpq hAbab hAbI
    ((Nat.pow_le_pow_right hp.pos hk).trans (hcardAb ▸ hr))
  set σ := conjProj h P hP with hσ
  set ψ' : L' →* LargeEvenProj (unitarySU 2 n K d) := σ.toMonoidHom.comp ψ with hψ'def
  have hψ' : Function.Surjective ψ' := σ.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    have h1 : σ (ψ z) = 1 := hz
    exact (MulEquiv.map_eq_one_iff σ).mp h1
  have hPN : P ∈ NN := hN (mem_guSet_of_mem_primeFormUnitary h hP)
  have hmodel : ∀ a ∈ A, ∃ (τ : Fin d → Kˣ) (hτ : diagHom d τ ∈ NN),
      ∀ l, TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hτ⟩ (ψ' l) = ψ' (a l) := by
    intro a ha
    obtain ⟨φ, hφ⟩ := hind a ha
    obtain ⟨M, hM, hdiagM, hφM⟩ := hframe φ ⟨a, ha, hφ⟩
    obtain ⟨τ, hτ⟩ := exists_diagHom_of_isDiag hdiagM
    have hPMP : P⁻¹ * M * P ∈ NN := NN.mul_mem (NN.mul_mem (NN.inv_mem hPN) (hN hM)) hPN
    have hτN : diagHom d τ ∈ NN := hτ ▸ hPMP
    refine ⟨τ, hτN, fun l => ?_⟩
    have h1 := conjProj_projConj h P hP ⟨M, hN hM⟩ hPMP (ψ l)
    have h2 : (⟨P⁻¹ * M * P, hPMP⟩ : NN) = ⟨diagHom d τ, hτN⟩ := Subtype.ext hτ
    rw [h2, ← hφM, hφ] at h1
    exact h1.symm
  have hind' : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (unitarySU 2 n K d)),
      ∀ l, φ (ψ' l) = ψ' (a l) := fun a ha => by
    obtain ⟨τ, hτ, hτa⟩ := hmodel a ha
    exact ⟨_, hτa⟩
  have hcard' := TypeA.card_inducedSub hψ' hker' hperf hind'
  refine endNode_of_induced hψ' hker' hperf hind' ?_
  refine endNode_of_diag h hK hp hpq hd hq (TypeA.isElemAbelian_inducedSub hψ' hA) ?_
    (hcard' ▸ hr)
  rintro φ ⟨a, ha, hφ⟩
  obtain ⟨τ, hτ, hτa⟩ := hmodel a ha
  exact ⟨τ, hτ, TypeA.induced_unique ψ' hψ' hφ hτa⟩

end EndNode

end TableBUD

end CFSG.StandardType
