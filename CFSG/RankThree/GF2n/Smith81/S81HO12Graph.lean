module

public import CFSG.RankThree.GF2n.Smith81.S81HO12Flag
public import CFSG.RankThree.GF2n.Smith81.S81HO12Torus
public import CFSG.RankThree.GF2n.Smith81.S81HO12Layer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthGraph

open Module QuadraticMap CFSG.RankThree.PartOne.StrongP
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem isUnitri_diagonal_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ι → ℕ}
    {a u : GL ι K} (ha : IsUnitri r a) (d e : ι → K)
    (hu : (u : Matrix ι ι K) = Matrix.diagonal d * a * Matrix.diagonal e)
    (hde : ∀ i, d i * e i = 1) : IsUnitri r u := by
  intro i j hij
  rw [hu, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  by_cases h : i = j
  · subst h
    rw [ha.diag, Matrix.one_apply_eq, mul_one, hde, sub_self] at hij
    exact absurd rfl hij
  · rw [Matrix.one_apply_ne h, sub_zero] at hij
    apply ha i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]
    intro h0
    apply hij
    rw [h0, mul_zero, zero_mul]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem le_commutator_of_normalizer (hK : 4 ≤ Nat.card K) {Q : QuadraticForm K V} {n : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hV : finrank K V = 2 * n + 2)
    {H E : Subgroup (V ≃ₗ[K] V)} (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hOH : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ H)
    (hEH : E ≤ H) (hE2 : ∀ x ∈ E, x * x = 1) {k : ℕ} (hEk : Nat.card E = Nat.card K ^ k)
    (hcfg : ∀ S : Subgroup (V ≃ₗ[K] V), E ≤ S → S ≤ H → IsPGroup 2 S →
      ∀ h ∈ H, h ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)) →
        h ∈ Subgroup.normalizer (E : Set (V ≃ₗ[K] V))) :
    E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  have : Nonempty (PIdx n) := ⟨.inr (.inl 0)⟩
  have h2 : ∀ g : E, g * g = 1 := fun g => Subtype.ext (hE2 g g.2)
  have hE : IsPGroup 2 E := fun g => ⟨1, by rw [pow_one, pow_two, h2]⟩
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hinvx : x⁻¹ = x := (eq_inv_of_mul_eq_one_left (hE2 x hx)).symm
    have hinvy : y⁻¹ = y := (eq_inv_of_mul_eq_one_left (hE2 y hy)).symm
    have := mul_eq_one_iff_eq_inv.mp (hE2 (x * y) (E.mul_mem hx hy))
    rwa [mul_inv_rev, hinvx, hinvy] at this
  obtain ⟨b, hb, hEu⟩ := exists_pairBasis_unitri hQ hV E hE (hEH.trans hHO)
  let UT : Subgroup (V ≃ₗ[K] V) :=
    (unitriSubgroup 2 prank (2 * n + 2) prank_lt).comap (basisMat b).toMonoidHom
  have hmemUT : ∀ g, g ∈ UT ↔ IsUnitri prank (basisMat b g) := fun g => Iff.rfl
  have hEUT : E ≤ UT := fun g hg => hEu g hg
  have hUT2 : IsPGroup 2 UT := fun g => ⟨2 * n + 2, by
    have h := ((hmemUT g).1 g.2).pow_eq_one prank_lt (2 * n + 2)
      (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h
    rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]
    exact h⟩
  let S : Subgroup (V ≃ₗ[K] V) := UT ⊓ H
  have hES : E ≤ S := le_inf hEUT hEH
  have hSH : S ≤ H := inf_le_right
  have hS2 : IsPGroup 2 S := hUT2.to_le inf_le_left
  let T₁ : Subgroup (V ≃ₗ[K] V) := (ptorus b).range
  have hT1O' : T₁ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rintro _ ⟨c, rfl⟩
    exact ptorus_mem_commutator hb c
  have hT1O : T₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨c, rfl⟩
    exact ptorus_mem_orthogonalGroup hb c
  have hT1H : T₁ ≤ H := fun x hx => hOH (hT1O' hx)
  have hconjUT : ∀ c : Fin n → Kˣ, ∀ g ∈ UT, ptorus b c * g * (ptorus b c)⁻¹ ∈ UT := by
    intro c g hg
    rw [hmemUT] at hg ⊢
    refine isUnitri_diagonal_conj hg (fun p => ((pchar c p : Kˣ) : K))
      (fun p => ((pchar c⁻¹ p : Kˣ) : K)) ?_ fun p => ?_
    · rw [← map_inv (ptorus b) c, map_mul, map_mul, Units.val_mul, Units.val_mul,
        basisMat_ptorus, basisMat_ptorus]
    · rw [← Units.val_mul, ← pchar_mul, mul_inv_cancel, pchar_one, Units.val_one]
  have hconjS : ∀ c : Fin n → Kˣ, ∀ g ∈ S, ptorus b c * g * (ptorus b c)⁻¹ ∈ S := by
    intro c g hg
    exact ⟨hconjUT c g hg.1,
      H.mul_mem (H.mul_mem (hT1H ⟨c, rfl⟩) hg.2) (H.inv_mem (hT1H ⟨c, rfl⟩))⟩
  have hT1NS : T₁ ≤ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconjS c g, fun hg => ?_⟩
    have h := hconjS c⁻¹ _ hg
    rw [map_inv] at h
    have e : (ptorus b c)⁻¹ * (ptorus b c * g * (ptorus b c)⁻¹) * ((ptorus b c)⁻¹)⁻¹ = g := by
      group
    rwa [e] at h
  have hT1N : T₁ ≤ Subgroup.normalizer (E : Set (V ≃ₗ[K] V)) := fun t ht =>
    hcfg S hES hSH hS2 t (hT1H ht) (hT1NS ht)
  have hNab : ∀ x y : E, x * y = y * x := fun x y => Subtype.ext (hEab x x.2 y y.2)
  have hcopq : Nat.Coprime (Nat.card K - 1) (Nat.card K) :=
    (Nat.coprime_self_sub_left (by omega)).mpr (Nat.coprime_one_left _)
  have hT1card : Nat.card T₁ ∣ (Nat.card K - 1) ^ n := by
    have h := Subgroup.card_range_dvd (ptorus b)
    rwa [Nat.card_fun, Nat.card_units, Nat.card_fin] at h
  have hcop : Nat.Coprime (Nat.card T₁) (Nat.card E) := by
    rw [hEk]
    exact Nat.Coprime.coprime_dvd_left hT1card (Nat.Coprime.pow n k hcopq)
  obtain ⟨hsup, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp E T₁ hT1N hNab hcop
  have hDE : ⁅E, T₁⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he t ht
    have he' : ⁅e, t⁆ = e * (t * e⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he']
    exact E.mul_mem he ((Subgroup.mem_normalizer_iff.mp (hT1N ht) e⁻¹).mp (E.inv_mem he))
  have hDT : ∀ t ∈ T₁, ∀ g ∈ ⁅E, T₁⁆, t * g * t⁻¹ ∈ ⁅E, T₁⁆ := by
    intro t ht g hg
    have hle : ⁅E, T₁⁆ ≤ (⁅E, T₁⁆).comap (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro e he s hs
      show MulAut.conj t ⁅e, s⁆ ∈ ⁅E, T₁⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hT1N ht) e).mp he)
        (T₁.mul_mem (T₁.mul_mem ht hs) (T₁.inv_mem ht))
    exact hle hg
  let iu : PIdx n := .inr (.inl 0)
  let iu' : PIdx n := .inr (.inl 1)
  have huu' : iu ≠ iu' := Sum.inr_injective.ne (Sum.inl_injective.ne (by decide))
  let ent : (V ≃ₗ[K] V) → K := fun x =>
    ((basisMat b x : GL (PIdx n) K) : Matrix (PIdx n) (PIdx n) K) iu iu'
  have hent_one : ent 1 = 0 := by
    simp only [ent, map_one, Units.val_one]
    exact Matrix.one_apply_ne huu'
  have hent_mul : ∀ x y, x ∈ UT → y ∈ UT → ent (x * y) = ent x + ent y := by
    intro x y hx hy
    rw [hmemUT] at hx hy
    simp only [ent, map_mul, Units.val_mul, Matrix.mul_apply]
    rw [Fintype.sum_eq_add iu iu' huu' ?_]
    · rw [hx.diag, hy.diag, one_mul, mul_one, add_comm]
    · rintro l ⟨hl1, hl2⟩
      by_contra hne
      have r1 := hx iu l (by
        rw [Matrix.sub_apply, Matrix.one_apply_ne (Ne.symm hl1), sub_zero]
        exact left_ne_zero_of_mul hne)
      have r2 := hy l iu' (by
        rw [Matrix.sub_apply, Matrix.one_apply_ne hl2, sub_zero]
        exact right_ne_zero_of_mul hne)
      simp only [iu, iu', prank_inr_inl, Fin.val_zero, Fin.val_one] at r1 r2
      omega
  have hent_conj : ∀ (c : Fin n → Kˣ) x, ent (ptorus b c * x * (ptorus b c)⁻¹) = ent x := by
    intro c x
    simp only [ent]
    rw [← map_inv (ptorus b) c, map_mul, map_mul, Units.val_mul, Units.val_mul, basisMat_ptorus,
      basisMat_ptorus, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [iu, iu', pchar_inr_inl, Units.val_one, one_mul, mul_one]
  let Z : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {x | x ∈ UT ∧ ent x = 0}
      mul_mem' := fun {x y} hx hy =>
        ⟨UT.mul_mem hx.1 hy.1, by rw [hent_mul x y hx.1 hy.1, hx.2, hy.2, add_zero]⟩
      one_mem' := ⟨UT.one_mem, hent_one⟩
      inv_mem' := fun {x} hx => ⟨UT.inv_mem hx.1, by
        have h := hent_mul x x⁻¹ hx.1 (UT.inv_mem hx.1)
        rw [mul_inv_cancel, hent_one, hx.2, zero_add] at h
        exact h.symm⟩ }
  have hDZ : ⁅E, T₁⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    rintro e he _ ⟨c, rfl⟩
    have hEe : e ∈ UT := hEUT he
    have hinv : e⁻¹ ∈ UT := UT.inv_mem hEe
    have hc := hconjUT c e⁻¹ hinv
    have he' : ⁅e, ptorus b c⁆ = e * (ptorus b c * e⁻¹ * (ptorus b c)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he']
    refine ⟨UT.mul_mem hEe hc, ?_⟩
    rw [hent_mul _ _ hEe hc, hent_conj, ← hent_mul _ _ hEe hinv, mul_inv_cancel, hent_one]
  let A : Subgroup (GL (PIdx n) K) := (⁅E, T₁⁆).map (basisMat b).toMonoidHom
  obtain ⟨m, hm⟩ := card_eq_pow_of_isUnitri prank (fun c => basisMat b (ptorus b c)) pchar
    (fun c => basisMat_ptorus b c) A
    (by
      rintro a ⟨g, hg, rfl⟩
      exact hEu g (hDE hg))
    (by
      intro c a ha
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      refine Subgroup.mem_map.mpr ⟨ptorus b c * g * (ptorus b c)⁻¹, hDT _ ⟨c, rfl⟩ g hg, ?_⟩
      show basisMat b (ptorus b c * g * (ptorus b c)⁻¹) =
        basisMat b (ptorus b c) * basisMat b g * (basisMat b (ptorus b c))⁻¹
      rw [map_mul, map_mul, map_inv])
    (by
      intro i j hij
      by_cases h : i = iu ∧ j = iu'
      · left
        obtain ⟨rfl, rfl⟩ := h
        rintro a ⟨g, hg, rfl⟩
        exact (hDZ hg).2
      · right
        exact pchar_root_surjective hij h)
  have hAcard : Nat.card A = Nat.card (⁅E, T₁⁆ : Subgroup (V ≃ₗ[K] V)) :=
    Subgroup.card_map_of_injective (basisMat b).injective
  rw [hAcard] at hm
  have hle2 : Nat.card (E ⊓ Subgroup.centralizer (T₁ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ 2 :=
    card_le_two_of_commute hK hb _ (fun g hg => hHO (hEH hg.1)) (fun g hg => hEu g hg.1)
      (fun g hg c => (Subgroup.mem_centralizer_iff.mp hg.2 _ ⟨c, rfl⟩).symm)
  set C : Subgroup (V ≃ₗ[K] V) := E ⊓ Subgroup.centralizer (T₁ : Set (V ≃ₗ[K] V)) with hC
  set D' : Subgroup (V ≃ₗ[K] V) := ⁅E, T₁⁆ with hD'
  have hcomm : ∀ (c : C) (d : D'), Commute (C.subtype c) (D'.subtype d) := fun c d =>
    hEab _ c.2.1 _ (hDE d.2)
  have hφi : Function.Injective (MonoidHom.noncommCoprod C.subtype D'.subtype hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr ⟨C.subtype_injective,
      D'.subtype_injective, by rw [Subgroup.range_subtype, Subgroup.range_subtype]; exact hdisj⟩
  have hφr : (MonoidHom.noncommCoprod C.subtype D'.subtype hcomm).range = E := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
  have hcardE : Nat.card E = Nat.card C * Nat.card D' := by
    rw [← Nat.card_prod]
    conv_lhs => rw [← hφr]
    exact (Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv).symm
  have hC1 : Nat.card C = 1 := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    by_contra hne
    have hC2 : Nat.card C = 2 := by omega
    rw [hEk, hC2, hm] at hcardE
    have hq0 : 0 < Nat.card K := by omega
    have hqm : 0 < Nat.card K ^ m := pow_pos hq0 m
    rcases le_or_gt k m with hkm | hkm
    · have := Nat.pow_le_pow_right hq0 hkm
      omega
    · have h1 := Nat.pow_le_pow_right hq0 hkm
      rw [pow_succ'] at h1
      have h3 : 4 * Nat.card K ^ m ≤ Nat.card K * Nat.card K ^ m := Nat.mul_le_mul_right _ hK
      omega
  rw [Subgroup.card_eq_one.mp hC1, bot_sup_eq] at hsup
  calc E = D' := hsup.symm
    _ ≤ _ := Subgroup.commutator_mono (hEH.trans hHO) hT1O

end CFSG.RankThree.GF2n.Smith81.OrthGraph
