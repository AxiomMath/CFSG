module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineAutomorphismClassification
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

variable (J C) in
@[expose] def sublineFixingAut [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (MulAut (J.specialSubgroup ⧸ C)) where
  carrier := {β | ∀ x ∈ sublineL J C hJ, β x = x}
  mul_mem' {β γ} hβ hγ x hx := by
    rw [MulAut.mul_apply, hγ x hx, hβ x hx]
  one_mem' _ _ := rfl
  inv_mem' {β} hβ x hx := by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hβ x hx]

theorem mem_sublineFixingAut [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {β : MulAut (J.specialSubgroup ⧸ C)} :
    β ∈ sublineFixingAut J C hJ ↔ ∀ x ∈ sublineL J C hJ, β x = x :=
  Iff.rfl

theorem conj_ne_one [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) : J.conj ≠ 1 := by
  intro h
  have hall : ∀ x : K, J.conj x = x := fun x => by rw [h]; rfl
  have hK : Nat.card {x : K // J.conj x = x} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hfixed, hcard] at hK
  rw [hcard] at h1
  have hq : 2 ≤ q := by
    by_contra hq
    interval_cases q <;> simp at h1
  nlinarith

theorem card_conjGroup [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) : Nat.card (conjGroup J) = 2 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime conj_sq (conj_ne_one hcard hfixed)

variable [Finite K] [CharP K 2]

theorem range_sublineAutHom {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J) :
    (sublineAutHom J C hJ hC).range = sublineFixingAut J C hJ := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun y hy => sublineAutHom_apply_of_mem hJ hC x hy
  · intro β hβ
    exact mem_range_sublineAutHom hf hcard hfixed hJ hC hβ

theorem map_eq_self_of_fix {G : Type*} [Group G] {β : MulAut G} {H : Subgroup G}
    (h : ∀ x ∈ H, β x = x) : H.map (β : G →* G) = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change β x ∈ H
    rw [h x hx]
    exact hx
  · intro hy
    exact ⟨y, hy, h y hy⟩

theorem unitary_central_cover_subline_automorphism_two_part (J : HermitianForm 3 K) (f : ℕ)
    (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (C : Subgroup J.specialSubgroup) [C.Normal] (hC : C ≤ scalarCenter J) :
    let q := 2 ^ f
    let L := J.specialSubgroup ⧸ C
    let J₀ := sublineL J C hJ
    let Ψ := sublineAutHom J C hJ hC
    let bar : conjGroup J := ⟨J.conj, Subgroup.mem_zpowers _⟩
    (∀ c : K, J.conj c = c ^ q) ∧
    (∀ g : J.specialSubgroup, g ∈ scalarCenter J ↔ ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c ∧
        c ^ (q + 1) = 1 ∧ c ^ 3 = 1) ∧
    (∀ c : Kˣ, c ∈ normOne J ↔ (c : K) ^ (q + 1) = 1) ∧
    IsCyclic (normOne J) ∧ Nat.card (normOne J) = q + 1 ∧
    (∀ σ : K ≃+* K, σ ∈ conjGroup J ↔ σ = 1 ∨ σ = J.conj) ∧ J.conj ≠ 1 ∧
    (∀ d : normOne J, normOneAction J bar d = d⁻¹) ∧
    (∀ (x : normOne J ⋊[normOneAction J] conjGroup J) (g : J.specialSubgroup),
      ∃ hg : diag3 1 (x.left : Kˣ) 1 * glAut (x.right : K ≃+* K) (g : GL (Fin 3) K) *
          (diag3 1 (x.left : Kˣ) 1)⁻¹ ∈ J.specialSubgroup,
        Ψ x (g : L) = ((⟨_, hg⟩ : J.specialSubgroup) : L)) ∧
    (∀ g : J.specialSubgroup, ∃ hg : glAut J.conj (g : GL (Fin 3) K) ∈ J.specialSubgroup,
      Ψ (SemidirectProduct.inr bar) (g : L) = ((⟨_, hg⟩ : J.specialSubgroup) : L)) ∧
    Function.Injective Ψ ∧ Ψ.range = sublineFixingAut J C hJ ∧
    (∀ β : MulAut L, (∀ x ∈ J₀, β x = x) → ∃! x, Ψ x = β) ∧
    Nonempty (sublineFixingAut J C hJ ≃* normOne J ⋊[normOneAction J] conjGroup J) ∧
    Nat.card (sublineFixingAut J C hJ) = 2 * (q + 1) ∧
    (∀ P : Subgroup (MulAut L), IsPGroup 2 P → (∀ β ∈ P, ∀ x ∈ J₀, β x = x) →
      Nat.card P ≤ 2) ∧
    (∀ β ∈ sublineFixingAut J C hJ, β ≠ 1 → β ^ 2 = 1 →
      ∃ e : normOne J, (Ψ (SemidirectProduct.inl e))⁻¹ * β * Ψ (SemidirectProduct.inl e) =
          Ψ (SemidirectProduct.inr bar) ∧
        (∀ x ∈ J₀, Ψ (SemidirectProduct.inl e) x = x) ∧
        (upperRootL J C hJ).map (Ψ (SemidirectProduct.inl e) : L →* L) = upperRootL J C hJ ∧
        (lowerRootL J C hJ).map (Ψ (SemidirectProduct.inl e) : L →* L) = lowerRootL J C hJ) := by
  intro q L J₀ Ψ bar
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hM : Nat.card (normOne J) = q + 1 := card_normOne Nat.prime_two hq hcard hfixed
  have hB : Nat.card (conjGroup J) = 2 := card_conjGroup hcard hfixed
  have hinj : Function.Injective Ψ := sublineAutHom_injective hJ hC hcard hfixed
  have hrange : Ψ.range = sublineFixingAut J C hJ := range_sublineAutHom hf hcard hfixed hJ hC
  set e : normOne J ⋊[normOneAction J] conjGroup J ≃* sublineFixingAut J C hJ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hFcard : Nat.card (sublineFixingAut J C hJ) = 2 * (q + 1) := by
    rw [← Nat.card_congr e.toEquiv, SemidirectProduct.card, hM, hB, mul_comm]
  have hqodd : Odd (q + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have : Finite (normOne J) := Nat.finite_of_card_ne_zero (by rw [hM]; omega)
  have : Finite (conjGroup J) := Nat.finite_of_card_ne_zero (by rw [hB]; omega)
  have : Finite (normOne J ⋊[normOneAction J] conjGroup J) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have : Finite (sublineFixingAut J C hJ) := Finite.of_equiv _ e.toEquiv
  refine ⟨huppert_II_10_4_conj_eq_frobenius J q hcard hfixed,
    mem_scalarCenter_iff_pow hcard hfixed, mem_normOne_iff_pow hcard hfixed, inferInstance, hM,
    fun σ => mem_conjGroup_iff,
    conj_ne_one hcard hfixed, normOneAction_conj, sublineAutHom_mk hJ hC, fun g => ?_, hinj,
    hrange, fun β hβ => ?_, ⟨e.symm⟩, hFcard, fun P hP hPfix => ?_, fun β hβ hβ1 hβ2 => ?_⟩
  ·
    refine ⟨glAut_mem_specialSubgroup hJ (conjGroup_commute bar.2) g.2, ?_⟩
    obtain ⟨hg, h⟩ := sublineAutHom_mk hJ hC (SemidirectProduct.inr bar) g
    rw [h]
    congr 1
    apply Subtype.ext
    change diag3 1 ((1 : normOne J) : Kˣ) 1 * glAut J.conj (g : GL (Fin 3) K) *
      (diag3 1 ((1 : normOne J) : Kˣ) 1)⁻¹ = glAut J.conj (g : GL (Fin 3) K)
    rw [OneMemClass.coe_one, diag3_one, one_mul, inv_one, mul_one]
  ·
    obtain ⟨x, hx⟩ := (hrange ▸ hβ : β ∈ Ψ.range)
    exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩
  ·
    have hle : P ≤ sublineFixingAut J C hJ := hPfix
    have : Finite P := Finite.of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
    have hdvd : Nat.card P ∣ 2 * (q + 1) := hFcard ▸ Subgroup.card_dvd_of_le hle
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) (q + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hqodd)
    exact Nat.le_of_dvd two_pos (hcop.dvd_of_dvd_mul_right hdvd)
  ·
    obtain ⟨x, rfl⟩ := (hrange ▸ hβ : β ∈ Ψ.range)
    have hx2 : x ^ 2 = 1 := hinj (by rw [map_pow, hβ2, map_one])
    have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hxr : (x.right : K ≃+* K) = J.conj := by
      rcases mem_conjGroup_iff.mp x.right.2 with h | h
      · exfalso
        apply hx1
        have hl : (x ^ 2).left = x.left * x.left := by
          rw [pow_two, SemidirectProduct.mul_left]
          congr 1
          have hr : x.right = 1 := Subtype.ext h
          rw [hr, map_one, MulAut.one_apply]
        have hd2 : x.left * x.left = 1 := by rw [← hl, hx2, SemidirectProduct.one_left]
        have hd : x.left = 1 := by
          apply Subtype.ext
          apply Units.ext
          have := congrArg (fun y : normOne J => ((y : Kˣ) : K)) hd2
          simp only [Subgroup.coe_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one] at this
          exact eq_one_of_sq_eq_one_charTwo (by rw [pow_two]; exact this)
        exact SemidirectProduct.ext hd (Subtype.ext h)
      · exact h
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) ((x.left : Kˣ) : K)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact (x.left : Kˣ).ne_zero (by rw [hr, mul_zero])
    have hrn : r * J.conj r = 1 := by
      apply eq_one_of_sq_eq_one_charTwo
      have h := x.left.2
      change ((x.left : Kˣ) : K) * J.conj ((x.left : Kˣ) : K) = 1 at h
      rw [hr, map_mul] at h
      linear_combination h
    set ε : normOne J := ⟨Units.mk0 r hr0, hrn⟩
    have hconj : (SemidirectProduct.inl ε)⁻¹ * x * SemidirectProduct.inl ε =
        SemidirectProduct.inr bar := by
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
          SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.mul_right,
          SemidirectProduct.inv_right, SemidirectProduct.left_inr, inv_one, map_one,
          MulAut.one_apply, one_mul]
        have hxbar : x.right = bar := Subtype.ext hxr
        rw [hxbar, normOneAction_conj]
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
          OneMemClass.coe_one, Units.val_one, ε, Units.val_mk0, hr]
        field_simp
      · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
          SemidirectProduct.right_inl, SemidirectProduct.right_inr, inv_one, one_mul, mul_one]
        exact Subtype.ext hxr
    have hfixε : ∀ y ∈ J₀, Ψ (SemidirectProduct.inl ε) y = y :=
      fun y hy => sublineAutHom_apply_of_mem hJ hC _ hy
    refine ⟨ε, ?_, hfixε, map_eq_self_of_fix fun y hy => hfixε y (upperRootL_le_sublineL hJ hy),
      map_eq_self_of_fix fun y hy => hfixε y (lowerRootL_le_sublineL hJ hy)⟩
    rw [← hconj, map_mul, map_mul, map_inv]

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
