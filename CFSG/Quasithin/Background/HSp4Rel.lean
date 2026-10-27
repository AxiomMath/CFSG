module

public import CFSG.Quasithin.Background.HSp4Pair
public import CFSG.Quasithin.Background.HConj
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Assembly.LowTwoRank Matrix PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp coe_conjSp
  coe_fieldSp proj_surjective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj projEquiv)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

theorem card_fix_conj {V : Type*} [Group V] (x a : MulAut V) :
    Nat.card {v : V // (x * a * x⁻¹) v = v} = Nat.card {v : V // a v = v} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨x⁻¹ v.1, ?_⟩
      invFun := fun v => ⟨x v.1, ?_⟩
      left_inv := fun v => Subtype.ext (MulAut.apply_inv_self V x v.1)
      right_inv := fun v => Subtype.ext (MulAut.inv_apply_self V x v.1) }
  · have h : x (a (x⁻¹ v.1)) = v.1 := v.2
    calc a (x⁻¹ v.1) = x⁻¹ (x (a (x⁻¹ v.1))) := (MulAut.inv_apply_self V x _).symm
      _ = x⁻¹ v.1 := by rw [h]
  · show x (a (x⁻¹ (x v.1))) = x v.1
    rw [MulAut.inv_apply_self, v.2]

theorem card_lt_of_imp {α : Type*} [Finite α] {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {a₀ : α}
    (hQ : Q a₀) (hP : ¬ P a₀) : Nat.card {a // P a} < Nat.card {a // Q a} := by
  classical
  let f : Option {a // P a} → {a // Q a} := fun o => o.elim ⟨a₀, hQ⟩ fun a => ⟨a.1, hPQ a.1 a.2⟩
  have hf : Function.Injective f := by
    rintro (_ | ⟨a, ha⟩) (_ | ⟨b, hb⟩) h
    · rfl
    · have h' : a₀ = b := congrArg Subtype.val h
      exact (hP (h' ▸ hb)).elim
    · have h' : a = a₀ := congrArg Subtype.val h
      exact (hP (h' ▸ ha)).elim
    · have h' : a = b := congrArg Subtype.val h
      exact congrArg some (Subtype.ext h')
  have := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option] at this
  omega

variable {K : Type} [Field K]

theorem natAut_conjSp (A : gsp 2 K) (g : StatedSp 2 K) :
    natAut (StatedSp 2 K) (conjSp 2 K A g) =
      matAut (A : GL (Fin 2 ⊕ Fin 2) K) * natAut (StatedSp 2 K) g *
        (matAut (A : GL (Fin 2 ⊕ Fin 2) K))⁻¹ := by
  change matHom ((conjSp 2 K A g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
    matHom (A : GL (Fin 2 ⊕ Fin 2) K) * matHom (g : GL (Fin 2 ⊕ Fin 2) K) *
      (matHom (A : GL (Fin 2 ⊕ Fin 2) K))⁻¹
  rw [coe_conjSp, map_mul, map_mul, map_inv]

theorem natAut_fieldSp (σ : K ≃+* K) (g : StatedSp 2 K) :
    natAut (StatedSp 2 K) (fieldSp 2 K σ g) =
      fieldMap σ * natAut (StatedSp 2 K) g * (fieldMap σ)⁻¹ :=
  toAddMap_injective fun v => by
    rw [toAddMap_natAut, coe_fieldSp]
    exact (toAddMap_fieldMap_conj σ (g : GL (Fin 2 ⊕ Fin 2) K) v).symm

theorem natAut_ofAdd (γ : StatedSp 2 K) (u : Fin 2 ⊕ Fin 2 → K) :
    natAut (StatedSp 2 K) γ (Multiplicative.ofAdd u) =
      Multiplicative.ofAdd (((γ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) := rfl

variable [CharP K 2]

theorem card_fix_tau_lt [Finite K] :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K //
        natAut (StatedSp 2 K) (tauSp (upSp (sym2_transpose (1 : K) 0 0))) v = v} <
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K //
        natAut (StatedSp 2 K) (upSp (sym2_transpose (1 : K) 0 0)) v = v} := by
  have hP : ∀ u : Fin 2 ⊕ Fin 2 → K,
      natAut (StatedSp 2 K) (tauSp (upSp (sym2_transpose (1 : K) 0 0)))
          (Multiplicative.ofAdd u) = Multiplicative.ofAdd u ↔ u ι₃ = 0 ∧ u ι₂ = 0 := by
    intro u
    rw [natAut_ofAdd, tauSp_upSp_diag_mulVec]
    constructor
    · intro h
      have h' := congrArg Multiplicative.toAdd h
      simp only [toAdd_ofAdd] at h'
      have e0 := congrFun h' ι₀
      have e1 := congrFun h' ι₁
      simp at e0 e1
      exact ⟨e0, e1⟩
    · rintro ⟨h3, h2⟩
      rw [h3, h2]
      simp
  have hQ : ∀ u : Fin 2 ⊕ Fin 2 → K,
      natAut (StatedSp 2 K) (upSp (sym2_transpose (1 : K) 0 0))
          (Multiplicative.ofAdd u) = Multiplicative.ofAdd u ↔ u ι₂ = 0 := by
    intro u
    rw [natAut_ofAdd, coe_upSp, up_mulVec]
    constructor
    · intro h
      have h' := congrArg Multiplicative.toAdd h
      simp only [toAdd_ofAdd] at h'
      have e0 := congrFun h' ι₀
      simpa using e0
    · intro h2
      rw [h2]
      simp
  refine card_lt_of_imp (a₀ := Multiplicative.ofAdd (Pi.single ι₃ (1 : K))) (fun v hv => ?_)
    ((hQ _).mpr (by simp)) (fun h => by simpa using ((hP _).mp h).1)
  exact (hQ (Multiplicative.toAdd v)).mpr ((hP (Multiplicative.toAdd v)).mp hv).2

variable [Finite K]

theorem exists_aut_eq (θ : MulAut (StatedSp 2 K)) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), (∀ g, θ g = conjSp 2 K A (fieldSp 2 K σ g)) ∨
      ∀ g, θ g = conjSp 2 K A (fieldSp 2 K σ (tauSp g)) := by
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow
      ((projEquiv K).symm.trans (θ.trans (projEquiv K)))
  refine ⟨A, σ, ?_⟩
  have key : ∀ g, projEquiv K (θ g) =
      ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut 2 K A *
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K σ * tauAut ^ ε :
          MulAut (StatedProj (StatedSp 2 K))) (proj 2 K g)) := by
    intro g
    rw [← hα]
    show projEquiv K (θ g) = projEquiv K (θ ((projEquiv K).symm (projEquiv K g)))
    rw [MulEquiv.symm_apply_apply]
  interval_cases ε
  · left
    intro g
    have h := key g
    rw [pow_zero, mul_one, MulAut.mul_apply,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_proj] at h
    exact (projEquiv K).injective h
  · right
    intro g
    have h := key g
    rw [pow_one, MulAut.mul_apply, MulAut.mul_apply, tauAut_proj,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_proj] at h
    exact (projEquiv K).injective h

theorem exists_conjHom_eq (g : ↥(natNorm (StatedSp 2 K))) :
    ∃ (B : StatedSp 2 K) (σ : K ≃+* K),
      ∀ γ, conjHom (StatedSp 2 K) g γ = B * fieldSp 2 K σ γ * B⁻¹ := by
  obtain ⟨A, σ, h | h⟩ := exists_aut_eq (conjHom (StatedSp 2 K) g)
  · obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
    obtain ⟨B, rfl⟩ := proj_surjective y
    refine ⟨B, σ, fun γ => ?_⟩
    rw [h γ]
    have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 K)) =>
      α (proj 2 K (fieldSp 2 K σ γ))) hy
    simp only [MulAut.conj_apply,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_proj] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact ((projEquiv K).injective h1).symm
  · exfalso
    set l := upSp (sym2_transpose (1 : K) 0 0) with hl
    have h1 := natAut_conjHom (StatedSp 2 K) g l
    rw [h l, natAut_conjSp, natAut_fieldSp] at h1
    have c1 := card_fix_conj (g : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) (natAut (StatedSp 2 K) l)
    have c2 := card_fix_conj (matAut (A : GL (Fin 2 ⊕ Fin 2) K))
      (fieldMap σ * natAut (StatedSp 2 K) (tauSp l) * (fieldMap σ)⁻¹)
    have c3 := card_fix_conj (fieldMap (ι := Fin 2 ⊕ Fin 2) σ) (natAut (StatedSp 2 K) (tauSp l))
    rw [h1] at c2
    have := card_fix_tau_lt (K := K)
    rw [← hl] at this
    omega

omit [CharP K 2] [Finite K] in
theorem exists_smul_of_conj_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Subgroup (GL ι K)}
    (hΓ : HasScalarCommutant Γ) {x y : MulAut (StdMod ι K)}
    (h : ∀ γ : ↥Γ, x * natAut Γ γ * x⁻¹ = y * natAut Γ γ * y⁻¹) :
    ∃ D : K, ∀ v, toAddMap x v = toAddMap y (D • v) := by
  set h' := y⁻¹ * x with hh'
  have hcomm : ∀ γ : ↥Γ, h' * natAut Γ γ = natAut Γ γ * h' := by
    intro γ
    have := h γ
    calc h' * natAut Γ γ = y⁻¹ * (x * natAut Γ γ * x⁻¹) * x := by rw [hh']; group
      _ = y⁻¹ * (y * natAut Γ γ * y⁻¹) * x := by rw [this]
      _ = natAut Γ γ * h' := by rw [hh']; group
  let F : (ι → K) →+ (ι → K) := AddMonoidHom.mk' (toAddMap h') (toAddMap_add h')
  obtain ⟨D, hD⟩ := hΓ F fun γ hγ v => by
    have := congrArg (fun z => toAddMap z v) (hcomm ⟨γ, hγ⟩)
    simp only [toAddMap_mul, toAddMap_natAut] at this
    exact this
  refine ⟨D, fun v => ?_⟩
  have hx : x = y * h' := by rw [hh']; group
  rw [hx, toAddMap_mul]
  exact congrArg (toAddMap y) (hD v)

omit [CharP K 2] [Finite K] in
theorem toAddMap_matAut_fieldMap_smul {ι : Type} [Fintype ι] [DecidableEq ι] (B : GL ι K)
    (σ : K ≃+* K) (D : K) (v : ι → K) :
    toAddMap (matAut B * fieldMap σ) (D • v) =
      σ D • ((B : Matrix ι ι K) *ᵥ fun i => σ (v i)) := by
  rw [toAddMap_mul, toAddMap_fieldMap, toAddMap_matAut, ← Matrix.mulVec_smul]
  congr 1
  ext i
  simp

theorem exists_eq_of_mem_natNorm {g : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hg : g ∈ natNorm (StatedSp 2 K)) :
    ∃ (B : StatedSp 2 K) (σ : K ≃+* K) (D : K),
      (∀ γ, conjHom (StatedSp 2 K) ⟨g, hg⟩ γ = B * fieldSp 2 K σ γ * B⁻¹) ∧
      ∀ v, toAddMap g v =
        D • (((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          fun i => σ (v i)) := by
  obtain ⟨B, σ, hB⟩ := exists_conjHom_eq ⟨g, hg⟩
  have hconj : ∀ γ : StatedSp 2 K, g * natAut (StatedSp 2 K) γ * g⁻¹ =
      (natAut (StatedSp 2 K) B * fieldMap σ) * natAut (StatedSp 2 K) γ *
        (natAut (StatedSp 2 K) B * fieldMap σ)⁻¹ := by
    intro γ
    have h1 := natAut_conjHom (StatedSp 2 K) ⟨g, hg⟩ γ
    rw [hB γ] at h1
    simp only [map_mul, map_inv, natAut_fieldSp] at h1
    change _ = g * natAut (StatedSp 2 K) γ * g⁻¹ at h1
    rw [← h1]
    group
  obtain ⟨D, hD⟩ := exists_smul_of_conj_eq hasScalarCommutant_statedSp hconj
  exact ⟨B, σ, σ D, hB, fun v => (hD v).trans (toAddMap_matAut_fieldMap_smul _ σ D v)⟩

theorem exists_eq_of_mem_pairNormSp {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hx : pairAut a b ∈ pairNormSp K) :
    ∃ (B : StatedSp 2 K) (σ : K ≃+* K) (D₁ D₂ : K),
      (∀ v, toAddMap a v =
        D₁ • (((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          fun i => σ (v i))) ∧
      ∀ v, toAddMap b v =
        D₂ • ((((tauSp B : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ fun i => σ (v i)) := by
  have ha := fst_mem_natNorm hx
  obtain ⟨B, σ, D₁, hB, hD₁⟩ := exists_eq_of_mem_natNorm ha
  have hconj : ∀ γ : StatedSp 2 K, b * natAut (StatedSp 2 K) γ * b⁻¹ =
      (natAut (StatedSp 2 K) (tauSp B) * fieldMap σ) * natAut (StatedSp 2 K) γ *
        (natAut (StatedSp 2 K) (tauSp B) * fieldMap σ)⁻¹ := by
    intro γ
    obtain ⟨γ₀, rfl⟩ := tauSp_surjective γ
    obtain ⟨δ, h1, h2⟩ := exists_conj hx γ₀
    have h3 : δ = B * fieldSp 2 K σ γ₀ * B⁻¹ := by
      rw [← hB γ₀]
      exact natAut_injective _ (h1.symm.trans (natAut_conjHom (StatedSp 2 K) ⟨a, ha⟩ γ₀).symm)
    rw [h2, h3]
    simp only [map_mul, map_inv, CFSG.RankThree.PartTwo.KFacts.tauSp_fieldSp, natAut_fieldSp]
    group
  obtain ⟨D, hD⟩ := exists_smul_of_conj_eq hasScalarCommutant_statedSp hconj
  exact ⟨B, σ, D₁, σ D, hD₁, fun v => (hD v).trans (toAddMap_matAut_fieldMap_smul _ σ D v)⟩

end Sp4

end H

end CFSG.Quasithin
