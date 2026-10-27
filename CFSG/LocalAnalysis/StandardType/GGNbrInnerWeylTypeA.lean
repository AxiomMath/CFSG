module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA TypeANbrDvd

namespace NbrInnerWeylA

theorem comm_fixes_of_mem_zpowers {H : Type*} [Group H] {a x y : H}
    (hx : x * a * x⁻¹ ∈ Subgroup.zpowers a) (hy : y * a * y⁻¹ ∈ Subgroup.zpowers a) :
    ((y * x)⁻¹ * (x * y)) * a * ((y * x)⁻¹ * (x * y))⁻¹ = a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h1 : x * y * a * (x * y)⁻¹ = a ^ (k * l) := by
    calc x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
      _ = x * a ^ l * x⁻¹ := by rw [hl]
      _ = (x * a * x⁻¹) ^ l := (conj_zpow ..).symm
      _ = (a ^ k) ^ l := by rw [hk]
      _ = a ^ (k * l) := (zpow_mul a k l).symm
  have h2 : y * x * a * (y * x)⁻¹ = a ^ (l * k) := by
    calc y * x * a * (y * x)⁻¹ = y * (x * a * x⁻¹) * y⁻¹ := by group
      _ = y * a ^ k * y⁻¹ := by rw [hk]
      _ = (y * a * y⁻¹) ^ k := (conj_zpow ..).symm
      _ = (a ^ l) ^ k := by rw [hl]
      _ = a ^ (l * k) := (zpow_mul a l k).symm
  calc ((y * x)⁻¹ * (x * y)) * a * ((y * x)⁻¹ * (x * y))⁻¹
      = (y * x)⁻¹ * (x * y * a * (x * y)⁻¹) * (y * x) := by group
    _ = (y * x)⁻¹ * (y * x * a * (y * x)⁻¹) * (y * x) := by rw [h1, h2, mul_comm k l]
    _ = a := by group

section Perm

variable {d : ℕ} {K : Type} [Field K] [CharP K 2]

theorem permSL_one : (permSL (1 : Equiv.Perm (Fin d)) : SpecialLinearGroup (Fin d) K) = 1 :=
  Subtype.ext (by rw [coe_permSL, Matrix.SpecialLinearGroup.coe_one, permMatrix_one])

theorem permSL_mul (σ τ : Equiv.Perm (Fin d)) :
    (permSL (σ * τ) : SpecialLinearGroup (Fin d) K) = permSL τ * permSL σ :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL, coe_permSL, permMatrix_mul])

@[expose] noncomputable def permConj {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L') :
    Equiv.Perm (Fin d) →* MulAut L' where
  toFun σ := MulAut.conj (φ' (permSL σ⁻¹))
  map_one' := by rw [inv_one, permSL_one, map_one, map_one]
  map_mul' σ τ := by rw [_root_.mul_inv_rev, permSL_mul, map_mul, map_mul]

theorem commutator_swap_apply {i j k : Fin d} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((Equiv.swap i k * Equiv.swap i j)⁻¹ * (Equiv.swap i j * Equiv.swap i k)) i = j ∧
      ∀ m, m ≠ i → m ≠ j → m ≠ k →
        ((Equiv.swap i k * Equiv.swap i j)⁻¹ * (Equiv.swap i j * Equiv.swap i k)) m = m := by
  refine ⟨?_, fun m hmi hmj hmk => ?_⟩
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hij, hik, hjk, hij.symm, hik.symm,
      hjk.symm]
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hmi, hmj, hmk]

end Perm

section Line

variable {d : ℕ} {K : Type} [Field K] [CharP K 2] {L' : Type} [Group L']
  {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem exists_perm_not_mem_zpowers (hd : 5 ≤ d) (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {a₀ : MulAut L'} {t : Fin d → K}
    (ha₀ : ActsDiag φ' a₀ t) (ha₁ : a₀ ≠ 1) :
    ∃ σ : Equiv.Perm (Fin d), MulAut.conj (φ' (permSL σ)) * a₀ *
      (MulAut.conj (φ' (permSL σ)))⁻¹ ∉ Subgroup.zpowers a₀ := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ i j, t i = t j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hki, hkj⟩ := exists_ne_of_two (by omega : 3 ≤ d) i j
    obtain ⟨m, hmi, hmj, hmk, -⟩ := exists_ne_of_four hd i j k k
    obtain ⟨hρi, hρm⟩ := commutator_swap_apply (i := i) (j := j) (k := k) hij hki.symm hkj.symm
    set ρ := (Equiv.swap i k * Equiv.swap i j)⁻¹ * (Equiv.swap i j * Equiv.swap i k) with hρ
    have hfix : permConj φ' ρ * a₀ * (permConj φ' ρ)⁻¹ = a₀ := by
      have h := comm_fixes_of_mem_zpowers (hcon (Equiv.swap i j)⁻¹) (hcon (Equiv.swap i k)⁻¹)
      rw [hρ, map_mul, map_inv, map_mul, map_mul]
      exact h
    have h1 : ActsDiag φ' (permConj φ' ρ * a₀ * (permConj φ' ρ)⁻¹) (fun x => t (ρ⁻¹ x)) :=
      ha₀.conj_perm ρ⁻¹
    rw [hfix] at h1
    have hmρ : ρ⁻¹ m = m := Equiv.Perm.inv_eq_iff_eq.mpr (hρm m hmi hmj hmk).symm
    have key : ∀ x, t (ρ⁻¹ x) = t x := by
      intro x
      by_cases hxm : x = m
      · rw [hxm, hmρ]
      have h2 := ha₀.ratio hφker h1 hxm
      simp only [hmρ] at h2
      exact (mul_right_cancel₀ (inv_ne_zero (ha₀.ne_zero m)) h2).symm
    rw [← key j, Equiv.Perm.inv_eq_iff_eq.mpr hρi.symm]
  exact ha₁ (ha₀.eq_one (by omega) hφ's hconst)

end Line

end NbrInnerWeylA

open NbrInnerWeylA

section Model

variable {d p : ℕ} {K : Type} [Field K] [CharP K 2] {L' : Type} [Group L']
  {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem weyl_mul_apply_inv_diag {A : Subgroup (MulAut L')}
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (hAp : ∀ a ∈ A, a ^ p = 1) :
    ∀ n ∈ Set.range fun σ : Equiv.Perm (Fin d) => φ' (permSL σ), ∀ a ∈ A,
      (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  rintro _ ⟨σ, rfl⟩ a ha
  obtain ⟨t, hat⟩ := hdiag a ha
  obtain ⟨E, hE, haE⟩ := id hat
  have hg : ((permSL σ * (CatalogueBHigherLinearAction.slConjugation d K E (permSL σ))⁻¹ :
      SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal fun i => t (σ i) * (t i)⁻¹ := by
    rw [← map_inv, permSL_inv, Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, coe_permSL,
      coe_permSL, coe_inv_of_diagonal hE, hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      permMatrix_mul_diagonal_mul_inv, diagonal_mul_diagonal]
    rfl
  have e : φ' (permSL σ) * (a (φ' (permSL σ)))⁻¹ =
      φ' (permSL σ * (CatalogueBHigherLinearAction.slConjugation d K E (permSL σ))⁻¹) := by
    rw [haE, map_mul, map_inv]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [e, ← map_pow,
      pow_eq_one_of_diagonal hg (fun i => hat.ratio_pow hφker (hAp a ha) (σ i) i), map_one]
  · obtain ⟨t', hat'⟩ := hdiag a' ha'
    rw [e]
    exact hat'.apply_of_isDiag (by rw [hg]; exact isDiag_diagonal _)

end Model

theorem ggTorusNoLine_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) :
    GGTorusNoLine p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp h0
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  obtain ⟨A₀, hA₀⟩ := ggPGLTorality_holds (d := d) hp hp2 hpK _ hXA hXI (hcardX ▸ hr)
    (hcardX ▸ h3)
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    TypeANbrDvd.exists_actsDiag_model hperfSL (slHasSections_of_five_le hd) hψ hker hperf hAI hA₀
  refine ⟨Set.range fun σ : Equiv.Perm (Fin d) => φ' (permSL σ),
    weyl_mul_apply_inv_diag hφ'ker hdiag hA.2, fun _ a₀ ha₀ ha₁ => ?_⟩
  obtain ⟨t, ht⟩ := hdiag a₀ ha₀
  obtain ⟨σ, hσ⟩ := exists_perm_not_mem_zpowers hd hφ's hφ'ker ht ha₁
  exact ⟨_, ⟨σ, rfl⟩, hσ⟩

theorem largeEvenLabelAll_torusLift_noLine_typeADvd {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (h : GGTableBNbrInnerTypeADvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNoLine p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hpd⟩ := h
  dsimp only at ht hl hpn hpd
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  refine ⟨K, inferInstance, inferInstance, hK, hQ', l + 1 - 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le (by omega))),
    ggTorusNoLine_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (ggTorusNoLine_PSL hp hpK (by omega))⟩

@[expose] def GGNbrWeylInnerTypeALabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ GGTableBNbrInnerTypeADvdLabel p lab

section Main

theorem ggNbrInnerWeylOn_innerTypeA : GGNbrInnerWeylOn GGNbrWeylInnerTypeALabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, h⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_torusLift_noLine_typeADvd hp h)

end Main

end CFSG.StandardType

end
