module

public import CFSG.RankThree.PartTwo.KFacts.KS116ProofSubfield
public import CFSG.RankThree.PartTwo.KFacts.KS116

public section

namespace CFSG.RankThree.PartTwo.KFacts

namespace LandazuriSeitzProof

open scoped MatrixGroups
open KS116Proof (uu hh uu_add uu_zero uu_injective uu_mul_comm hh_conj_uu exists_conj_eq_uu_one)

section Linear

variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V] (P : A → Module.End K V)

theorem exists_common_eigenvector (hcomm : ∀ a b, Commute (P a) (P b))
    (hsq : ∀ a, P a * P a = 1) (X : Submodule K V) (hX : ∀ a, ∀ x ∈ X, P a x ∈ X)
    {v₀ : V} (hv₀X : v₀ ∈ X) (hv₀ : v₀ ≠ 0) (s : Finset A) :
    ∃ v ∈ X, v ≠ 0 ∧ ∃ χ : A → K, ∀ a ∈ s, P a v = χ a • v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨v₀, hv₀X, hv₀, fun _ => 0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨v, hvX, hv0, χ, hχ⟩ := ih
    have hjj : P j (P j v) = v := by
      rw [← Module.End.mul_apply, hsq, Module.End.one_apply]
    have hne : ∀ a ∈ s, a ≠ j := fun a ha h => hj (h ▸ ha)
    by_cases h : v + P j v = 0
    · refine ⟨v, hvX, hv0, Function.update χ j (-1), fun a ha => ?_⟩
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rw [Function.update_self, neg_one_smul]
        exact eq_neg_of_add_eq_zero_right h
      · rw [Function.update_of_ne (hne a ha)]
        exact hχ a ha
    · refine ⟨v + P j v, X.add_mem hvX (hX j v hvX), h, Function.update χ j 1, fun a ha => ?_⟩
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rw [Function.update_self, one_smul, map_add, hjj, add_comm]
      · rw [Function.update_of_ne (hne a ha), map_add, hχ a ha, smul_add,
          ← Module.End.mul_apply, (hcomm a j).eq, Module.End.mul_apply, hχ a ha, map_smul]

theorem linearIndependent_of_eigen {ι : Type*} (hcomm : ∀ a b, Commute (P a) (P b))
    (χ : ι → A → K) (hχ : Function.Injective χ) (v : ι → V)
    (hv : ∀ i a, P a (v i) = χ i a • v i) (hv0 : ∀ i, v i ≠ 0) : LinearIndependent K v := by
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo P
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  refine (hind.comp hχ).linearIndependent _ (fun i => ?_) hv0
  simp only [Function.comp_apply, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace]
  exact fun a => ⟨1, by simp [hv i a]⟩

theorem natCard_le_finrank {M ι : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
    [Finite ι] {v : ι → M} (h : LinearIndependent K v) : Nat.card ι ≤ Module.finrank K M := by
  have := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact h.fintype_card_le_finrank

end Linear

section Group

variable {F K V : Type} [Field F] [Field K] [AddCommGroup V] [Module K V]

theorem sigma_uu_mul_self [CharP F 2] (σ : SL(2, F) →* Module.End K V) (a : F) :
    σ (uu a) * σ (uu a) = 1 := by
  rw [← map_mul, ← uu_add, CharTwo.add_self_eq_zero, uu_zero, map_one]

theorem commute_sigma_uu (σ : SL(2, F) →* Module.End K V) (a b : F) :
    Commute (σ (uu a)) (σ (uu b)) :=
  (show Commute (uu a) (uu b) from uu_mul_comm a b).map σ

theorem sigma_apply_ne_zero (σ : SL(2, F) →* Module.End K V) (g : SL(2, F)) {v : V}
    (hv : v ≠ 0) : σ g v ≠ 0 := by
  have h : σ g⁻¹ (σ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro h0
  rw [h0, map_zero] at h
  exact hv h.symm

theorem ker_sigma_eq_bot (σ : SL(2, F) →* Module.End K V) (g : SL(2, F)) :
    LinearMap.ker (σ g) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro m hm
  by_contra h
  exact sigma_apply_ne_zero σ g h hm

variable {σ : SL(2, F) →* Module.End K V} {v : V} {χ : F → K}

theorem eigen_add (hv0 : v ≠ 0) (hv : ∀ a, σ (uu a) v = χ a • v) (a b : F) :
    χ (a + b) = χ a * χ b := by
  apply smul_left_injective K hv0
  change χ (a + b) • v = (χ a * χ b) • v
  rw [← hv, uu_add, map_mul, Module.End.mul_apply, hv, map_smul, hv, smul_smul, mul_comm]

theorem eigen_zero (hv0 : v ≠ 0) (hv : ∀ a, σ (uu a) v = χ a • v) : χ 0 = 1 := by
  apply smul_left_injective K hv0
  change χ 0 • v = (1 : K) • v
  rw [← hv, uu_zero, map_one, Module.End.one_apply, one_smul]

theorem eigen_mul_self [CharP F 2] (hv0 : v ≠ 0) (hv : ∀ a, σ (uu a) v = χ a • v) (a : F) :
    χ a * χ a = 1 := by
  rw [← eigen_add hv0 hv, CharTwo.add_self_eq_zero, eigen_zero hv0 hv]

theorem uu_sq_mul_apply_hh [CharP F 2] (hv : ∀ a, σ (uu a) v = χ a • v) (x : Fˣ) (c : F) :
    σ (uu ((x : F) ^ 2 * c)) (σ (hh x) v) = χ c • σ (hh x) v := by
  have h : uu ((x : F) ^ 2 * c) * hh x = hh x * uu c := by
    rw [← hh_conj_uu x c, inv_mul_cancel_right]
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply, hv, map_smul]

theorem exists_eigen_mul [CharP F 2] [Finite F] (hv0 : v ≠ 0) (hv : ∀ a, σ (uu a) v = χ a • v)
    (μ : Fˣ) :
    ∃ w : V, w ≠ 0 ∧ ∀ b, σ (uu b) w = χ (μ * b) • w := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) ((μ⁻¹ : Fˣ) : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact (μ⁻¹).ne_zero hr
  refine ⟨σ (hh (Units.mk0 r hr0)) v, sigma_apply_ne_zero σ _ hv0, fun b => ?_⟩
  have hb : b = ((Units.mk0 r hr0 : Fˣ) : F) ^ 2 * (μ * b) := by
    rw [Units.val_mk0, pow_two, ← hr, ← mul_assoc, Units.inv_mul, one_mul]
  conv_lhs => rw [hb]
  exact uu_sq_mul_apply_hh hv _ _

theorem injective_mul_char (hK : (2 : K) ≠ 0) (hadd : ∀ a b, χ (a + b) = χ a * χ b)
    (hsq : ∀ a, χ a * χ a = 1) (h1 : χ 1 = -1) :
    Function.Injective fun (μ : Fˣ) (b : F) => χ (μ * b) := by
  intro μ ν h
  by_contra hne
  have hne' : (μ : F) - ν ≠ 0 := sub_ne_zero.mpr fun h' => hne (Units.ext h')
  have hb : (μ : F) * ((μ : F) - ν)⁻¹ = ν * ((μ : F) - ν)⁻¹ + 1 := by
    rw [← sub_eq_iff_eq_add', ← sub_mul, mul_inv_cancel₀ hne']
  have e : χ ((μ : F) * ((μ : F) - ν)⁻¹) = χ ((ν : F) * ((μ : F) - ν)⁻¹) :=
    congrFun h ((μ : F) - ν)⁻¹
  rw [hb, hadd, h1] at e
  have h2 : (2 : K) * χ ((ν : F) * ((μ : F) - ν)⁻¹) = 0 := by linear_combination -e
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact hK h2
  · have h3 := hsq ((ν : F) * ((μ : F) - ν)⁻¹)
    rw [h2, zero_mul] at h3
    exact zero_ne_one h3

theorem two_mul_card_eq [CharP F 2] [Finite F] (hK : (2 : K) ≠ 0)
    (hadd : ∀ a b, χ (a + b) = χ a * χ b) (hsq : ∀ a, χ a * χ a = 1) (h1 : χ 1 = -1) :
    2 * Nat.card {x : F // χ x = 1} = Nat.card F := by
  classical
  have hne : (-1 : K) ≠ 1 := fun h => hK (by linear_combination -h)
  have hshift : ∀ x, χ (x + 1) = -χ x := fun x => by rw [hadd, h1, mul_neg_one]
  have hback : ∀ x : F, x + 1 + 1 = x := fun x => by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  let e : {x : F // χ x = 1} ≃ {x : F // ¬χ x = 1} :=
    { toFun := fun x => ⟨x.1 + 1, by rw [hshift, x.2]; exact hne⟩
      invFun := fun x => ⟨x.1 + 1, by
        rw [hshift]
        rcases mul_self_eq_one_iff.mp (hsq x.1) with h | h
        · exact absurd h x.2
        · rw [h, neg_neg]⟩
      left_inv := fun x => Subtype.ext (hback x.1)
      right_inv := fun x => Subtype.ext (hback x.1) }
  rw [← Nat.card_congr (Equiv.sumCompl fun x : F => χ x = 1), Nat.card_sum,
    ← Nat.card_congr e, two_mul]

theorem card_units_add_one [Finite F] (h0 : χ 0 = 1) :
    Nat.card {μ : Fˣ // χ μ = 1} + 1 = Nat.card {x : F // χ x = 1} := by
  classical
  let e : {y : {x : F // χ x = 1} // ¬y.1 = 0} ≃ {μ : Fˣ // χ μ = 1} :=
    { toFun := fun y => ⟨Units.mk0 y.1.1 y.2, y.1.2⟩
      invFun := fun μ => ⟨⟨μ.1, μ.2⟩, μ.1.ne_zero⟩
      left_inv := fun y => rfl
      right_inv := fun μ => Subtype.ext (Units.ext rfl) }
  have hu : Nat.card {y : {x : F // χ x = 1} // y.1 = 0} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨⟨0, h0⟩, rfl⟩, fun y => Subtype.ext (Subtype.ext y.2)⟩
  rw [← Nat.card_congr (Equiv.sumCompl fun y : {x : F // χ x = 1} => y.1 = 0), Nat.card_sum,
    hu, Nat.card_congr e, add_comm]

theorem finrank_bounds [CharP F 2] [Finite F] [Module.Finite K V] (hK : (2 : K) ≠ 0)
    (σ : SL(2, F) →* Module.End K V) (hσ : Function.Injective σ) :
    Nat.card F - 1 ≤ Module.finrank K V ∧
      ∀ X : SL(2, F), X * X = 1 → X ≠ 1 →
        Nat.card F / 2 - 1 ≤ Module.finrank K (LinearMap.ker (σ X - 1)) := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨v₁, hv₁⟩ : ∃ v, σ (uu 1) v ≠ v := by
    by_contra! h
    have h1 : σ (uu 1) = σ 1 := by
      rw [map_one]
      exact LinearMap.ext h
    exact one_ne_zero (uu_injective ((hσ h1).trans uu_zero.symm))
  have hu1 : ∀ w, σ (uu 1) (σ (uu 1) w) = w := fun w => by
    rw [← Module.End.mul_apply, sigma_uu_mul_self, Module.End.one_apply]
  have hX₀ : ∀ a, ∀ x ∈ LinearMap.ker (σ (uu 1) + 1), σ (uu a) x ∈
      LinearMap.ker (σ (uu 1) + 1) := by
    intro a x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hx ⊢
    rw [← Module.End.mul_apply, ← (commute_sigma_uu σ a 1).eq, Module.End.mul_apply, ← map_add,
      hx, map_zero]
  have hv₀ : v₁ - σ (uu 1) v₁ ∈ LinearMap.ker (σ (uu 1) + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_sub, hu1]
    abel
  obtain ⟨v, hvX, hv0, χ, hχ⟩ := exists_common_eigenvector (fun a => σ (uu a))
    (commute_sigma_uu σ) (sigma_uu_mul_self σ) _ hX₀ hv₀ (sub_ne_zero.mpr hv₁.symm)
    Finset.univ
  have hv : ∀ a, σ (uu a) v = χ a • v := fun a => hχ a (Finset.mem_univ a)
  have h1 : χ 1 = -1 := by
    apply smul_left_injective K hv0
    change χ 1 • v = (-1 : K) • v
    rw [← hv, neg_one_smul]
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hvX
    exact eq_neg_of_add_eq_zero_left hvX
  have hadd := eigen_add hv0 hv
  have hsq := eigen_mul_self hv0 hv
  choose w hw0 hw using exists_eigen_mul hv0 hv
  have hind : LinearIndependent K w :=
    linearIndependent_of_eigen (fun a => σ (uu a)) (commute_sigma_uu σ) _
      (injective_mul_char hK hadd hsq h1) w hw hw0
  refine ⟨?_, fun Y hY2 hY1 => ?_⟩
  · have h := natCard_le_finrank hind
    rwa [Nat.card_units] at h
  · obtain ⟨M, rfl⟩ := exists_conj_eq_uu_one hY2 hY1
    have hmem : ∀ μ : {μ : Fˣ // χ μ = 1},
        σ M (w μ.1) ∈ LinearMap.ker (σ (M * uu 1 * M⁻¹) - 1) := by
      intro μ
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
        hw, mul_one, μ.2, one_smul]
    let w' : {μ : Fˣ // χ μ = 1} → LinearMap.ker (σ (M * uu 1 * M⁻¹) - 1) :=
      fun μ => ⟨σ M (w μ.1), hmem μ⟩
    have hind' : LinearIndependent K w' := by
      apply LinearIndependent.of_comp (LinearMap.ker (σ (M * uu 1 * M⁻¹) - 1)).subtype
      exact (hind.comp Subtype.val Subtype.val_injective).map' (σ M) (ker_sigma_eq_bot σ M)
    have h := natCard_le_finrank hind'
    have hc1 := card_units_add_one (eigen_zero hv0 hv)
    have hc2 := two_mul_card_eq hK hadd hsq h1
    omega

end Group

end LandazuriSeitzProof

open LandazuriSeitzProof KS116Proof in
theorem landazuriSeitzL2Even : LandazuriSeitzL2Even := by
  intro f hf p _ hp V _ _ _ ρ hρ
  have hK : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp)
  set E := projSLEquiv (GaloisField 2 f)
  obtain ⟨h1, h2⟩ := finrank_bounds hK (ρ.comp E.toMonoidHom) (hρ.comp E.injective)
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rw [hcard] at h1 h2
  refine ⟨h1, fun t ht => ?_⟩
  obtain ⟨X, rfl⟩ := E.surjective t
  have hX2 : X * X = 1 := by
    apply E.injective
    have h := pow_orderOf_eq_one (E X)
    rw [ht] at h
    rw [map_mul, map_one, ← pow_two]
    exact h
  have hX1 : X ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    omega
  have hf2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e : (2 ^ f - 2) / 2 = 2 ^ f / 2 - 1 := by omega
  rw [e]
  exact h2 X hX2 hX1

end CFSG.RankThree.PartTwo.KFacts
