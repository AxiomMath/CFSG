module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

set_option linter.style.haveILetI false

public section

namespace CFSG.RankThree.PerfectCover

open scoped commutatorElement

universe u

variable {S : Type u} [Group S]

noncomputable abbrev hopfCoverTwistMap (δ : MulAut S) : HopfCover S →* S :=
  δ.symm.toMonoidHom.comp (hopfCoverMap S)

theorem hopfCoverTwistMap_surjective [Group.IsPerfect S] (δ : MulAut S) :
    Function.Surjective (hopfCoverTwistMap δ) :=
  δ.symm.surjective.comp (hopfCoverMap_surjective)

theorem hopfCoverTwistMap_ker (δ : MulAut S) :
    (hopfCoverTwistMap δ).ker ≤ Subgroup.center (HopfCover S) := by
  intro x hx
  apply hopfMultiplier_le_center (S := S)
  have hx' : δ.symm (hopfCoverMap S x) = 1 := by simpa [hopfCoverTwistMap] using hx
  have hx'' : hopfCoverMap S x = 1 := δ.symm.injective (by simpa using hx')
  exact hx''

@[expose] noncomputable def hopfCoverAutHom [Finite S] [Group.IsPerfect S] (δ : MulAut S) :
    HopfCover S →* HopfCover S :=
  hopfLift (hopfCoverTwistMap δ) (hopfCoverTwistMap_surjective δ)
    (hopfCoverTwistMap_ker δ)

theorem hopfCoverAutHom_surjective [Finite S] [Group.IsPerfect S] (δ : MulAut S) :
    Function.Surjective (hopfCoverAutHom δ) := by
  classical
  letI : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect (S := S)
  unfold hopfCoverAutHom
  exact hopfLift_surjective _ _ _

@[expose] noncomputable def hopfCoverAut [Finite S] [Group.IsPerfect S] (δ : MulAut S) :
    MulAut (HopfCover S) := by
  classical
  letI : Finite (HopfCover S) := finite_hopfCover (inferInstance : Group.IsPerfect S)
  exact MulEquiv.ofBijective (hopfCoverAutHom δ)
    (Finite.surjective_iff_bijective.1 (hopfCoverAutHom_surjective δ))

@[simp]
theorem hopfCoverAut_toMonoidHom [Finite S] [Group.IsPerfect S] (δ : MulAut S) :
    (hopfCoverAut δ).toMonoidHom = hopfCoverAutHom δ := rfl

theorem hopfCoverMap_hopfCoverAut [Finite S] [Group.IsPerfect S] (δ : MulAut S) :
    (hopfCoverMap S).comp (hopfCoverAut δ).toMonoidHom =
      δ.toMonoidHom.comp (hopfCoverMap S) := by
  classical
  rw [hopfCoverAut_toMonoidHom]
  unfold hopfCoverAutHom
  have h := comp_hopfLift (hopfCoverTwistMap δ) (hopfCoverTwistMap_surjective δ)
    (hopfCoverTwistMap_ker δ)
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun h x
  have hx' := congrArg δ hx
  simpa [hopfCoverTwistMap] using hx'

theorem hopfCoverAut_pow_three [Finite S] [Group.IsPerfect S] (δ : MulAut S)
    (hδ : δ ^ 3 = 1) : hopfCoverAut δ ^ 3 = 1 := by
  classical
  letI : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect (S := S)
  have hpow : ∀ n : ℕ, (hopfCoverMap S).comp ((hopfCoverAut δ ^ n).toMonoidHom) =
      (δ ^ n).toMonoidHom.comp (hopfCoverMap S) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      rfl
    | succ n ih =>
      rw [pow_succ]
      change (hopfCoverMap S).comp
        ((hopfCoverAut δ ^ n).toMonoidHom.comp (hopfCoverAut δ).toMonoidHom) =
        (δ ^ (n + 1)).toMonoidHom.comp (hopfCoverMap S)
      calc
        (hopfCoverMap S).comp
            ((hopfCoverAut δ ^ n).toMonoidHom.comp (hopfCoverAut δ).toMonoidHom)
            = ((hopfCoverMap S).comp (hopfCoverAut δ ^ n).toMonoidHom).comp
                (hopfCoverAut δ).toMonoidHom := by rw [MonoidHom.comp_assoc]
        _ = ((δ ^ n).toMonoidHom.comp (hopfCoverMap S)).comp
                (hopfCoverAut δ).toMonoidHom := by rw [ih]
        _ = (δ ^ n).toMonoidHom.comp
                ((hopfCoverMap S).comp (hopfCoverAut δ).toMonoidHom) := by
              rw [MonoidHom.comp_assoc]
        _ = (δ ^ n).toMonoidHom.comp (δ.toMonoidHom.comp (hopfCoverMap S)) := by
              rw [hopfCoverMap_hopfCoverAut]
        _ = ((δ ^ n).toMonoidHom.comp δ.toMonoidHom).comp (hopfCoverMap S) := by
              rw [MonoidHom.comp_assoc]
        _ = (δ ^ (n + 1)).toMonoidHom.comp (hopfCoverMap S) := by
              rw [pow_succ]
              rfl
  have h3 : (δ ^ 3).toMonoidHom = MonoidHom.id S := by
    rw [hδ]
    exact MulEquiv.toMonoidHom_refl
  have hcomp : (hopfCoverMap S).comp ((hopfCoverAut δ ^ 3).toMonoidHom) =
      hopfCoverMap S := by
    have h := hpow 3
    rw [h3, MonoidHom.id_comp] at h
    exact h
  have huniq := hopfCover_hom_ext (S := S) (q := hopfCoverMap S)
    (hopfMultiplier_le_center (S := S))
    ((hopfCoverAut δ ^ 3).toMonoidHom) (MonoidHom.id (HopfCover S)) hcomp
    (by simp)
  exact MulEquiv.ext fun x => by
    have hx := congrFun (congrArg DFunLike.coe huniq) x
    simpa using hx

theorem hopfCover_hom_ext_of_comp_eq {E : Type u} [Group E] [Group.IsPerfect S]
    (q : E →* S) (hker : q.ker ≤ Subgroup.center E)
    (h₁ h₂ : HopfCover S →* E) (he : q.comp h₁ = q.comp h₂) : h₁ = h₂ := by
  have hc : ∀ u, (h₁ u)⁻¹ * h₂ u ∈ Subgroup.center E := by
    intro u
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
      he, inv_mul_cancel]
  have hcomm : commutator (HopfCover S) ≤ MonoidHom.eqLocus h₁ h₂ := by
    rw [_root_.commutator_def (HopfCover S), Subgroup.commutator_le]
    intro u _ v _
    change h₁ ⁅u, v⁆ = h₂ ⁅u, v⁆
    rw [map_commutatorElement, map_commutatorElement]
    have hu : h₂ u = h₁ u * ((h₁ u)⁻¹ * h₂ u) := by group
    have hv : h₂ v = h₁ v * ((h₁ v)⁻¹ * h₂ v) := by group
    rw [hu, hv, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc u) (hc v)]
  have : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect
  rw [Group.IsPerfect.commutator_eq_top (G := HopfCover S)] at hcomm
  refine MonoidHom.ext fun u => ?_
  exact hcomm (Subgroup.mem_top u)

theorem hopfCoverAut_mul [Finite S] [Group.IsPerfect S] (δ₁ δ₂ : MulAut S) :
    hopfCoverAut (δ₁ * δ₂) = hopfCoverAut δ₁ * hopfCoverAut δ₂ := by
  apply MulEquiv.ext
  intro x
  have hhom : (hopfCoverAut (δ₁ * δ₂)).toMonoidHom =
      ((hopfCoverAut δ₁) * (hopfCoverAut δ₂)).toMonoidHom := by
    apply hopfCover_hom_ext_of_comp_eq (S := S) (E := HopfCover S)
      (q := hopfCoverMap S) (hker := hopfMultiplier_le_center (S := S))
    ext y
    simp only [MonoidHom.comp_apply]
    change hopfCoverMap S (hopfCoverAut (δ₁ * δ₂) (y : HopfCover S)) =
      hopfCoverMap S ((hopfCoverAut δ₁ * hopfCoverAut δ₂) (y : HopfCover S))
    rw [show hopfCoverMap S (hopfCoverAut (δ₁ * δ₂) (y : HopfCover S)) =
        (δ₁ * δ₂) (hopfCoverMap S (y : HopfCover S)) from
      DFunLike.congr_fun (hopfCoverMap_hopfCoverAut (δ₁ * δ₂)) (y : HopfCover S)]
    rw [MulAut.mul_apply]
    rw [MulAut.mul_apply]
    rw [show hopfCoverMap S (hopfCoverAut δ₁ (hopfCoverAut δ₂ (y : HopfCover S))) =
        δ₁ (hopfCoverMap S (hopfCoverAut δ₂ (y : HopfCover S))) from
      DFunLike.congr_fun (hopfCoverMap_hopfCoverAut δ₁) (hopfCoverAut δ₂ (y : HopfCover S))]
    rw [show hopfCoverMap S (hopfCoverAut δ₂ (y : HopfCover S)) =
        δ₂ (hopfCoverMap S (y : HopfCover S)) from
      DFunLike.congr_fun (hopfCoverMap_hopfCoverAut δ₂) (y : HopfCover S)]
  exact DFunLike.congr_fun hhom x

theorem hopfCoverAut_sq [Finite S] [Group.IsPerfect S] (δ : MulAut S) :
    hopfCoverAut (δ ^ 2) = hopfCoverAut δ ^ 2 := by
  rw [pow_two, hopfCoverAut_mul, pow_two]

theorem fixed_free_pow_two (α : MulAut (HopfCover S)) (hα3 : α ^ 3 = 1)
    (hfree : ∀ z ∈ hopfMultiplier S, (∃ k : ℕ, z ^ (2 ^ k) = 1) → α z = z → z = 1) :
    ∀ z ∈ hopfMultiplier S, (∃ k : ℕ, z ^ (2 ^ k) = 1) → (α ^ 2) z = z → z = 1 := by
  intro z hz h2 hfix
  apply hfree z hz h2
  have h2fix : α (α z) = z := by simpa [pow_two] using hfix
  have h3z : (α ^ 3) z = z := by simpa using DFunLike.congr_fun hα3 z
  calc α z = α (α (α z)) := by rw [h2fix]
    _ = (α ^ 3) z := by simp [pow_succ]
    _ = z := h3z

end CFSG.RankThree.PerfectCover

namespace CFSG.GroupTheory

theorem fixed_eq_one_of_aut_pow_three_card_four {V : Type} [Group V] [Finite V]
    (hcardV : Nat.card V = 4) (α : MulAut V) (hα3 : α ^ 3 = 1) (hαne : α ≠ 1) :
    ∀ v : V, α v = v → v = 1 := by
  classical
  let A : Subgroup (MulAut V) := Subgroup.zpowers α
  have hAcard : Nat.card A = 3 := by
    rw [show A = Subgroup.zpowers α from rfl, Nat.card_zpowers]
    have hdvd : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hαne
    · exact h
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hmod := hA3.card_modEq_card_fixedPoints V
  let F : Subgroup V := fixedPointSubgroup A V
  have hCeq : (MulAction.fixedPoints A V) = (F : Set V) := rfl
  have hcardFix : Nat.card ↥(MulAction.fixedPoints A V) = Nat.card F := by
    rw [hCeq]
    rfl
  rw [hcardV, hcardFix] at hmod
  have hmod' : Nat.card F ≡ 1 [MOD 3] :=
    hmod.symm.trans (by decide : 4 ≡ 1 [MOD 3])
  have hdvd : Nat.card F ∣ 4 := by
    simpa [hcardV] using Subgroup.card_dvd_of_le (le_top : F ≤ ⊤)
  have hmem : Nat.card F ∈ Nat.divisors 4 := by simp [hdvd]
  have hdiv4 : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdiv4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hmemF : ∀ {v : V}, α v = v → v ∈ F := by
    intro v hv
    change v ∈ FixedPoints.subgroup A V
    rw [FixedPoints.mem_subgroup A V v]
    intro a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
    change (a : MulAut V) v = v
    rw [← hn]
    have hinv : α⁻¹ v = v := by
      calc α⁻¹ v = α⁻¹ (α v) := by rw [hv]
        _ = v := MulAut.inv_apply_self V α v
    have hz : ∀ k : ℤ, (α ^ k) v = v := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ k ih =>
          rw [zpow_add_one, MulAut.mul_apply V (α ^ (k : ℤ)) α v, hv, ih]
      | pred k ih =>
          rw [zpow_sub_one, MulAut.mul_apply V (α ^ (-(k : ℤ))) α⁻¹ v, hinv, ih]
    exact hz n
  rcases hmem with h1 | h2 | h4
  · have hFbot : F = ⊥ := F.eq_bot_of_card_eq h1
    intro v hv
    have hvF : v ∈ F := hmemF hv
    rw [hFbot] at hvF
    simpa using hvF
  · rw [h2] at hmod'
    exact absurd hmod' (by decide)
  · have hFtop : F = ⊤ := F.eq_top_of_card_eq (by rw [h4, hcardV])
    have hα1 : α = 1 := by
      apply MulEquiv.ext
      intro v
      have hvF : v ∈ F := by rw [hFtop]; exact Subgroup.mem_top v
      have hv : (⟨α, Subgroup.mem_zpowers α⟩ : A) • v = v := by
        change v ∈ FixedPoints.subgroup A V at hvF
        rw [FixedPoints.mem_subgroup A V v] at hvF
        exact hvF _
      simpa using hv
    exact (hαne hα1).elim

end CFSG.GroupTheory
