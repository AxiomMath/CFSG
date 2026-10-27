module

public import CFSG.RankThree.PartOne.CTP.EStructure
public import CFSG.RankThree.PartOne.CTP.LinearTransfer
public import CFSG.RankThree.PartOne.CTP.LinearModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.RankThree.PartOne.CTP.LinearCore

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open scoped MatrixGroups

section Group

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {e : G} (hA : e ∈ Subgroup.normalizer (A : Set G))
    (hB : e ∈ Subgroup.normalizer (B : Set G)) :
    e ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have conj_mem : ∀ {e : G}, (∀ h ∈ A, e * h * e⁻¹ ∈ A) → (∀ h ∈ B, e * h * e⁻¹ ∈ B) →
      ∀ x ∈ A ⊔ B, e * x * e⁻¹ ∈ A ⊔ B := by
    intro e hA hB x hx
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj e).toMonoidHom := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · exact Subgroup.mem_sup_left (hA h hh)
      · exact Subgroup.mem_sup_right (hB h hh)
    exact hle hx
  have hA1 : ∀ h ∈ A, e * h * e⁻¹ ∈ A := fun h hh => (Subgroup.mem_normalizer_iff.mp hA h).mp hh
  have hB1 : ∀ h ∈ B, e * h * e⁻¹ ∈ B := fun h hh => (Subgroup.mem_normalizer_iff.mp hB h).mp hh
  have hA2 : ∀ h ∈ A, e⁻¹ * h * e⁻¹⁻¹ ∈ A := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp (inv_mem hA) h).mp hh
  have hB2 : ∀ h ∈ B, e⁻¹ * h * e⁻¹⁻¹ ∈ B := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp (inv_mem hB) h).mp hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨conj_mem hA1 hB1 x, fun hx => by
    have := conj_mem hA2 hB2 _ hx
    simpa [mul_assoc] using this⟩

theorem EdgeTorus.symm {p : ℕ} {E A B : Subgroup G} (h : EdgeTorus p E A B) :
    EdgeTorus p E B A where
  decA := h.decB
  idxA := h.idxB
  decB := h.decA
  idxB := h.idxA
  idxAB := by rw [sup_comm]; exact h.idxAB

theorem map_range_eq {K : Type*} [Group K] {C : Subgroup G} {Γ : Type*} [Group Γ]
    (θ : Γ →* G) (ρ : K ≃* ↥C) (φ : K →* Γ) (hφ : ∀ a, θ (φ a) = (ρ a : G)) :
    φ.range.map θ = C := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [hφ a]
    exact (ρ a).2
  · intro hx
    refine ⟨φ (ρ.symm ⟨x, hx⟩), ⟨_, rfl⟩, ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply]

end Group

section Center

theorem center_sl2_eq_bot {K : Type} [Field K] [CharP K 2] :
    Subgroup.center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  have hr' : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hr1 : r = 1 := by
    have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr' + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
  subst hr1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

end Center

section Lift

variable {F : Type} [Field F] {G : Type} [Group G]
  (θ : SL(3, F) →* G) (hker : θ.ker ≤ Subgroup.center SL(3, F))

include hker in
theorem not_two_dvd_card_ker [Finite F] : ¬ 2 ∣ Nat.card θ.ker := by
  intro h2
  have h1 : Nat.card θ.ker ∣ Nat.card (Subgroup.center SL(3, F)) := Subgroup.card_dvd_of_le hker
  have h3 := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3) (by omega) F
  have h4 : Nat.card θ.ker ∣ 3 := h1.trans (h3.trans (Nat.gcd_dvd_left 3 _))
  have := h2.trans h4
  omega

include hker in
theorem exists_sl2_lift [Finite F] {K : Type} [Field K] [Finite K] [CharP K 2] {C : Subgroup G}
    (hC : C ≤ θ.range) (ρ : SL(2, K) →* ↥C) :
    ∃ φ : SL(2, K) →* SL(3, F), ∀ a, θ (φ a) = (ρ a : G) := by
  have hπ : Function.Surjective θ.rangeRestrict := MonoidHom.rangeRestrict_surjective θ
  have hcen : θ.rangeRestrict.ker ≤ Subgroup.center SL(3, F) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hodd : ¬ 2 ∣ Nat.card θ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]; exact not_two_dvd_card_ker θ hker
  obtain ⟨φ, hφ, -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := 2) hπ hcen hodd
    ((Subgroup.inclusion hC).comp ρ)
  refine ⟨φ, fun a => ?_⟩
  have := DFunLike.congr_fun hφ a
  simpa using congrArg Subtype.val this

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
include hker in
theorem aut_pow_eq_one {e : G} (he : e ∈ Subgroup.normalizer (θ.range : Set G))
    {α : MulAut (projectiveSL 3 F)}
    (hα : ∀ g g' : SL(3, F), θ g' = e * θ g * e⁻¹ → α (proj 3 F g) = proj 3 F g') {p : ℕ}
    (hep : e ^ p = 1) : α ^ p = 1 := by
  have hex : ∀ x ∈ θ.range, e * x * e⁻¹ ∈ θ.range := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp he x).mp hx
  have key : ∀ k : ℕ, ∀ g : SL(3, F), ∃ g' : SL(3, F), θ g' = e ^ k * θ g * (e ^ k)⁻¹ ∧
      (α ^ k) (proj 3 F g) = proj 3 F g' := by
    intro k
    induction k with
    | zero => intro g; exact ⟨g, by simp, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨g', hg', hαg'⟩ := ih g
      obtain ⟨g'', hg''⟩ := hex (θ g') ⟨g', rfl⟩
      refine ⟨g'', ?_, ?_⟩
      · rw [hg'', hg']
        group
      · rw [pow_succ', MulAut.mul_apply, hαg']
        exact hα g' g'' hg''
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  obtain ⟨g', hg', hαg'⟩ := key p g
  rw [hαg']
  have hθ : θ g' = θ g := by rw [hg', hep]; simp
  have : g'⁻¹ * g ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ]; simp
  rw [proj_eq_proj_iff.mpr (by rw [scalars_eq_center]; exact hker this)]
  rfl

end Lift


section Main

variable {F : Type} [Field F] {G : Type} [Group G]
  (θ : SL(3, F) →* G) (hker : θ.ker ≤ Subgroup.center SL(3, F))

theorem edge_aut_data {C D : Subgroup G} {KC KD : Type} [Field KC] [Field KD] [CharP KD 2]
    (ρC : SL(2, KC) ≃* ↥C) (ρD : SL(2, KD) ≃* ↥D)
    (φC : SL(2, KC) →* SL(3, F)) (φD : SL(2, KD) →* SL(3, F))
    (hφC : ∀ a, θ (φC a) = (ρC a : G)) (hφD : ∀ b, θ (φD b) = (ρD b : G))
    {e : G} {α : MulAut (projectiveSL 3 F)}
    (hα : ∀ g g' : SL(3, F), θ g' = e * θ g * e⁻¹ → α (proj 3 F g) = proj 3 F g')
    (hcen : ∀ x ∈ C, e * x = x * e) (hnorm : ∀ y ∈ D, e * y * e⁻¹ ∈ D)
    (hmov : ∃ y ∈ D, e * y ≠ y * e) :
    (∀ a, α (proj 3 F (φC a)) = proj 3 F (φC a)) ∧
      (∀ b, ∃ b', α (proj 3 F (φD b)) = proj 3 F (φD b')) ∧
      ∃ b, α (proj 3 F (φD b)) ≠ proj 3 F (φD b) := by
  have hfix : ∀ a, α (proj 3 F (φC a)) = proj 3 F (φC a) := by
    intro a
    refine hα _ _ ?_
    rw [hφC a, eq_comm, mul_inv_eq_iff_eq_mul]
    exact hcen _ (ρC a).2
  have hstab : ∀ b, ∃ b', θ (φD b') = e * θ (φD b) * e⁻¹ := by
    intro b
    set y : G := e * θ (φD b) * e⁻¹ with hy
    have hyD : y ∈ D := by rw [hy, hφD b]; exact hnorm _ (ρD b).2
    refine ⟨ρD.symm ⟨y, hyD⟩, ?_⟩
    rw [hφD, MulEquiv.apply_symm_apply]
  refine ⟨hfix, fun b => ?_, ?_⟩
  · obtain ⟨b', hb'⟩ := hstab b
    exact ⟨b', hα _ _ hb'⟩
  · obtain ⟨y, hy, hyne⟩ := hmov
    let b0 := ρD.symm ⟨y, hy⟩
    obtain ⟨b', hb'⟩ := hstab b0
    have hθb0 : θ (φD b0) = y := by rw [hφD, MulEquiv.apply_symm_apply]
    refine ⟨b0, fun h => ?_⟩
    rw [hα _ _ hb'] at h
    have hz : (φD b0)⁻¹ * φD b' ∈ Subgroup.center SL(3, F) := by
      rw [← scalars_eq_center]
      exact proj_eq_proj_iff.mp h.symm
    have hzD : b0⁻¹ * b' ∈ Subgroup.center SL(2, KD) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := Subgroup.mem_center_iff.mp hz (φD x)
      have h2 : θ ((φD b0)⁻¹ * φD b') * θ (φD x) = θ (φD x) * θ ((φD b0)⁻¹ * φD b') := by
        rw [← map_mul, ← map_mul, h1]
      simp only [map_mul, map_inv, hφD] at h2
      apply ρD.injective
      apply Subtype.ext
      simpa [map_mul, map_inv] using h2.symm
    rw [center_sl2_eq_bot (K := KD), Subgroup.mem_bot, inv_mul_eq_one] at hzD
    subst hzD
    apply hyne
    have := hb'
    rw [hθb0] at this
    exact mul_inv_eq_iff_eq_mul.mp this.symm

include hker in
theorem edge_half {p : ℕ} (hp : p.Prime) {E A B : Subgroup G} [CFSG.IsElementaryAbelian p E]
    (hE : EdgeTorus p E A B) (hAB : A ⊔ B = θ.range) {KA KB : Type} [Field KA] [Field KB]
    [CharP KB 2] (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B)
    (φA : SL(2, KA) →* SL(3, F)) (φB : SL(2, KB) →* SL(3, F))
    (hφA : ∀ a, θ (φA a) = (ρA a : G)) (hφB : ∀ b, θ (φB b) = (ρB b : G)) :
    ∃ α : MulAut (projectiveSL 3 F), α ^ p = 1 ∧
      (∀ a, α (proj 3 F (φA a)) = proj 3 F (φA a)) ∧
      (∀ b, ∃ b', α (proj 3 F (φB b)) = proj 3 F (φB b')) ∧
      ∃ b, α (proj 3 F (φB b)) ≠ proj 3 F (φB b) := by
  obtain ⟨e, heE, hcen, hmov, hnorm, hord⟩ := hE.exists_centralizing hp
  have heA : e ∈ Subgroup.normalizer (A : Set G) := le_normalizer_of_dec hE.decA heE
  have heB : e ∈ Subgroup.normalizer (B : Set G) := le_normalizer_of_dec hE.decB heE
  have hX : e ∈ Subgroup.normalizer (θ.range : Set G) := by
    rw [← hAB]; exact mem_normalizer_sup heA heB
  obtain ⟨α, hα⟩ := exists_aut_of_conj θ hker hX
  have hep : e ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one e
  obtain ⟨h1, h2, h3⟩ := edge_aut_data θ ρA ρB φA φB hφA hφB hα hcen hnorm hmov
  exact ⟨α, aut_pow_eq_one θ hker hX hα hep, h1, h2, h3⟩

end Main

section Final

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]
  (θ : SL(3, F) →* G) (hker : θ.ker ≤ Subgroup.center SL(3, F))

include hker in
theorem linear_edge_standardPair (hq : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {E A B : Subgroup G} [CFSG.IsElementaryAbelian p E]
    (hE : EdgeTorus p E A B) (hAB : A ⊔ B = θ.range) {KA KB : Type} [Field KA] [Field KB]
    [Finite KA] [Finite KB] [CharP KA 2] [CharP KB 2]
    (hKA : Nat.card KA = Nat.card F) (hKB : Nat.card KB = Nat.card F)
    (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B) :
    ∃ c : SL(3, F), ((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = A ∧
      ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = B := by
  have hA : A ≤ θ.range := by rw [← hAB]; exact le_sup_left
  have hB : B ≤ θ.range := by rw [← hAB]; exact le_sup_right
  obtain ⟨φA, hφA⟩ := exists_sl2_lift θ hker hA ρA.toMonoidHom
  obtain ⟨φB, hφB⟩ := exists_sl2_lift θ hker hB ρB.toMonoidHom
  have hφA' : ∀ a, θ (φA a) = (ρA a : G) := fun a => hφA a
  have hφB' : ∀ b, θ (φB b) = (ρB b : G) := fun b => hφB b
  obtain ⟨αA, hαA, hAfix, hAB', hmovB⟩ := edge_half θ hker hp hE hAB ρA ρB φA φB hφA' hφB'
  obtain ⟨αB, hαB, hBfix, hBA', hmovA⟩ :=
    edge_half θ hker hp hE.symm (by rw [sup_comm]; exact hAB) ρB ρA φB φA hφB' hφA'
  have hinjA : Function.Injective φA := fun a a' h =>
    ρA.injective (Subtype.ext (by rw [← hφA' a, ← hφA' a', h]))
  have hinjB : Function.Injective φB := fun b b' h =>
    ρB.injective (Subtype.ext (by rw [← hφB' b, ← hφB' b', h]))
  obtain ⟨b, hbA, hbB⟩ := linear_edge_core hq hKA hKB hp hp2 hpq φA hinjA φB hinjB αA αB hαA hαB
    hAfix hBfix hAB' hBA' hmovB hmovA
  obtain ⟨c, hc1, hc2⟩ := exists_conj_of_basis b
  exact ⟨c, by rw [hc1, ← hbA]; exact map_range_eq θ ρA φA hφA',
    by rw [hc2, ← hbB]; exact map_range_eq θ ρB φB hφB'⟩

end Final

end CFSG.RankThree.PartOne.CTP
