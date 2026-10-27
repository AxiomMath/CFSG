module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.EmptyFaithful.S146zNAmtA
public import CFSG.Quasithin.Background.RonanH163Tiso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

private def pairType (X : Type*) : Type _ :=
  {τ : Equiv.Perm X // τ * τ = 1 ∧ τ ≠ 1 ∧ ∀ x, τ x ≠ x}

private lemma pairType_sq {X : Type*} (τ : pairType X) (x : X) : τ.1 (τ.1 x) = x := by
  have := congrArg (fun f : Equiv.Perm X => f x) τ.2.1
  simpa [Equiv.Perm.mul_apply] using this

private instance pairTypeMulAction (X : Type*) : MulAction (Equiv.Perm X) (pairType X) where
  smul σ τ := ⟨σ * τ.1 * σ⁻¹, by
    obtain ⟨h1, h2, h3⟩ := τ.2
    refine ⟨?_, ?_, ?_⟩
    · calc (σ * τ.1 * σ⁻¹) * (σ * τ.1 * σ⁻¹) = σ * (τ.1 * τ.1) * σ⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h
      exact h2 (by
        have := congrArg (fun f : Equiv.Perm X => σ⁻¹ * f * σ) h
        simpa [mul_assoc] using this)
    · intro x hx
      exact h3 (σ⁻¹ x) (σ.injective (by simpa [Equiv.Perm.mul_apply] using hx))⟩
  one_smul τ := by
    apply Subtype.ext
    show (1 : Equiv.Perm X) * τ.1 * 1⁻¹ = τ.1
    group
  mul_smul σ ρ τ := by
    apply Subtype.ext
    show (σ * ρ) * τ.1 * (σ * ρ)⁻¹ = σ * (ρ * τ.1 * ρ⁻¹) * σ⁻¹
    group

private def dbl : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

private lemma dbl_fpf (j : Fin 3) :
    dbl j * dbl j = 1 ∧ dbl j ≠ 1 ∧ ∀ x, dbl j x ≠ x := by
  fin_cases j <;> decide

private def fpfIdx (τ : pairType (Fin 4)) : Fin 3 :=
  if τ.1 0 = 1 then 0 else if τ.1 0 = 2 then 1 else 2

private def ofIdx (j : Fin 3) : pairType (Fin 4) := ⟨dbl j, dbl_fpf j⟩

private lemma fpf_perm_mem {f : Fin 4 → Fin 4} (hinv : ∀ x, f (f x) = x)
    (hfix : ∀ x, f x ≠ x) :
    f ∈ ({(dbl 0 : Fin 4 → Fin 4), (dbl 1 : Fin 4 → Fin 4),
      (dbl 2 : Fin 4 → Fin 4)} : Finset (Fin 4 → Fin 4)) := by
  have hinj : Function.Injective f := fun x y h => by rw [← hinv x, h, hinv y]
  obtain ⟨k, hk⟩ : ∃ k : Fin 4, f 0 = k := ⟨_, rfl⟩
  fin_cases k <;>
    simp only [Finset.mem_insert, Finset.mem_singleton]
  · exact absurd hk (hfix 0)
  · left
    have h1 : f 1 = 0 := by have := hinv 0; rwa [hk] at this
    have h2 : f 2 = 3 := by
      have hne0 : f 2 ≠ 0 := fun h => absurd (hinj (h.trans h1.symm)) (by decide)
      have hne1 : f 2 ≠ 1 := fun h => absurd (hinj (h.trans hk.symm)) (by decide)
      have hne2 : f 2 ≠ 2 := hfix 2
      obtain ⟨v, hv⟩ : ∃ v : Fin 4, f 2 = v := ⟨_, rfl⟩
      fin_cases v
      · exact absurd hv hne0
      · exact absurd hv hne1
      · exact absurd hv hne2
      · exact hv
    have h3 : f 3 = 2 := by have := hinv 2; rwa [h2] at this
    funext x
    fin_cases x <;> simp [dbl, hk, h1, h2, h3, Equiv.swap_apply_def]
  · right; left
    have h2 : f 2 = 0 := by have := hinv 0; rwa [hk] at this
    have h1 : f 1 = 3 := by
      have hne0 : f 1 ≠ 0 := fun h => absurd (hinj (h.trans h2.symm)) (by decide)
      have hne2 : f 1 ≠ 2 := fun h => absurd (hinj (h.trans hk.symm)) (by decide)
      have hne1 : f 1 ≠ 1 := hfix 1
      obtain ⟨v, hv⟩ : ∃ v : Fin 4, f 1 = v := ⟨_, rfl⟩
      fin_cases v
      · exact absurd hv hne0
      · exact absurd hv hne1
      · exact absurd hv hne2
      · exact hv
    have h3 : f 3 = 1 := by have := hinv 1; rwa [h1] at this
    funext x
    fin_cases x <;> simp [dbl, hk, h1, h2, h3, Equiv.swap_apply_def]
  · right; right
    have h3 : f 3 = 0 := by have := hinv 0; rwa [hk] at this
    have h1 : f 1 = 2 := by
      have hne0 : f 1 ≠ 0 := fun h => absurd (hinj (h.trans h3.symm)) (by decide)
      have hne3 : f 1 ≠ 3 := fun h => absurd (hinj (h.trans hk.symm)) (by decide)
      have hne1 : f 1 ≠ 1 := hfix 1
      obtain ⟨v, hv⟩ : ∃ v : Fin 4, f 1 = v := ⟨_, rfl⟩
      fin_cases v
      · exact absurd hv hne0
      · exact absurd hv hne1
      · exact hv
      · exact absurd hv hne3
    have h2 : f 2 = 1 := by have := hinv 1; rwa [h1] at this
    funext x
    fin_cases x <;> simp [dbl, hk, h1, h2, h3, Equiv.swap_apply_def]

private lemma fpfIdx_dbl (j : Fin 3) : fpfIdx (ofIdx j) = j := by
  fin_cases j <;> decide

private lemma fpfIdx_eq_of_eq_dbl {τ : pairType (Fin 4)} {j : Fin 3}
    (h : (τ.1 : Fin 4 → Fin 4) = (dbl j : Fin 4 → Fin 4)) : fpfIdx τ = j := by
  have h' : fpfIdx τ = fpfIdx (ofIdx j) := by
    simp only [fpfIdx, ofIdx]
    rw [h]
    rfl
  rw [h', fpfIdx_dbl]

private lemma fpfIdx_injective : Function.Injective fpfIdx := by
  intro τ σ h
  have hτ := fpf_perm_mem (f := τ.1) (pairType_sq τ) τ.2.2.2
  have hσ := fpf_perm_mem (f := σ.1) (pairType_sq σ) σ.2.2.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ hσ
  have key : ∀ (a b : Fin 3) (u v : pairType (Fin 4)),
      (u.1 : Fin 4 → Fin 4) = (dbl a : Fin 4 → Fin 4) →
      (v.1 : Fin 4 → Fin 4) = (dbl b : Fin 4 → Fin 4) → fpfIdx u = fpfIdx v → u = v := by
    intro a b u v hu hv hh
    have hh' : a = b := by
      rw [fpfIdx_eq_of_eq_dbl hu, fpfIdx_eq_of_eq_dbl hv] at hh
      exact hh
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [hu, hv, hh']
  rcases hτ with h0 | h1 | h2 <;> rcases hσ with g0 | g1 | g2
  · exact key 0 0 τ σ h0 g0 h
  · exact key 0 1 τ σ h0 g1 h
  · exact key 0 2 τ σ h0 g2 h
  · exact key 1 0 τ σ h1 g0 h
  · exact key 1 1 τ σ h1 g1 h
  · exact key 1 2 τ σ h1 g2 h
  · exact key 2 0 τ σ h2 g0 h
  · exact key 2 1 τ σ h2 g1 h
  · exact key 2 2 τ σ h2 g2 h

private lemma fpfIdx_surjective : Function.Surjective fpfIdx :=
  fun j => ⟨ofIdx j, fpfIdx_dbl j⟩

private lemma pairType_ncard_fin4 : Nat.card (pairType (Fin 4)) = 3 := by
  rw [Nat.card_congr (Equiv.ofBijective fpfIdx ⟨fpfIdx_injective, fpfIdx_surjective⟩),
    Nat.card_fin]

private def pairCongr {X : Type*} (e : X ≃ Fin 4) : pairType X ≃ pairType (Fin 4) where
  toFun τ := ⟨e.permCongrHom τ.1, by
    obtain ⟨h1, h2, h3⟩ := τ.2
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · intro h
      exact h2 (e.permCongrHom.injective (by rw [h, map_one]))
    · intro y hy
      exact h3 (e.symm y) (e.injective (by
        simpa [Equiv.permCongrHom, Equiv.permCongr_apply] using hy))⟩
  invFun τ := ⟨e.symm.permCongrHom τ.1, by
    obtain ⟨h1, h2, h3⟩ := τ.2
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · intro h
      exact h2 (e.symm.permCongrHom.injective (by rw [h, map_one]))
    · intro x hx
      exact h3 (e x) (e.symm.injective (by
        simpa [Equiv.permCongrHom, Equiv.permCongr_apply] using hx))⟩
  left_inv τ := by
    apply Subtype.ext
    ext x
    simp [Equiv.permCongrHom, Equiv.permCongr_apply]
  right_inv τ := by
    apply Subtype.ext
    ext x
    simp [Equiv.permCongrHom, Equiv.permCongr_apply]

private lemma pairType_ncard {X : Type*} [Finite X] (hX : Nat.card X = 4) :
    Nat.card (pairType X) = 3 := by
  have e : X ≃ Fin 4 := Finite.equivFinOfCardEq hX
  rw [Nat.card_congr (pairCongr e)]
  exact pairType_ncard_fin4

private lemma pairType_extract {X : Type*} [Finite X] (hX : Nat.card X = 4)
    (Q : Subgroup (Equiv.Perm X)) (τ : pairType X) (hτ : ∀ q : ↥Q, q • τ = τ) :
    ∃ B₁ B₂ : Set X, B₁ ∪ B₂ = Set.univ ∧ Disjoint B₁ B₂ ∧ B₁.ncard = 2 ∧ B₂.ncard = 2 ∧
      ∀ q ∈ Q, (q '' B₁ = B₁ ∧ q '' B₂ = B₂) ∨ (q '' B₁ = B₂ ∧ q '' B₂ = B₁) := by
  have hτ2 : ∀ x, τ.1 (τ.1 x) = x := pairType_sq τ
  have hτfix : ∀ x, τ.1 x ≠ x := τ.2.2.2
  have hne : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  obtain ⟨x₀⟩ := hne
  let B₁ : Set X := {x₀, τ.1 x₀}
  let B₂ : Set X := B₁ᶜ
  have hB₁card : B₁.ncard = 2 := by
    show ({x₀, τ.1 x₀} : Set X).ncard = 2
    exact Set.ncard_pair (Ne.symm (hτfix x₀))
  have hB₂card : B₂.ncard = 2 := by
    show B₁ᶜ.ncard = 2
    exact Set.ncard_compl_of_ncard_eq_add B₁ (by rw [hX, hB₁card])
  have hB₁inv : τ.1 '' B₁ = B₁ := by
    show τ.1 '' ({x₀, τ.1 x₀} : Set X) = {x₀, τ.1 x₀}
    rw [Set.image_pair]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hτ2 x₀]
    tauto
  have hB₂inv : τ.1 '' B₂ = B₂ := by
    show τ.1 '' B₁ᶜ = B₁ᶜ
    rw [Set.image_compl_eq τ.1.bijective, hB₁inv]
  refine ⟨B₁, B₂, ?_, ?_, hB₁card, hB₂card, ?_⟩
  · show B₁ ∪ B₁ᶜ = Set.univ
    exact Set.union_compl_self B₁
  · show Disjoint B₁ B₁ᶜ
    exact disjoint_compl_right
  · intro q hq
    have h2 : q * τ.1 * q⁻¹ = τ.1 := Subtype.ext_iff.mp (hτ ⟨q, hq⟩)
    have hcomm : q * τ.1 = τ.1 * q := by
      calc q * τ.1 = q * τ.1 * q⁻¹ * q := by group
        _ = τ.1 * q := by rw [h2]
    have hqB₁ : q '' B₁ = B₁ ∨ q '' B₁ = B₂ := by
      have hqB₁eq : q '' B₁ = ({q x₀, τ.1 (q x₀)} : Set X) := by
        show q '' ({x₀, τ.1 x₀} : Set X) = {q x₀, τ.1 (q x₀)}
        rw [Set.image_pair]
        congr 1
        have := congrArg (fun f : Equiv.Perm X => f x₀) hcomm
        simpa [Equiv.Perm.mul_apply] using this
      rw [hqB₁eq]
      by_cases hx : q x₀ ∈ B₁
      · left
        have hsub : ({q x₀, τ.1 (q x₀)} : Set X) ⊆ B₁ := by
          intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl | hz
          · exact hx
          · rw [Set.mem_singleton_iff] at hz
            rw [hz, ← hB₁inv]
            exact ⟨q x₀, hx, rfl⟩
        have hsc : ({q x₀, τ.1 (q x₀)} : Set X).ncard = 2 :=
          Set.ncard_pair (Ne.symm (hτfix (q x₀)))
        exact Set.eq_of_subset_of_ncard_le hsub (by rw [hB₁card, hsc])
      · right
        have hx₂ : q x₀ ∈ B₂ := by
          have : q x₀ ∈ B₁ ∪ B₂ := by
            show q x₀ ∈ B₁ ∪ B₁ᶜ
            rw [Set.union_compl_self]; exact Set.mem_univ _
          rcases (Set.mem_union _ _ _).mp this with h | h
          · exact absurd h hx
          · exact h
        have hsub : ({q x₀, τ.1 (q x₀)} : Set X) ⊆ B₂ := by
          intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl | hz
          · exact hx₂
          · rw [Set.mem_singleton_iff] at hz
            rw [hz, ← hB₂inv]
            exact ⟨q x₀, hx₂, rfl⟩
        have hsc : ({q x₀, τ.1 (q x₀)} : Set X).ncard = 2 :=
          Set.ncard_pair (Ne.symm (hτfix (q x₀)))
        exact Set.eq_of_subset_of_ncard_le hsub (by rw [hB₂card, hsc])
    rcases hqB₁ with h | h
    · left
      refine ⟨h, ?_⟩
      show q '' B₁ᶜ = B₁ᶜ
      rw [Set.image_compl_eq q.bijective, h]
    · right
      refine ⟨h, ?_⟩
      show q '' B₁ᶜ = B₁
      rw [Set.image_compl_eq q.bijective, h]
      show B₂ᶜ = B₁
      rw [show B₂ = B₁ᶜ from rfl, compl_compl]

theorem s16c167_exists_fixed_pairing {X : Type*} [Finite X] (hX : Nat.card X = 4)
    (Q : Subgroup (Equiv.Perm X)) (hQ : IsPGroup 2 Q) :
    ∃ B₁ B₂ : Set X, B₁ ∪ B₂ = Set.univ ∧ Disjoint B₁ B₂ ∧ B₁.ncard = 2 ∧ B₂.ncard = 2 ∧
      ∀ q ∈ Q, (q '' B₁ = B₁ ∧ q '' B₂ = B₂) ∨ (q '' B₁ = B₂ ∧ q '' B₂ = B₁) := by
  have hcard : Nat.card (pairType X) = 3 := pairType_ncard hX
  have hndvd : ¬ 2 ∣ Nat.card (pairType X) := by rw [hcard]; decide
  obtain ⟨τ, hτ⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card (pairType X) hndvd
  exact pairType_extract hX Q τ (fun q => MulAction.mem_fixedPoints.mp hτ q)

private lemma map_biSup_image {W : Type} [CommGroup W] {ι : Type*} (φ : MulAut W)
    (f : ι → Subgroup W) (σ : ι → ι) (hσ : ∀ i, (f i).map φ.toMonoidHom = f (σ i))
    (B : Set ι) :
    (⨆ i ∈ B, f i).map φ.toMonoidHom = ⨆ i ∈ σ '' B, f i := by
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_iSup, hσ]
  exact (iSup_image (f := σ) (g := f) (t := B)).symm

theorem s16c167_pairing_core {W : Type} [CommGroup W] [Finite W] {Mb P : Subgroup (MulAut W)}
    {m : ℕ} (hsym : SymSumOfConj Mb (⊤ : Subgroup W) 3 m) (hPM : P ≤ Mb) (hP : IsPGroup 2 P) :
    ∃ Δ : Set (Subgroup W), Δ.ncard = 2 ∧ sSupIndep Δ ∧ sSup Δ = ⊤ ∧
      (∀ I ∈ Δ, rk ↥I = 2 * m) ∧ (∀ φ ∈ P, ∀ I ∈ Δ, I.map φ.toMonoidHom ∈ Δ) ∧
      PairsOfConj Mb m Δ := by
  classical
  obtain ⟨Z, hZrk, hind, hsup, hXcard, hS4⟩ := hsym
  have hX4 : Nat.card ↥(conjSubs Mb Z) = 4 := by
    rw [Nat.card_coe_set_eq, hXcard]
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) (fun f g h => MulEquiv.ext (congrFun h))
  haveI hfin : Finite ↥(conjSubs Mb Z) :=
    Finite.of_surjective
      (fun g : ↥Mb => (⟨Z.map (g : MulAut W).toMonoidHom,
        ⟨(g : MulAut W), g.2, rfl⟩⟩ : ↥(conjSubs Mb Z)))
      (by
        rintro ⟨Y, hY⟩
        obtain ⟨g, hg, rfl⟩ := hY
        exact ⟨⟨g, hg⟩, rfl⟩)
  have hmem : ∀ (p : ↥P) (Y : ↥(conjSubs Mb Z)),
      (Y : Subgroup W).map (p : MulAut W).toMonoidHom ∈ conjSubs Mb Z := by
    intro p Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    refine ⟨(p : MulAut W) * g, Mb.mul_mem (hPM p.2) hg, ?_⟩
    rw [hgY, Subgroup.map_map]
    rfl
  letI : MulAction ↥P ↥(conjSubs Mb Z) :=
    { smul := fun p Y => ⟨(Y : Subgroup W).map (p : MulAut W).toMonoidHom, hmem p Y⟩
      one_smul := by
        intro Y
        apply Subtype.ext
        show (Y : Subgroup W).map (MonoidHom.id W) = (Y : Subgroup W)
        rw [Subgroup.map_id]
      mul_smul := by
        intro p q Y
        apply Subtype.ext
        show (Y : Subgroup W).map (((p * q : ↥P) : MulAut W)).toMonoidHom
            = ((Y : Subgroup W).map (q : MulAut W).toMonoidHom).map (p : MulAut W).toMonoidHom
        rw [Subgroup.map_map]
        rfl }
  let ρ : ↥P →* Equiv.Perm ↥(conjSubs Mb Z) := MulAction.toPermHom ↥P ↥(conjSubs Mb Z)
  let Q : Subgroup (Equiv.Perm ↥(conjSubs Mb Z)) := ρ.range
  have hQ : IsPGroup 2 Q :=
    hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨B₁, B₂, hBunion, hBdisj, hB1card, hB2card, hBfix⟩ :=
    s16c167_exists_fixed_pairing hX4 Q hQ
  have hind' : iSupIndep (fun Y : ↥(conjSubs Mb Z) => (Y : Subgroup W)) :=
    (sSupIndep_iff (conjSubs Mb Z)).1 hind
  obtain ⟨Y₁, Y₂, hYne, hB₁eq⟩ := Set.ncard_eq_two.1 hB1card
  obtain ⟨Y₃, Y₄, hYne₃, hB₂eq⟩ := Set.ncard_eq_two.1 hB2card
  let G : ↥(conjSubs Mb Z) → Subgroup W := fun Y => (Y : Subgroup W)
  let I : Set ↥(conjSubs Mb Z) → Subgroup W := fun B => ⨆ Y ∈ B, G Y
  let Δ : Set (Subgroup W) := {I B₁, I B₂}
  have hmemΔ : ∀ J, J ∈ Δ ↔ J = I B₁ ∨ J = I B₂ := by
    intro J; simp [Δ, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
  have hIB₁ : I B₁ = G Y₁ ⊔ G Y₂ := by
    show (⨆ Y ∈ B₁, G Y) = G Y₁ ⊔ G Y₂
    rw [hB₁eq, iSup_pair]
  have hIB₂ : I B₂ = G Y₃ ⊔ G Y₄ := by
    show (⨆ Y ∈ B₂, G Y) = G Y₃ ⊔ G Y₄
    rw [hB₂eq, iSup_pair]
  have hpair12 : Disjoint (G Y₁) (G Y₂) :=
    hind.pairwiseDisjoint Y₁.2 Y₂.2 (fun h => hYne (Subtype.ext h))
  have hpair34 : Disjoint (G Y₃) (G Y₄) :=
    hind.pairwiseDisjoint Y₃.2 Y₄.2 (fun h => hYne₃ (Subtype.ext h))
  have hII : Disjoint (I B₁) (I B₂) := by
    have hfin₁ : B₁.Finite := by
      rw [hB₁eq]
      exact (Set.finite_singleton Y₂).insert Y₁
    exact hind'.disjoint_biSup_biSup' hBdisj hfin₁
  have hGYne : ∀ Y : ↥(conjSubs Mb Z), G Y ≠ ⊥ := by
    have hZne : Z ≠ ⊥ := by
      intro hZ
      have hsub : conjSubs Mb Z ⊆ {⊥} := by
        rintro X ⟨g, hg, rfl⟩
        simp [hZ]
      have hle : (conjSubs Mb Z).ncard ≤ 1 := by
        calc (conjSubs Mb Z).ncard ≤ ({⊥} : Set (Subgroup W)).ncard :=
              Set.ncard_le_ncard hsub
          _ = 1 := by simp
      rw [hXcard] at hle
      omega
    intro Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    intro hbot
    change (Y : Subgroup W) = ⊥ at hbot
    rw [hgY] at hbot
    exact hZne ((Subgroup.map_eq_bot_iff_of_injective Z (f := g.toMonoidHom) g.injective).mp hbot)
  have hI₁ne : I B₁ ≠ ⊥ := by
    rw [hIB₁]
    exact fun h => hGYne Y₁ (sup_eq_bot_iff.mp h).1
  have hIne : I B₁ ≠ I B₂ := by
    intro h
    apply hI₁ne
    have h' := hII
    rw [← h, disjoint_self] at h'
    exact h'
  have hΔcard : Δ.ncard = 2 := by
    show ({I B₁, I B₂} : Set (Subgroup W)).ncard = 2
    exact Set.ncard_pair hIne
  have hΔind : sSupIndep Δ := by
    show sSupIndep ({I B₁, I B₂} : Set (Subgroup W))
    exact (sSupIndep_pair hIne).2 hII
  have htop : (⨆ Y : ↥(conjSubs Mb Z), G Y) = ⊤ := by
    rw [show (⨆ Y : ↥(conjSubs Mb Z), G Y) = sSup (conjSubs Mb Z) from
      (sSup_eq_iSup' (conjSubs Mb Z)).symm]
    exact hsup
  have hΔsup : sSup Δ = ⊤ := by
    show sSup ({I B₁, I B₂} : Set (Subgroup W)) = ⊤
    rw [sSup_pair]
    have h1 : I B₁ ⊔ I B₂ = ⨆ Y ∈ B₁ ∪ B₂, G Y := by
      show (⨆ Y ∈ B₁, G Y) ⊔ (⨆ Y ∈ B₂, G Y) = ⨆ Y ∈ B₁ ∪ B₂, G Y
      exact (iSup_union (f := G) (s := B₁) (t := B₂)).symm
    rw [h1, hBunion, iSup_univ]
    exact htop
  have hrkY : ∀ Y : ↥(conjSubs Mb Z), rk ↥(G Y) = m := by
    intro Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    change rk ↥(Y : Subgroup W) = m
    rw [hgY, CFSG.Quasithin.RonanH163.rk_map g Z, hZrk]
  have hrkI : ∀ J ∈ Δ, rk ↥J = 2 * m := by
    intro J hJ
    rw [hmemΔ] at hJ
    rcases hJ with rfl | rfl
    · rw [hIB₁,
        CFSG.Quasithin.A6Amt.rk_sup_of_inf_eq_bot
          (disjoint_iff.mp (show Disjoint (G Y₁) (G Y₂) from hpair12)),
        hrkY Y₁, hrkY Y₂]
      ring
    · rw [hIB₂,
        CFSG.Quasithin.A6Amt.rk_sup_of_inf_eq_bot
          (disjoint_iff.mp (show Disjoint (G Y₃) (G Y₄) from hpair34)),
        hrkY Y₃, hrkY Y₄]
      ring
  have hmapI : ∀ (φ : MulAut W) (hφ : φ ∈ P) (B : Set ↥(conjSubs Mb Z)),
      (I B).map φ.toMonoidHom = I ((ρ ⟨φ, hφ⟩) '' B) := by
    intro φ hφ B
    change (⨆ Y ∈ B, G Y).map φ.toMonoidHom = ⨆ Y ∈ (ρ ⟨φ, hφ⟩) '' B, G Y
    rw [map_biSup_image φ G (fun Y => (⟨φ, hφ⟩ : ↥P) • Y) (fun Y => rfl) B]
    rfl
  have hpairs : PairsOfConj Mb m Δ := by
    refine ⟨Z, hZrk, hind, hsup, hXcard, hS4, ?_⟩
    intro J hJ
    rw [hmemΔ] at hJ
    rcases hJ with rfl | rfl
    · exact ⟨(Y₁ : Subgroup W), Y₁.2, (Y₂ : Subgroup W), Y₂.2,
        fun h => hYne (Subtype.ext h), hIB₁⟩
    · exact ⟨(Y₃ : Subgroup W), Y₃.2, (Y₄ : Subgroup W), Y₄.2,
        fun h => hYne₃ (Subtype.ext h), hIB₂⟩
  refine ⟨Δ, hΔcard, hΔind, hΔsup, hrkI, ?_, hpairs⟩
  intro φ hφ J hJ
  rw [hmemΔ] at hJ
  have hfix := hBfix (ρ ⟨φ, hφ⟩) ⟨⟨φ, hφ⟩, rfl⟩
  rcases hJ with rfl | rfl
  · rw [hmapI φ hφ B₁]
    rcases hfix with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact (hmemΔ (I B₁)).2 (Or.inl rfl)
    · exact (hmemΔ (I B₂)).2 (Or.inr rfl)
  · rw [hmapI φ hφ B₂]
    rcases hfix with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact (hmemΔ (I B₂)).2 (Or.inr rfl)
    · exact (hmemΔ (I B₁)).2 (Or.inl rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
