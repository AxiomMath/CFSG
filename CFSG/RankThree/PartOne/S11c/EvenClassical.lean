module

public import CFSG.RankThree.PartOne.S11c.CoverBridge
public import CFSG.RankThree.PartOne.S11c.ClassicalFiveFixed
public import CFSG.RankThree.PartOne.KF.ClsSpWit
public import CFSG.RankThree.CentralCover.HigherClassicalFourGroupWitness

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def rotHom : Multiplicative (Fin 6 → ZMod 3) →* Equiv.Perm (Fin 6 × ZMod 3) where
  toFun a := Equiv.prodShear (Equiv.refl _) fun j => Equiv.addRight (Multiplicative.toAdd a j)
  map_one' := by
    ext ⟨j, t⟩ <;> simp
  map_mul' a b := by
    ext ⟨j, t⟩
    · simp
    · simp
      ring

theorem rotHom_injective : Function.Injective rotHom := by
  intro a b h
  have : ∀ j, Multiplicative.toAdd a j = Multiplicative.toAdd b j := by
    intro j
    have := congrArg (fun σ : Equiv.Perm (Fin 6 × ZMod 3) => (σ (j, 0)).2) h
    simpa [rotHom] using this
  exact Multiplicative.toAdd.injective (funext this)

theorem exists_perm_rank_six_witness {k : Type} [Field k] {n : ℕ} (hn : 20 ≤ n)
    (E : Subgroup (GL (Fin n) k))
    (hE : ∀ σ : Equiv.Perm (Fin n), (permGL σ : GL (Fin n) k) ∈ E) :
    ∃ (θ : Multiplicative (Fin 6 → ZMod 3) →* StatedProj E) (s : StatedProj E),
      Function.Injective θ ∧ s ≠ 1 ∧ s ^ 2 = 1 ∧ ∀ a, s * θ a = θ a * s := by
  obtain ⟨emb⟩ : Nonempty (((Fin 6 × ZMod 3) ⊕ Fin 2) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simp [ZMod.card]; omega)
  let Φ : Equiv.Perm ((Fin 6 × ZMod 3) ⊕ Fin 2) →* Equiv.Perm (Fin n) :=
    Equiv.Perm.viaEmbeddingHom emb
  have hΦ : Function.Injective Φ := Equiv.Perm.viaEmbeddingHom_injective emb
  let S := Equiv.Perm.sumCongrHom (Fin 6 × ZMod 3) (Fin 2)
  let Θ : Multiplicative (Fin 6 → ZMod 3) →* Equiv.Perm (Fin n) :=
    Φ.comp (S.comp ((MonoidHom.inl _ (Equiv.Perm (Fin 2))).comp rotHom))
  have hΘ : Function.Injective Θ := by
    intro a b h
    have h2 := Equiv.Perm.sumCongrHom_injective (hΦ h)
    exact rotHom_injective (congrArg Prod.fst h2)
  let σs : Equiv.Perm (Fin n) := Φ (S (1, Equiv.swap (0 : Fin 2) 1))
  let q : E →* StatedProj E := QuotientGroup.mk' _
  let Θ' : Multiplicative (Fin 6 → ZMod 3) →* E :=
    MonoidHom.codRestrict ((permGL : Equiv.Perm (Fin n) →* GL (Fin n) k).comp Θ) E
      fun a => hE _
  have hscal : ∀ g : E, q g = 1 → (g : GL (Fin n) k) ∈ StatedScalars (Fin n) k := fun g hg => by
    have : g ∈ (StatedScalars (Fin n) k).subgroupOf E := (QuotientGroup.eq_one_iff _).1 hg
    exact this
  refine ⟨q.comp Θ', q ⟨permGL σs, hE _⟩, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    have hΘ1 : Θ a ≠ 1 := fun h => hne (hΘ (h.trans (map_one Θ).symm))
    exact permGL_not_mem_statedScalars (K := k) hΘ1 (hscal _ ha)
  · intro h
    have hσ : σs ≠ 1 := by
      intro h1
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (emb (Sum.inr 0))) h1
      simp only [σs, Φ, S, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply,
        Equiv.Perm.sumCongrHom_apply, Equiv.Perm.coe_one, id_eq] at this
      simp at this
    exact permGL_not_mem_statedScalars (K := k) hσ (hscal _ h)
  · rw [← map_pow]
    have : (⟨permGL σs, hE _⟩ : E) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← map_pow]
      have : σs ^ 2 = 1 := by
        rw [show σs = Φ (S (1, Equiv.swap (0 : Fin 2) 1)) from rfl, ← map_pow, ← map_pow,
          Prod.pow_mk, one_pow, sq, Equiv.swap_mul_self]
        rw [show ((1 : Equiv.Perm (Fin 6 × ZMod 3)), (1 : Equiv.Perm (Fin 2))) = 1 from rfl,
          map_one, map_one]
      rw [this, map_one]
      rfl
    rw [this, map_one]
  · intro a
    have hc : σs * Θ a = Θ a * σs := by
      change Φ (S (1, Equiv.swap (0 : Fin 2) 1)) * Φ (S (rotHom a, 1)) =
        Φ (S (rotHom a, 1)) * Φ (S (1, Equiv.swap (0 : Fin 2) 1))
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 2
    show q ⟨permGL σs, hE _⟩ * q (Θ' a) = q (Θ' a) * q ⟨permGL σs, hE _⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change permGL σs * permGL (Θ a) = permGL (Θ a) * permGL σs
    rw [← map_mul, ← map_mul, hc]

theorem permGL_mem_statedSL_even {k : Type} [Field k] [CharP k 2] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : (permGL σ : GL (Fin n) k) ∈ StatedSL n k := by
  refine Subgroup.subset_closure ?_
  show (((permGL σ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).det = 1
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> simp [h, CharTwo.neg_eq]

theorem exists_cover_of_model {H : Type} [Group H] {X : Subgroup H} {T : Type} [Group T]
    (e : (↥X ⧸ Subgroup.center ↥X) ≃* T) :
    ∃ η : X →* T, Function.Surjective η ∧ η.ker ≤ Subgroup.center X := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact hx

theorem evenTypeA_rank_four {H : Type} [Group H] [Finite H] (X : Subgroup H) {τ : StatedLieTag}
    (hτ : τ = .PSL ∨ τ = .PSU) {n f : ℕ}
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) τ n 2 f) (hn : 20 ≤ n) :
    4 ≤ localRank 3 H := by
  have hf : 1 ≤ f := hmod.1.2.1
  rcases hτ with rfl | rfl
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    have : CharP k 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hf hk
    obtain ⟨η, hη, hker⟩ := exists_cover_of_model e
    obtain ⟨θ, s, hθ, hs1, hs2, hsθ⟩ := exists_perm_rank_six_witness hn (StatedSL n k)
      fun σ => permGL_mem_statedSL_even σ
    exact four_le_localRank_of_rank_six_witness η hη hker θ hθ hs1 hs2 hsθ
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    have : CharP k 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (k := f * 2) (by omega) (by rw [hk, ← pow_mul])
    obtain ⟨η, hη, hker⟩ := exists_cover_of_model e
    obtain ⟨θ, s, hθ, hs1, hs2, hsθ⟩ := exists_perm_rank_six_witness hn
      (StatedSU n (2 ^ f) k) fun σ =>
        CFSG.RankThree.CentralCover.permGL_mem_statedSU (pow_ne_zero f (by norm_num)) σ
    exact four_le_localRank_of_rank_six_witness η hη hker θ hθ hs1 hs2 hsθ

theorem evenSp_rank_four {H : Type} [Group H] [Finite H] (X : Subgroup H) {n f : ℕ}
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp n 2 f) (hn : 20 ≤ 2 * n) :
    4 ≤ localRank 3 H := by
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hk
  obtain ⟨η, hη, hker⟩ := exists_cover_of_model e
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h6 : 6 ≤ localRank 3 (StatedProj (StatedSp (m + 1) k)) :=
    (by omega : 6 ≤ m).trans
      (CFSG.RankThree.PartOne.KFU.le_localRank_three_statedSp_blocks (K := k) (by omega))
  exact four_le_localRank_of_cover η hη hker Nat.prime_three (by norm_num) h6

@[expose] def EvenOrthogonalHighDimRankFour : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (X : Subgroup H) (τ : StatedLieTag) (n f : ℕ),
    (τ = .POmegaPlus ∨ τ = .POmegaMinus) →
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) τ n 2 f → 10 ≤ n → 4 ≤ localRank 3 H

theorem evenClassicalHighDimRankFour_of_orthogonal (hOrth : EvenOrthogonalHighDimRankFour) :
    EvenClassicalHighDimRankFour := by
  intro H _ _ X τ n f hmod h20
  have hτ : τ = .PSL ∨ τ = .PSU ∨ τ = .PSp ∨ τ = .POmegaOdd ∨ τ = .POmegaPlus ∨
      τ = .POmegaMinus := by
    have h2 := hmod.2
    cases τ <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      | exact h2.elim
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact evenTypeA_rank_four X (Or.inl rfl) hmod h20
  · exact evenTypeA_rank_four X (Or.inr rfl) hmod h20
  · exact evenSp_rank_four X hmod (by simpa [naturalDim] using h20)
  · exact absurd rfl hmod.1.2.2.2
  · exact hOrth H X _ n f (Or.inl rfl) hmod (by simp only [naturalDim] at h20; omega)
  · exact hOrth H X _ n f (Or.inr rfl) hmod (by simp only [naturalDim] at h20; omega)

end CFSG.RankThree.PartOne.HNRed
