module

public import CFSG.Quasithin.Background.G25Eight

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G] {F : Type*} [Field F]

theorem sup_inf_le_of_coord {Sx N : Subgroup G} {r : ℕ}
    (φ : ↥Sx →* Multiplicative (Fin r → Fin 3 → F))
    (hk : ∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ N) (A : Fin 3 → Subgroup G) (hAS : ∀ k, A k ≤ Sx)
    (hc : ∀ (k : Fin 3) (x : ↥Sx), (x : G) ∈ A k ↔
      ∀ (l : Fin r) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0)
    {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) : (A i ⊔ A j) ⊓ A k ≤ N := by
  let C : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ Sx, ∀ l : Fin r, Multiplicative.toAdd (φ ⟨x, hx⟩) l k = 0}
      one_mem' := ⟨Sx.one_mem, fun l => by
        have : φ ⟨1, Sx.one_mem⟩ = 1 := map_one φ
        rw [this]
        simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Sx.mul_mem hx hy, fun l => ?_⟩
        have : φ ⟨x * y, Sx.mul_mem hx hy⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ :=
          map_mul φ ⟨x, hx⟩ ⟨y, hy⟩
        rw [this]
        simp [hx' l, hy' l]
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨Sx.inv_mem hx, fun l => ?_⟩
        have : φ ⟨x⁻¹, Sx.inv_mem hx⟩ = (φ ⟨x, hx⟩)⁻¹ := map_inv φ ⟨x, hx⟩
        rw [this]
        simp [hx' l] }
  have hAC : ∀ m, m ≠ k → A m ≤ C := fun m hm x hx =>
    ⟨hAS m hx, fun l => (hc m ⟨x, hAS m hx⟩).1 hx l k (Ne.symm hm)⟩
  intro x hx
  obtain ⟨hxS, hx0⟩ := sup_le (hAC i hik) (hAC j hjk) hx.1
  refine (hk ⟨x, hxS⟩).1 ?_
  apply Multiplicative.toAdd.injective
  funext l j
  by_cases hj : j = k
  · subst hj
    simpa using hx0 l
  · simpa using (hc k ⟨x, hxS⟩).1 hx.2 l j hj

namespace TripleL3

variable [CharP F 2] {I S : Subgroup G} {Uk : Fin 3 → Subgroup G} {Φ : ↥I →* SL(3, F)}
  {p : Fin 3 → Fin 3 → F} {Q : SL(3, F)} {lam : Fin 3 → F}
  (hT : TripleL3 I S Uk Φ p Q lam)

include hT

theorem direct_seven [Finite G] [Finite F] {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) :
    ((TripleGrp.W S Uk i ⊔ TripleGrp.S₃ S Uk) ⊔ (TripleGrp.W S Uk j ⊔ TripleGrp.S₃ S Uk)) ⊓
      (TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk) = TripleGrp.S₃ S Uk := by
  obtain ⟨r, φ, hs, hk, he, hc, -⟩ := hT.exists_seven_core
  refine le_antisymm (sup_inf_le_of_coord φ hk
    (fun m => TripleGrp.W S Uk m ⊔ TripleGrp.S₃ S Uk)
    (fun m => sup_le inf_le_right TripleGrp.S₃_le_S) hc hik hjk) ?_
  exact le_inf (le_sup_of_le_left le_sup_right) le_sup_right

theorem direct_six [Finite G] [Finite F] {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) :
    (pairFam S Uk i ⊔ pairFam S Uk j) ⊓ pairFam S Uk k = TripleGrp.S₂ Uk := by
  obtain ⟨s, φ, hs, hk, he, hc, -⟩ := hT.exists_six_core
  refine le_antisymm (sup_inf_le_of_coord φ hk (pairFam S Uk) (pairFam_le_S₃ S Uk) hc hik hjk) ?_
  have hN : ∀ m, TripleGrp.S₂ Uk ≤ pairFam S Uk m := fun m z hz =>
    (mem_pairFam_iff S Uk m z).2 fun m' _ => hT.tg.S₂_le_W m' hz
  exact le_inf (le_sup_of_le_left (hN i)) (hN k)

end TripleL3

namespace AlmostSpecialL3Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL3Hyp n V V₁ L T H)

include hyp

theorem G25_direct {U I S W : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    S = W ⊔ rconj W g ⊔ rconj W h ∧
      (W ⊔ sThree W g h) ⊓ (rconj W g ⊔ sThree W g h) = sThree W g h ∧
      (W ⊔ sThree W g h) ⊓ (rconj W h ⊔ sThree W g h) = sThree W g h ∧
      (rconj W g ⊔ sThree W g h) ⊓ (rconj W h ⊔ sThree W g h) = sThree W g h ∧
      ((W ⊔ sThree W g h) ⊔ (rconj W g ⊔ sThree W g h)) ⊓ (rconj W h ⊔ sThree W g h) =
        sThree W g h ∧
      (W ⊓ rconj W g) ⊓ (W ⊓ rconj W h) = U ⊓ rconj U g ⊓ rconj U h ∧
      (W ⊓ rconj W g) ⊓ (rconj W g ⊓ rconj W h) = U ⊓ rconj U g ⊓ rconj U h ∧
      (W ⊓ rconj W h) ⊓ (rconj W g ⊓ rconj W h) = U ⊓ rconj U g ⊓ rconj U h ∧
      ((W ⊓ rconj W g) ⊔ (W ⊓ rconj W h)) ⊓ (rconj W g ⊓ rconj W h) =
        U ⊓ rconj U g ⊓ rconj U h := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n V V₁ L T H := ⟨hyp, D⟩
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (St.G25_two_aux hg hh hV)
  have hS' : S = pCoreOf 2 (L ⊔ conjClosure V H) := by rw [hS, hI']
  subst hS'
  subst hW
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := St.sxFacts
  have hnorm : ∀ a ∈ L, a ∈ Subgroup.normalizer
      ((pCoreOf 2 (L ⊔ conjClosure V H) : Subgroup G) : Set G) := fun a ha =>
    (le_normalizer_of_conj_mem (fun x hx y hy => hINorm x hx y hy))
      ((le_sup_left : L ≤ L ⊔ conjClosure V H) ha)
  obtain ⟨hW0, hW1, hW2⟩ := W_tripleU (U := conjClosure V H) (hnorm g hg) (hnorm h hh)
  have hS₃ := S₃_tripleU (U := conjClosure V H) (hnorm g hg) (hnorm h hh)
  have hS₂ := S₂_tripleU (U := conjClosure V H) (g := g) (h := h)
  obtain ⟨Q, lam, hT⟩ := St.tripleL3 hg hh hV
  have hSeq : pCoreOf 2 (L ⊔ conjClosure V H) =
      (conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H)) ⊔
        rconj (conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H)) g ⊔
        rconj (conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H)) h := by
    have h1 := hT.tg.S_eq
    rw [tripleU_zero] at h1
    exact h1.trans (by rw [← hW1, ← hW2])
  have hP0 := pairFam_eq (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h)
    (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
  have hP1 := pairFam_eq (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h)
    (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
  have hP2 := pairFam_eq (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h)
    (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
  rw [hW1, hW2] at hP0
  rw [hW0, hW2] at hP1
  rw [hW0, hW1] at hP2
  have d01 := hT.direct_seven (i := 0) (j := 0) (k := 1) (by decide) (by decide)
  have d02 := hT.direct_seven (i := 0) (j := 0) (k := 2) (by decide) (by decide)
  have d12 := hT.direct_seven (i := 1) (j := 1) (k := 2) (by decide) (by decide)
  have d012 := hT.direct_seven (i := 0) (j := 1) (k := 2) (by decide) (by decide)
  have e21 := hT.direct_six (i := 2) (j := 2) (k := 1) (by decide) (by decide)
  have e20 := hT.direct_six (i := 2) (j := 2) (k := 0) (by decide) (by decide)
  have e10 := hT.direct_six (i := 1) (j := 1) (k := 0) (by decide) (by decide)
  have e210 := hT.direct_six (i := 2) (j := 1) (k := 0) (by decide) (by decide)
  rw [sup_idem] at d01 d02 d12 e21 e20 e10
  rw [hW0, hW1, hS₃] at d01
  rw [hW0, hW2, hS₃] at d02
  rw [hW1, hW2, hS₃] at d12
  rw [hW0, hW1, hW2, hS₃] at d012
  rw [hP2, hP1, hS₂] at e21
  rw [hP2, hP0, hS₂] at e20
  rw [hP1, hP0, hS₂] at e10
  rw [hP2, hP1, hP0, hS₂] at e210
  exact ⟨hSeq, d01, d02, d12, d012, e21, e20, e10, e210⟩

end AlmostSpecialL3Hyp

end CFSG.Quasithin
