module

public import CFSG.Quasithin.Background.G25Count
public import CFSG.Quasithin.Background.G25Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem card_eq_mul_relIndex_le {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥B = Nat.card ↥A * A.relIndex B := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact h1.symm

@[expose] def IsSumOfSL3ModulesVia {F : Type*} [Field F] (r : ℕ) (M Sx N : Subgroup G)
    (θ : ↥M →* SL(3, F)) (φ : ↥Sx →* Multiplicative (Fin r → Fin 3 → F)) : Prop :=
  Function.Surjective φ ∧ (∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ N) ∧
    ∀ (a : ↥M) (x y : ↥Sx), (y : G) = (a : G) * (x : G) * (a : G)⁻¹ →
      φ y = Multiplicative.ofAdd (fun l => θ a • Multiplicative.toAdd (φ x) l)

@[expose] def sThree (W : Subgroup G) (g h : G) : Subgroup G :=
  (W ⊓ rconj W g) ⊔ (W ⊓ rconj W h) ⊔ (rconj W g ⊓ rconj W h)

section Translate

variable {U S : Subgroup G} {g h : G}

theorem W_tripleU (hg : g ∈ Subgroup.normalizer (S : Set G))
    (hh : h ∈ Subgroup.normalizer (S : Set G)) :
    TripleGrp.W S (tripleU U g h) 0 = U ⊓ S ∧
      TripleGrp.W S (tripleU U g h) 1 = rconj (U ⊓ S) g ∧
      TripleGrp.W S (tripleU U g h) 2 = rconj (U ⊓ S) h := by
  refine ⟨?_, ?_, ?_⟩
  · show tripleU U g h 0 ⊓ S = _
    rw [tripleU_zero]
  · show tripleU U g h 1 ⊓ S = _
    rw [tripleU_one, rconj_inf_eq_of_normalizes hg]
  · show tripleU U g h 2 ⊓ S = _
    rw [tripleU_two, rconj_inf_eq_of_normalizes hh]

theorem S₃_tripleU (hg : g ∈ Subgroup.normalizer (S : Set G))
    (hh : h ∈ Subgroup.normalizer (S : Set G)) :
    TripleGrp.S₃ S (tripleU U g h) = sThree (U ⊓ S) g h := by
  obtain ⟨h0, h1, h2⟩ := W_tripleU (U := U) hg hh
  show (TripleGrp.W S (tripleU U g h) 0 ⊓ TripleGrp.W S (tripleU U g h) 1) ⊔
    (TripleGrp.W S (tripleU U g h) 0 ⊓ TripleGrp.W S (tripleU U g h) 2) ⊔
    (TripleGrp.W S (tripleU U g h) 1 ⊓ TripleGrp.W S (tripleU U g h) 2) = _
  rw [h0, h1, h2]
  rfl

theorem S₂_tripleU : TripleGrp.S₂ (tripleU U g h) = U ⊓ rconj U g ⊓ rconj U h := by
  show tripleU U g h 0 ⊓ tripleU U g h 1 ⊓ tripleU U g h 2 = _
  rw [tripleU_zero, tripleU_one, tripleU_two]

end Translate

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)
  {g h : G} (hg : g ∈ L) (hh : h ∈ L)

omit [Finite G] in
include St in
theorem card_V : Nat.card ↥V = Nat.card (GaloisField 2 n) ^ 3 := by
  have h1 : Nat.card ↥V = Nat.card (W3 (GaloisField 2 n)) := Nat.card_congr St.D.ψ.toEquiv
  have h2 : Nat.card (W3 (GaloisField 2 n)) = Nat.card (Fin 3 → GaloisField 2 n) :=
    Nat.card_congr Multiplicative.toAdd
  rw [h1, h2, Nat.card_fun]
  simp

omit [Finite G] in
theorem pvec_tripleConj_zero (hg : g ∈ L) (hh : h ∈ L) :
    St.pvec (tripleConj_mem hg hh 0) = vE (GaloisField 2 n) 0 := by
  have e : (⟨tripleConj g h 0, tripleConj_mem hg hh 0⟩ : ↥L) = 1 :=
    Subtype.ext (by simp [tripleConj])
  rw [pvec, e, inv_one, map_one, one_smul]

omit [Finite G] in
theorem pvec_tripleConj_one (hg : g ∈ L) (hh : h ∈ L) :
    St.pvec (tripleConj_mem hg hh 1) = St.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0 := by
  have e : (⟨tripleConj g h 1, tripleConj_mem hg hh 1⟩ : ↥L) = ⟨g, hg⟩ :=
    Subtype.ext (by simp [tripleConj])
  rw [pvec, e]

omit [Finite G] in
theorem pvec_tripleConj_two (hg : g ∈ L) (hh : h ∈ L) :
    St.pvec (tripleConj_mem hg hh 2) = St.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0 := by
  have e : (⟨tripleConj g h 2, tripleConj_mem hg hh 2⟩ : ↥L) = ⟨h, hh⟩ :=
    Subtype.ext (by simp [tripleConj])
  rw [pvec, e]

include St hg hh in
theorem G25_fam (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ∃ (r s : ℕ)
      (φ₇ : ↥(pCoreOf 2 (L ⊔ conjClosure V H)) →*
        Multiplicative (Fin r → Fin 3 → GaloisField 2 n))
      (φ₆ : ↥(TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h)) →*
        Multiplicative (Fin s → Fin 3 → GaloisField 2 n)),
      IsSumOfSL3ModulesVia r (L ⊔ conjClosure V H) (pCoreOf 2 (L ⊔ conjClosure V H))
        (TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h))
        St.Phi φ₇ ∧
      (∀ (k : Fin 3) (x : ↥(pCoreOf 2 (L ⊔ conjClosure V H))),
        (x : G) ∈ TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) k ⊔
            TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) ↔
          ∀ l : Fin r, ∃ c : GaloisField 2 n, Multiplicative.toAdd (φ₇ x) l =
            c • St.pvec (tripleConj_mem hg hh k)) ∧
      IsSumOfSL3ModulesVia s (L ⊔ conjClosure V H)
        (TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h))
        (TripleGrp.S₂ (tripleU (conjClosure V H) g h))
        ((dualHom (GaloisField 2 n) 3).comp St.Phi) φ₆ ∧
      (∀ (i j : Fin 3), i ≠ j → ∀ x : ↥(TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H))
          (tripleU (conjClosure V H) g h)),
        (x : G) ∈ TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) i ⊓
            TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) j ↔
          ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ St.pvec (tripleConj_mem hg hh i) = 0 ∧
            Multiplicative.toAdd (φ₆ x) l ⬝ᵥ St.pvec (tripleConj_mem hg hh j) = 0) ∧
      Nat.card ↥(conjClosure V H) = 2 ^ (n * (2 * s + r + 5)) *
        V.relIndex (TripleGrp.S₂ (tripleU (conjClosure V H) g h)) := by
  obtain ⟨Q, lam, hT⟩ := St.tripleL3 hg hh hV
  have : NeZero n := ⟨St.hyp.n_pos.ne'⟩
  obtain ⟨r, φ₇, hs₇, hk₇, he₇, hc₇, -⟩ := hT.exists_seven_core
  obtain ⟨s, φ₆, hs₆, hk₆, he₆, hc₆, -⟩ := hT.exists_six_core
  have hcard := hT.card_Uk_zero_formula φ₇ hs₇ hk₇ hc₇ φ₆ hs₆ hk₆ hc₆
  obtain ⟨φ₇', h1, h2, h3, h4⟩ := hT.seven_untwist φ₇ hs₇ hk₇ he₇ hc₇
  obtain ⟨φ₆', h1', h2', h3', h4'⟩ := hT.six_untwist φ₆ hs₆ hk₆ he₆ hc₆
  refine ⟨r, s, φ₇', φ₆', ⟨h1, h2, h3⟩, h4, ⟨h1', h2', h3'⟩, h4', ?_⟩
  have hVS₂ : V ≤ TripleGrp.S₂ (tripleU (conjClosure V H) g h) := by
    refine le_inf (le_inf ?_ ?_) ?_
    · rw [tripleU_zero]
      exact le_conjClosure V H
    · exact St.V_le_rconj_U hg
    · exact St.V_le_rconj_U hh
  have hS₂ := card_eq_mul_relIndex_le hVS₂
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n NeZero.out
  rw [tripleU_zero] at hcard
  rw [hcard, hS₂, St.card_V, hF]
  ring

end L3Setting

namespace AlmostSpecialL3Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL3Hyp n V V₁ L T H)

include hyp

theorem G25_four_inv {U I S W : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    I ≤ Subgroup.normalizer ((sThree W g h : Subgroup G) : Set G) := by
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
  rw [← S₃_tripleU (hnorm g hg) (hnorm h hh), hI']
  exact St.G25_four_inv hg hh hV

theorem G25_six_seven_eight {U I S W : Subgroup G} (hU : U = conjClosure V H) {g h : G}
    (hg : g ∈ L) (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S)
    (D : NatData3 n L (pCoreOf 2 (L ⊔ T)) V V₁) :
    ∃ (r s : ℕ) (φ₇ : ↥S →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n))
      (φ₆ : ↥(sThree W g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)),
      IsSumOfSL3ModulesVia r L S (sThree W g h) D.θ φ₇ ∧
      (∀ x : ↥S, (x : G) ∈ W ⊔ sThree W g h ↔
        ∀ l : Fin r, ∃ c : GaloisField 2 n,
          Multiplicative.toAdd (φ₇ x) l = c • vE (GaloisField 2 n) 0) ∧
      (∀ x : ↥S, (x : G) ∈ rconj W g ⊔ sThree W g h ↔
        ∀ l : Fin r, ∃ c : GaloisField 2 n,
          Multiplicative.toAdd (φ₇ x) l = c • (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0)) ∧
      (∀ x : ↥S, (x : G) ∈ rconj W h ⊔ sThree W g h ↔
        ∀ l : Fin r, ∃ c : GaloisField 2 n,
          Multiplicative.toAdd (φ₇ x) l = c • (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0)) ∧
      IsSumOfSL3ModulesVia s L (sThree W g h) (U ⊓ rconj U g ⊓ rconj U h)
        ((dualHom (GaloisField 2 n) 3).comp D.θ) φ₆ ∧
      (∀ x : ↥(sThree W g h), (x : G) ∈ W ⊓ rconj W g ↔
        ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
          Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ∧
      (∀ x : ↥(sThree W g h), (x : G) ∈ W ⊓ rconj W h ↔
        ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
          Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ∧
      (∀ x : ↥(sThree W g h), (x : G) ∈ rconj W g ⊓ rconj W h ↔
        ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0 ∧
          Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ∧
      Nat.card ↥U = 2 ^ (n * (2 * s + r + 5)) * V.relIndex (U ⊓ rconj U g ⊓ rconj U h) := by
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
  have hSg := hnorm g hg
  have hSh := hnorm h hh
  obtain ⟨hW0, hW1, hW2⟩ := W_tripleU (U := conjClosure V H) hSg hSh
  have hS₃ := S₃_tripleU (U := conjClosure V H) hSg hSh
  have hS₂ := S₂_tripleU (U := conjClosure V H) (g := g) (h := h)
  have hΦ : ∀ a : ↥L, St.Phi ⟨(a : G), (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ = D.θ a :=
    fun a => St.Phi_of_L a
  obtain ⟨r, s, φ₇, φ₆, ⟨hs₇, hk₇, he₇⟩, hc₇, ⟨hs₆, hk₆, he₆⟩, hc₆, hcard⟩ :=
    St.G25_fam hg hh hV
  rw [← hS₃]
  rw [hS₂] at hk₆ hcard
  refine ⟨r, s, φ₇, φ₆, ⟨hs₇, hk₇, fun a x y hy => ?_⟩, fun x => ?_, fun x => ?_, fun x => ?_,
    ⟨hs₆, hk₆, fun a x y hy => ?_⟩, fun x => ?_, fun x => ?_, fun x => ?_, hcard⟩
  · rw [← hΦ a]
    exact he₇ ⟨(a : G), (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ x y hy
  · have := hc₇ 0 x
    rwa [hW0, St.pvec_tripleConj_zero hg hh] at this
  · have := hc₇ 1 x
    rwa [hW1, St.pvec_tripleConj_one hg hh] at this
  · have := hc₇ 2 x
    rwa [hW2, St.pvec_tripleConj_two hg hh] at this
  · have h6 := he₆ ⟨(a : G), (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ x y hy
    simp only [MonoidHom.comp_apply, hΦ a] at h6
    exact h6
  · have := hc₆ 0 1 (by decide) x
    rwa [hW0, hW1, St.pvec_tripleConj_zero hg hh, St.pvec_tripleConj_one hg hh] at this
  · have := hc₆ 0 2 (by decide) x
    rwa [hW0, hW2, St.pvec_tripleConj_zero hg hh, St.pvec_tripleConj_two hg hh] at this
  · have := hc₆ 1 2 (by decide) x
    rwa [hW1, hW2, St.pvec_tripleConj_one hg hh, St.pvec_tripleConj_two hg hh] at this

end AlmostSpecialL3Hyp

end CFSG.Quasithin
