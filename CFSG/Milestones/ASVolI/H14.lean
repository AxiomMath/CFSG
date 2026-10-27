module

public import CFSG.Quasithin.AppendixH.H14.H141Main
public import CFSG.Quasithin.AppendixH.H14.H142Main
public import CFSG.Quasithin.AppendixH.H14.H142Uniq
public import CFSG.Quasithin.AppendixH.H14.MathieuModuleRanks
public import CFSG.Quasithin.Background.RonanH143Main

public section

open scoped Pointwise Matrix

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code

@[expose] def H_14_1 : Prop :=
  ∀ (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup S24), Cfg14 a b O Tr S B T₀ →
    (KY M24g S ≠ KY M24g Tr ∧
      ∀ A : Subgroup S24, (A ≤ T₀ ∧ IsE2k 6 A) ↔ (A = KY M24g S ∨ A = KY M24g Tr)) ∧
    (∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
      ∃ (Ω : Set (Submodule K (Fin 3 → K))) (φ : ↥(KY M24g S) ≃* Multiplicative (Fin 3 → K))
        (π : ↥(MY M24g S) →* MulAut (Multiplicative (Fin 3 → K))),
        IsHyperoval K Ω ∧ ConjIso (MY M24g S) (KY M24g S) (Multiplicative (Fin 3 → K))
          (hatS6set K Ω) φ π ∧
        (∀ g : ↥(MY M24g S), (g : S24) ∈ perfectCore (MY M24g S) → IsKLinearAut (π g)) ∧
        IsE2k 2 (KY M24g O ⊓ KY M24g S) ∧
        (∃ w : Fin 3 → K, w ≠ 0 ∧ ∀ k : ↥(KY M24g S),
          (k : S24) ∈ KY M24g O ⊓ KY M24g S ↔ ∃ c : K, Multiplicative.toAdd (φ k) = c • w) ∧
        Set.ncard {C : Subgroup S24 | ∃ g ∈ MY M24g S, C = conjSubg g (KY M24g O ⊓ KY M24g S)} = 15) ∧
    ConjIsoModel (MY M24g Tr) (KY M24g Tr) (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2)))
      tensorSet32 ∧
    ConjIsoModel (MY M24g O) (KY M24g O) (Multiplicative (Fin 4 → ZMod 2))
      ((natSub 4 (ZMod 2) ⊤ : Subgroup (MulAut (Multiplicative (Fin 4 → ZMod 2)))) :
        Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) ∧
    (∀ A : Subgroup S24, A ≤ M24g → A ≠ ⊥ → IsElemAbelian 2 A → 5 ≤ rk ↥A →
      ∃ g ∈ M24g, conjSubg g A ≤ KY M24g S ∨ conjSubg g A ≤ KY M24g Tr)

section H14_1


theorem as_H_14_1 : H_14_1 := by
  intro a b O Tr S B T₀ hcfg
  exact ⟨CFSG.Quasithin.AppendixH.H14.h141_part1 hcfg,
    CFSG.Quasithin.AppendixH.H14.h141_part26 hcfg,
    CFSG.Quasithin.AppendixH.H14.h141_part3 hcfg,
    CFSG.Quasithin.AppendixH.H14.h141_part4 hcfg,
    CFSG.Quasithin.AppendixH.H14.h141_part5 hcfg⟩

end H14_1

@[expose] def H_14_2 : Prop :=
  ∀ (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup S24), Cfg14 a b O Tr S B T₀ → IsSylowIn 2 (T₀ ⊓ M23g a) (M23g a) →
    (KY (M23g a) (S.erase B) ≠ KY (M23g a) (O.erase a) ∧
      ∀ A : Subgroup S24, (A ≤ T₀ ⊓ M23g a ∧ IsE2k 4 A) ↔
        (A = KY (M23g a) (S.erase B) ∨ A = KY (M23g a) (O.erase a))) ∧
    (∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
      ConjIsoModel (MY (M23g a) (S.erase B)) (KY (M23g a) (S.erase B)) (Multiplicative (Fin 2 → K))
        (gammaLset 2 K)) ∧
    ((∃ π : ↥(MY (M23g a) (O.erase a)) →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
        π.ker = (KY (M23g a) (O.erase a)).subgroupOf (MY (M23g a) (O.erase a))) ∧
      Nat.card ↥(KY (M23g a) (O.erase a)) = 16 ∧
      ∀ W : Subgroup S24, W ≤ KY (M23g a) (O.erase a) → W ≠ ⊥ →
        (∀ g ∈ MY (M23g a) (O.erase a), conjSubg g W = W) → W = KY (M23g a) (O.erase a))

section H14Two


theorem as_H_14_2 : H_14_2 := by
  intro a b O Tr S B T₀ hcfg hT
  have hOu := hcfg.trio_union O hcfg.O_mem
  exact ⟨CFSG.Quasithin.AppendixH.H14.h142_part1 hcfg.sextet hcfg.B_mem hcfg.a_B hcfg.a_O hOu
      hcfg.stab_O hcfg.stab_S hT,
    CFSG.Quasithin.AppendixH.H14.h142_part2 hcfg.sextet hcfg.B_mem hcfg.a_B hcfg.a_O hOu,
    CFSG.Quasithin.AppendixH.H14.h142_part3 hcfg.sextet hcfg.B_mem hcfg.a_B hcfg.a_O hOu⟩

end H14Two

@[expose] def H_14_3 : Prop :=
  ∀ (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup S24), Cfg14 a b O Tr S B T₀ →
  ∀ Γ : Subgroup S24, M22g a b ≤ Γ → Γ ≤ M2ab a b → IsSylowIn 2 (T₀ ⊓ Γ) Γ →
    (KY Γ (S.erase B) ⊓ M22g a b ≠ KY Γ (O.erase a |>.erase b) ∧
      (∀ A : Subgroup S24, (A ≤ T₀ ⊓ M22g a b ∧ IsE2k 4 A) ↔
        (A = KY Γ (S.erase B) ⊓ M22g a b ∨ A = KY Γ (O.erase a |>.erase b))) ∧
      (Γ ≠ M22g a b → ∀ A : Subgroup S24, (A ≤ T₀ ⊓ Γ ∧ IsE2k 5 A) ↔ A = KY Γ (S.erase B))) ∧
    ((∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
        ConjIsoModel (perfectCore (MY Γ (S.erase B) ⊓ M22g a b)) (KY Γ (S.erase B) ⊓ M22g a b)
          (Multiplicative (Fin 2 → K))
          ((natSub 2 K (CFSG.Open.StatedSL 2 K) : Subgroup (MulAut (Multiplicative (Fin 2 → K)))) :
            Set (MulAut (Multiplicative (Fin 2 → K))))) ∧
      (Γ ≠ M22g a b →
        (∃ π : ↥(MY Γ (S.erase B)) →* Equiv.Perm (Fin 5), π.range = ⊤ ∧
          π.ker = (KY Γ (S.erase B)).subgroupOf (MY Γ (S.erase B))) ∧
        Nat.card ↥(KY Γ (S.erase B)) = 32 ∧
        ∀ W₁ W₂ : Subgroup S24, W₁ ≤ KY Γ (S.erase B) → W₂ ≤ KY Γ (S.erase B) →
          (∀ g ∈ MY Γ (S.erase B), conjSubg g W₁ = W₁) → (∀ g ∈ MY Γ (S.erase B), conjSubg g W₂ = W₂) →
          W₁ ⊔ W₂ = KY Γ (S.erase B) → W₁ ⊓ W₂ = ⊥ → W₁ = ⊥ ∨ W₂ = ⊥)) ∧
    ((Γ = M22g a b → ConjSymNatural (MY Γ (O.erase a |>.erase b)) (KY Γ (O.erase a |>.erase b)) 6
        (alternatingGroup (Fin 6))) ∧
      (Γ ≠ M22g a b → ConjSymNatural (MY Γ (O.erase a |>.erase b)) (KY Γ (O.erase a |>.erase b)) 6 ⊤))

section

theorem as_H_14_3 : H_14_3 := by
  intro a b O Tr S B T₀ hcfg Γ hL hΓ hSyl
  exact CFSG.Quasithin.RonanH143.main hcfg.ne hcfg.octad.1 hcfg.a_O hcfg.b_O hcfg.sextet
    hcfg.B_mem hcfg.a_B hcfg.b_B hcfg.stab_O hcfg.stab_S hL hΓ hSyl

end

@[expose] def H_14_4 : Prop :=
  ((∀ z ∈ M24g, orderOf z = 2 →
      ((IsTwoCentralElt M24g z ↔ ∃ O : Finset (Fin 24), IsOctad O ∧ fixedSet z = O) ∧
        (¬ IsTwoCentralElt M24g z ↔ ∀ i : Fin 24, z i ≠ i))) ∧
    (∃ z ∈ M24g, orderOf z = 2 ∧ IsTwoCentralElt M24g z) ∧
    (∃ t ∈ M24g, orderOf t = 2 ∧ ¬ IsTwoCentralElt M24g t) ∧
    (∀ z ∈ M24g, ∀ z' ∈ M24g, orderOf z = 2 → orderOf z' = 2 → IsTwoCentralElt M24g z →
      IsTwoCentralElt M24g z' → IsConjIn M24g z z') ∧
    (∀ t ∈ M24g, ∀ t' ∈ M24g, orderOf t = 2 → orderOf t' = 2 → ¬ IsTwoCentralElt M24g t →
      ¬ IsTwoCentralElt M24g t' → IsConjIn M24g t t')) ∧
  (∀ a b : Fin 24, a ≠ b →
    ((∃ z ∈ M23g a, orderOf z = 2) ∧
      (∀ z ∈ M23g a, ∀ z' ∈ M23g a, orderOf z = 2 → orderOf z' = 2 → IsConjIn (M23g a) z z') ∧
      (∀ z ∈ M23g a, orderOf z = 2 → ∃ O : Finset (Fin 24), IsOctad O ∧ a ∈ O ∧ fixedSet z = O)) ∧
    ((∃ z ∈ M22g a b, orderOf z = 2) ∧
      (∀ z ∈ M22g a b, ∀ z' ∈ M22g a b, orderOf z = 2 → orderOf z' = 2 → IsConjIn (M22g a b) z z') ∧
      (∀ z ∈ M22g a b, orderOf z = 2 →
        ∃ O : Finset (Fin 24), IsOctad O ∧ a ∈ O ∧ b ∈ O ∧ fixedSet z = O))) ∧
  (∀ (isCode : Bool) (d : ℕ), (d = 22 ∨ d = 23 ∨ d = 24) → ∀ a b : Fin 24, a ≠ b →
    ∀ Γ : Subgroup S24, Ld d a b ≤ Γ → Γ ≤ AutLd d a b →
    ∀ (V : Type) [CommGroup V] (ρ : ↥Γ →* MulAut V), IsMathModule isCode d a b Γ ρ →
      (∀ z ∈ Ld d a b, orderOf z = 2 → IsTwoCentralElt (Ld d a b) z →
        rkIdx (fixV (rImg ρ (Subgroup.zpowers z))) = 4) ∧
      (d = 24 → ∀ t ∈ M24g, orderOf t = 2 → ¬ IsTwoCentralElt M24g t →
        rkIdx (fixV (rImg ρ (Subgroup.zpowers t))) = 5)) ∧
  (∀ a b : Fin 24, a ≠ b →
    ((∀ i ∈ M2ab a b, i ∉ M22g a b → orderOf i = 2 →
        ((∀ x : Fin 24, i x ≠ x) ∨
          ∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ fixedSet i = O)) ∧
      (∃ i ∈ M2ab a b, i ∉ M22g a b ∧ orderOf i = 2 ∧ ∀ x : Fin 24, i x ≠ x) ∧
      (∃ i ∈ M2ab a b, i ∉ M22g a b ∧ orderOf i = 2 ∧
        ∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ fixedSet i = O) ∧
      (∀ i ∈ M2ab a b, ∀ i' ∈ M2ab a b, i ∉ M22g a b → i' ∉ M22g a b → orderOf i = 2 →
        orderOf i' = 2 → (∀ x : Fin 24, i x ≠ x) → (∀ x : Fin 24, i' x ≠ x) →
          IsConjIn (M2ab a b) i i') ∧
      (∀ i ∈ M2ab a b, ∀ i' ∈ M2ab a b, i ∉ M22g a b → i' ∉ M22g a b → orderOf i = 2 →
        orderOf i' = 2 →
        (∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ fixedSet i = O) →
        (∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ fixedSet i' = O) →
          IsConjIn (M2ab a b) i i')) ∧
    (∀ (isCode : Bool) (V : Type) [CommGroup V] (ρ : ↥(M2ab a b) →* MulAut V),
      IsMathModule isCode 22 a b (M2ab a b) ρ →
        ∀ i ∈ M2ab a b, i ∉ M22g a b → orderOf i = 2 →
          ((∀ x : Fin 24, i x ≠ x) → rkIdx (fixV (rImg ρ (Subgroup.zpowers i))) = 5) ∧
          ((∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ fixedSet i = O) →
            rkIdx (fixV (rImg ρ (Subgroup.zpowers i))) = 3)))

section H14Four


theorem as_H_14_4 : H_14_4 := by
  have hfix : ∀ (z : S24) (O : Finset (Fin 24)), fixedSet z = O ↔ ∀ i, i ∈ O ↔ z i = i := by
    intro z O
    constructor
    · intro h i
      rw [← h]
      simp [fixedSet]
    · intro h
      ext i
      rw [h i]
      simp [fixedSet]
  obtain ⟨c1a, c1b, c1c, c1d, c1e⟩ := CFSG.Quasithin.AppendixH.H14.m24_involution_classes
  refine ⟨⟨?_, c1b, c1c, c1d, c1e⟩, ?_, ?_, ?_⟩
  · intro z hz hz2
    simpa only [hfix] using c1a z hz hz2
  · intro a b hab
    obtain ⟨⟨c2a, c2b, c2c⟩, ⟨c2d, c2e, c2f⟩⟩ :=
      CFSG.Quasithin.AppendixH.H14.m23_m22_involution_classes a b hab
    refine ⟨⟨c2a, c2b, ?_⟩, c2d, c2e, ?_⟩
    · intro z hz hz2
      simpa only [hfix] using c2c z hz hz2
    · intro z hz hz2
      simpa only [hfix] using c2f z hz hz2
  · exact CFSG.Quasithin.AppendixH.H14.rkIdx_fixV_involutions
  · intro a b hab
    obtain ⟨c4a, c4b, c4c, c4d, c4e⟩ :=
      CFSG.Quasithin.AppendixH.H14.outer_involution_classes hab
    refine ⟨⟨?_, c4b, ?_, c4d, ?_⟩, ?_⟩
    · intro i hi hi' hi2
      simpa only [hfix] using c4a i hi hi' hi2
    · simpa only [hfix] using c4c
    · intro i hi i' hi' hio hio' hi2 hi2' hO hO'
      simp only [hfix] at hO hO'
      exact c4e i hi i' hi' hio hio' hi2 hi2' hO hO'
    · intro isCode V _ ρ h i hi hi' hi2
      simpa only [hfix] using
        CFSG.Quasithin.AppendixH.H14.rkIdx_fixV_outer_involutions a b hab isCode V ρ h i hi hi' hi2

end H14Four

end CFSG.ASVolI
