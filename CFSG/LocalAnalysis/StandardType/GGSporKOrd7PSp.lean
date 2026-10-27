module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Lift
public import CFSG.LieType.ChevTwo.OppCl.AutLifts

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

open CFSG.LieType.ChevTwo.OppCl CFSG.LieType.BorelTits in
private lemma lr2opsp_bound {r f : ℕ} (h7 : ¬ 7 ∣ f)
    (K : Type) [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ f) [CharP K 2]
    (R : Type) [Group R] (e : R ≃* StatedProj (StatedSp r K)) (hr2 : 2 ≤ r)
    (hind : ∀ R' : Subgroup (MulAut (StatedProj (StatedSp r K))), IsPGroup 7 R' →
      ∀ α ∈ R', ∃ s : Equiv.Perm (Fin r ⊕ Fin r → K),
        s ∈ semilinGroup K (Fin r ⊕ Fin r → K) ∧ SemiIso (spForm r K) s ∧
        Induces (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))
          (natRep (StatedSp r K)) s α) :
    (Nat.card (MulAut R)).factorization 7 ≤ (Nat.card R).factorization 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcardAutField : Nat.card (K ≃+* K) = f := by
    let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod 2] K) :=
      { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x =>
          DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) K))
            (algebraMap (ZMod 2) K)) x
        invFun := fun σ => σ.toRingEquiv
        left_inv := fun _ => RingEquiv.ext fun _ => rfl
        right_inv := fun _ => AlgEquiv.ext fun _ => rfl
        map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
    rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) K = 2 ^ f
    rw [FiniteField.pow_finrank_eq_natCard, hKcard]
  have h7F : ¬ 7 ∣ Nat.card (K ≃+* K) := by rw [hcardAutField]; exact h7
  have h7k : ¬ 7 ∣ Nat.card ((QuotientGroup.mk'
      ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K))).ker) := by
    rw [QuotientGroup.ker_mk',
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.card_bot]
    norm_num
  haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin r ⊕ Fin r → K) := Function.nontrivial
  have hlin : ∀ s : Equiv.Perm (Fin r ⊕ Fin r → K),
      s ∈ semilinGroup K (Fin r ⊕ Fin r → K) → SemiIso (spForm r K) s →
      (∀ (c : K) (v : Fin r ⊕ Fin r → K), s (c • v) = c • s v) →
      IsPGroup 7 (Subgroup.zpowers s) →
      ∃ h : StatedSp r K, ∀ v : Fin r ⊕ Fin r → K,
        s v = natRep (StatedSp r K) h v := by
    intro s hsm hsi hsmul _
    obtain ⟨hadd, σ, hσ⟩ := hsm
    obtain ⟨τ, hτ⟩ := hsi
    obtain ⟨u, v, huv⟩ : ∃ u v : Fin r ⊕ Fin r → K, (spForm r K).β u v ≠ 0 := by
      obtain ⟨w, hw⟩ := exists_ne (0 : Fin r ⊕ Fin r → K)
      have hw' : ∃ v : Fin r ⊕ Fin r → K, (spForm r K).β w v ≠ 0 := by
        by_contra h
        exact hw ((spForm r K).nondeg w (fun v => by
          by_contra hv
          exact h ⟨v, hv⟩))
      obtain ⟨v, hv⟩ := hw'
      exact ⟨w, v, hv⟩
    have hτeq : τ = RingEquiv.refl K := by
      ext c
      have h1 : (spForm r K).β (s (c • u)) (s v) = τ ((spForm r K).β (c • u) v) := hτ _ _
      rw [hsmul c u, (spForm r K).smul_left, hτ u v, (spForm r K).smul_left, map_mul] at h1
      rw [show (spForm r K).σ = RingEquiv.refl K from rfl] at h1
      simp only [RingEquiv.refl_apply] at h1
      have hx : τ ((spForm r K).β u v) ≠ 0 := by
        intro h0
        exact huv (τ.injective (by rw [h0, map_zero]))
      exact (mul_right_cancel₀ hx h1).symm
    have hiso : ∀ u v : Fin r ⊕ Fin r → K,
        (spForm r K).β (s u) (s v) = (spForm r K).β u v := by
      intro u v
      rw [hτ u v, hτeq]
      rfl
    obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry r K
      ({ toFun := s, map_add' := hadd, map_smul' := hsmul } :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))
      (fun u v => hiso u v)
    exact ⟨g, fun v => (hg v).symm⟩
  have hbound : (Nat.card (MulAut (StatedProj (StatedSp r K)))).factorization 7 ≤
      (Nat.card (StatedProj (StatedSp r K))).factorization 7 :=
    ord7_factorization_le_of_lift
      (F := K) (V := Fin r ⊕ Fin r → K) (H := StatedSp r K)
      (K := StatedProj (StatedSp r K))
      (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))
      (QuotientGroup.mk'_surjective _)
      (natRep (StatedSp r K))
      (CFSG.LieType.BorelTits.natRep_injective _)
      (fun s => SemiIso (spForm r K) s)
      (semiIso_one (spForm r K))
      (fun a b ha hb => semiIso_mul (spForm r K) ha hb)
      (fun a ha => semiIso_inv (spForm r K) ha)
      h7F h7k hind hlin
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
  exact hbound

open CFSG.LieType.ChevTwo.OppCl CFSG.LieType.BorelTits in
theorem ord7Param_PSp {r f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .PSp r 2 f := by
  intro R _ _ hR hmodel
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hSC : StatedClassicalModel R .PSp r 2 f :=
    LieModel.statedClassicalModel hmodel (by decide)
  obtain ⟨hadm, hKdata⟩ := hSC
  obtain ⟨h2prime, hf1, hr2, hnot⟩ := hadm
  by_cases hr3 : 3 ≤ r
  · obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hKdata
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKft : Fintype.card K = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]; exact hKcard
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) hKft
    have hind : ∀ R' : Subgroup (MulAut (StatedProj (StatedSp r K))), IsPGroup 7 R' →
        ∀ α ∈ R', ∃ s : Equiv.Perm (Fin r ⊕ Fin r → K),
          s ∈ semilinGroup K (Fin r ⊕ Fin r → K) ∧ SemiIso (spForm r K) s ∧
          Induces (QuotientGroup.mk'
            ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))
            (natRep (StatedSp r K)) s α := by
      intro R' hR' α hα
      exact induced_PSp K 7 (by norm_num) r hr3 R' hR' α hα
    exact lr2opsp_bound h7 K hKcard R e hr2 hind
  · have hr_eq : r = 2 := by omega
    subst r
    have hf_ne1 : f ≠ 1 := by
      intro hf1eq
      apply hnot
      rw [hf1eq, pow_one]
    have hf2 : 2 ≤ f := by omega
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hKdata
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKft : Fintype.card K = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]; exact hKcard
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) hKft
    have hF : 4 ≤ Nat.card K := by
      rw [hKcard]
      have hpow : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      simpa using hpow
    have hind : ∀ R' : Subgroup (MulAut (StatedProj (StatedSp 2 K))), IsPGroup 7 R' →
        ∀ α ∈ R', ∃ s : Equiv.Perm (Fin 2 ⊕ Fin 2 → K),
          s ∈ semilinGroup K (Fin 2 ⊕ Fin 2 → K) ∧ SemiIso (spForm 2 K) s ∧
          Induces (QuotientGroup.mk'
            ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)))
            (natRep (StatedSp 2 K)) s α := by
      intro R' hR' α hα
      exact induced_PSp_two K 7 (by norm_num) hF R' hR' α hα
    exact lr2opsp_bound (r := 2) h7 K hKcard R e hr2 hind

end CFSG.StandardType.SporadicShape
