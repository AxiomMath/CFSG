module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5CoreD
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Klein
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Subrep
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem sz5e1_dim_le_of_fixBound {F K : Type} [Field F] [Group K] [Finite K] (R : Subgroup K)
    [R.Normal]
    (hK : SzSetup K R) {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : K →* (V ≃ₗ[F] V)) {r : ℕ}
    (hfix : FixBound ρ r) :
    Module.finrank F V ≤ 3 * r := by
  obtain ⟨a, b, ha, hb, hab, ha2, hb2, hcomm⟩ := sz5e1_klein_four R hK
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h1 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
    rw [h1, h2]
  have hab2 : (a * b) ^ 2 = 1 := by
    have hc : Commute a b := hcomm
    rw [hc.mul_pow, ha2, hb2, one_mul]
  have hsum := sz5e1_klein_sum hF (ρ a) (ρ b) (by rw [← map_pow, ha2, map_one])
    (by rw [← map_pow, hb2, map_one]) (by rw [← map_mul, ← map_mul, hcomm])
  have h1 : Module.finrank F (fixSpaceOf (ρ a)) ≤ r :=
    hfix a ha (isPGroup_two_zpowers_of_sq a ha2)
  have h2 : Module.finrank F (fixSpaceOf (ρ b)) ≤ r :=
    hfix b hb (isPGroup_two_zpowers_of_sq b hb2)
  have h3 : Module.finrank F (fixSpaceOf (ρ (a * b))) ≤ r :=
    hfix (a * b) hab1 (isPGroup_two_zpowers_of_sq _ hab2)
  rw [map_mul] at h3
  omega

theorem fixBound_of_surjective {F K D V : Type} [Field F] [Group K] [Finite K] [Group D]
    [AddCommGroup V]
    [Module F V] (φ : K →* D) (hφ : Function.Surjective φ)
    (ρ : K →* (V ≃ₗ[F] V)) (ρ' : D →* (V ≃ₗ[F] V)) (hcomp : ∀ k, ρ' (φ k) = ρ k)
    {r : ℕ} (hfix : FixBound ρ r) : FixBound ρ' r := by
  intro d hd1 hd2
  obtain ⟨t, rfl, ht2⟩ := exists_two_lift φ d (by obtain ⟨k, hk⟩ := hφ d; exact ⟨k, hk⟩) hd2
  have ht1 : t ≠ 1 := fun h => hd1 (by rw [h, map_one])
  have h' : Module.finrank F (fixSpaceOf (ρ t)) ≤ r := hfix t ht1 ht2
  show Module.finrank F (fixSpaceOf (ρ' (φ t))) ≤ r
  rw [hcomp]
  exact h'

theorem irreducibleRep_of_surjective {F K D V : Type} [Field F] [Group K] [Group D]
    [AddCommGroup V]
    [Module F V] (φ : K →* D) (ρ : K →* (V ≃ₗ[F] V))
    (ρ' : D →* (V ≃ₗ[F] V)) (hcomp : ∀ k, ρ' (φ k) = ρ k)
    (hirr : IsIrreducibleRep ρ) : IsIrreducibleRep ρ' := by
  intro W hW
  apply hirr W
  intro k w hw
  have h := hW (φ k) w hw
  rwa [hcomp] at h

theorem noInvariantAlt_of_surjective {F K D V : Type} [Field F] [Group K] [Group D]
    [AddCommGroup V]
    [Module F V] (φ : K →* D) (hφ : Function.Surjective φ)
    (ρ : K →* (V ≃ₗ[F] V)) (ρ' : D →* (V ≃ₗ[F] V)) (hcomp : ∀ k, ρ' (φ k) = ρ k)
    (hna : NoInvariantAlt ρ') : NoInvariantAlt ρ := by
  intro f hf hinv
  apply hna f hf
  intro d v w
  obtain ⟨k, rfl⟩ := hφ d
  rw [hcomp]
  exact hinv k v w

theorem sz5e1_core_K1 {F K : Type} [Field F] [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : K →* (V ≃ₗ[F] V)) (hirr : IsIrreducibleRep ρ)
    (hnt : ∃ k, ρ k ≠ 1) (hfix : FixBound ρ 3) : False := by
  have hD := hK.quotient ρ.ker (ker_le_of_nontrivial R hK ρ hnt)
  have hinj := QuotientGroup.kerLift_injective ρ
  have hdim : Module.finrank F V ≤ 12 := by
    have := sz5e1_dim_le_of_fixBound R hK hF ρ hfix
    omega
  have hmk := QuotientGroup.mk'_surjective ρ.ker
  have hfix' := fixBound_of_surjective (QuotientGroup.mk' ρ.ker) hmk ρ
    (QuotientGroup.kerLift ρ) (fun k => rfl) hfix
  have hirr' := irreducibleRep_of_surjective (QuotientGroup.mk' ρ.ker) ρ
    (QuotientGroup.kerLift ρ) (fun k => rfl) hirr
  exact sz5e1_core_D3 _ hD hF (QuotientGroup.kerLift ρ) hinj hirr' hdim hfix'

theorem sz5e1_core_K2 {F K : Type} [Field F] [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : K →* (V ≃ₗ[F] V)) (hirr : IsIrreducibleRep ρ)
    (hnt : ∃ k, ρ k ≠ 1) (hfix : FixBound ρ 4) : NoInvariantAlt ρ := by
  have hD := hK.quotient ρ.ker (ker_le_of_nontrivial R hK ρ hnt)
  have hinj := QuotientGroup.kerLift_injective ρ
  have hdim : Module.finrank F V ≤ 12 := by
    have := sz5e1_dim_le_of_fixBound R hK hF ρ hfix
    omega
  have hmk := QuotientGroup.mk'_surjective ρ.ker
  have hfix' := fixBound_of_surjective (QuotientGroup.mk' ρ.ker) hmk ρ
    (QuotientGroup.kerLift ρ) (fun k => rfl) hfix
  have hirr' := irreducibleRep_of_surjective (QuotientGroup.mk' ρ.ker) ρ
    (QuotientGroup.kerLift ρ) (fun k => rfl) hirr
  exact noInvariantAlt_of_surjective (QuotientGroup.mk' ρ.ker) hmk ρ (QuotientGroup.kerLift ρ)
    (fun k => rfl) (sz5e1_core_D2 _ hD hF (QuotientGroup.kerLift ρ) hinj hirr' hdim hfix')

theorem sz5e1_R_nontrivial {F K : Type} [Field F] [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : K →* (V ≃ₗ[F] V)) (hnt : ∃ k, ρ k ≠ 1)
    (hfix : FixBound ρ 4) : ∃ r ∈ R, ∃ v, ρ r v ≠ v := by
  by_contra hcon
  have hR : ∀ r ∈ R, ρ r = 1 := by
    intro r hr
    apply LinearEquiv.ext
    intro v
    by_contra hne
    exact hcon ⟨r, hr, v, hne⟩
  have hker : ρ.ker ≤ R := ker_le_of_nontrivial R hK ρ hnt
  let ρ' : K ⧸ R →* (V ≃ₗ[F] V) := QuotientGroup.lift R ρ (fun r hr => hR r hr)
  have hcomp : ∀ k, ρ' (QuotientGroup.mk' R k) = ρ k := fun k => rfl
  have hinj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
    have h1 : ρ k = 1 := hd
    exact (QuotientGroup.eq_one_iff k).mpr (hker h1)
  have hfix' := fixBound_of_surjective (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
    ρ ρ' hcomp hfix
  exact sz5e1_core_D1 hK.2.2 hF ρ' hinj hfix'

theorem fixBound_of_subrep {F K A : Type} [Field F] [Group K] [AddCommGroup A] [Module F A]
    [Module.Finite F A] (ρ : K →* (A ≃ₗ[F] A)) (B : Submodule F A)
    (σ : K →* (↥B ≃ₗ[F] ↥B)) (hσ : ∀ (k : K) (b : ↥B), ((σ k b : ↥B) : A) = ρ k b)
    {r : ℕ} (hfix : FixBound ρ r) : FixBound σ r := by
  intro t ht h2
  refine le_trans ?_ (hfix t ht h2)
  let f : (fixSpace σ t) →ₗ[F] (fixSpace ρ t) :=
    LinearMap.codRestrict (fixSpace ρ t) (B.subtype ∘ₗ (fixSpace σ t).subtype) (by
      intro x
      have hx := (mem_fixSpace σ t (x : ↥B)).mp x.2
      rw [mem_fixSpace]
      show ρ t ((x : ↥B) : A) = ((x : ↥B) : A)
      rw [← hσ, hx])
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fixSpace ρ t => (z : A)) hxy
  exact LinearMap.finrank_le_finrank_of_injective hf

theorem sz5e1_module_trivial {F K : Type} [Field F] [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) {A : Type} [AddCommGroup A] [Module F A]
    [Module.Finite F A] (hF : ringChar F ≠ 2) (ρ : K →* (A ≃ₗ[F] A)) (hfix : FixBound ρ 3) :
    ∀ k, ρ k = 1 := by
  by_contra hcon
  obtain ⟨k0, hk0⟩ := not_forall.mp hcon
  have hR := sz5e1_R_nontrivial R hK hF ρ ⟨k0, hk0⟩ (fixBound_mono hfix (by norm_num))
  obtain ⟨B, σ, hσ, hirr, r, -, b, hb⟩ := sz5e1_irreducible_subrep hF R hK.2.1 ρ hR
  have hnt : ∃ k, σ k ≠ 1 := ⟨r, fun h => hb (by rw [h]; rfl)⟩
  exact sz5e1_core_K1 R hK hF σ hirr hnt (fixBound_of_subrep ρ B σ hσ hfix)

theorem sz5e1_module_forms {F K : Type} [Field F] [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) {A : Type} [AddCommGroup A] [Module F A]
    [Module.Finite F A] (hF : ringChar F ≠ 2) (ρ : K →* (A ≃ₗ[F] A)) (hfix : FixBound ρ 4)
    (hnt : ∃ k, ρ k ≠ 1) :
    ∃ B : Submodule F A, (∀ k : K, ∀ b ∈ B, ρ k b ∈ B) ∧
      (∃ k : K, ∃ b ∈ B, ρ k b ≠ b) ∧
      ∀ f : A →ₗ[F] A →ₗ[F] F, (∀ v, f v v = 0) →
        (∀ (k : K) (v w : A), f (ρ k v) (ρ k w) = f v w) → ∀ v ∈ B, ∀ w ∈ B, f v w = 0 := by
  have hR := sz5e1_R_nontrivial R hK hF ρ hnt hfix
  obtain ⟨B, σ, hσ, hirr, r, -, b, hb⟩ := sz5e1_irreducible_subrep hF R hK.2.1 ρ hR
  have hntσ : ∃ k, σ k ≠ 1 := ⟨r, fun h => hb (by rw [h]; rfl)⟩
  have hna := sz5e1_core_K2 R hK hF σ hirr hntσ (fixBound_of_subrep ρ B σ hσ hfix)
  refine ⟨B, fun k b hb => ?_, ⟨r, b, b.2, fun h => hb (Subtype.ext ?_)⟩, ?_⟩
  · have := hσ k ⟨b, hb⟩
    rw [← this]
    exact (σ k ⟨b, hb⟩).2
  · rw [hσ]
    exact h
  · intro f hf hinv v hv w hw
    have h0 := hna (f.compl₁₂ B.subtype B.subtype) (fun x => hf x) (by
      intro k x y
      show f ((σ k x : ↥B) : A) ((σ k y : ↥B) : A) = f x y
      rw [hσ, hσ]
      exact hinv k x y)
    exact congrArg (fun g => g ⟨v, hv⟩ ⟨w, hw⟩) h0

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
