module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4ThreeWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4SchurHolds
import CFSG.LocalAnalysis.StandardType.GGIOneExcLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTriD4LineWeylStrong (n : ℕ) (K : Type) [Field K] : Prop :=
  ∀ A : Subgroup (MulAut (GGTriD4R n K)), IsElemAbelian 3 A → 27 ≤ Nat.card A →
    ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ GGTriD4ID n K →
      (∃ m : GGTriD4R n K, (∀ a ∈ A, (m * (a m)⁻¹) ^ 3 = 1 ∧
          ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹) ∧
        MulAut.conj m * a₀ * (MulAut.conj m)⁻¹ ∉ Subgroup.zpowers a₀) ∨
      ∃ f ∈ A, f ∉ Subgroup.zpowers a₀ ∧
        ∀ J₁ : Subgroup (GGTriD4R n K), IsComponentOf J₁ (ggFix a₀) → ∀ l ∈ J₁, f l = l

private lemma ggIE_indAutHom_conj {L' : Type} [Group L'] [Finite L'] {R : Type} [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (n : L') :
    ggIE_indAutHom hψ hZ hker (MulAut.conj n) = MulAut.conj (ψ n) := by
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  change ggIE_indAut hψ hZ hker (MulAut.conj n) (ψ l) = MulAut.conj (ψ n) (ψ l)
  simp only [ggIE_indAut_apply, MulAut.conj_apply, map_mul, map_inv]

private lemma ggFix_map_eq {L' : Type} [Group L'] {R : Type} [Group R] [Finite L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hinj : Function.Injective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L') (a : MulAut L') :
    (ggFix a).map ψ = ggFix (ggIE_indAutHom hψ hZ hker a) := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    change a l = l at hl
    change ggIE_indAut hψ hZ hker a (ψ l) = ψ l
    rw [ggIE_indAut_apply, hl]
  · intro r hr
    change ggIE_indAut hψ hZ hker a r = r at hr
    obtain ⟨l, rfl⟩ := hψ r
    refine Subgroup.mem_map_of_mem ψ ?_
    change a l = l
    apply hinj
    rw [← ggIE_indAut_apply hψ hZ hker a l]
    exact hr

private lemma two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ', pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private lemma even_of_three_dvd_two_pow_sub_one {n : ℕ} (h : 3 ∣ 2 ^ n - 1) : Even n := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact hev
  · exfalso
    have h1 : 2 ^ n % 3 = 2 := two_pow_mod_three_odd hodd
    have h2 : 2 ^ n % 3 = 1 := by
      have hx : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h0 : (2 ^ n - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
      calc 2 ^ n % 3 = (2 ^ n - 1 + 1) % 3 := by rw [Nat.sub_add_cancel hx]
        _ = ((2 ^ n - 1) % 3 + 1 % 3) % 3 := by rw [Nat.add_mod]
        _ = 1 := by simp [h0]
    omega

theorem ggTriD4LineWeylKnown_of_strong
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (hs : IsSimpleGroup (GGTriD4R n K)) (hna : ∃ a b : GGTriD4R n K, a * b ≠ b * a)
    (h : GGTriD4LineWeylStrong n K) (F : Set (MulAut (GGTriD4R n K))) :
    GGTriD4LineWeylKnown 3 (GGTriD4R n K) (GGTriD4ID n K) F := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  intro L' _ _ ψ hψ hker hperf A hA hAI hcard hcent a₀ ha₀ ha₀ne hφ hfix
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    rw [hn0] at hK
    have hcard1 : Nat.card K = 1 := by simpa using hK
    haveI : Subsingleton K := (Nat.card_eq_one_iff_unique.mp hcard1).1
    exact (zero_ne_one (α := K)) (Subsingleton.elim (0 : K) 1)
  have hZR : Subgroup.center (GGTriD4R n K) = ⊥ := by
    haveI := hs
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (GGTriD4R n K)) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center (GGTriD4R n K) := by
        rw [h1]
        trivial
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  have hψker : ψ.ker = Subgroup.center L' := ggIE_ker_eq_center hψ hZR hker
  have hZcenter : Subgroup.center L' = ⊥ := by
    let θ : L' ⧸ Subgroup.center L' ≃* GGTriD4R n K :=
      (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    exact ggTriD4SchurInput_holds n hn K hK hs L' hperf θ
  have hkerbot : ψ.ker = ⊥ := by rw [hψker, hZcenter]
  have hinjψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  let ρ : MulAut L' →* MulAut (GGTriD4R n K) := ggIE_indAutHom hψ hZR hker
  have hinjρ : Function.Injective ρ := ggIE_indAutHom_injective hψ hZR hker hperf
  have hA' : IsElemAbelian 3 (A.map ρ) := ggIE_isElemAbelian_map ρ hA
  have h27 : 27 ≤ Nat.card (A.map ρ) := by
    rw [Subgroup.card_map_of_injective hinjρ]
    norm_num at hcard ⊢
    exact hcard
  have ha₀A : ρ a₀ ∈ A.map ρ := Subgroup.mem_map_of_mem ρ ha₀
  have hρa₀ne : ρ a₀ ≠ 1 := by
    intro h1
    exact ha₀ne (hinjρ (by rw [h1, map_one]))
  have hρa₀I : ρ a₀ ∈ GGTriD4ID n K := by
    obtain ⟨φ, hφI, hφ⟩ := hφ
    have hφeq : φ = ggIE_indAutHom hψ hZR hker a₀ :=
      ggIE_eq_indAut_of_forall hψ hZR hker hφ
    rw [show ρ a₀ = ggIE_indAutHom hψ hZR hker a₀ from rfl, ← hφeq]
    exact hφI
  rcases h (A.map ρ) hA' h27 (ρ a₀) ha₀A hρa₀ne hρa₀I with
    ⟨m, hcomm, hconj⟩ | ⟨f', hf'A', hf'not, hfix'⟩
  · left
    obtain ⟨n', rfl⟩ := hψ m
    refine ⟨n', ?_, ?_⟩
    · intro a ha
      constructor
      · apply hinjψ
        rw [map_pow, map_mul, map_inv, map_one, ← ggIE_indAut_apply hψ hZR hker a n']
        exact (hcomm (ρ a) (Subgroup.mem_map_of_mem ρ ha)).1
      · intro a' ha'
        apply hinjψ
        rw [← ggIE_indAut_apply hψ hZR hker a' (n' * (a n')⁻¹), map_mul, map_inv,
          ← ggIE_indAut_apply hψ hZR hker a n']
        exact (hcomm (ρ a) (Subgroup.mem_map_of_mem ρ ha)).2 (ρ a')
          (Subgroup.mem_map_of_mem ρ ha')
    · intro hmem
      apply hconj
      have h1 : ρ (MulAut.conj n' * a₀ * (MulAut.conj n')⁻¹) ∈
          Subgroup.zpowers (ρ a₀) := by
        have h2 := Subgroup.mem_map_of_mem ρ hmem
        rwa [MonoidHom.map_zpowers] at h2
      rw [map_mul, map_mul, map_inv, ggIE_indAutHom_conj hψ hZR hker n'] at h1
      exact h1
  · right
    obtain ⟨f, hfA, hρf⟩ := Subgroup.mem_map.mp hf'A'
    refine ⟨f, hfA, ?_, ?_⟩
    · intro hfz
      apply hf'not
      have h2 := Subgroup.mem_map_of_mem ρ hfz
      rwa [MonoidHom.map_zpowers, hρf] at h2
    · intro J₁ hJ l hl
      apply hinjψ
      have hmap : IsComponentOf (J₁.map ψ) (ggFix (ρ a₀)) := by
        have h1 := isComponentOf_map_of_injective ψ hinjψ hJ
        rwa [ggFix_map_eq ψ hψ hinjψ hZR hker a₀] at h1
      have hfixl : f' (ψ l) = ψ l := hfix' (J₁.map ψ) hmap (ψ l)
        (Subgroup.mem_map_of_mem ψ hl)
      rw [← ggIE_indAut_apply hψ hZR hker f l]
      change ρ f (ψ l) = ψ l
      rw [hρf]
      exact hfixl

theorem ggNbrKGFieldTriD4ThreeLineWeyl_of_strong
    (h : ∀ {n : ℕ} (K : Type) [Field K] [Finite K], 2 ≤ n → Even n →
      Nat.card K = (2 ^ n) ^ 3 → IsSimpleGroup (GGTriD4R n K) → GGTriD4LineWeylStrong n K) :
    GGNbrKGFieldTriD4ThreeLineWeyl := by
  intro lab hlab ht hn h3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, ?_⟩
  intro hs hna
  exact ggTriD4LineWeylKnown_of_strong K hK hs hna
    (h K hn (even_of_three_dvd_two_pow_sub_one h3) hK hs) _

end CFSG.StandardType

end
