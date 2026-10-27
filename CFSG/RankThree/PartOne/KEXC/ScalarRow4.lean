module

public import CFSG.RankThree.PartOne.KEXC.ScalarAssemble
public import CFSG.RankThree.PartOne.KFOUT3.G2Aut
public import CFSG.RankThree.PartOne.KF.F4Sylow
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFOUT3
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover
  CFSG.ComponentClassification.UnbalancedCatalog

variable {p a : ℕ} {K : Type} [Field K]

section Power


theorem units_map_torusPair (β : K ≃+* K) (u v : Kˣ) :
    Units.map (entrywiseHom β.toRingHom) (torusPair (K := K) a (u, v)) =
      torusPair a (Units.map β.toRingHom.toMonoidHom u, Units.map β.toRingHom.toMonoidHom v) := by
  simp only [torusPair_apply, map_mul, entrywise_torusElt, map_pow]

theorem units_map_tp4Hom (β : K ≃+* K) {n : ℤ}
    (hn : ∀ ξ : Kˣ, ξ ^ p = 1 → Units.map β.toRingHom.toMonoidHom ξ = ξ ^ n)
    (b : Fin 2 → rootsOfUnity p K) :
    Units.map (entrywiseHom β.toRingHom) (tp4Hom p a K b) = tp4Hom p a K b ^ n := by
  have h1 : tp4Hom p a K b ^ n = tp4Hom p a K (b ^ n) := (map_zpow (tp4Hom p a K) b n).symm
  have hb : ∀ j : Fin 2, ((b j : rootsOfUnity p K) : Kˣ) ^ p = 1 := fun j =>
    (mem_rootsOfUnity p _).mp (b j).2
  have e0 : Units.map β.toRingHom.toMonoidHom ((b 0 : rootsOfUnity p K) : Kˣ) =
      (((b ^ n) 0 : rootsOfUnity p K) : Kˣ) := by
    show _ = (((b 0) ^ n : rootsOfUnity p K) : Kˣ)
    rw [Subgroup.coe_zpow]
    exact hn _ (hb 0)
  have e1 : Units.map β.toRingHom.toMonoidHom ((b 1 : rootsOfUnity p K) : Kˣ) =
      (((b ^ n) 1 : rootsOfUnity p K) : Kˣ) := by
    show _ = (((b 1) ^ n : rootsOfUnity p K) : Kˣ)
    rw [Subgroup.coe_zpow]
    exact hn _ (hb 1)
  rw [h1, tp4Hom_apply, tp4Hom_apply, units_map_torusPair, e0, e1]

end Power

section Row


theorem ree_normal_scalar (ha : 1 ≤ a) [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hP : F4Param p a K) (α : MulAut ↥(F4.reeGamma K a)) :
    ∃ (g : ↥(F4.reeGamma K a)) (n : ℤ), ∀ t ∈ Tp4 hP, α t = g * t ^ n * g⁻¹ := by
  obtain ⟨hfa, hNF, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨g, β⟩, hgβ, -⟩ := hNF α
  obtain ⟨n, hn⟩ := exists_zpow_of_ringEquiv β hp hζ
  refine ⟨g, n, fun t ht => ?_⟩
  obtain ⟨b, rfl⟩ := ht
  apply Subtype.ext
  rw [hgβ]
  have h1 := (hfa β).1 (tp4M hP b)
  have h2 : Units.map (entrywiseHom β.toRingHom) (((tp4M hP b : ↥(F4.reeGamma K a)) :
      ModGL F4.tag K)) = ((tp4M hP b : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ^ n :=
    units_map_tp4Hom β hn b
  change (g : ModGL F4.tag K) * ((F4.reeGammaFieldAut K a β (tp4M hP b) : ↥(F4.reeGamma K a)) :
      ModGL F4.tag K) * (g : ModGL F4.tag K)⁻¹ = _
  rw [h1, h2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]

theorem exists_ree_toral
    {G : Type} [Group G] [Finite G] {L F : Subgroup G} (hp : p.Prime) (h5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hFL : F ≤ L) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F)
    (hmodel : RowModel p L 4) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime)
      (hP : F4Param p a K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* ↥(F4.reeGamma K a), IsCentralPQuot p ε ∧
        (∀ t ∈ Tp4 hP, ∃ x : F, ε (Subgroup.inclusion hFL x) = t) ∧
        (∀ x : F, ε (Subgroup.inclusion hFL x) ∈ Tp4 hP) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  rcases hmod with ⟨hcl, -⟩ | ⟨-, hex, -⟩ | ⟨-, -, hree⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hex (by decide)
  · have hS := ReeTag.large_Ree_model_Schreier (L ⧸ Subgroup.center L) 2 f hree
    obtain ⟨-, a, hfa, K, hKf, hKfin, hK, ⟨e⟩⟩ := hree
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CharP K ReeTag.F4.prime := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [Fintype.card_eq_nat_card]
        exact hK)
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hP : F4Param p a K := ⟨hp, h5, hK', by rw [← hfa]; exact hpq⟩
    have hpK : p ∣ Nat.card K - 1 := by rw [hK']; exact hP.dvd
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    refine ⟨a, K, hKf, hKfin, hchar, hP, hζ, ?_⟩
    obtain ⟨e'⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
    have hε₀ := isCentralPQuot_center' e' hcop
    obtain ⟨ε, hε, hT1, hT2⟩ := exists_toral_quot (T := Tp4 hP) (MonoidHom.id _)
      (isCentralPQuot_id p) _ hε₀ (fun t ht => Tp4_exp hP t ht)
      (fun s hs t ht => Tp4_comm hP s t hs ht) (fun X hexp _ => exists_conj_into_Tp4 hP X hexp)
      hFL hFexp hFcomm hmax
    refine ⟨ε, hε, fun t ht => ?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hT1 t ht
      exact ⟨x, hx⟩
    · obtain ⟨t, ht, hx⟩ := hT2 x
      rw [hx]
      exact ht
  · exact absurd ht (by decide)

theorem exists_weyl_scalar_ree
    {G : Type} [Group G] [Finite G] {L F : Subgroup G} (hp : p.Prime) (h5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hFL : F ≤ L) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F)
    (hmodel : RowModel p L 4) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ n : ℤ, ∀ x ∈ F, y * x * y⁻¹ = h * x ^ n * h⁻¹ := by
  obtain ⟨a, K, hKf, hKfin, hchar, hP, hζ, ε, hε, hT1, hT2⟩ :=
    exists_ree_toral hp h5 hZ hFL hFexp hFcomm hmax hmodel
  have hQ : ∀ z ∈ Subgroup.center ↥(F4.reeGamma K a), z = 1 := fun z hz => by
    rw [large_Ree_fixed_group_center_trivial a K hP.card] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨α, hα⟩ := exists_mulAut_of_normalizer ε hε hQ hyL
  obtain ⟨g, n, hgn⟩ := ree_normal_scalar hP.one_le hP.card hp hζ hP α
  obtain ⟨h, hhL, hhF, hrel⟩ :=
    exists_scalar_of_aut ε hε hFL hFexp hT1 hT2 hyL hyF α hα g n hgn
  exact ⟨h, hhL, hhF, n, hrel⟩

theorem kf1215Scalar4 : KF1215Scalar 4 := by
  intro G _ _ p A c L E ctx hmodel n hn
  have hcore := ctx.table_core
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact exists_weyl_scalar_ree hcore.prime hcore.five_le hcore.center_pPrime hcore.F_le
    hcore.F_exp hcore.F_comm hcore.maximal hmodel hyL hyF

end Row

end CFSG.RankThree.PartOne.KEXC
