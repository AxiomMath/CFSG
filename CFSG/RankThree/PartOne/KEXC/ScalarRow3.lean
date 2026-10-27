module

public import CFSG.RankThree.PartOne.KEXC.ScalarAssemble
public import CFSG.RankThree.PartOne.KFOUT3.G2Aut
public import CFSG.RankThree.PartOne.KF.D4Sylow
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
import CFSG.LieType.Chevalley.DiagonalFieldActorData

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFOUT3
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {p f : ℕ} {K : Type} [Field K]

theorem units_map_tp3Hom (δ : K ≃+* K) {n : ℤ}
    (hn : ∀ ξ : Kˣ, ξ ^ p = 1 → Units.map δ.toRingHom.toMonoidHom ξ = ξ ^ n)
    (b : Fin 2 → rootsOfUnity p K) :
    Units.map (entrywiseHom δ.toRingHom) (tp3Hom p K b) = tp3Hom p K b ^ n := by
  have h1 : tp3Hom p K b ^ n = tp3Hom p K (b ^ n) := (map_zpow (tp3Hom p K) b n).symm
  rw [h1, tp3Hom_apply, tp3Hom_apply, units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  congr 1
  funext i
  have hb : ∀ j : Fin 2, ((b j : rootsOfUnity p K) : Kˣ) ^ p = 1 := fun j =>
    (mem_rootsOfUnity p _).mp (b j).2
  by_cases hi : i = d4i2
  · subst hi
    rw [KFU.d4Tuple_two, KFU.d4Tuple_two]
    show _ = (((b 0) ^ n : rootsOfUnity p K) : Kˣ)
    rw [Subgroup.coe_zpow]
    exact hn _ (hb 0)
  · have hx : ∀ x y : Kˣ, KFU.d4Tuple x y i = x := fun x y => by simp [KFU.d4Tuple, hi]
    rw [hx, hx]
    show _ = (((b 1) ^ n : rootsOfUnity p K) : Kˣ)
    rw [Subgroup.coe_zpow]
    exact hn _ (hb 1)


theorem d4_normal_scalar (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hP : D4Param p f K σ.toRingHom)
    (α : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (n : ℤ),
      ∀ t ∈ Tp3 hP, α t = g * t ^ n * g⁻¹ := by
  obtain ⟨hfa, hNF, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF α
  obtain ⟨n, hn⟩ := exists_zpow_of_ringEquiv δ hp hζ
  refine ⟨g, n, fun t ht => ?_⟩
  obtain ⟨b, rfl⟩ := ht
  apply Subtype.ext
  rw [hgδ]
  have h1 := hfa δ (tp3M hP b)
  have h2 : Units.map (entrywiseHom δ.toRingHom) (((tp3M hP b : ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) : ModGL TwistTag.D4.tag K)) =
      ((tp3M hP b : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) ^ n :=
    units_map_tp3Hom δ hn b
  change (g : ModGL TwistTag.D4.tag K) * ((fieldActor σ δ (tp3M hP b) :
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : ModGL TwistTag.D4.tag K) *
      (g : ModGL TwistTag.D4.tag K)⁻¹ = _
  rw [h1, h2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]

theorem exists_d4_toral
    {G : Type} [Group G] [Finite G] {L F : Subgroup G} (hp : p.Prime) (h5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hFL : F ≤ L) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F)
    (hmodel : RowModel p L 3) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (σ : K ≃+* K) (hP : D4Param p f K σ.toRingHom),
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsCentralPQuot p ε ∧
        (∀ t ∈ Tp3 hP, ∃ x : F, ε (Subgroup.inclusion hFL x) = t) ∧
        (∀ x : F, ε (Subgroup.inclusion hFL x) ∈ Tp3 hP) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  rcases hmod with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, hKf, hKfin, hK, σ₀, hσ₀, ⟨e⟩⟩ := hexc
    have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
    obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
      ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
    have hP : D4Param p f K σ.toRingHom := ⟨hp, h5, hf1, hK3, hσ₀, hpq⟩
    have hpK : p ∣ Nat.card K - 1 := by
      rw [hK3]
      exact hpq.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3)
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    refine ⟨f, K, hKf, σ, hP, hζ, ?_⟩
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
    obtain ⟨-, -, -, -, -, -, -, ⟨E⟩⟩ :=
      even_triality_exact_automorphism_normal_form hf1 K hK3 σ hσ₀
    have hε₀ := isCentralPQuot_center' (e.trans E) hcop
    obtain ⟨ε, hε, hT1, hT2⟩ := exists_toral_quot (T := Tp3 hP) (MonoidHom.id _)
      (isCentralPQuot_id p) _ hε₀ (fun t ht => Tp3_exp hP t ht)
      (fun s hs t ht => Tp3_comm hP s t hs ht) (fun X hexp _ => exists_conj_into_Tp3 hP X hexp)
      hFL hFexp hFcomm hmax
    refine ⟨ε, hε, fun t ht => ?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hT1 t ht
      exact ⟨x, hx⟩
    · obtain ⟨t, ht, hx⟩ := hT2 x
      rw [hx]
      exact ht
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

theorem exists_weyl_scalar_d4
    {G : Type} [Group G] [Finite G] {L F : Subgroup G} (hp : p.Prime) (h5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hFL : F ≤ L) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F)
    (hmodel : RowModel p L 3) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ n : ℤ, ∀ x ∈ F, y * x * y⁻¹ = h * x ^ n * h⁻¹ := by
  obtain ⟨f, K, hKf, σ, hP, hζ, ε, hε, hT1, hT2⟩ :=
    exists_d4_toral hp h5 hZ hFL hFexp hFcomm hmax hmodel
  have := hP.finite
  obtain ⟨-, -, -, -, -, -, hZc, -⟩ :=
    even_triality_exact_automorphism_normal_form hP.one_le K hP.card σ hP.frob
  have hQ : ∀ z ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), z = 1 :=
    fun z hz => by
      rw [hZc] at hz
      exact Subgroup.mem_bot.mp hz
  obtain ⟨α, hα⟩ := exists_mulAut_of_normalizer ε hε hQ hyL
  obtain ⟨g, n, hgn⟩ := d4_normal_scalar hP.one_le hP.card σ hP.frob hp hζ hP α
  obtain ⟨h, hhL, hhF, hrel⟩ :=
    exists_scalar_of_aut ε hε hFL hFexp hT1 hT2 hyL hyF α hα g n hgn
  exact ⟨h, hhL, hhF, n, hrel⟩

theorem kf1215Scalar3 : KF1215Scalar 3 := by
  intro G _ _ p A c L E ctx hmodel n hn
  have hcore := ctx.table_core
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact exists_weyl_scalar_d4 hcore.prime hcore.five_le hcore.center_pPrime hcore.F_le
    hcore.F_exp hcore.F_comm hcore.maximal hmodel hyL hyF

end CFSG.RankThree.PartOne.KEXC
