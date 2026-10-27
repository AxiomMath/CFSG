module

public import CFSG.RankThree.PartOne.KFOUT3.G2Lift
public import CFSG.RankThree.PartOne.KFOUT3.CQuot
public import CFSG.RankThree.PartOne.KF.G2Sylow
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S12.InputsTable
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
import CFSG.LieType.Chevalley.DiagonalFieldActorData

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

theorem exists_zpow_of_ringEquiv {K : Type} [Field K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    ∃ n : ℤ, ∀ ξ : Kˣ, ξ ^ p = 1 → Units.map σ.toRingHom.toMonoidHom ξ = ξ ^ n := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hσζ : (Units.map σ.toRingHom.toMonoidHom ζ) ^ p = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).mpr hσζ)
  refine ⟨m, fun ξ hξ => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).mpr hξ)
  rw [map_pow, ← hm, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]

theorem units_map_tpHom {p : ℕ}
    {K : Type} [Field K] (σ : K ≃+* K) {n : ℤ}
    (hn : ∀ ξ : Kˣ, ξ ^ p = 1 → Units.map σ.toRingHom.toMonoidHom ξ = ξ ^ n)
    (b : Fin Tag.G2.rank → rootsOfUnity p K) :
    Units.map (entrywiseHom σ.toRingHom) (tpHom p K b) = tpHom p K b ^ n := by
  have h1 : tpHom p K b ^ n = tpHom p K (b ^ n) := (map_zpow (tpHom p K) b n).symm
  rw [h1, tpHom_apply, tpHom_apply, units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  congr 1
  funext i
  have hi : ((b i : rootsOfUnity p K) : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).mp (b i).2
  show _ = (((b i) ^ n : rootsOfUnity p K) : Kˣ)
  rw [Subgroup.coe_zpow]
  exact hn _ hi

theorem g2_normal_scalar
    {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (α : MulAut ↥(adjointGroup .G2 K)) :
    ∃ (g : ↥(adjointGroup .G2 K)) (n : ℤ), ∀ t ∈ Tp p K, α t = g * t ^ n * g⁻¹ := by
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (even_G2_exact_automorphism_normal_form hf K hK).1 α
  obtain ⟨n, hn⟩ := exists_zpow_of_ringEquiv σ hp hζ
  refine ⟨g, n, fun t ht => ?_⟩
  obtain ⟨b, rfl⟩ := ht
  apply Subtype.ext
  have h1 := hgσ (tpM p K b)
  have h2 : Units.map (entrywiseHom σ.toRingHom) ((tpM p K b : ↥(adjointGroup .G2 K)) :
      ModGL .G2 K) = ((tpM p K b : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ^ n :=
    units_map_tpHom σ hn b
  rw [h1, h2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]

theorem exists_g2_toral
    {G : Type} [Group G] [Finite G] {p : ℕ} {L F : Subgroup G} (hp : p.Prime) (h5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F)
    (hmodel : RowModel p L 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), 2 ≤ f ∧ Nat.card K = 2 ^ f ∧
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* ↥(adjointGroup .G2 K), IsCentralPQuot p ε ∧
        (∀ t ∈ Tp p K, ∃ x : F, ε (Subgroup.inclusion hFL x) = t) ∧
        (∀ x : F, ε (Subgroup.inclusion hFL x) ∈ Tp p K) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  rcases hmod with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hexc
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have h1 : f = 1 := by omega
      subst h1
      have h2 : p ∣ 1 := by simpa using hpq
      have := Nat.le_of_dvd one_pos h2
      omega
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    refine ⟨K, hKf, hKfin, f, hf2, hK, hζ, ?_⟩
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
    let iso : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot
    have hε₀ := isCentralPQuot_center' (e.trans iso) hcop
    obtain ⟨ε, hε, hT1, hT2⟩ := exists_toral_quot (T := Tp p K) (MonoidHom.id _)
      (isCentralPQuot_id p) _ hε₀ (fun t ht => Tp_exp t ht) (fun s hs t ht => Tp_comm s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp hp h5 hpK X hexp) hFL hFexp hFcomm hmax
    refine ⟨ε, hε, fun t ht => ?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hT1 t ht
      exact ⟨x, hx⟩
    · obtain ⟨t, ht, hx⟩ := hT2 x
      rw [hx]
      exact ht
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

theorem exists_weyl_scalar
    {G : Type} [Group G] [Finite G] {p : ℕ} {L F : Subgroup G} (hp : p.Prime) (h5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F)
    (hmodel : RowModel p L 2) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ n : ℤ, ∀ f ∈ F, y * f * y⁻¹ = h * f ^ n * h⁻¹ := by
  obtain ⟨K, hKf, hKfin, f, hf2, hK, hζ, ε, hε, hT1, hT2⟩ :=
    exists_g2_toral hp h5 hZ hFL hFexp hFcomm hmax hmodel
  have hQ : ∀ z ∈ Subgroup.center ↥(adjointGroup .G2 K), z = 1 := fun z hz => by
    rw [center_adjointGroup_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨α, hα⟩ := exists_mulAut_of_normalizer ε hε hQ hyL
  obtain ⟨g, n, hgn⟩ := g2_normal_scalar hf2 K hK hp hζ α
  obtain ⟨h, hhL, hhF, hrel⟩ :=
    exists_scalar_of_aut ε hε hFL hFexp hT1 hT2 hyL hyF α hα g n hgn
  exact ⟨h, hhL, hhF, n, hrel⟩

end CFSG.RankThree.PartOne.KFOUT3
