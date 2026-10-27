module

public import CFSG.RankThree.PartOne.TCX.PlanePair
public import CFSG.RankThree.PartOne.KF.G2Sylow

public section

namespace CFSG.RankThree.PartOne.TCX.G2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KFU (g2Tuple g2Tuple_ia g2Tuple_ir rootDiagUnit_mem_adjointGroup_g2
  rootDiagUnit_mem_torusGroup_g2 exists_isPrimitiveRoot_of_dvd_card_sub_one)

open CFSG.RankThree.PartOne.TCX
open CFSG.ComponentClassification.UnbalancedCatalog (g2ia g2ir)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem g2_plane_split {K : Type} [Field K] [Finite K] {p f₀ : ℕ} (hp : p.Prime) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ (p * f₀)) {σ : K ≃+* K} (hσord : orderOf σ = p)
    (hpq : p ∣ 2 ^ f₀ - 1) :
    ∃ R U : Subgroup (adjointGroup Tag.G2 K),
      IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
        (∀ r ∈ R, entrywiseAdjointAut Tag.G2 σ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
        (∀ u ∈ U, entrywiseAdjointAut Tag.G2 σ u ∈ U) ∧
        R ≤ Subgroup.normalizer (U : Set (adjointGroup Tag.G2 K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK
  obtain ⟨-, hcard⟩ := SteinbergBT.card_fixSubfield Nat.prime_two hpf hK σ
  rw [hσord, show p * f₀ / p = f₀ from Nat.mul_div_cancel_left f₀ hp.pos] at hcard
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_of_dvd_card_sub_one (K := fixSubfield σ) hp
    (by rw [hcard]; exact hpq)
  set ζ : Kˣ := Units.map (fixSubfield σ).subtype.toMonoidHom ζ₀ with hζ
  have hinjζ : Function.Injective (Units.map (fixSubfield σ).subtype.toMonoidHom) := by
    intro u v h
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val h
  have hζp : ζ ^ p = 1 := by rw [hζ, ← map_pow, hζ₀.pow_eq_one, map_one]
  have hζ1 : ζ ≠ 1 := by
    intro h
    have : ζ₀ = 1 := hinjζ (h.trans (map_one _).symm)
    exact hζ₀.ne_one hp.one_lt this
  have hζσ : Units.map σ.toRingHom.toMonoidHom ζ = ζ := by
    apply Units.ext
    exact (mem_fixSubfield σ).1 (ζ₀ : fixSubfield σ).2
  have hσ1 : Units.map σ.toRingHom.toMonoidHom (1 : Kˣ) = 1 := map_one _
  set a₁ : Fin Tag.G2.rank → Kˣ := g2Tuple ζ 1 with ha₁
  set a₂ : Fin Tag.G2.rank → Kˣ := g2Tuple 1 ζ with ha₂
  have hia : g2ia ≠ g2ir := by decide
  have ha₁ia : a₁ g2ia = ζ := g2Tuple_ia _ _
  have ha₁ir : a₁ g2ir = 1 := g2Tuple_ir _ _
  have ha₂ia : a₂ g2ia = 1 := g2Tuple_ia _ _
  have ha₂ir : a₂ g2ir = ζ := g2Tuple_ir _ _
  have hfin : ∀ i : Fin Tag.G2.rank, i = g2ia ∨ i = g2ir := CFSG.RankThree.Chevalley.fin_G2_cases
  set u₁ : adjointGroup Tag.G2 K := ⟨rootDiagUnit Tag.G2 a₁, rootDiagUnit_mem_adjointGroup_g2 a₁⟩
    with hu₁
  set u₂ : adjointGroup Tag.G2 K := ⟨rootDiagUnit Tag.G2 a₂, rootDiagUnit_mem_adjointGroup_g2 a₂⟩
    with hu₂
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.G2 K) := rootDiagUnit_injective
  have hcoe : ∀ a, rootDiagUnitHom Tag.G2 K a = rootDiagUnit Tag.G2 a := fun a => rfl
  have hpow₁ : a₁ ^ p = 1 := by
    funext i
    rcases hfin i with rfl | rfl
    · simp [ha₁ia, hζp]
    · simp [ha₁ir]
  have hpow₂ : a₂ ^ p = 1 := by
    funext i
    rcases hfin i with rfl | rfl
    · simp [ha₂ia]
    · simp [ha₂ir, hζp]
  have hu₁p : u₁ ^ p = 1 := Subtype.ext (by
    have h : (rootDiagUnit Tag.G2 a₁) ^ p = 1 := by
      rw [← hcoe, ← map_pow, hpow₁, map_one]
    exact h)
  have hu₂p : u₂ ^ p = 1 := Subtype.ext (by
    have h : (rootDiagUnit Tag.G2 a₂) ^ p = 1 := by
      rw [← hcoe, ← map_pow, hpow₂, map_one]
    exact h)
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    have h1 : rootDiagUnit Tag.G2 a₁ = 1 := congrArg Subtype.val h
    have h2 : a₁ = 1 := hinj0 (by rw [hcoe, h1, map_one])
    have := congrFun h2 g2ia
    rw [ha₁ia] at this
    exact hζ1 this
  have hu₂1 : u₂ ≠ 1 := by
    intro h
    have h1 : rootDiagUnit Tag.G2 a₂ = 1 := congrArg Subtype.val h
    have h2 : a₂ = 1 := hinj0 (by rw [hcoe, h1, map_one])
    have := congrFun h2 g2ir
    rw [ha₂ir] at this
    exact hζ1 this
  have hao : orderOf u₁ = p := orderOf_eq_prime hu₁p hu₁1
  have hbo : orderOf u₂ = p := orderOf_eq_prime hu₂p hu₂1
  have hcomm : Commute u₁ u₂ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hu₁, hu₂]
    have h1 := (rootDiagUnitHom Tag.G2 K).map_mul a₁ a₂
    have h2 := (rootDiagUnitHom Tag.G2 K).map_mul a₂ a₁
    rw [mul_comm a₂ a₁] at h2
    exact h1.symm.trans h2
  have hind : u₂ ∉ Subgroup.zpowers u₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : rootDiagUnit Tag.G2 a₂ = (rootDiagUnit Tag.G2 a₁) ^ k := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    have h2 : a₂ = a₁ ^ k := hinj0 (by rw [hcoe, h1, map_zpow]; rfl)
    have := congrFun h2 g2ir
    rw [ha₂ir, Pi.pow_apply, ha₁ir, one_zpow] at this
    exact hζ1 this
  have hfu₁ : entrywiseAdjointAut Tag.G2 σ u₁ = u₁ := by
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut, hu₁]
    change Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.G2 a₁) = rootDiagUnit Tag.G2 a₁
    rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    congr 1
    funext i
    rcases hfin i with rfl | rfl
    · rw [ha₁ia, hζσ]
    · rw [ha₁ir, hσ1]
  have hfu₂ : entrywiseAdjointAut Tag.G2 σ u₂ = u₂ := by
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut, hu₂]
    change Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.G2 a₂) = rootDiagUnit Tag.G2 a₂
    rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    congr 1
    funext i
    rcases hfin i with rfl | rfl
    · rw [ha₂ia, hσ1]
    · rw [ha₂ir, hζσ]
  exact plane_of_torus_pair hp σ (by decide) (rootDiagUnit_mem_torusGroup_g2 a₁)
    (rootDiagUnit_mem_torusGroup_g2 a₂) hind hcomm hao hbo hfu₁ hfu₂

end CFSG.RankThree.PartOne.TCX.G2
