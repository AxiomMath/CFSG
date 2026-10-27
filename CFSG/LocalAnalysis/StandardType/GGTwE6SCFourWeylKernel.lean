module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylSound
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem prod_zpow_eq {G : Type*} [CommGroup G] (y : G) (e : Fin Tag.E6.rank → ℤ) :
    ∏ k, y ^ e k = y ^ ∑ k, e k := by
  have h : ∀ n : ℤ, y ^ n = zpowersHom G y (Multiplicative.ofAdd n) := fun _ => rfl
  simp only [h, ofAdd_sum, map_prod]

private theorem rootChar_pow_val {Ω : Type} [Field Ω] (ζ : Ωˣ) (x : Fin Tag.E6.rank → ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun k => ζ ^ (x k).val) v = ζ ^ ∑ k, ((x k).val : ℤ) * v k := by
  simp only [rootChar]
  rw [← prod_zpow_eq]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, ← zpow_mul]

private theorem cast_sum_eq (x : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    ((∑ k, ((x k).val : ℤ) * v k : ℤ) : ZMod 3) = triPairing x v := by
  simp only [triPairing, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]


theorem mem_closure_familyKernel_of_card {Ω : Type} [Field Ω] {ι : Type}
    {a : ι → Fin Tag.E6.rank → Ωˣ} (ha : ∀ i, a i ^ 3 = 1) (hinj : Function.Injective a)
    (hcard : 81 ≤ Nat.card ι) {u : WeylGroup Tag.E6} (hu : u ∈ familyStabilizer a) :
    u ∈ Subgroup.closure (rootReflection '' familyKernel a) := by
  have : Finite ι := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype ι := Fintype.ofFinite ι
  have hai : ∀ i k, a i k ^ 3 = 1 := fun i k => by simpa using congrFun (ha i) k
  obtain ⟨i₁, i₂, h12⟩ := Fintype.exists_pair_of_one_lt_card (α := ι)
    (by rw [← Nat.card_eq_fintype_card]; omega)
  obtain ⟨i₀, k₀, h0⟩ : ∃ i k, a i k ≠ 1 := by
    by_contra h
    refine h12 (hinj (funext fun k => ?_))
    simp only [not_exists, ne_eq, not_not] at h
    rw [h i₁ k, h i₂ k]
  obtain ⟨ζ, hζ3, hζ1⟩ : ∃ ζ : Ωˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 := ⟨a i₀ k₀, hai i₀ k₀, h0⟩
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hprim : IsPrimitiveRoot ζ 3 := hζo ▸ IsPrimitiveRoot.orderOf ζ
  have hroot : ∀ y : Ωˣ, y ^ 3 = 1 → ∃ m : ZMod 3, ζ ^ m.val = y := fun y hy => by
    obtain ⟨n, hn, rfl⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 y).2 hy)
    exact ⟨n, by rw [ZMod.val_natCast_of_lt hn]⟩
  choose b hb using fun i k => hroot (a i k) (hai i k)
  have hab : ∀ i, a i = fun k => ζ ^ (b i k).val := fun i => funext fun k => (hb i k).symm
  have K1 : ∀ i v v', rootChar (a i) v = rootChar (a i) v' ↔
      triPairing (b i) v = triPairing (b i) v' := fun i v v' => by
    rw [hab i, rootChar_pow_val, rootChar_pow_val, zpow_eq_zpow_iff_modEq, hζo,
      ← ZMod.intCast_eq_intCast_iff, cast_sum_eq, cast_sum_eq]
  have K2 : ∀ i v, rootChar (a i) v = 1 ↔ triPairing (b i) v = 0 := fun i v => by
    rw [← rootChar_zero (a i), K1, triPairing_zero]
  have hbinj : Function.Injective b := fun i i' h => hinj (by rw [hab i, hab i', h])
  have hV : 81 ≤ (Finset.univ.image b).card := by
    rw [Finset.card_image_of_injective _ hbinj, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hcard
  have hcore := mem_closure_rootReflection_of_card_fix hV fun c hc v => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    exact (K1 i _ _).1 (hu i v)
  refine Subgroup.closure_mono (Set.image_mono fun α hα => ?_) hcore
  show IsRoot Tag.E6 α ∧ ∀ i, rootChar (a i) α = 1
  exact ⟨hα.1, fun i => (K2 i α).2 (hα.2 _ (Finset.mem_image_of_mem b (Finset.mem_univ i)))⟩

end CFSG.StandardType.SCFourCover

end
