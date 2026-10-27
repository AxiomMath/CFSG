module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeWeylGoodDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylKernel

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.SCFourCover

private theorem prod_zpow_eq {G : Type*} [CommGroup G] (y : G) (e : Fin Tag.E6.rank → ℤ) :
    ∏ k, y ^ e k = y ^ ∑ k, e k := by
  have h : ∀ n : ℤ, y ^ n = zpowersHom G y (Multiplicative.ofAdd n) := fun _ => rfl
  simp only [h, ofAdd_sum, map_prod]

private theorem rootChar_pow_val {Ω : Type} [Field Ω] (ζ : Ωˣ)
    (x : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun k => ζ ^ (x k).val) v = ζ ^ ∑ k, ((x k).val : ℤ) * v k := by
  simp only [rootChar]
  rw [← prod_zpow_eq]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, ← zpow_mul]

private theorem cast_sum_eq (x : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    ((∑ k, ((x k).val : ℤ) * v k : ℤ) : ZMod 3) = triPairing x v := by
  simp only [triPairing, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem rootChar_pow_eq_iff {Ω : Type} [Field Ω] (ζ : Ωˣ) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) (x x' : Fin Tag.E6.rank → ZMod 3) (v v' : Fin Tag.E6.rank → ℤ) :
    rootChar (fun k => ζ ^ (x k).val) v = rootChar (fun k => ζ ^ (x' k).val) v' ↔
      triPairing x v = triPairing x' v' := by
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  rw [rootChar_pow_val, rootChar_pow_val, zpow_eq_zpow_iff_modEq, hζo,
    ← ZMod.intCast_eq_intCast_iff, cast_sum_eq, cast_sum_eq]

private theorem triPairing_add_left (p q : Fin Tag.E6.rank → ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) :
    triPairing (p + q) v = triPairing p v + triPairing q v := by
  simp only [triPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem triPairing_neg (p : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    triPairing (-p) v = -triPairing p v := by
  simp only [triPairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem zpow_val_add {Ω : Type} [Field Ω] (ζ : Ωˣ) (hζo : orderOf ζ = 3)
    (x y : ZMod 3) :
    ζ ^ ((x + y).val : ℤ) = ζ ^ ((x).val : ℤ) * ζ ^ ((y).val : ℤ) := by
  rw [← zpow_add]
  refine (zpow_eq_zpow_iff_modEq).2 ?_
  rw [hζo]
  have h : ((x + y).val : ZMod 3) = ((x.val + y.val : ℕ) : ZMod 3) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).1 h

theorem weylGoodRankFive
    (Ω : Type) [Field Ω] : WeylGoodRankFive Ω := by
  intro ι a h3 hcard
  classical
  have hzeta : ∃ ζ : Ωˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 := by
    by_contra h
    push Not at h
    have hall : ∀ i k, a i k = 1 := fun i k => h (a i k) (h3 i k)
    have hgen : ∀ i, rootDiagUnit .E6 (a i) = 1 := by
      intro i
      have hai : a i = 1 := funext (hall i)
      rw [hai, rootDiagUnit_one]
    have hbot : Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i)) = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro g ⟨i, rfl⟩
      simp [hgen i]
    have h1 : Nat.card (Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i))) = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [h1] at hcard
    norm_num at hcard
  obtain ⟨ζ, hζ3, hζ1⟩ := hzeta
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hprim : IsPrimitiveRoot ζ 3 := hζo ▸ IsPrimitiveRoot.orderOf ζ
  have hroot : ∀ y : Ωˣ, y ^ 3 = 1 → ∃ m : ZMod 3, ζ ^ m.val = y := fun y hy => by
    obtain ⟨n, hn, rfl⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 y).2 hy)
    exact ⟨n, by rw [ZMod.val_natCast_of_lt hn]⟩
  choose b hb using fun i k => hroot (a i k) (h3 i k)
  have hab : ∀ i, a i = fun k => ζ ^ (b i k).val := fun i => funext fun k => (hb i k).symm
  have K1 : ∀ i v v', rootChar (a i) v = rootChar (a i) v' ↔
      triPairing (b i) v = triPairing (b i) v' := fun i v v' => by
    rw [hab i]
    exact rootChar_pow_eq_iff ζ hζ3 hζ1 (b i) (b i) v v'
  have K2 : ∀ i v, rootChar (a i) v = 1 ↔ triPairing (b i) v = 0 := fun i v => by
    rw [← rootChar_zero (a i), K1, triPairing_zero]
  intro w hw
  let A := Multiplicative (Fin Tag.E6.rank → ZMod 3)
  let Wsub : Subgroup A :=
    Subgroup.closure (Set.range fun i => Multiplicative.ofAdd (b i))
  let Φ : A →* ModGL .E6 Ω := MonoidHom.mk'
    (fun x => rootDiagUnit .E6 (fun k => ζ ^ ((Multiplicative.toAdd x k).val : ℤ))) (by
      intro x y
      rw [← rootDiagUnit_mul]
      congr 1
      funext k
      exact zpow_val_add ζ hζo (Multiplicative.toAdd x k) (Multiplicative.toAdd y k))
  have hmap : Wsub.map Φ =
      Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i)) := by
    apply le_antisymm
    · refine Subgroup.map_le_iff_le_comap.2 ?_
      dsimp only [Wsub]
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨i, rfl⟩
      refine Subgroup.mem_comap.2 ?_
      rw [show Φ (Multiplicative.ofAdd (b i)) =
        rootDiagUnit .E6 (fun k => ζ ^ (b i k).val) from rfl, ← hab i]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨i, rfl⟩
      refine Subgroup.mem_map.2 ⟨Multiplicative.ofAdd (b i), Subgroup.subset_closure ⟨i, rfl⟩, ?_⟩
      rw [show Φ (Multiplicative.ofAdd (b i)) =
        rootDiagUnit .E6 (fun k => ζ ^ (b i k).val) from rfl, ← hab i]
  have hcardW : 3 ^ 5 ≤ Nat.card Wsub := by
    refine le_trans hcard ?_
    refine Nat.card_le_card_of_surjective
      (fun x : Wsub => (⟨Φ x.1, ?_⟩ : Subgroup.closure
        (Set.range fun i => rootDiagUnit .E6 (a i)))) ?_
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem Φ x.2
    · intro y
      have hy : y.1 ∈ Wsub.map Φ := by rw [hmap]; exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let V : Finset (Fin Tag.E6.rank → ZMod 3) :=
    (Wsub : Set A).toFinset.image (fun x => Multiplicative.toAdd x)
  have hVeq : V = (Wsub : Set A).toFinset.image (fun x => Multiplicative.toAdd x) := rfl
  have hbmem : ∀ i, b i ∈ V := by
    intro i
    rw [hVeq]
    refine Finset.mem_image.2 ⟨Multiplicative.ofAdd (b i), ?_, rfl⟩
    rw [Set.mem_toFinset]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hVcard : 81 ≤ V.card := by
    rw [hVeq, Finset.card_image_of_injective]
    · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      exact le_trans (by norm_num) hcardW
    · exact Multiplicative.toAdd.injective
  have hfix_i : ∀ i v, triPairing (b i) (w • v) = triPairing (b i) v := fun i v => by
    have hwi : w ∈ rootCharStabilizer (a i) := hw i
    exact (K1 i (w • v) v).1 (hwi v)
  have hfixW : ∀ x ∈ Wsub, ∀ v, triPairing (Multiplicative.toAdd x) (w • v) =
      triPairing (Multiplicative.toAdd x) v := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hfix_i i
    | one => intro v; simp [triPairing]
    | mul x y hx hy ihx ihy =>
      intro v
      have hxy : Multiplicative.toAdd (x * y) =
          Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
      calc triPairing (Multiplicative.toAdd (x * y)) (w • v)
          = triPairing (Multiplicative.toAdd x + Multiplicative.toAdd y) (w • v) := by rw [hxy]
        _ = triPairing (Multiplicative.toAdd x) (w • v) +
              triPairing (Multiplicative.toAdd y) (w • v) := triPairing_add_left _ _ _
        _ = triPairing (Multiplicative.toAdd x) v + triPairing (Multiplicative.toAdd y) v := by
              rw [ihx v, ihy v]
        _ = triPairing (Multiplicative.toAdd x + Multiplicative.toAdd y) v :=
              (triPairing_add_left _ _ _).symm
        _ = triPairing (Multiplicative.toAdd (x * y)) v := by rw [hxy]
    | inv x hx ihx =>
      intro v
      have hxy : Multiplicative.toAdd x⁻¹ = -Multiplicative.toAdd x := rfl
      calc triPairing (Multiplicative.toAdd x⁻¹) (w • v)
          = triPairing (-Multiplicative.toAdd x) (w • v) := by rw [hxy]
        _ = -triPairing (Multiplicative.toAdd x) (w • v) := triPairing_neg _ _
        _ = -triPairing (Multiplicative.toAdd x) v := by rw [ihx v]
        _ = triPairing (-Multiplicative.toAdd x) v := (triPairing_neg _ _).symm
        _ = triPairing (Multiplicative.toAdd x⁻¹) v := by rw [hxy]
  have hu : ∀ c ∈ V, ∀ v, triPairing c (w • v) = triPairing c v := by
    intro c hc v
    rw [hVeq] at hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact hfixW x (by rwa [Set.mem_toFinset] at hx) v
  have hmain := mem_closure_rootReflection_of_card_fix (u := w) hVcard hu
  rw [show Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α} =
      Subgroup.closure (rootReflection '' familyKernel a) by
    congr 1
    ext s
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ⟨α, hα, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨α, hα, rfl⟩]
  refine Subgroup.closure_mono (Set.image_mono fun α hα => ?_) hmain
  exact ⟨hα.1, fun i => (K2 i α).2 (hα.2 (b i) (hbmem i))⟩

end CFSG.StandardType
