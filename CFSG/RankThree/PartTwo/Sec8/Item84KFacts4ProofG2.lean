module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
import CFSG.RankThree.PartTwo.KFacts.K73Lines
import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped MatrixGroups

section TwoByTwo

variable {K : Type} [Field K]

theorem commute_of_commute_nonscalar {B X Y : Matrix (Fin 2) (Fin 2) K}
    (hB : B 0 1 ≠ 0 ∨ B 1 0 ≠ 0 ∨ B 0 0 ≠ B 1 1) (hX : X * B = B * X) (hY : Y * B = B * Y) :
    X * Y = Y * X := by
  have eX : ∀ i j, (X * B) i j = (B * X) i j := fun i j => by rw [hX]
  have eY : ∀ i j, (Y * B) i j = (B * Y) i j := fun i j => by rw [hY]
  have x00 := eX 0 0
  have x01 := eX 0 1
  have x10 := eX 1 0
  have y00 := eY 0 0
  have y01 := eY 0 1
  have y10 := eY 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at x00 x01 x10 y00 y01 y10
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    rcases hB with hb | hc | had <;> grind

end TwoByTwo


variable {K : Type} [Field K]

section Classes

theorem commute_of_mem_short {x a b : adjointGroup .G2 K} (hx : x ∈ g2ShortSL2 K)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (ha : a ∈ g2ShortSL2 K) (hb : b ∈ g2ShortSL2 K)
    (hax : a * x = x * a) (hbx : b * x = x * b) : a * b = b * a := by
  obtain ⟨X, hX⟩ := mem_g2ShortSL2_iff.mp hx
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp ha
  obtain ⟨B, hB⟩ := mem_g2ShortSL2_iff.mp hb
  have hinj := rhoV_injective (K := K)
  have hAX : A * X = X * A := hinj (by
    rw [map_mul, map_mul, hA, hX]
    exact congrArg Subtype.val hax)
  have hBX : B * X = X * B := hinj (by
    rw [map_mul, map_mul, hB, hX]
    exact congrArg Subtype.val hbx)
  have hX3 : X ^ 3 = 1 := hinj (by
    rw [map_pow, hX, map_one]
    exact congrArg Subtype.val hx3)
  have hns : (X : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 ∨ (X : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∨
      (X : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ (X : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    by_contra h
    push Not at h
    obtain ⟨h01, h10, h00⟩ := h
    have hdet := X.2
    rw [Matrix.det_fin_two, h01, h10, h00] at hdet
    have h3' : ((X ^ 3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [hX3]; rfl
    rw [Matrix.SpecialLinearGroup.coe_pow] at h3'
    have h3 := congrFun (congrFun h3' 0) 0
    simp only [pow_three, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h00,
      Matrix.one_apply_eq] at h3
    have hl : (X : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by grind
    apply hx1
    have hX1 : X = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, hl]
    apply Subtype.ext
    rw [← hX, hX1, map_one]
    rfl
  have hAB : (A : Matrix (Fin 2) (Fin 2) K) * B = B * A :=
    commute_of_commute_nonscalar hns (congrArg Subtype.val hAX) (congrArg Subtype.val hBX)
  apply Subtype.ext
  change (a : ModGL .G2 K) * b = b * a
  rw [← hA, ← hB, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hAB

theorem false_of_conj_long_short [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    {z g h : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hg : g * z * g⁻¹ ∈ g2LongSL2 K) (hh : h * z * h⁻¹ ∈ g2ShortSL2 K) : False := by
  have hc3 : ∀ m : adjointGroup .G2 K, (m * z * m⁻¹) ^ 3 = 1 := fun m => by
    rw [conj_pow, hz3, mul_one, mul_inv_cancel]
  have hc1 : ∀ m : adjointGroup .G2 K, m * z * m⁻¹ ≠ 1 := fun m h1 => by
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hz1 h1
  obtain ⟨hcomm, -⟩ := g2ThreeBCent_split h31 hg (hc3 g) (hc1 g)
  obtain ⟨N, hNC, -, hNq, x, hxN, hxc, hx1, hx3⟩ := g2ThreeACent_split h31 hh (hc3 h) (hc1 h)
  have hperf : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp hNq.1
  set k := g * h⁻¹ with hk
  have hkz : k * (h * z * h⁻¹) * k⁻¹ = g * z * g⁻¹ := by rw [hk]; group
  have hNS : ∀ n ∈ N, k * n * k⁻¹ ∈ g2ShortSL2 K := by
    have hle : ⁅N, N⁆ ≤ (g2ShortSL2 K).comap (MulAut.conj k).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      have e : k * (a * b * a⁻¹ * b⁻¹) * k⁻¹ =
          k * a * k⁻¹ * (k * b * k⁻¹) * (k * a * k⁻¹)⁻¹ * (k * b * k⁻¹)⁻¹ := by
        group
      rw [e]
      apply hcomm
      · rw [← hkz]
        exact conj_mem_centralizer (hNC ha)
      · rw [← hkz]
        exact conj_mem_centralizer (hNC hb)
    intro n hn
    rw [← hperf] at hn
    exact hle hn
  have hx3' : (k * x * k⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hx1' : k * x * k⁻¹ ≠ 1 := fun h1 => by
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hx1 h1
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have hconj : ∀ c ∈ N, (k * c * k⁻¹) * (k * x * k⁻¹) = (k * x * k⁻¹) * (k * c * k⁻¹) := by
      intro c hc
      have := hxc c hc
      calc k * c * k⁻¹ * (k * x * k⁻¹) = k * (c * x) * k⁻¹ := by group
        _ = k * (x * c) * k⁻¹ := by rw [this]
        _ = k * x * k⁻¹ * (k * c * k⁻¹) := by group
    have h1 := commute_of_mem_short (hNS x hxN) hx3' hx1' (hNS a ha) (hNS b hb) (hconj a ha)
      (hconj b hb)
    calc a * b = k⁻¹ * (k * a * k⁻¹ * (k * b * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * b * k⁻¹ * (k * a * k⁻¹)) * k := by rw [h1]
      _ = b * a := by group
  have hbot : ⁅N, N⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hNab a ha b hb
  rw [hperf] at hbot
  rw [hbot] at hxN
  exact hx1 (Subgroup.mem_bot.mp hxN)

end Classes

section Torus

theorem exists_conj_torus_pair [Finite K] (h31 : 3 ∣ Nat.card K - 1) {u v : adjointGroup .G2 K}
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u) :
    ∃ (g : adjointGroup .G2 K) (b b' : Fin Tag.G2.rank → Kˣ),
      ((g * u * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 b ∧
        ((g * v * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 b' := by
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  set E := Subgroup.closure ({u, v} : Set (adjointGroup .G2 K)) with hE
  have hEmem : ∀ w ∈ E, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨i, j, -, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair huv hu3 hv3 hw
    rw [(Commute.pow_pow huv i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
      pow_mul, pow_mul, hu3, hv3, one_pow, one_pow, one_mul]
  have hEp : IsPGroup 3 E := by
    rintro ⟨w, hw⟩
    exact ⟨1, Subtype.ext (by simpa using hEmem w hw)⟩
  obtain ⟨y, hy⟩ := exists_conj_le_range_of_three_dvd_sub_one h31 φ hφinj E hEp
  have huE : u ∈ E := Subgroup.subset_closure (by simp)
  have hvE : v ∈ E := Subgroup.subset_closure (by simp)
  obtain ⟨Xu, hXu⟩ : y * u * y⁻¹ ∈ φ.range := hy ⟨u, huE, rfl⟩
  obtain ⟨Xv, hXv⟩ : y * v * y⁻¹ ∈ φ.range := hy ⟨v, hvE, rfl⟩
  have hXu3 : Xu ^ 3 = 1 := hφinj (by
    rw [map_pow, hXu, conj_pow, hu3, mul_one, mul_inv_cancel, map_one])
  have hXv3 : Xv ^ 3 = 1 := hφinj (by
    rw [map_pow, hXv, conj_pow, hv3, mul_one, mul_inv_cancel, map_one])
  have hXuv : Xu * Xv = Xv * Xu := hφinj (by
    rw [map_mul, map_mul, hXu, hXv]
    calc y * u * y⁻¹ * (y * v * y⁻¹) = y * (u * v) * y⁻¹ := by group
      _ = y * (v * u) * y⁻¹ := by rw [huv]
      _ = y * v * y⁻¹ * (y * u * y⁻¹) := by group)
  set E' := Subgroup.closure ({Xu, Xv} : Set (Matrix.SpecialLinearGroup (Fin (2 + 1)) K))
  have hE'3 : ∀ x ∈ E', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, -, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hXuv hXu3 hXv3 hx
    rw [(Commute.pow_pow hXuv i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
      pow_mul, pow_mul, hXu3, hXv3, one_pow, one_pow, one_mul]
  have hE'c : ∀ x ∈ E', ∀ x' ∈ E', x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨i, j, -, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hXuv hXu3 hXv3 hx
    obtain ⟨i', j', -, -, rfl⟩ :=
      KFacts.exists_pow_mul_pow_of_mem_closure_pair hXuv hXu3 hXv3 hx'
    have c1 : Commute (Xu ^ i) (Xv ^ j') := Commute.pow_pow hXuv i j'
    have c2 : Commute (Xv ^ j) (Xu ^ i') := (Commute.pow_pow hXuv i' j).symm
    exact ((((Commute.pow_pow_self Xu i i').mul_right c1).mul_left
      (c2.mul_right (Commute.pow_pow_self Xv j j'))) : Commute _ _).eq
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three h31
  obtain ⟨hω, hω1⟩ := primitive_cube_root_of_orderOf hζ
  obtain ⟨Y, hY⟩ := exists_diagonalizing_of_commuting_cube_one (ζ : K) hω hω1 E' hE'3 hE'c
  have hdu := phi_diag_mem_torusGroup φ hφ (Y * Xu * Y⁻¹)
    (hY Xu (Subgroup.subset_closure (by simp)))
  have hdv := phi_diag_mem_torusGroup φ hφ (Y * Xv * Y⁻¹)
    (hY Xv (Subgroup.subset_closure (by simp)))
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdu
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdv
  refine ⟨φ Y * y, b, b', ?_, ?_⟩
  · rw [← hb, map_mul, map_mul, map_inv, hXu]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · rw [← hb', map_mul, map_mul, map_inv, hXv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem pow_three_eq_one_of_conj_rootDiagUnit {z g : adjointGroup .G2 K} (hz3 : z ^ 3 = 1)
    {b : Fin Tag.G2.rank → Kˣ}
    (hb : ((g * z * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 b) :
    b ^ 3 = 1 := by
  apply rootDiagUnit_injective (τ := .G2) (K := K)
  change rootDiagUnitHom .G2 K (b ^ 3) = rootDiagUnitHom .G2 K 1
  rw [map_pow, map_one]
  change rootDiagUnit .G2 b ^ 3 = 1
  rw [← hb, ← Subgroup.coe_pow, conj_pow, hz3, mul_one, mul_inv_cancel, Subgroup.coe_one]

theorem exists_conj_long_of_torus {z g : adjointGroup .G2 K} {b : Fin Tag.G2.rank → Kˣ}
    (hb : ((g * z * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 b)
    (hb3 : b ^ 3 = 1) (hb0 : b g2ia ≠ 1) :
    ∃ g' : adjointGroup .G2 K, g' * z * g'⁻¹ ∈ g2LongSL2 K := by
  obtain ⟨w, ζ, -, hw⟩ := exists_weyl_threeB hb3 hb0
  have h1 := (rootDiagUnit_eq_conj_canonicalRep_iff b (Pi.mulSingle g2ia ζ) w).mpr hw
  set n : adjointGroup .G2 K :=
    ⟨canonicalRep (coxeterSystem .G2) K w, canonicalRep_mem_adjointGroup _ K w⟩ with hn
  set n' : adjointGroup .G2 K :=
    ⟨canonicalRep (coxeterSystem .G2) K wV, canonicalRep_mem_adjointGroup _ K wV⟩ with hn'
  refine ⟨n' * n⁻¹ * g, mem_g2LongSL2_iff.mpr ⟨HSL ζ, ?_⟩⟩
  have hnv : (n : ModGL .G2 K) = canonicalRep (coxeterSystem .G2) K w := rfl
  have hnv' : (n' : ModGL .G2 K) = canonicalRep (coxeterSystem .G2) K wV := rfl
  have h2 : rootDiagUnit .G2 (Pi.mulSingle g2ia ζ) =
      (n : ModGL .G2 K)⁻¹ * rootDiagUnit .G2 b * (n : ModGL .G2 K) := by
    rw [h1, hnv]
    group
  rw [rhoA_HSL, rootDiagUnit_threeB_conj, h2, ← hb]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnv']
  group

theorem exists_mem_pair_conj_long [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    {u v : adjointGroup .G2 K} (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u)
    (hu1 : u ≠ 1) (hvu : v ∉ Subgroup.zpowers u) :
    ∃ z ∈ ({u, v} : Set (adjointGroup .G2 K)), ∃ g : adjointGroup .G2 K,
      g * z * g⁻¹ ∈ g2LongSL2 K := by
  obtain ⟨g, b, b', hb, hb'⟩ := exists_conj_torus_pair h31 hu3 hv3 huv
  have hb3 := pow_three_eq_one_of_conj_rootDiagUnit hu3 hb
  have hb'3 := pow_three_eq_one_of_conj_rootDiagUnit hv3 hb'
  by_cases hb0 : b g2ia = 1
  · by_cases hb'0 : b' g2ia = 1
    · exfalso
      apply hvu
      have h1 : b g2ir ≠ 1 := by
        intro h1
        apply hu1
        have hb1 : b = 1 := by
          funext j
          rcases fin_G2_cases j with rfl | rfl
          · exact hb0
          · exact h1
        have : g * u * g⁻¹ = 1 := Subtype.ext (by rw [hb, hb1, Subgroup.coe_one]; exact
          rootDiagUnit_one')
        rwa [mul_inv_eq_one, mul_eq_left] at this
      have hβ3 : b g2ir ^ 3 = 1 := by simpa using congrFun hb3 g2ir
      have hβ'3 : b' g2ir ^ 3 = 1 := by simpa using congrFun hb'3 g2ir
      have hpow : ∃ k : ℕ, b' = b ^ k := by
        rcases cube_root_cases hβ3 h1 hβ'3 with h | h | h
        · refine ⟨0, ?_⟩
          funext j
          rcases fin_G2_cases j with rfl | rfl
          · rw [hb'0, pow_zero, Pi.one_apply]
          · rw [h, pow_zero, Pi.one_apply]
        · refine ⟨1, ?_⟩
          funext j
          rcases fin_G2_cases j with rfl | rfl
          · rw [hb'0, pow_one, hb0]
          · rw [h, pow_one]
        · refine ⟨2, ?_⟩
          funext j
          rcases fin_G2_cases j with rfl | rfl
          · rw [hb'0, Pi.pow_apply, hb0, one_pow]
          · rw [h, Pi.pow_apply]
      obtain ⟨k, hk⟩ := hpow
      have hv : g * v * g⁻¹ = g * u ^ k * g⁻¹ := Subtype.ext (by
        rw [hb', ← conj_pow, Subgroup.coe_pow, hb, hk]
        change rootDiagUnitHom .G2 K (b ^ k) = rootDiagUnitHom .G2 K b ^ k
        rw [map_pow])
      have hvk : v = u ^ k := by
        have := congrArg (fun t => g⁻¹ * t * g) hv
        simpa [mul_assoc] using this
      rw [hvk]
      exact Subgroup.npow_mem_zpowers u k
    · exact ⟨v, by simp, exists_conj_long_of_torus hb' hb'3 hb'0⟩
  · exact ⟨u, by simp, exists_conj_long_of_torus hb hb3 hb0⟩

end Torus

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
