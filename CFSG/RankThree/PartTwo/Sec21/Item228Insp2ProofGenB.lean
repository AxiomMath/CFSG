module

public import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofGen
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)
open Matrix

variable {G : Type} [Group G] {X A : Subgroup G} {K : Type} [Field K]

structure IsNormalForm (A : Subgroup G) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) : Prop where
  mem_of_tZero : ∀ y ∈ tZero K, ((ι.symm y : X) : G) ∈ A
  tZero_of_mem : ∀ x : X, (x : G) ∈ A → ι x ∈ tZero K
  act : ∀ a (ha : a ∈ A), ∃ s t : Kˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
    actSL ι ⟨a, hAX ha⟩ = slConjugation 3 K (diagUnits 1 s t)

theorem diagonal_omega_eq_scalar (ω : K) :
    (diagonal ![ω, ω, ω] : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) ω := by
  rw [scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem scal_mul_comm {ω : K} (hω : IsPrimitiveRoot ω 3)
    (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) (x : X) :
    ι.symm (scalSL hω) * x = x * ι.symm (scalSL hω) := by
  apply ι.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  apply ext_of_coe
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_scalSL,
    diagonal_omega_eq_scalar]
  exact (scalar_commute ω (fun r => Commute.all ω r) _).eq

theorem inf_centralizer_eq_zpowers [Finite G] {ω : K} (hω : IsPrimitiveRoot ω 3)
    {hAX : A ≤ Subgroup.normalizer (X : Set G)} {ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K}
    (hN : IsNormalForm A hAX ι) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3) :
    A ⊓ Subgroup.centralizer (X : Set G) =
      Subgroup.zpowers ((ι.symm (scalSL hω) : X) : G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z : X := ι.symm (scalSL hω) with hz
  have hzA : (z : G) ∈ A := hN.mem_of_tZero _ (scalSL_mem_tZero hω)
  have hzC : (z : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (congrArg Subtype.val (scal_mul_comm hω ι ⟨x, hx⟩)).symm
  have hz1 : (z : G) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    have h2 := congrArg ι h1
    rw [hz, MulEquiv.apply_symm_apply, map_one] at h2
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) K =>
      (M : Matrix (Fin 3) (Fin 3) K) 0 0) h2
    simp only [coe_scalSL, Matrix.SpecialLinearGroup.coe_one, diagonal_apply_eq,
      one_apply_eq] at h3
    exact hω.ne_one (by norm_num) h3
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzA, hzC⟩))
  rw [hC3, Nat.card_zpowers, orderOf_eq_prime (hAe.2 _ hzA) hz1]

theorem exists_mem_inf_ne_one [Finite G] {B : Subgroup G} (hBA : B ≤ A)
    (hA27 : Nat.card A = 3 ^ 3) (hAX9 : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2)
    (hB9 : Nat.card B = 3 ^ 2) : ∃ u : X, (u : G) ∈ B ∧ u ≠ 1 := by
  set B' : Subgroup A := B.subgroupOf A with hB'
  set X' : Subgroup A := X.subgroupOf A with hX'
  have hcB : Nat.card B' = 9 := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, hB9]
    norm_num
  have hcX : Nat.card X' = 9 := by
    rw [hX', ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ X ≤ A)).toEquiv, hAX9]
    norm_num
  have hA : Nat.card A = 27 := by rw [hA27]; norm_num
  have hiB := Subgroup.card_mul_index B'
  have hiX := Subgroup.card_mul_index X'
  rw [hcB, hA] at hiB
  rw [hcX, hA] at hiX
  have hiB3 : B'.index = 3 := by omega
  have hiX3 : X'.index = 3 := by omega
  have hi := Subgroup.index_inf_le (H := B') (K := X')
  rw [hiB3, hiX3] at hi
  have hne : B' ⊓ X' ≠ ⊥ := by
    intro h
    have hc := Subgroup.card_mul_index (B' ⊓ X')
    rw [h, Subgroup.card_bot, hA, one_mul] at hc
    rw [h] at hi
    omega
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have huB : ((u : A) : G) ∈ B := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp u.2).1
  have huX : ((u : A) : G) ∈ X := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp u.2).2
  refine ⟨⟨_, huX⟩, huB, fun h => hu ?_⟩
  have h' : ((u : A) : G) = 1 := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem exists_rootSL_of_le_centralizer [Finite G] [Finite K] {ω : K} (hω : IsPrimitiveRoot ω 3)
    {hAX : A ≤ Subgroup.normalizer (X : Set G)} {ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K}
    (hN : IsNormalForm A hAX ι) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 3 ^ 3) (hAX9 : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3)
    {B P : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 3 ^ 2) (hPB :
      P ≤ Subgroup.centralizer (B : Set G)) [Group.IsPerfect (imageSL ι P)]
    (hPcard : Nat.card (imageSL ι P) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ b, ∃ hb : b ∈ A, ∃ s t : Kˣ, ∃ k : Fin 3, b ∈ B ∧ s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      B = Subgroup.zpowers ((ι.symm (scalSL hω) : X) : G) ⊔ Subgroup.zpowers b ∧
      actSL ι ⟨b, hAX hb⟩ = slConjugation 3 K (diagUnits 1 s t) ∧ IsOddCoord s t k ∧
      imageSL ι P = rootSL k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  set z : X := ι.symm (scalSL hω) with hzdef
  have hιz : ι z = scalSL hω := by rw [hzdef, MulEquiv.apply_symm_apply]
  have hzA : (z : G) ∈ A := hN.mem_of_tZero _ (scalSL_mem_tZero hω)
  have hAC := inf_centralizer_eq_zpowers hω hN hAe hC3
  rw [← hzdef] at hAC
  have hz3 : z ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hAe.2 _ hzA)
  have hzcard : Nat.card (Subgroup.zpowers (z : G)) = 3 := by rw [← hAC, hC3]
  have hPnd : ¬ imageSL ι P ≤ diagSL K :=
    not_imageSL_le_diagSL (by rw [hPcard]; exact one_lt_card_SL2)
  have hPBc : ∀ x ∈ P, ∀ u ∈ B, u * x = x * u := fun x hx u hu =>
    Subgroup.mem_centralizer_iff.mp (hPB hx) u hu
  have htri : ∀ u : X, (u : G) ∈ B → u = 1 ∨ u = z ∨ u = z ^ 2 := by
    intro u hu
    have huT := hN.tZero_of_mem u (hBA hu)
    have hrep : ¬ Function.Injective fun i =>
        ((ι u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i :=
      fun hinj => hPnd (imageSL_le_diagSL_of_commute ι (fun x hx => hPBc x hx u hu) huT.1 hinj)
    rw [Function.not_injective_iff] at hrep
    obtain ⟨i, j, hij, hne⟩ := hrep
    have hsc := eq_scalar_of_mem_tZero huT hne hij
    have hc3 := apply_self_pow_three_of_mem_tZero huT 0
    rcases cube_root_cases' hω3 hω1 hc3 with h | h | h
    · left
      apply ι.injective
      apply ext_of_coe
      rw [hsc, h, map_one ι, Matrix.SpecialLinearGroup.coe_one, map_one (scalar (Fin 3))]
    · right; left
      apply ι.injective
      apply ext_of_coe
      rw [hsc, h, hιz, coe_scalSL, diagonal_omega_eq_scalar]
    · right; right
      apply ι.injective
      apply ext_of_coe
      rw [hsc, h, map_pow ι, hιz, Matrix.SpecialLinearGroup.coe_pow, coe_scalSL,
        diagonal_omega_eq_scalar, ← map_pow]
  have hzB : (z : G) ∈ B := by
    obtain ⟨u, huB, hu1⟩ := exists_mem_inf_ne_one hBA hA27 hAX9 hB9
    rcases htri u huB with h | h | h
    · exact absurd h hu1
    · rw [← h]
      exact huB
    · have hzu : z = u ^ 2 := by
        rw [h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hz3, one_mul]
      rw [hzu, Subgroup.coe_pow]
      exact B.pow_mem huB 2
  have hbex : ∃ b ∈ B, b ∉ X := by
    by_contra hall
    push Not at hall
    have hle : B ≤ Subgroup.zpowers (z : G) := by
      intro b hb
      rcases htri ⟨b, hall b hb⟩ hb with h | h | h
      · have hb1 : b = 1 := congrArg Subtype.val h
        rw [hb1]
        exact one_mem _
      · have hbz : b = z := congrArg Subtype.val h
        rw [hbz]
        exact Subgroup.mem_zpowers _
      · have hbz : b = (z : G) ^ 2 := by
          have := congrArg Subtype.val h
          rwa [Subgroup.coe_pow] at this
        rw [hbz]
        exact Subgroup.npow_mem_zpowers _ 2
    have := Subgroup.card_le_of_le hle
    rw [hzcard, hB9] at this
    norm_num at this
  obtain ⟨b, hbB, hbX⟩ := hbex
  have hbA := hBA hbB
  have hsup : Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers b ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hzB) (Subgroup.zpowers_le.mpr hbB)
  have hBeq : B = Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers b := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hsup
    have hlt : Subgroup.zpowers (z : G) < Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers b := by
      refine lt_of_le_of_ne le_sup_left fun h => hbX ?_
      have hb' : b ∈ Subgroup.zpowers (z : G) := by
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
      exact (Subgroup.zpowers_le.mpr z.2) hb'
    have h1 := Subgroup.card_lt_of_lt hlt
    have hdvd := Subgroup.card_dvd_of_le hsup
    rw [hB9] at hdvd ⊢
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hzcard, hk'] at h1
    rw [hk']
    interval_cases k
    · norm_num at h1
    · norm_num at h1
    · exact le_rfl
  obtain ⟨s, t, hs, ht, hD⟩ := hN.act b hbA
  have hst : ¬ (s = 1 ∧ t = 1) := by
    rintro ⟨rfl, rfl⟩
    have h1 : actSL ι ⟨b, hAX hbA⟩ = 1 := by
      rw [hD]
      have hd1 : diagUnits (1 : Kˣ) 1 1 = 1 := by
        apply Units.ext
        rw [coe_diagUnits, Units.val_one, Units.val_one, ← diagonal_one]
        congr 1
        funext i
        fin_cases i <;> simp
      rw [hd1, map_one]
    have hbC := (actSL_eq_one_iff ι _).mp h1
    have hbAC : b ∈ A ⊓ Subgroup.centralizer (X : Set G) :=
      ⟨hbA, Subgroup.mem_centralizer_iff.mpr fun x hx => (hbC x hx).symm⟩
    rw [hAC] at hbAC
    exact hbX ((Subgroup.zpowers_le.mpr z.2) hbAC)
  have hPD : ∀ M ∈ imageSL ι P, (M : Matrix (Fin 3) (Fin 3) K) *
      ((diagUnits 1 s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((diagUnits 1 s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_comm_of_actSL ι hD (hPBc _ (Subgroup.mem_subgroupOf.mp hx) b hbB)
  have hreg : ¬ Function.Injective (![1, (s : K), (t : K)] : Fin 3 → K) := by
    intro hinj
    apply hPnd
    intro M hM
    have h := hPD M hM
    rw [coe_diagUnits, Units.val_one] at h
    exact Sec4.Res417Frame.isDiag_of_commute_diagonal hinj h
  obtain ⟨k, hk⟩ := exists_isOddCoord hst hreg
  have hle : imageSL ι P ≤ rootSL k := by
    apply le_rootSL_of_isPerfect
    intro M hM
    have h := hPD M hM
    rw [coe_diagUnits, Units.val_one] at h
    exact block_of_commute_diagonal hk.1 h
  have heq : imageSL ι P = rootSL k :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard]; exact card_rootSL_le k)
  exact ⟨b, hbA, s, t, k, hbB, hs, ht, hBeq, hD, hk, heq⟩

theorem sup_eq_of_normalForm [Finite G] [Finite K] (hK4 : 4 ≤ Nat.card K) {ω : K}
    (hω : IsPrimitiveRoot ω 3) {hAX : A ≤ Subgroup.normalizer (X : Set G)}
    {ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K} (hN : IsNormalForm A hAX ι)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 3 ^ 3)
    (hAX9 : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3) :
    ∀ B₁ B₂ P₁ P₂ : Subgroup G, B₁ ≤ A → B₂ ≤ A → Nat.card B₁ = 3 ^ 2 →
      Nat.card B₂ = 3 ^ 2 → B₁ ≠ B₂ → P₁ ≤ X ⊓ Subgroup.centralizer (B₁ : Set G) →
      P₂ ≤ X ⊓ Subgroup.centralizer (B₂ : Set G) →
      Nonempty (P₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
      Nonempty (P₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K) → P₁ ⊔ P₂ = X := by
  intro B₁ B₂ P₁ P₂ hB₁ hB₂ h9₁ h9₂ hne hP₁ hP₂ ⟨e₁⟩ ⟨e₂⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK4).1
  have hPX₁ : P₁ ≤ X := hP₁.trans inf_le_left
  have hPX₂ : P₂ ≤ X := hP₂.trans inf_le_left
  set f₁ : Matrix.SpecialLinearGroup (Fin 2) K ≃* imageSL ι P₁ :=
    e₁.symm.trans (imageSLEquiv ι hPX₁) with hf₁
  set f₂ : Matrix.SpecialLinearGroup (Fin 2) K ≃* imageSL ι P₂ :=
    e₂.symm.trans (imageSLEquiv ι hPX₂) with hf₂
  have : Group.IsPerfect (imageSL ι P₁) :=
    Group.IsPerfect.ofSurjective (f := f₁.toMonoidHom) f₁.surjective
  have : Group.IsPerfect (imageSL ι P₂) :=
    Group.IsPerfect.ofSurjective (f := f₂.toMonoidHom) f₂.surjective
  obtain ⟨b₁, hb₁A, s₁, t₁, k₁, hb₁B, hs₁, ht₁, hB₁eq, hD₁, hk₁, hι₁⟩ :=
    exists_rootSL_of_le_centralizer hω hN hAe hA27 hAX9 hC3 hB₁ h9₁ (hP₁.trans inf_le_right)
      (Nat.card_congr f₁.toEquiv).symm
  obtain ⟨b₂, hb₂A, s₂, t₂, k₂, hb₂B, hs₂, ht₂, hB₂eq, hD₂, hk₂, hι₂⟩ :=
    exists_rootSL_of_le_centralizer hω hN hAe hA27 hAX9 hC3 hB₂ h9₂ (hP₂.trans inf_le_right)
      (Nat.card_congr f₂.toEquiv).symm
  set z : X := ι.symm (scalSL hω) with hzdef
  have hAC := inf_centralizer_eq_zpowers hω hN hAe hC3
  rw [← hzdef] at hAC
  have hzB₁ : (z : G) ∈ B₁ := by
    rw [hB₁eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hk : k₁ ≠ k₂ := by
    intro hkk
    rw [← hkk] at hk₂
    apply hne
    have key : ∀ ε : ℕ, diagUnits 1 s₂ t₂ = diagUnits 1 s₁ t₁ ^ ε → b₂ ∈ B₁ := by
      intro ε hε
      set n₁ : Subgroup.normalizer (X : Set G) := ⟨b₁, hAX hb₁A⟩ with hn₁
      set n₂ : Subgroup.normalizer (X : Set G) := ⟨b₂, hAX hb₂A⟩ with hn₂
      have h : actSL ι (n₂ * (n₁ ^ ε)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_pow, hD₁, hD₂, hε, map_pow, mul_inv_cancel]
      have hc := (actSL_eq_one_iff ι _).mp h
      have hcA : b₂ * (b₁ ^ ε)⁻¹ ∈ A := A.mul_mem hb₂A (A.inv_mem (A.pow_mem hb₁A ε))
      have hcC : b₂ * (b₁ ^ ε)⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (hc x hx).symm
      have hcz : b₂ * (b₁ ^ ε)⁻¹ ∈ Subgroup.zpowers (z : G) := by
        rw [← hAC]
        exact ⟨hcA, hcC⟩
      have hcB : b₂ * (b₁ ^ ε)⁻¹ ∈ B₁ := (Subgroup.zpowers_le.mpr hzB₁) hcz
      have : b₂ = b₂ * (b₁ ^ ε)⁻¹ * b₁ ^ ε := by group
      rw [this]
      exact B₁.mul_mem hcB (B₁.pow_mem hb₁B ε)
    have hb₂B₁ : b₂ ∈ B₁ := by
      rcases eq_or_eq_sq_of_isOddCoord hs₁ ht₁ hs₂ ht₂ hk₁ hk₂ with h | h
      · exact key 1 (by rw [h, pow_one])
      · exact key 2 h
    have hle : B₂ ≤ B₁ := by
      rw [hB₂eq]
      exact sup_le (Subgroup.zpowers_le.mpr hzB₁) (Subgroup.zpowers_le.mpr hb₂B₁)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9₁, h9₂])).symm
  apply sup_eq_of_imageSL ι hPX₁ hPX₂
  rw [hι₁, hι₂]
  exact sup_rootSL_eq_top hk

end CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof
