module

public import CFSG.RankThree.PartOne.TCX.G2.Frame
public import CFSG.RankThree.PartOne.TCX.A1Layer
public import CFSG.RankThree.PartOne.TCX.LayerEngine
public import CFSG.RankThree.PartOne.TCX.G2.Weyl

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.G2

open Matrix Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped MatrixGroups

section Torus

variable {L : Type} [Field L] [IsAlgClosed L]

theorem twistedTorus_neg_eq {τ : Tag} {n : ModGL τ L} (hnm : n ∈ monomialSubgroup τ L)
    (hnW : ∀ u, weylQuotientHom τ L ⟨n, hnm⟩ • u =
      (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) *ᵥ u) (Fr : L →+* L) :
    twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) Fr).map
        (rootDiagUnitHom τ L) := by
  have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
  rw [← h]
  exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr

end Torus

section Stab


theorem kernelReflectionGroup_le_closure {K : Type} [Field K] {τ : Tag} (a : Fin τ.rank → Kˣ) :
    kernelReflectionGroup a ≤ Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro r ⟨w, i, hk, rfl⟩
  exact Subgroup.subset_closure ⟨_, hk, (rootReflection_eq_conj rfl).symm⟩

theorem hstab_G2 {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (a : Fin Tag.G2.rank → Kˣ) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.G2)) := by
  have hap' : a ^ p = 1 := funext fun i => hap i
  intro w hw
  exact kernelReflectionGroup_le_closure a
    (rootCharStabilizer_le_kernelReflectionGroup_G2 hp hp3 hap' ha1 hw)

end Stab

section Main


theorem g2_sector_qplus {K : Type} [Field K] [Finite K] {p f₀ : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀))
    {σ : K ≃+* K} (hσord : orderOf σ = p) (hσ : ∀ a, σ a = a ^ 2 ^ f₀)
    (hΦ : ((2 ^ f₀ : ℕ) : ZMod p) + 1 = 0)
    {x : adjointGroup Tag.G2 K} (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hxσ : entrywiseAdjointAut Tag.G2 σ x = x) :
    ((∀ a ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)),
        ∀ b ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)), a * b = b * a) ∧
      ∀ y ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)),
        y ^ (Nat.card K + 1) = 1) ∨
    SingleLayerData p (entrywiseAdjointAut Tag.G2 σ)
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK
  obtain ⟨K₀, _, _, _, hK₀⟩ := exists_subfield_of_frobenius hp hf₀ hK hσord
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := K₀) (K := K) (L := L)
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀K : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [hΦ₀def, iterateFrobenius_def, ← map_pow, hσ]
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hΦ₀K₀ : ∀ c, Φ₀ c = c ^ Nat.card K₀ := fun c => by rw [hΦ₀c, hK₀]
  have hFrc : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hΦK : ∀ u : ModGL Tag.G2 L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  have hΦ₀' : ((Nat.card K₀ : ℕ) : ZMod p) + 1 = 0 := by
    rw [hK₀]
    exact hΦ
  set n₀ : ModGL Tag.G2 L := g2Rep L with hn₀def
  have hn₀m : n₀ ∈ monomialSubgroup Tag.G2 L := g2Rep_mem_monomial
  have hn₀C : n₀ ∈ adjointGroup Tag.G2 L := g2Rep_mem_adjointGroup
  have hn₀fix : Units.map (entrywiseHom Φ₀) n₀ = n₀ := canonicalRep_frobenius_fixed f₀ g2W
  have hn₀sq : n₀ * n₀ = 1 := g2Rep_mul_self
  have hNn : n₀ ^ p = n₀ := by
    obtain ⟨m, hm⟩ := hpo
    rw [hm, pow_succ, pow_mul, pow_two, hn₀sq, one_pow, one_mul]
  have hnW : ∀ u, weylQuotientHom Tag.G2 L ⟨n₀, hn₀m⟩ • u =
      (-1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) *ᵥ u := fun u => by
    rw [weylQuotientHom_g2Rep_smul, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hq2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have hqeven : Even (Nat.card K₀) := by
    rw [hK₀]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.G2 L) := rootDiagUnit_injective
  have hT₀ := twistedTorus_neg_eq hn₀m hnW Φ₀
  set Z0 : Subgroup (ModGL Tag.G2 L) := twistedTorusOf n₀ (Units.map (entrywiseHom Φ₀)) with hZ0def
  have hZ0card : Nat.card Z0 = (Nat.card K₀ + 1) ^ 2 := by
    rw [hT₀, Subgroup.card_map_of_injective hinj0]
    exact g2_card_fixedCharTuples (τ := Tag.G2) hΦ₀K₀ hqeven
  have hN₁ : (Nat.card K₀ + 1) ^ 2 ≠ 0 := by positivity
  have hord : p ^ (Nat.card (adjointGroup Tag.G2 K₀)).factorization p =
      p ^ ((Nat.card K₀ + 1) ^ 2).factorization p := g2QPlus_ordProj K₀ hp hp5 hK₀ hf₀ hΦ₀'
  obtain ⟨g₀, hg₀C, hg₀, hconj⟩ := frame_conj_G2 (K₀ := K₀) (K := K) (L := L) hf₀ hK₀ hp hp3 n₀
    hn₀C Z0 le_rfl hN₁ hZ0card hord
  have hxfix : Units.map (entrywiseHom Φ₀) (adjEmb Tag.G2 K L x) = adjEmb Tag.G2 K L x := by
    rw [entrywise_adjEmb hΦ₀K x, hxσ]
  obtain ⟨c, hcfix, hcx⟩ := hconj x hxord hxfix
  have hcσ : entrywiseAdjointAut Tag.G2 σ c = c := by
    apply adjEmb_injective (τ := Tag.G2) (K := K) (L := L)
    rw [← entrywise_adjEmb hΦ₀K c]
    exact hcfix
  set N : ModGL Tag.G2 L := n₀ ^ p with hNdef
  have hNm : N ∈ monomialSubgroup Tag.G2 L := pow_mem hn₀m p
  have hg₀N : Units.map (entrywiseHom Fr) g₀ = g₀ * N := by
    rw [hΦK, iterate_lang (Units.map (entrywiseHom Φ₀)) hn₀fix hg₀ p]
  have hperfK : ∀ Y : Subgroup (ModGL Tag.G2 L), Finite Y → Y ≤ adjointGroup Tag.G2 L →
      (∀ y ∈ Y, Units.map (entrywiseHom Fr) y = y) → ⁅Y, Y⁆ = Y →
        Y ≤ (adjEmb Tag.G2 K L).range := by
    intro Y _ hYC hYF _
    rw [adjEmb_range, ← (G2_F4_exact_finite_field_fixed_root_matrices Tag.G2 (Or.inl rfl) K L Fr
      hFrc).1]
    intro y hy
    exact ⟨hYC hy, hYF y hy⟩
  have hstab : ∀ a : Fin Tag.G2.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit Tag.G2 a ∈ twistedTorusOf N (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.G2)) :=
    fun a hap ha1 _ => hstab_G2 hp hp3 a hap ha1
  have hTN : twistedTorusOf N (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (-1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) Fr).map
        (rootDiagUnitHom Tag.G2 L) := by
    rw [hNn]
    exact twistedTorus_neg_eq hn₀m hnW Fr
  have hzmem : g₀⁻¹ * adjEmb Tag.G2 K L (c * x * c⁻¹) * g₀ ∈ Z0 :=
    (mem_subtorusImage_iff _ _ _ _).1 hcx
  set h : ModGL Tag.G2 L := g₀⁻¹ * adjEmb Tag.G2 K L (c * x * c⁻¹) * g₀ with hhdef
  have hzmem' := hzmem
  rw [hT₀] at hzmem'
  obtain ⟨b, hbZ, hbh⟩ := Subgroup.mem_map.1 hzmem'
  have hbh' : rootDiagUnit Tag.G2 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (adjEmb Tag.G2 K L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective
        (adjEmb Tag.G2 K L (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (adjEmb Tag.G2 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective (adjEmb Tag.G2 K L) adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hxord]
  have hbp : orderOf (rootDiagUnit Tag.G2 b) = p := by
    rw [hbh']
    exact hordh
  have hap := KE.pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hap' : b ^ p = 1 := funext fun i => hap i
  have hb1 := KE.ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker' : ∀ a : Fin Tag.G2.rank → Lˣ, rootDiagUnit Tag.G2 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have hhN : h ∈ twistedTorusOf N (Units.map (entrywiseHom Fr)) :=
    twistedTorusOf_le_pow hn₀fix p hΦK hzmem
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hcS : c * x * c⁻¹ ∈ subtorusImage (adjEmb Tag.G2 K L) g₀
      (subtorusSigma N (Units.map (entrywiseHom Fr)) (rootCharKernel b)) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨hhN, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hle := rootSpan_le_centralizer (K := L) b (fun α hα => hα : rootCharKernel b ⊆ _)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hbh'] at h1
    exact h1
  have hkerZ : ∀ a : Fin Tag.G2.rank → Lˣ, rootDiagUnit Tag.G2 a = h →
      rootCharKernel a ⊆ rootCharKernel b := fun a ha => by rw [hker' a ha]
  have hFr'' : ∀ c, Fr c = c ^ 2 ^ (f₀ * p) := fun c => iterateFrobenius_def 2 (f₀ * p) c
  have hfp : 1 ≤ f₀ * p := Nat.mul_pos hf₀ hp.pos
  have hfp2 : 2 ≤ f₀ * p := hp.two_le.trans (Nat.le_mul_of_pos_left p hf₀)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, mul_comm p f₀]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f₀ * p) := Nat.pow_le_pow_right (by norm_num) hfp2
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσord
    exact hp.one_lt.ne hσord
  rcases rootCharKernel_G2_cases hp hp3 hap' hb1 with hA | ⟨θ, hθ, hkerθ⟩
  ·
    left
    have hspan : rootSpan Tag.G2 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    obtain ⟨ψ, hψinj, -, hψHQ, hψfix, -, -, -⟩ := sigma_embedding_data_of_stab (adjEmb Tag.G2 K L)
      adjEmb_injective adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrc) N g₀
      hg₀C hg₀N hperfK hp hstab (S := rootCharKernel b) (fun α hα => hα.1) hrootneg
      (ι' := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, mem_twistedFixedPoints.1 hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := Subgroup.mem_bot.1 hg
        rw [this, one_mul, mul_one])
      hxord c hcS hkerZ
    have hψt : ∀ y, ψ y ∈ torusGroup Tag.G2 L := fun y => by
      have := hψHQ y
      rwa [hspan, sup_bot_eq] at this
    have hψT : ∀ y, ψ y ∈ twistedTorusOf N (Units.map (entrywiseHom Fr)) := fun y =>
      mem_twistedTorusOf.2 ⟨hψt y, hψfix y⟩
    refine ⟨fun a ha b' hb' => ?_, fun y hy => ?_⟩
    · have key : ψ (⟨a, ha⟩ * ⟨b', hb'⟩) = ψ (⟨b', hb'⟩ * ⟨a, ha⟩) := by
        rw [map_mul, map_mul]
        exact KE.torusGroup_comm (hψt ⟨a, ha⟩) (hψt ⟨b', hb'⟩)
      exact congrArg Subtype.val (hψinj key)
    · have hmem := hψT ⟨y, hy⟩
      rw [hTN] at hmem
      obtain ⟨b'', hb'', hb''v⟩ := hmem
      have hb''p := (g2_mem_fixedCharTuples_iff hFrc b'').1 hb''
      have h1 : (ψ ⟨y, hy⟩) ^ (Nat.card K + 1) = 1 := by
        rw [← hb''v, ← map_pow]
        have : b'' ^ (Nat.card K + 1) = 1 := funext fun i => hb''p i
        rw [this, map_one]
      have h2 : ψ (⟨y, hy⟩ ^ (Nat.card K + 1)) = 1 := by
        rw [map_pow]
        exact h1
      have := hψinj (h2.trans (map_one ψ).symm)
      exact congrArg Subtype.val this
  ·
    right
    have hS : ∀ α ∈ ({θ, -θ} : Set (Fin Tag.G2.rank → ℤ)), IsRoot Tag.G2 α := by
      intro α hα
      rcases hα with rfl | rfl
      exacts [hθ, IsRoot.neg hθ]
    have hSeq : rootCharKernel b = {θ, -θ} := hkerθ
    have hn₀J : ∀ B : SL(2, L), n₀ * rootSL2 Tag.G2 L θ B * n₀⁻¹ =
        rootSL2 Tag.G2 L θ (WSL * B * WSL⁻¹) :=
      conj_rootSL2_of_neg_rep (fun α hα c => g2Rep_conj_pinnedX hα c) hθ
    have hJ₀fix : Matrix.SpecialLinearGroup.map Φ₀ (WSL : SL(2, L)) = WSL := map_wsl Φ₀
    have hJ₀sq : (WSL : SL(2, L)) * WSL = 1 := wsl_mul_self
    obtain ⟨P₀, hP₀⟩ := exists_P0_wsl (K := K₀) (L := L) Φ₀ hΦ₀K₀
    have hJpow : ∀ J : SL(2, L), J * J = 1 → J ^ p = J := fun J hJ => by
      obtain ⟨m, hm⟩ := hpo
      rw [hm, pow_succ, pow_mul, pow_two, hJ, one_pow, one_mul]
    have hNJ : ∀ B : SL(2, L), n₀ ^ p * rootSL2 Tag.G2 L θ B * (n₀ ^ p)⁻¹ =
        rootSL2 Tag.G2 L θ (WSL * B * WSL⁻¹) := fun B => by
      rw [pow_conj_rootSL2 hn₀J p B, hJpow WSL hJ₀sq]
    have hP : P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹ =
        Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
      have hJGL : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL
          (WSL : SL(2, L))) = Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
        have h2 : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL
            (WSL : SL(2, L))) = Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.map Φ₀ (WSL : SL(2, L))) := by
          ext i j
          rfl
        rw [h2, hJ₀fix]
      have h1 := P_frobenius_pow hJGL hP₀ p
      rw [h1]
      have hsq : Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) *
          Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) = 1 := by
        rw [← map_mul, hJ₀sq, map_one]
      obtain ⟨m, hm⟩ := hpo
      rw [hm, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
    have hX := a1_hX_of_J hNJ Fr hP
    obtain ⟨P, hfam, hP'⟩ := a1_sigma_family_of_action hK4 hθ Fr hFrc P₀ hX
    have hfam' : IsSigmaFamily N Fr (rootCharKernel b) P := by rw [hSeq]; exact hfam
    have hjoin : rootSpan Tag.G2 L (rootCharKernel b) ⊓
        twistedFixedPoints N (Units.map (entrywiseHom Fr)) ≤ P () := by
      rw [hSeq, hP', a1_fixed_range_of_action hθ Fr hFrc P₀ hX]
    obtain ⟨D, hD, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ :=
      a1_layer_of_frame (K := K) (L := L) hp5 hf₀ hK hσ1 hn₀J hΦ₀K hP₀
    have hrr : ρ'.range = P () := by rw [hρ'range, hP']
    exact singleLayerData_of_engine hp hΦ₀K hFrc hn₀fix hg₀C hg₀ hΦK hperfK hstab
      (fun α hα => hα.1) hrootneg P hfam' hjoin hxord hcσ hcS hkerZ
      ⟨D, hD, ρ', τ', hρ'inj, hrr, hρ'compat, hclaims⟩

end Main

end CFSG.RankThree.PartOne.TCX.G2
