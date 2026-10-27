module

public import CFSG.RankThree.PartOne.S11c.G2Abstract
public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley

variable {K : Type} [Field K]

theorem toralCentralizer_G2_le (hK : ringChar K ≠ 2) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) : toralCentralizer .G2 K a ≤ toralRootGroup .G2 K a := by
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient .G2 K a
  have hW : ∀ w ∈ rootCharStabilizer a, w ∈ kernelReflectionGroup a := by
    intro w hw
    rw [kernelReflectionGroup_eq_kernelWeylGroup hK ha]
    have := (sign_character_Weyl_stabilizer_quotients .G2
      (maskChar (signTupleBits a))).2.2.1 (Or.inl rfl)
    rw [← this]
    exact (mem_rootCharStabilizer_iff hK ha).1 hw
  intro g hg
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : (QuotientGroup.mk ⟨w, hw⟩ : _ ⧸ (kernelReflectionGroup a).subgroupOf
      (rootCharStabilizerSubgroup a)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hW w hw
  rw [h1, map_one] at hq
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq.symm)

theorem exists_torus_mul_rootSpan (hK : ringChar K ≠ 2) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {g : ModGL .G2 K} (hg : g ∈ toralCentralizer .G2 K a) :
    ∃ x ∈ torusGroup .G2 K, ∃ s ∈ rootSpan .G2 K (rootCharKernel a), x * s = g := by
  have hM := toralCentralizer_G2_le hK ha hg
  have hsup : (torusGroup .G2 K ⊔ rootSpan .G2 K (rootCharKernel a)).subgroupOf
      (toralCentralizer .G2 K a) =
      (torusGroup .G2 K).subgroupOf (toralCentralizer .G2 K a) ⊔
        (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a) :=
    Subgroup.subgroupOf_sup (torusGroup_le_toralCentralizer a)
      (rootSpan_rootCharKernel_le_toralCentralizer a)
  have h1 : (⟨g, hg⟩ : toralCentralizer .G2 K a) ∈
      (torusGroup .G2 K).subgroupOf (toralCentralizer .G2 K a) ⊔
        (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a) := by
    rw [← hsup]
    exact hM
  obtain ⟨x, hx, s, hs, hxs⟩ := Subgroup.mem_sup_of_normal_right.1 h1
  exact ⟨x, hx, s, hs, congrArg Subtype.val hxs⟩

@[expose] noncomputable def g2Mul {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) (K : Type)
    [Field K] : SL2 K × SL2 K →* ModGL .G2 K :=
  (rootSL2 .G2 K α).noncommCoprod (rootSL2 .G2 K β) fun A B => g2_pair_commute h A B

theorem g2Mul_apply {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) (A B : SL2 K) :
    g2Mul h K (A, B) = rootSL2 .G2 K α A * rootSL2 .G2 K β B :=
  rfl

theorem ker_g2Mul_central {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) :
    ∀ z ∈ (g2Mul h K).ker,
      z.1 ∈ Subgroup.center (SL2 K) ∧ z.2 ∈ Subgroup.center (SL2 K) := by
  rintro ⟨A, B⟩ hz
  rw [MonoidHom.mem_ker, g2Mul_apply] at hz
  have hA : rootSL2 .G2 K α A = (rootSL2 .G2 K β B)⁻¹ := eq_inv_of_mul_eq_one_left hz
  have hB : rootSL2 .G2 K β B = (rootSL2 .G2 K α A)⁻¹ := eq_inv_of_mul_eq_one_right hz
  refine ⟨mem_center_of_forall_rootSL2_commute (β := α) fun D => ?_,
    mem_center_of_forall_rootSL2_commute (β := β) fun D => ?_⟩
  · rw [hA]
    exact (g2_pair_commute h D B).inv_right
  · rw [hB]
    exact (g2_pair_commute h A D).symm.inv_right

theorem rootChar_mul' {τ : Tag} (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem g2_torus_sq {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) {x : ModGL .G2 K}
    (hx : x ∈ torusGroup .G2 K) : x ^ 2 ∈ (g2Mul h K).range := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hl : rootChar (l * l) α = rootChar l α ^ 2 := by
    rw [rootChar_mul', sq]
  obtain ⟨c₁, c₂, hc⟩ := g2_pair_rootDiagUnit h (l * l) (rootChar l α) hl
  refine ⟨(HSL c₁, HSL c₂), ?_⟩
  rw [g2Mul_apply, ← hc, sq, ← rootDiagUnit_mul]

theorem g2_sq_mem (hK : ringChar K ≠ 2) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β)
    (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a)) {g : ModGL .G2 K}
    (hg : g ∈ toralCentralizer .G2 K a) : g ^ 2 ∈ (g2Mul h K).range := by
  obtain ⟨x, hx, s, hs, rfl⟩ := exists_torus_mul_rootSpan hK ha hg
  have hxX : x ∈ toralCentralizer .G2 K a := torusGroup_le_toralCentralizer a hx
  have hsq := g2_torus_sq h hx
  have hs' : s ∈ (g2Mul h K).range := hS ▸ hs
  have hn : x⁻¹ * s * x ∈ (g2Mul h K).range := by
    have := (Subgroup.mem_normalizer_iff.1
      (toralCentralizer_le_normalizer_rootSpan a (inv_mem hxX)) s).1 (hS ▸ hs'
        : s ∈ rootSpan .G2 K (rootCharKernel a))
    rw [inv_inv] at this
    exact hS ▸ this
  have e : (x * s) ^ 2 = x ^ 2 * (x⁻¹ * s * x * s) := by rw [sq (x * s), sq x]; group
  rw [e]
  exact (g2Mul h K).range.mul_mem hsq ((g2Mul h K).range.mul_mem hn hs')

theorem g2_toral_largePrime (hK : ringChar K ≠ 2) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β)
    (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {P U : Subgroup (ModGL .G2 K)} [Finite U] (hPX : P ≤ toralCentralizer .G2 K a)
    (hUX : U ≤ toralCentralizer .G2 K a) (hPp : IsPGroup p P) (hU2 : IsPGroup 2 U)
    (hPU : ∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U) : ∀ x ∈ P, ∀ u ∈ U, x * u = u * x :=
  xlevel_largePrime hK (toralCentralizer .G2 K a) (g2Mul h K) (ker_g2Mul_central h)
    (fun g hg s hs => by
      have hs' : s ∈ rootSpan .G2 K (rootCharKernel a) := hS ▸ hs
      exact hS ▸ (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer_rootSpan a hg) s).1
        hs')
    (fun g hg => g2_sq_mem hK ha h hS hg) hp hp3 hPX hUX hPp hU2 hPU

end CFSG.RankThree.PartOne
