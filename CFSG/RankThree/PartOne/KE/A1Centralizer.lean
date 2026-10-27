module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal)
open scoped Pointwise

section Stabilizer

variable {τ : Tag} {L : Type} [Field L]

theorem rootCharStabilizer_subset_closure {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    exact ha1 (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have hord0 : orderOf (a i0) = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hap i0)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hi0
    · exact h
  have hprim : IsPrimitiveRoot ((a i0 : Lˣ) : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hord0)
  have hexp : ∀ i, ∃ n : ℕ, a i = (a i0) ^ n := fun i => by
    have hi : ((a i : Lˣ) : L) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  intro w hw
  have hmem : w ∈ dualWeylStabilizer (fun i => (e i : ZMod p)) := fun y =>
    (rootChar_eq_rootChar_iff hord0 e a he (w • y) y).1 (hw y)
  rw [dualWeylStabilizer_eq_closure hord] at hmem
  have hker : rootKernel (fun i => (e i : ZMod p)) = rootCharKernel a := by
    ext α
    have h := rootChar_eq_rootChar_iff hord0 e a he α 0
    rw [rootChar_zero] at h
    have h0 : charVal (fun i => (e i : ZMod p)) (0 : Fin τ.rank → ℤ) = 0 := by simp [charVal]
    rw [h0] at h
    exact and_congr_right fun _ => h.symm
  rw [hker] at hmem
  exact hmem

end Stabilizer

section Centralizer

variable {τ : Tag} {L : Type} [Field L]

theorem torusGroup_le_normalizer_rootRankOneGroup {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    torusGroup τ L ≤ Subgroup.normalizer (rootRankOneGroup τ L θ : Set (ModGL τ L)) := by
  intro h hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hconj : ∀ b : Fin τ.rank → Lˣ, ∀ x ∈ rootRankOneGroup τ L θ,
      rootDiagUnit τ b * x * (rootDiagUnit τ b)⁻¹ ∈ rootRankOneGroup τ L θ := by
    intro b
    rintro _ ⟨A, rfl⟩
    rw [rootDiagUnit_conj_rootSL2 b hθ]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj a x, fun hx => ?_⟩
  have h1 := hconj a⁻¹ _ hx
  have hinv : rootDiagUnit τ a⁻¹ = (rootDiagUnit τ a)⁻¹ := (rootDiagUnitHom τ L).map_inv a
  rw [hinv, inv_inv] at h1
  convert h1 using 1
  group

theorem rootRankOneGroup_neg {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    rootRankOneGroup τ L (-θ) = rootRankOneGroup τ L θ := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ L (IsRoot.neg hθ)).1,
    (exceptional_Lang_root_rank_one_torus_transport τ L hθ).1, neg_neg, sup_comm]

theorem toralCentralizer_le_sup_rootRankOne {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hker : rootCharKernel a ⊆ {θ, -θ}) :
    toralCentralizer τ L a ≤ torusGroup τ L ⊔ rootRankOneGroup τ L θ := by
  classical
  set Q := rootRankOneGroup τ L θ with hQ
  set H := torusGroup τ L with hH
  have hQsplit : Q = rootSubgroup τ L θ ⊔ rootSubgroup τ L (-θ) :=
    (exceptional_Lang_root_rank_one_torus_transport τ L hθ).1
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ L a).2.2.2]
  refine sup_le (sup_le le_sup_left ?_) ?_
  ·
    have hθQ : rootSubgroup τ L θ ≤ Q := by rw [hQsplit]; exact le_sup_left
    have hnθQ : rootSubgroup τ L (-θ) ≤ Q := by rw [hQsplit]; exact le_sup_right
    have hspan : rootSpan τ L {θ, -θ} ≤ Q := iSup₂_le fun α hα => by
      rcases hα with rfl | hα
      · exact hθQ
      · rw [Set.mem_singleton_iff] at hα
        subst hα
        exact hnθQ
    exact ((rootSpan_mono hker).trans hspan).trans le_sup_right
  ·
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hwcl := rootCharStabilizer_subset_closure hp hord hap ha1 hw
    let N := monomialSubgroup τ L
    let π := weylQuotientHom τ L
    let Wsub : Subgroup (WeylGroup τ) := ((H ⊔ Q).subgroupOf N).map π
    have hgen : ∀ α, IsRoot τ α → (α = θ ∨ α = -θ) → rootReflection α ∈ Wsub := by
      intro α hα hαθ
      obtain ⟨hmem, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hα).2.2.1 1
      refine ⟨⟨rootWeylSL2 τ L α 1, hmem⟩, ?_, hπ⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_sup_right ?_
      have hQα : rootRankOneGroup τ L α = Q := by
        rcases hαθ with rfl | rfl
        · rfl
        · exact rootRankOneGroup_neg hθ
      rw [← hQα]
      exact ⟨_, rfl⟩
    have hclW : Subgroup.closure {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} ≤ Wsub := by
      rw [Subgroup.closure_le]
      rintro _ ⟨α, hα, rfl⟩
      exact hgen α hα.1 (by simpa using hker hα)
    obtain ⟨m, hm, hmπ⟩ := hclW hwcl
    have hcanN : canonicalRep (coxeterSystem τ) L w ∈ N := canonicalRep_mem_monomialSubgroup L w
    obtain ⟨ρ, -, hρ, -, -, hρker⟩ := (Weyl_normalizer_quotient τ L).2.1
    have hρπ : ∀ g : N, ρ g = π g := fun g =>
      (hρ g).unique (mapsRootLines_weylQuotientHom g)
    have hcan : π ⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ = w :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)
    have hker1 : (⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ * m⁻¹ : N) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρπ, hρπ, hcan, hmπ, mul_inv_cancel]
    rw [hρker, Subgroup.mem_subgroupOf] at hker1
    have hker2 : canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹ ∈ H := hker1
    have hmQ : (m : ModGL τ L) ∈ H ⊔ Q := hm
    have hc : canonicalRep (coxeterSystem τ) L w =
        (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) := by group
    have h3 : (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) ∈
        H ⊔ Q := mul_mem (Subgroup.mem_sup_left hker2) hmQ
    rw [← hc] at h3
    exact h3

theorem mem_torus_mul_rootRankOne_of_commute {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hker : rootCharKernel a ⊆ {θ, -θ})
    {y : ModGL τ L} (hy : y ∈ adjointGroup τ L)
    (hcomm : y * rootDiagUnit τ a = rootDiagUnit τ a * y) :
    y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L θ : Set (ModGL τ L)) := by
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootRankOneGroup hθ)]
  refine toralCentralizer_le_sup_rootRankOne hp hord hap ha1 hθ hker ?_
  exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩

end Centralizer

end CFSG.RankThree.PartOne.KE
