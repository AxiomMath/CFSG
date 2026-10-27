module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6LE3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeSideDatum_of_LE3_seven {G : Type} [Group G] [Finite G] {Bs K J : Subgroup G}
    {y : G} (hy : y ∈ Bs) (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) (hy1 : y ≠ 1)
    (hCard : Nat.card ↥Bs = 3 ^ 7) (hJ192 : Nat.card ↥(ggAutomizer J Bs) = 192)
    (hK3 : GGResLeviSideDatumLE3 3 Bs K J) : GGResTwoNodeSideDatum 3 Bs K J := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfixy := ggRC_automizer_fixes_y hy hKy
  obtain ⟨Λ, i1, i2, S, M, C, MJ, V, i3, i4, ι, φ, h, α, hS2, hS3, hWM, hC, hWMJ, hMJ, hlin,
    hrefl, hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hclosJ, hconj⟩ := hK3
  letI := i1; letI := i2; letI := i3; letI := i4
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let z : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hz0 : z ≠ 0 := by
    intro h0
    apply hy1
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := ι.injective (by simpa [z] using h0)
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by simpa using congrArg Additive.toMul h1
    exact congrArg Subtype.val h2
  have hzα : ∀ i, α i z = 0 := by
    intro i
    have hmem : φ i ∈ ggAutomizer K Bs := by
      rw [hclos]; exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfix : ggLin (p := 3) ι (φ i) z = z :=
      (ggLin_fix_iff (p := 3) ι (φ i) (⟨y, hy⟩ : ↥Bs)).mp (hfixy (φ i) hmem)
    have h3 := hlin i z
    rw [hfix] at h3
    have h1 : α i z • h i = 0 := sub_eq_self.mp h3.symm
    have h4 : α i z * (2 : ZMod 3) = 0 := by
      have := congrArg (α i) h1
      rw [map_smul, smul_eq_mul, hpair i i, hC.1 i, map_zero] at this
      simpa using this
    exact (mul_eq_zero.mp h4).resolve_right (by decide)
  have hfinrank : Module.finrank (ZMod 3) V = 7 := by
    have hVcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 7 := by rw [← hVcard, hcardV, hCard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
  have hle := ggPZ_card_le_finrank hp2 hWM hC h α hpair hz0 hzα
  have hm4 : 4 ≤ Fintype.card {j : Λ // j ∉ S} := by
    refine ggQ2s08_ce6_four_le_nodes hWMJ ?_
    rw [Nat.card_congr fJ.toEquiv]
    exact hJ192
  have hcardS : Fintype.card {j : Λ // j ∉ S} + S.card = Fintype.card Λ := by
    have h1 : Fintype.card {j : Λ // j ∈ S} = S.card := Fintype.card_coe S
    have h2 := Fintype.card_subtype_compl (fun j : Λ => j ∈ S)
    have h3 := Fintype.card_subtype_le (fun j : Λ => j ∈ S)
    omega
  have hn7 : Fintype.card Λ ≠ 7 := by
    intro h7
    have hdimn : Module.finrank (ZMod 3) V ≤ Fintype.card Λ := by omega
    rcases ggIntCartan_A_or_E6_of_finrank_le hWM hC hp2 h α hpair hz0 hzα hdimn with
      ⟨n, e, _, hpd, _⟩ | ⟨_, e, _⟩
    · have hcn : Fintype.card Λ = n := by
        rw [← Fintype.card_fin n]; exact (Fintype.card_congr e).symm
      omega
    · have hcn : Fintype.card Λ = 6 := by
        rw [← Fintype.card_fin 6]; exact (Fintype.card_congr e).symm
      omega
  have hS2' : S.card = 2 := by omega
  obtain ⟨b₁, b₂, hb, hSeq⟩ := Finset.card_eq_two.mp hS2'
  subst hSeq
  let e' : {j : Λ // j ∉ ({b₁, b₂} : Finset Λ)} ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} :=
    Equiv.subtypeEquivRight (fun j => by simp [not_or])
  refine ⟨Λ, i1, i2, b₁, b₂, M, C, MJ.reindex e', V, i3, i4, ι, φ, h, α, hb, hWM, hC,
    l05nBL_weyl_reindex hWMJ e', ?_, hlin, hrefl, hpair, ⟨f, hf⟩, hclos, ?_, ?_, ?_⟩
  · intro j j'
    rw [CoxeterMatrix.reindex_apply]
    exact hMJ _ _
  · refine ⟨(CoxeterMatrix.reindexGroupEquiv MJ e').trans fJ, fun j => ?_⟩
    rw [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_apply_simple, hfJ]
    rfl
  · rw [hclosJ]
    congr 1
    ext g
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨e' j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨e'.symm j, rfl⟩
  · intro t ht hrt
    obtain ⟨w, hw, j, hj⟩ := hconj t ht hrt
    exact ⟨w, hw, e' j, hj⟩

end CFSG.StandardType

end
