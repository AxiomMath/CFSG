module

public import CFSG.LocalAnalysis.StandardType.E8SevenLayerOrderCenter
public import CFSG.LocalAnalysis.StandardType.E8SevenFactorModels
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenLabelA2
public import CFSG.RankThree.PartOne.KE6.E8T3Layers
public import CFSG.RankThree.PartOne.KE6.E8T3Seven
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate1952
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.E7FourStabBase

public noncomputable section

namespace CFSG.StandardType

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE6
open scoped MatrixGroups

set_option maxRecDepth 100000 in
theorem e8T3_supports_of_card_seven : ∀ J ∈ e8T3Supports, (e8PhiCard J = 30 ∨ e8PhiCard J = 72) →
    J = {0, 1, 2, 3, 4, 5} ∨ J = {1, 2, 3, 4, 6, 7} := by
  decide +kernel

section Dispatch

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {k : Type} [Field k] [Algebra k L]
  [IsAlgClosure k L]

theorem dispatch_E6_seven_with_model (hE6 : E6Layer Tag.E8) (hk : Nat.card k = 2 ^ 1) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧
      7 ^ 2 ∣ Nat.card (P ()) ∧
      (∀ z ∈ P (), (∀ w ∈ P (), z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      P () = rootSpan Tag.E8 L ((fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1))) := by
  classical
  have hSeq : S = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    rw [← preimage_eq_image_inv]
    exact set_eq_preimage u hS
  have h1 : ∀ α : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      (u * e8T3W * u⁻¹) • α := fun α => by
    have := conj_smul_eq (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1) hnW u⁻¹ α
    simpa using this
  have hmaps : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α ∈
        parabolicRoots Tag.E8 (e6Nodes Tag.E8) := fun α hα => by
    rw [h1]
    exact hmapsT α hα
  have hrelW : ∀ x : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) •
      ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • x +
        ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • x + x = 0 := fun x => by
    simp only [h1]
    exact hrelT x
  obtain ⟨P, hfam, hPeq, -⟩ := e8_e6_family hE6 (ℓ := 2) (f := 1) le_rfl hk (Or.inl rfl) u⁻¹ n
    hnm hnC hmaps (fun α hα => by rw [one_smul]; exact hrelW α)
  subst hSeq
  refine ⟨P, hfam, ?_, ?_, hPeq⟩
  · rw [hPeq]
    exact seven_sq_dvd_card_rootSpan_image_inf_twistedFixedPoints u⁻¹ n hnm (Or.inl rfl) hmaps
      hrelW
  · refine eq_one_of_pow_seven_of_central_of_centralizer u⁻¹ (Or.inl rfl) (hfam.2.2.1 ()) ?_
    intro y hy hyc
    exact (Subgroup.mem_inf.1 (hfam.2.2.2.2.2.2 y (Subgroup.mem_sup_right (hfam.2.2.1 () hy))
      (hfam.2.2.2.1 () hy) (fun _ w hw => hyc w hw))).2

theorem dispatch_E6_seven (hE6 : E6Layer Tag.E8) (hk : Nat.card k = 2 ^ 1) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧
      7 ^ 2 ∣ Nat.card (P ()) ∧
      ∀ z ∈ P (), (∀ w ∈ P (), z * w = w * z) → z ^ 7 = 1 → z = 1  := by
  obtain ⟨P, hfam, hcard, hcent, _⟩ :=
    dispatch_E6_seven_with_model hE6 hk n hnm hnC hnW u hS hrelT hmapsT
  exact ⟨P, hfam, hcard, hcent⟩

theorem dispatch_D4A2_seven_with_models (hD4 : D4TrialityLayer Tag.E8) (hk : Nat.card k = 2 ^ 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S =
      parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))})
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))},
      (u * e8T3W * u⁻¹) • β ∈
        parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))}) :
    ∃ P : Unit ⊕ Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧
      7 ^ 2 ∣ Nat.card (P (Sum.inl ())) ∧
      (∀ z ∈ P (Sum.inl ()), (∀ w ∈ P (Sum.inl ()), z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      (∃ a b c : Fin Tag.E8.rank, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        a.val ∈ ({1, 2, 4} : Set ℕ) ∧ b.val ∈ ({1, 2, 4} : Set ℕ) ∧
        c.val ∈ ({1, 2, 4} : Set ℕ) ∧
        (∃ u' ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
          ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
            ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
              u' • permLattice (List.formPerm [a, b, c]) α) ∧
        P (Sum.inl ()) = rootSpan Tag.E8 L
          ((fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) ∧
      Nonempty (P (Sum.inr ()) ≃* SL(3, k)) := by
  classical
  have hcols := e8T3_cols_D4A2 hrelT (by rw [e8T3_coe_d4a2]; exact hmapsT)
  obtain ⟨hcD, hcA⟩ := cols_D4A2_split hcols
  obtain ⟨a, b, c, hab, hbc, hac, ha, hb, hc, u', hu', hcert⟩ :=
    e8T3_D4_cert hcD (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
  have h67 : ((6 : Fin Tag.E8.rank), (7 : Fin Tag.E8.rank)) ∈ e8Edges := by decide
  obtain ⟨ent, hent, h1, h2⟩ := e8A2Trans_edges (6, 7) h67
  have hm := maps_of_colsA2 (e8Edges_ne _ h67) hcA
  have hSeq := set_eq_preimage u hS
  have hSu : S = {α : V8 | u • α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8)} ∪
      {α : V8 | u • α ∈ parabolicRoots Tag.E8 {i | i ∈ ([6, 7] : List (Fin Tag.E8.rank))}} := by
    rw [hSeq]
    ext α
    simp only [Set.mem_union, Set.mem_ofPred_eq, d4Nodes_eq_list, mem_parabolicRoots_iff_E8]
    constructor
    · intro h
      exact e8D4A2_union_fwd _ h
    · rintro (h | h)
      · exact e8D4A2_union_bwd.1 _ h
      · exact e8D4A2_union_bwd.2 _ h
  have hS₂ : (fun γ => u • γ) '' {α : V8 | u • α ∈ parabolicRoots Tag.E8
      {i | i ∈ ([6, 7] : List (Fin Tag.E8.rank))}} = parabolicRoots Tag.E8
        {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))} := by
    rw [image_preimage_smul]
    simp only [h1, h2]
  have hv₂ := exists_v_of_A2 hent hS₂
  have hSv₂ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2),
      e8T3We 1 • α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
    rw [← hv₂]
    exact stab_preimage (Or.inl rfl) u _ hm (fun β hβ => parabolicRoots_zsmul hβ (Or.inl rfl))
  have hSn₂ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2),
      -α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
    rw [← hv₂]
    exact neg_preimage _ u (fun β hβ => parabolicRoots_neg hβ)
  have horth : ∀ α ∈ (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      ∀ β ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2),
        iform (τ := Tag.E8) α β = 0 := by
    intro α hα β hβ
    rw [← preimage_eq_image_inv] at hα
    rw [← hv₂] at hβ
    have hxa : u • α ∈ e8RootsIn [1, 2, 3, 4] := by
      have : u • α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8) := hα
      rw [d4Nodes_eq_list] at this
      exact (mem_parabolicRoots_iff_E8 _).1 this
    have hyb : u • β ∈ e8RootsIn [6, 7] := (mem_parabolicRoots_iff_E8 _).1 hβ
    rw [← iform_smul u]
    exact e8D4A2_orth _ hxa _ hyb
  have hSeq' : S = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) ∪
      sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
    rw [hSu, hv₂, preimage_eq_image_inv]
  have h1ε : ∀ α : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      (1 : ℤ) • ((u * e8T3W * u⁻¹) • α) := fun α => by
    have := conj_smul_eq (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1) hnW u⁻¹ α
    simpa using this
  have h1 : ∀ α : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      (u * e8T3W * u⁻¹) • α := fun α => by rw [h1ε, one_smul]
  have hrelW : ∀ x : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) •
      ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • x +
        ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • x + x = 0 := fun x => by
    simp only [h1]
    exact hrelT x
  have hsuppD : ∀ j ∈ ([1, 2, 3, 4] : List (Fin Tag.E8.rank)), ∀ i,
      i ∉ ([1, 2, 3, 4] : List (Fin Tag.E8.rank)) → colT (u * e8T3W * u⁻¹) j i = 0 := by
    intro j hj i hi
    refine d4Cols_supp _ hcD (colT (u * e8T3W * u⁻¹) j) ?_ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    rcases hj with rfl | rfl | rfl | rfl <;> simp
  have hmapsD0 := maps_of_supp (T := u * e8T3W * u⁻¹) [1, 2, 3, 4] (by decide) hsuppD
  have hmapsD : ∀ β ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • β ∈
        parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
    intro β hβ
    rw [h1]
    rw [d4Nodes_eq_list] at hβ ⊢
    exact hmapsD0 β hβ
  obtain ⟨P₁, hP₁, hfac₁, -⟩ := e8_d4_factor hD4 (ℓ := 2) (f := 1) le_rfl hk u⁻¹ n hnm hnC a b c
    hab hbc hac ha hb hc ⟨u', hu', fun α hα => by rw [h1ε]; exact hcert α hα⟩
  obtain ⟨P₂, hP₂, hfac₂, hmodel₂, -⟩ := layer_A2_with_model (ℓ := 2) (f := 1) le_rfl hk (Or.inl rfl)
    (fun h => absurd h (by norm_num)) (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) n hnm hnC
    hnW hSv₂ hSn₂
  have hroots : ∀ r ∈ (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      IsRoot Tag.E8 r := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 u⁻¹
  rw [hSeq']
  refine ⟨Sum.elim (fun _ => P₁) (fun _ => P₂),
    sigmaFactor_union hroots (sigmaSetE8_isRoot _) horth hfac₁ hfac₂, ?_, ?_, ?_, ?_⟩
  · show 7 ^ 2 ∣ Nat.card P₁
    rw [hP₁]
    exact seven_sq_dvd_card_rootSpan_image_inf_twistedFixedPoints u⁻¹ n hnm (Or.inr rfl) hmapsD
      hrelW
  · show ∀ z ∈ P₁, (∀ w ∈ P₁, z * w = w * z) → z ^ 7 = 1 → z = 1
    refine eq_one_of_pow_seven_of_central_of_centralizer u⁻¹ (Or.inr rfl) (hfac₁.le_root ()) ?_
    intro y hy hyc
    exact (hfac₁.thetaFree y (Subgroup.mem_sup_right (hfac₁.le_root () hy))
      (fun _ w hw => hyc w hw)).2
  · exact ⟨a, b, c, hab, hbc, hac, ha, hb, hc,
      ⟨u', hu', fun α hα => by rw [h1ε]; exact hcert α hα⟩, hP₁⟩
  · exact hmodel₂ rfl

theorem dispatch_D4A2_seven (hD4 : D4TrialityLayer Tag.E8) (hk : Nat.card k = 2 ^ 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S =
      parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))})
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))},
      (u * e8T3W * u⁻¹) • β ∈
        parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))}) :
    ∃ P : Unit ⊕ Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧
      7 ^ 2 ∣ Nat.card (P (Sum.inl ())) ∧
      ∀ z ∈ P (Sum.inl ()), (∀ w ∈ P (Sum.inl ()), z * w = w * z) → z ^ 7 = 1 → z = 1  := by
  obtain ⟨P, hfam, hcard, hcent, _, _⟩ :=
    dispatch_D4A2_seven_with_models hD4 hk n hnm hnC hnW u hS hrelT hmapsT
  exact ⟨P, hfam, hcard, hcent⟩

theorem e8T3_seven_layers (hD4 : D4TrialityLayer Tag.E8) (hE6 : E6Layer Tag.E8)
    (hk : Nat.card k = 2 ^ 1) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) (J : Finset (Fin Tag.E8.rank)) (hJ : J ≠ Finset.univ) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)))
    (hSneg : ∀ α ∈ S, -α ∈ S) (hSw : ∀ α ∈ S, e8T3We 1 • α ∈ S)
    (hcard : S.ncard = 30 ∨ S.ncard = 72) :
    ∃ (ι' : Type) (P : ι' → Subgroup (ModGL Tag.E8 L)) (i₀ : ι'),
      Finite ι' ∧ (Nat.card ι' = 1 ∨ Nat.card ι' = 2) ∧
      IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧ 7 ^ 2 ∣ Nat.card (P i₀) ∧
        ∀ z ∈ P i₀, (∀ w ∈ P i₀, z * w = w * z) → z ^ 7 = 1 → z = 1 := by
  classical
  have hε : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hS3 : ∀ α ∈ S, e8T3W • α ∈ S := stab_of_We hε hSneg hSw
  have hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0 :=
    fun x => rel_conj e8T3W_rel u x
  have hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)) := by
    intro β hβ
    rw [← hS] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    show (u * e8T3W * u⁻¹) • u • α ∈ _
    rw [conj_smul_apply, ← hS]
    exact ⟨_, hS3 α hα, rfl⟩
  have hsup := e8T3_supports hJ hrelT hmapsT
  have hcount : e8PhiCard J = 30 ∨ e8PhiCard J = 72 := by
    rw [← ncard_parabolicRoots_E8, ← hS, Set.ncard_image_of_injective _ (MulAction.injective u)]
    exact hcard
  rcases e8T3_supports_of_card_seven J hsup hcount with rfl | rfl
  · obtain ⟨P, hfam, hA, hB⟩ := dispatch_E6_seven hE6 hk n hnm hnC hnW u
      (by rw [← e8T3_coe_e6]; exact hS) hrelT (by rw [← e8T3_coe_e6]; exact hmapsT)
    exact ⟨Unit, P, (), inferInstance, Or.inl (by simp), hfam, hA, hB⟩
  · obtain ⟨P, hfam, hA, hB⟩ := dispatch_D4A2_seven hD4 hk n hnm hnC hnW u
      (by rw [← e8T3_coe_d4a2]; exact hS) hrelT (by rw [← e8T3_coe_d4a2]; exact hmapsT)
    exact ⟨Unit ⊕ Unit, P, Sum.inl (), inferInstance, Or.inr (by simp), hfam, hA, hB⟩

section Labels


theorem dispatch_E6_seven_with_labels (hE6 : E6Layer Tag.E8) (hk : Nat.card k = 2 ^ 1) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧
      7 ^ 2 ∣ Nat.card (P ()) ∧
      (∀ z ∈ P (), (∀ w ∈ P (), z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      GGHasLabel ⟨.E6, 0, 1⟩ (P () ⧸ Subgroup.center (P ()))  := by
  obtain ⟨P, hfam, hcard, hcent, hP⟩ :=
    dispatch_E6_seven_with_model hE6 hk n hnm hnC hnW u hS hrelT hmapsT
  have hπ : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We 1 :=
    ext_single fun i => hnW (Pi.single i 1)
  have h3 := E8SevenModels.not_three_dvd_center_sigma_singleton n hnm hπ P hfam
  have h1 : ∀ α : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      (u * e8T3W * u⁻¹) • α := fun α => by
    have h := conj_smul_eq (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1) hnW u⁻¹ α
    simpa using h
  have hmaps : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • β ∈
        parabolicRoots Tag.E8 (e6Nodes Tag.E8) := fun β hβ => by
    rw [h1]
    exact hmapsT β hβ
  exact ⟨P, hfam, hcard, hcent,
    E8SevenModels.ggHasLabel_transported_e6_layer u⁻¹ n hnm hmaps hP h3⟩

theorem dispatch_D4A2_seven_with_labels (hD4 : D4TrialityLayer Tag.E8) (hk : Nat.card k = 2 ^ 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S =
      parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))})
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))},
      (u * e8T3W * u⁻¹) • β ∈
        parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))}) :
    ∃ P : Unit ⊕ Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧
      7 ^ 2 ∣ Nat.card (P (Sum.inl ())) ∧
      (∀ z ∈ P (Sum.inl ()), (∀ w ∈ P (Sum.inl ()), z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      GGHasLabel ⟨.triD4, 0, 1⟩ (P (Sum.inl ()) ⧸ Subgroup.center (P (Sum.inl ()))) ∧
      GGHasLabel ⟨.A, 2, 1⟩ (P (Sum.inr ()) ⧸ Subgroup.center (P (Sum.inr ())))  := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  obtain ⟨P, hfam, hcard, hcent, hD4model, ⟨eA⟩⟩ :=
    dispatch_D4A2_seven_with_models hD4 hk n hnm hnC hnW u hS hrelT hmapsT
  obtain ⟨a, b, c, hab, hbc, hac, ha, hb, hc, hact, hP⟩ := hD4model
  have hk2 : Nat.card k = 2 := by simpa using hk
  exact ⟨P, hfam, hcard, hcent,
    E8SevenModels.ggHasLabel_transported_d4_layer_two (k := k) hk2 u⁻¹ a b c
      hab hbc hac ha hb hc n hnm hact hP,
    E6TwoSeven.ggHasLabel_A21_of_mulEquiv_SL3 hk2 eA⟩

theorem e8T3_seven_layers_with_labels (hD4 : D4TrialityLayer Tag.E8) (hE6 : E6Layer Tag.E8)
    (hk : Nat.card k = 2 ^ 1) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We 1 • x)
    (u : WeylGroup Tag.E8) (J : Finset (Fin Tag.E8.rank)) (hJ : J ≠ Finset.univ) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)))
    (hSneg : ∀ α ∈ S, -α ∈ S) (hSw : ∀ α ∈ S, e8T3We 1 • α ∈ S)
    (hcard : S.ncard = 30 ∨ S.ncard = 72) :
    ∃ (ι' : Type) (P : ι' → Subgroup (ModGL Tag.E8 L)) (i₀ : ι'),
      Finite ι' ∧ (Nat.card ι' = 1 ∨ Nat.card ι' = 2) ∧
      IsSigmaFamily n (iterateFrobenius L 2 1) S P ∧ 7 ^ 2 ∣ Nat.card (P i₀) ∧
        (∀ z ∈ P i₀, (∀ w ∈ P i₀, z * w = w * z) → z ^ 7 = 1 → z = 1) ∧
      ∀ i, ∃ lab : CFSG.Assembly.LargeEvenLabel,
        lab ∈ [⟨.E6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.A, 2, 1⟩] ∧
        GGHasLabel lab (P i ⧸ Subgroup.center (P i))  := by
  classical
  have hε : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hS3 : ∀ α ∈ S, e8T3W • α ∈ S := stab_of_We hε hSneg hSw
  have hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0 :=
    fun x => rel_conj e8T3W_rel u x
  have hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)) := by
    intro β hβ
    rw [← hS] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    show (u * e8T3W * u⁻¹) • u • α ∈ _
    rw [conj_smul_apply, ← hS]
    exact ⟨_, hS3 α hα, rfl⟩
  have hsup := e8T3_supports hJ hrelT hmapsT
  have hcount : e8PhiCard J = 30 ∨ e8PhiCard J = 72 := by
    rw [← ncard_parabolicRoots_E8, ← hS, Set.ncard_image_of_injective _ (MulAction.injective u)]
    exact hcard
  rcases e8T3_supports_of_card_seven J hsup hcount with rfl | rfl
  · obtain ⟨P, hfam, hA, hB, hlabel⟩ := dispatch_E6_seven_with_labels hE6 hk n hnm hnC hnW u
      (by rw [← e8T3_coe_e6]; exact hS) hrelT (by rw [← e8T3_coe_e6]; exact hmapsT)
    refine ⟨Unit, P, (), inferInstance, Or.inl (by simp), hfam, hA, hB, ?_⟩
    intro i
    cases i
    exact ⟨⟨.E6, 0, 1⟩, by simp, hlabel⟩
  · obtain ⟨P, hfam, hA, hB, hD, hA2⟩ := dispatch_D4A2_seven_with_labels hD4 hk n hnm hnC hnW u
      (by rw [← e8T3_coe_d4a2]; exact hS) hrelT (by rw [← e8T3_coe_d4a2]; exact hmapsT)
    refine ⟨Unit ⊕ Unit, P, Sum.inl (), inferInstance, Or.inr (by simp), hfam, hA, hB, ?_⟩
    intro i
    rcases i with ⟨⟩ | ⟨⟩
    · exact ⟨⟨.triD4, 0, 1⟩, by simp, hD⟩
    · exact ⟨⟨.A, 2, 1⟩, by simp, hA2⟩

end Labels

end Dispatch

end CFSG.StandardType
