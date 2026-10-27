module

public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.Sporadic.Recognition.McLCentralizer
public import CFSG.Sporadic.Recognition.McLASThreeFacts

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.RankThree.Native

theorem card_cent_conj {M : Type*} [Group M] {P : Subgroup M} [Finite M] {g t : M}
    (hg : g ∈ P) :
    Nat.card ↥(P ⊓ centralizer ({g * t * g⁻¹} : Set M)) =
      Nat.card ↥(P ⊓ centralizer ({t} : Set M)) := by
  rw [inf_centralizer_conj P hg t]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem ncard_orderOf_mclP
    {m : ℕ} (hm : 0 < m) :
    ({y : Equiv.Perm (Fin 275) | y ∈ mclP ∧ orderOf y = m}).ncard =
      countOrd PairMcL.bs m PairMcL.blocks := by
  have h := mcl_card_order m hm
  rw [← mclP_eq_original, card_orderOf_coe] at h
  rw [← h, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun y => y ∈ mclP)
    (fun y => orderOf y = m))).symm

theorem class_union_eq {M : Type*} [Group M] [Finite M] {P : Subgroup M} {p : ℕ} {t₁ t₂ : M}
    (h₁ : t₁ ∈ P) (h₂ : t₂ ∈ P) (o₁ : orderOf t₁ = p) (o₂ : orderOf t₂ = p)
    (hdisj : Disjoint (conjClass P t₁) (conjClass P t₂)) {N : ℕ}
    (hN : ({y : M | y ∈ P ∧ orderOf y = p}).ncard = N)
    (hsum : (conjClass P t₁).ncard + (conjClass P t₂).ncard = N) :
    conjClass P t₁ ∪ conjClass P t₂ = {y : M | y ∈ P ∧ orderOf y = p} := by
  have hsub : conjClass P t₁ ∪ conjClass P t₂ ⊆ {y : M | y ∈ P ∧ orderOf y = p} := by
    have hc : ∀ {t : M}, t ∈ P → orderOf t = p →
        conjClass P t ⊆ {y : M | y ∈ P ∧ orderOf y = p} := by
      intro t ht hot y hy
      obtain ⟨g, hg, rfl⟩ := hy
      refine ⟨P.mul_mem (P.mul_mem hg ht) (P.inv_mem hg), ?_⟩
      rw [← hot]
      exact (MulAut.conj g).orderOf_eq t
    exact Set.union_subset (hc h₁ o₁) (hc h₂ o₂)
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [hN, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hsum]

theorem disjoint_conjClass_of_card_ne {M : Type*} [Group M] [Finite M] {P : Subgroup M}
    {t₁ t₂ : M}
    (hne : Nat.card ↥(P ⊓ centralizer ({t₁} : Set M)) ≠
      Nat.card ↥(P ⊓ centralizer ({t₂} : Set M))) :
    (¬ ∃ g ∈ P, t₂ = g * t₁ * g⁻¹) ∧ Disjoint (conjClass P t₁) (conjClass P t₂) := by
  have hnc : ¬ ∃ g ∈ P, t₂ = g * t₁ * g⁻¹ := by
    rintro ⟨g, hg, hgt⟩
    have := card_cent_conj (P := P) (t := t₁) hg
    rw [← hgt] at this
    exact hne this.symm
  refine ⟨hnc, ?_⟩
  rw [Set.disjoint_left]
  rintro y ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, hy⟩
  apply hnc
  refine ⟨g₂⁻¹ * g₁, P.mul_mem (P.inv_mem hg₂) hg₁, ?_⟩
  calc t₂ = g₂⁻¹ * (g₂ * t₂ * g₂⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₁ * t₁ * g₁⁻¹) * g₂ := by rw [← hy]
    _ = g₂⁻¹ * g₁ * t₁ * (g₂⁻¹ * g₁)⁻¹ := by group

noncomputable abbrev three₁ : Equiv.Perm (Fin 275) := tp 275 (threeTbl 0)

noncomputable abbrev three₂ : Equiv.Perm (Fin 275) := tp 275 (threeTbl 3)

theorem mclP_order_three_classes (h : ThreeFacts) :
    three₁ ∈ mclP ∧ three₂ ∈ mclP ∧ orderOf three₁ = 3 ∧ orderOf three₂ = 3 ∧
      Nat.card ↥(mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275)))) = 29160 ∧
      Nat.card ↥(mclP ⊓ centralizer ({three₂} : Set (Equiv.Perm (Fin 275)))) = 972 ∧
      (conjClass mclP three₁).ncard = 30800 ∧ (conjClass mclP three₂).ncard = 924000 ∧
      (¬ ∃ g ∈ mclP, three₂ = g * three₁ * g⁻¹) ∧
      ∀ y ∈ mclP, orderOf y = 3 →
        (∃ g ∈ mclP, y = g * three₁ * g⁻¹) ∨ ∃ g ∈ mclP, y = g * three₂ * g⁻¹ := by
  have c₁ := h.row₁.cent
  have c₂ := h.row₂.cent
  have k₁ := h.row₁.cls
  have k₂ := h.row₂.cls
  have m₁ := h.row₁.mem
  have m₂ := h.row₂.mem
  have o₁ := h.row₁.order
  have o₂ := h.row₂.order
  have hcov := h.cover
  dsimp only [threeRow₁, threeRow₂] at c₁ c₂ k₁ k₂ m₁ m₂ o₁ o₂ hcov
  obtain ⟨hnc, -⟩ := disjoint_conjClass_of_card_ne (P := mclP) (t₁ := three₁)
    (t₂ := three₂) (by rw [c₁, c₂]; norm_num)
  exact ⟨m₁, m₂, o₁, o₂, c₁, c₂, k₁, k₂, hnc, hcov⟩

theorem card_inf_mul_two {M : Type*} [Group M] [Finite M] {P R C : Subgroup M}
    (hidx : P.relIndex R = 2) (hCR : C ≤ R) {o : M} (ho : o ∈ C) (hoP : o ∉ P) :
    Nat.card ↥(P ⊓ C) * 2 = Nat.card C := by
  have hmul := Subgroup.relIndex_mul_card (H := P) (K := C)
  have hle : P.relIndex C ≤ 2 := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right hCR (by rw [hidx]; norm_num)
  have hne1 : P.relIndex C ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hoP (h ho)
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hne0 : P.relIndex C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    omega
  have h2 : P.relIndex C = 2 := by omega
  rw [h2] at hmul
  omega

noncomputable abbrev five₁ : Equiv.Perm (Fin 275) := mcl275FiveLine 1

noncomputable abbrev five₂ : Equiv.Perm (Fin 275) := mcl275FiveLine 0

theorem sift_of_mem_mcl275P
    {g : Array ℕ} {G : Equiv.Perm (Fin 275)} (hG : CFSG.Monster.B.Co2.Rep 275 g G)
    (h : G ∈ mcl275P) : CFSG.Monster.B.Co2.Native.siftA 275 mcl275PLevels PairMcL.baseArr 0 g =
      true := by
  rw [mcl275P_eq, mclP_eq_original] at h
  exact (CFSG.Certificates.siftA_iff_mem_originalSubgroup mclChainArrays (by norm_num)
    PairMcL.chain_check.1 hG).2 h

theorem exists_outer_of_fiveOuter
    {gs : Array (Array ℕ)} (hvalid : ∀ k < gs.size, validA 275 gs[k]! = true)
    (h : (List.range gs.size).any
      (fun k => !CFSG.Monster.B.Co2.Native.siftA 275 mcl275PLevels PairMcL.baseArr 0 gs[k]!) =
        true) :
    ∃ o ∈ Subgroup.closure (permsA 275 gs), o ∉ mcl275P := by
  rw [List.any_eq_true] at h
  obtain ⟨k, hk, hs⟩ := h
  rw [List.mem_range] at hk
  refine ⟨CFSG.Monster.B.Co2.permOfArr 275 gs[k]!, Subgroup.subset_closure (mem_permsA hk),
    fun hmem => ?_⟩
  have := sift_of_mem_mcl275P (rep_of_validA (hvalid k hk)) hmem
  rw [this] at hs
  exact Bool.false_ne_true hs

theorem mclP_order_five_classes
    (h : fiveOuterCheck = true) :
    five₁ ∈ mclP ∧ five₂ ∈ mclP ∧ orderOf five₁ = 5 ∧ orderOf five₂ = 5 ∧
      Nat.card ↥(mclP ⊓ centralizer ({five₁} : Set (Equiv.Perm (Fin 275)))) = 750 ∧
      Nat.card ↥(mclP ⊓ centralizer ({five₂} : Set (Equiv.Perm (Fin 275)))) = 25 ∧
      (conjClass mclP five₁).ncard = 1197504 ∧ (conjClass mclP five₂).ncard = 35925120 ∧
      (¬ ∃ g ∈ mclP, five₂ = g * five₁ * g⁻¹) ∧
      ∀ y ∈ mclP, orderOf y = 5 →
        (∃ g ∈ mclP, y = g * five₁ * g⁻¹) ∨ ∃ g ∈ mclP, y = g * five₂ * g⁻¹ := by
  obtain ⟨⟨hQP, -, -, -⟩, -, -, -, -, ⟨hC0, hC0c⟩, ⟨hC1, hC1c⟩, -, -⟩ :=
    R3E_McL_full_five_centralizer_structures
  simp only [fiveOuterCheck, Bool.and_eq_true] at h
  obtain ⟨o₀, ho₀, ho₀P⟩ := exists_outer_of_fiveOuter
    (fun k hk => enumOK_gens_valid mcl275FiveC0_enum hk) h.1
  obtain ⟨o₁, ho₁, ho₁P⟩ := exists_outer_of_fiveOuter
    (fun k hk => enumOK_gens_valid mcl275FiveC1_enum hk) h.2
  have hPR : mcl275P ≤ mcl275R := by
    rw [← mcl275R_eq_sup]; exact le_sup_left
  have hcardR : Nat.card mclR = 1796256000 := by
    obtain ⟨-, -, -, -, -, -, -, -, hR, -⟩ := mcl_normalizing_model
    exact hR
  have hidx : mcl275P.relIndex mcl275R = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := mcl275P) (K := mcl275R)
    have hc : Nat.card ↥mcl275R = 1796256000 := by rw [mcl275R_eq]; exact hcardR
    have hc' : Nat.card ↥(mcl275P ⊓ mcl275R) = 898128000 := by
      rw [inf_of_le_left hPR, mcl275P_eq]; exact card_mclP
    rw [hc, hc'] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 898128000)
      (h1.trans (by norm_num : 1796256000 = 2 * 898128000))
  have hline_mem : ∀ j : Fin 31, mcl275FiveLine j ∈ mcl275P := fun j =>
    mcl275FiveQ_le_P (linesOK_mem mcl275FiveKeys_lt mcl275Five_lines_ok j)
  have hline_ord : ∀ j : Fin 31, orderOf (mcl275FiveLine j) = 5 := fun j =>
    linesOK_orderOf mcl275Five_lines_ok j
  have hcentR : ∀ (j : Fin 31) (C : Subgroup (Equiv.Perm (Fin 275))),
      C = centralizer {mcl275FiveLine j} ⊓ mcl275R → C ≤ mcl275R := fun j C hC => by
    rw [hC]; exact inf_le_right
  have hcentP : ∀ (j : Fin 31) (C : Subgroup (Equiv.Perm (Fin 275))),
      C = centralizer {mcl275FiveLine j} ⊓ mcl275R →
        mcl275P ⊓ C = mcl275P ⊓ centralizer {mcl275FiveLine j} := fun j C hC => by
    rw [hC]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxP, hxc, -⟩
      exact ⟨hxP, hxc⟩
    · rintro ⟨hxP, hxc⟩
      exact ⟨hxP, hxc, hPR hxP⟩
  have p₁ : Nat.card ↥(mclP ⊓ centralizer ({five₁} : Set (Equiv.Perm (Fin 275)))) = 750 := by
    have := card_inf_mul_two hidx (hcentR 1 _ hC1) ho₁ ho₁P
    rw [hcentP 1 _ hC1, hC1c] at this
    show Nat.card ↥(mcl275P ⊓ centralizer {mcl275FiveLine 1}) = 750
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
      (this.trans (by norm_num : 1500 = 750 * 2))
  have p₂ : Nat.card ↥(mclP ⊓ centralizer ({five₂} : Set (Equiv.Perm (Fin 275)))) = 25 := by
    have := card_inf_mul_two hidx (hcentR 0 _ hC0) ho₀ ho₀P
    rw [hcentP 0 _ hC0, hC0c] at this
    show Nat.card ↥(mcl275P ⊓ centralizer {mcl275FiveLine 0}) = 25
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
      (this.trans (by norm_num : 50 = 25 * 2))
  have k₁ : (conjClass mclP five₁).ncard = 1197504 := by
    have := ncard_conjClass_mul_card mclP five₁
    rw [p₁, card_mclP] at this
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 750)
      (this.trans (by norm_num : 898128000 = 1197504 * 750))
  have k₂ : (conjClass mclP five₂).ncard = 35925120 := by
    have := ncard_conjClass_mul_card mclP five₂
    rw [p₂, card_mclP] at this
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 25)
      (this.trans (by norm_num : 898128000 = 35925120 * 25))
  obtain ⟨hnc, hdisj⟩ := disjoint_conjClass_of_card_ne (P := mclP) (t₁ := five₁) (t₂ := five₂)
    (by rw [p₁, p₂]; norm_num)
  have hN := ncard_orderOf_mclP (m := 5) (by norm_num)
  rw [PairMcL.count_five] at hN
  have hU := class_union_eq (P := mclP) (t₁ := five₁) (t₂ := five₂) (hline_mem 1) (hline_mem 0)
    (hline_ord 1) (hline_ord 0) hdisj hN (by rw [k₁, k₂])
  refine ⟨hline_mem 1, hline_mem 0, hline_ord 1, hline_ord 0, p₁, p₂, k₁, k₂, hnc,
    fun y hy hy5 => ?_⟩
  have : y ∈ conjClass mclP five₁ ∪ conjClass mclP five₂ := by
    rw [hU]; exact ⟨hy, hy5⟩
  rcases this with h1 | h2
  · exact Or.inl h1
  · exact Or.inr h2

theorem exists_two_classes_of_equiv_rep {n : ℕ} {T : Type*} [Group T]
    {P : Subgroup (Equiv.Perm (Fin n))}
    (e : T ≃* P) {p c₁ c₂ : ℕ} {t₁ t₂ : Equiv.Perm (Fin n)} (h₁ : t₁ ∈ P) (h₂ : t₂ ∈ P)
    (o₁ : orderOf t₁ = p) (o₂ : orderOf t₂ = p)
    (k₁ : Nat.card ↥(P ⊓ centralizer ({t₁} : Set (Equiv.Perm (Fin n)))) = c₁)
    (k₂ : Nat.card ↥(P ⊓ centralizer ({t₂} : Set (Equiv.Perm (Fin n)))) = c₂)
    (hnc : ¬ ∃ g ∈ P, t₂ = g * t₁ * g⁻¹)
    (hall : ∀ y ∈ P, orderOf y = p →
      (∃ g ∈ P, y = g * t₁ * g⁻¹) ∨ ∃ g ∈ P, y = g * t₂ * g⁻¹) :
    ∃ x₁ x₂ : T, orderOf x₁ = p ∧ orderOf x₂ = p ∧
      Nat.card ↥(centralizer ({x₁} : Set T)) = c₁ ∧
      Nat.card ↥(centralizer ({x₂} : Set T)) = c₂ ∧ ¬ IsConj x₁ x₂ ∧
      (∀ y : T, orderOf y = p → IsConj y x₁ ∨ IsConj y x₂) ∧
      ((e x₁ : P) : Equiv.Perm (Fin n)) = t₁ ∧ ((e x₂ : P) : Equiv.Perm (Fin n)) = t₂ := by
  let ι : T →* Equiv.Perm (Fin n) := P.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hcard : ∀ {t : Equiv.Perm (Fin n)} (ht : t ∈ P) {c : ℕ},
      Nat.card ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = c →
      Nat.card ↥(centralizer ({e.symm ⟨t, ht⟩} : Set T)) = c := by
    intro t ht c hc
    have hιx : ι (e.symm ⟨t, ht⟩) = t := by simp [ι]
    have hE := McLCentralizer.centralizerEquivOfInjective ι hι (e.symm ⟨t, ht⟩)
    have e1 : ι.range ⊓ centralizer ({ι (e.symm ⟨t, ht⟩)} : Set (Equiv.Perm (Fin n))) =
        P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) := by rw [hrange, hιx]
    rw [e1] at hE
    rw [← hc]
    exact Nat.card_congr hE.toEquiv
  have hord : ∀ {t : Equiv.Perm (Fin n)} (ht : t ∈ P) {q : ℕ}, orderOf t = q →
      orderOf (e.symm ⟨t, ht⟩) = q := by
    intro t ht q hq
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hq]
  have hconj : ∀ {a b : T}, IsConj a b ↔ ∃ g : P, (g : Equiv.Perm (Fin n)) *
      ((e a : P) : Equiv.Perm (Fin n)) * (g : Equiv.Perm (Fin n))⁻¹ =
      ((e b : P) : Equiv.Perm (Fin n)) := by
    intro a b
    rw [isConj_iff]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by simp⟩
    · rintro ⟨g, hg⟩
      refine ⟨e.symm g, e.injective (Subtype.ext ?_)⟩
      simpa using hg
  refine ⟨e.symm ⟨t₁, h₁⟩, e.symm ⟨t₂, h₂⟩, hord h₁ o₁, hord h₂ o₂, hcard h₁ k₁, hcard h₂ k₂,
    ?_, fun y hy => ?_, by simp, by simp⟩
  · rw [hconj]
    rintro ⟨g, hg⟩
    simp only [MulEquiv.apply_symm_apply] at hg
    exact hnc ⟨g, g.2, hg.symm⟩
  · have hyo : orderOf ((e y : P) : Equiv.Perm (Fin n)) = p := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
    rcases hall _ (e y).2 hyo with ⟨g, hg, hgy⟩ | ⟨g, hg, hgy⟩
    · left
      rw [hconj]
      refine ⟨⟨g, hg⟩⁻¹, ?_⟩
      simp only [MulEquiv.apply_symm_apply, Subgroup.coe_inv, inv_inv]
      rw [hgy]
      group
    · right
      rw [hconj]
      refine ⟨⟨g, hg⟩⁻¹, ?_⟩
      simp only [MulEquiv.apply_symm_apply, Subgroup.coe_inv, inv_inv]
      rw [hgy]
      group

theorem exists_two_classes_of_equiv {n : ℕ} {T : Type*} [Group T]
    {P : Subgroup (Equiv.Perm (Fin n))}
    (e : T ≃* P) {p c₁ c₂ : ℕ} {t₁ t₂ : Equiv.Perm (Fin n)} (h₁ : t₁ ∈ P) (h₂ : t₂ ∈ P)
    (o₁ : orderOf t₁ = p) (o₂ : orderOf t₂ = p)
    (k₁ : Nat.card ↥(P ⊓ centralizer ({t₁} : Set (Equiv.Perm (Fin n)))) = c₁)
    (k₂ : Nat.card ↥(P ⊓ centralizer ({t₂} : Set (Equiv.Perm (Fin n)))) = c₂)
    (hnc : ¬ ∃ g ∈ P, t₂ = g * t₁ * g⁻¹)
    (hall : ∀ y ∈ P, orderOf y = p →
      (∃ g ∈ P, y = g * t₁ * g⁻¹) ∨ ∃ g ∈ P, y = g * t₂ * g⁻¹) :
    ∃ x₁ x₂ : T, orderOf x₁ = p ∧ orderOf x₂ = p ∧
      Nat.card ↥(centralizer ({x₁} : Set T)) = c₁ ∧
      Nat.card ↥(centralizer ({x₂} : Set T)) = c₂ ∧ ¬ IsConj x₁ x₂ ∧
      ∀ y : T, orderOf y = p → IsConj y x₁ ∨ IsConj y x₂ := by
  obtain ⟨x₁, x₂, a, b, c, d, f, g, -, -⟩ :=
    exists_two_classes_of_equiv_rep e h₁ h₂ o₁ o₂ k₁ k₂ hnc hall
  exact ⟨x₁, x₂, a, b, c, d, f, g⟩

theorem mcl_two_classes_order_three
    (h : ThreeFacts) :
    ∃ x₁ x₂ : CFSG.Blueprint.NativeSporadic.McL, orderOf x₁ = 3 ∧ orderOf x₂ = 3 ∧
      Nat.card ↥(centralizer ({x₁} : Set CFSG.Blueprint.NativeSporadic.McL)) = 29160 ∧
      Nat.card ↥(centralizer ({x₂} : Set CFSG.Blueprint.NativeSporadic.McL)) = 972 ∧
      ¬ IsConj x₁ x₂ ∧
      ∀ y : CFSG.Blueprint.NativeSporadic.McL, orderOf y = 3 → IsConj y x₁ ∨ IsConj y x₂ := by
  obtain ⟨m₁, m₂, o₁, o₂, c₁, c₂, -, -, hnc, hall⟩ := mclP_order_three_classes h
  exact @exists_two_classes_of_equiv 275 CFSG.Blueprint.NativeSporadic.McL inferInstance mclP
    mclPermEquiv _ _ _ _ _ m₁ m₂ o₁ o₂ c₁ c₂ hnc hall

theorem mcl_two_classes_order_five
    (h : fiveOuterCheck = true) :
    ∃ x₁ x₂ : CFSG.Blueprint.NativeSporadic.McL, orderOf x₁ = 5 ∧ orderOf x₂ = 5 ∧
      Nat.card ↥(centralizer ({x₁} : Set CFSG.Blueprint.NativeSporadic.McL)) = 750 ∧
      Nat.card ↥(centralizer ({x₂} : Set CFSG.Blueprint.NativeSporadic.McL)) = 25 ∧
      ¬ IsConj x₁ x₂ ∧
      ∀ y : CFSG.Blueprint.NativeSporadic.McL, orderOf y = 5 → IsConj y x₁ ∨ IsConj y x₂ := by
  obtain ⟨m₁, m₂, o₁, o₂, c₁, c₂, -, -, hnc, hall⟩ := mclP_order_five_classes h
  exact @exists_two_classes_of_equiv 275 CFSG.Blueprint.NativeSporadic.McL inferInstance mclP
    mclPermEquiv _ _ _ _ _ m₁ m₂ o₁ o₂ c₁ c₂ hnc hall

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Certificates.Native in
theorem mclP_five_power
    (h : fivePowerCheck = true) :
    ∃ g ∈ mclP, g * five₁ * g⁻¹ = five₁ ^ 2 := by
  simp only [fivePowerCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hs⟩, he⟩ := h
  refine ⟨permOfArr 275 fivePowArr, ?_, ?_⟩
  · rw [← mcl275P_eq]
    exact mem_mcl275P_of_sift (rep_of_validA hv) hs
  · exact eq_of_eqA (rep_conjA hv (rep_mcl275FiveLine 1))
      (rep_powArr (rep_mcl275FiveLine 1) 2) he

theorem isConj_pow_of_pow_two {G : Type*} [Group G] {x g : G} (ho : orderOf x = 5)
    (hg : g * x * g⁻¹ = x ^ 2) {j : ℕ} (hj : ¬ 5 ∣ j) : IsConj x (x ^ j) := by
  have hx5 : x ^ 5 = 1 := by rw [← ho]; exact pow_orderOf_eq_one x
  have hpow : ∀ i : ℕ, g ^ i * x * (g ^ i)⁻¹ = x ^ (2 ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc g ^ (i + 1) * x * (g ^ (i + 1))⁻¹ = g * (g ^ i * x * (g ^ i)⁻¹) * g⁻¹ := by group
        _ = g * x ^ (2 ^ i) * g⁻¹ := by rw [ih]
        _ = (g * x * g⁻¹) ^ (2 ^ i) := (conj_pow).symm
        _ = x ^ (2 ^ (i + 1)) := by rw [hg, ← pow_mul, pow_succ, mul_comm]
  have hj' : x ^ j = x ^ (j % 5) := by
    rw [← ho, pow_mod_orderOf]
  have hmod : j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
  rw [isConj_iff]
  rcases hmod with h | h | h | h
  · exact ⟨1, by rw [hj', h]; simp⟩
  · exact ⟨g, by rw [hj', h]; exact hg⟩
  · refine ⟨g ^ 3, ?_⟩
    rw [hpow 3, hj', h]
    calc x ^ (2 ^ 3) = x ^ (5 + 3) := by norm_num
      _ = x ^ 3 := by rw [pow_add, hx5, one_mul]
  · refine ⟨g ^ 2, ?_⟩
    rw [hpow 2, hj', h]
    norm_num

structure TwoClassesSubgroups (G : Type*) [Group G] (p c₁ c₂ : ℕ) (X X₂ : Subgroup G) : Prop where
  card_X : Nat.card ↥X = p
  card_X₂ : Nat.card ↥X₂ = p
  card_centralizer_X : Nat.card ↥(centralizer (X : Set G)) = c₁
  card_centralizer_X₂ : Nat.card ↥(centralizer (X₂ : Set G)) = c₂
  not_conj : ¬ ∃ g : G, X.map (MulAut.conj g).toMonoidHom = X₂
  classes : ∀ K : Subgroup G, Nat.card ↥K = p →
    (∃ g : G, K = X.map (MulAut.conj g).toMonoidHom) ∨
      ∃ g : G, K = X₂.map (MulAut.conj g).toMonoidHom

theorem twoClassesSubgroups_five {G : Type*} [Group G] {x₁ x₂ : G} {c₁ c₂ : ℕ}
    (o₁ : orderOf x₁ = 5) (o₂ : orderOf x₂ = 5)
    (k₁ : Nat.card ↥(centralizer ({x₁} : Set G)) = c₁)
    (k₂ : Nat.card ↥(centralizer ({x₂} : Set G)) = c₂) (hnc : ¬ IsConj x₁ x₂)
    (hall : ∀ y : G, orderOf y = 5 → IsConj y x₁ ∨ IsConj y x₂)
    (p₁ : ∃ g : G, g * x₁ * g⁻¹ = x₁ ^ 2) :
    TwoClassesSubgroups G 5 c₁ c₂ (zpowers x₁) (zpowers x₂) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcent : ∀ x : G, centralizer ((zpowers x : Subgroup G) : Set G) = centralizer {x} := by
    intro x
    rw [zpowers_eq_closure, centralizer_closure]
  have hz : ∀ {x : G}, orderOf x = 5 → (∃ g : G, g * x * g⁻¹ = x ^ 2) →
      ∀ y ∈ zpowers x, orderOf y = 5 → IsConj x y := by
    intro x ho hp y hy hyo
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    obtain ⟨g, hg⟩ := hp
    have hk : x ^ k = x ^ (k % 5).toNat := by
      have h1 := zpow_mod_orderOf x k
      rw [ho] at h1
      rw [← h1, ← zpow_natCast]
      congr 1
      rw [Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
      rfl
    have hx5 : x ^ 5 = 1 := by rw [← ho]; exact pow_orderOf_eq_one x
    have hj : ¬ 5 ∣ (k % 5).toNat := by
      intro hd
      obtain ⟨m, hm⟩ := hd
      have : x ^ k = 1 := by rw [hk, hm, pow_mul, hx5, one_pow]
      rw [this, orderOf_one] at hyo
      exact absurd hyo (by norm_num)
    rw [hk] at hyo ⊢
    exact isConj_pow_of_pow_two ho hg hj
  refine ⟨by rw [Nat.card_zpowers, o₁], by rw [Nat.card_zpowers, o₂],
    by rw [hcent]; exact k₁, by rw [hcent]; exact k₂, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    have hx₂ : x₂ ∈ (zpowers x₁).map (MulAut.conj g).toMonoidHom := hg ▸ mem_zpowers x₂
    obtain ⟨y, hy, hyx⟩ := mem_map.1 hx₂
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hyo : orderOf y = 5 := by
      rw [← o₂, ← hyx, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hnc ((hz o₁ p₁ y hy hyo).trans (isConj_iff.2 ⟨g, hyx⟩))
  · intro K hK
    have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
    have hnt : Nontrivial K := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    obtain ⟨k, hk1⟩ := exists_ne (1 : K)
    have hkord : orderOf (k : G) = 5 := by
      have hd : orderOf (k : G) ∣ 5 := by
        rw [Subgroup.orderOf_coe, ← hK]
        exact orderOf_dvd_natCard k
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hd with h1 | h5
      · exfalso
        apply hk1
        have : (k : G) = 1 := orderOf_eq_one_iff.1 h1
        exact Subtype.ext this
      · exact h5
    have hKeq : zpowers (k : G) = K :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 k.2) (by rw [Nat.card_zpowers, hkord, hK])
    have hconj : ∀ {x : G}, IsConj (k : G) x →
        ∃ c : G, K = (zpowers x).map (MulAut.conj c).toMonoidHom := by
      intro x hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hx
      refine ⟨c⁻¹, ?_⟩
      rw [← hKeq, MonoidHom.map_zpowers]
      have : (MulAut.conj c⁻¹).toMonoidHom x = (k : G) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hc]
        group
      rw [this]
    rcases hall (k : G) hkord with h1 | h2
    · exact Or.inl (hconj h1)
    · exact Or.inr (hconj h2)

theorem exists_pow_witness_of_equiv {n : ℕ} {T : Type*} [Group T]
    {P : Subgroup (Equiv.Perm (Fin n))} (e : T ≃* P) {x : T} {t : Equiv.Perm (Fin n)}
    (hx : ((e x : P) : Equiv.Perm (Fin n)) = t) {r : ℕ}
    (h : ∃ g ∈ P, g * t * g⁻¹ = t ^ r) : ∃ g : T, g * x * g⁻¹ = x ^ r := by
  obtain ⟨g, hg, hgt⟩ := h
  refine ⟨e.symm ⟨g, hg⟩, e.injective (Subtype.ext ?_)⟩
  simp only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_pow]
  rw [hx]
  exact hgt

theorem mcl_two_classes_subgroups_order_five
    (h : fiveOuterCheck = true) (hp : fivePowerCheck = true) :
    ∃ X X₂ : Subgroup CFSG.Blueprint.NativeSporadic.McL,
      TwoClassesSubgroups CFSG.Blueprint.NativeSporadic.McL 5 750 25 X X₂ := by
  obtain ⟨m₁, m₂, o₁, o₂, c₁, c₂, -, -, hnc, hall⟩ := mclP_order_five_classes h
  obtain ⟨g₁, hg₁, hg₁'⟩ := mclP_five_power hp
  obtain ⟨x₁, x₂, a₁, a₂, b₁, b₂, hxnc, hxall, r₁, r₂⟩ :=
    @exists_two_classes_of_equiv_rep 275 CFSG.Blueprint.NativeSporadic.McL inferInstance mclP
      mclPermEquiv _ _ _ _ _ m₁ m₂ o₁ o₂ c₁ c₂ hnc hall
  have p₁ : ∃ g : CFSG.Blueprint.NativeSporadic.McL, g * x₁ * g⁻¹ = x₁ ^ 2 :=
    @exists_pow_witness_of_equiv 275 CFSG.Blueprint.NativeSporadic.McL inferInstance mclP
      mclPermEquiv x₁ five₁ r₁ 2 ⟨g₁, hg₁, hg₁'⟩
  have hT := @twoClassesSubgroups_five CFSG.Blueprint.NativeSporadic.McL
    inferInstance x₁ x₂ 750 25 a₁ a₂ b₁ b₂ hxnc hxall p₁
  exact ⟨zpowers x₁, zpowers x₂, hT⟩

end CFSG.Sporadic.Recognition.McLAS
