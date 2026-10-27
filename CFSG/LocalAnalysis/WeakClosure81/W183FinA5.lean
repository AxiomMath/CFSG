module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Rank
public import CFSG.GH74.KGroups.L27
import CFSG.GH74.KGroups.A5Inputs
import CFSG.GH74.KGroups.AutModelIndexTwo
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Quasithin.Background.P4InspEndAbs
public import CFSG.GH74.KGroups.Generic6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3)
open CFSG.GH74.KGroups
open CFSG.Quasithin
open Subgroup

private def w183finA5V4 {G : Type*} [Group G] (a b : G) : List G := [1, a, b, a * b]

private def w183finA5InvB {n : ℕ} (g : Equiv.Perm (Fin n)) : Bool :=
  decide (g * g = 1 ∧ g ≠ 1)

private def w183finA5KleinB {n : ℕ} (a b : Equiv.Perm (Fin n)) : Bool :=
  decide (a * b = b * a) && !(decide (a = b))

private def w183finA5TiB {n : ℕ} (Y : List (Equiv.Perm (Fin n))) (a b : Equiv.Perm (Fin n)) :
    Bool :=
  [a, b, a * b].all fun t => Y.all fun g =>
    !(decide (g * t = t * g)) ||
      ((w183finA5V4 a b).contains (g * a * g⁻¹) && (w183finA5V4 a b).contains (g * b * g⁻¹))

private def w183finA5CpB {n : ℕ} (P : List (Equiv.Perm (Fin n))) (a b : Equiv.Perm (Fin n)) :
    Bool :=
  [a, b, a * b].all fun t => P.all fun g =>
    !(decide (g * t = t * g)) || (decide (g * a = a * g) && decide (g * b = b * g))

private def w183finA5FinA5B {n : ℕ} (Y P : List (Equiv.Perm (Fin n))) : Bool :=
  let I := Y.filter w183finA5InvB
  I.all fun a => I.all fun b =>
    !(w183finA5KleinB a b) || !(w183finA5TiB Y a b) || (P.contains a && P.contains b)

private def w183finA5Rank2B {n : ℕ} (Y : List (Equiv.Perm (Fin n))) : Bool :=
  let I := Y.filter w183finA5InvB
  I.all fun a => I.all fun b => I.all fun c =>
    !(decide (a * b = b * a ∧ a * c = c * a ∧ b * c = c * b)) || decide (b = a) ||
      [a, b, a * b].contains c

private def w183finA5FinG3A5B {n : ℕ} (Y P : List (Equiv.Perm (Fin n))) : Bool :=
  let I := Y.filter w183finA5InvB
  I.all fun a => I.all fun b => !(w183finA5KleinB a b) || !(w183finA5CpB P a b) ||
    (P.contains a && P.contains b &&
      P.any fun m => (w183finA5V4 a b).contains (m * a * m⁻¹) &&
        (w183finA5V4 a b).contains (m * b * m⁻¹) &&
        decide (m * a * m⁻¹ ≠ a) && decide (m * b * m⁻¹ ≠ b) &&
        decide (m * (a * b) * m⁻¹ ≠ a * b))

private def w183finA5FinG3L32B {n : ℕ} (Y P : List (Equiv.Perm (Fin n))) : Bool :=
  let I := Y.filter w183finA5InvB
  I.all fun a => I.all fun b => !(w183finA5KleinB a b) || !(w183finA5CpB P a b)

private theorem w183finA5_s5_finA5B :
    w183finA5FinA5B (elemsT A5.QA) (elemsT A5.QP) = true := by decide +kernel

private theorem w183finA5_s5_rank2B : w183finA5Rank2B (elemsT A5.QA) = true := by decide +kernel

private theorem w183finA5_s5_finG3B :
    w183finA5FinG3A5B (elemsT A5.QA) (elemsT A5.QP) = true := by decide +kernel

private theorem w183finA5_pgl_rank2B : w183finA5Rank2B (elemsT L27.QA) = true := by
  decide +kernel

private theorem w183finA5_pgl_finG3B :
    w183finA5FinG3L32B (elemsT L27.QA) (elemsT L27.QP) = true := by decide +kernel

private theorem w183finA5FinA5B_sound {n : ℕ} {Y P : List (Equiv.Perm (Fin n))}
    (h : w183finA5FinA5B Y P = true) {a b : Equiv.Perm (Fin n)}
    (ha : a ∈ Y) (hb : b ∈ Y) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a)
    (hTI : ∀ t ∈ [a, b, a * b], ∀ g ∈ Y, g * t = t * g →
      g * a * g⁻¹ ∈ w183finA5V4 a b ∧ g * b * g⁻¹ ∈ w183finA5V4 a b) : a ∈ P ∧ b ∈ P := by
  simp only [w183finA5FinA5B, w183finA5InvB, List.all_eq_true, List.mem_filter, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
  have h1 := h a ⟨ha, ha2, ha1⟩ b ⟨hb, hb2, hb1⟩
  have hk : w183finA5KleinB a b = true := by simp [w183finA5KleinB, hc, hab]
  have ht : w183finA5TiB Y a b = true := by
    simp only [w183finA5TiB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, List.contains_iff_mem]
    intro t ht g hg
    by_cases hgt : g * t = t * g
    · exact Or.inr (hTI t ht g hg hgt)
    · exact Or.inl hgt
  rcases h1 with (h1 | h1) | h1
  · rw [hk] at h1; simp at h1
  · rw [ht] at h1; simp at h1
  · simpa [List.contains_iff_mem] using h1

private theorem w183finA5Rank2B_sound {n : ℕ} {Y : List (Equiv.Perm (Fin n))}
    (h : w183finA5Rank2B Y = true) {a b c : Equiv.Perm (Fin n)}
    (ha : a ∈ Y) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb : b ∈ Y) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hc : c ∈ Y) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    b = a ∨ c = a ∨ c = b ∨ c = a * b := by
  simp only [w183finA5Rank2B, w183finA5InvB, List.all_eq_true, List.mem_filter, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_false_iff_not] at h
  have h1 := h a ⟨ha, ha2, ha1⟩ b ⟨hb, hb2, hb1⟩ c ⟨hc, hc2, hc1⟩
  rcases h1 with (h1 | h1) | h1
  · exact absurd ⟨hab, hac, hbc⟩ h1
  · exact Or.inl h1
  · simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h1
    tauto

private theorem w183finA5FinG3L32B_sound {n : ℕ} {Y P : List (Equiv.Perm (Fin n))}
    (h : w183finA5FinG3L32B Y P = true) {a b : Equiv.Perm (Fin n)}
    (ha : a ∈ Y) (hb : b ∈ Y) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a)
    (hcp : ∀ t ∈ [a, b, a * b], ∀ g ∈ P, g * t = t * g → g * a = a * g ∧ g * b = b * g) :
    False := by
  simp only [w183finA5FinG3L32B, w183finA5InvB, List.all_eq_true, List.mem_filter,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
  have h1 := h a ⟨ha, ha2, ha1⟩ b ⟨hb, hb2, hb1⟩
  have hk : w183finA5KleinB a b = true := by simp [w183finA5KleinB, hc, hab]
  have hp : w183finA5CpB P a b = true := by
    simp only [w183finA5CpB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_true, decide_eq_false_iff_not, decide_eq_true_eq]
    intro t ht g hg
    by_cases hgt : g * t = t * g
    · exact Or.inr (hcp t ht g hg hgt)
    · exact Or.inl hgt
  rcases h1 with h1 | h1
  · rw [hk] at h1; simp at h1
  · rw [hp] at h1; simp at h1

private theorem w183finA5FinG3A5B_sound {n : ℕ} {Y P : List (Equiv.Perm (Fin n))}
    (h : w183finA5FinG3A5B Y P = true) {a b : Equiv.Perm (Fin n)}
    (ha : a ∈ Y) (hb : b ∈ Y) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a)
    (hcp : ∀ t ∈ [a, b, a * b], ∀ g ∈ P, g * t = t * g → g * a = a * g ∧ g * b = b * g) :
    a ∈ P ∧ b ∈ P ∧ ∃ m ∈ P, m * a * m⁻¹ ∈ w183finA5V4 a b ∧
      m * b * m⁻¹ ∈ w183finA5V4 a b ∧ m * a * m⁻¹ ≠ a ∧ m * b * m⁻¹ ≠ b ∧
      m * (a * b) * m⁻¹ ≠ a * b := by
  simp only [w183finA5FinG3A5B, w183finA5InvB, List.all_eq_true, List.mem_filter,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
  have h1 := h a ⟨ha, ha2, ha1⟩ b ⟨hb, hb2, hb1⟩
  have hk : w183finA5KleinB a b = true := by simp [w183finA5KleinB, hc, hab]
  have hp : w183finA5CpB P a b = true := by
    simp only [w183finA5CpB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_true, decide_eq_false_iff_not, decide_eq_true_eq]
    intro t ht g hg
    by_cases hgt : g * t = t * g
    · exact Or.inr (hcp t ht g hg hgt)
    · exact Or.inl hgt
  rcases h1 with (h1 | h1) | h1
  · rw [hk] at h1; simp at h1
  · rw [hp] at h1; simp at h1
  · obtain ⟨⟨haP, hbP⟩, hex⟩ := h1
    refine ⟨List.contains_iff_mem.mp haP, List.contains_iff_mem.mp hbP, ?_⟩
    obtain ⟨m, hmP, hm⟩ := List.any_eq_true.mp hex
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hm
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hm
    exact ⟨m, hmP, h1, h2, h3, h4, h5⟩

private theorem w183finA5CardLeFourOfRank2B {n : ℕ} {Y : List (Equiv.Perm (Fin n))}
    (h : w183finA5Rank2B Y = true) {B : Subgroup (Equiv.Perm (Fin n))}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hmem : ∀ g ∈ B, g ∈ Y) : Nat.card B ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hex : ∀ s : Finset (Equiv.Perm (Fin n)), s.card < Nat.card B → ∃ a ∈ B, a ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hsub : (B : Set (Equiv.Perm (Fin n))) ⊆ (s : Set (Equiv.Perm (Fin n))) :=
      fun a ha => hcon a ha
    have h1 : Nat.card B ≤ Nat.card (s : Set (Equiv.Perm (Fin n))) :=
      Nat.card_mono s.finite_toSet hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
    omega
  have hsq : ∀ g ∈ B, g * g = 1 := fun g hg => by rw [← pow_two]; exact hB.2 g hg
  have hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  obtain ⟨γ, hγ, hγ1⟩ := hex {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨δ, hδ, hδ1⟩ := hex {1, γ}
    (by have := Finset.card_le_two (a := (1 : Equiv.Perm (Fin n))) (b := γ); omega)
  obtain ⟨ε, hε, hε1⟩ := hex {1, γ, δ, γ * δ}
    (by have := Finset.card_le_four (a := (1 : Equiv.Perm (Fin n))) (b := γ) (c := δ)
          (d := γ * δ); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ1 hδ1 hε1
  rcases w183finA5Rank2B_sound h (hmem γ hγ) (hsq γ hγ) hγ1 (hmem δ hδ) (hsq δ hδ) hδ1.1
      (hmem ε hε) (hsq ε hε) hε1.1 (hcomm γ hγ δ hδ) (hcomm γ hγ ε hε)
      (hcomm δ hδ ε hε) with h1 | h1 | h1 | h1
  · exact hδ1.2 h1
  · exact hε1.2.1 h1
  · exact hε1.2.2.1 h1
  · exact hε1.2.2.2 h1

private theorem w183finA5A5Model {Y : Type} [Group Y]
    (L : Subgroup Y) (hL : IsL2 ↥L 2) :
    ∃ M : AutModel ↥L (Equiv.Perm (Fin 5)), M.P = alternatingGroup (Fin 5) ∧ M.A = ⊤ ∧
      Nat.card M.A = 2 * Nat.card M.P := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥L hL
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  let Φ' : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≃* MulAut (alternatingGroup (Fin 5)) :=
    Subgroup.topEquiv.trans (MulEquiv.ofBijective _ hbij)
  refine ⟨AutModel.ofRealization (alternatingGroup (Fin 5)) ⊤ e Φ'
    (fun σ x => by
      show ((MulAut.conjNormal (σ : Equiv.Perm (Fin 5)) x : alternatingGroup (Fin 5)) :
        Equiv.Perm (Fin 5)) = σ * x * (σ : Equiv.Perm (Fin 5))⁻¹
      rw [MulAut.conjNormal_apply]), rfl, rfl, ?_⟩
  show Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 5))) = 2 * Nat.card (alternatingGroup (Fin 5))
  rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  decide

private theorem w183finA5L32Model {Y : Type} [Group Y]
    (L : Subgroup Y) (hL : IsL3 ↥L 1) :
    ∃ M : AutModel ↥L (Equiv.Perm (Fin 8)), M.P = L27.QP.originalSubgroup ∧
      M.A = L27.QA.originalSubgroup ∧ Nat.card M.A = 2 * Nat.card M.P := by
  obtain ⟨e⟩ := L27.equiv_of_lieModel3 hL
  obtain ⟨M, hP, hA⟩ := L27.autModel e
  refine ⟨M, hP, hA, ?_⟩
  rw [hP, hA, card_group _ L27.QA_ok, card_group _ L27.QP_ok, L27.QA_valid.2, L27.QP_valid.2]

private theorem w183finA5L27PLeA : L27.QP.originalSubgroup ≤ L27.QA.originalSubgroup := by
  have hpa : L27.pa ∈ L27.QA.originalSubgroup := by
    rw [L27.QA, CFSG.Sporadic.Schreier.certificate_originalSubgroup]
    exact Subgroup.subset_closure (by simp)
  have hpb : L27.pb ∈ L27.QA.originalSubgroup := by
    rw [L27.QA, CFSG.Sporadic.Schreier.certificate_originalSubgroup]
    exact Subgroup.subset_closure (by simp)
  rw [L27.QP_closure, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact hpa
  · rw [Set.mem_singleton_iff] at hg; subst hg; exact hpb

private theorem w183finA5ActHomOfMem {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    {G : Type*} [Group G] (M : AutModel ↥N G) (hPA : M.P ≤ M.A) (x : H) (hx : x ∈ N) :
    M.actHom N x = (M.e ⟨x, hx⟩ : G) := by
  have hτA : (M.e ⟨x, hx⟩ : G) ∈ M.A := hPA (M.e ⟨x, hx⟩).2
  have hσA : M.actHom N x ∈ M.A := M.actHom_mem N x
  have hcomm : ∀ y ∈ M.P, ((M.e ⟨x, hx⟩ : G)⁻¹ * M.actHom N x) * y =
      y * ((M.e ⟨x, hx⟩ : G)⁻¹ * M.actHom N x) := by
    intro y hy
    obtain ⟨z, hz⟩ := M.e.surjective ⟨y, hy⟩
    have hzy : (M.e z : G) = y := congrArg Subtype.val hz
    have h1 := M.actHom_spec N x z
    have h2 : MulAut.conjNormal (H := N) x z = ⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      rfl
    simp only [h2, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hzy] at h1
    generalize (M.e ⟨x, hx⟩ : G) = τ at h1 ⊢
    generalize M.actHom N x = σ at h1 ⊢
    calc (τ⁻¹ * σ) * y = τ⁻¹ * (σ * y * σ⁻¹) * σ := by group
      _ = τ⁻¹ * (τ * y * τ⁻¹) * σ := by rw [← h1]
      _ = y * (τ⁻¹ * σ) := by group
  have hone : (M.e ⟨x, hx⟩ : G)⁻¹ * M.actHom N x = 1 :=
    M.centralizer_trivial (M.A.mul_mem (M.A.inv_mem hτA) hσA) hcomm
  calc M.actHom N x = (M.e ⟨x, hx⟩ : G) * ((M.e ⟨x, hx⟩ : G)⁻¹ * M.actHom N x) := by group
    _ = (M.e ⟨x, hx⟩ : G) := by rw [hone, mul_one]

private theorem w183finA5KleinData {Y : Type*} [Group Y] [Finite Y] {A : Subgroup Y}
    (h4 : Nat.card A = 4) (hel : IsElemAbelian 2 A) :
    ∃ a b : Y, a ∈ A ∧ b ∈ A ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a ∧ ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  obtain ⟨x, y, hx1, hy1, hxy⟩ :=
    CFSG.Quasithin.G11.P4InspEnd.p4inspend_two_ne_one (P := A) (by omega)
  have ha1 : (x : Y) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hb1 : (y : Y) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hab : (x : Y) ≠ y := fun h => hxy (Subtype.ext h)
  exact ⟨x, y, x.2, y.2, ha1, hb1, hab, CFSG.Goldschmidt.Sec8.mul_self_eq_one hel x.2,
    CFSG.Goldschmidt.Sec8.mul_self_eq_one hel y.2, CFSG.Goldschmidt.Sec8.comm hel x.2 y.2,
    fun z hz => CFSG.Goldschmidt.Sec8.mem_four hel h4 x.2 y.2 hz ha1 hb1 hab⟩

private theorem w183finA5MemV4OfMap {n : ℕ} {Y : Type*} [Group Y]
    (ψ : Y →* Equiv.Perm (Fin n)) {a b x : Y}
    (h : x = 1 ∨ x = a ∨ x = b ∨ x = a * b) : ψ x ∈ w183finA5V4 (ψ a) (ψ b) := by
  simp only [w183finA5V4, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one ψ)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul ψ _ _)))

private theorem w183finA5ExistsMemAOfMemV4 {n : ℕ} {Y : Type*} [Group Y]
    {ψ : Y →* Equiv.Perm (Fin n)} {A : Subgroup Y} {a b : Y} (ha : a ∈ A) (hb : b ∈ A)
    {h : Equiv.Perm (Fin n)} (hh : h ∈ w183finA5V4 (ψ a) (ψ b)) : ∃ x ∈ A, ψ x = h := by
  simp only [w183finA5V4, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact ⟨1, A.one_mem, map_one ψ⟩
  · exact ⟨a, ha, rfl⟩
  · exact ⟨b, hb, rfl⟩
  · exact ⟨a * b, A.mul_mem ha hb, map_mul ψ a b⟩

private theorem w183finA5MemOfActHomMem {Y : Type*} [Group Y] (L : Subgroup Y) [L.Normal]
    {G : Type*} [Group G] (M : AutModel ↥L G) (hPA : M.P ≤ M.A)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (y : Y)
    (hy : M.actHom L y ∈ M.P) : y ∈ L := by
  obtain ⟨k, hk⟩ := M.e.surjective ⟨M.actHom L y, hy⟩
  have h1 : M.actHom L (k : Y) = M.actHom L y := by
    rw [w183finA5ActHomOfMem L M hPA (k : Y) k.2]
    exact congrArg Subtype.val hk
  have h2 := M.actHom_injective L hC h1
  rw [← h2]; exact k.2

private theorem w183finA5MapLeA {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    {G : Type*} [Group G] (M : AutModel N G) {A : Subgroup H} :
    A.map (M.actHom N) ≤ M.A := by
  rintro g ⟨a, _, rfl⟩
  exact M.actHom_mem N a

private theorem w183finA5ElemsTA5QAMem :
    ∀ g : Equiv.Perm (Fin 5), g ∈ elemsT A5.QA := by decide +kernel

private theorem w183finA5ElemsTA5QPSign :
    ∀ g ∈ elemsT A5.QP, Equiv.Perm.sign g = 1 := by decide +kernel

private theorem w183finA5ElemsTA5QPMemAlt (g : Equiv.Perm (Fin 5))
    (hg : g ∈ elemsT A5.QP) : g ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact w183finA5ElemsTA5QPSign g hg

theorem finA5_holds : FinA5 := by
  intro Y _ _ L hLn hL hC A hA4 hAel hTI
  haveI := hLn
  obtain ⟨M, hMP, hMA, h2⟩ := w183finA5A5Model L hL
  have hcardL : Nat.card L = 60 := by
    have h1 : Nat.card ↥L = Nat.card M.P := Nat.card_congr M.e.toEquiv
    rw [h1, hMP, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hA_le_L : A ≤ L := by
    rcases M.nonempty_mulEquiv_or_eq_top L hC h2 with ⟨⟨eYA⟩⟩ | hLtop
    · let ψ := M.actHom L
      have hψinj : Function.Injective ψ := M.actHom_injective L hC
      have hψmem : ∀ y, ψ y ∈ M.A := M.actHom_mem L
      have hcardYA : Nat.card Y = Nat.card M.A := Nat.card_congr eYA.toEquiv
      have hsurj : ∀ g ∈ M.A, ∃ y, ψ y = g := by
        let f : Y →* M.A := ψ.codRestrict M.A hψmem
        have hf : Function.Injective f := fun a b hab => hψinj (congrArg Subtype.val hab)
        haveI : Finite M.A := Nat.finite_of_card_ne_zero (by
          rw [← hcardYA]; exact Nat.card_pos.ne')
        have hfb : Function.Bijective f := hf.bijective_of_nat_card_le (le_of_eq hcardYA.symm)
        intro g hg
        obtain ⟨y, hy⟩ := hfb.2 ⟨g, hg⟩
        exact ⟨y, congrArg Subtype.val hy⟩
      obtain ⟨a, b, haA, hbA, ha1, hb1, hab, ha2, hb2, hcomm, hmem⟩ :=
        w183finA5KleinData hA4 hAel
      have hψa2 : ψ a * ψ a = 1 := by rw [← map_mul, ha2, map_one]
      have hψb2 : ψ b * ψ b = 1 := by rw [← map_mul, hb2, map_one]
      have hψa1 : ψ a ≠ 1 := fun h => ha1 (hψinj (by rw [h, map_one]))
      have hψb1 : ψ b ≠ 1 := fun h => hb1 (hψinj (by rw [h, map_one]))
      have hψab : ψ a ≠ ψ b := fun h => hab (hψinj h)
      have hψc : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hcomm]
      have hTI' : ∀ t ∈ [ψ a, ψ b, ψ a * ψ b], ∀ g ∈ elemsT A5.QA, g * t = t * g →
          g * ψ a * g⁻¹ ∈ w183finA5V4 (ψ a) (ψ b) ∧
            g * ψ b * g⁻¹ ∈ w183finA5V4 (ψ a) (ψ b) := by
        intro t ht g hg hgt
        obtain ⟨y, rfl⟩ := hsurj g (by rw [hMA]; exact Subgroup.mem_top g)
        have key : ∀ t₀ ∈ A, t₀ ≠ 1 → ψ y * ψ t₀ = ψ t₀ * ψ y →
            ψ y * ψ a * (ψ y)⁻¹ ∈ w183finA5V4 (ψ a) (ψ b) ∧
              ψ y * ψ b * (ψ y)⁻¹ ∈ w183finA5V4 (ψ a) (ψ b) := by
          intro t₀ ht₀A ht₀1 hc
          have hyt : y * t₀ = t₀ * y := hψinj (by rw [map_mul, map_mul]; exact hc)
          have hN := hTI t₀ ht₀A ht₀1 y hyt
          have hya : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hN a).mp haA
          have hyb : y * b * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hN b).mp hbA
          have h1 := w183finA5MemV4OfMap ψ (hmem _ hya)
          have h2 := w183finA5MemV4OfMap ψ (hmem _ hyb)
          rw [map_mul, map_mul, map_inv] at h1 h2
          exact ⟨h1, h2⟩
        rw [List.mem_cons, List.mem_cons, List.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact key a haA ha1 hgt
        · exact key b hbA hb1 hgt
        · refine key (a * b) (A.mul_mem haA hbA) ?_ (by rw [map_mul]; exact hgt)
          intro h
          exact hab (by
            have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
            rw [this]
            exact inv_eq_of_mul_eq_one_right hb2)
      have hsound := w183finA5FinA5B_sound w183finA5_s5_finA5B
        (a := ψ a) (b := ψ b) (w183finA5ElemsTA5QAMem (ψ a))
        (w183finA5ElemsTA5QAMem (ψ b)) hψa2 hψa1 hψb2 hψb1 hψab hψc hTI'
      have haP : ψ a ∈ M.P := by rw [hMP]; exact w183finA5ElemsTA5QPMemAlt _ hsound.1
      have hbP : ψ b ∈ M.P := by rw [hMP]; exact w183finA5ElemsTA5QPMemAlt _ hsound.2
      intro x hx
      rcases hmem x hx with hx1 | hx2 | hx3 | hx4
      · rw [hx1]; exact L.one_mem
      · rw [hx2]; exact w183finA5MemOfActHomMem L M (by rw [hMA]; exact le_top) hC a haP
      · rw [hx3]; exact w183finA5MemOfActHomMem L M (by rw [hMA]; exact le_top) hC b hbP
      · rw [hx4]
        exact L.mul_mem (w183finA5MemOfActHomMem L M (by rw [hMA]; exact le_top) hC a haP)
          (w183finA5MemOfActHomMem L M (by rw [hMA]; exact le_top) hC b hbP)
    · rw [hLtop]; exact le_top
  refine ⟨hA_le_L, IsPGroup.of_card (n := 2) (by rw [hA4]; norm_num), ?_⟩
  have hrel : A.relIndex L * Nat.card A = Nat.card L := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := L)
    rwa [inf_eq_left.2 hA_le_L] at h
  have h15 : A.relIndex L = 15 := by
    rw [hA4, hcardL] at hrel
    omega
  rw [h15]; norm_num

theorem finRk2_holds : FinRk2 := by
  intro Y _ _ L hLn hC hshape A hAel
  haveI := hLn
  rcases hshape with hL2 | hL3
  · obtain ⟨M, hMP, hMA, h2⟩ := w183finA5A5Model L hL2
    let ψ := M.actHom L
    have hψinj : Function.Injective ψ := M.actHom_injective L hC
    have hB : IsElemAbelian 2 (A.map ψ) := IsElemAbelian.map hAel ψ
    have hmem : ∀ g ∈ A.map ψ, g ∈ elemsT A5.QA := fun g _ => w183finA5ElemsTA5QAMem g
    have hcard : Nat.card A = Nat.card (A.map ψ) :=
      Nat.card_congr (Subgroup.equivMapOfInjective A ψ hψinj).toEquiv
    rw [hcard]
    exact w183finA5CardLeFourOfRank2B w183finA5_s5_rank2B hB hmem
  · obtain ⟨M, hMP, hMA, h2⟩ := w183finA5L32Model L hL3
    let ψ := M.actHom L
    have hψinj : Function.Injective ψ := M.actHom_injective L hC
    have hB : IsElemAbelian 2 (A.map ψ) := IsElemAbelian.map hAel ψ
    have hmem : ∀ g ∈ A.map ψ, g ∈ elemsT L27.QA := by
      intro g hg
      rw [mem_elemsT _ L27.QA_ok, ← hMA]
      exact w183finA5MapLeA L M hg
    have hcard : Nat.card A = Nat.card (A.map ψ) :=
      Nat.card_congr (Subgroup.equivMapOfInjective A ψ hψinj).toEquiv
    rw [hcard]
    exact w183finA5CardLeFourOfRank2B w183finA5_pgl_rank2B hB hmem

theorem finG3A5_holds
    (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (hLn : L.Normal) (hL : IsL2 ↥L 2)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (A : Subgroup Y) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    A ≤ L ∧ ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  haveI := hLn
  obtain ⟨M, hMP, hMA, h2⟩ := w183finA5A5Model L hL
  have hPA : M.P ≤ M.A := by rw [hMA]; exact le_top
  let ψ := M.actHom L
  have hψinj : Function.Injective ψ := M.actHom_injective L hC
  obtain ⟨a, b, haA, hbA, ha1, hb1, hab, ha2, hb2, hcomm, hmem⟩ := w183finA5KleinData hcard hel
  have hψa2 : ψ a * ψ a = 1 := by rw [← map_mul, ha2, map_one]
  have hψb2 : ψ b * ψ b = 1 := by rw [← map_mul, hb2, map_one]
  have hψa1 : ψ a ≠ 1 := fun h => ha1 (hψinj (by rw [h, map_one]))
  have hψb1 : ψ b ≠ 1 := fun h => hb1 (hψinj (by rw [h, map_one]))
  have hψab : ψ a ≠ ψ b := fun h => hab (hψinj h)
  have hψc : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hcomm]
  have hcp : ∀ t ∈ [ψ a, ψ b, ψ a * ψ b], ∀ g ∈ elemsT A5.QP, g * t = t * g →
      g * ψ a = ψ a * g ∧ g * ψ b = ψ b * g := by
    intro t ht g hg hgt
    have hgP : g ∈ M.P := by rw [hMP]; exact w183finA5ElemsTA5QPMemAlt g hg
    obtain ⟨k, hk⟩ := M.e.surjective ⟨g, hgP⟩
    have hkψ : ψ k = g := by
      rw [w183finA5ActHomOfMem L M hPA (k : Y) k.2]
      exact congrArg Subtype.val hk
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hcommk : (k : Y) * a = a * (k : Y) := by
        apply hψinj
        simpa only [map_mul, hkψ] using hgt
      have hthis := hTI1 a haA ha1 (k : Y) k.2 hcommk
      exact ⟨by rw [← hkψ, ← map_mul, ← map_mul, hthis a haA],
             by rw [← hkψ, ← map_mul, ← map_mul, hthis b hbA]⟩
    · have hcommk : (k : Y) * b = b * (k : Y) := by
        apply hψinj
        simpa only [map_mul, hkψ] using hgt
      have hthis := hTI1 b hbA hb1 (k : Y) k.2 hcommk
      exact ⟨by rw [← hkψ, ← map_mul, ← map_mul, hthis a haA],
             by rw [← hkψ, ← map_mul, ← map_mul, hthis b hbA]⟩
    · have hcommk : (k : Y) * (a * b) = (a * b) * (k : Y) := by
        apply hψinj
        simpa only [map_mul, hkψ] using hgt
      have hne : a * b ≠ 1 := by
        intro h
        exact hab (by
          have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this]
          exact inv_eq_of_mul_eq_one_right hb2)
      have hthis := hTI1 (a * b) (A.mul_mem haA hbA) hne (k : Y) k.2 hcommk
      exact ⟨by rw [← hkψ, ← map_mul, ← map_mul, hthis a haA],
             by rw [← hkψ, ← map_mul, ← map_mul, hthis b hbA]⟩
  have hsound := w183finA5FinG3A5B_sound w183finA5_s5_finG3B
    (a := ψ a) (b := ψ b) (w183finA5ElemsTA5QAMem (ψ a))
    (w183finA5ElemsTA5QAMem (ψ b)) hψa2 hψa1 hψb2 hψb1 hψab hψc hcp
  have haP : ψ a ∈ M.P := by rw [hMP]; exact w183finA5ElemsTA5QPMemAlt _ hsound.1
  have hbP : ψ b ∈ M.P := by rw [hMP]; exact w183finA5ElemsTA5QPMemAlt _ hsound.2.1
  have haL : a ∈ L := w183finA5MemOfActHomMem L M hPA hC a haP
  have hbL : b ∈ L := w183finA5MemOfActHomMem L M hPA hC b hbP
  have hA_le_L : A ≤ L := by
    intro x hx
    rcases hmem x hx with rfl | rfl | rfl | rfl
    · exact L.one_mem
    · exact haL
    · exact hbL
    · exact L.mul_mem haL hbL
  obtain ⟨m, hmP, hm1, hm2, hm3, hm4, hm5⟩ := hsound.2.2
  have hmP' : m ∈ M.P := by rw [hMP]; exact w183finA5ElemsTA5QPMemAlt m hmP
  obtain ⟨n, hn⟩ := M.e.surjective ⟨m, hmP'⟩
  have hnψ : ψ n = m := by
    rw [w183finA5ActHomOfMem L M hPA (n : Y) n.2]
    exact congrArg Subtype.val hn
  have hna : (n : Y) * a * (n : Y)⁻¹ ∈ A := by
    obtain ⟨x', hx'A, hx'eq⟩ := w183finA5ExistsMemAOfMemV4 haA hbA hm1
    have h : (n : Y) * a * (n : Y)⁻¹ = x' := by
      apply hψinj
      rw [map_mul, map_mul, map_inv, hnψ]
      exact hx'eq.symm
    rw [h]; exact hx'A
  have hnb : (n : Y) * b * (n : Y)⁻¹ ∈ A := by
    obtain ⟨x', hx'A, hx'eq⟩ := w183finA5ExistsMemAOfMemV4 haA hbA hm2
    have h : (n : Y) * b * (n : Y)⁻¹ = x' := by
      apply hψinj
      rw [map_mul, map_mul, map_inv, hnψ]
      exact hx'eq.symm
    rw [h]; exact hx'A
  refine ⟨hA_le_L, (n : Y), n.2, ?_, ?_⟩
  · intro x hx
    rcases hmem x hx with rfl | rfl | rfl | rfl
    · simpa using A.one_mem
    · exact hna
    · exact hnb
    · have heq : (n : Y) * (a * b) * (n : Y)⁻¹ =
          ((n : Y) * a * (n : Y)⁻¹) * ((n : Y) * b * (n : Y)⁻¹) := by group
      rw [heq]; exact A.mul_mem hna hnb
  · intro x hx hx1
    rcases hmem x hx with rfl | rfl | rfl | rfl
    · exact absurd rfl hx1
    · intro hfix
      exact hm3 (by
        have h := congrArg ψ hfix
        simpa only [map_mul, map_inv, hnψ] using h)
    · intro hfix
      exact hm4 (by
        have h := congrArg ψ hfix
        simpa only [map_mul, map_inv, hnψ] using h)
    · intro hfix
      exact hm5 (by
        have h := congrArg ψ hfix
        simpa only [map_mul, map_inv, hnψ] using h)

theorem finG3L32_holds
    (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (hLn : L.Normal) (hL : IsL3 ↥L 1)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (A : Subgroup Y) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) : False := by
  haveI := hLn
  obtain ⟨M, hMP, hMA, h2⟩ := w183finA5L32Model L hL
  have hPA : M.P ≤ M.A := by rw [hMP, hMA]; exact w183finA5L27PLeA
  let ψ := M.actHom L
  have hψinj : Function.Injective ψ := M.actHom_injective L hC
  obtain ⟨a, b, haA, hbA, ha1, hb1, hab, ha2, hb2, hcomm, hmem⟩ := w183finA5KleinData hcard hel
  have hψa2 : ψ a * ψ a = 1 := by rw [← map_mul, ha2, map_one]
  have hψb2 : ψ b * ψ b = 1 := by rw [← map_mul, hb2, map_one]
  have hψa1 : ψ a ≠ 1 := fun h => ha1 (hψinj (by rw [h, map_one]))
  have hψb1 : ψ b ≠ 1 := fun h => hb1 (hψinj (by rw [h, map_one]))
  have hψab : ψ a ≠ ψ b := fun h => hab (hψinj h)
  have hψc : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hcomm]
  have hcp : ∀ t ∈ [ψ a, ψ b, ψ a * ψ b], ∀ g ∈ elemsT L27.QP, g * t = t * g →
      g * ψ a = ψ a * g ∧ g * ψ b = ψ b * g := by
    intro t ht g hg hgt
    have hgP : g ∈ M.P := by rw [hMP]; exact (mem_elemsT L27.QP L27.QP_ok g).mp hg
    obtain ⟨k, hk⟩ := M.e.surjective ⟨g, hgP⟩
    have hkψ : ψ k = g := by
      rw [w183finA5ActHomOfMem L M hPA (k : Y) k.2]
      exact congrArg Subtype.val hk
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hcommk : (k : Y) * a = a * (k : Y) := by
        apply hψinj
        simpa only [map_mul, hkψ] using hgt
      have hthis := hTI1 a haA ha1 (k : Y) k.2 hcommk
      exact ⟨by rw [← hkψ, ← map_mul, ← map_mul, hthis a haA],
             by rw [← hkψ, ← map_mul, ← map_mul, hthis b hbA]⟩
    · have hcommk : (k : Y) * b = b * (k : Y) := by
        apply hψinj
        simpa only [map_mul, hkψ] using hgt
      have hthis := hTI1 b hbA hb1 (k : Y) k.2 hcommk
      exact ⟨by rw [← hkψ, ← map_mul, ← map_mul, hthis a haA],
             by rw [← hkψ, ← map_mul, ← map_mul, hthis b hbA]⟩
    · have hcommk : (k : Y) * (a * b) = (a * b) * (k : Y) := by
        apply hψinj
        simpa only [map_mul, hkψ] using hgt
      have hne : a * b ≠ 1 := by
        intro h
        exact hab (by
          have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this]
          exact inv_eq_of_mul_eq_one_right hb2)
      have hthis := hTI1 (a * b) (A.mul_mem haA hbA) hne (k : Y) k.2 hcommk
      exact ⟨by rw [← hkψ, ← map_mul, ← map_mul, hthis a haA],
             by rw [← hkψ, ← map_mul, ← map_mul, hthis b hbA]⟩
  exact w183finA5FinG3L32B_sound w183finA5_pgl_finG3B
    (a := ψ a) (b := ψ b)
    (by rw [mem_elemsT _ L27.QA_ok, ← hMA]; exact M.actHom_mem L a)
    (by rw [mem_elemsT _ L27.QA_ok, ← hMA]; exact M.actHom_mem L b)
    hψa2 hψa1 hψb2 hψb1 hψab hψc hcp

end CFSG.LocalAnalysis.WeakClosure81

end
