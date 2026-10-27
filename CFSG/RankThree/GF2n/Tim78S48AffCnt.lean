module

public import Mathlib.GroupTheory.Index
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.RankThree.GF2n.Tim78

open scoped commutatorElement

variable {G : Type} [Group G]

open _root_.Classical in
private noncomputable def signChar (F : Subgroup G) (u : G) : ℂˣ := if u ∈ F then 1 else -1

private theorem signChar_eq_one_iff (F : Subgroup G) (u : G) : signChar F u = 1 ↔ u ∈ F := by
  unfold signChar
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    intro h1
    have := congrArg Units.val h1
    norm_num at this

private theorem signChar_one (F : Subgroup G) : signChar F 1 = 1 :=
  (signChar_eq_one_iff F 1).mpr F.one_mem

private theorem commutator_mul_left' (y x p : G) :
    ⁅y * x, p⁆ = y * ⁅x, p⁆ * y⁻¹ * ⁅y, p⁆ := by
  simp only [commutatorElement_def]; group

private theorem commutator_mul_right' (y p p' : G) :
    ⁅y, p * p'⁆ = ⁅y, p⁆ * (p * ⁅y, p'⁆ * p⁻¹) := by
  simp only [commutatorElement_def]; group

section Finite

variable [Finite G]

private theorem index_subgroupOf_eq_two' {B F : Subgroup G} (hFB : F ≤ B)
    (hF2 : Nat.card F * 2 = Nat.card B) : (F.subgroupOf B).index = 2 := by
  have h1 := Subgroup.card_mul_index (F.subgroupOf B)
  have h2 : Nat.card (F.subgroupOf B) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFB).toEquiv
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hF2.symm)

private theorem signChar_mul {B F : Subgroup G} (hFB : F ≤ B)
    (hF2 : Nat.card F * 2 = Nat.card B) {u v : G} (hu : u ∈ B) (hv : v ∈ B) :
    signChar F (u * v) = signChar F u * signChar F v := by
  have key : u * v ∈ F ↔ (u ∈ F ↔ v ∈ F) :=
    Subgroup.mul_mem_iff_of_index_two (index_subgroupOf_eq_two' hFB hF2)
      (a := ⟨u, hu⟩) (b := ⟨v, hv⟩)
  unfold signChar
  by_cases h1 : u ∈ F
  · by_cases h2 : v ∈ F
    · rw [if_pos h1, if_pos h2, if_pos (key.mpr (iff_of_true h1 h2)), mul_one]
    · rw [if_pos h1, if_neg h2, if_neg fun h => h2 ((key.mp h).mp h1), one_mul]
  · by_cases h2 : v ∈ F
    · rw [if_neg h1, if_pos h2, if_neg fun h => h1 ((key.mp h).mpr h2), mul_one]
    · rw [if_neg h1, if_neg h2, if_pos (key.mpr (iff_of_false h1 h2))]
      simp

private theorem relIndex_le_and_surj {P B C : Subgroup G}
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (η : G → G) (hηC : ∀ p ∈ P, η p ∈ C) (hηB : ∀ p ∈ C, η p ∈ B)
    (hηmul : ∀ p ∈ P, ∀ p' ∈ P, ∃ β ∈ B, η (p * p') = η p * η p' * β)
    (hηker : ∀ p ∈ P, η p ∈ B → p ∈ C) :
    C.relIndex P ≤ B.relIndex C ∧
      (C.relIndex P = B.relIndex C → ∀ c ∈ C, ∃ p ∈ P, ∃ β ∈ B, η p = c * β) := by
  haveI : IsMulCommutative C :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hCab a a.2 b b.2)
  let e : P → C := fun p => ⟨η p, hηC p p.2⟩
  let φ : P →* C ⧸ B.subgroupOf C := MonoidHom.mk'
    (fun p : P => (QuotientGroup.mk (e p) : C ⧸ B.subgroupOf C)) (fun p p' => by
      obtain ⟨β, hβ, h⟩ := hηmul p p.2 p' p'.2
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((e (p * p'))⁻¹ * (e p * e p') : C) : G) = β⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, e]
        rw [h]; group
      rw [this]
      exact B.inv_mem hβ)
  have hker : φ.ker = C.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk (e p) : C ⧸ B.subgroupOf C) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => hηker p p.2 h, fun h => hηB p h⟩
  have hidx : C.relIndex P = Nat.card φ.range := by
    rw [← Subgroup.index_ker φ, hker]; rfl
  have hle : Nat.card φ.range ≤ Nat.card (C ⧸ B.subgroupOf C) :=
    Subgroup.card_le_card_group φ.range
  have hB : B.relIndex C = Nat.card (C ⧸ B.subgroupOf C) := Subgroup.index_eq_card _
  refine ⟨hidx.trans_le (hle.trans_eq hB.symm), fun heq c hc => ?_⟩
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← hidx, heq, hB]
  have hmem : (QuotientGroup.mk (⟨c, hc⟩ : C) : C ⧸ B.subgroupOf C) ∈ φ.range := by
    rw [hrange]; trivial
  obtain ⟨p, hp⟩ := hmem
  have h2 : (e p)⁻¹ * (⟨c, hc⟩ : C) ∈ B.subgroupOf C := QuotientGroup.eq.mp hp
  rw [Subgroup.mem_subgroupOf] at h2
  refine ⟨p, p.2, c⁻¹ * η p, ?_, by group⟩
  have := B.inv_mem h2
  simpa [e] using this

open IsMulCommutative in
private theorem relIndex_le_relIndex {P B C F : Subgroup G}
    (hBC : B ≤ C) (hCP : C ≤ P)
    (hcommP : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ B)
    (hBcent : ∀ b ∈ B, ∀ p ∈ P, b * p = p * b)
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hFB : F ≤ B) (hF2 : Nat.card F * 2 = Nat.card B)
    (hZ : ∀ y ∈ P, (∀ p ∈ P, ⁅y, p⁆ ∈ F) → y ∈ B) :
    B.relIndex C ≤ C.relIndex P := by
  have hcen : ∀ b ∈ B, ∀ x ∈ P, x * b * x⁻¹ = b := fun b hb x hx => by
    rw [← hBcent b hb x hx]; group
  have h2 : ∀ z ∈ P, ∀ p ∈ P, ∀ p' ∈ P, ⁅z, p * p'⁆ = ⁅z, p⁆ * ⁅z, p'⁆ :=
    fun z hz p hp p' hp' => by
      rw [commutator_mul_right', hcen _ (hcommP z hz p' hp') p hp]
  have h1 : ∀ z ∈ P, ∀ x ∈ P, ∀ p ∈ P, ⁅z * x, p⁆ = ⁅x, p⁆ * ⁅z, p⁆ :=
    fun z hz x hx p hp => by
      rw [commutator_mul_left', hcen _ (hcommP x hx p hp) z hz]
  have hone : ∀ n ∈ B, ∀ z ∈ P, ⁅n, z⁆ = 1 := fun n hn z hz =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hBcent n hn z hz)
  have hCone : ∀ c ∈ C, ∀ c' ∈ C, ⁅c, c'⁆ = 1 := fun c hc c' hc' =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hCab c hc c' hc')
  set N : Subgroup P := C.subgroupOf P
  have hN : ∀ a b : P, ⁅a, b⁆ ∈ N := fun a b =>
    Subgroup.mem_subgroupOf.mpr (hBC (hcommP _ a.2 _ b.2))
  haveI : N.Normal := ⟨fun n hn g => by
    have h := N.mul_mem (hN g n) hn
    simpa [commutatorElement_def, mul_assoc] using h⟩
  haveI : IsMulCommutative (P ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      rw [commutator_eq_closure]
      exact (Subgroup.closure_le N).mpr (by rintro _ ⟨a, b, rfl⟩; exact hN a b))
  have hmul : ∀ c : C, ∀ p p' : P, signChar F ⁅(c : G), ((p * p' : P) : G)⁆ =
      signChar F ⁅(c : G), (p : G)⁆ * signChar F ⁅(c : G), (p' : G)⁆ := fun c p p' => by
    rw [Subgroup.coe_mul, h2 _ (hCP c.2) _ p.2 _ p'.2,
      signChar_mul hFB hF2 (hcommP _ (hCP c.2) _ p.2) (hcommP _ (hCP c.2) _ p'.2)]
  let χ : C → (P ⧸ N) →* ℂˣ := fun c => QuotientGroup.lift N
    (MonoidHom.mk' (fun p : P => signChar F ⁅(c : G), (p : G)⁆) (hmul c)) (fun n hn => by
      change signChar F ⁅(c : G), (n : G)⁆ = 1
      rw [hCone _ c.2 _ (Subgroup.mem_subgroupOf.mp hn), signChar_one])
  let ψ : C →* ((P ⧸ N) →* ℂˣ) := MonoidHom.mk' χ (fun c c' =>
    MonoidHom.ext fun x => QuotientGroup.induction_on x fun p => by
      change signChar F ⁅((c * c' : C) : G), (p : G)⁆ =
        signChar F ⁅(c : G), (p : G)⁆ * signChar F ⁅(c' : G), (p : G)⁆
      rw [Subgroup.coe_mul, h1 _ (hCP c.2) _ (hCP c'.2) _ p.2,
        signChar_mul hFB hF2 (hcommP _ (hCP c'.2) _ p.2) (hcommP _ (hCP c.2) _ p.2), mul_comm])
  have hker : ψ.ker = B.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine hZ _ (hCP c.2) fun p hp => ?_
      have := DFunLike.congr_fun h ((⟨p, hp⟩ : P) : P ⧸ N)
      exact (signChar_eq_one_iff F _).mp this
    · intro hcB
      refine MonoidHom.ext fun x => QuotientGroup.induction_on x fun p => ?_
      change signChar F ⁅(c : G), (p : G)⁆ = 1
      rw [hone _ hcB _ p.2, signChar_one]
  haveI : NeZero ((Monoid.exponent (P ⧸ N) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card ((P ⧸ N) →* ℂˣ) = Nat.card (P ⧸ N) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (P ⧸ N) ℂ
  haveI : Finite ((P ⧸ N) →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  calc B.relIndex C = ψ.ker.index := by rw [hker]; rfl
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ ≤ Nat.card ((P ⧸ N) →* ℂˣ) := Subgroup.card_le_card_group ψ.range
    _ = Nat.card (P ⧸ N) := hcard
    _ = N.index := (Subgroup.index_eq_card N).symm
    _ = C.relIndex P := rfl

end Finite

theorem card_eq_mul_relIndex [Finite G] {P B C F : Subgroup G}
    (hBC : B ≤ C) (hCP : C ≤ P)
    (hcommP : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ B)
    (hBcent : ∀ b ∈ B, ∀ p ∈ P, b * p = p * b)
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hFB : F ≤ B) (hF2 : Nat.card F * 2 = Nat.card B)
    (hZ : ∀ y ∈ P, (∀ p ∈ P, ⁅y, p⁆ ∈ F) → y ∈ B)
    (η : G → G) (hηC : ∀ p ∈ P, η p ∈ C) (hηB : ∀ p ∈ C, η p ∈ B)
    (hηmul : ∀ p ∈ P, ∀ p' ∈ P, ∃ β ∈ B, η (p * p') = η p * η p' * β)
    (hηker : ∀ p ∈ P, η p ∈ B → p ∈ C) :
    Nat.card C = Nat.card B * C.relIndex P ∧
      ∀ c ∈ C, ∃ p ∈ P, ∃ β ∈ B, η p = c * β := by
  obtain ⟨hle, hsurj⟩ := relIndex_le_and_surj hCab η hηC hηB hηmul hηker
  have heq : C.relIndex P = B.relIndex C :=
    le_antisymm hle (relIndex_le_relIndex hBC hCP hcommP hBcent hCab hFB hF2 hZ)
  refine ⟨?_, hsurj heq⟩
  have h1 := Subgroup.card_mul_index (B.subgroupOf C)
  have h2 : Nat.card (B.subgroupOf C) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  rw [h2] at h1
  rw [heq]
  exact h1.symm

end CFSG.RankThree.GF2n.Tim78
