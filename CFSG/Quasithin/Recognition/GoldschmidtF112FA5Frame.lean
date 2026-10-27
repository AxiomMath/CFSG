module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Odd
public import CFSG.Quasithin.Recognition.F112WKernel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace FA5

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

abbrev P1 (L1 L2 S : Subgroup G) : Subgroup G := L1 ⊔ bigB L1 L2 S

abbrev P2 (L1 L2 S : Subgroup G) : Subgroup G := L2 ⊔ bigB L1 L2 S

abbrev Q1 (L1 L2 S : Subgroup G) : Subgroup G := pCoreOf 2 (P1 L1 L2 S)

abbrev Q2 (L1 L2 S : Subgroup G) : Subgroup G := pCoreOf 2 (P2 L1 L2 S)

omit [Finite G] in
theorem P1_le_normalizer_Q1 (L1 L2 S : Subgroup G) :
    P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _

omit [Finite G] in
theorem P2_le_normalizer_Q2 (L1 L2 S : Subgroup G) :
    P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _

structure Frame (L1 L2 S D X : Subgroup G) : Prop where
  pair : Pair L1 L2 S
  card1 : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20
  D_le : D ≤ L2
  D_card : Nat.card D = 3
  D_inf : D ⊓ S = ⊥
  D_norm : D ≤ Subgroup.normalizer (L1 : Set G)
  D_borel : D ≤ borelOf L2 S
  bigB_eq : bigB L1 L2 S = S ⊔ D
  X_le : X ≤ L1
  X_card : Nat.card X = 5
  D_cent : D ≤ Subgroup.centralizer (X : Set G)
  X_mul : ∀ l ∈ L1, ∃ x ∈ X, ∃ b ∈ borelOf L1 S, l = x * b
  untw : ∀ s ∈ S, ∃ l ∈ L2, ∃ q ∈ pCoreOf 2 (P2 L1 L2 S), s = l * q

theorem Pair.exists_frame {L1 L2 S : Subgroup G} (h : Pair L1 L2 S)
    (hc : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20)
    (hu : ∀ s ∈ S, ∃ l ∈ L2, ∃ q ∈ pCoreOf 2 (P2 L1 L2 S), s = l * q) :
    ∃ D X : Subgroup G, Frame L1 L2 S D X := by
  obtain ⟨D, hDL, hD3, hDS, hDN, hsup, hBeq⟩ := h.exists_cartan
  obtain ⟨X, hXL, hX5, hDX, -, hXmul⟩ := h.exists_five hDN hD3
  exact ⟨D, X, ⟨h, hc, hDL, hD3, hDS, hDN, hsup ▸ le_sup_right, hBeq, hXL, hX5, hDX, hXmul, hu⟩⟩

namespace Frame

variable {L1 L2 S D X : Subgroup G} (F : Frame L1 L2 S D X)
include F

theorem sylow_P1 : IsSylowTwoOf S (P1 L1 L2 S) := F112W.isSylowTwoOf_parabolic F.pair.hyp

theorem sylow_P2 : IsSylowTwoOf S (P2 L1 L2 S) := F112W.isSylowTwoOf_parabolic' F.pair.hyp

theorem Q1_le_S : Q1 L1 L2 S ≤ S := isSylowTwoOf_pCoreOf_le F.sylow_P1

theorem Q2_le_S : Q2 L1 L2 S ≤ S := isSylowTwoOf_pCoreOf_le F.sylow_P2

omit [Finite G] in
theorem D_le_B : D ≤ bigB L1 L2 S := F.bigB_eq ▸ le_sup_right

theorem P1_inf_P2 : P1 L1 L2 S ⊓ P2 L1 L2 S = bigB L1 L2 S := F1.parabolic_inf_parabolic F.pair.hyp

omit [Finite G] in
theorem charTwo_P1 : CharTwo (P1 L1 L2 S) := F112W.charTwo_beta F.pair.hyp

theorem charTwo_P2 : CharTwo (P2 L1 L2 S) :=
  (F112W.amalgamHyp_alpha F.pair.hyp).charTwo

omit [Finite G] in
theorem B_le_normalizer_L1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
  (F1.bigB_le_normalizer_left F.pair.hyp).1

omit [Finite G] in
theorem B_le_normalizer_L2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
  (F1.bigB_le_normalizer_left F.pair.hyp).2

theorem normalizes_S : ∀ d ∈ D, ∀ s ∈ S, d * s * d⁻¹ ∈ S := by
  intro d hd s hs
  obtain ⟨l, hl, q, hq, rfl⟩ := F.untw s hs
  have hqS : q ∈ S := F.Q2_le_S hq
  have hlS : l ∈ S := by
    have : l = (l * q) * q⁻¹ := by group
    rw [this]
    exact S.mul_mem hs (S.inv_mem hqS)
  have hdB : d ∈ borelOf L2 S := F.D_borel hd
  have hdN : d ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := hdB.2
  have h1 : d * l * d⁻¹ ∈ S ⊓ L2 :=
    (Subgroup.mem_normalizer_iff.mp hdN l).mp ⟨hlS, hl⟩
  have hdP2 : d ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (F.D_le_B hd)
  have h2 : d * q * d⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (P2_le_normalizer_Q2 L1 L2 S hdP2) q).mp hq
  have : d * (l * q) * d⁻¹ = (d * l * d⁻¹) * (d * q * d⁻¹) := by group
  rw [this]
  exact S.mul_mem h1.1 (F.Q2_le_S h2)

theorem B_le_normalizer_S : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  rw [F.bigB_eq]
  refine sup_le Subgroup.le_normalizer ?_
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => F.normalizes_S d hd s hs, fun hs => ?_⟩
  have := F.normalizes_S d⁻¹ (D.inv_mem hd) _ hs
  simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_mul : ∀ p ∈ P1 L1 L2 S, ∃ x ∈ X, ∃ b ∈ bigB L1 L2 S, p = x * b := by
  intro p hp
  obtain ⟨l, hl, b', hb', rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes F.B_le_normalizer_L1).mp hp
  obtain ⟨x, hx, b, hb, rfl⟩ := F.X_mul l hl
  refine ⟨x, hx, b * b', ?_, by group⟩
  have hle : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  exact (bigB L1 L2 S).mul_mem (hle hb) hb'

theorem pCore_L1_le_Q1 : pCoreOf 2 L1 ≤ Q1 L1 L2 S := by
  have hN : P1 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    le_normalizer_pCoreOf_of_le_normalizer (sup_le Subgroup.le_normalizer F.B_le_normalizer_L1)
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L1).trans le_sup_left) hN
    (pCoreOf_isPGroup 2 L1)

theorem exists_gen : ∃ x0 ∈ X, x0 ^ 5 = 1 ∧ x0 ≠ 1 ∧ ∀ x ∈ X, ∃ j : ℤ, x = x0 ^ j := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXcyc : IsCyclic X := isCyclic_of_prime_card (p := 5) F.X_card
  obtain ⟨⟨x0, hx0⟩, hgen⟩ := hXcyc.exists_generator
  have hx05 : x0 ^ 5 = 1 := by
    have := pow_card_eq_one' (G := ↥X) (x := ⟨x0, hx0⟩)
    rw [F.X_card] at this
    simpa using congrArg Subtype.val this
  have hx01 : x0 ≠ 1 := by
    intro h
    have hall : ∀ x : X, x = 1 := by
      intro x
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
      rw [← hj]
      have : (⟨x0, hx0⟩ : ↥X) = 1 := Subtype.ext h
      rw [this, one_zpow]
    have : Nat.card X = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [hall a, hall b]⟩, ⟨1⟩⟩
    rw [F.X_card] at this
    omega
  refine ⟨x0, hx0, hx05, hx01, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
  exact ⟨j, by simpa using (congrArg Subtype.val hj).symm⟩

theorem mem_P1_of_mem_X {x : G} (hx : x ∈ X) : x ∈ P1 L1 L2 S :=
  (le_sup_left : L1 ≤ P1 L1 L2 S) (F.X_le hx)

theorem mem_P1_of_mem_S {s : G} (hs : s ∈ S) : s ∈ P1 L1 L2 S :=
  (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) ((show S ≤ bigB L1 L2 S from le_sup_right) hs)

theorem mem_B_of_mem_S {s : G} (hs : s ∈ S) : s ∈ bigB L1 L2 S :=
  (show S ≤ bigB L1 L2 S from le_sup_right) hs

theorem inf_kerα_le : S ⊓ F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S) ≤ Q1 L1 L2 S := by
  set K := F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S) with hK
  have hKB : K ≤ bigB L1 L2 S := by
    have := F112W.kerα_le_inf (G₁ := P1 L1 L2 S) (G₂ := P2 L1 L2 S)
    rwa [F.P1_inf_P2] at this
  have hnorm : K ≤ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_inf (hKB.trans F.B_le_normalizer_S) Subgroup.le_normalizer
  have hp : IsPGroup 2 (S ⊓ K : Subgroup G) := F.pair.hyp.hyp.h1.pgroup.to_le inf_le_left
  have hle : S ⊓ K ≤ pCoreOf 2 K := le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hp
  rw [F112W.pCoreOf_kerα (F112W.amalgamHyp_beta F.pair.hyp)] at hle
  exact hle

theorem mem_Q1_of_conj_mem {s : G} (hs : s ∈ S)
    (h : ∀ x ∈ X, x⁻¹ * s * x ∈ bigB L1 L2 S) : s ∈ Q1 L1 L2 S := by
  have hsK : s ∈ F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S) := by
    have hsB : s ∈ bigB L1 L2 S := (show S ≤ bigB L1 L2 S from le_sup_right) hs
    refine ⟨(le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hsB, fun p hp => ?_⟩
    obtain ⟨x, hx, b, hb, rfl⟩ := F.exists_mul p hp
    have h1 : (x * b)⁻¹ * s * (x * b) = b⁻¹ * (x⁻¹ * s * x) * b := by group
    have hB : b⁻¹ * (x⁻¹ * s * x) * b ∈ bigB L1 L2 S :=
      (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb) (h x hx)) hb
    rw [h1, F.P1_inf_P2]
    exact hB
  exact F.inf_kerα_le ⟨hs, hsK⟩

end Frame

end FA5

end CFSG.Quasithin
