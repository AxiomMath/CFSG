module

public import CFSG.OddTranspositions.PartThree.Nine.Statements
public import CFSG.Fischer.Uniq.Graph
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import CFSG.Fischer.Classification.SRG.Conference
import CFSG.OddTranspositions.O4PairCommSet
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ CFSG.Fischer

theorem not_isSquare_srg_discriminant {q s m j : ℕ} (hq : q = 2 ^ m) (hm : 2 ≤ m)
    (hs : s = q ^ j + 1) : ¬ IsSquare (((q : ℤ) - 3) ^ 2 + 4 * ((s : ℤ) * (q - 1) - 1)) := by
  rintro ⟨c, hc⟩
  obtain ⟨m, rfl⟩ : ∃ m' : ℕ, m = m' + 2 := ⟨m - 2, by omega⟩
  subst hq hs
  push_cast at hc
  set x : ℤ := 2 ^ (m + 2) - 1 with hx
  have hcop : IsCoprime x (x + 4 * (2 ^ (m + 2)) ^ j) := by
    have h2 : IsCoprime x 2 := ⟨-1, 2 ^ (m + 1), by rw [hx]; ring⟩
    have h' := (h2.pow_right (n := (m + 2) * j + 2)).mul_add_left_right 1
    rwa [mul_one, pow_add, pow_mul, mul_comm] at h'
  obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop (c := c) (by rw [hx]; linear_combination hc)
  · have h := congrArg (Int.cast : ℤ → ZMod 4) ha
    rw [hx] at h
    push_cast at h
    rw [pow_add, show (2 : ZMod 4) ^ 2 = 0 from rfl, mul_zero, zero_sub] at h
    generalize (a : ZMod 4) = b at h
    revert b
    decide
  · have hpos : (0 : ℤ) < x := by
      rw [hx]
      have : (4 : ℤ) ≤ 2 ^ (m + 2) := by
        rw [pow_add]
        nlinarith [one_le_pow₀ (M₀ := ℤ) (a := 2) (n := m) (by norm_num)]
      linarith
    nlinarith [sq_nonneg a]

theorem not_isSRGWith {V : Type*} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {n q s m j : ℕ} (hq : q = 2 ^ m) (hm : 2 ≤ m) (hs : s = q ^ j + 1) (hn : 0 < n) :
    ¬ Γ.IsSRGWith n (s * (q - 1)) (q - 2) 1 := by
  intro h
  have hq4 : 4 ≤ q := hq ▸ (Nat.pow_le_pow_right two_pos hm : 2 ^ 2 ≤ 2 ^ m)
  have hsq : ¬ IsSquare ((((q - 2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) ^ 2 +
      4 * (((s * (q - 1) : ℕ) : ℤ) - ((1 : ℕ) : ℤ))) := by
    have h := not_isSquare_srg_discriminant hq hm hs
    rwa [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ q), Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_one, Nat.cast_ofNat, show (q : ℤ) - 2 - 1 = q - 3 by ring]
  obtain ⟨-, h2⟩ := h.conference_of_not_isSquare hn hsq
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ q), Nat.cast_sub (by omega : 1 ≤ q)] at h2
  have hs1 : (1 : ℤ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hq4' : (4 : ℤ) ≤ q := by exact_mod_cast hq4
  push_cast at h2
  nlinarith

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commSet_inter_nonempty_of_theorem8_7 (h87 : Theorem8_7) (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d})
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : ¬ Commute a b) :
    (commSet D a ∩ commSet D b).Nonempty := by
  have hcls : ∀ x ∈ D, ({x} : Set G) ∈ blockClass hC.alpha := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
    rw [hα]
    exact ⟨ConjAct.toConjAct c, by rw [Set.smul_set_singleton, ConjAct.toConjAct_smul, hc]⟩
  rcases h87 G D hC hrad hO4 {a} (hcls a ha) {b} (hcls b hb) with h | h | ⟨δ, hδa, hδb⟩
  · obtain rfl := Set.singleton_eq_singleton_iff.mp h
    exact absurd (Commute.refl a) hab
  · exact absurd (h.2.2.2 a (Set.mem_singleton a) b (Set.mem_singleton b)) hab
  · obtain ⟨⟨g, rfl⟩, hδD, hδne, hδc⟩ := hδa
    obtain ⟨-, -, hδne', hδc'⟩ := hδb
    rw [Set.smul_set_singleton] at hδD hδne hδc hδne' hδc'
    have heD : g • a ∈ D := hδD (Set.mem_singleton _)
    refine ⟨g • a, ⟨heD, ?_, fun h => hδne (by rw [h])⟩, heD, ?_, fun h => hδne' (by rw [h])⟩
    · exact (hδc a (Set.mem_singleton a) _ (Set.mem_singleton _)).symm
    · exact (hδc' b (Set.mem_singleton b) _ (Set.mem_singleton _)).symm

theorem isSRGWith_commGraph (h87 : Theorem8_7) (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    [Fintype D] [DecidableRel (commGraph D).Adj] {k q : ℕ} (hk : (commSet D hC.d).ncard = k)
    (hlam : ∀ v ∈ commSet D hC.d,
      ({e | e ∈ D ∧ Commute e hC.d} ∩ {e | e ∈ D ∧ Commute e v}).ncard = q)
    (hmu : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Subsingleton) :
    (commGraph D).IsSRGWith D.ncard k (q - 2) 1 := by
  classical
  have hmem : ∀ g a x : G, x ∈ commSet D (g * a * g⁻¹) ↔ g⁻¹ * x * g ∈ commSet D a := by
    intro g a x
    have hD : x ∈ D ↔ g⁻¹ * x * g ∈ D :=
      ⟨fun h => by simpa using hC.setup.conj_mem g⁻¹ h,
        fun h => by simpa [mul_assoc] using hC.setup.conj_mem g h⟩
    have hc : Commute x (g * a * g⁻¹) ↔ Commute (g⁻¹ * x * g) a := by
      rw [← Commute.conj_iff g⁻¹, inv_inv, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
    have hne : x ≠ g * a * g⁻¹ ↔ g⁻¹ * x * g ≠ a := by
      refine not_congr ⟨fun h => ?_, fun h => ?_⟩
      · rw [h]; group
      · rw [← h]; group
    simp only [commSet, Set.mem_setOf_eq]
    rw [hD, hc, hne]
  have htr : ∀ g a b : G, (commSet D (g * a * g⁻¹) ∩ commSet D (g * b * g⁻¹)).ncard =
      (commSet D a ∩ commSet D b).ncard := by
    intro g a b
    have himg : commSet D (g * a * g⁻¹) ∩ commSet D (g * b * g⁻¹) =
        (fun y => g * y * g⁻¹) '' (commSet D a ∩ commSet D b) := by
      ext x
      rw [Set.mem_inter_iff, hmem, hmem]
      constructor
      · intro h
        exact ⟨g⁻¹ * x * g, h, by group⟩
      · rintro ⟨y, hy, rfl⟩
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    rw [himg]
    exact Set.ncard_image_of_injective _ fun y z h => by simpa using h
  have hloc : ∀ a : G, CFSG.Blueprint.Fischer.LocalClass D a = commSet D a := by
    intro a
    ext f
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩⟩
  have hcard : ∀ (S : Set D) {_ : Fintype S}, Fintype.card S = (Subtype.val '' S).ncard := by
    intro S _
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq]
  have hcommon : ∀ a b : D, Subtype.val '' (commGraph D).commonNeighbors a b =
      commSet D a ∩ commSet D b := by
    intro a b
    rw [SimpleGraph.commonNeighbors, Set.image_inter Subtype.val_injective, image_neighborSet,
      image_neighborSet, hloc, hloc]
  have hconj : ∀ a ∈ D, ∃ g : G, g * a * g⁻¹ = hC.d := fun a ha =>
    isConj_iff.mp (hC.setup.isConj ha hC.hd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  · intro a
    obtain ⟨g, hg⟩ := hconj a a.2
    rw [← SimpleGraph.card_neighborSet_eq_degree, hcard, image_neighborSet, hloc, ← hk, ← hg,
      ← Set.inter_self (commSet D (g * a * g⁻¹)), htr, Set.inter_self]
  · intro a b hab
    obtain ⟨g, hg⟩ := hconj a a.2
    obtain ⟨hne, hcomm⟩ := commGraph_adj_iff.mp hab
    rw [hcard, hcommon, ← htr g, hg]
    have hvu : Commute (g * b * g⁻¹) hC.d := by
      rw [← hg]
      exact (Commute.conj_iff g).mpr (Commute.symm hcomm)
    have hvne : g * (b : G) * g⁻¹ ≠ hC.d := by
      rw [← hg]
      exact fun h => hne (by simpa using h.symm)
    have hv : g * (b : G) * g⁻¹ ∈ commSet D hC.d := ⟨hC.setup.conj_mem g b.2, hvu, hvne⟩
    have heq : commSet D hC.d ∩ commSet D (g * b * g⁻¹) =
        ({e | e ∈ D ∧ Commute e hC.d} ∩ {e | e ∈ D ∧ Commute e (g * b * g⁻¹)}) \
          {hC.d, g * (b : G) * g⁻¹} := by
      ext e
      simp only [commSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    have hsub : ({hC.d, g * (b : G) * g⁻¹} : Set G) ⊆
        {e | e ∈ D ∧ Commute e hC.d} ∩ {e | e ∈ D ∧ Commute e (g * b * g⁻¹)} := by
      rintro e (rfl | rfl)
      · exact ⟨⟨hC.hd, Commute.refl _⟩, hC.hd, hvu.symm⟩
      · exact ⟨⟨hv.1, hvu⟩, hv.1, Commute.refl _⟩
    rw [heq, Set.ncard_diff hsub, Set.ncard_pair hvne.symm, hlam _ hv]
  · intro a b hne hnadj
    obtain ⟨g, hg⟩ := hconj a a.2
    have hab : ¬ Commute (a : G) b := fun h =>
      hnadj (commGraph_adj_iff.mpr ⟨fun h' => hne (Subtype.ext h'), h.eq⟩)
    rw [hcard, hcommon, ← htr g, hg]
    have hwD : g * (b : G) * g⁻¹ ∈ D := hC.setup.conj_mem g b.2
    have hwu : ¬ Commute (g * b * g⁻¹) hC.d := by
      rw [← hg, Commute.conj_iff]
      exact fun h => hab h.symm
    obtain ⟨e, he⟩ := commSet_inter_nonempty_of_theorem8_7 h87 hC hα hrad hO4 hC.hd hwD
      fun h => hwu h.symm
    exact Set.ncard_eq_one.mpr ⟨e, (hmu _ hwD hwu).eq_singleton_of_mem he⟩

theorem false_of_commSet_inter_subsingleton (h87 : Theorem8_7) (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {q s m j : ℕ} (hq : q = 2 ^ m) (hm : 2 ≤ m) (hs : s = q ^ j + 1) (hj : 1 ≤ j)
    (hk : (commSet D hC.d).ncard = s * (q - 1))
    (hlam : ∀ v ∈ commSet D hC.d,
      ({e | e ∈ D ∧ Commute e hC.d} ∩ {e | e ∈ D ∧ Commute e v}).ncard = q)
    (hmu : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Subsingleton) :
    False := by
  classical
  have : Fintype D := Fintype.ofFinite D
  have hq4 : 4 ≤ q := hq ▸ (Nat.pow_le_pow_right two_pos hm : 2 ^ 2 ≤ 2 ^ m)
  have hqj : q ≤ q ^ j := Nat.le_self_pow (by omega) q
  have hk10 : 10 < s * (q - 1) := by
    have h5 : 5 ≤ s := by omega
    have h3 : 3 ≤ q - 1 := by omega
    nlinarith
  have hO4 : ¬ O4PairData G D := fun h => by
    have := ncard_commSet_of_o4PairData h hC.hd
    omega
  exact not_isSRGWith hq hm hs ((Set.ncard_pos (Set.toFinite D)).2 ⟨hC.d, hC.hd⟩)
    (isSRGWith_commGraph h87 hC hα hrad hO4 hk hlam hmu)

end CFSG.OddTranspositions.PartThree.Nine
