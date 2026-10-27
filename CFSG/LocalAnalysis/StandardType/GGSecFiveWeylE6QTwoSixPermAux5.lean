module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrame
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem e6QTwoSix_C0_le_sup_Z
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    Subgroup.centralizer (L : Set G) ⊓ (L ⊔ Bs) ≤
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer (L : Set G)
  set Z : Subgroup G := L ⊓ C
  set C0 : Subgroup G := C ⊓ (L ⊔ Bs)
  have hCL : C ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G)
  have hcardZ : Nat.card ↥(Bs ⊓ (L ⊔ C)) = 3 ^ 5 :=
    card_inf_sup_centralizer_of_card_six hK θ hperf hBs hcard hx hBL hNL hI
  have hbut := card_inf_sup_mul_card_inf (B := Bs) (C := C) hNL hCL
  have hbut' : Nat.card ↥C0 * Nat.card ↥(Bs ⊓ L) = Nat.card ↥Z * 3 ^ 5 := by
    change Nat.card ↥(C ⊓ (L ⊔ Bs)) * Nat.card ↥(Bs ⊓ L) =
      Nat.card ↥(L ⊓ C) * 3 ^ 5
    rw [hcardZ] at hbut
    rwa [inf_comm C L] at hbut
  have hZleC0 : Z ≤ C0 := by
    change L ⊓ C ≤ C ⊓ (L ⊔ Bs)
    exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
  have hxC : x ∈ C := by
    have hxzp : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    rw [← hBL] at hxzp
    exact hxzp.2
  have hxC0 : x ∈ C0 := Subgroup.mem_inf.mpr ⟨hxC, Subgroup.mem_sup_right hx⟩
  have hP1 := e6QTwoSix_card_inf_L_of_card_six hK θ hperf hBs hcard hx hx1 hBL hstar hNL hI hLx
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  by_cases hxL : x ∈ L
  ·
    have h35 : 3 ^ 5 ≤ Nat.card ↥(Bs ⊓ L) := hP1.2 hxL
    have hle : Nat.card ↥C0 ≤ Nat.card ↥Z := by
      have h1 : Nat.card ↥C0 * 3 ^ 5 ≤ Nat.card ↥Z * 3 ^ 5 := by
        calc Nat.card ↥C0 * 3 ^ 5
            ≤ Nat.card ↥C0 * Nat.card ↥(Bs ⊓ L) := Nat.mul_le_mul_left _ h35
          _ = Nat.card ↥Z * 3 ^ 5 := hbut'
      exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
    have hEq : C0 = Z := (Subgroup.eq_of_le_of_card_ge hZleC0 hle).symm
    rw [hEq]
    exact le_sup_right
  ·
    have h34 : 3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) := hP1.1
    have hle : Nat.card ↥C0 ≤ 3 * Nat.card ↥Z := by
      have h1 : Nat.card ↥C0 * 3 ^ 4 ≤ Nat.card ↥Z * 3 ^ 5 := by
        calc Nat.card ↥C0 * 3 ^ 4
            ≤ Nat.card ↥C0 * Nat.card ↥(Bs ⊓ L) := Nat.mul_le_mul_left _ h34
          _ = Nat.card ↥Z * 3 ^ 5 := hbut'
      have h2 : Nat.card ↥Z * 3 ^ 5 = 3 * Nat.card ↥Z * 3 ^ 4 := by ring
      rw [h2] at h1
      exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
    have hxnotZ : x ∉ Z := fun hxz => hxL hxz.1
    have hxInter : Subgroup.zpowers x ⊓ Z = ⊥ := by
      have hIdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ∣ 3 := by
        rw [← hxcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hIne : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ≠ 3 := by
        intro h3
        have heq : Subgroup.zpowers x ⊓ Z = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hxcard])
        exact hxnotZ (Subgroup.zpowers_le.mp (inf_eq_left.mp heq))
      have hI1 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) = 1 := by
        rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hIdvd) with h | h
        · exact h
        · exact absurd h hIne
      exact Subgroup.eq_bot_of_card_eq (H := Subgroup.zpowers x ⊓ Z) hI1
    have hcardSup : Nat.card ↥(Subgroup.zpowers x ⊔ Z) = 3 * Nat.card ↥Z := by
      have hsupnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set G) :=
        (Subgroup.zpowers_le.mpr hx).trans (e6QTwoSixNormalizesCenter hNL)
      have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := Subgroup.zpowers x) (K := Z) hsupnorm
      rw [hxInter, Subgroup.card_bot, mul_one, hxcard] at h
      exact h
    have hsup_le : Subgroup.zpowers x ⊔ Z ≤ C0 :=
      sup_le (Subgroup.zpowers_le.mpr hxC0) hZleC0
    have hcard_le : Nat.card ↥(Subgroup.zpowers x ⊔ Z) ≤ Nat.card ↥C0 :=
      Subgroup.card_le_of_le hsup_le
    have hEq : C0 = Subgroup.zpowers x ⊔ Z :=
      (Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hcardSup]; exact hle)).symm
    rw [hEq]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hx)) le_sup_right

end CFSG.StandardType.E6QTwo

end