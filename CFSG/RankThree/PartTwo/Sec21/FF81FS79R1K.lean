module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1KRed
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79QuoK
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1KCore

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)
open CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_top_quotient_eq_bot :
    CFSG.pPrimeCore 3 (↥(⊤ : Subgroup G) ⧸ (CFSG.pPrimeCore 3 G).subgroupOf ⊤) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : G ⧸ CFSG.pPrimeCore 3 G ≃* ↥(⊤ : Subgroup G) ⧸ (CFSG.pPrimeCore 3 G).subgroupOf ⊤ :=
    QuotientGroup.congr (G' := CFSG.pPrimeCore 3 G) (H' := (CFSG.pPrimeCore 3 G).subgroupOf ⊤)
      Subgroup.topEquiv.symm (by
        ext x
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨(x : G), hx, Subtype.ext rfl⟩)
  have h := CFSG.pPrimeCore_map_iso 3 e
  rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3, Subgroup.map_bot] at h
  exact h.symm

theorem coprime_card_of_pow_mem {Z O : Subgroup G} (hZc : Nat.Coprime 3 (Nat.card Z))
    (hO : ∀ o ∈ O, ∃ m : ℕ, Nat.Coprime 6 m ∧ o ^ m ∈ Z) : Nat.Coprime 3 (Nat.card O) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥O) 3 hd
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨m, hm6, hmZ⟩ := hO (x : G) x.2
  have hm3 : Nat.Coprime 3 m := Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) hm6
  have hord : orderOf ((x : G) ^ m) = 3 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hxG]; exact hm3), hxG]
  exact not_mem_of_coprime hZc hord hmZ

theorem kf_fs79Prop2OneK_of (hKF1 : FF84KF1) (hKS : FF84KSOut) : KF_FS79Prop2OneK := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro G _ _ hK
  refine (prop2OneAt_iff G).mpr fun b t c J h => ?_
  set Z : Subgroup G := CFSG.pPrimeCore 3 G with hZdef
  have hZc : Nat.Coprime 3 (Nat.card Z) := CFSG.pPrimeCore_coprime_card
  have D := h.qdata_top (Z := Z) hZc
  have hR1 : ∀ (G' : Type) [Group G'] [Finite G'],
      (KCore.KGroupNonab InCatalog G' ∧ CFSG.pPrimeCore 3 G' = ⊥) → Prop2OneAt G' := by
    intro G' _ _ hP
    refine (prop2OneAt_iff G').mpr fun b' t' c' J' h' => ?_
    have htop := h'.nor_eq_top hKF1 hKS hP.1 hP.2
    ext g
    simp only [Set.mem_univ, iff_true]
    exact ⟨1, Subgroup.one_mem _, g, by rw [htop]; exact Subgroup.mem_top g, (one_mul g).symm⟩
  obtain ⟨O, hZO, -, hOn, hOm, hdec⟩ := D.conclusionP
    (fun G' _ _ => KCore.KGroupNonab InCatalog G' ∧ CFSG.pPrimeCore 3 G' = ⊥) hR1
    ⟨kGroupNonab_quotient hK ⊤ _, pPrimeCore_top_quotient_eq_bot⟩
  have hOc : Nat.Coprime 3 (Nat.card O) := coprime_card_of_pow_mem hZc hOm
  have hOle : O ≤ Opp 3 (⊤ : Subgroup G) := L14.le_Opp_of_normalized le_top hOn hOc
  ext g
  simp only [Set.mem_univ, iff_true]
  obtain ⟨o, ho, n, hn, rfl⟩ := hdec g (Subgroup.mem_top g)
  obtain ⟨z, hz, n', hn', rfl⟩ := nor_sup_decomp h.ord_b hZc hn.2
  exact ⟨o * z, hOle (O.mul_mem ho (hZO hz)), n', hn', by group⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
