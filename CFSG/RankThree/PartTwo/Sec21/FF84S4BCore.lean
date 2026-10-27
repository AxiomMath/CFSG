module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3B
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

private theorem comm_of_mem_elemAb {E : Subgroup G} [IsElementaryAbelian 3 E] {x e : G}
    (hx : x ∈ E) (he : e ∈ E) : x * e = e * x := by
  have h : (⟨x, hx⟩ : E) * ⟨e, he⟩ = ⟨e, he⟩ * ⟨x, hx⟩ :=
    IsMulCommutative.is_comm.comm _ _
  exact congrArg Subtype.val h

private theorem not_three_dvd_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  intro h
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem B_gen_centralizers {E X : Subgroup G} [IsElementaryAbelian 3 E] (hE : 9 ≤ Nat.card E)
    (hX : IsPGroup 2 X) (hEX : E ≤ Nor X) :
    X ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), X ⊓ Cen a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.le_iSup_centralizer_of_coprime
    (p := 3) (A := E) (U := X) (by simpa using hE) (not_three_dvd_of_isPGroup_two hX) hEX

theorem B_max_of_centralizers {E Y X : Subgroup G} [IsElementaryAbelian 3 E] (hE : 9 ≤ Nat.card E)
    (hX : X ≤ Y ∧ IsPGroup 2 X ∧ E ≤ Nor X)
    (hmax : ∀ e ∈ E, e ≠ 1 → X ⊓ Cen e ∈ PiStar (Y ⊓ Cen e) E 2) :
    X ∈ PiStar Y E 2 := by
  obtain ⟨hXY, hX2, hEX⟩ := hX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [PiStar, Set.mem_setOf_eq]
  refine ⟨hXY, hX2, hEX, fun V hXV hVY hV2 hEV => ?_⟩
  have hcen : ∀ e ∈ E, e ≠ 1 → V ⊓ Cen e = X ⊓ Cen e := by
    intro e he he1
    have hECe : E ≤ Cen e := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2 (comm_of_mem_elemAb hx he)
    have hEN : E ≤ Nor (V ⊓ Cen e) := by
      intro x hx
      have h1 : x ∈ Nor V := hEV hx
      have h2 : x ∈ Nor (Cen e) := Subgroup.le_normalizer (hECe hx)
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro g
      rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 g, h2 g]
    exact (hmax e he he1).2.2.2 (V ⊓ Cen e) (inf_le_inf_right _ hXV) (inf_le_inf_right _ hVY)
      hV2.to_inf_left hEN
  have hp : ¬ 3 ∣ Nat.card V := not_three_dvd_of_isPGroup_two hV2
  have hgen : V ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), V ⊓ Cen a :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.le_iSup_centralizer_of_coprime
      (p := 3) (A := E) (U := V) (by simpa using hE) hp hEV
  have hVX : V ≤ X := by
    refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    exact (le_of_eq (hcen a ha ha1)).trans inf_le_left
  exact le_antisymm hVX hXV

theorem B_PQ {p : ℕ} [Fact p.Prime] (P Q B : Subgroup G) (hPp : IsPGroup p P) (hBp : IsPGroup p B)
    (hQ : Nat.Coprime p (Nat.card Q)) (hPB : P ≤ Nor B) (hQB : Q ≤ Nor B) (hPQ : ⁅P, Q⁆ = ⊥)
    (hfix : B ⊓ CenS P ≤ CenS Q) : ⁅B, Q⁆ = ⊥ :=
  CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q P Q B hPp hBp hQ hPB hQB hPQ hfix

theorem B_charTwo (hc : CFSG.Assembly.IsCharTwoType G) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hX1 : X ≠ ⊥) : Nor X ⊓ CenS (Op 2 (Nor X)) ≤ Op 2 (Nor X) :=
  S3.B_charTwo hc X hX1 hX

theorem B_charTwo_cen (hc : CFSG.Assembly.IsCharTwoType G) {t : G} (ht : orderOf t = 2) :
    Cen t ⊓ CenS (Op 2 (Cen t)) ≤ Op 2 (Cen t) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hQ2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have hQ1 : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    have hmem := Subgroup.mem_zpowers t
    rw [h, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  have hNQ : Nor (Subgroup.zpowers t) = Cen t := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have htQ : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      have hgt := (Subgroup.mem_normalizer_iff.1 hg t).1 htQ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgt
      have hmod : t ^ (k % 2) = t ^ k := by
        have := zpow_mod_orderOf t k
        rw [ht] at this
        simpa using this
      have hgt' : g * t * g⁻¹ = t := by
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · exfalso
          have hne : g * t * g⁻¹ ≠ 1 := by
            intro h1
            apply ht1
            calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
              _ = 1 := by rw [h1]; group
          rw [← hk, ← hmod, h0, zpow_zero] at hne
          exact hne rfl
        · rw [← hk, ← hmod, h1, zpow_one]
      rw [mul_inv_eq_iff_eq_mul] at hgt'
      exact hgt'
    · intro hg
      have hcomm : Commute g t := hg
      have hfix : ∀ y ∈ Subgroup.zpowers t, g * y * g⁻¹ = y := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        rw [(hcomm.zpow_right k).eq]
        group
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hfix h hh]
        exact hh
      · intro hh
        set y := g * h * g⁻¹ with hydef
        have hy : g * y = y * g := by
          have := hfix y hh
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this
        have hh' : h = y := by
          calc h = g⁻¹ * y * g := by rw [hydef]; group
            _ = y := by
              calc g⁻¹ * y * g = g⁻¹ * (y * g) := by group
                _ = g⁻¹ * (g * y) := by rw [hy]
                _ = y := by group
        rw [hh']
        exact hh
  have key := B_charTwo hc hQ2 hQ1
  rw [hNQ] at key
  exact key

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
