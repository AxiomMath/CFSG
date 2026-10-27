module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Cov
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

@[expose] def S16t3CoverL (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Lb : Subgroup (MulAut (Vtil V₀ V hV))) (Y : Subgroup G) : Prop :=
  Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧ barSub V₀ V hV Y = Lb ∧ Group.IsPerfect ↥Y ∧
    CFSG.pCore 2 ↥Y ≤ (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y ∧
    ((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ≤
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
    (∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) → p = 2 ∨ p = 3) ∧
    ∀ x ∈ Y ⊓ F11.CTilde D.M V₀ V, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1

@[expose] def S16t3CoverK (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Kb : Subgroup (MulAut (Vtil V₀ V hV))) (Y : Subgroup G) : Prop :=
  Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧ barSub V₀ V hV Y = Kb ∧
    IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V)

private theorem s16t3_isSimpleGroup_of_isAlt {X : Type} [Group X] {n : ℕ} (h : IsAlt X n)
    (hn : 5 ≤ n) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (α := Fin n) (by simpa [Nat.card_fin] using hn)
  exact e.isSimpleGroup

theorem s16t3_exists_coverL_alt (hset : Setting16 D V₀ V L) (h127 : R127 D)
    (h119 : F11.R119 D)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7) :
    ∃ YL : Subgroup G, S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL := by
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
    simpa only [lBar] using barSub_mono V₀ V hV hset.hyp151.le
  have hLN : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hT.normal
  have hLbcard : Nat.card ↥(lBar V₀ V hV L) = 360 ∨ Nat.card ↥(lBar V₀ V hV L) = 2520 := by
    rcases hL with h6 | h7
    · left
      obtain ⟨e⟩ := h6
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    · right
      obtain ⟨e⟩ := h7
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
  have hLs : IsSimpleGroup ↥(lBar V₀ V hV L) := by
    rcases hL with h6 | h7
    · exact s16t3_isSimpleGroup_of_isAlt h6 (by norm_num)
    · exact s16t3_isSimpleGroup_of_isAlt h7 (by norm_num)
  have hLnc : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
    intro hc
    haveI := hc
    have hp : (Nat.card ↥(lBar V₀ V hV L)).Prime :=
      Group.is_simple_iff_prime_card.mp hLs
    have h360 : ¬ (360 : ℕ).Prime := by norm_num
    have h2520 : ¬ (2520 : ℕ).Prime := by norm_num
    rcases hLbcard with h | h
    · rw [h] at hp; exact absurd hp h360
    · rw [h] at hp; exact absurd hp h2520
  obtain ⟨YL, hYLle, hYLnorm, hYLbar, hYLperf, hYLo2, hYLcent, hYLbound⟩ :=
    s16t3_cover_of_simple_odd hset h127 h119 hLM hLN hLs hLnc
  have h23 : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card ↥(YL ⊓ F11.CTilde D.M V₀ V) → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · right
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hxord⟩ :=
        exists_prime_orderOf_dvd_card' p (G := ↥(YL ⊓ F11.CTilde D.M V₀ V)) hpdvd
      have hxmem : (x : G) ∈ YL ⊓ F11.CTilde D.M V₀ V := x.2
      have hxpow : (x : G) ^ p ^ 1 = 1 := by
        have h1 : (x : ↥(YL ⊓ F11.CTilde D.M V₀ V)) ^ p = 1 :=
          hxord ▸ pow_orderOf_eq_one x
        simpa using congrArg Subtype.val h1
      have hxne : (x : G) ≠ 1 := by
        intro h0
        have hx1 : x = 1 := Subtype.ext h0
        rw [hx1, orderOf_one] at hxord
        have := hp.two_le
        omega
      have hp2dvd : p ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) := by
        by_contra hnot
        exact hxne ((hYLbound p hp hp2 (x : G) hxmem 1 hxpow).1 hnot)
      have hp50 : p ≤ 50 := by
        haveI : Nonempty ↥(lBar V₀ V hV L) := ⟨1⟩
        have hle : p ^ 2 ≤ Nat.card ↥(lBar V₀ V hV L) :=
          Nat.le_of_dvd Nat.card_pos hp2dvd
        have hle' : p ^ 2 ≤ 2520 := by
          rcases hLbcard with hc | hc <;> rw [hc] at hle <;> omega
        by_contra h
        have h51 : 51 ≤ p := by omega
        have hle'' : 51 ^ 2 ≤ p ^ 2 := pow_le_pow_left' h51 2
        norm_num at hle''
        omega
      have hcheck : ∀ q : Fin 51, (q : ℕ).Prime → (q : ℕ) ≠ 2 →
          (q : ℕ) ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) → (q : ℕ) = 3 := by
        rcases hLbcard with hc | hc <;> rw [hc] <;> decide
      exact hcheck ⟨p, by omega⟩ hp hp2 hp2dvd
  have hexp3 : ∀ x ∈ YL ⊓ F11.CTilde D.M V₀ V, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
    intro x hx n hxpow
    have h27 : ¬ 3 ^ 3 ∣ Nat.card ↥(lBar V₀ V hV L) := by
      rcases hLbcard with h | h <;> rw [h] <;> norm_num
    exact (hYLbound 3 Nat.prime_three (by norm_num) x hx n hxpow).2 h27
  exact ⟨YL, ⟨hYLle, hYLnorm, hYLbar, hYLperf, hYLo2, hYLcent, h23, hexp3⟩⟩

theorem s16t3_exists_covers_alt (hset : Setting16 D V₀ V L) (h127 : R127 D)
    (h119 : F11.R119 D)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    ∃ YL YK : Subgroup G, S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL ∧
      S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK := by
  obtain ⟨YL, hYL⟩ := s16t3_exists_coverL_alt hset h127 h119 hT hL
  obtain ⟨N, hNle, hLleN, hNfix, hcomm, hNKbot, hNKsup, hKstruct⟩ :=
    hT.structure_of_seven h7
  have hKs : IsSimpleGroup ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
    rcases hKstruct with h | h | ⟨h, hsimp⟩
    · exfalso; omega
    · exfalso; omega
    · exact hsimp
  have hKnc : ¬ IsMulCommutative ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
    intro hc
    haveI := hc
    have hp : (Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))).Prime :=
      Group.is_simple_iff_prime_card.mp hKs
    rw [hK] at hp
    have h168 : ¬ (168 : ℕ).Prime := by norm_num
    exact absurd hp h168
  have hKM : s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤ Mbar D.M V₀ V hV :=
    inf_le_left
  have hKN : ((s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)).subgroupOf
      (Mbar D.M V₀ V hV)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKM]
    have hNcent : N ≤ Subgroup.centralizer
        (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :
          Set (MulAut (Vtil V₀ V hV))) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm n hn k hk).symm
    calc Mbar D.M V₀ V hV
        = N ⊔ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := hNKsup.symm
      _ ≤ Subgroup.normalizer
            (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :
              Set (MulAut (Vtil V₀ V hV))) :=
          sup_le (hNcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  obtain ⟨YK, hYKle, hYKnorm, hYKbar, hYKperf, hYKo2, hYKcent, hYKbound⟩ :=
    s16t3_cover_of_simple_odd hset h127 h119 hKM hKN hKs hKnc
  have hYK2 : IsPGroup 2 ↥(YK ⊓ F11.CTilde D.M V₀ V) := by
    have hprime : ∀ {d : ℕ}, d.Prime →
        d ∣ Nat.card ↥(YK ⊓ F11.CTilde D.M V₀ V) → d = 2 := by
      intro d hd hddvd
      by_cases hd2 : d = 2
      · exact hd2
      · exfalso
        haveI : Fact d.Prime := ⟨hd⟩
        obtain ⟨x, hxord⟩ :=
          exists_prime_orderOf_dvd_card' d (G := ↥(YK ⊓ F11.CTilde D.M V₀ V)) hddvd
        have hxmem : (x : G) ∈ YK ⊓ F11.CTilde D.M V₀ V := x.2
        have hxpow : (x : G) ^ d ^ 1 = 1 := by
          have h1 : (x : ↥(YK ⊓ F11.CTilde D.M V₀ V)) ^ d = 1 :=
            hxord ▸ pow_orderOf_eq_one x
          simpa using congrArg Subtype.val h1
        have hxne : (x : G) ≠ 1 := by
          intro h0
          have hx1 : x = 1 := Subtype.ext h0
          rw [hx1, orderOf_one] at hxord
          have := hd.two_le
          omega
        have hd2dvd : d ^ 2 ∣
            Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
          by_contra hnot
          exact hxne ((hYKbound d hd hd2 (x : G) hxmem 1 hxpow).1 hnot)
        rw [hK] at hd2dvd
        have hdle : d ≤ 12 := by
          have hle : d ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hd2dvd
          by_contra h
          have h13 : 13 ≤ d := by omega
          have hle' : 13 ^ 2 ≤ d ^ 2 := pow_le_pow_left' h13 2
          norm_num at hle'
          omega
        have hcheck : ∀ q : Fin 13, (q : ℕ).Prime → (q : ℕ) ≠ 2 →
            (q : ℕ) ^ 2 ∣ 168 → False := by decide
        exact hcheck ⟨d, by omega⟩ hd hd2 hd2dvd
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
      (fun {d} hd hddvd => hprime hd hddvd))
  exact ⟨YL, YK, hYL, ⟨hYKle, hYKnorm, hYKbar, hYK2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
