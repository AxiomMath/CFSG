module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2No
public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem prop84_theta_odd (hB : KFacts.BlackburnRankTwo) (hFC : FactFieldCentralizerL2Odd)
    (h : Sec11StdLocal G A c L a R Y) {p e : ℕ} [Fact p.Prime] (hp : 3 < p) (he : 2 ≤ e)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e))))
    {w : G} (hwa : w * a * w⁻¹ ∈ Subgroup.zpowers a)
    (hYw : Y.map (MulAut.conj w).toMonoidHom ≠ Y) : Odd (Nat.card (thetaCent a)) := by
  have hpp : p.Prime := Fact.out
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hpp (by norm_num)
    omega
  have hd := pRankData_of_l2Odd hFC h hp (by omega) hL
  have hd' := hd.conj ha3 hwa
  have hYa : Y ∈ thetaComponentsAt 3 a := h.mem_thetaComponentsAt_Y
  have hYa' := map_conj_mem_thetaComponentsAt ha3 hYa hwa
  have hloc := h.localRank_lt p hpp hp
  refine odd_card_theta_of_components hB hp5 hloc (ι := Bool)
    (fun b => cond b Y (Y.map (MulAut.conj w).toMonoidHom)) ?_ ?_ (fun _ => e) ?_ ?_
  · intro b b' hbb'
    cases b <;> cases b'
    · rfl
    · exact absurd hbb' hYw
    · exact absurd hbb'.symm hYw
    · rfl
  · intro b
    cases b
    · exact hYa'
    · exact hYa
  · simp
    omega
  · intro b
    cases b
    · exact hd'
    · exact hd

theorem prop84_theta_odd_of_ge_four (hB : KFacts.BlackburnRankTwo)
    (hFC : FactFieldCentralizerL2Odd) (h : Sec11StdLocal G A c L a R Y) {p e : ℕ} [Fact p.Prime]
    (hp : 3 < p) (he : 4 ≤ e)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e)))) :
    Odd (Nat.card (thetaCent a)) := by
  have hpp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hpp (by norm_num)
    omega
  have hd := pRankData_of_l2Odd hFC h hp (by omega) hL
  have hYa : Y ∈ thetaComponentsAt 3 a := h.mem_thetaComponentsAt_Y
  have hloc := h.localRank_lt p hpp hp
  exact odd_card_theta_of_components hB hp5 hloc (ι := Unit) (fun _ => Y)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hYa) (fun _ => e) (by simp; omega)
    (fun _ => hd)

theorem theta_odd_of_swap_l3 (hB : KFacts.BlackburnRankTwo) (hFC : FactFieldCentralizerL3)
    (h : Sec11StdLocal G A c L a R Y) {m : ℕ} (hm : 2 ≤ m)
    (hL : Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * m))
    {w : G} (hwa : w * a * w⁻¹ ∈ Subgroup.zpowers a)
    (hYw : Y.map (MulAut.conj w).toMonoidHom ≠ Y) : Odd (Nat.card (thetaCent a)) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  obtain ⟨r, hr, hr5, hd⟩ := pRankData_of_l3 hFC h (by omega) hL
  have hd2 : PRankData r a Y 2 := by simpa [show 2 ≤ m from hm] using hd
  have hd' := hd2.conj ha3 hwa
  have hYa : Y ∈ thetaComponentsAt 3 a := h.mem_thetaComponentsAt_Y
  have hYa' := map_conj_mem_thetaComponentsAt ha3 hYa hwa
  have hloc := h.localRank_lt r hr.out (by omega)
  refine odd_card_theta_of_components hB hr5 hloc (ι := Bool)
    (fun b => cond b Y (Y.map (MulAut.conj w).toMonoidHom)) ?_ ?_ (fun _ => 2) ?_ ?_
  · intro b b' hbb'
    cases b <;> cases b'
    · rfl
    · exact absurd hbb' hYw
    · exact absurd hbb'.symm hYw
    · rfl
  · intro b
    cases b
    · exact hYa'
    · exact hYa
  · simp
  · intro b
    cases b
    · exact hd'
    · exact hd2

theorem false_of_R1_oddChar (hB : KFacts.BlackburnRankTwo) (hFC : FactFieldCentralizerL2Odd)
    (h45 : Sec4.Item4_5) (hcore : Item116P2bCore) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) {p e : ℕ} [Fact p.Prime] (hp : 3 < p) (he : 2 ≤ e)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e))))
    (hR1 : ResidueR1 G A c a d) : False := by
  obtain ⟨hEven, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  have hYn := (item116P2b_of_core h45 hcore) G A c L a R Y (h.toSec11Std hT) d h.inf_eq_zpowers
    h.normalizer_le h.isIrreducibleOn h.isSylowOf_top h.not_mem_zpowers hD8 n hnW hnc hnd hna
  have hodd := prop84_theta_odd hB hFC h.toSec11StdLocal hp he hL (w := n)
    (by rw [hna]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hYn
  exact (Nat.not_even_iff_odd.mpr hodd) hEven

theorem false_of_R1_l3 (hB : KFacts.BlackburnRankTwo) (hFC : FactFieldCentralizerL3)
    (h45 : Sec4.Item4_5) (hcore : Item116P2bCore) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) {m : ℕ} (hm : 2 ≤ m)
    (hL : Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * m))
    (hR1 : ResidueR1 G A c a d) : False := by
  obtain ⟨hEven, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  have hYn := (item116P2b_of_core h45 hcore) G A c L a R Y (h.toSec11Std hT) d h.inf_eq_zpowers
    h.normalizer_le h.isIrreducibleOn h.isSylowOf_top h.not_mem_zpowers hD8 n hnW hnc hnd hna
  have hodd := theta_odd_of_swap_l3 hB hFC h.toSec11StdLocal hm hL (w := n)
    (by rw [hna]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hYn
  exact (Nat.not_even_iff_odd.mpr hodd) hEven

theorem theorem85 (hB : KFacts.BlackburnRankTwo) (hFC : FactFieldCentralizerL2Odd)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) {p e : ℕ} [Fact p.Prime]
    (hp : 3 < p) (he : 2 ≤ e)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e)))) :
    False := by
  rcases h.residue with hR1 | hR2
  · exact false_of_R1_oddChar hB hFC h45 hcore h hT hp he hL hR1
  · exact false_of_R2 h45 h113 h (Or.inl hT) hR2

end Certified

section Glue


@[expose] def ResidueOddCharGe2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ∀ (p e : ℕ) (_ : Fact p.Prime), 3 < p → 2 ≤ e →
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e))) → False

@[expose] def ResidueOddCharOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ∀ (p : ℕ) (_ : Fact p.Prime), 3 < p →
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * 1))) → False

theorem residueOddChar_of_split (h2 : ResidueOddCharGe2) (h1 : ResidueOddCharOne) :
    ResidueOddChar := by
  intro G _ _ A c L a R Y d h hT hodd
  obtain ⟨p, e, hp, hp3, he, hL⟩ := hodd
  by_cases he1 : e = 1
  · subst he1
    exact h1 G A c L a R Y d h hT p hp hp3 hL
  · exact h2 G A c L a R Y d h hT p e hp hp3 (by omega) hL

theorem residueOddCharGe2_of (hB : KFacts.BlackburnRankTwo) (hFC : FactFieldCentralizerL2Odd)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) : ResidueOddCharGe2 := by
  intro G _ _ A c L a R Y d h hT p e hp hp3 he hL
  exact theorem85 hB hFC h45 h113 hcore h hT hp3 he hL

end Glue

end CFSG.RankThree.PartTwo.Sec11
