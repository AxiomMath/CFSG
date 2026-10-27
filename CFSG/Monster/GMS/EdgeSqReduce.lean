module

public import CFSG.Monster.GMS.EdgeSqLeech
public import CFSG.Monster.GMS.S365Cent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section TwoGroup

variable {G : Type*} [Group G]

theorem isPGroup_two_closure {s : Set G} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (h4 : ∀ x ∈ s, x ^ 4 = 1) : IsPGroup 2 (Subgroup.closure s) := by
  have hc : IsMulCommutative (Subgroup.closure s) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  have key : ∀ x ∈ Subgroup.closure s, x ^ 4 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h4 x hx
    | one => exact one_pow 4
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure s) ⟨y, hy⟩)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  simpa using key x.1 x.2

theorem pow_four_eq_one_of_mul_self {x : G} (h : x * x = 1) : x ^ 4 = 1 := by
  have e : x ^ 4 = (x * x) * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [e, h, mul_one]

end TwoGroup

private theorem exists_twoB_mem_center_sylow {G : Type*} [Group G] [Finite G] {z₀ : G}
    (hz₀ : GMSLeechCentralizer z₀) (P : Sylow 2 G) (hP : Nontrivial (P : Subgroup G)) :
    ∃ t : G, IsConj z₀ t ∧ orderOf t = 2 ∧ t ∈ (P : Subgroup G) ∧
      ∀ x ∈ (P : Subgroup G), x * t = t * x := by
  have : Nontrivial (Subgroup.center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hCp : IsPGroup 2 (Subgroup.center (P : Subgroup G)) := P.isPGroup'.to_subgroup _
  have h2 : 2 ∣ Nat.card (Subgroup.center (P : Subgroup G)) := by
    rcases hCp.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp h).1 (not_subsingleton _)
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw' : orderOf ((w : (P : Subgroup G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  refine ⟨((w : (P : Subgroup G)) : G), ?_, hw', (w : (P : Subgroup G)).2, fun x hx => ?_⟩
  · exact isConj_of_mem_center_sylow hz₀.1 hz₀.2.1 hz₀.2.2.2.2 P hw'
      (Subgroup.mem_map.mpr ⟨w, w.2, rfl⟩)
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨x, hx⟩)

theorem eq_one_of_dvd_eightCentOrder {n : ℕ} (hn : n = 1 ∨ n = 3 ∨ n = 4)
    (h : 2 ^ 38 ∣ eightCentOrder n) : n = 1 := by
  rcases hn with rfl | rfl | rfl
  · rfl
  · exact absurd h (by unfold eightCentOrder; norm_num)
  · exact absurd h (by unfold eightCentOrder; norm_num)

section Reduce

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem exists_twoB_centralizing
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b w g : G}
    (hb : IsConj a b) (hw : w ∈ twoANbr a b)
    (hg : g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {w}) (hg4 : g ^ 4 = 1) :
    ∃ z : G, IsConj z₀ z ∧ g * z = z * g ∧ b * z = z * b ∧ w * z = z * w ∧
      2 ^ 38 ∣ Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {w} ⊓
        Subgroup.centralizer {z}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : orderOf a = 2 := hG.1.1
  have hl : IsLineTriple a b w := ⟨hb, hw.1, hw.2⟩
  have hK := S365.isKlein_of_isLineTriple ha hl
  set K : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {w}
  have hcardK : Nat.card K = tableVOrderB :=
    card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hb hw
  have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).1
  have hgw : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
  have hbw : b * w = w * b := hK.comm
  have hbK : b ∈ K := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
      Subgroup.mem_centralizer_singleton_iff.mpr hbw⟩
  have hwK : w ∈ K := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hbw.symm,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  set s : Set G := {g, b, w} with hs
  have hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> rw [h, h'] <;>
      first | rfl | assumption | exact hgb.symm | exact hgw.symm | exact hbw.symm
  have h4 : ∀ x ∈ s, x ^ 4 = 1 := by
    intro x hx
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact hg4
    · rw [h]; exact pow_four_eq_one_of_mul_self hK.sq_x
    · rw [h]; exact pow_four_eq_one_of_mul_self hK.sq_y
  have hP : IsPGroup 2 (Subgroup.closure s) := isPGroup_two_closure hcomm h4
  have hsK : s ⊆ K := by
    intro x hx
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact hg
    · rw [h]; exact hbK
    · rw [h]; exact hwK
  have hPK : Subgroup.closure s ≤ K := (Subgroup.closure_le K).mpr hsK
  have hg38 : 2 ^ 38 ∣ Nat.card K := by
    rw [hcardK]
    norm_num [tableVOrderB]
  have hPdvd : Nat.card (Subgroup.closure s) ∣ 2 ^ 38 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
    have hdvd : 2 ^ n ∣ tableVOrderB := by
      rw [← hn, ← hcardK]
      exact Subgroup.card_dvd_of_le hPK
    have hn38 : n ≤ 38 := by
      by_contra hlt
      have : 2 ^ 39 ∣ tableVOrderB := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num [tableVOrderB] at this
    rw [hn]
    exact pow_dvd_pow 2 hn38
  obtain ⟨T, hTcard, hPT, hTK⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hPdvd hg38 hPK
  obtain ⟨S, hTS⟩ := (IsPGroup.of_card hTcard : IsPGroup 2 T).exists_le_sylow
  have hgS : g ∈ (S : Subgroup G) :=
    hTS (hPT (Subgroup.subset_closure (Set.mem_insert g _)))
  have hbS : b ∈ (S : Subgroup G) :=
    hTS (hPT (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert b _))))
  have hwS : w ∈ (S : Subgroup G) :=
    hTS (hPT (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton w)))))
  have hSnt : Nontrivial (S : Subgroup G) :=
    ⟨⟨⟨b, hbS⟩, 1, fun h => S365.ne_one_of_isConj_a ha hb (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz, -, -, hzc⟩ := exists_twoB_mem_center_sylow hG.2 S hSnt
  refine ⟨z, hz, hzc g hgS, hzc b hbS, hzc w hwS, ?_⟩
  have hle : T ≤ K ⊓ Subgroup.centralizer {z} :=
    le_inf hTK fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hzc x (hTS hx))
  rw [← hTcard]
  exact Subgroup.card_dvd_of_le hle

theorem mem_leechQ_of_good
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b w z : G}
    (hl : IsLineTriple a b w) (hz : IsConj z₀ z) (hzb : b * z = z * b) (hzw : w * z = z * w)
    (hdvd : 2 ^ 38 ∣ Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {w} ⊓
      Subgroup.centralizer {z})) :
    b ∈ leechQ z ∧ w ∈ leechQ z ∧ b * w ∈ leechQ z := by
  have hz2 : orderOf z = 2 := (orderOf_eq_of_isConj hz).symm.trans hG.2.1
  have hE : IsEightExt b w z := by
    refine ⟨mul_self_eq_one_of_orderOf hz2, hzb.symm, hzw.symm, ne_one_of_orderOf hz2, ?_, ?_, ?_⟩
    · intro h
      rw [h] at hz
      exact hG.not_isConj (hl.1.trans hz.symm)
    · intro h
      rw [h] at hz
      exact hG.not_isConj (hl.2.1.trans hz.symm)
    · intro h
      rw [h] at hz
      exact hG.not_isConj (hl.2.2.trans hz.symm)
  have hcnt := S365.twoBCount_cases I hG b w z hl hE
  have hcard := eightCentOrders_of I hG b w z hl hE
  rw [hcard] at hdvd
  have h1 : twoBCount z₀ b w z = 1 := eq_one_of_dvd_eightCentOrder hcnt hdvd
  have hcount := S365.twoBCount_eq_of_twoB I hG hl hz hzb hzw
  rw [h1] at hcount
  split_ifs at hcount with hb hw hbw
  · exact ⟨hb, hw, hbw⟩
  all_goals omega

theorem false_of_edge_square_at
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hfact : Co1EdgeFact) {b w g z : G} (hl : IsLineTriple a b w) (hz : IsConj z₀ z)
    (hgz : g * z = z * g) (hbQ : b ∈ leechQ z) (hwQ : w ∈ leechQ z) (hbwQ : b * w ∈ leechQ z)
    (hgb : g * b = b * g) (hgw : g * w = w * g)
    (hc : g * g = b ∨ g * g = w ∨ g * g = b * w) : False := by
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG hz
  have hK := S365.isKlein_of_isLineTriple hG.1.1 hl
  have hb0 : b ∈ L.typeSet 0 := S365.mem_typeSet_zero_of_isConj I hG hz L hbQ hl.1
  have hw0 : w ∈ L.typeSet 0 := S365.mem_typeSet_zero_of_isConj I hG hz L hwQ hl.2.1
  have hbw0 : b * w ∈ L.typeSet 0 := S365.mem_typeSet_zero_of_isConj I hG hz L hbwQ hl.2.2
  have hgC : g ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgz
  have hwb : w * b = b * w := hK.comm.symm
  rcases hc with hc | hc | hc
  · refine L.false_of_edge_square hfact hgC (by rw [hc]; exact hb0) hw0 ?_ hgw
    rw [hc]
    exact hbw0
  · refine L.false_of_edge_square hfact hgC (by rw [hc]; exact hw0) hb0 ?_ hgb
    rw [hc, hwb]
    exact hbw0
  · refine L.false_of_edge_square hfact hgC (by rw [hc]; exact hbw0) hb0 ?_ hgb
    have e : g * g * b = w := by
      rw [hc]
      calc b * w * b = b * (w * b) := mul_assoc _ _ _
        _ = b * (b * w) := by rw [hwb]
        _ = (b * b) * w := (mul_assoc _ _ _).symm
        _ = w := by rw [hK.sq_x, one_mul]
    rw [e]
    exact hw0

theorem edgeSquares_of_fact
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hfact : Co1EdgeFact) : EdgeSquares a := by
  intro b w hb hw g hg hc
  by_contra hne
  have hl : IsLineTriple a b w := ⟨hb, hw.1, hw.2⟩
  have hK := S365.isKlein_of_isLineTriple hG.1.1 hl
  have hcK : S365.InKlein b w (g * g) := by
    simpa [S365.InKlein, Set.mem_insert_iff, Set.mem_singleton_iff] using hc
  have hg4 : g ^ 4 = 1 := by
    have e : g ^ 4 = (g * g) * (g * g) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [e]
    exact hK.mul_self_of_mem hcK
  have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).1
  have hgw : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
  obtain ⟨z, hz, hgz, hbz, hwz, hdvd⟩ := exists_twoB_centralizing I hG hb hw hg hg4
  obtain ⟨hbQ, hwQ, hbwQ⟩ := mem_leechQ_of_good I hG hl hz hbz hwz hdvd
  refine false_of_edge_square_at I hG hfact hl hz hgz hbQ hwQ hbwQ hgb hgw ?_
  rcases hcK with h | h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Reduce

end CFSG.Monster.GMS
