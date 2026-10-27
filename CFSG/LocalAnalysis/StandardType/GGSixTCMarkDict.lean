module

public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem exists_label_of_marking_tc
    {K : Type} [Group K] {Q : LargeEvenLabel → Prop}
    (h : LargeEvenMarking K (fun lab _ _ _ _ _ => Q lab)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ Q lab ∧
      MarkedModel lab (K ⧸ Subgroup.center K) := by
  obtain ⟨lab, hlab, R, instR, I, F, θ, -, -, hP, hm⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel h
  exact ⟨lab, hlab, hP, MarkedModel.of_mulEquiv θ.symm hm⟩

theorem split_of_markTag_PSL {p : ℕ} {lab : LargeEvenLabel} {k g : ℕ}
    (ht : markTag lab = .PSL) (hk : markRank lab = k) (hc : markChar lab = 2)
    (hg : markDeg lab = g) (hk3 : 3 ≤ k) (h : LargeEvenSplit p lab) :
    p ∣ 2 ^ g - 1 ∨ (g = 1 ∧ p = 3) := by
  obtain ⟨tag, r, e⟩ := lab
  cases tag <;> simp only [markTag, markRank, markChar, markDeg] at ht hk hc hg <;>
    (try split_ifs at ht hk hg) <;>
    first
    | (simp_all [LargeEvenSplit, LargeEvenUntwisted]; done)
    | (subst hk hg; simp_all [LargeEvenSplit, LargeEvenUntwisted])

theorem halfSplit_of_markTag_PSL {p : ℕ} {lab : LargeEvenLabel} {k g : ℕ} {Z : Prop}
    (ht : markTag lab = .PSL) (hk : markRank lab = k) (hc : markChar lab = 2)
    (hg : markDeg lab = g) (hk5 : 5 ≤ k) (h : LargeEvenHalfSplit p lab Z) :
    p ∣ 2 ^ g - 1 ∨ (g = 1 ∧ p = 3) ∨ (k = 6 ∧ g = 2 ∧ Z ∧ p = 5) ∨ (k = 9 ∧ g = 1 ∧ p = 7) := by
  obtain ⟨tag, r, e⟩ := lab
  cases tag <;> simp only [markTag, markRank, markChar, markDeg] at ht hk hc hg <;>
    (try split_ifs at ht hk hg) <;>
    first
    | (simp_all [LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted]; done)
    | (subst hk hg; simp_all [LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] <;>
        first | omega | tauto)

theorem split_of_markTag_PSU {p : ℕ} {lab : LargeEvenLabel} {k g : ℕ}
    (ht : markTag lab = .PSU) (hk : markRank lab = k) (hc : markChar lab = 2)
    (hg : markDeg lab = g) (hk5 : 5 ≤ k) (h : LargeEvenSplit p lab) :
    p ∣ 2 ^ g + 1 ∨ (g = 1 ∧ p = 3) := by
  obtain ⟨tag, r, e⟩ := lab
  cases tag <;> simp only [markTag, markRank, markChar, markDeg] at ht hk hc hg <;>
    (try split_ifs at ht hk hg) <;>
    first
    | (simp_all [LargeEvenSplit, LargeEvenUntwisted]; done)
    | (subst hk hg; simp_all [LargeEvenSplit, LargeEvenUntwisted])

theorem halfSplit_of_markTag_PSU {p : ℕ} {lab : LargeEvenLabel} {k g : ℕ} {Z : Prop}
    (ht : markTag lab = .PSU) (hk : markRank lab = k) (hc : markChar lab = 2)
    (hg : markDeg lab = g) (hk5 : 5 ≤ k) (h : LargeEvenHalfSplit p lab Z) :
    p ∣ 2 ^ g + 1 ∨ (g = 1 ∧ p = 3) ∨ (k = 6 ∧ p ∣ 2 ^ g - 1) := by
  obtain ⟨tag, r, e⟩ := lab
  cases tag <;> simp only [markTag, markRank, markChar, markDeg] at ht hk hc hg <;>
    (try split_ifs at ht hk hg) <;>
    first
    | (simp_all [LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted]; done)
    | (subst hk hg; simp_all [LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] <;> omega)

private theorem tcDict_exp_eq {m N a r : ℕ} {Z : ℕ → Prop}
    (h : CFSG.Timmesfeld.Orders.Profile m N Z) (hr : Odd r) (hm : m = 2 ^ a * r) : N = a := by
  by_contra hne
  exact h.ne_of_ne hr hne hm

private theorem tcDict_charTwoOrder_ne {t : StatedLieTag} {k g : ℕ}
    (hadm : StatedLieAdmissible t k 2 g)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder t k g ≠ 360 ∧
      CFSG.SeitzReduction.F4Pilot.evenLieOrder t k g ≠ 6048 := by
  obtain ⟨-, hg, hrest⟩ := hadm
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨hk, -, -⟩ := hrest
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    have hP := CFSG.Timmesfeld.Orders.profile_ordA (n := n) (f := g) hn hg
    change CFSG.Open.ordA n (2 ^ g) ≠ 360 ∧ CFSG.Open.ordA n (2 ^ g) ≠ 6048
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := tcDict_exp_eq (a := 3) (r := 45) hP
        (by decide) (h.trans (by norm_num))
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
      · have hN' : g * 1 = 3 := hN
        obtain rfl : g = 3 := by omega
        revert h; decide
      · have hN' : g * 3 = 3 := hN
        obtain rfl : g = 1 := by omega
        revert h; decide
      · have h12 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul h3 (by omega)
        have hle : n * (n + 1) / 2 ≤ g * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ hg
        omega
    · have hN := tcDict_exp_eq (a := 5) (r := 189) hP
        (by decide) (h.trans (by norm_num))
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
      · have hN' : g * 1 = 5 := hN
        obtain rfl : g = 5 := by omega
        revert h; decide
      · have hN' : g * 3 = 5 := hN
        omega
      · have h12 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul h3 (by omega)
        have hle : n * (n + 1) / 2 ≤ g * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ hg
        omega
  ·
    obtain ⟨hk, -⟩ := hrest
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hn : 2 ≤ n := by omega
    have hP := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := n) (g := g) hn hg
    change CFSG.Open.ordTwistedA n (2 ^ g) ≠ 360 ∧ CFSG.Open.ordTwistedA n (2 ^ g) ≠ 6048
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := tcDict_exp_eq (a := 3) (r := 45) hP
        (by decide) (h.trans (by norm_num))
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
      · have hN' : g * 3 = 3 := hN
        obtain rfl : g = 1 := by omega
        revert h; decide
      · have h12 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul h3 (by omega)
        have hle : n * (n + 1) / 2 ≤ g * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ hg
        omega
    · have hN := tcDict_exp_eq (a := 5) (r := 189) hP
        (by decide) (h.trans (by norm_num))
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
      · have hN' : g * 3 = 5 := hN
        omega
      · have h12 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul h3 (by omega)
        have hle : n * (n + 1) / 2 ≤ g * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ hg
        omega
  ·
    obtain ⟨hk, -⟩ := hrest
    have hP := CFSG.Timmesfeld.Orders.profile_ordBC (n := k) (f := g) hg
    change CFSG.Open.ordBC k (2 ^ g) ≠ 360 ∧ CFSG.Open.ordBC k (2 ^ g) ≠ 6048
    have h4 : 2 * 2 ≤ k * k := Nat.mul_le_mul hk hk
    have hle : k * k ≤ g * (k * k) := Nat.le_mul_of_pos_left _ hg
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := tcDict_exp_eq (a := 3) (r := 45) hP
        (by decide) (h.trans (by norm_num))
      omega
    · have hN := tcDict_exp_eq (a := 5) (r := 189) hP
        (by decide) (h.trans (by norm_num))
      rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | h3
      · have hN' : g * 4 = 5 := hN
        omega
      · have h9 : 3 * 3 ≤ k * k := Nat.mul_le_mul h3 h3
        omega
  ·
    have hk : 4 ≤ k := hrest
    have hP := CFSG.Timmesfeld.Orders.profile_ordD (n := k) (f := g) (by omega) hg
    have hev : Even (g * (k * (k - 1))) := (Nat.even_mul_pred_self k).mul_left g
    change CFSG.Open.ordD k (2 ^ g) ≠ 360 ∧ CFSG.Open.ordD k (2 ^ g) ≠ 6048
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := tcDict_exp_eq (a := 3) (r := 45) hP
        (by decide) (h.trans (by norm_num))
      rw [hN] at hev
      obtain ⟨j, hj⟩ := hev
      omega
    · have hN := tcDict_exp_eq (a := 5) (r := 189) hP
        (by decide) (h.trans (by norm_num))
      rw [hN] at hev
      obtain ⟨j, hj⟩ := hev
      omega
  ·
    have hk : 4 ≤ k := hrest
    have hP := CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := k) (f := g) (by omega) hg
    have hev : Even (g * (k * (k - 1))) := (Nat.even_mul_pred_self k).mul_left g
    change CFSG.Open.ordTwistedD k (2 ^ g) ≠ 360 ∧ CFSG.Open.ordTwistedD k (2 ^ g) ≠ 6048
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := tcDict_exp_eq (a := 3) (r := 45) hP
        (by decide) (h.trans (by norm_num))
      rw [hN] at hev
      obtain ⟨j, hj⟩ := hev
      omega
    · have hN := tcDict_exp_eq (a := 5) (r := 189) hP
        (by decide) (h.trans (by norm_num))
      rw [hN] at hev
      obtain ⟨j, hj⟩ := hev
      omega

private theorem tcDict_card_B2der {R : Type} [Group R]
    (hM : MarkedModel ⟨.B2der, 0, 1⟩ R) : Nat.card R = 360 := by
  have hm' : CFSG.Blueprint.LieModel R .PSL 2 3 2 := hM
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm'.statedClassicalModel (by decide)
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 2) (by norm_num), hK]
  decide

private theorem tcDict_card_G2der {R : Type} [Group R]
    (hM : MarkedModel ⟨.G2der, 0, 1⟩ R) : Nat.card R = 6048 := by
  have hm' : CFSG.Blueprint.LieModel R .PSU 3 3 1 := hM
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm'.statedClassicalModel (by decide)
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (n := 3) Nat.prime_three le_rfl hK
      (by norm_num)]
  decide

private theorem tcDict_tag_of_char_ne {lab : LargeEvenLabel} (h : markChar lab ≠ 2) :
    lab.tag = .B2der ∨ lab.tag = .G2der := by
  obtain ⟨tg, r, m⟩ := lab
  cases tg <;> first
    | exact (h rfl).elim
    | exact Or.inl rfl
    | exact Or.inr rfl

private theorem tcDict_label_B2der {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .B2der) : lab = ⟨.B2der, 0, 1⟩ := by
  obtain ⟨tg, r, m⟩ := lab
  obtain rfl : tg = .B2der := h
  obtain ⟨-, hr, hm⟩ : 1 ≤ m ∧ r = 0 ∧ m = 1 := hlab
  subst hr hm
  rfl

private theorem tcDict_label_G2der {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .G2der) : lab = ⟨.G2der, 0, 1⟩ := by
  obtain ⟨tg, r, m⟩ := lab
  obtain rfl : tg = .G2der := h
  obtain ⟨-, hr, hm⟩ : 1 ≤ m ∧ r = 0 ∧ m = 1 := hlab
  subst hr hm
  rfl

theorem markData_of_lieModel
    {R : Type} [Group R] {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hM : MarkedModel lab R) {t' : StatedLieTag} {k g : ℕ}
    (ht : t' = .PSL ∨ t' = .PSU ∨ t' = .PSp ∨ t' = .POmegaPlus ∨ t' = .POmegaMinus)
    (hadm : StatedLieAdmissible t' k 2 g) (hrk : 2 ≤ (ggU t' k g).D.rank)
    (hR : LieModel R t' k 2 g) :
    markTag lab = t' ∧ markRank lab = k ∧ markChar lab = 2 ∧ markDeg lab = g := by
  have hc : markChar lab = 2 := by
    by_contra hne
    have hcard := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hR
    have hne2 := tcDict_charTwoOrder_ne hadm ht
    rcases tcDict_tag_of_char_ne hne with h | h
    · have hl := tcDict_label_B2der hlab h
      subst hl
      exact hne2.1 (hcard.symm.trans (tcDict_card_B2der hM))
    · have hl := tcDict_label_G2der hlab h
      subst hl
      exact hne2.2 (hcard.symm.trans (tcDict_card_G2der hM))
  have ht' : t' = .PSL ∨ t' = .PSU ∨ t' = .PSp ∨ t' = .POmegaPlus ∨ t' = .POmegaMinus ∨
      t' = .E7 := by
    rcases ht with h | h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))]
  exact ggMarkTypeDetAt_classical hc ht' R k g hadm hrk hR hM

end CFSG.StandardType.TableCRes
