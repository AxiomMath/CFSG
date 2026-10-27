module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Count

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem sec51_arith {P q i y e₀ e₁ b : ℕ} (hq : 2 ≤ q) (hP : 0 < P) (he₁ : Even e₁)
    (h1 : (P * i) ^ 2 * q ^ e₁ = y ^ 2) (h2 : y * q ^ e₀ = P * q ^ b) (hi1 : 2 ≤ i)
    (hi2 : i ≤ q) : i = q := by
  obtain ⟨k, hk⟩ := he₁
  have hq0 : 0 < q := by omega
  have hy : y = P * i * q ^ k := by
    have h3 : y ^ 2 = (P * i * q ^ k) ^ 2 := by
      rw [← h1, hk, pow_add, mul_pow]
      ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h3
  rw [hy] at h2
  have h4 : i * q ^ (k + e₀) = q ^ b := by
    have h5 : P * (i * q ^ (k + e₀)) = P * q ^ b := by rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hP h5
  have hab : k + e₀ ≤ b := by
    by_contra hcon
    push Not at hcon
    have : q ^ b < q ^ (k + e₀) := Nat.pow_lt_pow_right (by omega) hcon
    have h6 : q ^ (k + e₀) ≤ i * q ^ (k + e₀) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨c, hc⟩ : ∃ c, b = c + (k + e₀) := ⟨b - (k + e₀), by omega⟩
  have h7 : i = q ^ c := by
    have h4' : i * q ^ (k + e₀) = q ^ c * q ^ (k + e₀) := by rw [← pow_add, ← hc]; exact h4
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h4'
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · interval_cases c
    · simp at h7; omega
    · simpa using h7
  · have : q ^ 2 ≤ q ^ c := Nat.pow_le_pow_right hq0 hc2
    have h8 : q < q ^ 2 := by nlinarith
    omega


section Group

variable {G : Type} [Group G]

theorem sec51_T_le_conj {R L Q T : Subgroup G} (hQL : Q ≤ L)
    (hT : ∀ x, x ∈ T ↔ x ∈ L ∧ ∀ g ∈ R, ⁅g, x⁆ ∈ Q) {s : G} (hs : s ∈ R) :
    T ≤ conjSubgroup s L := by
  intro x hx
  obtain ⟨hxL, hxc⟩ := (hT x).mp hx
  rw [mem_conjSubgroup]
  have e : s⁻¹ * x * s = ⁅s⁻¹, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [e]
  exact L.mul_mem (hQL (hxc s⁻¹ (R.inv_mem hs))) hxL

theorem sec51_T_normal {R M L Q T : Subgroup G} (hRM : R ≤ M)
    (hQn : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q) (hQL : Q ≤ L)
    (hT : ∀ x, x ∈ T ↔ x ∈ L ∧ ∀ g ∈ R, ⁅g, x⁆ ∈ Q) {g : G} (hg : g ∈ R) {x : G} (hx : x ∈ T) :
    g * x * g⁻¹ ∈ T := by
  obtain ⟨hxL, hxc⟩ := (hT x).mp hx
  rw [hT]
  refine ⟨?_, fun h hh => ?_⟩
  · have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem (hQL (hxc g hg)) hxL
  · have e : ⁅h, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * h * g, x⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hQn g (hRM hg) _ (hxc _ (R.mul_mem (R.mul_mem (R.inv_mem hg) hh) hg))

end Group


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.sec51_assembly (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    (hN311 : hc.CN t = ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t),
      conjSubgroup h (LB M Q B) ⊓ hc.CN t)
    (hNN : ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B) (T : Subgroup G)
    (hT : ∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ g ∈ Rt M (LB M Q B) t, ⁅g, x⁆ ∈ Q)
    (hTcard : Nat.card T ≤ Nat.card Q * Nat.card Z)
    (hL35 : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (G1 : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup s B)))
    (G2 : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      LB M Q B ⊓ LB M Q (conjSubgroup s B) ≤ hc.CN t)
    (G3a : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      ∃ l ∈ LB M Q B, HypPlane Q Z B (conjSubgroup (s⁻¹ * l * s) B) t)
    (G3b : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      ∃ l ∈ LB M Q (conjSubgroup s B), HypPlane Q Z B (conjSubgroup l B) t)
    (G4 : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      (∀ g ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup s B),
        g * x * g⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup s B)) →
      IsOppDecomp (hc.CN t) (LB M Q B ⊓ LB M Q (conjSubgroup s B)) (LB M Q B)
        (LB M Q (conjSubgroup s B)) (LB M Q B ⊓ hc.CN t)
        (LB M Q (conjSubgroup s B) ⊓ hc.CN t) →
      ∃ e : ℕ, Even e ∧
        Nat.card (hc.CN t) = Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup s B)) * Nat.card Z ^ e)
    (G5 : ∃ e₀ : ℕ, Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ e₀ = Nat.card (LB M Q B)) :
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      (∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
        ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b) ∧
      Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) = Nat.card Q * Nat.card Z ∧
      (∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B), ⁅s, x⁆ ∈ Q) ∧
      IsOppDecomp (hc.CN t) (LB M Q B ⊓ LB M Q (conjSubgroup r B)) (LB M Q B)
        (LB M Q (conjSubgroup r B)) (LB M Q B ⊓ hc.CN t)
        (LB M Q (conjSubgroup r B) ⊓ hc.CN t) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQn : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hRM : Rt M (LB M Q B) t ≤ M := fun x hx => hc.Rt_le_M t hx
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLsR : ∀ s ∈ Rt M (LB M Q B) t, LB M Q (conjSubgroup s B) ≤ Rt M (LB M Q B) t :=
    fun s hs' => hc.LB_conj_le_Rt_of_mem ht hs'
  have hLs : ∀ s ∈ Rt M (LB M Q B) t,
      LB M Q (conjSubgroup s B) = conjSubgroup s (LB M Q B) := fun s hs' =>
    hc.LB_conj (hRM hs')
  have hcore : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      (∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
        ∃ b ∈ LB M Q (conjSubgroup s B) ⊓ hc.CN t, x = a * b) ∧
      (∀ g ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup s B), ⁅g, x⁆ ∈ Q) ∧
      ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B ⊓ LB M Q (conjSubgroup s B) := by
    intro s hs' hpl
    have hgen : Rt M (LB M Q B) t = hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup s B) :=
      le_antisymm (by rw [sup_assoc]; exact G1 s hs' hpl)
        (sup_le (sup_le hNR hLR) (hLsR s hs'))
    exact hc.sec51_core h35 ht hs' hN311 hNN hgen
  have hIeq : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      LB M Q B ⊓ LB M Q (conjSubgroup s B) = T := by
    intro s hs' hpl
    refine le_antisymm (fun x hx => (hT x).mpr ⟨hx.1, fun g hg =>
      (hcore s hs' hpl).2.1 g hg x hx⟩) (fun x hx => ?_)
    rw [hLs s hs']
    exact ⟨((hT x).mp hx).1, sec51_T_le_conj hQL hT hs' hx⟩
  intro r hr hplane
  have hrM : r ∈ M := hRM hr
  have hC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hcr := hcore r hr hplane
  have hIr := hIeq r hr hplane
  have hQI : Q ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) := le_inf hQL sec39_Q_le_LB
  have hInorm : ∀ g ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B),
      g * x * g⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    intro g hg x hx
    rw [hIr] at hx ⊢
    exact sec51_T_normal hRM hQn hQL hT hg hx
  have hInorm' : ∀ g ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B),
      g⁻¹ * x * g ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    intro g hg x hx
    simpa using hInorm g⁻¹ ((Rt M (LB M Q B) t).inv_mem hg) x hx
  have hIN : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ hc.CN t := G2 r hr hplane
  have hfL : ∀ x ∈ hc.CN t, (x ∈ LB M Q B ⊓ hc.CN t ↔
      ∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B)) := by
    intro x hxN
    constructor
    · intro hx l hl
      have h1 : ⁅l, x⁆ ∈ Q := Subgroup.commutator_le.mp hc.commutator_LB_le_Q l hl x hx.1
      exact hQI h1
    · intro hx
      refine ⟨?_, hxN⟩
      obtain ⟨a, ha, b, hb, hxab⟩ := hcr.1 x hxN
      obtain ⟨l₀, hl₀, hopp⟩ := G3a r hr hplane
      have hsR : r⁻¹ * l₀ * r ∈ Rt M (LB M Q B) t :=
        (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem
          ((Rt M (LB M Q B) t).inv_mem hr) (hLR hl₀)) hr
      have hla : ⁅l₀, a⁆ ∈ Q := Subgroup.commutator_le.mp hc.commutator_LB_le_Q l₀ hl₀ a ha.1
      have hlx := hx l₀ hl₀
      have hi : a⁻¹ * (⁅l₀, a⁆⁻¹ * ⁅l₀, x⁆) * a ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
        hInorm' a (hNR ha.2) _ ((LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem
          (hQI ((Q).inv_mem hla)) hlx)
      have hc_eq : l₀ * b * l₀⁻¹ = (a⁻¹ * (⁅l₀, a⁆⁻¹ * ⁅l₀, x⁆) * a) * b := by
        subst hxab
        simp only [commutatorElement_def]
        group
      have hcL' : l₀ * b * l₀⁻¹ ∈ LB M Q (conjSubgroup r B) := by
        rw [hc_eq]
        exact (LB M Q (conjSubgroup r B)).mul_mem hi.2 hb.1
      have hy'L : r⁻¹ * (l₀ * b * l₀⁻¹) * r ∈ LB M Q B := by
        have h2 : l₀ * b * l₀⁻¹ ∈ LB M Q (conjSubgroup r B) := hcL'
        rw [hLs r hr, mem_conjSubgroup] at h2
        exact h2
      have hy'Ls : r⁻¹ * (l₀ * b * l₀⁻¹) * r ∈ LB M Q (conjSubgroup (r⁻¹ * l₀ * r) B) := by
        rw [hLs _ hsR, mem_conjSubgroup]
        have e : (r⁻¹ * l₀ * r)⁻¹ * (r⁻¹ * (l₀ * b * l₀⁻¹) * r) * (r⁻¹ * l₀ * r) =
            r⁻¹ * b * r := by group
        rw [e]
        have hb1 : b ∈ LB M Q (conjSubgroup r B) := hb.1
        rw [hLs r hr, mem_conjSubgroup] at hb1
        exact hb1
      have hy'T : r⁻¹ * (l₀ * b * l₀⁻¹) * r ∈ T := by
        rw [← hIeq _ hsR hopp]
        exact ⟨hy'L, hy'Ls⟩
      have hcT : l₀ * b * l₀⁻¹ ∈ T := by
        have := sec51_T_normal hRM hQn hQL hT hr hy'T
        rwa [show r * (r⁻¹ * (l₀ * b * l₀⁻¹) * r) * r⁻¹ = l₀ * b * l₀⁻¹ by group] at this
      have hcI : l₀ * b * l₀⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
        rw [hIr]; exact hcT
      have hbI : b ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
        have e : b = (a⁻¹ * (⁅l₀, a⁆⁻¹ * ⁅l₀, x⁆) * a)⁻¹ * (l₀ * b * l₀⁻¹) := by
          rw [hc_eq]; group
        rw [e]
        exact (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem
          ((LB M Q B ⊓ LB M Q (conjSubgroup r B)).inv_mem hi) hcI
      rw [hxab]
      exact (LB M Q B).mul_mem ha.1 hbI.1
  have hfL' : ∀ x ∈ hc.CN t, (x ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t ↔
      ∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B)) := by
    intro x hxN
    constructor
    · intro hx l hl
      have h1 : ⁅l, x⁆ ∈ Q := Subgroup.commutator_le.mp hC.commutator_LB_le_Q l hl x hx.1
      exact hQI h1
    · intro hx
      refine ⟨?_, hxN⟩
      obtain ⟨a, ha, b, hb, hxab⟩ := hcr.1 x hxN
      obtain ⟨l₀, hl₀, hopp⟩ := G3b r hr hplane
      have hl₀R : l₀ ∈ Rt M (LB M Q B) t := hLsR r hr hl₀
      have hlb : ⁅l₀, b⁆ ∈ Q := Subgroup.commutator_le.mp hC.commutator_LB_le_Q l₀ hl₀ b hb.1
      have hlx := hx l₀ hl₀
      have hi : ⁅l₀, x⁆ * (a * ⁅l₀, b⁆⁻¹ * a⁻¹) ∈
          LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
        (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem hlx
          (hInorm a (hNR ha.2) _ (hQI ((Q).inv_mem hlb)))
      have hc_eq : l₀ * a * l₀⁻¹ = (⁅l₀, x⁆ * (a * ⁅l₀, b⁆⁻¹ * a⁻¹)) * a := by
        subst hxab
        simp only [commutatorElement_def]
        group
      have hcL : l₀ * a * l₀⁻¹ ∈ LB M Q B := by
        rw [hc_eq]
        exact (LB M Q B).mul_mem hi.1 ha.1
      have hcLs : l₀ * a * l₀⁻¹ ∈ LB M Q (conjSubgroup l₀ B) := by
        rw [hLs l₀ hl₀R, mem_conjSubgroup]
        rw [show l₀⁻¹ * (l₀ * a * l₀⁻¹) * l₀ = a by group]
        exact ha.1
      have hcT : l₀ * a * l₀⁻¹ ∈ T := by
        rw [← hIeq l₀ hl₀R hopp]
        exact ⟨hcL, hcLs⟩
      have hcI : l₀ * a * l₀⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
        rw [hIr]; exact hcT
      have haI : a ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
        have e : a = (⁅l₀, x⁆ * (a * ⁅l₀, b⁆⁻¹ * a⁻¹))⁻¹ * (l₀ * a * l₀⁻¹) := by
          rw [hc_eq]; group
        rw [e]
        exact (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem
          ((LB M Q B ⊓ LB M Q (conjSubgroup r B)).inv_mem hi) hcI
      rw [hxab]
      exact (LB M Q (conjSubgroup r B)).mul_mem haI.2 hb.1
  have hdec : IsOppDecomp (hc.CN t) (LB M Q B ⊓ LB M Q (conjSubgroup r B)) (LB M Q B)
      (LB M Q (conjSubgroup r B)) (LB M Q B ⊓ hc.CN t)
      (LB M Q (conjSubgroup r B) ⊓ hc.CN t) := by
    refine ⟨le_inf inf_le_left hIN, inf_le_right, le_inf inf_le_right hIN, inf_le_right,
      le_antisymm (sup_le inf_le_right inf_le_right) (fun x hx => ?_), ?_, ?_, ?_, hfL, hfL'⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := hcr.1 x hx
      exact Subgroup.mul_mem_sup ha hb
    · ext x
      constructor
      · rintro ⟨⟨hxL, -⟩, ⟨hxL', -⟩⟩
        exact ⟨hxL, hxL'⟩
      · intro hx
        exact ⟨⟨hx.1, hIN hx⟩, ⟨hx.2, hIN hx⟩⟩
    · intro x hx y hy
      exact hcr.2.2 (Subgroup.commutator_mem_commutator hx hy)
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hcr.1 x hx
      have ha2 : a ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB ha.1
      have hb2 : b ^ 2 ∈ Q := hC.sq_mem_Q_of_mem_LB hb.1
      have hcom : ⁅b, a⁆ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
        hcr.2.2 (Subgroup.commutator_mem_commutator hb.2 ha.2)
      have hconj : a * ⁅b, a⁆ * a⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
        hInorm a (hNR ha.2) _ hcom
      have e : (a * b) ^ 2 = (a * ⁅b, a⁆ * a⁻¹) * a ^ 2 * b ^ 2 := by
        simp only [commutatorElement_def, pow_two]; group
      rw [e]
      exact (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem
        ((LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem hconj (hQI ha2)) (hQI hb2)
  refine ⟨hcr.1, ?_, hcr.2.1, hdec⟩
  obtain ⟨e₁, he₁, hN₁⟩ := G4 r hr hplane hInorm hdec
  obtain ⟨e₀, he₀⟩ := G5
  have hcardAB := card_mul_card_isOppDecomp hdec
  have hNnorm : r ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hr hx
  have hconj : LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [conjSubgroup_inf, ← hc.LB_conj hrM, conjSubgroup_eq_self_iff.mpr hNnorm]
  have hcard2 : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    rw [hconj]
    exact card_conjSubgroup r _
  rw [hcard2] at hcardAB
  obtain ⟨i, hi⟩ := Subgroup.card_dvd_of_le hQI
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hPpos : 0 < Nat.card Q := Nat.card_pos
  have hi2 : 2 ≤ i := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) ≤ Nat.card Q := by
      rw [hi]
      interval_cases i
      · simp
      · simp
    have heq := Subgroup.eq_of_le_of_card_ge hQI hle
    have htI : t ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
      refine ⟨ht, ?_⟩
      rw [hLs r hr]
      exact hc.mem_conjSubgroup_LB_of_mem_Rt ht hr
    rw [← heq] at htI
    exact hs.notQ htI
  have hle2 : i ≤ Nat.card Z := by
    have h3 : Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) ≤ Nat.card Q * Nat.card Z := by
      rw [hIr]; exact hTcard
    rw [hi] at h3
    exact Nat.le_of_mul_le_mul_left h3 hPpos
  have hy : Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ e₀ =
      Nat.card Q * Nat.card Z ^ (n - 1) := by rw [he₀, hL35]
  have h1 : (Nat.card Q * i) ^ 2 * Nat.card Z ^ e₁ =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) ^ 2 := by
    rw [← hi]
    calc Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) ^ 2 * Nat.card Z ^ e₁
        = (Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) * Nat.card Z ^ e₁) *
            Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) := by ring
      _ = Nat.card (hc.CN t) * Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) := by
          rw [← hN₁]
      _ = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := hcardAB
      _ = Nat.card ↥(LB M Q B ⊓ hc.CN t) ^ 2 := by ring
  have hiq := sec51_arith hq2 hPpos he₁ h1 hy hi2 hle2
  rw [hi, hiq]

end CFSG.RankThree.GF2n.Stroth80
