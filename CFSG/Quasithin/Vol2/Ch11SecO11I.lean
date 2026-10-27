module

public import CFSG.Quasithin.Vol2.Ch11SecO11H
public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import CFSG.RankThree.PartOne.K1214.Basic
public import Certificates.Certificate2197
public import Certificates.Certificate4075
public import Certificates.Certificate7118
public import Certificates.Certificate7123
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat

@[expose] def m23L : Array ℕ := #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9]

@[expose] def inclM23 (j jj : ℕ) : Prop := jj = 16 ∨ (j < 16 ∧ jj < 16 ∧ jj ∈ m23Incl[j]!)

instance (j jj : ℕ) : Decidable (inclM23 j jj) :=
  inferInstanceAs (Decidable (jj = 16 ∨ (j < 16 ∧ jj < 16 ∧ jj ∈ m23Incl[j]!)))

abbrev GM23 : Type := ↥CFSG.Blueprint.NativeSporadic.M23

theorem not_dvd_card_of_l24 {Γ : Type} [Group Γ] [Finite Γ] {S B : Subgroup Γ}
    (hB : IsL24Sub S B) {p : ℕ} (hp : p.Prime) (hp15 : ¬ p ∣ 15) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card B := by
  obtain ⟨a, ha⟩ := card_of_l24 hB
  rw [ha]
  intro h
  rcases hp.dvd_mul.mp h with h' | h'
  · exact hp15 h'
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))


open CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card m23_eq_closure) in
noncomputable abbrev m23CtxO : LatCtx GM23 23 (List ℕ) := m23Ctx

theorem m23_hL : m23CtxO.D.Om.map (fun o => o.lbl.size) = m23L := m23_lat_cert.2.2

theorem m23_hN : m23CtxO.D.O.lbl.size = 79695 := m23_lat_cert.2.1

theorem m23_all : ∀ Z : Subgroup GM23, m23CtxO.S ≤ Z → ∃ j ≤ 16, Z = memberOrTop 16 m23CtxO.Y j :=
  lat_all m23CtxO m23_hL

theorem m23_card (j : ℕ) : Nat.card (memberOrTop 16 m23CtxO.Y j) = latSz m23L 79695 j * 2 ^ 7 :=
  list_card (lat_card m23CtxO m23_hL) (by rw [m23CtxO.hΓ, m23_hN]) j

theorem m23_member {j : ℕ} (hj : j < 16) : memberOrTop 16 m23CtxO.Y j = m23CtxO.Y j := by
  unfold memberOrTop
  rw [ite_eq_left hj]

theorem isSylowTwoOf_m23 : IsSylowTwoOf m23CtxO.S ⊤ := by
  have hN : m23CtxO.D.O.lbl.size = 79695 := m23_hN
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxO.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m23CtxO.S
  rw [m23CtxO.S_card, m23CtxO.hΓ, hN] at h1
  have h2 : m23CtxO.S.index = 79695 := by
    have : m23CtxO.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num


theorem m23O_Y_le_iff {j jj : ℕ} (hj : j < 16) (hjj : jj < 16) :
    m23CtxO.Y j ≤ m23CtxO.Y jj ↔ jj ∈ m23Incl[j]! := by
  rw [m23Ctx_Y, m23Ctx_Y]
  exact Certificates.certificate7123 j hj jj hjj

theorem m23_le_iff {j jj : ℕ} (hj : j ≤ 16) (hjj : jj ≤ 16) :
    memberOrTop 16 m23CtxO.Y j ≤ memberOrTop 16 m23CtxO.Y jj ↔ inclM23 j jj := by
  rcases Nat.lt_or_ge jj 16 with hjj' | hjj'
  · have hjj16 : jj ≠ 16 := by omega
    rcases Nat.lt_or_ge j 16 with hj' | hj'
    · rw [m23_member hj', m23_member hjj', m23O_Y_le_iff hj' hjj']
      simp only [inclM23, hjj16, false_or, hj', hjj', true_and]
    · have hj16 : j = 16 := by omega
      subst hj16
      simp only [inclM23, hjj16, false_or, lt_irrefl, false_and, iff_false]
      intro h
      have h1 := Subgroup.card_le_of_le h
      rw [m23_card, m23_card] at h1
      have h2 : ∀ i < 16, latSz m23L 79695 i < latSz m23L 79695 16 := by decide
      exact absurd h1 (not_le.mpr (Nat.mul_lt_mul_of_pos_right (h2 jj hjj') (by positivity)))
  · have hjj16 : jj = 16 := by omega
    subst hjj16
    simp only [inclM23, true_or, iff_true]
    unfold memberOrTop
    rw [ite_eq_right (lt_irrefl _)]
    exact le_top

theorem m23_false_of_normal {B : Subgroup GM23} (hB : IsL24Sub m23CtxO.S B)
    (h9 : B ⊔ m23CtxO.S = m23CtxO.Y 9) {n c p : ℕ} (hn : n ≤ 16) (hc : c < 16)
    (hN : memberOrTop 16 m23CtxO.Y n = Subgroup.normalizer (B : Set GM23))
    (hcn : inclM23 c n) (hbet : ∀ d ≤ 16, inclM23 c d → inclM23 d n → d = c ∨ d = n)
    (h9c : ¬ inclM23 9 c) (hp : p.Prime) (hpn : p ∣ latSz m23L 79695 n)
    (hpc : ¬ p ∣ latSz m23L 79695 c) (hp15 : ¬ p ∣ 15) (hp2 : p ≠ 2) : False := by
  have hcN : m23CtxO.Y c ≤ Subgroup.normalizer (B : Set GM23) := by
    rw [← hN, ← m23_member hc]
    exact (m23_le_iff (by omega) hn).mpr hcn
  obtain ⟨d, hd, hdZ⟩ := m23_all (B ⊔ m23CtxO.Y c) (le_sup_of_le_right (m23CtxO.S_le_Y c))
  have hcd : inclM23 c d := by
    rw [← m23_le_iff (j := c) (by omega) hd, ← hdZ, m23_member hc]
    exact le_sup_right
  have hdn : inclM23 d n := by
    rw [← m23_le_iff hd hn, ← hdZ, hN]
    exact sup_le Subgroup.le_normalizer hcN
  rcases hbet d hd hcd hdn with hdc | hdn'
  · rw [hdc, m23_member hc] at hdZ
    apply h9c
    rw [← m23_le_iff (j := 9) (jj := c) (by norm_num) (by omega), m23_member (j := 9) (by norm_num),
      m23_member hc, ← h9]
    exact sup_le (le_sup_left.trans hdZ.le) (m23CtxO.S_le_Y c)
  · rw [hdn'] at hdZ
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hcN
    rw [hdZ, m23_card, ← m23_member hc, m23_card] at hprod
    have h1 : p ∣ Nat.card B * (latSz m23L 79695 c * 2 ^ 7) := by
      rw [← hprod]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hpn _) _
    rcases hp.dvd_mul.mp h1 with h | h
    · exact not_dvd_card_of_l24 hB hp hp15 hp2 h
    · rcases hp.dvd_mul.mp h with h' | h'
      · exact hpc h'
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))

theorem m23_card_normalizer {B : Subgroup GM23} (hB : IsL24Sub m23CtxO.S B)
    (h9 : B ⊔ m23CtxO.S = m23CtxO.Y 9) :
    Nat.card (Subgroup.normalizer (B : Set GM23)) = 15 * 2 ^ 7 := by
  obtain ⟨n, hn, hNn⟩ := m23_all _ hB.2.2.1
  have h9n : inclM23 9 n := by
    rw [← m23_le_iff (j := 9) (by norm_num) hn, ← hNn, m23_member (j := 9) (by norm_num), ← h9]
    exact sup_le Subgroup.le_normalizer hB.2.2.1
  have hcases : n = 2 ∨ n = 5 ∨ n = 9 ∨ n = 16 := by
    have key : ∀ i ≤ 16, inclM23 9 i → i = 2 ∨ i = 5 ∨ i = 9 ∨ i = 16 := by decide
    exact key n hn h9n
  rcases hcases with rfl | rfl | rfl | rfl
  · exact (m23_false_of_normal hB h9 (c := 7) (p := 7) (by norm_num) (by norm_num) hNn.symm
      (by decide) (by decide) (by decide) (by norm_num) (by decide) (by decide) (by decide)
      (by norm_num)).elim
  · exact (m23_false_of_normal hB h9 (c := 15) (p := 7) (by norm_num) (by norm_num) hNn.symm
      (by decide) (by decide) (by decide) (by norm_num) (by decide) (by decide) (by decide)
      (by norm_num)).elim
  · rw [hNn, m23_card]
    all_goals rfl
  · exact (m23_false_of_normal hB h9 (c := 1) (p := 23) (by norm_num) (by norm_num) hNn.symm
      (by decide) (by decide) (by decide) (by norm_num) (by decide) (by decide) (by decide)
      (by norm_num)).elim

theorem noE9Pair_m23CtxO : NoE9Pair m23CtxO.S := by
  intro B₁ B₂ E h₁ h₂ hne hE hE₁ hE₂
  have key : ∀ {B : Subgroup GM23}, IsL24Sub m23CtxO.S B →
      B ⊔ m23CtxO.S = m23CtxO.Y 7 ∨ B ⊔ m23CtxO.S = m23CtxO.Y 9 := by
    intro B hB
    obtain ⟨j, hj, hZ, h15⟩ := exists_member_fifteen (L := m23L) (N := 79695)
      m23CtxO.S_isPGroup m23_all (lat_card m23CtxO m23_hL)
      (by rw [m23CtxO.hΓ, m23_hN]) (by decide) hB
    have hj' : j = 7 ∨ j = 9 := by
      have key : ∀ i ≤ m23L.size, latSz m23L 79695 i = 15 → i = 7 ∨ i = 9 := by decide
      exact key j hj h15
    rcases hj' with rfl | rfl
    · exact Or.inl (hZ.trans (m23_member (by norm_num)))
    · exact Or.inr (hZ.trans (m23_member (by norm_num)))
  have hno : ∀ {B : Subgroup GM23}, IsL24Sub m23CtxO.S B → B ⊔ m23CtxO.S = m23CtxO.Y 9 →
      E ≤ Subgroup.normalizer (B : Set GM23) → False := by
    intro B hB h9 hEB
    have h := Subgroup.card_dvd_of_le hEB
    rw [hE, m23_card_normalizer hB h9] at h
    norm_num at h
  rcases key h₁ with e₁ | e₁
  · rcases key h₂ with e₂ | e₂
    · exact hne (eq_of_sup_eq m23CtxO.S_isPGroup h₁ h₂ (e₁.trans e₂.symm))
    · exact hno h₂ e₂ hE₂
  · exact hno h₁ e₁ hE₁

theorem noE9Pair_m23 {Q : Type} [Group Q] [Finite Q] (hQ : IsSporadic .M23 Q) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : NoE9Pair S := by
  obtain ⟨e⟩ := hQ
  exact noE9Pair_of_equiv isSylowTwoOf_m23 noE9Pair_m23CtxO ⟨e⟩ hS

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
