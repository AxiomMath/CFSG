module

public import CFSG.RankThree.PartOne.S12.Sec12Fus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] def TableFamily (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ (n = 3 ∨ n = 4)) ∨ (t = .G2 ∧ n = 0) ∨ (t = .trialityD4 ∧ n = 0) ∨
    (t = .twistedF4 ∧ n = 0) ∨ (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ (n = 2 ∨ n = 3))

@[expose] def SpecialFamily (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ n = 3)

@[expose] def RowModelsDistinct : Prop :=
  ∀ (S : Type) [Group S] (t t' : StatedLieTag) (n n' f f' : ℕ), TableFamily t n →
    TableFamily t' n' → (SpecialFamily t n ∨ SpecialFamily t' n') → LieModel S t n 2 f →
      LieModel S t' n' 2 f' → t = t' ∧ n = n' ∧ f = f'

@[expose] def rowFamily : ℕ → StatedLieTag × ℕ
  | 1 => (.PSL, 3)
  | 2 => (.G2, 0)
  | 3 => (.trialityD4, 0)
  | 4 => (.twistedF4, 0)
  | 5 => (.PSU, 4)
  | 6 => (.PSU, 5)
  | 7 => (.PSp, 2)
  | 8 => (.PSL, 4)
  | 9 => (.PSU, 4)
  | 10 => (.PSp, 3)
  | _ => (.PSU, 5)

@[expose] def RowKClause (p : ℕ) (L K : Subgroup G) : ℕ → Prop
  | 9 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 2 f
  | 12 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 2 f
  | 10 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSp 2 2 f
  | r => 1 ≤ r ∧ r ≤ 8 ∧ ∃ g : ℕ, 1 ≤ g ∧ p ∣ 2 ^ g - 1 ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 g

theorem lieModel_of_statedClassicalModel {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (ht : t ∈ classicalTags) (h : StatedClassicalModel S t n 2 f) : LieModel S t n 2 f :=
  Or.inl ⟨ht, h⟩

theorem false_of_dvd_pow_sub_add {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ 2 ^ f - 1)
    (h2 : p ∣ 2 ^ f + 1) : False := by
  have h3 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h2 h1
  have h4 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
    have := Nat.one_le_two_pow (n := f)
    omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

theorem RowModel.data {p : ℕ} {L : Subgroup G} {r : ℕ} (hr1 : 1 ≤ r) (hr12 : r ≤ 12)
    (hr11 : r ≠ 11) (h : RowModel p L r) :
    ∃ f : ℕ, 1 ≤ f ∧ LieModel (L ⧸ Subgroup.center L) (rowFamily r).1 (rowFamily r).2 2 f ∧
      (r ≤ 7 → p ∣ 2 ^ f - 1) ∧ (8 ≤ r → p ∣ 2 ^ f + 1) := by
  interval_cases r
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, fun _ => hd, by omega⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, by omega, fun _ => hd⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, by omega, fun _ => hd⟩
  · obtain ⟨f, hf, hd, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, by omega, fun _ => hd⟩
  · exact absurd rfl hr11
  · obtain ⟨hp5, -, f, hf, hd, -, hm⟩ := h
    exact ⟨f, hf, lieModel_of_statedClassicalModel (by decide) hm, by omega, fun _ => hp5 ▸ hd⟩

theorem tableFamily_rowFamily {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ 12) :
    TableFamily (rowFamily r).1 (rowFamily r).2 := by
  interval_cases r <;> simp [TableFamily, rowFamily]

theorem sf_psu {n : ℕ} (hn : n = 4 ∨ n = 5) : SpecialFamily .PSU n := Or.inl ⟨rfl, hn⟩

theorem sf_psp : SpecialFamily .PSp 3 := Or.inr ⟨rfl, rfl⟩

theorem lieModel_of_scm_psu {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSU n 2 f) : LieModel S .PSU n 2 f :=
  lieModel_of_statedClassicalModel (by decide) h

theorem lieModel_of_scm_psp {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) : LieModel S .PSp n 2 f :=
  lieModel_of_statedClassicalModel (by decide) h

section Derive

variable (hdist : RowModelsDistinct)
include hdist

theorem psu_clause_absurd {S : Type} [Group S] {t : StatedLieTag} {n₀ f₀ n f : ℕ}
    (hT : TableFamily t n₀) (hmod : LieModel S t n₀ 2 f₀) (hne : ¬ (t = .PSU ∧ n₀ = n))
    (hn : n = 4 ∨ n = 5) (hm : StatedClassicalModel S .PSU n 2 f) : False := by
  have hT' : TableFamily .PSU n := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩))))
  obtain ⟨h1, h2, -⟩ := hdist S t .PSU n₀ n f₀ f hT hT' (Or.inr (sf_psu hn)) hmod
    (lieModel_of_scm_psu hm)
  exact hne ⟨h1, h2⟩

theorem psp_clause_absurd {S : Type} [Group S] {t : StatedLieTag} {n₀ f₀ f : ℕ}
    (hT : TableFamily t n₀) (hmod : LieModel S t n₀ 2 f₀) (hne : ¬ (t = .PSp ∧ n₀ = 3))
    (hm : StatedClassicalModel S .PSp 3 2 f) : False := by
  have hT' : TableFamily .PSp 3 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))))
  obtain ⟨h1, h2, -⟩ := hdist S t .PSp n₀ 3 f₀ f hT hT' (Or.inr sf_psp) hmod
    (lieModel_of_scm_psp hm)
  exact hne ⟨h1, h2⟩

theorem psu_clause_cong {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    {n₀ f₀ n f : ℕ} (hn₀ : n₀ = 4 ∨ n₀ = 5) (hn : n = 4 ∨ n = 5)
    (hmod : LieModel S .PSU n₀ 2 f₀) (hcong : p ∣ 2 ^ f₀ - 1) (hd : p ∣ 2 ^ f + 1)
    (hm : StatedClassicalModel S .PSU n 2 f) : False := by
  have hT : TableFamily .PSU n₀ := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn₀⟩))))
  have hT' : TableFamily .PSU n := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩))))
  obtain ⟨-, -, h3⟩ := hdist S .PSU .PSU n₀ n f₀ f hT hT' (Or.inl (sf_psu hn₀)) hmod
    (lieModel_of_scm_psu hm)
  subst h3
  exact false_of_dvd_pow_sub_add hp hp2 hcong hd

theorem row_clause_absurd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] {r r' f f' : ℕ}
    (hr : r = 9 ∨ r = 10 ∨ r = 12) (hr'1 : 1 ≤ r') (hr'8 : r' ≤ 8)
    (hmod : LieModel S (rowFamily r).1 (rowFamily r).2 2 f) (hcong : p ∣ 2 ^ f + 1)
    (hmod' : LieModel S (rowFamily r').1 (rowFamily r').2 2 f')
    (hcong' : r' ≤ 7 → p ∣ 2 ^ f' - 1) : False := by
  have hT : TableFamily (rowFamily r).1 (rowFamily r).2 := by
    rcases hr with rfl | rfl | rfl <;> exact tableFamily_rowFamily (by omega) (by omega)
  have hT' : TableFamily (rowFamily r').1 (rowFamily r').2 :=
    tableFamily_rowFamily hr'1 (by omega)
  have hsp : SpecialFamily (rowFamily r).1 (rowFamily r).2 := by
    rcases hr with rfl | rfl | rfl <;> simp [SpecialFamily, rowFamily]
  obtain ⟨h1, h2, h3⟩ := hdist S _ _ _ _ _ _ hT hT' (Or.inl hsp) hmod hmod'
  subst h3
  rcases hr with rfl | rfl | rfl <;> interval_cases r' <;>
    first
    | (exfalso; simp [rowFamily] at h1 h2; done)
    | exact false_of_dvd_pow_sub_add hp hp2 (hcong' (by omega)) hcong

theorem layerModel_of_rowK_low {p : ℕ} {L K : Subgroup G} {r f₀ : ℕ}
    (hlow : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 7 ∨ r = 8) (hr12 : r ≤ 12)
    (hmod : LieModel (L ⧸ Subgroup.center L) (rowFamily r).1 (rowFamily r).2 2 f₀)
    (hc : RowKClause p L K r) : LayerModel p L K 1 := by
  have hr1 : 1 ≤ r := by omega
  have hfam := tableFamily_rowFamily hr1 hr12
  have hc3 : ∀ {g : ℕ}, StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 g →
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 (1 * g) := fun h => by simpa using h
  have hne4 : ¬ ((rowFamily r).1 = .PSU ∧ (rowFamily r).2 = 4) := by
    rcases hlow with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rowFamily]
  have hne5 : ¬ ((rowFamily r).1 = .PSU ∧ (rowFamily r).2 = 5) := by
    rcases hlow with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rowFamily]
  have hnep : ¬ ((rowFamily r).1 = .PSp ∧ (rowFamily r).2 = 3) := by
    rcases hlow with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rowFamily]
  have hr8 : r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 12 := by omega
  refine ⟨fun f _ _ hm => ?_, fun f _ _ hm => ?_, fun _ => ?_⟩
  · exfalso
    rcases hm with hm | hm
    · exact psu_clause_absurd hdist hfam hmod hne4 (Or.inl rfl) hm
    · exact psu_clause_absurd hdist hfam hmod hne5 (Or.inr rfl) hm
  · exact (psp_clause_absurd hdist hfam hmod hnep hm).elim
  · have hrc : 1 ≤ r ∧ r ≤ 8 ∧ ∃ g : ℕ, 1 ≤ g ∧ p ∣ 2 ^ g - 1 ∧
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 g := by
      rcases hlow with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hc
    obtain ⟨-, -, g, hg, hd, hK⟩ := hrc
    exact ⟨g, hg, hd, hc3 hK⟩

theorem layerModel_of_rowK {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L K : Subgroup G} {r : ℕ} (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr11 : r ≠ 11)
    (hr : RowModel p L r) (hc : RowKClause p L K r) : LayerModel p L K 1 := by
  obtain ⟨f₀, hf₀, hmod, hc7, hc8⟩ := hr.data hr1 hr12 hr11
  have hfam := tableFamily_rowFamily hr1 hr12
  have hc3 : ∀ {g : ℕ}, StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 g →
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 (1 * g) := fun h => by simpa using h
  have tf4 : TableFamily .PSU 4 := by simp [TableFamily]
  have tf5 : TableFamily .PSU 5 := by simp [TableFamily]
  have tfp3 : TableFamily .PSp 3 := by simp [TableFamily]
  interval_cases r
  · exact layerModel_of_rowK_low hdist (by decide) hr12 hmod hc
  · exact layerModel_of_rowK_low hdist (by decide) hr12 hmod hc
  · exact layerModel_of_rowK_low hdist (by decide) hr12 hmod hc
  · exact layerModel_of_rowK_low hdist (by decide) hr12 hmod hc
  ·
    refine ⟨fun f _ hd hm => ?_, fun f _ _ hm => ?_, fun _ => ?_⟩
    · exfalso
      rcases hm with hm | hm
      · exact psu_clause_cong hdist hp hp2 (n₀ := 4) (Or.inl rfl) (Or.inl rfl)
          (by simpa [rowFamily] using hmod) (hc7 (by omega)) hd hm
      · exact psu_clause_cong hdist hp hp2 (n₀ := 4) (Or.inl rfl) (Or.inr rfl)
          (by simpa [rowFamily] using hmod) (hc7 (by omega)) hd hm
    · exact (psp_clause_absurd hdist hfam hmod (by simp [rowFamily]) hm).elim
    · obtain ⟨-, -, g, hg, hd, hK⟩ := hc
      exact ⟨g, hg, hd, hc3 hK⟩
  ·
    refine ⟨fun f _ hd hm => ?_, fun f _ _ hm => ?_, fun _ => ?_⟩
    · exfalso
      rcases hm with hm | hm
      · exact psu_clause_cong hdist hp hp2 (n₀ := 5) (Or.inr rfl) (Or.inl rfl)
          (by simpa [rowFamily] using hmod) (hc7 (by omega)) hd hm
      · exact psu_clause_cong hdist hp hp2 (n₀ := 5) (Or.inr rfl) (Or.inr rfl)
          (by simpa [rowFamily] using hmod) (hc7 (by omega)) hd hm
    · exact (psp_clause_absurd hdist hfam hmod (by simp [rowFamily]) hm).elim
    · obtain ⟨-, -, g, hg, hd, hK⟩ := hc
      exact ⟨g, hg, hd, hc3 hK⟩
  · exact layerModel_of_rowK_low hdist (by decide) hr12 hmod hc
  · exact layerModel_of_rowK_low hdist (by decide) hr12 hmod hc
  ·
    refine ⟨fun f hf hd hm => ?_, fun f _ _ hm => ?_, fun ⟨r', h1, h8, hr'⟩ => ?_⟩
    · obtain ⟨f', hf', hd', hL', hK'⟩ := hc
      rcases hm with hm | hm
      · obtain ⟨-, -, rfl⟩ := hdist _ .PSU .PSU 4 4 f' f tf4 tf4 (Or.inl (sf_psu (Or.inl rfl))) (lieModel_of_scm_psu hL')
          (lieModel_of_scm_psu hm)
        simpa using hK'
      · obtain ⟨-, h, -⟩ := hdist _ .PSU .PSU 4 5 f' f tf4 tf5 (Or.inl (sf_psu (Or.inl rfl))) (lieModel_of_scm_psu hL')
          (lieModel_of_scm_psu hm)
        omega
    · exact (psp_clause_absurd hdist hfam hmod (by simp [rowFamily]) hm).elim
    · exfalso
      obtain ⟨f', hf', hmod', hc7', hc8'⟩ := hr'.data h1 (by omega) (by omega)
      exact row_clause_absurd hdist hp hp2 (Or.inl rfl) h1 h8 hmod (hc8 (by omega)) hmod' hc7'
  ·
    refine ⟨fun f _ _ hm => ?_, fun f hf hd hm => ?_, fun ⟨r', h1, h8, hr'⟩ => ?_⟩
    · exfalso
      rcases hm with hm | hm
      · exact psu_clause_absurd hdist hfam hmod (by simp [rowFamily]) (Or.inl rfl) hm
      · exact psu_clause_absurd hdist hfam hmod (by simp [rowFamily]) (Or.inr rfl) hm
    · obtain ⟨f', hf', hd', hL', hK'⟩ := hc
      obtain ⟨-, -, rfl⟩ := hdist _ .PSp .PSp 3 3 f' f tfp3 tfp3 (Or.inl sf_psp) (lieModel_of_scm_psp hL')
        (lieModel_of_scm_psp hm)
      simpa using hK'
    · exfalso
      obtain ⟨f', hf', hmod', hc7', hc8'⟩ := hr'.data h1 (by omega) (by omega)
      exact row_clause_absurd hdist hp hp2 (Or.inr (Or.inl rfl)) h1 h8 hmod (hc8 (by omega))
        hmod' hc7'
  · exact absurd rfl hr11
  ·
    refine ⟨fun f hf hd hm => ?_, fun f _ _ hm => ?_, fun ⟨r', h1, h8, hr'⟩ => ?_⟩
    · obtain ⟨f', hf', hd', hL', hK'⟩ := hc
      rcases hm with hm | hm
      · obtain ⟨-, h, -⟩ := hdist _ .PSU .PSU 5 4 f' f tf5 tf4 (Or.inl (sf_psu (Or.inr rfl))) (lieModel_of_scm_psu hL')
          (lieModel_of_scm_psu hm)
        omega
      · obtain ⟨-, -, rfl⟩ := hdist _ .PSU .PSU 5 5 f' f tf5 tf5 (Or.inl (sf_psu (Or.inr rfl))) (lieModel_of_scm_psu hL')
          (lieModel_of_scm_psu hm)
        simpa using hK'
    · exact (psp_clause_absurd hdist hfam hmod (by simp [rowFamily]) hm).elim
    · exfalso
      obtain ⟨f', hf', hmod', hc7', hc8'⟩ := hr'.data h1 (by omega) (by omega)
      exact row_clause_absurd hdist hp hp2 (Or.inr (Or.inr rfl)) h1 h8 hmod (hc8 (by omega))
        hmod' hc7'

end Derive

end CFSG.RankThree.PartOne
