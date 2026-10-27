module

public import CFSG.RankThree.PartOne.KFR4.SuppGen
public import CFSG.RankThree.PartOne.KFR4.CentDecomp
public import CFSG.RankThree.PartOne.KFR4.UniGen
public import CFSG.RankThree.PartOne.KFR4.Flip
public import CFSG.RankThree.PartOne.KFCL.Core

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

namespace Signs

variable {p : ℕ}

def Bad (A : AddSubgroup (Fin 3 → ZMod p)) (s t : ZMod p) (i j : Fin 3) : Prop :=
  (∀ a ∈ A, s * a i = -(t * a j)) ∧ ∃ a ∈ A, a i ≠ 0

theorem zmod_mul_eq_zero (hp : p.Prime) {a b : ZMod p} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have := Fact.mk hp
  exact mul_eq_zero.1 h

theorem zmod_mul_ne_zero (hp : p.Prime) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := fun h => (zmod_mul_eq_zero hp h).elim ha hb

theorem bad_diag (hp : p.Prime) (h2 : (2 : ZMod p) ≠ 0) {A : AddSubgroup (Fin 3 → ZMod p)}
    {s : ZMod p} (hs : s ≠ 0) (i : Fin 3) : ¬ Bad A s s i i := by
  rintro ⟨h, a, ha, hai⟩
  have h1 := h a ha
  have : (2 * s) * a i = 0 := by linear_combination h1
  rcases zmod_mul_eq_zero hp this with h3 | h3
  · exact zmod_mul_ne_zero hp h2 hs h3
  · exact hai h3

theorem bad_symm (hp : p.Prime) {A : AddSubgroup (Fin 3 → ZMod p)} {s t : ZMod p} (hs : s ≠ 0)
    {i j : Fin 3} (h : Bad A s t i j) : Bad A t s j i := by
  obtain ⟨h1, a, ha, hai⟩ := h
  refine ⟨fun a ha => by linear_combination h1 a ha, a, ha, ?_⟩
  intro hj
  have h3 : s * a i = 0 := by rw [h1 a ha, hj]; simp
  exact hai ((zmod_mul_eq_zero hp h3).resolve_left hs)

theorem bad_opp (hp : p.Prime) (h2 : (2 : ZMod p) ≠ 0) {A : AddSubgroup (Fin 3 → ZMod p)}
    {s t : ZMod p} (hs : s ≠ 0) (ht : t ≠ 0) {i j : Fin 3}
    (h : Bad A s t i j) (h' : Bad A s (-t) i j) : False := by
  obtain ⟨h1, a, ha, hai⟩ := h
  obtain ⟨h1', -⟩ := h'
  have e1 := h1 a ha
  have e2 := h1' a ha
  have : (2 * t) * a j = 0 := by linear_combination e1 - e2
  rcases zmod_mul_eq_zero hp this with h3 | h3
  · exact zmod_mul_ne_zero hp h2 ht h3
  · have h4 : s * a i = 0 := by rw [e1, h3]; simp
    exact hai ((zmod_mul_eq_zero hp h4).resolve_left hs)

theorem exists_signs (hp : p.Prime) (hp2 : p ≠ 2) (A : AddSubgroup (Fin 3 → ZMod p)) :
    ∃ s : Fin 3 → ZMod p, (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ i j, ¬ Bad A (s i) (s j) i j := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have h1 : (1 : ZMod p) ≠ 0 := by
    have := Fact.mk hp.one_lt
    exact one_ne_zero
  have hm1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 h1
  obtain ⟨s₁, hs₁, hC01⟩ : ∃ s₁ : ZMod p, (s₁ = 1 ∨ s₁ = -1) ∧ ¬ Bad A 1 s₁ 0 1 := by
    by_cases hb : Bad A 1 1 0 1
    · refine ⟨-1, Or.inr rfl, fun hb' => ?_⟩
      exact bad_opp hp h2 h1 h1 hb (by simpa using hb')
    · exact ⟨1, Or.inl rfl, hb⟩
  have hs₁ne : s₁ ≠ 0 := by rcases hs₁ with rfl | rfl <;> assumption
  obtain ⟨s₂, hs₂, hC02, hC12⟩ : ∃ s₂ : ZMod p, (s₂ = 1 ∨ s₂ = -1) ∧ ¬ Bad A 1 s₂ 0 2 ∧
      ¬ Bad A s₁ s₂ 1 2 := by
    by_cases hb : Bad A 1 1 0 2 ∨ Bad A s₁ 1 1 2
    · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · intro hb'
        rcases hb with hb | hb
        · exact bad_opp hp h2 h1 h1 hb (by simpa using hb')
        · obtain ⟨e1, a, ha, hai⟩ := hb'
          obtain ⟨e2, -⟩ := hb
          exact hC01 ⟨fun a ha => by linear_combination e1 a ha + e2 a ha, a, ha, hai⟩
      · intro hb'
        rcases hb with hb | hb
        · obtain ⟨e1, a, ha, hai⟩ := hb
          obtain ⟨e2, -⟩ := hb'
          exact hC01 ⟨fun a ha => by linear_combination e1 a ha + e2 a ha, a, ha, hai⟩
        · exact bad_opp hp h2 hs₁ne h1 hb (by simpa using hb')
    · push Not at hb
      exact ⟨1, Or.inl rfl, hb.1, hb.2⟩
  have hs₂ne : s₂ ≠ 0 := by rcases hs₂ with rfl | rfl <;> assumption
  refine ⟨![1, s₁, s₂], fun i => ?_, fun i j => ?_⟩
  · fin_cases i
    · exact Or.inl rfl
    · exact hs₁
    · exact hs₂
  · fin_cases i <;> fin_cases j
    · exact bad_diag hp h2 h1 0
    · exact hC01
    · exact hC02
    · exact fun h => hC01 (bad_symm hp hs₁ne h)
    · exact bad_diag hp h2 hs₁ne 1
    · exact hC12
    · exact fun h => hC02 (bad_symm hp hs₂ne h)
    · exact fun h => hC12 (bad_symm hp hs₂ne h)
    · exact bad_diag hp h2 hs₂ne 2


end Signs

namespace DLe

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

def Stm (R : Subgroup (Vs K E ≃ₗ[K] Vs K E)) : Prop :=
  ⁅Subgroup.centralizer (R : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓ Om S.D,
    Subgroup.centralizer (R : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓ Om S.D⁆ ≤
    ⨆ ρ : {ρ : Root // R ≤ hypA S ρ}, Block S.D ρ.1

noncomputable def mapConj (k : Fin 3) (R : Subgroup (Vs K E ≃ₗ[K] Vs K E)) :
    Subgroup (Vs K E ≃ₗ[K] Vs K E) :=
  R.map (MulAut.conj (conjCoord S.D k)).toMonoidHom

omit [Module.Finite K E] in
theorem conjCoord_mul_self (k : Fin 3) : conjCoord S.D k * conjCoord S.D k = 1 := by
  have := mul_inv_cancel (conjCoord S.D k)
  rwa [conjCoord_inv] at this

theorem mapConj_mapConj (k : Fin 3) (R : Subgroup (Vs K E ≃ₗ[K] Vs K E)) :
    mapConj S k (mapConj S k R) = R := by
  unfold mapConj
  rw [Subgroup.map_map]
  have : (MulAut.conj (conjCoord S.D k)).toMonoidHom.comp
      (MulAut.conj (conjCoord S.D k)).toMonoidHom = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    show conjCoord S.D k * (conjCoord S.D k * x * (conjCoord S.D k)⁻¹) * (conjCoord S.D k)⁻¹ = x
    rw [conjCoord_inv]
    calc conjCoord S.D k * (conjCoord S.D k * x * conjCoord S.D k) * conjCoord S.D k
        = (conjCoord S.D k * conjCoord S.D k) * x * (conjCoord S.D k * conjCoord S.D k) := by
          simp only [mul_assoc]
      _ = x := by rw [conjCoord_mul_self, one_mul, mul_one]
  rw [this, Subgroup.map_id]

omit [Module.Finite K E] [Finite K] [CharP K 2] in
theorem map_conj_orthogonalGroup {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    {τ : V ≃ₗ[K] V} (hτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (TauCeti.QuadraticMap.orthogonalGroup Q).map (MulAut.conj τ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hτ hx) (inv_mem hτ)
  · intro hy
    refine ⟨τ⁻¹ * y * τ, mul_mem (mul_mem (inv_mem hτ) hy) hτ, ?_⟩
    show τ * (τ⁻¹ * y * τ) * τ⁻¹ = y
    group

omit [Module.Finite K E] in
theorem map_conj_orthDerived {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    {τ : V ≃ₗ[K] V} (hτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (CFSG.RankThree.Classical2.orthDerived Q).map (MulAut.conj τ).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived Q := by
  unfold CFSG.RankThree.Classical2.orthDerived
  rw [Subgroup.map_commutator, map_conj_orthogonalGroup Q hτ]

theorem stm_conj (k : Fin 3) {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)} (h : Stm S R) :
    Stm S (mapConj S k R) := by
  have hτ := conjCoord_mem_orthogonalGroup S k
  set φ : (Vs K E ≃ₗ[K] Vs K E) ≃* (Vs K E ≃ₗ[K] Vs K E) := MulAut.conj (conjCoord S.D k) with hφ
  have hC : Subgroup.centralizer ((mapConj S k R : Subgroup _) : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓
      Om S.D = (Subgroup.centralizer (R : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓ Om S.D).map
        φ.toMonoidHom := by
    rw [Subgroup.map_inf _ _ φ.toMonoidHom φ.injective,
      KFCL.map_centralizer_equiv, map_conj_orthDerived _ hτ]
    rfl
  unfold Stm at h ⊢
  rw [hC, ← Subgroup.map_commutator]
  refine (Subgroup.map_mono h).trans ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ρ => ?_
  refine le_iSup_of_le ⟨Root.flip k ρ.1, ?_⟩ ?_
  · rw [← hypA_conj_flip S k ρ.1]
    exact Subgroup.map_mono ρ.2
  · rw [block_conj_flip S k ρ.1]

theorem flipVec_apply (k i : Fin 3) (a : Fin 3 → ZMod p) :
    flipVec k a i = if i = k then -a k else a i := by
  by_cases h : i = k
  · subst h
    simp [flipVec]
  · simp [flipVec, h]

theorem flipVec_flipVec (k : Fin 3) (a : Fin 3 → ZMod p) : flipVec k (flipVec k a) = a := by
  funext i
  by_cases h : i = k
  · subst h
    simp [flipVec_apply]
  · simp [flipVec_apply, h]

omit [Module.Finite K E] in
theorem mem_coords_mapConj (k : Fin 3) (R : Subgroup (Vs K E ≃ₗ[K] Vs K E))
    (a : Fin 3 → ZMod p) : a ∈ coords S (mapConj S k R) ↔ flipVec k a ∈ coords S R := by
  constructor
  · rintro ⟨r, hr, hra⟩
    have h1 : r = tor S (flipVec k a) := by
      have h2 : conjCoord S.D k * r * (conjCoord S.D k)⁻¹ = tor S a := hra
      have h3 : r = (conjCoord S.D k)⁻¹ * tor S a * conjCoord S.D k := by
        rw [← h2]
        group
      rw [h3, conjCoord_inv, ← conjCoord_inv S.D k]
      exact conj_tor S k a
    rw [mem_coords, ← h1]
    exact hr
  · intro h
    refine ⟨tor S (flipVec k a), h, ?_⟩
    show conjCoord S.D k * tor S (flipVec k a) * (conjCoord S.D k)⁻¹ = tor S a
    rw [conj_tor, flipVec_flipVec]

noncomputable def flipList : List (Fin 3) → Subgroup (Vs K E ≃ₗ[K] Vs K E) →
    Subgroup (Vs K E ≃ₗ[K] Vs K E)
  | [], R => R
  | k :: L, R => mapConj S k (flipList L R)

def flipListVec : List (Fin 3) → (Fin 3 → ZMod p) → (Fin 3 → ZMod p)
  | [], a => a
  | k :: L, a => flipListVec L (flipVec k a)

theorem stm_of_flipList (L : List (Fin 3)) {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)}
    (h : Stm S (flipList S L R)) : Stm S R := by
  induction L with
  | nil => exact h
  | cons k L ih =>
    apply ih
    have := stm_conj S k h
    rwa [flipList, mapConj_mapConj] at this

theorem mem_coords_flipList (L : List (Fin 3)) (R : Subgroup (Vs K E ≃ₗ[K] Vs K E))
    (a : Fin 3 → ZMod p) :
    a ∈ coords S (flipList S L R) ↔ flipListVec L a ∈ coords S R := by
  induction L generalizing a with
  | nil => exact Iff.rfl
  | cons k L ih =>
    rw [flipList, mem_coords_mapConj, ih, flipListVec]

theorem flipListVec_apply (L : List (Fin 3)) (hL : L.Nodup) (a : Fin 3 → ZMod p) (i : Fin 3) :
    flipListVec L a i = if i ∈ L then -a i else a i := by
  induction L generalizing a with
  | nil => simp [flipListVec]
  | cons k L ih =>
    rw [List.nodup_cons] at hL
    rw [flipListVec, ih hL.2, flipVec_apply]
    by_cases h : i = k
    · subst h
      simp [hL.1]
    · simp [h]

theorem exists_flipList_coherent (R : Subgroup (Vs K E ≃ₗ[K] Vs K E)) :
    ∃ L : List (Fin 3), Coherent (coords S (flipList S L R)) := by
  classical
  have hp2 : p ≠ 2 := by have := S.hp5; omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq S.hp Nat.prime_two).1 this)
  have hne : (1 : ZMod p) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  obtain ⟨s, hs, hno⟩ := Signs.exists_signs S.hp hp2 (coords S R)
  let T : Finset (Fin 3) := Finset.univ.filter fun i => s i = -1
  refine ⟨T.toList, ?_⟩
  have hflip : ∀ (a : Fin 3 → ZMod p) (i : Fin 3), flipListVec T.toList a i = s i * a i := by
    intro a i
    rw [flipListVec_apply _ (Finset.nodup_toList T)]
    rcases hs i with h | h
    · have : i ∉ T.toList := by
        rw [Finset.mem_toList]
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact hne
      rw [ite_eq_right_iff.2 (fun h' => absurd h' this), h, one_mul]
    · have : i ∈ T.toList := by
        rw [Finset.mem_toList]
        simp [T, h]
      rw [ite_eq_left_iff.2 (fun h' => absurd this h'), h]
      ring
  have hsne : ∀ i, s i ≠ 0 := by
    intro i
    rcases hs i with h | h
    · rw [h]
      have := Fact.mk S.hp.one_lt
      exact one_ne_zero
    · rw [h]
      have := Fact.mk S.hp.one_lt
      exact neg_ne_zero.2 one_ne_zero
  have hsq : ∀ i, s i * s i = 1 := by
    intro i
    rcases hs i with h | h <;> rw [h] <;> ring
  intro i j hij b hb
  by_contra hbi
  have hb' : flipListVec T.toList b ∈ coords S R := (mem_coords_flipList S _ R b).1 hb
  refine hno i j ⟨fun a ha => ?_, flipListVec T.toList b, hb', ?_⟩
  · set b' : Fin 3 → ZMod p := flipListVec T.toList a with hb'def
    have hb'mem : b' ∈ coords S (flipList S T.toList R) := by
      rw [mem_coords_flipList]
      have : flipListVec T.toList b' = a := by
        funext k
        rw [hflip, hb'def, hflip, ← mul_assoc, hsq, one_mul]
      rw [this]
      exact ha
    have := hij b' hb'mem
    rw [hb'def, hflip, hflip] at this
    exact this
  · rw [hflip]
    exact (Signs.zmod_mul_ne_zero S.hp (hsne i) hbi)

theorem commutator_mul_of_commute {G : Type*} [Group G] {f₁ f₂ m₁ m₂ : G}
    (h11 : Commute f₁ m₁) (h12 : Commute f₁ m₂) (h21 : Commute f₂ m₁) (h22 : Commute f₂ m₂) :
    ⁅f₁ * m₁, f₂ * m₂⁆ = ⁅f₁, f₂⁆ * ⁅m₁, m₂⁆ := by
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  rw [h21.symm.left_comm, h11.inv_inv.symm.left_comm, h12.symm.inv_right.left_comm,
    h11.symm.inv_right.left_comm, h22.inv_inv.symm.eq, h21.inv_inv.symm.left_comm,
    h22.symm.inv_right.left_comm, h21.symm.inv_right.left_comm]

omit [Module.Finite K E] in
theorem tor_mem_Tstd' (a : Fin 3 → ZMod p) : tor S a ∈ Tstd S := ⟨Multiplicative.ofAdd a, rfl⟩

omit [Module.Finite K E] in
theorem mapConj_le_Tstd (k : Fin 3) {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)} (hR : R ≤ Tstd S) :
    mapConj S k R ≤ Tstd S := by
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨a, rfl⟩ := hR hr
  show conjCoord S.D k * tor S (Multiplicative.toAdd a) * (conjCoord S.D k)⁻¹ ∈ Tstd S
  rw [conj_tor]
  exact tor_mem_Tstd' S _

omit [Module.Finite K E] in
theorem flipList_le_Tstd (L : List (Fin 3)) {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)}
    (hR : R ≤ Tstd S) : flipList S L R ≤ Tstd S := by
  induction L with
  | nil => exact hR
  | cons k L ih => exact mapConj_le_Tstd S k ih

omit [Module.Finite K E] in
theorem flipList_ne_bot (L : List (Fin 3)) {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)} (hR : R ≠ ⊥) :
    flipList S L R ≠ ⊥ := by
  induction L with
  | nil => exact hR
  | cons k L ih =>
    intro h
    apply ih
    exact (Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj (conjCoord S.D k)).toMonoidHom)
      _ (MulAut.conj (conjCoord S.D k)).injective).1 h

theorem stm_of_coherent {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)} (hRT : R ≤ Tstd S) (hR : R ≠ ⊥)
    (hcoh : Coherent (coords S R)) : Stm S R := by
  have hA : coords S R ≠ ⊥ := by
    intro h
    apply hR
    rw [eq_bot_iff]
    intro r hr
    obtain ⟨a, rfl⟩ := hRT hr
    have h1 : Multiplicative.toAdd a ∈ coords S R := hr
    rw [h, AddSubgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have : a = 1 := Multiplicative.toAdd.injective h1
    rw [this, map_one]
  have hvan : ∀ ρ : Root, vanishes (coords S R) ρ ↔ R ≤ hypA S ρ := by
    intro ρ
    constructor
    · intro hv r hr
      obtain ⟨a, rfl⟩ := hRT hr
      exact ⟨Multiplicative.toAdd a, hv _ hr, rfl⟩
    · intro hle a ha
      obtain ⟨b, hb, hba⟩ := hle ha
      have h1 : torHom S (Multiplicative.ofAdd b) = torHom S (Multiplicative.ofAdd a) := hba
      have h2 : b = a := Multiplicative.ofAdd.injective (torHom_injective S h1)
      rw [← h2]
      exact hb
  have hO : ∀ g ∈ Om S.D, g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs S.D) := fun g hg =>
    (Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) hg
  have decomp : ∀ g ∈ Subgroup.centralizer (R : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓ Om S.D,
      ∃ (f : Vs K E ≃ₗ[K] Vs K E) (M : GL (Fin 3) E), f ∈ Supp S.D (fixedSet (coords S R)) ∧
        f ∈ Om S.D ∧ UniBdP S.D (coords S R) M ∧ g = f * matToG K M := by
    intro g hg
    have hcomm : ∀ a ∈ coords S R, g * tor S a = tor S a * g := fun a ha =>
      (Subgroup.mem_centralizer_iff.1 hg.1 (tor S a) ha).symm
    obtain ⟨f, M, hf, hM, hgfm, hfOm⟩ :=
      centralizer_decomp S (coords S R) hcoh (hO g hg.2) hcomm
    exact ⟨f, M, hf, hfOm hg.2, hM, hgfm⟩
  have hJ : (⨆ ρ : {ρ : Root // vanishes (coords S R) ρ}, Block S.D ρ.1) ≤
      ⨆ ρ : {ρ : Root // R ≤ hypA S ρ}, Block S.D ρ.1 :=
    iSup_le fun ρ => le_iSup_of_le ⟨ρ.1, (hvan _).1 ρ.2⟩ le_rfl
  unfold Stm
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨f₁, M₁, hf₁, hf₁O, hM₁, rfl⟩ := decomp g₁ hg₁
  obtain ⟨f₂, M₂, hf₂, hf₂O, hM₂, rfl⟩ := decomp g₂ hg₂
  rw [commutator_mul_of_commute (supp_commute_matToG S _ hf₁ hM₁) (supp_commute_matToG S _ hf₁ hM₂)
    (supp_commute_matToG S _ hf₂ hM₁) (supp_commute_matToG S _ hf₂ hM₂)]
  refine mul_mem (hJ (supp_commutator_mem S _ hA f₁ f₂ ⟨hf₁, hf₁O⟩ ⟨hf₂, hf₂O⟩)) ?_
  rw [← map_commutatorElement]
  exact hJ (unitary_commutator_mem S _ M₁ M₂ hM₁ hM₂)

theorem stm_of_le_Tstd {R : Subgroup (Vs K E ≃ₗ[K] Vs K E)} (hRT : R ≤ Tstd S) (hR : R ≠ ⊥) :
    Stm S R := by
  obtain ⟨L, hL⟩ := exists_flipList_coherent S R
  exact stm_of_flipList S L
    (stm_of_coherent S (flipList_le_Tstd S L hRT) (flipList_ne_bot S L hR) hL)

omit [Module.Finite K E] in
theorem card_Tstd : Nat.card (Tstd S) = p ^ 3 := by
  have h1 : Nat.card (Multiplicative (Fin 3 → ZMod p)) = p ^ 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [← h1]
  exact (Nat.card_congr (MonoidHom.ofInjective (torHom_injective S)).toEquiv).symm

end DLe

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

theorem derived_le_std (R : Subgroup (Vs K E ≃ₗ[K] Vs K E)) (hRT : R ≤ Tstd S)
    (hR : R.relIndex (Tstd S) = p ∨ ∃ e, e ∈ Tstd S ∧ e ≠ 1 ∧ R = Subgroup.zpowers e) :
    ⁅Subgroup.centralizer (R : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓ Om S.D,
      Subgroup.centralizer (R : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓ Om S.D⁆ ≤
      ⨆ ρ : {ρ : Root // R ≤ hypA S ρ}, Block S.D ρ.1 := by
  have hne : R ≠ ⊥ := by
    rcases hR with h | ⟨e, -, he1, rfl⟩
    · intro hb
      rw [hb, Subgroup.relIndex_bot_left] at h
      have h3 := DLe.card_Tstd S
      have h5 := S.hp5
      rw [h3] at h
      have : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      rw [pow_one] at this
      omega
    · intro hb
      apply he1
      have : e ∈ (⊥ : Subgroup (Vs K E ≃ₗ[K] Vs K E)) := hb ▸ Subgroup.mem_zpowers e
      exact Subgroup.mem_bot.1 this
  exact DLe.stm_of_le_Tstd S hRT hne

end CFSG.RankThree.PartOne.KFR4
