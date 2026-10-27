module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {ℓ f : ℕ} {K : Type} [Field K]

section Data

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

@[expose] noncomputable def unitaryProjData (hn : 1 ≤ n) :
    ProjData K (Fin n) (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) where
  ρ := (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype
  hρ := Subtype.val_injective
  π := QuotientGroup.mk' _
  hπ := QuotientGroup.mk'_surjective _
  hker := by
    intro g
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨c, -, -, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
      simpa using this
    · rintro ⟨c, hc⟩
      obtain ⟨h1, h2⟩ := mem_gramSU.1 g.2
      have hc' : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Matrix.diagonal fun _ => (c : K) := by
        rw [show ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Matrix.scalar (Fin n) (c : K) from hc, scalar_apply]
      refine ⟨c, ?_, ?_, Units.ext (by simpa using hc)⟩
      · rw [hc', Units.val_one, Matrix.mul_one, diagonal_map (map_zero _), diagonal_transpose,
          diagonal_mul_diagonal] at h1
        have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
        simp only [diagonal_apply_eq, Matrix.one_apply_eq] at h3
        rw [UnitaryFieldData.norm, mul_comm]
        exact h3
      · rw [hc', det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
        exact Units.ext (by simpa using h2)

end Data

theorem exists_norm_one_unit_ne_inv {L : Type} [Field L] {e : ℕ} (h₀ : UnitaryFieldData ℓ e L) :
    ∃ u : Lˣ, h₀.norm (u : L) = 1 ∧ u⁻¹ ≠ u := by
  classical
  have := h₀.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hℓ := h₀.prime.two_le
  have he := h₀.one_le
  set q := ℓ ^ e with hq
  have hq2 : 2 ≤ q := by
    calc 2 ≤ ℓ := hℓ
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right (by omega) he
  have hqq : ℓ ^ (2 * e) = q * q := by rw [two_mul, pow_add]
  have hcard : Nat.card Lˣ = q * q - 1 := by rw [Nat.card_units, h₀.card, hqq]
  have hord : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hfac : q * q - 1 = (q - 1) * (q + 1) := by
    zify [show 1 ≤ q * q from by nlinarith, show 1 ≤ q by omega]
    ring
  have hdvd : q - 1 ∣ orderOf g := by rw [hord, hfac]; exact Dvd.intro _ rfl
  have hu : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hfac, Nat.mul_div_cancel_left _ (by omega)]
  refine ⟨g ^ (q - 1), ?_, ?_⟩
  · have h1 : (g ^ (q - 1)) ^ (q + 1) = 1 := by rw [← hu]; exact pow_orderOf_eq_one _
    have h2 : (((g ^ (q - 1)) ^ (q + 1) : Lˣ) : L) = 1 := by rw [h1]; rfl
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
    rw [Units.val_pow_eq_pow_val] at h2
    exact h2
  · intro hinv
    have h1 : (g ^ (q - 1)) ^ 2 = 1 := by
      have : (g ^ (q - 1))⁻¹ * (g ^ (q - 1)) = (g ^ (q - 1)) * (g ^ (q - 1)) := by rw [hinv]
      rw [inv_mul_cancel] at this
      rw [pow_two]
      exact this.symm
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

section Irreducible

variable (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K} (h₀ : UnitaryFieldData ℓ e k)
  (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {n : ℕ}

theorem coe_subfieldSU_diag {d : Fin n → kˣ} (hd : ∀ i, h₀.norm (d i : k) = 1)
    (hdet : ∏ i, (d i : k) = 1) :
    (((subfieldSU h h₀ hbar n ⟨unitaryDiagGL d, unitaryDiagGL_mem_gramSU h₀ hd hdet⟩ :
      gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun i => (((d i : kˣ) : k) : K) := by
  change ((unitaryDiagGL d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map k.subtype = _
  rw [coe_unitaryDiagGL, diagonal_map (map_zero _)]
  rfl

theorem coe_subfieldSU_perm {π : Equiv.Perm (Fin n)} (hπ : Equiv.Perm.sign π = 1) :
    (((subfieldSU h h₀ hbar n ⟨unitaryPermGL π, unitaryPermGL_mem_gramSU h₀ hπ⟩ :
      gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = π.permMatrix K := by
  change ((unitaryPermGL π : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map k.subtype = _
  rw [coe_unitaryPermGL]
  ext a b
  rw [Matrix.map_apply, permMatrix_apply', permMatrix_apply']
  split_ifs <;> simp

theorem unitary_irreducible (hn : 3 ≤ n) (W : Submodule K (Fin n → K))
    (hW : ∀ g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k), ∀ v ∈ W,
      (((subfieldSU h h₀ hbar n g : gramSU h _) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, hu1, hu2⟩ := exists_norm_one_unit_ne_inv h₀
  have hu2' : ((u⁻¹ : kˣ) : K) ≠ (u : K) := fun hh =>
    hu2 (Units.ext (Subtype.ext hh))
  let d : Fin n → Fin n → Fin n → kˣ := fun a b => Pi.mulSingle a u * Pi.mulSingle b u⁻¹
  have hdiag : ∀ a b : Fin n, a ≠ b → ∀ v ∈ W,
      (fun i => (((d a b i : kˣ) : k) : K) * v i) ∈ W := by
    intro a b hab v hv
    obtain ⟨hnorm, hprod⟩ := pairDiag_norm_prod h₀ hu1 a b
    have := hW ⟨unitaryDiagGL (d a b), unitaryDiagGL_mem_gramSU h₀ hnorm hprod⟩ v hv
    rw [coe_subfieldSU_diag h h₀ hbar hnorm hprod] at this
    have e : (Matrix.diagonal fun i => (((d a b i : kˣ) : k) : K)) *ᵥ v =
        fun i => (((d a b i : kˣ) : k) : K) * v i := by
      ext i
      exact mulVec_diagonal _ _ _
    rw [e] at this
    exact this
  have hda : ∀ a b : Fin n, a ≠ b → d a b a = u := by
    intro a b hab
    simp [d, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab]
  have hdb : ∀ a b : Fin n, a ≠ b → d a b b = u⁻¹ := by
    intro a b hab
    simp [d, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab.symm]
  have hcoord : ∃ a : Fin n, (Pi.single a (1 : K) : Fin n → K) ∈ W := by
    let sz : (Fin n → K) → ℕ := fun v => (Finset.univ.filter fun i => v i ≠ 0).card
    have hex : ∃ m, ∃ w ∈ W, w ≠ 0 ∧ sz w = m := by
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      exact ⟨_, w, hw, hw0, rfl⟩
    obtain ⟨w, hwW, hw0, hwsz⟩ := Nat.find_spec hex
    have hmin : ∀ w' ∈ W, w' ≠ 0 → sz w ≤ sz w' := by
      intro w' hw' hw'0
      rw [hwsz]
      exact Nat.find_min' hex ⟨w', hw', hw'0, rfl⟩
    have hone : sz w = 1 := by
      by_contra hne
      have hpos : 0 < sz w := Finset.card_pos.mpr (by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
        exact ⟨i, by simpa using hi⟩)
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < sz w)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hw' := W.sub_mem (hdiag a b hab w hwW) (W.smul_mem (u : K) hwW)
      set w' : Fin n → K := (fun i => (((d a b i : kˣ) : k) : K) * w i) - (u : K) • w with hw'def
      have hw'i : ∀ i, w' i = ((((d a b i : kˣ) : k) : K) - (u : K)) * w i := fun i => by
        simp only [hw'def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hw'a : w' a = 0 := by rw [hw'i, hda a b hab, sub_self, zero_mul]
      have hw'b : w' b ≠ 0 := by
        rw [hw'i, hdb a b hab]
        refine mul_ne_zero (sub_ne_zero.mpr hu2') hb
      have hw'0 : w' ≠ 0 := fun hh => hw'b (by rw [hh]; rfl)
      have hsub : (Finset.univ.filter fun i => w' i ≠ 0) ⊆
          (Finset.univ.filter fun i => w i ≠ 0).erase a := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun hia => hi (hia ▸ hw'a), fun hwi => hi ?_⟩
        rw [hw'i, hwi, mul_zero]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simpa using ha)] at hcard
      have h1 := hmin w' hw' hw'0
      change (Finset.univ.filter fun i => w i ≠ 0).card ≤
        (Finset.univ.filter fun i => w' i ≠ 0).card at h1
      change 0 < (Finset.univ.filter fun i => w i ≠ 0).card at hpos
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
    have hwa : w a ≠ 0 := by
      have : a ∈ Finset.univ.filter fun i => w i ≠ 0 := by
        rw [ha]
        exact Finset.mem_singleton_self a
      simpa using this
    have hwi : ∀ i, i ≠ a → w i = 0 := by
      intro i hia
      by_contra hwi
      have : i ∈ Finset.univ.filter fun i => w i ≠ 0 := by simpa using hwi
      rw [ha] at this
      exact hia (Finset.mem_singleton.mp this)
    refine ⟨a, ?_⟩
    have := W.smul_mem (w a)⁻¹ hwW
    convert this using 1
    ext i
    by_cases hia : i = a
    · subst hia
      simp [inv_mul_cancel₀ hwa]
    · simp [hia, hwi i hia]
  obtain ⟨a, ha⟩ := hcoord
  have hall : ∀ b : Fin n, (Pi.single b (1 : K) : Fin n → K) ∈ W := by
    intro b
    by_cases hab : b = a
    · rw [hab]; exact ha
    · obtain ⟨c, hca, hcb⟩ := exists_fin_ne_ne hn a b
      let σ : Equiv.Perm (Fin n) := Equiv.swap b a * Equiv.swap a c
      have hσ : Equiv.Perm.sign σ = 1 := by
        simp [σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap (Ne.symm hca)]
      have hσb : σ b = a := by
        simp [σ, Equiv.swap_apply_of_ne_of_ne hab hcb.symm]
      have := hW ⟨unitaryPermGL σ, unitaryPermGL_mem_gramSU h₀ hσ⟩ _ ha
      rw [coe_subfieldSU_perm h h₀ hbar hσ, Matrix.permMatrix_mulVec] at this
      convert this using 1
      ext i
      by_cases hib : i = b
      · subst hib
        simp [hσb]
      · have : σ i ≠ a := fun hh => hib (σ.injective (hh.trans hσb.symm))
        simp [hib, this]
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, v i • (Pi.single i (1 : K) : Fin n → K) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact W.sum_mem (fun i _ => W.smul_mem _ (hall i))

end Irreducible

section PairDiag

theorem pairDiag_apply_self {L : Type*} [Group L] {n : ℕ} (u : L) {a b : Fin n} (hab : a ≠ b) :
    (Pi.mulSingle a u * Pi.mulSingle b u⁻¹ : Fin n → L) a = u := by
  simp [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab]

theorem pairDiag_apply_ne {L : Type*} [Group L] {n : ℕ} {u : L} (hu : u⁻¹ ≠ u) {a b i : Fin n}
    (hab : a ≠ b) (hia : i ≠ a) : (Pi.mulSingle a u * Pi.mulSingle b u⁻¹ : Fin n → L) i ≠ u := by
  by_cases hib : i = b
  · subst hib
    simpa [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hia] using hu
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hia, Pi.mulSingle_eq_of_ne hib, mul_one]
    intro h1
    apply hu
    rw [← h1, inv_one]

end PairDiag


section Centralizer

theorem commutator_central_mul_left {G : Type*} [Group G] {z : G} (hz : ∀ g, g * z = z * g)
    (a b : G) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc z * a * b * (a⁻¹ * z⁻¹) * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * z * z⁻¹ * b⁻¹ := by rw [← hz (a * b * a⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_central_mul_right {G : Type*} [Group G] {z : G} (hz : ∀ g, g * z = z * g)
    (a b : G) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc a * (z * b) * a⁻¹ * (b⁻¹ * z⁻¹) = (a * z) * b * a⁻¹ * b⁻¹ * z⁻¹ := by group
    _ = (z * a) * b * a⁻¹ * b⁻¹ * z⁻¹ := by rw [hz a]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [← hz (a * b * a⁻¹ * b⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commute_commutator_of_central {G : Type*} [Group G] (Zc : Subgroup G)
    (hZ : Zc ≤ Subgroup.center G) (x a b : G) (ha : x * a * x⁻¹ * a⁻¹ ∈ Zc)
    (hb : x * b * x⁻¹ * b⁻¹ ∈ Zc) : x * ⁅a, b⁆ = ⁅a, b⁆ * x := by
  have hza : ∀ g, g * (x * a * x⁻¹ * a⁻¹) = (x * a * x⁻¹ * a⁻¹) * g := fun g =>
    Subgroup.mem_center_iff.mp (hZ ha) g
  have hzb : ∀ g, g * (x * b * x⁻¹ * b⁻¹) = (x * b * x⁻¹ * b⁻¹) * g := fun g =>
    Subgroup.mem_center_iff.mp (hZ hb) g
  have h1 : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
    have := map_commutatorElement (MulAut.conj x) a b
    simp only [MulAut.conj_apply] at this
    exact this
  have ea : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
  have eb : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
  have h2 : ⁅x * a * x⁻¹, x * b * x⁻¹⁆ = ⁅a, b⁆ := by
    rw [ea, eb, commutator_central_mul_left hza, commutator_central_mul_right hzb]
  have h3 : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := h1.trans h2
  calc x * ⁅a, b⁆ = (x * ⁅a, b⁆ * x⁻¹) * x := by group
    _ = ⁅a, b⁆ * x := by rw [h3]

variable (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K} (h₀ : UnitaryFieldData ℓ e k)
  (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {n : ℕ}

theorem unitary_centralizer_eq_one (hn : 3 ≤ n) (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2))
    (x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hx : ∀ g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
      x * (QuotientGroup.mk' (normOneScalars h _ n) (subfieldSU h h₀ hbar n g)) =
        (QuotientGroup.mk' (normOneScalars h _ n) (subfieldSU h h₀ hbar n g)) * x) :
    x = 1 := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  have hcm : ∀ g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
      X * subfieldSU h h₀ hbar n g * X⁻¹ * (subfieldSU h h₀ hbar n g)⁻¹ ∈
        normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n := by
    intro g
    rw [← QuotientGroup.eq_one_iff]
    have h1 := hx g
    simp only [QuotientGroup.mk'_apply] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_iff_eq_mul.mpr h1, mul_inv_cancel]
  have hperf := isPerfect_gramSU_one h₀ hn hq₀
  have hS : ∀ g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
      X * subfieldSU h h₀ hbar n g = subfieldSU h h₀ hbar n g * X := by
    intro g
    let S : Subgroup (gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :=
      (Subgroup.centralizer ({X} : Set _)).comap (subfieldSU h h₀ hbar n)
    have hle : commutator (gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ≤ S := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      show subfieldSU h h₀ hbar n ⁅a, b⁆ ∈ Subgroup.centralizer ({X} : Set _)
      rw [map_commutatorElement, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact commute_commutator_of_central _ (normOneScalars_le_center h _ n) y _ _ (hcm a)
        (hcm b)
    exact Subgroup.mem_centralizer_iff.mp (hle (Group.IsPerfect.mem_commutator (g := g))) X rfl
  set M : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hcomm : ∀ g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
      M * (((subfieldSU h h₀ hbar n g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (((subfieldSU h h₀ hbar n g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          M := by
    intro g
    have := congrArg (fun y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =>
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hS g)
    simpa [hM] using this
  obtain ⟨u, hu1, hu2⟩ := exists_norm_one_unit_ne_inv h₀
  have hu2' : ((u⁻¹ : kˣ) : K) ≠ (u : K) := fun hh => hu2 (Units.ext (Subtype.ext hh))
  have hMdiag : ∀ a i : Fin n, i ≠ a → M i a = 0 := by
    intro a i hia
    obtain ⟨b, hba, -⟩ := exists_fin_ne_ne hn a a
    obtain ⟨hnorm, hprod⟩ := pairDiag_norm_prod h₀ hu1 a b
    have hc := hcomm ⟨unitaryDiagGL (Pi.mulSingle a u * Pi.mulSingle b u⁻¹),
      unitaryDiagGL_mem_gramSU h₀ hnorm hprod⟩
    rw [coe_subfieldSU_diag h h₀ hbar hnorm hprod] at hc
    have h1 := congrFun (congrFun hc i) a
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
      pairDiag_apply_self u hba.symm] at h1
    set t : K := (((u : kˣ) : k) : K) with ht
    set Di : K :=
      ((((Pi.mulSingle a u * Pi.mulSingle b u⁻¹ : Fin n → kˣ) i : kˣ) : k) : K) with hDi
    have hne : t - Di ≠ 0 := by
      refine sub_ne_zero.mpr fun hh => pairDiag_apply_ne hu2 hba.symm hia ?_
      exact Units.ext (Subtype.ext hh.symm)
    have h2 : (t - Di) * M i a = 0 := by
      rw [sub_mul]
      linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left hne
  have hMeq : ∀ a b : Fin n, M b b = M a a := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · obtain ⟨c, hca, hcb⟩ := exists_fin_ne_ne hn a b
      let σ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap b c
      have hσ : Equiv.Perm.sign σ = 1 := by
        simp [σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcb.symm]
      have hσa : σ a = b := by
        simp [σ, Equiv.swap_apply_of_ne_of_ne hab hca.symm]
      have hc := hcomm ⟨unitaryPermGL σ, unitaryPermGL_mem_gramSU h₀ hσ⟩
      rw [coe_subfieldSU_perm h h₀ hbar hσ] at hc
      have h1 := congrFun (congrFun hc a) b
      rw [Matrix.mul_apply, Matrix.mul_apply] at h1
      have hL : ∑ j, M a j * (σ.permMatrix K) j b = M a a := by
        rw [Finset.sum_eq_single a]
        · rw [permMatrix_apply', hσa]
          simp
        · intro j _ hj
          rw [hMdiag j a (Ne.symm hj), zero_mul]
        · intro ha
          exact absurd (Finset.mem_univ a) ha
      have hR : ∑ j, (σ.permMatrix K) a j * M j b = M b b := by
        rw [Finset.sum_eq_single b]
        · rw [permMatrix_apply', hσa]
          simp
        · intro j _ hj
          rw [permMatrix_apply', hσa]
          simp [Ne.symm hj]
        · intro hb
          exact absurd (Finset.mem_univ b) hb
      rw [hL, hR] at h1
      exact h1.symm
  let a0 : Fin n := ⟨0, by omega⟩
  have hMscalar : M = Matrix.scalar (Fin n) (M a0 a0) := by
    ext i j
    rw [scalar_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [hMeq a0 i]
    · simp [hij, hMdiag j i hij]
  have hdet : M.det = 1 := (mem_gramSU.1 X.2).2
  have hne : M a0 a0 ≠ 0 := by
    intro h0
    have : Nonempty (Fin n) := ⟨a0⟩
    rw [hMscalar, h0, map_zero, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  exact ((unitaryProjData h n hn1).hker X).mpr ⟨Units.mk0 _ hne, by
    rw [Units.val_mk0]
    exact hMscalar⟩

end Centralizer

@[expose] def UnitaryHeisenbergSystem {ℓ e : ℕ} {k : Type} [Field k]
    (h₀ : UnitaryFieldData ℓ e k) (n : ℕ) : Prop :=
  ∃ (A Z : Subgroup (gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)))
    (ι' : Type) (y : ι' → gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)),
    Finite A ∧ Finite ι' ∧ IsMulCommutative A ∧ IsPGroup ℓ A ∧ Z ≤ A ∧
    Nat.card ι' = ℓ ^ (e * (n - 2)) ∧ (∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z) ∧
    (∃ z ∈ Z, z ∉ normOneScalars h₀
      (gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) n) ∧
    ∀ (s : ℕ), s.Prime → ∀ (F : Type) [Field F] [CharP F s],
      ∀ ξ : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) → F,
        (∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z') → (∀ z ∈ Z, ξ z ≠ 0) →
        (∃ z ∈ Z, ξ z ≠ 1) → ∀ i j, i ≠ j → ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆

end CFSG.SignalizerFunctorTheorem.NonLocal
