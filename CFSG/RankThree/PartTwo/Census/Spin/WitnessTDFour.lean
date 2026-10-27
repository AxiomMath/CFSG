module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDFive

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

theorem five_witness_three {M : Type*} [Group M] {H : Subgroup M} {g₀ g₁ g₂ y₀ y₁ y₂ : M}
    (h5 : g₀ ^ 5 = 1 ∧ g₁ ^ 5 = 1 ∧ g₂ ^ 5 = 1)
    (hD : g₀ ∈ ⁅H, H⁆ ∧ g₁ ∈ ⁅H, H⁆ ∧ g₂ ∈ ⁅H, H⁆)
    (hgg : Commute g₀ g₁ ∧ Commute g₀ g₂ ∧ Commute g₁ g₂)
    (hy : y₀ ∈ ⁅H, H⁆ ∧ y₁ ∈ ⁅H, H⁆ ∧ y₂ ∈ ⁅H, H⁆)
    (hnc : ¬ Commute g₀ y₀ ∧ ¬ Commute g₁ y₁ ∧ ¬ Commute g₂ y₂)
    (hoff : Commute g₁ y₀ ∧ Commute g₂ y₀ ∧ Commute g₀ y₁ ∧ Commute g₂ y₁ ∧ Commute g₀ y₂ ∧
      Commute g₁ y₂)
    (P : Subgroup M) (hPD : P ≤ ⁅H, H⁆) (hP2 : IsPGroup 2 P)
    (hPz : ∃ x ∈ P, ∃ z ∈ ⁅H, H⁆, x * z ≠ z * x)
    (hPn : g₀ ∈ Subgroup.normalizer (P : Set M) ∧ g₁ ∈ Subgroup.normalizer (P : Set M) ∧
      g₂ ∈ Subgroup.normalizer (P : Set M)) :
    HasWitness (DerivedCentralQuotient H) 5 3 := by
  obtain ⟨a5, b5, c5⟩ := h5
  obtain ⟨aD, bD, cD⟩ := hD
  obtain ⟨g01, g02, g12⟩ := hgg
  obtain ⟨ay, by', cy⟩ := hy
  obtain ⟨an, bn, cn⟩ := hnc
  obtain ⟨o10, o20, o01, o21, o02, o12⟩ := hoff
  obtain ⟨aP, bP, cP⟩ := hPn
  let g : Fin 3 → M := ![g₀, g₁, g₂]
  let y : Fin 3 → M := ![y₀, y₁, y₂]
  have hg5 : ∀ a, g a ^ 5 = 1 := by
    intro a
    fin_cases a
    exacts [a5, b5, c5]
  have hnc' : ∀ a, ¬ Commute (g a) (y a) := by
    intro a
    fin_cases a
    exacts [an, bn, cn]
  have hgg' : ∀ a b, a ≠ b → Commute (g a) (g b) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    exacts [absurd rfl hab, g01, g02, g01.symm, absurd rfl hab, g12, g02.symm, g12.symm,
      absurd rfl hab]
  have hoff' : ∀ a b, a ≠ b → Commute (g b) (y a) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    exacts [absurd rfl hab, o10, o20, o01, absurd rfl hab, o21, o02, o12, absurd rfl hab]
  have hPn' : ∀ a, g a ∈ Subgroup.normalizer (P : Set M) := by
    intro a
    fin_cases a
    exacts [aP, bP, cP]
  have hgD : ∀ a, g a ∈ ⁅H, H⁆ := by
    intro a
    fin_cases a
    exacts [aD, bD, cD]
  have hyD : ∀ a, y a ∈ ⁅H, H⁆ := by
    intro a
    fin_cases a
    exacts [ay, by', cy]
  let ϕ : ∀ _ : Fin 3, Multiplicative (ZMod 5) →* M := fun a =>
    { toFun := fun k => g a ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hg5 a)] }
  have hp5 : ∀ (_ : Fin 3) (u : ZMod 5), 5 • u = 0 := fun _ u => by
    rw [nsmul_eq_mul, Nat.cast_ofNat, show (5 : ZMod 5) = 0 from rfl, zero_mul]
  have hcard : Nat.card (Fin 3 → Multiplicative (ZMod 5)) = 5 ^ 3 := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5) ≃ ZMod 5),
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdet : ∀ a u, Commute (ϕ a u) (y a) → u = 1 := fun a u h => by
    have hv := ZMod.val_lt (Multiplicative.toAdd u)
    change Commute (g a ^ (Multiplicative.toAdd u).val) (y a) at h
    have key : ∀ j j' : ℕ, j * j' = 5 * (j * j' / 5) + 1 → Commute (g a ^ j) (y a) → False :=
      fun j j' hjj h' => by
        have h2 := h'.pow_left j'
        rw [← pow_mul, hjj, pow_add, pow_mul, hg5 a, one_pow, one_mul, pow_one] at h2
        exact hnc' a h2
    rcases (show (Multiplicative.toAdd u).val = 0 ∨ (Multiplicative.toAdd u).val = 1 ∨
        (Multiplicative.toAdd u).val = 2 ∨ (Multiplicative.toAdd u).val = 3 ∨
        (Multiplicative.toAdd u).val = 4 by omega) with h0 | h1 | h2 | h3 | h4
    · rw [ZMod.val_eq_zero] at h0
      exact Multiplicative.toAdd.injective h0
    · exact (key 1 1 (by norm_num) (h1 ▸ h)).elim
    · exact (key 2 3 (by norm_num) (h2 ▸ h)).elim
    · exact (key 3 2 (by norm_num) (h3 ▸ h)).elim
    · exact (key 4 4 (by norm_num) (h4 ▸ h)).elim
  exact family_witness_normal (A := fun _ => ZMod 5) ϕ
    (fun a b hab _ _ => (hgg' a b hab).pow_pow _ _)
    (fun a _ => Subgroup.pow_mem _ (hgD a) _) hp5 hcard y hyD hdet
    (fun a b hab _ => (hoff' a b hab).pow_left _) P hPD hP2 hPz
    (fun a _ => Subgroup.pow_mem _ (hPn' a) _)

theorem mem_normalizer_closure_of_commute {G : Type*} [Group G] {S : Set G} {g : G}
    (h : ∀ s ∈ S, Commute g s) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ x ∈ Subgroup.closure S, Commute g x := fun x hx => by
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact h s hs
    | one => exact Commute.one_right g
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [(key x hx).eq, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := (key _ hx).eq
    rw [show g * x * g⁻¹ * g = g * x by group] at h1
    have e : g * x * g⁻¹ = x := mul_left_cancel h1
    rwa [e] at hx

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (R : RootData K N ι) in
@[expose] def rootElts (L : Subfield K) {m : ℕ} (X : Fin m → Matrix N N K) : Set R.G :=
  {x | ∃ k, ∃ u ∈ L, R.mat x = 1 + u • X k}

variable {R : RootData K N ι}

theorem closure_rootElts_le {D : Subgroup R.G} {L : Subfield K} {m : ℕ}
    {X : Fin m → Matrix N N K} (hX : ∀ k, R.RootOpIn D L (X k)) :
    Subgroup.closure (R.rootElts L X) ≤ D := by
  rw [Subgroup.closure_le]
  rintro x ⟨k, u, hu, hx⟩
  obtain ⟨g, hgD, hg⟩ := (hX k).memD u hu
  rw [R.mat_injective (hx.trans hg.symm)]
  exact hgD

theorem commute_of_smul {g g' : R.G} {X Y : Matrix N N K} {u v : K}
    (hg : R.mat g = 1 + u • X) (hg' : R.mat g' = 1 + v • Y) (h : Commute X Y) : Commute g g' :=
  R.commute_of_mat (by rw [hg, hg']; exact commute_one_add_smul h u v)

variable (hchar : (2 : K) = 0)
include hchar

theorem sl2_five {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {X Y : Matrix N N K} (hp : SqZeroPair X Y)
    (hne : X ≠ 0) {gx gy : R.G} (hgx : R.mat gx = 1 + X) (hgy : R.mat gy = 1 + ω • Y) :
    (gx * gy) ^ 5 = 1 ∧ ¬ Commute (gx * gy) gx := by
  have hφx : R.mat gx = SqZeroPair.φ X Y 1 1 0 1 := by rw [hgx, SqZeroPair.φ_upper, one_smul]
  have hφy : R.mat gy = SqZeroPair.φ X Y 1 0 ω 1 := by rw [hgy, SqZeroPair.φ_lower]
  have hφg : R.mat (gx * gy) = SqZeroPair.φ X Y (1 + ω) 1 ω 1 := by
    rw [mat_mul, hφx, hφy, hp.φ_mul]
    congr 1 <;> ring
  constructor
  · apply R.mat_injective
    have e2 : SqZeroPair.φ X Y (1 + ω) 1 ω 1 * SqZeroPair.φ X Y (1 + ω) 1 ω 1 =
        SqZeroPair.φ X Y 0 ω (ω + 1) (ω + 1) := by
      rw [hp.φ_mul]
      congr 1
      · linear_combination hω + ω * hchar
      · linear_combination hchar
      · linear_combination hω - hchar
      · ring
    have e4 : SqZeroPair.φ X Y 0 ω (ω + 1) (ω + 1) * SqZeroPair.φ X Y 0 ω (ω + 1) (ω + 1) =
        SqZeroPair.φ X Y 1 1 ω (ω + 1) := by
      rw [hp.φ_mul]
      congr 1
      · linear_combination hω - hchar
      · linear_combination hω - hchar
      · linear_combination hω
      · linear_combination (ω ^ 2 + ω) * hchar
    have e5 : SqZeroPair.φ X Y 1 1 ω (ω + 1) * SqZeroPair.φ X Y (1 + ω) 1 ω 1 =
        SqZeroPair.φ X Y 1 0 0 1 := by
      rw [hp.φ_mul]
      congr 1
      · linear_combination ω * hchar
      · linear_combination hchar
      · linear_combination (ω + ω ^ 2) * hchar
      · linear_combination ω * hchar
    rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, pow_two, pow_two, mat_mul,
      mat_mul, mat_mul, hφg, e2, e4, e5, SqZeroPair.φ_one_zero_zero_one, mat_one]
  · intro h
    have hm : R.mat (gx * gy) * R.mat gx = R.mat gx * R.mat (gx * gy) := by
      rw [← mat_mul, ← mat_mul]
      exact congrArg R.mat h.eq
    rw [hφg, hφx, hp.φ_mul, hp.φ_mul] at hm
    have h4 := (SqZeroPair.φ_injective hp hne hm).2.2.2
    have hω0 : ω = 0 := by linear_combination h4
    rw [hω0] at hω
    norm_num at hω

theorem conj_mem_closure_smul {L : Subfield K} {S : Set R.G} {g p : R.G} {Z X : Matrix N N K}
    {v u : K} (hv : v ∈ L) (hu : u ∈ L) (hg : R.mat g = 1 + v • Z) (hp : R.mat p = 1 + u • X)
    (hZ : Z * Z = 0) (hZXZ : Z * X * Z = 0) (hpS : p ∈ S)
    (h : Z * X - X * Z = 0 ∨ ∃ X' : Matrix N N K, (∀ w ∈ L, ∃ p' ∈ S, R.mat p' = 1 + w • X') ∧
      X * X' = 0 ∧ (Z * X - X * Z = X' ∨ Z * X - X * Z = -X')) :
    g * p * g⁻¹ ∈ Subgroup.closure S := by
  have hZ' : (v • Z) * (v • Z) = 0 := by rw [smul_mul_smul_comm, hZ, smul_zero]
  have hZXZ' : (v • Z) * (u • X) * (v • Z) = 0 := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hZXZ, smul_zero]
  have hm := mat_conj_one_add hg hp hZ' hZXZ'
  have hbr : v • Z * (u • X) - u • X * (v • Z) = (v * u) • (Z * X - X * Z) := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm u v, smul_sub]
  rw [hbr] at hm
  rcases h with h0 | ⟨X', hX'S, hXX', hW⟩
  · have e : g * p * g⁻¹ = p := R.mat_injective (by rw [hm, h0, smul_zero, add_zero, hp])
    rw [e]
    exact Subgroup.subset_closure hpS
  · have hneg : -X' = X' := by
      ext a b
      rw [Matrix.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, hchar, zero_mul]
    have hW' : Z * X - X * Z = X' := by rcases hW with hW | hW <;> rw [hW]; exact hneg
    obtain ⟨p', hp'S, hp'⟩ := hX'S (v * u) (L.mul_mem hv hu)
    have e2 : (1 + u • X) * (1 + (v * u) • X') = 1 + u • X + (v * u) • X' := by
      rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hXX', smul_zero, add_zero]
      abel
    have e : g * p * g⁻¹ = p * p' := R.mat_injective (by rw [hm, hW', mat_mul, hp, hp', e2])
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hpS) (Subgroup.subset_closure hp'S)

theorem isPGroup_closure_rootElts {L : Subfield K} {m : ℕ} {X : Fin m → Matrix N N K}
    (hXX : ∀ k k', X k * X k' = 0) : IsPGroup 2 (Subgroup.closure (R.rootElts L X)) := by
  have e2 : ∀ A B : Matrix N N K, A * B = 0 → (1 + A) * (1 + B) = 1 + A + B := fun A B h => by
    rw [show (1 + A) * (1 + B) = 1 + A + B + A * B by noncomm_ring, h, add_zero]
  have hsm : ∀ (k k' : Fin m) (u u' : K), (u • X k) * (u' • X k') = 0 := fun k k' u u' => by
    rw [smul_mul_smul_comm, hXX, smul_zero]
  have hcommS : ∀ x ∈ R.rootElts L X, ∀ y ∈ R.rootElts L X, x * y = y * x := by
    rintro x ⟨k, u, -, hx⟩ y ⟨k', u', -, hy⟩
    apply R.mat_injective
    rw [mat_mul, mat_mul, hx, hy, e2 _ _ (hsm k k' u u'), e2 _ _ (hsm k' k u' u)]
    abel
  have hc1 : ∀ x ∈ Subgroup.closure (R.rootElts L X), ∀ s ∈ R.rootElts L X, x * s = s * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact fun s hs => hcommS t ht s hs
    | one => exact fun s _ => by rw [one_mul, mul_one]
    | mul a b _ _ iha ihb =>
      exact fun s hs => (Commute.mul_left (iha s hs : Commute a s) (ihb s hs)).eq
    | inv a _ iha => exact fun s hs => (Commute.inv_left (iha s hs : Commute a s)).eq
  have hc2 : ∀ x ∈ Subgroup.closure (R.rootElts L X), ∀ y ∈ Subgroup.closure (R.rootElts L X),
      x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact hc1 x hx t ht
    | one => rw [one_mul, mul_one]
    | mul a b _ _ iha ihb => exact (Commute.mul_right (iha : Commute x a) ihb).eq
    | inv a _ iha => exact (Commute.inv_right (iha : Commute x a)).eq
  have hsq : ∀ x ∈ Subgroup.closure (R.rootElts L X), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨k, u, -, hs⟩ := hs
      exact mul_self_of_mat hchar hs (hsm k k u u)
    | one => rw [one_mul]
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * a * (b * b) := by rw [← hc2 a ha b hb]; group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a _ iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  exact fun x => ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, pow_two]; exact hsq x.1 x.2)⟩

end RootData

namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

section Block

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K]

theorem normalizer_of_cl_smul (hchar : (2 : K) = 0) {D : Subgroup (rootData n hn K).G}
    {L : Subfield K} {m : ℕ} {M : Fin m → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    {pc : Fin m → Cl n} (hM : ∀ k, IsIntOp n (pc k) (M k))
    (hMR : ∀ k, (rootData n hn K).RootOpIn D L (intMap K (M k)))
    (hpp : ∀ k k', pc k * pc k' = 0) {g : (rootData n hn K).G} {zc : Cl n}
    {MZ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (hZ : IsIntOp n zc MZ) {v : K}
    (hv : v ∈ L) (hg : (rootData n hn K).mat g = 1 + v • intMap K MZ) (hzz : zc * zc = 0)
    (hout : ∀ k, zc * pc k * zc = 0 ∧ (zc * pc k - pc k * zc = 0 ∨
      ∃ k', zc * pc k - pc k * zc = pc k' ∨ zc * pc k - pc k * zc = -pc k')) :
    g ∈ Subgroup.normalizer (Subgroup.closure ((rootData n hn K).rootElts L
      fun k => intMap K (M k)) : Set (rootData n hn K).G) := by
  have hZZ : intMap K MZ * intMap K MZ = 0 := by
    rw [← intMap_mul, (hZ.mul hZ).eq_zero hzz, intMap_zero]
  have hZZ' : (v • intMap K MZ) * (v • intMap K MZ) = 0 := by
    rw [smul_mul_smul_comm, hZZ, smul_zero]
  refine mem_normalizer_closure (mul_self_of_mat hchar hg hZZ') ?_
  rintro s ⟨k, u, hu, hs⟩
  obtain ⟨hsw, ho⟩ := hout k
  have hZXZ : intMap K MZ * intMap K (M k) * intMap K MZ = 0 := by
    rw [intMap_eq_of hZ (hM k) IsIntOp.zero hsw, intMap_zero]
  have hXX : ∀ k', intMap K (M k) * intMap K (M k') = 0 := fun k' => by
    rw [← intMap_mul, ((hM k).mul (hM k')).eq_zero (hpp k k'), intMap_zero]
  have hgen : ∀ k', ∀ w ∈ L, ∃ p' ∈ (rootData n hn K).rootElts L (fun k => intMap K (M k)),
      (rootData n hn K).mat p' = 1 + w • intMap K (M k') := fun k' w hw => by
    obtain ⟨p', hp'⟩ := (hMR k').mem w
    exact ⟨p', ⟨k', w, hw, hp'⟩, hp'⟩
  refine conj_mem_closure_smul hchar hv hu hg hs hZZ hZXZ ⟨k, u, hu, hs⟩ ?_
  rcases ho with h0 | ⟨k', h1 | h1⟩
  · left
    rw [intMap_bracket_D hZ (hM k) IsIntOp.zero h0, intMap_zero]
  · exact Or.inr ⟨intMap K (M k'), hgen k', hXX k',
      Or.inl (intMap_bracket_D hZ (hM k) (hM k') h1 K)⟩
  · refine Or.inr ⟨intMap K (M k'), hgen k', hXX k', Or.inr ?_⟩
    rw [intMap_bracket_D hZ (hM k) (hM k').neg h1, intMap_neg']

variable (n) in
noncomputable abbrev blockCl (a c0 c1 : Fin n) : Fin 4 → Cl n := fun k =>
  crD n a * ![anD n c1, anD n c0, crD n c1, crD n c0] k

variable {a c0 c1 : Fin n} (n01 : c0 ≠ c1) (na0 : a ≠ c0) (na1 : a ≠ c1)
include n01 na0 na1

omit n01 in
theorem blockCl_mul (k k' : Fin 4) : blockCl n a c0 c1 k * blockCl n a c0 c1 k' = 0 := by
  have hvk : ∀ k, ![anD n c1, anD n c0, crD n c1, crD n c0] k * crD n a =
      -(crD n a * ![anD n c1, anD n c0, crD n c1, crD n c0] k) := by
    intro k
    fin_cases k
    · exact an_cr (polarizationBasis n) na1
    · exact an_cr (polarizationBasis n) na0
    · exact cr_cr (polarizationBasis n) c1 a
    · exact cr_cr (polarizationBasis n) c0 a
  exact crm_mul_crm (hvk k)

omit na0 in
theorem block_houtE : ∀ k, crD n c0 * anD n c1 * blockCl n a c0 c1 k * (crD n c0 * anD n c1) = 0 ∧
    (crD n c0 * anD n c1 * blockCl n a c0 c1 k - blockCl n a c0 c1 k * (crD n c0 * anD n c1) = 0 ∨
      ∃ k', crD n c0 * anD n c1 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (crD n c0 * anD n c1) = blockCl n a c0 c1 k' ∨
        crD n c0 * anD n c1 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (crD n c0 * anD n c1) = -blockCl n a c0 c1 k') := by
  set b := polarizationBasis n
  have hzE : Commute (crD n c0 * anD n c1) (crD n a) :=
    (show Commute (crD n a) (crD n c0 * anD n c1) from
      commute_mul_of_anticomm₂ (cr_cr b a c0) (cr_an b na1)).symm
  intro k
  fin_cases k
  · exact ⟨sandwich_crm hzE (sandwich_right (an_sq b c1) (cr_an b n01) (an_an b c1 c1)),
      Or.inl ((bracket_crm hzE).trans ((congrArg (crD n a * ·)
        (bracket_anti (cr_an b n01) (an_an b c1 c1))).trans (mul_zero _)))⟩
  · exact ⟨sandwich_crm hzE (sandwich_right (an_sq b c1) (cr_an b n01) (an_an b c1 c0)),
      Or.inr ⟨0, Or.inr ((bracket_crm hzE).trans ((congrArg (crD n a * ·)
        (bracket_dual_left (an_an b c1 c0) (cr_an_self b c0))).trans (mul_neg _ _)))⟩⟩
  · exact ⟨sandwich_crm hzE (sandwich_left (cr_sq b c0) (cr_an b n01) (cr_cr b c0 c1)),
      Or.inr ⟨3, Or.inl ((bracket_crm hzE).trans (congrArg (crD n a * ·)
        (bracket_dual_right (cr_cr b c0 c1) (an_cr_self b c1))))⟩⟩
  · exact ⟨sandwich_crm hzE (sandwich_left (cr_sq b c0) (cr_an b n01) (cr_cr b c0 c0)),
      Or.inl ((bracket_crm hzE).trans ((congrArg (crD n a * ·)
        (bracket_anti (cr_cr b c0 c0) (an_cr b n01))).trans (mul_zero _)))⟩

omit na1 in
theorem block_houtF : ∀ k, crD n c1 * anD n c0 * blockCl n a c0 c1 k * (crD n c1 * anD n c0) = 0 ∧
    (crD n c1 * anD n c0 * blockCl n a c0 c1 k - blockCl n a c0 c1 k * (crD n c1 * anD n c0) = 0 ∨
      ∃ k', crD n c1 * anD n c0 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (crD n c1 * anD n c0) = blockCl n a c0 c1 k' ∨
        crD n c1 * anD n c0 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (crD n c1 * anD n c0) = -blockCl n a c0 c1 k') := by
  set b := polarizationBasis n
  have n10 : c1 ≠ c0 := n01.symm
  have hzF : Commute (crD n c1 * anD n c0) (crD n a) :=
    (show Commute (crD n a) (crD n c1 * anD n c0) from
      commute_mul_of_anticomm₂ (cr_cr b a c1) (cr_an b na0)).symm
  intro k
  fin_cases k
  · exact ⟨sandwich_crm hzF (sandwich_right (an_sq b c0) (cr_an b n10) (an_an b c0 c1)),
      Or.inr ⟨1, Or.inr ((bracket_crm hzF).trans ((congrArg (crD n a * ·)
        (bracket_dual_left (an_an b c0 c1) (cr_an_self b c1))).trans (mul_neg _ _)))⟩⟩
  · exact ⟨sandwich_crm hzF (sandwich_right (an_sq b c0) (cr_an b n10) (an_an b c0 c0)),
      Or.inl ((bracket_crm hzF).trans ((congrArg (crD n a * ·)
        (bracket_anti (cr_an b n10) (an_an b c0 c0))).trans (mul_zero _)))⟩
  · exact ⟨sandwich_crm hzF (sandwich_left (cr_sq b c1) (cr_an b n10) (cr_cr b c1 c1)),
      Or.inl ((bracket_crm hzF).trans ((congrArg (crD n a * ·)
        (bracket_anti (cr_cr b c1 c1) (an_cr b n10))).trans (mul_zero _)))⟩
  · exact ⟨sandwich_crm hzF (sandwich_left (cr_sq b c1) (cr_an b n10) (cr_cr b c1 c0)),
      Or.inr ⟨2, Or.inl ((bracket_crm hzF).trans (congrArg (crD n a * ·)
        (bracket_dual_right (cr_cr b c1 c0) (an_cr_self b c0))))⟩⟩

omit na0 na1 in
theorem block_houtT : ∀ k, crD n c0 * crD n c1 * blockCl n a c0 c1 k * (crD n c0 * crD n c1) = 0 ∧
    (crD n c0 * crD n c1 * blockCl n a c0 c1 k - blockCl n a c0 c1 k * (crD n c0 * crD n c1) = 0 ∨
      ∃ k', crD n c0 * crD n c1 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (crD n c0 * crD n c1) = blockCl n a c0 c1 k' ∨
        crD n c0 * crD n c1 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (crD n c0 * crD n c1) = -blockCl n a c0 c1 k') := by
  set b := polarizationBasis n
  have n10 : c1 ≠ c0 := n01.symm
  have hzT : Commute (crD n c0 * crD n c1) (crD n a) :=
    (show Commute (crD n a) (crD n c0 * crD n c1) from
      commute_mul_of_anticomm₂ (cr_cr b a c0) (cr_cr b a c1)).symm
  intro k
  fin_cases k
  · exact ⟨sandwich_crm hzT (sandwich_left (cr_sq b c0) (cr_cr b c0 c1) (cr_an b n01)),
      Or.inr ⟨3, Or.inl ((bracket_crm hzT).trans (congrArg (crD n a * ·)
        (bracket_dual_right (cr_an b n01) (cr_an_self b c1))))⟩⟩
  · exact ⟨sandwich_crm hzT (sandwich_right (cr_sq b c1) (cr_cr b c0 c1) (cr_an b n10)),
      Or.inr ⟨2, Or.inr ((bracket_crm hzT).trans ((congrArg (crD n a * ·)
        (bracket_dual_left (cr_an b n10) (cr_an_self b c0))).trans (mul_neg _ _)))⟩⟩
  · exact ⟨sandwich_crm hzT (sandwich_left (cr_sq b c0) (cr_cr b c0 c1) (cr_cr b c0 c1)),
      Or.inl ((bracket_crm hzT).trans ((congrArg (crD n a * ·)
        (bracket_anti (cr_cr b c0 c1) (cr_cr b c1 c1))).trans (mul_zero _)))⟩
  · exact ⟨sandwich_crm hzT (sandwich_left (cr_sq b c0) (cr_cr b c0 c1) (cr_cr b c0 c0)),
      Or.inl ((bracket_crm hzT).trans ((congrArg (crD n a * ·)
        (bracket_anti (cr_cr b c0 c0) (cr_cr b c1 c0))).trans (mul_zero _)))⟩

theorem block_houtT' : ∀ k, anD n c1 * anD n c0 * blockCl n a c0 c1 k * (anD n c1 * anD n c0) = 0 ∧
    (anD n c1 * anD n c0 * blockCl n a c0 c1 k - blockCl n a c0 c1 k * (anD n c1 * anD n c0) = 0 ∨
      ∃ k', anD n c1 * anD n c0 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (anD n c1 * anD n c0) = blockCl n a c0 c1 k' ∨
        anD n c1 * anD n c0 * blockCl n a c0 c1 k -
          blockCl n a c0 c1 k * (anD n c1 * anD n c0) = -blockCl n a c0 c1 k') := by
  set b := polarizationBasis n
  have n10 : c1 ≠ c0 := n01.symm
  have hzT' : Commute (anD n c1 * anD n c0) (crD n a) :=
    (show Commute (crD n a) (anD n c1 * anD n c0) from
      commute_mul_of_anticomm₂ (cr_an b na1) (cr_an b na0)).symm
  intro k
  fin_cases k
  · exact ⟨sandwich_crm hzT' (sandwich_left (an_sq b c1) (an_an b c1 c0) (an_an b c1 c1)),
      Or.inl ((bracket_crm hzT').trans ((congrArg (crD n a * ·)
        (bracket_anti (an_an b c1 c1) (an_an b c0 c1))).trans (mul_zero _)))⟩
  · exact ⟨sandwich_crm hzT' (sandwich_left (an_sq b c1) (an_an b c1 c0) (an_an b c1 c0)),
      Or.inl ((bracket_crm hzT').trans ((congrArg (crD n a * ·)
        (bracket_anti (an_an b c1 c0) (an_an b c0 c0))).trans (mul_zero _)))⟩
  · exact ⟨sandwich_crm hzT' (sandwich_right (an_sq b c0) (an_an b c1 c0) (an_cr b n10)),
      Or.inr ⟨1, Or.inr ((bracket_crm hzT').trans ((congrArg (crD n a * ·)
        (bracket_dual_left (an_cr b n10) (an_cr_self b c1))).trans (mul_neg _ _)))⟩⟩
  · exact ⟨sandwich_crm hzT' (sandwich_left (an_sq b c1) (an_an b c1 c0) (an_cr b n01)),
      Or.inr ⟨0, Or.inl ((bracket_crm hzT').trans (congrArg (crD n a * ·)
        (bracket_dual_right (an_cr b n01) (an_cr_self b c0))))⟩⟩

end Block

end CarrierD

namespace CarrierTD

open TauCeti TauCeti.TypeDSpinCarrier CarrierD Cliff RootData
open scoped commutatorElement

section Four

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K} {π : Equiv.Perm (Fin n)}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem twTorus_pow_five {ζ : Kˣ} (hζ5 : ζ ^ 5 = 1) :
    (rootData n hn K).torus (twTorus σ ζ) ^ 5 = 1 := by
  have hs : twTorus σ ζ ^ 5 = (1 : Fin n → Kˣ) := by
    funext j
    simp only [Pi.pow_apply, Pi.one_apply, twTorus]
    split_ifs
    · exact hζ5
    · rw [← map_pow, hζ5, map_one]
    · exact one_pow 5
  rw [← map_pow, hs, map_one]

theorem commute_twTorus_smul {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {z : Cl n}
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (hz : IsIntOp n z M) (a : ℤ)
    (hA : crD n (forkA n hn) * anD n (forkA n hn) * z -
      z * (crD n (forkA n hn) * anD n (forkA n hn)) = (a : ℚ) • z)
    (hB : crD n (forkB n hn) * anD n (forkB n hn) * z -
      z * (crD n (forkB n hn) * anD n (forkB n hn)) = 0)
    {g : (rootData n hn K).G} {u : K} (hg : (rootData n hn K).mat g = 1 + u • intMap K M) :
    Commute ((rootData n hn K).torus (twTorus σ c)) g := by
  have h1 := torus_mul_of_weight hn hz (twTorus σ c) (fun _ => a)
    (fun j hj => hcl_fork_bracket hn a hA hB (twTorus_ne_one hj))
  have hprod : (∏ j : Fin n, twTorus σ c j ^ a : Kˣ) = 1 := by
    rw [Finset.prod_zpow, twTorus_eq_mulSingle (hn := hn)]
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', hc, one_zpow]
  simp only [hprod, Units.val_one, one_smul] at h1
  have h2 : Commute ((rootData n hn K).mat ((rootData n hn K).torus (twTorus σ c)))
      (intMap K M) := h1
  apply (rootData n hn K).commute_of_mat
  rw [hg]
  exact (Commute.one_right _).add_right (h2.smul_right u)

theorem commute_twTorus_block {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {c0 c1 : Fin n}
    (h0A : c0 ≠ forkA n hn) (h0B : c0 ≠ forkB n hn) (h1A : c1 ≠ forkA n hn)
    (h1B : c1 ≠ forkB n hn) {M : Fin 4 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hM : ∀ k, IsIntOp n (blockCl n (forkA n hn) c0 c1 k) (M k)) (L : Subfield K) :
    ∀ s ∈ (rootData n hn K).rootElts L (fun k => intMap K (M k)),
      Commute ((rootData n hn K).torus (twTorus σ c)) s := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  rintro s ⟨k, u, -, hs⟩
  refine commute_twTorus_smul hc (hM k) 1 ?_ ?_ hs
  · fin_cases k
    · refine (bracket_mul_of (num_cr_self (b := polarizationBasis n) (forkA n hn))
        (num_an_ne (b := polarizationBasis n) h1A.symm)).trans ?_
      rw [mul_zero, add_zero, Int.cast_one, one_smul]
      rfl
    · refine (bracket_mul_of (num_cr_self (b := polarizationBasis n) (forkA n hn))
        (num_an_ne (b := polarizationBasis n) h0A.symm)).trans ?_
      rw [mul_zero, add_zero, Int.cast_one, one_smul]
      rfl
    · refine (bracket_mul_of (num_cr_self (b := polarizationBasis n) (forkA n hn))
        (num_cr_ne (b := polarizationBasis n) h1A.symm)).trans ?_
      rw [mul_zero, add_zero, Int.cast_one, one_smul]
      rfl
    · refine (bracket_mul_of (num_cr_self (b := polarizationBasis n) (forkA n hn))
        (num_cr_ne (b := polarizationBasis n) h0A.symm)).trans ?_
      rw [mul_zero, add_zero, Int.cast_one, one_smul]
      rfl
  · fin_cases k
    · refine (bracket_mul_of (num_cr_ne (b := polarizationBasis n) hAB.symm)
        (num_an_ne (b := polarizationBasis n) h1B.symm)).trans ?_
      rw [zero_mul, mul_zero, add_zero]
    · refine (bracket_mul_of (num_cr_ne (b := polarizationBasis n) hAB.symm)
        (num_an_ne (b := polarizationBasis n) h0B.symm)).trans ?_
      rw [zero_mul, mul_zero, add_zero]
    · refine (bracket_mul_of (num_cr_ne (b := polarizationBasis n) hAB.symm)
        (num_cr_ne (b := polarizationBasis n) h1B.symm)).trans ?_
      rw [zero_mul, mul_zero, add_zero]
    · refine (bracket_mul_of (num_cr_ne (b := polarizationBasis n) hAB.symm)
        (num_cr_ne (b := polarizationBasis n) h0B.symm)).trans ?_
      rw [zero_mul, mul_zero, add_zero]

theorem tdfour_ops (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) :
    (∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n ⟨n - 4, by omega⟩ * crD n ⟨n - 3, by omega⟩) M ∧
      IsIntOp n (anD n ⟨n - 3, by omega⟩ * anD n ⟨n - 4, by omega⟩) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N)) ∧
    ∃ M : Fin 4 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      (∀ k, IsIntOp n (blockCl n (forkA n hn) ⟨n - 4, by omega⟩ ⟨n - 3, by omega⟩ k) (M k)) ∧
      ∀ k, (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
        (RootData.fixedField σ) (intMap K (M k)) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  set A := forkA n hn with hAd
  set c0 : Fin n := ⟨n - 4, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 3, by omega⟩ with hc1
  have h0v : c0.val = n - 4 := rfl
  have h1v : c1.val = n - 3 := rfl
  have n01 : c0 ≠ c1 := fin_ne (by omega)
  have n0A : c0 ≠ A := fin_ne (by omega)
  have n1A : c1 ≠ A := fin_ne (by omega)
  have h01 : c0.val + 1 = c1.val := by omega
  have h1A : c1.val + 1 = A.val := by omega
  have hDj : ∀ j : Fin n, j.val < n - 2 → ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu j * g * (nu j)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j hj g hg =>
    conj_mem_commutator (nu_mem_fixed hF (hπ j hj)) g hg
  have base := exists_pairOp_fork hF hπ hπA hπB hc
  have m1 := chainWeyl_pair_first (b := polarizationBasis n) n01 n0A.symm n1A.symm
  have q1 := pairOps_move h01 (hDj c0 (by omega)) m1.1 m1.2 base
  have m2 := chainWeyl_pair_second (b := polarizationBasis n) n1A n01 n0A
  have q2 := pairOps_move h1A (hDj c1 (by omega)) m2.1 m2.2 q1
  refine ⟨q2, ?_⟩
  obtain ⟨MP, -, hMP, -, hMPR, -⟩ := base
  obtain ⟨M02, -, hM02, -, hM02R, -⟩ := q1
  have hM0 := isIntOp_chainF hn (j := c1) (k := A) h1A
  have hM0R : (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (rootIntMatrix n hn (.inr c1))) :=
    RootOpIn.of_y (R := rootData n hn K) c1 fun u hu =>
      (fixed_mem_commutator hF hπ hc c1 (by omega) hu).2
  have hw1 : chainWeyl (polarizationBasis n) c0 c1 * (crD n A * anD n c1) =
      crD n A * anD n c0 * chainWeyl (polarizationBasis n) c0 c1 := by
    have hcw := (commute_cr_weyls (b := polarizationBasis n) (i := c0) (k := c1) n0A.symm
      n1A.symm).1
    rw [← mul_assoc, ← hcw.eq, mul_assoc, chainWeyl_mul_an n01, ← mul_assoc]
  obtain ⟨hM1, hM1R⟩ := rootOpIn_conj (isIntOp_chainE hn (j := c0) (k := c1) h01)
    (isIntOp_chainF hn (j := c0) (k := c1) h01) (chain_E_sq n01) (chain_F_sq n01) hM0 hw1
    (hDj c0 (by omega)) hM0R
  have hM2 : IsIntOp n (crD n A * crD n c1) (-MP) :=
    hMP.neg.congr (by rw [cr_cr (polarizationBasis n) c1 A, neg_neg])
  have hM2R : (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (-MP)) := by
    rw [intMap_neg']
    exact hMPR.neg
  have hM3 : IsIntOp n (crD n A * crD n c0) (-M02) :=
    hM02.neg.congr (by rw [cr_cr (polarizationBasis n) c0 A, neg_neg])
  have hM3R : (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (-M02)) := by
    rw [intMap_neg']
    exact hM02R.neg
  refine ⟨![rootIntMatrix n hn (.inr c1), wlMat hn c0 * rootIntMatrix n hn (.inr c1) * wlInv hn c0,
    -MP, -M02], ?_, ?_⟩
  · intro k
    fin_cases k
    exacts [hM0, hM1, hM2, hM3]
  · intro k
    fin_cases k
    exacts [hM0R, hM1R, hM2R, hM3R]

theorem tdfour_commute {ω : K} {gθ gθ' : (rootData n hn K).G}
    {Mθ Nθ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hMθ : IsIntOp n (crD n ⟨n - 4, by omega⟩ * crD n ⟨n - 3, by omega⟩) Mθ)
    (hNθ : IsIntOp n (anD n ⟨n - 3, by omega⟩ * anD n ⟨n - 4, by omega⟩) Nθ)
    (hgθ : (rootData n hn K).mat gθ = 1 + (1 : K) • intMap K Mθ)
    (hgθ' : (rootData n hn K).mat gθ' = 1 + ω • intMap K Nθ) :
    Commute ((rootData n hn K).x ⟨n - 4, by omega⟩ 1 * (rootData n hn K).y ⟨n - 4, by omega⟩ ω)
      (gθ * gθ') ∧
    Commute (gθ * gθ') ((rootData n hn K).x ⟨n - 4, by omega⟩ 1) ∧
    Commute ((rootData n hn K).x ⟨n - 4, by omega⟩ 1 * (rootData n hn K).y ⟨n - 4, by omega⟩ ω)
      gθ ∧
    Commute ((rootData n hn K).x ⟨n - 4, by omega⟩ 1 * (rootData n hn K).y ⟨n - 4, by omega⟩ ω)
      ((rootData n hn K).pairX σ (forkA n hn) (forkB n hn) 1) ∧
    Commute (gθ * gθ') ((rootData n hn K).pairX σ (forkA n hn) (forkB n hn) 1) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  set A := forkA n hn with hAd
  set B := forkB n hn with hBd
  set c0 : Fin n := ⟨n - 4, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 3, by omega⟩ with hc1
  have h0v : c0.val = n - 4 := rfl
  have h1v : c1.val = n - 3 := rfl
  have n01 : c0 ≠ c1 := fin_ne (by omega)
  have n0A : c0 ≠ A := fin_ne (by omega)
  have n0B : c0 ≠ B := fin_ne (by omega)
  have n1A : c1 ≠ A := fin_ne (by omega)
  have n1B : c1 ≠ B := fin_ne (by omega)
  have hE0 := isIntOp_chainE hn (j := c0) (k := c1) (by omega)
  have hF0 := isIntOp_chainF hn (j := c0) (k := c1) (by omega)
  have hmx0 : (rootData n hn K).mat ((rootData n hn K).x c0 1) =
      1 + (1 : K) • intMap K (rootIntMatrix n hn (.inl c0)) := mat_x' c0 1
  have hmy0 : (rootData n hn K).mat ((rootData n hn K).y c0 ω) =
      1 + ω • intMap K (rootIntMatrix n hn (.inr c0)) := mat_y' c0 ω
  obtain ⟨d1, d2, d3, d4⟩ := block_commute (n := n) n01
  have k1 := commute_of_smul hmx0 hgθ (intMap_commute_of hE0 hMθ d1.eq)
  have k2 := commute_of_smul hmx0 hgθ' (intMap_commute_of hE0 hNθ d2.eq)
  have k3 := commute_of_smul hmy0 hgθ (intMap_commute_of hF0 hMθ d3.symm.eq)
  have k4 := commute_of_smul hmy0 hgθ' (intMap_commute_of hF0 hNθ d4.eq)
  have hcA : (rootData n hn K).CM A c0 = 0 := (CM_fork_of_far (j := c0) (by omega)).1
  have hcB : (rootData n hn K).CM B c0 = 0 := (CM_fork_of_far (j := c0) (by omega)).2
  have p1 := ((rootData n hn K).commute_x_x hcA 1 1).symm
  have p2 := ((rootData n hn K).commute_x_x hcB (σ 1) 1).symm
  have p3 := ((rootData n hn K).commute_x_y n0A.symm 1 ω).symm
  have p4 := ((rootData n hn K).commute_x_y n0B.symm (σ 1) ω).symm
  have hEA := isIntOp_chainE hn (j := A) (k := B) (by omega)
  have hEB := isIntOp_forkE hn
  have hmxA : (rootData n hn K).mat ((rootData n hn K).x A 1) =
      1 + (1 : K) • intMap K (rootIntMatrix n hn (.inl A)) := mat_x' A 1
  have hmxB : (rootData n hn K).mat ((rootData n hn K).x B (σ 1)) =
      1 + (1 : K) • intMap K (rootIntMatrix n hn (.inl B)) := by
    rw [map_one]
    exact mat_x' B 1
  have p5 := commute_of_smul hgθ hmxA
    (intMap_commute_of hMθ hEA (commute_gens true true true false n0A n0B n1A n1B).eq)
  have p6 := commute_of_smul hgθ hmxB
    (intMap_commute_of hMθ hEB (commute_gens true true true true n0A n0B n1A n1B).eq)
  have p7 := commute_of_smul hgθ' hmxA
    (intMap_commute_of hNθ hEA (commute_gens false false true false n1A n1B n0A n0B).eq)
  have p8 := commute_of_smul hgθ' hmxB
    (intMap_commute_of hNθ hEB (commute_gens false false true true n1A n1B n0A n0B).eq)
  exact ⟨(k1.mul_right k2).mul_left (k3.mul_right k4), k1.symm.mul_left k2.symm,
    k1.mul_left k3, (p1.mul_right p2).mul_left (p3.mul_right p4),
    (p5.mul_right p6).mul_left (p7.mul_right p8)⟩

theorem tdfour_torus {ζ : Kˣ} (hζN : ζ * Units.map (σ : K →* K) ζ = 1) {ω : K}
    {gθ gθ' : (rootData n hn K).G} {Mθ Nθ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hMθ : IsIntOp n (crD n ⟨n - 4, by omega⟩ * crD n ⟨n - 3, by omega⟩) Mθ)
    (hNθ : IsIntOp n (anD n ⟨n - 3, by omega⟩ * anD n ⟨n - 4, by omega⟩) Nθ)
    (hgθ : (rootData n hn K).mat gθ = 1 + (1 : K) • intMap K Mθ)
    (hgθ' : (rootData n hn K).mat gθ' = 1 + ω • intMap K Nθ) :
    Commute ((rootData n hn K).torus (twTorus σ ζ))
      ((rootData n hn K).x ⟨n - 4, by omega⟩ 1 * (rootData n hn K).y ⟨n - 4, by omega⟩ ω) ∧
    Commute ((rootData n hn K).torus (twTorus σ ζ)) ((rootData n hn K).x ⟨n - 4, by omega⟩ 1) ∧
    Commute ((rootData n hn K).torus (twTorus σ ζ)) (gθ * gθ') ∧
    Commute ((rootData n hn K).torus (twTorus σ ζ)) gθ := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  set A := forkA n hn with hAd
  set B := forkB n hn with hBd
  set c0 : Fin n := ⟨n - 4, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 3, by omega⟩ with hc1
  have h0v : c0.val = n - 4 := rfl
  have h1v : c1.val = n - 3 := rfl
  have n0A : c0 ≠ A := fin_ne (by omega)
  have n0B : c0 ≠ B := fin_ne (by omega)
  have n1A : c1 ≠ A := fin_ne (by omega)
  have n1B : c1 ≠ B := fin_ne (by omega)
  have hfar := CM_fork_of_far (hn := hn) (K := K) (j := c0) (by omega)
  have tx0 := (commute_twTorus_xy (hn := hn) hζN (Or.inl hfar) (1 : K)).1
  have ty0 := (commute_twTorus_xy (hn := hn) hζN (Or.inl hfar) ω).2
  have tθ := commute_twTorus_smul hζN hMθ 0
    (by rw [bracket_mul_of (num_cr_ne (b := polarizationBasis n) n0A.symm)
      (num_cr_ne (b := polarizationBasis n) n1A.symm), zero_mul, mul_zero, add_zero,
      Int.cast_zero, zero_smul])
    (by rw [bracket_mul_of (num_cr_ne (b := polarizationBasis n) n0B.symm)
      (num_cr_ne (b := polarizationBasis n) n1B.symm), zero_mul, mul_zero, add_zero]) hgθ
  have tθ' := commute_twTorus_smul hζN hNθ 0
    (by rw [bracket_mul_of (num_an_ne (b := polarizationBasis n) n1A.symm)
      (num_an_ne (b := polarizationBasis n) n0A.symm), zero_mul, mul_zero, add_zero,
      Int.cast_zero, zero_smul])
    (by rw [bracket_mul_of (num_an_ne (b := polarizationBasis n) n1B.symm)
      (num_an_ne (b := polarizationBasis n) n0B.symm), zero_mul, mul_zero, add_zero]) hgθ'
  exact ⟨tx0.mul_right ty0, tx0, tθ.mul_right tθ', tθ⟩

theorem tdfour_normal (hchar : (2 : K) = 0) {D : Subgroup (rootData n hn K).G} {L : Subfield K}
    {ω : K} (hωL : ω ∈ L) {M : Fin 4 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hM : ∀ k, IsIntOp n (blockCl n (forkA n hn) ⟨n - 4, by omega⟩ ⟨n - 3, by omega⟩ k) (M k))
    (hMR : ∀ k, (rootData n hn K).RootOpIn D L (intMap K (M k)))
    {gθ gθ' : (rootData n hn K).G} {Mθ Nθ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hMθ : IsIntOp n (crD n ⟨n - 4, by omega⟩ * crD n ⟨n - 3, by omega⟩) Mθ)
    (hNθ : IsIntOp n (anD n ⟨n - 3, by omega⟩ * anD n ⟨n - 4, by omega⟩) Nθ)
    (hgθ : (rootData n hn K).mat gθ = 1 + (1 : K) • intMap K Mθ)
    (hgθ' : (rootData n hn K).mat gθ' = 1 + ω • intMap K Nθ) :
    (rootData n hn K).x ⟨n - 4, by omega⟩ 1 * (rootData n hn K).y ⟨n - 4, by omega⟩ ω ∈
      Subgroup.normalizer (Subgroup.closure ((rootData n hn K).rootElts L
        fun k => intMap K (M k)) : Set (rootData n hn K).G) ∧
    gθ * gθ' ∈ Subgroup.normalizer (Subgroup.closure ((rootData n hn K).rootElts L
        fun k => intMap K (M k)) : Set (rootData n hn K).G) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  set A := forkA n hn with hAd
  set c0 : Fin n := ⟨n - 4, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 3, by omega⟩ with hc1
  have h0v : c0.val = n - 4 := rfl
  have h1v : c1.val = n - 3 := rfl
  have n01 : c0 ≠ c1 := fin_ne (by omega)
  have nA0 : A ≠ c0 := fin_ne (by omega)
  have nA1 : A ≠ c1 := fin_ne (by omega)
  have hpp := blockCl_mul (a := A) (c0 := c0) (c1 := c1) nA0 nA1
  have hmx0 : (rootData n hn K).mat ((rootData n hn K).x c0 1) =
      1 + (1 : K) • intMap K (rootIntMatrix n hn (.inl c0)) := mat_x' c0 1
  have hmy0 : (rootData n hn K).mat ((rootData n hn K).y c0 ω) =
      1 + ω • intMap K (rootIntMatrix n hn (.inr c0)) := mat_y' c0 ω
  have h1 := normalizer_of_cl_smul hchar hM hMR hpp (isIntOp_chainE hn (j := c0) (k := c1)
    (by omega)) L.one_mem hmx0 (chain_E_sq n01) (block_houtE n01 nA1)
  have h2 := normalizer_of_cl_smul hchar hM hMR hpp (isIntOp_chainF hn (j := c0) (k := c1)
    (by omega)) hωL hmy0 (chain_F_sq n01) (block_houtF n01 nA0)
  have h3 := normalizer_of_cl_smul hchar hM hMR hpp hMθ L.one_mem hgθ pair_E_sq
    (block_houtT (a := A) n01)
  have h4 := normalizer_of_cl_smul hchar hM hMR hpp hNθ hωL hgθ' pair_F_sq
    (block_houtT' n01 nA0 nA1)
  exact ⟨Subgroup.mul_mem _ h1 h2, Subgroup.mul_mem _ h3 h4⟩

theorem hasWitness_tdfour_gen (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) {ω : K} (hωσ : σ ω = ω)
    (hω : ω ^ 2 + ω + 1 = 0) {ζ : Kˣ} (hζσ : σ (σ ζ) = ζ) (hζ2 : (ζ : K) ^ 2 ≠ 1)
    (hζ5 : ζ ^ 5 = 1) (hζN : ζ * Units.map (σ : K →* K) ζ = 1) (hchar : (2 : K) = 0) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 5 3 := by
  obtain ⟨⟨Mθ, Nθ, hMθ, hNθ, hMθR, hNθR⟩, ⟨M, hM, hMR⟩⟩ := tdfour_ops hF hπ hπA hπB hc
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have h1L : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have hωL : ω ∈ RootData.fixedField σ := hωσ
  have hx0 := (fixed_mem_commutator hF hπ hc ⟨n - 4, by omega⟩ (by simp only; omega)
    (map_one σ)).1
  have hy0 := (fixed_mem_commutator hF hπ hc ⟨n - 4, by omega⟩ (by simp only; omega) hωσ).2
  obtain ⟨gθ, hgθD, hgθ⟩ := hMθR.memD 1 h1L
  obtain ⟨gθ', hgθ'D, hgθ'⟩ := hNθR.memD ω hωL
  have hgθ1 : (rootData n hn K).mat gθ = 1 + intMap K Mθ := by rw [hgθ, one_smul]
  have l01 : (⟨n - 4, by omega⟩ : Fin n) < ⟨n - 3, by omega⟩ := by
    rw [Fin.lt_def]
    simp only
    omega
  obtain ⟨g0_5, g0_nc⟩ := sl2_five hchar hω ((rootData n hn K).sqZero ⟨n - 4, by omega⟩)
    ((rootData n hn K).E_ne_zero _) (mat_x_one hn _) (mat_y' _ ω)
  obtain ⟨g1_5, g1_nc⟩ := sl2_five hchar hω
    (pair_sqZeroPair (ne_of_lt l01) hMθ hNθ hMθR.sq hNθR.sq) (pair_ne_zero l01 hMθ) hgθ1 hgθ'
  have hpp := blockCl_mul (a := forkA n hn) (c0 := ⟨n - 4, by omega⟩) (c1 := ⟨n - 3, by omega⟩)
    (fin_ne (by simp only; omega)) (fin_ne (by simp only; omega))
  have hXX : ∀ k k', intMap K (M k) * intMap K (M k') = 0 := fun k k' => by
    rw [← intMap_mul, ((hM k).mul (hM k')).eq_zero (hpp k k'), intMap_zero]
  have hPz : ∃ x ∈ Subgroup.closure ((rootData n hn K).rootElts (RootData.fixedField σ)
      fun k => intMap K (M k)), ∃ z ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, x * z ≠ z * x := by
    obtain ⟨p0, hp0⟩ := (hMR 0).mem 1
    have hM0 : M 0 = rootIntMatrix n hn (.inr ⟨n - 3, by omega⟩) :=
      (hM 0).eq (isIntOp_chainF hn (j := ⟨n - 3, by omega⟩) (k := forkA n hn)
        (by simp only; omega))
    have hp0' : (rootData n hn K).mat p0 =
        1 + intMap K (rootIntMatrix n hn (.inr ⟨n - 3, by omega⟩)) := by
      rw [hp0, one_smul, hM0]
    refine ⟨p0, Subgroup.subset_closure ⟨0, 1, h1L, hp0⟩,
      (rootData n hn K).x ⟨n - 3, by omega⟩ 1,
      (fixed_mem_commutator hF hπ hc ⟨n - 3, by omega⟩ (by simp only; omega) (map_one σ)).1,
      fun h => (one_ne_zero : (1 : K) ≠ 0) ?_⟩
    exact (rootData n hn K).eq_zero_of_commute_sqZeroPair
      ((rootData n hn K).sqZero ⟨n - 3, by omega⟩) ((rootData n hn K).E_ne_zero _)
      (mat_x' (R := rootData n hn K) ⟨n - 3, by omega⟩ 1) hp0' h.symm
  obtain ⟨n1, n2⟩ := tdfour_normal hchar hωL hM hMR hMθ hNθ hgθ hgθ'
  obtain ⟨cm1, cm2, cm3, cm4, cm5⟩ := tdfour_commute (σ := σ) hMθ hNθ hgθ hgθ'
  obtain ⟨ct1, ct2, ct3, ct4⟩ := tdfour_torus hζN hMθ hNθ hgθ hgθ'
  exact five_witness_three ⟨g0_5, g1_5, twTorus_pow_five hζ5⟩
    ⟨Subgroup.mul_mem _ hx0 hy0, Subgroup.mul_mem _ hgθD hgθ'D,
      twTorus_mem_commutator hF hπ hπA hπB hζσ hζ2 hζσ⟩
    ⟨cm1, ct1.symm, ct3.symm⟩
    ⟨hx0, hgθD, pairX_mem_commutator_sq hF hπ hπA hπB hζσ hζ2 (u := 1)
      (by rw [map_one, map_one])⟩
    ⟨g0_nc, g1_nc, not_commute_twTorus_pairX hζ2⟩ ⟨cm2, ct2, cm3, ct4, cm4, cm5⟩
    _ (closure_rootElts_le hMR) (isPGroup_closure_rootElts hchar hXX) hPz
    ⟨n1, n2, mem_normalizer_closure_of_commute (commute_twTorus_block hζN
      (fin_ne (by simp only; omega)) (fin_ne (by simp only; omega)) (fin_ne (by simp only; omega))
      (fin_ne (by simp only; omega)) hM _)⟩

end Four

variable (d : TypeTwistedDLieIndex)

theorem hasWitness_tdfour (h2 : d.1.characteristic = 2) (hf : d.1.fieldExponent = 2) :
    HasWitness d.Group 5 3 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := CarrierD.exists_unit_order_seven d.1 h2
  have hq : d.1.fieldOrder = 4 := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, h2, hf]
    norm_num
  have hσ : ∀ u : d.1.Closure, frob d u = u ^ 4 := fun u => by rw [frob_apply, hq]
  have : Finite (RootData.fixedField (frob d)) := Nat.finite_of_card_ne_zero (by
    rw [card_fixedField_frob]
    exact pow_ne_zero _ d.1.characteristic_prime.ne_zero)
  obtain ⟨μ, hμL, hμ2⟩ := exists_unit_sq_ne_one (RootData.fixedField (frob d)) (by
    rw [card_fixedField_frob, h2, hf]
    norm_num)
  have hμσ : frob d μ = μ := hμL
  have hμ4 : (μ : d.1.Closure) ^ 4 = μ := by rw [← hσ]; exact hμσ
  have hμ0 : (μ : d.1.Closure) ≠ 0 := μ.ne_zero
  have hμ3 : (μ : d.1.Closure) ^ 3 = 1 := by
    have h3 : (μ : d.1.Closure) * ((μ : d.1.Closure) ^ 3 - 1) = 0 := by
      linear_combination hμ4
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hμ0)
  have hμ1 : (μ : d.1.Closure) - 1 ≠ 0 := fun h => hμ2 (by rw [sub_eq_zero.mp h, one_pow])
  have hω : (μ : d.1.Closure) ^ 2 + μ + 1 = 0 := by
    have h3 : ((μ : d.1.Closure) - 1) * ((μ : d.1.Closure) ^ 2 + μ + 1) = 0 := by
      linear_combination hμ3
    exact (mul_eq_zero.mp h3).resolve_left hμ1
  have : Finite (fixedField2 d) := Nat.finite_of_card_ne_zero (by
    rw [card_fixedField2]
    exact pow_ne_zero _ d.1.characteristic_prime.ne_zero)
  obtain ⟨ζ, hζL, hζo⟩ := exists_unit_orderOf (fixedField2 d) (s := 5) (by
    rw [card_fixedField2, h2, hf]
    norm_num)
  have hζσ : frob d (frob d ζ) = ζ := hζL
  have hζ5 : ζ ^ 5 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζ5' : (ζ : d.1.Closure) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ5, Units.val_one]
  have hζ2 : (ζ : d.1.Closure) ^ 2 ≠ 1 := fun h => by
    have h1 : ζ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := Nat.le_of_dvd (by norm_num) (hζo ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  have hζN : ζ * Units.map (frob d : d.1.Closure →* d.1.Closure) ζ = 1 := Units.ext (by
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_one]
    rw [hσ]
    linear_combination hζ5')
  exact hasWitness_tdfour_gen (isTwistedFrobenius d) (fun i hi => perm_of_lt d hi)
    (perm_forkA d) (perm_forkB d) hc hμσ hω hζσ hζ2 hζ5 hζN hchar

end CarrierTD

end CFSG.RankThree.PartTwo.Census.Spin
