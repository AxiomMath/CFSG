module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDPair

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

theorem family_witness_normal {M : Type*} [Group M] {H : Subgroup M} {p k : ℕ}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {A : κ → Type*} [∀ a, AddCommGroup (A a)]
    (ϕ : ∀ a, Multiplicative (A a) →* M)
    (hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v))
    (hD : ∀ a u, ϕ a u ∈ ⁅H, H⁆) (hp : ∀ a (u : A a), p • u = 0)
    (hcard : Nat.card (∀ a, Multiplicative (A a)) = p ^ k)
    (y : κ → M) (hy : ∀ a, y a ∈ ⁅H, H⁆) (hdet : ∀ a u, Commute (ϕ a u) (y a) → u = 1)
    (hoff : ∀ a b, a ≠ b → ∀ u, Commute (ϕ b u) (y a))
    (P : Subgroup M) (hPD : P ≤ ⁅H, H⁆) (hP2 : IsPGroup 2 P)
    (hPz : ∃ x ∈ P, ∃ z ∈ ⁅H, H⁆, x * z ≠ z * x)
    (hPn : ∀ a u, ϕ a u ∈ Subgroup.normalizer (P : Set M)) :
    HasWitness (DerivedCentralQuotient H) p k := by
  set θ := MonoidHom.noncommPiCoprod ϕ hcomm
  have hdetect : ∀ e, (∀ a, Commute (θ e) (y a)) → e = 1 := by
    intro e he
    funext a
    have hsplit : e = Pi.mulSingle (M := fun i => Multiplicative (A i)) a (e a) *
        Function.update e a 1 := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [hb]
    have hrest : Commute (θ (Function.update e a 1)) (y a) := by
      rw [← Finset.univ_prod_mulSingle (Function.update e a 1)]
      have hmul : ∀ z z', Commute (θ z) (y a) → Commute (θ z') (y a) →
          Commute (θ (z * z')) (y a) := fun z z' hz hz' => by
        rw [map_mul]
        exact hz.mul_left hz'
      have hone : Commute (θ 1) (y a) := by
        rw [map_one]
        exact Commute.one_left _
      refine Finset.prod_induction _ (fun z => Commute (θ z) (y a)) hmul hone fun b _ => ?_
      rw [MonoidHom.noncommPiCoprod_mulSingle]
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, map_one]
        exact Commute.one_left _
      · exact hoff a b (Ne.symm hb) _
    have h1 := he a
    rw [hsplit, map_mul, MonoidHom.noncommPiCoprod_mulSingle] at h1
    have h3 : Commute (ϕ a (e a)) (y a) := by
      have e1 := h1.eq
      have e2 := hrest.eq
      refine mul_right_cancel (b := θ (Function.update e a 1)) ?_
      rw [mul_assoc, ← e2, ← mul_assoc, e1, mul_assoc]
    exact hdet a _ h3
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    exact (Subgroup.mem_bot).mpr (hdetect e fun a => by rw [he]; exact Commute.one_left _)
  have hN : θ.range ≤ Subgroup.normalizer (P : Set M) := by
    rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun a => ?_
    rintro _ ⟨u, rfl⟩
    exact hPn a u
  refine exists_quotient_witness (E := θ.range) (P := P) ⟨⟨fun a b => ?_⟩⟩ ?_ ?_ ?_ hPD hP2 ?_
    hPz ?_
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : M) * (b : M) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := by
      funext a
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (e a)) = Multiplicative.ofAdd 0
      rw [hp]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, hcard]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun a => ?_
    rintro _ ⟨u, rfl⟩
    exact hD a u
  · rintro _ ⟨e, rfl⟩ hz
    rw [hdetect e fun a => hz _ (hy a), map_one]
  · intro e he x hx
    exact (Subgroup.mem_normalizer_iff.mp (hN he) x).mp hx

theorem mem_normalizer_closure {G : Type*} [Group G] {S : Set G} {g : G} (hg : g * g = 1)
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have key : ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ Subgroup.closure S := fun x hx => by
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact h s hs
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key x, fun hx => ?_⟩
  have e : x = g * (g * x * g⁻¹) * g⁻¹ := by
    rw [hgi]
    calc x = g * g * x * (g * g) := by rw [hg, one_mul, mul_one]
      _ = g * (g * x * g) * g := by group
  rw [e]
  exact key _ hx

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {R : RootData K N ι}

variable (hchar : (2 : K) = 0)
include hchar

theorem three_witness_pairs_normal {F : R.G →* R.G} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X Y : κ → Matrix N N K} (hp : ∀ a, SqZeroPair (X a) (Y a)) (hne : ∀ a, X a ≠ 0)
    (gx gy : κ → R.G) (hgx : ∀ a, R.mat (gx a) = 1 + X a) (hgy : ∀ a, R.mat (gy a) = 1 + Y a)
    (hxD : ∀ a, gx a ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hyD : ∀ a, gy a ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hXX : ∀ a b, a ≠ b → Commute (X a) (X b)) (hXY : ∀ a b, a ≠ b → Commute (X a) (Y b))
    (hYY : ∀ a b, a ≠ b → Commute (Y a) (Y b)) (P : Subgroup R.G)
    (hPD : P ≤ ⁅fixedSubgroup F, fixedSubgroup F⁆) (hP2 : IsPGroup 2 P)
    (hPz : ∃ x ∈ P, ∃ z ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, x * z ≠ z * x)
    (hPx : ∀ a, gx a ∈ Subgroup.normalizer (P : Set R.G))
    (hPy : ∀ a, gy a ∈ Subgroup.normalizer (P : Set R.G)) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 (Fintype.card κ) := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact hchar
  let g : κ → R.G := fun a => gx a * gy a
  have hφx : ∀ a, R.mat (gx a) = SqZeroPair.φ (X a) (Y a) 1 1 0 1 := fun a => by
    rw [hgx, SqZeroPair.φ_upper, one_smul]
  have hφy : ∀ a, R.mat (gy a) = SqZeroPair.φ (X a) (Y a) 1 0 1 1 := fun a => by
    rw [hgy, SqZeroPair.φ_lower, one_smul]
  have hφg : ∀ a, R.mat (g a) = SqZeroPair.φ (X a) (Y a) 0 1 1 1 := fun a => by
    show R.mat (gx a * gy a) = _
    rw [mat_mul, hφx, hφy, (hp a).φ_mul]
    simp only [mul_one, mul_zero, zero_add]
    rw [h11]
  have hg3 : ∀ a, g a ^ 3 = 1 := fun a => by
    apply R.mat_injective
    have e2 : SqZeroPair.φ (X a) (Y a) 0 1 1 1 * SqZeroPair.φ (X a) (Y a) 0 1 1 1 =
        SqZeroPair.φ (X a) (Y a) 1 1 1 0 := by
      rw [(hp a).φ_mul]
      simp only [mul_one, mul_zero, zero_add]
      rw [h11]
    have e3 : SqZeroPair.φ (X a) (Y a) 1 1 1 0 * SqZeroPair.φ (X a) (Y a) 0 1 1 1 =
        SqZeroPair.φ (X a) (Y a) 1 0 0 1 := by
      rw [(hp a).φ_mul]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      rw [h11]
    rw [pow_succ, pow_two, mat_mul, mat_mul, hφg, e2, e3, SqZeroPair.φ_one_zero_zero_one,
      mat_one]
  have hnc : ∀ a, ¬ Commute (g a) (gx a) := fun a h => by
    have hm : R.mat (g a) * R.mat (gx a) = R.mat (gx a) * R.mat (g a) := by
      rw [← mat_mul, ← mat_mul]
      exact congrArg R.mat h.eq
    rw [hφg, hφx, (hp a).φ_mul, (hp a).φ_mul] at hm
    simp only [mul_one, mul_zero, add_zero, zero_add] at hm
    rw [h11] at hm
    exact zero_ne_one (SqZeroPair.φ_injective (hp a) (hne a) hm).1
  let ϕ : ∀ _ : κ, Multiplicative (ZMod 3) →* R.G := fun a =>
    { toFun := fun k => g a ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hg3 a)] }
  have cxx : ∀ a b, a ≠ b → Commute (gx a) (gx b) := fun a b hab =>
    R.commute_of_mat (by
      rw [hgx, hgx, ← one_smul K (X a), ← one_smul K (X b)]
      exact commute_one_add_smul (hXX a b hab) 1 1)
  have cxy : ∀ a b, a ≠ b → Commute (gx a) (gy b) := fun a b hab =>
    R.commute_of_mat (by
      rw [hgx, hgy, ← one_smul K (X a), ← one_smul K (Y b)]
      exact commute_one_add_smul (hXY a b hab) 1 1)
  have cyy : ∀ a b, a ≠ b → Commute (gy a) (gy b) := fun a b hab =>
    R.commute_of_mat (by
      rw [hgy, hgy, ← one_smul K (Y a), ← one_smul K (Y b)]
      exact commute_one_add_smul (hYY a b hab) 1 1)
  have hgg : ∀ a b, a ≠ b → Commute (g a) (g b) := fun a b hab =>
    ((cxx a b hab).mul_right (cxy a b hab)).mul_left
      ((cxy b a (Ne.symm hab)).symm.mul_right (cyy a b hab))
  have hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v) := fun a b hab u v =>
    (hgg a b hab).pow_pow _ _
  have hD : ∀ a u, ϕ a u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun a u =>
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (hxD a) (hyD a)) _
  have hp3 : ∀ (a : κ) (u : ZMod 3), 3 • u = 0 := fun a u => by
    rw [nsmul_eq_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 from rfl, zero_mul]
  have hcard : Nat.card (κ → Multiplicative (ZMod 3)) = 3 ^ Fintype.card κ := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.card_zmod, Nat.card_eq_fintype_card]
  have hdet : ∀ a u, Commute (ϕ a u) (gx a) → u = 1 := fun a u h => by
    have hv := ZMod.val_lt (Multiplicative.toAdd u)
    change Commute (g a ^ (Multiplicative.toAdd u).val) (gx a) at h
    rcases (show (Multiplicative.toAdd u).val = 0 ∨ (Multiplicative.toAdd u).val = 1 ∨
        (Multiplicative.toAdd u).val = 2 by omega) with h0 | h1 | h2
    · rw [ZMod.val_eq_zero] at h0
      exact Multiplicative.toAdd.injective h0
    · rw [h1, pow_one] at h
      exact absurd h (hnc a)
    · rw [h2] at h
      have h4 := h.pow_left 2
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hg3 a, one_mul, pow_one] at h4
      exact absurd h4 (hnc a)
  have hoff : ∀ a b, a ≠ b → ∀ u, Commute (ϕ b u) (gx a) := fun a b hab u =>
    ((cxx b a (Ne.symm hab)).mul_left (cxy a b hab).symm).pow_left _
  have hPn : ∀ a u, ϕ a u ∈ Subgroup.normalizer (P : Set R.G) := fun a u =>
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (hPx a) (hPy a)) _
  exact family_witness_normal ϕ hcomm hD hp3 hcard gx hxD hdet hoff P hPD hP2 hPz hPn

omit hchar in
theorem mat_conj_one_add {g h : R.G} {Z X : Matrix N N K} (hg : R.mat g = 1 + Z)
    (hh : R.mat h = 1 + X) (hZ : Z * Z = 0) (hZXZ : Z * X * Z = 0) :
    R.mat (g * h * g⁻¹) = 1 + X + (Z * X - X * Z) := by
  have hgi : R.mat g⁻¹ = 1 - Z := R.mat_inv_of_mul (by
    rw [hg, add_mul, one_mul, mul_sub, mul_one, hZ, sub_zero, sub_add_cancel])
  rw [mat_mul, mat_mul, hg, hh, hgi]
  calc (1 + Z) * (1 + X) * (1 - Z) = 1 + X + (Z * X - X * Z) - Z * Z - Z * X * Z := by
        noncomm_ring
    _ = 1 + X + (Z * X - X * Z) := by rw [hZ, hZXZ, sub_zero, sub_zero]

theorem conj_mem_closure_step {S : Set R.G} {g p : R.G} {Z X : Matrix N N K}
    (hg : R.mat g = 1 + Z) (hp : R.mat p = 1 + X) (hZ : Z * Z = 0) (hZXZ : Z * X * Z = 0)
    (hpS : p ∈ S)
    (h : Z * X - X * Z = 0 ∨ ∃ p' ∈ S, ∃ X', R.mat p' = 1 + X' ∧ X * X' = 0 ∧
      (Z * X - X * Z = X' ∨ Z * X - X * Z = -X')) :
    g * p * g⁻¹ ∈ Subgroup.closure S := by
  have hm := mat_conj_one_add hg hp hZ hZXZ
  rcases h with h0 | ⟨p', hp'S, X', hp', hXX', hW⟩
  · have e : g * p * g⁻¹ = p := R.mat_injective (by rw [hm, h0, add_zero, hp])
    rw [e]
    exact Subgroup.subset_closure hpS
  · have hneg : -X' = X' := by
      ext a b
      rw [Matrix.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, hchar, zero_mul]
    have hW' : Z * X - X * Z = X' := by rcases hW with hW | hW <;> rw [hW]; exact hneg
    have e : g * p * g⁻¹ = p * p' := R.mat_injective (by
      rw [hm, hW', mat_mul, hp, hp', mul_add, mul_one, add_mul, one_mul, hXX', add_zero,
        add_assoc])
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hpS) (Subgroup.subset_closure hp'S)

theorem mul_self_of_mat {g : R.G} {Z : Matrix N N K} (hg : R.mat g = 1 + Z) (hZ : Z * Z = 0) :
    g * g = 1 := by
  apply R.mat_injective
  have hZZ : Z + Z = 0 := by
    ext a b
    rw [Matrix.add_apply, Matrix.zero_apply, ← two_mul, hchar, zero_mul]
  rw [mat_mul, hg, mat_one, mul_add, mul_one, add_mul, one_mul, hZ, add_zero, add_assoc, hZZ,
    add_zero]

end RootData

namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

section Blocks

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K]
  {F : (rootData n hn K).G →* (rootData n hn K).G} {L : Subfield K}

theorem three_witness_blocks_normal (hchar : (2 : K) = 0) {β : Type*} [Fintype β] [DecidableEq β]
    (i j : β → Fin n) (hij : ∀ b, (i b).val + 1 = (j b).val)
    (hdisj : ∀ b b', b ≠ b' → i b ≠ i b' ∧ i b ≠ j b' ∧ j b ≠ i b' ∧ j b ≠ j b')
    (hD : ∀ b, (rootData n hn K).x (i b) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n hn K).y (i b) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (MP NP : β → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ)
    (hMP : ∀ b, IsIntOp n (crD n (i b) * crD n (j b)) (MP b))
    (hNP : ∀ b, IsIntOp n (anD n (j b) * anD n (i b)) (NP b))
    (hMPR : ∀ b, (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ L
      (intMap K (MP b)))
    (hNPR : ∀ b, (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ L
      (intMap K (NP b)))
    (P : Subgroup (rootData n hn K).G) (hPD : P ≤ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hP2 : IsPGroup 2 P) (hPz : ∃ x ∈ P, ∃ z ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, x * z ≠ z * x)
    (hPn : ∀ (b : β) (g : (rootData n hn K).G),
      ((rootData n hn K).mat g = 1 + intMap K (rootIntMatrix n hn (.inl (i b))) ∨
        (rootData n hn K).mat g = 1 + intMap K (rootIntMatrix n hn (.inr (i b))) ∨
        (rootData n hn K).mat g = 1 + intMap K (MP b) ∨
        (rootData n hn K).mat g = 1 + intMap K (NP b)) →
      g ∈ Subgroup.normalizer (P : Set (rootData n hn K).G)) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 (Fintype.card β * 2) := by
  have hne : ∀ b, i b ≠ j b := fun b => fin_ne (by have := hij b; omega)
  have hlt : ∀ b, i b < j b := fun b => by rw [Fin.lt_def]; have := hij b; omega
  choose gP hgPD hgP using fun b => (hMPR b).memD 1 L.one_mem
  choose gN hgND hgN using fun b => (hNPR b).memD 1 L.one_mem
  let MX : β × Fin 2 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    fun p => ![rootIntMatrix n hn (.inl (i p.1)), MP p.1] p.2
  let MY : β × Fin 2 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    fun p => ![rootIntMatrix n hn (.inr (i p.1)), NP p.1] p.2
  let sX : Fin 2 → Bool := ![false, true]
  let sY : Fin 2 → Bool := ![true, false]
  let cX : β × Fin 2 → Cl n := fun p =>
    gen (polarizationBasis n) true (i p.1) * gen (polarizationBasis n) (sX p.2) (j p.1)
  let cY : β × Fin 2 → Cl n := fun p =>
    gen (polarizationBasis n) (sY p.2) (j p.1) * gen (polarizationBasis n) false (i p.1)
  let gx : β × Fin 2 → (rootData n hn K).G := fun p => ![(rootData n hn K).x (i p.1) 1, gP p.1] p.2
  let gy : β × Fin 2 → (rootData n hn K).G := fun p => ![(rootData n hn K).y (i p.1) 1, gN p.1] p.2
  have hMX : ∀ p, IsIntOp n (cX p) (MX p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact isIntOp_chainE hn (hij b)
    · exact hMP b
  have hMY : ∀ p, IsIntOp n (cY p) (MY p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact isIntOp_chainF hn (hij b)
    · exact hNP b
  have hgx : ∀ p, (rootData n hn K).mat (gx p) = 1 + (1 : K) • intMap K (MX p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact mat_x' _ _
    · exact hgP b
  have hgy : ∀ p, (rootData n hn K).mat (gy p) = 1 + (1 : K) • intMap K (MY p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact mat_y' _ _
    · exact hgN b
  have hpair : ∀ p, SqZeroPair (intMap K (MX p)) (intMap K (MY p)) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact (rootData n hn K).sqZero (i b)
    · exact pair_sqZeroPair (hne b) (hMP b) (hNP b) (hMPR b).sq (hNPR b).sq
  have hX0 : ∀ p, intMap K (MX p) ≠ 0 := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact (rootData n hn K).E_ne_zero (i b)
    · exact pair_ne_zero (hlt b) (hMP b)
  have hXX : ∀ p p', p ≠ p' → Commute (cX p) (cX p') := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ hpp
    by_cases hbb : b = b'
    · subst hbb
      have hc := block_commute (hne b)
      fin_cases s <;> fin_cases s'
      · exact absurd rfl hpp
      · exact hc.1
      · exact hc.1.symm
      · exact absurd rfl hpp
    · obtain ⟨h1, h2, h3, h4⟩ := hdisj b b' hbb
      exact commute_gens _ _ _ _ h1 h2 h3 h4
  have hXY : ∀ p p', p ≠ p' → Commute (cX p) (cY p') := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ hpp
    by_cases hbb : b = b'
    · subst hbb
      have hc := block_commute (hne b)
      fin_cases s <;> fin_cases s'
      · exact absurd rfl hpp
      · exact hc.2.1
      · exact hc.2.2.1
      · exact absurd rfl hpp
    · obtain ⟨h1, h2, h3, h4⟩ := hdisj b b' hbb
      exact commute_gens _ _ _ _ h2 h1 h4 h3
  have hYY : ∀ p p', p ≠ p' → Commute (cY p) (cY p') := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ hpp
    by_cases hbb : b = b'
    · subst hbb
      have hc := block_commute (hne b)
      fin_cases s <;> fin_cases s'
      · exact absurd rfl hpp
      · exact hc.2.2.2
      · exact hc.2.2.2.symm
      · exact absurd rfl hpp
    · obtain ⟨h1, h2, h3, h4⟩ := hdisj b b' hbb
      exact commute_gens _ _ _ _ h4 h3 h2 h1
  have hPx : ∀ p, gx p ∈ Subgroup.normalizer (P : Set (rootData n hn K).G) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact hPn b _ (Or.inl (by rw [hgx, one_smul]; rfl))
    · exact hPn b _ (Or.inr (Or.inr (Or.inl (by rw [hgx, one_smul]; rfl))))
  have hPy : ∀ p, gy p ∈ Subgroup.normalizer (P : Set (rootData n hn K).G) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact hPn b _ (Or.inr (Or.inl (by rw [hgy, one_smul]; rfl)))
    · exact hPn b _ (Or.inr (Or.inr (Or.inr (by rw [hgy, one_smul]; rfl))))
  have h := RootData.three_witness_pairs_normal (R := rootData n hn K) hchar (F := F)
    (X := fun p => intMap K (MX p)) (Y := fun p => intMap K (MY p)) hpair hX0 gx gy
    (fun p => by rw [hgx, one_smul]) (fun p => by rw [hgy, one_smul])
    (by rintro ⟨b, s⟩; fin_cases s; exacts [(hD b).1, hgPD b])
    (by rintro ⟨b, s⟩; fin_cases s; exacts [(hD b).2, hgND b])
    (fun p p' hpp => intMap_commute_of (hMX p) (hMX p') (hXX p p' hpp).eq)
    (fun p p' hpp => intMap_commute_of (hMX p) (hMY p') (hXY p p' hpp).eq)
    (fun p p' hpp => intMap_commute_of (hMY p) (hMY p') (hYY p p' hpp).eq) P hPD hP2 hPz hPx hPy
  rwa [Fintype.card_prod, Fintype.card_fin] at h
end Blocks

end CarrierD

section Ring

variable {A : Type*} [Ring A] {a b v : A}

theorem bracket_dual_right (hav : a * v = -(v * a)) (hbv : b * v + v * b = 1) :
    a * b * v - v * (a * b) = a := by
  calc a * b * v - v * (a * b) = a * (b * v) + a * (v * b) := by
        rw [← mul_assoc v a b, show v * a = -(a * v) by rw [hav, neg_neg]]
        noncomm_ring
    _ = a := by rw [← mul_add, hbv, mul_one]

theorem bracket_dual_left (hbv : b * v = -(v * b)) (hav : a * v + v * a = 1) :
    a * b * v - v * (a * b) = -b := by
  calc a * b * v - v * (a * b) = -((a * v + v * a) * b) := by
        rw [mul_assoc a b v, hbv]
        noncomm_ring
    _ = -b := by rw [hav, one_mul]

theorem bracket_anti (hav : a * v = -(v * a)) (hbv : b * v = -(v * b)) :
    a * b * v - v * (a * b) = 0 := by
  calc a * b * v - v * (a * b) = a * (b * v) - v * a * b := by noncomm_ring
    _ = -(a * v) * b - v * a * b := by rw [hbv]; noncomm_ring
    _ = 0 := by rw [hav]; noncomm_ring

theorem sandwich_right (hb : b * b = 0) (hab : a * b = -(b * a)) (hbv : b * v = -(v * b)) :
    a * b * v * (a * b) = 0 := by
  calc a * b * v * (a * b) = -(a * v * (b * a) * b) := by rw [mul_assoc a b v, hbv]; noncomm_ring
    _ = a * v * a * (b * b) := by
        rw [show b * a = -(a * b) by rw [hab, neg_neg]]
        noncomm_ring
    _ = 0 := by rw [hb, mul_zero]

theorem sandwich_left (ha : a * a = 0) (hab : a * b = -(b * a)) (hav : a * v = -(v * a)) :
    a * b * v * (a * b) = 0 := by
  calc a * b * v * (a * b) = a * b * (v * a) * b := by noncomm_ring
    _ = -(a * (b * a) * v * b) := by
        rw [show v * a = -(a * v) by rw [hav, neg_neg]]
        noncomm_ring
    _ = a * a * b * v * b := by
        rw [show b * a = -(a * b) by rw [hab, neg_neg]]
        noncomm_ring
    _ = 0 := by rw [ha, zero_mul, zero_mul, zero_mul]

end Ring


namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  {b : Module.Basis ι K P.W}

theorem bracket_crm {z v : CliffordAlgebra Q} {m : ι} (hz : Commute z (cr b m)) :
    z * (cr b m * v) - cr b m * v * z = cr b m * (z * v - v * z) := by
  rw [mul_sub, ← mul_assoc z, hz.eq]
  noncomm_ring

theorem sandwich_crm {z v : CliffordAlgebra Q} {m : ι} (hz : Commute z (cr b m))
    (hzvz : z * v * z = 0) : z * (cr b m * v) * z = 0 := by
  rw [← mul_assoc, hz.eq, mul_assoc (cr b m) z v, mul_assoc, hzvz, mul_zero]

theorem crm_mul_crm {v v' : CliffordAlgebra Q} {m : ι} (hv : v * cr b m = -(cr b m * v)) :
    cr b m * v * (cr b m * v') = 0 := by
  calc cr b m * v * (cr b m * v') = cr b m * (v * cr b m) * v' := by noncomm_ring
    _ = 0 := by rw [hv, mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_mul, zero_mul, neg_zero]

end Cliff


namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

section Five

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem nu_mem_frob (hF : (rootData n hn K).IsFrobenius σ F) (j : Fin n) :
    nu j ∈ fixedSubgroup F := by
  have h1 : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have hm1 : (-1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).neg_mem h1
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (x_mem_fixed hF h1) (y_mem_fixed hF hm1))
    (x_mem_fixed hF h1)

omit [Field K] in
theorem intMap_bracket_D {c : Cl n} {X Y Z : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    {zc xc : Cl n} (hZ : IsIntOp n zc X) (hX : IsIntOp n xc Y) (hc : IsIntOp n c Z)
    (h : zc * xc - xc * zc = c) (K' : Type*) [Field K'] :
    intMap K' X * intMap K' Y - intMap K' Y * intMap K' X = intMap K' Z := by
  rw [← intMap_mul, ← intMap_mul, ← intMap_sub', ((hZ.mul hX).sub (hX.mul hZ)).eq (hc.congr h.symm)]

theorem normalizer_of_cl (hchar : (2 : K) = 0) {pg : Fin 4 → (rootData n hn K).G}
    {M : Fin 4 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} {pc : Fin 4 → Cl n}
    (hM : ∀ k, IsIntOp n (pc k) (M k))
    (hpg : ∀ k, (rootData n hn K).mat (pg k) = 1 + intMap K (M k))
    (hpp : ∀ k k', pc k * pc k' = 0) {g : (rootData n hn K).G} {zc : Cl n}
    {MZ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (hZ : IsIntOp n zc MZ)
    (hg : (rootData n hn K).mat g = 1 + intMap K MZ) (hzz : zc * zc = 0)
    (hout : ∀ k, zc * pc k * zc = 0 ∧ (zc * pc k - pc k * zc = 0 ∨
      ∃ k', zc * pc k - pc k * zc = pc k' ∨ zc * pc k - pc k * zc = -pc k')) :
    g ∈ Subgroup.normalizer (Subgroup.closure (Set.range pg) : Set (rootData n hn K).G) := by
  have hZZ : intMap K MZ * intMap K MZ = 0 := by
    rw [← intMap_mul, (hZ.mul hZ).eq_zero hzz, intMap_zero]
  refine mem_normalizer_closure (mul_self_of_mat hchar hg hZZ) ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨hs, ho⟩ := hout k
  have hZXZ : intMap K MZ * intMap K (M k) * intMap K MZ = 0 := by
    rw [intMap_eq_of hZ (hM k) IsIntOp.zero hs, intMap_zero]
  have hXX : ∀ k', intMap K (M k) * intMap K (M k') = 0 := fun k' => by
    rw [← intMap_mul, ((hM k).mul (hM k')).eq_zero (hpp k k'), intMap_zero]
  refine conj_mem_closure_step hchar hg (hpg k) hZZ hZXZ ⟨k, rfl⟩ ?_
  rcases ho with h0 | ⟨k', h1 | h1⟩
  · left
    rw [intMap_bracket_D hZ (hM k) IsIntOp.zero h0, intMap_zero]
  · exact Or.inr ⟨pg k', ⟨k', rfl⟩, intMap K (M k'), hpg k', hXX k',
      Or.inl (intMap_bracket_D hZ (hM k) (hM k') h1 K)⟩
  · refine Or.inr ⟨pg k', ⟨k', rfl⟩, intMap K (M k'), hpg k', hXX k', Or.inr ?_⟩
    rw [intMap_bracket_D hZ (hM k) (hM k').neg h1, intMap_neg']


theorem hasWitness_five_gen (hF : (rootData n hn K).IsFrobenius σ F)
    (hR : (rootData n hn K).RootsInCommutator σ F) (hchar : (2 : K) = 0) (h5 : n = 5) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  have hDx : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n hn K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun i u hu => (hR i u hu).1
  have hDy : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n hn K).y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun i u hu => (hR i u hu).2
  have h1L : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have hnu : ∀ j : Fin n, ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu j * g * (nu j)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j g hg =>
    conj_mem_commutator (nu_mem_frob hF j) g hg
  let c0 : Fin n := ⟨0, by omega⟩
  let c1 : Fin n := ⟨1, by omega⟩
  let c2 : Fin n := ⟨2, by omega⟩
  have v0 : c0.val = 0 := rfl
  have v1 : c1.val = 1 := rfl
  have v2 : c2.val = 2 := rfl
  have vA : (forkA n hn).val = 3 := by show n - 2 = 3; omega
  have vB : (forkB n hn).val = 4 := by show n - 1 = 4; omega
  have n01 : c0 ≠ c1 := fin_ne (by omega)
  have n10 : c1 ≠ c0 := fin_ne (by omega)
  have n20 : c2 ≠ c0 := fin_ne (by omega)
  have n21 : c2 ≠ c1 := fin_ne (by omega)
  have n12 : c1 ≠ c2 := fin_ne (by omega)
  have n2A : c2 ≠ forkA n hn := fin_ne (by omega)
  have nAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  have nB2 : forkB n hn ≠ c2 := fin_ne (by omega)
  have nBA : forkB n hn ≠ forkA n hn := fin_ne (by omega)
  have nB1 : forkB n hn ≠ c1 := fin_ne (by omega)
  have nA1 : forkA n hn ≠ c1 := fin_ne (by omega)
  have nA2 : forkA n hn ≠ c2 := fin_ne (by omega)
  have nB0 : forkB n hn ≠ c0 := fin_ne (by omega)
  have nA0 : forkA n hn ≠ c0 := fin_ne (by omega)
  have n1B : c1 ≠ forkB n hn := fin_ne (by omega)
  have n1A : c1 ≠ forkA n hn := fin_ne (by omega)
  have hM0 := isIntOp_chainF hn (j := c1) (k := c2) (by omega)
  have hM0R : (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (rootIntMatrix n hn (.inr c1))) :=
    RootOpIn.of_y (R := rootData n hn K) c1 fun u hu => hDy c1 u hu
  have hw1 : chainWeyl (polarizationBasis n) c0 c1 * (crD n c2 * anD n c1) =
      crD n c2 * anD n c0 * chainWeyl (polarizationBasis n) c0 c1 := by
    have hc := (commute_cr_weyls (b := polarizationBasis n) (i := c0) (k := c1) n20 n21).1
    rw [← mul_assoc, ← hc.eq, mul_assoc, chainWeyl_mul_an n01, ← mul_assoc]
  obtain ⟨hM1, hM1R⟩ := rootOpIn_conj (isIntOp_chainE hn (j := c0) (k := c1) (by omega))
    (isIntOp_chainF hn (j := c0) (k := c1) (by omega)) (chain_E_sq n01) (chain_F_sq n01) hM0 hw1
    (hnu c0) hM0R
  have base : ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n (forkA n hn) * crD n (forkB n hn)) M ∧
      IsIntOp n (anD n (forkB n hn) * anD n (forkA n hn)) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N) :=
    ⟨_, _, isIntOp_forkE hn, isIntOp_forkF hn,
      RootOpIn.of_x (R := rootData n hn K) (forkB n hn) fun u hu => hDx _ u hu,
      RootOpIn.of_y (R := rootData n hn K) (forkB n hn) fun u hu => hDy _ u hu⟩
  have m1 := chainWeyl_pair_first (b := polarizationBasis n) n2A nB2 nBA
  have q1 := CarrierTD.pairOps_move (j := c2) (k := forkA n hn) (by omega) (hnu c2) m1.1 m1.2 base
  have m2 := chainWeyl_pair_first (b := polarizationBasis n) n12 nB1 nB2
  have q2 := CarrierTD.pairOps_move (j := c1) (k := c2) (by omega) (hnu c1) m2.1 m2.2 q1
  have m3 := chainWeyl_pair_second (b := polarizationBasis n) nAB n1A n1B
  have q3 := CarrierTD.pairOps_move (j := forkA n hn) (k := forkB n hn) (by omega)
    (hnu (forkA n hn)) m3.1 m3.2 q2
  have m4 := chainWeyl_pair_second (b := polarizationBasis n) n2A n12 n1A
  have q4 := CarrierTD.pairOps_move (j := c2) (k := forkA n hn) (by omega) (hnu c2) m4.1 m4.2 q3
  have m5 := chainWeyl_pair_first (b := polarizationBasis n) n01 n20 n21
  have q5 := CarrierTD.pairOps_move (j := c0) (k := c1) (by omega) (hnu c0) m5.1 m5.2 q4
  obtain ⟨M12, -, hM12, -, hM12R, -⟩ := q4
  obtain ⟨M02, -, hM02, -, hM02R, -⟩ := q5
  have hM2 : IsIntOp n (crD n c2 * crD n c1) (-M12) :=
    hM12.neg.congr (by rw [cr_cr (polarizationBasis n) c1 c2, neg_neg])
  have hM2R : (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (-M12)) := by
    rw [intMap_neg']
    exact hM12R.neg
  have hM3 : IsIntOp n (crD n c2 * crD n c0) (-M02) :=
    hM02.neg.congr (by rw [cr_cr (polarizationBasis n) c0 c2, neg_neg])
  have hM3R : (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (-M02)) := by
    rw [intMap_neg']
    exact hM02R.neg
  let M : Fin 4 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    ![rootIntMatrix n hn (.inr c1), wlMat hn c0 * rootIntMatrix n hn (.inr c1) * wlInv hn c0,
      -M12, -M02]
  let vk : Fin 4 → Cl n := ![anD n c1, anD n c0, crD n c1, crD n c0]
  let pc : Fin 4 → Cl n := fun k => crD n c2 * vk k
  have hM : ∀ k, IsIntOp n (pc k) (M k) := by
    intro k
    fin_cases k
    exacts [hM0, hM1, hM2, hM3]
  have hMR : ∀ k, (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (M k)) := by
    intro k
    fin_cases k
    exacts [hM0R, hM1R, hM2R, hM3R]
  have hvk : ∀ k, vk k * crD n c2 = -(crD n c2 * vk k) := by
    intro k
    fin_cases k
    · exact an_cr (polarizationBasis n) n21
    · exact an_cr (polarizationBasis n) n20
    · exact cr_cr (polarizationBasis n) c1 c2
    · exact cr_cr (polarizationBasis n) c0 c2
  have hpp : ∀ k k', pc k * pc k' = 0 := fun k k' => crm_mul_crm (hvk k)
  choose pg hpgD hpg using fun k => (hMR k).memD 1 h1L
  have hpg' : ∀ k, (rootData n hn K).mat (pg k) = 1 + intMap K (M k) := fun k => by
    rw [hpg, one_smul]
  have hXX : ∀ k k', intMap K (M k) * intMap K (M k') = 0 := fun k k' => by
    rw [← intMap_mul, ((hM k).mul (hM k')).eq_zero (hpp k k'), intMap_zero]
  have e2 : ∀ A B : Matrix (Fin (dimension n)) (Fin (dimension n)) K, A * B = 0 →
      (1 + A) * (1 + B) = 1 + A + B := fun A B h => by
    rw [show (1 + A) * (1 + B) = 1 + A + B + A * B by noncomm_ring, h, add_zero]
  have hcommS : ∀ x ∈ Set.range pg, ∀ y ∈ Set.range pg, x * y = y * x := by
    rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
    apply (rootData n hn K).mat_injective
    rw [mat_mul, mat_mul, hpg', hpg', e2 _ _ (hXX k k'), e2 _ _ (hXX k' k)]
    abel
  have hc1 : ∀ x ∈ Subgroup.closure (Set.range pg), ∀ s ∈ Set.range pg, x * s = s * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact fun s hs => hcommS t ht s hs
    | one => exact fun s _ => by rw [one_mul, mul_one]
    | mul a b _ _ iha ihb =>
      exact fun s hs => (Commute.mul_left (iha s hs : Commute a s) (ihb s hs)).eq
    | inv a _ iha => exact fun s hs => (Commute.inv_left (iha s hs : Commute a s)).eq
  have hc2 : ∀ x ∈ Subgroup.closure (Set.range pg), ∀ y ∈ Subgroup.closure (Set.range pg),
      x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact hc1 x hx t ht
    | one => rw [one_mul, mul_one]
    | mul a b _ _ iha ihb => exact (Commute.mul_right (iha : Commute x a) ihb).eq
    | inv a _ iha => exact (Commute.inv_right (iha : Commute x a)).eq
  have hsq : ∀ x ∈ Subgroup.closure (Set.range pg), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨k, rfl⟩ := hs
      exact mul_self_of_mat hchar (hpg' k) (hMR k).sq
    | one => rw [one_mul]
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * a * (b * b) := by rw [← hc2 a ha b hb]; group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a _ iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  have hP2 : IsPGroup 2 (Subgroup.closure (Set.range pg)) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, pow_two]; exact hsq x.1 x.2)⟩
  have hPD : Subgroup.closure (Set.range pg) ≤ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨k, rfl⟩; exact hpgD k)
  have hPz : ∃ x ∈ Subgroup.closure (Set.range pg), ∃ z ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      x * z ≠ z * x :=
    ⟨pg 0, Subgroup.subset_closure ⟨0, rfl⟩, (rootData n hn K).x c1 1, hDx c1 1 h1L, fun h =>
      (one_ne_zero : (1 : K) ≠ 0) ((rootData n hn K).eq_zero_of_commute_sqZeroPair
        ((rootData n hn K).sqZero c1) ((rootData n hn K).E_ne_zero c1) (mat_x' c1 1) (hpg' 0)
        h.symm)⟩
  obtain ⟨Xt, hXt, hXtR⟩ := exists_rootOp_theta (hn := hn) (H := fixedSubgroup F)
    (L := RootData.fixedField σ) hDx
  obtain ⟨Yt, hYt, hYtR⟩ := exists_rootOp_thetaY (hn := hn) (H := fixedSubgroup F)
    (L := RootData.fixedField σ) hDy
  let I : Fin 2 → Fin n := ![c0, forkA n hn]
  let J : Fin 2 → Fin n := ![c1, forkB n hn]
  have hIv : ∀ b, (I b).val = 3 * b.val := fun b => by
    fin_cases b
    · rfl
    · exact vA
  have hJv : ∀ b, (J b).val = 3 * b.val + 1 := fun b => by
    fin_cases b
    · rfl
    · exact vB
  let b := polarizationBasis n
  have hzE : Commute (crD n c0 * anD n c1) (crD n c2) :=
    (show Commute (crD n c2) (crD n c0 * anD n c1) from
      commute_mul_of_anticomm₂ (cr_cr b c2 c0) (cr_an b n21)).symm
  have hzF : Commute (crD n c1 * anD n c0) (crD n c2) :=
    (show Commute (crD n c2) (crD n c1 * anD n c0) from
      commute_mul_of_anticomm₂ (cr_cr b c2 c1) (cr_an b n20)).symm
  have hzT : Commute (crD n c0 * crD n c1) (crD n c2) :=
    (show Commute (crD n c2) (crD n c0 * crD n c1) from
      commute_mul_of_anticomm₂ (cr_cr b c2 c0) (cr_cr b c2 c1)).symm
  have hzT' : Commute (anD n c1 * anD n c0) (crD n c2) :=
    (show Commute (crD n c2) (anD n c1 * anD n c0) from
      commute_mul_of_anticomm₂ (cr_an b n21) (cr_an b n20)).symm
  have houtE : ∀ k, crD n c0 * anD n c1 * pc k * (crD n c0 * anD n c1) = 0 ∧
      (crD n c0 * anD n c1 * pc k - pc k * (crD n c0 * anD n c1) = 0 ∨
        ∃ k', crD n c0 * anD n c1 * pc k - pc k * (crD n c0 * anD n c1) = pc k' ∨
          crD n c0 * anD n c1 * pc k - pc k * (crD n c0 * anD n c1) = -pc k') := by
    intro k
    fin_cases k
    · exact ⟨sandwich_crm hzE (sandwich_right (an_sq b c1) (cr_an b n01) (an_an b c1 c1)),
        Or.inl ((bracket_crm hzE).trans ((congrArg (crD n c2 * ·)
          (bracket_anti (cr_an b n01) (an_an b c1 c1))).trans (mul_zero _)))⟩
    · exact ⟨sandwich_crm hzE (sandwich_right (an_sq b c1) (cr_an b n01) (an_an b c1 c0)),
        Or.inr ⟨0, Or.inr ((bracket_crm hzE).trans ((congrArg (crD n c2 * ·)
          (bracket_dual_left (an_an b c1 c0) (cr_an_self b c0))).trans (mul_neg _ _)))⟩⟩
    · exact ⟨sandwich_crm hzE (sandwich_left (cr_sq b c0) (cr_an b n01) (cr_cr b c0 c1)),
        Or.inr ⟨3, Or.inl ((bracket_crm hzE).trans (congrArg (crD n c2 * ·)
          (bracket_dual_right (cr_cr b c0 c1) (an_cr_self b c1))))⟩⟩
    · exact ⟨sandwich_crm hzE (sandwich_left (cr_sq b c0) (cr_an b n01) (cr_cr b c0 c0)),
        Or.inl ((bracket_crm hzE).trans ((congrArg (crD n c2 * ·)
          (bracket_anti (cr_cr b c0 c0) (an_cr b n01))).trans (mul_zero _)))⟩
  have houtF : ∀ k, crD n c1 * anD n c0 * pc k * (crD n c1 * anD n c0) = 0 ∧
      (crD n c1 * anD n c0 * pc k - pc k * (crD n c1 * anD n c0) = 0 ∨
        ∃ k', crD n c1 * anD n c0 * pc k - pc k * (crD n c1 * anD n c0) = pc k' ∨
          crD n c1 * anD n c0 * pc k - pc k * (crD n c1 * anD n c0) = -pc k') := by
    intro k
    fin_cases k
    · exact ⟨sandwich_crm hzF (sandwich_right (an_sq b c0) (cr_an b n10) (an_an b c0 c1)),
        Or.inr ⟨1, Or.inr ((bracket_crm hzF).trans ((congrArg (crD n c2 * ·)
          (bracket_dual_left (an_an b c0 c1) (cr_an_self b c1))).trans (mul_neg _ _)))⟩⟩
    · exact ⟨sandwich_crm hzF (sandwich_right (an_sq b c0) (cr_an b n10) (an_an b c0 c0)),
        Or.inl ((bracket_crm hzF).trans ((congrArg (crD n c2 * ·)
          (bracket_anti (cr_an b n10) (an_an b c0 c0))).trans (mul_zero _)))⟩
    · exact ⟨sandwich_crm hzF (sandwich_left (cr_sq b c1) (cr_an b n10) (cr_cr b c1 c1)),
        Or.inl ((bracket_crm hzF).trans ((congrArg (crD n c2 * ·)
          (bracket_anti (cr_cr b c1 c1) (an_cr b n10))).trans (mul_zero _)))⟩
    · exact ⟨sandwich_crm hzF (sandwich_left (cr_sq b c1) (cr_an b n10) (cr_cr b c1 c0)),
        Or.inr ⟨2, Or.inl ((bracket_crm hzF).trans (congrArg (crD n c2 * ·)
          (bracket_dual_right (cr_cr b c1 c0) (an_cr_self b c0))))⟩⟩
  have houtT : ∀ k, crD n c0 * crD n c1 * pc k * (crD n c0 * crD n c1) = 0 ∧
      (crD n c0 * crD n c1 * pc k - pc k * (crD n c0 * crD n c1) = 0 ∨
        ∃ k', crD n c0 * crD n c1 * pc k - pc k * (crD n c0 * crD n c1) = pc k' ∨
          crD n c0 * crD n c1 * pc k - pc k * (crD n c0 * crD n c1) = -pc k') := by
    intro k
    fin_cases k
    · exact ⟨sandwich_crm hzT (sandwich_left (cr_sq b c0) (cr_cr b c0 c1) (cr_an b n01)),
        Or.inr ⟨3, Or.inl ((bracket_crm hzT).trans (congrArg (crD n c2 * ·)
          (bracket_dual_right (cr_an b n01) (cr_an_self b c1))))⟩⟩
    · exact ⟨sandwich_crm hzT (sandwich_right (cr_sq b c1) (cr_cr b c0 c1) (cr_an b n10)),
        Or.inr ⟨2, Or.inr ((bracket_crm hzT).trans ((congrArg (crD n c2 * ·)
          (bracket_dual_left (cr_an b n10) (cr_an_self b c0))).trans (mul_neg _ _)))⟩⟩
    · exact ⟨sandwich_crm hzT (sandwich_left (cr_sq b c0) (cr_cr b c0 c1) (cr_cr b c0 c1)),
        Or.inl ((bracket_crm hzT).trans ((congrArg (crD n c2 * ·)
          (bracket_anti (cr_cr b c0 c1) (cr_cr b c1 c1))).trans (mul_zero _)))⟩
    · exact ⟨sandwich_crm hzT (sandwich_left (cr_sq b c0) (cr_cr b c0 c1) (cr_cr b c0 c0)),
        Or.inl ((bracket_crm hzT).trans ((congrArg (crD n c2 * ·)
          (bracket_anti (cr_cr b c0 c0) (cr_cr b c1 c0))).trans (mul_zero _)))⟩
  have houtT' : ∀ k, anD n c1 * anD n c0 * pc k * (anD n c1 * anD n c0) = 0 ∧
      (anD n c1 * anD n c0 * pc k - pc k * (anD n c1 * anD n c0) = 0 ∨
        ∃ k', anD n c1 * anD n c0 * pc k - pc k * (anD n c1 * anD n c0) = pc k' ∨
          anD n c1 * anD n c0 * pc k - pc k * (anD n c1 * anD n c0) = -pc k') := by
    intro k
    fin_cases k
    · exact ⟨sandwich_crm hzT' (sandwich_left (an_sq b c1) (an_an b c1 c0) (an_an b c1 c1)),
        Or.inl ((bracket_crm hzT').trans ((congrArg (crD n c2 * ·)
          (bracket_anti (an_an b c1 c1) (an_an b c0 c1))).trans (mul_zero _)))⟩
    · exact ⟨sandwich_crm hzT' (sandwich_left (an_sq b c1) (an_an b c1 c0) (an_an b c1 c0)),
        Or.inl ((bracket_crm hzT').trans ((congrArg (crD n c2 * ·)
          (bracket_anti (an_an b c1 c0) (an_an b c0 c0))).trans (mul_zero _)))⟩
    · exact ⟨sandwich_crm hzT' (sandwich_right (an_sq b c0) (an_an b c1 c0) (an_cr b n10)),
        Or.inr ⟨1, Or.inr ((bracket_crm hzT').trans ((congrArg (crD n c2 * ·)
          (bracket_dual_left (an_cr b n10) (an_cr_self b c1))).trans (mul_neg _ _)))⟩⟩
    · exact ⟨sandwich_crm hzT' (sandwich_left (an_sq b c1) (an_an b c1 c0) (an_cr b n01)),
        Or.inr ⟨0, Or.inl ((bracket_crm hzT').trans (congrArg (crD n c2 * ·)
          (bracket_dual_right (an_cr b n01) (an_cr_self b c0))))⟩⟩
  have hcomm34 : ∀ {z : Cl n}, z * z = 0 → (∀ k, Commute z (pc k)) → ∀ k,
      z * pc k * z = 0 ∧ (z * pc k - pc k * z = 0 ∨
        ∃ k', z * pc k - pc k * z = pc k' ∨ z * pc k - pc k * z = -pc k') :=
    fun hzz hc k => ⟨by rw [(hc k).eq, mul_assoc, hzz, mul_zero],
      Or.inl (sub_eq_zero.mpr (hc k).eq)⟩
  have hvkg : ∀ k, ∃ (s : Bool) (q : Fin n), vk k = gen b s q ∧ q.val < 2 := by
    intro k
    fin_cases k
    exacts [⟨false, c1, rfl, by omega⟩, ⟨false, c0, rfl, by omega⟩, ⟨true, c1, rfl, by omega⟩,
      ⟨true, c0, rfl, by omega⟩]
  have hcz : ∀ s₁ s₂ : Bool, ∀ p₁ p₂ : Fin n, (p₁ = forkA n hn ∨ p₁ = forkB n hn) →
      (p₂ = forkA n hn ∨ p₂ = forkB n hn) → ∀ k, Commute (gen b s₁ p₁ * gen b s₂ p₂) (pc k) := by
    intro s₁ s₂ p₁ p₂ hp₁ hp₂ k
    obtain ⟨s, q, hs, hq⟩ := hvkg k
    have h1 : 3 ≤ p₁.val := by rcases hp₁ with rfl | rfl <;> omega
    have h2 : 3 ≤ p₂.val := by rcases hp₂ with rfl | rfl <;> omega
    show Commute _ (crD n c2 * vk k)
    rw [hs]
    exact commute_gens s₁ s₂ true s (fin_ne (by omega)) (fin_ne (by omega)) (fin_ne (by omega))
      (fin_ne (by omega))
  have hPn : ∀ (b' : Fin 2) (g : (rootData n hn K).G),
      ((rootData n hn K).mat g = 1 + intMap K (rootIntMatrix n hn (.inl (I b'))) ∨
        (rootData n hn K).mat g = 1 + intMap K (rootIntMatrix n hn (.inr (I b'))) ∨
        (rootData n hn K).mat g = 1 + intMap K (![Xt, rootIntMatrix n hn (.inl (forkB n hn))] b') ∨
        (rootData n hn K).mat g = 1 + intMap K (![Yt, rootIntMatrix n hn (.inr (forkB n hn))] b')) →
      g ∈ Subgroup.normalizer (Subgroup.closure (Set.range pg) : Set (rootData n hn K).G) := by
    intro b' g hg
    fin_cases b'
    · rcases hg with hg | hg | hg | hg
      · exact normalizer_of_cl hchar hM hpg' hpp (isIntOp_chainE hn (j := c0) (k := c1) rfl) hg
          (chain_E_sq n01) houtE
      · exact normalizer_of_cl hchar hM hpg' hpp (isIntOp_chainF hn (j := c0) (k := c1) rfl) hg
          (chain_F_sq n01) houtF
      · exact normalizer_of_cl hchar hM hpg' hpp hXt hg pair_E_sq houtT
      · exact normalizer_of_cl hchar hM hpg' hpp hYt hg pair_F_sq houtT'
    · rcases hg with hg | hg | hg | hg
      · exact normalizer_of_cl hchar hM hpg' hpp (isIntOp_chainE hn (j := forkA n hn)
          (k := forkB n hn) (by omega)) hg (chain_E_sq nAB)
          (hcomm34 (chain_E_sq nAB) (hcz true false _ _ (Or.inl rfl) (Or.inr rfl)))
      · exact normalizer_of_cl hchar hM hpg' hpp (isIntOp_chainF hn (j := forkA n hn)
          (k := forkB n hn) (by omega)) hg (chain_F_sq nAB)
          (hcomm34 (chain_F_sq nAB) (hcz true false _ _ (Or.inr rfl) (Or.inl rfl)))
      · exact normalizer_of_cl hchar hM hpg' hpp (isIntOp_forkE hn) hg pair_E_sq
          (hcomm34 pair_E_sq (hcz true true _ _ (Or.inl rfl) (Or.inr rfl)))
      · exact normalizer_of_cl hchar hM hpg' hpp (isIntOp_forkF hn) hg pair_F_sq
          (hcomm34 pair_F_sq (hcz false false _ _ (Or.inr rfl) (Or.inl rfl)))
  have h := three_witness_blocks_normal hchar I J (fun b' => by rw [hIv, hJv])
    (fun b₁ b₂ hbb => by
      have hv : b₁.val ≠ b₂.val := fun h => hbb (Fin.ext h)
      have := b₁.isLt
      have := b₂.isLt
      exact ⟨fin_ne (by rw [hIv, hIv]; omega), fin_ne (by rw [hIv, hJv]; omega),
        fin_ne (by rw [hJv, hIv]; omega), fin_ne (by rw [hJv, hJv]; omega)⟩)
    (fun b' => hR (I b') 1 h1L) ![Xt, rootIntMatrix n hn (.inl (forkB n hn))]
    ![Yt, rootIntMatrix n hn (.inr (forkB n hn))]
    (fun b' => by fin_cases b'; exacts [hXt, isIntOp_forkE hn])
    (fun b' => by fin_cases b'; exacts [hYt, isIntOp_forkF hn])
    (fun b' => by
      fin_cases b'
      · exact ⟨hXtR.sq, hXtR.mem, hXtR.memD⟩
      · exact RootOpIn.of_x (R := rootData n hn K) (forkB n hn) fun u hu => hDx _ u hu)
    (fun b' => by
      fin_cases b'
      · exact ⟨hYtR.sq, hYtR.mem, hYtR.memD⟩
      · exact RootOpIn.of_y (R := rootData n hn K) (forkB n hn) fun u hu => hDy _ u hu)
    (Subgroup.closure (Set.range pg)) hPD hP2 hPz hPn
  exact h

end Five

theorem hasWitness_five (d : TypeDLieIndex) (h2 : d.1.characteristic = 2) (h5 : d.1.rank = 5) :
    HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  exact hasWitness_five_gen (isFrobenius d) (rootsInCommutator_two d h2) hchar h5

end CarrierD

end CFSG.RankThree.PartTwo.Census.Spin
