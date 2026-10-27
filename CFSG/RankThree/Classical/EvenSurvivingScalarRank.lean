module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.Classical.OrthogonalOrderThree
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open scoped Matrix

section LocalRank

variable {G : Type*} [Group G] [Finite G]

theorem pRank_le_natCard {p : ℕ} (hp : 1 < p) (X : Subgroup G) : pRank p X ≤ Nat.card G :=
  CFSG.SectionRank.pRank_le_card_of_one_lt hp X

theorem pRank_le_localRank {p : ℕ} (hp : 1 < p) {X : Subgroup G} (hX : IsTwoLocal X) :
    pRank p X ≤ localRank p G :=
  le_csSup ⟨Nat.card G, by rintro _ ⟨Y, -, rfl⟩; exact pRank_le_natCard hp Y⟩ ⟨X, hX, rfl⟩

theorem le_localRank_of_injective {p : ℕ} (hp : 1 < p) {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) {k : ℕ}
    (hA : Nat.card A = p ^ k) (φ : A →* G) (hφ : Function.Injective φ) {u : G} (hu : u ≠ 1)
    (hu2 : u ^ 2 = 1) (hcu : ∀ a, φ a * u = u * φ a) : k ≤ localRank p G := by
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu
  have hP2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers u ≠ ⊥ := fun h => hu (by
    have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rwa [h, Subgroup.mem_bot] at this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  refine le_trans ?_ (pRank_le_localRank hp hloc)
  refine CFSG.SectionRank.le_pRank_of_injective hp hcomm hpow hA φ hφ ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hconj : ∀ m : ℤ, φ a * u ^ m * (φ a)⁻¹ = u ^ m := fun m => by
    rw [((Commute.zpow_right (hcu a) m)).eq, mul_inv_cancel_right]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, (hconj m).symm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, mul_left_cancel (mul_right_cancel ((hconj m).trans hm))⟩

end LocalRank

section Torus

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def diagGL : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => K)).symm.toMonoidHom

theorem coe_diagGL (d : Fin n → Kˣ) :
    (diagGL d : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun i => (d i : K) :=
  rfl

theorem diagGL_mul_permGL_swap {d : Fin n → Kˣ} {a b : Fin n} (hab : d a = d b) :
    diagGL d * permGL (Equiv.swap a b) = permGL (Equiv.swap a b) * diagGL d := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diagGL, MonoidHom.coe_toHomUnits,
    Matrix.permMatrixHom_apply, Equiv.swap_inv]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  split_ifs with h
  · subst h
    have hd : d (Equiv.swap a b i) = d i := by
      rcases eq_or_ne i a with rfl | hia
      · rw [Equiv.swap_apply_left, hab]
      rcases eq_or_ne i b with rfl | hib
      · rw [Equiv.swap_apply_right, hab]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
    rw [hd, mul_one, one_mul]
  · rw [mul_zero, zero_mul]

@[expose] def coordEquiv (m : ℕ) : Fin 2 ⊕ Fin m ⊕ Fin 1 ≃ Fin (m + 3) :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

variable {p : ℕ}

@[expose] def torusExp (m : ℕ) (y : Fin m → ZMod p) : Fin (m + 3) → ZMod p :=
  fun k => Sum.elim (fun _ => -(∑ i, y i) * (((p + 1) / 2 : ℕ) : ZMod p))
    (Sum.elim y fun _ => 0) ((coordEquiv m).symm k)

theorem torusExp_coord {m : ℕ} (y : Fin m → ZMod p) (x : Fin 2 ⊕ Fin m ⊕ Fin 1) :
    torusExp m y (coordEquiv m x) =
      Sum.elim (fun _ => -(∑ i, y i) * (((p + 1) / 2 : ℕ) : ZMod p))
        (Sum.elim y fun _ => 0) x := by
  simp only [torusExp, Equiv.symm_apply_apply]

theorem torusExp_add {m : ℕ} (y y' : Fin m → ZMod p) :
    torusExp m (y + y') = torusExp m y + torusExp m y' := by
  funext k
  obtain ⟨x, rfl⟩ := (coordEquiv m).surjective k
  rw [Pi.add_apply, torusExp_coord, torusExp_coord, torusExp_coord]
  rcases x with x | x | x
  · simp only [Sum.elim_inl, Pi.add_apply, Finset.sum_add_distrib]
    ring
  · simp
  · simp

theorem torusExp_sum (hp : Odd p) {m : ℕ} (y : Fin m → ZMod p) :
    ∑ k, torusExp m y k = 0 := by
  have h2 : (2 : ZMod p) * (((p + 1) / 2 : ℕ) : ZMod p) = 1 := by
    have hn : 2 * ((p + 1) / 2) = p + 1 := by
      obtain ⟨k, rfl⟩ := hp
      omega
    have := congrArg (fun t : ℕ => (t : ZMod p)) hn
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, ZMod.natCast_self, zero_add,
      Nat.cast_one] at this
    exact this
  rw [← Equiv.sum_comp (coordEquiv m)]
  simp only [torusExp_coord, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const_zero, add_zero, Fin.sum_univ_two]
  linear_combination (-(∑ i, y i)) * h2

theorem pow_val_add [NeZero p] {M : Type*} [Monoid M] {ζ : M} (hζ : ζ ^ p = 1) (a b : ZMod p) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem pow_val_eq_one_iff [NeZero p] {M : Type*} [Monoid M] {ζ : M} (hζ : orderOf ζ = p)
    (a : ZMod p) :
    ζ ^ a.val = 1 ↔ a = 0 := by
  rw [← orderOf_dvd_iff_pow_eq_one, hζ, ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

@[expose] noncomputable def torusDiag (ζ : Kˣ) (m : ℕ) (y : Fin m → ZMod p) :
    GL (Fin (m + 3)) K :=
  diagGL fun k => ζ ^ (torusExp m y k).val

theorem torusDiag_add [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1) {m : ℕ} (y y' : Fin m → ZMod p) :
    torusDiag ζ m (y + y') = torusDiag ζ m y * torusDiag ζ m y' := by
  rw [torusDiag, torusDiag, torusDiag, ← map_mul, torusExp_add]
  congr 1
  funext k
  rw [Pi.add_apply, pow_val_add hζ, Pi.mul_apply]

theorem torusDiag_zero {ζ : Kˣ} {m : ℕ} : torusDiag ζ m (0 : Fin m → ZMod p) = 1 := by
  rw [torusDiag, ← map_one diagGL]
  congr 1
  funext k
  obtain ⟨x, rfl⟩ := (coordEquiv m).surjective k
  rw [torusExp_coord]
  rcases x with x | x | x <;> simp

theorem coe_torusDiag_apply {ζ : Kˣ} {m : ℕ} (y : Fin m → ZMod p) (k : Fin (m + 3)) :
    (torusDiag ζ m y : Matrix (Fin (m + 3)) (Fin (m + 3)) K) k k =
      ((ζ ^ (torusExp m y k).val : Kˣ) : K) := by
  rw [torusDiag, coe_diagGL, Matrix.diagonal_apply_eq]

end Torus

section Surviving

variable {K : Type} [Field K] [Finite K]

theorem le_localRank_of_surviving_scalar {p : ℕ} [hp : Fact p.Prime] (m : ℕ)
    {H : Subgroup (GL (Fin (m + 3)) K)} {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hdiag : ∀ y : Fin m → ZMod p, torusDiag ζ m y ∈ H)
    (hswap : ∀ a b : Fin (m + 3), permGL (K := K) (Equiv.swap a b) ∈ H)
    (B : Subgroup H) [B.Normal] (hB : B ≤ (StatedScalars (Fin (m + 3)) K).subgroupOf H)
    {z : H} (hzD : z ∈ (StatedScalars (Fin (m + 3)) K).subgroupOf H) (hzB : z ∉ B)
    (hzp : z ^ p ∈ B) : m + 1 ≤ localRank p (H ⧸ B) := by
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set D := (StatedScalars (Fin (m + 3)) K).subgroupOf H
  set a₀ := coordEquiv m (Sum.inl 0)
  set b₀ := coordEquiv m (Sum.inl 1)
  have hab : a₀ ≠ b₀ := fun h => by
    have := (coordEquiv m).injective h
    simp at this
  let s : H := ⟨permGL (Equiv.swap a₀ b₀), hswap a₀ b₀⟩
  set u : H ⧸ B := QuotientGroup.mk s
  have hu : u ≠ 1 := by
    intro h
    have h' := hB ((QuotientGroup.eq_one_iff s).mp h)
    rw [Subgroup.mem_subgroupOf] at h'
    exact permGL_not_mem_statedScalars (fun h1 => hab (Equiv.swap_eq_one_iff.mp h1)) h'
  have hu2 : u ^ 2 = 1 := by
    have : s ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, pow_two, Equiv.swap_mul_self, map_one]
      rfl)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  set x : H ⧸ B := QuotientGroup.mk z
  have hx1 : x ≠ 1 := fun h => hzB ((QuotientGroup.eq_one_iff z).mp h)
  have hxp : x ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hzp
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  obtain ⟨c, hc⟩ := hzD
  have hc' : (z : GL (Fin (m + 3)) K) = Matrix.GeneralLinearGroup.scalar (Fin (m + 3)) c :=
    hc.symm
  have hzc : ∀ g : H, z * g = g * z := fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc']
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (g : GL (Fin (m + 3)) K)).eq.symm)
  have hxc : ∀ g : H ⧸ B, Commute g x := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (g : H ⧸ B) * (z : H ⧸ B) = (z : H ⧸ B) * (g : H ⧸ B)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hzc g]
  let T : Multiplicative (Fin m → ZMod p) →* H :=
    { toFun := fun y => ⟨torusDiag ζ m y.toAdd, hdiag _⟩
      map_one' := Subtype.ext torusDiag_zero
      map_mul' := fun y y' => Subtype.ext (torusDiag_add hζp _ _) }
  let Ψ₁ : Multiplicative (Fin m → ZMod p) →* H ⧸ B := (QuotientGroup.mk' B).comp T
  let Ψ₂ : Multiplicative (ZMod p) →* H ⧸ B :=
    { toFun := fun j => x ^ j.toAdd.val
      map_one' := by simp
      map_mul' := fun j j' => pow_val_add hxp _ _ }
  let Ψ := Ψ₁.noncommCoprod Ψ₂ fun a j => ((hxc (Ψ₁ a)).pow_right _)
  have hΨ : ∀ g, Ψ g = Ψ₁ g.1 * x ^ g.2.toAdd.val := fun g =>
    MonoidHom.noncommCoprod_apply _ _ _ g
  refine le_localRank_of_injective hp.out.one_lt (fun a b => mul_comm a b) (fun a => ?_) ?_ Ψ
    ?_ hu hu2 ?_
  · refine Prod.ext ?_ ?_
    · change Multiplicative.ofAdd (p • a.1.toAdd) = 1
      have : p • a.1.toAdd = 0 := by
        funext i
        simp [nsmul_eq_mul]
      rw [this]
      rfl
    · change Multiplicative.ofAdd (p • a.2.toAdd) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
  · rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, pow_succ]
  · refine (injective_iff_map_eq_one Ψ).mpr ?_
    rintro ⟨a, j⟩ h
    rw [hΨ] at h
    have hmem : T a * z ^ j.toAdd.val ∈ B := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
      exact h
    have hTD : T a ∈ D := by
      have h1 : T a * z ^ j.toAdd.val ∈ D := hB hmem
      have h2 : z ^ j.toAdd.val ∈ D := D.pow_mem ⟨c, hc⟩ _
      simpa using D.mul_mem h1 (D.inv_mem h2)
    obtain ⟨ν, hν⟩ := hTD
    have hentry : ∀ k, ((ζ ^ (torusExp m a.toAdd k).val : Kˣ) : K) = ν := by
      intro k
      have := congrArg (fun g : GL (Fin (m + 3)) K => (g : Matrix _ _ K) k k) hν
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at this
      rw [this]
      exact (coe_torusDiag_apply a.toAdd k).symm
    have hν1 : (ν : K) = 1 := by
      rw [← hentry (coordEquiv m (Sum.inr (Sum.inr 0))), torusExp_coord]
      simp
    have ha : a = 1 := by
      refine Multiplicative.toAdd.injective ?_
      funext i
      have h1 := hentry (coordEquiv m (Sum.inr (Sum.inl i)))
      rw [hν1, torusExp_coord, Sum.elim_inr, Sum.elim_inl, Units.val_eq_one] at h1
      exact (pow_val_eq_one_iff hζ _).mp h1
    subst ha
    have hj : x ^ j.toAdd.val = 1 := by
      rw [map_one, one_mul] at h
      exact h
    have hj0 : j.toAdd = 0 := (pow_val_eq_one_iff hxo _).mp hj
    exact Prod.ext rfl (Multiplicative.toAdd.injective hj0)
  · intro g
    rw [hΨ]
    have h1 : Commute (Ψ₁ g.1) u := by
      change Commute (QuotientGroup.mk (T g.1)) (QuotientGroup.mk s)
      have hcomm : T g.1 * s = s * T g.1 := Subtype.ext (by
        change torusDiag ζ m g.1.toAdd * permGL (Equiv.swap a₀ b₀) =
          permGL (Equiv.swap a₀ b₀) * torusDiag ζ m g.1.toAdd
        refine diagGL_mul_permGL_swap ?_
        simp only [a₀, b₀, torusExp_coord, Sum.elim_inl])
      change (T g.1 : H ⧸ B) * (s : H ⧸ B) = (s : H ⧸ B) * (T g.1 : H ⧸ B)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
    have h2 : Commute (x ^ g.2.toAdd.val) u := ((hxc u).symm).pow_left _
    exact (h1.mul_left h2).eq

end Surviving

section Groups

theorem exists_mem_not_mem_pow_mem {G : Type*} [Group G] [Finite G] {B D : Subgroup G}
    [B.Normal] {p : ℕ} [hp : Fact p.Prime] (h : p ∣ B.relIndex D) :
    ∃ z ∈ D, z ∉ B ∧ z ^ p ∈ B := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  induction x using QuotientGroup.induction_on with
  | H w =>
    refine ⟨w, w.2, fun hw => ?_, ?_⟩
    · have h1 : (w : D ⧸ B.subgroupOf D) = 1 :=
        (QuotientGroup.eq_one_iff w).mpr (Subgroup.mem_subgroupOf.mpr hw)
      rw [h1, orderOf_one] at hx
      exact hp.out.one_lt.ne' hx.symm
    · have h1 : ((w ^ p : D) : D ⧸ B.subgroupOf D) = 1 := by
        rw [QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
      have h2 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
      simpa using h2

theorem prime_dvd_orderOf_of_pow_mem {G : Type*} [Group G] {B : Subgroup G} {p : ℕ}
    (hp : p.Prime) {z : G} (hzB : z ∉ B) (hzp : z ^ p ∈ B) : p ∣ orderOf z := by
  by_contra hdvd
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  exact hzB (hk ▸ B.pow_mem hzp k)

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  have : p ≠ 4 := fun h => by
    rw [h] at hp
    exact absurd hp (by decide)
  omega

variable {K : Type} [Field K]

theorem orderOf_scalar {n : ℕ} (hn : 1 ≤ n) (c : Kˣ) :
    orderOf (Matrix.GeneralLinearGroup.scalar (Fin n) c) = orderOf c := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine orderOf_injective _ (fun a b hab => Units.ext ?_) c
  have := congrArg Units.val hab
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar] at this
  exact Matrix.scalar_inj.mp this

theorem det_scalar_eq {n : ℕ} (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem det_torusDiag {p : ℕ} [NeZero p] (hp : Odd p) {ζ : Kˣ} (hζ : orderOf ζ = p) {m : ℕ}
    (y : Fin m → ZMod p) :
    ((torusDiag ζ m y : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K).det = 1 := by
  rw [torusDiag, coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod,
    Finset.prod_pow_eq_pow_sum]
  have hdvd : p ∣ ∑ k, (torusExp m y k).val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact torusExp_sum hp y
  have hdvd' : orderOf ζ ∣ ∑ k, (torusExp m y k).val := by
    rw [hζ]
    exact hdvd
  rw [orderOf_dvd_iff_pow_eq_one.mp hdvd', Units.val_one]

theorem det_permGL_swap {n : ℕ} (h2 : (2 : K) = 0) (a b : Fin n) :
    ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation,
    Equiv.Perm.sign_inv]
  rcases eq_or_ne a b with rfl | hab
  · rw [Equiv.swap_self, Equiv.Perm.sign_refl]
    simp
  · rw [Equiv.Perm.sign_swap hab]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination (-1 : K) * h2

theorem permGL_swap_transpose_mul {n : ℕ} (a b : Fin n) :
    ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have hT : ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.transpose_permMatrix,
      inv_inv, Equiv.swap_inv]
  rw [hT, ← Units.val_mul, ← map_mul, Equiv.swap_mul_self, map_one, Units.val_one]

theorem even_linear_surviving_scalar_local_rank {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (_hf : 1 ≤ f) {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ f) (hn : 2 ≤ n)
    (B : Subgroup (StatedSL n k)) [B.Normal]
    (hB : B ≤ (StatedScalars (Fin n) k).subgroupOf (StatedSL n k))
    (hpB : p ∣ B.relIndex ((StatedScalars (Fin n) k).subgroupOf (StatedSL n k))) :
    p ∣ n ∧ p ∣ 2 ^ f - 1 ∧ 5 ≤ n ∧ n - 2 ≤ localRank p (StatedSL n k ⧸ B) ∧ 3 ≤ n - 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := five_le_of_prime hp hp3
  have := Fintype.ofFinite k
  have hchar : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card]
    exact hk)
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  obtain ⟨z, hzD, hzB, hzp⟩ := exists_mem_not_mem_pow_mem hpB
  have hpz := prime_dvd_orderOf_of_pow_mem hp hzB hzp
  obtain ⟨c, hc⟩ := hzD
  have hc' : (z : GL (Fin n) k) = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
  have hoc : orderOf c = orderOf z := by
    rw [← orderOf_scalar (n := n) (by omega) c, ← hc', Subgroup.orderOf_coe]
  rw [← hoc] at hpz
  have hdet : (c : k) ^ n = 1 := by
    have hz : (z : GL (Fin n) k) ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) k →* GL (Fin n) k).range :=
      (Subgroup.ext_iff.mp (statedSL_eq_range_toGL n k) (z : GL (Fin n) k)).mp z.2
    obtain ⟨g, hg⟩ := hz
    have : ((z : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det = 1 := by
      rw [← hg]
      exact g.2
    rwa [hc', det_scalar_eq] at this
  have hcn : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one (Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet))
  have hcq : orderOf c ∣ 2 ^ f - 1 := by
    have := orderOf_dvd_natCard c
    rwa [Nat.card_units, hk] at this
  have hpn : p ∣ n := hpz.trans hcn
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  refine ⟨hpn, hpz.trans hcq, hn5, ?_, by omega⟩
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  set ζ := c ^ (orderOf c / p)
  have hζ : orderOf ζ = p := orderOf_pow_orderOf_div hc0 hpz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have := le_localRank_of_surviving_scalar (K := k) (H := StatedSL (m + 3) k) m hζ
    (fun y => Subgroup.subset_closure (det_torusDiag hodd hζ y))
    (fun a b => Subgroup.subset_closure (det_permGL_swap h2 a b)) B hB ⟨c, hc⟩ hzB hzp
  simpa using this

theorem even_unitary_surviving_scalar_local_rank {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {K : Type} [Field K] [Finite K] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (hn : 3 ≤ n) (B : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K n)) [B.Normal]
    (hB : B ≤ (StatedScalars (Fin n) K).subgroupOf
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K n))
    (hpB : p ∣ B.relIndex ((StatedScalars (Fin n) K).subgroupOf
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K n))) :
    p ∣ n ∧ p ∣ 2 ^ f + 1 ∧ 5 ≤ n ∧
      n - 2 ≤ localRank p (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K n ⧸ B) ∧
      3 ≤ n - 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := five_le_of_prime hp hp3
  have hchar : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  obtain ⟨z, hzD, hzB, hzp⟩ := exists_mem_not_mem_pow_mem hpB
  have hpz := prime_dvd_orderOf_of_pow_mem hp hzB hzp
  obtain ⟨c, hc⟩ := hzD
  have hc' : (z : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
  have hoc : orderOf c = orderOf z := by
    rw [← orderOf_scalar (n := n) (by omega) c, ← hc', Subgroup.orderOf_coe]
  rw [← hoc] at hpz
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ f) K := by
    rw [← hc']
    exact z.2
  obtain ⟨hcn', hcq'⟩ := (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two
    h.card_eq_sq (by omega) c).mp hmem
  have hcn : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hcn'
  have hcq : orderOf c ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one hcq'
  have hpn : p ∣ n := hpz.trans hcn
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  refine ⟨hpn, hpz.trans hcq, hn5, ?_, by omega⟩
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  set ζ := c ^ (orderOf c / p)
  have hζ : orderOf ζ = p := orderOf_pow_orderOf_div hc0 hpz
  have hζq : ∀ j : ℕ, ((ζ ^ j : Kˣ) : K) ^ (2 ^ f + 1) = 1 := fun j => by
    rw [← Units.val_pow_eq_pow_val]
    have : ((c ^ (orderOf c / p)) ^ j) ^ (2 ^ f + 1) = 1 := by
      rw [← pow_mul, ← pow_mul,
        show orderOf c / p * (j * (2 ^ f + 1)) = (2 ^ f + 1) * (orderOf c / p * j) by ring,
        pow_mul, hcq', one_pow]
    rw [this, Units.val_one]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hdiag : ∀ y : Fin m → ZMod p, torusDiag ζ m y ∈ StatedSU (m + 3) (2 ^ f) K := by
    intro y
    refine Subgroup.subset_closure ⟨det_torusDiag hodd hζ y, ?_⟩
    rw [torusDiag, coe_diagGL, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    rw [← pow_succ, hζq]
  have hswap : ∀ a b : Fin (m + 3),
      permGL (K := K) (Equiv.swap a b) ∈ StatedSU (m + 3) (2 ^ f) K := by
    intro a b
    refine Subgroup.subset_closure ⟨det_permGL_swap h2 a b, ?_⟩
    have hmap : ((permGL (Equiv.swap a b) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K).map (· ^ (2 ^ f)) =
        ((permGL (Equiv.swap a b) : GL (Fin (m + 3)) K) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) K) := by
      ext i j
      rw [Matrix.map_apply]
      rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp
    rw [hmap]
    exact permGL_swap_transpose_mul a b
  have := le_localRank_of_surviving_scalar (K := K)
    (H := CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K (m + 3)) m hζ hdiag hswap B hB
    ⟨c, hc⟩ hzB hzp
  simpa using this

end Groups

end CFSG.RankThree.Classical
