module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix CFSG.RankThree.PartTwo.Census
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def liftTheta {G H : Type*} [CommGroup G] [CommGroup H] (ι : H →* G) (k : ℕ) :
    G × (Fin k → H) →* (Fin (k + 1) → G) where
  toFun x j := x.1 * Fin.cases 1 (fun i => ι (x.2 i)) j
  map_one' := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  map_mul' x y := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Fin.cases_succ, map_mul]
      exact mul_mul_mul_comm _ _ _ _

theorem liftTheta_zero {G H : Type*} [CommGroup G] [CommGroup H] (ι : H →* G) (k : ℕ)
    (x : G × (Fin k → H)) : liftTheta ι k x 0 = x.1 := by
  change x.1 * Fin.cases 1 (fun i => ι (x.2 i)) 0 = _
  simp

theorem liftTheta_succ {G H : Type*} [CommGroup G] [CommGroup H] (ι : H →* G) (k : ℕ)
    (x : G × (Fin k → H)) (i : Fin k) : liftTheta ι k x i.succ = x.1 * ι (x.2 i) := by
  change x.1 * Fin.cases 1 (fun i => ι (x.2 i)) i.succ = _
  simp

theorem gcd_pow_two_eq {r n : ℕ} (hr : r.Prime) (hrn : r ∣ n) (hrn2 : ¬ r ^ 2 ∣ n) :
    Nat.gcd n (r ^ 2) = r := by
  obtain ⟨g, hg⟩ := Nat.dvd_gcd hrn (dvd_pow_self r two_ne_zero)
  have hgr : g ∣ r := by
    have h1 : r * g ∣ r * r := by
      rw [← hg, ← sq]
      exact Nat.gcd_dvd_right _ _
    exact (Nat.mul_dvd_mul_iff_left hr.pos).mp h1
  rcases hr.eq_one_or_self_of_dvd g hgr with h1 | h1
  · rw [hg, h1, mul_one]
  · exfalso
    apply hrn2
    have h2 := Nat.gcd_dvd_left n (r ^ 2)
    rwa [hg, h1, ← sq] at h2

theorem isElemAbelian_range_of_pow {A H : Type*} [CommGroup A] [Group H] {p : ℕ} (φ : A →* H)
    (hA : ∀ a : A, φ (a ^ p) = 1) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : H) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨v, rfl⟩ := hx
    rw [← map_pow, hA]

theorem rootsOfUnity_val_pow {m : ℕ} (x : rootsOfUnity m K) : ((x : Kˣ) : K) ^ m = 1 :=
  (mem_rootsOfUnity' m (x : Kˣ)).mp x.2

@[expose] def liftEntries (m k n : ℕ) (K : Type) [Field K] :
    (Fin (k + 1) → rootsOfUnity m K) →* (Fin n → Kˣ) :=
  ((rootsOfUnity m K).subtype.compLeft (Fin n)).comp
    ((torusEntries (rootsOfUnity m K) (k + 2) n).comp (dupHom (rootsOfUnity m K) k))

theorem liftEntries_apply {m k n : ℕ} (s : Fin (k + 1) → rootsOfUnity m K) (i : Fin n) :
    liftEntries m k n K s i =
      ((torusEntries (rootsOfUnity m K) (k + 2) n (dupHom (rootsOfUnity m K) k s) i :
        rootsOfUnity m K) : Kˣ) :=
  rfl

theorem liftEntries_pow {m : ℕ} (k n : ℕ) (s : Fin (k + 1) → rootsOfUnity m K) (i : Fin n) :
    ((liftEntries m k n K s i : Kˣ) : K) ^ m = 1 := by
  rw [liftEntries_apply]
  exact rootsOfUnity_val_pow _

theorem liftEntries_of_lt {m k n : ℕ} (s : Fin (k + 1) → rootsOfUnity m K) {l : Fin n}
    (hl : l.val < k + 2) :
    liftEntries m k n K s l = ((s ⟨l.val - 1, by omega⟩ : rootsOfUnity m K) : Kˣ) := by
  rw [liftEntries_apply, torusEntries_of_lt _ hl, dupHom_apply]

theorem liftEntries_of_lt_two {m k n : ℕ} (s : Fin (k + 1) → rootsOfUnity m K) {l : Fin n}
    (hl : l.val < 2) : liftEntries m k n K s l = ((s 0 : rootsOfUnity m K) : Kˣ) := by
  rw [liftEntries_of_lt s (by omega)]
  congr 2
  ext
  simp only [Fin.val_zero]
  omega

theorem liftEntries_of_eq {m k n : ℕ} (s : Fin (k + 1) → rootsOfUnity m K) {l : Fin n}
    (hl : l.val = k + 2) :
    liftEntries m k n K s l =
      (((∏ j, dupHom (rootsOfUnity m K) k s j)⁻¹ : rootsOfUnity m K) : Kˣ) := by
  rw [liftEntries_apply, torusEntries_of_eq _ hl]

theorem diagGL_liftEntries_mem {p f : ℕ} (h : UnitaryFieldData p f K) {m : ℕ}
    (hm : m ∣ p ^ f + 1) {k n : ℕ} (hkn : k + 2 < n) (s : Fin (k + 1) → rootsOfUnity m K) :
    diagGL n K (liftEntries m k n K s) ∈ StatedSU n (p ^ f) K := by
  refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
  · rw [coe_diagGL, det_diagonal, ← Units.coe_prod]
    have : ∏ i, liftEntries m k n K s i = (rootsOfUnity m K).subtype
        (∏ i, torusEntries (rootsOfUnity m K) (k + 2) n (dupHom (rootsOfUnity m K) k s) i) := by
      rw [map_prod]
      rfl
    rw [this, prod_torusEntries hkn, map_one, Units.val_one]
  · rw [coe_diagGL, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      ← diagonal_one]
    refine congrArg diagonal (funext fun i => ?_)
    obtain ⟨c, hc⟩ := hm
    rw [h.bar_apply, ← pow_succ, hc, pow_mul, liftEntries_pow, one_pow]

@[expose] noncomputable def liftTorus {p f : ℕ} (h : UnitaryFieldData p f K) {m : ℕ}
    (hm : m ∣ p ^ f + 1) {k n : ℕ} (hkn : k + 2 < n) :
    (Fin (k + 1) → rootsOfUnity m K) →* StatedSU n (p ^ f) K :=
  ((diagGL n K).comp (liftEntries m k n K)).codRestrict _ (diagGL_liftEntries_mem h hm hkn)

theorem coe_liftTorus {p f : ℕ} (h : UnitaryFieldData p f K) {m : ℕ}
    (hm : m ∣ p ^ f + 1) {k n : ℕ} (hkn : k + 2 < n) (s : Fin (k + 1) → rootsOfUnity m K) :
    (((liftTorus h hm hkn s : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => ((liftEntries m k n K s i : Kˣ) : K) :=
  rfl

@[expose] def liftSwap [Finite K] [CharP K 2] {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ}
    (hn : 2 ≤ n) : StatedSU n (p ^ f) K :=
  ⟨swapGL hn, swapGL_mem_statedSU h hn⟩

theorem liftTorus_mul_swap [Finite K] [CharP K 2] {p f : ℕ} (h : UnitaryFieldData p f K)
    {m : ℕ} (hm : m ∣ p ^ f + 1) {k n : ℕ} (hkn : k + 2 < n)
    (s : Fin (k + 1) → rootsOfUnity m K) :
    liftTorus h hm hkn s * liftSwap h (by omega : 2 ≤ n) =
      liftSwap h (by omega : 2 ≤ n) * liftTorus h hm hkn s := by
  refine Subtype.ext (Units.ext ?_)
  change ((liftTorus h hm hkn s : StatedSU n (p ^ f) K) : GL (Fin n) K).1 * (1 + swapBlock n K) =
    (1 + swapBlock n K) * ((liftTorus h hm hkn s : StatedSU n (p ^ f) K) : GL (Fin n) K).1
  rw [coe_liftTorus]
  refine diagonal_mul_swap fun i j hi hj => ?_
  rw [liftEntries_of_lt_two s hi, liftEntries_of_lt_two s hj]

@[expose] def liftInc (r : ℕ) (K : Type) [Field K] : rootsOfUnity r K →* rootsOfUnity (r ^ 2) K :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd (dvd_pow_self r two_ne_zero))

theorem liftInc_injective (r : ℕ) : Function.Injective (liftInc r K) :=
  Subgroup.inclusion_injective _

@[expose] noncomputable def liftPhi {p f : ℕ} (h : UnitaryFieldData p f K) {r : ℕ}
    (hrq : r ^ 2 ∣ p ^ f + 1) (k : ℕ) :
    rootsOfUnity (r ^ 2) K × (Fin k → rootsOfUnity r K) →*
      StatedProj (StatedSU (k + 3) (p ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin (k + 3)) K).subgroupOf
      (StatedSU (k + 3) (p ^ f) K))).comp
    ((liftTorus h hrq (k := k) (n := k + 3) (by omega)).comp (liftTheta (liftInc r K) k))

theorem liftEntries_const {r k : ℕ} (hrn : r ∣ k + 3) (a : rootsOfUnity (r ^ 2) K)
    (hb : a ^ r = 1) (i : Fin (k + 3)) :
    liftEntries (r ^ 2) k (k + 3) K (fun _ => a) i = (a : Kˣ) := by
  by_cases hi : i.val < k + 2
  · rw [liftEntries_of_lt _ hi]
  · have hi' : i.val = k + 2 := by omega
    rw [liftEntries_of_eq _ hi']
    have hpow : a ^ (k + 3) = 1 := by
      obtain ⟨u, hu⟩ := hrn
      rw [hu, pow_mul, hb, one_pow]
    have hprod : ∏ j, dupHom (rootsOfUnity (r ^ 2) K) k (fun _ => a) j = a ^ (k + 2) := by
      have hj : ∀ j : Fin (k + 2), dupHom (rootsOfUnity (r ^ 2) K) k (fun _ => a) j = a :=
        fun _ => rfl
      simp only [hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod, inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hpow)]

theorem liftPhi_eq_one_iff {p f : ℕ} (h : UnitaryFieldData p f K) {r : ℕ} (hr : r.Prime)
    (hrq : r ^ 2 ∣ p ^ f + 1) {k : ℕ} (hrn : r ∣ k + 3) (hrn2 : ¬ r ^ 2 ∣ k + 3)
    (a : rootsOfUnity (r ^ 2) K) (α : Fin k → rootsOfUnity r K) :
    liftPhi h hrq k (a, α) = 1 ↔ α = 1 ∧ a ^ r = 1 := by
  have hkn : k + 2 < k + 3 := by omega
  constructor
  · intro hΦ
    set s := liftTheta (liftInc r K) k (a, α) with hs
    have hZ : liftTorus h hrq hkn s ∈ (StatedScalars (Fin (k + 3)) K).subgroupOf
        (StatedSU (k + 3) (p ^ f) K) :=
      (QuotientGroup.eq_one_iff (liftTorus h hrq hkn s)).mp hΦ
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hZ
    have hc' : GeneralLinearGroup.scalar (Fin (k + 3)) c =
        ((liftTorus h hrq hkn s : StatedSU (k + 3) (p ^ f) K) : GL (Fin (k + 3)) K) := hc
    have hci : ∀ i : Fin (k + 3), c = liftEntries (r ^ 2) k (k + 3) K s i := by
      intro i
      have := congrArg (fun A : GL (Fin (k + 3)) K =>
        (A : Matrix (Fin (k + 3)) (Fin (k + 3)) K) i i) hc'
      refine Units.ext ?_
      simpa only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        coe_liftTorus] using this
    have hc0 : c = (a : Kˣ) := by
      rw [hci ⟨0, by omega⟩, liftEntries_of_lt_two s (by simp), hs, liftTheta_zero]
    refine ⟨funext fun i => ?_, ?_⟩
    · have h1 := hci ⟨i.val + 2, by omega⟩
      rw [liftEntries_of_lt s (by simp), hc0] at h1
      have h2 : (⟨(⟨i.val + 2, by omega⟩ : Fin (k + 3)).val - 1, by simp⟩ : Fin (k + 1)) =
          i.succ := Fin.ext (by simp)
      rw [h2, hs, liftTheta_succ] at h1
      have h3 : (a : Kˣ) * (α i : Kˣ) = (a : Kˣ) := h1.symm
      exact Subtype.ext (mul_eq_left.mp h3)
    · have hcn : (c : K) ^ (k + 3) = 1 := by
        have hdet := ((mem_unitarySU_iff h).mp (liftTorus h hrq hkn s).2).1
        rw [← hc', GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
        exact hdet
      rw [hc0] at hcn
      have hg : ((a : Kˣ) : K) ^ Nat.gcd (k + 3) (r ^ 2) = 1 :=
        pow_gcd_eq_one.mpr ⟨hcn, rootsOfUnity_val_pow a⟩
      rw [gcd_pow_two_eq hr hrn hrn2] at hg
      refine Subtype.ext (Units.ext ?_)
      simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using hg
  · rintro ⟨rfl, hb⟩
    refine (QuotientGroup.eq_one_iff (liftTorus h hrq hkn _)).mpr
      (Subgroup.mem_subgroupOf.mpr ⟨(a : Kˣ), ?_⟩)
    refine Units.ext ?_
    have hs : liftTheta (liftInc r K) k (a, (1 : Fin k → rootsOfUnity r K)) = fun _ => a := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [liftTheta_zero]
      · rw [liftTheta_succ]
        simp
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_liftTorus, hs]
    exact congrArg diagonal (funext fun i => by rw [liftEntries_const hrn a hb i])

theorem card_rootsOfUnity_of_dvd_succ [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K) {m : ℕ}
    [NeZero m] (hm : m ∣ p ^ f + 1) : Nat.card (rootsOfUnity m K) = m := by
  refine CFSG.LinearGroups.card_rootsOfUnity_of_dvd ?_
  rw [h.card, pow_mul', sq, show p ^ f * p ^ f - 1 = p ^ f * p ^ f - 1 * 1 by rw [mul_one],
    Nat.mul_self_sub_mul_self_eq]
  exact dvd_mul_of_dvd_left hm _

theorem card_ker_liftPhi [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K) {r : ℕ}
    (hr : r.Prime) (hrq : r ^ 2 ∣ p ^ f + 1) {k : ℕ} (hrn : r ∣ k + 3)
    (hrn2 : ¬ r ^ 2 ∣ k + 3) : Nat.card (liftPhi h hrq k).ker = r := by
  have : NeZero r := ⟨hr.ne_zero⟩
  have hμ₁ : Nat.card (rootsOfUnity r K) = r :=
    card_rootsOfUnity_of_dvd_succ h ((dvd_pow_self r two_ne_zero).trans hrq)
  set κ : rootsOfUnity r K →* rootsOfUnity (r ^ 2) K × (Fin k → rootsOfUnity r K) :=
    (MonoidHom.inl _ _).comp (liftInc r K) with hκdef
  have hκ : Function.Injective κ := fun x y hxy => liftInc_injective r (congrArg Prod.fst hxy)
  have hker : (liftPhi h hrq k).ker = κ.range := by
    ext ⟨a, α⟩
    rw [MonoidHom.mem_ker, liftPhi_eq_one_iff h hr hrq hrn hrn2, MonoidHom.mem_range]
    constructor
    · rintro ⟨rfl, hb⟩
      refine ⟨⟨(a : Kˣ), (mem_rootsOfUnity r _).mpr (congrArg Subtype.val hb)⟩, ?_⟩
      exact Prod.ext (Subtype.ext rfl) rfl
    · rintro ⟨b, hb⟩
      have h1 : liftInc r K b = a := congrArg Prod.fst hb
      have h2 : (1 : Fin k → rootsOfUnity r K) = α := congrArg Prod.snd hb
      refine ⟨h2.symm, ?_⟩
      rw [← h1, ← map_pow, rootsOfUnity_pow_eq_one, map_one]
  rw [hker, ← Nat.card_congr (MonoidHom.ofInjective hκ).toEquiv]
  exact hμ₁

theorem card_range_liftPhi [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K) {r : ℕ}
    (hr : r.Prime) (hrq : r ^ 2 ∣ p ^ f + 1) {k : ℕ} (hrn : r ∣ k + 3)
    (hrn2 : ¬ r ^ 2 ∣ k + 3) : Nat.card (liftPhi h hrq k).range = r ^ (k + 1) := by
  have : NeZero r := ⟨hr.ne_zero⟩
  have : NeZero (r ^ 2) := ⟨pow_ne_zero 2 hr.ne_zero⟩
  have hμ₁ : Nat.card (rootsOfUnity r K) = r :=
    card_rootsOfUnity_of_dvd_succ h ((dvd_pow_self r two_ne_zero).trans hrq)
  have hμ₂ : Nat.card (rootsOfUnity (r ^ 2) K) = r ^ 2 := card_rootsOfUnity_of_dvd_succ h hrq
  have h1 := Subgroup.card_ker_mul_card_range (liftPhi h hrq k)
  rw [card_ker_liftPhi h hr hrq hrn hrn2, Nat.card_prod, hμ₂, card_fun_rootsOfUnity hμ₁] at h1
  refine Nat.eq_of_mul_eq_mul_left hr.pos ?_
  rw [h1]
  ring

theorem liftPhi_pow_eq_one {p f : ℕ} (h : UnitaryFieldData p f K) {r : ℕ} (hr : r.Prime)
    (hrq : r ^ 2 ∣ p ^ f + 1) {k : ℕ} (hrn : r ∣ k + 3) (hrn2 : ¬ r ^ 2 ∣ k + 3)
    (g : rootsOfUnity (r ^ 2) K × (Fin k → rootsOfUnity r K)) :
    liftPhi h hrq k (g ^ r) = 1 := by
  obtain ⟨a, α⟩ := g
  change liftPhi h hrq k (a ^ r, α ^ r) = 1
  rw [liftPhi_eq_one_iff h hr hrq hrn hrn2]
  refine ⟨funext fun i => ?_, ?_⟩
  · rw [Pi.pow_apply, rootsOfUnity_pow_eq_one, Pi.one_apply]
  · rw [← pow_mul, ← sq]
    exact rootsOfUnity_pow_eq_one a

theorem liftSwap_sq [Finite K] [CharP K 2] {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ}
    (hn : 2 ≤ n) : liftSwap h hn ^ 2 = 1 :=
  Subtype.ext (Units.ext (by
    rw [pow_two]
    exact one_add_mul_one_add (swapBlock_mul_self hn)))

theorem liftSwap_not_mem [Finite K] [CharP K 2] {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ}
    (hn : 2 ≤ n) :
    liftSwap h hn ∉ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) := by
  intro htZ
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp htZ
  have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
    ⟨1, by omega⟩) hc
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, liftSwap, coe_swapGL, swapBlock,
    Matrix.add_apply, of_apply, Matrix.one_apply] at this
  simp at this

theorem le_localRank_statedSU_lift [Finite K] [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K)
    {r n : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2) (hrq : r ^ 2 ∣ 2 ^ f + 1) (hrn : r ∣ n)
    (hrn2 : ¬ r ^ 2 ∣ n) (hn : 4 ≤ n) :
    n - 2 ≤ localRank r (StatedProj (StatedSU n (2 ^ f) K)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hn2 : 2 ≤ k + 3 := by omega
  have hkn : k + 2 < k + 3 := by omega
  set Z := (StatedScalars (Fin (k + 3)) K).subgroupOf (StatedSU (k + 3) (2 ^ f) K) with hZ
  have hc := card_range_liftPhi h hr hrq hrn hrn2
  have hE : IsElemAbelian r (liftPhi h hrq k).range :=
    isElemAbelian_range_of_pow _ (liftPhi_pow_eq_one h hr hrq hrn hrn2)
  have ht2 : liftSwap h hn2 ^ 2 ∈ Z := by
    rw [liftSwap_sq h hn2]
    exact Z.one_mem
  have hEt : ∀ x ∈ (liftPhi h hrq k).range,
      x * QuotientGroup.mk' Z (liftSwap h hn2) = QuotientGroup.mk' Z (liftSwap h hn2) * x := by
    rintro _ ⟨g, rfl⟩
    have hg : liftPhi h hrq k g =
        QuotientGroup.mk' Z (liftTorus h hrq hkn (liftTheta (liftInc r K) k g)) := rfl
    rw [hg, ← map_mul, ← map_mul, liftTorus_mul_swap h hrq hkn]
  have key := le_localRank_of_commute_involution hr
    (orderOf_mk_eq_two Z (liftSwap_not_mem h hn2) ht2) hE hc hEt
  have e : k + 3 - 2 = k + 1 := by omega
  rw [e]
  exact key

end CFSG.RankThree.PartOne.KFU
