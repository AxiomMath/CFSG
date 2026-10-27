module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Vol2.Ch10SecQ34MJ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ)

theorem exists_herm_hom {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {Z : Subgroup V}
    {π : ↥(StatedSL 2 K) →* ↥H} (hπ : (FFModel.twistTensor a (StatedSL 2 K)).RealizesVia H ⊤ Z π) :
    ∃ B : V →* ↥(hermSub a (Fin 2) K), Function.Surjective B ∧ (∀ w, B w = 1 ↔ w ∈ Z) ∧
      ∀ (γ : ↥(StatedSL 2 K)) (w : V),
        ((B (((π γ : ↥H) : MulAut V) w) : ↥(hermSub a (Fin 2) K)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) K)) = twistAct a (StatedSL 2 K) γ (B w) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap rfl hπ
  let g : V → ↥(hermSub a (Fin 2) K) := fun w =>
    ⟨(((f ⟨w, Subgroup.mem_top w⟩ : ↥(FFModel.twistTensor a (StatedSL 2 K)).sec) :
      (FFModel.twistTensor a (StatedSL 2 K)).Amb) : Multiplicative (Matrix (Fin 2) (Fin 2) K)),
      (f ⟨w, Subgroup.mem_top w⟩).2⟩
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Subtype.val (map_one f)
  · intro x y
    apply Subtype.ext
    exact congrArg Subtype.val (map_mul f ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩)
  · intro m
    obtain ⟨u, hu⟩ := hfs ⟨(m : Multiplicative (Matrix (Fin 2) (Fin 2) K)), m.2⟩
    refine ⟨u, Subtype.ext ?_⟩
    exact congrArg Subtype.val hu
  · intro w
    rw [← hfk ⟨w, Subgroup.mem_top w⟩]
    constructor
    · intro h
      exact Subtype.ext (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (congrArg Subtype.val h)
  · intro γ w
    exact hfe γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)

omit [CharP K 2] in
theorem det_um (t : K) : (um t).det = 1 := by
  simp [um, Matrix.det_fin_two_of]

theorem det_wm : (wm : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [wm, Matrix.det_fin_two_of, CharTwo.neg_eq]

@[expose] noncomputable def uSL (t : K) : ↥(StatedSL 2 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (um t) (by rw [det_um]; exact one_ne_zero),
    Subgroup.subset_closure (det_um t)⟩

@[expose] noncomputable def wSL : ↥(StatedSL 2 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero wm (by rw [det_wm]; exact one_ne_zero),
    Subgroup.subset_closure det_wm⟩

@[expose] def dm (l : Kˣ) : Matrix (Fin 2) (Fin 2) K := !![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)]

omit [CharP K 2] in
theorem det_dm (l : Kˣ) : (dm l).det = 1 := by
  simp [dm, Matrix.det_fin_two_of]

@[expose] noncomputable def dSL (l : Kˣ) : ↥(StatedSL 2 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (dm l) (by rw [det_dm]; exact one_ne_zero),
    Subgroup.subset_closure (det_dm l)⟩

omit [CharP K 2] in
theorem coe_uSL (t : K) :
    (((uSL t : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = um t := rfl

theorem coe_wSL :
    (((wSL : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = wm := rfl

omit [CharP K 2] in
theorem tw_d_e11 (l : Kˣ) (c : K) :
    tw a (dm l) (e11 c) = e11 ((l : K) * (l : K) ^ 2 ^ a * c) := by
  have h2 : (2 ^ a : ℕ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, dm, e11, frobPow, Matrix.mul_apply, Fin.sum_univ_two, zero_pow h2]
  ring

omit [CharP K 2] in
theorem isHerm_e11_one : IsHerm a (e11 (1 : K)) := by
  have h2 : (2 ^ a : ℕ) ≠ 0 := by positivity
  rw [isHerm_iff]
  simp [e11, zero_pow h2]

theorem factCommOrth_aux [Finite K] {V : Type} [CommGroup V] {H A : Subgroup (MulAut V)}
    {Z : Subgroup V} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpH : ¬ p ∣ Nat.card H)
    (hA : IsPGroup p A) {x : MulAut V} (hx : x ∈ A) {π : ↥(StatedSL 2 K) →* ↥H}
    {B : V →* ↥(hermSub a (Fin 2) K)} (hBs : Function.Surjective B)
    (hBk : ∀ w, B w = 1 ↔ w ∈ Z)
    (hBe : ∀ (γ : ↥(StatedSL 2 K)) (w : V),
      ((B (((π γ : ↥H) : MulAut V) w) : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) = twistAct a (StatedSL 2 K) γ (B w))
    {Y : ↥(hermSub a (Fin 2) K) →* ↥(hermSub a (Fin 2) K)} (hY' : ∀ w, Y (B w) = B (x w))
    {μ : K} (hμq : μ ^ 2 ^ a = μ)
    (hYμ : ∀ m : ↥(hermSub a (Fin 2) K),
      Multiplicative.toAdd ((Y m : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        μ • Multiplicative.toAdd (m : Multiplicative (Matrix (Fin 2) (Fin 2) K))) (v : V) :
    x v * v⁻¹ ∈ Z := by
  have hit : ∀ (k : ℕ) (w : V), Y^[k] (B w) = B ((x ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [Function.iterate_succ_apply, hY', ih, pow_succ, MulAut.mul_apply]
  have hitμ : ∀ (k : ℕ) (m : ↥(hermSub a (Fin 2) K)),
      Multiplicative.toAdd ((Y^[k] m : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        μ ^ k • Multiplicative.toAdd (m : Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [Function.iterate_succ_apply, ih, hYμ, smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨w₀, hw₀⟩ := hBs ⟨Multiplicative.ofAdd (e11 1), isHerm_e11_one a⟩
  have hμ1 : μ ^ p ^ k = 1 := by
    have h1 := hit (p ^ k) w₀
    rw [hxk, MulAut.one_apply, hw₀] at h1
    have h2 := congrArg (fun z => z 0 0) (hitμ (p ^ k) ⟨Multiplicative.ofAdd (e11 1),
      isHerm_e11_one a⟩)
    simp only [h1, toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul] at h2
    simpa [e11] using h2.symm
  have hμ' : μ = 1 := by
    by_contra hne
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, zero_pow (pow_ne_zero k hp.ne_zero)] at hμ1
      exact zero_ne_one hμ1
    set l : Kˣ := Units.mk0 μ hμ0 with hl
    have hlk : l ^ p ^ k = 1 := Units.ext (by simp [hl, hμ1])
    have hl1 : l ≠ 1 := fun h => hne (by simpa [hl] using congrArg Units.val h)
    have hpl : p ∣ orderOf l := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hlk)
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hl1
      · rw [hj]
        exact dvd_pow_self p (Nat.succ_ne_zero j)
    set t := dSL l with ht
    have hBpow : ∀ (r : ℕ) (w : V),
        ((B ((((π t) ^ r : ↥H) : MulAut V) w) : ↥(hermSub a (Fin 2) K)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        (twistAct a (StatedSL 2 K) t)^[r] (B w) := by
      intro r
      induction r with
      | zero => intro w; simp
      | succ r ih =>
        intro w
        calc ((B ((((π t) ^ (r + 1) : ↥H) : MulAut V) w) : ↥(hermSub a (Fin 2) K)) :
              Multiplicative (Matrix (Fin 2) (Fin 2) K))
            = ((B ((((π t) ^ r : ↥H) : MulAut V) (((π t : ↥H) : MulAut V) w)) :
                ↥(hermSub a (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
              rw [pow_succ, Subgroup.coe_mul, MulAut.mul_apply]
          _ = (twistAct a (StatedSL 2 K) t)^[r] (B (((π t : ↥H) : MulAut V) w)) := ih _
          _ = (twistAct a (StatedSL 2 K) t)^[r] (twistAct a (StatedSL 2 K) t (B w)) :=
              congrArg _ (hBe t w)
          _ = (twistAct a (StatedSL 2 K) t)^[r + 1] (B w) :=
              (Function.iterate_succ_apply _ _ _).symm
    have hTpow : ∀ (r : ℕ) (c : K), (twistAct a (StatedSL 2 K) t)^[r]
        (Multiplicative.ofAdd (e11 c)) = Multiplicative.ofAdd (e11 ((μ * μ) ^ r * c)) := by
      intro r
      induction r with
      | zero => intro c; simp
      | succ r ih =>
        intro c
        rw [Function.iterate_succ_apply', ih]
        change Multiplicative.ofAdd (tw a (dm l) (e11 _)) = _
        rw [tw_d_e11, hl, Units.val_mk0, hμq, pow_succ']
        congr 2
        ring
    have hord : p ∣ orderOf (π t) := by
      have h1 : ((((π t) ^ orderOf (π t) : ↥H) : MulAut V) w₀) = w₀ := by
        rw [pow_orderOf_eq_one]
        rfl
      have h2 := (congrArg (fun w => ((B w : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K))) h1).symm.trans (hBpow (orderOf (π t)) w₀)
      rw [hw₀] at h2
      change Multiplicative.ofAdd (e11 1) = _ at h2
      rw [hTpow, mul_one] at h2
      have h3 := congrArg
        (fun z : Multiplicative (Matrix (Fin 2) (Fin 2) K) => Multiplicative.toAdd z 0 0) h2
      simp only [toAdd_ofAdd, e11, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h3
      have h4 : l ^ (2 * orderOf (π t)) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, hl, Units.val_mk0, pow_mul, sq, ← h3]
      have h6 := hpl.trans (orderOf_dvd_of_pow_eq_one h4)
      rcases (Nat.Prime.dvd_mul hp).mp h6 with h7 | h7
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h7) hp2
      · exact h7
    exact hpH (hord.trans (orderOf_dvd_natCard _))
  have h := hYμ (B v)
  rw [hY', hμ', one_smul] at h
  have h2 : B (x v) = B v := Subtype.ext (Multiplicative.toAdd.injective h)
  have h3 : B (x v * v⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  exact (hBk _).mp h3

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
