module

public import CFSG.LocalAnalysis.StandardType.GGKGPosSULevi
import Mathlib.Tactic.Group
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType.KGPosSU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section Separate

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

theorem isBlk_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : ζ ^ p = 1)
    (hζ1 : ζ ≠ 1) {blk : Fin n → ℕ} {κ κ' : Fin n → ℤ}
    (hsep : ∀ a b, a ≠ b → ¬(blk a = blk b ∧ blk a ≠ 0) → κ a ≠ κ b ∨ κ' a ≠ κ' b)
    (hbd : ∀ a, -1 ≤ κ a ∧ κ a ≤ 1 ∧ -1 ≤ κ' a ∧ κ' a ≤ 1) {x x' g : SU σ n}
    (hx : mat σ n x = Matrix.diagonal fun a => ζ ^ κ a)
    (hx' : mat σ n x' = Matrix.diagonal fun a => ζ ^ κ' a) (hgx : x * g = g * x)
    (hgx' : x' * g = g * x') {m : ℕ} (hg : g ^ 2 ^ m = 1) : IsBlk blk (mat σ n g) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have hne : ∀ {u v : ℤ}, -1 ≤ u → u ≤ 1 → -1 ≤ v → v ≤ 1 → u ≠ v → ζ ^ u ≠ ζ ^ v := by
    intro u v hu1 hu2 hv1 hv2 huv h
    have h' : ζ ^ (u - v) = 1 := by rw [zpow_sub₀ hζ0, h, div_self (zpow_ne_zero _ hζ0)]
    exact zpow_ne_one_of_pow_eq_one hp hp2 hζ hζ1 (sub_ne_zero.mpr huv) (by omega) (by omega) h'
  have hzero : ∀ a b, a ≠ b → ¬(blk a = blk b ∧ blk a ≠ 0) → mat σ n g a b = 0 := by
    intro a b hab h
    obtain ⟨ha1, ha2, ha3, ha4⟩ := hbd a
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbd b
    rcases hsep a b hab h with h1 | h1
    · exact mat_apply_eq_zero_of_commute hx hgx (hne ha1 ha2 hb1 hb2 h1)
    · exact mat_apply_eq_zero_of_commute hx' hgx' (hne ha3 ha4 hb3 hb4 h1)
  intro a b h
  by_cases hab : a = b
  · subst hab
    have ha0 : blk a = 0 := by
      by_contra h0
      exact h ⟨rfl, h0⟩
    have hcol : ∀ r, r ≠ a → mat σ n g r a = 0 := fun r hr =>
      hzero r a hr fun h' => h'.2 (h'.1.trans ha0)
    have hpow := pow_apply_self_of_col hcol (2 ^ m)
    rw [← map_pow, hg, map_one, Matrix.one_apply_eq] at hpow
    rw [Matrix.one_apply_eq]
    exact eq_one_of_pow_char_pow_eq_one 2 hpow.symm
  · rw [Matrix.one_apply_ne hab]
    exact hzero a b hab h

theorem det_toBlock_eq_one {blk : Fin n → ℕ} {p q : Fin n} (hpq : p ≠ q)
    (hblk : ∀ c, blk c = blk p → c = p ∨ c = q) (hqp : blk q = blk p)
    {M : Matrix (Fin n) (Fin n) F} (hM : IsBlk blk M) {m : ℕ} (hMm : M ^ 2 ^ m = 1) :
    (toBlock p q M).det = 1 := by
  have hpow : ∀ N : ℕ, toBlock p q (M ^ N) = toBlock p q M ^ N := by
    intro N
    induction N with
    | zero => rw [pow_zero, pow_zero, toBlock_one hpq]
    | succ N ih => rw [pow_succ', pow_succ', toBlock_mul hpq hblk hqp hM, ih]
  have h := congrArg Matrix.det (hpow (2 ^ m))
  rw [hMm, toBlock_one hpq, Matrix.det_one, Matrix.det_pow] at h
  exact eq_one_of_pow_char_pow_eq_one 2 h.symm

theorem mem_rankOne_of_commute_short (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : ζ ^ p = 1)
    (hζ1 : ζ ≠ 1) {κ κ' : Fin n → ℤ}
    (hsep : ∀ a b, a ≠ b → ¬(blkShort k hk a = blkShort k hk b ∧ blkShort k hk a ≠ 0) →
      κ a ≠ κ b ∨ κ' a ≠ κ' b)
    (hbd : ∀ a, -1 ≤ κ a ∧ κ a ≤ 1 ∧ -1 ≤ κ' a ∧ κ' a ≤ 1) {x x' g : SU σ n}
    (hx : mat σ n x = Matrix.diagonal fun a => ζ ^ κ a)
    (hx' : mat σ n x' = Matrix.diagonal fun a => ζ ^ κ' a) (hgx : x * g = g * x)
    (hgx' : x' * g = g * x') {m : ℕ} (hg : g ^ 2 ^ m = 1) :
    g ∈ rankOne (rootGroup σ hσ n) k := by
  have hblk := isBlk_of_commute hp hp2 hζ hζ1 hsep hbd hx hx' hgx hgx' hg
  refine mem_rankOne_of_isBlk_short hσ hk hblk ?_
  refine det_toBlock_eq_one (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk) hblk
    (m := m) ?_
  rw [← map_pow, hg, map_one]

theorem mem_rankOne_of_commute_last (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) (he : Even n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) {κ κ' : Fin n → ℤ}
    (hsep : ∀ a b, a ≠ b → ¬(blkLast k a = blkLast k b ∧ blkLast k a ≠ 0) →
      κ a ≠ κ b ∨ κ' a ≠ κ' b)
    (hbd : ∀ a, -1 ≤ κ a ∧ κ a ≤ 1 ∧ -1 ≤ κ' a ∧ κ' a ≤ 1) {x x' g : SU σ n}
    (hx : mat σ n x = Matrix.diagonal fun a => ζ ^ κ a)
    (hx' : mat σ n x' = Matrix.diagonal fun a => ζ ^ κ' a) (hgx : x * g = g * x)
    (hgx' : x' * g = g * x') {m : ℕ} (hg : g ^ 2 ^ m = 1) :
    g ∈ rankOne (rootGroup σ hσ n) k := by
  have hblk := isBlk_of_commute hp hp2 hζ hζ1 hsep hbd hx hx' hgx hgx' hg
  refine mem_rankOne_of_isBlk_last hσ hk he hblk ?_
  refine det_toBlock_eq_one (lowIdx_ne_rev k k) (blkLast_hblk_even he) (by
    rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))]) hblk (m := m) ?_
  rw [← map_pow, hg, map_one]

theorem mul_self_eq_one_of_mem_short (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n (Pi.single k 1) ∨ x ∈ rootGroup σ hσ n (-Pi.single k 1)) :
    x * x = 1 := by
  have hxL : x ∈ rankOne (rootGroup σ hσ n) k :=
    hx.elim Subgroup.mem_sup_left Subgroup.mem_sup_right
  refine eq_one_of_toBlock_short hk (mul_mem hxL hxL) ?_
  rw [map_mul, toBlock_mul (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk)
    (isBlk_short_of_mem hk hxL).1]
  rcases hx with hx | hx
  · rw [toBlock_of_mem_pos hk hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  · rw [toBlock_of_mem_neg hk hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem mul_self_eq_one_of_mem_last (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) (he : Even n) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n (Pi.single k 1) ∨ x ∈ rootGroup σ hσ n (-Pi.single k 1)) :
    x * x = 1 := by
  have hxL : x ∈ rankOne (rootGroup σ hσ n) k :=
    hx.elim Subgroup.mem_sup_left Subgroup.mem_sup_right
  have hpp := lowIdx_ne_rev (n := n) k k
  have hblk := isBlk_last_of_mem hk hxL
  refine eq_one_of_isBlk_last he (by rw [map_mul]; exact hblk.mul hblk) ?_
  rw [map_mul, toBlock_mul hpp (blkLast_hblk_even he) (by
    rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))]) hblk]
  rcases hx with hx | hx
  · have hne : toStd n (Pi.single k 1) ≠ 0 := by
      rw [toStd_last_even hk he]
      intro h
      exact weight_ne_zero hpp (two_nsmul_injective' (by rw [h, smul_zero]))
    have h1 := mat_apply_self_of_mem_rootGroup hσ hne hx (lowIdx k)
    have h2 := mat_apply_self_of_mem_rootGroup hσ hne hx (Fin.rev (lowIdx k))
    have h3 : mat σ n x (Fin.rev (lowIdx k)) (lowIdx k) = 0 :=
      mat_apply_of_weight_sub_eq_neg hσ hne hx (by rw [toStd_last_even hk he, weight_rev']; abel)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, CharTwo.add_self_eq_zero]
  · have hne : toStd n (-Pi.single k 1) ≠ 0 := by
      rw [toStd_neg_last_even hk he]
      intro h
      exact weight_ne_zero (rev_ne_rev_rev hpp) (two_nsmul_injective' (by rw [h, smul_zero]))
    have h1 := mat_apply_self_of_mem_rootGroup hσ hne hx (lowIdx k)
    have h2 := mat_apply_self_of_mem_rootGroup hσ hne hx (Fin.rev (lowIdx k))
    have h3 : mat σ n x (lowIdx k) (Fin.rev (lowIdx k)) = 0 :=
      mat_apply_of_weight_sub_eq_neg hσ hne hx (by
        rw [toStd_neg_last_even hk he, weight_rev']; abel)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem isBlk_commute_diagonal {blk : Fin n → ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : IsBlk blk M) {d : Fin n → F} (hd : ∀ a b, blk a = blk b → blk a ≠ 0 → d a = d b) :
    M * Matrix.diagonal d = Matrix.diagonal d * M := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : blk a = blk b ∧ blk a ≠ 0
  · rw [hd a b h.1 h.2, mul_comm]
  · rw [hM a b h]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · rw [Matrix.one_apply_ne hab, zero_mul, mul_zero]

theorem centralizer_map_conj {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, SetLike.mem_coe, forall_exists_index, and_imp]
  constructor
  · intro hz
    refine ⟨g⁻¹ * z * g, fun h hh => ?_, by group⟩
    have h1 := hz _ h hh rfl
    calc h * (g⁻¹ * z * g) = g⁻¹ * (g * h * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * h * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * z * g * h := by group
  · rintro ⟨z₀, hz₀, rfl⟩ _ h hh rfl
    have h1 := hz₀ h hh
    calc g * h * g⁻¹ * (g * z₀ * g⁻¹) = g * (h * z₀) * g⁻¹ := by group
      _ = g * (z₀ * h) * g⁻¹ := by rw [h1]
      _ = g * z₀ * g⁻¹ * (g * h * g⁻¹) := by group

end Separate

section Six

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hF : Nat.card F = (2 ^ f) ^ 2}
  {ν : GGWeyl (Unitary.rootDatum hF 6) →* SU (unitaryInvolution F 2 f) 6}

variable (ν) in
@[expose] noncomputable def diagFix (p : ℕ) (u : GGWeyl (Unitary.rootDatum hF 6)) :
    Subgroup (SU (unitaryInvolution F 2 f) 6) :=
  diagP F f p ⊓ Subgroup.centralizer {ν u}

theorem mem_diagFix {p : ℕ} {u : GGWeyl (Unitary.rootDatum hF 6)}
    {x : SU (unitaryInvolution F 2 f) 6} :
    x ∈ diagFix ν p u ↔ x ∈ diagP F f p ∧ x * ν u = ν u * x := by
  rw [diagFix, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem mem_diagFix_simple_iff (hν : GGWeylLift (Unitary.rootDatum hF 6) ν) {p : ℕ}
    (k : Fin (6 / 2)) {x : SU (unitaryInvolution F 2 f) 6} (hxP : x ∈ diagP F f p)
    {d : Fin 6 → F} (hx : mat _ 6 x = Matrix.diagonal d) :
    x ∈ diagFix ν p ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) ↔
      ∀ r, d ((levelPerm k).symm r) = d r := by
  have hc := mat_conj_simple hF hν k hx
  rw [mem_diagFix]
  constructor
  · rintro ⟨-, h1⟩
    rw [← h1, mul_inv_cancel_right, hx] at hc
    intro r
    exact (congrFun (Matrix.diagonal_injective hc) r).symm
  · intro hd
    refine ⟨hxP, ?_⟩
    have h2 : ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) * x *
        (ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k))⁻¹ = x := by
      apply mat_injective
      rw [hc, hx]
      exact congrArg Matrix.diagonal (funext hd)
    calc x * ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) =
        ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) * x *
          (ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k))⁻¹ *
          ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) := by rw [h2]
      _ = ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) * x := by group

theorem exists_tau (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : 0 < p)
    (hpq : p ∣ 2 ^ f - 1) {ζ : F} (hζ : ζ ^ p = 1) :
    ∃ τ : Fin (6 / 2) → SU (unitaryInvolution F 2 f) 6, ∀ c, τ c ∈ diagP F f p ∧
      mat _ 6 (τ c) = Matrix.diagonal fun a => ζ ^ weight 6 a c := by
  choose τ hτP hτ using fun c : Fin (6 / 2) =>
    exists_mem_diagP_longTorusFun hF hp hpq hζ (lowIdx_ne_rev (n := 6) c c)
  refine ⟨τ, fun c => ⟨hτP c, ?_⟩⟩
  rw [hτ c]
  exact congrArg Matrix.diagonal (funext fun a => longTorusFun_lowIdx_eq_zpow c ζ a)

omit [Finite F] [CharP F 2] in
theorem mat_mul_zpow {σ : F ≃+* F} {x y : SU σ 6} {ζ : F} (hζ0 : ζ ≠ 0) {κ κ' : Fin 6 → ℤ}
    (hx : mat σ 6 x = Matrix.diagonal fun a => ζ ^ κ a)
    (hy : mat σ 6 y = Matrix.diagonal fun a => ζ ^ κ' a) :
    mat σ 6 (x * y) = Matrix.diagonal fun a => ζ ^ (κ a + κ' a) := by
  rw [map_mul, hx, hy, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [zpow_add₀ hζ0]

theorem mem_rankOne_of_mem_centralizer_diagFix (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (k : Fin (6 / 2))
    {g : SU (unitaryInvolution F 2 f) 6}
    (hg : g ∈ Subgroup.centralizer
      (diagFix ν p ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) :
        Set (SU (unitaryInvolution F 2 f) 6)))
    {m : ℕ} (hg2 : g ^ 2 ^ m = 1) :
    g ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6) k := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ, hζ1⟩ := exists_pow_eq_one_ne_one hF hp hpq
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨τ, hτ⟩ := exists_tau hF hp.pos hpq hζ
  have hmem : ∀ {x : SU (unitaryInvolution F 2 f) 6} {κ : Fin 6 → ℤ}, x ∈ diagP F f p →
      mat _ 6 x = Matrix.diagonal (fun a => ζ ^ κ a) → (∀ r, κ ((levelPerm k).symm r) = κ r) →
      x * g = g * x := fun hxP hx hκ =>
    Subgroup.mem_centralizer_iff.mp hg _
      ((mem_diagFix_simple_iff hν k hxP hx).mpr fun r => by rw [hκ r])
  fin_cases k
  · exact mem_rankOne_of_commute_short hσ (by decide) hp hp2 hζ hζ1
      (κ := fun a => weight 6 a 0 + weight 6 a 1) (κ' := fun a => weight 6 a 2)
      (by decide) (by decide) (mat_mul_zpow hζ0 (hτ 0).2 (hτ 1).2) (hτ 2).2
      (hmem (mul_mem (hτ 0).1 (hτ 1).1) (mat_mul_zpow hζ0 (hτ 0).2 (hτ 1).2) (by decide))
      (hmem (hτ 2).1 (hτ 2).2 (by decide)) hg2
  · exact mem_rankOne_of_commute_short hσ (by decide) hp hp2 hζ hζ1
      (κ := fun a => weight 6 a 1 + weight 6 a 2) (κ' := fun a => weight 6 a 0)
      (by decide) (by decide) (mat_mul_zpow hζ0 (hτ 1).2 (hτ 2).2) (hτ 0).2
      (hmem (mul_mem (hτ 1).1 (hτ 2).1) (mat_mul_zpow hζ0 (hτ 1).2 (hτ 2).2) (by decide))
      (hmem (hτ 0).1 (hτ 0).2 (by decide)) hg2
  · exact mem_rankOne_of_commute_last hσ (by decide) ⟨3, rfl⟩ hp hp2 hζ hζ1
      (κ := fun a => weight 6 a 0) (κ' := fun a => weight 6 a 1)
      (by decide) (by decide) (hτ 0).2 (hτ 1).2
      (hmem (hτ 0).1 (hτ 0).2 (by decide)) (hmem (hτ 1).1 (hτ 1).2 (by decide)) hg2

theorem ggOTwoPrime_centralizer_diagFix_simple (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (k : Fin (6 / 2)) :
    ggOTwoPrime (Subgroup.centralizer
      (diagFix ν p ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) :
        Set (SU (unitaryInvolution F 2 f) 6))) =
      ggRootLevi (Unitary.rootDatum hF 6) (Pi.single k 1) := by
  have hσ := unitaryInvolution_involutive hF
  apply le_antisymm
  · rw [ggOTwoPrime, Subgroup.closure_le]
    rintro y ⟨hy, m, hm⟩
    exact mem_rankOne_of_mem_centralizer_diagFix hν hp hp2 hpq k hy hm
  have hC : ∀ z ∈ rankOne (rootGroup (unitaryInvolution F 2 f) hσ 6) k,
      z ∈ Subgroup.centralizer
        (diagFix ν p ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) :
          Set (SU (unitaryInvolution F 2 f) 6)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsP := (mem_diagFix.mp hs).1
    obtain ⟨d, hd⟩ := hsP.1
    have hdk := (mem_diagFix_simple_iff hν k hsP hd).mp hs
    have hblk : ∃ blk : Fin 6 → ℕ, IsBlk blk (mat _ 6 z) ∧
        ∀ a b, blk a = blk b → blk a ≠ 0 → a = b ∨ a = (levelPerm k).symm b := by
      fin_cases k
      · exact ⟨_, (isBlk_short_of_mem (by decide) hz).1, by decide⟩
      · exact ⟨_, (isBlk_short_of_mem (by decide) hz).1, by decide⟩
      · exact ⟨_, isBlk_last_of_mem (by decide) hz, by decide⟩
    obtain ⟨blk, hzb, hb⟩ := hblk
    have hcomm := isBlk_commute_diagonal hzb (d := d) fun a b hab ha => by
      rcases hb a b hab ha with rfl | rfl
      · rfl
      · exact hdk b
    apply mat_injective
    rw [map_mul, map_mul, show mat _ 6 s = Matrix.diagonal d from hd]
    exact hcomm.symm
  have h2 : ∀ x, (x ∈ rootGroup (unitaryInvolution F 2 f) hσ 6 (Pi.single k 1) ∨
      x ∈ rootGroup (unitaryInvolution F 2 f) hσ 6 (-Pi.single k 1)) → x * x = 1 := by
    intro x hx
    by_cases hk : k.val + 1 < 6 / 2
    · exact mul_self_eq_one_of_mem_short hσ hk hx
    · exact mul_self_eq_one_of_mem_last hσ hk ⟨3, rfl⟩ hx
  refine sup_le (fun x hx => Subgroup.subset_closure
      ⟨hC x (Subgroup.mem_sup_left hx), 1, ?_⟩)
    (fun x hx => Subgroup.subset_closure ⟨hC x (Subgroup.mem_sup_right hx), 1, ?_⟩)
  · rw [pow_one, sq]
    exact h2 x (Or.inl hx)
  · rw [pow_one, sq]
    exact h2 x (Or.inr hx)

theorem diagFix_conj (hν : GGWeylLift (Unitary.rootDatum hF 6) ν) {p : ℕ}
    (w u : GGWeyl (Unitary.rootDatum hF 6)) :
    diagFix ν p (w * u * w⁻¹) = (diagFix ν p u).map (MulAut.conj (ν w)).toMonoidHom := by
  ext s
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_diagFix,
    map_mul, map_inv]
  constructor
  · rintro ⟨hsP, hc⟩
    refine ⟨(ν w)⁻¹ * s * ν w, ⟨?_, ?_⟩, by group⟩
    · have h := conj_mem_diagP hF hν w⁻¹ hsP
      rwa [map_inv, inv_inv] at h
    · calc (ν w)⁻¹ * s * ν w * ν u = (ν w)⁻¹ * (s * (ν w * ν u * (ν w)⁻¹)) * ν w := by group
        _ = (ν w)⁻¹ * (ν w * ν u * (ν w)⁻¹ * s) * ν w := by rw [hc]
        _ = ν u * ((ν w)⁻¹ * s * ν w) := by group
  · rintro ⟨s₀, ⟨hs₀P, hc⟩, rfl⟩
    refine ⟨conj_mem_diagP hF hν w hs₀P, ?_⟩
    calc ν w * s₀ * (ν w)⁻¹ * (ν w * ν u * (ν w)⁻¹) = ν w * (s₀ * ν u) * (ν w)⁻¹ := by group
      _ = ν w * (ν u * s₀) * (ν w)⁻¹ := by rw [hc]
      _ = ν w * ν u * (ν w)⁻¹ * (ν w * s₀ * (ν w)⁻¹) := by group

theorem ggRootLevi_weylAction (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    (w : GGWeyl (Unitary.rootDatum hF 6)) (i : Fin (6 / 2)) :
    ggRootLevi (Unitary.rootDatum hF 6)
        (weylAction (Unitary.rootDatum hF 6).isFiniteType w (Pi.single i 1)) =
      (ggRootLevi (Unitary.rootDatum hF 6) (Pi.single i 1)).map
        (MulAut.conj (ν w)).toMonoidHom := by
  have hact := ggStdPos_actsAs_weylLift hν w
  rw [ggRootLevi, ggRootLevi, Subgroup.map_sup, hact _ (single_mem_roots i),
    hact _ (neg_single_mem_roots i), map_neg]

theorem ggOTwoPrime_centralizer_diagFix (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1)
    (w : GGWeyl (Unitary.rootDatum hF 6)) (i : Fin (6 / 2)) :
    ggOTwoPrime (Subgroup.centralizer
      (diagFix ν p (w * (coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple i * w⁻¹) :
        Set (SU (unitaryInvolution F 2 f) 6))) =
      ggRootLevi (Unitary.rootDatum hF 6)
        (weylAction (Unitary.rootDatum hF 6).isFiniteType w (Pi.single i 1)) := by
  rw [diagFix_conj hν w, centralizer_map_conj,
    ← ggOTwoPrime_map_of_injective (MulAut.conj (ν w)).toMonoidHom (MulAut.conj (ν w)).injective,
    ggOTwoPrime_centralizer_diagFix_simple hν hp hp2 hpq i, ggRootLevi_weylAction hν w i]

end Six

section Ratio

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem diagP_apply_ne_zero {p : ℕ} {x : SU (unitaryInvolution F 2 f) 6}
    (hx : x ∈ diagP F f p) (a : Fin 6) : mat _ 6 x a a ≠ 0 := by
  obtain ⟨d, hd⟩ := hx.1
  rw [mat_apply, hd, Matrix.diagonal_apply_eq]
  exact ne_zero_of_unitary (unitary_of_coe_eq_diagonal (σ := unitaryInvolution F 2 f) hd) a

theorem mat_mul_apply_self {p : ℕ} {x y : SU (unitaryInvolution F 2 f) 6}
    (hx : x ∈ diagP F f p) (hy : y ∈ diagP F f p) (a : Fin 6) :
    mat _ 6 (x * y) a a = mat _ 6 x a a * mat _ 6 y a a := by
  obtain ⟨d, hd⟩ := hx.1
  obtain ⟨e, he⟩ := hy.1
  rw [map_mul, mat_apply, mat_apply, hd, he, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]

variable (F f) in
@[expose] noncomputable def diagRatio (p : ℕ) (a b : Fin 6) : ↥(diagP F f p) →* Fˣ where
  toFun x := Units.mk0 (mat _ 6 (x : SU (unitaryInvolution F 2 f) 6) a a /
      mat _ 6 (x : SU (unitaryInvolution F 2 f) 6) b b)
    (div_ne_zero (diagP_apply_ne_zero x.2 a) (diagP_apply_ne_zero x.2 b))
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    rw [mat_mul_apply_self x.2 y.2, mat_mul_apply_self x.2 y.2, mul_div_mul_comm]

theorem diagRatio_apply {p : ℕ} {a b : Fin 6} (x : ↥(diagP F f p)) :
    (diagRatio F f p a b x : F) = mat _ 6 (x : SU (unitaryInvolution F 2 f) 6) a a /
      mat _ 6 (x : SU (unitaryInvolution F 2 f) 6) b b :=
  rfl

theorem card_range_diagRatio {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) {a b : Fin 6}
    (hne : ∃ x, diagRatio F f p a b x ≠ 1) : Nat.card (diagRatio F f p a b).range = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hle : (diagRatio F f p a b).range ≤ rootsOfUnity p F := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    obtain ⟨d, hd⟩ := x.2.1
    have ha := (diagP_entries hpq x.2 hd a).1
    have hb := (diagP_entries hpq x.2 hd b).1
    rw [Units.val_pow_eq_pow_val, diagRatio_apply, div_pow, Units.val_one, mat_apply, hd,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ha, hb, div_one]
  apply le_antisymm
  · exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F p)
  · obtain ⟨x, hx⟩ := hne
    have hord : orderOf (diagRatio F f p a b x) = p := by
      refine orderOf_eq_prime ?_ hx
      have h := hle ⟨x, rfl⟩
      rwa [mem_rootsOfUnity] at h
    have hdvd := Subgroup.orderOf_dvd_natCard (diagRatio F f p a b).range ⟨x, rfl⟩
    rw [hord] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd

theorem levelPerm_symm_cases (k : Fin (6 / 2)) (r : Fin 6) :
    (levelPerm k).symm r = r ∨
      (r = lowIdx k ∧ (levelPerm k).symm r = levelPerm k (lowIdx k)) ∨
      (r = levelPerm k (lowIdx k) ∧ (levelPerm k).symm r = lowIdx k) ∨
      (r = Fin.rev (lowIdx k) ∧ (levelPerm k).symm r = Fin.rev (levelPerm k (lowIdx k))) ∨
      (r = Fin.rev (levelPerm k (lowIdx k)) ∧ (levelPerm k).symm r = Fin.rev (lowIdx k)) := by
  revert k r
  decide

omit [Finite F] [CharP F 2] in
theorem levelPerm_fixed_iff {d : Fin 6 → F} (hrev : ∀ s, d (Fin.rev s) = (d s)⁻¹)
    (k : Fin (6 / 2)) :
    (∀ r, d ((levelPerm k).symm r) = d r) ↔ d (lowIdx k) = d (levelPerm k (lowIdx k)) := by
  constructor
  · intro h
    have h1 := h (levelPerm k (lowIdx k))
    rwa [Equiv.symm_apply_apply] at h1
  · intro hab r
    rcases levelPerm_symm_cases k r with h | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rw [h]
    · rw [h, hab]
    · rw [h, hab]
    · rw [h, hrev, hrev, hab]
    · rw [h, hrev, hrev, hab]

theorem card_range_diagRatio_simple (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (k : Fin (6 / 2)) :
    Nat.card (diagRatio F f p (lowIdx k) (levelPerm k (lowIdx k))).range = p := by
  obtain ⟨ζ, hζ, hζ1⟩ := exists_pow_eq_one_ne_one hF hp hpq
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨τ, hτ⟩ := exists_tau hF hp.pos hpq hζ
  refine card_range_diagRatio hp hpq ⟨⟨τ k, (hτ k).1⟩, fun h => ?_⟩
  have h1 := congrArg Units.val h
  rw [diagRatio_apply, Units.val_one, (hτ k).2, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_eq, ← zpow_sub₀ hζ0] at h1
  have hw : ∀ k : Fin (6 / 2), weight 6 (lowIdx k) k - weight 6 (levelPerm k (lowIdx k)) k = 1 ∨
      weight 6 (lowIdx k) k - weight 6 (levelPerm k (lowIdx k)) k = 2 := by
    decide
  rcases hw k with hw | hw <;> rw [hw] at h1
  · exact zpow_ne_one_of_pow_eq_one hp hp2 hζ hζ1 one_ne_zero (by norm_num) (by norm_num) h1
  · exact zpow_ne_one_of_pow_eq_one hp hp2 hζ hζ1 two_ne_zero (by norm_num) (by norm_num) h1

end Ratio

section SixRatio

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hF : Nat.card F = (2 ^ f) ^ 2}
  {ν : GGWeyl (Unitary.rootDatum hF 6) →* SU (unitaryInvolution F 2 f) 6}

theorem mem_diagFix_simple_iff_diagRatio (hν : GGWeylLift (Unitary.rootDatum hF 6) ν) {p : ℕ}
    (hpq : p ∣ 2 ^ f - 1) (k : Fin (6 / 2)) (x : ↥(diagP F f p)) :
    (x : SU (unitaryInvolution F 2 f) 6) ∈
        diagFix ν p ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) ↔
      diagRatio F f p (lowIdx k) (levelPerm k (lowIdx k)) x = 1 := by
  obtain ⟨d, hd⟩ := x.2.1
  have hrev : ∀ s, d (Fin.rev s) = (d s)⁻¹ := fun s => (diagP_entries hpq x.2 hd s).2
  rw [mem_diagFix_simple_iff hν k x.2 hd, levelPerm_fixed_iff hrev k, ← Units.val_eq_one,
    diagRatio_apply, mat_apply, hd, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
    div_eq_one_iff_eq (ne_zero_of_unitary
      (unitary_of_coe_eq_diagonal (σ := unitaryInvolution F 2 f) hd) _)]

end SixRatio

end CFSG.StandardType.KGPosSU

end
