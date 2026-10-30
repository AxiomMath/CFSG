module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Semilinear
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Finset

instance gd_finite_ringAut (K : Type*) [Field K] [Finite K] : Finite (RingAut K) :=
  Finite.of_injective (DFunLike.coe : RingAut K → K → K) DFunLike.coe_injective

theorem gd_dedekind {K : Type*} [Field K] (σ : RingAut K) {m : ℕ} (hm : m = orderOf σ)
    (b : ℕ → K) (h : ∀ a : K, ∑ i ∈ range m, b i * (σ ^ i) a = 0) :
    ∀ i < m, b i = 0 := by
  classical
  subst hm
  let χ : ℕ → (Kˣ →* K) := fun i => (RingEquiv.toMonoidHom (σ ^ i)).comp (Units.coeHom K)
  have hχ : ∀ (i : ℕ) (u : Kˣ), χ i u = (σ ^ i) (u : K) := fun i u => rfl
  have hinj : ∀ i ∈ Set.Iio (orderOf σ), ∀ j ∈ Set.Iio (orderOf σ), χ i = χ j → i = j := by
    intro i hi j hj hij
    have hpow : σ ^ i = σ ^ j := by
      apply RingEquiv.ext
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · have h1 := congrArg (fun φ : Kˣ →* K => φ (Units.mk0 x hx)) hij
        simpa [hχ] using h1
    exact pow_injOn_Iio_orderOf hi hj hpow
  have hli : LinearIndependent K (fun f : Kˣ →* K => (f : Kˣ → K)) :=
    linearIndependent_monoidHom Kˣ K
  have hli' : LinearIndependent K (fun i : Fin (orderOf σ) => (χ i : Kˣ → K)) :=
    hli.comp (fun i : Fin (orderOf σ) => χ i) (fun i j hij => Fin.ext
      (hinj (i : ℕ) (Set.mem_Iio.mpr i.2) (j : ℕ) (Set.mem_Iio.mpr j.2) hij))
  intro i hi
  rw [Fintype.linearIndependent_iff] at hli'
  refine hli' (fun j : Fin (orderOf σ) => b j) ?_ ⟨i, hi⟩
  funext u
  have hu : ∑ j : Fin (orderOf σ), b j * (σ ^ (j : ℕ)) (u : K) = 0 :=
    (Fin.sum_univ_eq_sum_range (fun i => b i * (σ ^ i) (u : K)) (orderOf σ)).trans (h u)
  simpa [Finset.sum_apply, hχ, smul_eq_mul] using hu

theorem gd_sum_range_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (m : ℕ) (h : f m = f 0) :
    ∑ i ∈ range m, f (i + 1) = ∑ i ∈ range m, f i := by
  have h1 := Finset.sum_range_succ' f m
  have h2 := Finset.sum_range_succ f m
  have h3 : (∑ i ∈ range m, f (i + 1)) + f 0 = (∑ i ∈ range m, f i) + f 0 := by
    rw [← h1, h2, h]
  exact add_right_cancel h3

theorem gd_hilbert90 {K : Type*} [Field K] (σ : RingAut K) {m : ℕ} (hm : m = orderOf σ)
    (hmpos : 0 < m) (x : K) (hx : x ≠ 0) (hN : ∏ i ∈ range m, (σ ^ i) x = 1) :
    ∃ z : K, z ≠ 0 ∧ x * σ z = z := by
  classical
  have hσm : σ ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one σ
  have hσm_apply : ∀ a : K, (σ ^ m) a = a := fun a => congrArg (fun φ : RingAut K => φ a) hσm
  have hσ0_apply : ∀ a : K, (σ ^ 0) a = a := fun a => rfl
  have hpow_succ : ∀ (k : ℕ) (a : K), (σ ^ (k + 1)) a = σ ((σ ^ k) a) := fun k a => by
    rw [pow_succ']; rfl
  let b : ℕ → K := fun j => ∏ i ∈ range j, (σ ^ i) x
  have hbm : b m = 1 := hN
  have hb0 : b 0 = 1 := by simp [b]
  have hbsucc : ∀ j, x * σ (b j) = b (j + 1) := by
    intro j
    have e1 : σ (b j) = ∏ i ∈ range j, (σ ^ (i + 1)) x := by
      show σ (∏ i ∈ range j, (σ ^ i) x) = _
      rw [map_prod]
      exact Finset.prod_congr rfl (fun i _ => (hpow_succ i x).symm)
    have e2 : b (j + 1) = (∏ i ∈ range j, (σ ^ (i + 1)) x) * x := by
      show ∏ i ∈ range (j + 1), (σ ^ i) x = _
      rw [Finset.prod_range_succ']
      rfl
    rw [e1, e2, mul_comm]
  have hex : ∃ y : K, ∑ j ∈ range m, b j * (σ ^ j) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := gd_dedekind σ hm b hcon 0 hmpos
    rw [hb0] at h0
    exact one_ne_zero h0
  obtain ⟨y, hy⟩ := hex
  refine ⟨∑ j ∈ range m, b j * (σ ^ j) y, hy, ?_⟩
  let f : ℕ → K := fun j => b j * (σ ^ j) y
  have hfm : f m = f 0 := by
    show b m * (σ ^ m) y = b 0 * (σ ^ 0) y
    rw [hσm_apply, hσ0_apply, hbm, hb0]
  have hshift : ∑ j ∈ range m, f (j + 1) = ∑ j ∈ range m, f j :=
    gd_sum_range_shift f m hfm
  show x * σ (∑ j ∈ range m, f j) = ∑ j ∈ range m, f j
  rw [map_sum, Finset.mul_sum, ← hshift]
  apply Finset.sum_congr rfl
  intro j _
  show x * σ (b j * (σ ^ j) y) = b (j + 1) * (σ ^ (j + 1)) y
  rw [map_mul, hpow_succ j y, ← hbsucc j]
  ring

theorem gd_range_eq_ker {G : Type*} [Group G] [Finite G] (N H : G →* G)
    (hNH : N.ker ≤ H.range) (hsub : N.range ≤ H.ker) : N.range = H.ker := by
  have e1 : Nat.card N.ker * Nat.card N.range = Nat.card G := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index N.ker
  have e2 : Nat.card H.ker * Nat.card H.range = Nat.card G := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index H.ker
  have l1 : Nat.card N.ker ≤ Nat.card H.range := Subgroup.card_le_of_le hNH
  have hpos : 0 < Nat.card H.range := Nat.card_pos
  apply Subgroup.eq_of_le_of_card_ge hsub
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc Nat.card H.ker * Nat.card H.range = Nat.card G := e2
    _ = Nat.card N.ker * Nat.card N.range := e1.symm
    _ ≤ Nat.card H.range * Nat.card N.range := Nat.mul_le_mul_right _ l1
    _ = Nat.card N.range * Nat.card H.range := mul_comm _ _

theorem gd_norm_surj {K : Type*} [Field K] [Finite K] (σ : RingAut K) {m : ℕ}
    (hm : m = orderOf σ) (hmpos : 0 < m) (e : K) (he : e ≠ 0) (hσe : σ e = e) :
    ∃ l : K, l ≠ 0 ∧ ∏ i ∈ range m, (σ ^ i) l = e := by
  classical
  have hσm : σ ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one σ
  have hσm_apply : ∀ a : K, (σ ^ m) a = a := fun a => congrArg (fun φ : RingAut K => φ a) hσm
  have hσ_succ : ∀ (k : ℕ) (a : K), (σ ^ (k + 1)) a = σ ((σ ^ k) a) := fun k a => by
    rw [pow_succ']; rfl
  have hPσ : ∀ x : K, x ≠ 0 → σ (∏ i ∈ range m, (σ ^ i) x) = ∏ i ∈ range m, (σ ^ i) x := by
    intro x hx
    have e1 : σ (∏ i ∈ range m, (σ ^ i) x) = ∏ i ∈ range m, (σ ^ (i + 1)) x := by
      rw [map_prod]
      exact Finset.prod_congr rfl (fun i _ => (hσ_succ i x).symm)
    have e2 : ∏ i ∈ range (m + 1), (σ ^ i) x = (∏ i ∈ range m, (σ ^ (i + 1)) x) * x := by
      rw [Finset.prod_range_succ']
      rfl
    have e3 : ∏ i ∈ range (m + 1), (σ ^ i) x = (∏ i ∈ range m, (σ ^ i) x) * x := by
      rw [Finset.prod_range_succ, hσm_apply]
    have e4 : (∏ i ∈ range m, (σ ^ (i + 1)) x) * x = (∏ i ∈ range m, (σ ^ i) x) * x := by
      rw [← e2, e3]
    rw [e1]
    exact mul_right_cancel₀ hx e4
  have hPne : ∀ u : Kˣ, ∏ i ∈ range m, (σ ^ i) (u : K) ≠ 0 := by
    intro u
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (map_ne_zero (σ ^ i)).mpr u.ne_zero
  have hσne : ∀ u : Kˣ, σ (u : K) ≠ 0 := fun u => (map_ne_zero σ).mpr u.ne_zero
  let Nm : Kˣ →* Kˣ := MonoidHom.mk'
    (fun u => Units.mk0 (∏ i ∈ range m, (σ ^ i) (u : K)) (hPne u))
    (fun u v => Units.ext (by simp [Finset.prod_mul_distrib]))
  let Hm : Kˣ →* Kˣ := MonoidHom.mk'
    (fun u => Units.mk0 ((u : K) / σ (u : K)) (div_ne_zero u.ne_zero (hσne u)))
    (fun u v => Units.ext (by simp only [Units.val_mk0, Units.val_mul, map_mul]; ring))
  have hNval : ∀ u : Kˣ, ((Nm u : Kˣ) : K) = ∏ i ∈ range m, (σ ^ i) (u : K) :=
    fun u => rfl
  have hHval : ∀ u : Kˣ, ((Hm u : Kˣ) : K) = (u : K) / σ (u : K) := fun u => rfl
  have hNH : Nm.ker ≤ Hm.range := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : ∏ i ∈ range m, (σ ^ i) (x : K) = 1 := by
      have h1 := congrArg Units.val hx
      rw [hNval, Units.val_one] at h1
      exact h1
    obtain ⟨z, hz, hxz⟩ := gd_hilbert90 σ hm hmpos (x : K) x.ne_zero hx'
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 z hz, Units.ext ?_⟩
    rw [hHval, Units.val_mk0, div_eq_iff ((map_ne_zero σ).mpr hz)]
    exact hxz.symm
  have hsub : Nm.range ≤ Hm.ker := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hHval, hNval, Units.val_one, hPσ x x.ne_zero]
    exact div_self (hPne x)
  have hEq : Nm.range = Hm.ker := gd_range_eq_ker Nm Hm hNH hsub
  have hmem : Units.mk0 e he ∈ Hm.ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hHval, Units.val_mk0, hσe, div_self he, Units.val_one]
  rw [← hEq, MonoidHom.mem_range] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨(x : K), x.ne_zero, ?_⟩
  have h1 := congrArg Units.val hx
  rw [hNval, Units.val_mk0] at h1
  exact h1

theorem gd_speiser {K : Type*} [Field K] (σ : RingAut K) {m : ℕ} (hm : m = orderOf σ)
    (hmpos : 0 < m) (ψ : (Fin 2 → K) → (Fin 2 → K))
    (hadd : ∀ v w, ψ (v + w) = ψ v + ψ w)
    (hsemi : ∀ (a : K) (v : Fin 2 → K), ψ (a • v) = σ a • ψ v)
    (hpow : ∀ v, ψ^[m] v = v) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ψ v = v := by
  classical
  have hσ_succ : ∀ (k : ℕ) (a : K), (σ ^ (k + 1)) a = σ ((σ ^ k) a) := fun k a => by
    rw [pow_succ']; rfl
  have hit : ∀ (k : ℕ) (a : K) (v : Fin 2 → K), ψ^[k] (a • v) = (σ ^ k) a • ψ^[k] v := by
    intro k
    induction k with
    | zero => intro a v; rfl
    | succ k ih =>
      intro a v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hsemi, hσ_succ]
  have hsumadd : ∀ (s : Finset ℕ) (g : ℕ → (Fin 2 → K)),
      ψ (∑ i ∈ s, g i) = ∑ i ∈ s, ψ (g i) :=
    fun s g => map_sum (AddMonoidHom.mk' ψ hadd) g s
  let w : Fin 2 → K := ![1, 0]
  have hw : w ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [w] at h0
  let T : K → (Fin 2 → K) := fun a => ∑ i ∈ range m, ψ^[i] (a • w)
  have hTfix : ∀ a, ψ (T a) = T a := by
    intro a
    show ψ (∑ i ∈ range m, ψ^[i] (a • w)) = ∑ i ∈ range m, ψ^[i] (a • w)
    rw [hsumadd]
    have e : ∀ i, ψ (ψ^[i] (a • w)) = ψ^[i + 1] (a • w) := fun i =>
      (Function.iterate_succ_apply' ψ i _).symm
    simp only [e]
    exact gd_sum_range_shift (fun i => ψ^[i] (a • w)) m (hpow (a • w))
  have hex : ∃ a : K, T a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcoord : ∀ j : Fin 2, w j = 0 := by
      intro j
      have hcoef : ∀ a : K, ∑ i ∈ range m, (ψ^[i] w) j * (σ ^ i) a = 0 := by
        intro a
        have h1 := congrFun (hcon a) j
        have h2 : T a j = ∑ i ∈ range m, (σ ^ i) a * (ψ^[i] w) j := by
          show (∑ i ∈ range m, ψ^[i] (a • w)) j = _
          rw [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i _
          rw [hit, Pi.smul_apply, smul_eq_mul]
        rw [h2, Pi.zero_apply] at h1
        exact (Finset.sum_congr rfl
          (fun i _ => mul_comm ((ψ^[i] w) j) ((σ ^ i) a))).trans h1
      have hd := gd_dedekind σ hm (fun i => (ψ^[i] w) j) hcoef 0 hmpos
      simpa using hd
    apply hw
    ext j
    simpa using hcoord j
  obtain ⟨a, ha⟩ := hex
  exact ⟨T a, ha, hTfix a⟩

theorem exists_eigenvector_of_pow_scalar {K : Type*} [Field K] [Finite K]
    (σ : RingAut K) (Φ : Equiv.Perm (Fin 2 → K)) (hΦ : IsSemilinear σ Φ)
    (c : K) (hc : ∀ v, (Φ ^ orderOf σ) v = c • v) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∃ μ : K, Φ v = μ • v := by
  obtain ⟨hadd, hsemi⟩ := hΦ
  have hmpos : 0 < orderOf σ := orderOf_pos σ
  have hΦ0 : Φ 0 = 0 := by simpa using hadd 0 0
  have hΦne : ∀ v, v ≠ 0 → Φ v ≠ 0 := by
    intro v hv h
    apply hv
    apply Φ.injective
    rw [h, hΦ0]
  have hw0ne : (![1, 0] : Fin 2 → K) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hw0ne
    apply (Φ ^ orderOf σ).injective
    simp [hc, hc0]
  have hcomm : ∀ v, (Φ ^ orderOf σ) (Φ v) = Φ ((Φ ^ orderOf σ) v) := by
    intro v
    have h2 : Φ ^ orderOf σ * Φ = Φ * Φ ^ orderOf σ :=
      (pow_succ Φ (orderOf σ)).symm.trans (pow_succ' Φ (orderOf σ))
    calc (Φ ^ orderOf σ) (Φ v) = (Φ ^ orderOf σ * Φ) v := rfl
      _ = (Φ * Φ ^ orderOf σ) v := by rw [h2]
      _ = Φ ((Φ ^ orderOf σ) v) := rfl
  have hσc : σ c = c := by
    have hv : Φ ![1, 0] ≠ 0 := hΦne _ hw0ne
    have h1 : c • Φ ![1, 0] = σ c • Φ ![1, 0] := by
      rw [← hc (Φ ![1, 0]), hcomm, hc, hsemi]
    exact ((smul_left_injective K hv) h1).symm
  have hσc' : σ c⁻¹ = c⁻¹ := by rw [map_inv₀, hσc]
  obtain ⟨l, hl0, hl⟩ := gd_norm_surj σ rfl hmpos c⁻¹ (inv_ne_zero hc0) hσc'
  let ψ : (Fin 2 → K) → (Fin 2 → K) := fun v => l • Φ v
  have hψadd : ∀ v w, ψ (v + w) = ψ v + ψ w := fun v w => by
    show l • Φ (v + w) = l • Φ v + l • Φ w
    rw [hadd, smul_add]
  have hψsemi : ∀ (a : K) (v : Fin 2 → K), ψ (a • v) = σ a • ψ v := fun a v => by
    show l • Φ (a • v) = σ a • (l • Φ v)
    rw [hsemi, smul_comm]
  have hσ_succ : ∀ (k : ℕ) (a : K), (σ ^ (k + 1)) a = σ ((σ ^ k) a) := fun k a => by
    rw [pow_succ']; rfl
  have hψit : ∀ (k : ℕ) (v : Fin 2 → K),
      ψ^[k] v = (∏ i ∈ range k, (σ ^ i) l) • (Φ ^ k) v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have hP : ∏ i ∈ range (k + 1), (σ ^ i) l = l * σ (∏ i ∈ range k, (σ ^ i) l) := by
        have e : ∏ i ∈ range k, (σ ^ (i + 1)) l = ∏ i ∈ range k, σ ((σ ^ i) l) :=
          Finset.prod_congr rfl (fun i _ => hσ_succ i l)
        have e0 : (σ ^ 0) l = l := rfl
        rw [Finset.prod_range_succ', e0, map_prod, e, mul_comm]
      rw [Function.iterate_succ_apply', ih]
      show l • Φ ((∏ i ∈ range k, (σ ^ i) l) • (Φ ^ k) v) = _
      rw [hsemi, smul_smul, hP, pow_succ', Equiv.Perm.mul_apply]
  have hpow : ∀ v, ψ^[orderOf σ] v = v := by
    intro v
    rw [hψit, hl, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨v, hv0, hvfix⟩ := gd_speiser σ rfl hmpos ψ hψadd hψsemi hpow
  refine ⟨v, hv0, l⁻¹, ?_⟩
  have hvfix' : l • Φ v = v := hvfix
  calc Φ v = l⁻¹ • (l • Φ v) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
    _ = l⁻¹ • v := by rw [hvfix']

end CFSG.Quasithin.Vol2.Ch10Reselect
