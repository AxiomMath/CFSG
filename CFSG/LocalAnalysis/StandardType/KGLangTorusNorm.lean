module

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CFSG.LocalAnalysis.StandardType.KGLangH90
import CFSG.Quasithin.Vol2.Ch10Reselect.GaloisDescent
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.StandardType

private theorem kgLangCNormAux_single_ne_zero {ι : Type*} [DecidableEq ι] {K : ι → Type*}
    [∀ i, Field (K i)] (i : ι) : (Pi.single i (1 : K i) : ∀ i, K i) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

private theorem kgLangCNormAux_apply_ne_zero_of_mul_single_one_eq {ι : Type*} [DecidableEq ι]
    {K : ι → Type*} [∀ i, Field (K i)] {g : ∀ i, K i} {i : ι}
    (hg : g * Pi.single i 1 = g) (hg0 : g ≠ 0) : g i ≠ 0 := by
  intro hi
  apply hg0
  funext l
  by_cases hl : l = i
  · subst hl; exact hi
  · have := congrFun hg l
    simpa [Pi.single_eq_of_ne hl] using this.symm

private theorem kgLangCNormAux_mul_single_one {ι : Type*} [DecidableEq ι] {K : ι → Type*}
    [∀ i, Field (K i)] (y : ∀ i, K i) (i : ι) :
    y * (Pi.single i (1 : K i) : ∀ i, K i) = Pi.single i (y i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

private theorem kgLangCNormAux_single_support {ι : Type*} [DecidableEq ι] {K : ι → Type*}
    [∀ i, Field (K i)] {i : ι} {y : ∀ i, K i}
    (h : (Pi.single i (1 : K i) : ∀ i, K i) * y = y) :
    y = Pi.single i (y i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · have h2 := congrFun h j
    rw [Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul] at h2
    rw [← h2, Pi.single_eq_of_ne hj]

private theorem kgLangCNormAux_single_mul_single_of_ne {ι : Type*} [DecidableEq ι]
    {K : ι → Type*} [∀ i, Field (K i)] {i j : ι} (hij : i ≠ j) :
    (Pi.single i (1 : K i) : ∀ i, K i) * Pi.single j (1 : K j) = 0 := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [Pi.single_eq_of_ne hij]
  · simp [Pi.single_eq_of_ne hl]

private theorem kgLangCNormAux_single_mul_eq_single_one {ι : Type*} [DecidableEq ι]
    {K : ι → Type*} [∀ i, Field (K i)] {f : ∀ i, K i} {j : ι} (hj : f j = 1) :
    (Pi.single j (1 : K j) : ∀ i, K i) * f = Pi.single j 1 := by
  funext l
  by_cases hl : l = j
  · subst hl; simp [hj]
  · simp [Pi.single_eq_of_ne hl]

private theorem kgLangCNormAux_single_one {ι : Type*} [DecidableEq ι]
    {K : ι → Type*} [∀ i, Field (K i)] (σ : (∀ i, K i) ≃+* (∀ i, K i)) (i : ι) :
    ∃ j, σ (Pi.single i 1) = Pi.single j 1 := by
  set f : ∀ i, K i := σ (Pi.single i 1) with hf
  have hidem : f * f = f := by
    rw [hf, ← map_mul, ← Pi.single_mul]; simp
  have hf0 : f ≠ 0 := fun h => kgLangCNormAux_single_ne_zero (K := K) i (σ.injective (by
    rw [map_zero]; exact h))
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra hcon
    exact hf0 (funext fun l => by_contra fun hl => hcon ⟨l, hl⟩)
  have hj1 : f j = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.1 (congrFun hidem j)).resolve_left hj
  refine ⟨j, ?_⟩
  funext k
  by_cases hkj : k = j
  · subst hkj; simp [hj1]
  · rw [Pi.single_eq_of_ne hkj]
    by_contra hk
    have hk1 : f k = 1 :=
      (IsIdempotentElem.iff_eq_zero_or_one.1 (congrFun hidem k)).resolve_left hk
    have key : ∀ l, f l = 1 →
        σ.symm (Pi.single l 1) * Pi.single i 1 = σ.symm (Pi.single l 1) := by
      intro l hl
      apply σ.injective
      rw [map_mul, σ.apply_symm_apply, kgLangCNormAux_single_mul_eq_single_one hl]
    have hg0 : ∀ l, σ.symm (Pi.single l 1) ≠ 0 := fun l h => by
      apply kgLangCNormAux_single_ne_zero (K := K) l
      have := congrArg σ h
      simp at this
    have h1 := kgLangCNormAux_apply_ne_zero_of_mul_single_one_eq (key j hj1) (hg0 j)
    have h2 := kgLangCNormAux_apply_ne_zero_of_mul_single_one_eq (key k hk1) (hg0 k)
    have h3 : σ.symm (Pi.single j 1) * σ.symm (Pi.single k 1) = 0 := by
      rw [← map_mul, kgLangCNormAux_single_mul_single_of_ne (Ne.symm hkj), map_zero]
    exact mul_ne_zero h1 h2 (congrFun h3 i)

private theorem kgLangCNormAux_pow_ne_self {α : Type*} (g : Equiv.Perm α) {p : ℕ}
    (hp : p.Prime) (hgp : g ^ p = 1) {x : α} (hx : g x ≠ x) {n : ℕ}
    (hn0 : 0 < n) (hnp : n < p) : (g ^ n) x ≠ x := by
  classical
  intro hn
  have hP : ∃ d, 0 < d ∧ (g ^ d) x = x := ⟨p, hp.pos, by rw [hgp]; rfl⟩
  have hm_pos : 0 < Nat.find hP := (Nat.find_spec hP).1
  have hm_x : (g ^ Nat.find hP) x = x := (Nat.find_spec hP).2
  have hm_dvd : ∀ d, (g ^ d) x = x → Nat.find hP ∣ d := by
    intro d hd
    by_contra hnd
    have hmod_pos : 0 < d % Nat.find hP :=
      Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hmod_x : (g ^ (d % Nat.find hP)) x = x := by
      have h1 : (g ^ d) x =
          ((g ^ Nat.find hP) ^ (d / Nat.find hP)) ((g ^ (d % Nat.find hP)) x) := by
        conv_lhs => rw [← Nat.div_add_mod d (Nat.find hP)]
        rw [pow_add, pow_mul, Equiv.Perm.mul_apply]
      have h2 : ((g ^ Nat.find hP) ^ (d / Nat.find hP)) x = x := by
        induction d / Nat.find hP with
        | zero => rfl
        | succ q ih => rw [pow_succ, Equiv.Perm.mul_apply, hm_x, ih]
      have h3 : (((g ^ Nat.find hP) ^ (d / Nat.find hP)).symm) x = x :=
        (Equiv.symm_apply_eq _).mpr h2.symm
      rw [hd] at h1
      calc (g ^ (d % Nat.find hP)) x =
            (((g ^ Nat.find hP) ^ (d / Nat.find hP)).symm)
              (((g ^ Nat.find hP) ^ (d / Nat.find hP)) ((g ^ (d % Nat.find hP)) x)) :=
              (Equiv.symm_apply_apply _ _).symm
        _ = (((g ^ Nat.find hP) ^ (d / Nat.find hP)).symm) x := by rw [← h1]
        _ = x := h3
    exact Nat.find_min hP (Nat.mod_lt d hm_pos) ⟨hmod_pos, hmod_x⟩
  have hmn : Nat.find hP ∣ n := hm_dvd n hn
  have hmp : Nat.find hP ∣ p := hm_dvd p (by rw [hgp]; rfl)
  have hgcd : Nat.find hP ∣ Nat.gcd n p := Nat.dvd_gcd hmn hmp
  have hcop : Nat.Coprime n p := ((hp.coprime_iff_not_dvd).mpr fun hdvd => by
    have hle := Nat.le_of_dvd hn0 hdvd
    omega).symm
  rw [hcop.gcd_eq_one] at hgcd
  have hm1 : Nat.find hP = 1 := Nat.dvd_one.mp hgcd
  rw [hm1] at hm_x
  exact hx hm_x

private theorem kgLangCNormAux_normSurjPi {p : ℕ} (hp : p.Prime) {ι : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Finite (L i)]
    (F : (∀ i, L i) ≃+* (∀ i, L i)) (hF : F ^ p = 1)
    (hstar : ∀ ε : ∀ i, L i, IsIdempotentElem ε → ε ≠ 0 → F ε = ε →
      ∃ x : ∀ i, L i, F (ε * x) ≠ ε * x) :
    ∀ c : (∀ i, L i)ˣ, F (c : ∀ i, L i) = (c : ∀ i, L i) →
      ∃ s : (∀ i, L i)ˣ,
        (c : ∀ i, L i) = ∏ m ∈ Finset.range p, (F ^ m) (s : ∀ i, L i) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hFp : ∀ y : ∀ i, L i, (F ^ p) y = y := fun y =>
    congrArg (fun e : (∀ i, L i) ≃+* (∀ i, L i) => e y) hF
  have hσ_aux : ∀ i, ∃ j, F (Pi.single i (1 : L i)) = Pi.single j (1 : L j) :=
    fun i => kgLangCNormAux_single_one F i
  let σ : ι → ι := fun i => Classical.choose (hσ_aux i)
  have hσ : ∀ i, F (Pi.single i (1 : L i)) = Pi.single (σ i) (1 : L (σ i)) :=
    fun i => Classical.choose_spec (hσ_aux i)
  have hsingle_inj : ∀ i j : ι, (Pi.single i (1 : L i) : ∀ i, L i) = Pi.single j 1 → i = j := by
    intro i j hij
    by_cases hne : i = j
    · exact hne
    · have h2 : Pi.single j (1 : L j) i = 0 := Pi.single_eq_of_ne hne (1 : L j)
      have h1 := congrFun hij i
      rw [Pi.single_eq_same, h2] at h1
      exact False.elim (one_ne_zero h1)
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    apply hsingle_inj i j
    apply F.injective
    rw [hσ i, hσ j, hij]
  have hσ_bij : Function.Bijective σ :=
    ⟨hσ_inj, (Finite.injective_iff_surjective).mp hσ_inj⟩
  let σe : Equiv.Perm ι := Equiv.ofBijective σ hσ_bij
  have hσe : ∀ i, σe i = σ i := fun i => Equiv.ofBijective_apply σ hσ_bij i
  have hσe_spec : ∀ i, F (Pi.single i (1 : L i)) = Pi.single (σe i) (1 : L (σe i)) :=
    fun i => by rw [hσe i]; exact hσ i
  have hσe_pow : σe ^ p = 1 := by
    ext i
    have hpow_single : ∀ (m : ℕ) (i : ι), (F ^ m) (Pi.single i (1 : L i)) =
        Pi.single ((σe ^ m) i) (1 : L ((σe ^ m) i)) := by
      intro m i
      induction m with
      | zero => rfl
      | succ m ih =>
          rw [pow_succ', RingAut.mul_apply, ih, hσe_spec, pow_succ', Equiv.Perm.mul_apply]
    have h1 := hpow_single p i
    rw [hF] at h1
    exact (hsingle_inj i ((σe ^ p) i) h1).symm
  let φb : ∀ I : ι, L (σe.symm I) →+* L I := fun I =>
    { toFun := fun x => (F (Pi.single (σe.symm I) x)) I
      map_one' := by
        have h1 : F (Pi.single (σe.symm I) (1 : L (σe.symm I))) = Pi.single I (1 : L I) := by
          rw [hσe_spec (σe.symm I), σe.apply_symm_apply]
        rw [h1, Pi.single_eq_same]
      map_mul' := by
        intro x y
        rw [Pi.single_mul, map_mul, Pi.mul_apply]
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [Pi.single_add, map_add, Pi.add_apply] }
  have hF_coord_b : ∀ (y : ∀ i, L i) (I : ι), (F y) I = φb I (y (σe.symm I)) := by
    intro y I
    have h1 : y * (Pi.single (σe.symm I) (1 : L (σe.symm I))) =
        Pi.single (σe.symm I) (y (σe.symm I)) :=
      kgLangCNormAux_mul_single_one y (σe.symm I)
    have h2 := congrArg F h1
    rw [map_mul, hσe_spec (σe.symm I), σe.apply_symm_apply] at h2
    have h3 := congrArg (fun z => z I) h2
    rw [Pi.mul_apply, Pi.single_eq_same, mul_one] at h3
    simpa [φb] using h3
  have hF_iter_b : ∀ (m : ℕ) (I : ι), ∃ Ψ : L ((σe.symm ^ m) I) →+* L I,
      ∀ y, (F ^ m) y I = Ψ (y ((σe.symm ^ m) I)) := by
    intro m
    induction m with
    | zero =>
        intro I
        refine ⟨RingHom.id (L I), ?_⟩
        intro y
        rfl
    | succ m ih =>
        intro I
        obtain ⟨Ψ, hΨ⟩ := ih (σe.symm I)
        refine ⟨(φb I).comp Ψ, ?_⟩
        intro y
        rw [pow_succ', RingAut.mul_apply, hF_coord_b, hΨ]
        rfl
  let orbSetoid : Setoid ι :=
    { r := fun i j => ∃ k : ℕ, (σe ^ k) i = j
      iseqv :=
        { refl := fun i => ⟨0, rfl⟩
          symm := fun {i j} h => by
            obtain ⟨k, hk⟩ := h
            have hkmod : (σe ^ k) i = (σe ^ (k % p)) i := by
              conv_lhs => rw [← Nat.mod_add_div k p]
              rw [pow_add, pow_mul, hσe_pow, one_pow, mul_one]
            refine ⟨p - k % p, ?_⟩
            rw [← hk, hkmod, ← Equiv.Perm.mul_apply, ← pow_add,
              Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt k hp.pos)), hσe_pow]
            rfl
          trans := fun {i j l} hij hjl => by
            obtain ⟨a, ha⟩ := hij
            obtain ⟨b, hb⟩ := hjl
            refine ⟨b + a, ?_⟩
            rw [pow_add, Equiv.Perm.mul_apply, ha, hb] } }
  let rep : ι → ι := fun i => Quotient.out (Quotient.mk orbSetoid i)
  have hrep_mem : ∀ i, ∃ k, (σe ^ k) (rep i) = i :=
    fun i => Quotient.exact (Quotient.out_eq (Quotient.mk orbSetoid i))
  have hrep_eq : ∀ {i j : ι}, (∃ k, (σe ^ k) i = j) → rep i = rep j := by
    intro i j hij
    exact congrArg Quotient.out (Quotient.sound hij)
  let τfun : ∀ (I : ι), σe I = I → L I →+* L I := fun I h =>
    { toFun := fun x => (F (Pi.single I x)) I
      map_one' := by
        have h1 : F (Pi.single I (1 : L I)) = Pi.single I (1 : L I) := by
          rw [hσe_spec I, h]
        rw [h1, Pi.single_eq_same]
      map_mul' := by
        intro x y
        rw [Pi.single_mul, map_mul, Pi.mul_apply]
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [Pi.single_add, map_add, Pi.add_apply] }
  have hτfun : ∀ (I : ι) (h : σe I = I) (y : ∀ i, L i), (F y) I = τfun I h (y I) := by
    intro I h y
    have h1 : y * (Pi.single I (1 : L I)) = Pi.single I (y I) :=
      kgLangCNormAux_mul_single_one y I
    have h2 := congrArg F h1
    rw [map_mul, hσe_spec I, h] at h2
    have h3 := congrArg (fun z => z I) h2
    rw [Pi.mul_apply, Pi.single_eq_same, mul_one] at h3
    simpa [τfun] using h3
  have hτpow : ∀ (I : ι) (h : σe I = I) (m : ℕ) (y : ∀ i, L i),
      (F ^ m) y I = (τfun I h ^ m) (y I) := by
    intro I h m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        have h1 : (F ^ (m + 1)) y = F ((F ^ m) y) := by rw [pow_succ']; rfl
        rw [h1, hτfun I h, ih, pow_succ']
        rfl
  have hτ_support : ∀ (I : ι) (h : σe I = I) (x : L I),
      F (Pi.single I x) = Pi.single I (τfun I h x) := by
    intro I h x
    apply kgLangCNormAux_single_support
    have hfix1 : F (Pi.single I (1 : L I)) = Pi.single I (1 : L I) := by
      rw [hσe_spec I, h]
    have h2 : (Pi.single I (1 : L I) : ∀ i, L i) * Pi.single I x = Pi.single I x := by
      rw [← Pi.single_mul, one_mul]
    rw [← hfix1, ← map_mul, h2]
  have hτ_inj : ∀ (I : ι) (h : σe I = I), Function.Injective (τfun I h) := by
    intro I h x y hxy
    have h2 : F (Pi.single I x) = F (Pi.single I y) := by
      rw [hτ_support I h x, hτ_support I h y, hxy]
    have h3 := F.injective h2
    simpa using congrFun h3 I
  let tauEquiv : ∀ (I : ι), σe I = I → L I ≃+* L I := fun I h =>
    RingEquiv.ofBijective (τfun I h) ⟨hτ_inj I h, Finite.injective_iff_surjective.mp (hτ_inj I h)⟩
  have htauEquiv_apply : ∀ (I : ι) (h : σe I = I) (x : L I), tauEquiv I h x = τfun I h x :=
    fun I h x => rfl
  have hτpow_eq : ∀ (I : ι) (h : σe I = I) (m : ℕ) (y : ∀ i, L i),
      (F ^ m) y I = ((tauEquiv I h) ^ m) (y I) := by
    intro I h m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        have h1 : (F ^ (m + 1)) y = F ((F ^ m) y) := by rw [pow_succ']; rfl
        rw [h1, hτfun I h, ih, pow_succ']
        rfl
  have hτpow_one : ∀ (I : ι) (h : σe I = I), (tauEquiv I h) ^ p = 1 := by
    intro I h
    ext x
    have h1 := hτpow_eq I h p (Pi.single I x)
    rw [hFp] at h1
    simpa using h1.symm
  have hτ_ne_one : ∀ (I : ι) (h : σe I = I), tauEquiv I h ≠ 1 := by
    intro I h h1
    have hidem : IsIdempotentElem (Pi.single I (1 : L I) : ∀ i, L i) := by
      rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
    have hne : (Pi.single I (1 : L I) : ∀ i, L i) ≠ 0 := kgLangCNormAux_single_ne_zero I
    have hfix : F (Pi.single I (1 : L I) : ∀ i, L i) = Pi.single I (1 : L I) := by
      rw [hσe_spec I, h]
    obtain ⟨x, hx⟩ := hstar _ hidem hne hfix
    apply hx
    have h2 : (Pi.single I (1 : L I) : ∀ i, L i) * x = Pi.single I (x I) := by
      rw [mul_comm, kgLangCNormAux_mul_single_one x I]
    rw [h2, hτ_support I h (x I)]
    congr 1
    rw [← htauEquiv_apply I h (x I), h1]
    rfl
  have hτ_order : ∀ (I : ι) (h : σe I = I), orderOf (tauEquiv I h) = p :=
    fun I h => orderOf_eq_prime (hτpow_one I h) (hτ_ne_one I h)
  intro c hc
  let cv : ∀ i, L i := (c : ∀ i, L i)
  have hcv : F cv = cv := by simpa [cv] using hc
  have hcvk : ∀ m, (F ^ m) cv = cv := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', RingAut.mul_apply, ih, hcv]
  have hcI_ne : ∀ I, cv I ≠ 0 := by
    intro I h0
    have h1 : cv * ((c⁻¹ : (∀ i, L i)ˣ) : ∀ i, L i) = 1 := by
      show (c : ∀ i, L i) * ((c⁻¹ : (∀ i, L i)ˣ) : ∀ i, L i) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 := congrFun h1 I
    rw [Pi.mul_apply, h0, zero_mul, Pi.one_apply] at h2
    exact one_ne_zero h2.symm
  have hfixed_exists : ∀ (I : ι) (h : σe I = I),
      ∃ l : L I, ∏ m ∈ Finset.range p, (tauEquiv I h ^ m) l = cv I := by
    intro I h
    have hcI : tauEquiv I h (cv I) = cv I := by
      rw [htauEquiv_apply I h (cv I)]
      have h1 := hτfun I h cv
      rw [hcv] at h1
      exact h1.symm
    obtain ⟨l, _, hl⟩ := CFSG.Quasithin.Vol2.Ch10Reselect.gd_norm_surj
      (tauEquiv I h) (hτ_order I h).symm hp.pos (cv I) (hcI_ne I) hcI
    exact ⟨l, hl⟩
  let lf : ∀ (I : ι) (h : σe I = I), L I := fun I h => Classical.choose (hfixed_exists I h)
  have hlf : ∀ (I : ι) (h : σe I = I),
      ∏ m ∈ Finset.range p, (tauEquiv I h ^ m) (lf I h) = cv I :=
    fun I h => Classical.choose_spec (hfixed_exists I h)
  let s : (I : ι) → L I := fun I =>
    if h : σe I = I then lf I h
    else if I = rep I then cv I else 1
  have hs_coord : ∀ I : ι, (∏ m ∈ Finset.range p, (F ^ m) s) I = cv I := by
    intro I
    by_cases hfix : σe I = I
    · have hsI : s I = lf I hfix := by
        dsimp only [s]
        rw [dif_pos hfix]
      calc (∏ m ∈ Finset.range p, (F ^ m) s) I
          = ∏ m ∈ Finset.range p, (F ^ m) s I :=
              Finset.prod_apply I (Finset.range p) (fun m => (F ^ m) s)
        _ = ∏ m ∈ Finset.range p, (tauEquiv I hfix ^ m) (s I) := by
              refine Finset.prod_congr rfl (fun m _ => ?_)
              rw [hτpow_eq I hfix m s]
        _ = ∏ m ∈ Finset.range p, (tauEquiv I hfix ^ m) (lf I hfix) := by rw [hsI]
        _ = cv I := hlf I hfix
    · have hsymm_pow : ∀ m, (σe.symm ^ m : Equiv.Perm ι) = (σe ^ m)⁻¹ := by
        intro m
        change ((σe⁻¹) ^ m : Equiv.Perm ι) = (σe ^ m)⁻¹
        exact inv_pow σe m
      have happly_inv : ∀ (m : ℕ) (x : ι), (σe ^ m) ((σe.symm ^ m) x) = x := by
        intro m x
        rw [hsymm_pow m]
        exact Equiv.apply_symm_apply (σe ^ m) x
      have hinv_apply : ∀ (m : ℕ) (x : ι), (σe.symm ^ m) ((σe ^ m) x) = x := by
        intro m x
        rw [hsymm_pow m]
        exact Equiv.symm_apply_apply (σe ^ m) x
      obtain ⟨k0, hk0⟩ := hrep_mem I
      let k := k0 % p
      have hklt : k < p := Nat.mod_lt _ hp.pos
      have hpow_mod : (σe ^ k0 : Equiv.Perm ι) = σe ^ (k0 % p) := by
        conv_lhs => rw [← Nat.mod_add_div k0 p]
        rw [pow_add, pow_mul, hσe_pow, one_pow, mul_one]
      have hkr : (σe ^ k) (rep I) = I := by
        show (σe ^ (k0 % p)) (rep I) = I
        rw [← hpow_mod]
        exact hk0
      have hr_ne : σe (rep I) ≠ rep I := by
        intro hrr
        have hkr' : (σe ^ k) (rep I) = rep I := by
          induction k with
          | zero => rfl
          | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, hrr, ih]
        have hIr : I = rep I := by
          conv_lhs => rw [← hkr]
          exact hkr'
        exact hfix (by rw [hIr, hrr])
      have horb : ∀ a b, a < p → b < p → (σe ^ a) (rep I) = (σe ^ b) (rep I) → a = b := by
        intro a b ha hb hab
        rcases lt_trichotomy a b with hlt | heq | hgt
        · exfalso
          have h1 : (σe ^ (b - a)) (rep I) = rep I := by
            have h2 : (σe.symm ^ a) ((σe ^ b) (rep I)) = (σe ^ (b - a)) (rep I) := by
              conv_lhs => rw [show b = a + (b - a) from (Nat.add_sub_of_le (le_of_lt hlt)).symm]
              rw [pow_add, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hsymm_pow a,
                inv_mul_cancel, Equiv.Perm.one_apply]
            rw [← hab, hinv_apply a (rep I)] at h2
            exact h2.symm
          exact absurd h1 (kgLangCNormAux_pow_ne_self σe hp hσe_pow hr_ne
            (Nat.sub_pos_of_lt hlt) (by omega))
        · exact heq
        · exfalso
          have h1 : (σe ^ (a - b)) (rep I) = rep I := by
            have h2 : (σe.symm ^ b) ((σe ^ a) (rep I)) = (σe ^ (a - b)) (rep I) := by
              conv_lhs => rw [show a = b + (a - b) from (Nat.add_sub_of_le (le_of_lt hgt)).symm]
              rw [pow_add, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hsymm_pow b,
                inv_mul_cancel, Equiv.Perm.one_apply]
            rw [hab, hinv_apply b (rep I)] at h2
            exact h2.symm
          exact absurd h1 (kgLangCNormAux_pow_ne_self σe hp hσe_pow hr_ne
            (Nat.sub_pos_of_lt hgt) (by omega))
      have hj_iff : ∀ m, m < p → ((σe.symm ^ m) I = rep I ↔ m = k) := by
        intro m hm
        constructor
        · intro h
          have h1 : (σe ^ m) (rep I) = I := by
            rw [← h, happly_inv m I]
          have h2 : (σe ^ m) (rep I) = (σe ^ k) (rep I) := by rw [h1, hkr]
          exact horb m k hm hklt h2
        · intro h
          rw [h]
          conv_lhs => rw [← hkr]
          exact hinv_apply k (rep I)
      have hs_j : ∀ m, m < p →
          s ((σe.symm ^ m) I) = if m = k then cv ((σe.symm ^ m) I) else 1 := by
        intro m hm
        have hnotfix_j : σe ((σe.symm ^ m) I) ≠ (σe.symm ^ m) I := by
          intro hJ
          obtain ⟨a, ha⟩ := (show ∃ a, (σe ^ a) ((σe.symm ^ m) I) = I from ⟨m, happly_inv m I⟩)
          have hall : ∀ a, (σe ^ a) ((σe.symm ^ m) I) = (σe.symm ^ m) I := by
            intro a
            induction a with
            | zero => rfl
            | succ a ih => rw [pow_succ, Equiv.Perm.mul_apply, hJ, ih]
          have hIm : I = (σe.symm ^ m) I := by
            conv_lhs => rw [← ha]
            exact hall a
          exact hfix (by rw [hIm, hJ])
        have hrep_j : rep ((σe.symm ^ m) I) = rep I := hrep_eq ⟨m, happly_inv m I⟩
        have hsdef : s ((σe.symm ^ m) I) =
            (if (σe.symm ^ m) I = rep I then cv ((σe.symm ^ m) I) else 1) := by
          have h1 : s ((σe.symm ^ m) I) =
              (if (σe.symm ^ m) I = rep ((σe.symm ^ m) I) then
                cv ((σe.symm ^ m) I) else 1) := by
            simp only [s, dif_neg hnotfix_j]
          rw [h1, hrep_j]
        rw [hsdef]
        by_cases hmk : m = k
        · rw [if_pos ((hj_iff m hm).mpr hmk), if_pos hmk]
        · rw [if_neg (fun h => hmk ((hj_iff m hm).mp h)), if_neg hmk]
      let Ψ : ∀ (m : ℕ) (I : ι), L ((σe.symm ^ m) I) →+* L I :=
        fun m I => Classical.choose (hF_iter_b m I)
      have hΨ : ∀ (m : ℕ) (I : ι) (y : ∀ i, L i), (F ^ m) y I = Ψ m I (y ((σe.symm ^ m) I)) :=
        fun m I y => Classical.choose_spec (hF_iter_b m I) y
      have hc_iter : Ψ k I (cv ((σe.symm ^ k) I)) = cv I := by
        rw [← hΨ k I cv]
        exact congrFun (hcvk k) I
      calc (∏ m ∈ Finset.range p, (F ^ m) s) I
          = ∏ m ∈ Finset.range p, (F ^ m) s I :=
              Finset.prod_apply I (Finset.range p) (fun m => (F ^ m) s)
        _ = ∏ m ∈ Finset.range p, Ψ m I (s ((σe.symm ^ m) I)) := by
              refine Finset.prod_congr rfl (fun m _ => ?_)
              rw [hΨ m I s]
        _ = Ψ k I (cv ((σe.symm ^ k) I)) := by
              rw [Finset.prod_eq_single k
                    (fun m hm hmk => by
                      rw [hs_j m (Finset.mem_range.mp hm), if_neg hmk, map_one])
                    (fun hknot => absurd (Finset.mem_range.mpr hklt) hknot),
                  hs_j k hklt, if_pos rfl]
        _ = cv I := hc_iter
  have hs_ne_zero : ∀ I, s I ≠ 0 := by
    intro I hzero
    have hprod := hs_coord I
    have h0 : (∏ m ∈ Finset.range p, (F ^ m) s) I = 0 := by
      rw [Finset.prod_apply I (Finset.range p) (fun m => (F ^ m) s)]
      refine Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hp.pos) ?_
      simp [hzero]
    rw [hprod] at h0
    exact hcI_ne I h0
  let sU : (∀ i, L i)ˣ :=
    { val := s
      inv := fun I => (s I)⁻¹
      val_inv := by
        funext I
        simpa [Pi.mul_apply] using mul_inv_cancel₀ (hs_ne_zero I)
      inv_val := by
        funext I
        simpa [Pi.mul_apply] using inv_mul_cancel₀ (hs_ne_zero I) }
  refine ⟨sU, ?_⟩
  funext I
  show cv I = (∏ m ∈ Finset.range p, (F ^ m) s) I
  exact (hs_coord I).symm
theorem kgLangC_normSurj {p : ℕ} (hp : p.Prime) {B : Type} [CommRing B] [Finite B] [IsReduced B]
    (β : B ≃+* B) (hβ : β ^ p = 1)
    (hstar : ∀ ε : B, IsIdempotentElem ε → ε ≠ 0 → β ε = ε → ∃ x : B, β (ε * x) ≠ ε * x) :
    ∀ c : Bˣ, β (c : B) = c → ∃ s : Bˣ, (c : B) = ∏ i ∈ Finset.range p, (β ^ i) (s : B) := by
  classical
  haveI hArt : IsArtinianRing B := isArtinian_of_finite
  letI hField : ∀ I : MaximalSpectrum B, Field (B ⧸ I.asIdeal) := fun I =>
    Ideal.Quotient.field I.asIdeal
  letI hFin : ∀ I : MaximalSpectrum B, Finite (B ⧸ I.asIdeal) := fun I =>
    Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let P := ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal
  let e : B ≃+* P := (IsArtinianRing.equivPi B).toRingEquiv
  let F : P ≃+* P := e.symm.trans (β.trans e)
  have hF_apply : ∀ y : B, F (e y) = e (β y) := by
    intro y
    change (e.symm.trans (β.trans e)) (e y) = e (β y)
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, e.symm_apply_apply]
  have hF_iter : ∀ (m : ℕ) (y : B), (F ^ m) (e y) = e ((β ^ m) y) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [pow_succ', RingAut.mul_apply, ih, hF_apply, pow_succ', RingAut.mul_apply]
  have hF : F ^ p = 1 := by
    ext y
    conv_lhs => rw [← e.apply_symm_apply y]
    rw [hF_iter p (e.symm y), hβ]
    simp
  have hstarP : ∀ ε : P, IsIdempotentElem ε → ε ≠ 0 → F ε = ε →
      ∃ x : P, F (ε * x) ≠ ε * x := by
    intro ε hidem hne hfix
    let εB : B := e.symm ε
    have hidemB : IsIdempotentElem εB := by
      rw [IsIdempotentElem] at hidem ⊢
      exact e.injective (by rw [map_mul, show e εB = ε from e.apply_symm_apply ε, hidem])
    have hneB : εB ≠ 0 := by
      intro h0
      apply hne
      rw [← show e εB = ε from e.apply_symm_apply ε]
      rw [h0, map_zero]
    have hfixB : β εB = εB := by
      apply e.injective
      rw [← hF_apply εB]
      rw [show e εB = ε from e.apply_symm_apply ε]
      exact hfix
    obtain ⟨xB, hxB⟩ := hstar εB hidemB hneB hfixB
    refine ⟨e xB, ?_⟩
    intro hcon
    apply hxB
    have h1 : e (β (εB * xB)) = e (εB * xB) := by
      rw [← hF_apply (εB * xB), map_mul, show e εB = ε from e.apply_symm_apply ε]
      exact hcon
    exact e.injective h1
  intro c hc
  let φ : Bˣ ≃* Pˣ := Units.mapEquiv e.toMulEquiv
  let c' : Pˣ := φ c
  have hc'_val : (c' : P) = e (c : B) := by
    change (Units.mapEquiv e.toMulEquiv c : P) = e (c : B)
    rw [Units.coe_mapEquiv]
    rfl
  have hc' : F (c' : P) = (c' : P) := by
    rw [hc'_val, hF_apply, hc]
  obtain ⟨s', hs'⟩ := kgLangCNormAux_normSurjPi
    (L := fun I : MaximalSpectrum B => B ⧸ I.asIdeal) hp F hF hstarP c' hc'
  let φs : Pˣ ≃* Bˣ := Units.mapEquiv e.symm.toMulEquiv
  let sU : Bˣ := φs s'
  have hsU_val : (sU : B) = e.symm (s' : P) := by
    change (Units.mapEquiv e.symm.toMulEquiv s' : B) = e.symm (s' : P)
    rw [Units.coe_mapEquiv]
    rfl
  have hsU_e : e (sU : B) = (s' : P) := by
    rw [hsU_val, e.apply_symm_apply]
  have hterm : ∀ m, e.symm ((F ^ m) (s' : P)) = (β ^ m) (sU : B) := by
    intro m
    have h2 : (F ^ m) (s' : P) = e ((β ^ m) (sU : B)) := by
      rw [← hsU_e]
      exact hF_iter m (sU : B)
    rw [h2, e.symm_apply_apply]
  refine ⟨sU, ?_⟩
  calc (c : B) = e.symm (c' : P) := by rw [hc'_val, e.symm_apply_apply]
    _ = e.symm (∏ m ∈ Finset.range p, (F ^ m) (s' : P)) := by rw [hs']
    _ = ∏ m ∈ Finset.range p, e.symm ((F ^ m) (s' : P)) := map_prod e.symm _ _
    _ = ∏ m ∈ Finset.range p, (β ^ m) (sU : B) :=
          Finset.prod_congr rfl (fun m _ => hterm m)

theorem kgLangC_unitary_h90 {p : ℕ} (hp : p.Prime) {B : Type} [CommRing B] [Finite B] [IsReduced B]
    [CharP B 2] (β : B ≃+* B) (hβ : β ^ p = 1)
    (hstar : ∀ ε : B, IsIdempotentElem ε → ε ≠ 0 → β ε = ε → ∃ x : B, β (ε * x) ≠ ε * x)
    (τ : B ≃+* B) (hτ : τ * τ = 1) (hβτ : β * τ = τ * β) :
    ∀ c : Bˣ, (c : B) * τ c = 1 → ∏ i ∈ Finset.range p, (β ^ i) (c : B) = 1 →
      ∃ s : Bˣ, (s : B) * τ s = 1 ∧ (c : B) = ((s⁻¹ : Bˣ) : B) * β s := by
  classical
  intro c hcτ hcN
  let β' : MulAut Bˣ := Units.mapEquiv β
  let τ' : MulAut Bˣ := Units.mapEquiv τ
  have hβ'val : ∀ (i : ℕ) (u : Bˣ), (((β' ^ i) u : Bˣ) : B) = (β ^ i) (u : B) := by
    intro i
    induction i with
    | zero => intro u; rfl
    | succ i ih =>
      intro u
      rw [pow_succ, MulAut.mul_apply, ih]
      change (β ^ i) (β (u : B)) = (β ^ (i + 1)) (u : B)
      rw [pow_succ]
      rfl
  have hlist_eq : ∀ (f : ℕ → Bˣ), ((List.range p).map f).prod = ∏ i ∈ Finset.range p, f i := by
    intro f
    rw [← List.prod_toFinset f List.nodup_range, List.toFinset_range]
  have hval_prod : ∀ (f : ℕ → Bˣ), ((((List.range p).map f).prod : Bˣ) : B) =
      ∏ i ∈ Finset.range p, (f i : B) := by
    intro f
    rw [hlist_eq f]
    exact map_prod (Units.coeHom B) f (Finset.range p)
  have hnormSurj : ∀ d : Bˣ, β' d = d →
      ∃ s, d = ((List.range p).map fun i => (β' ^ i) s).prod := by
    intro d hd
    have hdfix : β (d : B) = (d : B) := by
      have h := congrArg (fun u : Bˣ => (u : B)) hd
      simpa [β'] using h
    obtain ⟨s, hs⟩ := kgLangC_normSurj hp β hβ hstar d hdfix
    refine ⟨s, ?_⟩
    apply Units.ext
    rw [hval_prod (fun i => (β' ^ i) s)]
    rw [hs]
    exact Finset.prod_congr rfl (fun i _ => (hβ'val i s).symm)
  have hnorm_c : ((List.range p).map fun i => (β' ^ i) c).prod = 1 := by
    apply Units.ext
    rw [hval_prod (fun i => (β' ^ i) c), Units.val_one]
    exact (Finset.prod_congr rfl (fun i _ => hβ'val i c)).trans hcN
  have hβ' : β' ^ p = 1 := by
    ext u
    rw [hβ'val p u]
    have hh : (β ^ p) (u : B) = (u : B) := by
      have := congrArg (fun f : B ≃+* B => f (u : B)) hβ
      simpa using this
    simpa using hh
  obtain ⟨s, hs⟩ := (kgLangH90_iff_normSurj β' hβ').mpr hnormSurj c hnorm_c
  have hττ_val : ∀ x : B, τ (τ x) = x := by
    intro x
    have h := congrArg (fun f : B ≃+* B => f x) hτ
    simpa using h
  have hβτ_val : ∀ x : B, β (τ x) = τ (β x) := by
    intro x
    have h := congrArg (fun f : B ≃+* B => f x) hβτ
    simpa using h
  have hsβ : β' s = s * c := by
    rw [hs, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsval : β (s : B) = (s : B) * (c : B) := by
    have h := congrArg (fun u : Bˣ => (u : B)) hsβ
    simpa [β'] using h
  have hcτ' : c * τ' c = 1 := by
    apply Units.ext
    change (c : B) * τ (c : B) = 1
    exact hcτ
  let b : Bˣ := s * τ' s
  have hbval : (b : B) = (s : B) * τ (s : B) := rfl
  have hβb : β' b = b := by
    apply Units.ext
    change β ((s : B) * τ (s : B)) = (s : B) * τ (s : B)
    rw [map_mul, hβτ_val, hsval, map_mul]
    rw [mul_mul_mul_comm, hcτ, mul_one]
  have hτb : τ' b = b := by
    apply Units.ext
    change τ ((s : B) * τ (s : B)) = (s : B) * τ (s : B)
    rw [map_mul, hττ_val]
    exact mul_comm _ _
  have hsq_inj : Function.Injective (fun x : B => x ^ 2) := by
    intro x y hxy
    have hxy' : x ^ 2 = y ^ 2 := hxy
    have h0 : (x + y) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hxy', ← two_mul, CharTwo.two_eq_zero, zero_mul]
    have hnil : IsNilpotent (x + y) := ⟨2, h0⟩
    have hz := IsReduced.eq_zero (x + y) hnil
    exact CharTwo.add_eq_zero.mp hz
  have hsq_surj : Function.Surjective (fun x : B => x ^ 2) :=
    (Finite.injective_iff_surjective).mp hsq_inj
  obtain ⟨z, hz⟩ := hsq_surj ((b⁻¹ : Bˣ) : B)
  have hzz : z * z = ((b⁻¹ : Bˣ) : B) := by rw [← pow_two]; exact hz
  have hzunit : IsUnit z := by
    rw [isUnit_iff_exists]
    refine ⟨z * (b : B), ?_, ?_⟩
    · rw [← mul_assoc, hzz, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rw [mul_comm z (b : B), mul_assoc, hzz, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let zU : Bˣ := hzunit.unit
  have hzUval : (zU : B) = z := hzunit.unit_spec
  have hzU2 : zU * zU = b⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, hzUval, hzz]
  have hzzU : (zU : B) * (zU : B) = ((b⁻¹ : Bˣ) : B) := by
    rw [← Units.val_mul]; exact congrArg (fun u : Bˣ => (u : B)) hzU2
  have hβzU : β' zU = zU := by
    have h1 : β' zU * β' zU = zU * zU := by
      rw [← map_mul, hzU2, map_inv, hβb]
    apply Units.ext
    apply hsq_inj
    have h := congrArg (fun u : Bˣ => (u : B)) h1
    simpa [Units.val_mul, pow_two] using h
  have hτzU : τ' zU = zU := by
    have h1 : τ' zU * τ' zU = zU * zU := by
      rw [← map_mul, hzU2, map_inv, hτb]
    apply Units.ext
    apply hsq_inj
    have h := congrArg (fun u : Bˣ => (u : B)) h1
    simpa [Units.val_mul, pow_two] using h
  have hτzU_val : τ (zU : B) = (zU : B) := congrArg (fun u : Bˣ => (u : B)) hτzU
  have hβzU_val : β (zU : B) = (zU : B) := congrArg (fun u : Bˣ => (u : B)) hβzU
  refine ⟨s * zU, ?_, ?_⟩
  · change ((s : B) * (zU : B)) * τ ((s : B) * (zU : B)) = 1
    rw [map_mul, hτzU_val]
    rw [mul_mul_mul_comm, ← hbval, hzzU, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · let s' : Bˣ := s * zU
    have hs'val : (s' : B) = (s : B) * (zU : B) := rfl
    have hkey : (s' : B) * (c : B) = β (s' : B) := by
      rw [hs'val]
      change ((s : B) * (zU : B)) * (c : B) = β ((s : B) * (zU : B))
      rw [map_mul, hβzU_val]
      conv_rhs => rw [hsval]
      ring
    calc (c : B) = ((s'⁻¹ : Bˣ) : B) * ((s' : B) * (c : B)) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = ((s'⁻¹ : Bˣ) : B) * β (s' : B) := by rw [hkey]

end CFSG.StandardType
