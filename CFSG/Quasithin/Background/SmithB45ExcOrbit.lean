module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeights
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

namespace CFSG.Quasithin.B45Exc

open Module Polynomial CFSG.QuasithinUnique.Setup.Family

section Comb

theorem dvd_sum_of_free_iterate {α : Type*} [DecidableEq α] (σ : α → α) (m : ℕ) (hm : 0 < m)
    (d : α → ℕ) (R : Finset α) (hσR : ∀ x ∈ R, σ x ∈ R) (hper : ∀ x ∈ R, σ^[m] x = x)
    (hfree : ∀ x ∈ R, ∀ j, 0 < j → j < m → σ^[j] x ≠ x) (hd : ∀ x ∈ R, d (σ x) = d x) :
    m ∣ ∑ x ∈ R, d x := by
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | ⟨x, hx⟩
  · simp [hR]
  have hiter : ∀ j, σ^[j] x ∈ R := by
    intro j
    induction j with
    | zero => exact hx
    | succ j ihj =>
      rw [Function.iterate_succ_apply']
      exact hσR _ ihj
  have hdj : ∀ j, d (σ^[j] x) = d x := by
    intro j
    induction j with
    | zero => rfl
    | succ j ihj =>
      rw [Function.iterate_succ_apply', hd _ (hiter j), ihj]
  have hinjR : ∀ a ∈ R, ∀ b ∈ R, σ a = σ b → a = b := by
    intro a ha b hb hab
    have h1 : σ^[m - 1] (σ a) = σ^[m - 1] (σ b) := by rw [hab]
    rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply,
      Nat.succ_eq_add_one, Nat.sub_add_cancel hm, hper a ha, hper b hb] at h1
    exact h1
  set O : Finset α := (Finset.range m).image (fun j => σ^[j] x) with hO
  have hOR : O ⊆ R := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact hiter j
  have hinj : Set.InjOn (fun j => σ^[j] x) (Finset.range m : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : σ^[m - j] (σ^[i] x) = σ^[m - j] (σ^[j] x) := by
        simp only at hij
        rw [hij]
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hj.le, hper x hx] at h1
      exact hfree x hx (m - j + i) (by omega) (by omega) h1
    · have h1 : σ^[m - i] (σ^[i] x) = σ^[m - i] (σ^[j] x) := by
        simp only at hij
        rw [hij]
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hi.le, hper x hx] at h1
      exact hfree x hx (m - i + j) (by omega) (by omega) h1.symm
  have hOcard : O.card = m := by
    rw [hO, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsumO : ∑ y ∈ O, d y = m * d x := by
    rw [Finset.sum_congr rfl fun y hy => ?_, Finset.sum_const, hOcard, smul_eq_mul]
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact hdj j
  have hσc : ∀ y ∈ R \ O, σ y ∈ R \ O := by
    intro y hy
    obtain ⟨hyR, hyO⟩ := Finset.mem_sdiff.1 hy
    refine Finset.mem_sdiff.2 ⟨hσR y hyR, fun hσO => hyO ?_⟩
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hσO
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      have e1 : σ (σ^[m - 1] x) = x := by
        rw [← Function.iterate_succ_apply' σ (m - 1) x, Nat.succ_eq_add_one,
          Nat.sub_add_cancel hm, hper x hx]
      have h1 : σ y = σ (σ^[m - 1] x) := by
        rw [e1]
        exact hjx.symm
      rw [hinjR y hyR _ (hiter _) h1]
      exact Finset.mem_image.2 ⟨m - 1, Finset.mem_range.2 (by omega), rfl⟩
    · have e1 : σ (σ^[j - 1] x) = σ^[j] x := by
        rw [← Function.iterate_succ_apply' σ (j - 1) x, Nat.succ_eq_add_one,
          Nat.sub_add_cancel hpos]
      have h1 : σ y = σ (σ^[j - 1] x) := by
        rw [e1]
        exact hjx.symm
      rw [hinjR y hyR _ (hiter _) h1]
      exact Finset.mem_image.2 ⟨j - 1, Finset.mem_range.2 (by omega), rfl⟩
  have hxO : x ∈ O := Finset.mem_image.2 ⟨0, Finset.mem_range.2 hm, rfl⟩
  have hlt : R \ O ⊂ R := Finset.sdiff_ssubset hOR ⟨x, hxO⟩
  have hrec := ih (R \ O) hlt (fun y hy => hσc y hy)
    (fun y hy => hper y (Finset.mem_sdiff.1 hy).1)
    (fun y hy => hfree y (Finset.mem_sdiff.1 hy).1)
    (fun y hy => hd y (Finset.mem_sdiff.1 hy).1)
  rw [← Finset.sum_sdiff hOR, hsumO]
  exact dvd_add hrec (dvd_mul_right m _)

end Comb

section Indep

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_biSup_of_iSupIndep {ι : Type*} [DecidableEq ι] {Y : ι → Submodule K V}
    (hY : iSupIndep Y) (S : Finset ι) :
    finrank K (⨆ i ∈ S, Y i : Submodule K V) = ∑ i ∈ S, finrank K (Y i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hdisj : Disjoint (Y a) (⨆ i ∈ S, Y i) := by
      have := hY.disjoint_biSup (y := (S : Set ι)) (x := a) (by simpa using ha)
      simpa using this
    have := Submodule.finrank_sup_add_finrank_inf_eq (Y a) (⨆ i ∈ S, Y i)
    rw [hdisj.eq_bot, finrank_bot] at this
    omega

end Indep

section Orbit

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

omit [Module.Finite (ZMod 2) E] in
theorem eq_zero_of_mem_range_sub1 {p : ℕ} (hp : Odd p) {y : E ≃ₗ[ZMod 2] E} (hy : y ^ p = 1)
    {v : E} (hv : v ∈ LinearMap.range (sub1 y)) (hfix : y v = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  rw [sub1_apply'] at hfix ⊢
  have h2 : y (y u) = u := by
    have h1 : y (y u) + y u = u + y u := by
      rw [add_comm u]
      rwa [map_add] at hfix
    exact add_right_cancel h1
  have hpow : ∀ q : ℕ, (y ^ (2 * q)) u = u := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 2 * (q + 1) = 2 + 2 * q by ring, pow_add, LinearEquiv.mul_apply, ih, pow_two,
        LinearEquiv.mul_apply, h2]
  obtain ⟨q, rfl⟩ := hp
  have h1 : (y ^ (2 * q + 1)) u = u := by rw [hy]; rfl
  rw [pow_succ', LinearEquiv.mul_apply, hpow q] at h1
  rw [h1, e_add_self]

omit [Module.Finite (ZMod 2) E] in
theorem apply_mem_range_sub1 (y : E ≃ₗ[ZMod 2] E) {v : E}
    (hv : v ∈ LinearMap.range (sub1 y)) : y v ∈ LinearMap.range (sub1 y) := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨y u, ?_⟩
  simp [sub1_apply]

omit [Module.Finite (ZMod 2) E] in
theorem range_sub1_pow_le (y : E ≃ₗ[ZMod 2] E) (k : ℕ) :
    LinearMap.range (sub1 (y ^ k)) ≤ LinearMap.range (sub1 y) := by
  induction k with
  | zero =>
    rintro _ ⟨u, rfl⟩
    simp [sub1_apply]
  | succ k ih =>
    rintro _ ⟨u, rfl⟩
    have h1 : sub1 (y ^ (k + 1)) u = sub1 y ((y ^ k) u) + sub1 (y ^ k) u := by
      simp only [sub1_apply, pow_succ', LinearEquiv.mul_apply]
      abel
    rw [h1]
    exact Submodule.add_mem _ ⟨_, rfl⟩ (ih ⟨u, rfl⟩)

omit [Module.Finite (ZMod 2) E] in
theorem conj_apply_mem_range_sub1 {y g : E ≃ₗ[ZMod 2] E} {k : ℕ} (hgy : g * y * g⁻¹ = y ^ k)
    {v : E} (hv : v ∈ LinearMap.range (sub1 y)) : g v ∈ LinearMap.range (sub1 y) := by
  obtain ⟨u, rfl⟩ := hv
  have hgg : g⁻¹ (g u) = u := by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have h1 : g (sub1 y u) = sub1 (y ^ k) (g u) := by
    rw [← hgy]
    simp only [sub1_apply, map_sub, LinearEquiv.mul_apply, hgg]
  rw [h1]
  exact range_sub1_pow_le y k ⟨g u, rfl⟩

end Orbit

end CFSG.Quasithin.B45Exc

namespace CFSG.Quasithin.B45Exc

open Module Polynomial CFSG.QuasithinUnique.Setup.Family
open scoped TensorProduct

section Main

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

@[expose] noncomputable def restrictEquiv (y : E ≃ₗ[ZMod 2] E) (T : Submodule (ZMod 2) E)
    (hT : ∀ v ∈ T, y v ∈ T) : T ≃ₗ[ZMod 2] T :=
  LinearEquiv.ofBijective ((y : E →ₗ[ZMod 2] E).restrict hT)
    (by
      have hinj : Function.Injective ((y : E →ₗ[ZMod 2] E).restrict hT) := by
        intro a b hab
        apply Subtype.ext
        have := congrArg Subtype.val hab
        simpa using this
      exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩)

theorem restrictEquiv_apply (y : E ≃ₗ[ZMod 2] E) (T : Submodule (ZMod 2) E)
    (hT : ∀ v ∈ T, y v ∈ T) (v : T) : (restrictEquiv y T hT v : E) = y v := rfl

theorem restrictEquiv_pow_apply (y : E ≃ₗ[ZMod 2] E) (T : Submodule (ZMod 2) E)
    (hT : ∀ v ∈ T, y v ∈ T) (n : ℕ) (v : T) :
    ((restrictEquiv y T hT ^ n) v : E) = (y ^ n) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, restrictEquiv_apply, ih, pow_succ',
      LinearEquiv.mul_apply]

theorem orderOf_dvd_finrank_of_algClosed {K V : Type*} [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {f h : V ≃ₗ[K] V} (hf : f ^ p = 1)
    (hfix : ∀ v : V, f v = v → v = 0) {k : ℕ} (hk : (k : ZMod p) ≠ 0)
    (hfh : h * f ^ k = f * h) :
    orderOf (k : ZMod p) ∣ finrank K V := by
  classical
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hp0 : 0 < p := hp.out.pos
  set F : Module.End K V := (f : V →ₗ[K] V) with hF
  have hFpow : ∀ n : ℕ, F ^ n = ((f ^ n : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      rfl
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact fun h2 => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hsep := Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero
  have hann : aeval F (X ^ p - C (1 : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hFpow, hf]
    exact sub_self _
  have hss := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree hann
  have htop := hss.iSup_eigenspace_eq_top
  set R : Finset K := (nthRootsFinset p (1 : K)).erase 1 with hR
  have hbot : ∀ μ : K, μ ∉ R → F.eigenspace μ = ⊥ := by
    intro μ hμ
    rw [eq_bot_iff]
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [Submodule.mem_bot]
    by_contra hv0
    apply hμ
    have hpow : ∀ n : ℕ, (F ^ n) v = μ ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ, mul_comm]
    have h1 : (F ^ p) v = v := by rw [hFpow, hf]; rfl
    rw [hpow p] at h1
    have hμp : μ ^ p = 1 := by
      by_contra hne
      have : (μ ^ p - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact hv0 ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
    have hμ1 : μ ≠ 1 := by
      rintro rfl
      exact hv0 (hfix v (by rw [one_smul] at hv; exact hv))
    rw [hR, Finset.mem_erase, mem_nthRootsFinset hp0]
    exact ⟨hμ1, hμp⟩
  have hsup : (⨆ μ ∈ R, F.eigenspace μ) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ R
    · exact le_biSup (fun μ => F.eigenspace μ) hμ
    · rw [hbot μ hμ]
      exact bot_le
  have hsum : finrank K V = ∑ μ ∈ R, finrank K (F.eigenspace μ) := by
    rw [← finrank_biSup_of_iSupIndep (Module.End.eigenspaces_iSupIndep F) R, hsup, finrank_top]
  have hmap : ∀ μ : K, (F.eigenspace μ).map (h : V →ₗ[K] V) ≤ F.eigenspace (μ ^ k) := by
    intro μ
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [Module.End.mem_eigenspace_iff]
    have hfk : ∀ n : ℕ, (f ^ n) v = μ ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul]
        have : f v = μ • v := hv
        rw [this, smul_smul, pow_succ, mul_comm]
    have e1 : f (h v) = h ((f ^ k) v) := by
      rw [← LinearEquiv.mul_apply, ← hfh, LinearEquiv.mul_apply]
    show f (h v) = μ ^ k • h v
    rw [e1, hfk k, map_smul]
  have hle : ∀ μ : K, finrank K (F.eigenspace μ) ≤ finrank K (F.eigenspace (μ ^ k)) := by
    intro μ
    rw [← LinearEquiv.finrank_map_eq h (F.eigenspace μ)]
    exact Submodule.finrank_mono (hmap μ)
  set m := orderOf (k : ZMod p) with hm
  have hp1 : 2 ≤ p := hp.out.two_le
  have hm0 : 0 < m := by
    rw [hm]
    exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one hk⟩)
  have hiter : ∀ (j : ℕ) (μ : K), (fun x : K => x ^ k)^[j] μ = μ ^ (k ^ j) := by
    intro j
    induction j with
    | zero => intro μ; simp
    | succ j ih =>
      intro μ
      rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ, mul_comm]
  have hRmem : ∀ μ ∈ R, μ ^ p = 1 ∧ μ ≠ 1 := by
    intro μ hμ
    rw [hR, Finset.mem_erase, mem_nthRootsFinset hp0] at hμ
    exact ⟨hμ.2, hμ.1⟩
  have hordμ : ∀ μ ∈ R, orderOf μ = p := by
    intro μ hμ
    obtain ⟨h1, h2⟩ := hRmem μ hμ
    exact orderOf_eq_prime h1 h2
  have hpowμ : ∀ μ ∈ R, ∀ n : ℕ, μ ^ n = μ ↔ (n : ZMod p) = 1 := by
    intro μ hμ n
    obtain ⟨hμp, hμ1⟩ := hRmem μ hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp0.ne'] at hμp
      exact zero_ne_one hμp
    constructor
    · intro h1
      rcases Nat.eq_zero_or_pos n with h0 | hn
      · subst h0
        exact absurd h1.symm (by rw [pow_zero]; exact hμ1)
      have h2 : μ ^ (n - 1) = 1 := by
        have h3 : μ ^ (n - 1) * μ = 1 * μ := by
          rw [← pow_succ, Nat.sub_add_cancel hn, one_mul, h1]
        exact mul_right_cancel₀ hμ0 h3
      have h4 : p ∣ n - 1 := by
        rw [← hordμ μ hμ]
        exact orderOf_dvd_of_pow_eq_one h2
      have h5 : ((n - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h4
      rw [Nat.cast_sub hn, Nat.cast_one, sub_eq_zero] at h5
      exact h5
    · intro h1
      have h2 : n ≡ 1 [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
        exact h1
      have := pow_eq_pow_of_modEq h2 hμp
      rwa [pow_one] at this
  have hσR : ∀ μ ∈ R, μ ^ k ∈ R := by
    intro μ hμ
    obtain ⟨h1, h2⟩ := hRmem μ hμ
    rw [hR, Finset.mem_erase, mem_nthRootsFinset hp0]
    refine ⟨fun h3 => ?_, by rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]⟩
    have h4 : orderOf μ ∣ k := orderOf_dvd_of_pow_eq_one h3
    rw [hordμ μ hμ] at h4
    exact hk ((ZMod.natCast_eq_zero_iff k p).2 h4)
  have hper : ∀ μ ∈ R, (fun x : K => x ^ k)^[m] μ = μ := by
    intro μ hμ
    rw [hiter, hpowμ μ hμ, Nat.cast_pow, hm, pow_orderOf_eq_one]
  have hfree : ∀ μ ∈ R, ∀ j, 0 < j → j < m → (fun x : K => x ^ k)^[j] μ ≠ μ := by
    intro μ hμ j hj0 hjm h1
    rw [hiter, hpowμ μ hμ, Nat.cast_pow] at h1
    have := orderOf_le_of_pow_eq_one hj0 h1
    omega
  have hd : ∀ μ ∈ R, finrank K (F.eigenspace (μ ^ k)) = finrank K (F.eigenspace μ) := by
    intro μ hμ
    refine le_antisymm ?_ (hle μ)
    have hchain : ∀ j, finrank K (F.eigenspace μ) ≤
        finrank K (F.eigenspace ((fun x : K => x ^ k)^[j] μ)) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih => rw [Function.iterate_succ_apply']; exact ih.trans (hle _)
    have hchain' : ∀ j, finrank K (F.eigenspace ((fun x : K => x ^ k)^[1] μ)) ≤
        finrank K (F.eigenspace ((fun x : K => x ^ k)^[j + 1] μ)) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply' _ (j + 1)]
        exact ih.trans (hle _)
    have h1 := hchain' (m - 1)
    rw [Nat.sub_add_cancel hm0, hper μ hμ, Function.iterate_one] at h1
    exact h1
  rw [hsum]
  exact dvd_sum_of_free_iterate (fun x : K => x ^ k) m hm0 (fun μ => finrank K (F.eigenspace μ))
    R hσR hper hfree hd

theorem orderOf_dvd_finrank_range_sub1 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {y g : E ≃ₗ[ZMod 2] E} (hy : y ^ p = 1) {k : ℕ} (hgy : g * y * g⁻¹ = y ^ k) :
    orderOf (k : ZMod p) ∣ finrank (ZMod 2) (LinearMap.range (sub1 y)) := by
  classical
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set T := LinearMap.range (sub1 y) with hT
  by_cases hk : (k : ZMod p) = 0
  ·
    have hyk : y ^ k = 1 := by
      obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff k p).1 hk
      rw [hc, pow_mul, hy, one_pow]
    have hy1 : y = 1 := by
      rw [hyk] at hgy
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [hgy]; group
    have hT0 : T = ⊥ := by
      rw [hT, eq_bot_iff]
      rintro _ ⟨u, rfl⟩
      simp [sub1_apply, hy1]
    rw [hT0, finrank_bot]
    exact dvd_zero _
  have hyT : ∀ v ∈ T, y v ∈ T := fun v hv => apply_mem_range_sub1 y hv
  have hgT : ∀ v ∈ T, g v ∈ T := fun v hv => conj_apply_mem_range_sub1 hgy hv
  set yT := restrictEquiv y T hyT with hyTdef
  set gT := restrictEquiv g T hgT with hgTdef
  have hyTp : yT ^ p = 1 := by
    ext v
    rw [restrictEquiv_pow_apply, hy]
    rfl
  have hrelT : gT⁻¹ * yT ^ k = yT * gT⁻¹ := by
    have h1 : yT ^ k * gT = gT * yT := by
      ext v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, restrictEquiv_pow_apply,
        restrictEquiv_apply, restrictEquiv_apply, restrictEquiv_apply]
      rw [← hgy]
      simp only [LinearEquiv.mul_apply]
      congr 1
      rw [← LinearEquiv.mul_apply g⁻¹ g, inv_mul_cancel]
      rfl
    calc gT⁻¹ * yT ^ k = gT⁻¹ * (yT ^ k * gT) * gT⁻¹ := by group
      _ = gT⁻¹ * (gT * yT) * gT⁻¹ := by rw [h1]
      _ = yT * gT⁻¹ := by group
  set D : Module.End (ZMod 2) T := (yT : T →ₗ[ZMod 2] T) - 1 with hD
  have hDinj : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, hD, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have h1 : y (v : E) = v := congrArg Subtype.val hv
    exact eq_zero_of_mem_range_sub1 hodd hy v.2 h1
  set De : T ≃ₗ[ZMod 2] T :=
    LinearEquiv.ofBijective D ⟨hDinj, LinearMap.injective_iff_surjective.1 hDinj⟩ with hDe
  let K := AlgebraicClosure (ZMod 2)
  set f := yT.baseChange (ZMod 2) K T T with hf
  set h := (gT⁻¹).baseChange (ZMod 2) K T T with hh
  have hfp : f ^ p = 1 := by
    rw [hf, ← LinearEquiv.baseChange_pow, hyTp, LinearEquiv.baseChange_one]
  have hfh : h * f ^ k = f * h := by
    rw [hh, hf, ← LinearEquiv.baseChange_pow, ← LinearEquiv.baseChange_mul,
      ← LinearEquiv.baseChange_mul, hrelT]
  have hfix : ∀ w : K ⊗[ZMod 2] T, f w = w → w = 0 := by
    intro w hw
    have hDw : (De.baseChange (ZMod 2) K T T) w = 0 := by
      have e1 : ((De.baseChange (ZMod 2) K T T : K ⊗[ZMod 2] T ≃ₗ[K] K ⊗[ZMod 2] T) :
          K ⊗[ZMod 2] T →ₗ[K] K ⊗[ZMod 2] T) = D.baseChange K := by
        rw [LinearEquiv.coe_baseChange]
        rfl
      have e2 : D.baseChange K = (yT : T →ₗ[ZMod 2] T).baseChange K - 1 := by
        rw [hD, LinearMap.baseChange_sub, LinearMap.baseChange_one]
      have e3 : ((yT : T →ₗ[ZMod 2] T).baseChange K) = (f : K ⊗[ZMod 2] T →ₗ[K] _) := by
        rw [hf, LinearEquiv.coe_baseChange]
      have := LinearMap.congr_fun e1 w
      rw [LinearEquiv.coe_coe] at this
      rw [this, e2, e3, LinearMap.sub_apply, LinearEquiv.coe_coe, hw, Module.End.one_apply,
        sub_self]
    exact (LinearEquiv.map_eq_zero_iff _).1 hDw
  have hmain := orderOf_dvd_finrank_of_algClosed hp2 hfp hfix hk hfh
  rwa [Module.finrank_baseChange] at hmain

theorem orderOf_two_dvd_finrank_range_sub1 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {y : E ≃ₗ[ZMod 2] E} (hy : y ^ p = 1) :
    orderOf (2 : ZMod p) ∣ finrank (ZMod 2) (LinearMap.range (sub1 y)) := by
  classical
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set T := LinearMap.range (sub1 y) with hT
  have hyT : ∀ v ∈ T, y v ∈ T := fun v hv => apply_mem_range_sub1 y hv
  set yT := restrictEquiv y T hyT with hyTdef
  have hyTp : yT ^ p = 1 := by
    ext v
    rw [restrictEquiv_pow_apply, hy]
    rfl
  have : Finite T := Module.finite_of_finite (ZMod 2)
  have hpg : IsPGroup p (Subgroup.zpowers yT) := by
    have hdvd : orderOf yT ∣ p := orderOf_dvd_of_pow_eq_one hyTp
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · refine IsPGroup.of_card (n := 0) ?_
      rw [Nat.card_zpowers, h1, pow_zero]
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, h1, pow_one]
  have hmod := hpg.card_modEq_card_fixedPoints T
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers yT) T) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, fun g => map_zero (g : T ≃ₗ[ZMod 2] T)⟩⟩⟩
    have hz : ∀ c : MulAction.fixedPoints (Subgroup.zpowers yT) T, (c : T) = 0 := by
      intro c
      have h1 : yT (c : T) = c := c.2 ⟨yT, Subgroup.mem_zpowers yT⟩
      apply Subtype.ext
      exact eq_zero_of_mem_range_sub1 hodd hy (c : T).2 (congrArg Subtype.val h1)
    exact Subtype.ext ((hz a).trans (hz b).symm)
  rw [hfix] at hmod
  have hcard : Nat.card T = 2 ^ finrank (ZMod 2) T := by
    have : Fintype T := Fintype.ofFinite T
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [hcard] at hmod
  have h2 : ((2 ^ finrank (ZMod 2) T : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  exact orderOf_dvd_of_pow_eq_one h2

end Main

end CFSG.Quasithin.B45Exc
