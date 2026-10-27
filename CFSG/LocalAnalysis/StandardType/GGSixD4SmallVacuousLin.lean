module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmMain
public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.StandardType

namespace D4Vac

open Module Multiplicative SevOm

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

section Gen

noncomputable abbrev gen (F : Frame Q p A r) (i : Fin r) : V ≃ₗ[K] V :=
  F.ι (ofAdd (Pi.single i 1))

theorem gen_pow_mem (F : Frame Q p A r) (i : Fin r) (k : ℕ) : gen F i ^ k ∈ A :=
  A.pow_mem (F.mem _) k

theorem gen_pow_mapsTo (F : Frame Q p A r) (i j : Fin r) (k : ℕ) {u : V} (hu : u ∈ F.U j) :
    (gen F i ^ k) u ∈ F.U j := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply]
    exact F.mapsTo _ j _ ih

theorem gen_triv (F : Frame Q p A r) {i j : Fin r} (hji : j ≠ i) {u : V} (hu : u ∈ F.U j) :
    gen F i u = u :=
  F.triv _ j (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hji]) u hu

theorem gen_pow_triv (F : Frame Q p A r) {i j : Fin r} (hji : j ≠ i) (k : ℕ) {u : V}
    (hu : u ∈ F.U j) : (gen F i ^ k) u = u := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, gen_triv F hji hu]

theorem gen_pow_p (F : Frame Q p A r) (i : Fin r) : gen F i ^ p = 1 := F.pow_p _

theorem gen_fpf [Fact p.Prime] (F : Frame Q p A r) (i : Fin r) {u : V} (hu : u ∈ F.U i)
    (h : gen F i u = u) : u = 0 :=
  F.fpf _ i (by rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero) u hu h

end Gen

section Proj

@[expose] noncomputable def nrm (F : Frame Q p A r) (i : Fin r) : V →ₗ[K] V :=
  ∑ k ∈ Finset.range p, ((gen F i ^ k : V ≃ₗ[K] V) : V →ₗ[K] V)

@[expose] noncomputable def pr (F : Frame Q p A r) (i : Fin r) : V →ₗ[K] V :=
  LinearMap.id + nrm F i

theorem nrm_apply (F : Frame Q p A r) (i : Fin r) (v : V) :
    nrm F i v = ∑ k ∈ Finset.range p, (gen F i ^ k) v := by
  rw [nrm, LinearMap.sum_apply]
  rfl

theorem pr_apply (F : Frame Q p A r) (i : Fin r) (v : V) : pr F i v = v + nrm F i v := rfl

theorem nrm_mem (F : Frame Q p A r) (i : Fin r) {W : Submodule K V}
    (hWA : ∀ a ∈ A, ∀ v ∈ W, a v ∈ W) {v : V} (hv : v ∈ W) : nrm F i v ∈ W := by
  rw [nrm_apply]
  exact W.sum_mem fun k _ => hWA _ (gen_pow_mem F i k) v hv

theorem pr_mem_of_mem (F : Frame Q p A r) (i : Fin r) {W : Submodule K V}
    (hWA : ∀ a ∈ A, ∀ v ∈ W, a v ∈ W) {v : V} (hv : v ∈ W) : pr F i v ∈ W :=
  W.add_mem hv (nrm_mem F i hWA hv)

theorem gen_nrm (F : Frame Q p A r) (i : Fin r) (v : V) : gen F i (nrm F i v) = nrm F i v := by
  rw [nrm_apply, map_sum]
  have h1 : ∀ k : ℕ, gen F i ((gen F i ^ k) v) = (gen F i ^ (k + 1)) v := fun k => by
    rw [pow_succ', LinearEquiv.mul_apply]
  simp only [h1]
  have h2 := Finset.sum_range_succ' (fun k => (gen F i ^ k) v) p
  rw [Finset.sum_range_succ, gen_pow_p, pow_zero] at h2
  exact add_right_cancel h2.symm

theorem nrm_eq_zero [Fact p.Prime] (F : Frame Q p A r) (i : Fin r) {u : V} (hu : u ∈ F.U i) :
    nrm F i u = 0 := by
  refine gen_fpf F i ?_ (gen_nrm F i u)
  rw [nrm_apply]
  exact (F.U i).sum_mem fun k _ => gen_pow_mapsTo F i i k hu

theorem pr_apply_of_mem [Fact p.Prime] (F : Frame Q p A r) (i : Fin r) {u : V}
    (hu : u ∈ F.U i) : pr F i u = u := by
  rw [pr_apply, nrm_eq_zero F i hu, add_zero]

theorem add_self_charTwo [CharP K 2] (u : V) : u + u = 0 := by
  rw [← two_smul K u, CharTwo.two_eq_zero, zero_smul]

theorem two_mul_nsmul_charTwo [CharP K 2] (u : V) (n : ℕ) : (2 * n) • u = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, add_nsmul, ih, zero_add, two_nsmul, add_self_charTwo (K := K)]

theorem pr_apply_of_ne [CharP K 2] (hp : Odd p) (F : Frame Q p A r) {i j : Fin r} (hji : j ≠ i)
    {u : V} (hu : u ∈ F.U j) : pr F i u = 0 := by
  rw [pr_apply, nrm_apply]
  simp only [gen_pow_triv F hji _ hu, Finset.sum_const, Finset.card_range]
  obtain ⟨m, rfl⟩ := hp
  rw [add_nsmul, two_mul_nsmul_charTwo (K := K), one_nsmul, zero_add, add_self_charTwo (K := K)]

end Proj

section Dim

variable [CharP K 2] [FiniteDimensional K V]

omit [CharP K 2] [FiniteDimensional K V] in
theorem le_ker_polar {X : Submodule K V} {u : V} (h : ∀ x ∈ X, QuadraticMap.polar Q x u = 0) :
    X ≤ LinearMap.ker ((QuadraticMap.polarBilin Q).flip u) := fun x hx => by
  rw [LinearMap.mem_ker, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
  exact h x hx

omit [CharP K 2] in
theorem finrank_four_le (F : Frame Q p A r) {i j k l : Fin r} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finrank K (F.U i) + finrank K (F.U j) + finrank K (F.U k) + finrank K (F.U l) ≤
      finrank K ↥(F.U i ⊔ F.U j ⊔ F.U k ⊔ F.U l) := by
  have hdisj : (F.U i ⊔ F.U j ⊔ F.U k) ⊓ F.U l = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => F.nondeg l w hw.2 fun v hv => ?_
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hw.1
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      F.orth l i (Ne.symm hil) v hv a ha, F.orth l j (Ne.symm hjl) v hv b hb,
      F.orth l k (Ne.symm hkl) v hv c hc, add_zero, add_zero]
  have h1 := F.finrank_add_add_le hij hik hjk (W := F.U i ⊔ F.U j ⊔ F.U k)
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) le_sup_right
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F.U i ⊔ F.U j ⊔ F.U k) (F.U l)
  rw [hdisj, finrank_bot, add_zero] at h2
  omega

theorem sup_four_eq_top (F : Frame Q p A r) (hV : finrank K V ≤ 8) {i j k l : Fin r}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    F.U i ⊔ F.U j ⊔ F.U k ⊔ F.U l = ⊤ := by
  have h := finrank_four_le F hij hik hil hjk hjl hkl
  have := F.two_le_finrank i
  have := F.two_le_finrank j
  have := F.two_le_finrank k
  have := F.two_le_finrank l
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))

theorem r_le_four (F : Frame Q p A r) (hV : finrank K V ≤ 8) : r ≤ 4 := by
  by_contra h
  push Not at h
  have htop := sup_four_eq_top F hV (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (k := ⟨2, by omega⟩) (l := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff])
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot ⟨4, h⟩)
  refine hu0 (F.nondeg _ u hu fun v _ => ?_)
  have hle : (⊤ : Submodule K V) ≤ LinearMap.ker ((QuadraticMap.polarBilin Q).flip u) := by
    rw [← htop]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;>
      refine le_ker_polar fun x hx => F.orth _ _ ?_ x hx u hu <;> simp [Fin.ext_iff]
  have h1 := hle (Submodule.mem_top (x := v))
  rwa [LinearMap.mem_ker, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply] at h1

theorem iSup_eq_top (F : Frame Q p A r) (hV : finrank K V ≤ 8) (hr : 4 ≤ r) :
    ⨆ i, F.U i = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← sup_four_eq_top F hV (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩)
    (l := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
  exact sup_le (sup_le (sup_le (le_iSup F.U _) (le_iSup F.U _)) (le_iSup F.U _)) (le_iSup F.U _)

theorem finrank_piece_eq_two (F : Frame Q p A r) (hV : finrank K V ≤ 8) (hr : 4 ≤ r) (i : Fin r) :
    finrank K (F.U i) = 2 := by
  obtain ⟨i₁, i₂, i₃, h12, h13, h23, h1, h2, h3⟩ := exists_three_ne hr i
  have h := finrank_four_le F (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) h12 h13 h23
  have h8 := Submodule.finrank_le (F.U i ⊔ F.U i₁ ⊔ F.U i₂ ⊔ F.U i₃)
  have := F.two_le_finrank i
  have := F.two_le_finrank i₁
  have := F.two_le_finrank i₂
  have := F.two_le_finrank i₃
  omega

end Dim

section Irred

theorem exists_eq_smul_add [Finite K] [Fact p.Prime] (hpK : ¬ p ∣ Nat.card K - 1)
    (F : Frame Q p A r) {i : Fin r} (h2 : finrank K (F.U i) = 2) {v w : V} (hv : v ∈ F.U i)
    (hv0 : v ≠ 0) (hw : w ∈ F.U i) : ∃ α β : K, w = α • v + β • gen F i v := by
  have hgv : gen F i v ∈ F.U i := F.mapsTo _ i v hv
  have hli : LinearIndependent K ![v, gen F i v] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero] at hac
      exact ⟨(smul_eq_zero.mp hac).resolve_right hv0, rfl⟩
    · exfalso
      set l : K := -(a / c) with hl
      have hgl : gen F i v = l • v := by
        have e1 : c • gen F i v = -(a • v) :=
          eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hac)
        calc gen F i v = c⁻¹ • (c • gen F i v) := by
              rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = l • v := by rw [e1, smul_neg, smul_smul, hl, neg_smul, div_eq_inv_mul]
      have hpow : ∀ k : ℕ, (gen F i ^ k) v = l ^ k • v := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hgl, smul_smul, pow_succ]
      have hlp : l ^ p = 1 := by
        have h1 := hpow p
        rw [gen_pow_p, LinearEquiv.coe_one, id] at h1
        have h3 : (l ^ p - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)
      have hl1 : l ≠ 1 := by
        intro h
        exact hv0 (gen_fpf F i hv (by rw [hgl, h, one_smul]))
      have hl0 : l ≠ 0 := by
        intro h
        rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hlp
        exact zero_ne_one hlp
      set u : Kˣ := Units.mk0 l hl0 with hu
      have hu3 : u ^ p = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hlp, Units.val_one])
      have hu1 : u ≠ 1 := fun h => hl1 (by
        have := congrArg Units.val h
        rwa [hu, Units.val_mk0, Units.val_one] at this)
      have ho : orderOf u = p := orderOf_eq_prime hu3 hu1
      have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
      rw [Nat.card_units, ho] at hdvd
      exact hpK hdvd
  set f : Fin 2 → ↥(F.U i) := ![⟨v, hv⟩, ⟨gen F i v, hgv⟩] with hf
  have hfli : LinearIndependent K f := by
    apply LinearIndependent.of_comp (F.U i).subtype
    convert hli using 1
    ext j : 1
    fin_cases j <;> rfl
  have htop := hfli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h2])
  have hw' : (⟨w, hw⟩ : ↥(F.U i)) ∈ Submodule.span K (Set.range f) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw'
  refine ⟨c 0, c 1, ?_⟩
  have h4 := congrArg Subtype.val hc
  rw [Fin.sum_univ_two] at h4
  simpa [hf] using h4.symm

end Irred

section Span

variable [CharP K 2] [Fact p.Prime]

theorem pr_mem (hp : Odd p) (F : Frame Q p A r) (hsup : ⨆ j, F.U j = ⊤) (i : Fin r) (v : V) :
    pr F i v ∈ F.U i := by
  have hle : ⨆ j, F.U j ≤ (F.U i).comap (pr F i) := iSup_le fun j u hu => by
    rw [Submodule.mem_comap]
    by_cases hji : j = i
    · subst hji
      rw [pr_apply_of_mem F j hu]
      exact hu
    · rw [pr_apply_of_ne hp F hji hu]
      exact (F.U i).zero_mem
  exact hle (by rw [hsup]; exact Submodule.mem_top)

theorem eq_sum_pr (hp : Odd p) (F : Frame Q p A r) (hsup : ⨆ j, F.U j = ⊤) (v : V) :
    v = ∑ i, pr F i v := by
  have hle : ⨆ j, F.U j ≤ LinearMap.ker (LinearMap.id - ∑ i, pr F i) := iSup_le fun j u hu => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      Finset.sum_eq_single j, pr_apply_of_mem F j hu, sub_self]
    · intro i _ hij
      exact pr_apply_of_ne hp F (Ne.symm hij) hu
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h := hle (show v ∈ ⨆ j, F.U j by rw [hsup]; exact Submodule.mem_top)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    sub_eq_zero] at h
  exact h

theorem polar_pr (hp : Odd p) (F : Frame Q p A r) (hsup : ⨆ j, F.U j = ⊤) {i : Fin r} {z : V}
    (hz : z ∈ F.U i) (x : V) :
    QuadraticMap.polar Q x z = QuadraticMap.polar Q (pr F i x) z := by
  conv_lhs => rw [eq_sum_pr hp F hsup x]
  have hsum : QuadraticMap.polar Q (∑ j, pr F j x) z =
      ∑ j, QuadraticMap.polar Q (pr F j x) z := by
    have e : QuadraticMap.polarBilin Q (∑ j, pr F j x) z =
        ∑ j, QuadraticMap.polarBilin Q (pr F j x) z := by
      rw [map_sum, LinearMap.sum_apply]
    exact e
  rw [hsum, Finset.sum_eq_single i]
  · intro j _ hji
    exact F.orth j i hji _ (pr_mem hp F hsup j x) z hz
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem le_or_pr_eq_zero [Finite K] (hpK : ¬ p ∣ Nat.card K - 1) (hp : Odd p)
    (F : Frame Q p A r) (hsup : ⨆ j, F.U j = ⊤) {i : Fin r} (h2 : finrank K (F.U i) = 2)
    {W : Submodule K V} (hWA : ∀ a ∈ A, ∀ v ∈ W, a v ∈ W) :
    F.U i ≤ W ∨ ∀ v ∈ W, pr F i v = 0 := by
  by_cases hall : ∀ v ∈ W, pr F i v = 0
  · exact Or.inr hall
  · left
    push Not at hall
    obtain ⟨w, hw, hw0⟩ := hall
    have hpw : pr F i w ∈ W := pr_mem_of_mem F i hWA hw
    intro z hz
    obtain ⟨α, β, rfl⟩ := exists_eq_smul_add hpK F h2 (pr_mem hp F hsup i w) hw0 hz
    exact W.add_mem (W.smul_mem _ hpw) (W.smul_mem _ (hWA _ (F.mem _) _ hpw))

end Span

theorem eq_bot_of_frame [Finite K] [CharP K 2] [FiniteDimensional K V] (hV : finrank K V ≤ 8)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) (F : Frame Q p A r) (hr : 4 ≤ r)
    {T : Subgroup (V ≃ₗ[K] V)} (hT : IsPGroup 2 T)
    (hTQ : ∀ t ∈ T, ∀ u w : V, QuadraticMap.polar Q (t u) (t w) = QuadraticMap.polar Q u w)
    (hAT : ∀ a ∈ A, ∀ t ∈ T, a⁻¹ * t * a ∈ T) : T = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hsup := iSup_eq_top F hV hr
  have h2 := finrank_piece_eq_two F hV hr
  set W : Submodule K V :=
    ⨅ t : T, LinearMap.ker (((t : V ≃ₗ[K] V) : V →ₗ[K] V) - LinearMap.id) with hWdef
  have hmemW : ∀ v, v ∈ W ↔ ∀ t ∈ T, t v = v := by
    intro v
    rw [hWdef, Submodule.mem_iInf]
    constructor
    · intro hv t ht
      have h1 := hv ⟨t, ht⟩
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
    · intro hv t
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hv t t.2
  have hWA : ∀ a ∈ A, ∀ v ∈ W, a v ∈ W := by
    intro a ha v hv
    rw [hmemW] at hv ⊢
    intro t ht
    have e : a * (a⁻¹ * t * a) = t * a := by group
    rw [show t (a v) = (a * (a⁻¹ * t * a)) v by rw [e, LinearEquiv.mul_apply],
      LinearEquiv.mul_apply, hv _ (hAT a ha t ht)]
  have hdich : ∀ i, F.U i ≤ W ∨ ∀ v ∈ W, pr F i v = 0 := fun i =>
    le_or_pr_eq_zero hpK hpo F hsup (h2 i) hWA
  set X : Submodule K V := ⨅ (i : Fin r) (_ : F.U i ≤ W), LinearMap.ker (pr F i) with hXdef
  have hmemX : ∀ v, v ∈ X ↔ ∀ i, F.U i ≤ W → pr F i v = 0 := by
    intro v
    simp only [hXdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hXW : ∀ v ∈ X, v ∈ W → v = 0 := by
    intro v hvX hvW
    rw [eq_sum_pr hpo F hsup v]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hdich i with h | h
    · exact (hmemX v).mp hvX i h
    · exact h v hvW
  have hTX : ∀ t ∈ T, ∀ u ∈ X, t u ∈ X := by
    intro t ht u hu
    rw [hmemX] at hu ⊢
    intro i hi
    refine F.nondeg i _ (pr_mem hpo F hsup i _) fun z hz => ?_
    have hzW : t z = z := (hmemW z).mp (hi hz) t ht
    rw [QuadraticMap.polar_comm, ← polar_pr hpo F hsup hz, ← hzW, hTQ t ht,
      polar_pr hpo F hsup hz, hu i hi, QuadraticMap.polar_zero_left]
  have hXbot : X = ⊥ := by
    by_contra hne
    have : Nontrivial X := Submodule.nontrivial_iff_ne_bot.mpr hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite X := Module.finite_of_finite K
    let ρX : T →* Module.End K X :=
      { toFun := fun t => ((t : V ≃ₗ[K] V) : V →ₗ[K] V).restrict (fun u hu => hTX t t.2 u hu)
        map_one' := by
          refine LinearMap.ext fun u => Subtype.ext ?_
          simp
        map_mul' := by
          intro a b
          refine LinearMap.ext fun u => Subtype.ext ?_
          simp [Module.End.mul_apply] }
    obtain ⟨v, hv0, hvfix⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero ρX 2 ⊤
      (hT.to_subgroup ⊤)
    apply hv0
    refine Subtype.ext (hXW _ v.2 ((hmemW _).mpr fun t ht => ?_))
    have h1 := hvfix ⟨t, ht⟩ (Subgroup.mem_top _)
    exact congrArg Subtype.val h1
  have hS : ∀ i, F.U i ≤ W := by
    intro i
    by_contra hi
    have hle : F.U i ≤ X := by
      intro v hv
      rw [hmemX]
      intro j hj
      have hij : i ≠ j := fun e => hi (by rw [e]; exact hj)
      exact pr_apply_of_ne hpo F hij hv
    rw [hXbot] at hle
    exact F.ne_bot i (le_bot_iff.mp hle)
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ W := by
    rw [eq_sum_pr hpo F hsup v]
    exact Submodule.sum_mem _ fun i _ => hS i (pr_mem hpo F hsup i v)
  rw [(hmemW v).mp hv t ht, LinearEquiv.coe_one, id]

end D4Vac

end CFSG.StandardType
