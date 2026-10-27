module

public import CFSG.Quasithin.Vol2.KGNatComm

public section

namespace CFSG.ASVolI

open CFSG.Open

variable {F : Type} [Field F]

theorem burnsideC41b_commutant (T : (Fin 3 → F) →+ (Fin 3 → F))
    (hT : ∀ (γ : ↥(StatedSL 3 F)) (x : Fin 3 → F),
      T (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x) =
        ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (T x)) :
    ∃ c : F, ∀ x, T x = c • x :=
  CFSG.Quasithin.Vol2.KGNat.commutant_statedSL (by norm_num) T fun γ x => by
    rw [CFSG.Quasithin.Vol2.KGNat.linModelNat_lin, CFSG.Quasithin.Vol2.KGNat.linModelNat_lin]
    exact hT γ x

theorem burnsideC41b_exists_transvection (i j : Fin 3) (hij : i ≠ j) (t : F) :
    ∃ γ : ↥(StatedSL 3 F),
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection i j t :=
  ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
    ⟨Matrix.transvection i j t, Matrix.det_transvection_of_ne i j hij t⟩, rfl⟩

theorem burnsideC41b_transvection_mulVec (i j : Fin 3) (t : F) (x : Fin 3 → F) :
    (Matrix.transvection i j t).mulVec x = x + Pi.single i (t * x j) := by
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem burnsideC41b_eq_top_of_invariant (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ (γ : ↥(StatedSL 3 F)) (x : Fin 3 → F), x ∈ S →
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ S)
    {x : Fin 3 → F} (hx : x ∈ S) (hx0 : x ≠ 0) : S = ⊤ := by
  have key : ∀ y ∈ S, ∀ j : Fin 3, y j ≠ 0 → ∀ i : Fin 3, i ≠ j → ∀ s : F,
      Pi.single i s ∈ S := by
    intro y hy j hyj i hij s
    obtain ⟨γ, hγ⟩ := burnsideC41b_exists_transvection i j hij (s / y j)
    have h1 := hS γ y hy
    rw [hγ, burnsideC41b_transvection_mulVec, div_mul_cancel₀ s hyj] at h1
    have h2 := S.sub_mem h1 hy
    rwa [add_sub_cancel_left] at h2
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 3, i₀ ≠ j := by
    by_cases h : j = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, Ne.symm h⟩
  have hall : ∀ i : Fin 3, ∀ s : F, Pi.single i s ∈ S := by
    intro i s
    by_cases hij : i = j
    · have h1 : Pi.single i₀ (1 : F) ∈ S := key x hx j hj i₀ hi₀ 1
      refine key _ h1 i₀ (by simp) i ?_ s
      rw [hij]
      exact Ne.symm hi₀
    · exact key x hx j hj i hij s
  rw [eq_top_iff]
  intro v _
  rw [← Finset.univ_sum_single v]
  exact AddSubgroup.sum_mem S fun i _ => hall i (v i)

theorem burnsideC41b_eq_one_of_mulVec {g : GL (Fin 3) F}
    (h : ∀ x : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F).mulVec x = x) : g = 1 := by
  have hm : (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    exact LinearMap.ext fun x => by rw [Matrix.toLin'_apply, h x, LinearMap.id_apply]
  exact Units.ext hm

theorem burnsideC41b_eq_one_of_pow_two_pow [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {d : F} {m : ℕ} (h : d ^ (2 ^ m) = 1) : d = 1 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero m two_ne_zero)] at h
    exact zero_ne_one h
  have h1 := FiniteField.pow_card_sub_one_eq_one d hd0
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Fintype.one_lt_card (α := F)
      rw [hF, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact hn
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hcop : Nat.Coprime (2 ^ m) (Fintype.card F - 1) := by
    rw [hF]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  have h2 : d ^ (2 ^ m).gcd (Fintype.card F - 1) = 1 := pow_gcd_eq_one.mpr ⟨h, h1⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h2

theorem burnsideC41b_smul_of_normalizes (θ θ' : (Fin 3 → F) →+ (Fin 3 → F))
    (hθθ' : ∀ v, θ (θ' v) = v) (hθ'θ : ∀ v, θ' (θ v) = v)
    (hN : ∀ γ : ↥(StatedSL 3 F), ∃ γ' : ↥(StatedSL 3 F), ∀ v,
      θ (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((γ' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (θ v))
    (hN' : ∀ γ : ↥(StatedSL 3 F), ∃ γ' : ↥(StatedSL 3 F), ∀ v,
      θ' (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((γ' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (θ' v))
    {w : Fin 3 → F} (hw : w ≠ 0) (hfix : ∀ c : F, θ (c • w) = c • w) (c : F)
    (v : Fin 3 → F) : θ (c • v) = c • θ v := by
  let T : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun x => θ (c • θ' x)
      map_zero' := by simp
      map_add' := fun x y => by rw [map_add, smul_add, map_add] }
  have hTapp : ∀ x, T x = θ (c • θ' x) := fun x => rfl
  have hT : ∀ (γ : ↥(StatedSL 3 F)) (x : Fin 3 → F),
      T (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x) =
        ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (T x) := by
    intro γ x
    obtain ⟨γ₁, hγ₁⟩ := hN' γ
    obtain ⟨γ₂, hγ₂⟩ := hN γ₁
    have hγ₂γ : ∀ y, ((γ₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec y =
        ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec y := by
      intro y
      have h := hγ₂ (θ' y)
      rw [← hγ₁, hθθ', hθθ'] at h
      exact h.symm
    rw [hTapp, hTapp, hγ₁, ← Matrix.mulVec_smul, hγ₂, hγ₂γ]
  obtain ⟨d, hd⟩ := burnsideC41b_commutant T hT
  have hθc : ∀ u, θ (c • u) = d • θ u := by
    intro u
    have h := hd (θ u)
    rwa [hTapp, hθ'θ] at h
  have hw1 : θ w = w := by simpa using hfix 1
  have hcd : c = d := by
    have h1 := hθc w
    rw [hfix c, hw1] at h1
    by_contra hne
    apply hw
    have h2 : (c - d) • w = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  rw [hθc v, hcd]

theorem burnsideC41b_exists_decomp (W₀ : Submodule F (Fin 3 → F))
    (hW₀ : Module.finrank F W₀ = 2) {e : Fin 3 → F} (he : e ∉ W₀) (v : Fin 3 → F) :
    ∃ w ∈ W₀, ∃ c : F, v = w + c • e := by
  have he0 : e ≠ 0 := fun h => he (h ▸ W₀.zero_mem)
  have hinf : W₀ ⊓ Submodule.span F {e} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((Submodule.smul_mem_iff W₀ hc).mp hx1) he
  have hsup : W₀ ⊔ Submodule.span F {e} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W₀ (Submodule.span F {e})
    rw [hinf, finrank_bot, add_zero, hW₀, finrank_span_singleton he0] at h1
    rw [h1, Module.finrank_fin_fun]
  have hv : v ∈ W₀ ⊔ Submodule.span F {e} := hsup ▸ Submodule.mem_top
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  exact ⟨w, hw, c, rfl⟩

theorem burnsideC41b_linearMap_eq (W₀ : Submodule F (Fin 3 → F))
    (hW₀ : Module.finrank F W₀ = 2) {e : Fin 3 → F} (he : e ∉ W₀)
    {θ θ' : (Fin 3 → F) →ₗ[F] (Fin 3 → F)} (h₀ : ∀ w ∈ W₀, θ w = θ' w) (h₁ : θ e = θ' e) :
    θ = θ' := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, hw, c, rfl⟩ := burnsideC41b_exists_decomp W₀ hW₀ he v
  rw [map_add, map_add, map_smul, map_smul, h₀ w hw, h₁]

theorem burnsideC41b_sub_mem_of_iterate (W₀ : Submodule F (Fin 3 → F))
    (hW₀ : Module.finrank F W₀ = 2) {e : Fin 3 → F} (he : e ∉ W₀)
    (θ : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) (hfix : ∀ w ∈ W₀, θ w = w) {N : ℕ}
    (hN : θ^[N] e = e) (hd : ∀ d : F, d ^ N = 1 → d = 1) : θ e - e ∈ W₀ := by
  obtain ⟨w, hw, d, hθe⟩ := burnsideC41b_exists_decomp W₀ hW₀ he (θ e)
  have hiter : ∀ j : ℕ, ∃ w' ∈ W₀, θ^[j] e = w' + d ^ j • e := by
    intro j
    induction j with
    | zero => exact ⟨0, W₀.zero_mem, by simp⟩
    | succ j ih =>
      obtain ⟨w', hw', hj⟩ := ih
      refine ⟨w' + d ^ j • w, W₀.add_mem hw' (W₀.smul_mem _ hw), ?_⟩
      rw [Function.iterate_succ_apply', hj, map_add, map_smul, hfix w' hw', hθe, smul_add,
        smul_smul, ← pow_succ, add_assoc]
  obtain ⟨w', hw', hN'⟩ := hiter N
  rw [hN] at hN'
  have hdN : d ^ N = 1 := by
    by_contra hne
    apply he
    have h1 : (1 - d ^ N) • e = w' := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [hN']
      abel
    have h2 : (1 - d ^ N) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [← inv_smul_smul₀ h2 e, h1]
    exact W₀.smul_mem _ hw'
  rw [hθe, hd d hdN, one_smul, add_sub_cancel_right]
  exact hw

end CFSG.ASVolI
