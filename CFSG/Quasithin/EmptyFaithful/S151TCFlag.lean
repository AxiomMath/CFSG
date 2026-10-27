module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.Quasithin.S151TC

lemma flag_diag_mul {F : Type} [Field F] (A B : Matrix (Fin 3) (Fin 3) F)
    (hA : ∀ i j : Fin 3, j < i → A i j = 0) (hB : ∀ i j : Fin 3, j < i → B i j = 0)
    (i : Fin 3) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma flag_pow_four_eq_one {F : Type} [Field F] [CharP F 2] (A : Matrix (Fin 3) (Fin 3) F)
    (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) (h21 : A 2 1 = 0)
    (h00 : A 0 0 = 1) (h11 : A 1 1 = 1) (h22 : A 2 2 = 1) : A ^ 4 = 1 := by
  have hA : A = !![1, A 0 1, A 0 2; 0, 1, A 1 2; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [*]
  rw [hA]
  generalize A 0 1 = a
  generalize A 0 2 = b
  generalize A 1 2 = c
  have e2 : !![1, a, b; 0, 1, c; 0, 0, 1] ^ 2 = !![1, 0, a * c; 0, 1, 0; 0, 0, 1] := by
    rw [pow_two, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact CharTwo.add_self_eq_zero a
    · rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    · exact CharTwo.add_self_eq_zero c
  have e4 : (!![1, 0, a * c; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 2 = 1 := by
    rw [pow_two, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    exact CharTwo.add_self_eq_zero _
  rw [show 4 = 2 * 2 from rfl, pow_mul, e2, e4]

theorem flag_normal_of_triangular {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {T : Type} [Group T] (hT : Nat.card T = 24)
    (M : T →* Matrix (Fin 3) (Fin 3) F) (hM : Function.Injective M)
    (hlow : ∀ t i j, j < i → M t i j = 0) (h00 : ∀ t, M t 0 0 = 1) :
    ∃ N : Subgroup T, Nat.card N = 8 ∧ N.Normal := by
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by simpa using hF)
  let d : Fin 3 → T →* Fˣ := fun i =>
    MonoidHom.toHomUnits
      { toFun := fun t => M t i i
        map_one' := by simp
        map_mul' := fun s t => by
          rw [map_mul]
          exact flag_diag_mul _ _ (hlow s) (hlow t) i }
  let χ : T →* Fˣ × Fˣ := (d 1).prod (d 2)
  have hdval : ∀ i t, ((d i t : Fˣ) : F) = M t i i := fun i t => rfl
  have hK : IsPGroup 2 χ.ker := by
    intro x
    refine ⟨2, ?_⟩
    have hx : χ x = 1 := x.2
    have h1 : d 1 x = 1 := congrArg Prod.fst hx
    have h2 : d 2 x = 1 := congrArg Prod.snd hx
    have e1 : M x 1 1 = 1 := by rw [← hdval, h1]; rfl
    have e2 : M x 2 2 = 1 := by rw [← hdval, h2]; rfl
    apply Subtype.ext
    apply hM
    have := flag_pow_four_eq_one (M x) (hlow x 1 0 (by decide)) (hlow x 2 0 (by decide))
      (hlow x 2 1 (by decide)) (h00 x) e1 e2
    simpa [map_pow] using this
  have hcard : Nat.card χ.ker * Nat.card χ.range = 24 := by
    have := Subgroup.card_mul_index χ.ker
    rw [Subgroup.index_ker] at this
    rw [this, hT]
  have hr : Nat.card χ.range ∣ 9 := by
    have h1 := Subgroup.card_subgroup_dvd_card χ.range
    have h2 : Nat.card (Fˣ × Fˣ) = 9 := by
      rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card, hF]
    rwa [h2] at h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hK
  refine ⟨χ.ker, ?_, χ.normal_ker⟩
  have hle : Nat.card χ.range ≤ 9 := Nat.le_of_dvd (by norm_num) hr
  have h3 : Nat.card χ.range ≠ 1 := by
    intro h1
    have hk : Nat.card χ.ker = 24 := by rw [h1] at hcard; omega
    rw [hk] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  generalize Nat.card χ.range = r at *
  interval_cases r <;> omega

theorem flag_false_of_not_mem {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {Γ : Type} [Group Γ] (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hρ : Function.Injective ρ) (T : Subgroup Γ) (hT : Nat.card T = 24)
    (w₀ : Fin 3 → F) (hw₀ : w₀ ≠ 0)
    (hTw : ∀ t ∈ T, (ρ t : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀)
    (W : Submodule F (Fin 3 → F)) (hW : Module.finrank F W = 2)
    (hTW : ∀ t ∈ T, ∀ w ∈ W, (ρ t : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    (hw : w₀ ∉ W) : False := by
  have hsup : ∀ v : Fin 3 → F, ∃ c : F, ∃ w ∈ W, v = c • w₀ + w := by
    intro v
    have hsupTop : W ⊔ Submodule.span F {w₀} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F {w₀})
      have h2 : W ⊓ Submodule.span F {w₀} = ⊥ := by
        rw [← disjoint_iff]
        exact (Submodule.disjoint_span_singleton' hw₀).2 hw
      rw [h2, finrank_bot, finrank_span_singleton hw₀, hW] at h1
      rw [Module.finrank_fin_fun]
      omega
    have hv : v ∈ W ⊔ Submodule.span F {w₀} := by rw [hsupTop]; trivial
    obtain ⟨w, hwW, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨c, w, hwW, add_comm _ _⟩
  let φ : T →* Module.End F W :=
    { toFun := fun t => (Matrix.mulVecLin (ρ t.1 : Matrix (Fin 3) (Fin 3) F)).restrict
        (hTW t.1 t.2)
      map_one' := by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        show (ρ (s * t).1 : Matrix (Fin 3) (Fin 3) F).mulVec w =
          (ρ s.1 : Matrix (Fin 3) (Fin 3) F).mulVec ((ρ t.1 : Matrix (Fin 3) (Fin 3) F).mulVec w)
        rw [Matrix.mulVec_mulVec]
        simp }
  have hinj : Function.Injective φ.toHomUnits := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have ht' : φ t = 1 := by
      have := congrArg Units.val ht
      simpa using this
    have hW1 : ∀ w ∈ W, (ρ t.1 : Matrix (Fin 3) (Fin 3) F).mulVec w = w := by
      intro w hwW
      have := congrArg (fun f : Module.End F W => (f ⟨w, hwW⟩ : Fin 3 → F)) ht'
      exact this
    have hall : ∀ v, (ρ t.1 : Matrix (Fin 3) (Fin 3) F).mulVec v = v := by
      intro v
      obtain ⟨c, w, hwW, rfl⟩ := hsup v
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hTw t.1 t.2, hW1 w hwW]
    have hmat : (ρ t.1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
      exact hall v
    have : ρ t.1 = 1 := Units.ext hmat
    exact Subtype.ext (hρ (by simp [this]))
  have hdvd := Subgroup.card_dvd_of_injective φ.toHomUnits hinj
  have hcard180 : Nat.card (Module.End F W)ˣ = 180 := by
    let bW : Module.Basis (Fin 2) F W := Module.finBasisOfFinrankEq F W hW
    have e : (Module.End F W)ˣ ≃* Matrix.GeneralLinearGroup (Fin 2) F :=
      Units.mapEquiv (LinearMap.toMatrixAlgEquiv bW).toMulEquiv
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, hF]
    simp [Fin.prod_univ_two]
  rw [hcard180, hT] at hdvd
  omega

theorem flag_normal_of_mem {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {Γ : Type} [Group Γ] (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hρ : Function.Injective ρ) (T : Subgroup Γ) (hT : Nat.card T = 24)
    (w₀ : Fin 3 → F) (hw₀ : w₀ ≠ 0)
    (hTw : ∀ t ∈ T, (ρ t : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀)
    (W : Submodule F (Fin 3 → F)) (hW : Module.finrank F W = 2)
    (hTW : ∀ t ∈ T, ∀ w ∈ W, (ρ t : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    (hw : w₀ ∈ W) : ∃ N : Subgroup T, Nat.card N = 8 ∧ N.Normal := by
  obtain ⟨w₁, hw₁W, hw₁⟩ : ∃ w₁ ∈ W, w₁ ∉ Submodule.span F {w₀} := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ Submodule.span F {w₀} := fun w hw' => hcon w hw'
    have h1 := Submodule.finrank_mono hle
    rw [hW, finrank_span_singleton hw₀] at h1
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : Fin 3 → F, w₂ ∉ W := by
    by_contra hcon
    push Not at hcon
    have htop : W = ⊤ := Submodule.eq_top_iff'.2 hcon
    rw [htop, finrank_top, Module.finrank_fin_fun] at hW
    omega
  have hli : LinearIndependent F ![w₀, w₁, w₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
    have hg2 : g 2 = 0 := by
      by_contra h2
      apply hw₂
      have h3 : g 2 • w₂ = -(g 0 • w₀ + g 1 • w₁) := eq_neg_of_add_eq_zero_right hg
      have h4 : g 2 • w₂ ∈ W := by
        rw [h3]
        exact W.neg_mem (W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hw₁W))
      have := W.smul_mem (g 2)⁻¹ h4
      rwa [inv_smul_smul₀ h2] at this
    rw [hg2, zero_smul, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra h1
      apply hw₁
      have h3 : g 1 • w₁ = -(g 0 • w₀) := eq_neg_of_add_eq_zero_right hg
      have h4 : g 1 • w₁ ∈ Submodule.span F {w₀} := by
        rw [h3]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₀))
      have := Submodule.smul_mem _ (g 1)⁻¹ h4
      rwa [inv_smul_smul₀ h1] at this
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := by
      rcases smul_eq_zero.1 hg with h | h
      · exact h
      · exact absurd h hw₀
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  let b : Module.Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ∀ i, b i = ![w₀, w₁, w₂] i := fun i => by simp [b]
  have hb0 : b 0 = w₀ := hb 0
  have hb1 : b 1 = w₁ := hb 1
  have hb2 : b 2 = w₂ := hb 2
  have hrepr2 : ∀ v ∈ W, b.repr v 2 = 0 := by
    intro v hv
    by_contra hc
    apply hw₂
    have hsum := b.sum_repr v
    rw [Fin.sum_univ_three, hb0, hb1, hb2] at hsum
    have h2 : b.repr v 2 • w₂ ∈ W := by
      rw [eq_sub_of_add_eq' hsum]
      exact W.sub_mem hv (W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hw₁W))
    have := W.smul_mem (b.repr v 2)⁻¹ h2
    rwa [inv_smul_smul₀ hc] at this
  let e : Matrix (Fin 3) (Fin 3) F ≃ₐ[F] Matrix (Fin 3) (Fin 3) F :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
  have he : ∀ g i j, e g i j = b.repr (g.mulVec (b j)) i := by
    intro g i j
    simp [e, LinearMap.toMatrixAlgEquiv_apply]
  let M : T →* Matrix (Fin 3) (Fin 3) F :=
    (MonoidHom.ofClass e).comp ((Units.coeHom _).comp (ρ.comp T.subtype))
  have hMe : ∀ t : T, M t = e (ρ t.1 : Matrix (Fin 3) (Fin 3) F) := fun t => rfl
  have hM : Function.Injective M := by
    intro s t hst
    rw [hMe, hMe] at hst
    have := e.injective hst
    exact Subtype.ext (hρ (Units.ext this))
  have hcol0 : ∀ t : T, (ρ t.1 : Matrix (Fin 3) (Fin 3) F).mulVec (b 0) = b 0 := by
    intro t
    rw [hb0]
    exact hTw t.1 t.2
  have hlow : ∀ t i j, j < i → M t i j = 0 := by
    intro t i j hij
    rw [hMe, he]
    have hi : i = 1 ∨ i = 2 := by
      fin_cases i <;> simp_all
    have hj : j = 0 ∨ j = 1 := by
      fin_cases j <;> fin_cases i <;> simp_all
    rcases hj with rfl | rfl
    · rw [hcol0]
      have : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
      rw [Module.Basis.repr_self_apply]
      simp [this.symm]
    · have : i = 2 := by
        rcases hi with rfl | rfl
        · exact absurd hij (by decide)
        · rfl
      subst this
      apply hrepr2
      rw [hb1]
      exact hTW t.1 t.2 w₁ hw₁W
  have h00 : ∀ t, M t 0 0 = 1 := by
    intro t
    rw [hMe, he, hcol0]
    simp
  exact flag_normal_of_triangular hF hT M hM hlow h00

theorem flag_normal_subgroup {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {Γ : Type} [Group Γ] (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hρ : Function.Injective ρ) (T : Subgroup Γ) (hT : Nat.card T = 24)
    (w₀ : Fin 3 → F) (hw₀ : w₀ ≠ 0)
    (hTw : ∀ t ∈ T, (ρ t : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀)
    (W : Submodule F (Fin 3 → F)) (hW : Module.finrank F W = 2)
    (hTW : ∀ t ∈ T, ∀ w ∈ W, (ρ t : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) :
    ∃ N : Subgroup Γ, N ≤ T ∧ Nat.card N = 8 ∧ (N.subgroupOf T).Normal := by
  by_cases hw : w₀ ∈ W
  · obtain ⟨N₀, h8, hn⟩ := flag_normal_of_mem hF ρ hρ T hT w₀ hw₀ hTw W hW hTW hw
    refine ⟨N₀.map T.subtype, Subgroup.map_subtype_le N₀, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective T.subtype_injective, h8]
    · have : (N₀.map T.subtype).subgroupOf T = N₀ :=
        Subgroup.comap_map_eq_self_of_injective T.subtype_injective N₀
      rw [this]
      exact hn
  · exact (flag_false_of_not_mem hF ρ hρ T hT w₀ hw₀ hTw W hW hTW hw).elim

end CFSG.Quasithin.S151TC
