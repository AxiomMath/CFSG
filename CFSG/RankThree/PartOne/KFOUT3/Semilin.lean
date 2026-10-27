module

public import CFSG.RankThree.PartOne.KFOUT3.Normalize

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K]

@[expose] def HasForm (Ψ : MulAut (PSL3 K)) (ρ : Blk → Blk) (σ : K ≃+* K) (c : Blk → K) : Prop :=
  ∀ (b : Blk) (s : K), Ψ (RB b s) = RB (ρ b) (c b * σ s)

theorem HasForm.one : HasForm (1 : MulAut (PSL3 K)) id (1 : K ≃+* K) (fun _ => 1) := by
  intro b s
  simp

theorem HasForm.comp {Ψ₁ Ψ₂ : MulAut (PSL3 K)} {ρ₁ ρ₂ : Blk → Blk} {σ₁ σ₂ : K ≃+* K}
    {c₁ c₂ : Blk → K} (h₁ : HasForm Ψ₁ ρ₁ σ₁ c₁) (h₂ : HasForm Ψ₂ ρ₂ σ₂ c₂) :
    HasForm (Ψ₁ * Ψ₂) (ρ₁ ∘ ρ₂) (σ₁ * σ₂) (fun b => c₁ (ρ₂ b) * σ₁ (c₂ b)) := by
  intro b s
  rw [MulAut.mul_apply, h₂, h₁]
  simp only [Function.comp_apply, map_mul, RingAut.mul_apply]
  rw [mul_assoc]

theorem HasForm.pow {Ψ : MulAut (PSL3 K)} {ρ : Blk → Blk} {σ : K ≃+* K} {c : Blk → K}
    (h : HasForm Ψ ρ σ c) (n : ℕ) : ∃ c' : Blk → K, HasForm (Ψ ^ n) (ρ^[n]) (σ ^ n) c' := by
  induction n with
  | zero => exact ⟨_, by simpa using (HasForm.one : HasForm (1 : MulAut (PSL3 K)) id 1 _)⟩
  | succ n ih =>
    obtain ⟨c', hc'⟩ := ih
    rw [pow_succ', Function.iterate_succ', pow_succ']
    exact ⟨_, h.comp hc'⟩

theorem RB_one_ne_one (b : Blk) : (RB b (1 : K) : PSL3 K) ≠ 1 := by
  intro h
  have := (Matrix.SpecialLinearGroup.transvection_mem_center_iff b.2 (1 : K)).1
    ((QuotientGroup.eq_one_iff _).1 h)
  exact one_ne_zero this

theorem RB_zero (b : Blk) : (RB b (0 : K) : PSL3 K) = 1 := by
  show (QuotientGroup.mk (rt b.2 (0 : K)) : PSL3 K) = 1
  rw [rt_zero, QuotientGroup.mk_one]

theorem HasForm.unique {Ψ : MulAut (PSL3 K)} {ρ ρ' : Blk → Blk} {σ σ' : K ≃+* K} {c c' : Blk → K}
    (h : HasForm Ψ ρ σ c) (h' : HasForm Ψ ρ' σ' c') : ρ = ρ' ∧ σ = σ' ∧ c = c' := by
  have hc : ∀ b, c b ≠ 0 := by
    intro b hb
    have h1 := h b 1
    rw [map_one, mul_one, hb, RB_zero] at h1
    exact RB_one_ne_one b (Ψ.injective (h1.trans (map_one Ψ).symm))
  have hρ : ∀ b, ρ b = ρ' b := by
    intro b
    have h1 := h b 1
    have h2 := h' b 1
    rw [map_one, mul_one] at h1 h2
    have h3 : RB (ρ b) (c b) = RB (ρ' b) (c' b) := h1.symm.trans h2
    obtain ⟨e1, e2, -⟩ := rt_eq_of_mk_eq (ρ b).2 (ρ' b).2 (hc b) h3
    exact Subtype.ext (Prod.ext e1 e2)
  have hcc : ∀ b, c b = c' b := by
    intro b
    have h6 := h b 1
    have h7 := h' b 1
    rw [← hρ b, map_one, mul_one] at h7
    rw [map_one, mul_one] at h6
    exact mk_rt_injective (ρ b).2 (h6.symm.trans h7)
  refine ⟨funext hρ, ?_, funext hcc⟩
  ext s
  let b₀ : Blk := ⟨(0, 1), by decide⟩
  have h1 := h b₀ s
  have h2 := h' b₀ s
  rw [← hρ b₀] at h2
  have h3 : RB (ρ b₀) (c b₀ * σ s) = RB (ρ b₀) (c' b₀ * σ' s) := h1.symm.trans h2
  have h4 := mk_rt_injective (ρ b₀).2 h3
  rw [← hcc b₀] at h4
  exact mul_left_cancel₀ (hc b₀) h4

theorem HasForm.pow_eq_one {Ψ : MulAut (PSL3 K)} {ρ : Blk → Blk} {σ : K ≃+* K} {c : Blk → K}
    (h : HasForm Ψ ρ σ c) {n : ℕ} (hn : Ψ ^ n = 1) : ρ^[n] = id ∧ σ ^ n = 1 := by
  obtain ⟨c', hc'⟩ := h.pow n
  rw [hn] at hc'
  obtain ⟨h1, h2, -⟩ := hc'.unique HasForm.one
  exact ⟨h1, h2⟩

theorem HasForm.pow_scalar_eq_one {Ψ : MulAut (PSL3 K)} {c : Blk → K}
    (h : HasForm Ψ id (1 : K ≃+* K) c) {n : ℕ} (hn : Ψ ^ n = 1) : ∀ b, c b ^ n = 1 := by
  have key : ∀ m : ℕ, HasForm (Ψ ^ m) id (1 : K ≃+* K) (fun b => c b ^ m) := by
    intro m
    induction m with
    | zero => simpa using (HasForm.one : HasForm (1 : MulAut (PSL3 K)) id 1 _)
    | succ m ih =>
      have := h.comp ih
      rw [pow_succ']
      intro b s
      have h1 := this b s
      simp only [Function.comp_apply, id_eq, mul_one, RingAut.one_apply] at h1 ⊢
      rw [h1, pow_succ']
  have h1 := key n
  rw [hn] at h1
  intro b
  have := (h1.unique HasForm.one).2.2
  exact congrFun this b

section Exists

variable [CharP K 2] [Finite K]

theorem rho_eq_permB (π : Equiv.Perm (Fin 3)) (ε : Bool) (b : Blk) :
    rho π ε b = permB π (cond ε (swapB b) b) := by
  cases ε <;> rfl

omit [Finite K] in
theorem hasForm_of_std {Ψ : MulAut (PSL3 K)} {π : Equiv.Perm (Fin 3)} {ε : Bool}
    {d : Fin 3 → Kˣ} {σ : K ≃+* K}
    (h : ∀ x : SL3 K, Ψ (QuotientGroup.mk x) =
      cPerm π (gammaPow ε (QuotientGroup.mk (stdHom (KFU.diagU d) σ x)))) :
    HasForm Ψ (rho π ε) σ (fun b => (d b.1.1 : K) * (((d b.1.2)⁻¹ : Kˣ) : K)) := by
  intro b s
  have h1 := h (rt b.2 s)
  rw [stdHom_diagU_rt] at h1
  show Ψ (QuotientGroup.mk (rt b.2 s)) = _
  rw [h1]
  have e : (d b.1.1 : K) * σ s * (((d b.1.2)⁻¹ : Kˣ) : K) =
      ((d b.1.1 : K) * (((d b.1.2)⁻¹ : Kˣ) : K)) * σ s := by ring
  rw [e]
  show cPerm π (gammaPow ε (RB b _)) = _
  rw [gammaPow_RB, cPerm_RB, rho_eq_permB]

omit [CharP K 2] [Finite K] in
theorem coeff_ne_zero (d : Fin 3 → Kˣ) (b : Blk) :
    (d b.1.1 : K) * (((d b.1.2)⁻¹ : Kˣ) : K) ≠ 0 :=
  mul_ne_zero (d _).ne_zero (Units.ne_zero _)

theorem exists_hasForm {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) (Ψ : MulAut (PSL3 K))
    (hT : ∀ t, t ∈ Tbar p K ↔ Ψ t ∈ Tbar p K) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Bool) (σ : K ≃+* K) (c : Blk → K),
      (∀ b, c b ≠ 0) ∧ HasForm Ψ (rho π ε) σ c := by
  obtain ⟨π, ε, d, σ, h⟩ := exists_std_normalization hζ Ψ hT
  exact ⟨π, ε, σ, _, coeff_ne_zero d, hasForm_of_std h⟩

end Exists

section Torus

theorem conj_RB (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (b : Blk) (s : K) :
    (QuotientGroup.mk (diagSL v hv) : PSL3 K) * RB b s * (QuotientGroup.mk (diagSL v hv))⁻¹ =
      RB b (((v b.1.1 * (v b.1.2)⁻¹ : Kˣ) : K) * s) := by
  have h := diagSL_conj_rt v hv b.2 s
  have h2 := congrArg (QuotientGroup.mk (s := Subgroup.center (SL3 K))) h
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
  rw [Units.val_mul]
  exact h2

theorem conj_pow_RB (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (b : Blk) (s : K) (n : ℕ) :
    (QuotientGroup.mk (diagSL v hv) : PSL3 K) ^ n * RB b s *
        ((QuotientGroup.mk (diagSL v hv) : PSL3 K) ^ n)⁻¹ =
      RB b ((((v b.1.1 * (v b.1.2)⁻¹ : Kˣ) : K)) ^ n * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_inv_rev]
    calc (QuotientGroup.mk (diagSL v hv) : PSL3 K) * (QuotientGroup.mk (diagSL v hv)) ^ n *
          RB b s * (((QuotientGroup.mk (diagSL v hv) : PSL3 K) ^ n)⁻¹ *
            (QuotientGroup.mk (diagSL v hv))⁻¹)
        = (QuotientGroup.mk (diagSL v hv) : PSL3 K) * ((QuotientGroup.mk (diagSL v hv)) ^ n *
          RB b s * ((QuotientGroup.mk (diagSL v hv) : PSL3 K) ^ n)⁻¹) *
            (QuotientGroup.mk (diagSL v hv))⁻¹ := by group
      _ = _ := by rw [ih, conj_RB, pow_succ']; congr 1; ring

theorem rel_of_action {p : ℕ} {Ψ : MulAut (PSL3 K)} {ρ : Blk → Blk} {σ : K ≃+* K} {c : Blk → K}
    (hc : ∀ b, c b ≠ 0) (h : HasForm Ψ ρ σ c) {k : ℕ}
    (hact : ∀ t ∈ Tor p K, Ψ (QuotientGroup.mk t) = (QuotientGroup.mk t) ^ k)
    (v : Fin 3 → Kˣ) (hvp : ∀ i, v i ^ p = 1) (hv : ∏ i, v i = 1) (b : Blk) :
    σ ((v b.1.1 * (v b.1.2)⁻¹ : Kˣ) : K) =
      (((v (ρ b).1.1 * (v (ρ b).1.2)⁻¹ : Kˣ) : K)) ^ k := by
  have ht : diagSL v hv ∈ Tor p K := diagSL_mem_Tor v hvp hv
  have h1 := hact _ ht
  have e1 := congrArg Ψ (conj_RB v hv b 1)
  simp only [map_mul, map_inv, h1, h b] at e1
  rw [conj_pow_RB] at e1
  have e2 := mk_rt_injective (ρ b).2 e1
  simp only [map_one, mul_one] at e2
  have e3 : c b * ((((v (ρ b).1.1 * (v (ρ b).1.2)⁻¹ : Kˣ) : K)) ^ k) =
      c b * σ ((v b.1.1 * (v b.1.2)⁻¹ : Kˣ) : K) := by
    rw [mul_comm (c b), ← e2]
  exact (mul_left_cancel₀ (hc b) e3).symm

theorem IsZeta.pow_eq_one_iff {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hζ : IsZeta p ζ) {n : ℕ} :
    ζ ^ n = 1 ↔ p ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ζ ≠ 1 := fun h => hζ.sq (by rw [h, one_pow])
  rw [← orderOf_dvd_iff_pow_eq_one, orderOf_eq_prime hζ.pow h1]

theorem nonreg_chi_ne {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hζ : IsZeta p ζ) {k : ℕ} (hk : ¬ p ∣ k)
    {c i j : Fin 3} (hij : i ≠ j) (hc : c = i ∨ c = j) :
    (((nonreg ζ c i * (nonreg ζ c j)⁻¹ : Kˣ) : K)) ^ k ≠ 1 := by
  intro h
  have h1 : (nonreg ζ c i * (nonreg ζ c j)⁻¹) ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact h
  have h2 : ζ ^ (3 * k) = 1 := by
    rcases hc with rfl | rfl
    · have hj : j ≠ c := fun e => hij e.symm
      rw [nonreg_self, nonreg_of_ne ζ hj] at h1
      have : (ζ ^ (3 * k))⁻¹ = 1 := by
        rw [← h1]
        group
      simpa using this
    · have hi : i ≠ c := hij
      rw [nonreg_self, nonreg_of_ne ζ hi] at h1
      have : ζ ^ (3 * k) = 1 := by
        rw [← h1]
        group
      exact this
  rw [hζ.pow_eq_one_iff hp] at h2
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact hζ.cube ((hζ.pow_eq_one_iff hp).2 h3)
  · exact hk h3

theorem perm_eq_one_of_forall : ∀ π : Equiv.Perm (Fin 3),
    (∀ i j c : Fin 3, i ≠ j → c ≠ i → c ≠ j → π i ≠ c ∧ π j ≠ c) → π = 1 := by
  decide

theorem scalar_action {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hζ : IsZeta p ζ) {Ψ : MulAut (PSL3 K)}
    {π : Equiv.Perm (Fin 3)} {ε : Bool} {σ : K ≃+* K} {c : Blk → K} (hc : ∀ b, c b ≠ 0)
    (h : HasForm Ψ (rho π ε) σ c) {k : ℕ} (hk : ¬ p ∣ k)
    (hact : ∀ t ∈ Tor p K, Ψ (QuotientGroup.mk t) = (QuotientGroup.mk t) ^ k) :
    π = 1 ∧ ((ε = false ∧ σ (ζ : K) = (ζ : K) ^ k) ∨
      (ε = true ∧ σ (ζ : K) = ((ζ : K) ^ k)⁻¹)) := by
  have hπ : π = 1 := by
    apply perm_eq_one_of_forall
    intro i j c' hij hci hcj
    have hrel := rel_of_action hc h hact (nonreg ζ c') (nonreg_pow hζ.pow c') (prod_nonreg ζ c')
      ⟨(i, j), hij⟩
    simp only [nonreg_of_ne ζ hci.symm, nonreg_of_ne ζ hcj.symm, mul_inv_cancel, Units.val_one,
      map_one] at hrel
    have hno : ¬ (c' = (rho π ε ⟨(i, j), hij⟩).1.1 ∨ c' = (rho π ε ⟨(i, j), hij⟩).1.2) := by
      intro hor
      exact nonreg_chi_ne hp hζ hk (rho π ε ⟨(i, j), hij⟩).2 hor hrel.symm
    push Not at hno
    cases ε
    · simp only [rho, Bool.false_eq_true, ite_false] at hno
      exact ⟨fun e => hno.1 e.symm, fun e => hno.2 e.symm⟩
    · simp only [rho, ite_true] at hno
      exact ⟨fun e => hno.2 e.symm, fun e => hno.1 e.symm⟩
  subst hπ
  refine ⟨rfl, ?_⟩
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → Kˣ, v = KFU.torusElt (0 : Fin 3) 2 ζ := ⟨_, rfl⟩
  have hvp : ∀ i, v i ^ p = 1 := fun i => by
    rw [hv]
    exact (KFU.torusElt_mem h02 hζ.pow : KFU.torusElt (0 : Fin 3) 2 ζ ∈ KFU.torusVec p 3 K).1 i
  have hvprod : ∏ i, v i = 1 := by rw [hv]; exact KFU.prod_torusElt 0 2 ζ
  have hrel := rel_of_action hc h hact v hvp hvprod ⟨(0, 1), h01⟩
  have e0 : v 0 = ζ := by rw [hv]; exact KFU.torusElt_apply_left h02 ζ
  have e1 : v 1 = 1 := by rw [hv]; exact KFU.torusElt_apply_other h01.symm h12 ζ
  have h2 : ((v 0 * (v 1)⁻¹ : Kˣ) : K) = (ζ : K) := by rw [e0, e1]; simp
  have h3 : ((v 1 * (v 0)⁻¹ : Kˣ) : K) = (ζ : K)⁻¹ := by rw [e0, e1]; simp
  cases ε
  · left
    refine ⟨rfl, ?_⟩
    have : (rho (1 : Equiv.Perm (Fin 3)) false ⟨(0, 1), h01⟩).1 = (0, 1) := rfl
    simp only [rho, Bool.false_eq_true, ite_false, Equiv.Perm.coe_one, id_eq] at hrel
    rw [h2] at hrel
    exact hrel
  · right
    refine ⟨rfl, ?_⟩
    simp only [rho, ite_true, Equiv.Perm.coe_one, id_eq] at hrel
    rw [h2, h3] at hrel
    rw [← inv_pow]
    exact hrel

end Torus

end CFSG.RankThree.PartOne.KFOUT3
