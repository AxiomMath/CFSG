module

public import CFSG.Quasithin.H13.L32AL2y

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

@[expose] def InE (t r : MulAut (VM F)) : Prop :=
  (r ∈ sZero ∧ r * t = t * r) ∨ (r * t ∈ sZero ∧ r * t * t = t * (r * t))

theorem conjSL_mul (A : GL (Fin 2) F) (g g' : SpecialLinearGroup (Fin 2) F) :
    conjSL A (g * g') = conjSL A g * conjSL A g' := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_conjSL, coe_conjSL, coe_conjSL,
    Matrix.SpecialLinearGroup.coe_mul]
  have h1 : (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (A : Matrix (Fin 2) (Fin 2) F), h1, Matrix.one_mul]

@[expose] noncomputable def phiA (A : GL (Fin 2) F) :
    SpecialLinearGroup (Fin 2) F →* MulAut (VM F) :=
  MonoidHom.mk' (fun g => rho (g, conjSL A g)) fun g g' => by
    rw [conjSL_mul, ← map_mul, Prod.mk_mul_mk]

theorem phiA_apply (A : GL (Fin 2) F) (g : SpecialLinearGroup (Fin 2) F) :
    phiA A g = rho (g, conjSL A g) := rfl

namespace L2Cfg

variable {Hs Ts Ls Rs O : Subgroup (MulAut (VM F))} {Vs : Subgroup (VM F)} {t : MulAut (VM F)}
  {a : VM F} [Finite F] [CharP F 2]

theorem fix_iff_comm (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {s : MulAut (VM F)} (hs : s ∈ sZero) :
    s a = a ↔ s * t = t * s := by
  obtain ⟨A, -, htA, c, hc0, hac⟩ := C.exists_A
  obtain ⟨p, q, rfl⟩ := hs
  rw [htA, comm_iff, hac, fix_aJ_iff A hc0]

theorem fix_iff_inE (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {r : MulAut (VM F)} (hr : r ∈ Rs) :
    r a = a ↔ InE t r := by
  constructor
  · intro hra
    rcases C.lin_cases (C.hRT hr) (C.isSemi_one_of_mem hr) with h | h
    · exact Or.inl ⟨h, (C.fix_iff_comm h).mp hra⟩
    · refine Or.inr ⟨h, (C.fix_iff_comm h).mp ?_⟩
      rw [MulAut.mul_apply, C.t_fix, hra]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact (C.fix_iff_comm h1).mpr h2
    · have := (C.fix_iff_comm h1).mpr h2
      rwa [MulAut.mul_apply, C.t_fix] at this

theorem conj_facts (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {n : MulAut (VM F)}
    (hn : n ∈ Ls ∨ n ∈ Ts) :
    (∀ s ∈ sZero, n * s * n⁻¹ ∈ sZero) ∧
      ∃ s₀ ∈ sZero, s₀ * t = t * s₀ ∧ n * t * n⁻¹ = s₀ * t := by
  obtain ⟨A, -, htA, -⟩ := C.exists_A
  have hnN : n ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) := by
    rcases hn with hn | hn
    · obtain ⟨g, h, -, -, rfl⟩ := C.ls_borel hn
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨γ, rfl⟩
        exact ⟨_, by rw [← map_inv, ← map_mul, ← map_mul]⟩
      · rintro ⟨γ, hγ⟩
        refine ⟨(g, h)⁻¹ * γ * (g, h), ?_⟩
        rw [map_mul, map_mul, hγ, map_inv]
        group
    · exact C.mem_gamma hn
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases hn with hn | hn
    · obtain ⟨g, h, hg, hh, rfl⟩ := C.ls_borel hn
      obtain ⟨p, q, rfl⟩ := hs
      rw [borel_conj_sZero hg hh]
      exact ⟨_, _, rfl⟩
    · rw [← C.hS0] at hs ⊢
      exact ⟨Ts.mul_mem (Ts.mul_mem hn hs.1) (Ts.inv_mem hn),
        (Subgroup.mem_normalizer_iff.mp hnN _).mp hs.2⟩
  · have hnR : n ∈ Subgroup.normalizer (Rs : Set (MulAut (VM F))) := C.hRn (by
      rcases hn with hn | hn
      · exact Subgroup.mem_sup_left hn
      · exact Subgroup.mem_sup_right hn)
    have ht' : n * t * n⁻¹ ∈ Rs := (Subgroup.mem_normalizer_iff.mp hnR _).mp C.ht
    obtain ⟨τ, hτ⟩ := isSemi_of_mem_normalizer (by rw [C.card]) hnN
    have hlin : IsSemi (n * t * n⁻¹) 1 := hτ.conj C.isSemi_t
    have hnotNS : ¬ IsNS (n * t * n⁻¹) := by
      intro hNS
      have := isNS_conj (by rw [C.card]) (Subgroup.inv_mem _ hnN) hNS
      rw [show n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t by group, htA] at this
      exact not_isNS_tA A this
    rcases C.lin_cases (C.hRT ht') hlin with h | h
    · exfalso
      apply hnotNS
      obtain ⟨p, q, hpq⟩ := h
      rw [hpq, rho_apply]
      exact ⟨_, _, 1, by rw [frM_one, mul_one]⟩
    · refine ⟨n * t * n⁻¹ * t, h, ?_, ?_⟩
      ·
        have hsq : (n * t * n⁻¹) * (n * t * n⁻¹) = 1 := by
          rw [show (n * t * n⁻¹) * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, C.ht2, mul_one,
            mul_inv_cancel]
        have hinv_t : t⁻¹ = t := inv_eq_of_mul_eq_one_right C.ht2
        have hinv_t' : (n * t * n⁻¹)⁻¹ = n * t * n⁻¹ := inv_eq_of_mul_eq_one_right hsq
        have hcomm : t * (n * t * n⁻¹) = (n * t * n⁻¹) * t := by
          have e := inv_eq_of_mul_eq_one_right (sZero_sq h)
          rwa [_root_.mul_inv_rev, hinv_t, hinv_t'] at e
        rw [← mul_assoc, hcomm]
      · rw [mul_assoc (n * t * n⁻¹) t t, C.ht2, mul_one]

theorem inE_conj (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {n : MulAut (VM F)} (hn : n ∈ Ls ∨ n ∈ Ts)
    {r : MulAut (VM F)} (hr : InE t r) : InE t (n * r * n⁻¹) := by
  obtain ⟨hS, s₀, hs₀, hs₀t, hnt⟩ := C.conj_facts hn
  have key : ∀ x : MulAut (VM F), x * t = t * x → n * x * n⁻¹ ∈ sZero →
      (n * x * n⁻¹) * t = t * (n * x * n⁻¹) := by
    intro x hx hxS
    have e : (n * x * n⁻¹) * (n * t * n⁻¹) = (n * t * n⁻¹) * (n * x * n⁻¹) := by
      rw [show (n * x * n⁻¹) * (n * t * n⁻¹) = n * (x * t) * n⁻¹ by group, hx]
      group
    rw [hnt] at e
    generalize n * x * n⁻¹ = x' at e hxS ⊢
    have : s₀ * (x' * t) = s₀ * (t * x') := by
      rw [← mul_assoc, sZero_comm hs₀ hxS, mul_assoc, e, mul_assoc]
    exact mul_left_cancel this
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hS r h1, key r h2 (hS r h1)⟩
  ·
    have hst : (r * t) * t = t * (r * t) := h2
    have hr' : n * r * n⁻¹ = (n * (r * t) * n⁻¹) * (s₀ * t) := by
      rw [← hnt]
      calc n * r * n⁻¹ = n * (r * (t * t)) * n⁻¹ := by rw [C.ht2, mul_one]
        _ = _ := by group
    have hs' := hS (r * t) h1
    have hc := key (r * t) hst hs'
    generalize n * (r * t) * n⁻¹ = s' at hr' hs' hc
    rw [hr']
    have e2 : s' * (s₀ * t) * t = s' * s₀ := by rw [mul_assoc, mul_assoc, C.ht2, mul_one]
    refine Or.inr ⟨by rw [e2]; exact sZero.mul_mem hs' hs₀, ?_⟩
    rw [e2]
    calc s' * s₀ * t = s' * (t * s₀) := by rw [mul_assoc, hs₀t]
      _ = (s' * t) * s₀ := by group
      _ = (t * s') * s₀ := by rw [hc]
      _ = t * (s' * s₀) := by group

theorem fix_iff (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {n : MulAut (VM F)} (hn : n ∈ Ls ⊔ Ts)
    {r : MulAut (VM F)} (hr : r ∈ Rs) : r (n a) = n a ↔ r a = a := by
  let S : Subgroup (MulAut (VM F)) :=
    { carrier := {n | ∀ r, InE t r ↔ InE t (n * r * n⁻¹)}
      mul_mem' := by
        intro m n hm hn r
        rw [hn r, hm (n * r * n⁻¹)]
        rw [show m * (n * r * n⁻¹) * m⁻¹ = m * n * r * (m * n)⁻¹ by group]
      one_mem' := by
        intro r
        rw [one_mul, inv_one, mul_one]
      inv_mem' := by
        intro n hn r
        rw [hn (n⁻¹ * r * n⁻¹⁻¹)]
        rw [show n * (n⁻¹ * r * n⁻¹⁻¹) * n⁻¹ = r by group] }
  have hgen : ∀ n, n ∈ Ls ∨ n ∈ Ts → n ∈ S := by
    intro n hn r
    refine ⟨C.inE_conj hn, fun h => ?_⟩
    have hn' : n⁻¹ ∈ Ls ∨ n⁻¹ ∈ Ts := by
      rcases hn with hn | hn
      · exact Or.inl (Ls.inv_mem hn)
      · exact Or.inr (Ts.inv_mem hn)
    have := C.inE_conj hn' h
    rwa [show n⁻¹ * (n * r * n⁻¹) * n⁻¹⁻¹ = r by group] at this
  have hS : Ls ⊔ Ts ≤ S := sup_le (fun n hn => hgen n (Or.inl hn)) (fun n hn => hgen n (Or.inr hn))
  have hnS := hS hn
  have hnR : n⁻¹ ∈ Subgroup.normalizer (Rs : Set (MulAut (VM F))) :=
    Subgroup.inv_mem _ (C.hRn hn)
  have hr' : n⁻¹ * r * n⁻¹⁻¹ ∈ Rs := (Subgroup.mem_normalizer_iff.mp hnR _).mp hr
  have e : r (n a) = n a ↔ (n⁻¹ * r * n⁻¹⁻¹) a = a := by
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro h
      rw [h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    · intro h
      have := congrArg n h
      rwa [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at this
  rw [e, C.fix_iff_inE hr', C.fix_iff_inE hr]
  exact ((Subgroup.inv_mem S hnS) r).symm

theorem le_zpowers (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {N : Subgroup (MulAut (VM F))}
    (hNH : N ≤ Hs) (hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1) (hNa : ∀ x ∈ N, x a = a)
    (hDN : ∀ d ∈ (rho (K := F)).range, d a = a →
      d ∈ Subgroup.normalizer (N : Set (MulAut (VM F)))) :
    N ≤ Subgroup.zpowers t := by
  obtain ⟨A, -, htA, c, hc0, hac⟩ := C.exists_A
  have hφa : ∀ g, phiA A g a = a := fun g => by
    rw [phiA_apply, hac, fix_aJ_iff A hc0]
    rfl
  have hφinj : Function.Injective (phiA A) := fun g g' h => by
    have := rho_injective h
    exact congrArg Prod.fst this
  have hD : ∀ d ∈ (rho (K := F)).range, d a = a → ∃ g, d = phiA A g := by
    rintro _ ⟨⟨g, h⟩, rfl⟩ hd
    rw [hac, fix_aJ_iff A hc0] at hd
    refine ⟨g, ?_⟩
    rw [phiA_apply]
    congr 2
    exact Subtype.ext hd
  set N' := N.comap (phiA A) with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun g hg g₀ => ?_⟩
    rw [hN', Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hDN _ ⟨_, rfl⟩ (hφa g₀)) _).mp hg
  have := sl2_isSimple (K := F) (by rw [C.card])
  have := hN'n
  have hN'bot : N' = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h | h
    · exact h
    · exfalso
      obtain ⟨ω, hω, -⟩ := exists_omega C.card
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have hω0 : ω ≠ 0 := by
        rintro rfl
        simp at hω
      have hω1 : ω ≠ 1 := by
        rintro rfl
        exact one_ne_zero (by linear_combination hω - h2)
      have hmem : diagS ω hω0 ∈ N' := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := hN2 _ hmem
      rw [← map_pow] at hk
      have hk' : diagS ω hω0 ^ (2 ^ k) = 1 := hφinj (by rw [hk, map_one])
      have h00 := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F)) hk') 0) 0
      have hUT : IsUT (Matrix.SpecialLinearGroup.toGL (diagS ω hω0)) := by
        change (diagS ω hω0 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        simp [coe_diagS]
      have := hUT.pow_apply_zero_zero (2 ^ k)
      rw [← map_pow] at this
      change ((diagS ω hω0 ^ (2 ^ k) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = _ at this
      rw [h00, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at this
      have e : ((Matrix.SpecialLinearGroup.toGL (diagS ω hω0) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) 0 0 = ω := rfl
      rw [e] at this
      exact hω1 (eq_one_of_pow_two_pow C.card this.symm)
  intro x hx
  have hxN := C.hN (hNH hx)
  have hcomm : ∀ g, x * rho (g, conjSL A g) = rho (g, conjSL A g) * x := by
    intro g
    set d := phiA A g with hd
    have hdN := hDN d ⟨_, rfl⟩ (hφa g)
    have h1 : x * d * x⁻¹ * d⁻¹ ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp hdN _).mp (N.inv_mem hx)
      have := N.mul_mem hx this
      simpa [mul_assoc] using this
    have h2 : x * d * x⁻¹ ∈ (rho (K := F)).range :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp ⟨_, rfl⟩
    have h3 : (x * d * x⁻¹) a = a := by
      have hxa := hNa x hx
      have hxa' : x⁻¹ a = a := by
        conv_lhs => rw [← hxa]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rw [MulAut.mul_apply, MulAut.mul_apply, hxa', hφa, hxa]
    obtain ⟨g', hg'⟩ := hD _ h2 h3
    have h4 : g' * g⁻¹ ∈ N' := by
      rw [hN', Subgroup.mem_comap, map_mul, map_inv, ← hg', ← hd]
      exact h1
    rw [hN'bot, Subgroup.mem_bot, mul_inv_eq_one] at h4
    rw [h4, ← hd] at hg'
    have : x * d = d * x := by
      calc x * d = x * d * x⁻¹ * x := by group
        _ = d * x := by rw [hg']
    exact this
  obtain ⟨k, hk⟩ := hN2 x hx
  rcases eq_of_comm_diag C.card A hxN hk hcomm with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h, ← htA]
    exact Subgroup.mem_zpowers t

theorem stab_of_fix (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {x : MulAut (VM F)} (hx : x ∈ Hs)
    {v₀ : VM F} (hv₀ : v₀ ∈ Vs) (hv1 : v₀ ≠ 1) (hxv : x v₀ = v₀) {v : VM F} (hv : v ∈ Vs) :
    x v ∈ Vs := by
  obtain ⟨τ, hτ⟩ := isSemi_of_mem_normalizer (by rw [C.card]) (C.hN hx)
  obtain ⟨c₀, rfl⟩ := (C.vs_iff _).mp hv₀
  obtain ⟨c, rfl⟩ := (C.vs_iff _).mp hv
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hv1
    rw [zero_smul]
    rfl
  have e : c • (matE : Matrix (Fin 2) (Fin 2) F) = (c / c₀) • (c₀ • matE) := by
    rw [smul_smul, div_mul_cancel₀ _ hc₀]
  rw [e]
  have h1 := hτ (c / c₀) (c₀ • matE)
  rw [hxv, toAdd_ofAdd] at h1
  rw [← ofAdd_toAdd (x _), h1, smul_smul]
  exact C.e11_mem _

end L2Cfg

end CFSG.Quasithin.H13.L32A.L2
