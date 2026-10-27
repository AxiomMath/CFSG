module

public import CFSG.RankThree.GF2n.Smith81.S81ZUniform

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 Module

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]
  {Γ : Type*} [Group Γ]

@[expose] def fixP (A : Γ →* (X ≃ₗ[K] X)) (P : Subgroup Γ) : Submodule K X where
  carrier := {v | ∀ p ∈ P, A p v = v}
  add_mem' {v w} hv hw p hp := by rw [map_add, hv p hp, hw p hp]
  zero_mem' p _ := map_zero _
  smul_mem' c v hv p hp := by rw [map_smul, hv p hp]

theorem mem_fixP {A : Γ →* (X ≃ₗ[K] X)} {P : Subgroup Γ} {v : X} :
    v ∈ fixP A P ↔ ∀ p ∈ P, A p v = v := Iff.rfl

theorem fixP_anti {A : Γ →* (X ≃ₗ[K] X)} {P P' : Subgroup Γ} (h : P ≤ P') :
    fixP A P' ≤ fixP A P := fun _ hv p hp => hv p (h hp)

theorem exists_fixed_ne_zero [Finite X] [Nontrivial X] (A : Γ →* (X ≃ₗ[K] X)) {P : Subgroup Γ}
    (hP : IsPGroup 2 P) : ∃ x : X, x ≠ 0 ∧ ∀ p ∈ P, A p x = x := by
  classical
  letI : MulAction P X := MulAction.compHom X (A.comp P.subtype)
  have h2 : 2 ∣ Nat.card K := by
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hKn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hKn]
    exact dvd_pow_self 2 n.ne_zero
  haveI : Module.Finite K X := Module.Finite.of_finite
  have hdvd : 2 ∣ Nat.card X := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := X)]
    exact dvd_pow h2 (Module.finrank_pos (R := K) (M := X)).ne'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : (0 : X) ∈ MulAction.fixedPoints P X := fun p => map_zero (A p)
  obtain ⟨x, hx, hx0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point X hdvd h0
  exact ⟨x, fun h => hx0 h.symm, fun p hp => hx ⟨p, hp⟩⟩

theorem fixP_eq_of_le_line [Finite X] (A : Γ →* (X ≃ₗ[K] X)) {P : Subgroup Γ} (hP : IsPGroup 2 P)
    {ℓ : Submodule K X} (hℓ : finrank K ℓ = 1) (hle : fixP A P ≤ ℓ) : fixP A P = ℓ := by
  haveI : Module.Finite K X := Module.Finite.of_finite
  haveI : Nontrivial X := by
    have hne : ℓ ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hℓ
      exact zero_ne_one hℓ
    obtain ⟨x, -, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨⟨x, 0, hx⟩⟩
  obtain ⟨x, hx0, hx⟩ := exists_fixed_ne_zero A hP
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [hℓ]
  exact Submodule.one_le_finrank_iff.2 (Submodule.ne_bot_iff _ |>.2 ⟨x, hx, hx0⟩)

theorem mem_smul_sylow {S : Sylow 2 Γ} {g x : Γ} :
    x ∈ ((g • S : Sylow 2 Γ) : Subgroup Γ) ↔ g⁻¹ * x * g ∈ (S : Subgroup Γ) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (MulAut.conj g • y) * g = y := by
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    rw [e]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

theorem fixP_map_conj (A : Γ →* (X ≃ₗ[K] X)) (H : Subgroup Γ) (g : Γ) :
    fixP A (H.map (MulAut.conj g).toMonoidHom) = (fixP A H).map (A g : X →ₗ[K] X) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨A g⁻¹ v, fun s hs => ?_, ?_⟩
    · have hmem : g * s * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
        ⟨s, hs, by simp [MulAut.conj_apply]⟩
      have h1 := hv _ hmem
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
      apply (A g).injective
      rw [h1, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    · show A g (A g⁻¹ v) = v
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  · rintro ⟨w, hw, rfl⟩ p ⟨s, hs, rfl⟩
    show A (g * s * g⁻¹) (A g w) = A g w
    have e : g * s * g⁻¹ * g = g * s := by group
    rw [← LinearEquiv.mul_apply, ← map_mul, e, map_mul, LinearEquiv.mul_apply, hw s hs]

theorem coe_smul_sylow (S : Sylow 2 Γ) (g : Γ) :
    ((g • S : Sylow 2 Γ) : Subgroup Γ) = (S : Subgroup Γ).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_smul_sylow, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy

theorem exists_sylow_translate [Finite Γ] [Finite X] (A : Γ →* (X ≃ₗ[K] X)) {P₁ P₂ : Subgroup Γ}
    (h₁ : IsPGroup 2 P₁) (h₂ : IsPGroup 2 P₂) {ℓ₁ ℓ₂ : Submodule K X}
    (hℓ₁ : finrank K ℓ₁ = 1) (hℓ₂ : finrank K ℓ₂ = 1) (hle₁ : fixP A P₁ ≤ ℓ₁)
    (hle₂ : fixP A P₂ ≤ ℓ₂) : ∃ g : Γ, ℓ₂ = ℓ₁.map (A g : X →ₗ[K] X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁⟩ := h₁.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := h₂.exists_le_sylow
  haveI : Finite (Sylow 2 Γ) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S₁ S₂
  have e₁ : fixP A S₁ = ℓ₁ :=
    fixP_eq_of_le_line A S₁.isPGroup' hℓ₁ ((fixP_anti hS₁).trans hle₁)
  have e₂ : fixP A S₂ = ℓ₂ :=
    fixP_eq_of_le_line A S₂.isPGroup' hℓ₂ ((fixP_anti hS₂).trans hle₂)
  refine ⟨g, ?_⟩
  rw [← e₁, ← e₂, ← hg, coe_smul_sylow, fixP_map_conj]

end Fixed

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]
  {Λ Γ : Type*} [Group Λ] [Group Γ]

theorem exists_lift_translate [Finite Γ] [Finite X] (θ : Λ →* Γ) (hθ : Function.Surjective θ)
    (T : Λ →* (X ≃ₗ[K] X)) (A₁ : Γ →* (X ≃ₗ[K] X)) (hA₁ : ∀ s, A₁ (θ s) = T s)
    {L₁ L₂ : Subgroup Λ} (h₁ : IsPGroup 2 (L₁.map θ)) (h₂ : IsPGroup 2 (L₂.map θ))
    {ℓ₁ ℓ₂ : Submodule K X} (hℓ₁ : finrank K ℓ₁ = 1) (hℓ₂ : finrank K ℓ₂ = 1)
    (hf₁ : ∀ v, (∀ s ∈ L₁, T s v = v) ↔ v ∈ ℓ₁) (hf₂ : ∀ v, (∀ s ∈ L₂, T s v = v) ↔ v ∈ ℓ₂) :
    ∃ s : Λ, ℓ₂ = ℓ₁.map (T s : X →ₗ[K] X) := by
  have hle : ∀ (L : Subgroup Λ) (ℓ : Submodule K X), (∀ v, (∀ s ∈ L, T s v = v) ↔ v ∈ ℓ) →
      fixP A₁ (L.map θ) ≤ ℓ := by
    intro L ℓ hf v hv
    refine (hf v).1 fun s hs => ?_
    rw [← hA₁ s]
    exact hv _ (Subgroup.mem_map_of_mem θ hs)
  obtain ⟨g, hg⟩ := exists_sylow_translate A₁ h₁ h₂ hℓ₁ hℓ₂ (hle L₁ ℓ₁ hf₁) (hle L₂ ℓ₂ hf₂)
  obtain ⟨s, rfl⟩ := hθ g
  exact ⟨s, by rw [hg, hA₁]⟩

end Lift

section Points

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {K : Type}
  [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem sup_eq_of_img_iff {A A' : Subgroup G} (hAQ : A ≤ Q) (hA'Q : A' ≤ Q)
    (h : ∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ ∃ x ∈ A', M₀.π x = v) : A ⊔ Z = A' ⊔ Z := by
  have key : ∀ {A A' : Subgroup G}, A ≤ Q → A' ≤ Q →
      (∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) → ∃ x ∈ A', M₀.π x = v) → A ≤ A' ⊔ Z := by
    intro A A' hAQ hA'Q h x hx
    obtain ⟨y, hy, hyx⟩ := h (M₀.π x) ⟨x, hx, rfl⟩
    have hz : y⁻¹ * x ∈ Z := (M₀.pi_eq_iff (hA'Q hy) (hAQ hx)).1 hyx
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx']
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hz)
  apply le_antisymm
  · exact sup_le (key hAQ hA'Q (fun v hv => (h v).1 hv)) le_sup_right
  · exact sup_le (key hA'Q hAQ (fun v hv => (h v).2 hv)) le_sup_right

variable {Λ : Subgroup G}

theorem img_conj_iff (T : Λ →* (M₀.E ≃ₗ[K] M₀.E)) (hBQ : B ≤ Q)
    (hTe : ∀ (s : Λ) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x)) (s : Λ)
    (v : M₀.E) :
    (∃ x ∈ conjSubgroup (s : G) B, M₀.π x = v) ↔ ∃ w, (∃ b ∈ B, M₀.π b = w) ∧ T s w = v := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_conjSubgroup] at hx
    refine ⟨M₀.π ((s : G)⁻¹ * x * (s : G)), ⟨_, hx, rfl⟩, ?_⟩
    rw [← hTe s _ (hBQ hx)]
    congr 1
    group
  · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨(s : G) * b * (s : G)⁻¹, ?_, hTe s b (hBQ hb)⟩
    rw [mem_conjSubgroup, show (s : G)⁻¹ * ((s : G) * b * (s : G)⁻¹) * (s : G) = b by group]
    exact hb

theorem LB_eq_conj_of_img (hSame : ∀ C C' : Subgroup G, Ctx M Q Z C → Ctx M Q Z C' →
      C ⊔ Z = C' ⊔ Z → LB M Q C = LB M Q C')
    (hctx : Ctx M Q Z B) {A : Subgroup G} (hA : Ctx M Q Z A) (T : Λ →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Λ) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x)) (s : Λ)
    (hsM : (s : G) ∈ M)
    (himg : ∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ ∃ w, (∃ b ∈ B, M₀.π b = w) ∧ T s w = v) :
    LB M Q A = conjSubgroup (s : G) (LB M Q B) := by
  have hBs : Ctx M Q Z (conjSubgroup (s : G) B) := hctx.conj_of_mem hsM
  have hsup : A ⊔ Z = conjSubgroup (s : G) B ⊔ Z :=
    sup_eq_of_img_iff (M₀ := M₀) hA.le hBs.le fun v => (himg v).trans (img_conj_iff T hctx.le hTe s v).symm
  rw [hSame A _ hA hBs hsup, hctx.LB_conj hsM]

end Points

section PointLift


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_line_fix (h34 : Stroth34Statement) {A : Subgroup G} (hctxA : Ctx M Q Z A) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hg : GlobalModelData M Q Z γ M₀) (hno : NoA2 Q Z (LB M Q A))
    (hgen : GenByB M Q A) {Lg : Subgroup G} (T : Lg →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lg) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hLBle : LB M Q A ≤ Lg) :
    ∃ e : M₀.E, e ≠ 0 ∧ (∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ v ∈ Submodule.span K {e}) ∧
      ∀ v : M₀.E, (∀ s : Lg, (s : G) ∈ LB M Q A → T s v = v) ↔ v ∈ Submodule.span K {e} := by
  have hZQ : Z ≤ Q := hctxA.hyp.Z_normal.1
  have hM : M ≤ Subgroup.normalizer (Q : Set G) := hctxA.hyp.Q_normal.2
  obtain ⟨-, hCQt, -, -⟩ := stroth_3_5 h34 hctxA hw hn hno hgen
  obtain ⟨e, he0, he⟩ := exists_span_eq_img hg hctxA.conj hctxA.le hctxA.ne
  refine ⟨e, he0, he, fun v => ?_⟩
  rw [← he v]
  exact fixed_iff_mem_img (Lg := Lg) hctxA hctxA.LB_le_M hM hZQ rfl hCQt hctxA.le T hTe hLBle v

theorem exists_lift_point (hSame : ∀ C C' : Subgroup G, Ctx M Q Z C → Ctx M Q Z C' →
      C ⊔ Z = C' ⊔ Z → LB M Q C = LB M Q C')
    (h34 : Stroth34Statement) (hctx : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hg : GlobalModelData M Q Z γ M₀) {Γ : Type*} [Group Γ] [Finite Γ]
    (θ : Lgen M (LB M Q B) →* Γ) (hθs : Function.Surjective θ)
    (hθk : ∀ s : Lgen M (LB M Q B), θ s = 1 ↔ (s : G) ∈ Q)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (A₁ : Γ →* (M₀.E ≃ₗ[K] M₀.E)) (hA₁ : ∀ s, A₁ (θ s) = T s)
    (hTac : ∀ A : Subgroup G, Ctx M Q Z A → NoA2 Q Z (LB M Q A) ∧ GenByB M Q A)
    (hLBle : ∀ A : Subgroup G, Ctx M Q Z A → LB M Q A ≤ Lgen M (LB M Q B))
    {A : Subgroup G} (hctxA : Ctx M Q Z A) :
    ∃ s : Lgen M (LB M Q B), LB M Q A = conjSubgroup (s : G) (LB M Q B) ∧
      ∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ ∃ w, (∃ b ∈ B, M₀.π b = w) ∧ T s w = v := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hline : ∀ C : Subgroup G, Ctx M Q Z C →
      ∃ e : M₀.E, e ≠ 0 ∧ (∀ v : M₀.E, (∃ x ∈ C, M₀.π x = v) ↔ v ∈ Submodule.span K {e}) ∧
        ∀ v : M₀.E, (∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q C → T s v = v) ↔
          v ∈ Submodule.span K {e} := fun C hC =>
    exists_line_fix h34 hC hw hn hg (hTac C hC).1 (hTac C hC).2 T hTe (hLBle C hC)
  have hP2 : ∀ C : Subgroup G, Ctx M Q Z C →
      IsPGroup 2 (((LB M Q C).subgroupOf (Lgen M (LB M Q B))).map θ) := by
    intro C hC x
    obtain ⟨y, hy, hyx⟩ := x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← hyx, ← map_pow, hθk, Subgroup.coe_pow]
    exact hC.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hy)
  obtain ⟨eB, heB0, heBi, heBf⟩ := hline B hctx
  obtain ⟨eA, heA0, heAi, heAf⟩ := hline A hctxA
  have hfin : ∀ e : M₀.E, e ≠ 0 → finrank K (Submodule.span K {e}) = 1 :=
    fun e he => finrank_span_singleton he
  obtain ⟨s, hs⟩ := exists_lift_translate θ hθs T A₁ hA₁ (hP2 B hctx) (hP2 A hctxA) (hfin eB heB0)
    (hfin eA heA0)
    (fun v => by
      rw [← heBf v]
      exact ⟨fun h s hs => h s (Subgroup.mem_subgroupOf.2 hs), fun h s hs =>
        h s (Subgroup.mem_subgroupOf.1 hs)⟩)
    (fun v => by
      rw [← heAf v]
      exact ⟨fun h s hs => h s (Subgroup.mem_subgroupOf.2 hs), fun h s hs =>
        h s (Subgroup.mem_subgroupOf.1 hs)⟩)
  have himg : ∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ ∃ w, (∃ b ∈ B, M₀.π b = w) ∧ T s w = v := by
    intro v
    rw [heAi v, hs, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw', rfl⟩
      exact ⟨w, (heBi w).2 hw', rfl⟩
    · rintro ⟨w, hw', rfl⟩
      exact ⟨w, (heBi w).1 hw', rfl⟩
  refine ⟨s, ?_, himg⟩
  have hsM : (s : G) ∈ M := Lgen_le hctx.LB_le_M s.2
  exact LB_eq_conj_of_img hSame hctx hctxA T hTe s hsM himg

theorem mem_normalizer_of_stab (hSame : ∀ C C' : Subgroup G, Ctx M Q Z C → Ctx M Q Z C' →
      C ⊔ Z = C' ⊔ Z → LB M Q C = LB M Q C')
    (hctx : Ctx M Q Z B) {Γ : Type*} [Group Γ] (θ : Lgen M (LB M Q B) →* Γ)
    (hθs : Function.Surjective θ) (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (A₁ : Γ →* (M₀.E ≃ₗ[K] M₀.E)) (hA₁ : ∀ s, A₁ (θ s) = T s) {ℓ : Submodule K M₀.E}
    (hℓ : ∀ v : M₀.E, (∃ x ∈ B, M₀.π x = v) ↔ v ∈ ℓ) {g : Γ}
    (hg : ℓ.map (A₁ g : M₀.E →ₗ[K] M₀.E) = ℓ) :
    g ∈ Subgroup.normalizer ((((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ : Subgroup Γ) :
      Set Γ) := by
  obtain ⟨s, rfl⟩ := hθs g
  have hsM : (s : G) ∈ M := Lgen_le hctx.LB_le_M s.2
  have hTs : ℓ.map (T s : M₀.E →ₗ[K] M₀.E) = ℓ := by rw [← hA₁]; exact hg
  have himg : ∀ v : M₀.E, (∃ x ∈ B, M₀.π x = v) ↔ ∃ w, (∃ b ∈ B, M₀.π b = w) ∧ T s w = v := by
    intro v
    rw [hℓ v, ← hTs, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (hℓ w).2 hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (hℓ w).1 hw, rfl⟩
  have hLB : LB M Q B = conjSubgroup (s : G) (LB M Q B) :=
    LB_eq_conj_of_img hSame hctx hctx T hTe s hsM himg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨s * t * s⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have h1 : (s : G) * (t : G) * (s : G)⁻¹ ∈ conjSubgroup (s : G) (LB M Q B) := by
      rw [mem_conjSubgroup, show (s : G)⁻¹ * ((s : G) * (t : G) * (s : G)⁻¹) * (s : G) = (t : G)
        by group]
      exact Subgroup.mem_subgroupOf.1 ht
    rw [← hLB] at h1
    exact h1
  · rintro ⟨t, ht, hth⟩
    refine ⟨s⁻¹ * t * s, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have h1 : (t : G) ∈ conjSubgroup (s : G) (LB M Q B) := by
        rw [← hLB]
        exact Subgroup.mem_subgroupOf.1 ht
      rw [mem_conjSubgroup] at h1
      simpa using h1
    · rw [map_mul, map_mul, map_inv, hth]
      group

theorem point_of_translate {V : Type} [AddCommGroup V] [Module K V] {Γ : Subgroup (V ≃ₗ[K] V)}
    {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)} (hctx : Ctx M Q Z B)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E)) (ψ : M₀.E ≃ₗ[K] V)
    (φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V))
    (hker : ∀ s : Lgen M (LB M Q B), φ s = 1 ↔ (s : G) ∈ Q)
    (hφT : ∀ (s : Lgen M (LB M Q B)) (v : M₀.E), ψ (T s v) = φ s (ψ v))
    (hΓ : ∀ s : Lgen M (LB M Q B), φ s ∈ Γ)
    (hψB : ∀ w : V, (∃ x ∈ B, ψ (M₀.π x) = w) ↔ w ∈ Submodule.span K {p₀})
    (hφB : ∀ u : V ≃ₗ[K] V, (∃ t : Lgen M (LB M Q B), (t : G) ∈ LB M Q B ∧ φ t = u) ↔ u ∈ U₀)
    (hlift : ∀ A : Subgroup G, Ctx M Q Z A → ∃ s : Lgen M (LB M Q B),
      LB M Q A = conjSubgroup (s : G) (LB M Q B) ∧
        ∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ ∃ w, (∃ b ∈ B, M₀.π b = w) ∧ T s w = v) :
    ∀ A : Subgroup G, IsZConjugate Z A → A ≤ Q → A ≠ Z → ∃ g ∈ Γ,
      (fun a : G => ψ (M₀.π a)) '' (A : Set G) = (Submodule.span K {g p₀} : Set V) ∧
      ∀ u ∈ conjSub g U₀, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A ∧ φ t = u := by
  classical
  intro A hAZ hAQ hAne
  have hctxA : Ctx M Q Z A := ⟨hctx.hyp, hAZ, hAQ, hAne⟩
  have hM : M ≤ Subgroup.normalizer (Q : Set G) := hctx.hyp.Q_normal.2
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  obtain ⟨s, hLA, himg⟩ := hlift A hctxA
  refine ⟨φ s, hΓ s, ?_, fun u hu => ?_⟩
  · ext w
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w', ⟨b, hb, rfl⟩, hw'⟩ := (himg (M₀.π x)).1 ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ((hψB (ψ (M₀.π b))).1 ⟨b, hb, rfl⟩)
      refine ⟨c, ?_⟩
      rw [← hw', hφT, ← hc, map_smul]
    · rintro ⟨c, rfl⟩
      obtain ⟨b, hb, hbc⟩ := (hψB (c • p₀)).2 (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self p₀))
      obtain ⟨x, hx, hxb⟩ := (himg (T s (M₀.π b))).2 ⟨M₀.π b, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      rw [hxb, hφT, hbc, map_smul]
  · obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.1 hu
    obtain ⟨t₀, ht₀, hφt₀⟩ := (hφB u₀).2 hu₀
    have hsLB : ((s * t₀ * s⁻¹ : Lgen M (LB M Q B)) : G) ∈ LB M Q A := by
      rw [hLA, mem_conjSubgroup]
      have : (s : G)⁻¹ * (((s * t₀ * s⁻¹ : Lgen M (LB M Q B))) : G) * (s : G) = (t₀ : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact ht₀
    have hsup : ((s * t₀ * s⁻¹ : Lgen M (LB M Q B)) : G) ∈ (QB A ⊓ M) ⊔ Q := by
      rw [sup_comm]
      exact hsLB
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := QB A ⊓ M) (K := Q)
        (fun x hx => hM (Subgroup.mem_inf.1 hx).2) hsup
    have hyLg : y ∈ Lgen M (LB M Q B) := by
      have e : y = ((s * t₀ * s⁻¹ : Lgen M (LB M Q B)) : G) * z⁻¹ := by
        rw [← hyz]
        group
      rw [e]
      exact mul_mem (s * t₀ * s⁻¹).2 (inv_mem (hQLg hz))
    refine ⟨⟨y, hyLg⟩, hy.1, ?_⟩
    have hs_eq : s * t₀ * s⁻¹ = ⟨y, hyLg⟩ * ⟨z, hQLg hz⟩ := Subtype.ext hyz.symm
    have h1 : φ (s * t₀ * s⁻¹) = φ ⟨y, hyLg⟩ := by
      rw [hs_eq, map_mul, (hker ⟨z, hQLg hz⟩).2 hz, mul_one]
    rw [← h1, map_mul, map_mul, map_inv, hφt₀]

end PointLift

end CFSG.RankThree.GF2n.Smith81.S81Z
