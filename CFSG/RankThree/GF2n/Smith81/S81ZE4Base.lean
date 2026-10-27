module

public import CFSG.RankThree.GF2n.Smith81.S81ZPts
public import CFSG.RankThree.GF2n.Smith81.S81QM2
public import CFSG.RankThree.GF2n.Smith81.S81QGraphAut

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.S81V Module


section Transport

variable {𝔾 : Type*} [Group 𝔾] {E : Subgroup 𝔾}

theorem mem_normalizer_map_subtype {H : Subgroup ↥E} {g : ↥E}
    (hg : g ∈ Subgroup.normalizer (H : Set ↥E)) :
    (g : 𝔾) ∈ Subgroup.normalizer ((H.map E.subtype : Subgroup 𝔾) : Set 𝔾) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (hg y).1 hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hy' : g⁻¹ * y * g ∈ H := (hg _).2 (by simpa [mul_assoc] using hy)
    refine ⟨g⁻¹ * y * g, hy', ?_⟩
    have hyx' : (y : 𝔾) = (g : 𝔾) * x * (g : 𝔾)⁻¹ := hyx
    show (g : 𝔾)⁻¹ * (y : 𝔾) * (g : 𝔾) = x
    rw [hyx']
    group

theorem mem_normalizer_of_map_subtype {H : Subgroup ↥E} {g : ↥E}
    (hg : (g : 𝔾) ∈ Subgroup.normalizer ((H.map E.subtype : Subgroup 𝔾) : Set 𝔾)) :
    g ∈ Subgroup.normalizer (H : Set ↥E) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  have h1 := hg (x : 𝔾)
  have e1 : (x : 𝔾) ∈ (H.map E.subtype : Subgroup 𝔾) ↔ x ∈ H :=
    Subgroup.mem_map_iff_mem E.subtype_injective
  have e2 : (g : 𝔾) * (x : 𝔾) * (g : 𝔾)⁻¹ ∈ (H.map E.subtype : Subgroup 𝔾) ↔ g * x * g⁻¹ ∈ H :=
    Subgroup.mem_map_iff_mem (f := E.subtype) (x := g * x * g⁻¹) E.subtype_injective
  rw [← e1, ← e2]
  exact h1

end Transport

section Fixed

variable {K : Type} [Field K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]
  {Γ : Type*} [Group Γ]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup Γ} {t : Γ}
    (ht : t ∈ Subgroup.normalizer (H : Set Γ)) :
    H.map (MulAut.conj t).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_normalizer_iff] at ht
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (ht y).1 hy
  · intro hx
    refine ⟨t⁻¹ * x * t, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact (ht _).2 (by simpa [mul_assoc] using hx)

theorem fixP_map_of_mem_normalizer [Finite K] (A : Γ →* (X ≃ₗ[K] X)) {H : Subgroup Γ} {t : Γ}
    (ht : t ∈ Subgroup.normalizer (H : Set Γ)) :
    (fixP A H).map (A t : X →ₗ[K] X) = fixP A H := by
  rw [← fixP_map_conj, map_conj_eq_of_mem_normalizer ht]

theorem fixP_map_of_mem [Finite K] (A : Γ →* (X ≃ₗ[K] X)) {H : Subgroup Γ} {u : Γ} (hu : u ∈ H) :
    (fixP A H).map (A u : X →ₗ[K] X) = fixP A H := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    show A u w ∈ fixP A H
    rw [hw u hu]
    exact hw
  · intro hv
    exact ⟨v, hv, hv u hu⟩

theorem isElemAbelian_of_sq {H : Type*} [Group H] (A : Subgroup H) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    IsElemAbelian 2 A := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, hsq⟩
  have h1 : (a : H) * a = 1 := by rw [← pow_two]; exact hsq a a.2
  have h2 : (b : H) * b = 1 := by rw [← pow_two]; exact hsq b b.2
  have h3 : (a : H) * b * ((a : H) * b) = 1 := by rw [← pow_two]; exact hsq _ (mul_mem a.2 b.2)
  apply Subtype.ext
  show (a : H) * b = b * a
  rw [eq_inv_of_mul_eq_one_left h3, mul_inv_rev, inv_eq_of_mul_eq_one_left h1,
    inv_eq_of_mul_eq_one_left h2]

end Fixed

section Base

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem isPGroup_of_sq {H : Type*} [Group H] (A : Subgroup H) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    IsPGroup 2 A := fun x =>
  ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]; exact hsq x x.2)⟩

theorem sq_of_map_subtype {𝔾 : Type*} [Group 𝔾] {E : Subgroup 𝔾} {H : Subgroup ↥E}
    (hsq : ∀ h ∈ H, h ^ 2 = 1) : ∀ a ∈ H.map E.subtype, a ^ 2 = 1 := by
  rintro _ ⟨h, hh, rfl⟩
  show (h : 𝔾) ^ 2 = 1
  rw [← Subgroup.coe_pow, hsq h hh]
  rfl

theorem exists_base_E4
    (hSame : ∀ C C' : Subgroup G, Ctx M Q Z C → Ctx M Q Z C' → C ⊔ Z = C' ⊔ Z →
      LB M Q C = LB M Q C')
    (h34 : Stroth34Statement) (hctx : Ctx M Q Z B) (hw : Width Q Z 16)
    (hg : GlobalModelData M Q Z γ M₀) (hnoB : NoA2 Q Z (LB M Q B)) (hgenB : GenByB M Q B)
    (hUp : IsPGroup 2 (posU0 K)) (hT0E : T0 K ≤ EAut0 K)
    (hTnorm : ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (posU0 K : Set (W K ≃ₗ[K] W K)))
    (θ₀ : Lgen M (LB M Q B) →* ↥(EAut0 K)) (hθ₀s : Function.Surjective θ₀)
    (hθ₀k : ∀ s : Lgen M (LB M Q B), θ₀ s = 1 ↔ (s : G) ∈ Q) :
    ∃ θ : Lgen M (LB M Q B) →* ↥(EAut0 K), Function.Surjective θ ∧
      (∀ s : Lgen M (LB M Q B), θ s = 1 ↔ (s : G) ∈ Q) ∧
      ((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ = (rootRad0 K).subgroupOf (EAut0 K) := by
  classical
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hq : 4 ≤ Nat.card K := by
    rw [hKcard]
    exact hctx.hyp.q4
  obtain ⟨-, -, hLBcard, -⟩ := stroth_3_5 h34 hctx hw (by norm_num) hnoB hgenB
  obtain ⟨T, hTe, hTker, -⟩ := exists_T_Lgen_isom hctx hg
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hsqθ : ∀ θ : Lgen M (LB M Q B) →* ↥(EAut0 K), (∀ s, θ s = 1 ↔ (s : G) ∈ Q) →
      ∀ s ∈ (LB M Q B).subgroupOf (Lgen M (LB M Q B)), θ s ^ 2 = 1 := by
    intro θ hθ s hs
    rw [← map_pow, hθ, Subgroup.coe_pow]
    exact hctx.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hs)
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ↥(EAut0 K) →* (M₀.E ≃ₗ[K] M₀.E),
      ∀ s : Lgen M (LB M Q B), A₀ (θ₀ s) = T s := by
    have hle : θ₀.ker ≤ T.ker := fun s hs => by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact (hTker s).2 ((hθ₀k s).1 hs)
    exact ⟨θ₀.liftOfRightInverse (Function.surjInv hθ₀s) (Function.rightInverse_surjInv hθ₀s)
      ⟨T, hle⟩, fun s => θ₀.liftOfRightInverse_comp_apply _ _ _ s⟩
  set P₀ : Subgroup ↥(EAut0 K) := ((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ₀ with hP₀
  have hP₀sq : ∀ a ∈ P₀.map (EAut0 K).subtype, a ^ 2 = 1 := by
    refine sq_of_map_subtype ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hsqθ θ₀ hθ₀k s hs
  obtain ⟨g, hgE, hgU⟩ := exists_conj_le_posU0 (A := P₀.map (EAut0 K).subtype)
    (Subgroup.map_subtype_le P₀) (isPGroup_of_sq _ hP₀sq)
  set g₁ : ↥(EAut0 K) := ⟨g, hgE⟩ with hg₁
  let θ₁ : Lgen M (LB M Q B) →* ↥(EAut0 K) := (MulAut.conj g₁).toMonoidHom.comp θ₀
  have hθ₁s : Function.Surjective θ₁ := (MulAut.conj g₁).surjective.comp hθ₀s
  have hθ₁k : ∀ s : Lgen M (LB M Q B), θ₁ s = 1 ↔ (s : G) ∈ Q := fun s => by
    rw [← hθ₀k s]
    show (MulAut.conj g₁) (θ₀ s) = 1 ↔ _
    exact map_eq_one_iff _ (MulAut.conj g₁).injective
  let A₁ : ↥(EAut0 K) →* (M₀.E ≃ₗ[K] M₀.E) := A₀.comp (MulAut.conj g₁⁻¹).toMonoidHom
  have hA₁ : ∀ s : Lgen M (LB M Q B), A₁ (θ₁ s) = T s := by
    intro s
    rw [← hA₀ s]
    show A₀ (g₁⁻¹ * (g₁ * θ₀ s * g₁⁻¹) * g₁⁻¹⁻¹) = A₀ (θ₀ s)
    congr 1
    group
  set P₁ : Subgroup ↥(EAut0 K) := ((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ₁ with hP₁
  set U'' : Subgroup ↥(EAut0 K) := (posU0 K).subgroupOf (EAut0 K) with hU''
  have hP₁U : P₁ ≤ U'' := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hU'', Subgroup.mem_subgroupOf]
    apply hgU
    exact ⟨((θ₀ s : ↥(EAut0 K)) : W K ≃ₗ[K] W K), ⟨θ₀ s, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨e, he0, heB, hfixB⟩ :=
    exists_line_fix h34 hctx hw (by norm_num) hg hnoB hgenB T hTe (le_Lgen _)
  set ℓ : Submodule K M₀.E := Submodule.span K {e} with hℓ
  have hℓ1 : finrank K ℓ = 1 := finrank_span_singleton he0
  have hCle : fixP A₁ U'' ≤ ℓ := by
    intro v hv
    refine (hfixB v).1 fun s hs => ?_
    rw [← hA₁ s]
    exact hv _ (hP₁U ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩)
  have hU''p : IsPGroup 2 U'' := hUp.comap_subtype
  have hCeq : fixP A₁ U'' = ℓ := fixP_eq_of_le_line A₁ hU''p hℓ1 hCle
  have hstabU : ∀ u ∈ U'', ℓ.map (A₁ u : M₀.E →ₗ[K] M₀.E) = ℓ := by
    intro u hu
    rw [← hCeq]
    exact fixP_map_of_mem A₁ hu
  have hU''N : ∀ t : ↥(EAut0 K), (t : W K ≃ₗ[K] W K) ∈ T0 K →
      t ∈ Subgroup.normalizer (U'' : Set ↥(EAut0 K)) := by
    intro t ht
    apply mem_normalizer_of_map_subtype (E := EAut0 K) (H := U'')
    rw [hU'', Subgroup.map_subgroupOf_eq_of_le (posU0_le_EAut0 (K := K))]
    exact hTnorm _ ht
  have hstabT : ∀ t : ↥(EAut0 K), (t : W K ≃ₗ[K] W K) ∈ T0 K →
      ℓ.map (A₁ t : M₀.E →ₗ[K] M₀.E) = ℓ := by
    intro t ht
    rw [← hCeq]
    exact fixP_map_of_mem_normalizer A₁ (hU''N t ht)
  have hnorm : ∀ x : ↥(EAut0 K), ℓ.map (A₁ x : M₀.E →ₗ[K] M₀.E) = ℓ →
      x ∈ Subgroup.normalizer (P₁ : Set ↥(EAut0 K)) := fun x hx =>
    mem_normalizer_of_stab hSame hctx θ₁ hθ₁s T hTe A₁ hA₁ heB hx
  set P₁V : Subgroup (W K ≃ₗ[K] W K) := P₁.map (EAut0 K).subtype with hP₁V
  have hP₁Vsq : ∀ a ∈ P₁V, a ^ 2 = 1 := by
    refine sq_of_map_subtype ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hsqθ θ₁ hθ₁k s hs
  have hP₁Vcard : Nat.card K ^ 15 ≤ Nat.card P₁V := by
    have key : Nat.card (LB M Q B) = Nat.card Q * Nat.card P₁ :=
      card_eq_card_mul_card_map_of_ker (S := LB M Q B) θ₁ hθ₁k hQLg le_sup_left (le_Lgen _)
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have h15 : Nat.card P₁ = Nat.card Z ^ 15 := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [← key, hLBcard]
    rw [hP₁V, Subgroup.card_map_of_injective (EAut0 K).subtype_injective, h15, hKcard]
  have hP₁VU : P₁V ≤ posU0 K := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hP₁U hx)
  have hT : ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (P₁V : Set (W K ≃ₗ[K] W K)) := by
    intro t ht
    have htE : t ∈ EAut0 K := hT0E ht
    exact mem_normalizer_map_subtype (hnorm ⟨t, htE⟩ (hstabT ⟨t, htE⟩ ht))
  have hU : ∀ u ∈ posU0 K, u ∈ Subgroup.normalizer (P₁V : Set (W K ≃ₗ[K] W K)) := by
    intro u hu
    have huE : u ∈ EAut0 K := posU0_le_EAut0 hu
    have hu'' : (⟨u, huE⟩ : ↥(EAut0 K)) ∈ U'' := Subgroup.mem_subgroupOf.2 hu
    exact mem_normalizer_map_subtype (hnorm ⟨u, huE⟩ (hstabU _ hu''))
  have hM2 := eq_rootRad0_or_rootRadν_of_torus hq hP₁VU (isElemAbelian_of_sq _ hP₁Vsq)
    hP₁Vcard hT hU
  have hP₁eq : ∀ R : Subgroup (W K ≃ₗ[K] W K), P₁V = R → P₁ = R.subgroupOf (EAut0 K) := by
    intro R hR
    ext x
    rw [Subgroup.mem_subgroupOf, ← hR, hP₁V]
    exact (Subgroup.mem_map_iff_mem (EAut0 K).subtype_injective).symm
  rcases hM2 with h | h
  · exact ⟨θ₁, hθ₁s, hθ₁k, hP₁eq _ h⟩
  · obtain ⟨gr, hgr⟩ := exists_graphAut_EAut0 (K := K)
    refine ⟨gr.toMonoidHom.comp θ₁, gr.surjective.comp hθ₁s, fun s => ?_, ?_⟩
    · rw [← hθ₁k s]
      show gr (θ₁ s) = 1 ↔ _
      exact map_eq_one_iff _ gr.injective
    · rw [← Subgroup.map_map]
      show P₁.map gr.toMonoidHom = _
      rw [hP₁eq _ h, hgr]

end Base

end CFSG.RankThree.GF2n.Smith81.S81Z
