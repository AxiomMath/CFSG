module

public import CFSG.RankThree.GF2n.Smith81.S81ZCore
public import CFSG.RankThree.GF2n.Smith81.S81ZGSide
public import CFSG.RankThree.GF2n.Smith81.S81VGroupSide

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z.Tr
  CFSG.RankThree.GF2n.Smith81.S81V Module


@[expose] def E7M2 (K : Type) [Field K] [Finite K] : Prop :=
  ∀ A : Subgroup (Gp K), (∀ a ∈ A, a ^ 2 = 1) → Nat.card K ^ 27 ≤ Nat.card A →
    ∃ h : Gp K, A = (UA K a7).map (MulAut.conj h).toMonoidHom

section Fix

variable {K : Type} [Field K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]

theorem mem_fix7_conj (A₁ : Gp K →* (X ≃ₗ[K] X)) (h : Gp K) {v : X} :
    v ∈ fix7 (A₁.comp (MulAut.conj h).toMonoidHom) ↔ ∀ u ∈ UA K a7, A₁ (h * u * h⁻¹) v = v :=
  Iff.rfl

theorem apply_mem_fix7_conj (A₁ : Gp K →* (X ≃ₗ[K] X)) (h h' : Gp K) {v : X}
    (hv : v ∈ fix7 (A₁.comp (MulAut.conj h).toMonoidHom)) :
    A₁ (h' * h⁻¹) v ∈ fix7 (A₁.comp (MulAut.conj h').toMonoidHom) := by
  rw [mem_fix7_conj] at hv ⊢
  intro u hu
  have h1 := hv u hu
  have e : h' * u * h'⁻¹ * (h' * h⁻¹) = h' * h⁻¹ * (h * u * h⁻¹) := by group
  rw [← LinearEquiv.mul_apply, ← map_mul, e, map_mul, LinearEquiv.mul_apply, h1]

end Fix

section Pt

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_span_eq_img (hg : GlobalModelData M Q Z γ M₀) {A : Subgroup G}
    (hAZ : IsZConjugate Z A) (hAQ : A ≤ Q) (hAne : A ≠ Z) :
    ∃ e : M₀.E, e ≠ 0 ∧ ∀ v : M₀.E, (∃ x ∈ A, M₀.π x = v) ↔ v ∈ Submodule.span K {e} := by
  obtain ⟨g, rfl⟩ := hAZ
  obtain ⟨e, he0, he⟩ := hg.line g hAne hAQ
  refine ⟨e, he0, fun v => ?_⟩
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs⟩ := (he (M₀.π x)).1 ⟨x, hx, hAQ hx, rfl⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨x, hx, -, hxs⟩ := (he (s • e)).2 ⟨s, rfl⟩
    exact ⟨x, hx, hxs⟩

theorem point_fix_E5 (hM2 : E7M2 K) (h34 : Stroth34Statement) (hctx : Ctx M Q Z B)
    (hw : Width Q Z 28) (hg : GlobalModelData M Q Z γ M₀)
    (θ : Lgen M (LB M Q B) →* Gp K) (hθk : ∀ s : Lgen M (LB M Q B), θ s = 1 ↔ (s : G) ∈ Q)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (A₁ : Gp K →* (M₀.E ≃ₗ[K] M₀.E)) (hA₁ : ∀ s, A₁ (θ s) = T s)
    {A : Subgroup G} (hctxA : Ctx M Q Z A) (hno : NoA2 Q Z (LB M Q A)) (hgen : GenByB M Q A)
    (hLBle : LB M Q A ≤ Lgen M (LB M Q B)) :
    ∃ h : Gp K,
      (∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A → ∃ u ∈ UA K a7, θ s = h * u * h⁻¹) ∧
      (∀ u ∈ UA K a7, ∃ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A ∧ θ s = h * u * h⁻¹) ∧
      ∀ v : M₀.E, v ∈ fix7 (A₁.comp (MulAut.conj h).toMonoidHom) ↔ ∃ x ∈ A, M₀.π x = v := by
  classical
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hM : M ≤ Subgroup.normalizer (Q : Set G) := hctx.hyp.Q_normal.2
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  obtain ⟨-, hCQt, hLBcard, -⟩ := stroth_3_5 h34 hctxA hw (by norm_num) hno hgen
  have hKcard : Nat.card K = Nat.card Z := hg.card
  set Lb : Subgroup (Gp K) := ((LB M Q A).subgroupOf (Lgen M (LB M Q B))).map θ with hLb
  have hLbsq : ∀ u ∈ Lb, u ^ 2 = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_pow, hθk, Subgroup.coe_pow]
    exact hctxA.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hs)
  have hLbcard : Nat.card Lb = Nat.card K ^ 27 := by
    have key : Nat.card (LB M Q A) = Nat.card Q * Nat.card Lb :=
      card_eq_card_mul_card_map_of_ker (S := LB M Q A) θ hθk hQLg le_sup_left hLBle
    have hpos : 0 < Nat.card Q := Nat.card_pos
    rw [hKcard]
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← key, hLBcard]
  obtain ⟨h, hh⟩ := hM2 Lb hLbsq hLbcard.ge
  have hfwd : ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A → ∃ u ∈ UA K a7, θ s = h * u * h⁻¹ := by
    intro s hs
    have hmem : θ s ∈ Lb := Subgroup.mem_map.2 ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [hh] at hmem
    obtain ⟨u, hu, hθ⟩ := Subgroup.mem_map.1 hmem
    exact ⟨u, hu, hθ.symm⟩
  have hbwd : ∀ u ∈ UA K a7, ∃ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A ∧ θ s = h * u * h⁻¹ := by
    intro u hu
    have hmem : h * u * h⁻¹ ∈ (UA K a7).map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [← hh] at hmem
    obtain ⟨s, hs, hθ⟩ := Subgroup.mem_map.1 hmem
    exact ⟨s, Subgroup.mem_subgroupOf.1 hs, hθ⟩
  refine ⟨h, hfwd, hbwd, fun v => ?_⟩
  rw [← fixed_iff_mem_img (Lg := Lgen M (LB M Q B)) hctxA hctxA.LB_le_M hM hZQ rfl hCQt hctxA.le T
    hTe hLBle v, mem_fix7_conj]
  constructor
  · intro hv s hs
    obtain ⟨u, hu, hθ⟩ := hfwd s hs
    rw [← hA₁ s, hθ]
    exact hv u hu
  · intro hv u hu
    obtain ⟨s, hs, hθ⟩ := hbwd u hu
    rw [← hθ, hA₁ s]
    exact hv s hs

theorem uniform_of_core_E5 (hM2 : E7M2 K) (hChar : E5StabChar K) (h34 : Stroth34Statement)
    (hctx : Ctx M Q Z B) (hw : Width Q Z 28) (hg : GlobalModelData M Q Z γ M₀)
    (hTac : ∀ A : Subgroup G, Ctx M Q Z A → NoA2 Q Z (LB M Q A) ∧ GenByB M Q A)
    (hLBle : ∀ A : Subgroup G, Ctx M Q Z A → LB M Q A ≤ Lgen M (LB M Q B))
    (θ : Lgen M (LB M Q B) →* Gp K) (hθs : Function.Surjective θ)
    (hθk : ∀ s : Lgen M (LB M Q B), θ s = 1 ↔ (s : G) ∈ Q) :
    ∃ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
      φ.range = EAut K ∧ (∀ s : Lgen M (LB M Q B), φ s = 1 ↔ (s : G) ∈ Q) ∧
      ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
        ψ (M₀.π ((s : G) * x * (s : G)⁻¹)) = φ s (ψ (M₀.π x)) := by
  classical
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hq : 4 ≤ Nat.card K := by
    rw [hKcard]
    exact hctx.hyp.q4
  have hX : Module.finrank K M₀.E = 56 := finrank_E_eq_of_card hg hZQ (m := 56) hw
  obtain ⟨T, hTe, hTker, hTiso⟩ := exists_T_Lgen_isom hctx hg
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Gp K →* (M₀.E ≃ₗ[K] M₀.E), ∀ s : Lgen M (LB M Q B), A₁ (θ s) = T s := by
    have hle : θ.ker ≤ T.ker := fun s hs => by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact (hTker s).2 ((hθk s).1 hs)
    exact ⟨θ.liftOfRightInverse (Function.surjInv hθs) (Function.rightInverse_surjInv hθs) ⟨T, hle⟩,
      fun s => θ.liftOfRightInverse_comp_apply _ _ _ s⟩
  obtain ⟨hnoB, hgenB⟩ := hTac B hctx
  obtain ⟨gG, hB1, hB2, hBfix⟩ := point_fix_E5 hM2 h34 hctx hw hg θ hθk T hTe A₁ hA₁ hctx hnoB hgenB
    (le_Lgen _)
  set A'' : Gp K →* (M₀.E ≃ₗ[K] M₀.E) := A₁.comp (MulAut.conj gG).toMonoidHom with hA''
  have hAT : ∀ s : Lgen M (LB M Q B), A'' (gG⁻¹ * θ s * gG) = T s := by
    intro s
    rw [← hA₁ s]
    show A₁ (gG * (gG⁻¹ * θ s * gG) * gG⁻¹) = A₁ (θ s)
    congr 1
    group
  have hAT' : ∀ g : Gp K, ∃ s : Lgen M (LB M Q B), T s = A'' g := by
    intro g
    obtain ⟨s, hs⟩ := hθs (gG * g * gG⁻¹)
    refine ⟨s, ?_⟩
    rw [← hA₁ s, hs]
    rfl
  obtain ⟨e, he0, he⟩ := exists_span_eq_img hg hctx.conj hctx.le hctx.ne
  have hfixB : fix7 A'' = Submodule.span K {e} := by
    ext v
    rw [← he v]
    exact hBfix v
  have hline : Module.finrank K (fix7 A'') = 1 := by
    rw [hfixB]
    exact finrank_span_singleton he0
  have hβA : ∀ g u w, M₀.B (A'' g u) (A'' g w) = M₀.B u w := by
    intro g u w
    obtain ⟨s, hs⟩ := hAT' g
    rw [← hs]
    exact hTiso s u w
  have hspan : ⨆ g : Gp K, (fix7 A'').map (A'' g : M₀.E →ₗ[K] M₀.E) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hle : (⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
        Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G))) ≤
        ⨆ g : Gp K, (fix7 A'').map (A'' g : M₀.E →ₗ[K] M₀.E) := by
      apply iSup_le
      intro A'
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hctxA : Ctx M Q Z A'.1 := ⟨hctx.hyp, A'.2.1, A'.2.2.1, A'.2.2.2⟩
      obtain ⟨hnoA, hgenA⟩ := hTac A'.1 hctxA
      obtain ⟨h, -, -, hfixA⟩ := point_fix_E5 hM2 h34 hctx hw hg θ hθk T hTe A₁ hA₁ hctxA hnoA hgenA
        (hLBle A'.1 hctxA)
      have hπx : M₀.π x ∈ fix7 (A₁.comp (MulAut.conj h).toMonoidHom) := (hfixA _).2 ⟨x, hx, rfl⟩
      have hmem := apply_mem_fix7_conj A₁ h gG hπx
      refine Submodule.mem_iSup_of_mem (gG⁻¹ * h) ?_
      refine ⟨A₁ (gG * h⁻¹) (M₀.π x), hmem, ?_⟩
      show A₁ (gG * (gG⁻¹ * h) * gG⁻¹) (A₁ (gG * h⁻¹) (M₀.π x)) = M₀.π x
      rw [← LinearEquiv.mul_apply, ← map_mul]
      have e : gG * (gG⁻¹ * h) * gG⁻¹ * (gG * h⁻¹) = 1 := by group
      rw [e, map_one]
      rfl
    exact hle (points_span hctx.hyp M₀ v)
  have hV1 : Module.finrank K (V17 A'' M₀.B) ≤ 28 := by
    refine finrank_le_of_V1 h34 hctx hg hw (by norm_num) hnoB hgenB T hTe (V17 A'' M₀.B) ?_ ?_
    · intro b hb w hw'
      have hmem : M₀.π b ∈ fix7 A'' := (hBfix _).2 ⟨b, hb, rfl⟩
      exact ((mem_V17 A'').1 hw').1 _ hmem
    · intro s hs w hw'
      obtain ⟨u, hu, hθ⟩ := hB1 s hs
      have hTs : T s = A'' u := by
        rw [← hA₁ s, hθ]
        rfl
      have h1 := ((mem_V17 A'').1 hw').2 u hu
      rw [hTs]
      exact (hBfix _).1 h1
  obtain ⟨σ, ψ, hψ, -⟩ := core_main_E5 hq hChar hX A'' M₀.B M₀.alt hβA hline hspan hV1
  let φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K) :=
    (ιV K).comp ((twistGp σ).toMonoidHom.comp ((MulAut.conj gG⁻¹).toMonoidHom.comp θ))
  have hφ : ∀ s, φ s = ιV K (twistGp σ (gG⁻¹ * θ s * gG)) := by
    intro s
    show ιV K (twistGp σ (gG⁻¹ * θ s * gG⁻¹⁻¹)) = _
    rw [inv_inv]
  have hφT : ∀ (s : Lgen M (LB M Q B)) (v : M₀.E), ψ (T s v) = φ s (ψ v) := by
    intro s v
    rw [← hAT s, hψ, hφ]
    rfl
  refine ⟨ψ, φ, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      rw [hφ]
      exact ιV_mem_EAut _
    · intro x hx
      obtain ⟨g₀, rfl⟩ := mem_EAut_iff_range.1 hx
      obtain ⟨s, hs⟩ := hθs (gG * (twistGp σ).symm g₀ * gG⁻¹)
      refine ⟨s, ?_⟩
      rw [hφ, hs]
      have e : gG⁻¹ * (gG * (twistGp σ).symm g₀ * gG⁻¹) * gG = (twistGp σ).symm g₀ := by group
      rw [e, MulEquiv.apply_symm_apply]
  · intro s
    have h1 : φ s = 1 ↔ θ s = 1 := by
      show ιV K (twistGp σ (MulAut.conj gG⁻¹ (θ s))) = 1 ↔ _
      rw [map_eq_one_iff _ ιV_injective, map_eq_one_iff _ (twistGp σ).injective,
        map_eq_one_iff _ (MulAut.conj gG⁻¹).injective]
    rw [h1, hθk]
  · intro s x hx
    rw [hTe s x hx, hφT]

end Pt

end CFSG.RankThree.GF2n.Smith81.S81Z
