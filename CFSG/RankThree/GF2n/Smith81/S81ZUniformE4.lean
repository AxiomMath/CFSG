module

public import CFSG.RankThree.GF2n.Smith81.S81ZE4Base
public import CFSG.RankThree.GF2n.Smith81.S81QTwist

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.S81V Module


section V1

variable {K : Type} [Field K] {X : Type} [AddCommGroup X] [Module K X] {Γ : Type*} [Group Γ]

@[expose] def V1P [Finite K] [CharP K 2] (A : Γ →* (X ≃ₗ[K] X)) (R : Subgroup Γ)
    (β : X →ₗ[K] X →ₗ[K] K) : Submodule K X where
  carrier := {w | (∀ v ∈ fixP A R, β v w = 0) ∧ ∀ u ∈ R, A u w - w ∈ fixP A R}
  add_mem' {w w'} hw hw' := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_add, hw.1 v hv, hw'.1 v hv, add_zero]
    · have : A u (w + w') - (w + w') = (A u w - w) + (A u w' - w') := by rw [map_add]; abel
      rw [this]
      exact (fixP A R).add_mem (hw.2 u hu) (hw'.2 u hu)
  zero_mem' := ⟨fun v _ => by simp, fun u _ => by simp⟩
  smul_mem' c w hw := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_smul, hw.1 v hv, smul_zero]
    · have : A u (c • w) - c • w = c • (A u w - w) := by rw [map_smul, smul_sub]
      rw [this]
      exact (fixP A R).smul_mem c (hw.2 u hu)

theorem mem_V1P [Finite K] [CharP K 2] {A : Γ →* (X ≃ₗ[K] X)} {R : Subgroup Γ}
    {β : X →ₗ[K] X →ₗ[K] K} {w : X} :
    w ∈ V1P A R β ↔ (∀ v ∈ fixP A R, β v w = 0) ∧ ∀ u ∈ R, A u w - w ∈ fixP A R := Iff.rfl

end V1

@[expose] def rad0 (K : Type) [Field K] : Subgroup ↥(EAut0 K) := (rootRad0 K).subgroupOf (EAut0 K)

@[expose] def E4CoreStatement (K : Type) [Field K] [Finite K] [CharP K 2] : Prop :=
  4 ≤ Nat.card K → ∀ (X : Type) [AddCommGroup X] [Module K X], finrank K X = 32 →
    ∀ (A : ↥(EAut0 K) →* (X ≃ₗ[K] X)) (β : X →ₗ[K] X →ₗ[K] K), (∀ v, β v v = 0) →
      (∀ g u w, β (A g u) (A g w) = β u w) → finrank K (fixP A (rad0 K)) = 1 →
      ⨆ g : ↥(EAut0 K), (fixP A (rad0 K)).map (A g : X →ₗ[K] X) = ⊤ →
      finrank K (V1P A (rad0 K) β) ≤ 16 →
      ∃ (σ : K ≃+* K) (ψ : X ≃ₗ[K] W K),
        (∀ (g : ↥(EAut0 K)) (v : X), ψ (A g v) = ((eAut0Congr σ g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (ψ v)) ∧
          (fixP A (rad0 K)).map (ψ : X →ₗ[K] W K) = Submodule.span K {p0 K}

section Main

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem uniform_of_core_E4
    (hSame : ∀ C C' : Subgroup G, Ctx M Q Z C → Ctx M Q Z C' → C ⊔ Z = C' ⊔ Z →
      LB M Q C = LB M Q C')
    (h34 : Stroth34Statement) (hctx : Ctx M Q Z B) (hw : Width Q Z 16)
    (hg : GlobalModelData M Q Z γ M₀)
    (hTac : ∀ A : Subgroup G, Ctx M Q Z A → NoA2 Q Z (LB M Q A) ∧ GenByB M Q A)
    (hLBle : ∀ A : Subgroup G, Ctx M Q Z A → LB M Q A ≤ Lgen M (LB M Q B))
    (hUp : IsPGroup 2 (posU0 K)) (hT0E : T0 K ≤ EAut0 K)
    (hTnorm : ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (posU0 K : Set (W K ≃ₗ[K] W K)))
    (hcore : E4CoreStatement K)
    (θ₀ : Lgen M (LB M Q B) →* ↥(EAut0 K)) (hθ₀s : Function.Surjective θ₀)
    (hθ₀k : ∀ s : Lgen M (LB M Q B), θ₀ s = 1 ↔ (s : G) ∈ Q) :
    ∃ (ψ : M₀.E ≃ₗ[K] W K) (φ : Lgen M (LB M Q B) →* (W K ≃ₗ[K] W K)),
      EUniData M Q Z B M₀ ψ φ (EAut0 K) (p0 K) (rootRad0 K) := by
  classical
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hq : 4 ≤ Nat.card K := by
    rw [hKcard]
    exact hctx.hyp.q4
  have hX : Module.finrank K M₀.E = 32 := finrank_E_eq_of_card hg hZQ (m := 32) hw
  haveI : Finite M₀.E := Module.finite_of_finite K
  obtain ⟨hnoB, hgenB⟩ := hTac B hctx
  obtain ⟨θ, hθs, hθk, hθB⟩ := exists_base_E4 hSame h34 hctx hw hg hnoB hgenB hUp hT0E hTnorm θ₀ hθ₀s hθ₀k
  haveI : Finite ↥(EAut0 K) := Finite.of_surjective θ hθs
  obtain ⟨T, hTe, hTker, hTiso⟩ := exists_T_Lgen_isom hctx hg
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ↥(EAut0 K) →* (M₀.E ≃ₗ[K] M₀.E),
      ∀ s : Lgen M (LB M Q B), A₁ (θ s) = T s := by
    have hle : θ.ker ≤ T.ker := fun s hs => by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact (hTker s).2 ((hθk s).1 hs)
    exact ⟨θ.liftOfRightInverse (Function.surjInv hθs) (Function.rightInverse_surjInv hθs)
      ⟨T, hle⟩, fun s => θ.liftOfRightInverse_comp_apply _ _ _ s⟩
  obtain ⟨e, he0, heB, hfixB⟩ :=
    exists_line_fix h34 hctx hw (by norm_num) hg hnoB hgenB T hTe (le_Lgen _)
  have hfix : ∀ v : M₀.E, v ∈ fixP A₁ (rad0 K) ↔ v ∈ Submodule.span K {e} := by
    intro v
    rw [← hfixB v, mem_fixP]
    constructor
    · intro h s hs
      rw [← hA₁ s]
      refine h _ ?_
      rw [rad0, ← hθB]
      exact ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    · intro h r hr
      rw [rad0, ← hθB] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      rw [hA₁ s]
      exact h s (Subgroup.mem_subgroupOf.1 hs)
  have hline : finrank K (fixP A₁ (rad0 K)) = 1 := by
    have : fixP A₁ (rad0 K) = Submodule.span K {e} := Submodule.ext hfix
    rw [this]
    exact finrank_span_singleton he0
  have hβA : ∀ g u w, M₀.B (A₁ g u) (A₁ g w) = M₀.B u w := by
    intro g u w
    obtain ⟨s, rfl⟩ := hθs g
    rw [hA₁ s]
    exact hTiso s u w
  have hspan : ⨆ g : ↥(EAut0 K), (fixP A₁ (rad0 K)).map (A₁ g : M₀.E →ₗ[K] M₀.E) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hle : (⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
        Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G))) ≤
        ⨆ g : ↥(EAut0 K), (fixP A₁ (rad0 K)).map (A₁ g : M₀.E →ₗ[K] M₀.E) := by
      apply iSup_le
      intro A'
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hctxA : Ctx M Q Z A'.1 := ⟨hctx.hyp, A'.2.1, A'.2.2.1, A'.2.2.2⟩
      obtain ⟨s, -, himg⟩ := exists_lift_point hSame h34 hctx hw (by norm_num) hg θ hθs hθk T hTe A₁
        hA₁ hTac hLBle hctxA
      obtain ⟨w, ⟨b, hb, rfl⟩, hw'⟩ := (himg (M₀.π x)).1 ⟨x, hx, rfl⟩
      refine Submodule.mem_iSup_of_mem (θ s) ⟨M₀.π b, ?_, ?_⟩
      · exact (hfix _).2 ((heB _).1 ⟨b, hb, rfl⟩)
      · show A₁ (θ s) (M₀.π b) = M₀.π x
        rw [hA₁ s]
        exact hw'
    exact hle (points_span hctx.hyp M₀ v)
  have hV1 : finrank K (V1P A₁ (rad0 K) M₀.B) ≤ 16 := by
    refine finrank_le_of_V1 h34 hctx hg hw (by norm_num) hnoB hgenB T hTe (V1P A₁ (rad0 K) M₀.B)
      ?_ ?_
    · intro b hb w hw'
      exact ((mem_V1P).1 hw').1 _ ((hfix _).2 ((heB _).1 ⟨b, hb, rfl⟩))
    · intro s hs w hw'
      have hmem : θ s ∈ rad0 K := by
        rw [rad0, ← hθB]
        exact ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
      have h1 := ((mem_V1P).1 hw').2 _ hmem
      rw [hA₁ s] at h1
      exact (heB _).2 ((hfix _).1 h1)
  obtain ⟨σ, ψ, hψ, hψfix⟩ := hcore hq M₀.E hX A₁ M₀.B M₀.alt hβA hline hspan hV1
  let θ' : Lgen M (LB M Q B) →* ↥(EAut0 K) := (eAut0Congr σ).toMonoidHom.comp θ
  let φ : Lgen M (LB M Q B) →* (W K ≃ₗ[K] W K) := (EAut0 K).subtype.comp θ'
  have hθ's : Function.Surjective θ' := (eAut0Congr σ).surjective.comp hθs
  have hθ'k : ∀ s : Lgen M (LB M Q B), θ' s = 1 ↔ (s : G) ∈ Q := fun s => by
    rw [← hθk s]
    show eAut0Congr σ (θ s) = 1 ↔ _
    exact map_eq_one_iff _ (eAut0Congr σ).injective
  have hθ'B : ((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ' = rad0 K := by
    have h1 : ((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ' =
        (((LB M Q B).subgroupOf (Lgen M (LB M Q B))).map θ).map (eAut0Congr σ).toMonoidHom :=
      (Subgroup.map_map _ _ _).symm
    rw [h1, hθB, rad0, map_rootRad0 σ]
  have hφT : ∀ (s : Lgen M (LB M Q B)) (v : M₀.E), ψ (T s v) = φ s (ψ v) := by
    intro s v
    rw [← hA₁ s, hψ]
    rfl
  have hφE : ∀ s, φ s ∈ EAut0 K := fun s => (θ' s).2
  have hφker : ∀ s : Lgen M (LB M Q B), φ s = 1 ↔ (s : G) ∈ Q := by
    intro s
    have h1 : φ s = 1 ↔ θ' s = 1 := by
      show ((θ' s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) = 1 ↔ _
      exact OneMemClass.coe_eq_one
    rw [h1, hθ'k]
  have hψB : ∀ w : W K, (∃ x ∈ B, ψ (M₀.π x) = w) ↔ w ∈ Submodule.span K {p0 K} := by
    intro w
    rw [← hψfix, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨M₀.π x, (hfix _).2 ((heB _).1 ⟨x, hx, rfl⟩), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (heB v).2 ((hfix v).1 hv)
      exact ⟨x, hx, rfl⟩
  have hφB : ∀ u : W K ≃ₗ[K] W K,
      (∃ t : Lgen M (LB M Q B), (t : G) ∈ LB M Q B ∧ φ t = u) ↔ u ∈ rootRad0 K := by
    intro u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : θ' t ∈ rad0 K := by
        rw [← hθ'B]
        exact ⟨t, Subgroup.mem_subgroupOf.2 ht, rfl⟩
      exact h1
    · intro hu
      have hu' : (⟨u, rootRad0_le_EAut0 hu⟩ : ↥(EAut0 K)) ∈ rad0 K := hu
      rw [← hθ'B] at hu'
      obtain ⟨t, ht, hθt⟩ := hu'
      exact ⟨t, Subgroup.mem_subgroupOf.1 ht, congrArg Subtype.val hθt⟩
  refine ⟨ψ, φ, ⟨?_, hφker, Lgen_le_normalizer_Q hctx, ?_, ?_⟩⟩
  ·
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact hφE s
    · intro x hx
      obtain ⟨s, hs⟩ := hθ's ⟨x, hx⟩
      exact ⟨s, congrArg Subtype.val hs⟩
  · intro s x hx
    rw [hTe s x hx, hφT]
  · exact point_of_translate hctx T ψ φ hφker hφT hφE hψB hφB fun A hA =>
      exists_lift_point hSame h34 hctx hw (by norm_num) hg θ hθs hθk T hTe A₁ hA₁ hTac hLBle hA

end Main

end CFSG.RankThree.GF2n.Smith81.S81Z
