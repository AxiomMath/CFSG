module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentFam
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Part22
public import CFSG.Quasithin.EmptyFaithful.SBd18Out
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.Quasithin CFSG.Open

theorem exists_ambient_involution {S : Type} [Group S] [Finite S] (w : MulAut S) (hw : w * w = 1) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (ι : S →* G) (t : G), Function.Injective ι ∧
      ι.range.Normal ∧ t * t = 1 ∧ ∀ s, t * ι s * t⁻¹ = ι (w s) := by
  classical
  let H : Subgroup (MulAut S) := Subgroup.zpowers w
  have : Finite (MulAut S) := inferInstance
  have hfin : Finite (S ⋊[H.subtype] H) :=
    Finite.of_equiv (S × H) (SemidirectProduct.equivProd (N := S) (G := H) (φ := H.subtype)).symm
  refine ⟨S ⋊[H.subtype] H, inferInstance, hfin, SemidirectProduct.inl,
    SemidirectProduct.inr ⟨w, Subgroup.mem_zpowers w⟩, SemidirectProduct.inl_injective, ?_, ?_, ?_⟩
  · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact MonoidHom.normal_ker _
  · rw [← map_mul]
    have : (⟨w, Subgroup.mem_zpowers w⟩ : H) * ⟨w, Subgroup.mem_zpowers w⟩ = 1 := Subtype.ext hw
    rw [this, map_one]
  · intro s
    have h := SemidirectProduct.inl_aut (φ := H.subtype) (⟨w, Subgroup.mem_zpowers w⟩ : H) s
    rw [← map_inv]
    exact h.symm

theorem center_eq_bot_of_equiv {S X : Type*} [Group S] [Group X] [IsSimpleGroup S] (e : X ≃* S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  have h := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := S) hnab).2
  have h2 := Subgroup.map_center_eq e
  rw [h] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h2

noncomputable def quotCenterEquiv {S X : Type*} [Group S] [Group X] [IsSimpleGroup S] (e : X ≃* S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : (X ⧸ Subgroup.center X) ≃* S :=
  ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_equiv e hnab)).trans
    QuotientGroup.quotientBot).trans e

theorem range_inf_centralizer_eq_map {S G : Type} [Group S] [Group G] {w : MulAut S} {ι : S →* G}
    {t : G} (hι : Function.Injective ι) (hconj : ∀ s, t * ι s * t⁻¹ = ι (w s)) :
    ι.range ⊓ Subgroup.centralizer ({t} : Set G) = (SBd18.fixedSub w).map ι := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, hc⟩
    refine ⟨s, SBd18.mem_fixedSub.mpr (hι ?_), rfl⟩
    have h1 : ι s * t = t * ι s := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [← hconj s, ← h1]
    group
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hconj s
    rw [SBd18.mem_fixedSub.mp hs] at h1
    calc ι s * t = (t * ι s * t⁻¹) * t := by rw [h1]
      _ = t * ι s := by group

theorem isComponentIn_map_of_injective {S G : Type} [Group S] [Group G] (ι : S →* G)
    (hι : Function.Injective ι) {F K : Subgroup S} (h : IsComponentIn K F) {Y : Subgroup G}
    (hY : F.map ι = Y) : IsComponentIn (K.map ι) Y := by
  have hKF : K ≤ F := h.1
  refine ⟨hY ▸ Subgroup.map_mono hKF, ?_⟩
  let e : ↥F ≃* ↥Y := (F.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hY)
  have hcomp : CFSG.IsComponent ((K.subgroupOf F).map e.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e h.2
  have heq : (K.map ι).subgroupOf Y = (K.subgroupOf F).map e.toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hk, hky⟩ := (Subgroup.mem_subgroupOf.mp hy)
      have hyF : (y : G) ∈ F.map ι := hY ▸ y.2
      obtain ⟨f, hf, hfy⟩ := hyF
      refine ⟨⟨f, hf⟩, ?_, Subtype.ext ?_⟩
      · change f ∈ K
        have : k = f := hι (hky.trans hfy.symm)
        exact this ▸ hk
      · exact hfy
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [heq]
  exact hcomp

theorem ident_simple_of_row {P : ∀ {G : Type} [Group G], Subgroup G → Prop} (hrow : TabIdentFor P)
    {S : Type} [Group S] [Finite S] [hS : IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (w : MulAut S) (hw2 : w * w = 1) (hw1 : w ≠ 1) {K : Subgroup S}
    (hK : IsSubnormal K (SBd18.fixedSub w)) (hKq : CFSG.IsQuasisimple ↥K) (hL32 : IsPSL 3 2 1 ↥K)
    (hP : ∀ (G : Type) [Group G] (X : Subgroup G), Nonempty (↥X ≃* S) → P X) :
    IsPSL 3 2 2 S ∨ IsSporadic .J2 S := by
  classical
  obtain ⟨G, _, _, ι, t, hι, hnorm, ht2, hconj⟩ := exists_ambient_involution w hw2
  let X : Subgroup G := ι.range
  let eX : ↥X ≃* S := (MonoidHom.ofInjective hι).symm
  have hXs : IsSimpleGroup ↥X := eX.isSimpleGroup
  have hq := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := S) hnab
  have hXq : CFSG.IsQuasisimple ↥X := CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hq.1
  have htN : t ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
    exact Subgroup.mem_top t
  obtain ⟨s₀, hs₀⟩ : ∃ s, w s ≠ s := by
    by_contra hcon
    push Not at hcon
    exact hw1 (MulEquiv.ext hcon)
  have hnc : ¬ ∀ k ∈ X, t * k = k * t := by
    intro h
    have h1 := h (ι s₀) ⟨s₀, rfl⟩
    have h2 := hconj s₀
    have : ι (w s₀) = ι s₀ := by
      rw [← h2, h1]
      group
    exact hs₀ (hι this)
  have hcomm : ⁅X, Subgroup.zpowers t⁆ = X := commutator_zpowers_eq_of_simple hXs htN hnc
  have hY : ι.range ⊓ Subgroup.centralizer ({t} : Set G) = (SBd18.fixedSub w).map ι :=
    range_inf_centralizer_eq_map hι hconj
  have hcompK : IsComponentIn (K.map ι) (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have h0 : IsComponentIn K (SBd18.fixedSub w) :=
      ⟨A3.subnormal_le hK, CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (A3.subnormal_le hK)).symm hKq,
        subgroupOf_isSubnormal_of_open hK⟩
    exact isComponentIn_map_of_injective ι hι h0 hY.symm
  have hL32' : IsL32 (K.map ι) :=
    IsPSL.of_mulEquiv (K.equivMapOfInjective ι hι) hL32
  have hset : IdentSetting X (K.map ι) t :=
    ⟨hXq, htN, ht2, hcomm, hcompK, Or.inr (Or.inl hL32')⟩
  have hconcl := hrow G X (K.map ι) t hset (hP G X ⟨eX⟩)
  let eZ : (↥X ⧸ Subgroup.center ↥X) ≃* S := quotCenterEquiv eX hnab
  rcases hconcl.2.2.2.1 hL32' with hA | hB
  · exact Or.inl (IsPSL.of_mulEquiv eZ hA.2.1)
  · exact Or.inr (hB.2.1.elim fun f => ⟨eZ.symm.trans f⟩)

end CFSG.Quasithin.SBd19F
