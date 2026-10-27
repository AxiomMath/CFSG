module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley

namespace InnerDiagTwE6

section Transport

variable {K : Type} [Field K]

theorem exists_twistedTransport_of_eq (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) (hS : S = IsRoot TwistTag.E6.tag) :
    ∃ (e : Module.End K (RootModule TwistTag.E6.tag K) ≃* Module.End K (MarkChev.Space S K))
      (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
        ↥(MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)),
      (∀ g, ((T g : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) ∧
      (∀ b : Fin TwistTag.E6.tag.rank → Kˣ, e (rootDiag b) = TableB.markDiag S K b) := by
  subst hS
  exact ⟨MulEquiv.refl _, MulEquiv.subgroupCongr (twistedH_eq_commutator K .E6 n σ hσ).symm,
    fun _ => rfl, fun b => (TableB.TwE6.markDiag_isRoot b).symm⟩

theorem exists_twistedTransport (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
        Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
      (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
        ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)),
      (∀ g, ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) ∧
      (∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
        e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b) := by
  obtain ⟨e, T, hT, he⟩ := exists_twistedTransport_of_eq n σ hσ _
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
  refine ⟨e, T.trans (MulEquiv.subgroupCongr (largeEvenTwistedH_eq _ K _ n).symm),
    fun g => hT g, fun b => ?_⟩
  rw [he, TableB.largeEvenDiagMap_eq_markDiag]


theorem markDiagUnit_conj_mem_twistedH_of_eq (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) (hS : S = IsRoot TwistTag.E6.tag)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) {h : MarkChev.GLS S K}
    (hh : h ∈ MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n) :
    InndiagE6.markDiagUnit S K b * h * (InndiagE6.markDiagUnit S K b)⁻¹ ∈
      MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n := by
  subst hS
  rw [twistedH_eq_commutator K .E6 n σ hσ] at hh ⊢
  rw [InndiagE6.markDiagUnit_isRoot]
  have hmap := map_conj_eq_of_mem_normalizer
    (rootDiagUnit_mem_normalizer_twistedFixedGroup (t := TwistTag.E6) (σ := σ) hb)
  have hmap' : (⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆).map
      (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom =
        ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ := by
    rw [Subgroup.map_commutator, hmap]
  rw [← hmap']
  exact ⟨h, hh, rfl⟩

theorem diagHom_conj_mem_twistedH (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i))
    {h : LargeEvenChevGL TwistTag.E6.tag.cartan K}
    (hh : h ∈ LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n) :
    TableB.diagHom TwistTag.E6.tag.cartan K b * h * (TableB.diagHom TwistTag.E6.tag.cartan K b)⁻¹ ∈
      LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n := by
  rw [largeEvenTwistedH_eq] at hh ⊢
  rw [InndiagE6.diagHom_eq_markDiagUnit]
  exact markDiagUnit_conj_mem_twistedH_of_eq n σ hσ _ (largeEvenIsRoot_eq_isRoot _) hb hh

theorem diagHom_inv_conj_mem_twistedH (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i))
    {h : LargeEvenChevGL TwistTag.E6.tag.cartan K}
    (hh : h ∈ LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n) :
    (TableB.diagHom TwistTag.E6.tag.cartan K b)⁻¹ * h * TableB.diagHom TwistTag.E6.tag.cartan K b ∈
      LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n := by
  have hb' : ∀ i, b⁻¹ (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b⁻¹ i) := fun i => by
    simp only [Pi.inv_apply, hb, map_inv]
  have h1 := diagHom_conj_mem_twistedH n σ hσ hb' hh
  rwa [map_inv, inv_inv] at h1

end Transport

section Input

@[expose] def TwE6DiagInput (f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] (ψ : twistedE6Group 2 f →* G),
    ψ.ker ≤ Subgroup.center (twistedE6Group 2 f) → ∀ c : G,
      GGPsiInnerDiag (twistedE6Datum 2 f) ψ c →
        ∃ g ∈ ψ.range, ∃ b : Fin TwistTag.E6.tag.rank → (GaloisField 2 (2 * f))ˣ,
          (∀ i, b (TwistTag.E6.perm i) = Units.map (frobQ 2 f).toMonoidHom (b i)) ∧
          ∀ (j : Fin (Tag.rank .F4)) (γ : Fin (Tag.rank .F4) → ℤ),
            (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
            ∀ z ∈ (twistedE6Datum 2 f).rootGroup γ, ∃ z' : twistedE6Group 2 f,
              (c * g)⁻¹ * ψ z * (c * g) = ψ z' ∧
                ((e6IsogenyT (GaloisField 2 (2 * f)) (z' : e6Data_valid.minGroup _) :
                    ↥(adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
                    ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
                  rootDiagUnit TwistTag.E6.tag b *
                    ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup _) :
                      ↥(adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
                      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
                    (rootDiagUnit TwistTag.E6.tag b)⁻¹

end Input


section Abstract

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
  {H : Subgroup (LargeEvenChevGL A K)} {U : Type} [Group U] {G : Type} [Group G]

theorem exists_centerQuot_equiv (hperfU : commutator U = ⊤) (ψ : U →* G)
    (hker : ψ.ker ≤ Subgroup.center U) (Φ : U →* ↥H) (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker ≤ Subgroup.center U) (hZ : Subgroup.center ↥H = ⊥) :
    ∃ θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* LargeEvenCenterQuot H,
      ∀ u, θ (QuotientGroup.mk (ψ.rangeRestrict u)) = LargeEvenCenterMk H (Φ u) := by
  let q₁ : U →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    (QuotientGroup.mk' _).comp ψ.rangeRestrict
  let q₂ : U →* LargeEvenCenterQuot H := (LargeEvenCenterMk H).comp Φ
  have hq₁ : Function.Surjective q₁ :=
    (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective
  have hq₂ : Function.Surjective q₂ := (QuotientGroup.mk'_surjective _).comp hΦs
  have hk₁ : q₁.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hperfU ψ hker, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  have hk₂ : q₂.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot]
    refine ⟨fun h => hΦk h, fun hu => ?_⟩
    have hc : Φ u ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨v, rfl⟩ := hΦs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu v]
    rwa [hZ, Subgroup.mem_bot] at hc
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂)), fun u => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
      (u : U ⧸ q₁.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  change ((QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂))) (q₁ u) = q₂ u
  simp only [MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem exists_induces_of_diag (hZ : Subgroup.center ↥H = ⊥) (ψ : U →* G)
    (θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* LargeEvenCenterQuot H) (Φ : U →* ↥H)
    (hθ : ∀ u, θ (QuotientGroup.mk (ψ.rangeRestrict u)) = LargeEvenCenterMk H (Φ u))
    {X : Set U} (hX : Subgroup.closure X = ⊤) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) {g : G} (hg : g ∈ ψ.range)
    (a : Fin r → Kˣ) (h1 : ∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H)
    (h2 : ∀ h ∈ H, (TableB.diagHom A K a)⁻¹ * h * TableB.diagHom A K a ∈ H)
    (hact : ∀ z ∈ X, ∃ z' : U, (c * g)⁻¹ * ψ z * (c * g) = ψ z' ∧
      (Φ z' : LargeEvenChevGL A K) =
        TableB.diagHom A K a * (Φ z : LargeEvenChevGL A K) * (TableB.diagHom A K a)⁻¹) :
    ∃ φ ∈ LargeEvenChevIDImage A K H,
      LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
  obtain ⟨φa, hφaD, hφa⟩ := InnerDiagE6.exists_diagAut hZ a h1 h2
  have hcg : c * g ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.le_normalizer hg)
  have hmem : ∀ l : ↥ψ.range, (c * g)⁻¹ * (l : G) * (c * g) ∈ ψ.range := fun l => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcg) l).mp l.2
    rwa [inv_inv] at this
  let β : ↥ψ.range →* ↥ψ.range :=
    { toFun := fun l => ⟨(c * g)⁻¹ * (l : G) * (c * g), hmem l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  let F₁ : U →* LargeEvenCenterQuot H :=
    θ.toMonoidHom.comp ((QuotientGroup.mk' _).comp (β.comp ψ.rangeRestrict))
  let F₂ : U →* LargeEvenCenterQuot H := φa.toMonoidHom.comp ((LargeEvenCenterMk H).comp Φ)
  have hF : F₁ = F₂ := by
    refine MonoidHom.eq_of_eqOn_dense hX fun z hz => ?_
    obtain ⟨z', hz'1, hz'2⟩ := hact z hz
    have e1 : β (ψ.rangeRestrict z) = ψ.rangeRestrict z' := Subtype.ext hz'1
    change θ (QuotientGroup.mk (β (ψ.rangeRestrict z))) = φa (LargeEvenCenterMk H (Φ z))
    rw [e1, hθ, hφa]
    congr 1
    exact Subtype.ext hz'2
  refine ⟨MulAut.conj (θ (QuotientGroup.mk (⟨g, hg⟩ : ↥ψ.range))) * φa,
    Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
      (Subgroup.subset_closure (Or.inr hφaD)), fun l l' hl => ?_⟩
  obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
  have hl' : l' = ⟨g, hg⟩ * β (ψ.rangeRestrict u) * (⟨g, hg⟩ : ↥ψ.range)⁻¹ := by
    apply Subtype.ext
    rw [hl]
    show c⁻¹ * ψ u * c = g * ((c * g)⁻¹ * ψ u * (c * g)) * g⁻¹
    group
  have h3 : θ (QuotientGroup.mk (β (ψ.rangeRestrict u))) = φa (LargeEvenCenterMk H (Φ u)) :=
    DFunLike.congr_fun hF u
  rw [hl', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv, h3, MulAut.mul_apply, MulAut.conj_apply, hθ u]

end Abstract

section Generation


theorem closure_fundamental_eq_top {k : Type*} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    Subgroup.closure {z : fixedGroup k θ | ∃ (j : Fin (Tag.rank .F4)) (γ : Fin (Tag.rank .F4) → ℤ),
      (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) ∧ z ∈ (twistedDatum k θ).rootGroup γ} = ⊤ :=
  InnerDiagSU.eq_top_of_rankOne_le
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)) _ fun j =>
      sup_le (fun _ hz => Subgroup.subset_closure ⟨j, _, Or.inl rfl, hz⟩)
        (fun _ hz => Subgroup.subset_closure ⟨j, _, Or.inr rfl, hz⟩)

end Generation

section Marking

theorem exists_isogeny_twisted {f : ℕ} (hf : 1 ≤ f) :
    ∃ (e : Module.End (GaloisField 2 (2 * f)) (RootModule TwistTag.E6.tag (GaloisField 2 (2 * f)))
        ≃* Module.End (GaloisField 2 (2 * f))
          (LargeEvenChevModule TwistTag.E6.tag.cartan (GaloisField 2 (2 * f))))
      (Φ : twistedE6Group 2 f →*
        ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan (GaloisField 2 (2 * f)) TwistTag.E6.perm f)),
      Function.Surjective Φ ∧ Φ.ker ≤ Subgroup.center (twistedE6Group 2 f) ∧
      Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan (GaloisField 2 (2 * f))
        TwistTag.E6.perm f) = ⊥ ∧
      (∀ z : twistedE6Group 2 f,
        ((Φ z : LargeEvenChevGL TwistTag.E6.tag.cartan (GaloisField 2 (2 * f))) :
          Module.End (GaloisField 2 (2 * f))
            (LargeEvenChevModule TwistTag.E6.tag.cartan (GaloisField 2 (2 * f)))) =
          e ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup _) :
            ↥(adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
              ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ∧
      (∀ b : Fin TwistTag.E6.tag.rank → (GaloisField 2 (2 * f))ˣ,
        e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan (GaloisField 2 (2 * f)) b) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := frobQ_apply 2 f
  obtain ⟨e, T, hT, he⟩ := exists_twistedTransport (K := GaloisField 2 (2 * f)) f (frobQ 2 f) hσ
  refine ⟨e, T.toMonoidHom.comp (twistedE6Isogeny 2 f hf),
    T.surjective.comp (twistedE6Isogeny_surjective 2 f hf), fun z hz => ?_, ?_,
    fun z => hT _, he⟩
  · have h1 : twistedE6Isogeny 2 f hf z = 1 := T.injective (by
      rw [map_one]
      exact hz)
    have h2 : e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup _) = 1 := by
      apply Subtype.ext
      have h3 := congrArg Subtype.val h1
      rw [coe_twistedE6Isogeny] at h3
      exact h3
    have h4 := ker_e6IsogenyT_le_center (GaloisField 2 (2 * f)) h2
    rw [Subgroup.mem_center_iff] at h4 ⊢
    intro y
    exact Subtype.ext (h4 y)
  · obtain ⟨hZ, -⟩ := (InndiagE6.twistedNFOn_isRoot_E6 hf (GaloisField 2 (2 * f)) hK).of_eq
      (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
    rw [largeEvenTwistedH_eq]
    exact hZ

theorem largeEvenMarking_twistedE6 {f : ℕ} (hf : 1 ≤ f) (hD : TwE6DiagInput f) {G : Type}
    [Group G] (ψ : twistedE6Group 2 f →* G)
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    [hsimple : IsSimpleGroup (↥ψ.range ⧸ Subgroup.center ↥ψ.range)] :
    LargeEvenMarking ↥ψ.range (fun _ _ _ I _ θ => ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (twistedE6Datum 2 f) ψ c →
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c := frobQ_frobQ 2 f hf
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := frobQ_apply 2 f
  have hperfU : commutator (twistedE6Group 2 f) = ⊤ :=
    Group.isPerfect_def.mp (fixedGroup_isPerfect_of_four_le_card (frobQ 2 f) hθ
      (four_le_card_galoisField 2 f hf))
  obtain ⟨e, Φ, hΦs, hΦk, hZ, hΦe, he⟩ := exists_isogeny_twisted hf
  obtain ⟨θ, hθ'⟩ := exists_centerQuot_equiv hperfU ψ hker Φ hΦs hΦk hZ
  have hX := closure_fundamental_eq_top (frobQ 2 f) hθ
  have hcomm : commutator ↥ψ.range = ⊤ := by
    have h1 := congrArg (Subgroup.map ψ.rangeRestrict) hperfU
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.rangeRestrict_surjective] at h1
    rw [commutator_def]
    exact h1
  have hnab : ∃ a b : ↥ψ.range ⧸ Subgroup.center ↥ψ.range, a * b ≠ b * a :=
    exists_mul_ne_mul_centerQuot_of_perfect hcomm IsSimpleGroup.toNontrivial
  have key : ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (twistedE6Datum 2 f) ψ c →
        ∃ φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan (GaloisField 2 (2 * f))
            (LargeEvenTwistedH TwistTag.E6.tag.cartan (GaloisField 2 (2 * f)) TwistTag.E6.perm f),
          LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
    intro c hcN hc
    obtain ⟨g, hg, b, hb, hact⟩ := hD G ψ hker c hc
    refine exists_induces_of_diag hZ ψ θ Φ hθ' hX hcN hg b
      (fun _ hh => diagHom_conj_mem_twistedH f (frobQ 2 f) hσ hb hh)
      (fun _ hh => diagHom_inv_conj_mem_twistedH f (frobQ 2 f) hσ hb hh) ?_
    rintro z ⟨j, γ, hγ, hz⟩
    obtain ⟨z', hz'1, hz'2⟩ := hact j γ hγ z hz
    refine ⟨z', hz'1, ?_⟩
    apply Units.ext
    have hd1 : e ((rootDiagUnit TwistTag.E6.tag b : ModGL TwistTag.E6.tag _) :
        Module.End _ (RootModule TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
        LargeEvenDiagMap TwistTag.E6.tag.cartan (GaloisField 2 (2 * f)) b := he b
    have hd2 : e (((rootDiagUnit TwistTag.E6.tag b)⁻¹ : ModGL TwistTag.E6.tag _) :
        Module.End _ (RootModule TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
        LargeEvenDiagMap TwistTag.E6.tag.cartan (GaloisField 2 (2 * f)) b⁻¹ := he b⁻¹
    rw [hΦe, hz'2, Units.val_mul, Units.val_mul, map_mul, map_mul, ← hΦe z, Units.val_mul,
      Units.val_mul, TableB.coe_diagHom, InnerDiagE6.coe_diagHom_inv, hd1, hd2]
  have hraw : LargeEvenRecipeTwisted TwistTag.E6.tag.cartan TwistTag.E6.perm 2 f fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R,
          ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
            GGPsiInnerDiag (twistedE6Datum 2 f) ψ c →
              ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ :=
    ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, hK, θ.symm.isSimpleGroup,
      nonabelian_of_mulEquiv θ hnab, θ, key⟩
  exact ⟨hcomm, ⟨.twE6, 0, f⟩, ⟨hf, rfl⟩, hraw⟩

end Marking

end InnerDiagTwE6

section Genuine

theorem ggInnerDiagMarkingAt_twistedE6_of_diag
    (hD : ∀ f, 1 ≤ f → InnerDiagTwE6.TwE6DiagInput f) : GGInnerDiagMarkingAt .twistedE6 := by
  intro G _ _ n f ψ G₀ hpres
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, hmodel⟩ := hpres
  subst hrange
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hmodel
  have hf : 1 ≤ f := hadm.2.1
  exact InnerDiagTwE6.largeEvenMarking_twistedE6 hf (hD f hf) ψ hker (hsimple := hs)

end Genuine

end CFSG.StandardType
