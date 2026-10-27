module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherE6
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace InnerDiagE6

section Diag

variable (τ : Tag) {K : Type}
  [Field K]

theorem largeEvenDiagMap_mul_xOp (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) (c : K) :
    LargeEvenDiagMap τ.cartan K a * LargeEvenXOp τ.cartan K i c =
      LargeEvenXOp τ.cartan K i ((a i : K) * c) * LargeEvenDiagMap τ.cartan K a := by
  have key : ∀ S : (Fin τ.rank → ℤ) → Prop, S = IsRoot τ →
      TableB.markDiag S K a * MarkChev.xOp τ.cartan S K i c =
        MarkChev.xOp τ.cartan S K i ((a i : K) * c) * TableB.markDiag S K a := by
    rintro S rfl
    rw [TableB.TwE6.markDiag_isRoot, ← xOp_eq_markChev, ← xOp_eq_markChev]
    exact rootDiag_mul_xOp a i c
  rw [TableB.largeEvenDiagMap_eq_markDiag, largeEvenXOp_eq, largeEvenXOp_eq]
  exact key _ (largeEvenIsRoot_eq_isRoot τ)

theorem largeEvenDiagMap_mul_yOp (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) (c : K) :
    LargeEvenDiagMap τ.cartan K a * LargeEvenYOp τ.cartan K i c =
      LargeEvenYOp τ.cartan K i (((a i)⁻¹ : Kˣ) * c) * LargeEvenDiagMap τ.cartan K a := by
  have key : ∀ S : (Fin τ.rank → ℤ) → Prop, S = IsRoot τ →
      TableB.markDiag S K a * MarkChev.yOp τ.cartan S K i c =
        MarkChev.yOp τ.cartan S K i (((a i)⁻¹ : Kˣ) * c) * TableB.markDiag S K a := by
    rintro S rfl
    rw [TableB.TwE6.markDiag_isRoot, ← yOp_eq_markChev, ← yOp_eq_markChev]
    exact rootDiag_mul_yOp a i c
  rw [TableB.largeEvenDiagMap_eq_markDiag, largeEvenYOp_eq, largeEvenYOp_eq]
  exact key _ (largeEvenIsRoot_eq_isRoot τ)

theorem coe_diagHom_inv (a : Fin τ.rank → Kˣ) :
    (((TableB.diagHom τ.cartan K a)⁻¹ : LargeEvenChevGL τ.cartan K) :
      Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenDiagMap τ.cartan K a⁻¹ := by
  rw [← map_inv]
  rfl

theorem diagHom_conj_xOp (a : Fin τ.rank → Kˣ) {g : LargeEvenChevGL τ.cartan K}
    {i : Fin τ.rank} {c : K}
    (hg : (g : Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenXOp τ.cartan K i c) :
    ((TableB.diagHom τ.cartan K a * g * (TableB.diagHom τ.cartan K a)⁻¹ :
      LargeEvenChevGL τ.cartan K) : Module.End K (LargeEvenChevModule τ.cartan K)) =
      LargeEvenXOp τ.cartan K i ((a i : K) * c) := by
  rw [Units.val_mul, Units.val_mul, hg, coe_diagHom_inv, TableB.coe_diagHom,
    largeEvenDiagMap_mul_xOp, mul_assoc, ← TableB.largeEvenDiagMap_mul, mul_inv_cancel,
    TableB.largeEvenDiagMap_one, mul_one]

theorem diagHom_conj_yOp (a : Fin τ.rank → Kˣ) {g : LargeEvenChevGL τ.cartan K}
    {i : Fin τ.rank} {c : K}
    (hg : (g : Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenYOp τ.cartan K i c) :
    ((TableB.diagHom τ.cartan K a * g * (TableB.diagHom τ.cartan K a)⁻¹ :
      LargeEvenChevGL τ.cartan K) : Module.End K (LargeEvenChevModule τ.cartan K)) =
      LargeEvenYOp τ.cartan K i (((a i)⁻¹ : Kˣ) * c) := by
  rw [Units.val_mul, Units.val_mul, hg, coe_diagHom_inv, TableB.coe_diagHom,
    largeEvenDiagMap_mul_yOp, mul_assoc, ← TableB.largeEvenDiagMap_mul, mul_inv_cancel,
    TableB.largeEvenDiagMap_one, mul_one]

theorem diagHom_conj_mem (a : Fin τ.rank → Kˣ) {h : LargeEvenChevGL τ.cartan K}
    (hh : h ∈ LargeEvenChevGroup τ.cartan K) :
    TableB.diagHom τ.cartan K a * h * (TableB.diagHom τ.cartan K a)⁻¹ ∈
      LargeEvenChevGroup τ.cartan K := by
  have hle : LargeEvenChevGroup τ.cartan K ≤ (LargeEvenChevGroup τ.cartan K).comap
      (MulAut.conj (TableB.diagHom τ.cartan K a)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      exact Subgroup.subset_closure ⟨i, (a i : K) * c, Or.inl (diagHom_conj_xOp τ a hg)⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      exact Subgroup.subset_closure
        ⟨i, (((a i)⁻¹ : Kˣ) : K) * c, Or.inr (diagHom_conj_yOp τ a hg)⟩
  exact hle hh

theorem diagHom_inv_conj_mem (a : Fin τ.rank → Kˣ) {h : LargeEvenChevGL τ.cartan K}
    (hh : h ∈ LargeEvenChevGroup τ.cartan K) :
    (TableB.diagHom τ.cartan K a)⁻¹ * h * TableB.diagHom τ.cartan K a ∈
      LargeEvenChevGroup τ.cartan K := by
  have h1 := diagHom_conj_mem τ a⁻¹ hh
  rwa [map_inv, inv_inv] at h1

end Diag

section Transport

variable (τ : Tag) {K : Type}
  [Field K]

theorem exists_chevEquiv_of_eq (S : (Fin τ.rank → ℤ) → Prop) (hS : S = IsRoot τ) :
    ∃ T : ↥(adjointGroup τ K) ≃* ↥(MarkChev.chevGroup τ.cartan S K),
      (∀ (i : Fin τ.rank) (c : K),
        ((T (CFSG.LieType.Chevalley.xElement i c) : MarkChev.GLS S K) :
          Module.End K (MarkChev.Space S K)) = MarkChev.xOp τ.cartan S K i c) ∧
      (∀ (i : Fin τ.rank) (c : K),
        ((T (CFSG.LieType.Chevalley.yElement i c) : MarkChev.GLS S K) :
          Module.End K (MarkChev.Space S K)) = MarkChev.yOp τ.cartan S K i c) := by
  subst hS
  refine ⟨MulEquiv.subgroupCongr (adjointGroup_eq_markChev τ K), fun i c => ?_, fun i c => ?_⟩
  · rw [← xOp_eq_markChev]
    exact coe_xUnit i c
  · rw [← yOp_eq_markChev]
    exact coe_yUnit i c

theorem exists_largeEvenChevEquiv :
    ∃ T : ↥(adjointGroup τ K) ≃* ↥(LargeEvenChevGroup τ.cartan K),
      (∀ (i : Fin τ.rank) (c : K),
        ((T (CFSG.LieType.Chevalley.xElement i c) : LargeEvenChevGL τ.cartan K) :
          Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenXOp τ.cartan K i c) ∧
      (∀ (i : Fin τ.rank) (c : K),
        ((T (CFSG.LieType.Chevalley.yElement i c) : LargeEvenChevGL τ.cartan K) :
          Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenYOp τ.cartan K i c) := by
  obtain ⟨T, hx, hy⟩ := exists_chevEquiv_of_eq τ (K := K) _ (largeEvenIsRoot_eq_isRoot τ)
  refine ⟨T.trans (MulEquiv.subgroupCongr (largeEvenChevGroup_eq τ.cartan K).symm),
    fun i c => ?_, fun i c => ?_⟩
  · rw [largeEvenXOp_eq]
    exact hx i c
  · rw [largeEvenYOp_eq]
    exact hy i c

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ Subgroup.center X := (InnerDiagSU.mem_center_iff_of_mulEquiv e).mp hy
  rw [h, Subgroup.mem_bot] at hx
  rw [hx, map_one]
  exact Subgroup.one_mem _

end Transport

section DiagAut

variable {K : Type} [Field K]

theorem exists_diagAut {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {H : Subgroup (LargeEvenChevGL A K)}
    (hZ : Subgroup.center ↥H = ⊥) (a : Fin r → Kˣ)
    (h1 : ∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H)
    (h2 : ∀ h ∈ H, (TableB.diagHom A K a)⁻¹ * h * TableB.diagHom A K a ∈ H) :
    ∃ φ ∈ LargeEvenChevDiagImage A K H, ∀ h : ↥H,
      φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H ⟨_, h1 h h.2⟩ := by
  set d := TableB.diagHom A K a
  let α : ↥H ≃* ↥H :=
    { toFun := fun h => ⟨d * h * d⁻¹, h1 h h.2⟩
      invFun := fun h => ⟨d⁻¹ * h * d, h2 h h.2⟩
      left_inv := fun h => Subtype.ext (by
        show d⁻¹ * (d * (h : LargeEvenChevGL A K) * d⁻¹) * d = h
        group)
      right_inv := fun h => Subtype.ext (by
        show d * (d⁻¹ * (h : LargeEvenChevGL A K) * d) * d⁻¹ = h
        group)
      map_mul' := fun h h' => Subtype.ext (by
        show d * ((h : LargeEvenChevGL A K) * h') * d⁻¹ = d * h * d⁻¹ * (d * h' * d⁻¹)
        group) }
  let φ : MulAut (LargeEvenCenterQuot H) :=
    (centerQuotEquivOfBot hZ).trans (α.trans (centerQuotEquivOfBot hZ).symm)
  have hφ : ∀ h : ↥H, φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H ⟨_, h1 h h.2⟩ := by
    intro h
    show (centerQuotEquivOfBot hZ).symm (α (centerQuotEquivOfBot hZ (LargeEvenCenterMk H h))) = _
    rw [centerQuotEquivOfBot_mk, centerQuotEquivOfBot_symm]
    rfl
  exact ⟨φ, mem_chevDiagImage_of_isConjOn ⟨h1, fun h _ => hφ h⟩ h2, hφ⟩

end DiagAut

section Marking

variable {K : Type} [Field K] [Finite K]

theorem exists_isogeny_largeEven :
    ∃ Φ : ↥(e6Data_valid.minGroup K) →* ↥(LargeEvenChevGroup (Tag.cartan .E6) K),
      Function.Surjective Φ ∧ Φ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) ∧
      Subgroup.center ↥(LargeEvenChevGroup (Tag.cartan .E6) K) = ⊥ ∧
      (∀ (i : Fin (Tag.rank .E6)) (c : K),
        ((Φ (e6Data_valid.xm K (Pi.single i 1) c) : LargeEvenChevGL (Tag.cartan .E6) K) :
          Module.End K (LargeEvenChevModule (Tag.cartan .E6) K)) =
            LargeEvenXOp (Tag.cartan .E6) K i c) ∧
      (∀ (i : Fin (Tag.rank .E6)) (c : K),
        ((Φ (e6Data_valid.xm K (-Pi.single i 1) c) : LargeEvenChevGL (Tag.cartan .E6) K) :
          Module.End K (LargeEvenChevModule (Tag.cartan .E6) K)) =
            LargeEvenYOp (Tag.cartan .E6) K i c) := by
  obtain ⟨T, hTx, hTy⟩ := exists_largeEvenChevEquiv (τ := .E6) (K := K)
  refine ⟨T.toMonoidHom.comp (e6Isogeny K), T.surjective.comp (e6Isogeny_surjective K),
    fun u hu => ?_, center_eq_bot_of_mulEquiv T CFSG.LieType.Chevalley.center_adjointGroup_eq_bot,
    fun i c => ?_, fun i c => ?_⟩
  · have h1 : e6Isogeny K u = 1 := T.injective (by
      rw [map_one]
      exact hu)
    exact ker_e6IsogenyT_le_center K h1
  · show ((T (e6Isogeny K (e6Data_valid.xm K (Pi.single i 1) c)) :
      LargeEvenChevGL (Tag.cartan .E6) K) :
        Module.End K (LargeEvenChevModule (Tag.cartan .E6) K)) = _
    rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]
    exact hTx i c
  · show ((T (e6Isogeny K (e6Data_valid.xm K (-Pi.single i 1) c)) :
      LargeEvenChevGL (Tag.cartan .E6) K) :
        Module.End K (LargeEvenChevModule (Tag.cartan .E6) K)) = _
    rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
    exact hTy i c

variable [CharP K 2]

theorem largeEvenMarking_E6 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup K) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K))
    [hsimple : IsSimpleGroup (↥ψ.range ⧸ Subgroup.center ↥ψ.range)] :
    LargeEvenMarking ↥ψ.range (fun _ _ _ I _ θ => ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (e6Datum K) ψ c →
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) := by
  have hperfU : commutator ↥(e6Data_valid.minGroup K) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LieType.CurtisTits.isPerfect_e6 K)
  obtain ⟨Φ, hΦs, hΦk, hZ, hΦx, hΦy⟩ := exists_isogeny_largeEven (K := K)
  let C := LargeEvenChevGroup (Tag.cartan .E6) K
  let q₁ : ↥(e6Data_valid.minGroup K) →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    (QuotientGroup.mk' _).comp ψ.rangeRestrict
  let q₂ : ↥(e6Data_valid.minGroup K) →* LargeEvenCenterQuot C :=
    (LargeEvenCenterMk C).comp Φ
  have hq₁ : Function.Surjective q₁ :=
    (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective
  have hq₂ : Function.Surjective q₂ := (QuotientGroup.mk'_surjective _).comp hΦs
  have hk₁ : q₁.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (ψ.rangeRestrict u) : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hperfU ψ hker, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  have hk₂ : q₂.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (Φ u) : LargeEvenCenterQuot C) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot]
    refine ⟨fun h => hΦk h, fun hu => ?_⟩
    have hc : Φ u ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨v, rfl⟩ := hΦs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu v]
    rwa [hZ, Subgroup.mem_bot] at hc
  let θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* LargeEvenCenterQuot C :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂))
  have hθ : ∀ u, θ (q₁ u) = q₂ u := fun u => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
        (u : ↥(e6Data_valid.minGroup K) ⧸ q₁.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hcomm : commutator ↥ψ.range = ⊤ := by
    have h1 := congrArg (Subgroup.map ψ.rangeRestrict) hperfU
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.rangeRestrict_surjective] at h1
    rw [commutator_def]
    exact h1
  have hnab : ∃ a b : ↥ψ.range ⧸ Subgroup.center ↥ψ.range, a * b ≠ b * a :=
    exists_mul_ne_mul_centerQuot_of_perfect hcomm IsSimpleGroup.toNontrivial
  have key : ∀ c ∈ Subgroup.normalizer (ψ.range : Set G), GGPsiInnerDiag (e6Datum K) ψ c →
      ∃ φ ∈ LargeEvenChevIDImage (Tag.cartan .E6) K C,
        LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
    intro c hcN hc
    obtain ⟨g, hg, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker hc
    obtain ⟨φa, hφaD, hφa⟩ := exists_diagAut hZ a (fun _ hh => diagHom_conj_mem .E6 a hh)
      (fun _ hh => diagHom_inv_conj_mem .E6 a hh)
    have hcg : c * g ∈ Subgroup.normalizer (ψ.range : Set G) :=
      Subgroup.mul_mem _ hcN (Subgroup.le_normalizer hg)
    have hmem : ∀ l : ↥ψ.range, (c * g)⁻¹ * (l : G) * (c * g) ∈ ψ.range := fun l => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcg) l).mp l.2
      rwa [inv_inv] at this
    let β : ↥ψ.range →* ↥ψ.range :=
      { toFun := fun l => ⟨(c * g)⁻¹ * (l : G) * (c * g), hmem l⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    let F₁ : ↥(e6Data_valid.minGroup K) →* LargeEvenCenterQuot C :=
      θ.toMonoidHom.comp ((QuotientGroup.mk' _).comp (β.comp ψ.rangeRestrict))
    let F₂ : ↥(e6Data_valid.minGroup K) →* LargeEvenCenterQuot C := φa.toMonoidHom.comp q₂
    have hF : F₁ = F₂ := by
      refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid K) ?_
      rintro _ ⟨i, t, rfl | rfl⟩
      · have e1 : β (ψ.rangeRestrict (e6Data_valid.xm K (Pi.single i 1) t)) =
            ψ.rangeRestrict (e6Data_valid.xm K (Pi.single i 1) ((a i : K) * t)) :=
          Subtype.ext ((ha i t).1)
        show θ (QuotientGroup.mk (β (ψ.rangeRestrict _))) = φa (q₂ _)
        rw [e1]
        change θ (q₁ _) = φa (q₂ _)
        rw [hθ]
        show LargeEvenCenterMk C (Φ _) = φa (LargeEvenCenterMk C (Φ _))
        rw [hφa]
        congr 1
        apply Subtype.ext
        apply Units.ext
        rw [hΦx]
        exact (diagHom_conj_xOp .E6 a (hΦx i t)).symm
      · have e1 : β (ψ.rangeRestrict (e6Data_valid.xm K (-Pi.single i 1) t)) =
            ψ.rangeRestrict (e6Data_valid.xm K (-Pi.single i 1) ((((a i)⁻¹ : Kˣ) : K) * t)) :=
          Subtype.ext ((ha i t).2)
        show θ (QuotientGroup.mk (β (ψ.rangeRestrict _))) = φa (q₂ _)
        rw [e1]
        change θ (q₁ _) = φa (q₂ _)
        rw [hθ]
        show LargeEvenCenterMk C (Φ _) = φa (LargeEvenCenterMk C (Φ _))
        rw [hφa]
        congr 1
        apply Subtype.ext
        apply Units.ext
        rw [hΦy]
        exact (diagHom_conj_yOp .E6 a (hΦy i t)).symm
    refine ⟨MulAut.conj (θ (QuotientGroup.mk (⟨g, hg⟩ : ↥ψ.range))) * φa,
      Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subgroup.subset_closure (Or.inr hφaD)), fun l l' hl => ?_⟩
    obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
    have hl' : l' = ⟨g, hg⟩ * β (ψ.rangeRestrict u) * (⟨g, hg⟩ : ↥ψ.range)⁻¹ := by
      apply Subtype.ext
      rw [hl]
      show c⁻¹ * ψ u * c = g * ((c * g)⁻¹ * ψ u * (c * g)) * g⁻¹
      group
    have h2 : θ (QuotientGroup.mk (β (ψ.rangeRestrict u))) = φa (q₂ u) :=
      DFunLike.congr_fun hF u
    have h3 : θ (QuotientGroup.mk (ψ.rangeRestrict u)) = q₂ u := hθ u
    rw [hl', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, h2, MulAut.mul_apply, MulAut.conj_apply, h3]
  have hraw : LargeEvenRecipeChevalley (Tag.cartan .E6) (2 ^ f) false fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R,
          ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
            GGPsiInnerDiag (e6Datum K) ψ c →
              ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ :=
    ⟨K, inferInstance, inferInstance, hK, θ.symm.isSimpleGroup, nonabelian_of_mulEquiv θ hnab, θ,
      key⟩
  exact ⟨hcomm, ⟨.E6, 0, f⟩, ⟨hf, rfl⟩, hraw⟩

end Marking

end InnerDiagE6

section Genuine

theorem ggInnerDiagMarkingAt_E6 : GGInnerDiagMarkingAt .E6 := by
  intro G _ _ n f ψ G₀ hpres
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, hmodel⟩ := hpres
  subst hrange
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hmodel
  have hf : 1 ≤ f := hadm.2.1
  exact InnerDiagE6.largeEvenMarking_E6 (K := GaloisField 2 f) (GaloisField.card 2 f (by omega))
    hf ψ hker (hsimple := hs)

end Genuine

end CFSG.StandardType
