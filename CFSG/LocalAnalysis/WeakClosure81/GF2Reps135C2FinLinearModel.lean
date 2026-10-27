module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def mulAutLinear {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    (a : MulAut W) : Additive W →ₗ[ZMod 2] Additive W :=
  AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive a).toAddMonoidHom

theorem mulAutLinear_apply {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    (a : MulAut W) (x : Additive W) :
    mulAutLinear a x = Additive.ofMul (a (Additive.toMul x)) :=
  rfl

theorem mulAutLinear_mul {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    (a b : MulAut W) : mulAutLinear (a * b) = mulAutLinear a * mulAutLinear b :=
  LinearMap.ext fun _ => rfl

theorem mulAutLinear_one {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)] :
    mulAutLinear (1 : MulAut W) = 1 :=
  LinearMap.ext fun _ => rfl

@[expose] def mulAutLinearHom {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)] :
    MulAut W →* Additive W →ₗ[ZMod 2] Additive W where
  toFun := mulAutLinear
  map_one' := mulAutLinear_one
  map_mul' := mulAutLinear_mul

@[expose] def mulAutLinearEquiv {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    (a : MulAut W) : Additive W ≃ₗ[ZMod 2] Additive W :=
  LinearEquiv.ofLinear (mulAutLinear a) (mulAutLinear a⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← mulAutLinear_mul, mul_inv_cancel, mulAutLinear_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← mulAutLinear_mul, inv_mul_cancel, mulAutLinear_one]; rfl)

@[expose] def specialLinearRep {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {G : Type} [Group G] (σ : G ≃* ↥L) :
    Representation (ZMod 2) G (Additive W) :=
  mulAutLinearHom.comp (L.subtype.comp σ.toMonoidHom)

theorem specialLinearRep_apply {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {G : Type} [Group G] (σ : G ≃* ↥L) (x : G) :
    specialLinearRep σ x = mulAutLinear ((σ x : ↥L) : MulAut W) :=
  rfl

private theorem w183_commutator_mul_center {G : Type} [Group G] {z z' a b : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) :
    ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have hz1 : ⁅z, b * z'⁆ = 1 :=
    Commute.commutator_eq ((Subgroup.mem_center_iff.mp hz (b * z')).symm)
  have hz2 : ⁅a, z'⁆ = 1 :=
    Commute.commutator_eq (Subgroup.mem_center_iff.mp hz' a)
  rw [commutatorElement_mul_left_eq_conj_mul, hz1,
    commutatorElement_mul_right_eq_mul_conj, hz2]
  group

theorem exists_mulEquiv_specialLinear_of_lieModel
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {n : ℕ} (hn : 3 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin n) K ≃* ↥L) := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun a b h => MulEquiv.ext (congr_fun h))
  have hsc : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 1 :=
    hlie.statedClassicalModel_of_ne_zero (by omega)
  simp only [StatedClassicalModel] at hsc
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hsc
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card, hKcard, pow_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime hK2
  have hunits : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, hK2]
  haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp hunits.le
  have hScal : StatedScalars (Fin n) K = ⊥ := by
    rw [StatedScalars, MonoidHom.range_eq_bot_iff]
    ext x
    rw [Subsingleton.elim x 1, map_one]
    rfl
  have hScalSub : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [hScal, Subgroup.bot_subgroupOf]
  have ebot : StatedProj (StatedSL n K) ≃* ↥(StatedSL n K) :=
    (QuotientGroup.quotientMulEquivOfEq hScalSub).trans QuotientGroup.quotientBot
  let φ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(StatedSL n K) := e.trans ebot
  let π : ↥L →* ↥(StatedSL n K) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    exact ⟨x, rfl⟩
  have hker : π.ker = Subgroup.center ↥L := by
    change (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))).ker = _
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
      φ.toMonoidHom φ.injective, QuotientGroup.ker_mk']
  have hcen : π.ker ≤ Subgroup.center ↥L := le_of_eq hker
  have hodd : Odd (Nat.card π.ker) := hker ▸ w135_odd_card_center hctx
  obtain ⟨s, hs, -⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated (n := n)
      (by omega) hπ hcen hodd
  have hcomm : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ s.range := by
    rw [Subgroup.commutator_le]
    intro l₁ _ l₂ _
    have hz₁ : (s (π l₁))⁻¹ * l₁ ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs]
      simp
    have hz₂ : (s (π l₂))⁻¹ * l₂ ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs]
      simp
    have h1 : l₁ = s (π l₁) * ((s (π l₁))⁻¹ * l₁) := by group
    have h2 : l₂ = s (π l₂) * ((s (π l₂))⁻¹ * l₂) := by group
    rw [h1, h2, w183_commutator_mul_center hz₁ hz₂]
    exact MonoidHom.mem_range.mpr ⟨⁅π l₁, π l₂⁆, map_commutatorElement s (π l₁) (π l₂)⟩
  have hsurj : Function.Surjective s := by
    refine MonoidHom.range_eq_top.mp (le_antisymm le_top ?_)
    rw [← hctx.2.2.2.2.1.1.commutator_eq_top]
    exact hcomm
  let s' : Matrix.SpecialLinearGroup (Fin n) K →* ↥L :=
    s.comp (specialLinearGroupEquivStatedSL n K).toMonoidHom
  have hinj : Function.Injective s' := by
    intro a b hab
    have h1 : π (s' a) = (specialLinearGroupEquivStatedSL n K) a := by
      simp only [s', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs]
    have h2 : π (s' b) = (specialLinearGroupEquivStatedSL n K) b := by
      simp only [s', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs]
    exact (specialLinearGroupEquivStatedSL n K).injective
      (by rw [← h1, ← h2, hab])
  have hsurj' : Function.Surjective s' :=
    hsurj.comp (specialLinearGroupEquivStatedSL n K).surjective
  exact ⟨K, hKfield, Fintype.ofFinite K, hK2, ⟨MulEquiv.ofBijective s' ⟨hinj, hsurj'⟩⟩⟩

theorem center_specialLinear_eq_bot_of_card_two {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {n : ℕ} :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hunits : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, hK]
  haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp hunits.le
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin n) K) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim A 1
  · have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, Fintype.card_fin, zero_pow (Fin.pos_iff_nonempty.mpr hn).ne'] at hr
      exact zero_ne_one hr
    have hr1 : r = 1 := by
      have h := Subsingleton.elim (Units.mk0 r hr0) (1 : Kˣ)
      exact congrArg (fun u : Kˣ => (u : K)) h
    apply Subtype.ext
    rw [← hrA, hr1]
    simp

theorem isIrreducible_specialLinearRep {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    {G : Type} [Group G] (σ : G ≃* ↥L) : (specialLinearRep σ).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
  have hIrr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · haveI : Nontrivial W := by
      have hne : (⊤ : Subgroup W) ≠ ⊥ := (ne_of_lt hIrr.1).symm
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      exact ⟨(a : W), 1, fun h => ha (Subtype.ext h)⟩
    infer_instance
  · intro U hU
    let U' : Subgroup W :=
      { carrier := {w | Additive.ofMul w ∈ U}
        one_mem' := U.zero_mem
        mul_mem' := fun ha hb => U.add_mem ha hb
        inv_mem' := fun ha => U.neg_mem ha }
    have hst : StableUnder L U' := by
      intro x hx u hu
      have h := hU (σ.symm ⟨x, hx⟩) (Additive.ofMul u) hu
      rw [specialLinearRep_apply, σ.apply_symm_apply, mulAutLinear_apply] at h
      exact h
    rcases hIrr.2.2.2 U' hst bot_le le_top with h0 | h1
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : Additive.toMul v ∈ U' := by
        change Additive.ofMul (Additive.toMul v) ∈ U
        rwa [ofMul_toMul]
      rw [h0, Subgroup.mem_bot] at hv'
      rw [← ofMul_toMul v, hv']
      rfl
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hv' : Additive.toMul v ∈ U' := by rw [h1]; trivial
      change Additive.ofMul (Additive.toMul v) ∈ U at hv'
      rwa [ofMul_toMul] at hv'

theorem specialLinearRep_ne_one {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {G : Type} [Group G]
    (σ : G ≃* ↥L) : ∃ x : G, specialLinearRep σ x ≠ 1 := by
  obtain ⟨x, y, hxy⟩ := hctx.2.2.2.2.1.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hne : x' * y' ≠ y' * x' := by
    intro h
    exact hxy (by
      have := congrArg (QuotientGroup.mk' (Subgroup.center ↥L)) h
      simpa using this)
  have hx'1 : x' ≠ 1 := by
    intro h
    exact hne (by rw [h, one_mul, mul_one])
  refine ⟨σ.symm x', ?_⟩
  intro h
  apply hx'1
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have h1 := congrArg (fun (f : Additive W →ₗ[ZMod 2] Additive W) => f (Additive.ofMul w)) h
  simp only [specialLinearRep_apply, σ.apply_symm_apply, mulAutLinear_apply,
    Module.End.one_apply] at h1
  apply Additive.ofMul.injective
  simpa using h1

private theorem w183_mem_fixV_zpowers {W : Type} [CommGroup W] (a : MulAut W) (u : W) :
    u ∈ fixV (Subgroup.zpowers a) ↔ a u = u := by
  rw [show u ∈ fixV (Subgroup.zpowers a) ↔
      Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut W) u by
    simp only [mem_fixV, SetLike.le_def, MulAction.mem_stabilizer_iff, MulAut.smul_def]]
  rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]

theorem mQuot_fixV_zpowers_eq_finrank_range_sub_one {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] (a : MulAut W) :
    E3.mQuot ⊤ (fixV (Subgroup.zpowers a)) =
      Module.finrank (ZMod 2) (LinearMap.range (mulAutLinear a - 1)) := by
  haveI : Fintype (Additive W) := Fintype.ofFinite _
  haveI : Fintype ↥(LinearMap.range (mulAutLinear a - 1)) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : Additive W →ₗ[ZMod 2] ↥(LinearMap.range (mulAutLinear a - 1)) :=
    (mulAutLinear a - 1).codRestrict (LinearMap.range (mulAutLinear a - 1))
      (fun x => ⟨x, rfl⟩)
  have coe_ψ : ∀ x, ((ψ x : ↥(LinearMap.range (mulAutLinear a - 1))) : Additive W) =
      (mulAutLinear a - 1) x := fun x => rfl
  let φ : W →* Multiplicative ↥(LinearMap.range (mulAutLinear a - 1)) :=
    (ψ : Additive W →+ _).toMultiplicativeRight
  have hker : φ.ker = fixV (Subgroup.zpowers a) := by
    ext w
    rw [MonoidHom.mem_ker, w183_mem_fixV_zpowers]
    constructor
    · intro h
      have h1 : ψ (Additive.ofMul w) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa [φ, AddMonoidHom.coe_toMultiplicativeRight] using this
      have h2 : (mulAutLinear a - 1) (Additive.ofMul w) = 0 := by
        have h1' := congrArg (fun z : ↥(LinearMap.range (mulAutLinear a - 1)) =>
          (z : Additive W)) h1
        simpa [coe_ψ] using h1'
      rw [LinearMap.sub_apply, Module.End.one_apply] at h2
      have h3 : mulAutLinear a (Additive.ofMul w) = Additive.ofMul w := sub_eq_zero.mp h2
      rw [mulAutLinear_apply] at h3
      simpa using Additive.ofMul.injective h3
    · intro h
      apply Multiplicative.ext
      change ψ (Additive.ofMul w) = 0
      apply Subtype.ext
      rw [coe_ψ]
      have h3 : mulAutLinear a (Additive.ofMul w) = Additive.ofMul w := by
        rw [mulAutLinear_apply, show Additive.toMul (Additive.ofMul w) = w from rfl, h]
      rw [LinearMap.sub_apply, Module.End.one_apply, h3, sub_self]
      rfl
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := y.toAdd.2
    refine ⟨Additive.toMul x, ?_⟩
    apply Multiplicative.ext
    change ψ (Additive.ofMul (Additive.toMul x)) = y.toAdd
    apply Subtype.ext
    rw [coe_ψ, ofMul_toMul]
    exact hx
  have hcard : Nat.card (W ⧸ fixV (Subgroup.zpowers a)) =
      Nat.card ↥(LinearMap.range (mulAutLinear a - 1)) := by
    rw [← hker]
    calc Nat.card (W ⧸ φ.ker)
        = Nat.card (Multiplicative ↥(LinearMap.range (mulAutLinear a - 1))) :=
          Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
      _ = Nat.card ↥(LinearMap.range (mulAutLinear a - 1)) :=
          Nat.card_congr Multiplicative.toAdd
  rw [E3.mQuot, Subgroup.relIndex_top_right, Subgroup.index_eq_card, hcard]
  have hfin : Nat.card ↥(LinearMap.range (mulAutLinear a - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (mulAutLinear a - 1)) := by
    have h1 : Fintype.card ↥(LinearMap.range (mulAutLinear a - 1)) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (mulAutLinear a - 1)) := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
    rwa [Nat.card_eq_fintype_card]
  rw [hfin, padicValNat.prime_pow]

@[expose] def slToY {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {G : Type} [Group G]
    (hLY : L ≤ Y) (σ : G ≃* ↥L) : G →* ↥Y :=
  (Subgroup.inclusion hLY).comp σ.toMonoidHom

theorem slToY_injective {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {G : Type}
    [Group G] (hLY : L ≤ Y) (σ : G ≃* ↥L) : Function.Injective (slToY hLY σ) :=
  (Subgroup.inclusion_injective hLY).comp σ.injective

theorem coe_slToY {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {G : Type} [Group G]
    (hLY : L ≤ Y) (σ : G ≃* ↥L) (x : G) :
    ((slToY hLY σ x : ↥Y) : MulAut W) = ((σ x : ↥L) : MulAut W) :=
  rfl

theorem slToY_mem_normalizer {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) {G : Type} [Group G] (σ : G ≃* ↥L) {g : MulAut W} (hg : g ∈ Y) :
    (⟨g, hg⟩ : ↥Y) ∈ Subgroup.normalizer ((slToY hctx.2.2.1 σ).range : Set ↥Y) := by
  have hrange : (slToY hctx.2.2.1 σ).range = L.subgroupOf Y := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, rfl⟩
      exact (σ y).2
    · intro hx
      refine ⟨σ.symm ⟨(x : MulAut W), hx⟩, ?_⟩
      apply Subtype.ext
      simp only [coe_slToY, σ.apply_symm_apply]
  have htop : Subgroup.normalizer ((slToY hctx.2.2.1 σ).range : Set ↥Y) = ⊤ := by
    rw [hrange]
    exact Subgroup.normalizer_eq_top_iff.mpr (w135_normal_of_ctx hctx)
  rw [htop]
  trivial

theorem eq_one_of_mem_centralizer_slToY {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {G : Type} [Group G]
    (σ : G ≃* ↥L) (hG : Subgroup.center G = ⊥) {c : ↥Y}
    (hc : c ∈ Subgroup.centralizer ((slToY hctx.2.2.1 σ).range : Set ↥Y)) : c = 1 := by
  have hmem : (c : MulAut W) ∈ Zc L := by
    refine w135c2_mem_Zc_of_comm hctx c.2 (fun l hl => ?_)
    have h1 : ⁅c, slToY hctx.2.2.1 σ (σ.symm ⟨l, hl⟩)⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hc)
        _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have h2 : ⁅(c : MulAut W), l⁆ = 1 := by
      have h := congrArg (Y.subtype) h1
      rw [map_commutatorElement] at h
      simpa [coe_slToY, σ.apply_symm_apply] using h
    rw [h2]
    exact (Zc L).one_mem
  obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.mp hmem
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have h := Subgroup.map_center_eq (σ : G ≃* ↥L)
    rw [hG, Subgroup.map_bot] at h
    exact h.symm
  have hz1 : z = 1 := by
    rw [hcenter, Subgroup.mem_bot] at hz
    exact hz
  apply Subtype.ext
  change (c : MulAut W) = 1
  rw [← hzc, hz1]
  rfl

end CFSG.LocalAnalysis.WeakClosure81
