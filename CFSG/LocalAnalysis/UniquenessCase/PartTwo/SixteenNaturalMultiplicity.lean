module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeNaturalProduct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallBridge
public import CFSG.LocalAnalysis.SteinbergCEIsotypicMultiplicity
public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.Quasithin.Background.F918D9
public import CFSG.Quasithin.H13.GoldschmidtG52Sec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.GroupTheory.InvariantMinimal
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped TensorProduct Matrix

structure NaturalThreeMultiplicityData
    {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
    (A L : Subgroup (MulAut V)) where
  Q : Type
  [qAdd : AddCommGroup Q]
  [qModule : Module (ZMod 2) Q]
  [qFinite : Finite Q]
  X : Type
  [xAdd : AddCommGroup X]
  [xModule : Module (ZMod 2) X]
  [xFinite : Finite X]
  rhoQ : Representation (ZMod 2) ↥L Q
  theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2))
  coordQ : Q ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)
  coordQ_apply : ∀ l q,
    coordQ (rhoQ l q) =
      (((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ coordQ q)
  dual_model : Explicit.BinaryNaturalSL (Representation.dual rhoQ) 3 (ZMod 2) .dual
  no_fixed_Q : ∀ q : Q, (∀ l : ↥L, rhoQ l q = q) → q = 0
  no_invariant_Q : ∀ psi : Q →ₗ[ZMod 2] ZMod 2,
    (∀ l q, psi (rhoQ l q) = psi q) → psi = 0
  kappaX : Representation (ZMod 2) ↥(s1t3KBar A L) X
  finrank_X : Module.finrank (ZMod 2) X = 3
  irreducible_X : kappaX.IsIrreducible
  kappaZ : Representation (ZMod 2) ↥(s1t3KBar A L) ↥(s16smSubmod (fixV L))
  kappaZ_apply : ∀ k z,
    ((kappaZ k z : ↥(s16smSubmod (fixV L))) : Additive V) =
      s16smRepW (MonoidHom.id ↥(s1t3KBar A L)) k (z : Additive V)
  qW : Additive V →ₗ[ZMod 2] Q ⊗[ZMod 2] X
  qW_surjective : Function.Surjective qW
  ker_qW : LinearMap.ker qW = s16smSubmod (fixV L)
  qW_L : ∀ l w,
    qW (s16smRepW (MonoidHom.id ↥L) l w) =
      TensorProduct.map (rhoQ l) LinearMap.id (qW w)
  qW_K : ∀ k w,
    qW (s16smRepW (MonoidHom.id ↥(s1t3KBar A L)) k w) =
      TensorProduct.map LinearMap.id (kappaX k) (qW w)
  no_invariant_W : ∀ psi : Additive V →ₗ[ZMod 2] ZMod 2,
    (∀ l w, psi (s16smRepW (MonoidHom.id ↥L) l w) = psi w) → psi = 0

section Quotient

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
variable {L : Subgroup (MulAut V)}

@[instance_reducible] private noncomputable def quotFixModule (hV : ∀ v : V, v * v = 1) :
    Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
  MulAutTwo.zmod2Module (V := V ⧸ modFix L (⊤ : Subgroup V)) (fun q => by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, hV v, QuotientGroup.mk_one])

variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]

private noncomputable def quotFixMap :
    Additive V →ₗ[ZMod 2] Additive (V ⧸ modFix L (⊤ : Subgroup V)) :=
  AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (QuotientGroup.mk' (modFix L ⊤)))

private theorem quotFixMap_apply (x : Additive V) :
    quotFixMap (L := L) x = Additive.ofMul (QuotientGroup.mk (Additive.toMul x)) := rfl

private theorem quotFixMap_surjective : Function.Surjective (quotFixMap (L := L)) := by
  intro q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨Additive.ofMul v, rfl⟩

private theorem quotFixMap_eq_zero_iff (x : Additive V) :
    quotFixMap (L := L) x = 0 ↔ x ∈ s16smSubmod (fixV L) := by
  have hmk : quotFixMap (L := L) x = 0 ↔
      (QuotientGroup.mk' (modFix L ⊤)) (Additive.toMul x) = 1 := by
    rw [quotFixMap_apply]
    constructor
    · intro h
      exact congrArg Additive.toMul h
    · intro h
      exact congrArg Additive.ofMul h
  have hker : (QuotientGroup.mk' (modFix L ⊤)) (Additive.toMul x) = 1 ↔
      Additive.toMul x ∈ modFix L ⊤ := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  refine hmk.trans (hker.trans ?_)
  rw [CFSG.Quasithin.SmithD391.modFix_top_eq, mem_s16smSubmod]

end Quotient

section FixedSpace

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}

private noncomputable def kappaZOfThreeNat (h : ThreeNat A L T) :
    Representation (ZMod 2) ↥(s1t3KBar A L) ↥(s16smSubmod (fixV L)) :=
  (s16smRepW (W := V) (H := s1t3KBar A L) (MonoidHom.id ↥(s1t3KBar A L))).subrepresentation
    (s16smSubmod (fixV L)) (by
      intro k z hz
      have hz' : Additive.toMul z ∈ fixV L := hz
      rw [mem_fixV] at hz'
      rw [Submodule.mem_comap]
      show Additive.toMul ((s16smRepW (MonoidHom.id ↥(s1t3KBar A L))) k z) ∈ fixV L
      rw [show Additive.toMul ((s16smRepW (MonoidHom.id ↥(s1t3KBar A L))) k z) =
          (k : MulAut V) (Additive.toMul z) from rfl]
      rw [mem_fixV]
      have hk : ((k : MulAut V)) ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
        (Subgroup.mem_inf.mp k.2).2
      intro l hl
      have hcomm : (l : MulAut V) * (k : MulAut V) = (k : MulAut V) * (l : MulAut V) :=
        (Subgroup.mem_centralizer_iff.mp hk) l hl
      calc (l : MulAut V) ((k : MulAut V) (Additive.toMul z))
          = ((l : MulAut V) * (k : MulAut V)) (Additive.toMul z) := rfl
        _ = ((k : MulAut V) * (l : MulAut V)) (Additive.toMul z) := by rw [hcomm]
        _ = (k : MulAut V) ((l : MulAut V) (Additive.toMul z)) := rfl
        _ = (k : MulAut V) (Additive.toMul z) := by rw [hz' l hl])

private theorem kappaZOfThreeNat_apply (h : ThreeNat A L T) (k : ↥(s1t3KBar A L))
    (z : ↥(s16smSubmod (fixV L))) :
    ((kappaZOfThreeNat h k z : ↥(s16smSubmod (fixV L))) : Additive V) =
      s16smRepW (MonoidHom.id ↥(s1t3KBar A L)) k (z : Additive V) := rfl

private theorem no_invariant_W_of_threeNat (h : ThreeNat A L T) :
    ∀ psi : Additive V →ₗ[ZMod 2] ZMod 2,
      (∀ l w, psi (s16smRepW (MonoidHom.id ↥L) l w) = psi w) → psi = 0 := by
  intro psi hpsi
  have hzero := s16sm_hperf_of_comm (W := V) (H := L) (MonoidHom.id ↥L) Function.surjective_id
    (U := ⊤) h.comm (psi.comp (s16smSubmod (⊤ : Subgroup V)).subtype)
    (fun γ m => hpsi γ (m : Additive V))
  ext x
  have hx : x ∈ s16smSubmod (⊤ : Subgroup V) := trivial
  have h1 := LinearMap.congr_fun hzero ⟨x, hx⟩
  simpa using h1

end FixedSpace

section Action

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
variable {L : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]
variable {T : Subgroup (MulAut V)}

private noncomputable def quotRepT (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    Representation (ZMod 2) ↥T (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
  letI := quotAct (X := L) (T := T) (W := (⊤ : Subgroup V)) hTL
    (fun _ _ _ _ => Subgroup.mem_top _)
  s16smRepW (H := ⊤)
    (MonoidHom.codRestrict (MulDistribMulAction.toMulAut ↥T (V ⧸ modFix L ⊤)) ⊤
      (fun _ => Subgroup.mem_top _))

private theorem quotRepT_apply (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V))) (t : ↥T) (v : V) :
    quotRepT (L := L) hTL t (quotFixMap (L := L) (Additive.ofMul v)) =
      quotFixMap (L := L) (Additive.ofMul ((t : MulAut V) v)) := by
  letI := quotAct (X := L) (T := T) (W := (⊤ : Subgroup V)) hTL
    (fun _ _ _ _ => Subgroup.mem_top _)
  rw [quotFixMap_apply, quotFixMap_apply, quotRepT, s16smRepW_apply]
  congr 1

end Action

section EndUnits

variable (W : Type) [CommGroup W] [Module (ZMod 2) (Additive W)]

private noncomputable def mulAutOfEndUnits (u : (Module.End (ZMod 2) (Additive W))ˣ) : MulAut W :=
  (MulAutTwo.linEquiv (V := W)).symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive W)) u)

private noncomputable def unitsToMulAutHom :
    (Module.End (ZMod 2) (Additive W))ˣ →* MulAut W :=
  (MulAutTwo.linEquiv (V := W)).symm.toMonoidHom.comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive W)).toMonoidHom

private theorem unitsToMulAutHom_apply (u : (Module.End (ZMod 2) (Additive W))ˣ) :
    unitsToMulAutHom W u = mulAutOfEndUnits W u := rfl

private theorem mulAutOfEndUnits_apply (u : (Module.End (ZMod 2) (Additive W))ˣ) (w : Additive W) :
    Additive.ofMul ((mulAutOfEndUnits W u) (Additive.toMul w)) =
      (u : Module.End (ZMod 2) (Additive W)) w := by
  rw [mulAutOfEndUnits, ← MulAutTwo.linEquiv_apply, MulEquiv.apply_symm_apply]
  rfl

end EndUnits

section Summands

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]

private noncomputable def quotAlphaL (h : ThreeNat A L T) :
    Representation (ZMod 2) ↥L (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
  (quotRepT (L := L) (T := A) h.normal).comp (Subgroup.inclusion h.le)

private noncomputable def quotAlphaK (h : ThreeNat A L T) :
    Representation (ZMod 2) ↥(s1t3KBar A L) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
  (quotRepT (L := L) (T := A) h.normal).comp
    (Subgroup.inclusion (show s1t3KBar A L ≤ A from inf_le_left))

private noncomputable def quotLActionHom (h : ThreeNat A L T) :
    ↥L →* MulAut (V ⧸ modFix L (⊤ : Subgroup V)) :=
  (unitsToMulAutHom (V ⧸ modFix L (⊤ : Subgroup V))).comp (quotAlphaL h).asGroupHom

private noncomputable abbrev quotLImage (h : ThreeNat A L T) :
    Subgroup (MulAut (V ⧸ modFix L (⊤ : Subgroup V))) :=
  (quotLActionHom h).range

private theorem quotAlphaL_apply (h : ThreeNat A L T) (l : ↥L) (v : V) :
    quotAlphaL h l (quotFixMap (L := L) (Additive.ofMul v)) =
      quotFixMap (L := L) (Additive.ofMul ((l : MulAut V) v)) :=
  quotRepT_apply (L := L) (T := A) h.normal (Subgroup.inclusion h.le l) v

private theorem quotAlphaL_apply_mk (h : ThreeNat A L T) (l : ↥L) (v : V) :
    quotAlphaL h l (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk ((l : MulAut V) v)) := by
  have h2 := quotAlphaL_apply h l v
  rwa [quotFixMap_apply] at h2

private theorem quotLActionHom_apply (h : ThreeNat A L T) (l : ↥L) (q : V ⧸ modFix L (⊤ : Subgroup V)) :
    quotLActionHom h l q = Additive.toMul ((quotAlphaL h l) (Additive.ofMul q)) := by
  have h2 := mulAutOfEndUnits_apply (W := V ⧸ modFix L (⊤ : Subgroup V))
    ((quotAlphaL h).asGroupHom l) (Additive.ofMul q)
  rw [Representation.asGroupHom_apply] at h2
  rw [quotLActionHom, MonoidHom.comp_apply, unitsToMulAutHom_apply]
  exact Additive.ofMul.injective h2

private theorem binaryNaturalSL_tilde (h : ThreeNat A L T) {I : Subgroup V}
    (hI : BinaryNaturalSL L I (fixV L) 3 1) :
    BinaryNaturalSL (quotLImage h) (tilde L (⊤ : Subgroup V) I) ⊥ 3 1 := by
  have hρ : (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))).ker = fixV L := by
    rw [QuotientGroup.ker_mk', CFSG.Quasithin.SmithD391.modFix_top_eq]
  refine s16k_binaryNaturalSL_map (H := L) (H' := quotLImage h) hI
    (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))) hρ (quotLActionHom h).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) (fun l v => ?_)
  rw [show ((quotLActionHom h).rangeRestrict l : MulAut (V ⧸ modFix L (⊤ : Subgroup V))) =
      quotLActionHom h l from rfl]
  rw [quotLActionHom_apply]
  exact (congrArg Additive.toMul (quotAlphaL_apply_mk h l v)).symm

private theorem exists_natSum3_quot (h : ThreeNat A L T) (hL : IsL3 ↥L 1) :
    NatSum3 (quotLImage h) (⊤ : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))) := by
  have hc : Nat.card ↥L = 168 := CFSG.LocalAnalysis.WeakClosure81.card_eq_of_isL3 hL
  obtain ⟨I₀, hnat, -, hind, htop⟩ := s16t3_quot_summands h.quasi h.sum
  refine s16c167_natSum3_of_sumOfNat ⟨fun i => tilde L ⊤ (I₀ i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact bot_le
  · intro i
    rw [bot_sup_eq]
    exact (iSupIndep_def.mp hind i).le_bot
  · rw [bot_sup_eq]
    exact htop
  · intro i
    exact binaryNaturalSL_tilde h
      (s16t3_sumOfNat_one (SumOfNatShape.sl3_of_card_eq_168 h.quasi hc (hnat i)))

private theorem finrank_quot_eq_nine (h : ThreeNat A L T) (hL : IsL3 ↥L 1) :
    Module.finrank (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) = 9 := by
  have hrk : rk ↥(⊤ : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))) = 9 :=
    s16c167_rk_natSum3 (exists_natSum3_quot h hL)
  have h1 : padicValNat 2 (Nat.card ↥(⊤ : Subgroup (V ⧸ modFix L (⊤ : Subgroup V)))) = 9 := hrk
  rw [Subgroup.card_top] at h1
  have h3 : padicValNat 2 (2 ^ Module.finrank (ZMod 2) (Additive (V ⧸ modFix L ⊤))) = 9 := by
    rw [← MulAutTwo.card_eq_pow_finrank (V := V ⧸ modFix L (⊤ : Subgroup V))]
    exact h1
  rwa [padicValNat.prime_pow] at h3

end Summands

section Summand

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]

private theorem quotAlphaL_apply_smul (h : ThreeNat A L T) (l : ↥L)
    (z : V ⧸ modFix L (⊤ : Subgroup V)) :
    quotAlphaL h l (Additive.ofMul z) = Additive.ofMul (l • z) := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective z
  rw [quotAlphaL_apply_mk]
  exact congrArg Additive.ofMul (XMod.smul_quotMk (L := (⊤ : Subgroup V)) l v).symm

private theorem toMul_quotAlphaL (h : ThreeNat A L T) (l : ↥L)
    (v : Additive (V ⧸ modFix L (⊤ : Subgroup V))) :
    Additive.toMul (quotAlphaL h l v) = l • Additive.toMul v := by
  have h2 := congrArg Additive.toMul (quotAlphaL_apply_smul h l (Additive.toMul v))
  simpa using h2

private theorem card_submod (Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))) :
    Nat.card ↥(s16smSubmod Y) = Nat.card ↥Y := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
      invFun := fun y => ⟨Additive.ofMul y.1, y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

private theorem finrank_submod_of_binaryNaturalSL_three
    {H : Subgroup (MulAut (V ⧸ modFix L (⊤ : Subgroup V)))}
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hY : BinaryNaturalSL H Y ⊥ 3 1) :
    Module.finrank (ZMod 2) ↥(s16smSubmod Y) = 3 := by
  have hcard : Nat.card ↥(s16smSubmod Y) = 8 := by
    rw [card_submod, s15_T7_card_eight hY]
  have h2 : Nat.card ↥(s16smSubmod Y) =
      2 ^ Module.finrank (ZMod 2) ↥(s16smSubmod Y) := by
    haveI : Module.Finite (ZMod 2) ↥(s16smSubmod Y) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(s16smSubmod Y))
    rwa [Nat.card_zmod] at h
  rw [hcard] at h2
  have h3 : 2 ^ (3 : ℕ) = 2 ^ Module.finrank (ZMod 2) ↥(s16smSubmod Y) := by
    rw [← h2]; norm_num
  exact (Nat.pow_right_injective (by norm_num) h3).symm

private theorem s16smSubmod_ne_bot_of_isIrr {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))}
    (hY : XMod.IsIrr ↥L Y) : s16smSubmod Y ≠ ⊥ := by
  intro hbot
  have hlt : (⊥ : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))) < Y := hY.2.1
  have hYne : Y ≠ ⊥ := bot_lt_iff_ne_bot.mp hlt
  have hex : ∃ y ∈ Y, y ≠ 1 := by
    by_contra h
    apply hYne
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    exact h ⟨y, hy, hy1⟩
  obtain ⟨y, hy, hy1⟩ := hex
  have hmem : Additive.ofMul y ∈ s16smSubmod Y := by
    show Additive.toMul (Additive.ofMul y) ∈ Y
    simpa using hy
  rw [hbot] at hmem
  have h2 : Additive.ofMul y = Additive.ofMul 1 := by
    simpa using (Subgroup.mem_bot.mp hmem)
  exact hy1 (Additive.ofMul.injective h2)

private theorem isIrrSubmodule_of_isIrr (h : ThreeNat A L T)
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hY : XMod.IsIrr ↥L Y) :
    ∀ U ≤ s16smSubmod Y,
      (∀ (l : ↥L), ∀ v ∈ U, (quotAlphaL h) l v ∈ U) → U = ⊥ ∨ U = s16smSubmod Y := by
  intro U hU hInv
  let Z : Subgroup (V ⧸ modFix L (⊤ : Subgroup V)) := AddSubgroup.toSubgroup' U.toAddSubgroup
  have hZmem : ∀ z : V ⧸ modFix L (⊤ : Subgroup V),
      z ∈ Z ↔ Additive.ofMul z ∈ U := fun z => AddSubgroup.mem_toSubgroup' U.toAddSubgroup z
  have hZle : Z ≤ Y := by
    intro z hz
    have h1 : Additive.ofMul z ∈ s16smSubmod Y := hU hz
    exact h1
  have hZinv : XMod.IsInv ↥L Z := by
    intro l z hz
    rw [hZmem] at hz ⊢
    have h2 := hInv l (Additive.ofMul z) hz
    rwa [quotAlphaL_apply_smul] at h2
  rcases hY.2.2 Z hZinv bot_le hZle with hZ | hZ
  · left
    refine Submodule.ext fun v => ?_
    rw [Submodule.mem_bot]
    constructor
    · intro hv
      have h1 : Additive.toMul v ∈ Z := (hZmem _).mpr (by simpa using hv)
      rw [hZ, Subgroup.mem_bot] at h1
      show v = 0
      calc v = Additive.ofMul (Additive.toMul v) := rfl
        _ = Additive.ofMul 1 := by rw [h1]
        _ = 0 := rfl
    · intro hv
      rw [hv]
      exact U.zero_mem
  · right
    refine Submodule.ext fun v => ?_
    constructor
    · intro hv
      exact hU hv
    · intro hv
      have h1 : Additive.toMul v ∈ Z := by
        rw [hZ]
        exact hv
      exact (hZmem _).mp h1

section QPackage

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]
variable {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))}

private noncomputable def quotD (h : ThreeNat A L T) :
    Subgroup (Module.End (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))))ˣ :=
  (quotAlphaL h).asGroupHom.range

private theorem mem_quotD {h : ThreeNat A L T} {d : (Module.End (ZMod 2)
    (Additive (V ⧸ modFix L (⊤ : Subgroup V))))ˣ} :
    d ∈ quotD h ↔ ∃ l : ↥L, (quotAlphaL h).asGroupHom l = d :=
  MonoidHom.mem_range

private theorem submod_invariant (h : ThreeNat A L T) (hY : XMod.IsIrr ↥L Y) :
    ∀ l : ↥L, s16smSubmod Y ≤ (s16smSubmod Y).comap (quotAlphaL h l) := by
  intro l v hv
  rw [Submodule.mem_comap]
  have hv' : v = Additive.ofMul (Additive.toMul v) := rfl
  rw [hv', quotAlphaL_apply_smul]
  exact hY.1 l (Additive.toMul v) hv

private theorem submod_invariant_D (h : ThreeNat A L T) (hY : XMod.IsIrr ↥L Y) :
    ∀ d ∈ quotD h, ∀ v ∈ s16smSubmod Y, (d.1 : Module.End (ZMod 2)
      (Additive (V ⧸ modFix L (⊤ : Subgroup V)))) v ∈ s16smSubmod Y := by
  intro d hd v hv
  obtain ⟨l, rfl⟩ := mem_quotD.mp hd
  exact Submodule.mem_comap.mp (submod_invariant h hY l hv)

private theorem isIrrSubmodule_D (h : ThreeNat A L T) (hY : XMod.IsIrr ↥L Y) :
    ∀ U ≤ s16smSubmod Y,
      (∀ d ∈ quotD h, ∀ v ∈ U, (d.1 : Module.End (ZMod 2)
        (Additive (V ⧸ modFix L (⊤ : Subgroup V)))) v ∈ U) →
      U = ⊥ ∨ U = s16smSubmod Y := by
  intro U hU hInv
  refine isIrrSubmodule_of_isIrr h hY U hU (fun l v hv => ?_)
  exact hInv ((quotAlphaL h).asGroupHom l) (mem_quotD.mpr ⟨l, rfl⟩) v hv

private noncomputable def rhoQOf (h : ThreeNat A L T) (hY : XMod.IsIrr ↥L Y) :
    Representation (ZMod 2) ↥L ↥(s16smSubmod Y) :=
  (quotAlphaL h).subrepresentation (s16smSubmod Y) (submod_invariant h hY)

private theorem isIrrSubmodule_subtype (h : ThreeNat A L T) (hYirr : XMod.IsIrr ↥L Y) :
    ∀ U : Submodule (ZMod 2) ↥(s16smSubmod Y),
      (∀ (l : ↥L), ∀ v ∈ U, rhoQOf h hYirr l v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  set K : Submodule (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
    U.map (s16smSubmod Y).subtype with hK
  have hKle : K ≤ s16smSubmod Y := by
    intro v hv
    obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hv
    exact w.2
  have hKinv : ∀ l : ↥L, ∀ v ∈ K, quotAlphaL h l v ∈ K := by
    intro l v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨rhoQOf h hYirr l w, hU l w hw, rfl⟩
  rcases isIrrSubmodule_of_isIrr h hYirr K hKle hKinv with hKbot | hKtop
  · left
    refine Submodule.ext fun w => ?_
    constructor
    · intro hw
      have h1 : (w : Additive (V ⧸ modFix L (⊤ : Subgroup V))) ∈ K :=
        Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      rw [hKbot, Submodule.mem_bot] at h1
      exact Subtype.ext h1
    · intro hw
      rw [Submodule.mem_bot] at hw
      rw [hw]
      exact U.zero_mem
  · right
    refine Submodule.ext fun w => ?_
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      have h1 : (w : Additive (V ⧸ modFix L (⊤ : Subgroup V))) ∈ K := by
        rw [hKtop]
        exact w.2
      obtain ⟨w', hw', hww'⟩ := Submodule.mem_map.mp h1
      have hww : w' = w := Subtype.ext hww'
      rwa [hww] at hw'

private theorem no_fixed_Q_of (h : ThreeNat A L T) (hYirr : XMod.IsIrr ↥L Y)
    (hYnat : BinaryNaturalSL (quotLImage h) Y ⊥ 3 1) :
    ∀ q : ↥(s16smSubmod Y), (∀ l : ↥L, rhoQOf h hYirr l q = q) → q = 0 := by
  intro q hq
  have hfr : Module.finrank (ZMod 2) ↥(s16smSubmod Y) = 3 :=
    finrank_submod_of_binaryNaturalSL_three hYnat
  have hspan : Submodule.span (ZMod 2) {q} = ⊥ ∨ Submodule.span (ZMod 2) {q} = ⊤ := by
    refine isIrrSubmodule_subtype h hYirr _ (fun l v hv => ?_)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by rw [← hc, map_smul, hq l]⟩
  rcases hspan with hbot | htop
  · have hmem : q ∈ Submodule.span (ZMod 2) {q} := Submodule.subset_span (Set.mem_singleton q)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  · exfalso
    have h2 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {q}) = 3 := by
      rw [htop, finrank_top]
      exact hfr
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0] at htop
      have hbot : (⊤ : Submodule (ZMod 2) ↥(s16smSubmod Y)) = ⊥ := by
        rw [← htop]
        exact Submodule.span_singleton_eq_bot.mpr rfl
      have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) ↥(s16smSubmod Y)) = 0 := by
        rw [hbot]
        exact finrank_bot (ZMod 2) ↥(s16smSubmod Y)
      rw [finrank_top] at h1
      omega
    rw [finrank_span_singleton hq0] at h2
    omega

private theorem no_invariant_Q_of (h : ThreeNat A L T) (hYirr : XMod.IsIrr ↥L Y)
    (hYnat : BinaryNaturalSL (quotLImage h) Y ⊥ 3 1) :
    ∀ psi : ↥(s16smSubmod Y) →ₗ[ZMod 2] ZMod 2,
      (∀ (l : ↥L) (q : ↥(s16smSubmod Y)), psi (rhoQOf h hYirr l q) = psi q) → psi = 0 := by
  intro psi hpsi
  have hcard : Nat.card ↥(s16smSubmod Y) = 8 := by
    rw [card_submod, s15_T7_card_eight hYnat]
  have hker : LinearMap.ker psi = ⊥ ∨ LinearMap.ker psi = ⊤ := by
    refine isIrrSubmodule_subtype h hYirr _ (fun l v hv => ?_)
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hpsi]
    exact hv
  rcases hker with hbot | htop
  · exfalso
    have hinj : Function.Injective psi := LinearMap.ker_eq_bot.mp hbot
    have hle : Nat.card ↥(s16smSubmod Y) ≤ Nat.card (ZMod 2) :=
      Nat.card_le_card_of_injective psi hinj
    rw [hcard, Nat.card_zmod] at hle
    omega
  · ext x
    have hx : x ∈ LinearMap.ker psi := by rw [htop]; trivial
    simpa using hx

end QPackage

section AIrreducible

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]

private theorem quotRepT_apply_mk (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V))) (t : ↥T) (v : V) :
    quotRepT (L := L) hTL t (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk ((t : MulAut V) v)) := by
  have h := quotRepT_apply (L := L) hTL t v
  rwa [quotFixMap_apply] at h

private theorem isIrr_of_minimal_submodule (h : ThreeNat A L T)
    {I : Submodule (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))}
    (hIne : I ≠ ⊥) (hIinv : ∀ l : ↥L, ∀ v ∈ I, quotAlphaL h l v ∈ I)
    (hImin : ∀ I' ≤ I, (∀ l : ↥L, ∀ v ∈ I', quotAlphaL h l v ∈ I') → I' = ⊥ ∨ I' = I) :
    ∃ Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V)),
      XMod.IsIrr ↥L Y ∧ (∀ z, z ∈ Y ↔ Additive.ofMul z ∈ I) := by
  let Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V)) := AddSubgroup.toSubgroup' I.toAddSubgroup
  have hYmem : ∀ z, z ∈ Y ↔ Additive.ofMul z ∈ I :=
    fun z => AddSubgroup.mem_toSubgroup' I.toAddSubgroup z
  have hYinv : XMod.IsInv ↥L Y := by
    intro l z hz
    rw [hYmem] at hz ⊢
    have h2 := hIinv l (Additive.ofMul z) hz
    rwa [quotAlphaL_apply_smul] at h2
  have hYpos : (⊥ : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))) < Y := by
    have hex : ∃ z : V ⧸ modFix L (⊤ : Subgroup V), Additive.ofMul z ∈ I ∧
        Additive.ofMul z ≠ 0 := by
      by_contra h
      apply hIne
      refine Submodule.ext fun v => ?_
      constructor
      · intro hv
        by_contra hv0
        exact h ⟨Additive.toMul v, by simpa using hv, by simpa using hv0⟩
      · intro hv
        rw [Submodule.mem_bot] at hv
        rw [hv]
        exact I.zero_mem
    obtain ⟨z, hz, hz0⟩ := hex
    refine lt_of_le_of_ne bot_le ?_
    intro hbot
    have h1 : z ∈ Y := hYmem z |>.mpr hz
    rw [← hbot, Subgroup.mem_bot] at h1
    exact hz0 (by rw [h1]; rfl)
  have hYsec : ∀ J : Subgroup (V ⧸ modFix L (⊤ : Subgroup V)), XMod.IsInv ↥L J → ⊥ ≤ J → J ≤ Y →
      J = ⊥ ∨ J = Y := by
    intro J hJinv _ hJY
    let I' : Submodule (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
      { carrier := {v | v ∈ I ∧ Additive.toMul v ∈ J}
        add_mem' := by
          intro a b ha hb
          refine ⟨I.add_mem ha.1 hb.1, ?_⟩
          have h : Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b := rfl
          rw [h]
          exact J.mul_mem ha.2 hb.2
        zero_mem' := ⟨I.zero_mem, J.one_mem⟩
        smul_mem' := by
          intro c v hv
          refine ⟨I.smul_mem c hv.1, ?_⟩
          have hc : c = 0 ∨ c = 1 := by revert c; decide
          rcases hc with rfl | rfl
          · simp
          · simpa using hv.2 }
    have hI'le : I' ≤ I := fun v hv => hv.1
    have hI'inv : ∀ l : ↥L, ∀ v ∈ I', quotAlphaL h l v ∈ I' := by
      intro l v hv
      refine ⟨hIinv l v hv.1, ?_⟩
      rw [toMul_quotAlphaL]
      exact hJinv l (Additive.toMul v) hv.2
    rcases hImin I' hI'le hI'inv with hbot | htop
    · left
      refine le_antisymm ?_ bot_le
      intro z hz
      have hzI : Additive.ofMul z ∈ I := hYmem z |>.mp (hJY hz)
      have hzJ : Additive.ofMul z ∈ I' := ⟨hzI, hz⟩
      rw [hbot] at hzJ
      have h1 : Additive.ofMul z = 0 := (Submodule.mem_bot (ZMod 2)).mp hzJ
      refine Subgroup.mem_bot.mpr ?_
      have h2 := congrArg Additive.toMul h1
      simpa using h2
    · right
      refine le_antisymm hJY ?_
      intro z hz
      have hzI : Additive.ofMul z ∈ I := hYmem z |>.mp hz
      have hzJ : Additive.ofMul z ∈ I' := by rw [htop]; exact hzI
      have h1 : Additive.toMul (Additive.ofMul z) ∈ J := hzJ.2
      simpa using h1
  exact ⟨Y, ⟨hYinv, hYpos, hYsec⟩, hYmem⟩

private theorem irreducible_quot_A (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∀ W : Submodule (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))),
      (∀ a : ↥A, ∀ v ∈ W, quotRepT (L := L) (T := A) h.normal a v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  · right
    obtain ⟨I, hIle, hIne, hIinv, hImin⟩ :=
      CFSG.GroupTheory.exists_minimal_invariant_submodule (p := 2) (G := ↥L) (quotAlphaL h)
        hW0 (fun l v hv => hW (Subgroup.inclusion h.le l) v hv)
    obtain ⟨Y, hYirr, hYmem⟩ := isIrr_of_minimal_submodule h hIne hIinv hImin
    obtain ⟨hJmem, hJtilde⟩ := s16t3_lift h.quasi hYirr
    obtain ⟨I₀, -, hYirr₀, -, htop⟩ := s16t3_quot_summands h.quasi h.sum
    let R : Subgroup (V ⧸ modFix L (⊤ : Subgroup V)) := AddSubgroup.toSubgroup' W.toAddSubgroup
    have hRmem : ∀ z : V ⧸ modFix L (⊤ : Subgroup V), z ∈ R ↔ Additive.ofMul z ∈ W :=
      fun z => AddSubgroup.mem_toSubgroup' W.toAddSubgroup z
    have hYle : ∀ i, tilde L (⊤ : Subgroup V) (I₀ i) ≤ R := by
      intro i
      have hJi := s16t3_lift h.quasi (hYirr₀ i)
      let Ji : Subgroup V := modComm L (Subgroup.comap
        (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))) (tilde L (⊤ : Subgroup V) (I₀ i)))
      have hJimem : Ji ∈ irrSet L := hJi.1
      have hJitilde : tilde L (⊤ : Subgroup V) Ji = tilde L (⊤ : Subgroup V) (I₀ i) := hJi.2
      have htrans := h.trans (modComm L (Subgroup.comap
        (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))) Y)) hJmem Ji hJimem
      let g : MulAut V := Classical.choose htrans
      have hg : g ∈ A ⊓ Subgroup.normalizer (L : Set (MulAut V)) :=
        (Classical.choose_spec htrans).1
      have hgJ : Ji = (modComm L (Subgroup.comap
          (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))) Y)).map g.toMonoidHom :=
        (Classical.choose_spec htrans).2
      have hstep : ∀ u ∈ modComm L (Subgroup.comap (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))) Y),
          (QuotientGroup.mk ((g : MulAut V) u) : V ⧸ modFix L (⊤ : Subgroup V)) ∈ R := by
        intro u hu
        rw [hRmem]
        have huW : Additive.ofMul (QuotientGroup.mk u) ∈ W := by
          have h1 : (QuotientGroup.mk u : V ⧸ modFix L (⊤ : Subgroup V)) ∈
              tilde L (⊤ : Subgroup V) (modComm L (Subgroup.comap
                (QuotientGroup.mk' (modFix L (⊤ : Subgroup V))) Y)) := by
            rw [mem_tilde_iff]
            exact ⟨u, hu, rfl⟩
          rw [hJtilde] at h1
          exact hIle ((hYmem _).mp h1)
        have h2 := hW ⟨g, hg.1⟩ (Additive.ofMul (QuotientGroup.mk u)) huW
        rwa [quotRepT_apply_mk] at h2
      intro y hy
      rw [← hJitilde] at hy
      obtain ⟨v, hv, hvy⟩ := mem_tilde_iff.mp hy
      rw [hgJ] at hv
      obtain ⟨u, hu, hvu⟩ := Subgroup.mem_map.mp hv
      rw [← hvy, ← hvu]
      exact hstep u hu
    have hRtop : R = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← htop]
      exact iSup_le hYle
    rw [Submodule.eq_top_iff']
    intro v
    exact (hRmem _).mp (by rw [hRtop]; trivial)

private noncomputable def quotK (h : ThreeNat A L T) :
    Subgroup (Module.End (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))))ˣ :=
  (quotAlphaK h).asGroupHom.range

private theorem mem_quotD_of (h : ThreeNat A L T) (l : ↥L) :
    (quotAlphaL h).asGroupHom l ∈ quotD h := ⟨l, rfl⟩

private theorem mem_quotK_of (h : ThreeNat A L T) (k : ↥(s1t3KBar A L)) :
    (quotAlphaK h).asGroupHom k ∈ quotK h := ⟨k, rfl⟩

private theorem mem_quotD_of_mem (h : ThreeNat A L T) {l : ↥A} (hl : (l : MulAut V) ∈ L) :
    (quotRepT (L := L) (T := A) h.normal).asGroupHom l ∈ quotD h := by
  have h1 : (Subgroup.inclusion h.le ⟨(l : MulAut V), hl⟩ : ↥A) = l := Subtype.ext rfl
  rw [← h1]
  exact mem_quotD_of h ⟨_, hl⟩

private theorem mem_quotK_of_mem (h : ThreeNat A L T) {k : ↥A} (hk : (k : MulAut V) ∈ s1t3KBar A L) :
    (quotRepT (L := L) (T := A) h.normal).asGroupHom k ∈ quotK h := by
  have h1 : (Subgroup.inclusion inf_le_left ⟨(k : MulAut V), hk⟩ : ↥A) = k := Subtype.ext rfl
  rw [← h1]
  exact mem_quotK_of h ⟨_, hk⟩

private theorem quotA_mem_sup (h : ThreeNat A L T)
    (hsup : L ⊔ s1t3KBar A L = A) (a : ↥A) :
    (quotRepT (L := L) (T := A) h.normal).asGroupHom a ∈ quotD h ⊔ quotK h := by
  have hLnorm : (L.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  haveI := hLnorm
  have hK : s1t3KBar A L = A ⊓ Subgroup.centralizer (L : Set (MulAut V)) := rfl
  have hsup' : L ⊔ (A ⊓ Subgroup.centralizer (L : Set (MulAut V))) = A := by
    rw [← hK]
    exact hsup
  have hsupA : L.subgroupOf A ⊔ (s1t3KBar A L).subgroupOf A = ⊤ := by
    rw [hK, ← Subgroup.subgroupOf_sup h.le inf_le_left, hsup', Subgroup.subgroupOf_self]
  obtain ⟨l, hl, k, hk, hlk⟩ := (Subgroup.mem_sup_of_normal_left
    (s := L.subgroupOf A) (t := (s1t3KBar A L).subgroupOf A)).mp (by rw [hsupA]; trivial)
  have hl' : (l : MulAut V) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hk' : (k : MulAut V) ∈ s1t3KBar A L := Subgroup.mem_subgroupOf.mp hk
  have hae : a = l * k := hlk.symm
  have hx : (quotRepT (L := L) (T := A) h.normal).asGroupHom (l * k) ∈ quotD h ⊔ quotK h := by
    rw [map_mul]
    exact Subgroup.mul_mem_sup (mem_quotD_of_mem h hl') (mem_quotK_of_mem h hk')
  exact hae ▸ hx

private theorem hirr_quot (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) (hL : IsL3 ↥L 1) :
    ∀ W : Submodule (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))),
      (∀ g ∈ quotK h ⊔ quotD h, ∀ v ∈ W,
        (g : Module.End (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  refine irreducible_quot_A h h7 W (fun a v hv => ?_)
  have hsup : L ⊔ s1t3KBar A L = A := ThreeNat.sup_kBar_eq_of_isL3 h h7 hL
  have hmem : (quotRepT (L := L) (T := A) h.normal).asGroupHom a ∈ quotK h ⊔ quotD h := by
    rw [sup_comm]
    exact quotA_mem_sup h hsup a
  exact hW _ hmem v hv

end AIrreducible

section Faithful

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]

private theorem quotLActionHom_ker (h : ThreeNat A L T) : MonoidHom.ker (quotLActionHom h) = ⊥ := by
  rw [eq_bot_iff]
  intro l hl
  rw [MonoidHom.mem_ker] at hl
  have hinv : ∀ x : V, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h.elem x)
  have hfix : ∀ w : V, (l : MulAut V) w * w⁻¹ ∈ fixV L := by
    intro w
    have h1 : quotLActionHom h l (QuotientGroup.mk w) = QuotientGroup.mk w := by
      rw [hl]
      rfl
    rw [quotLActionHom_apply] at h1
    have h2 : ((l : MulAut V) w) * w ∈ fixV L := by
      have h3 : ((l : MulAut V) w)⁻¹ * w ∈ modFix L (⊤ : Subgroup V) :=
        QuotientGroup.eq.mp h1
      rwa [CFSG.Quasithin.SmithD391.modFix_top_eq, hinv] at h3
    rwa [hinv w]
  have h1 : (l : MulAut V) = 1 := h.faithful (l : MulAut V) (h.le l.2) hfix
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

private theorem quotLActionHom_injective (h : ThreeNat A L T) :
    Function.Injective (quotLActionHom h) :=
  (MonoidHom.ker_eq_bot_iff (quotLActionHom h)).mp (quotLActionHom_ker h)

private theorem card_quotLImage (h : ThreeNat A L T) (hL : IsL3 ↥L 1) :
    Nat.card ↥(quotLImage h) = 168 := by
  have hker := quotLActionHom_injective h
  have hbij : Function.Bijective (quotLActionHom h).rangeRestrict :=
    ⟨fun a b hab => hker (congrArg Subtype.val hab),
      MonoidHom.rangeRestrict_surjective _⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij),
    CFSG.LocalAnalysis.WeakClosure81.card_eq_of_isL3 hL]

end Faithful

section Model

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
variable {A L T : Subgroup (MulAut V)}
variable [Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))]

private theorem exists_theta (h : ThreeNat A L T) (hL : IsL3 ↥L 1)
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(quotLImage h)}
    (hπsurj : Function.Surjective π) :
    ∃ theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2)),
      ∀ l : ↥L, π (theta l) = (quotLActionHom h).rangeRestrict l := by
  have hbijL : Function.Bijective (quotLActionHom h).rangeRestrict :=
    ⟨fun a b hab => quotLActionHom_injective h (congrArg Subtype.val hab),
      MonoidHom.rangeRestrict_surjective _⟩
  have hbijπ : Function.Bijective π := by
    haveI : Fintype ↥(StatedSL 3 (ZMod 2)) := Fintype.ofFinite _
    haveI : Fintype ↥(quotLImage h) := Fintype.ofFinite _
    refine (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hπsurj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.Open.StatedAPI.card_statedSL_three_zmod_two,
      card_quotLImage h hL]
  let πbi : ↥(StatedSL 3 (ZMod 2)) ≃* ↥(quotLImage h) := MulEquiv.ofBijective π hbijπ
  refine ⟨(MulEquiv.ofBijective _ hbijL).trans πbi.symm, fun l => ?_⟩
  change πbi (πbi.symm ((MulEquiv.ofBijective _ hbijL) l)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private noncomputable def submodAddEquiv (Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))) :
    ↥(s16smSubmod Y) ≃+ Additive ↥Y where
  toFun q := Additive.ofMul ⟨Additive.toMul (q : Additive (V ⧸ modFix L (⊤ : Subgroup V))), q.2⟩
  invFun y := ⟨Additive.ofMul (((Additive.toMul y : ↥Y) : V ⧸ modFix L (⊤ : Subgroup V))),
    (Additive.toMul y).2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Additive.ext
    apply Subtype.ext
    rfl
  map_add' q q' := rfl

private noncomputable def coordQOf {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))}
    (e : ↥Y ≃* Multiplicative (Fin 3 → ZMod 2)) :
    ↥(s16smSubmod Y) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  AddEquiv.toLinearEquiv
    ((submodAddEquiv (L := L) Y).trans (e.toAdditive : Additive ↥Y ≃+ (Fin 3 → ZMod 2)))
    (fun c q => by
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl <;> simp)

private theorem coordQOf_apply {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))}
    (e : ↥Y ≃* Multiplicative (Fin 3 → ZMod 2))
    (z : Additive (V ⧸ modFix L (⊤ : Subgroup V))) (hz : z ∈ s16smSubmod Y) :
    coordQOf (L := L) e ⟨z, hz⟩ =
      Multiplicative.toAdd (e ⟨Additive.toMul z, hz⟩) := rfl

private theorem coordQOf_rhoQOf (h : ThreeNat A L T)
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hYirr : XMod.IsIrr ↥L Y)
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(quotLImage h)}
    {e : ↥Y ≃* Multiplicative (Fin 3 → ZMod 2)}
    (he : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥Y)
      (hu : ((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (u : V ⧸ modFix L (⊤ : Subgroup V)) ∈ Y),
      e ⟨((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
          (u : V ⧸ modFix L (⊤ : Subgroup V)), hu⟩ =
        natAct (StatedSL 3 (ZMod 2)) γ (e u))
    {theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2))}
    (htheta : ∀ l : ↥L, π (theta l) = (quotLActionHom h).rangeRestrict l)
    (l : ↥L) (q : ↥(s16smSubmod Y)) :
    coordQOf (L := L) e (rhoQOf h hYirr l q) =
      (((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ coordQOf (L := L) e q) := by
  obtain ⟨z, hz⟩ := q
  have hcoe : Additive.toMul (quotAlphaL h l z) =
      ((quotLActionHom h).rangeRestrict l : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (Additive.toMul z) := by
    rw [toMul_quotAlphaL]
    rfl
  have hmem : ((quotLActionHom h).rangeRestrict l : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
      (Additive.toMul z) ∈ Y := by
    rw [← hcoe]
    exact submod_invariant h hYirr l hz
  have hπeq : ((π (theta l) : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V))) =
      ((quotLActionHom h).rangeRestrict l : MulAut (V ⧸ modFix L (⊤ : Subgroup V))) :=
    congrArg Subtype.val (htheta l)
  have h5 := he (theta l) ⟨Additive.toMul z, hz⟩ (by rw [hπeq]; exact hmem)
  have hsub : (⟨((π (theta l) : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (Additive.toMul z), by rw [hπeq]; exact hmem⟩ : ↥Y) =
      ⟨((quotLActionHom h).rangeRestrict l : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (Additive.toMul z), hmem⟩ :=
    Subtype.ext (congrArg (fun g : MulAut (V ⧸ modFix L (⊤ : Subgroup V)) =>
      g (Additive.toMul z)) hπeq)
  rw [hsub] at h5
  have hρ : (rhoQOf h hYirr l ⟨z, hz⟩ : ↥(s16smSubmod Y)) =
      ⟨quotAlphaL h l z, submod_invariant h hYirr l hz⟩ := rfl
  rw [hρ, coordQOf_apply]
  rw [show (⟨Additive.toMul (quotAlphaL h l z), submod_invariant h hYirr l hz⟩ : ↥Y) =
      ⟨((quotLActionHom h).rangeRestrict l : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (Additive.toMul z), hmem⟩ from Subtype.ext hcoe]
  rw [h5]
  rfl

private theorem commutantD_eq_bot (h : ThreeNat A L T)
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hYirr : XMod.IsIrr ↥L Y)
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(quotLImage h)}
    {e : ↥Y ≃* Multiplicative (Fin 3 → ZMod 2)}
    (he : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥Y)
      (hu : ((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (u : V ⧸ modFix L (⊤ : Subgroup V)) ∈ Y),
      e ⟨((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
          (u : V ⧸ modFix L (⊤ : Subgroup V)), hu⟩ =
        natAct (StatedSL 3 (ZMod 2)) γ (e u))
    {theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2))}
    (htheta : ∀ l : ↥L, π (theta l) = (quotLActionHom h).rangeRestrict l) :
    CommutingFactor.commutantD (submod_invariant_D h hYirr) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro φ hφ
  rw [CommutingFactor.mem_commutantD] at hφ
  let cq : ↥(s16smSubmod Y) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := coordQOf (L := L) e
  let F : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    cq.toLinearMap.comp (φ.comp cq.symm.toLinearMap)
  have hF : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (v : Fin 3 → ZMod 2),
      F (((γ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
      (((γ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ F v) := by
    intro γ v
    obtain ⟨l, rfl⟩ := theta.surjective γ
    have hcomm := hφ ⟨(quotAlphaL h).asGroupHom l, ⟨l, rfl⟩⟩
    have h1 : (CommutingFactor.resD (submod_invariant_D h hYirr)
        ⟨(quotAlphaL h).asGroupHom l, ⟨l, rfl⟩⟩ : Module.End (ZMod 2) ↥(s16smSubmod Y)) =
        rhoQOf h hYirr l := rfl
    have h2 : rhoQOf h hYirr l (φ (cq.symm v)) = φ (rhoQOf h hYirr l (cq.symm v)) := by
      have h3 := congrFun (congrArg DFunLike.coe hcomm) (cq.symm v)
      rw [h1] at h3
      simpa using h3
    have h4 := coordQOf_rhoQOf h hYirr he htheta l (cq.symm v)
    rw [LinearEquiv.apply_symm_apply] at h4
    have h4' : cq.symm (((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = rhoQOf h hYirr l (cq.symm v) := by
      rw [← h4, LinearEquiv.symm_apply_apply]
    show cq (φ (cq.symm (((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))) =
      ((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ F v
    rw [h4', ← h2, coordQOf_rhoQOf h hYirr he htheta l (φ (cq.symm v))]
    rfl
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, ∀ v : Fin 3 → ZMod 2, F v = c • v :=
    CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := ZMod 2) (d := 3) (by decide)
      F.toAddMonoidHom (fun γ hγ v => hF ⟨γ, hγ⟩ v)
  rw [Algebra.mem_bot]
  refine ⟨c, ?_⟩
  refine LinearMap.ext fun q => ?_
  have hFq : F (cq q) = cq (φ q) := by
    show cq (φ (cq.symm (cq q))) = cq (φ q)
    rw [LinearEquiv.symm_apply_apply]
  have h6 : cq (φ q) = c • cq q := by
    rw [← hFq]
    exact hc (cq q)
  have h7 : φ q = c • q := by
    rw [show φ q = cq.symm (cq (φ q)) from (LinearEquiv.symm_apply_apply cq (φ q)).symm]
    rw [h6, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]
  rw [h7, Algebra.algebraMap_eq_smul_one]
  simp

private theorem quotAlphaK_apply_mk (h : ThreeNat A L T) (k : ↥(s1t3KBar A L)) (v : V) :
    quotAlphaK h k (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk ((k : MulAut V) v)) := by
  show (quotRepT (L := L) (T := A) h.normal) (Subgroup.inclusion inf_le_left k)
      (Additive.ofMul (QuotientGroup.mk v)) = _
  rw [quotRepT_apply_mk]
  rfl

private theorem quotK_commutes_quotD (h : ThreeNat A L T) :
    ∀ x ∈ quotK h, ∀ d ∈ quotD h, x * d = d * x := by
  rintro x ⟨k, rfl⟩ d ⟨l, rfl⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  obtain ⟨z, hz⟩ : ∃ z, Additive.ofMul z = v := ⟨Additive.toMul v, rfl⟩
  rw [← hz]
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  show (quotAlphaK h k) ((quotAlphaL h l) (Additive.ofMul (QuotientGroup.mk w))) =
    (quotAlphaL h l) ((quotAlphaK h k) (Additive.ofMul (QuotientGroup.mk w)))
  rw [quotAlphaL_apply_mk, quotAlphaK_apply_mk, quotAlphaK_apply_mk, quotAlphaL_apply_mk]
  congr 2
  have hk : (k : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
    (Subgroup.mem_inf.mp k.2).2
  have hcomm : (l : MulAut V) * (k : MulAut V) = (k : MulAut V) * (l : MulAut V) :=
    (Subgroup.mem_centralizer_iff.mp hk) l l.2
  exact congrArg (fun g : MulAut V => g w) hcomm.symm

private theorem exists_eval_data (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (hL : IsL3 ↥L 1) {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))}
    (hYirr : XMod.IsIrr ↥L Y)
    (hYnat : BinaryNaturalSL (quotLImage h) Y ⊥ 3 1)
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(quotLImage h)}
    {e : ↥Y ≃* Multiplicative (Fin 3 → ZMod 2)}
    (he : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥Y)
      (hu : ((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (u : V ⧸ modFix L (⊤ : Subgroup V)) ∈ Y),
      e ⟨((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
          (u : V ⧸ modFix L (⊤ : Subgroup V)), hu⟩ =
        natAct (StatedSL 3 (ZMod 2)) γ (e u))
    {theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2))}
    (htheta : ∀ l : ↥L, π (theta l) = (quotLActionHom h).rangeRestrict l) :
    ∃ Φ : (Fin 3 → ↥(s16smSubmod Y)) ≃ₗ[ZMod 2]
        Additive (V ⧸ modFix L (⊤ : Subgroup V)),
      (∀ (d : ↥(quotD h)) (f : Fin 3 → ↥(s16smSubmod Y)),
        Φ (fun i => CommutingFactor.resD (submod_invariant_D h hYirr) d (f i)) =
          (d.1 : Module.End (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V)))) (Φ f)) ∧
      Function.Bijective (CommutingFactor.evalHom (submod_invariant_D h hYirr)) := by
  obtain ⟨r, Φ, hΦ⟩ := CommutingFactor.exists_isotypic_equiv (quotK_commutes_quotD h)
    (hirr_quot h h7 hL) (submod_invariant_D h hYirr) (s16smSubmod_ne_bot_of_isIrr hYirr)
    (isIrrSubmodule_D h hYirr)
  have hdimS : Module.finrank (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) = 9 :=
    finrank_quot_eq_nine h hL
  have hdimQ : Module.finrank (ZMod 2) ↥(s16smSubmod Y) = 3 :=
    finrank_submod_of_binaryNaturalSL_three hYnat
  have hS : Module.finrank (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) =
      r * Module.finrank (ZMod 2) ↥(s16smSubmod Y) := by
    rw [← Φ.finrank_eq, CommutingFactor.finrank_fin_fun_eq]
  rw [hdimS, hdimQ] at hS
  have hr3 : r = 3 := by omega
  subst hr3
  refine ⟨Φ, hΦ, ?_⟩
  exact (CommutingFactor.tensor_case (submod_invariant_D h hYirr) Φ (quotK_commutes_quotD h)
    (hirr_quot h h7 hL) (s16smSubmod_ne_bot_of_isIrr hYirr) hΦ (by norm_num)
    (commutantD_eq_bot h hYirr he htheta)).1

private theorem evalHom_map_lTensor (h : ThreeNat A L T)
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hYirr : XMod.IsIrr ↥L Y)
    (d : ↥(quotD h)) (t : ↥(s16smSubmod Y) ⊗[ZMod 2] ↥(CommutingFactor.homD
      (submod_invariant_D h hYirr))) :
    CommutingFactor.evalHom (submod_invariant_D h hYirr)
        (TensorProduct.map (CommutingFactor.resD (submod_invariant_D h hYirr) d)
          LinearMap.id t) =
      (d.1 : Module.End (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))))
        (CommutingFactor.evalHom (submod_invariant_D h hYirr) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul q f =>
    rw [TensorProduct.map_tmul, CommutingFactor.evalHom_tmul, CommutingFactor.evalHom_tmul]
    exact f.2 d q
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

private theorem evalHom_map_rTensor (h : ThreeNat A L T)
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hYirr : XMod.IsIrr ↥L Y)
    (x : ↥(quotK h)) (t : ↥(s16smSubmod Y) ⊗[ZMod 2] ↥(CommutingFactor.homD
      (submod_invariant_D h hYirr))) :
    CommutingFactor.evalHom (submod_invariant_D h hYirr)
        (TensorProduct.map LinearMap.id (CommutingFactor.homAct (quotK_commutes_quotD h)
          (submod_invariant_D h hYirr) x) t) =
      (x.1 : Module.End (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))))
        (CommutingFactor.evalHom (submod_invariant_D h hYirr) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul q f => rfl
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

private theorem exists_qW_data (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (hL : IsL3 ↥L 1) {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))}
    (hYirr : XMod.IsIrr ↥L Y)
    (hYnat : BinaryNaturalSL (quotLImage h) Y ⊥ 3 1)
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(quotLImage h)}
    {e : ↥Y ≃* Multiplicative (Fin 3 → ZMod 2)}
    (he : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥Y)
      (hu : ((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
        (u : V ⧸ modFix L (⊤ : Subgroup V)) ∈ Y),
      e ⟨((π γ : ↥(quotLImage h)) : MulAut (V ⧸ modFix L (⊤ : Subgroup V)))
          (u : V ⧸ modFix L (⊤ : Subgroup V)), hu⟩ =
        natAct (StatedSL 3 (ZMod 2)) γ (e u))
    {theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2))}
    (htheta : ∀ l : ↥L, π (theta l) = (quotLActionHom h).rangeRestrict l) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (ZMod 2) X) (_ : Finite X)
      (kappaX : Representation (ZMod 2) ↥(s1t3KBar A L) X)
      (qW : Additive V →ₗ[ZMod 2] ↥(s16smSubmod Y) ⊗[ZMod 2] X),
      Module.finrank (ZMod 2) X = 3 ∧ kappaX.IsIrreducible ∧
        Function.Surjective qW ∧
        LinearMap.ker qW = s16smSubmod (fixV L) ∧
        (∀ (l : ↥L) (w : Additive V),
          qW (s16smRepW (MonoidHom.id ↥L) l w) =
            TensorProduct.map (rhoQOf h hYirr l) LinearMap.id (qW w)) ∧
        (∀ (k : ↥(s1t3KBar A L)) (w : Additive V),
          qW (s16smRepW (MonoidHom.id ↥(s1t3KBar A L)) k w) =
            TensorProduct.map LinearMap.id (kappaX k) (qW w)) := by
  have hDI := submod_invariant_D h hYirr
  have hCD := quotK_commutes_quotD h
  obtain ⟨Φ, hΦ, hbij⟩ := exists_eval_data h h7 hL hYirr hYnat he htheta
  have hbot := commutantD_eq_bot h hYirr he htheta
  obtain ⟨hbijE, hDev, hXev, hinjX, hntriv, hinvSub⟩ :=
    CommutingFactor.tensor_case hDI Φ hCD (hirr_quot h h7 hL)
      (s16smSubmod_ne_bot_of_isIrr hYirr) hΦ (by norm_num) hbot
  haveI : Finite ↥(s16smSubmod Y) := inferInstance
  haveI : Finite (Additive (V ⧸ modFix L (⊤ : Subgroup V))) := inferInstance
  haveI : Finite (↥(s16smSubmod Y) → Additive (V ⧸ modFix L (⊤ : Subgroup V))) := inferInstance
  haveI : Finite (↥(s16smSubmod Y) →ₗ[ZMod 2]
      Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
    Finite.of_injective (fun f : ↥(s16smSubmod Y) →ₗ[ZMod 2]
      Additive (V ⧸ modFix L (⊤ : Subgroup V)) => (f : ↥(s16smSubmod Y) → _))
      (fun f g h => LinearMap.ext (congrFun h))
  haveI : Finite ↥(CommutingFactor.homD hDI) := Finite.of_injective _ Subtype.val_injective
  let ev : ↥(s16smSubmod Y) ⊗[ZMod 2] ↥(CommutingFactor.homD hDI) ≃ₗ[ZMod 2]
      Additive (V ⧸ modFix L (⊤ : Subgroup V)) :=
    LinearEquiv.ofBijective (CommutingFactor.evalHom hDI) hbijE
  have hX3 : Module.finrank (ZMod 2) ↥(CommutingFactor.homD hDI) = 3 := by
    obtain ⟨eX⟩ := CommutingFactor.homD_equiv_pi hDI Φ hΦ
    haveI : Nontrivial ↥(s16smSubmod Y) :=
      Submodule.nontrivial_iff_ne_bot.mpr (s16smSubmod_ne_bot_of_isIrr hYirr)
    have hcard1 : Nat.card ↥(CommutingFactor.commutantD hDI) = 2 := by
      rw [hbot, Nat.card_congr (Algebra.botEquiv (ZMod 2)
        (Module.End (ZMod 2) ↥(s16smSubmod Y))).toEquiv, Nat.card_zmod]
    have hcard : Nat.card ↥(CommutingFactor.homD hDI) = 8 := by
      rw [Nat.card_congr eX.toEquiv, Nat.card_fun, hcard1]
      norm_num
    have h2 : Nat.card ↥(CommutingFactor.homD hDI) =
        2 ^ Module.finrank (ZMod 2) ↥(CommutingFactor.homD hDI) := by
      haveI : Module.Finite (ZMod 2) ↥(CommutingFactor.homD hDI) := Module.Finite.of_finite
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(CommutingFactor.homD hDI))
      rwa [Nat.card_zmod] at h
    rw [hcard] at h2
    exact (Nat.pow_right_injective (a := 2) (by norm_num) h2).symm
  let qW : Additive V →ₗ[ZMod 2] ↥(s16smSubmod Y) ⊗[ZMod 2] ↥(CommutingFactor.homD hDI) :=
    ev.symm.toLinearMap.comp (quotFixMap (L := L))
  have hqWev : ∀ x : Additive V, ev (qW x) = quotFixMap (L := L) x := fun x =>
    LinearEquiv.apply_symm_apply ev (quotFixMap (L := L) x)
  have hevEq : ∀ t, ev t = CommutingFactor.evalHom hDI t := fun t => rfl
  have hqWevE : ∀ x : Additive V, CommutingFactor.evalHom hDI (qW x) =
      quotFixMap (L := L) x := fun x => hqWev x
  have hqWL : ∀ (l : ↥L) (w : Additive V),
      qW (s16smRepW (MonoidHom.id ↥L) l w) =
        TensorProduct.map (rhoQOf h hYirr l) LinearMap.id (qW w) := by
    intro l w
    apply ev.injective
    rw [hqWev]
    have h1 : quotFixMap (L := L) (s16smRepW (MonoidHom.id ↥L) l w) =
        quotAlphaL h l (quotFixMap (L := L) w) := by
      have h2 := quotRepT_apply (L := L) (T := A) h.normal
        (Subgroup.inclusion h.le l) (Additive.toMul w)
      rwa [quotFixMap_apply, quotFixMap_apply] at h2
    rw [h1]
    have hLmap : CommutingFactor.evalHom hDI
        (TensorProduct.map (rhoQOf h hYirr l) LinearMap.id (qW w)) =
        quotAlphaL h l (CommutingFactor.evalHom hDI (qW w)) := by
      have h4 := evalHom_map_lTensor h hYirr ⟨(quotAlphaL h).asGroupHom l, ⟨l, rfl⟩⟩ (qW w)
      rwa [show (CommutingFactor.resD hDI ⟨(quotAlphaL h).asGroupHom l, ⟨l, rfl⟩⟩ :
          Module.End (ZMod 2) ↥(s16smSubmod Y)) = rhoQOf h hYirr l from rfl] at h4
    rw [hevEq, hLmap, hqWevE w]
  have hqWK : ∀ (k : ↥(s1t3KBar A L)) (w : Additive V),
      qW (s16smRepW (MonoidHom.id ↥(s1t3KBar A L)) k w) =
        TensorProduct.map LinearMap.id (CommutingFactor.homAct hCD hDI
          ⟨(quotAlphaK h).asGroupHom k, ⟨k, rfl⟩⟩) (qW w) := by
    intro k w
    apply ev.injective
    rw [hqWev]
    have h1 : quotFixMap (L := L) (s16smRepW (MonoidHom.id ↥(s1t3KBar A L)) k w) =
        quotAlphaK h k (quotFixMap (L := L) w) := by
      have h2 := quotRepT_apply (L := L) (T := A) h.normal
        (Subgroup.inclusion inf_le_left k) (Additive.toMul w)
      rwa [quotFixMap_apply, quotFixMap_apply] at h2
    rw [h1]
    have hKmap : CommutingFactor.evalHom hDI
        (TensorProduct.map LinearMap.id (CommutingFactor.homAct hCD hDI
          ⟨(quotAlphaK h).asGroupHom k, ⟨k, rfl⟩⟩) (qW w)) =
        quotAlphaK h k (CommutingFactor.evalHom hDI (qW w)) :=
      evalHom_map_rTensor h hYirr ⟨(quotAlphaK h).asGroupHom k, ⟨k, rfl⟩⟩ (qW w)
    rw [hevEq, hKmap, hqWevE w]
  letI : AddCommGroup ↥(CommutingFactor.homD hDI) :=
    Submodule.addCommGroup (p := CommutingFactor.homD hDI)
  letI : Module (ZMod 2) ↥(CommutingFactor.homD hDI) :=
    Submodule.module (p := CommutingFactor.homD hDI)
  letI : Nontrivial ↥(CommutingFactor.homD hDI) := hntriv
  let kappaX : Representation (ZMod 2) ↥(s1t3KBar A L) ↥(CommutingFactor.homD hDI) :=
    (CommutingFactor.homAct hCD hDI).comp ((quotAlphaK h).asGroupHom.rangeRestrict)
  have hXirr : kappaX.IsIrreducible := by
    refine CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule (k := ZMod 2)
      (G := ↥(s1t3KBar A L)) (V := ↥(CommutingFactor.homD hDI)) kappaX ?_
    intro U hU
    exact hinvSub U (fun x f hf => by
      obtain ⟨k, hk⟩ := MonoidHom.rangeRestrict_surjective ((quotAlphaK h).asGroupHom) x
      rw [← hk]
      exact hU k f hf)
  refine ⟨↥(CommutingFactor.homD hDI), inferInstance, inferInstance, inferInstance, kappaX, qW,
    hX3, hXirr, ?_, ?_, hqWL, ?_⟩
  ·
    intro t
    obtain ⟨x, hx⟩ := quotFixMap_surjective (L := L) (ev t)
    exact ⟨x, by apply ev.injective; rw [hqWev, hx]⟩
  ·
    ext x
    rw [LinearMap.mem_ker, ← quotFixMap_eq_zero_iff]
    constructor
    · intro h
      rw [← hqWev x, h, map_zero]
    · intro h
      apply ev.injective
      rw [hqWev x, h, map_zero]
  ·
    intro k w
    exact hqWK k w

private theorem exists_dual_model (h : ThreeNat A L T)
    {Y : Subgroup (V ⧸ modFix L (⊤ : Subgroup V))} (hYirr : XMod.IsIrr ↥L Y)
    {cq : ↥(s16smSubmod Y) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)}
    {theta : ↥L ≃* ↥(StatedSL 3 (ZMod 2))}
    (hcq : ∀ (l : ↥L) (q : ↥(s16smSubmod Y)),
      cq (rhoQOf h hYirr l q) =
        (((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ cq q)) :
    Explicit.BinaryNaturalSL (Representation.dual (rhoQOf h hYirr)) 3 (ZMod 2) .dual := by
  show (FFModel.dualNat (StatedSL 3 (ZMod 2))).IsModel (Representation.dual (rhoQOf h hYirr))
  let cqA : ↥(s16smSubmod Y) ≃+ (Fin 3 → ZMod 2) := cq.toAddEquiv
  letI modN : Module (ZMod 2) (Fin 3 → ZMod 2) := by
    letI : Module (ZMod 2) (ZMod 2) := (ZMod.algebra (ZMod 2) 2).toModule
    infer_instance
  let cqNat : ↥(s16smSubmod Y) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { cqA with
      map_smul' := fun c x =>
        @ZMod.map_smul 2 ↥(s16smSubmod Y) (Fin 3 → ZMod 2)
          (↥(s16smSubmod Y) ≃+ (Fin 3 → ZMod 2)) _ _ _ _ _ modN cqA c x }
  let delta := Module.Dual.congr cqNat
  have hcqNat : ∀ (l : ↥L) (q : ↥(s16smSubmod Y)),
      cqNat (rhoQOf h hYirr l q) =
        (((theta l : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ cqNat q) := by
    intro l q
    show cqA (rhoQOf h hYirr l q) = _
    exact hcq l q
  have hδeq : ∀ (γ : ↥L) (w : Module.Dual (ZMod 2) ↥(s16smSubmod Y)),
      delta (Representation.dual (rhoQOf h hYirr) γ w) =
        Representation.dual (CFSG.Quasithin.SLCover.natRepQ 3 (ZMod 2)) (theta γ) (delta w) := by
    intro γ w
    apply LinearMap.ext
    intro v
    have h1 := hcqNat γ⁻¹ (cqNat.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    show w (rhoQOf h hYirr γ⁻¹ (cqNat.symm v)) =
      w (cqNat.symm ((((theta γ)⁻¹ : ↥(StatedSL 3 (ZMod 2))) :
        Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) *ᵥ v))
    rw [show rhoQOf h hYirr γ⁻¹ (cqNat.symm v) =
        cqNat.symm ((((theta γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) *ᵥ v)) from by
      rw [← h1, LinearEquiv.symm_apply_apply]]
    have hinv : ((theta γ)⁻¹ : ↥(StatedSL 3 (ZMod 2))) = theta γ⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
    rw [show (((theta γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((((theta γ)⁻¹ : ↥(StatedSL 3 (ZMod 2))) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) from congrArg
          (fun g : ↥(StatedSL 3 (ZMod 2)) =>
            ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
          hinv.symm]
  obtain ⟨θ₀, β₀, h1, h2, h3, h4⟩ := CFSG.Quasithin.SLCover.binaryNaturalSL_dual (d := 3)
    (F := ZMod 2)
  refine ⟨theta.trans θ₀, delta.toAddEquiv.trans β₀, h1, h2, h3, ?_⟩
  intro γ w m hm hw
  have h4' := h4 (theta γ) (delta w) m hm hw
  change β₀ (delta (((rhoQOf h hYirr).dual γ) w)) =
    Additive.ofMul (QuotientGroup.mk ⟨(Explicit.natDual (StatedSL 3 (ZMod 2))
      Explicit.NatDual.dual).act (θ₀ (theta γ))
      ((m : ↥(FFModel.dualNat (StatedSL 3 (ZMod 2))).sec) :
        (FFModel.dualNat (StatedSL 3 (ZMod 2))).Amb), hm⟩ :
      (Explicit.natDual (StatedSL 3 (ZMod 2)) Explicit.NatDual.dual).Sec)
  rw [← h4', hδeq γ w]

end Model

theorem ThreeNat.exists_naturalThreeMultiplicityData
    {V : Type} [CommGroup V] [Finite V] {A L T : Subgroup (MulAut V)}
    (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) (hL : IsL3 ↥L 1) :
    letI := MulAutTwo.zmod2Module h.elem
    Nonempty (NaturalThreeMultiplicityData A L) := by
  letI : Module (ZMod 2) (Additive V) := MulAutTwo.zmod2Module h.elem
  letI : Module (ZMod 2) (Additive (V ⧸ modFix L (⊤ : Subgroup V))) :=
    quotFixModule (L := L) h.elem
  obtain ⟨I₀, hnat₀, hYirr, hind, htop⟩ := s16t3_quot_summands h.quasi h.sum
  have hb : BinaryNaturalSL L (I₀ 0) (fixV L) 3 1 :=
    s16t3_sumOfNat_one (SumOfNatShape.sl3_of_card_eq_168 h.quasi
      (CFSG.LocalAnalysis.WeakClosure81.card_eq_of_isL3 hL) (hnat₀ 0))
  have hbq : BinaryNaturalSL (quotLImage h) (tilde L (⊤ : Subgroup V) (I₀ 0)) ⊥ 3 1 :=
    binaryNaturalSL_tilde h hb
  obtain ⟨π, hπ⟩ := CFSG.Quasithin.FFC.BinaryNaturalSL.exists_zmod hbq
  obtain ⟨e, he⟩ := CFSG.Quasithin.B5.exists_linModel hπ
  obtain ⟨theta, htheta⟩ := exists_theta h hL hπ.1
  obtain ⟨X, xAdd, xModule, xFinite, kappaX, qW, hX3, hXirr, hqWsurj, hker, hqWL, hqWK⟩ :=
    exists_qW_data h h7 hL (hYirr 0) hbq he htheta
  have hdual : Explicit.BinaryNaturalSL (Representation.dual (rhoQOf h (hYirr 0))) 3 (ZMod 2) .dual :=
    exists_dual_model h (hYirr 0) (cq := coordQOf (L := L) e) (theta := theta)
      (coordQOf_rhoQOf h (hYirr 0) he htheta)
  letI : AddCommGroup X := xAdd
  letI : Module (ZMod 2) X := xModule
  letI : Finite X := xFinite
  exact ⟨{
    Q := ↥(s16smSubmod (tilde L (⊤ : Subgroup V) (I₀ 0)))
    X := X
    rhoQ := rhoQOf h (hYirr 0)
    theta := theta
    coordQ := coordQOf (L := L) e
    coordQ_apply := fun l q => coordQOf_rhoQOf h (hYirr 0) he htheta l q
    dual_model := hdual
    no_fixed_Q := no_fixed_Q_of h (hYirr 0) hbq
    no_invariant_Q := no_invariant_Q_of h (hYirr 0) hbq
    kappaX := kappaX
    finrank_X := hX3
    irreducible_X := hXirr
    kappaZ := kappaZOfThreeNat h
    kappaZ_apply := fun k z => kappaZOfThreeNat_apply h k z
    qW := qW
    qW_surjective := hqWsurj
    ker_qW := hker
    qW_L := hqWL
    qW_K := hqWK
    no_invariant_W := no_invariant_W_of_threeNat h
  }⟩
