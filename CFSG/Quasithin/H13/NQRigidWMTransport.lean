module

public import CFSG.Quasithin.H13.NQRigidModule
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.NQSetup (QTNQNaturalFour QTNQNaturalThreeDouble
  QTNQNaturalThreeExtension)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)

variable {G : Type} [Group G]

structure WMDatum (L M : Subgroup G) (X : Type) [CommGroup X] where
  ι : X →* G
  inj : Function.Injective ι
  φ : ↥L →* MulAut X
  comp : ∀ (l : ↥L) (x : X), ι (φ l x) = (l : G) * ι x * (l : G)⁻¹
  ker : φ.ker = CFSG.solvableRadical L
  img : (commV φ.range).map ι = qtnqU L M

namespace WMDatum

variable {L M : Subgroup G} {X : Type} [CommGroup X] (D : WMDatum L M X)

@[expose] noncomputable def radEquiv : (L ⧸ CFSG.solvableRadical L) ≃* D.φ.range :=
  (QuotientGroup.quotientMulEquivOfEq D.ker.symm).trans (QuotientGroup.quotientKerEquivRange D.φ)

@[expose] noncomputable def uEquiv : ↥(commV D.φ.range) ≃* ↥(qtnqU L M) :=
  ((commV D.φ.range).equivMapOfInjective D.ι D.inj).trans (MulEquiv.subgroupCongr D.img)

theorem uEquiv_coe (u : ↥(commV D.φ.range)) : ((D.uEquiv u : qtnqU L M) : G) = D.ι u :=
  rfl

theorem act_symm {l : L} {x y : qtnqU L M} (hxy : (y : G) = (l : G) * x * (l : G)⁻¹) :
    D.φ l ((D.uEquiv.symm x : commV D.φ.range) : X) =
      ((D.uEquiv.symm y : commV D.φ.range) : X) := by
  apply D.inj
  rw [D.comp, ← uEquiv_coe, ← uEquiv_coe, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    hxy]

theorem act_symm' {ψ : MulAut X} {l : L} (hψ : ψ = D.φ l) {x y : qtnqU L M}
    (hxy : (y : G) = (l : G) * x * (l : G)⁻¹) :
    ψ ((D.uEquiv.symm x : commV D.φ.range) : X) = ((D.uEquiv.symm y : commV D.φ.range) : X) := by
  rw [hψ]
  exact D.act_symm hxy

theorem conj_eq_of_fix {u : ↥(commV D.φ.range)} (hu : (u : X) ∈ fixV D.φ.range) (l : L) :
    (l : G) * (D.uEquiv u : G) * (l : G)⁻¹ = D.uEquiv u := by
  rw [uEquiv_coe, ← D.comp]
  exact congrArg D.ι (hu _ ⟨l, rfl⟩)

@[expose] noncomputable def modelEquiv {Dm : FFModel} (hDm : Dm.Faithful) {U' Z' : Subgroup X}
    {π : Dm.Gam →* ↥D.φ.range} (h : Dm.RealizesVia D.φ.range U' Z' π) : Dm.Gam ≃* D.φ.range :=
  MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec hDm h, h.1⟩

theorem modelEquiv_apply {Dm : FFModel} (hDm : Dm.Faithful) {U' Z' : Subgroup X}
    {π : Dm.Gam →* ↥D.φ.range} (h : Dm.RealizesVia D.φ.range U' Z' π) (l : L) :
    ((π ((D.modelEquiv hDm h).symm (D.radEquiv (l : L ⧸ CFSG.solvableRadical L))) :
      D.φ.range) : MulAut X) = D.φ l := by
  have : π ((D.modelEquiv hDm h).symm (D.radEquiv (l : L ⧸ CFSG.solvableRadical L))) =
      D.radEquiv (l : L ⧸ CFSG.solvableRadical L) :=
    (D.modelEquiv hDm h).apply_symm_apply _
  rw [this]
  rfl

end WMDatum

section Linear

@[expose] noncomputable def statedSLLinEquiv (n : ℕ) (F : Type) [Field F] :
    ↥(StatedSL n F) ≃* SpecialLinearGroup F (Fin n → F) :=
  (specialLinearGroupEquivStatedSL n F).symm.trans Matrix.SpecialLinearGroup.toLin'_equiv

theorem statedSLLinEquiv_apply (n : ℕ) (F : Type) [Field F] (γ : ↥(StatedSL n F))
    (v : Fin n → F) :
    (statedSLLinEquiv n F γ : (Fin n → F) ≃ₗ[F] (Fin n → F)) v =
      (((γ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F).mulVec v := by
  set A := (specialLinearGroupEquivStatedSL n F).symm γ with hA
  have h1 : specialLinearGroupEquivStatedSL n F A = γ := MulEquiv.apply_symm_apply _ _
  have h2 := specialLinearGroupEquivStatedSL_coe n F A
  rw [h1] at h2
  rw [h2]
  rfl

theorem statedSL_zmod_eq_top (n : ℕ) : StatedSL n (ZMod 2) = ⊤ :=
  eq_top_iff.mpr fun x _ => FFC.mem_statedSL_zmod x

@[expose] noncomputable def statedSLZModLinEquiv (n : ℕ) :
    ↥(StatedSL n (ZMod 2)) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
  ((MulEquiv.subgroupCongr (statedSL_zmod_eq_top n)).trans Subgroup.topEquiv).trans
    (Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _))

theorem statedSLZModLinEquiv_apply (n : ℕ) (γ : ↥(StatedSL n (ZMod 2))) (v : Fin n → ZMod 2) :
    statedSLZModLinEquiv n γ v =
      (((γ : GL (Fin n) (ZMod 2))) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v :=
  rfl

@[expose] def coreAddEquiv (n : ℕ) : Additive ↥(G6.coreMod n) ≃+ ↥(evenWeight (Fin n)) where
  toFun x := ⟨Multiplicative.toAdd ((Additive.toMul x : G6.coreMod n) : G6.PermMod n),
    (Additive.toMul x).2⟩
  invFun v := Additive.ofMul ⟨Multiplicative.ofAdd (v : Fin n → ZMod 2), v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Linear

namespace WMDatum

variable {L M : Subgroup G} {X : Type} [CommGroup X] (D : WMDatum L M X)

@[expose] noncomputable def addMap {A : Type} [AddCommGroup A]
    (f : ↥(commV D.φ.range) →* Multiplicative A) : Additive ↥(qtnqU L M) →+ A where
  toFun x := Multiplicative.toAdd (f (D.uEquiv.symm (Additive.toMul x)))
  map_zero' := by
    show Multiplicative.toAdd (f (D.uEquiv.symm 1)) = 0
    rw [map_one, map_one, toAdd_one]
  map_add' x y := by
    show Multiplicative.toAdd (f (D.uEquiv.symm (Additive.toMul x * Additive.toMul y))) = _
    rw [map_mul, map_mul, toAdd_mul]

theorem addMap_apply {A : Type} [AddCommGroup A] (f : ↥(commV D.φ.range) →* Multiplicative A)
    (x : qtnqU L M) :
    D.addMap f (Additive.ofMul x) = Multiplicative.toAdd (f (D.uEquiv.symm x)) :=
  rfl

theorem addMap_surjective {A : Type} [AddCommGroup A]
    {f : ↥(commV D.φ.range) →* Multiplicative A} (hf : Function.Surjective f) :
    Function.Surjective (D.addMap f) := by
  intro v
  obtain ⟨u, hu⟩ := hf (Multiplicative.ofAdd v)
  refine ⟨Additive.ofMul (D.uEquiv u), ?_⟩
  rw [addMap_apply, MulEquiv.symm_apply_apply, hu, toAdd_ofAdd]

theorem addMap_ker {A : Type} [AddCommGroup A] {f : ↥(commV D.φ.range) →* Multiplicative A}
    (hfk : ∀ u : ↥(commV D.φ.range), f u = 1 → (u : X) ∈ fixV D.φ.range) (l : L)
    (x : qtnqU L M) (hx : D.addMap f (Additive.ofMul x) = 0) :
    (l : G) * x * (l : G)⁻¹ = x := by
  have h1 : f (D.uEquiv.symm x) = 1 := by
    rw [addMap_apply] at hx
    exact Multiplicative.toAdd.injective (by rw [hx]; rfl)
  have h3 := D.conj_eq_of_fix (hfk _ h1) l
  rwa [MulEquiv.apply_symm_apply] at h3

theorem naturalFour
    (h : BinaryNaturalSL D.φ.range (commV D.φ.range) (fixV D.φ.range ⊓ commV D.φ.range) 2 2) :
    QTNQNaturalFour L M := by
  classical
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  set πe := D.modelEquiv (FFModel.nat_faithful _) hπ with hπe
  refine ⟨F, inferInstance, inferInstance, ?_, Fin 2 → F, inferInstance, inferInstance,
    Module.finrank_fin_fun F, D.radEquiv.trans (πe.symm.trans (statedSLLinEquiv 2 F)), D.addMap f,
    D.addMap_surjective hfs, ?_, fun l x hx => D.addMap_ker (fun u hu => ((hfk u).mp hu).1) l x hx⟩
  · rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  · intro l x y hxy
    set γ := πe.symm (D.radEquiv (l : L ⧸ CFSG.solvableRadical L)) with hγ
    have hγl : ((π γ : D.φ.range) : MulAut X) = D.φ l := D.modelEquiv_apply _ hπ l
    have hu : ((π γ : D.φ.range) : MulAut X) ((D.uEquiv.symm x : commV D.φ.range) : X) ∈
        commV D.φ.range := by
      rw [hγl, D.act_symm hxy]
      exact (D.uEquiv.symm y).2
    have h1 := hfe γ (D.uEquiv.symm x) hu
    have h2 : (⟨((π γ : D.φ.range) : MulAut X) ((D.uEquiv.symm x : commV D.φ.range) : X), hu⟩ :
        commV D.φ.range) = D.uEquiv.symm y := Subtype.ext (D.act_symm' hγl hxy)
    have h1' : f (D.uEquiv.symm y) = natAct _ γ (f (D.uEquiv.symm x)) := by
      rw [← h2]
      exact h1
    rw [addMap_apply, addMap_apply, h1']
    exact (statedSLLinEquiv_apply 2 F γ _).symm

theorem naturalThreeExtension
    (h : BinaryNaturalSL D.φ.range (commV D.φ.range) (fixV D.φ.range ⊓ commV D.φ.range) 3 1) :
    QTNQNaturalThreeExtension L M := by
  classical
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  set πe := D.modelEquiv (FFModel.nat_faithful _) hπ with hπe
  let β : (L ⧸ CFSG.solvableRadical L) ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    D.radEquiv.trans (πe.symm.trans (statedSLZModLinEquiv 3))
  refine ⟨Fin 3 → ZMod 2, _, _, Module.finrank_fin_fun (ZMod 2), β, D.addMap f,
    D.addMap_surjective hfs, ?_, fun l x hx => D.addMap_ker (fun u hu => ((hfk u).mp hu).1) l x hx⟩
  intro l x y hxy
  set γ := πe.symm (D.radEquiv (l : L ⧸ CFSG.solvableRadical L)) with hγ
  have hγl : ((π γ : D.φ.range) : MulAut X) = D.φ l := D.modelEquiv_apply _ hπ l
  have hu : ((π γ : D.φ.range) : MulAut X) ((D.uEquiv.symm x : commV D.φ.range) : X) ∈
      commV D.φ.range := by
    rw [hγl, D.act_symm hxy]
    exact (D.uEquiv.symm y).2
  have h1 := hfe γ (D.uEquiv.symm x) hu
  have h2 : (⟨((π γ : D.φ.range) : MulAut X) ((D.uEquiv.symm x : commV D.φ.range) : X), hu⟩ :
      commV D.φ.range) = D.uEquiv.symm y := Subtype.ext (D.act_symm' hγl hxy)
  have h1' : f (D.uEquiv.symm y) = natAct _ γ (f (D.uEquiv.symm x)) := by
    rw [← h2]
    exact h1
  show Multiplicative.toAdd (f (D.uEquiv.symm y)) = β _ (Multiplicative.toAdd (f (D.uEquiv.symm x)))
  rw [h1']
  exact (statedSLZModLinEquiv_apply 3 γ _).symm

theorem deletedFive (h : AlternatingNatural D.φ.range (commV D.φ.range) ⊥ 5) :
    QTNQDeletedFive L M := by
  classical
  obtain ⟨π, hπ⟩ := h
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap
    (CFSG.QuasithinUnique.L246.altDn_ker_eq_bot (by decide : Odd 5)) hπ
  set πe := D.modelEquiv (FFC.altDn_faithful (by norm_num)) hπ with hπe
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).mp hu
    rw [mem_bot] at this
    exact Subtype.ext this
  let fe : ↥(commV D.φ.range) ≃* ↥(G6.coreMod 5) := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨Fin 5, inferInstance, inferInstance, Fintype.card_fin 5, D.radEquiv.trans πe.symm,
    (MulEquiv.toAdditive (D.uEquiv.symm.trans fe)).trans (coreAddEquiv 5), ?_⟩
  intro l x y hxy
  set γ := πe.symm (D.radEquiv (l : L ⧸ CFSG.solvableRadical L)) with hγ
  have hγl : ((π γ : D.φ.range) : MulAut X) = D.φ l := D.modelEquiv_apply _ hπ l
  have hu : ((π γ : D.φ.range) : MulAut X) ((D.uEquiv.symm x : commV D.φ.range) : X) ∈
      commV D.φ.range := by
    rw [hγl, D.act_symm hxy]
    exact (D.uEquiv.symm y).2
  have h1 := hfe γ (D.uEquiv.symm x) hu
  have h2 : (⟨((π γ : D.φ.range) : MulAut X) ((D.uEquiv.symm x : commV D.φ.range) : X), hu⟩ :
      commV D.φ.range) = D.uEquiv.symm y := Subtype.ext (D.act_symm' hγl hxy)
  have h1' : (f (D.uEquiv.symm y)).1 = G6.permAct 5 γ.1 (f (D.uEquiv.symm x)).1 := by
    rw [← h2]
    exact h1
  show Multiplicative.toAdd (f (D.uEquiv.symm y)).1 =
    permAct γ.1 (Multiplicative.toAdd (f (D.uEquiv.symm x)).1)
  rw [h1']
  rfl

theorem naturalThreeDouble {I : Fin 2 → Subgroup X} {π : ↥(StatedSL 3 (ZMod 2)) →* ↥D.φ.range}
    (hind : iSupIndep I) (hsup : (⨆ i, I i) = commV D.φ.range)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia D.φ.range (I i) ⊥ π) :
    QTNQNaturalThreeDouble L M := by
  classical
  have hle : ∀ i, I i ≤ commV D.φ.range := fun i => hsup ▸ le_iSup I i
  have hdisj : I 0 ⊓ I 1 = ⊥ :=
    disjoint_iff.mp (hind.pairwiseDisjoint (show (0 : Fin 2) ≠ 1 by decide))
  have hsup2 : I 0 ⊔ I 1 = commV D.φ.range := by
    rw [← hsup]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hmap : ∀ i, ∃ f : ↥(I i) →* Multiplicative (Fin 3 → ZMod 2), Function.Bijective f ∧
      ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥(I i))
        (hu : ((π γ : D.φ.range) : MulAut X) u ∈ I i),
        f ⟨_, hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (f u) := by
    intro i
    obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap (hreal i)
    refine ⟨f, ⟨?_, hfs⟩, hfe⟩
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).mp hu
    rw [mem_bot] at this
    exact Subtype.ext this
  choose f hfb hfe using hmap
  let g : ↥(I 0) × ↥(I 1) →* ↥(commV D.φ.range) :=
    { toFun := fun ab => ⟨(ab.1 : X) * ab.2, mul_mem (hle 0 ab.1.2) (hle 1 ab.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Prod.fst_mul, Prod.snd_mul, coe_mul]
        rw [mul_mul_mul_comm] }
  have hgi : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * b = 1 := congrArg Subtype.val hab
    have h2 : (a : X) ∈ I 0 ⊓ I 1 := by
      refine mem_inf.mpr ⟨a.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (I 1).inv_mem b.2
    rw [hdisj, mem_bot] at h2
    have h3 : (b : X) = 1 := by rw [h2, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hgs : Function.Surjective g := by
    rintro ⟨u, hu⟩
    rw [← hsup2, mem_sup] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := hu
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  let ge : ↥(I 0) × ↥(I 1) ≃* ↥(commV D.φ.range) := MulEquiv.ofBijective g ⟨hgi, hgs⟩
  let fe : ∀ i, ↥(I i) ≃* Multiplicative (Fin 3 → ZMod 2) := fun i =>
    MulEquiv.ofBijective (f i) (hfb i)
  let Θ : ↥(qtnqU L M) ≃* Multiplicative (Fin 3 → ZMod 2) × Multiplicative (Fin 3 → ZMod 2) :=
    D.uEquiv.symm.trans (ge.symm.trans (MulEquiv.prodCongr (fe 0) (fe 1)))
  let θ : Additive ↥(qtnqU L M) ≃+ (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
    { toFun := fun x => (Multiplicative.toAdd (Θ (Additive.toMul x)).1,
        Multiplicative.toAdd (Θ (Additive.toMul x)).2)
      invFun := fun v => Additive.ofMul (Θ.symm (Multiplicative.ofAdd v.1,
        Multiplicative.ofAdd v.2))
      left_inv := fun x => by
        show Additive.ofMul (Θ.symm (Θ (Additive.toMul x))) = x
        rw [MulEquiv.symm_apply_apply]
        rfl
      right_inv := fun v => by
        show (Multiplicative.toAdd (Θ (Θ.symm _)).1, Multiplicative.toAdd (Θ (Θ.symm _)).2) = v
        rw [MulEquiv.apply_symm_apply]
        rfl
      map_add' := fun x y => by
        show (Multiplicative.toAdd (Θ (Additive.toMul x * Additive.toMul y)).1,
          Multiplicative.toAdd (Θ (Additive.toMul x * Additive.toMul y)).2) = _
        rw [map_mul]
        rfl }
  set πe := D.modelEquiv (FFModel.nat_faithful _) (hreal 0) with hπe
  let β : (L ⧸ CFSG.solvableRadical L) ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    D.radEquiv.trans (πe.symm.trans (statedSLZModLinEquiv 3))
  refine ⟨Fin 3 → ZMod 2, _, _, Module.finrank_fin_fun (ZMod 2), β, θ, ?_⟩
  intro l x y hxy
  set γ := πe.symm (D.radEquiv (l : L ⧸ CFSG.solvableRadical L)) with hγ
  have hγl : ((π γ : D.φ.range) : MulAut X) = D.φ l := D.modelEquiv_apply _ (hreal 0) l
  set ab := ge.symm (D.uEquiv.symm x) with hab
  have hx : ((ab.1 : X) * ab.2) = ((D.uEquiv.symm x : commV D.φ.range) : X) := by
    have := ge.apply_symm_apply (D.uEquiv.symm x)
    exact congrArg Subtype.val this
  have hinv : ∀ i, ∀ u ∈ I i, ((π γ : D.φ.range) : MulAut X) u ∈ I i := fun i u hu =>
    (hreal i).2.2.2.1 (π γ) u hu
  set a' : ↥(I 0) := ⟨_, hinv 0 ab.1 ab.1.2⟩ with ha'
  set b' : ↥(I 1) := ⟨_, hinv 1 ab.2 ab.2.2⟩ with hb'
  have hy : ge (a', b') = D.uEquiv.symm y := by
    apply Subtype.ext
    show ((π γ : D.φ.range) : MulAut X) ab.1 * ((π γ : D.φ.range) : MulAut X) ab.2 = _
    rw [← map_mul, hx, hγl, D.act_symm hxy]
  have hy' : ge.symm (D.uEquiv.symm y) = (a', b') := by
    rw [← hy, MulEquiv.symm_apply_apply]
  have h1 := hfe 0 γ ab.1 (hinv 0 ab.1 ab.1.2)
  have h2 := hfe 1 γ ab.2 (hinv 1 ab.2 ab.2.2)
  show (Multiplicative.toAdd ((fe 0) (ge.symm (D.uEquiv.symm y)).1),
    Multiplicative.toAdd ((fe 1) (ge.symm (D.uEquiv.symm y)).2)) =
    (statedSLZModLinEquiv 3 γ (Multiplicative.toAdd ((fe 0) ab.1)),
      statedSLZModLinEquiv 3 γ (Multiplicative.toAdd ((fe 1) ab.2)))
  rw [hy']
  show (Multiplicative.toAdd (f 0 a'), Multiplicative.toAdd (f 1 b')) = _
  rw [h1, h2]
  exact Prod.ext (statedSLZModLinEquiv_apply 3 γ _).symm (statedSLZModLinEquiv_apply 3 γ _).symm

end WMDatum

end CFSG.Quasithin.H13.NQRigid
