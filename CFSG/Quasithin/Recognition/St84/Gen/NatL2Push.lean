module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannBridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRCor
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannSec
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRNat
import CFSG.Quasithin.EmptyFaithful.SzN6Borel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Push
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  CFSG.Quasithin.F53Mod
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem alpha_ker_eq_pCoreOf {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2] (α : ↥X →* SL(2, F))
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    α.ker = (pCoreOf 2 X).subgroupOf X := by
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  ext g
  change g ∈ α.ker ↔ g ∈ (pCoreOf 2 X).subgroupOf X
  rw [hαk, mem_centralizer_subgroupOf_iff hZX, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    rw [← h.cent_eq]
    exact ⟨g.2, hg⟩
  · intro hg
    rw [← h.cent_eq] at hg
    exact hg.2

private theorem z_ne_bot_of_surjective {X Z : Subgroup G} {F : Type} [Field F]
    (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hβ : Function.Surjective β) : Z ≠ ⊥ := by
  intro hZ
  have hV : Z.subgroupOf X = ⊥ := by rw [hZ, Subgroup.bot_subgroupOf]
  haveI : Subsingleton ↥(Z.subgroupOf X) := by rw [hV]; infer_instance
  haveI hsub : Subsingleton (Multiplicative (Fin 2 → F)) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hβ a
      obtain ⟨y, rfl⟩ := hβ b
      rw [Subsingleton.elim x y]⟩
  exact (not_subsingleton (Multiplicative (Fin 2 → F))) hsub

private theorem map_sylow {X P : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hP : IsSylowTwoOf P X) (α : ↥X →* SL(2, F)) (hα : Function.Surjective α) :
    IsSylowTwoOf ((P.subgroupOf X).map α) ⊤ :=
  CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hP) α hα

theorem beta_ker_eq_zZero {X Z : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X)) :
    β.ker = ((zZero X Z).subgroupOf X).subgroupOf (Z.subgroupOf X) := by
  ext v
  change v ∈ β.ker ↔
    v ∈ ((zZero X Z).subgroupOf X).subgroupOf (Z.subgroupOf X)
  rw [hβk, Subgroup.mem_subgroupOf, mem_centralizer_oddOrder_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hv
    exact ⟨Subgroup.mem_subgroupOf.mp v.2, hv⟩
  · rintro ⟨-, hv⟩
    exact hv

private theorem natCard_fixed_uElt {F : Type} [Field F] [Finite F] {t : F} (ht : t ≠ 0) :
    Nat.card {v : Fin 2 → F // (uElt t) • v = v} = Nat.card F := by
  classical
  let e₁ : {v : Fin 2 → F // (uElt t) • v = v} ≃
      {v : Fin 2 → F // t * v 1 = 0} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun v => uElt_smul_eq_iff t v)
  let e : {v : Fin 2 → F // t * v 1 = 0} ≃ F :=
    { toFun := fun v => v.1 0
      invFun := fun a => ⟨![a, 0], by simp⟩
      left_inv := by
        intro v
        apply Subtype.ext
        have h1 : v.1 1 = 0 := (mul_eq_zero.mp v.2).resolve_left ht
        ext i
        fin_cases i
        · simp
        · simpa [eq_comm] using h1
      right_inv := by
        intro a
        simp }
  exact Nat.card_congr (e₁.trans e)

private theorem natCard_fixed_conj {F : Type} [Field F] [Finite F]
    (x g : SL(2, F)) :
    Nat.card {v : Fin 2 → F // (x * g * x⁻¹) • v = v} =
      Nat.card {v : Fin 2 → F // g • v = v} := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun v => ⟨x⁻¹ • v.1, ?_⟩
      invFun := fun v => ⟨x • v.1, ?_⟩
      left_inv := fun v => by apply Subtype.ext; simp
      right_inv := fun v => by apply Subtype.ext; simp }
  · have h1 : (x * g * x⁻¹) • v.1 = v.1 := v.2
    have h2 : x⁻¹ • ((x * g * x⁻¹) • v.1) = x⁻¹ • v.1 := by rw [h1]
    simpa [mul_smul] using h2
  · have h1 : g • v.1 = v.1 := v.2
    rw [mul_smul, mul_smul, inv_smul_smul, h1]

private theorem exists_conj_uElt_of_mem_sylow {F : Type} [Field F] [Finite F] [CharP F 2]
    {S : Subgroup SL(2, F)} (hS : IsSylowTwoOf S ⊤) {γ : SL(2, F)}
    (hγS : γ ∈ S) (hγ : γ ≠ 1) :
    ∃ (x : SL(2, F)) (t : F), t ≠ 0 ∧ γ = x * uElt t * x⁻¹ := by
  classical
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent S hS.2.1
  have hmem : x⁻¹ * γ * x ∈ S.map (MulAut.conj x⁻¹).toMonoidHom := by
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hγS
  have hxγ : x⁻¹ * γ * x ∈ (upperUnipotent (F := F)).range := hx hmem
  obtain ⟨t, ht⟩ := (mem_rootGroup_iff (x⁻¹ * γ * x)).mp hxγ
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hγ
    have h1 : x⁻¹ * γ * x = 1 := by rw [ht, ht0, uElt_zero]
    calc γ = x * (x⁻¹ * γ * x) * x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  refine ⟨x, t, ht0, ?_⟩
  calc γ = x * (x⁻¹ * γ * x) * x⁻¹ := by group
    _ = x * uElt t * x⁻¹ := by rw [ht]

theorem irr_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hα : Function.Surjective α)
    (hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X))
    {W : Subgroup G} (hWZ : W ≤ Z) (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ zZero X Z ∨ Z ≤ W ⊔ zZero X Z := by
  classical
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hWX : W ≤ X := hWZ.trans hZX
  have hβker := beta_ker_eq_zZero β hβk
  let V : Subgroup ↥X := Z.subgroupOf X
  let WV : Subgroup V := (W.subgroupOf X).subgroupOf V
  let Y : Subgroup (Multiplicative (Fin 2 → F)) := WV.map β
  have hYinv : ∀ (A : SL(2, F)) (y : Multiplicative (Fin 2 → F)), y ∈ Y →
      Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd y)) ∈ Y := by
    intro A y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨g, rfl⟩ := hα A
    have hvZ : (((v : V) : ↥X) : G) ∈ Z :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp v.2)
    have hconjZ : (((g * v * g⁻¹ : ↥X) : G)) ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (h.normal g.2) (((v : V) : ↥X) : G)).mp hvZ
    have hVmem : (g * v * g⁻¹ : ↥X) ∈ V := Subgroup.mem_subgroupOf.mpr hconjZ
    have hWmem : (((v : V) : ↥X) : G) ∈ W :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hv)
    have hconjW : (((g * v * g⁻¹ : ↥X) : G)) ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hXW g.2) (((v : V) : ↥X) : G)).mp hWmem
    let v' : V := ⟨g * v * g⁻¹, hVmem⟩
    refine ⟨v', ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hconjW)
    · change Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v))
      exact hβe g v v' rfl
  have hY : Y = ⊥ ∨ Y = ⊤ := by
    by_cases hbot : Y = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
      have hyv : Multiplicative.toAdd y ≠ 0 := fun h0 =>
        hy1' (by simpa using congrArg Multiplicative.ofAdd h0)
      refine eq_top_iff.mpr fun u _ => ?_
      by_cases hu1 : u = 1
      · rw [hu1]; exact Y.one_mem
      · have huv : Multiplicative.toAdd u ≠ 0 := fun h0 =>
          hu1 (by simpa using congrArg Multiplicative.ofAdd h0)
        obtain ⟨A, hA⟩ := exists_smul_eq_of_ne_zero (Multiplicative.toAdd y)
          (Multiplicative.toAdd u) hyv huv
        have hAm : (A : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd y) =
            Multiplicative.toAdd u := by
          rwa [smul_eq_mulVec'] at hA
        have := hYinv A y hyY
        rw [hAm] at this
        simpa using this
  rcases hY with hYbot | hYtop
  · left
    intro w hwW
    have hwX : w ∈ X := hWX hwW
    let v : V := ⟨⟨w, hwX⟩, Subgroup.mem_subgroupOf.mpr (hWZ hwW)⟩
    have hvWV : v ∈ WV := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact Subgroup.mem_subgroupOf.mpr hwW
    have hβv : β v ∈ Y := Subgroup.mem_map_of_mem β hvWV
    rw [hYbot, Subgroup.mem_bot] at hβv
    have hvker : v ∈ β.ker := MonoidHom.mem_ker.mpr hβv
    rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hvker
    exact hvker
  · right
    intro z hz
    let v : V := ⟨⟨z, hZX hz⟩, Subgroup.mem_subgroupOf.mpr hz⟩
    have hβv : β v ∈ Y := by rw [hYtop]; exact Subgroup.mem_top _
    obtain ⟨v', hv'WV, hv'β⟩ := Subgroup.mem_map.mp hβv
    have hv'ker : v'⁻¹ * v ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hv'β]
      simp
    rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hv'ker
    have hw : ((v' : V) : G) ∈ W :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hv'WV)
    have hz0 : (((v' : V) : G)⁻¹ * z) ∈ zZero X Z := by
      simpa using hv'ker
    have hz_eq : z = ((v' : V) : G) * (((v' : V) : G)⁻¹ * z) := by group
    rw [hz_eq]
    exact (W ⊔ zZero X Z).mul_mem (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right hz0)

private theorem fixed_relIndex_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X))
    (hβ : Function.Surjective β)
    (hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X))
    {x : G} (hxP : x ∈ P) (hxQ : x ∉ pCoreOf 2 X) :
    (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).relIndex Z = Nat.card F := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hxX : x ∈ X := h.sylow.1 hxP
  have hαker : α.ker = (pCoreOf 2 X).subgroupOf X := alpha_ker_eq_pCoreOf h α hαk
  have hxN : x ∈ Subgroup.normalizer (zZero X Z : Set G) := h.le_normalizer_Z0 hxX
  let xH : ↥X := ⟨x, hxX⟩
  let γ : SL(2, F) := α xH
  have hγ1 : γ ≠ 1 := by
    intro hγ
    apply hxQ
    have hmem : xH ∈ α.ker := MonoidHom.mem_ker.mpr hγ
    rwa [hαker, Subgroup.mem_subgroupOf] at hmem
  have hγS : γ ∈ (P.subgroupOf X).map α :=
    Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.mpr hxP)
  have hS : IsSylowTwoOf ((P.subgroupOf X).map α) ⊤ := map_sylow h.sylow α hα
  obtain ⟨z, t, ht0, hγeq⟩ := exists_conj_uElt_of_mem_sylow hS hγS hγ1
  have hfixcard : Nat.card {v : Fin 2 → F // (γ : Matrix (Fin 2) (Fin 2) F).mulVec v = v} =
      Nat.card F := by
    rw [hγeq]
    exact (natCard_fixed_conj z (uElt t)).trans (natCard_fixed_uElt ht0)
  let φ : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
    { toFun := fun y => Multiplicative.ofAdd
        ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd y) -
          Multiplicative.toAdd y)
      map_one' := by simp
      map_mul' := by
        intro a b
        apply Multiplicative.toAdd.injective
        change (γ : Matrix (Fin 2) (Fin 2) F).mulVec
              (Multiplicative.toAdd a + Multiplicative.toAdd b) -
            (Multiplicative.toAdd a + Multiplicative.toAdd b) =
          ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd a) -
              Multiplicative.toAdd a) +
            ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd b) -
              Multiplicative.toAdd b)
        rw [Matrix.mulVec_add]
        abel }
  have hφmem : ∀ y : Multiplicative (Fin 2 → F),
      y ∈ φ.ker ↔ (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd y) =
        Multiplicative.toAdd y := by
    intro y
    change φ y = 1 ↔ _
    constructor
    · intro hy
      have h1 : Multiplicative.toAdd (φ y) = 0 := by simpa using congrArg Multiplicative.toAdd hy
      change (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd y) -
        Multiplicative.toAdd y = 0 at h1
      exact sub_eq_zero.mp h1
    · intro hy
      apply Multiplicative.toAdd.injective
      change (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd y) -
        Multiplicative.toAdd y = 0
      exact sub_eq_zero.mpr hy
  have hcardφker : Nat.card φ.ker = Nat.card F := by
    let e : φ.ker ≃ {v : Fin 2 → F //
        (γ : Matrix (Fin 2) (Fin 2) F).mulVec v = v} :=
      { toFun := fun y => ⟨Multiplicative.toAdd y.1, (hφmem y.1).mp y.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, (hφmem _).mpr (by simpa using v.2)⟩
        left_inv := fun y => by apply Subtype.ext; rfl
        right_inv := fun v => by apply Subtype.ext; rfl }
    exact (Nat.card_congr e).trans hfixcard
  have htarget : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card F * Nat.card F := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
      Nat.card_fun, Nat.card_eq_fintype_card (α := F), Nat.card_eq_fintype_card (α := Fin 2),
      Fintype.card_fin, pow_two]
  have hφidx : φ.ker.index = Nat.card F := by
    have hmul := Subgroup.card_mul_index φ.ker
    rw [hcardφker, htarget] at hmul
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
  let V : Subgroup ↥X := Z.subgroupOf X
  let cx : V →* V :=
    { toFun := fun v =>
        ⟨xH * v.1 * xH⁻¹, by
          have hvZ : (((v : V) : ↥X) : G) ∈ Z :=
            Subgroup.mem_subgroupOf.mp v.2
          exact Subgroup.mem_subgroupOf.mpr
            ((Subgroup.mem_normalizer_iff.mp (h.normal xH.2) (((v : V) : ↥X) : G)).mp hvZ)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  let δ : V →* Multiplicative (Fin 2 → F) := φ.comp β
  let Fx : Subgroup ↥X := (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).subgroupOf X
  have hδker : δ.ker = Fx.subgroupOf V := by
    ext v
    change v ∈ δ.ker ↔ v ∈ Fx.subgroupOf V
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_fixSecIn_zpowers_iff
      h.Z_le_normalizer_zZero hxN]
    have hvZ : (((v : V) : ↥X) : G) ∈ Z := Subgroup.mem_subgroupOf.mp v.2
    have hφv : φ (β v) = 1 ↔
        (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)) =
          Multiplicative.toAdd (β v) := by
      exact hφmem (β v)
    have hβcx : Multiplicative.toAdd (β (cx v)) =
        (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)) := by
      exact hβe xH v (cx v) rfl
    have hkerV : β (cx v * v⁻¹) = 1 ↔
        (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)) =
          Multiplicative.toAdd (β v) := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      constructor
      · intro h
        have h1 := congrArg Multiplicative.toAdd h
        simpa [hβcx] using h1
      · intro h
        apply Multiplicative.toAdd.injective
        simpa [hβcx] using h
    have hmemV0 : β (cx v * v⁻¹) = 1 ↔
        x * (((v : V) : ↥X) : G) * x⁻¹ * (((v : V) : ↥X) : G)⁻¹ ∈ zZero X Z := by
      have hβker := beta_ker_eq_zZero β hβk
      rw [← MonoidHom.mem_ker (f := β), hβker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hcoe : (((cx v * v⁻¹ : V) : ↥X) : G) = x * (((v : V) : ↥X) : G) * x⁻¹ *
          (((v : V) : ↥X) : G)⁻¹ := by
        simp [cx, xH]
      rw [hcoe]
    have hfix : φ (β v) = 1 ↔
        x * (((v : V) : ↥X) : G) * x⁻¹ * (((v : V) : ↥X) : G)⁻¹ ∈ zZero X Z :=
      hφv.trans (hkerV.symm.trans hmemV0)
    change φ (β v) = 1 ↔ _
    rw [hfix]
    exact (and_iff_right (by simpa using hvZ)).symm
  have hFixrel : ((fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).subgroupOf X).relIndex V =
      Nat.card F := by
    rw [Subgroup.relIndex]
    rw [← hδker]
    rw [Subgroup.index_ker]
    have hrange : (φ.comp β).range = φ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hβ]
      exact (MonoidHom.range_eq_map (f := φ)).symm
    rw [hrange]
    exact (Subgroup.index_ker φ).symm.trans hφidx
  rw [Subgroup.relIndex_subgroupOf hZX] at hFixrel
  exact hFixrel

theorem card_map_sylow_of_natCoord {X P : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hP : IsSylowTwoOf P X) (α : ↥X →* SL(2, F)) (hα : Function.Surjective α) :
    Nat.card ((P.subgroupOf X).map α) = Nat.card F := by
  classical
  have hS : IsSylowTwoOf ((P.subgroupOf X).map α) ⊤ := map_sylow hP α hα
  have hS0 : IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 2 F) ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (by norm_num)
  obtain ⟨φ, hφ⟩ := CFSG.Quasithin.SzN2.exists_mulEquiv_map_eq hS0 hS
  calc Nat.card ((P.subgroupOf X).map α) =
        Nat.card (((P.subgroupOf X).map α).map φ.toMonoidHom) :=
          (Subgroup.card_map_of_injective φ.injective).symm
    _ = Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 2 F) := by
          rw [hφ]
    _ = Nat.card F := by
          rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular]
          norm_num

private theorem relIndex_core_sylow_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    (pCoreOf 2 X).relIndex P = Nat.card F := by
  classical
  have hαker : α.ker = (pCoreOf 2 X).subgroupOf X := alpha_ker_eq_pCoreOf h α hαk
  have hrel := Subgroup.relIndex_ker (K := P.subgroupOf X) α
  rw [hαker, Subgroup.relIndex_subgroupOf h.sylow.1] at hrel
  rw [hrel, card_map_sylow_of_natCoord h.sylow α hα]

private theorem odd_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    ∃ u ∈ X, Odd (orderOf u) ∧ u ∉ pCoreOf 2 X := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαker : α.ker = (pCoreOf 2 X).subgroupOf X := alpha_ker_eq_pCoreOf h α hαk
  have hQX : (pCoreOf 2 X).relIndex X = Nat.card (SL(2, F)) := by
    rw [Subgroup.relIndex, ← hαker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hα,
      Subgroup.card_top]
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hm' : Nat.card F = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hm]
  have hsl2 : Nat.card (SL(2, F)) = Nat.card F * (Nat.card F ^ 2 - 1) :=
    CFSG.GorensteinWalter.sl2_card_formula F
  have h3dvd : 3 ∣ Nat.card F ^ 2 - 1 := by
    have hbase : ((2 : ZMod 3) ^ (m : ℕ)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      rw [show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
    have hcast : (((Nat.card F) ^ 2 : ℕ) : ZMod 3) = 1 := by
      rw [hm']
      push_cast
      exact hbase
    have hmod : (Nat.card F) ^ 2 ≡ 1 [MOD 3] :=
      (ZMod.natCast_eq_natCast_iff ((Nat.card F) ^ 2) 1 3).mp hcast
    have hpos : 0 < Nat.card F := Nat.card_pos
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 (Nat.card F) hpos)).mp hmod.symm
  have h3sl2 : 3 ∣ Nat.card (SL(2, F)) := by
    rw [hsl2]
    exact dvd_mul_of_dvd_right h3dvd (Nat.card F)
  have h3Q : 3 ∣ (pCoreOf 2 X).relIndex X := by rwa [hQX]
  refine exists_odd_notin_core h (fun k hk => ?_)
  rw [hk] at h3Q
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3Q
  omega

private theorem tr_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X))
    (hβ : Function.Surjective β)
    (hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X))
    {x : G} (hxP : x ∈ P) (hxQ : x ∉ pCoreOf 2 X) :
    (pCoreOf 2 X).relIndex P ≤
      (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).relIndex Z := by
  rw [relIndex_core_sylow_of_natCoord h α hα hαk,
    fixed_relIndex_of_natCoord h α β hα hαk hβ hβe hβk hxP hxQ]

theorem natFacts_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X))
    (hβ : Function.Surjective β)
    (hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X)) : NatFacts X P Z :=
  ⟨odd_of_natCoord h α hα hαk,
    fun W hWZ hXW => irr_of_natCoord h α β hα hβe hβk hWZ hXW,
    fun x hxP hxQ => tr_of_natCoord h α β hα hαk hβ hβe hβk hxP hxQ⟩

theorem baumannC_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X))
    (hβ : Function.Surjective β)
    (hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X))
    (hnc : NoCharNormal P X) : BaumannC X Z := by
  classical
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hPne : P ≠ ⊥ := by
    intro hP
    apply z_ne_bot_of_surjective (X := X) β hβ
    rw [hP] at h
    exact le_bot_iff.mp h.Z_le
  let R : Subgroup ↥X := P.subgroupOf X
  let S : Subgroup SL(2, F) := R.map α
  let M : Subgroup ↥X := Subgroup.normalizer (R : Set ↥X)
  have hsyl : IsSylowTwoOf R ⊤ := isSylowTwoOf_top_subgroupOf h.sylow
  have hnn : ¬ R.Normal := not_normal_subgroupOf hPne h.sylow.1 hnc
  have hαker : α.ker = (pCoreOf 2 X).subgroupOf X := alpha_ker_eq_pCoreOf h α hαk
  have hk : IsPGroup 2 ↥α.ker := by
    rw [hαker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 X)).symm
  have hMmax : ∀ Y : Subgroup ↥X, R ≤ Y → Y < ⊤ → Y ≤ M := by
    intro Y hRY hY
    exact CFSG.Quasithin.SzN6.normalizes_of_proper_overgroup α hα hk
      (fun U A hU hUA hA => CFSG.Quasithin.SzN6.sl2_proper_overgroup_le_normalizer U A hU hUA hA)
      hsyl hRY (ne_of_lt hY)
  have hMlt : M < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hnn (Subgroup.normalizer_eq_top_iff.mp htop)
  have hRM : R ≤ M := Subgroup.le_normalizer
  have hVe : IsElemAbelian 2 (Z.subgroupOf X) := isElemAbelian_subgroupOf h.elemAbelian
  have hVn : (Z.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr h.normal
  obtain ⟨ρ, -, hset⟩ := exists_natQuotSetting_of_sl2' (H := ↥X) (F := F)
    (R := R) (M := M) (V := Z.subgroupOf X) hsyl hnn hRM hMlt hMmax hVe hVn
    α hα hαk β hβ hβe hβk
  exact baumannC_of_natQuotSetting h hnc hset

theorem cor42_of_natCoord {X P Z : Subgroup G} (h : PushHyp X P Z)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : ↥X →* SL(2, F)) (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F))
    (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X))
    (hβ : Function.Surjective β)
    (hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X))
    (hnc : NoCharNormal P X) {H₀ : Subgroup G}
    (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G))
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    (∀ g ∈ H₀, cj g Z ≤ pCoreOf 2 X) ∧ conjJoinOf H₀ Z ≤ pCoreOf 2 X ∧
      (P ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G) →
        X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G)) := by
  have hB : BaumannC X Z := baumannC_of_natCoord h α β hα hαk hβ hβe hβk hnc
  have hN : NatFacts X P Z := natFacts_of_natCoord h α β hα hαk hβ hβe hβk
  have hle := cor42_join_le h hB hN hH₀ hodd
  exact ⟨cor42_cj_le h hB hN hH₀ hodd, hle, fun hP =>
    le_normalizer_of_core h hB hP hle
      (le_trans (cj_one Z).symm.le (cj_le_conjJoin H₀.one_mem))⟩

end CFSG.Quasithin.St84
