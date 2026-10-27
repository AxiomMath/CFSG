module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.Quasithin.Background.B42SmallComm
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel
public import CFSG.Quasithin.Background.SimsE214SevenSp4
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
public import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.Timmesfeld.Bridge.SchurNarrowCore
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
open CFSG.QuasithinUnique.Setup.X7b
open scoped Matrix commutatorElement Pointwise

private theorem card_natSp_mod (K : Type) [Field K] [Finite K] :
    Nat.card (FFModel.nat (StatedSp 2 K)).Mod = Nat.card K ^ 4 := by
  have e : (FFModel.nat (StatedSp 2 K)).Mod ≃ Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    (Equiv.ofBijective (CFSG.Quasithin.G64.natQuot (StatedSp 2 K))
      ⟨CFSG.Quasithin.G64.natQuot_injective, CFSG.Quasithin.G64.natQuot_surjective⟩).symm
  rw [Nat.card_congr e, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 2 ⊕ Fin 2), Fintype.card_sum]
  norm_num

private theorem card_of_realizes_natSp {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {I : Subgroup V} {K : Type} [Field K] [Finite K]
    {π : ↥(StatedSp 2 K) →* ↥H}
    (h : (FFModel.nat (StatedSp 2 K)).RealizesVia H I ⊥ π) :
    Nat.card I = Nat.card K ^ 4 := by
  rw [CFSG.Quasithin.G64.RealizesVia.card_eq h, card_natSp_mod, Subgroup.card_bot, mul_one]

private theorem exists_natEquiv_bot {K : Type} [Field K] [Finite K] {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {I : Subgroup V} {π : ↥(StatedSp 2 K) →* ↥H}
    (h : (FFModel.nat (StatedSp 2 K)).RealizesVia H I ⊥ π) :
    ∃ e : I ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K),
      ∀ (γ : ↥(StatedSp 2 K)) (u : I)
        (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ I),
        Multiplicative.toAdd (e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩) =
          ((γ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) *ᵥ
            Multiplicative.toAdd (e u) := by
  classical
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.G64.exists_natMap h
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (by simpa using Subgroup.mem_bot.1 ((hfk u).1 hu))
  let e : I ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K) := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e, fun γ u hu => ?_⟩
  have h1 := hfe γ u hu
  have h2 : Multiplicative.toAdd (f ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩) =
      ((γ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd (f u) := by
    rw [h1]
    rfl
  exact (congrArg Multiplicative.toAdd
    (MulEquiv.ofBijective_apply f ⟨hfi, hfs⟩ ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩)).trans h2

private theorem irr_of_realizes_natSp {K : Type} [Field K] [Finite K] {V : Type} [CommGroup V]
    [Finite V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : ↥(StatedSp 2 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H U ⊥ π)
    {X : Subgroup V} (hXU : X ≤ U) (hXH : ∀ h ∈ H, ∀ x ∈ X, h x ∈ X) :
    X = ⊥ ∨ X = U := by
  classical
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.G64.exists_natMap hπ
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  right
  have hne : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hbot (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨x₀, hx₀X, hx₀1⟩ := hne
  have hfx0 : f ⟨x₀, hXU hx₀X⟩ ≠ 1 := by
    intro h
    exact hx₀1 (by simpa using Subgroup.mem_bot.1 ((hfk _).1 h))
  refine le_antisymm hXU fun u hu => ?_
  by_cases hu1 : u = 1
  · rw [hu1]; exact Subgroup.one_mem X
  have hfu : f ⟨u, hu⟩ ≠ 1 := by
    intro h
    exact hu1 (by simpa using Subgroup.mem_bot.1 ((hfk _).1 h))
  have hvx : Multiplicative.toAdd (f ⟨x₀, hXU hx₀X⟩) ≠ 0 := by
    intro h
    exact hfx0 (Multiplicative.toAdd.injective (by simpa using h))
  have hvu : Multiplicative.toAdd (f ⟨u, hu⟩) ≠ 0 := by
    intro h
    exact hfu (Multiplicative.toAdd.injective (by simpa using h))
  obtain ⟨γ, hγ, hγv⟩ :=
    CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq hvx hvu
  let γ' : ↥(StatedSp 2 K) := ⟨γ, hγ⟩
  have hmem : ((π γ' : ↥H) : MulAut V) x₀ ∈ U := hXU (hXH _ (π γ').2 _ hx₀X)
  have hxγX : ((π γ' : ↥H) : MulAut V) x₀ ∈ X := hXH _ (π γ').2 _ hx₀X
  have hfeγ := hfe γ' ⟨x₀, hXU hx₀X⟩ hmem
  have hfx : f ⟨((π γ' : ↥H) : MulAut V) x₀, hmem⟩ = f ⟨u, hu⟩ := by
    rw [hfeγ]
    rw [show natAct (StatedSp 2 K) γ' (f ⟨x₀, hXU hx₀X⟩) =
      Multiplicative.ofAdd (Multiplicative.toAdd (f ⟨u, hu⟩)) from ?_]
    · simp
    · change Multiplicative.ofAdd (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd (f ⟨x₀, hXU hx₀X⟩))) = Multiplicative.ofAdd _
      rw [hγv]
  have hprod : (⟨u, hu⟩ : ↥U)⁻¹ * ⟨((π γ' : ↥H) : MulAut V) x₀, hmem⟩ = 1 := by
    have h1 : f ((⟨u, hu⟩ : ↥U)⁻¹ * ⟨((π γ' : ↥H) : MulAut V) x₀, hmem⟩) = 1 := by
      rw [map_mul, map_inv, hfx, inv_mul_cancel]
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk _).1 h1))
  have huX : u = ((π γ' : ↥H) : MulAut V) x₀ := by
    have h := congrArg Subtype.val hprod
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h
    exact inv_mul_eq_one.mp h
  exact huX.symm ▸ hxγX

private theorem isIrrOn_of_natSpn {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I : Subgroup W} {n : ℕ}
    (hI : NatSpn L I ⊥ 4 n) (hn : 1 < n) : IsIrrOn L I ⊥ := by
  classical
  obtain ⟨-, K, hKfield, hKfin, hKcard, π0, hreal⟩ := hI
  let π : ↥(StatedSp 2 K) →* ↥L := π0
  have hreal' : (FFModel.nat (StatedSp 2 K)).RealizesVia L I ⊥ π := hreal
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hIinv : ∀ l ∈ L, ∀ x ∈ I, l x ∈ I :=
    fun l hl x hx => hreal.2.2.2.1 ⟨l, hl⟩ x hx
  refine ⟨?_, hIinv, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro hbot
    have hcard := card_of_realizes_natSp hreal
    rw [hbot, Subgroup.card_bot] at hcard
    have h1 : 1 < Nat.card K := by
      rw [hKcard]; exact Nat.one_lt_two_pow (by omega)
    have h2 : 1 < Nat.card K ^ 4 := by
      calc 1 < 2 ^ 4 := by norm_num
        _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  · intro l hl x hx
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, map_one]
  · intro J hJ _ hJI
    exact irr_of_realizes_natSp hreal hJI (fun l hl x hx => hJ l hl x hx)

private theorem summand_label {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {n : ℕ} {I : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)]
    (hSp : IsSp4 ↥L n) (hn : 1 < n)
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* antiSp K)
    (hI : NatSpn L I ⊥ 4 n) :
    ∃ (ρ : Representation (ZMod 2) (antiSp K) (Additive ↥I)) (i : ℕ)
      (φ : Additive ↥I ≃+ (Fin 4 → K)),
      (∀ (g : antiSp K) (w : Additive ↥I),
        φ (ρ g w) = glMat (((minorAut K ^ i) g : antiSp K) :
          GL (Fin 4) K) *ᵥ φ w) ∧
      ρ.IsIrreducible ∧ (∃ g : antiSp K, ρ g ≠ 1) ∧
      (∀ (l : ↥L) (w : Additive ↥I),
        ((Additive.toMul (ρ (eL l) w) : ↥I) : W) =
          (l : MulAut W) ((Additive.toMul w : ↥I) : W)) ∧
      IsIrrOn L I ⊥ := by

  classical
  haveI : Finite K := Finite.of_fintype K

  obtain ⟨-, KI, hKIfield, hKIfin, hKIcard, πI0, hrealI⟩ := hI
  let πI : ↥(StatedSp 2 KI) →* ↥L := πI0
  have hrealI' : (FFModel.nat (StatedSp 2 KI)).RealizesVia L I ⊥ πI := hrealI
  letI : Field KI := hKIfield
  letI : Finite KI := hKIfin
  have hIinv : ∀ l ∈ L, ∀ x ∈ I, l x ∈ I :=
    fun l hl x hx => hrealI.2.2.2.1 ⟨l, hl⟩ x hx
  have hIrrOn : IsIrrOn L I ⊥ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro hbot
      have hcard := card_of_realizes_natSp hrealI
      rw [hbot, Subgroup.card_bot] at hcard
      have h1 : 1 < Nat.card KI := by
        rw [hKIcard]
        exact Nat.one_lt_two_pow (by omega)
      have h2 : 1 < Nat.card KI ^ 4 := by
        calc 1 < 2 ^ 4 := by norm_num
          _ ≤ Nat.card KI ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    · exact hIinv
    · intro l hl x hx
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx, map_one]
    · intro J hJ _ hJI
      exact irr_of_realizes_natSp hrealI hJI
        (fun l hl x hx => hJ l hl x hx)
  let actI : ↥L →* MulAut ↥I :=
    { toFun := fun l =>
        { toFun := fun x => ⟨(l : MulAut W) x, hIinv l l.2 x x.2⟩
          invFun := fun x => ⟨((l⁻¹ : ↥L) : MulAut W) x, hIinv (l⁻¹ : ↥L) (l⁻¹).2 x x.2⟩
          left_inv := fun x => by
            apply Subtype.ext
            simp
          right_inv := fun x => by
            apply Subtype.ext
            simp
          map_mul' := fun x y => by
            apply Subtype.ext
            simp [map_mul] }
      map_one' := by
        ext x
        simp
      map_mul' := fun l m => by
        ext x
        simp [map_mul] }
  let ρI : Representation (ZMod 2) (antiSp K) (Additive ↥I) :=
    { toFun := fun g => mulAutLinear (actI (eL.symm g))
      map_one' := by
        apply LinearMap.ext
        intro x
        simp [mulAutLinear_apply]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro x
        simp [mulAutLinear_apply, MulAut.mul_apply] }
  have hIne : I ≠ ⊥ := hIrrOn.1.ne'
  have hirrI : ρI.IsIrreducible := by
    change IsSimpleOrder (Subrepresentation ρI)
    refine (isSimpleOrder_iff _).mpr ⟨?_, ?_⟩
    · refine ⟨⊥, ⊤, ?_⟩
      intro h
      have h1 : (⊤ : Subrepresentation ρI).toSubmodule = ⊥ :=
        (congrArg Subrepresentation.toSubmodule h).symm
      have h2 : (⊤ : Submodule (ZMod 2) (Additive ↥I)) = ⊥ := h1
      have htriv : ∀ x : ↥I, x = 1 := by
        intro x
        have hx : (Additive.ofMul x : Additive ↥I) ∈ (⊥ : Submodule (ZMod 2) (Additive ↥I)) := by
          rw [← h2]
          exact Submodule.mem_top
        exact Additive.ofMul.injective ((Submodule.mem_bot (R := ZMod 2)).1 hx)
      apply hIne
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (by simpa using congrArg Subtype.val (htriv ⟨x, hx⟩))
    · intro S
      let J : Subgroup ↥I :=
        AddSubgroup.toSubgroup' (Submodule.toAddSubgroup S.toSubmodule)
      have hJmem : ∀ (x : ↥I), x ∈ J ↔ Additive.ofMul x ∈ S.toSubmodule := by
        intro x
        rw [show J = AddSubgroup.toSubgroup' (Submodule.toAddSubgroup S.toSubmodule) from rfl,
          AddSubgroup.mem_toSubgroup']
        rfl
      have hJ'L : StableUnder L (J.map I.subtype) := by
        intro l hl x hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hm : Additive.ofMul (actI ⟨l, hl⟩ y) ∈ S.toSubmodule := by
          have h1 := S.apply_mem_toSubmodule (eL ⟨l, hl⟩) (v := Additive.ofMul y)
            ((hJmem y).1 hy)
          have h2 : ρI (eL ⟨l, hl⟩) (Additive.ofMul y) =
              Additive.ofMul (actI ⟨l, hl⟩ y) := by
            simp [ρI, mulAutLinear_apply]
          rwa [h2] at h1
        exact ⟨actI ⟨l, hl⟩ y, (hJmem _).2 hm, rfl⟩
      have hJ'I : J.map I.subtype ≤ I := by
        rintro x ⟨y, hy, rfl⟩
        exact (y : ↥I).2
      rcases hIrrOn.2.2.2 (J.map I.subtype) hJ'L bot_le hJ'I with hbot | htop
      · left
        apply Subrepresentation.ext
        have hJbot : J = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (H := J) (f := I.subtype)
            I.subtype_injective).1 hbot
        have hbot' : Submodule.toAddSubgroup S.toSubmodule = ⊥ := by
          simpa [J] using congrArg (AddSubgroup.toSubgroup'.symm) hJbot
        rw [← Submodule.toAddSubgroup_toZModSubmodule 2 S.toSubmodule, hbot']
        rfl
      · right
        have hJtop : J = ⊤ := by
          apply le_antisymm le_top
          intro x hx
          have hxI : (x : W) ∈ J.map I.subtype := by
            rw [htop]
            exact x.2
          obtain ⟨y, hy, hyx⟩ := hxI
          exact (Subtype.ext hyx) ▸ hy
        apply Subrepresentation.ext
        have htop' : Submodule.toAddSubgroup S.toSubmodule = ⊤ := by
          simpa [J] using congrArg (AddSubgroup.toSubgroup'.symm) hJtop
        rw [← Submodule.toAddSubgroup_toZModSubmodule 2 S.toSubmodule, htop']
        rfl
  have hπIinj : Function.Injective πI :=
    CFSG.Quasithin.B42Small.injective_of_realizesVia_nat hrealI'
  obtain ⟨eI, heI⟩ := exists_natEquiv_bot hrealI'
  have hnat_apply_eq : ∀ δ : ↥(StatedSp 2 KI),
      (∀ x : ↥I, ((πI δ : ↥L) : MulAut W) x = x) → δ = 1 := by
    intro δ hδ
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    let v : Multiplicative (Fin 2 ⊕ Fin 2 → KI) :=
      Multiplicative.ofAdd (Pi.single j 1)
    let x : I := eI.symm v
    have hu : ((πI δ : ↥L) : MulAut W) (x : W) ∈ I := hIinv _ (πI δ).2 _ x.2
    have hxsub : (⟨((πI δ : ↥L) : MulAut W) (x : W), hu⟩ : ↥I) = x := by
      apply Subtype.ext
      exact hδ x
    have h1 := heI δ x hu
    rw [hxsub] at h1
    rw [MulEquiv.apply_symm_apply] at h1
    have hcol : ((((δ : ↥(StatedSp 2 KI)) : GL (Fin 2 ⊕ Fin 2) KI) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) KI)).mulVec
        (Pi.single j 1) = Pi.single j 1 := by
      simpa [v] using h1.symm
    have hcol' : ((((δ : ↥(StatedSp 2 KI)) : GL (Fin 2 ⊕ Fin 2) KI) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) KI)).col j =
        Pi.single j 1 := by
      simpa [Matrix.col, Matrix.mulVec] using hcol
    have := congrFun hcol' i
    simpa [Matrix.col_apply, Pi.single_apply, Matrix.one_apply] using this
  have hactIinj : Function.Injective actI := by
    intro l m h
    have ht : m⁻¹ * l = 1 := by
      obtain ⟨δ, hδ⟩ := hrealI'.1 (m⁻¹ * l)
      let δ' : ↥(StatedSp 2 KI) := δ
      have hδ' : πI δ' = m⁻¹ * l := hδ
      have hδtriv : ∀ x : ↥I, ((πI δ' : ↥L) : MulAut W) x = x := by
        intro x
        have hx : ((l : MulAut W) x : W) = ((m : MulAut W) x : W) :=
          congrArg (fun f : MulAut ↥I => ((f x : ↥I) : W)) h
        have h2 := congrArg (fun y : W => ((m⁻¹ : ↥L) : MulAut W) y) hx
        have h3 : ((m⁻¹ * l : ↥L) : MulAut W) x = x := by
          simpa [MulAut.mul_apply] using h2
        calc ((πI δ' : ↥L) : MulAut W) x
            = ((m⁻¹ * l : ↥L) : MulAut W) x := by rw [hδ']
          _ = x := h3
      have hδ1 := hnat_apply_eq δ' hδtriv
      rw [← hδ', hδ1]
      exact map_one πI
    calc l = m * (m⁻¹ * l) := by group
      _ = m * 1 := by rw [ht]
      _ = m := mul_one m
  have hntI : ∃ g : antiSp K, ρI g ≠ 1 := by
    haveI : Nontrivial ↥L := (K148.isSimpleGroup_of_isSp4 hSp).toNontrivial
    obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
    refine ⟨eL l, fun h => hl ?_⟩
    have h1 : actI l = 1 := by
      ext x
      have h2 := congrArg (fun f : Additive ↥I →ₗ[ZMod 2] Additive ↥I => f (Additive.ofMul x)) h
      simpa [ρI, mulAutLinear_apply] using h2
    exact hactIinj (by rw [h1, map_one])
  let πE : antiSp K →* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I) :=
    CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom ρI
  have hrep : CFSG.Quasithin.B42Sp4.repOf πE = ρI := by
    ext g x
    rw [CFSG.Quasithin.B42Sp4.repOf_apply]
    rfl
  haveI : Fact (CFSG.Quasithin.B42Sp4.repOf πE).IsIrreducible :=
    ⟨by rw [hrep]; exact hirrI⟩
  have hntE : ∃ g : antiSp K, CFSG.Quasithin.B42Sp4.repOf πE g ≠ 1 := by
    obtain ⟨g, hg⟩ := hntI
    exact ⟨g, by rwa [hrep]⟩
  have hKf : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have hcardI : Nat.card ↥I = 2 ^ (4 * n) := by
    rw [card_of_realizes_natSp hrealI', hKIcard, ← pow_mul, Nat.mul_comm n 4]
  have hcardA : Nat.card (Additive ↥I) < 2 ^ (8 * n) := by
    rw [Nat.card_congr Additive.toMul, hcardI]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdim : Module.finrank (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (CFSG.Quasithin.B42Sp4.repOf πE)) (Additive ↥I) = 4 :=
    CFSG.Quasithin.SimsE2.E214S.finrank_eq_four_of_card_lt (f := n) hKf (by omega)
      πE hntE hcardA
  obtain ⟨i, φ, hφ⟩ :=
    CFSG.Quasithin.B42Sp4.exists_natural_of_four hKf (by omega) πE hntE hdim
  refine ⟨ρI, i, φ, hφ, hirrI, hntI, ?_, hIrrOn⟩
  intro l w
  have h1 : ρI (eL l) = mulAutLinear (actI l) := by
    rw [show ρI (eL l) = mulAutLinear (actI (eL.symm (eL l))) from rfl,
      MulEquiv.symm_apply_apply]
  rw [h1, mulAutLinear_apply]
  rfl

private noncomputable def frobeniusField (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] : K ≃ₗ[ZMod 2] K :=
  LinearEquiv.ofBijective
    { toFun := fun x => (frobeniusEquiv K 2) x
      map_add' := by intro x y; exact map_add _ _ _
      map_smul' := by
        intro c x
        change (frobeniusEquiv K 2) (c • x) = c • (frobeniusEquiv K 2) x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        have h : ((frobeniusEquiv K 2).toRingHom.comp (algebraMap (ZMod 2) K)) =
            algebraMap (ZMod 2) K := RingHom.ext_zmod _ _
        exact congrArg (fun f : ZMod 2 →+* K => f c) h }
    (frobeniusEquiv K 2).bijective

private theorem frobeniusField_apply (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (x : K) : frobeniusField K x = x ^ 2 := by
  change (frobeniusEquiv K 2) x = x ^ 2
  rw [frobeniusEquiv_apply, frobenius_def]

private theorem frobeniusField_pow_sq (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (r : ℕ) (x : K) :
    (frobeniusField K ^ r) (x ^ 2) = ((frobeniusField K ^ r) x) ^ 2 := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, LinearEquiv.mul_apply]
      rw [show frobeniusField K (x ^ 2) = (frobeniusField K x) ^ 2 by
        rw [frobeniusField_apply, frobeniusField_apply]]
      rw [ih (frobeniusField K x)]
      rw [LinearEquiv.mul_apply]

private noncomputable def frobeniusVec (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (r : ℕ) : (Fin 4 → K) ≃ₗ[ZMod 2] (Fin 4 → K) :=
  { toFun := fun v i => (frobeniusField K ^ r) (v i)
    invFun := fun v i => ((frobeniusField K ^ r).symm) (v i)
    left_inv := by
      intro v
      ext i
      simp
    right_inv := by
      intro v
      ext i
      simp
    map_add' := by
      intro v w
      ext i
      simp
    map_smul' := by
      intro c v
      ext i
      simp }

private theorem frobeniusVec_zero (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (v : Fin 4 → K) : frobeniusVec K 0 v = v := by
  ext i
  simp [frobeniusVec]

private theorem frobeniusVec_succ (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (r : ℕ) (v : Fin 4 → K) :
    frobeniusVec K (r + 1) v = fun i => (frobeniusVec K r v i) ^ 2 := by
  ext i
  change (frobeniusField K ^ (r + 1)) (v i) = ((frobeniusField K ^ r) (v i)) ^ 2
  rw [pow_succ, LinearEquiv.mul_apply, frobeniusField_apply, frobeniusField_pow_sq]

private theorem frobeniusVec_natRepS (K : Type) [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (r i : ℕ) (g : antiSp K) (v : Fin 4 → K) :
    frobeniusVec K r (natRepS (F := K) K i g *ᵥ v) =
      natRepS (F := K) K (i + 2 * r) g *ᵥ frobeniusVec K r v := by
  induction r with
  | zero =>
      exact congrArg (fun w => (natRepS (F := K) K i g) *ᵥ w) (frobeniusVec_zero K v)
  | succ r ih =>
      rw [show i + 2 * (r + 1) = (i + 2 * r) + 2 by ring, natRepS_add_two' (k := K)]
      rw [frobeniusVec_succ]
      rw [ih]
      rw [frobeniusVec_succ]
      funext j
      have hmap : (natRepS (F := K) K (i + 2 * r) g).map (fun x => x ^ 2) =
          (natRepS (F := K) K (i + 2 * r) g).map (⇑(frobeniusEquiv K 2)) := by
        ext a b
        simp [frobeniusEquiv_apply, frobenius_def 2]
      have hw : (fun i => (frobeniusVec K r v) i ^ 2) =
          (⇑(frobeniusEquiv K 2) ∘ (frobeniusVec K r v)) := by
        funext i
        simp [frobeniusEquiv_apply, frobenius_def 2]
      rw [hmap, hw]
      simpa [frobenius_def 2] using
        (RingHom.map_mulVec (f := (frobeniusEquiv K 2 : K →+* K))
          (M := natRepS (F := K) K (i + 2 * r) g) (v := frobeniusVec K r v) j)

private def restrictAutToInvariant {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hIinv : StableUnder L I) : ↥L →* MulAut ↥I where
  toFun l :=
    { toFun := fun x => ⟨(l : MulAut W) x, hIinv l l.2 x x.2⟩
      invFun := fun x => ⟨((l⁻¹ : ↥L) : MulAut W) x, hIinv (l⁻¹ : ↥L) (l⁻¹).2 x x.2⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun x => by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp [map_mul] }
  map_one' := by ext x; simp
  map_mul' := fun l m => by ext x; simp [map_mul]

private theorem secIsoOn_of_labels
    {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {n : ℕ} {I J : Subgroup W}
    {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
    [Module (ZMod 2) (Additive ↥I)] [Module (ZMod 2) (Additive ↥J)]
    (eL : ↥L ≃* antiSp K)
    (hIinv : StableUnder L I) (hJinv : StableUnder L J)
    {ρI : Representation (ZMod 2) (antiSp K) (Additive ↥I)}
    {ρJ : Representation (ZMod 2) (antiSp K) (Additive ↥J)}
    {iI iJ r : ℕ} (hKf : Fintype.card K = 2 ^ n)
    (hr : iJ + 2 * n * iI = iI + 2 * r)
    {φI : Additive ↥I ≃+ (Fin 4 → K)} {φJ : Additive ↥J ≃+ (Fin 4 → K)}
    (hφI : ∀ (g : antiSp K) (w : Additive ↥I),
      φI (ρI g w) = natRepS (F := K) K iI g *ᵥ φI w)
    (hφJ : ∀ (g : antiSp K) (w : Additive ↥J),
      φJ (ρJ g w) = natRepS (F := K) K iJ g *ᵥ φJ w)
    (hρI : ∀ l : ↥L, ρI (eL l) = mulAutLinear (restrictAutToInvariant (I := I) hIinv l))
    (hρJ : ∀ l : ↥L, ρJ (eL l) = mulAutLinear (restrictAutToInvariant (I := J) hJinv l)) :
    SecIsoOn L I ⊥ J ⊥ := by
  classical
  haveI : Finite K := Finite.of_fintype K
  let ψ : Additive ↥I ≃+ Additive ↥J :=
    φI.trans ((frobeniusVec K r).toAddEquiv.trans φJ.symm)
  have hψφI : ∀ x : Additive ↥I, φJ (ψ x) = frobeniusVec K r (φI x) := fun x => by
    show φJ (φJ.symm (frobeniusVec K r (φI x))) = frobeniusVec K r (φI x)
    rw [AddEquiv.apply_symm_apply]
  have hψ : ∀ (g : antiSp K) (x : Additive ↥I), ψ (ρI g x) = ρJ g (ψ x) := by
    intro g x
    have h1 : ψ (ρI g x) = φJ.symm (frobeniusVec K r (φI (ρI g x))) := rfl
    rw [h1, hφI g x, frobeniusVec_natRepS]
    have h2 : natRepS (F := K) K (iI + 2 * r) g = natRepS (F := K) K iJ g := by
      have h3 : iI + 2 * r = iJ + 2 * n * iI := by omega
      rw [h3]
      exact natRepS_add_mul (k := K) hKf iJ iI g
    rw [h2, ← hψφI x, ← hφJ g (ψ x), AddEquiv.symm_apply_apply]
  have hψL : ∀ (l : ↥L) (x : Additive ↥I),
      ψ (mulAutLinear (restrictAutToInvariant (I := I) hIinv l) x) =
        mulAutLinear (restrictAutToInvariant (I := J) hJinv l) (ψ x) := by
    intro l x
    rw [← hρI l, ← hρJ l]
    exact hψ (eL l) x
  let βJ : ↥I →* ↥J :=
    { toFun := fun a => Additive.toMul (ψ (Additive.ofMul a))
      map_one' := by
        show Additive.toMul (ψ (0 : Additive ↥I)) = 1
        rw [map_zero]
        rfl
      map_mul' := fun a b => by
        change Additive.toMul (ψ (Additive.ofMul a + Additive.ofMul b)) =
          Additive.toMul (ψ (Additive.ofMul a)) * Additive.toMul (ψ (Additive.ofMul b))
        rw [map_add]
        rfl }
  let β : ↥I →* W := J.subtype.comp βJ
  have hβL : ∀ (l : ↥L) (a : ↥I), βJ (restrictAutToInvariant (I := I) hIinv l a) =
      restrictAutToInvariant (I := J) hJinv l (βJ a) := by
    intro l a
    have h := hψL l (Additive.ofMul a)
    exact congrArg Additive.toMul h
  refine ⟨bot_le, bot_le, hIinv,
    fun _ _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one], hJinv,
    fun _ _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one],
    β, fun a => (βJ a).2, ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h
      have h' : βJ a = 1 := by
        apply Subtype.ext
        exact Subgroup.mem_bot.1 h
      have h2 : ψ (Additive.ofMul a) = 0 := congrArg Additive.ofMul h'
      have h3 : Additive.ofMul a = 0 := ψ.injective (h2.trans (map_zero ψ).symm)
      have ha1 : a = 1 := Additive.ofMul.injective (by simpa using h3)
      exact Subgroup.mem_bot.2 (by rw [ha1]; rfl)
    · intro h
      have ha1 : a = 1 := Subtype.ext (Subgroup.mem_bot.1 h)
      subst ha1
      exact Subgroup.mem_bot.2 (by simp)
  · intro b hb
    refine ⟨Additive.toMul (ψ.symm (Additive.ofMul ⟨b, hb⟩)), ?_⟩
    have h1 : βJ (Additive.toMul (ψ.symm (Additive.ofMul ⟨b, hb⟩))) = ⟨b, hb⟩ := by
      apply Additive.toMul.injective
      change ψ (Additive.ofMul (Additive.toMul (ψ.symm (Additive.ofMul ⟨b, hb⟩)))) =
        Additive.ofMul ⟨b, hb⟩
      rw [show Additive.ofMul (Additive.toMul (ψ.symm (Additive.ofMul ⟨b, hb⟩))) =
        ψ.symm (Additive.ofMul ⟨b, hb⟩) from rfl]
      rw [AddEquiv.apply_symm_apply]
    rw [Subgroup.mem_bot]
    have h2 : β (Additive.toMul (ψ.symm (Additive.ofMul ⟨b, hb⟩))) = b := by
      change ((βJ (Additive.toMul (ψ.symm (Additive.ofMul ⟨b, hb⟩))) : ↥J) : W) = b
      rw [h1]
    rw [h2, mul_inv_cancel]
  · intro x hx a a' ha'
    have ha'' : a' = restrictAutToInvariant (I := I) hIinv ⟨x, hx⟩ a := Subtype.ext ha'
    subst ha''
    have h1 := hβL ⟨x, hx⟩ a
    have h2 : (β (restrictAutToInvariant (I := I) hIinv ⟨x, hx⟩ a) : W) =
        ((⟨x, hx⟩ : ↥L) : MulAut W) (β a : W) := by
      change ((βJ (restrictAutToInvariant (I := I) hIinv ⟨x, hx⟩ a) : ↥J) : W) =
        ((⟨x, hx⟩ : ↥L) : MulAut W) (((βJ a : ↥J) : W))
      rw [h1]
      rfl
    rw [Subgroup.mem_bot, h2, mul_inv_cancel]


private theorem parities_differ
    {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {n : ℕ} {I J : Subgroup W}
    {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
    [Module (ZMod 2) (Additive ↥I)] [Module (ZMod 2) (Additive ↥J)]
    (eL : ↥L ≃* antiSp K)
    (hIinv : StableUnder L I) (hJinv : StableUnder L J)
    {ρI : Representation (ZMod 2) (antiSp K) (Additive ↥I)}
    {ρJ : Representation (ZMod 2) (antiSp K) (Additive ↥J)}
    {iI iJ : ℕ}
    {φI : Additive ↥I ≃+ (Fin 4 → K)} {φJ : Additive ↥J ≃+ (Fin 4 → K)}
    (hKf : Fintype.card K = 2 ^ n) (hn : 1 ≤ n)
    (hφI : ∀ (g : antiSp K) (w : Additive ↥I),
      φI (ρI g w) = natRepS (F := K) K iI g *ᵥ φI w)
    (hφJ : ∀ (g : antiSp K) (w : Additive ↥J),
      φJ (ρJ g w) = natRepS (F := K) K iJ g *ᵥ φJ w)
    (hρI : ∀ l : ↥L, ρI (eL l) = mulAutLinear (restrictAutToInvariant (I := I) hIinv l))
    (hρJ : ∀ l : ↥L, ρJ (eL l) = mulAutLinear (restrictAutToInvariant (I := J) hJinv l))
    (hnot : ¬ SecIsoOn L I ⊥ J ⊥) :
    iI % 2 ≠ iJ % 2 := by
  intro hpar
  let iJ' : ℕ := iJ + 2 * n * iI
  have hle : iI ≤ iJ' := by
    dsimp [iJ']
    nlinarith
  have h2n : (2 * n * iI) % 2 = 0 := by
    rw [show 2 * n * iI = 2 * (n * iI) by ring]
    exact Nat.mul_mod_right 2 (n * iI)
  have hpar' : iJ' % 2 = iI % 2 := by
    have h1 : iJ' % 2 = iJ % 2 := by
      dsimp [iJ']
      rw [Nat.add_mod, h2n, Nat.add_zero,
        Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    rw [h1]
    exact hpar.symm
  have heven : (iJ' - iI) % 2 = 0 := by omega
  let r : ℕ := (iJ' - iI) / 2
  have hdiff : iJ' - iI = 2 * r := by
    dsimp [r]
    exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)).symm
  have hr : iJ + 2 * n * iI = iI + 2 * r := by
    dsimp [iJ'] at hdiff
    omega
  exact hnot (secIsoOn_of_labels eL hIinv hJinv hKf hr hφI hφJ hρI hρJ)

private theorem rk_commSub_top_eq_finrank
    {U : Type} [CommGroup U] [Finite U] [Module (ZMod 2) (Additive U)]
    (g : MulAut U) :
    rk (commSub (⊤ : Subgroup U) (Subgroup.zpowers g)) =
      Module.finrank (ZMod 2) (LinearMap.range (mulAutLinear g - 1)) := by
  classical
  have hmap : commSub (⊤ : Subgroup U) (Subgroup.zpowers g) =
      (⊤ : Subgroup U).map (commHom g) :=
    commSub_zpowers_eq_map (W := ⊤) (fun _ _ _ _ => trivial)
  have hcard : Nat.card ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers g)) =
      Nat.card ↥(LinearMap.range (mulAutLinear g - 1)) := by
    rw [hmap]
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨Additive.ofMul (x : U), ?_⟩
        invFun := fun v => ⟨Additive.toMul (v : Additive U), ?_⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun v => by ext; rfl }
    · obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp x.2
      refine ⟨Additive.ofMul y, ?_⟩
      show mulAutLinear g (Additive.ofMul y) - Additive.ofMul y = Additive.ofMul (x : U)
      rw [mulAutLinear_apply, ← hy, commHom_apply]
      simp [mul_inv, sub_eq_add_neg]
    · obtain ⟨z, hz⟩ := LinearMap.mem_range.mp v.2
      refine Subgroup.mem_map.mpr ⟨Additive.toMul z, trivial, ?_⟩
      show commHom g (Additive.toMul z) = Additive.toMul (v : Additive U)
      rw [commHom_apply]
      have h2 : Additive.toMul (mulAutLinear g z - z) = Additive.toMul (v : Additive U) :=
        congrArg Additive.toMul hz
      simpa [mulAutLinear_apply, sub_eq_add_neg, mul_inv] using h2
  have hpow : Nat.card ↥(LinearMap.range (mulAutLinear g - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (mulAutLinear g - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.range (mulAutLinear g - 1)), Nat.card_zmod]
  unfold rk
  rw [hcard, hpow, padicValNat.prime_pow]

private theorem map_commSub_restrictAct {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)]
    (hIinv : StableUnder L I) {z : ↥L} (hz : orderOf z = 2) :
    (commSub (⊤ : Subgroup ↥I)
        (Subgroup.zpowers (restrictAutToInvariant (I := I) hIinv z))).map I.subtype =
      commSub I (Subgroup.zpowers (z : MulAut W)) := by
  haveI : Finite ↥I := Finite.of_injective (fun x : ↥I => (x : W)) Subtype.val_injective
  have hzW : orderOf (z : MulAut W) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hIpow : ∀ x ∈ Subgroup.zpowers (z : MulAut W), ∀ w ∈ I, x w ∈ I := by
    intro x hx w hw
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzW).mp hx with
      rfl | rfl
    · simpa using hw
    · exact hIinv _ z.2 w hw
  rw [commSub_zpowers_eq_map (W := ⊤) (fun _ _ _ _ => trivial),
    commSub_zpowers_eq_map (W := I) hIpow]
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨(u : W), u.2, ?_⟩
    rw [← hu]
    rfl
  · rintro ⟨v, hv, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨commHom (restrictAutToInvariant (I := I) hIinv z) ⟨v, hv⟩,
        Subgroup.mem_map.mpr ⟨⟨v, hv⟩, trivial, rfl⟩, ?_⟩
    rfl

private theorem rk_commSub_natSpn {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {n : ℕ} {I : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)]
    (hIinv : StableUnder L I)
    {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
    {eL : ↥L ≃* antiSp K} (hKf : Fintype.card K = 2 ^ n)
    {ρ : Representation (ZMod 2) (antiSp K) (Additive ↥I)} {i : ℕ}
    {φ : Additive ↥I ≃+ (Fin 4 → K)}
    (hφ : ∀ (g : antiSp K) (w : Additive ↥I),
      φ (ρ g w) = natRepS (F := K) K i g *ᵥ φ w)
    (hρ : ∀ l : ↥L, ρ (eL l) = mulAutLinear (restrictAutToInvariant (I := I) hIinv l))
    {z : ↥L} (hz : orderOf z = 2) :
    rk (commSub I (Subgroup.zpowers (z : MulAut W))) =
      n * (natRepS (F := K) K i (eL z) - 1).rank := by
  classical
  haveI : Finite K := Finite.of_fintype K
  let φlin : Additive ↥I ≃ₗ[ZMod 2] (Fin 4 → K) :=
    φ.toLinearEquiv (by
      intro c x
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl <;> simp)
  let A : Matrix (Fin 4) (Fin 4) K := natRepS (F := K) K i (eL z)
  let Lm : (Fin 4 → K) →ₗ[ZMod 2] (Fin 4 → K) :=
    (Matrix.mulVecLin (A - 1) : (Fin 4 → K) →ₗ[K] (Fin 4 → K)).restrictScalars (ZMod 2)
  let T : Additive ↥I →ₗ[ZMod 2] Additive ↥I :=
    mulAutLinear (restrictAutToInvariant (I := I) hIinv z) - 1
  have hrk : rk (commSub I (Subgroup.zpowers (z : MulAut W))) =
      rk (commSub (⊤ : Subgroup ↥I)
        (Subgroup.zpowers (restrictAutToInvariant (I := I) hIinv z))) := by
    conv_lhs => rw [← map_commSub_restrictAct hIinv hz]
    unfold rk
    rw [Subgroup.card_map_of_injective I.subtype_injective]
  have hdisp := rk_commSub_top_eq_finrank (U := ↥I)
    (g := restrictAutToInvariant (I := I) hIinv z)
  rw [hrk, hdisp]
  have hT : ∀ w : Additive ↥I, φlin (T w) = (Matrix.mulVecLin (A - 1)) (φlin w) := by
    intro w
    have h1 : T w = mulAutLinear (restrictAutToInvariant (I := I) hIinv z) w - w := rfl
    rw [h1, map_sub]
    have h2 : φlin (mulAutLinear (restrictAutToInvariant (I := I) hIinv z) w) = A *ᵥ φlin w := by
      rw [← hρ z]
      exact hφ (eL z) w
    rw [h2]
    show A *ᵥ φlin w - φlin w = (A - 1) *ᵥ φlin w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hmaprange : (LinearMap.range T).map φlin.toLinearMap =
      (LinearMap.range (Matrix.mulVecLin (A - 1))).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨φlin w, (hT w).symm⟩
    · intro hv
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hv
      refine ⟨φlin.symm v, ?_, LinearEquiv.apply_symm_apply φlin v⟩
      refine ⟨φlin.symm y, ?_⟩
      apply φlin.injective
      rw [hT, LinearEquiv.apply_symm_apply, hy, LinearEquiv.apply_symm_apply]
  have hdim : Module.finrank (ZMod 2) (LinearMap.range T) =
      Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (A - 1))) := by
    rw [← φlin.finrank_map_eq, hmaprange]
    rfl
  rw [hdim, ← Module.finrank_mul_finrank (ZMod 2) K
    (LinearMap.range (Matrix.mulVecLin (A - 1))), Nat.mul_comm]
  have hfinK : Module.finrank (ZMod 2) K = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [Nat.card_zmod, Nat.card_eq_fintype_card, hKf] at h
    exact (Nat.pow_right_injective (by norm_num) h).symm
  have hrank : Module.finrank K (LinearMap.range (Matrix.mulVecLin (A - 1))) =
      (A - 1).rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  rw [hfinK, hrank, Nat.mul_comm]

private theorem rkIdx_fixV_eq_sum {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {I J : Subgroup W}
    (hIinv : StableUnder L I) (hJinv : StableUnder L J)
    (hIJinf : I ⊓ J = ⊥) (hIJsup : I ⊔ J = ⊤)
    {z : ↥L} (hz : orderOf z = 2) :
    rkIdx (fixV (Subgroup.zpowers (z : MulAut W))) =
      rk (commSub I (Subgroup.zpowers (z : MulAut W))) +
        rk (commSub J (Subgroup.zpowers (z : MulAut W))) := by
  have hzW : orderOf (z : MulAut W) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hIpow : ∀ x ∈ Subgroup.zpowers (z : MulAut W), ∀ w ∈ I, x w ∈ I := by
    intro x hx w hw
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzW).mp hx with
      rfl | rfl
    · simpa using hw
    · exact hIinv _ z.2 w hw
  have hJpow : ∀ x ∈ Subgroup.zpowers (z : MulAut W), ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzW).mp hx with
      rfl | rfl
    · simpa using hw
    · exact hJinv _ z.2 w hw
  have hcomm : commSub (⊤ : Subgroup W) (Subgroup.zpowers (z : MulAut W)) =
      commSub I (Subgroup.zpowers (z : MulAut W)) ⊔
        commSub J (Subgroup.zpowers (z : MulAut W)) := by
    rw [commSub_zpowers_eq_map (W := ⊤) (fun _ _ _ _ => trivial),
      commSub_zpowers_eq_map (W := I) hIpow,
      commSub_zpowers_eq_map (W := J) hJpow]
    refine le_antisymm ?_ (sup_le (Subgroup.map_mono le_top) (Subgroup.map_mono le_top))
    rintro _ ⟨w, -, rfl⟩
    have hw' : w ∈ I ⊔ J := by rw [hIJsup]; trivial
    obtain ⟨i, hi, j, hj, rfl⟩ := Subgroup.mem_sup.mp hw'
    rw [map_mul]
    exact Subgroup.mul_mem_sup
      (Subgroup.mem_map.mpr ⟨i, hi, rfl⟩) (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)
  have hdisj : commSub I (Subgroup.zpowers (z : MulAut W)) ⊓
      commSub J (Subgroup.zpowers (z : MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw' : w ∈ I ⊓ J :=
      ⟨commSub_le_of_invariant hIpow hw.1, commSub_le_of_invariant hJpow hw.2⟩
    rwa [hIJinf] at hw'
  rw [rkIdx_fixV_zpowers, commV_eq_commSub, hcomm]
  have h := rk_sup_add_rk_inf (commSub I (Subgroup.zpowers (z : MulAut W)))
    (commSub J (Subgroup.zpowers (z : MulAut W)))
  rw [hdisj, rk_bot] at h
  omega

private theorem inner_involution_bound {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {n : ℕ} {I J : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)] [Module (ZMod 2) (Additive ↥J)]
    {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
    {eL : ↥L ≃* antiSp K} (hKf : Fintype.card K = 2 ^ n)
    (hIinv : StableUnder L I) (hJinv : StableUnder L J)
    (hIJinf : I ⊓ J = ⊥) (hIJsup : I ⊔ J = ⊤)
    {ρI : Representation (ZMod 2) (antiSp K) (Additive ↥I)}
    {ρJ : Representation (ZMod 2) (antiSp K) (Additive ↥J)}
    {iI iJ : ℕ}
    {φI : Additive ↥I ≃+ (Fin 4 → K)} {φJ : Additive ↥J ≃+ (Fin 4 → K)}
    (hφI : ∀ (g : antiSp K) (w : Additive ↥I),
      φI (ρI g w) = natRepS (F := K) K iI g *ᵥ φI w)
    (hφJ : ∀ (g : antiSp K) (w : Additive ↥J),
      φJ (ρJ g w) = natRepS (F := K) K iJ g *ᵥ φJ w)
    (hρI : ∀ l : ↥L, ρI (eL l) = mulAutLinear (restrictAutToInvariant (I := I) hIinv l))
    (hρJ : ∀ l : ↥L, ρJ (eL l) = mulAutLinear (restrictAutToInvariant (I := J) hJinv l))
    (hpar : iI % 2 ≠ iJ % 2)
    {z : ↥L} (hz : orderOf z = 2) :
    3 * n ≤ rkIdx (fixV (Subgroup.zpowers (z : MulAut W))) := by
  rw [rkIdx_fixV_eq_sum hIinv hJinv hIJinf hIJsup hz,
    rk_commSub_natSpn hIinv hKf hφI hρI hz,
    rk_commSub_natSpn hJinv hKf hφJ hρJ hz]
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hz'2 : eL z * eL z = 1 := by rw [← map_mul, hz2, map_one]
  have hz'1 : eL z ≠ 1 := by
    intro h
    have h1 : z = 1 := eL.injective (h.trans (map_one eL).symm)
    rw [h1, orderOf_one] at hz
    omega
  rw [rank_natRepS_parity, rank_natRepS_parity]
  have hIpar : iI % 2 = 0 ∨ iI % 2 = 1 := Nat.mod_two_eq_zero_or_one iI
  have hJpar : iJ % 2 = 0 ∨ iJ % 2 = 1 := Nat.mod_two_eq_zero_or_one iJ
  rcases involution_rank_pair hz'2 hz'1 with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases hIpar with hI | hI <;> rcases hJpar with hJ | hJ
    · exact absurd (by rw [hI, hJ]) hpar
    · rw [if_pos hI, if_neg (by rw [hJ]; norm_num), h0, h1]; omega
    · rw [if_neg (by rw [hI]; norm_num), if_pos hJ, h0, h1]; omega
    · exact absurd (by rw [hI, hJ]) hpar
  · rcases hIpar with hI | hI <;> rcases hJpar with hJ | hJ
    · exact absurd (by rw [hI, hJ]) hpar
    · rw [if_pos hI, if_neg (by rw [hJ]; norm_num), h0, h1]; omega
    · rw [if_neg (by rw [hI]; norm_num), if_pos hJ, h0, h1]; omega
    · exact absurd (by rw [hI, hJ]) hpar
  · rcases hIpar with hI | hI <;> rcases hJpar with hJ | hJ
    · exact absurd (by rw [hI, hJ]) hpar
    · rw [if_pos hI, if_neg (by rw [hJ]; norm_num), h0, h1]; omega
    · rw [if_neg (by rw [hI]; norm_num), if_pos hJ, h0, h1]; omega
    · exact absurd (by rw [hI, hJ]) hpar

private theorem eq_summand_of_irreducible {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I J : Subgroup W}
    (hIinv : StableUnder L I) (hJinv : StableUnder L J)
    (hIJinf : I ⊓ J = ⊥) (hIJsup : I ⊔ J = ⊤)
    (hIrrI : IsIrrOn L I ⊥) (hIrrJ : IsIrrOn L J ⊥)
    (hnot : ¬ SecIsoOn L I ⊥ J ⊥)
    {X : Subgroup W} (hXstab : StableUnder L X)
    (hXsimple : CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L X)
    (hXcard : Nat.card X = Nat.card I) :
    X = I ∨ X = J := by
  classical
  let I2 : Fin 2 → Subgroup W := fun i => if i = 0 then I else J
  have hI2_0 : I2 0 = I := by simp [I2]
  have hI2_1 : I2 1 = J := by simp [I2]
  have hstab2 : ∀ i, StableUnder L (I2 i) := by
    intro i; fin_cases i
    · simpa [I2] using hIinv
    · simpa [I2] using hJinv
  have hspan2 : ⨆ i, I2 i = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hIJsup]
    exact sup_le (hI2_0 ▸ le_iSup I2 0) (hI2_1 ▸ le_iSup I2 1)
  have hsup0 : (⨆ (j : Fin 2) (_ : j ≠ (0 : Fin 2)), I2 j) = J := by
    refine le_antisymm ?_ ?_
    · apply iSup_le; intro j; apply iSup_le; intro hj
      have h : j = 1 := by fin_cases j <;> simp_all
      rw [h]; exact hI2_1.le
    · rw [← hI2_1]
      exact le_iSup_of_le (f := fun j : Fin 2 => ⨆ (_ : j ≠ (0 : Fin 2)), I2 j) (a := I2 1)
        1 (le_iSup (fun _ => I2 1) (show (1 : Fin 2) ≠ 0 by simp))
  have hsup1 : (⨆ (j : Fin 2) (_ : j ≠ (1 : Fin 2)), I2 j) = I := by
    refine le_antisymm ?_ ?_
    · apply iSup_le; intro j; apply iSup_le; intro hj
      have h : j = 0 := by fin_cases j <;> simp_all
      rw [h]; exact hI2_0.le
    · rw [← hI2_0]
      exact le_iSup_of_le (f := fun j : Fin 2 => ⨆ (_ : j ≠ (1 : Fin 2)), I2 j) (a := I2 0)
        0 (le_iSup (fun _ => I2 0) (show (0 : Fin 2) ≠ 1 by simp))
  have hind2 : ∀ i, I2 i ⊓ (⨆ (j : Fin 2) (_ : j ≠ i), I2 j) = ⊥ := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [hI2_0, hsup0]; exact hIJinf
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1; rw [hI2_1, hsup1]; simpa [inf_comm] using hIJinf
  let P : CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_Proj I2 L :=
    CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_mkProj hstab2 hspan2 hind2
  have hsimple2 : ∀ i, CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L
      (I2 i) := by
    intro i; fin_cases i
    · exact ⟨hIrrI.1.ne', hIrrI.2.1, fun K hK hKle => hIrrI.2.2.2 K hK bot_le hKle⟩
    · exact ⟨hIrrJ.1.ne', hIrrJ.2.1, fun K hK hKle => hIrrJ.2.2.2 K hK bot_le hKle⟩
  obtain ⟨i, hi⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_supp_nonempty P hXsimple.1
  have hsub : ∀ j, CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_projHom P X j ≠ 1 →
      j = i := by
    intro j hj
    by_contra hji
    have hsec := CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_SecIsoOn_of_proj
      P hstab2 hsimple2 hXsimple hi hj
    fin_cases i <;> fin_cases j
    · exact absurd rfl hji
    · exact hnot (by simpa [I2] using hsec)
    · exact hnot (by simpa [I2] using
        CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_SecIsoOn_symm hsec)
    · exact absurd rfl hji
  have hXeq := CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_eq_I_of_supp_subset
    P hsimple2 hXsimple hsub
  fin_cases i
  · left; simpa [I2] using hXeq
  · right; simpa [I2] using hXeq

private theorem rank_natRepS_conj {K : Type} [Field K] [Fintype K] [CharP K 2]
    [Algebra (ZMod 2) K] (i : ℕ) (g y : antiSp K) :
    (natRepS (F := K) K i g * natRepS (F := K) K i y *
        natRepS (F := K) K i g⁻¹ - 1).rank =
      (natRepS (F := K) K i y - 1).rank := by
  classical
  have hPR : natRepS (F := K) K i g * natRepS (F := K) K i g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hRP : natRepS (F := K) K i g⁻¹ * natRepS (F := K) K i g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hPunit : IsUnit (natRepS (F := K) K i g) := isUnit_iff_exists_inv.mpr ⟨_, hPR⟩
  have hRunit : IsUnit (natRepS (F := K) K i g⁻¹) := isUnit_iff_exists_inv.mpr ⟨_, hRP⟩
  have hunit : IsUnit (natRepS (F := K) K i g).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPunit
  have hunitR : IsUnit (natRepS (F := K) K i g⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hRunit
  have hmat : natRepS (F := K) K i g * natRepS (F := K) K i y *
        natRepS (F := K) K i g⁻¹ - 1 =
      natRepS (F := K) K i g * (natRepS (F := K) K i y - 1) *
        natRepS (F := K) K i g⁻¹ := by
    calc natRepS (F := K) K i g * natRepS (F := K) K i y *
          natRepS (F := K) K i g⁻¹ - 1
        = natRepS (F := K) K i g * natRepS (F := K) K i y *
            natRepS (F := K) K i g⁻¹ -
            natRepS (F := K) K i g * natRepS (F := K) K i g⁻¹ := by rw [hPR]
      _ = (natRepS (F := K) K i g * natRepS (F := K) K i y -
            natRepS (F := K) K i g) * natRepS (F := K) K i g⁻¹ := by
          rw [← Matrix.sub_mul]
      _ = (natRepS (F := K) K i g * (natRepS (F := K) K i y - 1)) *
            natRepS (F := K) K i g⁻¹ := by
          rw [Matrix.mul_sub, Matrix.mul_one]
      _ = natRepS (F := K) K i g * (natRepS (F := K) K i y - 1) *
            natRepS (F := K) K i g⁻¹ := by rw [mul_assoc]
  calc (natRepS (F := K) K i g * natRepS (F := K) K i y *
        natRepS (F := K) K i g⁻¹ - 1).rank
      = (natRepS (F := K) K i g * (natRepS (F := K) K i y - 1) *
          natRepS (F := K) K i g⁻¹).rank := by rw [hmat]
    _ = (natRepS (F := K) K i g * ((natRepS (F := K) K i y - 1) *
          natRepS (F := K) K i g⁻¹)).rank := by rw [mul_assoc]
    _ = ((natRepS (F := K) K i y - 1) * natRepS (F := K) K i g⁻¹).rank :=
        Matrix.rank_mul_eq_right_of_isUnit_det (natRepS (F := K) K i g)
          ((natRepS (F := K) K i y - 1) * natRepS (F := K) K i g⁻¹) hunit
    _ = (natRepS (F := K) K i y - 1).rank :=
        Matrix.rank_mul_eq_left_of_isUnit_det (natRepS (F := K) K i g⁻¹)
          (natRepS (F := K) K i y - 1) hunitR

private theorem secIsoOn_of_map_eq {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {A B : Subgroup W} (hA : StableUnder L A) (hB : StableUnder L B)
    {c : MulAut W} (hcomm : ∀ l ∈ L, c * l = l * c)
    (hm : A.map c.toMonoidHom = B) : SecIsoOn L A ⊥ B ⊥ := by
  refine ⟨bot_le, bot_le, hA, ?_, hB, ?_, ?_⟩
  · intro g hg x hx
    simpa using hx
  · intro g hg x hx
    simpa using hx
  · refine ⟨c.toMonoidHom.comp A.subtype, ?_, ?_, ?_, ?_⟩
    · intro a
      rw [← hm]
      exact Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩
    · intro a
      constructor
      · intro h
        rw [Subgroup.mem_bot] at h ⊢
        exact c.injective (by simpa using h)
      · intro h
        have ha : a = 1 := by simpa [Subgroup.mem_bot] using h
        show ((c.toMonoidHom.comp A.subtype) a) ∈ (⊥ : Subgroup W)
        rw [Subgroup.mem_bot, ha, map_one]
    · intro b hb
      rw [← hm] at hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [Subgroup.mem_bot]
      simp
    · intro g hg a a' ha'
      rw [Subgroup.mem_bot]
      have h1 : (a' : W) = g (a : W) := ha'
      have h := congrArg (fun f : MulAut W => f (a : W)) (hcomm g hg)
      show c (a' : W) * (g (c (a : W)))⁻¹ = 1
      rw [h1, show c (g (a : W)) = g (c (a : W)) from h]
      group

private theorem eq_one_on_of_centralizes_summand {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {I : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)]
    (hIinv : StableUnder L I) (hIrr : IsIrrOn L I ⊥)
    {c : MulAut W} (hcI : ∀ x ∈ I, c x ∈ I) (hc2 : c * c = 1)
    (hcomm : ∀ l ∈ L, c * l = l * c) :
    ∀ x ∈ I, c x = x := by
  classical
  let cI : MulAut ↥I :=
    { toFun := fun x => ⟨c x, hcI x x.2⟩
      invFun := fun x => ⟨c x, hcI x x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        have h := congrArg (fun f : MulAut W => f (x : W)) hc2
        simpa [pow_two] using h
      right_inv := fun x => by
        apply Subtype.ext
        have h := congrArg (fun f : MulAut W => f (x : W)) hc2
        simpa [pow_two] using h
      map_mul' := fun x y => by
        apply Subtype.ext
        simp [map_mul] }
  have hcI2 : cI ^ 2 = 1 := by
    rw [pow_two]
    ext x
    have h := congrArg (fun f : MulAut W => f (x : W)) hc2
    simpa [cI, MulAut.mul_apply, pow_two] using h
  let H : Subgroup (MulAut ↥I) := (restrictAutToInvariant hIinv).range
  have hIrrH : IsIrrOn H ⊤ ⊥ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro hbot
      obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIrr.1.ne'
      have hmem : x ∈ (⊥ : Subgroup ↥I) := by
        rw [← hbot]; exact Subgroup.mem_top _
      have hone : x = 1 := by simpa using hmem
      exact hxne hone
    · intro h _ x _
      exact Subgroup.mem_top _
    · intro h _ x hx
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx, map_one]
    · intro K hK _ _
      have hKinv : StableUnder L (K.map I.subtype) := by
        intro l hl x hx
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr
          ⟨⟨(l : MulAut W) (k : W), hIinv l hl (k : W) k.2⟩, ?_, rfl⟩
        have hmemH : restrictAutToInvariant hIinv (⟨l, hl⟩ : ↥L) ∈ H := by
          exact ⟨⟨l, hl⟩, rfl⟩
        exact hK (restrictAutToInvariant hIinv ⟨l, hl⟩) hmemH k hk
      rcases hIrr.2.2.2 (K.map I.subtype) hKinv bot_le
        (by rintro _ ⟨k, -, rfl⟩; exact k.2) with h | h
      · left
        apply le_antisymm
        · intro k hk
          have hkm : (k : W) ∈ (⊥ : Subgroup W) := by
            rw [← h]; exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
          rw [Subgroup.mem_bot] at hkm
          exact Subtype.ext hkm
        · exact bot_le
      · right
        apply le_antisymm le_top
        intro k _
        have hkI : (k : W) ∈ K.map I.subtype := by rw [h]; exact k.2
        obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp hkI
        have hk'k : k' = k := Subtype.ext hkk'
        rw [← hk'k]
        exact hk'
  have hcommH : ∀ h ∈ H, cI * h = h * cI := by
    rintro h ⟨l, rfl⟩
    ext x
    have h1 := congrArg (fun f : MulAut W => f (x : W)) (hcomm l l.2)
    change c ((l : MulAut W) (x : W)) = (l : MulAut W) (c (x : W))
    exact h1
  have hV : ∀ x : ↥I, x ^ 2 = 1 := fun x => Subtype.ext (by
    have h := hW (x : W)
    rwa [pow_two] at h ⊢)
  have hcI1 : cI = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.eq_one_of_commute_of_isIrrOn
      hV hIrrH hcI2 hcommH
  intro x hx
  have h := congrArg (fun f : MulAut ↥I => (f ⟨x, hx⟩ : ↥I)) hcI1
  have hval := congrArg Subtype.val h
  simpa [cI] using hval

private theorem preserves_I_false {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {n : ℕ} {I J : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)] [Module (ZMod 2) (Additive ↥J)]
    (hLY : L ≤ Y) (hLN : (L.subgroupOf Y).Normal)
    (hSp : IsSp4 ↥L n) (hodd : Odd n) (hn : 1 < n)
    (hI : NatSpn L I ⊥ 4 n) (hJ : NatSpn L J ⊥ 4 n)
    (hIJinf : I ⊓ J = ⊥) (hIJsup : I ⊔ J = ⊤) (hnot : ¬ SecIsoOn L I ⊥ J ⊥)
    {t : MulAut W} (htY : t ∈ Y) (htL : t ∉ L) (ht2 : orderOf t = 2)
    (hmapI : I.map t.toMonoidHom = I) : False := by  classical
  obtain ⟨hn2, K, hKfield, hKfin, hKchar, hKcard, ⟨eL0⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.exists_antiSp_of_isSp4 hSp
  letI : Field K := hKfield
  letI : Fintype K := hKfin
  letI : Finite K := Finite.of_fintype K
  letI : CharP K 2 := hKchar
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let eL : ↥L ≃* antiSp K := eL0
  have hKf : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hKcard
  have hn1 : 1 ≤ n := by omega
  have hIrrI : IsIrrOn L I ⊥ := isIrrOn_of_natSpn hI hn
  have hIrrJ : IsIrrOn L J ⊥ := isIrrOn_of_natSpn hJ hn
  have hIinv : StableUnder L I := hIrrI.2.1
  have hJinv : StableUnder L J := hIrrJ.2.1
  have hsimpleI : CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L I :=
    ⟨hIrrI.1.ne', hIrrI.2.1, fun K hK hKle => hIrrI.2.2.2 K hK bot_le hKle⟩
  have hsimpleJ : CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L J :=
    ⟨hIrrJ.1.ne', hIrrJ.2.1, fun K hK hKle => hIrrJ.2.2.2 K hK bot_le hKle⟩
  have hIJcard : Nat.card ↥I = Nat.card ↥J := by
    obtain ⟨-, KI, hKIfield, hKIfin, hKIcard, πI, hrealI⟩ := hI
    obtain ⟨-, KJ, hKJfield, hKJfin, hKJcard, πJ, hrealJ⟩ := hJ
    letI : Field KI := hKIfield
    letI : Finite KI := hKIfin
    letI : Field KJ := hKJfield
    letI : Finite KJ := hKJfin
    rw [card_of_realizes_natSp hrealI, card_of_realizes_natSp hrealJ, hKIcard, hKJcard]
  have hnorm : ∀ h k : MulAut W, h ∈ L → k ∈ Y → k * h * k⁻¹ ∈ L :=
    (Subgroup.normal_subgroupOf_iff hLY).mp hLN
  have hnorm' : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L :=
    fun y hy l hl => hnorm l y hl hy
  have ht2' : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  let αL : MulAut ↥L :=
    { toFun := fun l => ⟨t * (l : MulAut W) * t⁻¹, hnorm l t l.2 htY⟩
      invFun := fun l => ⟨t⁻¹ * (l : MulAut W) * t, hnorm l t⁻¹ l.2 (Y.inv_mem htY)⟩
      left_inv := fun l => by
        apply Subtype.ext
        change t⁻¹ * (t * (l : MulAut W) * t⁻¹) * t = (l : MulAut W)
        group
      right_inv := fun l => by
        apply Subtype.ext
        change t * (t⁻¹ * (l : MulAut W) * t) * t⁻¹ = (l : MulAut W)
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        change t * ((a : MulAut W) * b) * t⁻¹ =
          t * a * t⁻¹ * (t * b * t⁻¹)
        group }
  let α : MulAut (antiSp K) := MulAut.congr eL αL
  have hα_apply : ∀ l : ↥L, α (eL l) = eL ⟨t * (l : MulAut W) * t⁻¹,
      hnorm l t l.2 htY⟩ := by
    intro l
    change eL (αL (eL.symm (eL l))) = eL ⟨t * (l : MulAut W) * t⁻¹,
      hnorm l t l.2 htY⟩
    rw [eL.symm_apply_apply]
    rfl
  have hα2 : α * α = 1 := by
    have hαL2 : αL * αL = 1 := by
      ext l x
      change (t * (t * (l : MulAut W) * t⁻¹) * t⁻¹) (x : W) =
        (l : MulAut W) (x : W)
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
      rw [hti]
      have hg : t * (t * (l : MulAut W) * t) * t = (l : MulAut W) := by
        calc t * (t * (l : MulAut W) * t) * t
            = (t * t) * (l : MulAut W) * (t * t) := by group
          _ = (l : MulAut W) := by rw [ht2']; group
      rw [hg]
    change MulAut.congr eL αL * MulAut.congr eL αL = 1
    rw [← map_mul, hαL2, map_one]
  have inner_case : ∀ g : antiSp K, α = MulAut.conj g → False := by
    intro g hαeq
    let l : ↥L := eL.symm g
    have hle : eL l = g := eL.apply_symm_apply g
    have htlt : t * (l : MulAut W) * t⁻¹ = (l : MulAut W) := by
      have h1 := hα_apply l
      have h2 : α (eL l) = MulAut.conj g (eL l) := by rw [hαeq]
      rw [h2, hle] at h1
      have h3 : MulAut.conj g g = g := by simp [MulAut.conj_apply]
      rw [h3] at h1
      have h4 : eL ⟨t * (l : MulAut W) * t⁻¹, hnorm l t l.2 htY⟩ = eL l := by
        rw [← h1, hle]
      exact congrArg Subtype.val (eL.injective h4)
    have hgg : g * g = 1 := by
      have hconj : MulAut.conj (g * g) = 1 := by
        rw [map_mul, ← hαeq, hα2]
      exact conj_injective (by rw [hconj, map_one])
    have hl2 : (l : MulAut W) * (l : MulAut W) = 1 := by
      have h1 : eL l * eL l = 1 := by rw [hle, hgg]
      rw [← map_mul] at h1
      have h2 : l * l = 1 := eL.injective (by rw [h1]; exact (map_one eL).symm)
      simpa using congrArg Subtype.val h2
    have htl : t * (l : MulAut W) = (l : MulAut W) * t := by
      calc t * (l : MulAut W) = (t * (l : MulAut W) * t⁻¹) * t := by group
        _ = (l : MulAut W) * t := by rw [htlt]
    let c : MulAut W := (l : MulAut W)⁻¹ * t
    have hc2 : c * c = 1 := by
      have htl_inv : t * (l : MulAut W)⁻¹ = (l : MulAut W)⁻¹ * t := by
        calc t * (l : MulAut W)⁻¹ = (l * t⁻¹)⁻¹ := by group
          _ = (l * t)⁻¹ := by rw [inv_eq_of_mul_eq_one_right ht2']
          _ = (t * l)⁻¹ := by rw [htl]
          _ = (l : MulAut W)⁻¹ * t := by
              rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2']
      show ((l : MulAut W)⁻¹ * t) * ((l : MulAut W)⁻¹ * t) = 1
      calc (l : MulAut W)⁻¹ * t * ((l : MulAut W)⁻¹ * t)
          = (l : MulAut W)⁻¹ * (t * (l : MulAut W)⁻¹) * t := by group
        _ = (l : MulAut W)⁻¹ * ((l : MulAut W)⁻¹ * t) * t := by rw [htl_inv]
        _ = ((l : MulAut W) * (l : MulAut W))⁻¹ * (t * t) := by group
        _ = 1 := by rw [hl2, ht2']; group
    have hcY : c ∈ Y := Y.mul_mem (Y.inv_mem (hLY l.2)) htY
    have hc_comm : ∀ m ∈ L, c * m = m * c := by
      intro m hm
      have h1 := hα_apply ⟨m, hm⟩
      have h2 : α (eL ⟨m, hm⟩) = MulAut.conj g (eL ⟨m, hm⟩) := by rw [hαeq]
      rw [h2, ← hle] at h1
      have h5 : eL ⟨t * m * t⁻¹, hnorm m t hm htY⟩ =
          eL ⟨(l : MulAut W) * m * (l : MulAut W)⁻¹,
            L.mul_mem (L.mul_mem l.2 hm) (L.inv_mem l.2)⟩ := by
        rw [← h1, MulAut.conj_apply]
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl
      have h4 : t * m * t⁻¹ = (l : MulAut W) * m * (l : MulAut W)⁻¹ :=
        congrArg Subtype.val (eL.injective h5)
      show ((l : MulAut W)⁻¹ * t) * m = m * ((l : MulAut W)⁻¹ * t)
      calc (l : MulAut W)⁻¹ * t * m
          = (l : MulAut W)⁻¹ * (t * m * t⁻¹) * t := by group
        _ = (l : MulAut W)⁻¹ * ((l : MulAut W) * m * (l : MulAut W)⁻¹) * t := by
              rw [h4]
        _ = m * ((l : MulAut W)⁻¹ * t) := by group
    have hcI_stab : StableUnder L (I.map c.toMonoidHom) := by
      intro m hm x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨m y, hIinv m hm y hy, ?_⟩
      have h := congrArg (fun f : MulAut W => f y) (hc_comm m hm)
      simpa [MulAut.mul_apply] using h
    have hcI_card : Nat.card ↥(I.map c.toMonoidHom) = Nat.card ↥I :=
      Subgroup.card_map_of_injective (K := I) (f := c.toMonoidHom) c.injective
    have hcI_simple :
        CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L
          (I.map c.toMonoidHom) :=
      CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_simple_map hnorm' hsimpleI hcY
    have hcI_eq : I.map c.toMonoidHom = I := by
      rcases eq_summand_of_irreducible hIinv hJinv hIJinf hIJsup hIrrI hIrrJ hnot
        hcI_stab hcI_simple hcI_card with h | h
      · exact h
      · exact (hnot (secIsoOn_of_map_eq hIinv hJinv hc_comm h)).elim
    have hcJ_stab : StableUnder L (J.map c.toMonoidHom) := by
      intro m hm x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨m y, hJinv m hm y hy, ?_⟩
      have h := congrArg (fun f : MulAut W => f y) (hc_comm m hm)
      simpa [MulAut.mul_apply] using h
    have hcJ_card : Nat.card ↥(J.map c.toMonoidHom) = Nat.card ↥I := by
      rw [Subgroup.card_map_of_injective (K := J) (f := c.toMonoidHom) c.injective,
        hIJcard]
    have hcJ_simple :
        CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L
          (J.map c.toMonoidHom) :=
      CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_simple_map hnorm' hsimpleJ hcY
    have hcJ_eq : J.map c.toMonoidHom = J := by
      rcases eq_summand_of_irreducible hIinv hJinv hIJinf hIJsup hIrrI hIrrJ hnot
        hcJ_stab hcJ_simple hcJ_card with h | h
      · exact (hnot
          (CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_SecIsoOn_symm
            (secIsoOn_of_map_eq hJinv hIinv hc_comm h))).elim
      · exact h
    have hcI_fix : ∀ x ∈ I, c x = x :=
      eq_one_on_of_centralizes_summand hW hIinv hIrrI
        (fun x hx => by rw [← hcI_eq]; exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
        hc2 hc_comm
    have hcJ_fix : ∀ x ∈ J, c x = x :=
      eq_one_on_of_centralizes_summand hW hJinv hIrrJ
        (fun x hx => by rw [← hcJ_eq]; exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
        hc2 hc_comm
    have hc1 : c = 1 := by
      ext x
      have hx : x ∈ I ⊔ J := by rw [hIJsup]; trivial
      rcases Subgroup.mem_sup.mp hx with ⟨i, hi, j, hj, rfl⟩
      show c (i * j) = i * j
      rw [map_mul, hcI_fix i hi, hcJ_fix j hj]
    have htL' : t ∈ L := by
      have ht_eq : t = (l : MulAut W) * c := by
        show t = (l : MulAut W) * ((l : MulAut W)⁻¹ * t)
        group
      rw [ht_eq, hc1, mul_one]
      exact l.2
    exact htL htL'

  have graph_case : ∀ g : antiSp K, α = MulAut.conj g * minorAut K ^ n → False := by
    intro g hαeq
    have hy2 : orderOf (invX K) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact invX_mul_self) (invX_ne_one)
    let z : ↥L := eL.symm (invX K)
    let z' : ↥L := eL.symm (α (invX K))
    have hz : orderOf z = 2 := by
      rw [show orderOf z = orderOf (eL z) from (MulEquiv.orderOf_eq eL z).symm]
      rw [show eL z = invX K from eL.apply_symm_apply _]
      exact hy2
    have hz' : orderOf z' = 2 := by
      rw [show orderOf z' = orderOf (eL z') from (MulEquiv.orderOf_eq eL z').symm]
      rw [show eL z' = α (invX K) from eL.apply_symm_apply _]
      rw [show orderOf (α (invX K)) = orderOf (invX K) from (MulEquiv.orderOf_eq α _)]
      exact hy2
    have htzt : t * (z : MulAut W) * t⁻¹ = (z' : MulAut W) := by
      have h1 := hα_apply z
      rw [show eL z = invX K from eL.apply_symm_apply _] at h1
      have h2 : eL ⟨t * (z : MulAut W) * t⁻¹, hnorm z t z.2 htY⟩ = eL z' := by
        rw [← h1, show eL z' = α (invX K) from eL.apply_symm_apply _]
      exact congrArg Subtype.val (eL.injective h2)
    have hcommSubEq : (commSub I (Subgroup.zpowers (z : MulAut W))).map t.toMonoidHom =
        commSub I (Subgroup.zpowers (z' : MulAut W)) := by
      rw [commSub_zpowers_eq_map (W := I)
          (fun x hx w hw => hIinv x (Subgroup.zpowers_le.mpr z.2 hx) w hw),
        commSub_zpowers_eq_map (W := I)
          (fun x hx w hw => hIinv x (Subgroup.zpowers_le.mpr z'.2 hx) w hw),
        Subgroup.map_map]
      have hcomp : t.toMonoidHom.comp (commHom (z : MulAut W)) =
          (commHom (t * (z : MulAut W) * t⁻¹)).comp t.toMonoidHom := by
        ext x
        simp [MulAut.mul_apply, commHom, mul_assoc]
      rw [hcomp, ← Subgroup.map_map, hmapI, htzt]
    have hrk : rk (commSub I (Subgroup.zpowers (z : MulAut W))) =
        rk (commSub I (Subgroup.zpowers (z' : MulAut W))) := by
      rw [← hcommSubEq]
      rw [rk, rk, Subgroup.card_map_of_injective
        (K := commSub I (Subgroup.zpowers (z : MulAut W)))
        (f := t.toMonoidHom) t.injective]
    obtain ⟨ρI, iI, φI, hφI, -, -, hrelI, -⟩ := summand_label hW hSp hn hKcard eL hI
    have hρI : ∀ l : ↥L, ρI (eL l) = mulAutLinear (restrictAutToInvariant hIinv l) := by
      intro l
      refine LinearMap.ext fun w => ?_
      refine Additive.toMul.injective ?_
      refine Subtype.ext ?_
      rw [mulAutLinear_apply]
      exact hrelI l w
    have hrkz := rk_commSub_natSpn (I := I) hIinv hKf (ρ := ρI) (i := iI) (φ := φI) hφI hρI hz
    have hrkz' := rk_commSub_natSpn (I := I) hIinv hKf (ρ := ρI) (i := iI) (φ := φI) hφI hρI hz'
    rw [hrkz, hrkz'] at hrk
    have hrank : (natRepS (F := K) K iI (invX K) - 1).rank =
        (natRepS (F := K) K iI (α (invX K)) - 1).rank := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < n by omega)
      rw [show eL z = invX K from eL.apply_symm_apply _,
        show eL z' = α (invX K) from eL.apply_symm_apply _] at hrk
      exact hrk
    have hnat : natRepS (F := K) K iI (α (invX K)) =
        natRepS (F := K) K iI g *
          natRepS (F := K) K iI ((minorAut K ^ n) (invX K)) *
          natRepS (F := K) K iI g⁻¹ := by
      rw [hαeq, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul]
    rw [hnat, rank_natRepS_conj (i := iI) (g := g)
      (y := (minorAut K ^ n) (invX K)), natRepS_comp_pow] at hrank
    rw [rank_natRepS_parity (invX K) iI, rank_natRepS_parity (invX K) (iI + n),
      rk0_invX, rk1_invX] at hrank
    have hodd2 : n % 2 = 1 := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hpar : iI % 2 = 0 ∨ iI % 2 = 1 := by omega
    rcases hpar with h0 | h1
    · rw [h0] at hrank
      have h : ¬ (iI + n) % 2 = 0 := by omega
      rw [if_pos rfl, if_neg h] at hrank
      norm_num at hrank
    · rw [h1] at hrank
      have h : (iI + n) % 2 = 0 := by omega
      rw [if_neg (by norm_num : ¬ (1 : ℕ) = 0), if_pos h] at hrank
      norm_num at hrank

  by_cases hα1 : α = 1
  · exact inner_case 1 (by rw [hα1, map_one])
  · have hαord : orderOf α = 2 := orderOf_eq_prime (by rwa [sq]) hα1
    obtain ⟨g, j, hj, hαeq⟩ := involution_eq_conj_mul_pow hn1 hKcard α hαord
    rcases hj with hj0 | hjn
    · exact inner_case g (by rw [hαeq, hj0]; simp)
    · exact graph_case g (by rw [hαeq, hjn])


private theorem outer_bound {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {n : ℕ} {I J : Subgroup W}
    [Module (ZMod 2) (Additive ↥I)] [Module (ZMod 2) (Additive ↥J)]
    (hLY : L ≤ Y) (hLN : (L.subgroupOf Y).Normal)
    (hSp : IsSp4 ↥L n) (hodd : Odd n) (hn : 1 < n)
    (hI : NatSpn L I ⊥ 4 n) (hJ : NatSpn L J ⊥ 4 n)
    (hIJinf : I ⊓ J = ⊥) (hIJsup : I ⊔ J = ⊤) (hnot : ¬ SecIsoOn L I ⊥ J ⊥)
    {t : MulAut W} (htY : t ∈ Y) (htL : t ∉ L) (ht2 : orderOf t = 2) :
    3 * n ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hIrrI : IsIrrOn L I ⊥ := isIrrOn_of_natSpn hI hn
  have hIrrJ : IsIrrOn L J ⊥ := isIrrOn_of_natSpn hJ hn
  have hnorm : ∀ h k : MulAut W, h ∈ L → k ∈ Y → k * h * k⁻¹ ∈ L :=
    (Subgroup.normal_subgroupOf_iff hLY).mp hLN
  have hnorm' : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L :=
    fun y hy l hl => hnorm l y hl hy
  have hsimpleI : CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L I :=
    ⟨hIrrI.1.ne', hIrrI.2.1, fun K hK hKle => hIrrI.2.2.2 K hK bot_le hKle⟩
  have hXstab : StableUnder L (I.map t.toMonoidHom) := by
    intro l hl x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(t⁻¹ * l * t) a, ?_, ?_⟩
    · exact hIrrI.2.1 (t⁻¹ * l * t) (hnorm l t⁻¹ hl (Y.inv_mem htY)) a ha
    · show t ((t⁻¹ * l * t) a) = l (t a)
      simp [MulAut.mul_apply, mul_assoc]
  have hXsimple : CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_IsSimple L
      (I.map t.toMonoidHom) :=
    CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_simple_map hnorm' hsimpleI htY
  have hXcard : Nat.card ↥(I.map t.toMonoidHom) = Nat.card ↥I :=
    Subgroup.card_map_of_injective (K := I) (f := t.toMonoidHom) t.injective
  rcases eq_summand_of_irreducible hIrrI.2.1 hIrrJ.2.1 hIJinf hIJsup hIrrI hIrrJ hnot
      hXstab hXsimple hXcard with hmapI | hmapJ
  · exact (preserves_I_false hW hLY hLN hSp hodd hn hI hJ hIJinf hIJsup hnot htY htL ht2 hmapI).elim
  · have hCinf : fixV (Subgroup.zpowers t) ⊓ I = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf, mem_fixV_zpowers] at hx
      obtain ⟨htx, hxI⟩ := hx
      have hxJ : x ∈ J := by
        rw [← hmapJ]
        exact Subgroup.mem_map.mpr ⟨x, hxI, by simpa using htx⟩
      have hmem : x ∈ I ⊓ J := ⟨hxI, hxJ⟩
      rw [hIJinf] at hmem
      simpa using hmem
    have hinj : Function.Injective ((commHom t).comp I.subtype) := by
      intro x y hxy
      apply Subtype.ext
      have hxy' : (commHom t) (x : W) = (commHom t) (y : W) := hxy
      have h1 : commHom t ((x : W) * (y : W)⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy', mul_inv_cancel]
      have hfix : ((x : W) * (y : W)⁻¹) ∈ fixV (Subgroup.zpowers t) := by
        rw [mem_fixV_zpowers]
        exact mul_inv_eq_one.mp h1
      have hmem : ((x : W) * (y : W)⁻¹) ∈ I := I.mul_mem x.2 (I.inv_mem y.2)
      have hbot : ((x : W) * (y : W)⁻¹) ∈ (⊥ : Subgroup W) := by
        rw [← hCinf]; exact ⟨hfix, hmem⟩
      rw [Subgroup.mem_bot] at hbot
      exact mul_inv_eq_one.mp hbot
    have hcard : Nat.card ↥(I.map (commHom t)) = Nat.card ↥I := by
      have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥I))
        (f := (commHom t).comp I.subtype) hinj
      simpa using h
    have hle : I.map (commHom t) ≤ commV (Subgroup.zpowers t) := by
      rw [commV_eq_commSub, commSub_zpowers_eq_map (W := ⊤) (fun _ _ _ _ => trivial)]
      exact Subgroup.map_mono le_top
    have hrkImage : rk ↥(I.map (commHom t)) = rk ↥I := by
      rw [rk, rk, hcard]
    have hrkLe : rk ↥(I.map (commHom t)) ≤ rk ↥(commV (Subgroup.zpowers t)) :=
      rk_mono hle
    have hrkI : rk ↥I = 4 * n := by
      obtain ⟨-, K, hKfield, hKfin, hKcard, π, hreal⟩ := hI
      letI : Field K := hKfield
      letI : Finite K := hKfin
      have hc : Nat.card ↥I = 2 ^ (4 * n) := by
        rw [card_of_realizes_natSp hreal, hKcard, ← pow_mul,
          show n * 4 = 4 * n by omega]
      rw [rk, hc, padicValNat.prime_pow]
    have hrkV : rk ↥(commV (Subgroup.zpowers t)) = rkIdx (fixV (Subgroup.zpowers t)) :=
      (rkIdx_fixV_zpowers t).symm
    rw [← hrkV]
    calc 3 * n ≤ 4 * n := by omega
      _ = rk ↥I := hrkI.symm
      _ = rk ↥(I.map (commHom t)) := hrkImage.symm
      _ ≤ rk ↥(commV (Subgroup.zpowers t)) := hrkLe

theorem k146Sp4TwoNat_holds : K146Sp4TwoNat := by
  intro W _ _ hW Y L n I J hLY hLN hSp hodd hn hI hJ hIJinf hIJsup hnot
  classical
  obtain ⟨-, K, hKfield, hKfin, hKchar, hKcard, ⟨eL0⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.exists_antiSp_of_isSp4 hSp
  letI : Field K := hKfield
  letI : Fintype K := hKfin
  letI : Finite K := Finite.of_fintype K
  letI : CharP K 2 := hKchar
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let eL : ↥L ≃* antiSp K := eL0
  have hKf : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hKcard
  have hIexp : ∀ x : ↥I, x ^ 2 = 1 := fun x => Subtype.ext (by
    have h := hW (x : W)
    rwa [pow_two] at h ⊢)
  have hJexp : ∀ x : ↥J, x ^ 2 = 1 := fun x => Subtype.ext (by
    have h := hW (x : W)
    rwa [pow_two] at h ⊢)
  letI : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [two_nsmul]
      exact Additive.toMul.injective (by
        have h := hW (Additive.toMul x)
        simpa [pow_two] using h)
  letI : Module (ZMod 2) (Additive ↥I) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [two_nsmul]
      exact Additive.toMul.injective (by
        simpa [pow_two] using hIexp (Additive.toMul x))
  letI : Module (ZMod 2) (Additive ↥J) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [two_nsmul]
      exact Additive.toMul.injective (by
        simpa [pow_two] using hJexp (Additive.toMul x))
  obtain ⟨ρI, iI, φI, hφI, -, -, hrelI, hIrrI⟩ := summand_label hW hSp hn hKcard eL hI
  obtain ⟨ρJ, iJ, φJ, hφJ, -, -, hrelJ, hIrrJ⟩ := summand_label hW hSp hn hKcard eL hJ
  have hIinv : StableUnder L I := hIrrI.2.1
  have hJinv : StableUnder L J := hIrrJ.2.1
  have hρI : ∀ l : ↥L, ρI (eL l) = mulAutLinear (restrictAutToInvariant (I := I) hIinv l) := by
    intro l
    refine LinearMap.ext fun w => ?_
    refine Additive.toMul.injective ?_
    refine Subtype.ext ?_
    rw [mulAutLinear_apply]
    exact hrelI l w
  have hρJ : ∀ l : ↥L, ρJ (eL l) = mulAutLinear (restrictAutToInvariant (I := J) hJinv l) := by
    intro l
    refine LinearMap.ext fun w => ?_
    refine Additive.toMul.injective ?_
    refine Subtype.ext ?_
    rw [mulAutLinear_apply]
    exact hrelJ l w
  have hpar : iI % 2 ≠ iJ % 2 :=
    parities_differ eL hIinv hJinv hKf (by omega) hφI hφJ hρI hρJ hnot
  have hinvL : ∃ l : ↥L, orderOf l = 2 := by
    refine ⟨eL.symm (invX K), ?_⟩
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact invX_mul_self) (invX_ne_one)
  refine le_mParam_of_forall_involutions Y (3 * n) ?_ ?_ ?_
  · exact even_card_of_le_of_involution hLY hinvL
  · obtain ⟨l, hl⟩ := hinvL
    exact ⟨(l : MulAut W), hLY l.2, (Subgroup.orderOf_coe l).trans hl⟩
  · intro t htY ht2
    by_cases htL : t ∈ L
    · let z : ↥L := ⟨t, htL⟩
      have hz : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans ht2
      exact inner_involution_bound (hKf := hKf) (hIinv := hIinv) (hJinv := hJinv)
        (hIJinf := hIJinf) (hIJsup := hIJsup) (hφI := hφI) (hφJ := hφJ)
        (hρI := hρI) (hρJ := hρJ) (hpar := hpar) (z := z) (hz := hz)
    · exact outer_bound hW hLY hLN hSp hodd hn hI hJ hIJinf hIJsup hnot htY htL ht2
