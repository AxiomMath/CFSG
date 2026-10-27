module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs

import CFSG.Quasithin.Recognition.St84.Gen.NatL2Module
import CFSG.Quasithin.Recognition.St84.RelCentMap
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful
import CFSG.Quasithin.Recognition.St84.Sec6BaumannS3
import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six
import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ
import CFSG.RankThree.PartTwo.KFacts.K71Borel
import CFSG.GroupTheory.SL2SylowTwo
import CFSG.Quasithin.Vol2.Ch10SecKRPb
import CFSG.GroupTheory.OddOrderClosurePerfect
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F53Mod
  CFSG.Quasithin.H13 CFSG.Quasithin
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {L E Z T : Subgroup G} [Finite ↥L] [Finite ↥E]
  {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}

private lemma le_normalizer_of_isElemSec {K E : Subgroup G} (h : IsElemSec K E) :
    E ≤ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  exact (Subgroup.commutator_mono le_rfl h.1).trans h.2.1

private lemma le_relCent_of_le_normalizer {E Z A : Subgroup G} (hZE : Z ≤ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) : Z ≤ relCent E Z A := by
  intro z hz
  rw [mem_relCent hEZ]
  refine ⟨hZE hz, fun a ha => ?_⟩
  have hconj : a * z * a⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hAZ ha) z).mp hz
  have e : ⁅z, a⁆ = z * (a * z * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Z.mul_mem hz (Z.inv_mem hconj)

private lemma normalizer_relCent_of_le {E Z A L : Subgroup G}
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) :
    L ≤ Subgroup.normalizer (relCent E Z A : Set G) :=
  fun l hl => mem_normalizer_relCent (hLE hl) (hLZ hl) (hLA hl)

private lemma isElemSec_of_le_of_le {Y Z E : Subgroup G} (hZY : Z ≤ Y) (hYE : Y ≤ E)
    (hsec : IsElemSec Z E) : IsElemSec Y E :=
  ⟨hYE, hsec.2.1.trans hZY, fun e he => hZY (hsec.2.2 e he)⟩

theorem isNatSecOf_of_two_pow_le (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hcard : Z.relIndex E = 2 ^ (2 * n)) (hcent : relCent E Z L = Z)
    (hT : IsSylowTwoOf T L) (hC : 2 ^ n ≤ Z.relIndex (relCent E Z T)) :
    CFSG.Quasithin.F112R.St84.IsNatSecOf L E Z α := by
  classical
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_isElemSec hsec
  have hN : (Z.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEZ
  let hs : IsSec L Z E :=
    { le := hsec.1
      normN := hL.trans inf_le_left
      normL := hL.trans inf_le_right
      comm := fun x hx y hy => by
        simpa [commutatorElement_def] using
          (Subgroup.commutator_le.mp hsec.2.1) x hx y hy
      sq := fun x hx => hsec.2.2 x hx }
  have hker_le : α.ker ≤ hs.conjHom.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    have hlL : (l : G) ∈ pCoreOf 2 L := by
      rw [hker] at hl
      exact Subgroup.mem_subgroupOf.mp hl
    exact hs.conjHom_eq_one fun x hx => by
      simpa [commutatorElement_def] using hcore (l : G) hlL x hx
  let σ : SL(2, F) →* MulAut hs.W :=
    α.liftOfSurjective hα ⟨hs.conjHom, hker_le⟩
  have hσ : ∀ l : ↥L, σ (α l) = hs.conjHom l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨hs.conjHom, hker_le⟩ l
  have hsq : ∀ w : hs.W, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [← map_pow, hs.proj_eq_one_iff]
    simpa using hs.sq x x.2
  letI : Module (ZMod 2) (Additive hs.W) := zmod2ModuleOfExp hsq
  let ρ : Representation (ZMod 2) SL(2, F) (Additive hs.W) := linAutHom.comp σ
  have hρ_apply : ∀ (g : SL(2, F)) (w : hs.W),
      ρ g (Additive.ofMul w) = Additive.ofMul (σ g w) := fun g w =>
    autLin_apply (σ g) w
  have hfix : ∀ w : Additive hs.W, (∀ g, ρ g w = w) → w = 0 := by
    intro w hw
    obtain ⟨x, hx⟩ := hs.proj_surjective (Additive.toMul w)
    have hfixx : ∀ l : ↥L, hs.conjHom l (hs.proj x) = hs.proj x := by
      intro l
      have h1 : Additive.ofMul (σ (α l) (Additive.toMul w)) =
          Additive.ofMul (Additive.toMul w) := by
        have h : ρ (α l) (Additive.ofMul (Additive.toMul w)) =
            Additive.ofMul (Additive.toMul w) := hw (α l)
        simpa only [hρ_apply] using h
      rw [← hx] at h1
      simpa [hσ l] using h1
    have hcomm : ∀ l : ↥L, ⁅(x : G), (l : G)⁆ ∈ Z := by
      intro l
      have hproj : hs.proj (hs.conjN l x) = hs.proj x := by
        rw [← IsSec.conjHom_mk]
        exact hfixx l
      have hmem : ((hs.conjN l x * x⁻¹ : ↥E) : G) ∈ Z := by
        refine (hs.proj_eq_one_iff _).mp ?_
        rw [map_mul, map_inv, hproj, mul_inv_cancel]
      have hlx : ⁅(l : G), (x : G)⁆ ∈ Z := by
        simpa [IsSec.conjN, commutatorElement_def, mul_assoc] using hmem
      have e : ⁅(x : G), (l : G)⁆ = ⁅(l : G), (x : G)⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Z.inv_mem hlx
    have hxrel : (x : G) ∈ relCent E Z L := by
      rw [mem_relCent hEZ]
      exact ⟨x.2, fun l hl => hcomm ⟨l, hl⟩⟩
    have hxZ : (x : G) ∈ Z := hcent ▸ hxrel
    have hx1 : hs.proj x = 1 := (hs.proj_eq_one_iff x).mpr hxZ
    calc w = Additive.ofMul (Additive.toMul w) := (ofMul_toMul w).symm
      _ = Additive.ofMul (hs.proj x) := by rw [hx]
      _ = 0 := by rw [hx1]; rfl
  let B : Subgroup SL(2, F) := (T.subgroupOf L).map α
  have hBsyl : IsSylowTwoOf B ⊤ :=
    CFSG.Quasithin.Vol2.Ch10.SecA.isSylowTwoOf_map_of_surjective hT α hα
  obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.Unc25K1.exists_sylow_of_isSylowTwoOf_top hBsyl
  obtain ⟨hBelem, hBcardF, -⟩ := CFSG.RankThree.PartTwo.KFacts.sylow_two_sl2 S
  have hBelemB : CFSG.Open.IsElemAbelian 2 B := by
    rw [← hS]
    exact hBelem
  haveI : CFSG.IsElementaryAbelian 2 B :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).mpr hBelemB
  have hBcardF' : Nat.card B = Nat.card F := by
    rw [← hS]
    exact hBcardF
  have hBcard : Nat.card B = 2 ^ n := by
    rw [hBcardF', Nat.card_eq_fintype_card, hF]
  have hBne : B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card B = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hBcard] at h1
    have h2 : 1 < 2 ^ n := by
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  haveI : Finite hs.W := Finite.of_surjective hs.proj hs.proj_surjective
  let Fix : Subgroup hs.W :=
    { carrier := {w | ∀ b ∈ B, ρ b (Additive.ofMul w) = Additive.ofMul w}
      one_mem' := by
        intro b _
        change ρ b 0 = 0
        exact map_zero _
      mul_mem' := by
        intro a b ha hb c hc
        change ρ c (Additive.ofMul a + Additive.ofMul b) =
          Additive.ofMul a + Additive.ofMul b
        rw [map_add, ha c hc, hb c hc]
      inv_mem' := by
        intro a ha c hc
        change ρ c (-Additive.ofMul a) = -Additive.ofMul a
        rw [map_neg, ha c hc] }
  have hmapFix : ((fixSecIn T Z E).subgroupOf E).map hs.proj ≤ Fix := by
    rintro w ⟨x, hxN, rfl⟩
    have hxG : (x : G) ∈ fixSecIn T Z E := Subgroup.mem_subgroupOf.mp hxN
    rw [mem_fixSecIn_iff hEZ] at hxG
    intro b hb
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hb
    have htL : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp htT
    have hconj : ((hs.conjN t x * x⁻¹ : ↥E) : G) ∈ Z := by
      simpa [IsSec.conjN] using hxG.2 (t : G) htL
    have hproj : hs.proj (hs.conjN t x) = hs.proj x := by
      have h1 : hs.proj (hs.conjN t x) * (hs.proj x)⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]
        exact (hs.proj_eq_one_iff _).mpr hconj
      exact mul_inv_eq_one.mp h1
    show ρ (α t) (Additive.ofMul (hs.proj x)) = Additive.ofMul (hs.proj x)
    rw [hρ_apply, hσ, IsSec.conjHom_mk, hproj]
  have hprojker : hs.proj.ker = Z.subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, hs.proj_eq_one_iff]
    exact Iff.rfl
  have hfixE : fixSecIn T Z E ≤ E :=
    (Subgroup.closure_le E).mpr fun _ hx => hx.1
  have hNcard : Nat.card (((fixSecIn T Z E).subgroupOf E).map hs.proj) =
      Z.relIndex (fixSecIn T Z E) := by
    rw [← Subgroup.relIndex_ker (K := (fixSecIn T Z E).subgroupOf E) hs.proj, hprojker]
    exact Subgroup.relIndex_subgroupOf (H := Z) (K := fixSecIn T Z E) (L := E) hfixE
  have hFixcard : 2 ^ n ≤ Nat.card ↥Fix := by
    have hCfix : 2 ^ n ≤ Z.relIndex (fixSecIn T Z E) := by
      rw [← relCent_eq_fixSecIn hsec.1 hEZ]
      exact hC
    calc 2 ^ n ≤ Z.relIndex (fixSecIn T Z E) := hCfix
      _ = Nat.card (((fixSecIn T Z E).subgroupOf E).map hs.proj) := hNcard.symm
      _ ≤ Nat.card ↥Fix := Subgroup.card_le_of_le hmapFix
  have hfixcardEq : Nat.card {w : Additive hs.W // ∀ a ∈ B, ρ a w = w} =
      Nat.card ↥Fix :=
    Nat.card_congr
      { toFun := fun w => ⟨Additive.toMul w.1, w.2⟩
        invFun := fun w => ⟨Additive.ofMul w.1, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hWcard : Nat.card (Additive hs.W) = 2 ^ (2 * n) := by
    rw [Nat.card_congr Additive.toMul]
    exact hcard
  have hWbig : 1 < Nat.card (Additive hs.W) := by
    rw [hWcard]
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Finite (Additive hs.W) := inferInstance
  haveI : Nontrivial (Additive hs.W) := Finite.one_lt_card_iff_nontrivial.mp hWbig
  have hfixcard' : 2 ^ n ≤
      Nat.card {w : Additive hs.W // ∀ a ∈ B, ρ a w = w} := by
    rw [hfixcardEq]
    exact hFixcard
  have hoff : Nat.card (Additive hs.W) ≤
      Nat.card B * Nat.card {w : Additive hs.W // ∀ a ∈ B, ρ a w = w} := by
    calc Nat.card (Additive hs.W) = 2 ^ (2 * n) := hWcard
      _ = 2 ^ n * 2 ^ n := by
        rw [show 2 * n = n + n by omega, pow_add]
      _ = Nat.card B * 2 ^ n := by rw [hBcard]
      _ ≤ Nat.card B * Nat.card {w : Additive hs.W // ∀ a ∈ B, ρ a w = w} :=
        Nat.mul_le_mul_left _ hfixcard'
  obtain ⟨-, -, φ, hφ⟩ := exists_natural_of_offender hn hF ρ hfix B hBne hoff
  let eφ : hs.W ≃* Multiplicative (Fin 2 → F) :=
    { toFun := fun w => Multiplicative.ofAdd (φ (Additive.ofMul w))
      invFun := fun x => Additive.toMul (φ.symm (Multiplicative.toAdd x))
      left_inv := by
        intro w
        simp
      right_inv := by
        intro x
        simp
      map_mul' := by
        intro a b
        show Multiplicative.ofAdd (φ (Additive.ofMul (a * b))) =
          Multiplicative.ofAdd (φ (Additive.ofMul a)) *
            Multiplicative.ofAdd (φ (Additive.ofMul b))
        rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
          map_add]
        rfl }
  let β : ↥E →* Multiplicative (Fin 2 → F) := eφ.toMonoidHom.comp hs.proj
  refine ⟨β, ?_, ?_, ?_⟩
  · exact eφ.surjective.comp hs.proj_surjective
  · ext x
    show β x = 1 ↔ x ∈ Z.subgroupOf E
    rw [show β x = eφ (hs.proj x) from rfl, MulEquiv.map_eq_one_iff]
    exact hs.proj_eq_one_iff x
  · intro ℓ u v hv
    have hveq : v = hs.conjN ℓ u := Subtype.ext (by rw [hv]; rfl)
    have hρh : ρ (α ℓ) (Additive.ofMul (hs.proj u)) =
        Additive.ofMul (hs.conjHom ℓ (hs.proj u)) := by
      rw [hρ_apply, hσ]
    calc Multiplicative.toAdd (β v) = φ (Additive.ofMul (hs.proj v)) := rfl
      _ = φ (Additive.ofMul (hs.proj (hs.conjN ℓ u))) := by rw [hveq]
      _ = φ (Additive.ofMul (hs.conjHom ℓ (hs.proj u))) := by
        rw [IsSec.conjHom_mk]
      _ = φ (ρ (α ℓ) (Additive.ofMul (hs.proj u))) := by rw [hρh]
      _ = (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec
            (φ (Additive.ofMul (hs.proj u))) := hφ (α ℓ) _
      _ = (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec
            (Multiplicative.toAdd (β u)) := rfl

private lemma sq_sub_one_eq_zero_of_trivial_on_relCent (hs : IsSec L Z E)
    [Module (ZMod 2) (Additive hs.W)]
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    {σ : SL(2, F) →* MulAut hs.W}
    {ρ : Representation (ZMod 2) SL(2, F) (Additive hs.W)}
    (hρ : ∀ (g : SL(2, F)) (w : hs.W), ρ g (Additive.ofMul w) = Additive.ofMul (σ g w))
    (hσ : ∀ l : ↥L, σ (α l) = hs.conjHom l)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (htriv : ∀ l ∈ L, ∀ e ∈ E, ⁅l, e⁆ ∈ relCent E Z L)
    (g : SL(2, F)) : (ρ g - 1) ^ 2 = 0 := by
  obtain ⟨l, rfl⟩ := hα g
  apply LinearMap.ext
  intro w
  obtain ⟨x, hx⟩ := hs.proj_surjective (Additive.toMul w)
  have hw : w = Additive.ofMul (hs.proj x) := by
    rw [show w = Additive.ofMul (Additive.toMul w) from (ofMul_toMul w).symm, hx]
  rw [hw]
  have hstep : ρ (α l) (Additive.ofMul (hs.proj x)) - Additive.ofMul (hs.proj x) =
      Additive.ofMul (hs.proj (hs.conjN l x * x⁻¹)) := by
    rw [hρ (α l) (hs.proj x), hσ l, IsSec.conjHom_mk]
    rw [← ofMul_div, div_eq_mul_inv, ← map_inv, ← map_mul]
  have hyY : ((hs.conjN l x * x⁻¹ : ↥E) : G) ∈ relCent E Z L := by
    simpa [IsSec.conjN, commutatorElement_def] using htriv (l : G) l.2 (x : G) x.2
  have hyComm : ⁅((hs.conjN l x * x⁻¹ : ↥E) : G), (l : G)⁆ ∈ Z :=
    (mem_relCent hEZ).mp hyY |>.2 (l : G) l.2
  have hly : ⁅(l : G), ((hs.conjN l x * x⁻¹ : ↥E) : G)⁆ ∈ Z := by
    have e : ⁅(l : G), ((hs.conjN l x * x⁻¹ : ↥E) : G)⁆ =
        ⁅((hs.conjN l x * x⁻¹ : ↥E) : G), (l : G)⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z.inv_mem hyComm
  have hconjY : ((hs.conjN l (hs.conjN l x * x⁻¹) * (hs.conjN l x * x⁻¹)⁻¹ : ↥E) : G) ∈ Z := by
    simpa [IsSec.conjN, commutatorElement_def, mul_assoc] using hly
  have hprojY : hs.proj (hs.conjN l (hs.conjN l x * x⁻¹)) =
      hs.proj (hs.conjN l x * x⁻¹) := by
    have h1 : hs.proj (hs.conjN l (hs.conjN l x * x⁻¹)) *
        (hs.proj (hs.conjN l x * x⁻¹))⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact (hs.proj_eq_one_iff _).mpr hconjY
    exact mul_inv_eq_one.mp h1
  have hfixY : ρ (α l) (Additive.ofMul (hs.proj (hs.conjN l x * x⁻¹))) =
      Additive.ofMul (hs.proj (hs.conjN l x * x⁻¹)) := by
    rw [hρ (α l) (hs.proj (hs.conjN l x * x⁻¹)), hσ l, IsSec.conjHom_mk, hprojY]
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  rw [hstep, hfixY]
  simp

private lemma false_of_trivial_on_relCent (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (hs : IsSec L Z E) {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (htriv : ∀ l ∈ L, ∀ e ∈ E, ⁅l, e⁆ ∈ relCent E Z L)
    (hnt : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ Z) : False := by
  classical
  have hker_le : α.ker ≤ hs.conjHom.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    have hlL : (l : G) ∈ pCoreOf 2 L := by
      rw [hker] at hl
      exact Subgroup.mem_subgroupOf.mp hl
    exact hs.conjHom_eq_one fun x hx => by
      simpa [commutatorElement_def] using hcore (l : G) hlL x hx
  let σ : SL(2, F) →* MulAut hs.W := α.liftOfSurjective hα ⟨hs.conjHom, hker_le⟩
  have hσ : ∀ l : ↥L, σ (α l) = hs.conjHom l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨hs.conjHom, hker_le⟩ l
  have hsq : ∀ w : hs.W, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [← map_pow, hs.proj_eq_one_iff]
    simpa using hs.sq x x.2
  letI : Module (ZMod 2) (Additive hs.W) := zmod2ModuleOfExp hsq
  let ρ : Representation (ZMod 2) SL(2, F) (Additive hs.W) := linAutHom.comp σ
  have hρ_apply : ∀ (g : SL(2, F)) (w : hs.W),
      ρ g (Additive.ofMul w) = Additive.ofMul (σ g w) := fun g w => autLin_apply (σ g) w
  haveI : Finite hs.W := Finite.of_surjective hs.proj hs.proj_surjective
  haveI : Finite (Additive hs.W) := inferInstance
  have hquad : ∀ g : SL(2, F), (ρ g - 1) ^ 2 = 0 := fun g =>
    sq_sub_one_eq_zero_of_trivial_on_relCent hs hα hρ_apply hσ hEZ htriv g
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hodd : ∀ g : SL(2, F), Odd (orderOf g) → ρ g = 1 := fun g hg =>
    eq_one_of_sq_sub_one_eq_zero_of_odd_order ρ hg (hquad g)
  have htrivSL : ∀ g : SL(2, F), ρ g = 1 := by
    intro g
    have hmem : ρ.asGroupHom g ∈
        (⊥ : Subgroup ((Additive hs.W →ₗ[ZMod 2] Additive hs.W)ˣ)) :=
      CFSG.GroupTheory.map_le_of_isPerfect_of_forall_odd_order
        (f := ρ.asGroupHom) (K := ⊥) (fun x hx => by
          rw [Subgroup.mem_bot]
          exact Units.ext (by
            rw [Representation.asGroupHom_apply, hodd x hx, Units.val_one])) g
    have h1 : ρ.asGroupHom g = 1 := by simpa using hmem
    have h2 : ρ g = 1 := by
      have := congrArg Units.val h1
      simpa [Representation.asGroupHom_apply] using this
    exact h2
  obtain ⟨l0, hl0, e0, he0, hne⟩ := hnt
  have h1 : ρ (α ⟨l0, hl0⟩) (Additive.ofMul (hs.proj ⟨e0, he0⟩)) =
      Additive.ofMul (hs.proj ⟨e0, he0⟩) := by rw [htrivSL]; rfl
  have h2 : hs.conjHom ⟨l0, hl0⟩ (hs.proj ⟨e0, he0⟩) = hs.proj ⟨e0, he0⟩ := by
    have := h1
    rw [hρ_apply, hσ] at this
    exact Additive.ofMul.injective this
  have h3 : ((hs.conjN ⟨l0, hl0⟩ ⟨e0, he0⟩ * ⟨e0, he0⟩⁻¹ : ↥E) : G) ∈ Z := by
    have hproj : hs.proj (hs.conjN ⟨l0, hl0⟩ ⟨e0, he0⟩) = hs.proj ⟨e0, he0⟩ := by
      rw [← IsSec.conjHom_mk]
      exact h2
    have h1 : hs.proj (hs.conjN ⟨l0, hl0⟩ ⟨e0, he0⟩ * ⟨e0, he0⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hproj, mul_inv_cancel]
    exact (hs.proj_eq_one_iff _).mp h1
  exact hne (by simpa [IsSec.conjN, commutatorElement_def, mul_assoc] using h3)

private lemma two_pow_le_relIndex_relCent (hn : 1 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥L)) (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hnt : ∃ l ∈ L, ∃ v ∈ E, ⁅l, v⁆ ∉ relCent E Z L) :
    2 ^ (2 * n) ≤ (relCent E Z L).relIndex E := by
  classical
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_isElemSec hsec
  have hLZ : L ≤ Subgroup.normalizer (Z : Set G) := hL.trans inf_le_right
  have hZY : Z ≤ relCent E Z L := le_relCent_of_le_normalizer hsec.1 hEZ hLZ
  have hYE : relCent E Z L ≤ E := relCent_le E Z L
  have hsecY : IsElemSec (relCent E Z L) E := isElemSec_of_le_of_le hZY hYE hsec
  have hLY : L ≤ Subgroup.normalizer ((relCent E Z L) : Set G) :=
    normalizer_relCent_of_le (hL.trans inf_le_left) hLZ Subgroup.le_normalizer
  let H : Subgroup G := E ⊔ L
  have hEH : E ≤ H := le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hHfin : Finite ↥H := by
    refine Finite.of_surjective
      (fun p : ↥E × ↥L =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥H)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨e, he, l, hl, hxl⟩ :=
      CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer (hL.trans inf_le_left) hx
    exact ⟨⟨⟨e, he⟩, ⟨l, hl⟩⟩, Subtype.ext hxl.symm⟩
  haveI : Finite ↥H := hHfin
  let V' : Subgroup ↥H := E.subgroupOf H
  let Z' : Subgroup ↥H := (relCent E Z L).subgroupOf H
  have hsec' : IsElemSec Z' V' := by
    refine ⟨Subgroup.subgroupOf_mono H hYE, ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      have h1 := (Subgroup.commutator_le.mp hsecY.2.1) (x : G)
        (Subgroup.mem_subgroupOf.mp hx) (y : G) (Subgroup.mem_subgroupOf.mp hy)
      have hcoe : ((⁅x, y⁆ : ↥H) : G) = ⁅(x : G), (y : G)⁆ :=
        map_commutatorElement (f := H.subtype) (g₁ := x) (g₂ := y)
      exact Subgroup.mem_subgroupOf.mpr (by rw [hcoe]; exact h1)
    · intro x hx
      have h1 := hsecY.2.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
      exact Subgroup.mem_subgroupOf.mpr (by simpa [map_pow] using h1)
  have hHE : H ≤ Subgroup.normalizer (E : Set G) :=
    sup_le Subgroup.le_normalizer (hL.trans inf_le_left)
  have hL'V : L.subgroupOf H ≤ Subgroup.normalizer (V' : Set ↥H) :=
    (le_top : L.subgroupOf H ≤ ⊤).trans
      (le_normalizer_subgroupOf_of_le_normalizer hEH hHE)
  have hL'Z : L.subgroupOf H ≤ Subgroup.normalizer (Z' : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp
          (hLY (Subgroup.mem_subgroupOf.mp hx)) (y : G)).mp
          (Subgroup.mem_subgroupOf.mp hy))
    · intro hy
      have hx' : x⁻¹ ∈ L.subgroupOf H := Subgroup.inv_mem _ hx
      have hmem : ((x : G) * (y : G) * (x : G)⁻¹) ∈ relCent E Z L :=
        Subgroup.mem_subgroupOf.mp hy
      have hback := (Subgroup.mem_normalizer_iff.mp
        (hLY (Subgroup.mem_subgroupOf.mp hx'))
        ((x : G) * (y : G) * (x : G)⁻¹)).mp hmem
      exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using hback)
  have hL' : L.subgroupOf H ≤
      Subgroup.normalizer (V' : Set ↥H) ⊓ Subgroup.normalizer (Z' : Set ↥H) :=
    le_inf hL'V hL'Z
  have hQ' : ∀ p ∈ pCoreOf 2 (L.subgroupOf H), ∀ v ∈ V', ⁅p, v⁆ ∈ Z' := by
    intro p hp v hv
    have hpL : (p : G) ∈ pCoreOf 2 L := by
      have hmem := Subgroup.mem_map_of_mem (f := H.subtype) hp
      rwa [CFSG.Quasithin.Vol2.Ch10.SecB.KRP.map_pCoreOf_subgroupOf hLH] at hmem
    have hvE : (v : G) ∈ E := Subgroup.mem_subgroupOf.mp hv
    have hcomm : ⁅(p : G), (v : G)⁆ ∈ Z := hcore (p : G) hpL (v : G) hvE
    have hcoe : ((⁅p, v⁆ : ↥H) : G) = ⁅(p : G), (v : G)⁆ :=
      map_commutatorElement (f := H.subtype) (g₁ := p) (g₂ := v)
    exact Subgroup.mem_subgroupOf.mpr (by rw [hcoe]; exact hZY hcomm)
  have hqH : IsL2Quot n (oTwoQuot ↥(L.subgroupOf H)) := by
    obtain ⟨e⟩ := hq
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr
      (Subgroup.subgroupOfEquivOfLe hLH)).trans e⟩
  have hnt' : ∃ l ∈ (L.subgroupOf H), ∃ v ∈ V', ⁅l, v⁆ ∉ Z' := by
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    refine ⟨⟨l, hLH hl⟩, Subgroup.mem_subgroupOf.mpr hl, ⟨v, hEH hv⟩,
      Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    intro hmem
    exact hne (by
      have hcoe : ((⁅(⟨l, hLH hl⟩ : ↥H), (⟨v, hEH hv⟩ : ↥H)⁆ : ↥H) : G) = ⁅l, v⁆ := rfl
      have hmem' : ((⁅(⟨l, hLH hl⟩ : ↥H), (⟨v, hEH hv⟩ : ↥H)⁆ : ↥H) : G) ∈
          relCent E Z L := Subgroup.mem_subgroupOf.mp hmem
      rwa [hcoe] at hmem')
  have hle' := two_pow_le_relIndex_of_nontrivial (G := ↥H) (m := n) hn hqH hsec'
    hL' hQ' hnt'
  rw [← Subgroup.relIndex_subgroupOf (H := relCent E Z L) (K := E) (L := H) hEH]
  exact hle'

theorem isNatSecOf_of_two_pow_le_of_nontrivial (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hcard : Z.relIndex E = 2 ^ (2 * n))
    (hnt : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ Z)
    (hq : IsL2Quot n (oTwoQuot ↥L))
    (hT : IsSylowTwoOf T L) (hC : 2 ^ n ≤ Z.relIndex (relCent E Z T)) :
    CFSG.Quasithin.F112R.St84.IsNatSecOf L E Z α := by
  classical
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_isElemSec hsec
  have hLZ : L ≤ Subgroup.normalizer (Z : Set G) := hL.trans inf_le_right
  let Y : Subgroup G := relCent E Z L
  have hZY : Z ≤ Y := le_relCent_of_le_normalizer hsec.1 hEZ hLZ
  have hYE : Y ≤ E := relCent_le E Z L
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_relCent_of_le (hL.trans inf_le_left) hLZ Subgroup.le_normalizer
  have hsecY : IsElemSec Y E := isElemSec_of_le_of_le hZY hYE hsec
  let hs : IsSec L Z E :=
    { le := hsec.1
      normN := hL.trans inf_le_left
      normL := hL.trans inf_le_right
      comm := fun x hx y hy => by
        simpa [commutatorElement_def] using
          (Subgroup.commutator_le.mp hsec.2.1) x hx y hy
      sq := fun x hx => hsec.2.2 x hx }
  have hntY : ∃ l ∈ L, ∃ v ∈ E, ⁅l, v⁆ ∉ Y := by
    by_contra h
    push Not at h
    exact false_of_trivial_on_relCent hn hF hs hα hker hEZ hcore
      (fun l hl e he => h l hl e he) hnt
  have hYle : 2 ^ (2 * n) ≤ Y.relIndex E :=
    two_pow_le_relIndex_relCent (by omega) hq hsec hL hcore hntY
  haveI : Finite ↥Y :=
    Finite.of_injective (Subgroup.inclusion hYE) (Subgroup.inclusion_injective hYE)
  have hYpos : 0 < Y.relIndex E := by
    haveI : Finite (↥E ⧸ Y.subgroupOf E) := inferInstance
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (G := ↥E) (H := Y.subgroupOf E))
  have hZpos : 0 < Z.relIndex Y := by
    haveI : Finite (↥Y ⧸ Z.subgroupOf Y) := inferInstance
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (G := ↥Y) (H := Z.subgroupOf Y))
  have hrel : Z.relIndex Y * Y.relIndex E = Z.relIndex E :=
    Subgroup.relIndex_mul_relIndex (H := Z) (K := Y) (L := E) hZY hYE
  have hEqIndex : Y.relIndex E = Z.relIndex E := by
    refine le_antisymm ?_ ?_
    · rw [← hrel]
      exact Nat.le_mul_of_pos_left _ hZpos
    · rw [hcard]
      exact hYle
  have hZrel : Z.relIndex Y = 1 := by
    have h1 : Z.relIndex Y * Y.relIndex E = Y.relIndex E := by
      rw [hrel, ← hEqIndex]
    have h2 : Z.relIndex Y * Y.relIndex E = 1 * Y.relIndex E := by
      rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hYpos h2
  have hYZ : Y = Z := le_antisymm (Subgroup.relIndex_eq_one.mp hZrel) hZY
  have hcent : relCent E Z L = Z := hYZ
  exact isNatSecOf_of_two_pow_le hn hF hα hker hsec hL hcore hcard hcent hT hC

theorem exists_isNatSecOf_of_two_pow_le (hn : 2 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥L))
    (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hcard : Z.relIndex E = 2 ^ (2 * n))
    (hnt : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ Z)
    (hT : IsSylowTwoOf T L) (hC : 2 ^ n ≤ Z.relIndex (relCent E Z T)) :
    ∃ α : ↥L →* SL(2, GaloisField 2 n), Function.Surjective α ∧
      α.ker = (pCoreOf 2 L).subgroupOf L ∧
      CFSG.Quasithin.F112R.St84.IsNatSecOf L E Z α := by
  classical
  obtain ⟨α, hα, hker, -⟩ :=
    CFSG.GroupTheory.exists_SL2_hom_map_sylowTwo_eq_upperUnipotent hq hT
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  exact ⟨α, hα, hker,
    isNatSecOf_of_two_pow_le_of_nontrivial hn hF hα hker hsec hL hcore hcard hnt hq hT hC⟩

end CFSG.Quasithin.St84
