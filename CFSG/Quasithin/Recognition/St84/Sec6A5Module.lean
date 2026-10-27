module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LMod
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyAlt

public section

namespace CFSG.Quasithin.St84

open CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.H13.NFa2
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped commutatorElement LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

theorem card_eq_sixteen_of_irreducible {V Z L : Subgroup G}
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) (hVZ : Z ≤ V) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) : Z.relIndex V = 16 := by
  classical
  have hZV : Z < V := by
    refine lt_of_le_of_ne hVZ ?_
    intro heq
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    apply hne
    rw [heq]
    have hconj : l * v * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hL hl)).1 v).mp hv
    exact V.mul_mem hconj (V.inv_mem hv)
  obtain ⟨l₀, hl₀, v₀, hv₀, hne₀⟩ := hnt
  let l₀' : ↥L := ⟨l₀, hl₀⟩
  let v₀' : ↥V := ⟨v₀, hv₀⟩
  have hnormalZV : V ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hVZ).trans hsec.2.1)
  have hsecHyp : SecHyp L Z V :=
    { le := hVZ
      norm₀ := hL.trans inf_le_right
      norm₁ := hL.trans inf_le_left
      normal := hnormalZV
      comm := fun a ha b hb => hsec.2.1 (Subgroup.commutator_mem_commutator ha hb)
      sq := fun a ha => by simpa [pow_two] using hsec.2.2 a ha }
  have hChief : IsChiefPair L Z V :=
    { lt := hZV
      norm₀ := hL.trans inf_le_right
      norm₁ := hL.trans inf_le_left
      normal := hnormalZV
      min := fun N hZN hNV hLN => hirr N hZN hNV hLN }
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hsecHyp
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hfix : s.ρ l₀' (s.cl v₀') ≠ s.cl v₀' := by
    intro h
    exact hne₀ ((SecRep.fix_iff hsecHyp s l₀' v₀').mp h)
  have hPgrp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hPle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hPn : ∀ x ∈ L, ∀ p ∈ CFSG.Open.pCoreOf 2 L,
      x * p * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx p hp
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hx) p).mp hp
  have hkerP : CFSG.pCore 2 ↥L ≤ s.ρ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker]
    exact SecRep.ρ_eq_one_of_normal_pgroup hChief hsecHyp s hPle hPgrp hPn p
      ((CFSG.mem_openPCoreOf_iff p).mpr hp)
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  obtain ⟨e⟩ := hquot
  let eSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 2)
  let bar : oTwoQuot ↥L →* (W ≃ₗ[ZMod 2] W) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) s.ρ hkerP
  let Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) →* (W ≃ₗ[ZMod 2] W) :=
    bar.comp (e.symm.toMonoidHom.comp eSL.symm.toMonoidHom)
  let ρSL : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) W :=
    { toFun := fun g => (Φ g).toLinearMap
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by rw [map_mul]; rfl }
  have hΦ_mk : ∀ l : ↥L, Φ (eSL (e (q l))) = s.ρ l := by
    intro l
    simp [Φ, bar, q, QuotientGroup.lift_mk']
  have hρSL_mk : ∀ l : ↥L, ρSL (eSL (e (q l))) = (s.ρ l).toLinearMap := by
    intro l
    rw [show ρSL (eSL (e (q l))) = (Φ (eSL (e (q l)))).toLinearMap from rfl, hΦ_mk l]
  haveI : Nontrivial W := ⟨s.ρ l₀' (s.cl v₀'), s.cl v₀', hfix⟩
  have hirrSL : ρSL.IsIrreducible := by
    haveI : Nontrivial (Subrepresentation ρSL) := by
      refine ⟨⊥, ⊤, ?_⟩
      intro h
      exact bot_ne_top (α := Submodule (ZMod 2) W)
        (congrArg Subrepresentation.toSubmodule h)
    refine { eq_bot_or_eq_top := fun U => ?_ }
    have hS : ∀ l : ↥L, ∀ w ∈ U.toSubmodule, s.ρ l w ∈ U.toSubmodule := by
      intro l w hw
      have h1 := U.apply_mem_toSubmodule (eSL (e (q l))) hw
      rwa [hρSL_mk l] at h1
    rcases SecRep.irreducible hChief hsecHyp s U.toSubmodule hS with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  have hneρ : ρSL (eSL (e (q l₀'))) ≠ 1 := by
    intro h
    have hbar : s.ρ l₀' = 1 := by
      refine LinearEquiv.ext fun w => ?_
      have h1 : (s.ρ l₀').toLinearMap w = w := by
        rw [← hρSL_mk l₀']
        exact LinearMap.congr_fun h w
      simpa using h1
    apply hfix
    rw [hbar]
    rfl
  let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  let _ : Fintype (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) := Fintype.ofFinite _
  have hk : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨hcases, -, -, -, hcard⟩ :=
    irreducible_binary_SL2_four_module_production hk ρSL hirrSL
  obtain ⟨-, h16a, h16b⟩ := hcard
  have hW16 : Nat.card W = 16 := by
    rcases hcases with ⟨φ, hφ⟩ | ⟨φ, hφ⟩ | ⟨φ, hφ⟩
    · exfalso
      have htriv : ρSL (eSL (e (q l₀'))) = 1 := by
        refine LinearMap.ext fun w => ?_
        exact φ.injective (by simpa using hφ (eSL (e (q l₀'))) w)
      exact hneρ htriv
    · exact (Nat.card_congr φ.toEquiv).trans h16a
    · exact (Nat.card_congr φ.toEquiv).trans h16b
  have hker : s.cls.ker = Z.subgroupOf V := by
    ext n
    rw [MonoidHom.mem_ker, s.ker n, Subgroup.mem_subgroupOf]
  haveI hNZV : (Z.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVZ).mpr hnormalZV
  have hquotW : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card W := by
    have eW : (↥V ⧸ Z.subgroupOf V) ≃* Multiplicative W :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective s.cls s.surj)
    exact (Nat.card_congr eW.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  show (Z.subgroupOf V).index = 16
  rw [Subgroup.index_eq_card, hquotW, hW16]

end CFSG.Quasithin.St84
