module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ReeSylowGenerationHolds

import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.Quasithin.Vol2.Ch11SecE3Sz

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.LiteratureLocal
  (ward_kleidman_small_Ree_involution_centralizer_maximal)

theorem exists_injective_commutator_subgroupOf_centralizer {Q : Type} [Group Q] (L : Subgroup Q)
    (z : L) : ∃ φ : ↥(commutator ↥(L.subgroupOf (centralizer {(z : Q)}))) →*
      ↥⁅centralizer ({z} : Set ↥L), centralizer ({z} : Set ↥L)⁆, Function.Injective φ := by
  set C := centralizer {(z : Q)}
  let ψ : ↥(L.subgroupOf C) →* ↥L :=
    { toFun := fun a => ⟨((a : ↥C) : Q), a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b hab => by
    have h := congrArg (fun w : ↥L => (w : Q)) hab
    exact Subtype.ext (Subtype.ext h)
  have hle : (⊤ : Subgroup ↥(L.subgroupOf C)).map ψ ≤ centralizer ({z} : Set ↥L) := by
    rintro _ ⟨a, -, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have ha : ((a : ↥C) : Q) * (z : Q) = (z : Q) * ((a : ↥C) : Q) :=
      mem_centralizer_singleton_iff.1 (a : ↥C).2
    exact ha
  have hmap : (commutator ↥(L.subgroupOf C)).map ψ ≤
      ⁅centralizer ({z} : Set ↥L), centralizer ({z} : Set ↥L)⁆ := by
    rw [_root_.commutator_def, map_commutator]
    exact commutator_mono hle hle
  refine ⟨(ψ.comp (commutator ↥(L.subgroupOf C)).subtype).codRestrict _
    (fun c => hmap ⟨c, c.2, rfl⟩), fun c d hcd => ?_⟩
  exact Subtype.ext (hψ (congrArg Subtype.val hcd))


theorem exists_reeTitsModel_of_lieModel_twistedG2 {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Models.LieModel X .twistedG2 0 3 f) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * a + 1) := by
  obtain ⟨hadm, ⟨-, hF⟩ | ⟨-, ⟨d, hv⟩, hN, ⟨e⟩⟩⟩ := h
  · exact hF.elim
  · cases d <;> simp only [CFSG.Models.NamesTag] at hN
    case reeG2 a =>
      obtain ⟨-, rfl⟩ := hN
      obtain ⟨-, -, -, -, -, h3⟩ := hadm
      exact ⟨a, by omega, rfl, CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 a ⟨hv, ⟨e⟩⟩⟩

theorem not_hasCompFactor_isCalL0_of_commutator {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    [L.Normal] (hq : Group.IsSolvable (Q ⧸ L)) (X : Subgroup Q)
    (hX : CFSG.GH74.SectionalTwoRankLE ↥(commutator ↥(L.subgroupOf X)) 2) :
    ¬ HasCompFactor X IsCalL0 := by
  rintro ⟨M, _, hcf, hM⟩
  have : Finite M := isCompositionFactor_finite hcf
  have : (L.subgroupOf X).Normal := Subgroup.normal_subgroupOf
  have h1 := isCompositionFactor_subgroupOf_of_isSolvable_quot
    (isSolvable_quotient_subgroupOf hq X)
    ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr Subgroup.topEquiv).2 hcf)
    (isCalL0_nonabelian_not_sectionalTwoRankLE M hM).1
  have h2 : E1.IsCompositionFactor ↥(⊤ : Subgroup ↥(L.subgroupOf X)) M :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      ((Subgroup.subgroupOfEquivOfLe le_top).trans Subgroup.topEquiv.symm)).1 h1
  have hab : Group.IsSolvable (↥(L.subgroupOf X) ⧸ commutator ↥(L.subgroupOf X)) :=
    isSolvable_of_comm fun a b => by
      let a' : Abelianization ↥(L.subgroupOf X) := a
      let b' : Abelianization ↥(L.subgroupOf X) := b
      exact mul_comm a' b'
  exact not_hasCompFactor_of_sectionalTwoRankLE isCalL0_nonabelian_not_sectionalTwoRankLE hab hX ⊤
    ⟨M, inferInstance, h2, hM⟩


theorem lGen_eq_top_of_ree {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} [hLn : L.Normal]
    (hC : centralizer (L : Set Q) = ⊥)
    (hP : ∃ f : ℕ, CFSG.Models.LieModel ↥L .twistedG2 0 3 f) (hT : IsSylowIn 2 T ⊤) :
    lGen IsCalL0 ⊤ T = ⊤ := by
  obtain ⟨f, hf⟩ := hP
  obtain ⟨a, ha, -, hR⟩ := exists_reeTitsModel_of_lieModel_twistedG2 hf
  obtain ⟨-, ⟨-, hconj⟩, hcent, hmax, hcyc, -, hodd⟩ :=
    ward_kleidman_small_Ree_involution_centralizer_maximal a ha ↥L hR
  have hOut : Group.IsSolvable (Outer ↥L) := by
    have := hcyc
    exact isSolvable_of_comm fun u v => (IsCyclic.isMulCommutative (α := Outer ↥L)).is_comm.comm u v
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer hOut)
  have hTL : T ≤ L := by
    intro t ht
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨t, ht⟩
    exact CFSG.Quasithin.Vol2.Ch11.SecE3.mem_of_pow_two_pow_eq_one hC hodd (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hTsyl : IsSylowIn 2 T L := isSylowIn_of_le_of_le hT hTL le_top
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBL : CFSG.Blueprint.LieModel ↥L .twistedG2 0 3 (2 * a + 1) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
  obtain ⟨-, -, hSyl⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_ReeSylowGeneration_holds ↥L
      (3 ^ (2 * a + 1)) a ⟨a, rfl, hBL⟩ rfl ha
  obtain ⟨hEA, -, x, y, hx, hy, hxy, hx2, hy2, hKx, hKy, -⟩ := hSyl hTsyl.toSylow
  have hxT : (x : Q) ∈ T := hx
  have hyT : (y : Q) ∈ T := hy
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    have := hEA.1
    have h := (IsMulCommutative.is_comm (M := ↥(hTsyl.toSylow : Subgroup ↥L))).comm
      ⟨⟨s, hTL hs⟩, hs⟩ ⟨⟨t, hTL ht⟩, ht⟩
    exact congrArg (fun w : ↥(hTsyl.toSylow : Subgroup ↥L) => ((w : ↥L) : Q)) h
  have key : ∀ z : ↥L, orderOf z = 2 → (z : Q) ∈ T →
      CFSG.GH74.SectionalTwoRankLE ↥⁅centralizer ({z} : Set ↥L), centralizer ({z} : Set ↥L)⁆ 2 →
      centralizer {(z : Q)} ∈ calLT IsCalL0 ⊤ T := by
    intro z hz2 hzT hsec
    refine ⟨fun t ht => mem_centralizer_singleton_iff.2 (hTcomm t ht _ hzT), ?_, ?_⟩
    · refine lt_top_iff_ne_top.2 fun htop => ?_
      have hzc : (z : Q) ∈ centralizer (L : Set Q) := by
        rw [mem_centralizer_iff]
        intro l _
        have hl : l ∈ centralizer {(z : Q)} := htop ▸ mem_top l
        exact mem_centralizer_singleton_iff.1 hl
      rw [hC, mem_bot] at hzc
      have hz1 : z = 1 := Subtype.ext hzc
      rw [hz1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    · apply not_hasCompFactor_isCalL0_of_commutator hq
      obtain ⟨φ, hφ⟩ := exists_injective_commutator_subgroupOf_centralizer L z
      exact CFSG.GH74.SectionalTwoRankLE.of_injective φ hφ hsec
  have hsec : ∀ z : ↥L, CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsL2Over17
      ↥⁅centralizer ({z} : Set ↥L), centralizer ({z} : Set ↥L)⁆ (3 ^ (2 * a + 1)) →
      CFSG.GH74.SectionalTwoRankLE ↥⁅centralizer ({z} : Set ↥L), centralizer ({z} : Set ↥L)⁆ 2 := by
    rintro z ⟨r, f', -, hr2, -, -, hLM⟩
    exact CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model hr2 hLM
  have hxm := key x hx2 hxT (hsec x hKx)
  have hym := key y hy2 hyT (hsec y hKy)
  have hne : centralizer ({x} : Set ↥L) ≠ centralizer {y} := by
    intro heq
    obtain ⟨-, -, -, -, -, hzx⟩ := hcent x hx2
    obtain ⟨-, -, -, -, -, hzy⟩ := hcent y hy2
    rw [heq, hzy] at hzx
    have hyx : y ∈ zpowers x := hzx ▸ mem_zpowers y
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyx
    rw [← zpow_mod_orderOf, hx2] at hk
    have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk2 with h0 | h1
    · rw [h0, zpow_zero] at hk
      rw [← hk, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    · rw [h1, zpow_one] at hk
      exact hxy hk
  have hLsup := (hmax x hx2).sup_eq_top_of_ne (hmax y hy2) hne
  have hmapz : ∀ z : ↥L, (centralizer ({z} : Set ↥L)).map L.subtype ≤ centralizer {(z : Q)} := by
    rintro z _ ⟨l, hl, rfl⟩
    have hl' : l * z = z * l := mem_centralizer_singleton_iff.1 hl
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hl'
  have hLle : L ≤ centralizer {(x : Q)} ⊔ centralizer {(y : Q)} := by
    intro l hl
    have h1 : (⟨l, hl⟩ : ↥L) ∈ centralizer ({x} : Set ↥L) ⊔ centralizer {y} := hLsup ▸ mem_top _
    have h2 := mem_map_of_mem L.subtype h1
    rw [Subgroup.map_sup] at h2
    exact sup_le_sup (hmapz x) (hmapz y) h2
  have hFr : L ⊔ centralizer {(x : Q)} = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    have hzL : g * (x : Q) * g⁻¹ ∈ L := hLn.conj_mem _ x.2 g
    have hz2 : orderOf (⟨g * (x : Q) * g⁻¹, hzL⟩ : ↥L) = 2 := by
      rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx2]
    obtain ⟨c, hc⟩ := isConj_iff.1 (hconj x _ hx2 hz2)
    have hc' : (c : Q) * x * (c : Q)⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hc
    have hmem : (c : Q)⁻¹ * g ∈ centralizer {(x : Q)} := by
      rw [mem_centralizer_singleton_iff]
      calc (c : Q)⁻¹ * g * x = (c : Q)⁻¹ * (g * x * g⁻¹) * g := by group
        _ = (c : Q)⁻¹ * ((c : Q) * x * (c : Q)⁻¹) * g := by rw [hc']
        _ = x * ((c : Q)⁻¹ * g) := by group
    have hg : g = (c : Q) * ((c : Q)⁻¹ * g) := by group
    rw [hg]
    exact mul_mem_sup c.2 hmem
  refine eq_top_iff.2 ?_
  calc (⊤ : Subgroup Q) = L ⊔ centralizer {(x : Q)} := hFr.symm
    _ ≤ (centralizer {(x : Q)} ⊔ centralizer {(y : Q)}) ⊔ centralizer {(x : Q)} :=
      sup_le_sup_right hLle _
    _ ≤ lGen IsCalL0 ⊤ T :=
      sup_le (sup_le (le_iSup₂_of_le _ hxm le_rfl) (le_iSup₂_of_le _ hym le_rfl))
        (le_iSup₂_of_le _ hxm le_rfl)

theorem asch54Case_ree :
    Asch54Case fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .twistedG2 0 3 f := by
  intro Q _ _ L T _ hLn _ _ hC hP _ hT _
  exact Or.inl (lGen_eq_top_of_ree hC hP hT)

end CFSG.LocalAnalysis.WeakClosure81
