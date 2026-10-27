module

public import CFSG.Quasithin.Background.GoldschmidtS146PAut
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Quasithin.Background.GoldschmidtS146PWreath

public section

namespace CFSG.Quasithin.GoldS146P

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem finite_mulAut_of_finite (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

theorem sl_simple (n : ℕ) (hn : 3 ≤ n) : IsSimpleGroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hn

theorem sl_nonabelian (n : ℕ) (hn : 3 ≤ n) :
    ∃ a b : SpecialLinearGroup (Fin n) (ZMod 2), a * b ≠ b * a :=
  CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two (Nat.card_zmod 2) hn

theorem outer_sl_solvable (n : ℕ) (hn : 3 ≤ n) :
    Group.IsSolvable (Outer (SpecialLinearGroup (Fin n) (ZMod 2))) := by
  have hk : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hp := (CFSG.LieType.SteinbergBR.BinaryLinear.binary_linear_key (k := ZMod 2) (n := n)
    hn hk).2
  have : Finite (MulAut (projectiveSL n (ZMod 2))) := finite_mulAut_of_finite _
  have : Group.IsNilpotent (Outer (projectiveSL n (ZMod 2))) := hp.isNilpotent
  have : Group.IsSolvable (Outer (projectiveSL n (ZMod 2))) := inferInstance
  exact solvable_of_equiv (CFSG.QuasithinUnique.Vol2Native.A312L.slEquivProj hk n).symm

theorem perfInLayer_aut_sl (n : ℕ) (hn : 3 ≤ n) :
    PerfInLayer (MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) := by
  have := sl_simple n hn
  have := outer_sl_solvable n hn
  exact perfInLayer_mulAut _ (sl_nonabelian n hn)

abbrev F16 : Type := GaloisField 2 4

theorem card_F16 : Nat.card F16 = 16 := by
  rw [GaloisField.card 2 4 (by norm_num)]
  norm_num

theorem exists_four_F16 : ∃ s : Finset F16, s.card = 4 := by
  have : Fintype F16 := Fintype.ofFinite F16
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F16)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_F16]; norm_num)
  exact ⟨s, hs⟩

theorem sl2_simple : IsSimpleGroup (SpecialLinearGroup (Fin 2) F16) :=
  CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple exists_four_F16

theorem sl2_nonabelian : ∃ a b : SpecialLinearGroup (Fin 2) F16, a * b ≠ b * a :=
  CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian exists_four_F16

theorem perfInLayer_wreath_sl3 {Q : Type*} [Group Q] (hQ : Nat.card Q = 2) :
    PerfInLayer (SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Q) := by
  have := sl_simple 3 le_rfl
  have hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (sl_nonabelian 3 le_rfl)).1
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  have : Subsingleton (SpecialLinearGroup (Fin 3) (ZMod 2) ⧸
      (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)))) :=
    QuotientGroup.subsingleton_quotient_top
  have : Group.IsSolvable (SpecialLinearGroup (Fin 3) (ZMod 2) ⧸
      (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)))) := inferInstance
  exact perfInLayer_wreath ⊤ hQ hq'

theorem alt5_quasisimple : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hnc : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup (alternatingGroup (Fin 5)) :=
      { (inferInstance : Group ↥(alternatingGroup (Fin 5))) with mul_comm := fun a b => h a b }
    have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 5))
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [h60] at hp
    exact absurd hp (by norm_num)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem perm5_quot_solvable :
    Group.IsSolvable (Equiv.Perm (Fin 5) ⧸ alternatingGroup (Fin 5)) := by
  have h2 : Nat.card (Equiv.Perm (Fin 5) ⧸ alternatingGroup (Fin 5)) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact alternatingGroup.index_eq_two
  have : IsCyclic (Equiv.Perm (Fin 5) ⧸ alternatingGroup (Fin 5)) :=
    isCyclic_of_prime_card (p := 2) h2
  infer_instance

theorem perfInLayer_wreath_perm5 {Q : Type*} [Group Q] (hQ : Nat.card Q = 2) :
    PerfInLayer (Equiv.Perm (Fin 5) ≀ᵣ Q) := by
  have := perm5_quot_solvable
  exact perfInLayer_wreath (alternatingGroup (Fin 5)) hQ alt5_quasisimple

end CFSG.Quasithin.GoldS146P
