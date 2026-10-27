module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem le_fsuL0 (T L : Subgroup G) : L ≤ fsuL0 T L :=
  le_conjClosure L T

theorem fsuL0_le_fsuM (T L : Subgroup G) : fsuL0 T L ≤ fsuM T L :=
  Subgroup.le_normalizer

theorem le_fsuM (T L : Subgroup G) : T ≤ fsuM T L :=
  le_normalizer_conjClosure L T

theorem fsuL0_le_sup (T L : Subgroup G) : fsuL0 T L ≤ L ⊔ T :=
  conjClosure_le fun _ ht _ hl =>
    (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hl))
      ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))

theorem sup_le_fsuM (T L : Subgroup G) : L ⊔ T ≤ fsuM T L :=
  sup_le ((le_fsuL0 T L).trans (fsuL0_le_fsuM T L)) (le_fsuM T L)

theorem fsuL0_sup_eq (T L : Subgroup G) : fsuL0 T L ⊔ T = L ⊔ T :=
  le_antisymm (sup_le (fsuL0_le_sup T L) le_sup_right) (sup_le_sup_right (le_fsuL0 T L) T)

theorem fsuL0_normal (T L : Subgroup G) : ((fsuL0 T L).subgroupOf (fsuM T L)).Normal :=
  Subgroup.normal_in_normalizer

theorem subnormal_fsuL0 (T L : Subgroup G) : CFSG.Open.IsSubnormal (fsuL0 T L) (fsuM T L) :=
  CFSG.Open.IsSubnormal.step (fsuL0_le_fsuM T L) (fsuL0_normal T L) (CFSG.Open.IsSubnormal.refl _)

theorem conjClosure_fsuM (T L : Subgroup G) : conjClosure L (fsuM T L) = fsuL0 T L :=
  le_antisymm
    (conjClosure_le fun _ hm _ hl => (Subgroup.mem_normalizer_iff.mp hm _).mp (le_fsuL0 T L hl))
    (conjClosure_mono le_rfl (le_fsuM T L))

theorem le_normalizer_of_normal_fsuM {T L : Subgroup G}
    (hn : (L.subgroupOf (fsuM T L)).Normal) : T ≤ Subgroup.normalizer (L : Set G) :=
  (le_fsuM T L).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
    ((le_fsuL0 T L).trans (fsuL0_le_fsuM T L))).mp hn)

theorem pCoreOf_ne_bot_of_faithful {T L : Subgroup G} (h : quasithinIsFaithfulLocal T L) :
    pCoreOf 2 L ≠ ⊥ := by
  intro h2
  apply h.2.2.2
  rw [quasithinV2, h2]
  have hb : Subgroup.closure {z : G | z ∈ (⊥ : Subgroup G) ⊓
      Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ∧ z ^ 2 = 1} = ⊥ :=
    le_bot_iff.mp ((Subgroup.closure_le _).mpr fun _ hz => hz.1.1)
  rw [hb, Subgroup.commutator_bot_left]

variable [Finite G]

theorem mem_cComp_fsuL0 {T L : Subgroup G} (h : quasithinIsLocal T L) :
    L ∈ cComp (fsuL0 T L) :=
  cComp_mem_of_le (mem_cComp_iff.mpr h.2.1) (le_fsuL0 T L) (fsuL0_le_sup T L)

theorem mem_cComp_fsuM {T L : Subgroup G} (h : quasithinIsLocal T L) :
    L ∈ cComp (fsuM T L) :=
  cComp_mem_of_subnormal (subnormal_fsuL0 T L) (mem_cComp_fsuL0 h)

theorem pCoreOf_fsuM_ne_bot {T L : Subgroup G} (h : quasithinIsFaithfulLocal T L) :
    pCoreOf 2 (fsuM T L) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hM
  apply pCoreOf_ne_bot_of_faithful h
  have hle := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp (mem_cComp_fsuM h.1))
  rw [hM] at hle
  exact le_bot_iff.mp hle

theorem a38ForSQTKCat_proved
    : Vol2Native.A38ForSQTKCat :=
  Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
    Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved

theorem ncard_and_a38Types (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hq : quasithinIsQTKECat G) {T L : Subgroup G} (hf : quasithinIsFaithfulLocal T L)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    Set.ncard (conjSubgroupsBy (fsuM T L) L) = 2 ∧ A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have := hs
  have hK : LocalSQTK G := (qtkeCore_of_cat hn hq).1
  rcases Vol2Native.lemma_1_2_1_three hK h37 h38 (pCoreOf_fsuM_ne_bot hf) (mem_cComp_fsuM hf.1)
    with hnorm | h
  · exact absurd (le_normalizer_of_normal_fsuM hnorm) hnot
  · exact h

theorem ncard_conjSubgroupsBy_fsuM (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hq : quasithinIsQTKECat G) {T L : Subgroup G} (hf : quasithinIsFaithfulLocal T L)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    Set.ncard (conjSubgroupsBy (fsuM T L) L) = 2 :=
  (ncard_and_a38Types h37 h38 hs hn hq hf hnot).1

theorem a38Types_of_not_normal (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hq : quasithinIsQTKECat G) {T L : Subgroup G} (hf : quasithinIsFaithfulLocal T L)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) : A38Types (↥L ⧸ CFSG.pCore 2 ↥L) :=
  (ncard_and_a38Types h37 h38 hs hn hq hf hnot).2

theorem isSimpleGroup_of_not_normal (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hq : quasithinIsQTKECat G) {T L : Subgroup G} (hf : quasithinIsFaithfulLocal T L)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
  Vol2Native.L122A.isSimpleGroup_of_a38Types (a38Types_of_not_normal h37 h38 hs hn hq hf hnot)

end CFSG.Quasithin.Vol2.Ch10.SecA
