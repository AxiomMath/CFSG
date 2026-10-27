module

public import CFSG.Monster.Existence.Compat.Co1Iso

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint

theorem monsterIsExtraspecial_of_isExtraspecialPGroup {P : Type*} [Group P] [Finite P]
    (h : IsExtraspecialPGroup 2 P) : MonsterIsExtraspecial P := by
  obtain ⟨hp, hc, hf, hcard⟩ := h
  have : Fact (IsPGroup 2 P) := ⟨hp⟩
  refine ⟨hcard, hc, fun x => ?_⟩
  have h2 := pth_power_mem_frattini_of_isPGroup (p := 2) x
  rw [hf] at h2
  exact h2

variable {G : Type} [Group G]

theorem isLeechCentralizerType_of_isTwoBCentralizer
    {z : G}
    (h : Existence.IsTwoBCentralizer z) :
    MonsterIsLeechCentralizerType ↥(Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨hext, hcard, hcent, ⟨e⟩, -, -⟩ := h
  have hfin : Finite (pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine ⟨pCore 2 ↥(Subgroup.centralizer ({z} : Set G)), pCore_normal, hcard,
    monsterIsExtraspecial_of_isExtraspecialPGroup hext, ?_, ⟨e.trans co1EquivMonsterCo1⟩⟩
  intro y hy
  have hy' : (y : G) ∈ Subgroup.centralizer
      (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy q hq)
  obtain ⟨q, hq, hqy⟩ := hcent hy'
  rw [← Subtype.ext hqy]
  exact hq

theorem isDoubleBabyCentralizer_of_isTwoACentralizer {a : G} (h : Existence.IsTwoACentralizer a)
    (hsimple : IsSimpleGroup NativeSporadic.B)
    (hcard : Nat.card NativeSporadic.B = monsterBabyOrder) : MonsterIsDoubleBabyCentralizer a := by
  obtain ⟨hperf, hcenter, ⟨e⟩⟩ := h
  refine ⟨Group.isPerfect_def.1 hperf, hcenter, @MulEquiv.isSimpleGroup _ _ _ _ hsimple e, ?_⟩
  rw [Nat.card_congr e.toEquiv, hcard]

theorem isF1Type_of_canonical
    {a z : G} (ha : orderOf a = 2) (hz : orderOf z = 2)
    (hA : Existence.IsTwoACentralizer a) (hB : Existence.IsTwoBCentralizer z)
    (hsimple : IsSimpleGroup NativeSporadic.B)
    (hcard : Nat.card NativeSporadic.B = monsterBabyOrder) : MonsterIsF1Type a z :=
  ⟨ha, hz, isDoubleBabyCentralizer_of_isTwoACentralizer hA hsimple hcard,
    isLeechCentralizerType_of_isTwoBCentralizer hB⟩

end CFSG.Monster.Existence.Compat
