module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompAbs
public import CFSG.Walter.AStar.N1
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

section Abs

variable {X : Type*} [Group X] [Finite X]

theorem component_commutes_pCore {K : Subgroup X} (hK : CFSG.IsComponent K) {a p : X} (ha : a ∈ K)
    (hp : p ∈ CFSG.pCore 2 X) : a * p = p * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRs : Group.IsSolvable (CFSG.pCore 2 X) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
    infer_instance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRs
    (Subgroup.Normal.isSubnormal (CFSG.pCore_normal (p := 2) (G := X)))).1 K hK
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  exact (Subgroup.mem_centralizer_iff.mp (hcomm ha) p hp).symm

omit [Finite X] in
theorem not_le_centralizer_of_isComponent {K E : Subgroup X} (hK : CFSG.IsComponent K)
    (hKE : K ≤ E) : ¬ K ≤ Subgroup.centralizer (E : Set X) := by
  intro h
  have hcomm : IsMulCommutative ↥K := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (h a.2) b (hKE b.2)).symm⟩⟩
  have hperf : Group.IsPerfect ↥K := hK.1.1
  have hsub : Subsingleton ↥K := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  exact not_nontrivial_iff_subsingleton.mpr hsub hnt

theorem centralizer_layer_le_pCore (hO : CFSG.pPrimeCore 2 X = ⊥) {w : X}
    (hwc : ∀ g : X, g * w = w * g) (hw1 : w ≠ 1) (hwP : w ∈ CFSG.pCore 2 X)
    (hP : Nat.card (CFSG.pCore 2 X) ≤ 4) :
    Subgroup.centralizer (CFSG.layer X : Set X) ≤ CFSG.pCore 2 X := by
  have hch : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (CFSG.layer X).Normal := inferInstance
  refine le_pCore_of_no_component hO ?_ hwc hw1 hwP hP
  intro K hK hKZ
  exact not_le_centralizer_of_isComponent hK (CFSG.LocalCores.component_le_layer hK) hKZ

theorem map_component_facts (hO : CFSG.pPrimeCore 2 X = ⊥) {w : X} (hwc : ∀ g : X, g * w = w * g)
    (hw1 : w ≠ 1) (hwP : w ∈ CFSG.pCore 2 X) (hP : Nat.card (CFSG.pCore 2 X) ≤ 4)
    {L : Subgroup X} (hL : CFSG.IsComponent L) :
    Group.IsPerfect ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 X))) ∧
      L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≠ ⊥ ∧
      Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 X))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥L := hL.1.1
  have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have hZP : ∀ a : ↥L, a ∈ Subgroup.center ↥L → (a : X) ∈ CFSG.pCore 2 X := by
    intro a ha
    have hle : CFSG.layer X ≤ Subgroup.centralizer ({(a : X)} : Set X) := by
      refine sSup_le fun K hK k hk => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases CFSG.LocalCores.distinct_components_commute hL hK with hLK | hc
      · subst hLK
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨k, hk⟩)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
        exact Subgroup.mem_centralizer_iff.mp (hc a.2) k hk
    have hcentral : (a : X) ∈ Subgroup.centralizer (CFSG.layer X : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
    exact centralizer_layer_le_pCore hO hwc hw1 hwP hP hcentral
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hnonab : ∃ x y : ↥L ⧸ Subgroup.center ↥L, x * y ≠ y * x := hL.1.2.2
  refine ⟨Group.IsPerfect.map _, ?_, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hp2 : IsPGroup 2 ↥L := (CFSG.pCore_isPGroup (p := 2) (G := X)).to_le hbot
    have := hp2.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  · rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    obtain ⟨a, haL, haq⟩ := q.2
    set a' : ↥L := ⟨a, haL⟩ with ha'
    have hc : ∀ b : ↥L, (b * a')⁻¹ * (a' * b) ∈ Subgroup.center ↥L := by
      intro b
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hq
        ⟨QuotientGroup.mk' (CFSG.pCore 2 X) b, ⟨b, b.2, rfl⟩⟩)
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 X) ((b : X) * a) =
          QuotientGroup.mk' (CFSG.pCore 2 X) (a * b) := by
        rw [map_mul, map_mul, haq]
        exact h1
      have h3 := (QuotientGroup.eq (s := CFSG.pCore 2 X)).mp h2
      refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
      exact component_commutes_pCore hL y.2 h3
    have hmk : QuotientGroup.mk (s := Subgroup.center ↥L) a' ∈
        Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hc b
    rw [CFSG.Walter.center_eq_bot_of_isSimpleGroup hnonab, Subgroup.mem_bot,
      QuotientGroup.eq_one_iff] at hmk
    have haP : a ∈ CFSG.pCore 2 X := hZP a' hmk
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) a = 1 := (QuotientGroup.eq_one_iff a).mpr haP
    exact Subtype.ext (by rw [Subgroup.coe_one, ← haq]; exact h1)

end Abs

end InspW2

end S143

end CFSG.Quasithin
