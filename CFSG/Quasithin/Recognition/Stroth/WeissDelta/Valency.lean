module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootGroups
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Ball
public import CFSG.Quasithin.Recognition.Stroth.Weiss80AssemblyFacts
public import CFSG.Quasithin.Recognition.Stroth.SubconstNatural

public section

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y] [Finite Y]

private theorem f1_smul_lv_of_mem_subgroupOf
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) {m : ↥P1}
    (hm : m ∈ (P1 ⊓ P2).subgroupOf P1) :
    RankTwoAmalgam.Completion.f1 (c := c) m • c.lv = c.lv := by
  have hm' : (m : X) ∈ P1 ⊓ P2 := Subgroup.mem_subgroupOf.mp hm
  have heq : RankTwoAmalgam.Completion.f1 (c := c) m =
      RankTwoAmalgam.Completion.f2 (c := c)
        (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) ⟨m.1, hm'⟩) := by
    apply Subtype.ext
    change c.φ1 m = c.φ2 (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) ⟨m.1, hm'⟩)
    exact (c.comm1 ⟨m.1, hm'⟩).trans (c.comm2 ⟨m.1, hm'⟩).symm
  rw [heq]
  exact RankTwoAmalgam.Completion.f2_smul_lv _

private theorem f2_smul_xv_of_mem_subgroupOf
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) {m : ↥P2}
    (hm : m ∈ (P2 ⊓ P1).subgroupOf P2) :
    RankTwoAmalgam.Completion.f2 (c := c) m • c.xv = c.xv := by
  have hm' : (m : X) ∈ P2 ⊓ P1 := Subgroup.mem_subgroupOf.mp hm
  have heq : RankTwoAmalgam.Completion.f2 (c := c) m =
      RankTwoAmalgam.Completion.f1 (c := c)
        (Subgroup.inclusion (inf_le_right : P2 ⊓ P1 ≤ P1) ⟨m.1, hm'⟩) := by
    apply Subtype.ext
    change c.φ2 m = c.φ1 (Subgroup.inclusion (inf_le_right : P2 ⊓ P1 ≤ P1) ⟨m.1, hm'⟩)
    exact (c.comm2 ⟨m.1, hm'.2, hm'.1⟩).trans (c.comm1 ⟨m.1, hm'.2, hm'.1⟩).symm
  rw [heq]
  exact RankTwoAmalgam.Completion.f1_smul_xv _

theorem f1_range_eq_stabilizer_xv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (RankTwoAmalgam.Completion.f1 (c := c)).range = MulAction.stabilizer c.G0 c.xv := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (RankTwoAmalgam.Completion.f1_smul_xv a)
  · intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have h1 : (g : Y) ∈ CosetGeom.stab c.xv := CosetGeom.mem_stab_of_smul_eq hg
    rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, Subtype.ext ha⟩

theorem f1_range_le_stabilizer_xv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (RankTwoAmalgam.Completion.f1 (c := c)).range ≤ MulAction.stabilizer c.G0 c.xv := by
  rintro _ ⟨a, rfl⟩
  exact MulAction.mem_stabilizer_iff.mpr (RankTwoAmalgam.Completion.f1_smul_xv a)

theorem f2_range_eq_stabilizer_lv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (RankTwoAmalgam.Completion.f2 (c := c)).range = MulAction.stabilizer c.G0 c.lv := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (RankTwoAmalgam.Completion.f2_smul_lv a)
  · intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have h1 : (g : Y) ∈ CosetGeom.stab c.lv := CosetGeom.mem_stab_of_smul_eq hg
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, Subtype.ext ha⟩

theorem exists_f1_smul_lv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {w : c.Γ} (hw : c.graph.Adj c.xv w) :
    ∃ g : ↥P1, RankTwoAmalgam.Completion.f1 (c := c) g • c.lv = w := by
  obtain ⟨g, hg, hg2⟩ := CosetGeom.stab_transitive_on_nbrs
    (show c.lv ∈ CosetGeom.nbrs c.xv from CosetGeom.adj_γ₀_γ₁) hw
  rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨a, ?_⟩
  have hfa : RankTwoAmalgam.Completion.f1 (c := c) a = g := Subtype.ext ha
  rw [hfa]
  exact hg2

theorem exists_f2_smul_xv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {w : c.Γ} (hw : c.graph.Adj c.lv w) :
    ∃ g : ↥P2, RankTwoAmalgam.Completion.f2 (c := c) g • c.xv = w := by
  obtain ⟨g, hg, hg2⟩ := CosetGeom.stab_transitive_on_nbrs
    (show c.xv ∈ CosetGeom.nbrs c.lv from CosetGeom.adj_γ₀_γ₁.symm) hw
  rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨a, ?_⟩
  have hfa : RankTwoAmalgam.Completion.f2 (c := c) a = g := Subtype.ext ha
  rw [hfa]
  exact hg2

theorem f2_range_le_stabilizer_lv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (RankTwoAmalgam.Completion.f2 (c := c)).range ≤ MulAction.stabilizer c.G0 c.lv :=
  (f2_range_eq_stabilizer_lv c).le

theorem f1_range_inf_stabilizer_lv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful) :
    (RankTwoAmalgam.Completion.f1 (c := c)).range ⊓ MulAction.stabilizer c.G0 c.lv =
      (psiB P2 (RankTwoAmalgam.Completion.f1 (c := c))).range := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨hg1, hg2⟩
    obtain ⟨a, rfl⟩ := hg1
    have hg2' : RankTwoAmalgam.Completion.f1 (c := c) a • c.lv = c.lv :=
      MulAction.mem_stabilizer_iff.mp hg2
    have h1 : (RankTwoAmalgam.Completion.f1 (c := c) a : Y) ∈ CosetGeom.stab c.lv :=
      CosetGeom.mem_stab_of_smul_eq hg2'
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at h1
    have h2 : c.φ1 a ∈ c.φ1.range ⊓ c.φ2.range := ⟨⟨a, rfl⟩, h1⟩
    rw [c.inter] at h2
    obtain ⟨b, hb⟩ := h2
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change c.φ1 (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b) = c.φ1 a
    exact (c.comm1 b).trans hb
  · rintro g ⟨b, rfl⟩
    refine Subgroup.mem_inf.mpr
      ⟨⟨Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b, rfl⟩, ?_⟩
    exact MulAction.mem_stabilizer_iff.mpr
      (f1_smul_lv_of_mem_subgroupOf c (Subgroup.mem_subgroupOf.mpr b.2))

theorem f2_range_inf_stabilizer_xv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful) :
    (RankTwoAmalgam.Completion.f2 (c := c)).range ⊓ MulAction.stabilizer c.G0 c.xv =
      (psiB P1 (RankTwoAmalgam.Completion.f2 (c := c))).range := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨hg1, hg2⟩
    obtain ⟨a, rfl⟩ := hg1
    have hg2' : RankTwoAmalgam.Completion.f2 (c := c) a • c.xv = c.xv :=
      MulAction.mem_stabilizer_iff.mp hg2
    have h1 : (RankTwoAmalgam.Completion.f2 (c := c) a : Y) ∈ CosetGeom.stab c.xv :=
      CosetGeom.mem_stab_of_smul_eq hg2'
    rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at h1
    have h2 : c.φ2 a ∈ c.φ1.range ⊓ c.φ2.range := ⟨h1, ⟨a, rfl⟩⟩
    rw [c.inter] at h2
    obtain ⟨b, hb⟩ := h2
    refine ⟨⟨b.1, b.2.2, b.2.1⟩, ?_⟩
    apply Subtype.ext
    change c.φ2 (Subgroup.inclusion (inf_le_left : P2 ⊓ P1 ≤ P2) ⟨b.1, b.2.2, b.2.1⟩) =
      c.φ2 a
    exact (c.comm2 b).trans hb
  · rintro g ⟨b, rfl⟩
    refine Subgroup.mem_inf.mpr
      ⟨⟨Subgroup.inclusion (inf_le_left : P2 ⊓ P1 ≤ P2) b, rfl⟩, ?_⟩
    exact MulAction.mem_stabilizer_iff.mpr
      (f2_smul_xv_of_mem_subgroupOf c (Subgroup.mem_subgroupOf.mpr b.2))

theorem card_neighborSet_xv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) : Nat.card (c.graph.neighborSet c.xv) = (P1 ⊓ P2).relIndex P1 := by
  rw [show c.graph.neighborSet c.xv = CosetGeom.nbrs c.xv from rfl]
  rw [RankTwoAmalgam.Completion.nbrs_xv_card (c := c) hc]
  change (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1)).range.index = (P1 ⊓ P2).relIndex P1
  rw [Subgroup.inclusion_range]
  rfl

theorem card_neighborSet_lv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) : Nat.card (c.graph.neighborSet c.lv) = (P1 ⊓ P2).relIndex P2 := by
  rw [show c.graph.neighborSet c.lv = CosetGeom.nbrs c.lv from rfl]
  rw [RankTwoAmalgam.Completion.nbrs_lv_card (c := c) hc]
  change (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2)).range.index =
    (P1 ⊓ P2).relIndex P2
  rw [Subgroup.inclusion_range]
  rfl

private theorem card_neighborSet_smul (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (g : c.G0) (u : c.Γ) :
    Nat.card (c.graph.neighborSet (g • u)) = Nat.card (c.graph.neighborSet u) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun w => ⟨g⁻¹ • w.1, ?_⟩
      invFun := fun w => ⟨g • w.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ((GraphAction.adj_smul (Γ := c.graph) g (g⁻¹ • w.1) u).mp
      (by simpa using w.2.symm)).symm
  · exact (GraphAction.adj_smul (Γ := c.graph) g u w.1).mpr w.2
  · intro w; ext; simp
  · intro w; ext; simp

private theorem card_neighborSet_sdiff (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {v w : c.Γ} (h : c.graph.Adj v w) :
    Nat.card {y : c.Γ // c.graph.Adj v y ∧ y ≠ w} =
      Nat.card (c.graph.neighborSet v) - 1 := by
  have hset : {y : c.Γ | c.graph.Adj v y ∧ y ≠ w} = c.graph.neighborSet v \ {w} := by
    ext y
    simp [SimpleGraph.mem_neighborSet]
  rw [show Nat.card {y : c.Γ // c.graph.Adj v y ∧ y ≠ w} =
    ({y : c.Γ | c.graph.Adj v y ∧ y ≠ w}).ncard from Nat.card_coe_set_eq _,
    hset, Nat.card_coe_set_eq]
  exact Set.ncard_sdiff_singleton_of_mem (s := c.graph.neighborSet v) h

private theorem two_le_card_neighborSet (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1)
    (hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2) (v : c.Γ) :
    2 ≤ Nat.card (c.graph.neighborSet v) := by
  have hxv : 2 ≤ Nat.card (c.graph.neighborSet c.xv) := by
    rw [card_neighborSet_xv c hc]
    exact hv1
  have hlv : 2 ≤ Nat.card (c.graph.neighborSet c.lv) := by
    rw [card_neighborSet_lv c hc]
    exact hv2
  obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) v
  · rw [← hg, card_neighborSet_smul (c := c) g c.xv]
    exact hxv
  · rw [← hg, card_neighborSet_smul (c := c) g c.lv]
    exact hlv

private theorem exists_adj_ne_of_two_le
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1)
    (hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2) :
    ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w := by
  intro v w hvw
  have h2 := two_le_card_neighborSet c hc hv1 hv2 v
  have h1 : 1 < (c.graph.neighborSet v).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  exact Set.exists_ne_of_one_lt_ncard h1 w

theorem exists_regular_root_xv {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n)
    (hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1) (hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2) :
    ∃ R : Subgroup c.G0, R ≤ (psiB P2 (RankTwoAmalgam.Completion.f1 (c := c))).range ∧
      ∀ y y' : c.Γ, c.graph.Adj c.xv y → c.graph.Adj c.xv y' → y ≠ c.lv → y' ≠ c.lv →
        ∃! g : ↥R, (g : c.G0) • y = y' := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdeg := exists_adj_ne_of_two_le c hc hv1 hv2
  have hadj : c.graph.Adj c.lv c.xv := CosetGeom.adj_γ₀_γ₁.symm
  obtain ⟨p, hp, hplast, hpne⟩ := exists_backward_noBack (Γ := c.graph) hdeg hadj m
  have hx : c.graph.Adj (p m) c.xv := by rw [hplast]; exact hadj.symm
  have hqnb : (p.snoc c.xv hx).NoBack :=
    GPath.noBack_snoc hp hx (fun _ => (hpne (by omega)).symm)
  refine ⟨pathRootGroup c.G0 c.graph (p.snoc c.xv hx), ?_, ?_⟩
  · have hxle : pathRootGroup c.G0 c.graph (p.snoc c.xv hx) ≤
        MulAction.stabilizer c.G0 c.xv := by
      have h := pathRootGroup_le_stabilizer_last (D := c.G0) (p := p.snoc c.xv hx)
        (n := m + 1) (by omega)
      simpa [GPath.snoc_last] using h
    have hlle : pathRootGroup c.G0 c.graph (p.snoc c.xv hx) ≤
        MulAction.stabilizer c.G0 c.lv := by
      have h := pathRootGroup_le_stabilizer_penultimate (D := c.G0) (p := p.snoc c.xv hx)
        (n := m + 1) (by omega)
      simpa [GPath.snoc_of_le, hplast] using h
    rw [← f1_range_eq_stabilizer_xv c] at hxle
    rw [← f1_range_inf_stabilizer_lv c hc]
    exact le_inf hxle hlle
  · intro y y' hy hy' hne hne'
    refine pathRootGroup_regular_of_weissFree (n := m + 1) (by omega) hM hW hqnb ?_ ?_ ?_ ?_
    · simpa using hy
    · simpa using hy'
    · simpa [GPath.snoc_of_le, hplast] using hne
    · simpa [GPath.snoc_of_le, hplast] using hne'

theorem exists_regular_root_lv {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n)
    (hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1) (hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2) :
    ∃ R : Subgroup c.G0, R ≤ (psiB P1 (RankTwoAmalgam.Completion.f2 (c := c))).range ∧
      ∀ y y' : c.Γ, c.graph.Adj c.lv y → c.graph.Adj c.lv y' → y ≠ c.xv → y' ≠ c.xv →
        ∃! g : ↥R, (g : c.G0) • y = y' := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdeg := exists_adj_ne_of_two_le c hc hv1 hv2
  have hadj : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  obtain ⟨p, hp, hplast, hpne⟩ := exists_backward_noBack (Γ := c.graph) hdeg hadj m
  have hx : c.graph.Adj (p m) c.lv := by rw [hplast]; exact hadj.symm
  have hqnb : (p.snoc c.lv hx).NoBack :=
    GPath.noBack_snoc hp hx (fun _ => (hpne (by omega)).symm)
  refine ⟨pathRootGroup c.G0 c.graph (p.snoc c.lv hx), ?_, ?_⟩
  · have hxle : pathRootGroup c.G0 c.graph (p.snoc c.lv hx) ≤
        MulAction.stabilizer c.G0 c.lv := by
      have h := pathRootGroup_le_stabilizer_last (D := c.G0) (p := p.snoc c.lv hx)
        (n := m + 1) (by omega)
      simpa [GPath.snoc_last] using h
    have hllee : pathRootGroup c.G0 c.graph (p.snoc c.lv hx) ≤
        MulAction.stabilizer c.G0 c.xv := by
      have h := pathRootGroup_le_stabilizer_penultimate (D := c.G0) (p := p.snoc c.lv hx)
        (n := m + 1) (by omega)
      simpa [GPath.snoc_of_le, hplast] using h
    rw [← f2_range_eq_stabilizer_lv c] at hxle
    rw [← f2_range_inf_stabilizer_xv c hc]
    exact le_inf hxle hllee
  · intro y y' hy hy' hne hne'
    refine pathRootGroup_regular_of_weissFree (n := m + 1) (by omega) hM hW hqnb ?_ ?_ ?_ ?_
    · simpa using hy
    · simpa using hy'
    · simpa [GPath.snoc_of_le, hplast] using hne
    · simpa [GPath.snoc_of_le, hplast] using hne'

theorem card_neighborSet_eq (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (w : c.Γ) :
    ((∃ g : c.G0, g • c.xv = w) ∧
        Nat.card (c.graph.neighborSet w) = (P1 ⊓ P2).relIndex P1) ∨
      ((∃ g : c.G0, g • c.lv = w) ∧
        Nat.card (c.graph.neighborSet w) = (P1 ⊓ P2).relIndex P2) := by
  obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) w
  · left
    exact ⟨⟨g, hg⟩, by rw [← hg, card_neighborSet_smul (c := c) g c.xv, card_neighborSet_xv c hc]⟩
  · right
    exact ⟨⟨g, hg⟩, by rw [← hg, card_neighborSet_smul (c := c) g c.lv, card_neighborSet_lv c hc]⟩

theorem card_adj_ne_eq_two_pow (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    ∀ v w : c.Γ, c.graph.Adj v w →
      ∃ e : ℕ, Nat.card {y : c.Γ // c.graph.Adj v y ∧ y ≠ w} = 2 ^ e := by
  intro v w hvw
  have hdiff := card_neighborSet_sdiff c hvw
  obtain ⟨e, -, he⟩ := hV1
  obtain ⟨f, -, hf⟩ := hV2
  rcases card_neighborSet_eq c hc v with ⟨-, hv⟩ | ⟨-, hv⟩
  · exact ⟨e, by rw [hdiff, hv, he, Nat.add_sub_cancel]⟩
  · exact ⟨f, by rw [hdiff, hv, hf, Nat.add_sub_cancel]⟩

theorem exists_adj_ne (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (hv1 : 3 ≤ (P1 ⊓ P2).relIndex P1)
    (hv2 : 3 ≤ (P1 ⊓ P2).relIndex P2) :
    ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w :=
  exists_adj_ne_of_two_le c hc (by omega) (by omega)

private theorem natCard_neighborSet_eq_nbrs (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (u : c.Γ) :
    Nat.card (c.graph.neighborSet u) = Nat.card (nbrs (Γ := c.graph) u) := rfl

private theorem f1_injective (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) : Function.Injective (RankTwoAmalgam.Completion.f1 (c := c)) := by
  intro x y hxy
  exact hc.1 (congrArg Subtype.val hxy)

private theorem f2_injective (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) : Function.Injective (RankTwoAmalgam.Completion.f2 (c := c)) := by
  intro x y hxy
  exact hc.2.2 (congrArg Subtype.val hxy)

private theorem exists_pow_card_nbrs_xv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hV : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1) :
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card (nbrs (Γ := c.graph) c.xv) = 1 + 2 ^ e := by
  obtain ⟨e, he, hrel⟩ := hV
  exact ⟨e, he, by rw [← natCard_neighborSet_eq_nbrs, card_neighborSet_xv c hc, hrel, add_comm]⟩

private theorem exists_pow_card_nbrs_lv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hV : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card (nbrs (Γ := c.graph) c.lv) = 1 + 2 ^ e := by
  obtain ⟨e, he, hrel⟩ := hV
  exact ⟨e, he, by rw [← natCard_neighborSet_eq_nbrs, card_neighborSet_lv c hc, hrel, add_comm]⟩

private theorem relIndex_eq_card_nbrs_xv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) :
    (P1 ⊓ P2).relIndex P1 = Nat.card (nbrs (Γ := c.graph) c.xv) := by
  rw [← natCard_neighborSet_eq_nbrs, ← card_neighborSet_xv c hc]

private theorem relIndex_eq_card_nbrs_lv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) :
    (P1 ⊓ P2).relIndex P2 = Nat.card (nbrs (Γ := c.graph) c.lv) := by
  rw [← natCard_neighborSet_eq_nbrs, ← card_neighborSet_lv c hc]

theorem relIndex_eq_of_sz {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n) {a : ℕ} (ha : 1 ≤ a)
    (hSz : HasNormalCopy (Subconst P1 P2) ↥(Sz a))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    (P1 ⊓ P2).relIndex P1 = 2 ^ (2 * (2 * a + 1)) + 1 := by
  classical
  haveI : Fintype c.Γ := Fintype.ofFinite c.Γ
  haveI : DecidableRel c.graph.Adj := fun v w => Classical.dec _
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  obtain ⟨R, hRle, hRreg⟩ := exists_regular_root_xv hn c hc hM hW hv1 hv2
  have hcard := subconstNatural_sz (Γ := c.graph) (D := c.G0) subconstNatural a ha
    (f1_injective c hc) (f1_range_le_stabilizer_xv c) (f1_range_inf_stabilizer_lv c hc)
    (fun w hw => exists_f1_smul_lv c hw) R hRle hRreg CosetGeom.adj_γ₀_γ₁
    (by
      obtain ⟨e, he, hpow⟩ := exists_pow_card_nbrs_xv c hc hV1
      exact ⟨e, he, by rwa [Nat.card_eq_fintype_card] at hpow⟩) hSz
  rw [relIndex_eq_card_nbrs_xv c hc, Nat.card_eq_fintype_card, hcard]

theorem relIndex_eq_of_l2 {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n) {m : ℕ} (hm : 2 ≤ m)
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    (P1 ⊓ P2).relIndex P2 = 2 ^ m + 1 := by
  classical
  haveI : Fintype c.Γ := Fintype.ofFinite c.Γ
  haveI : DecidableRel c.graph.Adj := fun v w => Classical.dec _
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  obtain ⟨R, hRle, hRreg⟩ := exists_regular_root_lv hn c hc hM hW hv1 hv2
  have hcard := subconstNatural_l2 (Γ := c.graph) (D := c.G0) (P1 := P2) (P2 := P1)
    (ψ1 := RankTwoAmalgam.Completion.f2 (c := c)) (u := c.lv) (v := c.xv) subconstNatural m hm
    (f2_injective c hc) (f2_range_eq_stabilizer_lv c).le (f2_range_inf_stabilizer_xv c hc)
    (fun w hw => exists_f2_smul_xv c hw) R hRle hRreg CosetGeom.adj_γ₀_γ₁.symm
    (by
      obtain ⟨e, he, hpow⟩ := exists_pow_card_nbrs_lv c hc hV2
      exact ⟨e, he, by rwa [Nat.card_eq_fintype_card] at hpow⟩) hL2
  rw [relIndex_eq_card_nbrs_lv c hc, Nat.card_eq_fintype_card, hcard]

theorem relIndex_eq_of_u3 {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n) {k : ℕ} (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    (P1 ⊓ P2).relIndex P1 = 2 ^ (3 * k) + 1 := by
  classical
  haveI : Fintype c.Γ := Fintype.ofFinite c.Γ
  haveI : DecidableRel c.graph.Adj := fun v w => Classical.dec _
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  obtain ⟨R, hRle, hRreg⟩ := exists_regular_root_xv hn c hc hM hW hv1 hv2
  have hcard := subconstNatural_psu3 (Γ := c.graph) (D := c.G0) (X := X) (P1 := P1) (P2 := P2)
    (ψ1 := RankTwoAmalgam.Completion.f1 (c := c)) (u := c.xv) (v := c.lv) subconstNatural k F hk hF
    (f1_injective c hc) (f1_range_le_stabilizer_xv c) (f1_range_inf_stabilizer_lv c hc)
    (fun w hw => exists_f1_smul_lv c hw) R hRle hRreg CosetGeom.adj_γ₀_γ₁
    (by
      obtain ⟨e, he, hpow⟩ := exists_pow_card_nbrs_xv c hc hV1
      exact ⟨e, he, by rwa [Nat.card_eq_fintype_card] at hpow⟩) hU3
  rw [relIndex_eq_card_nbrs_xv c hc, Nat.card_eq_fintype_card, hcard]

private theorem f1_mem_fixingSubgroup_xv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {m : ↥P1} (hm : m ∈ ((P1 ⊓ P2).subgroupOf P1).normalCore) :
    RankTwoAmalgam.Completion.f1 (c := c) m ∈
      fixingSubgroup c.G0 (c.graph.neighborSet c.xv) := by
  rw [mem_fixingSubgroup_iff]
  intro z hz
  obtain ⟨a, ha⟩ := exists_f1_smul_lv c hz
  rw [← ha]
  let F1 : ↥P1 →* c.G0 := RankTwoAmalgam.Completion.f1 (c := c)
  change F1 m • (F1 a • c.lv) = F1 a • c.lv
  rw [← mul_smul, ← map_mul]
  conv_lhs => rw [show m * a = a * (a⁻¹ * m * a) by group]
  rw [map_mul, mul_smul]
  congr 1
  exact f1_smul_lv_of_mem_subgroupOf c
    (Subgroup.normalCore_le _ (by simpa using
      (Subgroup.normalCore_normal _).conj_mem m hm a⁻¹))

private theorem f2_mem_fixingSubgroup_lv
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {m : ↥P2} (hm : m ∈ ((P2 ⊓ P1).subgroupOf P2).normalCore) :
    RankTwoAmalgam.Completion.f2 (c := c) m ∈
      fixingSubgroup c.G0 (c.graph.neighborSet c.lv) := by
  rw [mem_fixingSubgroup_iff]
  intro z hz
  obtain ⟨a, ha⟩ := exists_f2_smul_xv c hz
  rw [← ha]
  let F2 : ↥P2 →* c.G0 := RankTwoAmalgam.Completion.f2 (c := c)
  change F2 m • (F2 a • c.xv) = F2 a • c.xv
  rw [← mul_smul, ← map_mul]
  conv_lhs => rw [show m * a = a * (a⁻¹ * m * a) by group]
  rw [map_mul, mul_smul]
  congr 1
  exact f2_smul_xv_of_mem_subgroupOf c
    (Subgroup.normalCore_le _ (by simpa using
      (Subgroup.normalCore_normal _).conj_mem m hm a⁻¹))

private theorem fixingSubgroup_conj_le (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (g : c.G0) (u : c.Γ) :
    (fixingSubgroup c.G0 (c.graph.neighborSet u)).map (MulAut.conj g).toMonoidHom ≤
      fixingSubgroup c.G0 (c.graph.neighborSet (g • u)) := by
  rintro _ ⟨k, hk, rfl⟩
  refine (mem_fixingSubgroup_iff c.G0).mpr ?_
  intro z hz
  show (MulAut.conj g) k • z = z
  have hk' := (mem_fixingSubgroup_iff c.G0).mp hk
  have hz' : c.graph.Adj u (g⁻¹ • z) :=
    (GraphAction.adj_smul (Γ := c.graph) g u (g⁻¹ • z)).mp (by simpa using hz)
  have hstep : (MulAut.conj g) k • z = g • (k • (g⁻¹ • z)) := by
    rw [MulAut.conj_apply, mul_smul, mul_smul]
  rw [hstep, hk' (g⁻¹ • z) hz']
  simp

private noncomputable def fixingSubgroupConjHom
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (g : c.G0) (u : c.Γ) :
    ↥(fixingSubgroup c.G0 (c.graph.neighborSet u)) →*
      ↥(fixingSubgroup c.G0 (c.graph.neighborSet (g • u))) where
  toFun k := ⟨(MulAut.conj g) (k : c.G0), fixingSubgroup_conj_le c g u ⟨k, k.2, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' := by intro a b; apply Subtype.ext; exact map_mul _ _ _

private theorem fixingSubgroupConjHom_injective
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (g : c.G0) (u : c.Γ) :
    Function.Injective (fixingSubgroupConjHom c g u) := by
  intro a b hab
  have h : (MulAut.conj g) (a : c.G0) = (MulAut.conj g) (b : c.G0) :=
    congrArg Subtype.val hab
  exact Subtype.ext ((MulAut.conj g).injective h)

theorem not_isPGroup_fixingSubgroup (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (hK1 : ¬ IsPGroup 2 ↥((P1 ⊓ P2).subgroupOf P1).normalCore)
    (hK2 : ¬ IsPGroup 2 ↥((P2 ⊓ P1).subgroupOf P2).normalCore) (w : c.Γ) :
    ¬ IsPGroup 2 ↥(fixingSubgroup c.G0 (c.graph.neighborSet w)) := by
  have hxv : ¬ IsPGroup 2 ↥(fixingSubgroup c.G0 (c.graph.neighborSet c.xv)) := by
    intro hP
    apply hK1
    let φ : ↥(((P1 ⊓ P2).subgroupOf P1).normalCore) →*
        ↥(fixingSubgroup c.G0 (c.graph.neighborSet c.xv)) :=
      { toFun := fun n => ⟨RankTwoAmalgam.Completion.f1 (c := c) (n : ↥P1),
          f1_mem_fixingSubgroup_xv c n.2⟩
        map_one' := by apply Subtype.ext; exact map_one _
        map_mul' := by intro a b; apply Subtype.ext; exact map_mul _ _ _ }
    refine hP.of_injective φ ?_
    intro a b hab
    have h1 : (a : ↥P1) = (b : ↥P1) :=
      f1_injective c hc (congrArg Subtype.val hab)
    exact Subtype.ext h1
  have hlv : ¬ IsPGroup 2 ↥(fixingSubgroup c.G0 (c.graph.neighborSet c.lv)) := by
    intro hP
    apply hK2
    let φ : ↥(((P2 ⊓ P1).subgroupOf P2).normalCore) →*
        ↥(fixingSubgroup c.G0 (c.graph.neighborSet c.lv)) :=
      { toFun := fun n => ⟨RankTwoAmalgam.Completion.f2 (c := c) (n : ↥P2),
          f2_mem_fixingSubgroup_lv c n.2⟩
        map_one' := by apply Subtype.ext; exact map_one _
        map_mul' := by intro a b; apply Subtype.ext; exact map_mul _ _ _ }
    refine hP.of_injective φ ?_
    intro a b hab
    have h1 : (a : ↥P2) = (b : ↥P2) :=
      f2_injective c hc (congrArg Subtype.val hab)
    exact Subtype.ext h1
  obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) w
  · rw [← hg]
    intro hP
    exact hxv (hP.of_injective (fixingSubgroupConjHom c g c.xv)
      (fixingSubgroupConjHom_injective c g c.xv))
  · rw [← hg]
    intro hP
    exact hlv (hP.of_injective (fixingSubgroupConjHom c g c.lv)
      (fixingSubgroupConjHom_injective c g c.lv))

end CFSG.Quasithin.Stroth.WeissDelta
