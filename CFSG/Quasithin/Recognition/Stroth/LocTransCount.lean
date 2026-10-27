module

public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang
public import CFSG.Quasithin.Recognition.F4Index

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin

universe u w

private theorem card_edgeStab {G : Type u} [Group G] {G₀ G₁ G₂ : Subgroup G}
    (h₁ : G₁ ≤ G₀) (h₂ : G₂ ≤ G₀) {u v : CosetGeom G₀ G₁ G₂}
    (h : (CosetGeom.graph G₀ G₁ G₂).Adj u v) :
    Nat.card ↥(MulAction.stabilizer ↥G₀ u ⊓ MulAction.stabilizer ↥G₀ v) =
      Nat.card ↥(G₁ ⊓ G₂) := by
  have hEmap : (MulAction.stabilizer ↥G₀ u ⊓ MulAction.stabilizer ↥G₀ v).map G₀.subtype =
      CosetGeom.stab u ⊓ CosetGeom.stab v := by
    rw [Subgroup.map_inf _ _ _ G₀.subtype_injective]
    rfl
  have key : ∀ g : G,
      (MulAction.stabilizer ↥G₀ u ⊓ MulAction.stabilizer ↥G₀ v).map G₀.subtype =
        conjSub g (G₁ ⊓ G₂) →
      Nat.card ↥(MulAction.stabilizer ↥G₀ u ⊓ MulAction.stabilizer ↥G₀ v) =
        Nat.card ↥(G₁ ⊓ G₂) := by
    intro g hmap
    calc Nat.card ↥(MulAction.stabilizer ↥G₀ u ⊓ MulAction.stabilizer ↥G₀ v)
        = Nat.card ↥((MulAction.stabilizer ↥G₀ u ⊓
            MulAction.stabilizer ↥G₀ v).map G₀.subtype) :=
          Nat.card_congr
            (Subgroup.equivMapOfInjective _ G₀.subtype G₀.subtype_injective).toEquiv
      _ = Nat.card ↥(conjSub g (G₁ ⊓ G₂)) := by rw [hmap]
      _ = Nat.card ↥(G₁ ⊓ G₂) :=
          Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective).toEquiv.symm
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge h
  · exact key (g : G) (by
      rw [hEmap, ← hg.1, ← hg.2, CosetGeom.stab_smul, CosetGeom.stab_smul,
        CosetGeom.stab_γ₀ h₁, CosetGeom.stab_γ₁ h₂, ← conjSub_inf])
  · exact key (g : G) (by
      rw [hEmap, ← hg.1, ← hg.2, CosetGeom.stab_smul, CosetGeom.stab_smul,
        CosetGeom.stab_γ₀ h₁, CosetGeom.stab_γ₁ h₂, ← conjSub_inf, inf_comm])

private theorem pathTrans_one {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    (c : α.Completion Y) (a : c.Γ) : c.PathTrans a 1 := by
  intro q q' hq hq'
  have hq1 : c.graph.Adj (q 0) (q 1) := q.adj 0 (by omega)
  have hq'1 : c.graph.Adj (q 0) (q' 1) := by
    rw [hq.1, ← hq'.1]
    exact q'.adj 0 (by omega)
  obtain ⟨g, hg, hg'⟩ := CosetGeom.exists_stab_smul_eq hq1 hq'1
  refine ⟨g, ?_, ?_⟩
  · rw [← hq.1]
    exact hg
  · rw [GPath.smul_eq_iff]
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
    · simpa [hq.1, hq'.1] using hg
    · exact hg'

private theorem qv_mul_qv_not {α : RankTwoAmalgam.{u}} (b : Bool) :
    α.qv b * α.qv (!b) = α.qOne * α.qTwo := by
  cases b <;> simp [RankTwoAmalgam.qv, mul_comm]

private theorem odd_card_stabPath {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    [Finite Y] {c : α.Completion Y} {j : ℕ}
    {q : GPath c.graph (2 * j + 1)}
    (h2 : ∀ g : ↥(c.φ1.range ⊔ c.φ2.range),
      (∀ i, i ≤ 2 * j + 1 → g • q i = q i) → (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1)
    (hq : q.NoBack) :
    Odd (Nat.card ↥(q.stabPath : Subgroup c.G0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdvd
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(q.stabPath : Subgroup c.G0)) 2 hdvd
  have hxfix : ∀ i, i ≤ 2 * j + 1 → (x : c.G0) • q i = q i := fun i hi => x.2 i hi
  have hx2 : orderOf (x : c.G0) = 2 := by
    rw [Subgroup.orderOf_coe, hx]
  have hone : (x : c.G0) = 1 :=
    h2 (x : c.G0) hxfix ⟨1, by rw [hx2, pow_one]⟩
  have hx1 : x = 1 := Subtype.ext (by simpa using hone)
  rw [hx1] at hx
  exact absurd hx (by norm_num)

private theorem exists_smul_of_relIndex_ge {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    [Finite Y] {c : α.Completion Y} {n : ℕ} {a : c.Γ} {q : GPath c.graph n}
    (hq : q ∈ GPath.nbPaths c.graph a n)
    (h : Nat.card ↥(GPath.nbPaths c.graph a n) ≤
      (q.stabPath : Subgroup c.G0).relIndex (c.stv a)) :
    ∀ q' : GPath c.graph n, q' ∈ GPath.nbPaths c.graph a n →
      ∃ g : c.G0, g • a = a ∧ g • q = q' := by
  intro q' hq'
  let A : Subgroup c.G0 := c.stv a
  let P : Subgroup c.G0 := (q.stabPath : Subgroup c.G0)
  let p0 : PathSet c.graph a := ⟨n, q, hq.1⟩
  have hstab : MulAction.stabilizer A p0 = P.subgroupOf A := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, GPath.mem_stabPath_iff]
    constructor
    · intro hfix i hi
      have h' := congrArg (fun x : PathSet c.graph a => x.2.1 i) hfix
      change ((g : c.G0) • q) i = q i at h'
      exact h'
    · intro hfix
      refine PathSet.ext rfl fun i => ?_
      show ((g : c.G0) • q) i = q i
      rw [GPath.smul_apply]
      by_cases hi : i ≤ n
      · exact hfix i hi
      · rw [q.tail i (by omega)]
        exact hfix n le_rfl
  have horbcard : (MulAction.orbit A p0).ncard = P.relIndex A := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  let ι : ↥(GPath.nbPaths c.graph a n) → PathSet c.graph a :=
    fun r => ⟨n, r.1, r.2.1⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : x.1 = y.1 := by
      have := Sigma.mk.inj hxy
      exact eq_of_heq (by simpa using this.2)
    exact Subtype.ext h1
  have hrange : (Set.range ι).ncard = Nat.card ↥(GPath.nbPaths c.graph a n) := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hι]
  have hsub : MulAction.orbit A p0 ⊆ Set.range ι := by
    rintro x ⟨g, rfl⟩
    exact ⟨⟨(g : c.G0) • q, ⟨by
        rw [GPath.smul_apply, hq.1]
        exact MulAction.mem_stabilizer_iff.mp g.2, GPath.smul_noBack hq.2⟩⟩,
      PathSet.ext rfl fun i => rfl⟩
  haveI : Finite (GPath c.graph n) := RankTwoAmalgam.Completion.finite_gpath (c := c) n
  have horbeq : MulAction.orbit A p0 = Set.range ι := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range ι)
    rw [hrange, horbcard]
    exact h
  have hto : ι ⟨q', hq'⟩ ∈ MulAction.orbit A p0 := by
    rw [horbeq]
    exact ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hto
  refine ⟨(g : c.G0), MulAction.mem_stabilizer_iff.mp g.2, ?_⟩
  refine GPath.ext' fun i hi => ?_
  have h' := congrArg (fun x : PathSet c.graph a => x.2.1 i) hg
  change ((g : c.G0) • q) i = q' i at h'
  exact h'

theorem exists_smul_eq_of_stabPath_two {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    [Finite Y] (c : α.Completion Y) (hc : c.IsFaithful) {j e₁ e₂ m : ℕ}
    (hq1 : α.qOne = 2 ^ e₁) (hq2 : α.qTwo = 2 ^ e₂) (hm : Odd m)
    (hB : Nat.card ↥(c.φ1.range ⊓ c.φ2.range) = (α.qOne * α.qTwo) ^ j * m)
    {a : c.Γ} {q q' : GPath c.graph (2 * j + 1)}
    (hq : q ∈ GPath.nbPaths c.graph a (2 * j + 1))
    (hq' : q' ∈ GPath.nbPaths c.graph a (2 * j + 1))
    (h2 : ∀ g : ↥(c.φ1.range ⊔ c.φ2.range),
      (∀ i, i ≤ 2 * j + 1 → g • q i = q i) → (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1) :
    ∃ g : c.G0, g • a = a ∧ g • q = q' := by
  let A : Subgroup c.G0 := c.stv a
  let P : Subgroup c.G0 := (q.stabPath : Subgroup c.G0)
  let E : Subgroup c.G0 :=
    MulAction.stabilizer c.G0 (q 0) ⊓ MulAction.stabilizer c.G0 (q 1)
  have hq0 : q 0 = a := hq.1
  have hP_le_A : P ≤ A := GPath.stabPath_le_stabilizer q hq.1
  have hP_le_E : P ≤ E := by
    intro g hg
    exact ⟨hg 0 (by omega), hg 1 (by omega)⟩
  have hE_le_A : E ≤ A := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, ← hq.1]
    exact (Subgroup.mem_inf.mp hg).1
  have hoddP : Odd (Nat.card ↥P) := odd_card_stabPath (c := c) h2 hq.2
  have hEcard : Nat.card ↥E = (α.qOne * α.qTwo) ^ j * m := by
    have hadj : c.graph.Adj (q 0) (q 1) := q.adj 0 (by omega)
    rw [show E = MulAction.stabilizer c.G0 (q 0) ⊓
          MulAction.stabilizer c.G0 (q 1) from rfl,
      card_edgeStab (G := Y) (G₀ := c.φ1.range ⊔ c.φ2.range)
        (G₁ := c.φ1.range) (G₂ := c.φ2.range) le_sup_left le_sup_right hadj,
      hB]
  have hPrelE : 2 ^ ((e₁ + e₂) * j) ≤ P.relIndex E := by
    have hcardE : Nat.card ↥E = 2 ^ ((e₁ + e₂) * j) * m := by
      rw [hEcard, hq1, hq2, ← pow_add, pow_mul]
    have hrel : P.relIndex E * Nat.card ↥(P ⊓ E) = Nat.card ↥E :=
      Subgroup.relIndex_mul_card (H := P) (K := E)
    rw [inf_eq_left.mpr hP_le_E, hcardE] at hrel
    have hdvd : 2 ^ ((e₁ + e₂) * j) ∣ P.relIndex E * Nat.card ↥P := by
      rw [hrel]
      exact ⟨m, rfl⟩
    have hcop : Nat.Coprime (2 ^ ((e₁ + e₂) * j)) (Nat.card ↥P) :=
      (hoddP.coprime_two_left).pow_left _
    have hdvd' : 2 ^ ((e₁ + e₂) * j) ∣ P.relIndex E :=
      hcop.dvd_of_dvd_mul_right hdvd
    have hpos : 0 < P.relIndex E := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := P.subgroupOf E))
    exact Nat.le_of_dvd hpos hdvd'
  have hEindex : E.relIndex A = α.qv (CosetGeom.vtype a) + 1 := by
    have htake : ((q.take 1 (by omega)).stabPath : Subgroup c.G0) = E := by
      rw [GPath.stabPath_take_one q (by omega)]
    have hmem1 : q.take 1 (by omega) ∈ GPath.nbPaths c.graph a 1 := by
      refine ⟨?_, hq.2.take 1 (by omega)⟩
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le 1)]
      exact hq.1
    have h := RankTwoAmalgam.Completion.relIndex_stabPath (c := c) hc (a := a) (n := 1)
      (pathTrans_one c a) (p := q.take 1 (by omega)) hmem1
    rw [← htake]
    exact h.trans (by simp [RankTwoAmalgam.pathNum])
  have hPrelA : P.relIndex A = P.relIndex E * E.relIndex A :=
    (Subgroup.relIndex_mul_relIndex P E A hP_le_E hE_le_A).symm
  have hbound : (α.qv (CosetGeom.vtype a) + 1) * 2 ^ ((e₁ + e₂) * j) ≤
      P.relIndex A := by
    rw [hPrelA, hEindex, mul_comm (P.relIndex E) (α.qv (CosetGeom.vtype a) + 1)]
    exact Nat.mul_le_mul_left _ hPrelE
  have hcardPaths : Nat.card ↥(GPath.nbPaths c.graph a (2 * j + 1)) =
      (α.qv (CosetGeom.vtype a) + 1) * 2 ^ ((e₁ + e₂) * j) := by
    rw [RankTwoAmalgam.Completion.card_nbPaths hc a (2 * j + 1),
      RankTwoAmalgam.pathNum_odd, qv_mul_qv_not, hq1, hq2, ← pow_add, pow_mul]
  have hle : Nat.card ↥(GPath.nbPaths c.graph a (2 * j + 1)) ≤
      (q.stabPath : Subgroup c.G0).relIndex (c.stv a) := by
    rw [hcardPaths]
    exact hbound
  exact exists_smul_of_relIndex_ge hq hle q' hq'

private theorem pathTrans_of_odd_stabPath {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    [Finite Y] (c : α.Completion Y) (hc : c.IsFaithful) {j e₁ e₂ m : ℕ}
    (hq1 : α.qOne = 2 ^ e₁) (hq2 : α.qTwo = 2 ^ e₂) (hm : Odd m)
    (hB : Nat.card ↥(c.φ1.range ⊓ c.φ2.range) = (α.qOne * α.qTwo) ^ j * m)
    (h2 : ∀ p : GPath c.graph (2 * j + 1), p.NoBack →
      ∀ g : ↥(c.φ1.range ⊔ c.φ2.range), (∀ i, i ≤ 2 * j + 1 → g • p i = p i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1)
    (a : c.Γ) : c.PathTrans a (2 * j + 1) := by
  intro q q' hq hq'
  exact exists_smul_eq_of_stabPath_two c hc hq1 hq2 hm hB hq hq'
    (fun g hfix hg => h2 q hq.2 g hfix hg)

theorem isLocallyTransHat_of_odd_stabPath (α : RankTwoAmalgam.{u}) {Y : Type w} [Group Y]
    [Finite Y] (c : α.Completion Y) (hc : c.IsFaithful) {j e₁ e₂ m : ℕ}
    (hq1 : α.qOne = 2 ^ e₁) (hq2 : α.qTwo = 2 ^ e₂) (hm : Odd m)
    (hB : Nat.card ↥(c.φ1.range ⊓ c.φ2.range) = (α.qOne * α.qTwo) ^ j * m)
    (h2 : ∀ p : GPath c.graph (2 * j + 1), p.NoBack →
      ∀ g : ↥(c.φ1.range ⊔ c.φ2.range), (∀ i, i ≤ 2 * j + 1 → g • p i = p i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1) :
    IsLocallyTransHat α (2 * j + 1) := by
  intro p p' hp hp' h0
  have htrans := pathTrans_of_odd_stabPath c hc hq1 hq2 hm hB h2 (c.Θ hc (p 0))
  obtain ⟨g, -, hg⟩ := (c.graphCovering hc).transitive_of_transitive' (p 0)
    (c.stabIso hc (p 0)) (2 * j + 1) htrans p p' ⟨rfl, hp⟩ ⟨h0.symm, hp'⟩
  exact ⟨g, hg⟩

end CFSG.Quasithin.Stroth
