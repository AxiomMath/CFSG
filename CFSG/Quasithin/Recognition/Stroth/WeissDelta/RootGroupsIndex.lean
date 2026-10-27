module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootGroups
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

universe u

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [GraphAction H Γ]

private theorem relIndex_inf_dvd_relIndex_of_normal {G : Type*} [Group G] [Finite G]
    {N K H : Subgroup G} (hKH : K ≤ H) (hNH : N ≤ H)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) :
    (N ⊓ K).relIndex N ∣ K.relIndex H := by
  have h1 := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := K) (K := N) hK).1
  rw [inf_comm] at h1
  have h2 := Subgroup.relIndex_mul_relIndex K (K ⊔ N) H le_sup_left (sup_le hKH hNH)
  rw [h1] at h2
  exact ⟨(K ⊔ N).relIndex H, h2.symm⟩

theorem exists_relIndex_stabPath_succ_eq_two_pow [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    {p : GPath Γ (n + 1)} (hp : p.NoBack) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ e : ℕ, (GPath.stabPath (H := H) (p.take (j + 1) (Nat.succ_le_succ hjn))).relIndex
      (GPath.stabPath (H := H) (p.take j (Nat.le_succ_of_le hjn))) = 2 ^ e := by
  classical
  let his : j ≤ n + 1 := Nat.le_succ_of_le hjn
  let his1 : j + 1 ≤ n + 1 := Nat.succ_le_succ hjn
  let Gj : Subgroup H := (p.take j his).stabPath
  let Gj1 : Subgroup H := (p.take (j + 1) his1).stabPath
  have hvw : Γ.Adj (p j) (p (j - 1)) := by
    have h := p.adj (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at h
    exact h.symm
  obtain ⟨e, he⟩ := hval (p j) (p (j - 1)) hvw
  have hxΩ : Γ.Adj (p j) (p (j + 1)) ∧ p (j + 1) ≠ p (j - 1) := by
    refine ⟨p.adj j (by omega), ?_⟩
    have h := hp (j - 1) (by omega)
    rw [show j - 1 + 2 = j + 1 by omega] at h
    exact h.symm
  let Ω : Type := {y : V // Γ.Adj (p j) y ∧ y ≠ p (j - 1)}
  have hGjv : ∀ g ∈ Gj, g • p j = p j := by
    intro g hg
    have h := (GPath.mem_stabPath_iff.mp hg) j le_rfl
    rwa [GPath.take_apply_of_le p j his (i := j) le_rfl] at h
  have hGjw : ∀ g ∈ Gj, g • p (j - 1) = p (j - 1) := by
    intro g hg
    have h := (GPath.mem_stabPath_iff.mp hg) (j - 1) (by omega)
    rwa [GPath.take_apply_of_le p j his (i := j - 1) (by omega)] at h
  letI : MulAction ↥Gj Ω := neighborAction Gj (p j) (p (j - 1)) hGjv hGjw
  haveI : MulAction.IsPretransitive ↥Gj Ω := by
    refine ⟨fun y y' => ?_⟩
    obtain ⟨g, hg, hgy⟩ :=
      exists_smul_of_mem_stabPath_take hn hM hne hp hj1 (s := n + 1) his hjn
        y.2.1 y'.2.1 y.2.2 y'.2.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩
  let x : Ω := ⟨p (j + 1), hxΩ⟩
  have hidx : (MulAction.stabilizer ↥Gj x).index = Nat.card Ω :=
    MulAction.index_stabilizer_of_transitive ↥Gj x
  have hcardΩ : Nat.card Ω = 2 ^ e := he
  have hle : Gj1 ≤ Gj :=
    GPath.stabPath_take_le (by omega : j ≤ j + 1) his1 his
  have heq : Gj1 = Gj ⊓ MulAction.stabilizer H (p (j + 1)) := by
    ext g
    rw [show Gj1 = (p.take (j + 1) his1).stabPath from rfl,
      show Gj = (p.take j his).stabPath from rfl,
      GPath.mem_stabPath_iff, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      refine ⟨?_, ?_⟩
      · intro i hi
        have h := hg i (by omega)
        rw [GPath.take_apply_of_le p (j + 1) his1 (i := i) (by omega)] at h
        rw [GPath.take_apply_of_le p j his (i := i) hi]
        exact h
      · have h := hg (j + 1) le_rfl
        rw [GPath.take_apply_of_le p (j + 1) his1 (i := j + 1) le_rfl] at h
        exact h
    · rintro ⟨h1, h2⟩
      intro i hi
      rw [GPath.take_apply_of_le p (j + 1) his1 (i := i) hi]
      rcases (by omega : i ≤ j ∨ i = j + 1) with hle' | rfl
      · have h := h1 i hle'
        rwa [GPath.take_apply_of_le p j his (i := i) hle'] at h
      · exact h2
  have hsub : Gj1.subgroupOf Gj = MulAction.stabilizer ↥Gj x := by
    ext g
    rw [Subgroup.mem_subgroupOf, heq, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, hfix⟩
      exact Subtype.ext hfix
    · intro hfix
      have h := congrArg Subtype.val hfix
      change g.1 • p (j + 1) = p (j + 1) at h
      exact ⟨g.2, h⟩
  refine ⟨e, ?_⟩
  rw [show Gj1.relIndex Gj = (Gj1.subgroupOf Gj).index from rfl, hsub, hidx, hcardΩ]

theorem two_pow_relIndex_stabPath [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    {p : GPath Γ (n + 1)} (hp : p.NoBack)
    (hK0 : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) (p 0)) :
    ∃ e : ℕ, (fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ p.stabPath).relIndex
      (fixingSubgroup H (Γ.neighborSet (p 0))) = 2 ^ e := by
  classical
  let K : Subgroup H := fixingSubgroup H (Γ.neighborSet (p 0))
  let G : (j : ℕ) → j ≤ n + 1 → Subgroup H := fun j hj => (p.take j hj).stabPath
  let S : (j : ℕ) → j ≤ n + 1 → Subgroup H := fun j hj => K ⊓ G j hj
  have hbase : ∃ e : ℕ, (S 1 (by omega)).relIndex K = 2 ^ e := by
    have hKG : K ≤ G 1 (by omega) := by
      rw [show G 1 (by omega) = MulAction.stabilizer H (p 0) ⊓
        MulAction.stabilizer H (p 1) from GPath.stabPath_take_one p (by omega)]
      refine le_inf hK0 ?_
      intro g hg
      rw [MulAction.mem_stabilizer_iff]
      exact (mem_fixingSubgroup_iff H).mp hg (p 1) (p.adj 0 (by omega))
    have hSeq : S 1 (by omega) = K := by
      show K ⊓ G 1 (by omega) = K
      exact inf_eq_left.mpr hKG
    rw [hSeq, Subgroup.relIndex_self]
    exact ⟨0, by rw [pow_zero]⟩
  have hstep : ∀ j (hj1 : 1 ≤ j) (hjn : j ≤ n) (hjprev : j ≤ n + 1)
      (hj : j + 1 ≤ n + 1), (∃ e : ℕ, (S j hjprev).relIndex K = 2 ^ e) →
      ∃ e : ℕ, (S (j + 1) hj).relIndex K = 2 ^ e := by
    intro j hj1 hjn hjprev hj hprev
    obtain ⟨e0, he0⟩ := hprev
    let Gj : Subgroup H := G j hjprev
    let Gj1 : Subgroup H := G (j + 1) hj
    let Sj : Subgroup H := S j hjprev
    let Sj1 : Subgroup H := S (j + 1) hj
    have hGle : Gj1 ≤ Gj := by
      show GPath.stabPath (H := H) (p.take (j + 1) hj) ≤
        GPath.stabPath (H := H) (p.take j hjprev)
      exact GPath.stabPath_take_le (by omega : j ≤ j + 1) hj hjprev
    have hSle : Sj1 ≤ Sj := by
      intro g hg
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1,
        hGle (Subgroup.mem_inf.mp hg).2⟩
    have hSleK : Sj ≤ K := inf_le_left
    have hGnormK : Gj ≤ Subgroup.normalizer (K : Set H) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have h0 : g • p 0 = p 0 := (GPath.mem_stabPath_iff.mp hg) 0 (by omega)
      have h0inv : g⁻¹ • p 0 = p 0 :=
        (GPath.mem_stabPath_iff.mp (Gj.inv_mem hg)) 0 (by omega)
      constructor
      · intro hs
        rw [mem_fixingSubgroup_iff] at hs ⊢
        intro y hy
        have hgy : g⁻¹ • y ∈ Γ.neighborSet (p 0) := by
          rw [SimpleGraph.mem_neighborSet]
          have h := (GraphAction.adj_smul g⁻¹ (p 0) y).mpr hy
          rwa [h0inv] at h
        calc (g * s * g⁻¹) • y = g • (s • (g⁻¹ • y)) := by rw [mul_smul, mul_smul]
          _ = g • (g⁻¹ • y) := by rw [hs _ hgy]
          _ = y := by rw [smul_inv_smul]
      · intro hs
        rw [mem_fixingSubgroup_iff] at hs ⊢
        intro y hy
        have hgy : g • y ∈ Γ.neighborSet (p 0) := by
          rw [SimpleGraph.mem_neighborSet]
          have h := (GraphAction.adj_smul g (p 0) y).mpr hy
          rwa [h0] at h
        have h1 := hs (g • y) hgy
        have h2 : g • (s • y) = g • y := by
          have h1' : (g * s * g⁻¹) • (g • y) = g • y := h1
          simpa only [mul_smul, inv_smul_smul] using h1'
        have h3 : g⁻¹ • (g • (s • y)) = g⁻¹ • (g • y) := congrArg (g⁻¹ • ·) h2
        rw [inv_smul_smul, inv_smul_smul] at h3
        exact h3
    have hGnormS : Gj ≤ Subgroup.normalizer (Sj : Set H) := by
      have h := Subgroup.inf_normalizer_le_normalizer_inf (H := K) (K := Gj)
      exact (le_inf hGnormK Subgroup.le_normalizer).trans h
    have hGj1normS : Gj1 ≤ Subgroup.normalizer (Sj : Set H) := le_trans hGle hGnormS
    have hSjeq : Sj1 = Sj ⊓ Gj1 := by
      show K ⊓ G (j + 1) hj = (K ⊓ G j hjprev) ⊓ G (j + 1) hj
      rw [inf_assoc, inf_eq_right.mpr hGle]
    have hdvd : Sj1.relIndex Sj ∣ Gj1.relIndex Gj := by
      rw [hSjeq]
      exact relIndex_inf_dvd_relIndex_of_normal hGle inf_le_right hGj1normS
    obtain ⟨ej, hej⟩ :=
      exists_relIndex_stabPath_succ_eq_two_pow hn hM hne hval hp hj1 hjn
    have hdvd2 : Sj1.relIndex Sj ∣ 2 ^ ej := by
      rw [← hej]
      exact hdvd
    obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    refine ⟨d + e0, ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex Sj1 Sj K hSle hSleK
    rw [hd, he0, ← pow_add] at hmul
    simpa [Sj1] using hmul.symm
  have key : ∀ j (hj1 : 1 ≤ j) (hj : j ≤ n + 1), ∃ e : ℕ, (S j hj).relIndex K = 2 ^ e := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base => intro _; exact hbase
    | succ j hj1 ih =>
        intro hj
        have hjn : j ≤ n := by omega
        have hjprev : j ≤ n + 1 := by omega
        exact hstep j hj1 hjn hjprev hj (ih hjprev)
  have htake : GPath.stabPath (H := H) (p.take (n + 1) le_rfl) =
      GPath.stabPath (H := H) p := by
    rw [GPath.take_self p]
  have hfinal := key (n + 1) (by omega) le_rfl
  rw [show S (n + 1) le_rfl = K ⊓ p.stabPath by
    show K ⊓ G (n + 1) le_rfl = K ⊓ p.stabPath
    rw [show G (n + 1) le_rfl = p.stabPath from htake]] at hfinal
  exact hfinal
