module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPath
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsSz
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsU3
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalL2

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

theorem isRootAt_pathRootGroup [Finite H] {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n)
    (hW : WeissFree H Γ n) (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {q : GPath Γ n}
    (hq : q.NoBack) : IsRootAt H Γ (q n) (q (n - 1)) (pathRootGroup H Γ q) := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hnm1 : n - 1 + 1 = n := by omega
  have hadj : Γ.Adj (q (n - 1)) (q n) := by
    have h := q.adj (n - 1) (by omega)
    rwa [hnm1] at h
  have hmfix : pathRootGroup H Γ q ≤
      MulAction.stabilizer H (q n) ⊓ MulAction.stabilizer H (q (n - 1)) := by
    intro g hg
    refine ⟨MulAction.mem_stabilizer_iff.mpr
        (smul_path_eq_self_of_mem_pathRootGroup hn hg n le_rfl), ?_⟩
    exact MulAction.mem_stabilizer_iff.mpr
      (smul_path_eq_self_of_mem_pathRootGroup hn hg (n - 1) (by omega))
  refine ⟨hmfix, pathRootGroup_isPGroup hn hW hval hq, ?_, ?_⟩
  · intro α β hα hβ hαne hβne
    obtain ⟨g, hg, hgα⟩ := hM q hq α β hα hβ hαne hβne
    exact ⟨g, mem_pathRootGroup.mpr hg, hgα⟩
  · obtain ⟨ω', hω', hω'ne⟩ := hne (q n) (q (n - 1)) hadj.symm
    refine ⟨ω', hω', hω'ne, ?_⟩
    intro t ht x hx
    exact pathRootGroup_torus_conj_mem hn hM hne hK hq hω' hω'ne t ht x hx

private theorem le_sup_of_map_le {z : V} {X : Type} [Group X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}]
    (π : ↥(MulAction.stabilizer H z) →* X)
    (hker : π.ker = (fixingSubgroup H (Γ.neighborSet z)).subgroupOf
      (MulAction.stabilizer H z))
    {U Q : Subgroup H} (hU : U ≤ MulAction.stabilizer H z)
    (hQ : Q ≤ MulAction.stabilizer H z)
    (hle : (Q.subgroupOf (MulAction.stabilizer H z)).map π ≤
      (U.subgroupOf (MulAction.stabilizer H z)).map π) :
    Q ≤ U ⊔ fixingSubgroup H (Γ.neighborSet z) := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  intro q hq
  have hqX : π (⟨q, hQ hq⟩ : Gz) ∈ (Q.subgroupOf Gz).map π :=
    Subgroup.mem_map_of_mem π (show (⟨q, hQ hq⟩ : Gz) ∈ Q.subgroupOf Gz from hq)
  have hqU : π (⟨q, hQ hq⟩ : Gz) ∈ (U.subgroupOf Gz).map π := hle hqX
  rcases Subgroup.mem_map.mp hqU with ⟨u, hu, hpi⟩
  have hprod : (⟨q, hQ hq⟩ : Gz) * u⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpi]
    simp
  rw [hker] at hprod
  have hF : q * (u : H)⁻¹ ∈ F := Subgroup.mem_subgroupOf.mp hprod
  have huU : (u : H) ∈ U := Subgroup.mem_subgroupOf.mp hu
  have hdecomp : q = (q * (u : H)⁻¹) * (u : H) := by group
  rw [hdecomp]
  exact (U ⊔ F).mul_mem (Subgroup.mem_sup_right hF) (Subgroup.mem_sup_left huU)

private theorem pathRootGroup_map_eq_root [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    {q : GPath Γ n} (hq : q.NoBack) {z : V} (hqz : q n = z)
    {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}]
    {N : Subgroup X} (π : ↥(MulAction.stabilizer H z) →* X)
    (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hL : RankOneLocal X {w : V // Γ.Adj z w} N)
    (hR : RankOneRoot X {w : V // Γ.Adj z w} N)
    (hfin : Finite {w : V // Γ.Adj z w})
    (ω : {w : V // Γ.Adj z w}) (hω : ω.1 = q (n - 1))
    (Rω : Subgroup X) (hRωst : Rω ≤ MulAction.stabilizer X ω)
    (hRωn : (Rω.subgroupOf (MulAction.stabilizer X ω)).Normal)
    (hRω2 : IsPGroup 2 Rω)
    (hRωreg : ∀ α β : {w : V // Γ.Adj z w}, α ≠ ω → β ≠ ω →
      ∃! r : Rω, (r : X) • α = β) :
    ((pathRootGroup H Γ q).subgroupOf (MulAction.stabilizer H z)).map π = Rω := by
  subst z
  classical
  letI : Fintype {w : V // Γ.Adj (q n) w} := Fintype.ofFinite {w : V // Γ.Adj (q n) w}
  let Gz := MulAction.stabilizer H (q n)
  let F := fixingSubgroup H (Γ.neighborSet (q n))
  let U := pathRootGroup H Γ q
  have hUGz : U ≤ Gz := by
    intro x hx
    exact MulAction.mem_stabilizer_iff.mpr
      (smul_path_eq_self_of_mem_pathRootGroup hn hx n le_rfl)
  have hUω : U ≤ MulAction.stabilizer H ω.1 := by
    intro x hx
    rw [hω]
    exact MulAction.mem_stabilizer_iff.mpr
      (smul_path_eq_self_of_mem_pathRootGroup hn hx (n - 1) (by omega))
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := q n) π hact
  have hSmap : ∀ (w y : V) (hw : Γ.Adj (q n) w) (hy : Γ.Adj (q n) y),
      ((socTorus H Γ (q n) w y).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj (q n) w}) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj (q n) w}) :=
    fun w y hw hy => compatibleQuotient_socTorus (H := H) (Γ := Γ) (z := q n) π hπ
      hact (hK (q n)) hL hw hy
  have hAt : IsRootAt H Γ (q n) ω.1 U := by
    rw [hω]
    exact isRootAt_pathRootGroup hn hM hW hne hval hK hq
  obtain ⟨ω', hzω', hω'ne, hnorm⟩ := hAt.2.2.2
  let Q := (U.subgroupOf Gz).map π
  have hU2 : IsPGroup 2 U := pathRootGroup_isPGroup hn hW hval hq
  have hUs2 : IsPGroup 2 (U.subgroupOf Gz) := by
    rw [← Subgroup.comap_subtype]
    exact hU2.comap_subtype
  have hQ2 : IsPGroup 2 Q := IsPGroup.map hUs2 π
  have hQleω : Q ≤ MulAction.stabilizer X ω := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    apply Subtype.ext
    rw [hact u ω]
    exact MulAction.mem_stabilizer_iff.mp (hUω (Subgroup.mem_subgroupOf.mp hu))
  have hQnorm : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓
      MulAction.stabilizer X (⟨ω', hzω'⟩ : {w : V // Γ.Adj (q n) w}),
      ∀ x ∈ Q, t * x * t⁻¹ ∈ Q :=
    conj_mem_map_subgroupOf_of_socTorus (H := H) (Γ := Γ) (z := q n) π hker hSmap (hK (q n))
      ω.2 hzω' hUGz hnorm
  have hω'ne' : ω ≠ ⟨ω', hzω'⟩ :=
    fun h => hω'ne (congrArg Subtype.val h).symm
  have hQleRω : Q ≤ Rω :=
    hR.le_root ω ⟨ω', hzω'⟩ hω'ne' Q Rω hQleω hRωst hRωn hQ2 hRω2 hRωreg hQnorm
  have hQtrans : ∀ α β : {w : V // Γ.Adj (q n) w}, α ≠ ω → β ≠ ω →
      ∃ q ∈ Q, q • α = β := by
    intro α β hα hβ
    have hαne : α.1 ≠ q (n - 1) := fun h => hα (Subtype.ext (h.trans hω.symm))
    have hβne : β.1 ≠ q (n - 1) := fun h => hβ (Subtype.ext (h.trans hω.symm))
    obtain ⟨g, hg, hgα⟩ := hM q hq α.1 β.1 α.2 β.2 hαne hβne
    refine ⟨π ⟨g, hUGz (mem_pathRootGroup.mpr hg)⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem π
        (show (⟨g, hUGz (mem_pathRootGroup.mpr hg)⟩ : Gz) ∈ U.subgroupOf Gz from
          mem_pathRootGroup.mpr hg)
    · apply Subtype.ext
      rw [hact ⟨g, hUGz (mem_pathRootGroup.mpr hg)⟩ α]
      exact hgα
  have hex : ∃ β : {w : V // Γ.Adj (q n) w}, β ≠ ω := by
    have hadj : Γ.Adj (q (n - 1)) (q n) := by
      have h := q.adj (n - 1) (by omega)
      rwa [show n - 1 + 1 = n by omega] at h
    obtain ⟨u, hu, hune⟩ := hne (q n) (q (n - 1)) hadj.symm
    exact ⟨⟨u, hu⟩, fun h => hune ((congrArg Subtype.val h).trans hω)⟩
  let η : {w : V // Γ.Adj (q n) w} := ⟨ω', hzω'⟩
  have hηne : η ≠ ω := fun h => hω'ne' h.symm
  have hRωcard : Nat.card Rω = Nat.card {w : V // Γ.Adj (q n) w} - 1 := by
    have hreg' : CFSG.BenderSuzuki.IsRegularOn Rω
        {α : {w : V // Γ.Adj (q n) w} | α ≠ ω} :=
      fun α β hα hβ => hRωreg α β hα hβ
    exact CFSG.BenderSuzuki.IsRegularOn.natCard_compl_point (G := X)
      (Ω := {w : V // Γ.Adj (q n) w}) (R := Rω) (α := ω) hreg' hRωst ⟨η, hηne⟩
  have hcompl : Nat.card {α : {w : V // Γ.Adj (q n) w} // α ≠ ω} =
      Nat.card {w : V // Γ.Adj (q n) w} - 1 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun α : {w : V // Γ.Adj (q n) w} => α = ω),
      Fintype.card_subtype_eq, Nat.card_eq_fintype_card]
  let f : Q → {α : {w : V // Γ.Adj (q n) w} // α ≠ ω} := fun q =>
    ⟨q.1 • η, by
      intro h
      have hqω : q.1 • ω = ω :=
        MulAction.mem_stabilizer_iff.mp (hQleω q.2)
      have h1 : η = ω := by
        calc η = q.1⁻¹ • (q.1 • η) := (inv_smul_smul q.1 η).symm
          _ = q.1⁻¹ • ω := by rw [h]
          _ = ω := by
              conv_lhs => rw [← hqω]
              exact inv_smul_smul q.1 ω
      exact hηne h1⟩
  have hfsurj : Function.Surjective f := by
    intro β
    obtain ⟨q, hqQ, hqβ⟩ := hQtrans η β.1 hηne β.2
    exact ⟨⟨q, hqQ⟩, Subtype.ext hqβ⟩
  have hQcard : Nat.card Rω ≤ Nat.card Q := by
    have h := Nat.card_le_card_of_surjective f hfsurj
    rw [hcompl] at h
    rw [hRωcard]
    exact h
  exact Subgroup.eq_of_le_of_card_ge hQleRω hQcard

private theorem rootFacts_of_rankOneData [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}]
    {N : Subgroup X} (hN : N.Normal) (hNs : IsSimpleGroup ↥N)
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hL : RankOneLocal X {w : V // Γ.Adj z w} N)
    (hR : RankOneRoot X {w : V // Γ.Adj z w} N)
    (h3 : 3 ≤ Nat.card {w : V // Γ.Adj z w}) : RootFacts H Γ n z := by
  classical
  have hfin : Finite {w : V // Γ.Adj z w} := Nat.finite_of_card_ne_zero (by omega)
  let Ω := {w : V // Γ.Adj z w}
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hker : π.ker = F.subgroupOf Gz := compatibleQuotient_ker (H := H) (Γ := Γ) π hact
  have hSmap : ∀ (w y : V) (hw : Γ.Adj z w) (hy : Γ.Adj z y),
      ((socTorus H Γ z w y).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : Ω) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : Ω) :=
    fun w y hw hy => compatibleQuotient_socTorus (H := H) (Γ := Γ) π hπ hact (hK z) hL hw hy
  refine ⟨?_, ?_⟩
  · intro q hq hqz ω' hzω' hω'ne Q hQ hQ2 hQnorm
    let ω : Ω := ⟨q (n - 1), by
      rw [← hqz]
      have h := q.adj (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at h
      exact h.symm⟩
    have hω : ω.1 = q (n - 1) := rfl
    obtain ⟨Rω, hRωst, hRωn, hRω2, hRωreg⟩ := hL.root ω
    have hmap : ((pathRootGroup H Γ q).subgroupOf Gz).map π = Rω :=
      pathRootGroup_map_eq_root hn hM hW hne hval hK hq hqz π hπ hact hL hR hfin
        ω hω Rω hRωst hRωn hRω2 hRωreg
    have hQGz : Q ≤ Gz := hQ.trans inf_le_left
    have hQω : Q ≤ MulAction.stabilizer H ω.1 := by
      rw [hω]
      exact hQ.trans inf_le_right
    have hQnorm' : ∀ t ∈ socTorus H Γ z ω.1 ω', ∀ x ∈ Q,
        t * x * t⁻¹ ∈ Q ⊔ F := by
      intro t ht x hx
      exact hQnorm t (by rwa [hω] at ht) x hx
    have hQXleω : (Q.subgroupOf Gz).map π ≤ MulAction.stabilizer X ω := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨q0, hq0, rfl⟩
      apply Subtype.ext
      rw [hact q0 ω]
      exact MulAction.mem_stabilizer_iff.mp (hQω (Subgroup.mem_subgroupOf.mp hq0))
    have hQs2 : IsPGroup 2 (Q.subgroupOf Gz) := by
      rw [← Subgroup.comap_subtype]
      exact hQ2.comap_subtype
    have hQX2 : IsPGroup 2 ((Q.subgroupOf Gz).map π) := IsPGroup.map hQs2 π
    have hQXnorm : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓
        MulAction.stabilizer X (⟨ω', hzω'⟩ : Ω),
        ∀ x ∈ (Q.subgroupOf Gz).map π, t * x * t⁻¹ ∈ (Q.subgroupOf Gz).map π :=
      conj_mem_map_subgroupOf_of_socTorus (H := H) (Γ := Γ) π hker hSmap (hK z) ω.2 hzω' hQGz
        hQnorm'
    have hω'ne' : ω ≠ ⟨ω', hzω'⟩ := fun h => hω'ne (congrArg Subtype.val h).symm
    let QX : Subgroup X := (Q.subgroupOf Gz).map π
    have hQXleRω : QX ≤ Rω :=
      hR.le_root ω ⟨ω', hzω'⟩ hω'ne' QX Rω hQXleω hRωst hRωn
        hQX2 hRω2 hRωreg hQXnorm
    have hUGz : pathRootGroup H Γ q ≤ Gz := by
      intro x hx
      change x ∈ MulAction.stabilizer H z
      rw [MulAction.mem_stabilizer_iff, ← hqz]
      exact smul_path_eq_self_of_mem_pathRootGroup hn hx n le_rfl
    have hle : QX ≤ ((pathRootGroup H Γ q).subgroupOf Gz).map π := by
      rw [hmap]
      exact hQXleRω
    exact le_sup_of_map_le (H := H) (Γ := Γ) π hker hUGz hQGz hle
  · intro q q' hq hq' hqz hq'z hne'
    let ω : Ω := ⟨q (n - 1), by
      rw [← hqz]
      have h := q.adj (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at h
      exact h.symm⟩
    let ω' : Ω := ⟨q' (n - 1), by
      rw [← hq'z]
      have h := q'.adj (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at h
      exact h.symm⟩
    have hω : ω.1 = q (n - 1) := rfl
    have hω' : ω'.1 = q' (n - 1) := rfl
    obtain ⟨Rω, hRωst, hRωn, hRω2, hRωreg⟩ := hL.root ω
    obtain ⟨Rω', hRω'st, hRω'n, hRω'2, hRω'reg⟩ := hL.root ω'
    have hmap : ((pathRootGroup H Γ q).subgroupOf Gz).map π = Rω :=
      pathRootGroup_map_eq_root hn hM hW hne hval hK hq hqz π hπ hact hL hR hfin
        ω hω Rω hRωst hRωn hRω2 hRωreg
    have hmap' : ((pathRootGroup H Γ q').subgroupOf Gz).map π = Rω' :=
      pathRootGroup_map_eq_root hn hM hW hne hval hK hq' hq'z π hπ hact hL hR hfin
        ω' hω' Rω' hRω'st hRω'n hRω'2 hRω'reg
    have hneω : ω ≠ ω' := fun h => hne' (congrArg Subtype.val h)
    have h3pt : ∃ α : Ω, α ≠ ω ∧ α ≠ ω' := by
      have hcard : 3 ≤ Cardinal.mk Ω := by
        rw [← Nat.cast_card (α := Ω)]
        exact_mod_cast h3
      exact Cardinal.exists_ne_ne_of_three_le hcard ω ω'
    have hRωtrans : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ r ∈ Rω, (r : X) • α = β := by
      intro α β hα hβ
      obtain ⟨r, hr, -⟩ := hRωreg α β hα hβ
      exact ⟨r, r.2, hr⟩
    have hRω'trans : ∀ α β : Ω, α ≠ ω' → β ≠ ω' → ∃ r ∈ Rω', (r : X) • α = β := by
      intro α β hα hβ
      obtain ⟨r, hr, -⟩ := hRω'reg α β hα hβ
      exact ⟨r, r.2, hr⟩
    have hRωnormT : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
        ∀ x ∈ Rω, t * x * t⁻¹ ∈ Rω := by
      intro t ht x hx
      exact (Subgroup.normal_subgroupOf_iff hRωst).mp hRωn x t hx ht.1.2
    have hRω'normT : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
        ∀ x ∈ Rω', t * x * t⁻¹ ∈ Rω' := by
      intro t ht x hx
      exact (Subgroup.normal_subgroupOf_iff hRω'st).mp hRω'n x t hx ht.2
    have hNsimp : N ≤ Rω ⊔ Rω' :=
      RankOneLocal.le_sup_root hN hNs hL hR hneω h3pt hRωst hRω'st hRω2 hRω'2
        hRωtrans hRω'trans hRωnormT hRω'normT
    have hUGz : pathRootGroup H Γ q ≤ Gz := by
      intro x hx
      change x ∈ MulAction.stabilizer H z
      rw [MulAction.mem_stabilizer_iff, ← hqz]
      exact smul_path_eq_self_of_mem_pathRootGroup hn hx n le_rfl
    have hU'Gz : pathRootGroup H Γ q' ≤ Gz := by
      intro x hx
      change x ∈ MulAction.stabilizer H z
      rw [MulAction.mem_stabilizer_iff, ← hq'z]
      exact smul_path_eq_self_of_mem_pathRootGroup hn hx n le_rfl
    have hUUGz : pathRootGroup H Γ q ⊔ pathRootGroup H Γ q' ≤ Gz := sup_le hUGz hU'Gz
    have hsocleMap : ((socleAt H Γ z).subgroupOf Gz).map π = N :=
      compatibleQuotient_socleAt (H := H) (Γ := Γ) π hπ hact (hK z) hL
    have hmapSU : ((pathRootGroup H Γ q ⊔ pathRootGroup H Γ q').subgroupOf Gz).map π =
        Rω ⊔ Rω' := by
      rw [Subgroup.subgroupOf_sup hUGz hU'Gz, Subgroup.map_sup, hmap, hmap']
    have hle : ((socleAt H Γ z).subgroupOf Gz).map π ≤
        ((pathRootGroup H Γ q ⊔ pathRootGroup H Γ q').subgroupOf Gz).map π := by
      rw [hsocleMap, hmapSU]
      exact hNsimp
    have hsocle : socleAt H Γ z ≤
        (pathRootGroup H Γ q ⊔ pathRootGroup H Γ q') ⊔ F :=
      le_sup_of_map_le (H := H) (Γ := Γ) π hker hUUGz
        (socleAt_le_stabilizer (H := H) (Γ := Γ) (hK z)) hle
    exact hsocle

private theorem rankOneData_l2 [Finite H] {z : V} {m : ℕ} (hm : 2 ≤ m)
    (h : IsLocalL2 H Γ z m) :
    ∃ N : Subgroup ↥(localGroup H Γ z), N.Normal ∧ IsSimpleGroup ↥N ∧
      RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N ∧
      RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N := by
  classical
  obtain ⟨hcard, h2, N, hN, ⟨e⟩⟩ := h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have hΩ : Fintype.card {w : V // Γ.Adj z w} = 2 ^ m + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hL : RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    rankOneLocal_psl2 h2 m hm N hN e hΩ
  have hZ : RankOneZassenhaus ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    rankOneZassenhaus_psl2 h2 m hm N hN e hΩ
  have hR : RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    RankOneLocal.rankOneRoot_of_zassenhaus hL hZ
  have hNs : IsSimpleGroup ↥N := by
    haveI : IsSimpleGroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
      have hKcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
      have hq4 : 4 ≤ Nat.card (GaloisField 2 m) := by
        rw [hKcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
    exact MulEquiv.isSimpleGroup e
  exact ⟨N, hN, hNs, hL, hR⟩

private theorem rankOneData_sz [Finite H] {z : V} {a : ℕ}
    (ha : 1 ≤ a) (h : IsLocalSz H Γ z a) :
    ∃ N : Subgroup ↥(localGroup H Γ z), N.Normal ∧ IsSimpleGroup ↥N ∧
      RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N ∧
      RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N ∧
      RankOneNonabelian ↥(localGroup H Γ z) {w : V // Γ.Adj z w} := by
  classical
  obtain ⟨hcard, h2, N, hN, ⟨e⟩⟩ := h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have hΩ : Fintype.card {w : V // Γ.Adj z w} = 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hL : RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    rankOneLocal_sz h2 a ha N hN e hΩ
  have hZ : RankOneZassenhaus ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    rankOneZassenhaus_sz h2 a ha N hN e hΩ
  have hR : RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    RankOneLocal.rankOneRoot_of_zassenhaus hL hZ
  have hNa : RankOneNonabelian ↥(localGroup H Γ z) {w : V // Γ.Adj z w} :=
    rankOneNonabelian_sz h2 a ha N hN e hΩ
  have hNs : IsSimpleGroup ↥N := by
    have hSuz : IsSimpleGroup (Sz a) := by
      have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
        GaloisField.card 2 (2 * a + 1) (by omega)
      haveI : IsSimpleGroup (suzukiGroup a (GaloisField 2 (2 * a + 1))) :=
        (suzuki_simple ha hK).2.2
      exact MulEquiv.isSimpleGroup (szToSuzukiGroup a)
    exact MulEquiv.isSimpleGroup e
  exact ⟨N, hN, hNs, hL, hR, hNa⟩

private theorem rankOneData_u3 [Finite H] {z : V} {k : ℕ} (hk : 2 ≤ k) (F : Type)
    [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2) (h : IsLocalU3 H Γ z k F) :
    ∃ N : Subgroup ↥(localGroup H Γ z), N.Normal ∧ IsSimpleGroup ↥N ∧
      RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N ∧
      RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N ∧
      RankOneNonabelian ↥(localGroup H Γ z) {w : V // Γ.Adj z w} := by
  classical
  obtain ⟨hcard, h2, N, hN, ⟨e⟩⟩ := h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have hΩ : Fintype.card {w : V // Γ.Adj z w} = 2 ^ (3 * k) + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hL : RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    rankOneLocal_psu3 h2 k hk F hF N hN e hΩ
  have hR : RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N :=
    rankOneRoot_psu3 h2 k hk F hF N hN e hΩ
  have hNa : RankOneNonabelian ↥(localGroup H Γ z) {w : V // Γ.Adj z w} :=
    rankOneNonabelian_psu3 h2 k hk F hF N hN e hΩ
  have hNs : IsSimpleGroup ↥N := by
    have hne32 : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
      rintro hh
      have h2k : 2 ^ k = 2 := (Prod.mk.inj hh).2
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    haveI : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) :=
      isSimpleGroup_statedProj_statedSU F 2 k (by rw [hF]) 3 le_rfl hne32
    exact MulEquiv.isSimpleGroup e
  exact ⟨N, hN, hNs, hL, hR, hNa⟩

private theorem rootFacts_of_localGroup [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {z : V}
    [Finite {w : V // Γ.Adj z w}] {N : Subgroup ↥(localGroup H Γ z)} (hN : N.Normal)
    (hNs : IsSimpleGroup ↥N)
    (hL : RankOneLocal ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N)
    (hR : RankOneRoot ↥(localGroup H Γ z) {w : V // Γ.Adj z w} N)
    (h3 : 3 ≤ Nat.card {w : V // Γ.Adj z w}) : RootFacts H Γ n z :=
  rootFacts_of_rankOneData hn hM hW hne hval hK hN hNs
    (localPermHom (H := H) Γ z).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    (fun _ _ => rfl) hL hR h3

theorem rootFacts_of_isLocalL2 [Finite H] {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n)
    (hW : WeissFree H Γ n) (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {z : V} {m : ℕ}
    (hm : 2 ≤ m) (h : IsLocalL2 H Γ z m) : RootFacts H Γ n z := by
  obtain ⟨N, hN, hNs, hL, hR⟩ := rankOneData_l2 hm h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [h.1]; exact Nat.succ_ne_zero _)
  refine rootFacts_of_localGroup hn hM hW hne hval hK hN hNs hL hR ?_
  rw [h.1]
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem rootFacts_of_isLocalSz [Finite H] {n : ℕ}
    (hn : 3 ≤ n) (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {z : V} {a : ℕ}
    (ha : 1 ≤ a) (h : IsLocalSz H Γ z a) : RootFacts H Γ n z := by
  obtain ⟨N, hN, hNs, hL, hR, -⟩ := rankOneData_sz ha h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [h.1]; exact Nat.succ_ne_zero _)
  refine rootFacts_of_localGroup hn hM hW hne hval hK hN hNs hL hR ?_
  rw [h.1]
  have h4 : 2 ≤ 2 ^ (2 * (2 * a + 1)) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem rootFacts_of_isLocalU3 [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {z : V} {k : ℕ}
    (hk : 2 ≤ k) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (h : IsLocalU3 H Γ z k F) : RootFacts H Γ n z := by
  obtain ⟨N, hN, hNs, hL, hR, -⟩ := rankOneData_u3 hk F hF h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [h.1]; exact Nat.succ_ne_zero _)
  refine rootFacts_of_localGroup hn hM hW hne hval hK hN hNs hL hR ?_
  rw [h.1]
  have h4 : 2 ≤ 2 ^ (3 * k) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem exists_not_comm_of_localGroup [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    {q : GPath Γ n} (hq : q.NoBack) [Finite {w : V // Γ.Adj (q n) w}]
    {N : Subgroup ↥(localGroup H Γ (q n))}
    (hL : RankOneLocal ↥(localGroup H Γ (q n)) {w : V // Γ.Adj (q n) w} N)
    (hR : RankOneRoot ↥(localGroup H Γ (q n)) {w : V // Γ.Adj (q n) w} N)
    (hNa : RankOneNonabelian ↥(localGroup H Γ (q n)) {w : V // Γ.Adj (q n) w}) :
    ∃ x ∈ pathRootGroup H Γ q, ∃ y ∈ pathRootGroup H Γ q, x * y ≠ y * x := by
  classical
  let π : ↥(MulAction.stabilizer H (q n)) →* ↥(localGroup H Γ (q n)) :=
    (localPermHom (H := H) Γ (q n)).rangeRestrict
  have hadj : Γ.Adj (q (n - 1)) (q n) := by
    have h := q.adj (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega] at h
  let ω : {w : V // Γ.Adj (q n) w} := ⟨q (n - 1), hadj.symm⟩
  obtain ⟨Rω, hRωst, hRωn, hRω2, hRωreg⟩ := hL.root ω
  have hmap : ((pathRootGroup H Γ q).subgroupOf (MulAction.stabilizer H (q n))).map π = Rω :=
    pathRootGroup_map_eq_root hn hM hW hne hval hK hq rfl π
      (MonoidHom.rangeRestrict_surjective _) (fun _ _ => rfl) hL hR inferInstance
      ω rfl Rω hRωst hRωn hRω2 hRωreg
  obtain ⟨c, hcR, d, hdR, hcd⟩ := hNa.not_comm ω Rω hRωst hRωn hRω2 hRωreg
  rw [← hmap] at hcR hdR
  rcases Subgroup.mem_map.mp hcR with ⟨x, hx, rfl⟩
  rcases Subgroup.mem_map.mp hdR with ⟨y, hy, rfl⟩
  refine ⟨(x : H), Subgroup.mem_subgroupOf.mp hx, (y : H), Subgroup.mem_subgroupOf.mp hy, ?_⟩
  intro hxy
  apply hcd
  have h2 := congrArg π (Subtype.ext hxy : x * y = y * x)
  rwa [map_mul, map_mul] at h2

theorem exists_not_comm_pathRootGroup_of_isLocalSz [Finite H]
    {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {a : ℕ} (ha : 1 ≤ a)
    {q : GPath Γ n} (hq : q.NoBack) (h : IsLocalSz H Γ (q n) a) :
    ∃ x ∈ pathRootGroup H Γ q, ∃ y ∈ pathRootGroup H Γ q, x * y ≠ y * x := by
  obtain ⟨N, -, -, hL, hR, hNa⟩ := rankOneData_sz (z := q n) ha h
  haveI : Finite {w : V // Γ.Adj (q n) w} :=
    Nat.finite_of_card_ne_zero (by rw [h.1]; exact Nat.succ_ne_zero _)
  exact exists_not_comm_of_localGroup hn hM hW hne hval hK hq hL hR hNa

theorem exists_not_comm_pathRootGroup_of_isLocalU3 [Finite H]
    {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {k : ℕ} (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    {q : GPath Γ n} (hq : q.NoBack) (h : IsLocalU3 H Γ (q n) k F) :
    ∃ x ∈ pathRootGroup H Γ q, ∃ y ∈ pathRootGroup H Γ q, x * y ≠ y * x := by
  obtain ⟨N, -, -, hL, hR, hNa⟩ := rankOneData_u3 (z := q n) hk F hF h
  haveI : Finite {w : V // Γ.Adj (q n) w} :=
    Nat.finite_of_card_ne_zero (by rw [h.1]; exact Nat.succ_ne_zero _)
  exact exists_not_comm_of_localGroup hn hM hW hne hval hK hq hL hR hNa

end CFSG.Quasithin.Stroth.WeissDelta
end
