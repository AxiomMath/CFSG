module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalFacts
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocal2

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem subgroupOf_map_subtype {G : Type*} [Group G] {K : Subgroup G}
    (P : Subgroup K) : (P.map K.subtype).subgroupOf K = P := by
  rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

private theorem subgroupOf_closure {G : Type*} [Group G] {K : Subgroup G} {S : Set G}
    (hS : S ⊆ K) :
    (Subgroup.closure S).subgroupOf K = Subgroup.closure {x : K | (x : G) ∈ S} := by
  have hSK : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr hS
  have hmap : (Subgroup.closure {x : K | (x : G) ∈ S}).map K.subtype =
      Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x, hSK (Subgroup.subset_closure hx)⟩, hx, rfl⟩
  rw [← Subgroup.comap_subtype, ← hmap,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

theorem compatibleQuotient_ker {z : V} {X : Type} [Group X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}]
    (π : ↥(MulAction.stabilizer H z) →* X)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V)) :
    π.ker = (fixingSubgroup H (Γ.neighborSet z)).subgroupOf
      (MulAction.stabilizer H z) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff]
    intro w hw
    have hxfix : π x • (⟨w, hw⟩ : {w : V // Γ.Adj z w}) = ⟨w, hw⟩ := by
      rw [hx]
      simp
    have hco := hact x ⟨w, hw⟩
    rw [hxfix] at hco
    exact hco.symm
  · intro hx
    rw [MonoidHom.mem_ker]
    apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := {w : V // Γ.Adj z w})
    intro w
    apply Subtype.ext
    have hxw : (x : H) • (w : V) = (w : V) :=
      (mem_fixingSubgroup_iff H).mp (Subgroup.mem_subgroupOf.mp hx) w w.2
    calc
      ((π x • w : {w : V // Γ.Adj z w}) : V) = (x : H) • (w : V) := hact x w
      _ = (w : V) := hxw
      _ = (((1 : X) • w : {w : V // Γ.Adj z w}) : V) := by simp

theorem compatibleQuotient_perfectResidual [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N) :
    (CFSG.perfectResidual ↥(MulAction.stabilizer H z)).map π = N := by
  have hmap : (CFSG.perfectResidual ↥(MulAction.stabilizer H z)).map π =
      CFSG.perfectResidual X := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
        ↥(MulAction.stabilizer H z)).map π =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual X
    exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq π hπ
  rw [hmap, h.perfectResidual_eq]

theorem compatibleQuotient_relIndex {z : V} {X : Type} [Group X]
    (π : ↥(MulAction.stabilizer H z) →* X)
    (hker : π.ker = (fixingSubgroup H (Γ.neighborSet z)).subgroupOf
      (MulAction.stabilizer H z))
    {K : Subgroup H} (hK : K ≤ MulAction.stabilizer H z) :
    (fixingSubgroup H (Γ.neighborSet z)).relIndex K =
      Nat.card ((K.subgroupOf (MulAction.stabilizer H z)).map π) := by
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  rw [← Subgroup.relIndex_subgroupOf (H := F) hK, ← hker]
  exact Subgroup.relIndex_ker (K.subgroupOf Gz) π

theorem compatibleQuotient_socleAt [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}]
    {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N) :
    ((socleAt H Γ z).subgroupOf (MulAction.stabilizer H z)).map π = N := by
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hFGz : F ≤ Gz := hK
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := z) π hact
  have hfixmap : (F.subgroupOf Gz).map π = ⊥ := by
    rw [← hker]
    exact Subgroup.map_ker_self π
  have hperf : (CFSG.perfectResidual Gz).map π = N :=
    compatibleQuotient_perfectResidual (H := H) (Γ := Γ) (z := z) π hπ h
  have hSzsub : (socleAt H Γ z).subgroupOf Gz =
      CFSG.perfectResidual Gz ⊔ F.subgroupOf Gz := by
    unfold socleAt CFSG.inSubgroup
    rw [Subgroup.subgroupOf_sup (Subgroup.map_subtype_le _) hFGz, subgroupOf_map_subtype]
  rw [hSzsub, Subgroup.map_sup, hperf, hfixmap]
  simp

theorem compatibleQuotient_socTorus [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}]
    {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N)
    {w y : V} (hw : Γ.Adj z w) (hy : Γ.Adj z y) :
    ((socTorus H Γ z w y).subgroupOf (MulAction.stabilizer H z)).map π =
      N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
        MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}) := by
  let Gz := MulAction.stabilizer H z
  have hSzmap : ((socleAt H Γ z).subgroupOf Gz).map π = N :=
    compatibleQuotient_socleAt (H := H) (Γ := Γ) (z := z) π hπ hact hK h
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have ha' : (a : H) ∈ socTorus H Γ z w y := Subgroup.mem_subgroupOf.mp ha
    have haS : (a : H) ∈ socleAt H Γ z := ha'.1.1
    have haw : (a : H) ∈ MulAction.stabilizer H w := ha'.1.2
    have hay : (a : H) ∈ MulAction.stabilizer H y := ha'.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hmem : π a ∈ ((socleAt H Γ z).subgroupOf Gz).map π := by
        refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        exact haS
      rwa [hSzmap] at hmem
    · apply Subtype.ext
      rw [hact a ⟨w, hw⟩]
      exact MulAction.mem_stabilizer_iff.mp haw
    · apply Subtype.ext
      rw [hact a ⟨y, hy⟩]
      exact MulAction.mem_stabilizer_iff.mp hay
  · rintro x ⟨⟨hxN, hxw⟩, hxy⟩
    rw [← hSzmap] at hxN
    rcases Subgroup.mem_map.mp hxN with ⟨a, haS, rfl⟩
    have haS' : (a : H) ∈ socleAt H Γ z := Subgroup.mem_subgroupOf.mp haS
    have haw : (a : H) ∈ MulAction.stabilizer H w := by
      rw [MulAction.mem_stabilizer_iff]
      have h1 : (π a • (⟨w, hw⟩ : {w : V // Γ.Adj z w})) = ⟨w, hw⟩ := by
        rw [MulAction.mem_stabilizer_iff.mp hxw]
      have h2 := hact a ⟨w, hw⟩
      rw [h1] at h2
      exact h2.symm
    have hay : (a : H) ∈ MulAction.stabilizer H y := by
      rw [MulAction.mem_stabilizer_iff]
      have h1 : (π a • (⟨y, hy⟩ : {w : V // Γ.Adj z w})) = ⟨y, hy⟩ := by
        rw [MulAction.mem_stabilizer_iff.mp hxy]
      have h2 := hact a ⟨y, hy⟩
      rw [h1] at h2
      exact h2.symm
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨haS', haw⟩, hay⟩

theorem localFacts_of_rankOneLocal [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h2 : ∀ w, Γ.Adj z w → ∃ w', Γ.Adj z w' ∧ w' ≠ w)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N) : LocalFacts H Γ z := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hFGz : F ≤ Gz := hK
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := z) π hact
  have hfixmap : (F.subgroupOf Gz).map π = ⊥ := by
    rw [← hker]
    exact Subgroup.map_ker_self π
  have hrel : ∀ K : Subgroup H, K ≤ Gz →
      F.relIndex K = Nat.card ((K.subgroupOf Gz).map π) :=
    fun K hK => compatibleQuotient_relIndex (H := H) (Γ := Γ) (z := z) π hker hK
  have hSsocle : socleAt H Γ z ≤ Gz :=
    socleAt_le_stabilizer (H := H) (Γ := Γ) (z := z) hK
  have hSmap : ∀ w y : {w : V // Γ.Adj z w},
      ((socTorus H Γ z (w : V) (y : V)).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X w ⊓ MulAction.stabilizer X y :=
    fun w y => compatibleQuotient_socTorus (H := H) (Γ := Γ) (z := z) π hπ hact hK h
      w.2 y.2
  refine ⟨hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw K hK hodd
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    have hKGz : K ≤ Gz := hK.trans inf_le_left
    let Kst : Subgroup Gz := K.subgroupOf Gz
    let KX : Subgroup X := Kst.map π
    have hKXw : KX ≤ MulAction.stabilizer X wΩ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [hact k wΩ]
      exact (hK (Subgroup.mem_subgroupOf.mp hk)).2
    have hKXodd : Odd (Nat.card KX) := by
      rw [← hrel K hKGz]
      exact hodd
    obtain ⟨w', hw'adj, hw'ne⟩ := h2 w hw
    have hpoint : ∃ ω₀ : {w : V // Γ.Adj z w}, ω₀ ≠ wΩ :=
      ⟨⟨w', hw'adj⟩, by
        intro h
        exact hw'ne (congrArg Subtype.val h)⟩
    obtain ⟨ω', hω'ne, hω'fix⟩ := h.oddFix wΩ KX hKXw hKXodd hpoint
    refine ⟨(ω' : {w : V // Γ.Adj z w}).1, ω'.2, ?_, ?_⟩
    · intro hEq
      exact hω'ne (Subtype.ext hEq)
    · intro k hk
      have hkGz : k ∈ Gz := hKGz hk
      let kGz : Gz := ⟨k, hkGz⟩
      have hkKst : kGz ∈ Kst := by
        rw [Subgroup.mem_subgroupOf]
        exact hk
      have hfix := hω'fix (π kGz) (Subgroup.mem_map_of_mem π hkKst)
      have hco := hact kGz ω'
      rw [hfix] at hco
      exact hco.symm
  · intro w y hw hy hwy
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hKsoc : socTorus H Γ z w y ≤ Gz := by
      intro x hx
      exact hSsocle hx.1.1
    rw [hrel (socTorus H Γ z w y) hKsoc, hSmap wΩ yΩ]
    exact h.torus_odd wΩ yΩ hwΩ
  · intro w y u hw hy hwy hu hfix
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    let uΩ : {w : V // Γ.Adj z w} := ⟨u, hu⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hfixX : ∀ t ∈ N ⊓ MulAction.stabilizer X wΩ ⊓ MulAction.stabilizer X yΩ,
        t • uΩ = uΩ := by
      intro t ht
      change t ∈ N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ at ht
      rw [← hSmap wΩ yΩ] at ht
      rcases Subgroup.mem_map.mp ht with ⟨a, ha, rfl⟩
      have ha' : (a : H) ∈ socTorus H Γ z w y := Subgroup.mem_subgroupOf.mp ha
      have h1 := hfix a ha'
      have hco := hact a uΩ
      rw [h1] at hco
      exact Subtype.ext hco
    rcases h.torus_fix wΩ yΩ uΩ hwΩ hfixX with h' | h'
    · left
      exact congrArg Subtype.val h'
    · right
      exact congrArg Subtype.val h'
  · intro w y hw hy hwy S hS hSodd
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hSGz : S ⊆ Gz := fun s hs => (hS hs).1.1
    let Sst : Set Gz := {s : Gz | (s : H) ∈ S}
    have hSst_odd : ∀ s ∈ Sst, Odd (orderOf s) := by
      intro s hs
      simpa using hSodd (s : H) hs
    let SX : Set X := π '' Sst
    have hSX_sub : SX ⊆ ↑(MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ) := by
      rintro x ⟨s, hs, rfl⟩
      have hs' := hS hs
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        rw [hact s wΩ]
        exact hs'.1.2
      · apply Subtype.ext
        rw [hact s yΩ]
        exact hs'.2
    have hSX_odd : ∀ x ∈ SX, Odd (orderOf x) := by
      rintro x ⟨s, hs, rfl⟩
      exact (hSst_odd s hs).of_dvd_nat (orderOf_map_dvd π s)
    have hSsub : Subgroup.closure S ≤ Gz := (Subgroup.closure_le Gz).mpr hSGz
    rw [hrel (Subgroup.closure S) hSsub, subgroupOf_closure hSGz,
      MonoidHom.map_closure]
    exact h.odd_closure wΩ yΩ hwΩ SX hSX_sub hSX_odd
  · intro w y hw hy hwy A hA hAsup
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hAGz : A ≤ Gz := hA.trans (by
      intro x hx
      exact hSsocle hx.1.1)
    let Ast : Subgroup Gz := A.subgroupOf Gz
    let AX : Subgroup X := Ast.map π
    have hAXle : AX ≤ N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ := by
      rw [← hSmap wΩ yΩ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono Gz hA)
    have hAXge : N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ ≤ AX := by
      have hle := Subgroup.subgroupOf_mono Gz hAsup
      rw [Subgroup.subgroupOf_sup hAGz hFGz] at hle
      rw [← hSmap wΩ yΩ]
      calc
        ((socTorus H Γ z w y).subgroupOf Gz).map π ≤
            (Ast ⊔ F.subgroupOf Gz).map π := Subgroup.map_mono hle
        _ = AX ⊔ ⊥ := by rw [Subgroup.map_sup, hfixmap]
        _ = AX := by simp
    have hAXeq : AX = N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ := le_antisymm hAXle hAXge
    obtain ⟨gen, hgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top
      (N ⊓ MulAction.stabilizer X wΩ ⊓ MulAction.stabilizer X yΩ)).mp
      (h.torus_cyclic wΩ yΩ hwΩ)
    have hgenodd : Odd (orderOf gen) :=
      (h.torus_odd wΩ yΩ hwΩ).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ (hgen ▸ Subgroup.mem_zpowers gen))
    have hgenAX : gen ∈ AX := by
      rw [hAXeq, ← hgen]
      exact Subgroup.mem_zpowers gen
    rcases Subgroup.mem_map.mp hgenAX with ⟨a, ha, ha_eq⟩
    have haA : ((a : Gz) : H) ∈ A := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨k, hkodd, hkimg⟩ := exists_odd_pow_map_eq π a (by rwa [ha_eq])
    let b : H := (((a : Gz) : H)) ^ k
    have hbA : b ∈ A := by
      simpa [b] using A.pow_mem haA k
    have hbodd : Odd (orderOf b) := by
      have hcoe : b = ((a ^ k : Gz) : H) := by simp [b, Subgroup.coe_pow]
      rw [hcoe, Subgroup.orderOf_coe]
      exact hkodd
    refine ⟨b, hbA, hbodd, ?_⟩
    intro t ht
    have htGz : t ∈ Gz := hSsocle ht.1.1
    let tGz : Gz := ⟨t, htGz⟩
    have htT : π tGz ∈ N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ := by
      rw [← hSmap wΩ yΩ]
      refine Subgroup.mem_map.mpr ⟨tGz, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact ht
    have htpi : π tGz ∈ Subgroup.zpowers gen := by
      rwa [← hgen] at htT
    rw [Subgroup.zpowers_eq_closure, Subgroup.mem_closure_singleton] at htpi
    rcases htpi with ⟨j, hj⟩
    have hbGz : b ∈ Gz := by
      have : (((a ^ k : Gz) : H)) ∈ Gz := (a ^ k : Gz).2
      simpa [b, Subgroup.coe_pow] using this
    let bGz : Gz := ⟨b, hbGz⟩
    have hbGz_eq : bGz = a ^ k := Subtype.ext (by simp [bGz, b, Subgroup.coe_pow])
    have hbpi : π bGz = gen := by
      rw [hbGz_eq, hkimg, ha_eq]
    have hjt : π (bGz ^ j) = π tGz := by
      rw [map_zpow, hbpi, hj]
    have hfker : (bGz ^ j)⁻¹ * tGz ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjt]
      simp
    have hfF : (((bGz ^ j)⁻¹ * tGz : Gz) : H) ∈ F := by
      have hmem : (bGz ^ j)⁻¹ * tGz ∈ F.subgroupOf Gz := by
        rwa [← hker]
      exact Subgroup.mem_subgroupOf.mp hmem
    have ht_eq : t = (((bGz ^ j : Gz) : H)) * (((bGz ^ j)⁻¹ * tGz : Gz) : H) := by
      simp [mul_assoc, tGz]
    rw [ht_eq]
    refine Subgroup.mul_mem_sup ?_ hfF
    have hbGzj : ((bGz ^ j : Gz) : H) = b ^ j := by simp [bGz]
    rw [hbGzj]
    exact Subgroup.zpow_mem (K := Subgroup.closure {b}) (x := b)
      (Subgroup.subset_closure (Set.mem_singleton b)) j
  · intro w y hw hy hwy A B hA hB hAodd hBodd hsup
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hAGz : A ≤ Gz := hA.trans inf_le_left
    have hBGz : B ≤ Gz := hB.trans inf_le_left
    let Ast : Subgroup Gz := A.subgroupOf Gz
    let Bst : Subgroup Gz := B.subgroupOf Gz
    let AX : Subgroup X := Ast.map π
    let BX : Subgroup X := Bst.map π
    have hAXle : AX ≤ MulAction.stabilizer X wΩ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [hact a wΩ]
      exact (hA (Subgroup.mem_subgroupOf.mp ha)).2
    have hBXle : BX ≤ MulAction.stabilizer X wΩ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [hact b wΩ]
      exact (hB (Subgroup.mem_subgroupOf.mp hb)).2
    have hAXodd : Odd (Nat.card AX) := by
      rw [← hrel A hAGz]
      exact hAodd
    have hBXodd : Odd (Nat.card BX) := by
      rw [← hrel B hBGz]
      exact hBodd
    have hTleAX : N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ ≤ AX := by
      have hle := Subgroup.subgroupOf_mono Gz hsup
      rw [Subgroup.subgroupOf_sup hAGz hFGz] at hle
      rw [← hSmap wΩ yΩ]
      calc
        ((socTorus H Γ z w y).subgroupOf Gz).map π ≤
            (Ast ⊔ F.subgroupOf Gz).map π := Subgroup.map_mono hle
        _ = AX ⊔ ⊥ := by rw [Subgroup.map_sup, hfixmap]
        _ = AX := by simp
    obtain ⟨cX, hcX, hfixX⟩ :=
      h.oddConj (ω := wΩ) (α := yΩ) (A := AX) (B := BX)
        hwΩ hAXle hBXle hAXodd hBXodd hTleAX
    have hABGz : A ⊔ B ≤ Gz := sup_le hAGz hBGz
    have hmapAB : ((A ⊔ B).subgroupOf Gz).map π = AX ⊔ BX := by
      rw [Subgroup.subgroupOf_sup hAGz hBGz, Subgroup.map_sup]
    rw [← hmapAB] at hcX
    rcases Subgroup.mem_map.mp hcX with ⟨c, hc, hc_eq⟩
    refine ⟨(c : H), Subgroup.mem_subgroupOf.mp hc, ?_⟩
    intro b hb
    have hbGz : b ∈ Gz := hBGz hb
    let bGz : Gz := ⟨b, hbGz⟩
    have hbBst : bGz ∈ Bst := by
      rw [Subgroup.mem_subgroupOf]
      exact hb
    have hfix := hfixX (π bGz) (Subgroup.mem_map_of_mem π hbBst)
    have h1 : (cX * π bGz * cX⁻¹) • yΩ = yΩ := hfix
    have h2 : π (c * bGz * c⁻¹) • yΩ = yΩ := by
      rw [← hc_eq] at h1
      have hgroup : π (c * bGz * c⁻¹) = π c * π bGz * (π c)⁻¹ := by
        simp [map_mul]
      rwa [hgroup]
    have hco := hact (c * bGz * c⁻¹) yΩ
    rw [h2] at hco
    have hcbc : (((c * bGz * c⁻¹ : Gz) : H)) = (c : H) * b * (c : H)⁻¹ := by
      simp [bGz]
    rw [hcbc] at hco
    exact hco.symm

theorem zassenhausFacts_of_rankOneZassenhaus [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N) (hZ : RankOneZassenhaus X {w : V // Γ.Adj z w} N) :
    ZassenhausFacts H Γ z := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hFGz : F ≤ Gz := hK
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := z) π hact
  have hfixmap : (F.subgroupOf Gz).map π = ⊥ := by
    rw [← hker]
    exact Subgroup.map_ker_self π
  have hSzmap : ((socleAt H Γ z).subgroupOf Gz).map π = N :=
    compatibleQuotient_socleAt (H := H) (Γ := Γ) (z := z) π hπ hact hK h
  have hrel : ∀ K : Subgroup H, K ≤ Gz →
      F.relIndex K = Nat.card ((K.subgroupOf Gz).map π) :=
    fun K hK => compatibleQuotient_relIndex (H := H) (Γ := Γ) (z := z) π hker hK
  have hSsocle : socleAt H Γ z ≤ Gz :=
    socleAt_le_stabilizer (H := H) (Γ := Γ) (z := z) hK
  have hSmap : ∀ w y : {w : V // Γ.Adj z w},
      ((socTorus H Γ z (w : V) (y : V)).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X w ⊓ MulAction.stabilizer X y :=
    fun w y => compatibleQuotient_socTorus (H := H) (Γ := Γ) (z := z) π hπ hact hK h
      w.2 y.2
  have hNnormal : N.Normal := by
    rw [← h.perfectResidual_eq]
    infer_instance
  refine ⟨?_, ?_⟩
  · intro w y hw hy hwy M hM hMnorm
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hMGz : M ≤ Gz := hM.trans (le_trans inf_le_left inf_le_left)
    let Mst : Subgroup Gz := M.subgroupOf Gz
    let MX : Subgroup X := Mst.map π
    let T : Subgroup X := N ⊓ MulAction.stabilizer X wΩ ⊓ MulAction.stabilizer X yΩ
    have hMXle : MX ≤ MulAction.stabilizer X wΩ ⊓ MulAction.stabilizer X yΩ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨m, hm, rfl⟩
      have hm' : (m : H) ∈ M := Subgroup.mem_subgroupOf.mp hm
      exact ⟨by
        apply Subtype.ext
        rw [hact m wΩ]
        exact (hM hm').1.2, by
        apply Subtype.ext
        rw [hact m yΩ]
        exact (hM hm').2⟩
    have hmapMF : ((M ⊔ F).subgroupOf Gz).map π = MX := by
      rw [Subgroup.subgroupOf_sup hMGz hFGz, Subgroup.map_sup, hfixmap]
      rw [sup_bot_eq]
    have hTnormMX : ∀ t ∈ T, ∀ m ∈ MX, t * m * t⁻¹ ∈ MX := by
      intro t ht m hm
      change t ∈ N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ at ht
      rw [← hSmap wΩ yΩ] at ht
      rcases Subgroup.mem_map.mp ht with ⟨t0, ht0, rfl⟩
      rcases Subgroup.mem_map.mp hm with ⟨m0, hm0, rfl⟩
      have ht0' : (t0 : H) ∈ socTorus H Γ z w y := Subgroup.mem_subgroupOf.mp ht0
      have hm0' : (m0 : H) ∈ M := Subgroup.mem_subgroupOf.mp hm0
      have h := hMnorm t0 ht0' (m0 : H) hm0'
      have hmem : (t0 * m0 * t0⁻¹ : Gz) ∈ (M ⊔ F).subgroupOf Gz := by
        rw [Subgroup.mem_subgroupOf]
        simpa using h
      have hmap := Subgroup.mem_map_of_mem π hmem
      rw [hmapMF] at hmap
      simpa [map_mul] using hmap
    have hMXnormT : ∀ m ∈ MX, ∀ t ∈ T, m * t * m⁻¹ ∈ T := by
      intro m hm t ht
      rcases Subgroup.mem_map.mp hm with ⟨m0, hm0, rfl⟩
      have hmle := hMXle (Subgroup.mem_map_of_mem π hm0)
      refine ⟨⟨hNnormal.conj_mem t ht.1.1 (π m0), ?_⟩, ?_⟩
      · change (π m0 * t * (π m0)⁻¹) • wΩ = wΩ
        calc
          (π m0 * t * (π m0)⁻¹) • wΩ =
              π m0 • (t • ((π m0)⁻¹ • wΩ)) := by simp [mul_smul]
          _ = π m0 • (t • wΩ) := by
            rw [MulAction.mem_stabilizer_iff.mp
              (Subgroup.inv_mem _ hmle.1)]
          _ = π m0 • wΩ := by rw [MulAction.mem_stabilizer_iff.mp ht.1.2]
          _ = wΩ := MulAction.mem_stabilizer_iff.mp hmle.1
      · change (π m0 * t * (π m0)⁻¹) • yΩ = yΩ
        calc
          (π m0 * t * (π m0)⁻¹) • yΩ =
              π m0 • (t • ((π m0)⁻¹ • yΩ)) := by simp [mul_smul]
          _ = π m0 • (t • yΩ) := by
            rw [MulAction.mem_stabilizer_iff.mp
              (Subgroup.inv_mem _ hmle.2)]
          _ = π m0 • yΩ := by rw [MulAction.mem_stabilizer_iff.mp ht.2]
          _ = yΩ := MulAction.mem_stabilizer_iff.mp hmle.2
    by_cases htriv : MX ⊓ T = ⊥
    · left
      have hTleNorm : T ≤ Subgroup.normalizer (MX : Set X) := by
        intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro m
        constructor
        · intro hm
          exact hTnormMX t ht m hm
        · intro hm
          have hinv := T.inv_mem ht
          have h := hTnormMX t⁻¹ hinv (t * m * t⁻¹) hm
          simpa [mul_assoc] using h
      have hMXleNorm : MX ≤ Subgroup.normalizer (T : Set X) := by
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro t
        constructor
        · intro ht
          exact hMXnormT m hm t ht
        · intro ht
          have hinv := MX.inv_mem hm
          have h := hMXnormT m⁻¹ hinv (m * t * m⁻¹) ht
          simpa [mul_assoc] using h
      have hcomm_leMX : ⁅MX, T⁆ ≤ MX :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hTleNorm
      have hcomm_leT : ⁅MX, T⁆ ≤ T :=
        (Subgroup.le_normalizer_iff_commutator_le_right).mp hMXleNorm
      have hcomm_bot : ⁅MX, T⁆ ≤ ⊥ := by
        rw [← htriv]
        exact le_inf hcomm_leMX hcomm_leT
      have hcentral : ∀ m ∈ MX, ∀ t ∈ T, m * t = t * m := by
        intro m hm t ht
        have hmem : ⁅m, t⁆ ∈ ⁅MX, T⁆ := Subgroup.commutator_mem_commutator hm ht
        have h1 : ⁅m, t⁆ = 1 := by simpa using hcomm_bot hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hMXleN : MX ≤ N := by
        intro m hm
        exact hZ.centralizer_le wΩ yΩ hwΩ m (hMXle hm)
          (fun t ht => hcentral m hm t ht)
      have hMXbot : MX = ⊥ := by
        apply le_bot_iff.mp
        rw [← htriv]
        exact le_inf le_rfl
          (le_inf (le_inf hMXleN (fun m hm => (hMXle hm).1))
            (fun m hm => (hMXle hm).2))
      intro m hm
      have hmst : (⟨m, hMGz hm⟩ : Gz) ∈ Mst := by
        rw [Subgroup.mem_subgroupOf]
        exact hm
      have hmX : π ⟨m, hMGz hm⟩ ∈ MX := Subgroup.mem_map_of_mem π hmst
      rw [hMXbot] at hmX
      have hmker : (⟨m, hMGz hm⟩ : Gz) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa using hmX
      rw [hker] at hmker
      exact Subgroup.mem_subgroupOf.mp hmker
    · right
      obtain ⟨t0, ht0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp htriv
      have ht0MX : (t0 : X) ∈ MX := t0.2.1
      have ht0T : (t0 : X) ∈ T := t0.2.2
      have ht0ne' : (t0 : X) ≠ 1 := fun h => ht0ne (Subtype.ext h)
      intro u hu hfixu
      let uΩ : {w : V // Γ.Adj z w} := ⟨u, hu⟩
      have ht0fix : (t0 : X) • uΩ = uΩ := by
        rcases Subgroup.mem_map.mp ht0MX with ⟨m, hm, hm_eq⟩
        have hm' : (m : H) ∈ M := Subgroup.mem_subgroupOf.mp hm
        have h1 := hfixu (m : H) hm'
        rw [← hm_eq]
        apply Subtype.ext
        rw [hact m uΩ]
        exact h1
      rcases hZ.fix_two wΩ yΩ hwΩ (t0 : X) ht0T ht0ne' uΩ ht0fix with h' | h'
      · left
        exact congrArg Subtype.val h'
      · right
        exact congrArg Subtype.val h'
  · intro w y hw hy hwy g0 hg0 hcomm
    let wΩ : {w : V // Γ.Adj z w} := ⟨w, hw⟩
    let yΩ : {w : V // Γ.Adj z w} := ⟨y, hy⟩
    have hwΩ : wΩ ≠ yΩ := by
      intro h'
      exact hwy (congrArg Subtype.val h')
    have hg0Gz : g0 ∈ Gz := hg0.1.1
    let gZ : Gz := ⟨g0, hg0Gz⟩
    have hgXle : π gZ ∈ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ := by
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        rw [hact gZ wΩ]
        exact MulAction.mem_stabilizer_iff.mp hg0.1.2
      · apply Subtype.ext
        rw [hact gZ yΩ]
        exact MulAction.mem_stabilizer_iff.mp hg0.2
    have hcentral : ∀ t ∈ N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ, π gZ * t = t * π gZ := by
      intro t ht
      change t ∈ N ⊓ MulAction.stabilizer X wΩ ⊓
        MulAction.stabilizer X yΩ at ht
      rw [← hSmap wΩ yΩ] at ht
      rcases Subgroup.mem_map.mp ht with ⟨t0, ht0, rfl⟩
      have ht0' : (t0 : H) ∈ socTorus H Γ z w y := Subgroup.mem_subgroupOf.mp ht0
      have h := hcomm t0 ht0'
      have hmem : (gZ * t0 * gZ⁻¹ * t0⁻¹ : Gz) ∈ F.subgroupOf Gz := by
        rw [Subgroup.mem_subgroupOf]
        simpa [gZ] using h
      have hmap := Subgroup.mem_map_of_mem π hmem
      rw [hfixmap] at hmap
      have hEq : π gZ * π t0 * (π gZ)⁻¹ * (π t0)⁻¹ = 1 := by
        simpa [map_mul] using hmap
      calc
        π gZ * π t0 =
            (π gZ * π t0 * (π gZ)⁻¹ * (π t0)⁻¹) * (π t0 * π gZ) := by group
        _ = π t0 * π gZ := by rw [hEq, one_mul]
    have hgXN : π gZ ∈ N :=
      hZ.centralizer_le wΩ yΩ hwΩ (π gZ) hgXle hcentral
    have hle : π.ker ≤ (socleAt H Γ z).subgroupOf Gz := by
      rw [hker]
      exact Subgroup.subgroupOf_mono Gz le_sup_right
    have hgZsoc : gZ ∈ (socleAt H Γ z).subgroupOf Gz := by
      rw [← Subgroup.comap_map_eq_self (f := π) hle, hSzmap]
      exact hgXN
    exact Subgroup.mem_subgroupOf.mp hgZsoc

end CFSG.Quasithin.Stroth.WeissDelta

end
