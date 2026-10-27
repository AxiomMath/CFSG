module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalFactsTransport
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFacts

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

theorem transitiveFacts_of_rankOneTransitive [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N)
    (hT : RankOneTransitive X {w : V // Γ.Adj z w} N) : TransitiveFacts H Γ z := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hFGz : F ≤ Gz := hK
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := z) π hact
  have hSmap : ∀ (w y : V) (hw : Γ.Adj z w) (hy : Γ.Adj z y),
      ((socTorus H Γ z w y).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}) :=
    fun w y hw hy => compatibleQuotient_socTorus (H := H) (Γ := Γ) (z := z) π hπ
      hact hK h hw hy
  refine ⟨?_⟩
  intro ω ω' hω hω' hne P hP hP2 hPnot hPnorm α β hα hβ hαω hβω
  have hPGz : P ≤ Gz := hP.trans inf_le_left
  have hPsub2 : IsPGroup 2 (P.subgroupOf Gz) := by
    rw [← Subgroup.comap_subtype]
    exact hP2.comap_subtype
  let PX : Subgroup X := (P.subgroupOf Gz).map π
  have hPX2 : IsPGroup 2 PX := IsPGroup.map hPsub2 π
  have hPXstab : PX ≤ MulAction.stabilizer X (⟨ω, hω⟩ : {w : V // Γ.Adj z w}) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    apply Subtype.ext
    rw [hact p ⟨ω, hω⟩]
    exact MulAction.mem_stabilizer_iff.mp (hP hp).2
  have hPXnot : PX ≠ ⊥ := by
    intro hbot
    apply hPnot
    intro p hp
    have hpGz : p ∈ Gz := hPGz hp
    have hpX : π (⟨p, hpGz⟩ : Gz) ∈ PX :=
      Subgroup.mem_map_of_mem π (show (⟨p, hpGz⟩ : Gz) ∈ P.subgroupOf Gz from hp)
    rw [hbot] at hpX
    have hpker : (⟨p, hpGz⟩ : Gz) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simpa using hpX
    rw [hker] at hpker
    exact Subgroup.mem_subgroupOf.mp hpker
  have hPXnorm : ∀ t ∈ N ⊓ MulAction.stabilizer X (⟨ω, hω⟩ : {w : V // Γ.Adj z w}) ⊓
      MulAction.stabilizer X (⟨ω', hω'⟩ : {w : V // Γ.Adj z w}),
      ∀ x ∈ PX, t * x * t⁻¹ ∈ PX := by
    intro t ht x hx
    rw [← hSmap ω ω' hω hω'] at ht
    rcases Subgroup.mem_map.mp ht with ⟨t0, ht0, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have ht0' : (t0 : H) ∈ socTorus H Γ z ω ω' := Subgroup.mem_subgroupOf.mp ht0
    have hpP : (p : H) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hmemH : (t0 : H) * (p : H) * (t0 : H)⁻¹ ∈ P ⊔ F := hPnorm (t0 : H) ht0' (p : H) hpP
    have hmem : (t0 * p * t0⁻¹ : Gz) ∈ (P ⊔ F).subgroupOf Gz := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hmemH
    have hFmap : (F.subgroupOf Gz).map π = ⊥ := by
      rw [← hker]
      exact Subgroup.map_ker_self π
    have hPF : ((P ⊔ F).subgroupOf Gz).map π = PX := by
      rw [Subgroup.subgroupOf_sup hPGz hFGz, Subgroup.map_sup, hFmap, sup_bot_eq]
    have hmap := Subgroup.mem_map_of_mem π hmem
    rw [hPF] at hmap
    simpa [map_mul] using hmap
  have hne' : (⟨ω, hω⟩ : {w : V // Γ.Adj z w}) ≠ ⟨ω', hω'⟩ :=
    fun h => hne (congrArg Subtype.val h)
  obtain ⟨rX, hrX, hrXeq⟩ := hT.transitive ⟨ω, hω⟩ ⟨ω', hω'⟩ hne' PX
    hPXstab hPX2 hPXnot hPXnorm ⟨α, hα⟩ ⟨β, hβ⟩
    (fun h => hαω (congrArg Subtype.val h)) (fun h => hβω (congrArg Subtype.val h))
  rcases Subgroup.mem_map.mp hrX with ⟨r, hr, rfl⟩
  refine ⟨(r : H), Subgroup.mem_subgroupOf.mp hr, ?_⟩
  simpa [hact r ⟨α, hα⟩] using congrArg Subtype.val hrXeq

theorem unitaryFacts_of_rankOneUnitary [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N) {q : ℕ}
    (hU : RankOneUnitary X {w : V // Γ.Adj z w} N q) : UnitaryFacts H Γ z q := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hFGz : F ≤ Gz := hK
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := z) π hact
  have hSsocle : socleAt H Γ z ≤ Gz := socleAt_le_stabilizer hK
  have hSmap : ∀ (w y : V) (hw : Γ.Adj z w) (hy : Γ.Adj z y),
      ((socTorus H Γ z w y).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}) :=
    fun w y hw hy => compatibleQuotient_socTorus (H := H) (Γ := Γ) (z := z) π hπ
      hact hK h hw hy
  refine ⟨?_, ?_, ?_⟩
  · intro w y hw hy hwy t ht hpow u hu hfix
    have htGz : t ∈ Gz := hSsocle (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
    let tGz : Gz := ⟨t, htGz⟩
    have htX : π tGz ∈ N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
        MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}) := by
      rw [← hSmap w y hw hy]
      exact Subgroup.mem_map_of_mem π (show tGz ∈ (socTorus H Γ z w y).subgroupOf Gz from ht)
    have hwy' : (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ≠ ⟨y, hy⟩ :=
      fun h => hwy (congrArg Subtype.val h)
    have hpowX : (π tGz) ^ (q + 1) ≠ 1 := by
      intro h1
      apply hpow
      have hpowGz : t ^ (q + 1) ∈ Gz := Gz.pow_mem htGz _
      have hker_mem : (⟨t ^ (q + 1), hpowGz⟩ : Gz) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        have hEq : (⟨t ^ (q + 1), hpowGz⟩ : Gz) = tGz ^ (q + 1) := Subtype.ext rfl
        rw [hEq]
        simpa [map_pow] using h1
      rw [hker] at hker_mem
      exact Subgroup.mem_subgroupOf.mp hker_mem
    have hfixX : (π tGz) • (⟨u, hu⟩ : {w : V // Γ.Adj z w}) = ⟨u, hu⟩ := by
      apply Subtype.ext
      rw [hact tGz ⟨u, hu⟩]
      exact hfix
    rcases hU.fix_two ⟨w, hw⟩ ⟨y, hy⟩ hwy' (π tGz) htX hpowX ⟨u, hu⟩ hfixX with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h
  · intro w y hw hy hwy t ht
    have htGz : t ∈ Gz := hSsocle (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
    let tGz : Gz := ⟨t, htGz⟩
    have htX : π tGz ∈ N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
        MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}) := by
      rw [← hSmap w y hw hy]
      exact Subgroup.mem_map_of_mem π (show tGz ∈ (socTorus H Γ z w y).subgroupOf Gz from ht)
    have hwy' : (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ≠ ⟨y, hy⟩ :=
      fun h => hwy (congrArg Subtype.val h)
    have hX := hU.pow_card ⟨w, hw⟩ ⟨y, hy⟩ hwy' (π tGz) htX
    have hpowGz : t ^ (q ^ 2 - 1) ∈ Gz := Gz.pow_mem htGz _
    have hker_mem : (⟨t ^ (q ^ 2 - 1), hpowGz⟩ : Gz) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hEq : (⟨t ^ (q ^ 2 - 1), hpowGz⟩ : Gz) = tGz ^ (q ^ 2 - 1) :=
        Subtype.ext rfl
      rw [hEq]
      simpa [map_pow] using hX
    rw [hker] at hker_mem
    exact Subgroup.mem_subgroupOf.mp hker_mem
  · intro w y hw hy hwy
    have hwy' : (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ≠ ⟨y, hy⟩ :=
      fun h => hwy (congrArg Subtype.val h)
    obtain ⟨tX, htX, hpowX⟩ := hU.exists_pow ⟨w, hw⟩ ⟨y, hy⟩ hwy'
    rw [← hSmap w y hw hy] at htX
    rcases Subgroup.mem_map.mp htX with ⟨tGz, htT, rfl⟩
    refine ⟨(tGz : H), Subgroup.mem_subgroupOf.mp htT, ?_⟩
    intro hF
    apply hpowX
    have hpowGz : (tGz : H) ^ (q + 1) ∈ Gz := Gz.pow_mem tGz.2 _
    have hpow2Gz : ((tGz : H) ^ (q + 1)) ^ (q + 1) ∈ Gz :=
      Gz.pow_mem hpowGz (q + 1)
    have hmemSub : (⟨((tGz : H) ^ (q + 1)) ^ (q + 1), hpow2Gz⟩ : Gz) ∈
        F.subgroupOf Gz := by
      rw [Subgroup.mem_subgroupOf]
      exact hF
    rw [← hker] at hmemSub
    have h1 : π (⟨((tGz : H) ^ (q + 1)) ^ (q + 1), hpow2Gz⟩ : Gz) = 1 :=
      MonoidHom.mem_ker.mp hmemSub
    have hEq : (⟨((tGz : H) ^ (q + 1)) ^ (q + 1), hpow2Gz⟩ : Gz) =
        (tGz ^ (q + 1)) ^ (q + 1) := Subtype.ext rfl
    rw [hEq, map_pow] at h1
    simpa [map_pow] using h1

private theorem map_root_eq [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (hRoot : RankOneRoot X {w : V // Γ.Adj z w} N)
    (ω : {w : V // Γ.Adj z w}) (R : Subgroup H) (Rω : Subgroup X)
    (hRωstab : Rω ≤ MulAction.stabilizer X ω)
    (hRωnorm : (Rω.subgroupOf (MulAction.stabilizer X ω)).Normal)
    (hRω2 : IsPGroup 2 Rω)
    (hRωreg : ∀ α β : {w : V // Γ.Adj z w}, α ≠ ω → β ≠ ω →
      ∃! r : Rω, (r : X) • α = β)
    (hker : π.ker = (fixingSubgroup H (Γ.neighborSet z)).subgroupOf
      (MulAction.stabilizer H z))
    (hSmap : ∀ (w y : V) (hw : Γ.Adj z w) (hy : Γ.Adj z y),
      ((socTorus H Γ z w y).subgroupOf (MulAction.stabilizer H z)).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}))
    (hAt : IsRootAt H Γ z ω.1 R) :
    ((R.subgroupOf (MulAction.stabilizer H z)).map π) = Rω := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hFGz : F ≤ Gz := hK
  have hRleGz : R ≤ Gz := hAt.1.trans inf_le_left
  have hRstab : R ≤ MulAction.stabilizer H ω.1 := hAt.1.trans inf_le_right
  have hR2 : IsPGroup 2 R := hAt.2.1
  have hRtrans := hAt.2.2.1
  obtain ⟨ω', hzω', hω'ne, hnorm⟩ := hAt.2.2.2
  have hω'ne' : (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) ≠ ω :=
    fun h => hω'ne (congrArg Subtype.val h)
  have hω'ne'' : ω ≠ (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) :=
    fun h => hω'ne (congrArg Subtype.val h).symm
  let Q : Subgroup X := (R.subgroupOf Gz).map π
  have hQle : Q ≤ MulAction.stabilizer X ω := by
    intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨r, hr, rfl⟩
    apply Subtype.ext
    rw [hact r ω]
    exact MulAction.mem_stabilizer_iff.mp (hRstab (Subgroup.mem_subgroupOf.mp hr))
  have hRsub2 : IsPGroup 2 (R.subgroupOf Gz) := by
    intro x
    obtain ⟨n, hn⟩ := hR2 ⟨(x : H), x.2⟩
    refine ⟨n, Subtype.ext ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change ((x : H) ^ 2 ^ n) = 1
    have hcoe : (((⟨(x : H), x.2⟩ : R) : H) ^ 2 ^ n) = 1 := by
      simpa [Subgroup.coe_pow] using congrArg (fun y : R => (y : H)) hn
    exact hcoe
  have hQ2 : IsPGroup 2 Q := IsPGroup.map hRsub2 π
  have hQnorm : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓
      MulAction.stabilizer X (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}),
      ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    rw [← hSmap ω.1 ω' ω.2 hzω'] at ht
    rcases Subgroup.mem_map.mp ht with ⟨t0, ht0, rfl⟩
    rcases Subgroup.mem_map.mp hq with ⟨r, hr, rfl⟩
    have ht0' : (t0 : H) ∈ socTorus H Γ z ω.1 ω' := Subgroup.mem_subgroupOf.mp ht0
    have hmemH : (t0 : H) * (r : H) * (t0 : H)⁻¹ ∈ R ⊔ F :=
      hnorm (t0 : H) ht0' (r : H) (Subgroup.mem_subgroupOf.mp hr)
    have hmem : (t0 * r * t0⁻¹ : Gz) ∈ (R ⊔ F).subgroupOf Gz := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hmemH
    have hmap : π (t0 * r * t0⁻¹) ∈ ((R ⊔ F).subgroupOf Gz).map π :=
      Subgroup.mem_map_of_mem π hmem
    have hFmap : (F.subgroupOf Gz).map π = ⊥ := by
      rw [← hker]
      exact Subgroup.map_ker_self π
    have hRF : ((R ⊔ F).subgroupOf Gz).map π = Q := by
      rw [Subgroup.subgroupOf_sup hRleGz hFGz, Subgroup.map_sup, hFmap, sup_bot_eq]
    rw [hRF] at hmap
    simpa [map_mul] using hmap
  have hQleRoot : Q ≤ Rω :=
    hRoot.le_root ω ⟨ω', hzω'⟩ hω'ne'' Q Rω hQle hRωstab hRωnorm hQ2 hRω2 hRωreg hQnorm
  refine le_antisymm hQleRoot ?_
  intro r hr
  have hQtrans : ∀ α β : {w : V // Γ.Adj z w}, α ≠ ω → β ≠ ω →
      ∃ q ∈ Q, q • α = β := by
    intro α β hα hβ
    obtain ⟨r0, hr0, hr0eq⟩ := hRtrans α.1 β.1 α.2 β.2
      (fun h => hα (Subtype.ext h)) (fun h => hβ (Subtype.ext h))
    refine ⟨π (⟨r0, hRleGz hr0⟩ : Gz), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem π (show (⟨r0, hRleGz hr0⟩ : Gz) ∈ R.subgroupOf Gz from hr0)
    · apply Subtype.ext
      rw [hact ⟨r0, hRleGz hr0⟩ α]
      exact hr0eq
  have hβne : r • (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) ≠ ω := by
    intro hEq
    have hfix : r⁻¹ ∈ MulAction.stabilizer X ω :=
      (MulAction.stabilizer X ω).inv_mem (hRωstab hr)
    have hfixω : r⁻¹ • ω = ω := MulAction.mem_stabilizer_iff.mp hfix
    have hω'eq : (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) = ω := by
      calc (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) = r⁻¹ • (r • ⟨ω', hzω'⟩) :=
            (inv_smul_smul r _).symm
        _ = r⁻¹ • ω := by rw [hEq]
        _ = ω := hfixω
    exact hω'ne (congrArg Subtype.val hω'eq)
  obtain ⟨q, hqQ, hqeq⟩ := hQtrans ⟨ω', hzω'⟩ (r • ⟨ω', hzω'⟩) hω'ne' hβne
  have hqR : q ∈ Rω := hQleRoot hqQ
  let qR : Rω := ⟨q, hqR⟩
  let rR : Rω := ⟨r, hr⟩
  have hfix : ((qR⁻¹ * rR : Rω) : X) • (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) =
      (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) := by
    calc ((qR⁻¹ * rR : Rω) : X) • (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) =
        q⁻¹ • (r • (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w})) := by
          simp [qR, rR, mul_smul]
      _ = q⁻¹ • (q • (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w})) := by rw [hqeq]
      _ = (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) := by rw [inv_smul_smul]
  have h1act : (1 : Rω) • (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) =
      (⟨ω', hzω'⟩ : {w : V // Γ.Adj z w}) := by
    rw [Subgroup.smul_def]
    simp
  have huniq := (hRωreg ⟨ω', hzω'⟩ ⟨ω', hzω'⟩ hω'ne' hω'ne').unique hfix h1act
  have hrq : r = q := by
    have h2 : rR = qR := by
      calc rR = 1 * rR := (one_mul _).symm
        _ = (qR * qR⁻¹) * rR := by rw [mul_inv_cancel]
        _ = qR * (qR⁻¹ * rR) := by group
        _ = qR * 1 := by rw [huniq]
        _ = qR := mul_one _
    simpa [qR, rR] using congrArg (fun s : Rω => (s : X)) h2
  simpa [Q, hrq] using hqQ

theorem conj_mem_map_subgroupOf_of_socTorus [Finite H] {z : V} {X : Type} [Group X]
    [MulAction X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X)
    (hker : π.ker = (fixingSubgroup H (Γ.neighborSet z)).subgroupOf
      (MulAction.stabilizer H z))
    (hSmap : ∀ (w y : V) (hw : Γ.Adj z w) (hy : Γ.Adj z y),
      ((socTorus H Γ z w y).subgroupOf (MulAction.stabilizer H z)).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    {ω ω' : V} (hω : Γ.Adj z ω) (hω' : Γ.Adj z ω')
    {A : Subgroup H} (hA : A ≤ MulAction.stabilizer H z)
    (hnorm : ∀ t ∈ socTorus H Γ z ω ω', ∀ x ∈ A,
      t * x * t⁻¹ ∈ A ⊔ fixingSubgroup H (Γ.neighborSet z)) :
    ∀ t ∈ N ⊓ MulAction.stabilizer X (⟨ω, hω⟩ : {w : V // Γ.Adj z w}) ⊓
        MulAction.stabilizer X (⟨ω', hω'⟩ : {w : V // Γ.Adj z w}),
      ∀ x ∈ (A.subgroupOf (MulAction.stabilizer H z)).map π,
        t * x * t⁻¹ ∈ (A.subgroupOf (MulAction.stabilizer H z)).map π := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  intro t ht x hx
  rw [← hSmap ω ω' hω hω'] at ht
  rcases Subgroup.mem_map.mp ht with ⟨t0, ht0, rfl⟩
  rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
  have hmemH : (t0 : H) * (a : H) * (t0 : H)⁻¹ ∈ A ⊔ F :=
    hnorm (t0 : H) (Subgroup.mem_subgroupOf.mp ht0) (a : H) (Subgroup.mem_subgroupOf.mp ha)
  have hmem : (t0 * a * t0⁻¹ : Gz) ∈ (A ⊔ F).subgroupOf Gz := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hmemH
  have hFmap : (F.subgroupOf Gz).map π = ⊥ := by
    rw [← hker]
    exact Subgroup.map_ker_self π
  have hAF : ((A ⊔ F).subgroupOf Gz).map π = (A.subgroupOf Gz).map π := by
    rw [Subgroup.subgroupOf_sup hA hK, Subgroup.map_sup, hFmap, sup_bot_eq]
  have hmap := Subgroup.mem_map_of_mem π hmem
  rw [hAF] at hmap
  simpa [map_mul] using hmap

private theorem image_commute_of_commutator_le [Finite H] {z : V} {X : Type} [Group X]
    (π : ↥(MulAction.stabilizer H z) →* X)
    (hker : π.ker = (fixingSubgroup H (Γ.neighborSet z)).subgroupOf
      (MulAction.stabilizer H z))
    {R : Subgroup H} (Rω : Subgroup X)
    (hRπ : (R.subgroupOf (MulAction.stabilizer H z)).map π = Rω)
    {A : Subgroup H} (hcomm : ⁅R, A⁆ ≤ fixingSubgroup H (Γ.neighborSet z))
    {x : X} (hx : x ∈ (A.subgroupOf (MulAction.stabilizer H z)).map π)
    {r : X} (hr : r ∈ Rω) : x * r = r * x := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
  have hrR : r ∈ (R.subgroupOf Gz).map π := by
    rw [hRπ]
    exact hr
  rcases Subgroup.mem_map.mp hrR with ⟨r0, hr0, rfl⟩
  have haA : (a : H) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hrR0 : (r0 : H) ∈ R := Subgroup.mem_subgroupOf.mp hr0
  have hcommH : ⁅(r0 : H), (a : H)⁆ ∈ F :=
    hcomm (Subgroup.commutator_mem_commutator hrR0 haA)
  have hGz : ⁅(r0 : H), (a : H)⁆ ∈ Gz :=
    Subgroup.commutator_le_self Gz (Subgroup.commutator_mem_commutator r0.2 a.2)
  have hker_mem : (⟨⁅(r0 : H), (a : H)⁆, hGz⟩ : Gz) ∈ π.ker := by
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr hcommH
  have hpi : π (⟨⁅(r0 : H), (a : H)⁆, hGz⟩ : Gz) = 1 :=
    MonoidHom.mem_ker.mp hker_mem
  have hzero : ⁅π r0, π a⁆ = 1 := by
    have hEq : (⟨⁅(r0 : H), (a : H)⁆, hGz⟩ : Gz) = ⁅r0, a⁆ := Subtype.ext rfl
    rw [hEq] at hpi
    simpa [map_commutatorElement] using hpi
  exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm

theorem centerFacts_of_rankOneCenter [Finite H] {z : V} {X : Type} [Group X] [Finite X]
    [MulAction X {w : V // Γ.Adj z w}] [FaithfulSMul X {w : V // Γ.Adj z w}] {N : Subgroup X}
    (π : ↥(MulAction.stabilizer H z) →* X) (hπ : Function.Surjective π)
    (hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V))
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : RankOneLocal X {w : V // Γ.Adj z w} N) (hR : RankOneRoot X {w : V // Γ.Adj z w} N)
    {e : ℕ} (hC : RankOneCenter X {w : V // Γ.Adj z w} N e) : CenterFacts H Γ z e := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  have hker : π.ker = F.subgroupOf Gz :=
    compatibleQuotient_ker (H := H) (Γ := Γ) (z := z) π hact
  have hSsocle : socleAt H Γ z ≤ Gz := socleAt_le_stabilizer hK
  have hSmap : ∀ (w y : V) (hw : Γ.Adj z w) (hy : Γ.Adj z y),
      ((socTorus H Γ z w y).subgroupOf Gz).map π =
        N ⊓ MulAction.stabilizer X (⟨w, hw⟩ : {w : V // Γ.Adj z w}) ⊓
          MulAction.stabilizer X (⟨y, hy⟩ : {w : V // Γ.Adj z w}) :=
    fun w y hw hy => compatibleQuotient_socTorus (H := H) (Γ := Γ) (z := z) π hπ
      hact hK h hw hy
  have hroot : ∀ (ω : {w : V // Γ.Adj z w}) (R : Subgroup H), IsRootAt H Γ z ω.1 R →
      ∃ Rω : Subgroup X, Rω ≤ MulAction.stabilizer X ω ∧
        (Rω.subgroupOf (MulAction.stabilizer X ω)).Normal ∧ IsPGroup 2 Rω ∧
        (∀ α β : {w : V // Γ.Adj z w}, α ≠ ω → β ≠ ω →
          ∃! r : Rω, (r : X) • α = β) ∧
        ((R.subgroupOf Gz).map π) = Rω := by
    intro ω R hAt
    obtain ⟨Rω, hRωstab, hRωnorm, hRω2, hRωreg⟩ := h.root ω
    refine ⟨Rω, hRωstab, hRωnorm, hRω2, hRωreg, ?_⟩
    exact map_root_eq (H := H) (Γ := Γ) (z := z) π hact hK hR ω R Rω
      hRωstab hRωnorm hRω2 hRωreg hker hSmap hAt
  have image_le_stabilizer : ∀ (A : Subgroup H) (ω : {w : V // Γ.Adj z w}),
      A ≤ MulAction.stabilizer H ω.1 →
        (A.subgroupOf Gz).map π ≤ MulAction.stabilizer X ω := by
    intro A ω hA x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    apply Subtype.ext
    rw [hact a ω]
    exact MulAction.mem_stabilizer_iff.mp (hA (Subgroup.mem_subgroupOf.mp ha))
  have image_centralizes : ∀ (R : Subgroup H) (Rω : Subgroup X),
      ((R.subgroupOf Gz).map π) = Rω → ∀ (A : Subgroup H), A ≤ Gz → ⁅R, A⁆ ≤ F →
        ∀ x ∈ (A.subgroupOf Gz).map π, ∀ r ∈ Rω, x * r = r * x := by
    intro R Rω hRπ A _ hcomm x hx r hr
    exact image_commute_of_commutator_le (H := H) (Γ := Γ) (z := z) π hker Rω
      hRπ hcomm hx hr
  refine ⟨?_, ?_⟩
  · intro ω hω R Z Z' hAt hZle hZ'le hTZ hTZ' hcommZ hcommZ' hZ'ne
    obtain ⟨Rω, hRωstab, hRωnorm, hRω2, hRωreg, hRπ⟩ := hroot ⟨ω, hω⟩ R hAt
    let ωΩ : {w : V // Γ.Adj z w} := ⟨ω, hω⟩
    have hZleGz : Z ≤ Gz := hZle.trans inf_le_left
    have hZleStab : Z ≤ MulAction.stabilizer H ω := hZle.trans inf_le_right
    have hZ'leGz : Z' ≤ Gz := hZ'le.trans inf_le_left
    have hZ'leStab : Z' ≤ MulAction.stabilizer H ω := hZ'le.trans inf_le_right
    let ZX : Subgroup X := (Z.subgroupOf Gz).map π
    let Z'X : Subgroup X := (Z'.subgroupOf Gz).map π
    have hZXstab : ZX ≤ MulAction.stabilizer X ωΩ := image_le_stabilizer Z ωΩ hZleStab
    have hZ'Xstab : Z'X ≤ MulAction.stabilizer X ωΩ := image_le_stabilizer Z' ωΩ hZ'leStab
    have hZXcomm : ∀ x ∈ ZX, ∀ r ∈ Rω, x * r = r * x :=
      image_centralizes R Rω hRπ Z hZleGz hcommZ
    have hZ'Xcomm : ∀ x ∈ Z'X, ∀ r ∈ Rω, x * r = r * x :=
      image_centralizes R Rω hRπ Z' hZ'leGz hcommZ'
    have hZXleRoot : ZX ≤ Rω := by
      intro x hx
      exact hC.centralizer_le ωΩ Rω hRωstab hRωnorm hRω2 hRωreg x (hZXstab hx)
        (fun r hr => hZXcomm x hx r hr)
    have hZ'XleRoot : Z'X ≤ Rω := by
      intro x hx
      exact hC.centralizer_le ωΩ Rω hRωstab hRωnorm hRω2 hRωreg x (hZ'Xstab hx)
        (fun r hr => hZ'Xcomm x hx r hr)
    have hZ'Xne : Z'X ≠ ⊥ := by
      intro hbot
      apply hZ'ne
      intro z hz
      have hzGz : z ∈ Gz := hZ'leGz hz
      have hzX : π (⟨z, hzGz⟩ : Gz) ∈ Z'X :=
        Subgroup.mem_map_of_mem π (show (⟨z, hzGz⟩ : Gz) ∈ Z'.subgroupOf Gz from hz)
      rw [hbot] at hzX
      have hker_mem : (⟨z, hzGz⟩ : Gz) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa using hzX
      rw [hker] at hker_mem
      exact Subgroup.mem_subgroupOf.mp hker_mem
    obtain ⟨ω', hzω', hω'ne, hnormZ'⟩ := hTZ'
    let ω'Ω : {w : V // Γ.Adj z w} := ⟨ω', hzω'⟩
    have hneΩ : ωΩ ≠ ω'Ω := fun h => hω'ne (congrArg Subtype.val h).symm
    have hZ'Xnorm : ∀ t ∈ N ⊓ MulAction.stabilizer X ωΩ ⊓
        MulAction.stabilizer X ω'Ω,
        ∀ x ∈ Z'X, t * x * t⁻¹ ∈ Z'X :=
      conj_mem_map_subgroupOf_of_socTorus (H := H) (Γ := Γ) (z := z) π hker hSmap hK hω hzω'
        hZ'leGz hnormZ'
    have hcenterLe : ∀ y ∈ Rω, (∀ r ∈ Rω, r * y = y * r) → y ∈ Z'X :=
      hC.center_le ωΩ ω'Ω hneΩ Rω Z'X hRωstab hRωnorm hRω2 hRωreg hZ'XleRoot
        (fun r hr y hy => (hZ'Xcomm y hy r hr).symm) hZ'Xnorm hZ'Xne
    have hZXleZ'X : ZX ≤ Z'X := by
      intro x hx
      exact hcenterLe x (hZXleRoot hx) (fun r hr => (hZXcomm x hx r hr).symm)
    intro z hz
    have hzX : π (⟨z, hZleGz hz⟩ : Gz) ∈ Z'X :=
      hZXleZ'X (Subgroup.mem_map_of_mem π
        (show (⟨z, hZleGz hz⟩ : Gz) ∈ Z.subgroupOf Gz from hz))
    rcases Subgroup.mem_map.mp hzX with ⟨z', hz', hzeq⟩
    have hz'Z' : (z' : H) ∈ Z' := Subgroup.mem_subgroupOf.mp hz'
    have hz'Gz : (z' : H) ∈ Gz := hZ'leGz hz'Z'
    have hquotGz : z * (z' : H)⁻¹ ∈ Gz := Gz.mul_mem (hZleGz hz) (Gz.inv_mem hz'Gz)
    have hquotF : z * (z' : H)⁻¹ ∈ F := by
      have hker_mem : (⟨z * (z' : H)⁻¹, hquotGz⟩ : Gz) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        have hEq : (⟨z * (z' : H)⁻¹, hquotGz⟩ : Gz) =
            (⟨z, hZleGz hz⟩ : Gz) * z'⁻¹ := Subtype.ext rfl
        rw [hEq, map_mul, map_inv, hzeq]
        simp
      rw [hker] at hker_mem
      exact Subgroup.mem_subgroupOf.mp hker_mem
    have hdecomp : z = (z * (z' : H)⁻¹) * (z' : H) := by group
    rw [hdecomp]
    exact (Z' ⊔ F).mul_mem (Subgroup.mem_sup_right hquotF) (Subgroup.mem_sup_left hz'Z')
  · intro ω ω' hω hω' hne R Z hAt hZle hTZ hcomm hZne g hg hgodd hcommZ
    let ωΩ : {w : V // Γ.Adj z w} := ⟨ω, hω⟩
    let ω'Ω : {w : V // Γ.Adj z w} := ⟨ω', hω'⟩
    have hneΩ : ωΩ ≠ ω'Ω := fun h => hne (congrArg Subtype.val h)
    obtain ⟨Rω, hRωstab, hRωnorm, hRω2, hRωreg, hRπ⟩ := hroot ωΩ R hAt
    have hZleGz : Z ≤ Gz := hZle.trans inf_le_left
    have hZleStab : Z ≤ MulAction.stabilizer H ω := hZle.trans inf_le_right
    let ZX : Subgroup X := (Z.subgroupOf Gz).map π
    have hZXstab : ZX ≤ MulAction.stabilizer X ωΩ := image_le_stabilizer Z ωΩ hZleStab
    have hZXcomm : ∀ x ∈ ZX, ∀ r ∈ Rω, x * r = r * x :=
      image_centralizes R Rω hRπ Z hZleGz hcomm
    have hZXleRoot : ZX ≤ Rω := by
      intro x hx
      exact hC.centralizer_le ωΩ Rω hRωstab hRωnorm hRω2 hRωreg x (hZXstab hx)
        (fun r hr => hZXcomm x hx r hr)
    obtain ⟨ωz, hzωz, hωz_ne, hnormZ⟩ := hTZ
    let ωzΩ : {w : V // Γ.Adj z w} := ⟨ωz, hzωz⟩
    have hneΩz : ωΩ ≠ ωzΩ := fun h => hωz_ne (congrArg Subtype.val h).symm
    have hZXne : ZX ≠ ⊥ := by
      intro hbot
      apply hZne
      intro z hz
      have hzGz : z ∈ Gz := hZleGz hz
      have hzX : π (⟨z, hzGz⟩ : Gz) ∈ ZX :=
        Subgroup.mem_map_of_mem π (show (⟨z, hzGz⟩ : Gz) ∈ Z.subgroupOf Gz from hz)
      rw [hbot] at hzX
      have hker_mem : (⟨z, hzGz⟩ : Gz) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa using hzX
      rw [hker] at hker_mem
      exact Subgroup.mem_subgroupOf.mp hker_mem
    have hZXnorm : ∀ t ∈ N ⊓ MulAction.stabilizer X ωΩ ⊓
        MulAction.stabilizer X ωzΩ,
        ∀ x ∈ ZX, t * x * t⁻¹ ∈ ZX :=
      conj_mem_map_subgroupOf_of_socTorus (H := H) (Γ := Γ) (z := z) π hker hSmap hK hω hzωz
        hZleGz hnormZ
    have hcenterLe : ∀ y ∈ Rω, (∀ r ∈ Rω, r * y = y * r) → y ∈ ZX :=
      hC.center_le ωΩ ωzΩ hneΩz Rω ZX hRωstab hRωnorm hRω2 hRωreg hZXleRoot
        (fun r hr y hy => (hZXcomm y hy r hr).symm) hZXnorm hZXne
    have hgGz : g ∈ Gz := hg.1.1
    let gGz : Gz := ⟨g, hgGz⟩
    have hgω : g ∈ MulAction.stabilizer H ω := hg.1.2
    have hgω' : g ∈ MulAction.stabilizer H ω' := hg.2
    have hgXmem : π gGz ∈ MulAction.stabilizer X ωΩ ⊓ MulAction.stabilizer X ω'Ω := by
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        rw [hact gGz ωΩ]
        exact MulAction.mem_stabilizer_iff.mp hgω
      · apply Subtype.ext
        rw [hact gGz ω'Ω]
        exact MulAction.mem_stabilizer_iff.mp hgω'
    have hgXodd : Odd (orderOf (π gGz)) := by
      refine hgodd.of_dvd_nat ?_
      rw [show orderOf g = orderOf gGz from Subgroup.orderOf_coe gGz]
      exact orderOf_map_dvd π gGz
    have hgcentral : ∀ y ∈ Rω, (∀ r ∈ Rω, r * y = y * r) → π gGz * y = y * π gGz := by
      intro y hy hcent
      have hyZX : y ∈ ZX := hcenterLe y hy hcent
      rcases Subgroup.mem_map.mp hyZX with ⟨z, hz, rfl⟩
      have hzZ : (z : H) ∈ Z := Subgroup.mem_subgroupOf.mp hz
      have hcommH : ⁅g, (z : H)⁆ ∈ F :=
        hcommZ (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers g) hzZ)
      have hker_mem : ⁅gGz, z⁆ ∈ π.ker := by
        rw [hker]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have hcoe : ((⁅gGz, z⁆ : Gz) : H) = ⁅g, (z : H)⁆ := rfl
        rwa [hcoe]
      have hpi : π ⁅gGz, z⁆ = 1 := MonoidHom.mem_ker.mp hker_mem
      have hzero : ⁅π gGz, π z⁆ = 1 := by
        simpa [map_commutatorElement] using hpi
      exact commutatorElement_eq_one_iff_mul_comm.mp hzero
    have hpow : (π gGz) ^ e = 1 :=
      hC.centralizer_center ωΩ ω'Ω hneΩ Rω hRωstab hRωnorm hRω2 hRωreg
        (π gGz) hgXmem hgXodd hgcentral
    have hpowGz : g ^ e ∈ Gz := Gz.pow_mem hgGz e
    have hker_mem : (⟨g ^ e, hpowGz⟩ : Gz) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hEq : (⟨g ^ e, hpowGz⟩ : Gz) = gGz ^ e := Subtype.ext rfl
      rw [hEq]
      simpa [map_pow] using hpow
    rw [hker] at hker_mem
    exact Subgroup.mem_subgroupOf.mp hker_mem

end CFSG.Quasithin.Stroth.WeissDelta

end
