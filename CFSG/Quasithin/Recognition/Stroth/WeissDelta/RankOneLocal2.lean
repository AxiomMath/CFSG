module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocal

public section

open scoped Pointwise

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

namespace RankOneLocal

theorem oddConj {X Ω : Type*} [Group X] [MulAction X Ω] [Finite X]
    {N : Subgroup X} (h : RankOneLocal X Ω N) {ω α : Ω} (hωα : ω ≠ α)
    {A B : Subgroup X} (hA : A ≤ MulAction.stabilizer X ω)
    (hB : B ≤ MulAction.stabilizer X ω)
    (hAo : Odd (Nat.card A)) (hBo : Odd (Nat.card B))
    (hT : N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X α ≤ A) :
    ∃ c ∈ A ⊔ B, ∀ b ∈ B, (c * b * c⁻¹) • α = α := by
  classical
  obtain ⟨R, hRstab, hRnorm, hR2, hRreg⟩ := h.root ω
  let Gω : Subgroup X := MulAction.stabilizer X ω
  let H : Subgroup X := A ⊔ B
  have hAH : A ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHstab : H ≤ Gω := sup_le hA hB
  let Rω : Subgroup Gω := R.subgroupOf Gω
  have hRGα : Rω.IsComplement' (MulAction.stabilizer Gω α) := by
    refine Subgroup.isComplement'_stabilizer (H := Rω) α ?_ ?_
    · intro r hr
      obtain ⟨r₀, hr₀, huniq⟩ := hRreg α α hωα.symm hωα.symm
      have hr₀1 : r₀ = 1 := (huniq 1 (by simp)).symm
      have hrr : (⟨((r : Gω) : X), r.2⟩ : R) = r₀ := by
        apply huniq
        simpa [Subgroup.smul_def] using hr
      apply Subtype.ext
      apply Subtype.ext
      rw [congrArg Subtype.val hrr, hr₀1]
      rfl
    · intro g
      have hgα : ((g : Gω) : X) • α ≠ ω := by
        intro hgω
        have hgfix : ((g : Gω) : X) • ω = ω := g.2
        have h : ((g : Gω) : X)⁻¹ • (((g : Gω) : X) • α) =
            ((g : Gω) : X)⁻¹ • (((g : Gω) : X) • ω) := by
          rw [hgω, hgfix]
        rw [inv_smul_smul, inv_smul_smul] at h
        exact hωα h.symm
      obtain ⟨r₀, hr₀, -⟩ := hRreg (((g : Gω) : X) • α) α hgα hωα.symm
      refine ⟨⟨⟨(r₀ : X), hRstab r₀.2⟩, r₀.2⟩, ?_⟩
      change (r₀ : X) • (((g : Gω) : X) • α) = α
      exact hr₀
  let e : Gω ⧸ Rω ≃* MulAction.stabilizer Gω α := hRGα.symm.QuotientMulEquiv
  let φ : H →* MulAction.stabilizer Gω α :=
    e.toMonoidHom.comp ((QuotientGroup.mk' Rω).comp (Subgroup.inclusion hHstab))
  have hφker : φ.ker = R.subgroupOf H := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxq : ((Subgroup.inclusion hHstab x : Gω) : Gω ⧸ Rω) = 1 := by
        apply e.injective
        simpa [φ] using hx
      have hxR : (Subgroup.inclusion hHstab x : Gω) ∈ Rω :=
        (QuotientGroup.eq_one_iff _).mp hxq
      exact hxR
    · intro hx
      rw [MonoidHom.mem_ker]
      have hq : ((Subgroup.inclusion hHstab x : Gω) : Gω ⧸ Rω) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hx
      show φ x = 1
      simp [φ, hq]
  have hAHsub : A.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAH hBH]
    change (A ⊔ B).subgroupOf (A ⊔ B) = ⊤
    rw [Subgroup.subgroupOf_self]
  have hrange : φ.range = (A.subgroupOf H).map φ ⊔ (B.subgroupOf H).map φ := by
    rw [MonoidHom.range_eq_map, ← hAHsub, Subgroup.map_sup]
  let incX : MulAction.stabilizer Gω α →* X :=
    { toFun := fun s => ((s : Gω) : X)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hincXinj : Function.Injective incX := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let Ssub : Set (MulAction.stabilizer Gω α) := {s | Odd (orderOf s)}
  let SX : Set X := {x : X | ∃ s : MulAction.stabilizer Gω α, s ∈ Ssub ∧ incX s = x}
  have hSXsub : SX ⊆ ↑(Gω ⊓ MulAction.stabilizer X α) := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨(s : Gω).2, ?_⟩
    have hs' : (s : Gω) • α = α := s.2
    simpa [incX, Subgroup.smul_def] using hs'
  have hSXodd : ∀ x ∈ SX, Odd (orderOf x) := by
    rintro x ⟨s, hs, rfl⟩
    have hcoe : orderOf (incX s) = orderOf s :=
      orderOf_injective incX hincXinj s
    rwa [hcoe]
  let P : Subgroup X := φ.range.map incX
  have hphi_le : φ.range ≤ Subgroup.closure Ssub := by
    rw [hrange]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.subset_closure (by
        have hdiv : orderOf (φ a) ∣ orderOf a := orderOf_map_dvd φ a
        have hAord : orderOf a ∣ Nat.card A := by
          have h3 : orderOf ((a : H) : X) ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A ha
          simpa [Subgroup.orderOf_coe a] using h3
        exact hAo.of_dvd_nat (hdiv.trans hAord))
    · rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.subset_closure (by
        have hdiv : orderOf (φ b) ∣ orderOf b := orderOf_map_dvd φ b
        have hBord : orderOf b ∣ Nat.card B := by
          have h3 : orderOf ((b : H) : X) ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hb
          simpa [Subgroup.orderOf_coe b] using h3
        exact hBo.of_dvd_nat (hdiv.trans hBord))
  have hmap_le : (Subgroup.closure Ssub).map incX ≤ Subgroup.closure SX := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hPle : P ≤ Subgroup.closure SX := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, hs, rfl⟩
    exact hmap_le (Subgroup.mem_map_of_mem incX (hphi_le hs))
  have hclosureOdd : Odd (Nat.card (Subgroup.closure SX)) :=
    h.odd_closure ω α hωα SX hSXsub hSXodd
  have hPodd : Odd (Nat.card P) :=
    hclosureOdd.of_dvd_nat
      (Subgroup.card_dvd_of_le (H := P) (K := Subgroup.closure SX) hPle)
  have hrangeOdd : Odd (Nat.card φ.range) := by
    have hcard : Nat.card P = Nat.card φ.range :=
      Subgroup.card_map_of_injective (f := incX) hincXinj
    rwa [hcard] at hPodd
  have hquotOdd : Odd (Nat.card (H ⧸ R.subgroupOf H)) := by
    have hcard : Nat.card (H ⧸ R.subgroupOf H) = Nat.card φ.range := by
      rw [← hφker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rwa [hcard]
  have hNHnormal : (R.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    change ((g : X) * (n : X) * (g : X)⁻¹) ∈ R
    exact (Subgroup.normal_subgroupOf_iff hRstab).mp hRnorm (n : X) (g : X) hn (hHstab g.2)
  haveI : (R.subgroupOf H).Normal := hNHnormal
  have hNH2 : IsPGroup 2 (R.subgroupOf H) := by
    intro x
    obtain ⟨k, hk⟩ := hR2 ⟨(x : X), x.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (x : X) ^ 2 ^ k = 1
    simpa using congrArg (fun y : R => (y : X)) hk
  haveI : Group.IsNilpotent ↥(R.subgroupOf H) :=
    IsPGroup.isNilpotent (p := 2) hNH2
  haveI : Group.IsSolvable ↥(R.subgroupOf H) := inferInstance
  haveI : Group.IsSolvable (H ⧸ R.subgroupOf H) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hquotOdd
  have hHsolv : Group.IsSolvable H :=
    Group.isSolvable_of_subgroup_quotient (R.subgroupOf H)
  let π : Set Nat.Primes := {p | p.val ≠ 2}
  letI : MulDistribMulAction Unit H :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
  have hcopUnit : Nat.Coprime (Nat.card Unit) (Nat.card H) := by simp
  have hApi : IsPiSubgroup π A := by
    intro q hq
    exact hAo.ne_two_of_dvd_nat hq
  have hBpi : IsPiSubgroup π B := by
    intro q hq
    exact hBo.ne_two_of_dvd_nat hq
  have hApiH : IsPiSubgroup π (A.subgroupOf H) := by
    intro q hq
    apply hApi
    have hcard : Nat.card (A.subgroupOf H) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
    rwa [hcard] at hq
  have hBpiH : IsPiSubgroup π (B.subgroupOf H) := by
    intro q hq
    apply hBpi
    have hcard : Nat.card (B.subgroupOf H) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
    rwa [hcard] at hq
  have hAinvH : IsInvariant Unit H (A.subgroupOf H) :=
    ⟨fun _ _ => Iff.rfl⟩
  have hBinvH : IsInvariant Unit H (B.subgroupOf H) :=
    ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨C, hChall, -, hAC⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := H) (A := Unit) hHsolv hcopUnit π (A.subgroupOf H) hApiH hAinvH
  obtain ⟨C', hC'hall, -, hBC'⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := H) (A := Unit) hHsolv hcopUnit π (B.subgroupOf H) hBpiH hBinvH
  have hCodd : Odd (Nat.card C) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2dvd : 2 ∣ Nat.card C := even_iff_two_dvd.mp heven
    have hmem : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ π :=
      hChall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h2dvd
    exact hmem (by simp [π])
  let CX : Subgroup X := C.map H.subtype
  have hCXle : CX ≤ MulAction.stabilizer X ω := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, -, rfl⟩
    exact hHstab c.2
  have hCXodd : Odd (Nat.card CX) := by
    rw [Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective]
    exact hCodd
  have hCXleT : N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X α ≤ CX := by
    intro t ht
    have htA : t ∈ A := hT ht
    have htAH : (⟨t, hAH htA⟩ : H) ∈ A.subgroupOf H := htA
    exact Subgroup.mem_map_of_mem H.subtype (hAC htAH)
  obtain ⟨ω', hω'ne, hω'fix⟩ := h.oddFix (ω := ω) (K := CX) hCXle hCXodd ⟨α, hωα.symm⟩
  have hω'eq : ω' = α :=
    h.oddFix_unique (ω := ω) (ω' := α) hωα hCXleT ω' hω'ne hω'fix
  have hCXfixα : ∀ k ∈ CX, k • α = α := by
    intro k hk
    rw [← hω'eq]
    exact hω'fix k hk
  obtain ⟨g, hg⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable (G := H) hHsolv hChall hC'hall
  refine ⟨((g⁻¹ : H) : X), ?_, ?_⟩
  · simpa [H] using (g⁻¹ : H).2
  · intro b hb
    let bH : B.subgroupOf H := ⟨⟨b, hBH hb⟩, hb⟩
    have hbHmem : (bH : H) ∈ B.subgroupOf H := by simpa using bH.2
    have hbC' : (bH : H) ∈ C' := hBC' hbHmem
    rw [hg] at hbC'
    rcases Subgroup.mem_map.mp hbC' with ⟨c, hc, hceq⟩
    have hceq' : g * c * g⁻¹ = (bH : H) := by
      simpa [MulAut.conj_apply] using hceq
    have hcEq : c = g⁻¹ * bH * g := by
      calc
        c = g⁻¹ * (g * c * g⁻¹) * g := by group
        _ = g⁻¹ * bH * g := by rw [hceq']
    have hcC : c ∈ C := hc
    have hfix := hCXfixα ((c : H) : X) (Subgroup.mem_map_of_mem H.subtype hcC)
    have hcX : ((c : H) : X) =
        ((g⁻¹ : H) : X) * b * (((g⁻¹ : H) : X))⁻¹ := by
      rw [hcEq]
      change ((g⁻¹ : H) : X) * b * ((g : H) : X) =
        ((g⁻¹ : H) : X) * b * (((g⁻¹ : H) : X))⁻¹
      have hgX : ((g : H) : X) = (((g⁻¹ : H) : X))⁻¹ := by simp
      rw [hgX]
    rwa [hcX] at hfix

end RankOneLocal

end CFSG.Quasithin.Stroth.WeissDelta
