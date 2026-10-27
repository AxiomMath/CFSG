module

public import CFSG.Monster.Existence.ELevelDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

namespace RankStep

theorem finrank_range_le_of_map_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : V →ₗ[K] V) (U W : Submodule K V) (hNU : U.map N ≤ W) {m n : ℕ}
    (hW : Module.finrank K W ≤ m) (hU : Module.finrank K V ≤ Module.finrank K U + n) :
    Module.finrank K (LinearMap.range N) ≤ m + n := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  have h1 : Module.finrank K U + Module.finrank K C = Module.finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hC
  have hC' : Module.finrank K C ≤ n := by omega
  have hrange : LinearMap.range N = U.map N ⊔ C.map N := by
    rw [← Submodule.map_sup, hC.sup_eq_top, Submodule.map_top]
  calc Module.finrank K (LinearMap.range N)
      = Module.finrank K ↥(U.map N ⊔ C.map N) := by rw [hrange]
    _ ≤ Module.finrank K (U.map N) + Module.finrank K (C.map N) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ m + n := add_le_add ((Submodule.finrank_mono hNU).trans hW)
        ((Submodule.finrank_map_le N C).trans hC')

theorem finrank_span_pair_le (a b : L2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a, b}) ≤ 2 := by
  classical
  have h1 := finrank_span_finset_le_card (R := ZMod 2) ({a, b} : Finset L2)
  rw [Finset.coe_pair] at h1
  exact h1.trans Finset.card_le_two

theorem finrank_le_finrank_ker_prod_add_two (a b : L2 →ₗ[ZMod 2] ZMod 2) :
    Module.finrank (ZMod 2) L2 ≤ Module.finrank (ZMod 2) (LinearMap.ker (a.prod b)) + 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (a.prod b)
  have h2 : Module.finrank (ZMod 2) (LinearMap.range (a.prod b)) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (a.prod b))
    rwa [Module.finrank_prod, Module.finrank_self] at this
  omega

theorem sq_add_one_mem {κ : Module.End (ZMod 2) L2} {W U : Submodule (ZMod 2) L2}
    (hUx : ∀ x, κ x + x ∈ U) (hUW : ∀ u ∈ U, κ u + u ∈ W) (x : L2) : κ (κ x) + x ∈ W := by
  have h := hUW _ (hUx x)
  have e : κ (κ x + x) + (κ x + x) = κ (κ x) + x := by
    rw [map_add]
    calc κ (κ x) + κ x + (κ x + x) = κ (κ x) + (κ x + κ x) + x := by abel
      _ = κ (κ x) + x := by rw [ZModModule.add_self, add_zero]
  rwa [e] at h

theorem pow_four_apply {κ : Module.End (ZMod 2) L2} {W U : Submodule (ZMod 2) L2}
    (hW : ∀ w ∈ W, κ w = w) (hUx : ∀ x, κ x + x ∈ U) (hUW : ∀ u ∈ U, κ u + u ∈ W) (x : L2) :
    κ (κ (κ (κ x))) = x := by
  have hm : κ (κ x) + x ∈ W := sq_add_one_mem hUx hUW x
  have hfix : κ (κ (κ (κ x) + x)) = κ (κ x) + x := by rw [hW _ hm, hW _ hm]
  simp only [map_add] at hfix
  have h2 : κ (κ (κ (κ x))) + κ (κ x) = x + κ (κ x) := by rw [hfix, add_comm]
  exact add_right_cancel h2

theorem eq_one_of_rank (hrank : RankSpec) {ψ : GLV} (hψ : ψ ∈ OLvis)
    {W U : Submodule (ZMod 2) L2}
    (hW : ∀ w ∈ W, (ψ : Module.End (ZMod 2) L2) w = w)
    (hUx : ∀ x, (ψ : Module.End (ZMod 2) L2) x + x ∈ U)
    (hUW : ∀ u ∈ U, (ψ : Module.End (ZMod 2) L2) u + u ∈ W)
    (hW2 : Module.finrank (ZMod 2) W ≤ 2)
    (hU2 : Module.finrank (ZMod 2) L2 ≤ Module.finrank (ZMod 2) U + 2) : ψ = 1 := by
  by_contra hne
  have h4 : ψ * ψ * (ψ * ψ) = 1 := by
    refine Units.ext (LinearMap.ext fun x => ?_)
    simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply]
    exact pow_four_apply hW hUx hUW x
  by_cases hψψ : ψ * ψ = 1
  · have h5 := hrank ψ hψ hψψ hne
    have h6 := finrank_range_le_of_map_le ((ψ : Module.End (ZMod 2) L2) - 1) U W
      (by
        rintro _ ⟨u, hu, rfl⟩
        rw [LinearMap.sub_apply, Module.End.one_apply, ZModModule.sub_eq_add]
        exact hUW u hu) hW2 hU2
    omega
  · have h5 := hrank (ψ * ψ) (mul_mem hψ hψ) h4 hψψ
    have hle : LinearMap.range (((ψ * ψ : GLV) : Module.End (ZMod 2) L2) - 1) ≤ W := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.sub_apply, Units.val_mul, Module.End.mul_apply, Module.End.one_apply,
        ZModModule.sub_eq_add]
      exact sq_add_one_mem hUx hUW x
    have h6 := Submodule.finrank_mono hle
    omega

theorem bL_modTwoEnd_of_fixed {g : latticeO} {v : L2} (hv : modTwoEnd g v = v) (x : L2) :
    bL v (modTwoEnd g x) = bL v x := by
  have := bL_modTwoEnd g v x
  rwa [hv] at this

theorem modTwoUnit_eq_one_of_rank (hrank : RankSpec) {g : latticeO} {v₁ v₂ : L2}
    (h₁ : modTwoEnd g v₁ = v₁) (h₂ : modTwoEnd g v₂ = v₂)
    (hperp : ∀ x, bL v₁ x = 0 → bL v₂ x = 0 →
      modTwoEnd g x + x ∈ Submodule.span (ZMod 2) {v₁, v₂}) : modTwoUnit g = 1 := by
  have hmem : ∀ x : L2, x ∈ LinearMap.ker ((bL v₁).prod (bL v₂)) ↔
      bL v₁ x = 0 ∧ bL v₂ x = 0 := fun x => LinearMap.mem_ker.trans Prod.mk_eq_zero
  have hW : ∀ w ∈ Submodule.span (ZMod 2) {v₁, v₂}, modTwoEnd g w = w := fun w hw =>
    LinearMap.eqOn_span' (f := modTwoEnd g) (g := LinearMap.id) (by
      rintro x (rfl | rfl)
      · exact h₁
      · exact h₂) hw
  have hUx : ∀ x : L2, modTwoEnd g x + x ∈ LinearMap.ker ((bL v₁).prod (bL v₂)) := fun x =>
    (hmem _).2 ⟨by rw [map_add, bL_modTwoEnd_of_fixed h₁, ZModModule.add_self],
      by rw [map_add, bL_modTwoEnd_of_fixed h₂, ZModModule.add_self]⟩
  exact eq_one_of_rank hrank (modTwoUnit_mem_OLvis g) hW hUx
    (fun u hu => hperp u ((hmem u).1 hu).1 ((hmem u).1 hu).2)
    (finrank_span_pair_le _ _) (finrank_le_finrank_ker_prod_add_two _ _)

theorem conj_rhoGriess {h : MGriess} {p : Pvis} (hp : thetaEquiv p = (h : SpaceB ≃ₗ[ℚ] SpaceB))
    (q : Q) : h * rhoGriess q * h⁻¹ = rhoGriess (conjQ p q) := by
  refine Subtype.ext ?_
  have := CFSG.Monster.Visible.thetaEquiv_conj_rhoEquiv p q
  rw [hp] at this
  exact this

theorem conjQ_eq_of_comm {h : MGriess} {p : Pvis} (hp : thetaEquiv p = (h : SpaceB ≃ₗ[ℚ] SpaceB))
    {q : Q} (hc : rhoGriess q * h = h * rhoGriess q) : conjQ p q = q := by
  apply rhoGriess_injective
  rw [← conj_rhoGriess hp q, mul_inv_eq_iff_eq_mul]
  exact hc.symm

theorem commutator_rhoGriess {h : MGriess} {p : Pvis}
    (hp : thetaEquiv p = (h : SpaceB ≃ₗ[ℚ] SpaceB)) (q : Q) :
    h * rhoGriess q * h⁻¹ * (rhoGriess q)⁻¹ = rhoGriess (q⁻¹ * conjQ p q) := by
  rw [conj_rhoGriess hp q, rhoGriess_mul, rhoGriess_inv]

theorem eq_of_rhoGriess_mem_FE {s : Q} (hs : rhoGriess s ∈ FE) :
    s = 1 ∨ s = rStar ∨ s = rTwo ∨ s = rTwo * rStar := by
  rcases mem_FE.1 hs with h | h | h | h
  · exact .inl (rhoGriess_injective (h.trans rhoGriess_one.symm))
  · exact .inr (.inl (rhoGriess_injective (h.trans rhoGriess_rStar.symm)))
  · exact .inr (.inr (.inl (rhoGriess_injective (h.trans rhoGriess_rTwo.symm))))
  · refine .inr (.inr (.inr (rhoGriess_injective (h.trans ?_))))
    rw [rhoGriess_mul, rhoGriess_rStar, rhoGriess_rTwo]

theorem phi0_mem_span_of_rhoGriess_mem_FE {s : Q} (hs : rhoGriess s ∈ FE) :
    phi0 (coordOf s) ∈
      Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)} := by
  have h1 : phi0 (coordOf rStar) ∈
      Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have h2 : phi0 (coordOf rTwo) ∈
      Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rcases eq_of_rhoGriess_mem_FE hs with rfl | rfl | rfl | rfl
  · rw [CFSG.Monster.B.coordOf_one', map_zero]
    exact Submodule.zero_mem _
  · exact h1
  · exact h2
  · rw [phi0_coordOf_mul]
    exact Submodule.add_mem _ h2 h1

theorem kappa_add_mem_span {h : MGriess} {p : Pvis}
    (hp : thetaEquiv p = (h : SpaceB ≃ₗ[ℚ] SpaceB)) {q : Q}
    (hq : h * rhoGriess q * h⁻¹ * (rhoGriess q)⁻¹ ∈ FE) :
    modTwoEnd p.1.2 (phi0 (coordOf q)) + phi0 (coordOf q) ∈
      Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)} := by
  rw [commutator_rhoGriess hp q] at hq
  have h1 := phi0_mem_span_of_rhoGriess_mem_FE hq
  rwa [phi0_coordOf_mul, phi0_coordOf_inv, phi0_conjQ, add_comm] at h1

theorem mem_RQ_iff_bL {q : Q} : q ∈ RQ ↔ bL (phi0 (coordOf rStar)) (phi0 (coordOf q)) = 0 ∧
    bL (phi0 (coordOf rTwo)) (phi0 (coordOf q)) = 0 :=
  Subgroup.mem_inf.trans (and_congr (mem_centralizer_iff_bL _ _) (mem_centralizer_iff_bL _ _))

theorem exists_mem_RQ_phi0_eq {x : L2} (h1 : bL (phi0 (coordOf rStar)) x = 0)
    (h2 : bL (phi0 (coordOf rTwo)) x = 0) : ∃ q ∈ RQ, phi0 (coordOf q) = x := by
  obtain ⟨q, hq⟩ := phiQ_surjective (Multiplicative.ofAdd x)
  have hqx : phi0 (coordOf q) = x := by rw [← toAdd_phiQ, hq, toAdd_ofAdd]
  exact ⟨q, mem_RQ_iff_bL.2 ⟨by rw [hqx]; exact h1, by rw [hqx]; exact h2⟩, hqx⟩

theorem exists_rhoEquiv_eq_of_modTwoUnit_eq_one {p : Pvis} (h1 : modTwoUnit p.1.2 = 1) :
    ∃ r : Q, rhoEquiv r = thetaEquiv p := by
  have h2 : (QuotientGroup.mk p.1.2 : latticeO ⧸ Subgroup.zpowers negOneO) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ((mem_zpowers_negOneO_iff _).2 ((modTwoUnit_eq_one_iff _).1 h1))
  have h3 : piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ = 1 := by
    rw [piVis_thetaEquiv, h2, MulOpposite.op_one]
  exact (piVis_eq_one_iff _).1 h3

end RankStep

theorem RE_hCR (hrank : RankSpec) :
    ∀ h ∈ Subgroup.centralizer (FE : Set MGriess) ⊓ Subgroup.centralizer ({xGriess} : Set MGriess),
      (∀ r ∈ RE, h * r * h⁻¹ * r⁻¹ ∈ FE) → h ∈ RE := by
  intro h hh hR
  obtain ⟨hhF, hhx⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨p, hp⟩ := mem_Gvis.1 (mem_Gvis_of_mem_cent_xGriess hhx)
  have hcF := Subgroup.mem_centralizer_iff.1 hhF
  have hct : rhoGriess rStar * h = h * rhoGriess rStar := by
    rw [rhoGriess_rStar]
    exact hcF _ (mem_FE.2 (.inr (.inl rfl)))
  have hcu : rhoGriess rTwo * h = h * rhoGriess rTwo := by
    rw [rhoGriess_rTwo]
    exact hcF _ (mem_FE.2 (.inr (.inr (.inl rfl))))
  have hψ := RankStep.modTwoUnit_eq_one_of_rank hrank (g := p.1.2)
    (v₁ := phi0 (coordOf rStar)) (v₂ := phi0 (coordOf rTwo))
    (by rw [← phi0_conjQ, RankStep.conjQ_eq_of_comm hp hct])
    (by rw [← phi0_conjQ, RankStep.conjQ_eq_of_comm hp hcu])
    (fun x h1 h2 => by
      obtain ⟨q, hq, rfl⟩ := RankStep.exists_mem_RQ_phi0_eq h1 h2
      exact RankStep.kappa_add_mem_span hp (hR _ (rhoGriess_mem_RE hq)))
  obtain ⟨r, hr⟩ := RankStep.exists_rhoEquiv_eq_of_modTwoUnit_eq_one hψ
  have hhr : h = rhoGriess r := Subtype.ext (hr.trans hp).symm
  refine mem_RE_iff.2 ⟨r, mem_RQ_iff.2 ⟨?_, ?_⟩, hhr⟩
  · apply rhoGriess_injective
    rw [rhoGriess_mul, rhoGriess_mul, ← hhr]
    exact hct
  · apply rhoGriess_injective
    rw [rhoGriess_mul, rhoGriess_mul, ← hhr]
    exact hcu

end CFSG.Monster.Existence
