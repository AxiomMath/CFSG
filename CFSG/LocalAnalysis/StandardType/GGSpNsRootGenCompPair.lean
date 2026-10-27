module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.Assembly.Subnormal
import CFSG.ClassicalGroups.Orthogonal.Basic
import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.SpNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem isComponentOf_map_omegaToGsp {X : Set ↥(orthDerived Q)} {z : ↥(orthDerived Q)}
    (hzX : z ∈ X) (hz : ∀ v, (z : V ≃ₗ[F] V) v = v → v = 0) {L : Subgroup ↥(orthDerived Q)}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer X)) :
    CFSG.Assembly.IsComponentOf (L.map (omegaToGsp Q))
      (Subgroup.centralizer (omegaToGsp Q '' X)) := by
  classical
  let C : Subgroup (Gsp (polarBilin Q)) := Subgroup.centralizer (omegaToGsp Q '' X)
  have hCle : C ≤ (orthToGsp Q).range := by
    intro g hg
    refine mem_range_orthToGsp_of_commute (Q := Q) (z := omegaToGsp Q z) ?_ ?_ ?_
    · exact range_omegaToGsp_le Q ⟨z, rfl⟩
    · intro v hv
      rw [omegaToGsp_app] at hv
      exact hz v hv
    · exact (Subgroup.mem_centralizer_iff.mp hg (omegaToGsp Q z) ⟨z, hzX, rfl⟩).symm
  let N : Subgroup (Gsp (polarBilin Q)) := (omegaToGsp Q).range ⊓ C
  have hEq : (Subgroup.centralizer X).map (omegaToGsp Q) = N := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change (omegaToGsp Q y) ∈ Subgroup.centralizer (omegaToGsp Q '' X)
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨x, hx, rfl⟩ := hs
      calc (omegaToGsp Q x) * (omegaToGsp Q y)
          = omegaToGsp Q (x * y) := (map_mul _ x y).symm
        _ = omegaToGsp Q (y * x) := by rw [Subgroup.mem_centralizer_iff.mp hy x hx]
        _ = (omegaToGsp Q y) * (omegaToGsp Q x) := map_mul _ y x
    · rintro ⟨⟨y, rfl⟩, hgC⟩
      refine ⟨y, ?_, rfl⟩
      change y ∈ Subgroup.centralizer X
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hgC' : (omegaToGsp Q y) ∈ Subgroup.centralizer (omegaToGsp Q '' X) := hgC
      have h := Subgroup.mem_centralizer_iff.mp hgC' (omegaToGsp Q x) ⟨x, hx, rfl⟩
      have h' : omegaToGsp Q (x * y) = omegaToGsp Q (y * x) := by
        rw [map_mul, map_mul]
        exact h
      exact omegaToGsp_injective Q h'
  have hY : CFSG.Assembly.IsComponentOf (L.map (omegaToGsp Q)) N := by
    rw [← hEq]
    exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hL
      (omegaToGsp Q) (omegaToGsp_injective Q)
  have hN : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (show N ≤ C from inf_le_right)]
    intro h k hh hk
    obtain ⟨hhω, hhC⟩ := hh
    obtain ⟨y, rfl⟩ := hhω
    obtain ⟨o, rfl⟩ := hCle hk
    let yO : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
      ⟨(y : V ≃ₗ[F] V), orthDerived_le_orthogonalGroup y.2⟩
    let w : V ≃ₗ[F] V := (o : V ≃ₗ[F] V) * (y : V ≃ₗ[F] V) * (o : V ≃ₗ[F] V)⁻¹
    have hw : w ∈ orthDerived Q := by
      have hO : (o : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := o.2
      have hle : (TauCeti.QuadraticMap.orthogonalGroup Q).map
          (MulAut.conj (o : V ≃ₗ[F] V)).toMonoidHom ≤
          TauCeti.QuadraticMap.orthogonalGroup Q := by
        rintro _ ⟨a, ha, rfl⟩
        exact mul_mem (mul_mem hO ha) (inv_mem hO)
      have h1 : (MulAut.conj (o : V ≃ₗ[F] V)).toMonoidHom (y : V ≃ₗ[F] V) ∈
          (orthDerived Q).map (MulAut.conj (o : V ≃ₗ[F] V)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ y.2
      rw [Subgroup.map_commutator] at h1
      exact Subgroup.commutator_mono hle hle h1
    change orthToGsp Q o * omegaToGsp Q y * (orthToGsp Q o)⁻¹ ∈
      (omegaToGsp Q).range ⊓ C
    refine ⟨⟨⟨w, hw⟩, ?_⟩, ?_⟩
    · have hyO : orthToGsp Q yO = omegaToGsp Q y := by
        rw [show yO = Subgroup.inclusion (orthDerived_le_orthogonalGroup (Q := Q)) y from
          Subtype.ext rfl]
        rfl
      have hωw : omegaToGsp Q ⟨w, hw⟩ = orthToGsp Q (o * yO * o⁻¹) := by
        change orthToGsp Q
          (Subgroup.inclusion (orthDerived_le_orthogonalGroup (Q := Q)) ⟨w, hw⟩) =
            orthToGsp Q (o * yO * o⁻¹)
        rw [show (Subgroup.inclusion (orthDerived_le_orthogonalGroup (Q := Q)) ⟨w, hw⟩ :
            ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = o * yO * o⁻¹ from Subtype.ext rfl]
      calc omegaToGsp Q ⟨w, hw⟩
          = orthToGsp Q (o * yO * o⁻¹) := hωw
        _ = orthToGsp Q o * orthToGsp Q yO * (orthToGsp Q o)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = orthToGsp Q o * omegaToGsp Q y * (orthToGsp Q o)⁻¹ := by rw [hyO]
    · exact C.mul_mem (C.mul_mem hk hhC) (C.inv_mem hk)
  exact CFSG.ComponentClassification.OddClassSelector.isComponentOf_of_normal_le hY
    inf_le_right hN

private theorem eq_zero_of_fixed_of_planePowers {p k : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e E)
    (htop : (⨆ j, U j) = ⊤) {d : ↥(orthDerived Q)}
    {f : Fin k → Multiplicative (ZMod p)}
    (hact : ∀ c, ∀ x ∈ U c, (d : V ≃ₗ[F] V) x =
      ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x)
    (hne : ∀ c, f c ≠ 1) : ∀ v, (d : V ≃ₗ[F] V) v = v → v = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hplane : ∀ c, ∀ x ∈ U c,
      ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x = x → x = 0 := by
    intro c x hx hfix
    have hne' : Multiplicative.toAdd (f c) ≠ 0 := by
      intro h0
      exact hne c (by rw [← ofAdd_toAdd (f c), h0, ofAdd_zero])
    have hpos : 0 < (Multiplicative.toAdd (f c)).val :=
      Nat.pos_of_ne_zero fun h => hne' ((ZMod.val_eq_zero (Multiplicative.toAdd (f c))).mp h)
    have hlt : (Multiplicative.toAdd (f c)).val < p := ZMod.val_lt _
    have hnd : ¬ p ∣ (Multiplicative.toAdd (f c)).val := by
      intro hd
      exact hpos.ne' (Nat.eq_zero_of_dvd_of_lt hd hlt)
    have hep : orderOf (e c : V ≃ₗ[F] V) = p := by
      rw [Subgroup.orderOf_coe]
      exact hF.orderOf_eq c
    have hpowmem : ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) ∈
        Subgroup.zpowers (e c : V ≃ₗ[F] V) :=
      Subgroup.npow_mem_zpowers _ _
    have hpowne : ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) ≠ 1 := by
      intro h1
      have hdvd : orderOf (e c : V ≃ₗ[F] V) ∣ (Multiplicative.toAdd (f c)).val :=
        orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [hep] at hdvd
      exact hnd hdvd
    have hfs : fixedSpace ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) =
        fixedSpace (e c : V ≃ₗ[F] V) :=
      fixedSpace_eq_of_mem_zpowers hp hep hpowmem hpowne
    have hxfs : x ∈ fixedSpace ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) :=
      mem_fixedSpace.mpr hfix
    rw [hfs, hF.fixedSpace_eq_polarPerp c] at hxfs
    have hbot : U c ⊓ polarPerp Q (U c) = ⊥ := (isCompl_polarPerp (hF.nondeg c)).inf_eq_bot
    have hxbot : x ∈ (⊥ : Submodule F V) := by
      rw [← hbot]
      exact ⟨hx, hxfs⟩
    simpa using hxbot
  intro v hv
  have hvperp : ∀ c, v ∈ polarPerp Q (U c) := by
    intro c
    rw [mem_polarPerp_iff]
    intro w hw
    have hpowU : ∀ n : ℕ, ∀ x ∈ U c, ((e c : V ≃ₗ[F] V) ^ n) x ∈ U c := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
          intro x hx
          rw [pow_succ, LinearEquiv.mul_apply]
          exact ih _ (hF.maps_to c x hx)
    have hdU : ∀ x ∈ U c, (d : V ≃ₗ[F] V) x ∈ U c := by
      intro x hx
      rw [hact c x hx]
      exact hpowU _ x hx
    let g : ↥(U c) →ₗ[F] ↥(U c) :=
      { toFun := fun x => ⟨(d : V ≃ₗ[F] V) (x : V) - (x : V),
          Submodule.sub_mem (U c) (hdU x x.2) x.2⟩
        map_add' := by
          intro x y
          exact Subtype.ext (by
            simp only [Submodule.coe_mk, Submodule.coe_add, map_add]
            abel)
        map_smul' := by
          intro a x
          exact Subtype.ext (by simp [smul_sub]) }
    have hginj : Function.Injective g := by
      intro x y hxy
      have hval : (d : V ≃ₗ[F] V) ((x : V) - (y : V)) = (x : V) - (y : V) := by
        have h := congrArg (fun z : ↥(U c) => (z : V)) hxy
        simp only [g, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk] at h
        have h' : ((d : V ≃ₗ[F] V) (x : V) - (x : V)) -
            ((d : V ≃ₗ[F] V) (y : V) - (y : V)) = 0 := sub_eq_zero.mpr h
        have h'' : ((d : V ≃ₗ[F] V) (x : V) - (d : V ≃ₗ[F] V) (y : V)) -
            ((x : V) - (y : V)) = 0 := by
          calc ((d : V ≃ₗ[F] V) (x : V) - (d : V ≃ₗ[F] V) (y : V)) -
                ((x : V) - (y : V))
              = ((d : V ≃ₗ[F] V) (x : V) - (x : V)) -
                ((d : V ≃ₗ[F] V) (y : V) - (y : V)) := by abel
            _ = 0 := h'
        rw [map_sub]
        exact sub_eq_zero.mp h''
      have hmem : (x : V) - (y : V) ∈ U c := Submodule.sub_mem (U c) x.2 y.2
      have hz : (x : V) - (y : V) = 0 :=
        hplane c _ hmem ((hact c _ hmem).symm.trans hval)
      exact Subtype.ext (sub_eq_zero.mp hz)
    obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hginj ⟨w, hw⟩
    have hwu : w = (d : V ≃ₗ[F] V) (u : V) - (u : V) := by
      have h := congrArg (fun z : ↥(U c) => (z : V)) hu
      simpa [g] using h.symm
    rw [hwu, polar_sub_left]
    have hpres : polar Q ((d : V ≃ₗ[F] V) (u : V)) v = polar Q (u : V) v := by
      have h1 := polar_map_of_mem (orthDerived_le_orthogonalGroup (Q := Q) d.2) (u : V) v
      rwa [hv] at h1
    rw [hpres, sub_self]
  have hvt : v ∈ polarPerp Q (⨆ j, U j) := by
    rw [mem_polarPerp_iff]
    intro y hy
    exact Submodule.iSup_induction U (motive := fun y => polar Q y v = 0) hy
      (fun j y hy => (mem_polarPerp_iff.mp (hvperp j)) y hy)
      (by simp)
      (fun y z hy hz => by rw [polar_add_left, hy, hz, add_zero])
  rw [htop] at hvt
  simpa [polarPerp, LinearMap.BilinForm.orthogonal_top_eq_bot hQ] using hvt

private theorem omPlusRefl_true_update {p k : ℕ} [NeZero p] {i j : Fin k} (hij : i < j) :
    CFSG.StandardType.omPlusRefl p (⟨(i, j), hij⟩, true)
      (Function.update (fun _ => Multiplicative.ofAdd (1 : ZMod p)) j
        (Multiplicative.ofAdd (-1))) =
    Function.update (fun _ => Multiplicative.ofAdd (1 : ZMod p)) j
      (Multiplicative.ofAdd (-1)) := by
  have hne : i ≠ j := hij.ne
  funext l
  rw [CFSG.StandardType.omPlusRefl_true (p := p) hij]
  simp only [MulAut.mul_apply, CFSG.StandardType.SpCoord.sgnAut_apply,
    CFSG.StandardType.SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hli : l = i
  · subst hli
    simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, Function.update_self]
  · by_cases hlj : l = j
    · subst hlj
      simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, Function.update_self]
    · simp [Function.update_of_ne hli, Function.update_of_ne hlj,
        Equiv.swap_apply_of_ne_of_ne hli hlj]

theorem exists_fixedPointFree_mem_image_fix_omPlusRefl
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p k : ℕ} (hp : p.Prime)
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e E) (htop : (⨆ j, U j) = ⊤)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hact : ∀ f c, ∀ x ∈ U c, ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      (((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x)
    (x : CFSG.StandardType.OmPlusIdx k) :
    ∃ z ∈ τ '' {f | CFSG.StandardType.omPlusRefl p x f = f},
      ∀ v, (z : V ≃ₗ[F] V) v = v → v = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hone : (1 : ZMod p) = 0 → False := by
    intro h1
    have hd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h1)
    exact hp.ne_one (Nat.dvd_one.mp hd)
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  cases s with
  | false =>
      refine ⟨τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)),
        ⟨fun _ => Multiplicative.ofAdd (1 : ZMod p), ?_, rfl⟩, ?_⟩
      · rw [show CFSG.StandardType.omPlusRefl p (⟨(i, j), hij⟩, false) =
            CFSG.StandardType.SpCoord.permAut (Equiv.swap i j) from
            CFSG.StandardType.omPlusRefl_false (p := p) hij]
        funext l
        simp [CFSG.StandardType.SpCoord.permAut_apply]
      · refine eq_zero_of_fixed_of_planePowers (Q := Q) hQ hp hF htop
          (fun c₀ => hact (fun _ => Multiplicative.ofAdd (1 : ZMod p)) c₀) ?_
        intro c₀
        intro h1
        rw [ofAdd_eq_one] at h1
        exact hone h1
  | true =>
      let f : Fin k → Multiplicative (ZMod p) :=
        Function.update (fun _ => Multiplicative.ofAdd (1 : ZMod p)) j
          (Multiplicative.ofAdd (-1))
      refine ⟨τ f, ⟨f, ?_, rfl⟩, ?_⟩
      · rw [show f = Function.update (fun _ => Multiplicative.ofAdd (1 : ZMod p)) j
            (Multiplicative.ofAdd (-1)) from rfl]
        exact omPlusRefl_true_update hij
      · refine eq_zero_of_fixed_of_planePowers (Q := Q) hQ hp hF htop
          (fun c₀ => hact f c₀) ?_
        intro c₀
        rw [show f c₀ = Function.update (fun _ => Multiplicative.ofAdd (1 : ZMod p)) j
            (Multiplicative.ofAdd (-1)) c₀ from rfl]
        by_cases hc₀ : c₀ = j
        · subst hc₀
          rw [Function.update_self]
          intro h1
          rw [ofAdd_eq_one] at h1
          exact hone (neg_eq_zero.mp h1)
        · rw [Function.update_of_ne hc₀]
          intro h1
          rw [ofAdd_eq_one] at h1
          exact hone h1

end CFSG.StandardType.SpNsRootGen

end
