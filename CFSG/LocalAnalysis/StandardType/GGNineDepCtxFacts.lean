module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtx
public import CFSG.LocalAnalysis.StandardType.GGExtCtx
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprim
import CFSG.LocalAnalysis.StandardType.GGNineDepRestrictAux
import CFSG.LocalAnalysis.StandardType.GGNineDepNegLift
import CFSG.LocalAnalysis.StandardType.GGResIBasic
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm
import CFSG.LocalAnalysis.StandardType.ZS.Adapter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
  {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}

namespace GGNineDepCtx

theorem finite (X : GGNineDepCtx h α r s x) : Module.Finite (ZMod p) V :=
  l04nD2_finite X.case

theorem extCtx (X : GGNineDepCtx h α r s x) :
    GGExtCtx (ggLargeGrp r s) (ggFixLineT r s) (ggNineQ X) := by
  refine ⟨?disp, ?fix, ?inj, ?restr⟩
  · exact l04nD2_disp X.case
  · intro v hv
    have hv' : v ∈ ggLinFix (Set.range r ∪ Set.range s) := by
      intro a ha
      rcases ha with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · exact hv _ (Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self i)))
      · exact hv _ (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_range_self k)))
    rw [l04nD2_fix_A X.case] at hv'
    simpa using hv'
  · intro a ha hT
    have hρ : ggLargeRho r s X.hA ⟨a, ha⟩ = 1 := by
      ext v
      rw [ggLargeRho_apply_coe]
      simpa using hT v.1 v.2
    have h1 : (⟨a, ha⟩ : ↥(ggLargeGrp r s)) = 1 := by
      apply X.restr.1
      rw [hρ, map_one]
    simpa using h1
  · intro q
    constructor
    · intro hq
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hq
      exact ⟨(a : V ≃ₗ[ZMod p] V), a.2, fun w => (ggLargeRho_apply_coe X.hA a w).symm⟩
    · rintro ⟨a, ha, hw⟩
      refine MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, ?_⟩
      ext w
      rw [ggLargeRho_apply_coe]
      exact hw w

private def ctxA_idx (N : ℕ) (j : Fin (N - 2)) : Fin (N - 1) :=
  Fin.castLE (by omega) j

private lemma ctxA_not_dvd (X : GGNineDepCtx h α r s x) : ¬ p ∣ (N - 2) + 1 := by
  have h5 : 5 ≤ N := X.case.lin.N_ge
  have hNm : (N - 2) + 1 = N - 1 := by omega
  rw [hNm]
  intro hdvd
  have h1 : p ∣ N - (N - 1) := Nat.dvd_sub X.case.lin.p_dvd hdvd
  have h2 : N - (N - 1) = 1 := by omega
  rw [h2] at h1
  exact (Fact.out : p.Prime).not_dvd_one h1

private lemma ctxA_pair (X : GGNineDepCtx h α r s x) (i j : Fin (N - 2)) :
    α (ctxA_idx N i) (h (ctxA_idx N j)) = (CartanMatrix.A (N - 2) i j : ZMod p) := by
  have hA : ∀ i j : Fin (N - 2),
      CartanMatrix.A (N - 1) (ctxA_idx N i) (ctxA_idx N j) = CartanMatrix.A (N - 2) i j := by
    intro i j
    simp only [CartanMatrix.A, Matrix.of_apply, ctxA_idx, Fin.ext_iff, Fin.val_castLE]
  rw [X.case.lin.pair, hA]

private lemma ctxA_linearIndependent (X : GGNineDepCtx h α r s x) :
    LinearIndependent (ZMod p) (fun j : Fin (N - 2) => h (ctxA_idx N j)) :=
  cartanA_linearIndependent (ctxA_not_dvd X) (ctxA_pair X)

theorem finrank_eq (X : GGNineDepCtx h α r s x) : Module.finrank (ZMod p) V = N := by
  haveI : Module.Finite (ZMod p) V := finite X
  set S : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range fun j : Fin (N - 2) => h (ctxA_idx N j)) with hS
  have hSdim : Module.finrank (ZMod p) S = N - 2 := by
    rw [hS, finrank_span_eq_card (ctxA_linearIndependent X), Fintype.card_fin]
  have hinf : S ⊓ ggLinFix (Set.range r) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    refine cartanA_eq_zero_of_mem_span (ctxA_not_dvd X) (ctxA_pair X) ?_ fun i => ?_
    · rw [← hS]
      exact hv.1
    · have hfix : r (ctxA_idx N i) v = v := hv.2 _ ⟨_, rfl⟩
      exact ggResI_alpha_eq_zero X.case.lin.p_ne_two (X.case.lin.refl_form (ctxA_idx N i))
        (l04nD2_pair_diag X.case (ctxA_idx N i)) hfix
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (ggLinFix (Set.range r))
  rw [hinf, finrank_bot, add_zero, hSdim] at hsum
  have hle := Submodule.finrank_le (S ⊔ ggLinFix (Set.range r))
  have htwo := X.case.two
  have hdim := X.case.lin.dim_le
  omega

theorem natCard_ggNineQ (X : GGNineDepCtx h α r s x) :
    Nat.card ↥(ggNineQ X) = Nat.card ↥(ggLargeGrp r s) :=
  (Nat.card_congr (MonoidHom.ofInjective X.restr.1).toEquiv).symm

theorem natCard_closure_r (X : GGNineDepCtx h α r s x) :
    Nat.card ↥(Subgroup.closure (Set.range r)) = N.factorial := by
  have h5 : 5 ≤ N := X.case.lin.N_ge
  have h := l04fD5_P_card (m := N - 1) X.case.lin.p_ne_two (by omega) X.case.lin.pair r
    X.case.lin.refl_form
  have hN : (N - 1) + 1 = N := Nat.sub_add_cancel (by omega)
  rwa [hN] at h

theorem factorial_dvd (X : GGNineDepCtx h α r s x) : N.factorial ∣ Nat.card ↥(ggNineQ X) := by
  rw [natCard_ggNineQ X]
  have hP : Subgroup.closure (Set.range r) ≤ ggLargeGrp r s := by
    rw [ggLargeGrp]
    exact Subgroup.closure_mono Set.subset_union_left
  rw [← natCard_closure_r X]
  exact Subgroup.card_dvd_of_le hP

theorem natCard_ne_factorial (X : GGNineDepCtx h α r s x) :
    Nat.card ↥(ggNineQ X) ≠ N.factorial := by
  intro hcard
  have hcardA : Nat.card ↥(ggLargeGrp r s) = N.factorial := by
    rw [← natCard_ggNineQ X]
    exact hcard
  haveI : Finite ↥(ggLargeGrp r s) :=
    Nat.finite_of_card_ne_zero (by rw [hcardA]; exact Nat.factorial_ne_zero N)
  have hP : Subgroup.closure (Set.range r) ≤ ggLargeGrp r s := by
    rw [ggLargeGrp]
    exact Subgroup.closure_mono Set.subset_union_left
  have hPA : Subgroup.closure (Set.range r) = ggLargeGrp r s :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hcardA, natCard_closure_r X])
  have hFne : ggLinFix (Set.range r) ≠ ⊥ := by
    intro hbot
    have h2 := X.case.two
    rw [hbot, finrank_bot] at h2
    omega
  obtain ⟨v, hvF, hv0⟩ := (Submodule.ne_bot_iff (ggLinFix (Set.range r))).mp hFne
  have hfixP : ∀ a ∈ Subgroup.closure (Set.range r), a v = v := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | one => rfl
    | mem y hy => exact hvF y hy
    | mul y z hy hz ihy ihz => rw [LinearEquiv.mul_apply, ihz, ihy]
    | inv y hy ihy =>
        calc y⁻¹ v = y⁻¹ (y v) := by rw [ihy]
          _ = v := by simpa using (y⁻¹).apply_symm_apply v
  have hv' : v ∈ ggLinFix (Set.range r ∪ Set.range s) := by
    intro a ha
    rcases ha with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · exact hvF _ ⟨i, rfl⟩
    · have hsk : s k ∈ Subgroup.closure (Set.range r) := by
        rw [hPA]
        exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_range_self k))
      exact hfixP (s k) hsk
  rw [l04nD2_fix_A X.case] at hv'
  exact hv0 (by simpa using hv')

theorem finrank_eq_of_neg_mem (X : GGNineDepCtx h α r s x)
    (hneg : (LinearEquiv.neg (ZMod p) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) ∈
      ggNineQ X) :
    Module.finrank (ZMod p) ↥(ggFixLineT r s) = N := by
  have htop := GGExtCtx.eq_top_of_neg_mem X.extCtx X.case.lin.p_ne_two hneg
  rw [htop, finrank_top]
  exact finrank_eq X

theorem natCard_le (X : GGNineDepCtx h α r s x) :
    Nat.card ↥(ggNineQ X) ≤ p ^ Module.finrank (ZMod p) ↥(ggFixLineT r s) *
      (6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s))) := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  haveI : Finite ↥(MulAction.orbit (ggLargeGrp r s) x) :=
    Finite.of_injective (fun y : ↥(MulAction.orbit (ggLargeGrp r s) x) => (y : V))
      Subtype.val_injective
  haveI : Finite ↥(ggFixLineT r s) :=
    Finite.of_injective (fun w : ↥(ggFixLineT r s) => (w : V)) Subtype.val_injective
  set A := ggLargeGrp r s
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥A x)
  rw [MulAction.index_stabilizer] at h1
  have h1' : Nat.card ↥A = Nat.card (MulAction.stabilizer ↥A x) *
      Nat.card ↥(MulAction.orbit ↥A x) := by
    rw [← h1, Nat.card_coe_set_eq]
  have h2 : Nat.card (MulAction.stabilizer ↥A x) ≤
      6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s)) := by
    refine le_trans ?_ X.case.stab
    refine Nat.card_le_card_of_injective
      (fun g => (⟨((g : ↥A) : V ≃ₗ[ZMod p] V), (g : ↥A).2, ?_⟩ :
        ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x))) ?_
    · have hg := MulAction.mem_stabilizer_iff.mp g.2
      rw [Subgroup.smul_def] at hg
      exact MulAction.mem_stabilizer_iff.mpr hg
    · intro g g' hgg'
      have h := congrArg (fun y : ↥(ggLargeGrp r s ⊓
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) => (y : V ≃ₗ[ZMod p] V)) hgg'
      exact Subtype.ext (Subtype.ext h)
  have h3 : Nat.card ↥(MulAction.orbit ↥A x) ≤
      p ^ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
    have hinj : Function.Injective
        (fun y : ↥(MulAction.orbit ↥A x) =>
          (⟨(y : V) - x, by
            obtain ⟨a, ha⟩ := y.2
            rw [← ha]
            simpa [Subgroup.smul_def] using l04nD2_disp X.case a a.2 x⟩ :
            ↥(ggFixLineT r s))) := by
      intro y y' h
      have h' : (y : V) - x = (y' : V) - x := congrArg Subtype.val h
      exact Subtype.ext (sub_left_injective h')
    calc Nat.card ↥(MulAction.orbit ↥A x) ≤ Nat.card ↥(ggFixLineT r s) :=
          Nat.card_le_card_of_injective _ hinj
      _ = p ^ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  calc Nat.card ↥(ggNineQ X) = Nat.card ↥A := natCard_ggNineQ X
    _ = Nat.card (MulAction.stabilizer ↥A x) * Nat.card ↥(MulAction.orbit ↥A x) := h1'
    _ ≤ (6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s))) *
        p ^ Module.finrank (ZMod p) ↥(ggFixLineT r s) := Nat.mul_le_mul h2 h3
    _ = p ^ Module.finrank (ZMod p) ↥(ggFixLineT r s) *
        (6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s))) := Nat.mul_comm _ _

theorem closure_s_le (X : GGNineDepCtx h α r s x) :
    Subgroup.closure (Set.range s) ≤
      ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x := by
  refine le_inf (Subgroup.closure_mono Set.subset_union_right) ?_
  rw [Subgroup.closure_le]
  rintro g ⟨k, rfl⟩
  have hx : x ∈ ggLinFix (Set.range s) := by
    rw [X.case.lin.fix_s]
    exact Submodule.subset_span (Set.mem_singleton x)
  have hg : s k x = x := hx (s k) ⟨k, rfl⟩
  exact MulAction.mem_stabilizer_iff.mpr (by rwa [LinearEquiv.smul_def])

theorem exists_stab_restrict (X : GGNineDepCtx h α r s x) (hxT : x ∈ ggFixLineT r s) :
    ∃ (x' : ↥(ggFixLineT r s))
      (H' : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))),
      x' ≠ 0 ∧
      H' ≤ ggNineQ X ⊓ MulAction.stabilizer (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) x' ∧
      Nat.card ↥H' = Nat.card ↥(Subgroup.closure (Set.range s)) ∧
      Nat.card ↥(ggNineQ X ⊓
          MulAction.stabilizer (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) x') ≤
        6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s)) := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  haveI : Finite ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) :=
    Finite.of_injective
      (fun y : ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) =>
        (y : V ≃ₗ[ZMod p] V)) Subtype.val_injective
  let ρ := ggLargeRho r s X.hA
  let B : Subgroup ↥(ggLargeGrp r s) :=
    (Subgroup.closure (Set.range s)).subgroupOf (ggLargeGrp r s)
  let H' : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) := B.map ρ
  refine ⟨⟨x, hxT⟩, H', ?_, ?_, ?_, ?_⟩
  · intro h0
    exact X.case.lin.x_ne (congrArg Subtype.val h0)
  · refine le_inf (Subgroup.map_le_range ρ B) ?_
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
    apply Subtype.ext
    rw [ggLargeRho_apply_coe]
    have haH : (a : V ≃ₗ[ZMod p] V) ∈ Subgroup.closure (Set.range s) :=
      Subgroup.mem_subgroupOf.mp ha
    have hfix := (Subgroup.mem_inf.mp ((closure_s_le X) haH)).2
    simpa [LinearEquiv.smul_def] using (MulAction.mem_stabilizer_iff.mp hfix)
  · have hcardB : Nat.card ↥B = Nat.card ↥(Subgroup.closure (Set.range s)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.closure_mono Set.subset_union_right)).toEquiv
    have hcardMap : Nat.card ↥H' = Nat.card ↥B :=
      Subgroup.card_map_of_injective (f := ρ) (K := B) (show Function.Injective ρ from X.restr.1)
    exact hcardMap.trans hcardB
  · set S : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
      ggNineQ X ⊓ MulAction.stabilizer (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))
        (⟨x, hxT⟩ : ↥(ggFixLineT r s)) with hS
    change Nat.card ↥S ≤ 6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s))
    have hSle : S ≤ ρ.range := by
      rw [hS]
      exact inf_le_left
    have hcardComap : Nat.card ↥(S.comap ρ) = Nat.card ↥S := by
      calc Nat.card ↥(S.comap ρ) = Nat.card ↥((S.comap ρ).map ρ) :=
            (Subgroup.card_map_of_injective (f := ρ) (K := S.comap ρ)
              (show Function.Injective ρ from X.restr.1)).symm
        _ = Nat.card ↥S := by
            rw [Subgroup.map_comap_eq_self hSle]
    let C : Subgroup (V ≃ₗ[ZMod p] V) :=
      (S.comap ρ).map (Subgroup.subtype (ggLargeGrp r s))
    have hcardC : Nat.card ↥C = Nat.card ↥(S.comap ρ) := by
      change Nat.card ↥((S.comap ρ).map (Subgroup.subtype (ggLargeGrp r s))) =
        Nat.card ↥(S.comap ρ)
      exact Subgroup.card_map_of_injective (f := Subgroup.subtype (ggLargeGrp r s))
        (K := S.comap ρ) (Subgroup.subtype_injective _)
    have hCle : C ≤ ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x := by
      rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
      have h1 : (ρ a) ⟨x, hxT⟩ = ⟨x, hxT⟩ :=
        MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp ha)).2
      have h2 := ggLargeRho_apply_coe X.hA a ⟨x, hxT⟩
      rw [h1] at h2
      exact h2.symm
    calc Nat.card ↥S = Nat.card ↥(S.comap ρ) := hcardComap.symm
      _ = Nat.card ↥C := hcardC.symm
      _ ≤ Nat.card ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) :=
          Subgroup.card_le_of_le hCle
      _ ≤ 6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s)) := X.case.stab

theorem weylTypeData
    (X : GGNineDepCtx h α r s x) :
    GGWeylTypeData (N - 1) (Nat.card ↥(Subgroup.closure (Set.range s)))
      (Nat.card ↥(Subgroup.center ↥(Subgroup.closure (Set.range s)))) := by
  obtain ⟨M, hM, ⟨φ⟩⟩ := X.case.weylL
  have h := ggWeylTypeData_of_isWeylMatrix hM
  have h1 : Nat.card M.Group = Nat.card ↥(Subgroup.closure (Set.range s)) :=
    Nat.card_congr φ.toEquiv
  have h2 : Nat.card ↥(Subgroup.center M.Group) =
      Nat.card ↥(Subgroup.center ↥(Subgroup.closure (Set.range s))) :=
    Nat.card_congr (Subgroup.centerCongr φ).toEquiv
  simpa [h1, h2] using h

theorem not_linearIndependent_α (X : GGNineDepCtx h α r s x) :
    ¬ LinearIndependent (ZMod p) α := by
  intro hLI
  haveI : Module.Finite (ZMod p) V := finite X
  have hN : Module.finrank (ZMod p) V = N := finrank_eq X
  set W : Submodule (ZMod p) (Module.Dual (ZMod p) V) :=
    Submodule.span (ZMod p) (Set.range α) with hW
  have hWdim : Module.finrank (ZMod p) W = N - 1 := by
    rw [hW, finrank_span_eq_card hLI, Fintype.card_fin]
  have hker : ggLinFix (Set.range r) = W.dualCoannihilator := by
    ext v
    rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro hv φ hφ
      have hspan : ∀ ψ ∈ Submodule.span (ZMod p) (Set.range α), ψ v = 0 := by
        intro ψ hψ
        induction hψ using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact ggResI_alpha_eq_zero X.case.lin.p_ne_two (X.case.lin.refl_form i)
              (l04nD2_pair_diag X.case i) (hv _ ⟨i, rfl⟩)
        | zero => simp
        | add y z hy hz ihy ihz => simp [ihy, ihz]
        | smul c y hy ihy => simp [ihy]
      exact hspan φ (by rwa [← hW])
    · intro hv
      have hα : ∀ i, α i v = 0 := fun i => hv (α i) (by
        rw [hW]
        exact Submodule.subset_span (Set.mem_range_self i))
      intro a ha
      obtain ⟨i, rfl⟩ := ha
      rw [X.case.lin.refl_form i v, hα i, zero_smul, sub_zero]
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [← hker, hWdim, hN] at hsum
  have htwo := X.case.two
  omega

theorem exists_restrict_frame (X : GGNineDepCtx h α r s x) :
    ∃ (h' : Fin (N - 1) → ↥(ggFixLineT r s))
      (α' : Fin (N - 1) → Module.Dual (ZMod p) ↥(ggFixLineT r s))
      (r' : Fin (N - 1) → (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))),
      (∀ i, r' i ∈ ggNineQ X) ∧ (∀ i v, r' i v = v - α' i v • h' i) ∧
      (∀ i j, α' i (h' j) = (CartanMatrix.A (N - 1) i j : ZMod p)) ∧
      ¬ LinearIndependent (ZMod p) h' := by
  let T := ggFixLineT r s
  let hrg : ∀ i : Fin (N - 1), r i ∈ ggLargeGrp r s := fun i =>
    Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self i))
  let h' : Fin (N - 1) → ↥T := fun i => ⟨h i, l04nD2_h_mem_T X.case i⟩
  let α' : Fin (N - 1) → Module.Dual (ZMod p) ↥T := fun i => (α i).comp T.subtype
  let r' : Fin (N - 1) → (↥T ≃ₗ[ZMod p] ↥T) := fun i => ggLargeRho r s X.hA ⟨r i, hrg i⟩
  refine ⟨h', α', r', ?_, ?_, ?_, ?_⟩
  · intro i
    exact MonoidHom.mem_range.mpr ⟨⟨r i, hrg i⟩, rfl⟩
  · intro i v
    apply Subtype.ext
    show (((ggLinRestrictHom T ⟨r i, X.hA (hrg i)⟩) v : ↥T) : V) =
      (v : V) - α i (v : V) • h i
    rw [l04nD2_restrict_apply, X.case.lin.refl_form i (v : V)]
  · intro i j
    show α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
    exact X.case.lin.pair i j
  · intro hlin
    apply X.case.dep
    have hcomp : h = T.subtype ∘ h' := by funext i; rfl
    rw [hcomp]
    exact LinearIndependent.map' hlin T.subtype (Submodule.ker_subtype T)

theorem not_isImprimitiveOnV (X : GGNineDepCtx h α r s x) :
    ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV (ggNineQ X) := by
  exact ggLargeDep_noImprim X.case.lin X.case.two X.hA X.restr

theorem family (X : GGNineDepCtx h α r s x) (hUse : ZS.UseInput) : ZS.Family p (ggNineQ X) := by
  haveI : Module.Finite (ZMod p) V := X.finite
  have h3 : 3 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
    have h5 := X.case.lin.N_ge
    have hd := X.d_ge
    omega
  have hrefl : ZS.ReflGen p (ggNineQ X) := by
    rw [ZS.reflGen_iff_eq_closure_ggLinRefl]
    exact X.restr.2.2
  exact hUse p ↥(ggFixLineT r s) (ggNineQ X) X.case.lin.p_ne_two h3 hrefl X.restr.2.1

end GGNineDepCtx

end CFSG.StandardType

end
