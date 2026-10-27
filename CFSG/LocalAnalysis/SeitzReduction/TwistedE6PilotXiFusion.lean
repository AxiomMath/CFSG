module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotXiFusionF4
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusionEta

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.SeitzReduction.F4Pilot.ClassReps (frameT weylEltC)


local instance twistedE6PilotXiFusionNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotXiFusionNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Checks

theorem orbitCertRoot_F4_27 : orbitCertRoot .F4 27 = Pi.single 1 1 :=
  List.ofFn_injective (by decide +kernel)

theorem f4CollWeylPerm_r_a2 : f4CollWeylPerm [0, 2, 1, 3, 2, 1, 0] 47 = 27 ∧
    ∀ j ∈ [0, 2, 1, 3, 2, 1, 0], j < 4 := by
  decide

end Checks

theorem baseChangeGL_twistedE6RelWeyl {k K : Type} [Field k] [Field K] (ι : k →+* K)
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    baseChangeGL ι (twistedE6RelWeyl k ω) = twistedE6RelWeyl K ω := by
  rw [twistedE6RelWeyl, twistedE6RelWeyl, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => baseChangeGL_weylElt_one ι j

theorem weylEltC_conj_frameT_eq {k : Type} [Field k] [CharP k 2] :
    weylEltC k [0, 2, 1, 3, 2, 1, 0] * frameT k * (weylEltC k [0, 2, 1, 3, 2, 1, 0])⁻¹ =
      ⟨f4x k 27 1, pinnedX_mem_adjointGroup _ _⟩ := by
  apply Subtype.ext
  have h := (f4CollWeylElt_conj (K := k) [0, 2, 1, 3, 2, 1, 0] f4CollWeylPerm_r_a2.2
    (p := 47) (by norm_num) 1).1
  rw [f4CollWeylPerm_r_a2.1] at h
  exact h

theorem isConj_highRoot_repXC_zero {K : Type} [Field K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) :
    IsConj (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, pinnedX_highRoot_one_mem σ⟩ :
      graphFixedRootGroup TwistTag.E6 K σ) (repXC hσσ 0) := by
  refine isConj_iff.2 ⟨relWeylC σ (repWordX 0), ?_⟩
  rw [repXC_eq_conj hσσ 0]
  rfl

section Structure

variable {f : ℕ} {k K : Type} [Field k] [Field K] [CharP K 2] [Algebra k K]

theorem mem_eqLocus_xiAut_iff (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (g : graphFixedRootGroup TwistTag.E6 K σ) :
    g ∈ (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) ↔
      (g : ModGL TwistTag.E6.tag K) ∈
          (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) ∧
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * g =
          g * pinnedX TwistTag.E6.tag K e6HighestRoot 1 := by
  obtain ⟨-, -, -, -, -, ⟨e, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨htJ, hJC, η₀, hη₀, -, -, -, hfixξ, -, -, -, -⟩ := hsec
  have hη₀e : η₀ = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, coe_etaAut])
  have hξe : MulAut.conj (⟨_, hJC htJ⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η₀ =
      xiAut σ (apply_apply_eq hK hσ) := by
    rw [hη₀e]
    rfl
  rw [← hfixξ g, hξe]
  rfl

theorem exists_eqLocus_xiAut_eq_map (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ (ψ : adjointGroup Tag.F4 k →* graphFixedRootGroup TwistTag.E6 K σ)
      (h' : adjointGroup Tag.F4 k), Function.Injective ψ ∧
      (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
          (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) =
        (centralizer ({h' * frameT k * h'⁻¹} : Set (adjointGroup Tag.F4 k))).map ψ ∧
      ψ (h' * frameT k * h'⁻¹) =
        ⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, pinnedX_highRoot_one_mem σ⟩ := by
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have h2k : (2 : k) = 0 := CharP.cast_eq_zero k 2
  set ι := algebraMap k K with hιdef
  set J := (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) with hJdef
  obtain ⟨-, -, -, -, -, ⟨e, he, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨htJ, hJC, -, -, -, -, -, -, -, -, -, -⟩ := hsec
  set ψ : adjointGroup Tag.F4 k →* graphFixedRootGroup TwistTag.E6 K σ :=
    (Subgroup.inclusion hJC).comp e.symm.toMonoidHom with hψdef
  have hψcoe : ∀ y, ((ψ y : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
      ((e.symm y : J) : ModGL TwistTag.E6.tag K) := fun _ => rfl
  have hψinj : Function.Injective ψ := fun y y' h => e.symm.injective (Subtype.ext
    (congrArg (fun g : graphFixedRootGroup TwistTag.E6 K σ => (g : ModGL TwistTag.E6.tag K)) h))
  have hnJ : twistedE6RelWeyl K relWordTX ∈ J :=
    ⟨_, graphFixedRootGroup_le _ _ _ (twistedE6RelWeyl_mem (RingHom.id k) relWordTX),
      baseChangeGL_twistedE6RelWeyl ι relWordTX⟩
  have hxbc : baseChangeGL ι (f4OrbitXUnit k 1 1) =
      pinnedX TwistTag.E6.tag K (Pi.single 3 1) 1 := by
    rw [(baseChangeGL_f4OrbitXUnit_one_two ι 1).1, map_one]
  have hxJ : pinnedX TwistTag.E6.tag K (Pi.single 3 1) 1 ∈ J := ⟨_, f4OrbitXUnit_mem 1 1, hxbc⟩
  have hex : e ⟨_, hxJ⟩ = ⟨f4x k 27 1, pinnedX_mem_adjointGroup _ _⟩ := by
    apply Subtype.ext
    change (e ⟨_, hxJ⟩ : ModGL Tag.F4 k) = f4x k 27 1
    rw [he ⟨_, f4OrbitXUnit_mem 1 1⟩ ⟨_, hxJ⟩ hxbc.symm, e6FixedToF4_f4OrbitXUnit h2k,
      ← pinnedX_single, f4x, orbitCertRoot_F4_27]
  have hconjJ : (⟨_, hxJ⟩ : J) =
      ⟨_, hnJ⟩ * ⟨_, htJ⟩ * (⟨_, hnJ⟩ : J)⁻¹ :=
    Subtype.ext (conj_relWordTX_pinnedX_highRoot 1).symm
  have hs₀ : e ⟨_, htJ⟩ = ((e ⟨_, hnJ⟩)⁻¹ * weylEltC k [0, 2, 1, 3, 2, 1, 0]) * frameT k *
      ((e ⟨_, hnJ⟩)⁻¹ * weylEltC k [0, 2, 1, 3, 2, 1, 0])⁻¹ := by
    have h1 : e ⟨_, hnJ⟩ * e ⟨_, htJ⟩ * (e ⟨_, hnJ⟩)⁻¹ =
        weylEltC k [0, 2, 1, 3, 2, 1, 0] * frameT k * (weylEltC k [0, 2, 1, 3, 2, 1, 0])⁻¹ := by
      rw [weylEltC_conj_frameT_eq, ← hex, hconjJ, map_mul, map_mul, map_inv]
    calc e ⟨_, htJ⟩ = (e ⟨_, hnJ⟩)⁻¹ * (e ⟨_, hnJ⟩ * e ⟨_, htJ⟩ * (e ⟨_, hnJ⟩)⁻¹) *
          e ⟨_, hnJ⟩ := by group
      _ = (e ⟨_, hnJ⟩)⁻¹ * (weylEltC k [0, 2, 1, 3, 2, 1, 0] * frameT k *
          (weylEltC k [0, 2, 1, 3, 2, 1, 0])⁻¹) * e ⟨_, hnJ⟩ := by rw [h1]
      _ = _ := by group
  refine ⟨ψ, (e ⟨_, hnJ⟩)⁻¹ * weylEltC k [0, 2, 1, 3, 2, 1, 0], hψinj, ?_, ?_⟩
  · rw [← hs₀]
    ext g
    rw [mem_eqLocus_xiAut_iff hf hk hK σ hσ]
    constructor
    · rintro ⟨hgJ, hgt⟩
      refine ⟨e ⟨_, hgJ⟩, ?_, Subtype.ext (by rw [hψcoe, e.symm_apply_apply])⟩
      refine mem_centralizer_singleton_iff.2 ?_
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext hgt.symm)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).2, ?_⟩
      have h1 := congrArg e.symm (mem_centralizer_singleton_iff.1 hy)
      rw [map_mul, map_mul, e.symm_apply_apply] at h1
      exact (congrArg (fun x : J => (x : ModGL TwistTag.E6.tag K)) h1).symm
  · rw [← hs₀]
    apply Subtype.ext
    rw [hψcoe, e.symm_apply_apply]

theorem four_le_card_of_two_le (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) : 4 ≤ Nat.card k := by
  rw [hk]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2

theorem commutator_eqLocus_xiAut (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅(xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)),
      (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))⁆ =
      (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  obtain ⟨ψ, h', -, hF, -⟩ := exists_eqLocus_xiAut_eq_map (by omega) hk hK σ hσ
  rw [hF, ← map_commutator, centralizer_conj_eq_map, ← map_commutator,
    commutator_centralizer_frameT (four_le_card_of_two_le hf2 hk)]

theorem isConj_of_mem_center_eqLocus_xiAut (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {w : (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))}
    (hw : w ∈ center ((xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))))
    (hw1 : w ≠ 1) :
    IsConj (w : graphFixedRootGroup TwistTag.E6 K σ)
      ⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, pinnedX_highRoot_one_mem σ⟩ := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  obtain ⟨ψ, h', hψinj, hF, hψs⟩ := exists_eqLocus_xiAut_eq_map (by omega) hk hK σ hσ
  have hwF : (w : graphFixedRootGroup TwistTag.E6 K σ) ∈
      (centralizer ({h' * frameT k * h'⁻¹} : Set (adjointGroup Tag.F4 k))).map ψ := by
    rw [← hF]
    exact w.2
  obtain ⟨y, hy, hyw⟩ := hwF
  have hyc : ∀ v ∈ centralizer ({h' * frameT k * h'⁻¹} : Set (adjointGroup Tag.F4 k)),
      y * v = v * y := by
    intro v hv
    have hvF : ψ v ∈ (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) := by
      rw [hF]
      exact mem_map_of_mem ψ hv
    have h := mem_center_iff.1 hw ⟨ψ v, hvF⟩
    apply hψinj
    rw [map_mul, map_mul, hyw]
    exact (congrArg Subtype.val h).symm
  have hy'c : ∀ v ∈ centralizer ({frameT k} : Set (adjointGroup Tag.F4 k)),
      (h'⁻¹ * y * h') * v = v * (h'⁻¹ * y * h') := by
    intro v hv
    have hv' : h' * v * h'⁻¹ ∈
        centralizer ({h' * frameT k * h'⁻¹} : Set (adjointGroup Tag.F4 k)) := by
      rw [centralizer_conj_eq_map]
      exact ⟨v, hv, rfl⟩
    have h1 := hyc _ hv'
    calc h'⁻¹ * y * h' * v = h'⁻¹ * (y * (h' * v * h'⁻¹)) * h' := by group
      _ = h'⁻¹ * ((h' * v * h'⁻¹) * y) * h' := by rw [h1]
      _ = v * (h'⁻¹ * y * h') := by group
  have hq3 : 3 ≤ Nat.card k := le_trans (by norm_num) (four_le_card_of_two_le hf2 hk)
  rcases eq_one_or_isConj_frameT_of_forall_commute hq3 hy'c with h1 | h1
  · exfalso
    apply hw1
    have hy1 : y = 1 := by
      calc y = h' * (h'⁻¹ * y * h') * h'⁻¹ := by group
        _ = 1 := by rw [h1]; group
    apply Subtype.ext
    rw [← hyw, hy1, map_one]
    rfl
  · obtain ⟨g, hg⟩ := isConj_iff.1 h1
    have hyu : y = (h' * g⁻¹ * h'⁻¹) * (h' * frameT k * h'⁻¹) * (h' * g⁻¹ * h'⁻¹)⁻¹ := by
      rw [← hg]
      group
    set u := h' * g⁻¹ * h'⁻¹
    refine isConj_iff.2 ⟨(ψ u)⁻¹, ?_⟩
    rw [← hyw, hyu, map_mul ψ (u * _), map_mul ψ u, map_inv ψ u, hψs]
    group

end Structure

section Xi

variable {f : ℕ} {k K : Type} [Field k] [Field K] [CharP K 2] [Algebra k K]

theorem xiAut_inv_mul_thetaTorus (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (a : kˣ)
    (hm : E6GraphLevi.thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom a⁻¹) ∈
      graphFixedRootGroup TwistTag.E6 K σ) :
    (((xiAut σ (apply_apply_eq hK hσ) ⟨_, hm⟩)⁻¹ * ⟨_, hm⟩ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K (1 - (a : k) ^ 2)) := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set m := E6GraphLevi.thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom a⁻¹) with hmdef
  have hPm : diagramMap TwistTag.E6 K * m * (diagramMap TwistTag.E6 K)⁻¹ = m := by
    rw [hmdef, E6GraphLevi.thetaTorusHom_eq_thetaSL2]
    exact E6GraphLevi.diagramMap_conj_thetaSL2 h2K _
  have hm' : m = (E6GraphLevi.thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom a))⁻¹ := by
    rw [hmdef, map_inv, map_inv]
  have hconjt : m⁻¹ * (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ * m =
      pinnedX TwistTag.E6.tag K e6HighestRoot
        (((Units.map (algebraMap k K).toMonoidHom a : Kˣ) : K) ^ 2 * (-1)) := by
    rw [hm', inv_inv, pinnedX_neg, E6GraphLevi.thetaTorusHom_apply]
    exact E6GraphLevi.rootTorusSL2_conj_pinnedX h2K _ _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_xiAut]
  change (pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
      (diagramMap TwistTag.E6 K * m * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹)⁻¹ * m = _
  rw [hPm]
  have e1 : (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * m *
      (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹)⁻¹ * m =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
        (m⁻¹ * (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ * m) := by group
  rw [e1, hconjt, ← pinnedX_add]
  congr 1
  rw [map_sub, map_one, map_pow, Units.coe_map]
  change (1 : K) + (algebraMap k K (a : k)) ^ 2 * (-1) = 1 - (algebraMap k K (a : k)) ^ 2
  ring

theorem twistedFusionIn_xiAut (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have h2k : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set hσσ := apply_apply_eq hK hσ with hσσdef
  set ι := algebraMap k K with hιdef
  have hσk : ∀ x, σ x = x ^ Nat.card k := fun x => by rw [hk]; exact hσ x
  have : Nontrivial kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
    have := four_le_card_of_two_le hf2 hk
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : kˣ)
  have hc0 : (1 - (a : k) ^ 2) ≠ 0 := by
    intro h0
    apply ha
    exact Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero h2k (by linear_combination -h0))
  have hm : E6GraphLevi.thetaTorusHom K (Units.map ι.toMonoidHom a⁻¹) ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
    E6GraphLevi.thetaRankOneGroup_le_graphFixedRootGroup h2K hσk
      (E6GraphLevi.thetaTorus_le_thetaRankOneGroup h2K ι ⟨a⁻¹, rfl⟩)
  have hy₀C : pinnedX TwistTag.E6.tag K e6HighestRoot (ι (1 - (a : k) ^ 2)) ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
    pinnedX_mem_graphFixedRootGroup_of_fixed σ isRoot_e6HighestRoot permLattice_e6HighestRoot
      (E6GraphLevi.fixed_algebraMap hσk _)
  have hy₀J : pinnedX TwistTag.E6.tag K e6HighestRoot (ι (1 - (a : k) ^ 2)) ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) :=
    ⟨_, graphFixedRootGroup_le _ _ _ (pinnedX_mem_graphFixedRootGroup_of_fixed (RingHom.id k)
      isRoot_e6HighestRoot permLattice_e6HighestRoot rfl), baseChangeGL_pinnedX ι _ _⟩
  have hy₀F : (⟨_, hy₀C⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈
      (xiAut σ hσσ).toMonoidHom.eqLocus (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) := by
    refine (mem_eqLocus_xiAut_iff hf hk hK σ hσ _).2 ⟨hy₀J, ?_⟩
    change pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
        pinnedX TwistTag.E6.tag K e6HighestRoot (ι (1 - (a : k) ^ 2)) =
      pinnedX TwistTag.E6.tag K e6HighestRoot (ι (1 - (a : k) ^ 2)) *
        pinnedX TwistTag.E6.tag K e6HighestRoot 1
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  obtain ⟨y₀, hy₀⟩ : ∃ y : (xiAut σ hσσ).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)),
      (y : graphFixedRootGroup TwistTag.E6 K σ) = ⟨_, hy₀C⟩ := ⟨⟨⟨_, hy₀C⟩, hy₀F⟩, rfl⟩
  have hy₀1 : ((y₀ : graphFixedRootGroup TwistTag.E6 K σ)) ≠ 1 := by
    rw [hy₀]
    intro h1
    apply hc0
    have h2 : pinnedX TwistTag.E6.tag K e6HighestRoot (ι (1 - (a : k) ^ 2)) =
        pinnedX TwistTag.E6.tag K e6HighestRoot 0 := by
      have h3 := congrArg Subtype.val h1
      rw [pinnedX_zero]
      exact h3
    exact (map_eq_zero_iff ι ι.injective).1
      (pinnedX_injective (τ := TwistTag.E6.tag) (R := K) _ h2)
  have hy₀Z : y₀ ∈ center ((xiAut σ hσσ).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) := by
    rw [mem_center_iff]
    intro v
    have hvt := ((mem_eqLocus_xiAut_iff hf hk hK σ hσ v).1 v.2).2
    have hvC : ((v : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
        centralizer ({pinnedX TwistTag.E6.tag K e6HighestRoot 1} :
          Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨mem_centralizer_singleton_iff.2 hvt.symm, (v : graphFixedRootGroup TwistTag.E6 K σ).2⟩
    rw [centralizer_pinnedX_highRoot_inf_eq (k := k) hf hk hK hσ] at hvC
    have h1 := mem_centralizer_iff.1 hvC.1 _
      ((E6GraphLevi.mem_thetaRootGroup ι).2 ⟨1 - (a : k) ^ 2, rfl⟩)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hy₀]
    exact Subtype.ext h1.symm
  refine ⟨commutator_eqLocus_xiAut hf2 hk hK σ hσ, ⟨_, hm⟩, y₀, hy₀1, ?_, fun β => ?_⟩
  · rw [hy₀]
    exact Subtype.ext (xiAut_inv_mul_thetaTorus hK σ hσ a hm)
  have hβZ : β y₀ ∈ center ((xiAut σ hσσ).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) := by
    rw [mem_center_iff]
    intro v
    obtain ⟨u, rfl⟩ := β.surjective v
    rw [← map_mul, ← map_mul, mem_center_iff.1 hy₀Z u]
  have hβ1 : β y₀ ≠ 1 := fun h => hy₀1 (congrArg Subtype.val
    (β.injective (h.trans (map_one β).symm)))
  exact Or.inl ((isConj_of_mem_center_eqLocus_xiAut hf2 hk hK σ hσ hβZ hβ1).trans
    (isConj_highRoot_repXC_zero hσσ))

end Xi

end CFSG.SeitzReduction.TwistedE6Pilot
