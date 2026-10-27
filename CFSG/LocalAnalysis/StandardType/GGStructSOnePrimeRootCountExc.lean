module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCount
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExc
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.StandardType

open RootCentExc Subgroup
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.LieType.ChevTwo
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Steinberg.TwistedE6
open CFSG.SeitzReduction.TwistedE6Pilot

section Quasisimple

variable {W : Type} [Group W]

theorem isChevTwoLayeredBy_of_isChevTwoLayered_of_isQuasisimple
    (hW : CFSG.Open.IsQuasisimple W) (h : IsChevTwoLayered W)
    (hZ : Subgroup.center W = ⊥) :
    IsChevTwoLayeredBy W [Nat.card W] := by
  have htop : CFSG.Open.IsComponentOf (⊤ : Subgroup W) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := W)) hW⟩
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (W ⧸ Subgroup.center W) :=
    isChevSimple_of_mulEquiv
      (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.topEquiv (G := W))).symm (h.2 ⊤ htop)
  have hb := isChevTwoLayeredBy_of_isQuasisimple hW hchev
  have hcard : Nat.card (W ⧸ Subgroup.center W) = Nat.card W :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv
  rwa [hcard] at hb

end Quasisimple

section Conj

variable {C : Type} [Group C]

theorem GGRootCentQLTypedBy.conj {z : C} {o : List ℕ} (h : GGRootCentQLTypedBy z o) (g : C) :
    GGRootCentQLTypedBy (g * z * g⁻¹) o :=
  h.map (MulAut.conj g)

theorem GGRootCentQLTypedBy.of_conj {z g : C} {o : List ℕ}
    (h : GGRootCentQLTypedBy (g * z * g⁻¹) o) : GGRootCentQLTypedBy z o := by
  have h' := h.conj g⁻¹
  rwa [show g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z by group] at h'

end Conj

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section C3


theorem isChevTwoLayeredBy_C3Levi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayeredBy ↥(F4Pilot.C3Levi K) [CFSG.Open.ordBC 3 (2 ^ f)] := by
  have hsc : StatedClassicalModel (F4Pilot.C3Levi K) .PSp 3 2 f :=
    (F4Pilot.lieModel_C3Levi hK).statedClassicalModel (by decide)
  have hcard : Nat.card ↥(F4Pilot.C3Levi K) = CFSG.Open.ordBC 3 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.2.1 rfl
  have h := isChevTwoLayeredBy_of_isChevTwoLayered_of_isQuasisimple
    F4Pilot.isQuasisimple_open_C3Levi (isChevTwoLayered_C3Levi hK)
    F4Pilot.center_C3Levi_eq_bot
  rwa [hcard] at h

end C3

section A5


theorem isChevTwoLayeredBy_a5Levi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayeredBy ↥(E6Pilot.a5Levi K) [CFSG.Open.ordA 5 (2 ^ f)] := by
  have hsc : StatedClassicalModel (E6Pilot.a5Levi K) .PSL 6 2 f :=
    (E6Pilot.lieModel_a5Levi hK).statedClassicalModel (by decide)
  have hcard : Nat.card ↥(E6Pilot.a5Levi K) = CFSG.Open.ordA 5 (2 ^ f) := by
    simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).1 rfl
  have h := isChevTwoLayeredBy_of_isChevTwoLayered_of_isQuasisimple
    E6Pilot.isQuasisimple_open_a5Levi (isChevTwoLayered_a5Levi hK) E6Pilot.center_a5Levi_eq_bot
  rwa [hcard] at h

end A5

section D6


theorem isChevTwoLayeredBy_perpLevi_E7 {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayeredBy ↥(EPilot.perpLevi .E7 K) [CFSG.Open.ordD 6 (2 ^ f)] := by
  have hsc : StatedClassicalModel (EPilot.perpLevi .E7 K) .POmegaPlus 6 2 f :=
    (E7Pilot.lieModel_perpLevi_E7 hK).statedClassicalModel (by decide)
  have hcard : Nat.card ↥(EPilot.perpLevi .E7 K) = CFSG.Open.ordD 6 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.1 rfl
  have h := isChevTwoLayeredBy_of_isChevTwoLayered_of_isQuasisimple
    E7Pilot.isQuasisimple_open_perpLevi_E7 (isChevTwoLayered_perpLevi_E7 hK)
    E7Pilot.center_perpLevi_E7_eq_bot
  rwa [hcard] at h

end D6

section E7


theorem isChevTwoLayeredBy_e7Levi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayeredBy ↥(E8Pilot.e7Levi K) [CFSG.Open.ordE7 (2 ^ f)] := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hcard : Nat.card ↥(E8Pilot.e7Levi K) = CFSG.Open.ordE7 (2 ^ f) := by
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (E8Pilot.chevalleyExceptionalModel_e7Levi hf hK)
  have h := isChevTwoLayeredBy_of_isChevTwoLayered_of_isQuasisimple
    E8Pilot.isQuasisimple_open_e7Levi (isChevTwoLayered_e7Levi hK) E8Pilot.center_e7Levi_eq_bot
  rwa [hcard] at h

end E7

end Levi

section SU6

variable {K : Type} [Field K] [CharP K 2]

variable {k : Type} [Field k] [Algebra k K]


theorem isChevTwoLayeredBy_su6Levi_subgroupOf {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsChevTwoLayeredBy ↥((TwistedE6Pilot.su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) [CFSG.Open.ordTwistedA 5 (2 ^ f)] := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ
  set L := (TwistedE6Pilot.su6Levi σ).subgroupOf C₀
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    ⟨(TwistedE6Pilot.isQuasisimple_su6Levi_subgroupOf hf hk hK hσ).1.commutator_eq_top,
      (TwistedE6Pilot.isQuasisimple_su6Levi_subgroupOf hf hk hK hσ).2.1⟩
  haveI : IsSimpleGroup (TwistedE6Pilot.su6Levi σ) :=
    TwistedE6Pilot.isSimpleGroup_su6Levi hf hk hK hσ
  have hnc : ∃ a b : TwistedE6Pilot.su6Levi σ, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have := TwistedE6Pilot.isPerfect_su6Levi hf hk hK hσ
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
  have hZsu : Subgroup.center (TwistedE6Pilot.su6Levi σ) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have hZ : Subgroup.center ↥L = ⊥ :=
    F4Pilot.center_eq_bot_congr
      (Subgroup.subgroupOfEquivOfLe (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup σ)).symm hZsu
  have hsc : StatedClassicalModel ((TwistedE6Pilot.su6Levi σ).subgroupOf C₀) .PSU 6 2 f :=
    (TwistedE6Pilot.lieModel_su6Levi_subgroupOf hf hk hK hσ).statedClassicalModel (by decide)
  have hcard : Nat.card ↥L = CFSG.Open.ordTwistedA 5 (2 ^ f) := by
    simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.1 rfl
  have h := isChevTwoLayeredBy_of_isChevTwoLayered_of_isQuasisimple hLq
    (isChevTwoLayered_su6Levi_subgroupOf hf hk hK hσ) hZ
  rwa [hcard] at h

end SU6

section Base

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section F4Base


theorem xPar_f4HighRoot_typedBy {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .F4) :
    GGRootCentQLTypedBy (xPar F f4HighRoot (1 : K)) [CFSG.Open.ordBC 3 (2 ^ f)] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F f4HighRoot (1 : K) = F4Pilot.zT K := by
    refine Subtype.ext ((coe_xPar_eq_pinnedX h2 F isRoot_f4HighRoot 1).trans ?_)
    change pinnedX .F4 K f4HighRoot 1 = pinnedX .F4 K (RootOps.orbitCertRoot .F4 47) 1
    rw [F4Pilot.orbitCertRoot_47_44.1]
    rfl
  rw [he]
  obtain ⟨hQ2, hQL, -, hLQ⟩ := F4Pilot.isTwoRadicalDecomp_zT (K := K)
  exact ⟨_, _, hQ2, hQL, hLQ, isChevTwoLayeredBy_C3Levi hK⟩

end F4Base

section EBase


theorem xPar_highRoot_E_typedBy {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {o : List ℕ} (hL : IsChevTwoLayeredBy ↥(EPilot.perpLevi τ K) o)
    (F : RootOperatorFamily τ) {i₀ : Fin τ.rank} (hd : HighRootData τ (highRoot τ) i₀) :
    GGRootCentQLTypedBy (xPar F (highRoot τ) (1 : K)) o := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F (highRoot τ) (1 : K) =
      EPilot.pinnedElt τ (highRoot τ) 1 :=
    Subtype.ext (coe_xPar_eq_pinnedX h2 F hd.maxHeight.1 1)
  rw [he]
  obtain ⟨hQ2, hQL, -, hLQ⟩ := EPilot.isTwoRadicalDecomp_highRoot (K := K) hτ one_ne_zero
  exact ⟨_, _, hQ2, hQL, hLQ, hL⟩

end EBase

section E6Base


theorem xPar_e6HighRoot_typedBy {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E6) :
    GGRootCentQLTypedBy (xPar F e6HighRoot (1 : K)) [CFSG.Open.ordA 5 (2 ^ f)] :=
  xPar_highRoot_E_typedBy (Or.inl rfl) (isChevTwoLayeredBy_a5Levi hK) F highRootData_E6

end E6Base

section E7Base


theorem xPar_e7HighRoot_typedBy {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E7) :
    GGRootCentQLTypedBy (xPar F e7HighRoot (1 : K)) [CFSG.Open.ordD 6 (2 ^ f)] :=
  xPar_highRoot_E_typedBy (Or.inr (Or.inl rfl)) (isChevTwoLayeredBy_perpLevi_E7 hK) F
    highRootData_E7

end E7Base

section E8Base


theorem xPar_e8HighRoot_typedBy {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E8) :
    GGRootCentQLTypedBy (xPar F e8HighRoot (1 : K)) [CFSG.Open.ordE7 (2 ^ f)] :=
  xPar_highRoot_E_typedBy (Or.inr (Or.inr rfl)) (isChevTwoLayeredBy_e7Levi hK) F
    highRootData_E8

end E8Base

end Base

section Isogeny

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section E6Iso


theorem e6Isogeny_qL_typedBy {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ (e6Datum K).roots)
    {z : e6Data_valid.minGroup K} (hz : z ∈ (e6Datum K).rootGroup γ)
    (hz1 : e6Isogeny K z ≠ 1) :
    GGRootCentQLTypedBy (e6Isogeny K z) [CFSG.Open.ordA 5 (2 ^ f)] := by
  have hγ' : IsRoot .E6 γ :=
    e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
  rw [e6Isogeny_xm K hγ'] at hz1 ⊢
  exact RootCentQLTyped.of_mem_rootGroup
    (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordA 5 (2 ^ f)])
    (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_E6
      (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordA 5 (2 ^ f)])
      (fun α z h => h.map α) _
      (xPar_e6HighRoot_typedBy hK _) j) hγ' (xPar_mem hγ' _) hz1

end E6Iso

section E7Iso


theorem e7Isogeny_qL_typedBy {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {γ : Fin Tag.E7.rank → ℤ} (hγ : γ ∈ (e7Datum K).roots)
    {z : e7Data_valid.minGroup K} (hz : z ∈ (e7Datum K).rootGroup γ)
    (hz1 : e7Isogeny K z ≠ 1) :
    GGRootCentQLTypedBy (e7Isogeny K z) [CFSG.Open.ordD 6 (2 ^ f)] := by
  have hγ' : IsRoot .E7 γ :=
    e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hz
  rw [e7Isogeny_xm] at hz1 ⊢
  exact RootCentQLTyped.of_mem_rootGroup
    (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordD 6 (2 ^ f)])
    (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_E7
      (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordD 6 (2 ^ f)])
      (fun α z h => h.map α) _
      (xPar_e7HighRoot_typedBy hK _) j) hγ' (xPar_mem hγ' _) hz1

end E7Iso

end Isogeny

section TwE6Base

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]


theorem stdRepC_zero_typedBy [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    GGRootCentQLTypedBy (stdRepC (apply_apply_eq hK hσ) 0 : graphFixedRootGroup TwistTag.E6 K σ)
      [CFSG.Open.ordTwistedA 5 (2 ^ f)] := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  have hC := centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
  obtain ⟨-, hLN, -⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  have hQ2 : IsPGroup 2 ((tRadical σ).subgroupOf C₀) := by
    obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
    obtain ⟨S, hS⟩ := hT.2.2.2.2.2.2.2.2.2.1
    refine S.isPGroup'.to_le ?_
    rw [hS]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hx).1,
      graphFixedRootGroup_le _ _ _ x.2⟩
  have hLN' : (su6Levi σ).subgroupOf C₀ ≤ normalizer ((tRadical σ).subgroupOf C₀ : Set C₀) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 (hLN hx) y
  exact ⟨_, _, hQ2, hC.symm, hLN', isChevTwoLayeredBy_su6Levi_subgroupOf hf hk hK hσ⟩

theorem pinnedX_highRoot_twE6_typedBy [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {c : K}
    (hc : c ≠ 0) (hcσ : σ c = c)
    (hmem : pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    GGRootCentQLTypedBy (⟨_, hmem⟩ : graphFixedRootGroup TwistTag.E6 K σ)
      [CFSG.Open.ordTwistedA 5 (2 ^ f)] := by
  have : Finite K := finite_of_card hK
  obtain ⟨h, hh, -, hconj⟩ := exists_twistedE6_torus_conj_frame_prod σ
    (F := [e6HighestRoot]) (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨isRoot_e6HighestRoot, permLattice_e6HighestRoot⟩)
    (List.pairwise_singleton _ _) (fun _ => c) (fun γ _ => ⟨hc, hcσ⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hconj
  have e : (⟨h, hh⟩ : graphFixedRootGroup TwistTag.E6 K σ) * ⟨_, hmem⟩ * ⟨h, hh⟩⁻¹ =
      stdRepC (apply_apply_eq hK hσ) 0 := Subtype.ext hconj
  have h1 := stdRepC_zero_typedBy (k := k) hf hk hK hσ
  rw [← e] at h1
  exact h1.of_conj

end TwE6Base

section TwE6Tag


theorem derivedAt_twE6_typedBy {f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (ψ : twistedE6Group 2 f →* X) (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥) {u z : twistedE6Group 2 f}
    (hz1 : ψ (u * z * u⁻¹) ≠ 1)
    (hzx : ∃ (x : twistedE6Group 2 f) (c : GaloisField 2 (2 * f)), frobQ 2 f c = c ∧
      ((x⁻¹ * z * x : twistedE6Group 2 f) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    ∃ (C : Type) (_ : Group C) (π : twistedE6Group 2 f →* C) (w : twistedE6Group 2 f),
      Function.Surjective π ∧ π.ker = ψ.ker ∧ ψ w = ψ (u * z * u⁻¹) ∧
        GGRootCentQLTypedBy (π w) [CFSG.Open.ordTwistedA 5 (2 ^ f)] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    rw [← hσθ]
    exact hder
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπker : π.ker = ψ.ker := by
    rw [AutSt.ker_eq_center hker hC]
    refine le_antisymm (RootDetectTwE6.ker_le_center f π hπvalT) fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc := RootCentExc.map_mem_center_of_surjective hπ hz
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  obtain ⟨x, c, hcθ, hc⟩ := hzx
  have hπz : ((π (x⁻¹ * z * x) : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c := by
    rw [hπvalT, hc]
    change ((e6Isogeny (GaloisField 2 (2 * f)) (e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
      adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) =
        pinnedX .E6 (GaloisField 2 (2 * f)) RootCentExc.e6HighRoot c
    rw [e6Isogeny_xm _ RootCentExc.isRoot_e6HighRoot, yPar,
      RootCentExc.coe_xPar_eq_pinnedX h2 _ RootCentExc.isRoot_e6HighRoot]
    have hδ : (relSignOr (rootOperatorFamily .E6) e6AdjData_valid RootCentExc.e6HighRoot :
        GaloisField 2 (2 * f)) = 1 := by
      have hm := relSignOr_mul_self (F := rootOperatorFamily .E6) (hD := e6AdjData_valid)
        (k := GaloisField 2 (2 * f)) RootCentExc.e6HighRoot
      set ε := (relSignOr (rootOperatorFamily .E6) e6AdjData_valid RootCentExc.e6HighRoot :
        GaloisField 2 (2 * f))
      have h' : (ε - 1) ^ 2 = 0 := by linear_combination hm + (1 - ε) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
    rw [hδ, one_mul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : x⁻¹ * z * x = 1 := Subtype.ext (by rw [hc, MinData.Valid.xm_zero]; rfl)
    have hz1' : z = 1 := by
      calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [hz1', mul_one, mul_inv_cancel, map_one] at hz1
    exact hz1 rfl
  have hcσ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom c = c := by
    rw [hσθ]
    exact hcθ
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  let _ : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := ι.toAlgebra
  have hmem := (π (x⁻¹ * z * x)).2
  rw [hπz] at hmem
  have hcent := pinnedX_highRoot_twE6_typedBy (k := GaloisField 2 f) hf hk hK
    (σ := (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom) hσ hc0 hcσ hmem
  have he : (⟨_, hmem⟩ : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) = π (x⁻¹ * z * x) :=
    Subtype.ext hπz.symm
  rw [he] at hcent
  have hw := hcent.conj (π (u * x))
  have e : π (u * x) * π (x⁻¹ * z * x) * (π (u * x))⁻¹ = π (u * z * u⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [e] at hw
  exact ⟨_, inferInstance, π, u * z * u⁻¹, hπ, hπker, rfl, hw⟩

end TwE6Tag

section TagTheorems

section TagF4


theorem ggRootInvolModelCountTag_F4 : GGRootInvolModelCountTag .F4 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQLTypedBy z [CFSG.Open.ordBC 3 (2 ^ f)] :=
    RootCentQLTyped.of_mem_rootGroup
      (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordBC 3 (2 ^ f)])
      (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_F4
        (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordBC 3 (2 ^ f)])
        (fun α z h => h.map α) _
        (xPar_f4HighRoot_typedBy hK _) j) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .F4 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  exact ⟨_, inferInstance, MonoidHom.id _, u * z * u⁻¹, Function.surjective_id,
    hker', rfl, [CFSG.Open.ordBC 3 (2 ^ f)], by simp [ggRootFactorOrders], hcz.conj u⟩

theorem ggRootInvolCountTag_F4 : GGRootInvolCountTag .F4 :=
  ggRootInvolCountTag_of_modelCount ggRootInvolModelCountTag_F4

end TagF4

section TagE6


theorem ggRootInvolModelCountTag_E6 : GGRootInvolModelCountTag .E6 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := e6Isogeny_qL_typedBy hK hγ hz hz1
  have e : e6Isogeny (GaloisField 2 f) (u * z * u⁻¹) =
      e6Isogeny (GaloisField 2 f) u * e6Isogeny (GaloisField 2 f) z *
        (e6Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  have hcz' : GGRootCentQLTypedBy (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹))
      [CFSG.Open.ordA 5 (2 ^ f)] := by
    have h := hcz.conj (e6Isogeny (GaloisField 2 f) u)
    rwa [← e] at h
  exact ⟨_, inferInstance, e6Isogeny (GaloisField 2 f), u * z * u⁻¹,
    e6Isogeny_surjective _, hπker, rfl, [CFSG.Open.ordA 5 (2 ^ f)],
    by simp [ggRootFactorOrders], hcz'⟩

theorem ggRootInvolCountTag_E6 : GGRootInvolCountTag .E6 :=
  ggRootInvolCountTag_of_modelCount ggRootInvolModelCountTag_E6

end TagE6

section TagE7


theorem ggRootInvolModelCountTag_E7 : GGRootInvolModelCountTag .E7 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e7Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e7Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := e7Isogeny_qL_typedBy hK hγ hz hz1
  have e : e7Isogeny (GaloisField 2 f) (u * z * u⁻¹) =
      e7Isogeny (GaloisField 2 f) u * e7Isogeny (GaloisField 2 f) z *
        (e7Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  have hcz' : GGRootCentQLTypedBy (e7Isogeny (GaloisField 2 f) (u * z * u⁻¹))
      [CFSG.Open.ordD 6 (2 ^ f)] := by
    have h := hcz.conj (e7Isogeny (GaloisField 2 f) u)
    rwa [← e] at h
  exact ⟨_, inferInstance, e7Isogeny (GaloisField 2 f), u * z * u⁻¹,
    e7Isogeny_surjective _, hπker, rfl, [CFSG.Open.ordD 6 (2 ^ f)],
    by simp [ggRootFactorOrders], hcz'⟩

theorem ggRootInvolCountTag_E7 : GGRootInvolCountTag .E7 :=
  ggRootInvolCountTag_of_modelCount ggRootInvolModelCountTag_E7

end TagE7

section TagE8


theorem ggRootInvolModelCountTag_E8 : GGRootInvolModelCountTag .E8 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQLTypedBy z [CFSG.Open.ordE7 (2 ^ f)] :=
    RootCentQLTyped.of_mem_rootGroup
      (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordE7 (2 ^ f)])
      (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_E8
        (P := fun z => GGRootCentQLTypedBy z [CFSG.Open.ordE7 (2 ^ f)])
        (fun α z h => h.map α) _
        (xPar_e8HighRoot_typedBy hK _) j) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .E8 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm
  exact ⟨_, inferInstance, MonoidHom.id _, u * z * u⁻¹, Function.surjective_id,
    hker', rfl, [CFSG.Open.ordE7 (2 ^ f)], by simp [ggRootFactorOrders], hcz.conj u⟩

theorem ggRootInvolCountTag_E8 : GGRootInvolCountTag .E8 :=
  ggRootInvolCountTag_of_modelCount ggRootInvolModelCountTag_E8

end TagE8

section TagTwE6


theorem ggRootInvolModelCountTag_twistedE6 : GGRootInvolModelCountTag .twistedE6 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨hr2, γ, ⟨hγ, hlong⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  obtain ⟨w, γ₀, hγ₀, hmax, hγw⟩ := hlong (Or.inr (Or.inr rfl))
  have hγ₀' : IsRoot .F4 γ₀ := isRoot_of_mem_twistedDatum_roots _ hγ₀
  have hγ₀eq : γ₀ = RootCentExc.f4HighRoot := RootCentExc.eq_f4HighRoot_of_le hγ₀'
    (hmax RootCentExc.f4HighRoot (by
      change RootCentExc.f4HighRoot ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots
      rw [twistedDatum_roots]
      exact RootCentExc.isRoot_f4HighRoot))
  subst hγ₀eq
  subst hγw
  have hz1 : ψ (u * z * u⁻¹) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨C, _, π, w', hπ, hπker, hw, htyped⟩ := derivedAt_twE6_typedBy hf ψ hker hC hz1
    (RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz)
  exact ⟨C, inferInstance, π, w', hπ, hπker, hw, [CFSG.Open.ordTwistedA 5 (2 ^ f)],
    by simp [ggRootFactorOrders], htyped⟩

theorem ggRootInvolCountTag_twistedE6 : GGRootInvolCountTag .twistedE6 :=
  ggRootInvolCountTag_of_modelCount ggRootInvolModelCountTag_twistedE6

end TagTwE6

end TagTheorems

end CFSG.StandardType
