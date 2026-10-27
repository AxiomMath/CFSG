module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofF4
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofGroup
import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.LieType.Ree

namespace Res4Seven

theorem le_perfectResidual_of_isPerfect {Γ : Type} [Group Γ] {L : Subgroup Γ}
    (hL : Group.IsPerfect L) : L ≤ perfectResidual Γ := by
  have h : ∀ n : ℕ, L ≤ derivedSeries Γ n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc L = ⁅L, L⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅derivedSeries Γ n, derivedSeries Γ n⁆ := Subgroup.commutator_mono ih ih
  exact le_iInf h

theorem not_hasType424_of_perfectResidual {Γ : Type} [Group Γ] [Finite Γ]
    (hN : IsQuasisimple (perfectResidual Γ))
    (hx : ∃ x ∈ perfectResidual Γ, (∀ n ∈ perfectResidual Γ, x * n = n * x) ∧ x ≠ 1 ∧
      x ^ 3 = 1) :
    ¬ Sec11.KS11Lie2Proof.HasType424 Γ := by
  rintro ⟨L, ⟨hLp, hLsn, hLq⟩, hT⟩
  set N := perfectResidual Γ with hNdef
  have hLN : L ≤ N := le_perfectResidual_of_isPerfect hLp
  have hsn : (L.subgroupOf N).IsSubnormal := hLsn.comap N.subtype
  have hNL : N ≤ L := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsn with
      htop | hcen
    · intro y hy
      have : (⟨y, hy⟩ : N) ∈ L.subgroupOf N := htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hLp' : Group.IsPerfect (L.subgroupOf N) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLN).symm.toMonoidHom)
          (MulEquiv.surjective _)
      have hbot := Sec11.KS11Lie4Proof.eq_bot_of_isPerfect_of_le_center hLp' hcen
      have hall : ∀ w : L, w = 1 := fun w => by
        have hw : (⟨w, hLN w.2⟩ : N) ∈ L.subgroupOf N := w.2
        rw [hbot, Subgroup.mem_bot] at hw
        exact Subtype.ext (by simpa using congrArg Subtype.val hw)
      obtain ⟨u, v, huv⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hLq).exists_pair_ne
      obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
      rw [hall u', hall v'] at huv
      exact huv rfl
  obtain ⟨x, hxN, hxc, hx1, hx3⟩ := hx
  have hxθ := Sec11.KS11Lie2Proof.mem_theta_of_central hT (hNL hxN)
    (fun k hk => hxc k (hLN hk))
  obtain ⟨⟨u, hu⟩, huθ, hue⟩ := hxθ
  have hu' : (⟨u, hu⟩ : L) = ⟨x, hNL hxN⟩ := Subtype.ext hue
  rw [hu'] at huθ
  have h1 := Sec11.eq_one_of_mem_theta_of_pow_eq_one huθ (k := 1)
    (Subtype.ext (by simpa using hx3))
  exact hx1 (congrArg Subtype.val h1)

theorem InnerConfig424.orderOf_c {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X}
    {K : Subgroup X} (h : InnerConfig424 X D c d K) : orderOf c = 3 :=
  orderOf_eq_prime (h.maximal.prop.2 c h.c_mem) h.c_ne_one

noncomputable def centralizerMapEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (c : X) :
    Subgroup.centralizer ({c} : Set X) ≃* Subgroup.centralizer ({φ c} : Set Y) :=
  ((Subgroup.centralizer ({c} : Set X)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h' := congrArg φ h
        simpa using h'
      · intro h
        apply φ.injective
        simpa using h))

noncomputable def perfectResidualEquivIn {Y : Type} [Group Y] (H : Subgroup Y) :
    perfectResidual H ≃* inSubgroup perfectResidual H :=
  (perfectResidual H).equivMapOfInjective H.subtype H.subtype_injective

theorem statedSU_three_facts {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hodd : Odd f) :
    IsQuasisimple (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F) ∧
      ∃ x : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F,
        x ∈ Subgroup.center _ ∧ x ≠ 1 ∧ x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hq, -⟩ := Sec8.Item87Proof.isQuasisimple_statedSU_three hF hf
  refine ⟨hq, ?_⟩
  have hnq : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h' : 2 ^ f = 2 := (Prod.mk.inj h).2
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF le_rfl hnq
  have hZc : Nat.card (Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F)) = 3 := by
    rw [hZ, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (by norm_num)).2.2]
    have h3 : 3 ∣ 2 ^ f + 1 := Res417Six.three_dvd_two_pow_add_one hodd
    exact Nat.gcd_eq_left h3
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center _) 3 (by rw [hZc])
  refine ⟨z, z.2, ?_, ?_⟩
  · intro h1
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    norm_num at hz
  · have h3 := pow_orderOf_eq_one z
    rw [hz] at h3
    exact congrArg Subtype.val h3

theorem census424_of_twistedF4
    (hR : Sec8.ReeF4OrderThreeConj) {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) : Census424 X := by
  intro D c d J h
  exfalso
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨ψ⟩⟩ := exists_mulEquiv_reeGamma hX
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv X ψ.toEquiv
  have hc3 := InnerConfig424.orderOf_c h
  have hψc : orderOf (ψ c) = 3 := by rw [MulEquiv.orderOf_eq]; exact hc3
  obtain ⟨K', _, _, hK', ⟨φ⟩⟩ :=
    Sec8.ReeF4Cent2Proof.kF83ReeCentThree_of_orderThreeConj hR a K ha hK (ψ c) hψc
  set H := Subgroup.centralizer ({ψ c} : Set (ReeTag.F4.reeGamma K a)) with hHdef
  have hHas : Sec11.KS11Lie2Proof.HasType424 (Subgroup.centralizer ({c} : Set X)) :=
    Sec11.KS11Lie2Proof.hasType424_of_mem h.mem_thetaComponentsIn h.isType424
  have hHasH : Sec11.KS11Lie2Proof.HasType424 H :=
    hHas.of_mulEquiv (centralizerMapEquiv ψ c)
  have hf : 2 ≤ 2 * a + 1 := by omega
  obtain ⟨hq, x, hxZ, hx1, hx3⟩ := statedSU_three_facts hK' hf ⟨a, rfl⟩
  let E : perfectResidual H ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (2 * a + 1)) K' :=
    (perfectResidualEquivIn H).trans φ
  refine not_hasType424_of_perfectResidual
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv E.symm hq) ?_ hHasH
  refine ⟨(E.symm x : H), (E.symm x).2, fun n hn => ?_, ?_, ?_⟩
  · have hc := Subgroup.mem_center_iff.mp hxZ (E ⟨n, hn⟩)
    have h2 : E.symm x * (⟨n, hn⟩ : perfectResidual H) =
        (⟨n, hn⟩ : perfectResidual H) * E.symm x := by
      apply E.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc.symm
    exact congrArg Subtype.val h2
  · intro h1
    apply hx1
    have h2 : E.symm x = 1 := Subtype.ext h1
    simpa using congrArg E h2
  · have h2 : (E.symm x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    exact congrArg Subtype.val h2

theorem census424_of_tits (hT3 : Res417Six.K417TitsCentThree) {X : Type} [Group X] [Finite X]
    {f : ℕ} (hX : ReeTitsModel X .Tits 2 f) : Census424 X := by
  intro D c d J h
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 := InnerConfig424.orderOf_c h
  obtain ⟨P, hP3, hCP, hPall⟩ := hT3 X f hX c hc3
  have hJC : J ≤ Subgroup.centralizer ({c} : Set X) :=
    (mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn).1
  have hq := Item424Proof.isQuasisimple_of_mem_thetaComponentsIn h.mem_thetaComponentsIn
  have hZ := Sec11.FieldCentRigid82.center_eq_bot_of_isType424 h.isType424
  set Q := J ⧸ aschbacherSolvableCore 3 J with hQdef
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 J) with hπdef
  set M : Subgroup J := P.subgroupOf J with hMdef
  have hMn : M.Normal := by
    refine ⟨fun m hm j => ?_⟩
    rw [hMdef, Subgroup.mem_subgroupOf] at hm ⊢
    have hjN := hCP (hJC j.2)
    simpa using (Subgroup.mem_normalizer_iff.mp hjN (m : X)).mp hm
  have hMbar : (M.map π).Normal := Subgroup.Normal.map hMn π (QuotientGroup.mk'_surjective _)
  have hM3 : IsPGroup 3 M := hP3.comap_subtype
  have h3Q : 3 ∣ Nat.card Q := Item424Proof.three_dvd_card_of_isType424 h.isType424
  have h3J : 3 ∣ Nat.card J := h3Q.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 h3J
  have hy3 := pow_orderOf_eq_one y
  rw [hy] at hy3
  have hyP : (y : X) ∈ P := hPall y (hJC y.2) (by simpa using congrArg Subtype.val hy3)
  have hyM : y ∈ M := by rw [hMdef, Subgroup.mem_subgroupOf]; exact hyP
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq
      hMbar.isSubnormal with htop | hcen
  ·
    have hQ3 : IsPGroup 3 Q := by
      intro u
      have hu : u ∈ M.map π := htop ▸ Subgroup.mem_top u
      obtain ⟨m, hm, rfl⟩ := hu
      obtain ⟨k, hk⟩ := hM3 ⟨m, hm⟩
      refine ⟨k, ?_⟩
      have hk' : m ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow, hk', map_one]
    have : Group.IsNilpotent Q := hQ3.isNilpotent
    have hQs : Group.IsSolvable Q := inferInstance
    have hQp : Group.IsPerfect Q := hq.1
    obtain ⟨u, v, huv⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hq).exists_pair_ne
    have hbot := Sec11.KS11Lie4Proof.eq_bot_of_isPerfect_of_isSolvable (Z := Q)
      (J := ⊤) (Group.IsPerfect.ofSurjective (f := Subgroup.topEquiv.symm.toMonoidHom)
        (MulEquiv.surjective _)) (Group.isSolvable_of_isSolvable_injective
          (f := (⊤ : Subgroup Q).subtype) (Subgroup.subtype_injective _))
    apply huv
    have hu : u ∈ (⊥ : Subgroup Q) := hbot ▸ Subgroup.mem_top u
    have hv : v ∈ (⊥ : Subgroup Q) := hbot ▸ Subgroup.mem_top v
    rw [Subgroup.mem_bot] at hu hv
    rw [hu, hv]
  ·
    have hyZ : π y ∈ Subgroup.center Q := hcen ⟨y, hyM, rfl⟩
    rw [hZ, Subgroup.mem_bot, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hyZ
    have h1 := Sec11.eq_one_of_mem_theta_of_pow_eq_one hyZ (k := 1) (by simpa using hy3)
    rw [h1, orderOf_one] at hy
    norm_num at hy

end Res4Seven

end CFSG.RankThree.PartTwo.Sec4
