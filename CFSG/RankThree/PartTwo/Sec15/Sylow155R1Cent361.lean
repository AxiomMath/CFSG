module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLFTools
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentE9
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentIdx
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentSL2
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentFit
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentUB
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentWeights
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped commutatorElement

@[expose] def Res1Thm150b (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    ∀ j ∈ res1J A X Y M z, j ≠ 1 →
      ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({j} : Set G))).map (Subgroup.centralizer ({j} : Set G)).subtype

@[expose] def Res1Lem154 (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    IsMulCommutative ↥(CFSG.Open.pCoreOf 2 Y)

@[expose] def Res1QE9 (Q : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z], Q Z →
    IsSimpleGroup Z ∧ ∃ E : Subgroup Z, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9

variable {G : Type} [Group G] [Finite G]

private theorem res1Cent361_normalizer_le_normalizer_pCoreOf (p : ℕ) (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p H : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map ((MulAut.conj h).toMonoidHom) ((CFSG.pCore p ↥H).map H.subtype) =
    (CFSG.pCore p ↥H).map H.subtype
  let α : MulAut ↥H := H.normalizerMonoidHom ⟨h, hh⟩
  have hcomp : H.subtype.comp α.toMonoidHom = (MulAut.conj h).toMonoidHom.comp H.subtype := by
    ext y
    simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map,
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) α]

private theorem res1Cent361_le_normalizer_map (H : Subgroup G) (N : Subgroup ↥H) [N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨h, hh⟩ * a * ⟨h, hh⟩⁻¹, ‹N.Normal›.conj_mem a ha _, ?_⟩
    simp
  · rintro ⟨a, ha, hag⟩
    refine ⟨⟨h, hh⟩⁻¹ * a * ⟨h, hh⟩, ?_, ?_⟩
    · simpa using ‹N.Normal›.conj_mem a ha ⟨h, hh⟩⁻¹
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hag ⊢
      rw [hag]
      group

private theorem res1Cent361_eq_bot_of_le_pCoreOf {L : Subgroup G} [Group.IsPerfect L]
    (hL : L ≤ CFSG.Open.pCoreOf 2 L) : L = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have := Sec11.TwoStarProof.eq_one_of_perfect_of_mem_pGroup L.subtype hp
    (fun y => hL y.2) ⟨x, hx⟩
  exact this

private theorem res1Cent361_theta_facts (H : Subgroup G) :
    Group.IsSolvable ↥((aschbacherSolvableCore 3 ↥H).map H.subtype) ∧
      ¬ 3 ∣ Nat.card ↥((aschbacherSolvableCore 3 ↥H).map H.subtype) ∧
      (aschbacherSolvableCore 3 ↥H).map H.subtype ≤ H ∧
      H ≤ Subgroup.normalizer
        (((aschbacherSolvableCore 3 ↥H).map H.subtype : Subgroup G) : Set G) := by
  obtain ⟨hsol, hchar, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three
  haveI := hsol
  haveI := hchar
  refine ⟨solvable_of_surjective (H.subtype.subgroupMap_surjective _), ?_,
    Subgroup.map_subtype_le _, res1Cent361_le_normalizer_map H _⟩
  rwa [Subgroup.card_map_of_injective H.subtype_injective]

theorem res1QE9_a7 : Res1QE9 (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) := by
  intro Z _ ⟨e⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact ⟨e.isSimpleGroup,
    res1Cent_exists_e9_of_mulEquiv e res1Cent_exists_e9_alternatingGroup_seven⟩

theorem res1QE9_m22 :
    Res1QE9 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) := by
  intro Z _ ⟨e⟩
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  exact ⟨e.isSimpleGroup, res1Cent_exists_e9_of_mulEquiv e res1Cent_exists_e9_m22⟩

namespace Res1Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

theorem x_le_centralizer_of_mem_j (h149 : Item149 A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) {j : G} (hj : j ∈ res1J A X Y M z) :
    X ≤ Subgroup.centralizer ({j} : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => by
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp (τ.x_le_centralizer_ob h149 hx)) j (τ.j_le_ob hj)

theorem isPerfect_l (τ : Res1Tau Q P A c L X K Y M T P' Yc z) : Group.IsPerfect L :=
  Sec6.isPerfect_of_mem_thetaComponentsAt τ.std.mem_lA.1

theorem pCoreOf_x_le (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 Y := by
  have hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y := by
    have h := τ.ctx.isY.2.2
    rwa [τ.ctx.res] at h
  have hXY : X ≤ Y := hY ▸ le_sup_left
  exact pCoreOf_le_pCoreOf_of_le_sup hXY hY.le

theorem isMulCommutative_pCoreOf_x (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (h154 : IsMulCommutative ↥(CFSG.Open.pCoreOf 2 Y)) :
    IsMulCommutative ↥(CFSG.Open.pCoreOf 2 X) := by
  have hle := τ.pCoreOf_x_le
  have hc : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr h154
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  exact hle.trans (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))

theorem isPerfect_quot (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have h := τ.ctx.isY.2.1
  rw [τ.ctx.res] at h
  exact h.2.2.2.1

theorem not_le_centralizer (h149 : Item149 A (lB A)) (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hL : L ≠ ⊥) : ¬ L ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) := by
  intro hLC
  haveI := τ.isPerfect_l
  have hchar := (isCharacteristicP_x_and_pCoreOf_ne_bot τ.std h149 τ.ctx τ.i_le).1
  exact hL (res1Cent361_eq_bot_of_le_pCoreOf
    ((le_inf le_rfl hLC).trans (inf_centralizer_le_pCoreOf hchar τ.l_le)))

theorem pCoreOf_centralizer_ne_bot (h149 : Item149 A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hQ : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      ∃ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (h154 : IsMulCommutative ↥(CFSG.Open.pCoreOf 2 Y)) {j : G} (hj : j ∈ res1J A X Y M z)
    (h150 : ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({j} : Set G))).map (Subgroup.centralizer ({j} : Set G)).subtype) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) ≠ ⊥ := by
  classical
  intro hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := τ.isPerfect_l
  set Yj := Subgroup.centralizer ({j} : Set G) with hYj
  set Γ := (aschbacherSolvableCore 3 ↥Yj).map Yj.subtype with hΓ
  set U := CFSG.Open.pCoreOf 2 X with hU
  obtain ⟨hΓsol, hΓ3, hΓYj, hYjΓ⟩ := res1Cent361_theta_facts Yj
  have hXYj : X ≤ Yj := τ.x_le_centralizer_of_mem_j h149 hj
  have hΓ2 : CFSG.Open.pCoreOf 2 Γ = ⊥ :=
    le_bot_iff.mp (hbot ▸ CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hΓYj hYjΓ)
  have hLne : L ≠ ⊥ := by
    haveI := hQ.1
    exact (Subgroup.nontrivial_iff_ne_bot L).mp
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L)).nontrivial
  have hUp : IsPGroup 2 U := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hUX : U ≤ X := Subgroup.map_subtype_le _
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer.trans (res1Cent361_normalizer_le_normalizer_pCoreOf 2 X)
  have hUc : IsMulCommutative ↥U := τ.isMulCommutative_pCoreOf_x h154
  have hLU : ¬ L ≤ Subgroup.centralizer (U : Set G) := τ.not_le_centralizer h149 hLne
  have hLUU : ⁅L, U⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro l hl u hu
    have hconj : l * u * l⁻¹ ∈ U :=
      ((Subgroup.mem_normalizer_iff.mp (hXU (τ.l_le hl))) u).mp hu
    rw [commutatorElement_def]
    exact U.mul_mem hconj (U.inv_mem hu)
  obtain ⟨p, hp, hp5, hLS⟩ := res1Cent_exists_prime_not_le_centralizer hΓsol hΓ2 hΓ3
    (hUX.trans (hXYj.trans hYjΓ)) h150
    (fun h => hLU (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)) (hUp.to_le hLUU)
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : IsPGroup p (CFSG.Open.pCoreOf p Γ) :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥Γ)).map Γ.subtype
  have hXS : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p Γ : Set G) :=
    hXYj.trans (hYjΓ.trans (res1Cent361_normalizer_le_normalizer_pCoreOf p Γ))
  obtain ⟨n, ρ, hubX, hact⟩ := res1Cent_exists_ub_rep (by omega : p ≠ 2)
    (τ.std.toTheoremFourHyp.localRank_lt p hp (by omega)) hS hXS
  have hmoveS : ∃ x ∈ L, ∃ s ∈ CFSG.Open.pCoreOf p Γ, x * s * x⁻¹ ≠ s := by
    by_contra hcon
    push Not at hcon
    refine hLS fun x hx => Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    have h := hcon x hx s hs
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  obtain ⟨x0, hx0L, hx0⟩ := hact L τ.l_le τ.isPerfect_l hmoveS
  obtain ⟨hNsol, -, hN3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨E, hE, hE9⟩ := res1Cent_exists_e9_lift (aschbacherSolvableCore 3 ↥L) hN3 hQ.2
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hn : ¬ Module.finrank (ZMod p) (Fin n → ZMod p) ≤ 2 := by
    intro hV
    have hD := res1Cent_rho_eq_one_of_finrank_le_two (L := ↥L)
      (N := aschbacherSolvableCore 3 ↥L) hNsol hN3 hQ.1 hE hE9 h3 hV
      (ρ.comp (Subgroup.inclusion τ.l_le)) ⟨x0, hx0L⟩
    have hx : Subgroup.inclusion τ.l_le ⟨(x0 : G), hx0L⟩ = x0 := Subtype.ext rfl
    rw [MonoidHom.comp_apply, hx] at hD
    exact hx0 hD
  set U1 := Subgroup.closure {u | u ∈ U ∧ u ^ 2 = 1} with hU1
  have hU1U : U1 ≤ U := (Subgroup.closure_le _).mpr fun u hu => hu.1
  have hU1X : U1 ≤ X := hU1U.trans hUX
  have hXU1 : X ≤ Subgroup.normalizer (U1 : Set G) := res1Cent_le_normalizer_closure_sq hXU
  haveI : (U1.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU1X).mpr hXU1
  have hLU1 : ¬ L ≤ Subgroup.centralizer (U1 : Set G) := by
    intro hc
    refine hLU (res1Cent_le_centralizer_of_sq hUp hUc (τ.l_le.trans hXU)
      fun l hl u hu hu2 => ?_)
    have h := Subgroup.mem_centralizer_iff.mp (hc hl) u (Subgroup.subset_closure ⟨hu, hu2⟩)
    rw [← h, mul_inv_cancel_right]
  have hU2 : ∀ u ∈ U1.subgroupOf X, u ^ 2 = 1 := fun u hu =>
    Subtype.ext (res1Cent_mem_closure_sq hUc (Subgroup.mem_subgroupOf.mp hu)).2
  have hU8 : 8 ≤ Nat.card ↥(U1.subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU1X).toEquiv]
    exact res1Cent_eight_le_card (hUp.to_le hU1U)
      fun h => hLU1 (res1Cent_le_centralizer_of_card_le_four (τ.l_le.trans hXU1) h)
  have hcU : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hUc
  have hPC : CFSG.pCore 2 ↥X ≤ Subgroup.centralizer ((U1.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyU : (y : G) ∈ U := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hcU hyU) u (hU1U (Subgroup.mem_subgroupOf.mp hu)))
  haveI := τ.isPerfect_quot
  have hidx : ∀ H : Subgroup ↥X,
      Subgroup.centralizer ((U1.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤ H → H.index < 5 →
        H = ⊤ := fun H hH h5 => res1Cent_eq_top_of_index_lt_five (hPC.trans hH) h5
  have hub : ∀ s ∈ U1.subgroupOf X, s ≠ 1 →
      Module.finrank (ZMod p) (LinearMap.ker (ρ s - 1)) ≤ 2 := fun s hs hs1 =>
    hubX s hs1 ⟨1, by rw [pow_one]; exact hU2 s hs⟩
  have hne : ∃ u ∈ U1.subgroupOf X, ∃ x : ↥X, ⁅u, x⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hLU1 fun l hl => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h := hcon ⟨u, hU1X hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨l, τ.l_le hl⟩
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact congrArg Subtype.val h
  exact hn (res1Cent_finrank_le_two h2 ρ hU2 hU8 hidx hub hne)

end Res1Tau

theorem res1Thm361_of (h149 : Sec16.Item149S14) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop} (hQ : Res1QE9 Q) (h150 : Res1Thm150b Q P)
    (h154 : Res1Lem154 Q P) : Res1Thm361 Q P := by
  intro G _ _ A c L X K Y M T P' Yc z τ j hj hj1
  exact τ.pCoreOf_centralizer_ne_bot (h149 G A c L τ.std) (hQ _ τ.q)
    (h154 G A c L X K Y M T P' Yc z τ) hj (h150 G A c L X K Y M T P' Yc z τ j hj hj1)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
