module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4SzAbs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4L2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem isQuasisimple_of_simple_of_perfect (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : commutator S = ⊤) : CFSG.Open.IsQuasisimple S := by
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
        have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm
      have hbot : commutator S = ⊥ := by
        apply le_bot_iff.mp
        apply Subgroup.commutator_le.mpr
        intro x _ y _
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x y)
      rw [hbot] at hperf
      have hx : ∀ x : S, x = 1 := fun x => Subgroup.mem_bot.mp (hperf ▸ Subgroup.mem_top x)
      obtain ⟨a, b, hab⟩ := exists_pair_ne S
      exact hab ((hx a).trans (hx b).symm)
  refine ⟨hperf, ?_⟩
  have e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup_congr.mpr inferInstance

theorem isPerfect_of_mulEquiv_829 {A B : Type} [Group A] [Group B] (e : A ≃* B)
    [hA : Group.IsPerfect A] : Group.IsPerfect B := by
  rw [Group.isPerfect_def] at hA ⊢
  have h1 : (commutator A).map e.toMonoidHom = commutator B := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  rw [hA] at h1
  rw [← h1]
  exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

theorem isPerfect_subgroupOf {G : Type} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (hK : ⁅K, K⁆ = K) : Group.IsPerfect ↥(K.subgroupOf H) := by
  have hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  exact isPerfect_of_mulEquiv_829 (Subgroup.subgroupOfEquivOfLe hKH).symm

theorem not_isMulCommutative_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : ¬ IsMulCommutative A) : ¬ IsMulCommutative B := fun hB => hA (by
  refine isMulCommutative_iff.mpr fun a b => ?_
  apply e.injective
  rw [map_mul, map_mul]
  exact isMulCommutative_iff.mp hB (e a) (e b))

theorem conjSub_mulEquiv {Ĥ : Type} [Group Ĥ] (t : Ĥ) (L : Subgroup Ĥ) :
    Nonempty (↥L ≃* ↥(B6.conjSub t L)) :=
  ⟨Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective⟩

theorem nonsolvable_structure_J {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
    (hmin : MinParabolic H T M) (hns : ¬ Group.IsSolvable ↥H) (J : Subgroup ↥H) [J.Normal]
    (hJ : kerIn (M.subgroupOf H) ⊤ = J) :
    ∃ L : Subgroup (↥H ⧸ J), IsSimpleGroup ↥L ∧ ¬ IsMulCommutative ↥L ∧
      L ≤ (twoResidual (⊤ : Subgroup ↥H)).map (QuotientGroup.mk' J) ∧
      (twoResidual (⊤ : Subgroup ↥H)).map (QuotientGroup.mk' J) =
        (⨆ t ∈ (T.subgroupOf H).map (QuotientGroup.mk' J), B6.conjSub t L) ∧
      ∀ t ∈ (T.subgroupOf H).map (QuotientGroup.mk' J),
        ((B6.conjSub t L).subgroupOf
          ((twoResidual (⊤ : Subgroup ↥H)).map (QuotientGroup.mk' J))).Normal := by
  subst hJ
  obtain ⟨L, h1, h2, h3, h4, -, h6, -, -⟩ :=
    CFSG.Quasithin.MinParabolic.nonsolvable_structure hmin.subgroupOf hns
  exact ⟨L, h1, h2, h3, h4, h6⟩

theorem not_surv1a_sz {G : Type} [Group G] [Finite G] {H T M K : Subgroup G}
    (hmin : MinParabolic H T M) (hns : ¬ Group.IsSolvable ↥H)
    (hKc : K ∈ cComp H) (hJ : kerIn M H = pCoreOf 2 H)
    (h3 : 3 ∣ Nat.card (E2.StarQuot M H)) {n : ℕ} (hSz : IsSz n (E2.star M H K)) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hodd : Odd n := by
    obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := hSz
    exact ⟨a, by omega⟩
  have hsimpK : IsSimpleGroup ↥(E2.star M H K) :=
    CFSG.Quasithin.isSimpleGroup_of_psl2_or_sz (Or.inr hSz)
  have h3K : ¬ 3 ∣ Nat.card ↥(E2.star M H K) := not_three_dvd_sz_odd hSz hodd
  have hNX : kerIn M H ≤ H := by
    rw [hJ]
    exact Subgroup.map_subtype_le _
  have hJsolv : Group.IsSolvable ↥(kerIn M H) := by
    have hp : IsPGroup 2 ↥(pCoreOf 2 H) := by
      intro g
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨x, hx⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : x ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxg, ← map_pow, hk', map_one]
    have hnil : Group.IsNilpotent ↥(pCoreOf 2 H) := hp.isNilpotent
    rw [hJ]
    exact inferInstance
  have hbij := cComp_quotient_bijOn_of_le hNX (by infer_instance) hJsolv
  set A : Subgroup (E2.StarQuot M H) := E2.star M H K with hAdef
  have hAc : A ∈ cComp (⊤ : Subgroup (E2.StarQuot M H)) := hbij.mapsTo hKc
  have hAperf : ⁅A, A⁆ = A := perfect_of_mem_cComp hAc
  have hAq : CFSG.Open.IsQuasisimple ↥A := by
    have hp : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hAperf
    exact isQuasisimple_of_simple_of_perfect ↥A (Group.isPerfect_def.mp hp)
  have hAcomp : IsComponentOf A (⊤ : Subgroup (E2.StarQuot M H)) :=
    ⟨le_top, subnormal_of_mem_cComp hAc, hAq⟩
  obtain ⟨L, hLs, hLnc, hLR, hRsup, hnorm⟩ :=
    nonsolvable_structure_J hmin hns ((kerIn M H).subgroupOf H) (B6.kerIn_subgroupOf_top M H)
  set R : Subgroup (E2.StarQuot M H) :=
    (twoResidual (⊤ : Subgroup ↥H)).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H)) with hRdef
  set Th : Subgroup (E2.StarQuot M H) :=
    (T.subgroupOf H).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H)) with hThdef
  let N : Th → Subgroup (E2.StarQuot M H) := fun t => B6.conjSub t.1 L
  have hF1 : R = ⨆ i, N i := by
    rw [hRsup]
    exact iSup_subtype'
  have hNR : ∀ i, N i ≤ R := fun i => by
    rw [hF1]
    exact le_iSup N i
  have hNn : ∀ i, ((N i).subgroupOf R).Normal := fun i => hnorm i.1 i.2
  have htR : (twoResidual (⊤ : Subgroup ↥H)).Normal := by
    have h := le_normalizer_twoResidual (⊤ : Subgroup ↥H)
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)
  haveI hRn : R.Normal := htR.map _ (QuotientGroup.mk'_surjective _)
  have hRsub : IsSubnormal R ⊤ :=
    IsSubnormal.step le_top (by infer_instance) (IsSubnormal.refl ⊤)
  have hNiso : ∀ i : Th, Nonempty (↥L ≃* ↥(N i)) := fun i => conjSub_mulEquiv i.1 L
  have hNs : ∀ i : Th, IsSimpleGroup ↥(N i) := fun i => by
    obtain ⟨e⟩ := hNiso i
    haveI := hLs
    exact e.isSimpleGroup_congr.mp inferInstance
  have hNnc : ∀ i : Th, ¬ IsMulCommutative ↥(N i) := fun i => by
    obtain ⟨e⟩ := hNiso i
    exact not_isMulCommutative_of_mulEquiv e hLnc
  have hNc : ∀ i, IsComponentOf (N i) ⊤ := fun i => by
    haveI := hNs i
    exact ⟨le_top, IsSubnormal.step (hNR i) (hNn i) hRsub,
      isQuasisimple_of_simple_nonabelian _ (hNnc i)⟩
  have hNcard : ∀ i : Th, Nat.card ↥(N i) = Nat.card ↥L := fun i => by
    obtain ⟨e⟩ := hNiso i
    exact (Nat.card_congr e.toEquiv).symm
  have hone : (1 : E2.StarQuot M H) ∈ Th :=
    Subgroup.mem_map.mpr ⟨1, Subgroup.one_mem _, map_one _⟩
  let i₀ : Th := ⟨1, hone⟩
  have hNcard' : ∀ i, Nat.card ↥(N i) = Nat.card ↥(N i₀) := fun i =>
    (hNcard i).trans (hNcard i₀).symm
  have hperfK : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hKperf : Group.IsPerfect ↥(K.subgroupOf H) := isPerfect_subgroupOf hKH hperfK
  have hK'R : K.subgroupOf H ≤ twoResidual (⊤ : Subgroup ↥H) :=
    B6.perfect_le_twoResidual
  have hAR : A ≤ R := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨k, hK'R hk, rfl⟩
  have hQ2 : IsPGroup 2 (↥H ⧸ twoResidual (⊤ : Subgroup ↥H)) := by
    intro x
    obtain ⟨xH, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup ↥H) xH (Subgroup.mem_top _)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hk]
  obtain ⟨m, hm⟩ := isPGroup_iff_card_dvd_pow.mp hQ2
  have hle : twoResidual (⊤ : Subgroup ↥H) ≤
      ((QuotientGroup.mk' R).comp (QuotientGroup.mk' ((kerIn M H).subgroupOf H))).ker := by
    intro x hx
    have hxR : QuotientGroup.mk' ((kerIn M H).subgroupOf H) x ∈ R :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr hxR
  let φ : (↥H ⧸ twoResidual (⊤ : Subgroup ↥H)) →* (E2.StarQuot M H ⧸ R) :=
    QuotientGroup.lift _ ((QuotientGroup.mk' R).comp (QuotientGroup.mk' ((kerIn M H).subgroupOf H))) hle
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(x : ↥H ⧸ twoResidual (⊤ : Subgroup ↥H)), rfl⟩
  have hdvd1 : Nat.card (E2.StarQuot M H ⧸ R) ∣ 2 ^ m :=
    (Subgroup.card_dvd_of_surjective hφ).trans hm
  have hq : Nat.card (E2.StarQuot M H) ∣ 2 ^ m * Nat.card ↥R := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R]
    exact mul_dvd_mul_right hdvd1 _
  exact not_three_dvd_of_components R N i₀ A hF1 hNR hNn hNc hNcard' hAR hAcomp h3K m hq h3

end CFSG.Quasithin.H13
