module

public import CFSG.RankThree.PartOne.N143.CaseB2Aux
public import CFSG.RankThree.PartOne.N143.CaseAFinal
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.N143.CaseBGroup

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}

theorem caseB2_false (hJ : JFacts) (hB2 : Node143CommB2) (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs)
    (hcard : Nat.card (reflectionGroup p A) = 54) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) (h2mod : 2 ^ f % 3 = 2)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set G))) : False := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ' := hJ
  obtain ⟨hX0, -, -, -, -, -, -, hB⟩ := hJ'
  obtain ⟨c1, h1⟩ := hgood L hctx.facts13.inZeroStar
  obtain ⟨k, hk1, hk3, hk⟩ := hspec.z_scalar
  obtain ⟨z0, hz0N, hz03, hz0π⟩ := exists_z hJ hctx hgood hspec
  have hz01 : z0 ≠ 1 := by
    intro h
    apply hspec.z_ne
    have : (⟨z0, hz0N⟩ : Subgroup.normalizer (A : Set G)) = 1 := Subtype.ext h
    rw [← hz0π, this, map_one]
  have hz0ord : orderOf z0 = 3 := orderOf_eq_prime hz03 hz01
  have hz0act : ∀ a ∈ A, z0 * a * z0⁻¹ = a ^ k := action_of_pi_eq hk hz0N hz0π
  have hscal : IsScalarOrderThree p A z0 := ⟨hz0N, hz0ord, k, hk1, hk3, hz0act⟩
  have hz0L : z0 ∈ Subgroup.normalizer (L : Set G) :=
    h1.mem_normalizer_of_scalar hz0N ⟨k, hz0act⟩
  have hf1 : 1 ≤ f := Nat.pos_of_ne_zero fun h => by subst h; simp at h2mod
  obtain ⟨hD3, hBU⟩ := hB G p A c1 L h1 f hf hm h2mod
  obtain ⟨x0, hx0, hx03, a0, ha0, hne0⟩ := hX0 G p A c1 L h1
  obtain ⟨hx0L, hx0W⟩ := Subgroup.mem_inf.1 hx0
  set D : Subgroup G := L ⊓ Subgroup.centralizer (A : Set G) with hD
  have hx0D : x0 ∉ D := fun h => hne0 (by
    have := Subgroup.mem_centralizer_iff.1 h.2 a0 ha0
    exact mul_inv_eq_iff_eq_mul.2 this.symm)
  have hx0ND : x0 ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun d hd => ?_
    have hd' : d ∈ D := hd
    show x0 * d * x0⁻¹ ∈ (D : Set G)
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx0L hd'.1) (Subgroup.inv_mem _ hx0L),
      conj_mem_centralizer hx0W hd'.2⟩
  have hYcard : Nat.card (Subgroup.zpowers x0 ⊔ D : Subgroup G) = 3 * Nat.card D :=
    card_sup_zpowers_of_normalizer hx03 hx0D hx0ND
  have hDpos : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hY3 : (Nat.card ↥(Subgroup.zpowers x0 ⊔ D)).factorization 3 = 1 := by
    rw [hYcard, Nat.factorization_mul (by norm_num) hDpos, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hD3, Nat.Prime.factorization_self Nat.prime_three]
  have hcommA : A.normalizerMonoidHom ⟨z0, hz0N⟩ * A.normalizerMonoidHom ⟨x0, hx0W⟩ =
      A.normalizerMonoidHom ⟨x0, hx0W⟩ * A.normalizerMonoidHom ⟨z0, hz0N⟩ := by
    rw [hz0π]
    exact hspec.z_central _
  have hd'C := inv_comm_mem_centralizer hx0W hz0N hcommA
  have hz0x0L : z0 * x0 * z0⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hz0L x0).1 hx0L
  have hd'D : x0⁻¹ * (z0 * x0 * z0⁻¹) ∈ D :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hx0L) hz0x0L, hd'C⟩
  have hz0x0 : z0 * x0 * z0⁻¹ = x0 * (x0⁻¹ * (z0 * x0 * z0⁻¹)) := by group
  have hz0x0Y : z0 * x0 * z0⁻¹ ∈ Subgroup.zpowers x0 ⊔ D := by
    rw [hz0x0]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x0))
      (Subgroup.mem_sup_right hd'D)
  have hz0NY : z0 ∈ Subgroup.normalizer ((Subgroup.zpowers x0 ⊔ D : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hle : (Subgroup.zpowers x0 ⊔ D) ≤
        (Subgroup.zpowers x0 ⊔ D).comap (MulAut.conj z0).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hz0x0Y
      · intro d hd
        have hdD : z0 * d * z0⁻¹ ∈ D :=
          ⟨(Subgroup.mem_normalizer_iff.1 hz0L d).1 hd.1, conj_mem_centralizer hz0N hd.2⟩
        exact Subgroup.mem_sup_right hdD
    exact hle hy
  have hz0L' : z0 ∉ L := by
    intro hz
    have hzs : zs ∈ torusImage A L := by
      rw [← hz0π]
      exact Sec12Three.mem_torusImage_iff.2 ⟨z0, hz, hz0N, rfl⟩
    have := Subgroup.disjoint_def.1 (h1.disjoint_zpowers hspec) ⟨hzs, hspec.z_mem⟩
      (Subgroup.mem_zpowers zs)
    exact hspec.z_ne this
  have hY1L : (Subgroup.zpowers x0 ⊔ D : Subgroup G) ≤ L :=
    sup_le (Subgroup.zpowers_le.2 hx0L) inf_le_left
  have hz0Y : z0 ∉ (Subgroup.zpowers x0 ⊔ D : Subgroup G) := fun h => hz0L' (hY1L h)
  obtain ⟨x, hxY, hxord, hxz⟩ := exists_commuting_of_normalizing hz03 hz0Y hz0NY hY3
  have hYLW : (Subgroup.zpowers x0 ⊔ D : Subgroup G) ≤ L ⊓ torusNormalizer A :=
    sup_le (Subgroup.zpowers_le.2 hx0) fun d hd =>
      ⟨hd.1, Subgroup.centralizer_le_normalizer _ hd.2⟩
  have hxLW : x ∈ L ⊓ torusNormalizer A := hYLW hxY
  have hx3 : x ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hxD : x ∉ D := by
    intro h
    apply hD3
    have h2 : orderOf (⟨x, h⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
    have h3 : orderOf (⟨x, h⟩ : D) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hxord
    rwa [h3] at h2
  have hxmove : ∃ a ∈ A, x * a * x⁻¹ ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hxD
    exact ⟨hxLW.1, Subgroup.mem_centralizer_iff.2 fun a ha =>
      (mul_inv_eq_iff_eq_mul.1 (hcon a ha)).symm⟩
  obtain ⟨U, hUmem, hUcyc, hUcard⟩ := hBU x hxLW hx3 hxmove
  have hxU : x ∈ U := (hUmem x).2
    ⟨⟨hxLW.1, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩, 1, by simpa using hx3⟩
  have hz0U : z0 ∉ U := fun h => hz0L' ((hUmem z0).1 h).1.1
  have hxz0 : z0 * x = x * z0 := hxz.symm
  have hz0inv_x : z0⁻¹ * x = x * z0⁻¹ := by
    calc z0⁻¹ * x = z0⁻¹ * (x * z0) * z0⁻¹ := by group
      _ = z0⁻¹ * (z0 * x) * z0⁻¹ := by rw [hxz]
      _ = x * z0⁻¹ := by group
  have hz0NU : z0 ∈ Subgroup.normalizer (U : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hu' := (hUmem u).1 hu
    show z0 * u * z0⁻¹ ∈ (U : Set G)
    refine (hUmem _).2 ⟨⟨(Subgroup.mem_normalizer_iff.1 hz0L u).1 hu'.1.1,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · have huc : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 hu'.1.2
      calc z0 * u * z0⁻¹ * x = z0 * u * (z0⁻¹ * x) := by group
        _ = z0 * u * (x * z0⁻¹) := by rw [hz0inv_x]
        _ = z0 * (u * x) * z0⁻¹ := by group
        _ = z0 * (x * u) * z0⁻¹ := by rw [huc]
        _ = (z0 * x) * u * z0⁻¹ := by group
        _ = (x * z0) * u * z0⁻¹ := by rw [hxz0]
        _ = x * (z0 * u * z0⁻¹) := by group
    · obtain ⟨n, hn⟩ := hu'.2
      exact ⟨n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩
  set a : ℕ := (Nat.card L).factorization 3 with ha
  have hMUcard : Nat.card (Subgroup.zpowers z0 ⊔ U : Subgroup G) = 3 * Nat.card U :=
    card_sup_zpowers_of_normalizer hz03 hz0U hz0NU
  have hMcard : Nat.card (Subgroup.zpowers z0 ⊔ U : Subgroup G) = 3 ^ (a + 1) := by
    rw [hMUcard, hUcard, pow_succ, mul_comm]
  set R : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers z0 with hR
  have hxzc : ∀ s ∈ Subgroup.zpowers x, ∀ t ∈ Subgroup.zpowers z0, s * t = t * s := by
    intro s hs t ht
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact (Commute.zpow_zpow hxz i j).eq
  have hz0x : z0 ∉ Subgroup.zpowers x := fun h =>
    hz0Y ((Subgroup.zpowers_le.2 hxY) h)
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers z0) :=
    disjoint_zpowers_of_prime hz0ord hz0x
  have hRcard : Nat.card R = 9 := by
    rw [hR, Torsion37.card_sup_of_commute_disjoint hxzc hdisj, Nat.card_zpowers,
      Nat.card_zpowers, hxord, hz0ord]
  have hRcl : R = Subgroup.closure ({x, z0} : Set G) := by
    rw [hR, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  obtain ⟨hRc, hRe⟩ := closure_comm_exp' (p := 3) ({x, z0} : Set G)
    (by
      intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hxz
      · exact hxz.symm
      · rfl)
    (by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hx3
      · exact hz03)
  rw [← hRcl] at hRc hRe
  have hRel : CFSG.IsElementaryAbelian 3 R := Torsion37.isElementaryAbelian_of_forall hRc hRe
  have hz0R : z0 ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers z0)
  have hxR : x ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hUN : U ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hgc : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 ((hUmem g).1 hg).1.2
    have hgxg : g * x * g⁻¹ = x := mul_inv_eq_iff_eq_mul.2 hgc
    have hw : z0 * g * z0⁻¹ * g⁻¹ ∈ U :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hz0NU g).1 hg) (Subgroup.inv_mem _ hg)
    have hw3 : (z0 * g * z0⁻¹ * g⁻¹) ^ 3 = 1 := cyclic3_commutator_cube hUcard hz03 hz0NU g hg
    have hwx : z0 * g * z0⁻¹ * g⁻¹ ∈ Subgroup.zpowers x :=
      mem_zpowers_of_cyclic_cube hxU hxord hw hw3
    have hgz : g * z0 * g⁻¹ ∈ R := by
      have : g * z0 * g⁻¹ = (z0 * g * z0⁻¹ * g⁻¹)⁻¹ * z0 := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hwx)) hz0R
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hle : Subgroup.closure ({x, z0} : Set G) ≤ R.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with hux | huz
      · rw [hux]
        show g * x * g⁻¹ ∈ R
        rw [hgxg]
        exact hxR
      · rw [huz]
        exact hgz
    rw [← hRcl] at hle
    exact hle hr
  have hMN : (Subgroup.zpowers z0 ⊔ U : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    refine sup_le ?_ hUN
    rw [Subgroup.zpowers_le]
    exact Subgroup.le_normalizer hz0R
  have hMNU : (Subgroup.zpowers z0 ⊔ U : Subgroup G) ≤ Subgroup.normalizer (U : Set G) :=
    sup_le ((Subgroup.zpowers_le).2 hz0NU) Subgroup.le_normalizer
  have hXs : reflectionGroup p A ≤ A.normalizerMonoidHom.range := WeylIso.closure_le_weyl
  have hz0X : z0 ∈ Xsub A (reflectionGroup p A) :=
    mem_Xsub.2 ⟨hz0N, by rw [hz0π]; exact hspec.P_le hspec.z_mem⟩
  have hxX : x ∈ Xsub A (reflectionGroup p A) :=
    mem_Xsub.2 ⟨hxLW.2, h1.torusImage_le (Sec12Three.mem_torusImage_iff.2 ⟨x, hxLW.1, hxLW.2, rfl⟩)⟩
  have hRX : R ≤ Xsub A (reflectionGroup p A) :=
    sup_le (Subgroup.zpowers_le.2 hxX) (Subgroup.zpowers_le.2 hz0X)
  obtain ⟨P, hRP, hPX, hP27, hPexp⟩ := exists_sylow_exp_three hC hXs hcard hspec.P_le
    hspec.card_P hspec.mem_P hRX hRe
  have hPnorm := normal_of_card_nine hRP hP27 hRcard
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun r hr => hPnorm y hy r hr
  have hbound := hB2 G p A c L A hctx.hyp hctx.facts12 hctx.facts13 hctx.notFive rfl hctx.allL3
    hctx.threeTransp hctx.hess ⟨f, hf1, hf, hm, h2mod⟩ hC x z0 hxLW hxord hscal hxz
  have hMpg : IsPGroup 3 (Subgroup.zpowers z0 ⊔ U : Subgroup G) := IsPGroup.of_card hMcard
  have := hRel
  refine sylow_contra (N := Subgroup.normalizer (R : Set G)) (M := Subgroup.zpowers z0 ⊔ U) (P := P)
    (U := U) (n := a + 1) ?_ hMN hMcard hPN hP27 hPexp hUcyc le_sup_right hMUcard.symm ?_
  · intro S hSN hS3
    exact three_subgroup_card_le_of_centralizer R hRcard hbound S hSN hS3
  · intro m hm' u hu
    exact (Subgroup.mem_normalizer_iff.1 (hMNU hm') u).1 hu

end CFSG.RankThree.PartOne.N143
