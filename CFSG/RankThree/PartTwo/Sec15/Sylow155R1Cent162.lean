module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T120
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T131X
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T133
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentDefs
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem res1Cent_mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have hH' : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hH
  have hK' : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hK
  have h := Subgroup.map_commutator H K (MulAut.conj g).toMonoidHom
  rw [hH', hK'] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact h

private theorem res1Cent_mem_normalizer_of_le_of_isCyclic {D E : Subgroup G} (hD : IsCyclic ↥D)
    (hED : E ≤ D) {g : G} (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (E : Set G) := by
  have := hD
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ D := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgD]
    exact Subgroup.map_mono hED
  have hcard : Nat.card ((E.map (MulAut.conj g).toMonoidHom).subgroupOf D) =
      Nat.card (E.subgroupOf D) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h := (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hle, inf_eq_left.mpr hED] at h
  exact h

private theorem res1Cent_mem_normalizer_centralizer {W : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (W : Set G)) :
    s ∈ Subgroup.normalizer ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun m hm => ?_
  have hm' : m ∈ Subgroup.centralizer (W : Set G) := hm
  show s * m * s⁻¹ ∈ Subgroup.centralizer (W : Set G)
  rw [Subgroup.mem_centralizer_iff] at hm' ⊢
  intro w hw
  have hw' : s⁻¹ * w * s ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hs) w).mp hw
    simpa using this
  have h1 := hm' _ hw'
  calc w * (s * m * s⁻¹) = s * ((s⁻¹ * w * s) * m) * s⁻¹ := by group
    _ = s * (m * (s⁻¹ * w * s)) * s⁻¹ := by rw [h1]
    _ = s * m * s⁻¹ * w := by group

private theorem res1Cent_centralizer_le_normalizer_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hc : Commute z g := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  exact (hc.zpow_left k).eq

private theorem res1Cent_normalizer_zpowers_le (j : G) :
    Subgroup.normalizer (Subgroup.zpowers j : Set G) ≤
      Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) : Set G) := by
  intro g hg
  have h1 := res1Cent_mem_normalizer_centralizer hg
  have hC : Subgroup.centralizer ((Subgroup.zpowers j : Subgroup G) : Set G) =
      Subgroup.centralizer ({j} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hC] at h1
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ h1

private theorem res1Cent_orderOf_conj (y z : G) : orderOf (y * z * y⁻¹) = orderOf z :=
  orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective z

private theorem res1Cent_le_of_two_involutions {V R O N : Subgroup G} (hV : IsPGroup 2 ↥V)
    (hRO : R ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O))
    (hZR : ∀ e ∈ V, e ∈ Subgroup.centralizer (V : Set G) → e ∈ R)
    (hZN : ∀ e ∈ V, e ∈ Subgroup.centralizer (V : Set G) → orderOf e = 2 →
      O ⊓ Subgroup.centralizer ({e} : Set G) ≤ N)
    {z e : G} (hz2 : orderOf z = 2) (hzV : z ∈ V) (hzC : z ∈ Subgroup.centralizer (V : Set G))
    (he2 : orderOf e = 2) (heV : e ∈ V) (heC : e ∈ Subgroup.centralizer (V : Set G))
    (hez : e ≠ z) : O ≤ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup G := Subgroup.closure {z, e} with hEdef
  have hEZ : E ≤ V ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hEdef, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨hzV, hzC⟩
    · exact ⟨heV, heC⟩
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hEZ hy).2 x (hEZ hx).1
  have hEcomm : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hEexp : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [← hz2]
        exact pow_orderOf_eq_one x
      · rw [← he2]
        exact pow_orderOf_eq_one x
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hcomm x hx y hy) 2), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hE2 : IsPGroup 2 ↥E := hV.to_le (hEZ.trans inf_le_left)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hE2
  have hzE : Subgroup.zpowers z ≤ E :=
    (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Set.mem_insert z {e}))
  have heE : e ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
  have hcz : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hlt' : k < 2 := by omega
    interval_cases k
    · have h := Subgroup.card_le_of_le hzE
      rw [hcz, hk] at h
      norm_num at h
    · have hEq : Subgroup.zpowers z = E :=
        Subgroup.eq_of_le_of_card_ge hzE (by rw [hk, hcz]; norm_num)
      rw [← hEq] at heE
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp heE
      rw [← zpow_mod_orderOf, hz2] at hm
      have h01 : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1 := by omega
      rcases h01 with h0 | h1
      · rw [h0, zpow_zero] at hm
        rw [← hm, orderOf_one] at he2
        omega
      · rw [h1, zpow_one] at hm
        exact hez hm.symm
  have hE4 : 4 ≤ Nat.card E := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hER : E ≤ R := by
    rw [hEdef, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hZR x hzV hzC
    · exact hZR x heV heC
  refine CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le hEcomm hEexp hE4
    (hER.trans hRO) hO fun x hx hx1 => ?_
  have hx2 : orderOf x = 2 := orderOf_eq_prime (hEexp x hx) hx1
  exact hZN x (hEZ hx).1 (hEZ hx).2 hx2

namespace Res1Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

theorem r_le_host (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    CFSG.Open.pCoreOf 2 Y ≤ res1Host A X Y M := by
  obtain ⟨-, hRH, -, -⟩ := Sylow155B1.delta_host_facts τ.std τ.i146 τ.ctx τ.endN τ.r_le
    (Sylow155S.sup_mem_invariant τ.ctx τ.endN τ.r_le) (Sylow155S.sup_le_u155 τ.endN τ.r_le)
    (Sylow155S.p_le_normalizer_sup τ.endN) le_sup_left
  exact hRH

theorem host_le_normalizer_ob (_ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    res1Host A X Y M ≤ Subgroup.normalizer (res1Ob A X Y M : Set G) :=
  le_normalizer_pPrimeCoreOf 2 _

theorem odd_card_ob (_ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    Odd (Nat.card (res1Ob A X Y M)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf 2 _)

theorem eq_of_mem_center (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) {e : G} (heV : e ∈ CFSG.Open.pCoreOf 2 K)
    (heC : e ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G)) (he2 : orderOf e = 2) :
    e = z := by
  have hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A) :=
    pCoreOf_two_mem_scriptQ_of_eq_sup_x τ.sec15 hbot h1444 τ.i146 τ.ctx τ.endN τ.r_le τ.k_eq
  have hcen := fun {e : G} (heV : e ∈ CFSG.Open.pCoreOf 2 K)
      (heC : e ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G)) =>
    mem_pCoreOf_two_of_mem_center τ.std h1444 τ.i146 h149 h153 (hbot G A c L τ.std) τ.ctx
      τ.maxT τ.above τ.endN τ.r_le τ.i_le τ.e_le τ.k_eq τ.ob_not_le hV heV heC
  by_contra hez
  apply τ.ob_not_le
  exact res1Cent_le_of_two_involutions (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
    (τ.r_le_host.trans τ.host_le_normalizer_ob) τ.odd_card_ob
    (fun _ hxV hxC => (hcen hxV hxC).1)
    (fun x hxV hxC hx2 => inf_le_right.trans
      (centralizer_le_n155 h153 τ.ctx.mem_k hx2 (hcen hxV hxC).2.1 (hcen hxV hxC).2.2))
    τ.z_two τ.z_v τ.z_cv he2 heV heC hez

theorem le_centralizer_z (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    Y ≤ Subgroup.centralizer ({z} : Set G) := by
  intro y hy
  have hyV : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (τ.ctx.norm_k hy)
  have heV : y * z * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := (Subgroup.mem_normalizer_iff.mp hyV z).mp τ.z_v
  have heC : y * z * y⁻¹ ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (res1Cent_mem_normalizer_centralizer hyV) z).mp τ.z_cv
  have he := eq_of_mem_center hbot h1444 h149 h153 τ heV heC
    ((res1Cent_orderOf_conj y z).trans τ.z_two)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * z = y * z * y⁻¹ * y := by group
    _ = z * y := by rw [he]

theorem x_le_centralizer_ob (h149 : Item149 A (lB A)) (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    X ≤ Subgroup.centralizer (res1Ob A X Y M : Set G) := by
  have hOE := pPrimeCoreOf_two_host_le_centralizer τ.std τ.i146 h149 τ.ctx τ.endN τ.r_le τ.i_le
  have hXE := x_le_oPrimeResidualOf_delta τ.ctx
  exact Subgroup.le_centralizer_iff.mp
    (hOE.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXE)))

theorem le_normalizer_ob (h149 : Item149 A (lB A)) (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    Y ≤ Subgroup.normalizer (res1Ob A X Y M : Set G) := by
  have hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y := by
    have h := τ.ctx.isY.2.2
    rwa [τ.ctx.res] at h
  refine hY.le.trans (sup_le ?_ (τ.r_le_host.trans τ.host_le_normalizer_ob))
  exact (τ.x_le_centralizer_ob h149).trans (Subgroup.centralizer_le_normalizer _)

theorem le_normalizer_j (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    Y ≤ Subgroup.normalizer (res1J A X Y M z : Set G) := fun _ hy =>
  res1Cent_mem_normalizer_commutator (τ.le_normalizer_ob h149 hy)
    (res1Cent_centralizer_le_normalizer_zpowers z (τ.le_centralizer_z hbot h1444 h149 h153 hy))

theorem j_le_centralizer (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    res1J A X Y M z ≤ Subgroup.centralizer (A : Set G) := by
  have hOA : res1Ob A X Y M ≤ Subgroup.centralizer (A : Set G) := τ.e_eq ▸ τ.e_le
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (τ.a_z ha)
  refine Subgroup.commutator_le.mpr fun o ho g hg => ?_
  have hg' : g ∈ Subgroup.centralizer (A : Set G) := (Subgroup.zpowers_le.mpr hzA) hg
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hOA ho) hg') (inv_mem (hOA ho))) (inv_mem hg')

theorem j_le_ob (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    res1J A X Y M z ≤ res1Ob A X Y M := by
  have hzN : z ∈ Subgroup.normalizer (res1Ob A X Y M : Set G) :=
    τ.host_le_normalizer_ob (τ.r_le_host τ.z_r)
  refine Subgroup.commutator_le.mpr fun o ho g hg => ?_
  have hgN : g ∈ Subgroup.normalizer (res1Ob A X Y M : Set G) := (Subgroup.zpowers_le.mpr hzN) hg
  have h1 : g * o⁻¹ * g⁻¹ ∈ res1Ob A X Y M :=
    (Subgroup.mem_normalizer_iff.mp hgN o⁻¹).mp (inv_mem ho)
  rw [commutatorElement_def, show o * g * o⁻¹ * g⁻¹ = o * (g * o⁻¹ * g⁻¹) by group]
  exact mul_mem ho h1

theorem j_mem_scriptQ (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    res1J A X Y M z ∈ scriptQ A (lB A) :=
  mem_scriptQ_of_le (pPrimeCoreOf_two_host_mem_scriptQ τ.std τ.i146 τ.ctx τ.endN τ.r_le)
    τ.j_le_ob ((Subgroup.le_centralizer_iff.mp τ.j_le_centralizer).trans
      (Subgroup.centralizer_le_normalizer _))

theorem j_not_le (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    ¬ res1J A X Y M z ≤ n155 A K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJN
  apply τ.ob_not_le
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (res1Ob A X Y M : Set G) :=
    Subgroup.zpowers_le.mpr (τ.host_le_normalizer_ob (τ.r_le_host τ.z_r))
  have hz : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, τ.z_two, pow_one])
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (Subgroup.zpowers z) (res1Ob A X Y M) hz hzN (coprime_card_pPrimeCoreOf 2 _)
  rw [← hfac]
  refine sup_le hJN (inf_le_right.trans ((Subgroup.centralizer_le ?_).trans τ.cz_le))
  exact Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z)

theorem centralizer_le (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) (hcyc : IsCyclic ↥(res1J A X Y M z))
    (h340 : ∀ M' : Subgroup G, Ctx155 A X K Y M' T → M' = M)
    (h361 : ∀ j ∈ res1J A X Y M z, j ≠ 1 →
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) ≠ ⊥)
    {j : G} (hj : j ∈ res1J A X Y M z) (hj1 : j ≠ 1) :
    Subgroup.centralizer ({j} : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQj : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({j} : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  obtain ⟨M'', hNM, hM''⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hQj (h361 j hj hj1))
  have hCM : Subgroup.centralizer ({j} : Set G) ≤ M'' :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hNM
  have hjJ : Subgroup.zpowers j ≤ res1J A X Y M z := Subgroup.zpowers_le.mpr hj
  have hYM : Y ≤ M'' := fun y hy =>
    hNM (res1Cent_normalizer_zpowers_le j (res1Cent_mem_normalizer_of_le_of_isCyclic hcyc hjJ
      (τ.le_normalizer_j hbot h1444 h149 h153 hy)))
  have hAM : A ≤ M'' := fun a ha => hCM (Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (τ.j_le_centralizer hj) a ha))
  have hJM : res1J A X Y M z ≤ M'' := by
    intro x hx
    refine hCM (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨j, hj⟩)
    have h1 : ((g ^ m : ↥(res1J A X Y M z)) : G) = x := congrArg Subtype.val hm
    have h2 : ((g ^ k : ↥(res1J A X Y M z)) : G) = j := congrArg Subtype.val hk
    rw [← h1, ← h2, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← zpow_add, ← zpow_add, add_comm]
  have hctx : Ctx155 A X K Y M'' T :=
    ⟨τ.ctx.isY, τ.ctx.res, τ.ctx.mem_k, τ.ctx.le_k, τ.ctx.hyp, τ.ctx.norm_k,
      ⟨hM'', SetLike.coe_subset_coe.mpr (sup_le hAM hYM)⟩,
      fun h => τ.j_not_le ((le_delta τ.j_mem_scriptQ hJM).trans h), τ.ctx.mem_t⟩
  rw [← h340 M'' hctx]
  exact hCM

end Res1Tau

theorem res1CentLeMN_of (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hcyc : Res1JCyclic Q P) (h340 : Res1Thm340 Q P) (h361 : Res1Thm361 Q P) :
    Res1CentLeMN Q P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN j hj hj1
  have τ : Res1Tau Q P A c L X K Y M T P' Yc z :=
    ⟨hR, hq, hN, hS, hC, hmax, habove, hE, h146, hRP, hIX, hY, hsimple, hP, hEA, hEO, hcomm,
      hfield, hLX, hLΔ, hKX, hΩ, hMX, hMO, hE0N, hz2, hzV, hzC, hzR, hAz, hKz, hCN⟩
  exact τ.centralizer_le hbot (h1444 G A c L hS) (h149 G A c L hS) (h153 G A c L hR hq)
    (hcyc G A c L X K Y M T P' Yc z τ) (h340 G A c L X K Y M T P' Yc z τ)
    (h361 G A c L X K Y M T P' Yc z τ) hj hj1

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
