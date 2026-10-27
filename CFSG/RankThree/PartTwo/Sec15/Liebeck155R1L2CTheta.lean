module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Tau
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162
import CFSG.RankThree.PartTwo.Sec15.Sylow155E0
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJRes
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

omit [Finite G] in
private theorem res1CT_conj_mem_centralizer {W : Subgroup G} {m x : G}
    (hm : m ∈ Subgroup.normalizer (W : Set G)) (hx : x ∈ Subgroup.centralizer (W : Set G)) :
    m * x * m⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hm' : m⁻¹ * a * m ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) a).mp ha
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hx _ hm'
  calc a * (m * x * m⁻¹) = m * ((m⁻¹ * a * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * a * m)) * m⁻¹ := by rw [h]
    _ = (m * x * m⁻¹) * a := by group

omit [Finite G] in
private theorem res1CT_le_res1C {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (L : Subgroup G) : A ≤ Res1C A L := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, (Subgroup.mem_inf.mp hb).1⟩ ⟨a, ha⟩)

omit [Finite G] in
private theorem res1CT_mem_centralizerSection {c : G} {K M' : Subgroup G}
    (hc : ∀ k ∈ K, c * k = k * c) (hM : M' ≤ K) : c ∈ centralizerSection K M' := by
  have hcK : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (hc k hk).symm
  have hcM : c ∈ Subgroup.centralizer (M' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm => (hc m (hM hm)).symm
  refine ⟨Subgroup.centralizer_le_normalizer _ hcK, Subgroup.centralizer_le_normalizer _ hcM,
    fun k hk => ?_⟩
  have : ⁅k, c⁆ = 1 := by
    rw [commutatorElement_def]
    calc k * c * k⁻¹ * c⁻¹ = (c * k) * k⁻¹ * c⁻¹ := by rw [hc k hk]
      _ = 1 := by group
  rw [this]
  exact one_mem _

theorem n155_le_centralizer_z_of_tau (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A)) (hn : Claim153Normal A (lB A))
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z) :
    n155 A K ≤ Subgroup.centralizer ({z} : Set G) := by
  have heq : n155 A K = Subgroup.normalizer (K : Set G) :=
    normalizer_x_eq_of_normal τ.std h149 hn τ.ctx.mem_k
  rw [heq]
  intro y hy
  have hyV : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hy
  have heV : y * z * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := (Subgroup.mem_normalizer_iff.mp hyV z).mp τ.z_v
  have heC : y * z * y⁻¹ ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    res1CT_conj_mem_centralizer hyV τ.z_cv
  have he2 : orderOf (y * z * y⁻¹) = 2 :=
    (orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective z).trans τ.z_two
  have he : y * z * y⁻¹ = z := τ.eq_of_mem_center hbot h1444 h149 h153 heV heC he2
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * z = y * z * y⁻¹ * y := by group
    _ = z * y := by rw [he]

private theorem res1CT_host_inf_le_n155 (hst : StellmacherKP)
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z) :
    Sylow155R1.res1Host A X Y M ⊓
        Subgroup.normalizer
          (Sec16.Proof165.stellmacherSub (CFSG.Open.pCoreOf 2 Y) : Set G) ≤ n155 A K := by
  obtain ⟨hHQ, -, -, -⟩ := Sylow155B1.delta_host_facts τ.std τ.i146 τ.ctx τ.endN τ.r_le
    (Sylow155S.sup_mem_invariant τ.ctx τ.endN τ.r_le) (Sylow155S.sup_le_u155 τ.endN τ.r_le)
    (Sylow155S.p_le_normalizer_sup τ.endN) le_sup_left
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  obtain ⟨hCR, hCne, hNC, -⟩ := Sec16.Proof165.stellmacherSub_spec hst τ.std.toTheoremFourHyp hR2
    τ.ctx.isY.1.1.2
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    τ.ctx.isY.1.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hVW : Sylow155R1.res1Host A X Y M ⊓ Subgroup.normalizer
      (Sec16.Proof165.stellmacherSub (CFSG.Open.pCoreOf 2 Y) : Set G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hHQ inf_le_left
      (Late.le_normalizer_inf hHQ.1.2.2 ((hAR.trans hNC).trans Subgroup.le_normalizer))
  exact (le_delta hVW inf_le_right).trans (τ.endN.claim _ hCne hCR
    (Proof155Wx.stellmacherSub_subgroupOf_characteristic (CFSG.Open.pCoreOf 2 Y)))

theorem host_comm_mem_ob_of_tau (hst : StellmacherKP) (hbot : Item145BotS14)
    (h1444 : Item1444 A (lB A)) (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (hn : Claim153Normal A (lB A)) (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z) :
    ∀ h ∈ Sylow155R1.res1Host A X Y M, h * z * h⁻¹ * z⁻¹ ∈ Sylow155R1.res1Ob A X Y M := by
  have hNz := n155_le_centralizer_z_of_tau hbot h1444 h149 h153 hn τ
  have hzN : z ∈ Subgroup.normalizer (Sylow155R1.res1Ob A X Y M : Set G) :=
    τ.host_le_normalizer_ob (τ.r_le_host τ.z_r)
  obtain ⟨hHQ, -, -, hsyl⟩ := Sylow155B1.delta_host_facts τ.std τ.i146 τ.ctx τ.endN τ.r_le
    (Sylow155S.sup_mem_invariant τ.ctx τ.endN τ.r_le) (Sylow155S.sup_le_u155 τ.endN τ.r_le)
    (Sylow155S.p_le_normalizer_sup τ.endN) le_sup_left
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hV3 : ¬ 3 ∣ Nat.card (Sylow155R1.res1Host A X Y M) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hHQ.1.2.1
  have hle := Sylow155E0.le_layerOddPreimage_sup hst τ.std.toTheoremFourHyp hR2 hsyl hV3
  have hWN := res1CT_host_inf_le_n155 hst τ
  let S : Subgroup G :=
    { carrier := {h | h ∈ Subgroup.normalizer (Sylow155R1.res1Ob A X Y M : Set G) ∧
        h * z * h⁻¹ * z⁻¹ ∈ Sylow155R1.res1Ob A X Y M}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, ?_⟩
        have h1 : a * b * z * (a * b)⁻¹ * z⁻¹ =
            (a * (b * z * b⁻¹ * z⁻¹) * a⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
        rw [h1]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp ha.1 _).mp hb.2) ha.2
      one_mem' := ⟨one_mem _, by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _⟩
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, ?_⟩
        have h1 : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem ha.1) _).mp (inv_mem ha.2) }
  have hObS : Sylow155R1.res1Ob A X Y M ≤ S := by
    intro o ho
    refine ⟨Subgroup.le_normalizer ho, ?_⟩
    rw [show o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) by group]
    exact mul_mem ho ((Subgroup.mem_normalizer_iff.mp hzN _).mp (inv_mem ho))
  have hWS : Sylow155R1.res1Host A X Y M ⊓ Subgroup.normalizer
      (Sec16.Proof165.stellmacherSub (CFSG.Open.pCoreOf 2 Y) : Set G) ≤ S := by
    intro h hh
    refine ⟨τ.host_le_normalizer_ob hh.1, ?_⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hNz (hWN hh))
    have h1 : h * z * h⁻¹ * z⁻¹ = 1 := by
      rw [hc]
      group
    rw [h1]
    exact one_mem _
  have hHS : Sylow155R1.res1Host A X Y M ≤ S := hle.trans (sup_le (τ.e_eq.le.trans hObS) hWS)
  exact fun h hh => (hHS hh).2

private theorem res1CT_theta_inf_ob_eq_one
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z) {w : G}
    (hwΘ : w ∈ pPrimeCoreOf 3 (Res1C A L)) (hwO : w ∈ Sylow155R1.res1Ob A X Y M) : w = 1 := by
  obtain ⟨w₀, hw₀, rfl⟩ := hwΘ
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w₀ = 1 :=
    (QuotientGroup.eq_one_iff w₀).mpr hw₀
  have h2 : w₀ = 1 := τ.comm w₀ hwO fun y _ => by rw [h1, one_mul, mul_one]
  rw [h2]
  rfl

theorem cTheta_le_host_of_tau (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z)
    (hB : b155 A M X = ⊥) :
    Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) ≤
      Sylow155R1.res1Host A X Y M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := τ.std.mem_partTwoF.1
  have hAΘ : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 (Res1C A L) : Set G) :=
    (res1CT_le_res1C hAab L).trans (le_normalizer_pPrimeCoreOf 3 _)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := Sylow155B1.le_normalizer_x τ.ctx
  have hAC : A ≤ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have hm' : m ∈ Subgroup.centralizer (X : Set G) := hm
    exact res1CT_conj_mem_centralizer (hAX ha) hm'
  have hQA : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAC hAΘ
  have hΘ3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Res1C A L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hQ3 : ¬ 3 ∣ Nat.card
      (Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) : Subgroup G) :=
    fun h => hΘ3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hQ𝓠 : Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) ∈ scriptQ A (lB A) :=
    Gagen155R1HJ.mem_scriptQ_of_le_sup τ.std τ.at_of.1 hQA hQ3
      (inf_le_right.trans le_sup_left)
  have hCM : Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) ≤ M := by
    rw [τ.m_eq]
    exact inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  have hCsec : Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) ≤
      centralizerSection X (CFSG.Open.pCoreOf 2 X) := fun x hx =>
    res1CT_mem_centralizerSection
      (fun k hk => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1 k hk).symm)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hCU : Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) ≤ u155 A M X :=
    le_inf (le_delta hQ𝓠 hCM) hCsec
  have hU3 : ¬ 3 ∣ Nat.card (u155 A M X) := not_three_dvd_of_oPrimeResidualOf_eq_bot hB
  have hUO : u155 A M X ≤ pPrimeCoreOf 3 (u155 A M X) :=
    le_pPrimeCoreOf le_rfl Subgroup.le_normalizer
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU3)
  exact le_delta hQ𝓠 (hCU.trans (hUO.trans le_sup_right))

theorem z_conj_cTheta_of_tau (hst : StellmacherKP) (hbot : Item145BotS14)
    (h1444 : Item1444 A (lB A)) (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (hn : Claim153Normal A (lB A)) (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z)
    (hB : b155 A M X = ⊥) :
    ∀ x ∈ Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L), z * x * z⁻¹ = x := by
  intro x hx
  obtain ⟨hxC, hxΘ⟩ := Subgroup.mem_inf.mp hx
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (τ.a_z ha)
  have hzP : z ∈ Res1C A L := res1L2_centralizer_le_res1C A L hzA
  have hzX : z ∈ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (τ.k_z (τ.ctx.le_k hk))
  have hzxz : z * x * z⁻¹ ∈ Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) :=
    Subgroup.mem_inf.mpr
      ⟨(Subgroup.centralizer (X : Set G)).mul_mem
        ((Subgroup.centralizer (X : Set G)).mul_mem hzX hxC)
        ((Subgroup.centralizer (X : Set G)).inv_mem hzX),
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 _ hzP) x).mp hxΘ⟩
  have hcomm : z * x * z⁻¹ * x⁻¹ ∈
      Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) :=
    (Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L)).mul_mem hzxz
      ((Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L)).inv_mem hx)
  have hxH := cTheta_le_host_of_tau τ hB hx
  have h1 := host_comm_mem_ob_of_tau hst hbot h1444 h149 h153 hn τ x hxH
  have h2 : z * x * z⁻¹ * x⁻¹ ∈ Sylow155R1.res1Ob A X Y M := by
    rw [show z * x * z⁻¹ * x⁻¹ = (x * z * x⁻¹ * z⁻¹)⁻¹ by group]
    exact inv_mem h1
  have h3 : z * x * z⁻¹ * x⁻¹ = 1 :=
    res1CT_theta_inf_ob_eq_one τ (Subgroup.mem_inf.mp hcomm).2 h2
  exact mul_inv_eq_one.mp h3

end Tau

theorem res1L2CThetaZ_of_b155 (hst : StellmacherKP) (hbot : Item145BotS14)
    (h1444 : Item1444S14) (h149 : Sec16.Item149S14) {Q : ∀ (X : Type) [Group X], Prop}
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (hB : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z → b155 A M X = ⊥) :
    Res1L2CThetaZ Q := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP hEA
    hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN _
  have τ : Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z :=
    ⟨hR, hq, hN, hS, hC, hmax, habove, hE, h146, hRP, hIX, hY, hsimple, hP, hEA, hEO, hcomm,
      hfield, hLX, hLΔ, hKX, hΩ, hMX, hMO, hE0N, hz2, hzV, hzC, hzR, hAz, hKz, hCN⟩
  exact z_conj_cTheta_of_tau hst hbot (h1444 G A c L hS) (h149 G A c L hS) (h153 G A c L hR hq)
    (hn G A c L X K Y M T P' Yc z τ) τ (hB G A c L X K Y M T P' Yc z τ)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
