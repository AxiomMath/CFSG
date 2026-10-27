module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJGen
public import CFSG.Quasithin.Background.C41PfI
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L140
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJLemA
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJRes
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJSyl
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1BarDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_25_le_of_quotient {L : Subgroup G} {N : Subgroup ↥L} [N.Normal]
    {J : Type} [Group J] (hN : N = ⊥)
    (e : ↥L ⧸ N ≃* J)
    (hE25 : ∃ E : Subgroup J, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25 ∧ E ≤ L := by
  obtain ⟨E₀, hE₀ab, hE₀card⟩ := hE25
  obtain ⟨E, hE, hc⟩ :=
    CFSG.Quasithin.C41Pf.exists_elemAbelian_of_mulEquiv
      (X := ↥L ⧸ N) (Y := J) (p := 5) (k := 2) e ⟨E₀, hE₀ab, hE₀card⟩
  have eL : ↥L ≃* (↥L ⧸ N) :=
    ((QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot (G := ↥L))).symm
  obtain ⟨E₁, hE₁ab, hE₁card⟩ :=
    CFSG.Quasithin.C41Pf.exists_elemAbelian_of_mulEquiv
      (X := ↥L) (Y := ↥L ⧸ N) (p := 5) (k := 2) eL ⟨E, hE, hc⟩
  refine ⟨E₁.map L.subtype, CFSG.Open.IsElemAbelian.map hE₁ab L.subtype, ?_,
    Subgroup.map_subtype_le E₁⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hE₁card]
  norm_num

theorem res1_exists_elemAbelian_25_le {L : Subgroup G} (hθ0 : aschbacherSolvableCore 3 ↥L = ⊥)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2)) (hE25 : J2HasE25) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25 ∧ E ≤ L := by
  obtain ⟨e⟩ := hJ
  obtain ⟨E₀, hE₀ab, hE₀card⟩ := hE25
  have hE₀card' : Nat.card E₀ = 5 ^ 2 := by simpa using hE₀card
  exact exists_elemAbelian_25_le_of_quotient (L := L) (N := aschbacherSolvableCore 3 ↥L)
    hθ0 e ⟨E₀, hE₀ab, hE₀card'⟩

theorem hj_exists_res1C_lift {A L M : Subgroup G} {c : G} {Yc : Subgroup (Res1Q A L)}
    (hS : Sec14Std G A c L) (hY : Res1AtOf A c L M Yc) :
    ∃ (c' : ↥(Res1C A L)),
      (c' : G) = c ∧ c ∈ Res1C A L ∧ c ∈ A ∧ orderOf c = 3 ∧ c ∉ L ∧
      IsHyperplane A (A ⊓ L) ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hAe27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.toSec13Data.mem_partTwoE
  obtain ⟨hcA, hc3card, -⟩ := zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA
  have hc3 : orderOf c = 3 := by rw [← Nat.card_zpowers]; exact hc3card
  have hcL : c ∉ L := Sylow155R1.res1_not_mem hS hY.2.2.2.1
  have hcB : c ∉ A ⊓ L := fun h => hcL (Subgroup.mem_inf.mp h).2
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have h := Proof1418Res2.eq_sup_zpowers_of_not_mem hAe27 hY.1 hcA hcB
    rwa [sup_comm] at h
  have hhyp : IsHyperplane A (A ⊓ L) := hY.1
  have hcC : c ∈ Res1C A L := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (hAe27.1.1.is_comm.comm ⟨b, (Subgroup.mem_inf.mp hb).1⟩ ⟨c, hcA⟩)
  exact ⟨⟨c, hcC⟩, rfl, hcC, hcA, hc3, hcL, hhyp, hAeq⟩

theorem hj_exists_sylow_two_normalized {A L M : Subgroup G} {c : G} {Yc : Subgroup (Res1Q A L)}
    {X K Y T : Subgroup G} (hS : Sec14Std G A c L) (h142 : Concl142 A (lB A))
    (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hYF : Res1HJYFacts ↥Yc) (hC : Ctx155 A X K Y M T)
    (c' : ↥(Res1C A L)) (hc' : (c' : G) = c) (hcA : c ∈ A) :
    ∃ (U : Sylow 2 ↥Yc), A ≤ M ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈
        Subgroup.normalizer
          (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)) ∧
      (∀ w : ↥(Res1C A L),
        (w : G) ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) →
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w ∈
            Subgroup.normalizer
              (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L))) := by
  classical
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  obtain ⟨U, hU⟩ := res1_exists_sylow_two_normalized hS hAM h142 hY hsimple hYF.1
  have hcM : c ∈ M := hAM hcA
  have hcNO2 : (c' : G) ∈ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) := by
    rw [hc']
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hcM
  exact ⟨U, hAM, hU c' hcNO2, hU⟩

theorem hj_orderOf_mk_eq_three {A L M : Subgroup G} {c : G} {Yc : Subgroup (Res1Q A L)}
    (hY : Res1AtOf A c L M Yc) (c' : ↥(Res1C A L)) (hc' : (c' : G) = c)
    (hc3 : orderOf c = 3) :
    orderOf c' = 3 ∧ QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc ∧
      orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') = 3 := by
  have hc'3 : orderOf c' = 3 := by
    rw [← hc3, ← hc']
    exact (Subgroup.orderOf_coe c').symm
  obtain ⟨-, hcY, -⟩ := hY.2.2.2.1
  rw [Subgroup.mem_map] at hcY
  obtain ⟨x0, hx0, hx0G⟩ := hcY
  have hx0c' : x0 = c' := Subtype.ext (hx0G.trans hc'.symm)
  have hyYc : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc := by
    rw [← hx0c']
    exact (Subgroup.mem_comap.mp hx0)
  have hc'notCore : c' ∉ CFSG.pPrimeCore 3 ↥(Res1C A L) := by
    intro hmem
    have hdvd : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Res1C A L)) := by
      have := orderOf_dvd_natCard (⟨c', hmem⟩ : CFSG.pPrimeCore 3 ↥(Res1C A L))
      rwa [Subgroup.orderOf_mk, hc'3] at this
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card) hdvd
  have hy3 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') = 3 := by
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') ∣ 3 := by
      rw [← hc'3]
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have h1' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' = 1 :=
        orderOf_eq_one_iff.mp h1
      apply hc'notCore
      have hmemker : c' ∈ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))).ker :=
        MonoidHom.mem_ker.mpr h1'
      rwa [QuotientGroup.ker_mk'] at hmemker
    · exact h3
  exact ⟨hc'3, hyYc, hy3⟩

theorem hj_mem_normalizer_sylow {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)}
    (U : Sylow 2 ↥Yc) (c' : ↥(Res1C A L))
    (hcU : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈
        Subgroup.normalizer
          (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)))
    (hyYc : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc) :
    (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc) ∈
      Subgroup.normalizer (((U : Subgroup ↥Yc) : Set ↥Yc)) := by
  rw [Subgroup.mem_normalizer_iff] at hcU ⊢
  intro u
  constructor
  · intro hu
    have hmem : Yc.subtype ((⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc) * u * (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc)⁻¹) ∈
        (U : Subgroup ↥Yc).map Yc.subtype := by
      have hu' : Yc.subtype u ∈ (U : Subgroup ↥Yc).map Yc.subtype :=
        Subgroup.mem_map_of_mem Yc.subtype hu
      have := (hcU (Yc.subtype u)).mp hu'
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    rw [Subgroup.mem_map] at hmem
    obtain ⟨v, hv, hv'⟩ := hmem
    have hveq : v = (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc) * u * (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc)⁻¹ := Subtype.ext hv'
    rwa [hveq] at hv
  · intro hu
    have hmemMap : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') * Yc.subtype u * (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c')⁻¹ ∈
        (U : Subgroup ↥Yc).map Yc.subtype := by
      have := Subgroup.mem_map_of_mem Yc.subtype hu
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hmem : Yc.subtype u ∈ (U : Subgroup ↥Yc).map Yc.subtype :=
      (hcU (Yc.subtype u)).mpr hmemMap
    rw [Subgroup.mem_map] at hmem
    obtain ⟨v, hv, hv'⟩ := hmem
    have hveq : v = u := Subtype.ext hv'
    rwa [hveq] at hv

theorem hj_exists_five_lift {A L : Subgroup G} {c : G} {Yc : Subgroup (Res1Q A L)}
    (hfix : J2AutFixNine) (hE25 : J2HasE25) (h415 : Sec4.Item4_15)
    (hS : Sec14Std G A c L) (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (c' : ↥(Res1C A L)) (hc' : (c' : G) = c)
    (hhyp : IsHyperplane A (A ⊓ L)) (t' : ↥Yc) (ht'5 : orderOf t' = 5)
    (htc : Commute (t' : Res1Q A L)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c')) :
    ∃ (f : ↥(Res1C A L)) (k : ℕ) (f₁ : G),
      (f : G) ∈ Subgroup.centralizer (A : Set G) ∧ orderOf (f : G) = 5 ^ k ∧ 0 < k ∧
      f₁ = (f : G) ^ 5 ^ (k - 1) ∧ f₁ ∈ Subgroup.centralizer (A : Set G) ∧
      orderOf f₁ = 5 ∧ (f : G) ∈ Subgroup.centralizer (L : Set G) ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) f = (t' : Res1Q A L) ∧
      CFSG.pCore 2 ↥L = ⊥ ∧ aschbacherSolvableCore 3 ↥L = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let t : Res1Q A L := (t' : Res1Q A L)
  have ht5 : orderOf t = 5 := by
    change orderOf (t' : Res1Q A L) = 5
    rw [Subgroup.orderOf_coe, ht'5]
  obtain ⟨f, hfA, ⟨k, hfk⟩, hft⟩ :=
    res1_exists_five_lift hS hAeq hc' ht5 htc
  have hfG : orderOf (f : G) = 5 ^ k := by
    rw [Subgroup.orderOf_coe, hfk]
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · exfalso
      have hf1 : f = 1 := orderOf_eq_one_iff.mp (by rw [hfk, hk0, pow_zero])
      have ht1 : t = 1 := by rw [← hft, hf1, map_one]
      rw [ht1, orderOf_one] at ht5
      exact absurd ht5 (by norm_num)
    · exact hk
  let f₁ : G := (f : G) ^ 5 ^ (k - 1)
  have hf₁A : f₁ ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.pow_mem _ hfA _
  have hf₁5 : orderOf f₁ = 5 := by
    apply orderOf_eq_prime
    · change ((f : G) ^ 5 ^ (k - 1)) ^ 5 = 1
      rw [← pow_mul]
      have hk_eq : 5 ^ (k - 1) * 5 = 5 ^ k := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hk_eq, ← hfG, pow_orderOf_eq_one]
    · intro h1
      have hdvd : orderOf (f : G) ∣ 5 ^ (k - 1) := orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [hfG] at hdvd
      have hle : 5 ^ k ≤ 5 ^ (k - 1) :=
        Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
      have hlt : 5 ^ (k - 1) < 5 ^ k :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  have h5 : CFSG.pCore 2 ↥L = ⊥ :=
    pCore_two_eq_bot_of_j2 hfix hE25 h415 hS hhyp hθ hJ hf₁A hf₁5
  have hθ0 : aschbacherSolvableCore 3 ↥L = ⊥ := hθ.trans h5
  have hcop : Nat.Coprime 3 (orderOf (f : G)) := by
    rw [hfG]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 5)
  have hfL : (f : G) ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_j2 hfix hS hhyp hθ0 hJ hfA hcop
  exact ⟨f, k, f₁, hfA, hfG, hkpos, rfl, hf₁A, hf₁5, hfL, hft, h5, hθ0⟩

theorem hj_exists_commutator {A L M : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L))
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    {X K Y T : Subgroup G} (hC : Ctx155 A X K Y M T) (hLX : L ≤ X)
    (hW : wE155 A M ∉ scriptQ A (lB A)) (hcA : c ∈ A) :
    ∃ (w : G) (x : ↥(Res1C A L)),
      w ∈ wE155 A M ∧ (x : G) = w * c * w⁻¹ * c⁻¹ ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x ≠ 1 ∧
      w ∈ Res1C A L ∧ (x : G) ∈ wE155 A M ∧
      (x : G) ∈ Subgroup.centralizer (L : Set G) ∧ (x : G) ≠ 1 ∧
      ∃ k : ℕ, orderOf (x : G) = 2 ^ k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  obtain ⟨w, hwW, x, hxG, hxπ⟩ :=
    res1_exists_commutator_ne_one hS hhyp hAeq hC hLX hW
  have hL_E : L ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
    hLX.trans (Sylow155R1.x_le_oPrimeResidualOf_delta hC)
  have hwEL : wE155 A M ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hL_E))
  have hwCL : w ∈ Subgroup.centralizer (L : Set G) := hwEL hwW
  have hwC : w ∈ Res1C A L :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_right : A ⊓ L ≤ L))) hwCL
  have hAE : A ≤ Subgroup.normalizer
      ((oPrimeResidualOf 3 (delta A (lB A) M) : Subgroup G) : Set G) :=
    Sec14.le_normalizer_oPrimeResidualOf (le_normalizer_delta (A := A) (LB := lB A) M)
  have hAW : A ≤ Subgroup.normalizer (wE155 A M : Set G) :=
    Late.le_normalizer_inf (hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      fun a ha => CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer (hAE ha)
  have hcW : c ∈ Subgroup.normalizer (wE155 A M : Set G) := hAW hcA
  have hxW : (x : G) ∈ wE155 A M := by
    rw [hxG]
    have hconj : c * w⁻¹ * c⁻¹ ∈ wE155 A M :=
      (Subgroup.mem_normalizer_iff.mp hcW (w⁻¹)).mp (inv_mem hwW)
    have hprod : w * (c * w⁻¹ * c⁻¹) ∈ wE155 A M := (wE155 A M).mul_mem hwW hconj
    simpa [mul_assoc] using hprod
  have hxCL : (x : G) ∈ Subgroup.centralizer (L : Set G) := hwEL hxW
  have hx1 : (x : G) ≠ 1 := by
    intro h
    apply hxπ
    have hx1' : x = 1 := Subtype.ext h
    rw [hx1', map_one]
  have hxO2 : (x : G) ∈ CFSG.Open.pCoreOf 2 M :=
    (inf_le_left : wE155 A M ≤ CFSG.Open.pCoreOf 2 M) hxW
  obtain ⟨kx, hkx⟩ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_orderOf_eq_pow ⟨(x : G), hxO2⟩
  have hx2 : ∃ k, orderOf (x : G) = 2 ^ k := by
    refine ⟨kx, ?_⟩
    rwa [Subgroup.orderOf_mk] at hkx
  exact ⟨w, x, hwW, hxG, hxπ, hwC, hxW, hxCL, hx1, hx2⟩

theorem hj_exists_sylow_sup_zpowers {A L M : Subgroup G} {c : G} {Yc : Subgroup (Res1Q A L)}
    (hS : Sec14Std G A c L) (hY : Res1AtOf A c L M Yc) (hYF : Res1HJYFacts ↥Yc)
    (U : Sylow 2 ↥Yc)
    (hU : ∀ w : ↥(Res1C A L),
      (w : G) ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) →
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w ∈
          Subgroup.normalizer
            (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)))
    (c' : ↥(Res1C A L)) (hc' : (c' : G) = c)
    (hcU : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈
        Subgroup.normalizer
          (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)))
    (w : G) (hwW : w ∈ wE155 A M) (hwC : w ∈ Res1C A L)
    (x : ↥(Res1C A L)) (hxG : (x : G) = w * c * w⁻¹ * c⁻¹)
    (hxCL : (x : G) ∈ Subgroup.centralizer (L : Set G))
    (t' : ↥Yc) (ht'5 : orderOf t' = 5)
    (ht'N : t' ∈ Subgroup.normalizer (((U : Subgroup ↥Yc) : Set ↥Yc)))
    (htc : Commute (t' : Res1Q A L)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c')) :
    ∃ V : Subgroup (Res1Q A L),
      V = ((U : Subgroup ↥Yc).map Yc.subtype ⊔
        Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c')) ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x ∈ V ∧
      (t' : Res1Q A L) ∈ Subgroup.normalizer (V : Set (Res1Q A L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let t : Res1Q A L := (t' : Res1Q A L)
  let w' : ↥(Res1C A L) := ⟨w, hwC⟩
  have hw' : (w' : G) = w := rfl
  let π : ↥(Res1C A L) →* Res1Q A L :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  let y : Res1Q A L := π c'
  let V : Subgroup (Res1Q A L) :=
    (U : Subgroup ↥Yc).map Yc.subtype ⊔ Subgroup.zpowers y
  have hwU : π w' ∈ Subgroup.normalizer
      (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)) := by
    apply hU w'
    rw [hw']
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
      (CFSG.LieType.BorelTits.pCoreOf_le 2 M
        ((inf_le_left : wE155 A M ≤ CFSG.Open.pCoreOf 2 M) hwW))
  have hcommV : π (w' * c' * w'⁻¹ * c'⁻¹) ∈ V :=
    res1_commutator_mem_sup hS hY hYF U hc' hcU hwU
  have hxEq : x = w' * c' * w'⁻¹ * c'⁻¹ := by
    apply Subtype.ext
    rw [hxG]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc', hw']
  have hxV : π x ∈ V := by
    rw [hxEq]
    exact hcommV
  have htN : t ∈ Subgroup.normalizer
      (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)) := by
    have hmem : Yc.subtype t' ∈ Subgroup.map Yc.subtype
        (Subgroup.normalizer ((U : Subgroup ↥Yc) : Set ↥Yc)) :=
      Subgroup.mem_map_of_mem Yc.subtype ht'N
    have h := Subgroup.le_normalizer_map Yc.subtype hmem
    simpa [t] using h
  have hconj : (MulAut.conj t) y = y := by
    rw [MulAut.conj_apply]
    change t * y * t⁻¹ = y
    rw [htc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have htNormV : t ∈ Subgroup.normalizer (V : Set (Res1Q A L)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp [V]
    rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp htN,
      MonoidHom.map_zpowers]
    change Subgroup.map Yc.subtype ↑U ⊔ Subgroup.zpowers ((MulAut.conj t) y) =
      Subgroup.map Yc.subtype ↑U ⊔ Subgroup.zpowers y
    rw [hconj]
  exact ⟨V, rfl, hxV, htNormV⟩

theorem hj_exists_centralizer_preimage {A L : Subgroup G}
    (V : Subgroup (Res1Q A L)) (x : ↥(Res1C A L))
    (hxV : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x ∈ V)
    (hxCL : (x : G) ∈ Subgroup.centralizer (L : Set G)) :
    ∃ (π : ↥(Res1C A L) →* Res1Q A L) (W1 Utilde : Subgroup G),
      π = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) ∧
      W1 = (V.comap π).map (Res1C A L).subtype ∧
      Utilde = W1 ⊓ Subgroup.centralizer (L : Set G) ∧ (x : G) ∈ Utilde := by
  let π : ↥(Res1C A L) →* Res1Q A L :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  let W1 : Subgroup G := (V.comap π).map (Res1C A L).subtype
  let Utilde : Subgroup G := W1 ⊓ Subgroup.centralizer (L : Set G)
  have hxW1 : (x : G) ∈ W1 :=
    Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mpr hxV, rfl⟩
  have hxUtilde : (x : G) ∈ Utilde := Subgroup.mem_inf.mpr ⟨hxW1, hxCL⟩
  exact ⟨π, W1, Utilde, rfl, rfl, rfl, hxUtilde⟩

theorem hj_mem_normalizer_preimage {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)}
    (V : Subgroup (Res1Q A L)) (W1 : Subgroup G) (π : ↥(Res1C A L) →* Res1Q A L)
    (hW1def : W1 = (V.comap π).map (Res1C A L).subtype)
    (t' : ↥Yc) (htNormV : (t' : Res1Q A L) ∈ Subgroup.normalizer (V : Set (Res1Q A L)))
    (f : ↥(Res1C A L)) (hft : π f = (t' : Res1Q A L))
    (hfA : (f : G) ∈ Subgroup.centralizer (A : Set G)) :
    (f : G) ∈ Subgroup.normalizer (W1 : Set G) := by
  have hfRes : (f : G) ∈ Subgroup.normalizer (Res1C A L : Set G) := by
    have hfC : (f : G) ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)) hfA
    have hfNA : (f : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer ((A ⊓ L : Subgroup G) : Set G) hfC
    exact CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer hfNA
  rw [hW1def]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨z0, hz0, rfl⟩
    have hz0V : π z0 ∈ V := Subgroup.mem_comap.mp hz0
    refine ⟨f * z0 * f⁻¹, ?_, rfl⟩
    show π (f * z0 * f⁻¹) ∈ V
    have hz1 : π (f * z0 * f⁻¹) = (t' : Res1Q A L) * π z0 * (t' : Res1Q A L)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hft]
    rw [hz1]
    exact (Subgroup.mem_normalizer_iff.mp htNormV (π z0)).mp hz0V
  · rintro ⟨z0, hz0, hz0f⟩
    refine ⟨f⁻¹ * z0 * f, ?_, ?_⟩
    · show π (f⁻¹ * z0 * f) ∈ V
      have hz0V : π z0 ∈ V := Subgroup.mem_comap.mp hz0
      have hz1 : π (f⁻¹ * z0 * f) = (t' : Res1Q A L)⁻¹ * π z0 * (t' : Res1Q A L) := by
        rw [map_mul, map_mul, map_inv, hft]
      rw [hz1]
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htNormV) (π z0)).mp hz0V
    · show (Res1C A L).subtype (f⁻¹ * z0 * f) = z
      change (f : G)⁻¹ * (z0 : G) * (f : G) = z
      have hz0f' : (z0 : G) = (f : G) * z * (f : G)⁻¹ := hz0f
      rw [hz0f']
      group

theorem hj_mem_normalizer_inf_centralizer {L : Subgroup G} (W1 Utilde : Subgroup G)
    (hUtildeDef : Utilde = W1 ⊓ Subgroup.centralizer (L : Set G))
    (f : G) (hfW1 : f ∈ Subgroup.normalizer (W1 : Set G))
    (hfL : f ∈ Subgroup.centralizer (L : Set G)) :
    f ∈ Subgroup.normalizer (Utilde : Set G) := by
  rw [hUtildeDef]
  have h1 : Subgroup.zpowers f ≤ Subgroup.normalizer (W1 : Set G) :=
    Subgroup.zpowers_le.mpr hfW1
  have hfNCL : f ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set G)) : Set G) :=
    CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer
      (Subgroup.centralizer_le_normalizer (L : Set G) hfL)
  have h2 : Subgroup.zpowers f ≤
      Subgroup.normalizer ((Subgroup.centralizer (L : Set G)) : Set G) :=
    Subgroup.zpowers_le.mpr hfNCL
  exact (Late.le_normalizer_inf h1 h2) (Subgroup.mem_zpowers f)

theorem hj_not_mem_sylow_sup_zpowers {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)}
    (V : Subgroup (Res1Q A L)) (U : Sylow 2 ↥Yc) (q t : Res1Q A L)
    (hVdef : V = (U : Subgroup ↥Yc).map Yc.subtype ⊔ Subgroup.zpowers q)
    (hy3 : orderOf q = 3) (ht5 : orderOf t = 5)
    (hcU : q ∈ Subgroup.normalizer
      (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L))) :
    t ∉ V := by
  intro htV
  have h5dvd : 5 ∣ Nat.card V := by
    have := Subgroup.orderOf_dvd_natCard V htV
    rwa [ht5] at this
  have hK2 : IsPGroup 2 ((U : Subgroup ↥Yc).map Yc.subtype) :=
    (U.isPGroup' : IsPGroup 2 ↥(U : Subgroup ↥Yc)).map Yc.subtype
  have hHnorm : Subgroup.zpowers q ≤ Subgroup.normalizer
      (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)) :=
    Subgroup.zpowers_le.mpr hcU
  have hcard :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers q) (K := (U : Subgroup ↥Yc).map Yc.subtype) hHnorm
  have hH3 : Nat.card (Subgroup.zpowers q) = 3 := by
    rw [Nat.card_zpowers, hy3]
  obtain ⟨kk, hkk⟩ := hK2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers q))
      (Nat.card ((U : Subgroup ↥Yc).map Yc.subtype)) := by
    rw [hH3, hkk]
    exact Nat.Coprime.pow_right kk (by norm_num : Nat.Coprime 3 2)
  have hdisj : Subgroup.zpowers q ⊓ ((U : Subgroup ↥Yc).map Yc.subtype) = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime hcop
  have hVcard : Nat.card V = 2 ^ kk * 3 := by
    have h := hcard
    rw [hdisj, Subgroup.card_bot, mul_one, hH3, hkk] at h
    rw [hVdef]
    simpa [sup_comm, mul_comm] using h
  have h5not : ¬ 5 ∣ Nat.card V := by
    rw [hVcard]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h2 | h3
    · have := Nat.prime_five.dvd_of_dvd_pow h2
      norm_num at this
    · norm_num at h3
  exact h5not h5dvd

theorem hj_not_mem_inf_centralizer {A L : Subgroup G}
    (V : Subgroup (Res1Q A L)) (π : ↥(Res1C A L) →* Res1Q A L)
    (W1 Utilde : Subgroup G)
    (hW1def : W1 = (V.comap π).map (Res1C A L).subtype)
    (hUtildeDef : Utilde = W1 ⊓ Subgroup.centralizer (L : Set G))
    (f : ↥(Res1C A L)) (t : Res1Q A L) (hft : π f = t) (htNotV : t ∉ V) :
    (f : G) ∉ Utilde := by
  intro hf
  rw [hUtildeDef] at hf
  have hfW1' : (f : G) ∈ W1 := (Subgroup.mem_inf.mp hf).1
  rw [hW1def] at hfW1'
  rw [Subgroup.mem_map] at hfW1'
  obtain ⟨z, hz, hzG⟩ := hfW1'
  have hzV : π z ∈ V := Subgroup.mem_comap.mp hz
  have hzf : z = f := Subtype.ext hzG
  rw [hzf, hft] at hzV
  exact htNotV hzV

theorem hj_exists_two_subgroup_five_normalizer {L : Subgroup G} (Utilde : Subgroup G)
    (hUtilde_le_CL : Utilde ≤ Subgroup.centralizer (L : Set G))
    (f x : G) (hfUtilde : f ∈ Subgroup.normalizer (Utilde : Set G))
    (hfL : f ∈ Subgroup.centralizer (L : Set G)) (hfNotUtilde : f ∉ Utilde)
    (hxUtilde : x ∈ Utilde) (hx1 : x ≠ 1) (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k)
    (k : ℕ) (hfG : orderOf f = 5 ^ k) :
    ∃ (S : Subgroup G) (z : G), S ≤ Utilde ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      orderOf z = 5 ∧ z ∈ (Utilde ⊔ Subgroup.zpowers f) ∧
      z ∈ Subgroup.normalizer (S : Set G) ∧ z ∈ Subgroup.centralizer (L : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hSU, hSne, hS2, z, hz5, hzUf, hzS⟩ :=
    exists_five_mem_normalizer_two hfUtilde ⟨k, hfG⟩ hfNotUtilde hxUtilde hx1 hx2
  have hzCL : z ∈ Subgroup.centralizer (L : Set G) :=
    (sup_le hUtilde_le_CL (Subgroup.zpowers_le.mpr hfL)) hzUf
  exact ⟨S, z, hSU, hSne, hS2, hz5, hzUf, hzS, hzCL⟩

theorem hj_exists_elemAbelian_25_centralizer {L : Subgroup G} (hE25 : J2HasE25) (h415 : Sec4.Item4_15)
    (hθ0 : aschbacherSolvableCore 3 ↥L = ⊥)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (Utilde S : Subgroup G) (z : G)
    (hSU : S ≤ Utilde) (hUtilde_le_CL : Utilde ≤ Subgroup.centralizer (L : Set G))
    (hz5 : orderOf z = 5) (hzCL : z ∈ Subgroup.centralizer (L : Set G)) :
    ∃ E₂ : Subgroup G, CFSG.Open.IsElemAbelian 5 E₂ ∧ Nat.card E₂ = 25 ∧
      z ∈ Subgroup.centralizer (E₂ : Set G) ∧ z ∉ E₂ ∧
      E₂ ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨E₂, hEab, hEcard, hE_le_L⟩ := res1_exists_elemAbelian_25_le hθ0 hJ hE25
  obtain ⟨e⟩ := hJ
  have hJ' : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hθ0).trans
      (QuotientGroup.quotientBot (G := ↥L))).symm.trans e⟩
  have hcenterL : Subgroup.center ↥L = ⊥ :=
    KFacts.KS14.center_eq_bot_of_j2 h415 hJ'
  have hzE : z ∈ Subgroup.centralizer (E₂ : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE_le_L)) hzCL
  have hzNotE : z ∉ E₂ := by
    intro hzE
    have hzL : z ∈ L := hE_le_L hzE
    have hzCenter : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzCL (w : G) w.2)
    rw [hcenterL, Subgroup.mem_bot] at hzCenter
    have hz1 : z = 1 := congrArg Subtype.val hzCenter
    rw [hz1, orderOf_one] at hz5
    exact absurd hz5 (by norm_num)
  have hS_CL : S ≤ Subgroup.centralizer (L : Set G) := hSU.trans hUtilde_le_CL
  have hL_CS : L ≤ Subgroup.centralizer (S : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hS_CL hs) l hl).symm
  have hL_NS : L ≤ Subgroup.normalizer (S : Set G) :=
    fun l hl => Subgroup.centralizer_le_normalizer (S : Set G) (hL_CS hl)
  have hE_NS : E₂ ≤ Subgroup.normalizer (S : Set G) := hE_le_L.trans hL_NS
  exact ⟨E₂, hEab, hEcard, hzE, hzNotE, hE_NS⟩

theorem hj_false_of_e125 {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    (S E₂ : Subgroup G) (z : G)
    (hEab : CFSG.Open.IsElemAbelian 5 E₂) (hEcard : Nat.card E₂ = 25)
    (hzE : z ∈ Subgroup.centralizer (E₂ : Set G)) (hz5 : orderOf z = 5)
    (hzNotE : z ∉ E₂) (hSne : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hE_NS : E₂ ≤ Subgroup.normalizer (S : Set G))
    (hzS : z ∈ Subgroup.normalizer (S : Set G)) : False := by
  have hlr : CFSG.Assembly.RankThreeEven.localRank 5 G < 3 :=
    hS.localRank_lt 5 Nat.prime_five (by norm_num)
  exact false_of_e125 hlr hEab hEcard hzE hz5 hzNotE hSne hS2 hE_NS hzS

theorem hj_exists_five_commute {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)}
    (hYF : Res1HJYFacts ↥Yc) (U : Sylow 2 ↥Yc) (c' : ↥(Res1C A L))
    (hyYc : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc)
    (hy3 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') = 3)
    (hyU : (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc) ∈
      Subgroup.normalizer (((U : Subgroup ↥Yc) : Set ↥Yc))) :
    ∃ t' : ↥Yc, t' ∈ Subgroup.normalizer (((U : Subgroup ↥Yc) : Set ↥Yc)) ∧
      orderOf t' = 5 ∧
      Commute (t' : Res1Q A L) (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') := by
  have hyc3 : orderOf (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ : ↥Yc) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hy3
  obtain ⟨t', ht'N, ht'5, ht'comm⟩ :=
    hYF.2.2 U ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hyYc⟩ hyU hyc3
  exact ⟨t', ht'N, ht'5, congrArg Subtype.val ht'comm⟩

theorem false_of_hj_le (hfix : J2AutFixNine) (hE25 : J2HasE25) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) (h142 : Concl142 A (lB A))
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) (hLX : L ≤ X)
    {Yc : Subgroup (Res1Q A L)} (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hYF : Res1HJYFacts ↥Yc) (hW : wE155 A M ∉ scriptQ A (lB A)) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c', hc', hcC, hcA, hc3, hcL, hhyp, hAeq⟩ := hj_exists_res1C_lift hS hY
  obtain ⟨U, hAM, hcU, hU⟩ := hj_exists_sylow_two_normalized hS h142 hY hsimple hYF hC c' hc' hcA
  obtain ⟨hc'3, hyYc, hy3⟩ := hj_orderOf_mk_eq_three hY c' hc' hc3
  have hyU := hj_mem_normalizer_sylow U c' hcU hyYc
  obtain ⟨t', ht'N, ht'5, htc⟩ := hj_exists_five_commute hYF U c' hyYc hy3 hyU
  obtain ⟨f, k, f₁, hfA, hfG, hkpos, hf₁eq, hf₁A, hf₁5, hfL, hft, h5, hθ0⟩ :=
    hj_exists_five_lift hfix hE25 h415 hS hθ hJ hAeq c' hc' hhyp t' ht'5 htc
  obtain ⟨w, x, hwW, hxG, hxπ, hwC, hxW, hxCL, hx1, hx2⟩ :=
    hj_exists_commutator hS hhyp hAeq hC hLX hW hcA
  obtain ⟨V, hVdef, hxV, htNormV⟩ :=
    hj_exists_sylow_sup_zpowers hS hY hYF U hU c' hc' hcU w hwW hwC x hxG hxCL t' ht'5 ht'N htc
  obtain ⟨π, W1, Utilde, hπdef, hW1def, hUtildeDef, hxUtilde⟩ :=
    hj_exists_centralizer_preimage V x hxV hxCL
  have hftπ : π f = (t' : Res1Q A L) := by rw [hπdef]; exact hft
  have hfW1 : (f : G) ∈ Subgroup.normalizer (W1 : Set G) :=
    hj_mem_normalizer_preimage V W1 π hW1def t' htNormV f hftπ hfA
  have hfUtilde : (f : G) ∈ Subgroup.normalizer (Utilde : Set G) :=
    hj_mem_normalizer_inf_centralizer W1 Utilde hUtildeDef (f : G) hfW1 hfL
  have ht5' : orderOf (t' : Res1Q A L) = 5 := by
    rw [Subgroup.orderOf_coe, ht'5]
  have htNotV : (t' : Res1Q A L) ∉ V :=
    hj_not_mem_sylow_sup_zpowers V U (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') (t' : Res1Q A L) hVdef hy3 ht5' hcU
  have hfNotUtilde : (f : G) ∉ Utilde :=
    hj_not_mem_inf_centralizer V π W1 Utilde hW1def hUtildeDef f (t' : Res1Q A L) hftπ htNotV
  have hUtilde_le_CL : Utilde ≤ Subgroup.centralizer (L : Set G) := by
    rw [hUtildeDef]
    exact inf_le_right
  obtain ⟨S, z, hSU, hSne, hS2, hz5, hzUf, hzS, hzCL⟩ :=
    hj_exists_two_subgroup_five_normalizer Utilde hUtilde_le_CL (f : G) (x : G) hfUtilde hfL hfNotUtilde
      hxUtilde hx1 hx2 k hfG
  obtain ⟨E₂, hEab, hEcard, hzE, hzNotE, hE_NS⟩ :=
    hj_exists_elemAbelian_25_centralizer hE25 h415 hθ0 hJ Utilde S z hSU hUtilde_le_CL hz5 hzCL
  exact hj_false_of_e125 hS S E₂ z hEab hEcard hzE hz5 hzNotE hSne hS2 hE_NS hzS

theorem step155HostE0WRes1TypeFBarLe_hj (h149 : Sec16.Item149S14) (h142 : Sec14.Concl142S14)
    (hfix : J2AutFixNine) (hE25 : J2HasE25) (h415 : Sec4.Item4_15) (hθ : HJThetaS14)
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hYF : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → P Y → Res1HJYFacts Y) :
    Step155HostE0WRes1TypeFBarLe
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX
  by_cases hWQ : wE155 A M ∈ scriptQ A (lB A)
  · rw [CFSG.RankThree.PartTwo.Sec15.Sylow155R1.pPrimeCoreOf_two_host_eq_bot_of_wE155_mem
      hS h146 (h149 G A c L hS) hC hE hRP hIX hWQ]
    exact bot_le
  · exact (false_of_hj_le hfix hE25 h415 hS (h142 G A c L hS) (hθ G A c L hS hq) hq hC hLX hY
      hsimple (hYF _ hsimple hP) hWQ).elim

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
