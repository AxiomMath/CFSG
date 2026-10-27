module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
import CFSG.Sporadic.Schreier.TitsIso
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.SPEBasics
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicBase
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
  (pow_eq_one_of_torus)
open CFSG.ComponentClassification.CoprimeAutomorphisms (eq_one_of_fixed_displacement)

theorem FixedFreeFive.of_torusLocal {L : Type*} [Group L] [Finite L] {R : Subgroup L}
    (hT : TorusLocal 5 R) : FixedFreeFive 5 L := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcard, -, -, -, t, htN, m, lam, -, hm, hlam, -, hpow, -, hline⟩ := hT
  have hexp : ∀ x ∈ R, x ^ 5 = 1 :=
    pow_eq_one_of_torus Nat.prime_five hcard htN fun Y₀ hY₀ hY₀c => by
      simpa using hline 1 one_pos (by omega) Y₀ hY₀ hY₀c
  have hRpg : IsPGroup 5 R := IsPGroup.of_card (n := 2) hcard
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq hcard ⟨a, ha⟩ ⟨b, hb⟩)
  have hord5 : ∀ s ∈ R, s ≠ 1 → orderOf s = 5 := by
    intro s hs hs1
    have h5 : orderOf s ∣ 5 := orderOf_dvd_iff_pow_eq_one.2 (hexp s hs)
    rcases (Nat.dvd_prime Nat.prime_five).1 h5 with h1 | h5'
    · exact absurd h1 (fun h => hs1 (orderOf_eq_one_iff.mp h))
    · exact h5'
  refine ⟨R, hRpg, hRne, hRcomm, t, htN, ?_⟩
  intro k hk0 hk5 s hs hfix
  by_contra hs1
  have hord : orderOf s = 5 := hord5 s hs hs1
  let q := k / m
  let r := k % m
  have hmpos : 0 < m := by omega
  have hk_eq : m * q + r = k := Nat.div_add_mod k m
  have hrlt : r < m := Nat.mod_lt k hmpos
  have hq_le : q ≤ 2 := by
    have h1 : 2 * q ≤ m * q := Nat.mul_le_mul_right q hm
    have h2 : m * q ≤ k := by omega
    omega
  have hpowq : ∀ q : ℕ, ∀ x ∈ R, t ^ (m * q) * x * (t ^ (m * q))⁻¹ = x ^ (lam ^ q) := by
    intro q
    induction q with
    | zero => intro x hx; simp
    | succ q ih =>
      intro x hx
      have hxlam : x ^ lam ∈ R := Subgroup.pow_mem R hx lam
      calc
        t ^ (m * (q + 1)) * x * (t ^ (m * (q + 1)))⁻¹
            = t ^ (m * q) * (t ^ m * x * (t ^ m)⁻¹) * (t ^ (m * q))⁻¹ := by
                rw [Nat.mul_succ, pow_add]
                group
        _ = t ^ (m * q) * (x ^ lam) * (t ^ (m * q))⁻¹ := by rw [hpow x hx]
        _ = (x ^ lam) ^ (lam ^ q) := ih (x ^ lam) hxlam
        _ = x ^ (lam ^ (q + 1)) := by
              rw [← pow_mul, pow_succ, Nat.mul_comm]
  let y : L := t ^ r * s * (t ^ r)⁻¹
  have hyR : y ∈ R := by
    have htrN : t ^ r ∈ Subgroup.normalizer (R : Set L) := Subgroup.pow_mem _ htN r
    exact (Subgroup.mem_normalizer_iff.mp htrN s).1 hs
  have hy_eq : y ^ (lam ^ q) = s := by
    have h := hpowq q y hyR
    calc y ^ (lam ^ q) = t ^ (m * q) * y * (t ^ (m * q))⁻¹ := h.symm
      _ = (t ^ (m * q) * t ^ r) * s * ((t ^ (m * q) * t ^ r))⁻¹ := by
            unfold y
            group
      _ = t ^ (m * q + r) * s * (t ^ (m * q + r))⁻¹ := by rw [pow_add]
      _ = t ^ k * s * (t ^ k)⁻¹ := by rw [hk_eq]
      _ = s := hfix
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hy_s : y = s := by simp [y, hr]
    have hpow_s : s ^ (lam ^ q) = s ^ 1 := by simpa [hy_s] using hy_eq
    have hmod : lam ^ q ≡ 1 [MOD 5] := by
      have h := (pow_eq_pow_iff_modEq (x := s)).1 hpow_s
      rwa [hord] at h
    have hz : ((lam : ZMod 5) ^ q) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff (lam ^ q) 1 5).2 hmod
      simpa [Nat.cast_pow] using h
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hq | hq
      · rw [hq, hr, mul_zero, zero_add] at hk_eq
        omega
      · exact hq
    have hq12 : q = 1 ∨ q = 2 := by omega
    rcases hq12 with hq1 | hq2
    · rw [hq1, pow_one] at hz
      rw [hz] at hlam
      simpa using hlam
    · rw [hq2] at hz
      have hdvd : orderOf ((lam : ZMod 5)) ∣ 2 := (orderOf_dvd_iff_pow_eq_one).2 hz
      rw [hlam] at hdvd
      norm_num at hdvd
  · have hyord : orderOf y = orderOf s := by
      have hconj : SemiconjBy (t ^ r) s y := by
        unfold y SemiconjBy
        group
      exact hconj.orderOf_eq.symm
    have hyord5 : orderOf y = 5 := by rw [hyord, hord]
    have hs_mem : s ∈ Subgroup.zpowers y := by
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨((lam ^ q : ℕ) : ℤ), by rw [zpow_natCast]; exact hy_eq⟩
    have hy_mem : y ∈ Subgroup.zpowers s := by
      let Y : Subgroup L := Subgroup.zpowers y
      haveI : IsCyclic Y := Subgroup.isCyclic_zpowers y
      let sY : Y := ⟨s, hs_mem⟩
      have hYcard : Nat.card Y = 5 := by rw [Nat.card_zpowers, hyord5]
      have hsYcard : Nat.card (Subgroup.zpowers sY) = 5 := by
        rw [Nat.card_zpowers]
        calc orderOf sY = orderOf ((sY : Y) : L) := (Subgroup.orderOf_coe sY).symm
          _ = orderOf s := by rfl
          _ = 5 := hord
      have hgen : Subgroup.zpowers sY = ⊤ := by
        rw [eq_comm, IsCyclic.subgroup_eq_iff_card_eq]
        rw [hsYcard, Subgroup.card_top, hYcard]
      have hyY : (⟨y, Subgroup.mem_zpowers y⟩ : Y) ∈ Subgroup.zpowers sY := by
        rw [hgen]
        exact Subgroup.mem_top _
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hyY
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨j, ?_⟩
      have := congrArg (fun x : Y => (x : L)) hj
      simpa using this
    have htrN : t ^ r ∈ Subgroup.normalizer (Subgroup.zpowers s : Set L) := by
      refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← hj]
      have hconjz : t ^ r * s ^ j * (t ^ r)⁻¹ = y ^ j := by
        simpa [y, MulAut.conj_apply] using map_zpow (MulAut.conj (t ^ r)).toMonoidHom s j
      rw [hconjz]
      exact Subgroup.zpow_mem (Subgroup.zpowers s) hy_mem j
    exact (hline r hr hrlt (Subgroup.zpowers s) (Subgroup.zpowers_le.2 hs)
      (by rw [Nat.card_zpowers, hord]) (by simpa using htrN))

section Certificates


theorem fixedFreeFive_tits
    {L : Type} [Group L] [Finite L] (hL : CFSG.AGLEmbedding.IsTitsGroup L) :
    FixedFreeFive 5 L := by
  obtain ⟨eD⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits hL
  have hcent : Subgroup.center L = ⊥ := by
    have hmap := Subgroup.map_center_eq eD
    rw [CFSG.Sporadic.Schreier.Tits.titsD_center] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center L) eD.injective).mp hmap
  have hKc : Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    exact hcent
  let eS : (⊤ : Subgroup L) ≃* CFSG.Sporadic.Schreier.Tits.titsD :=
    Subgroup.topEquiv.trans eD
  let R : Sylow 5 L := Classical.choice inferInstance
  have hT : TorusLocal 5 (R : Subgroup L) :=
    CFSG.AGLEmbeddingD2.torusLocal_tits_sylow hKc eS R
  exact FixedFreeFive.of_torusLocal hT

theorem good_tits
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (hL : CFSG.AGLEmbedding.IsTitsGroup ↥(CFSG.generalizedFitting X)) :
    Good 5 N := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let K : Subgroup X := CFSG.generalizedFitting X
  obtain ⟨hKsimple, hKnab, hKnormal, hKc⟩ :
      IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧ K.Normal ∧
        Subgroup.centralizer (K : Set X) = ⊥ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) (by norm_num) hO hN
  haveI : K.Normal := hKnormal
  obtain ⟨eD⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits hL
  obtain ⟨P, hPsyl, hPN⟩ := hN.exists_isSylowOf_le
  have hPindex : ¬ 5 ∣ P.index := by
    have := hPsyl.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let R : Sylow 5 X := hPsyl.2.1.toSylow hPindex
  have hRcoe : (R : Subgroup X) = P := IsPGroup.toSylow_coe hPsyl.2.1 hPindex
  have hRN : (R : Subgroup X) ≤ N := hRcoe ▸ hPN
  have hT : TorusLocal 5 (R : Subgroup X) :=
    CFSG.AGLEmbeddingD2.torusLocal_tits_sylow hKc eD R
  obtain ⟨hRcard, hRmax, hRC, -, t, htN, m, -, -, hm, -, -, -, -, hline⟩ := hT
  have hTpow : ∀ x ∈ (R : Subgroup X), x ^ 5 = 1 :=
    pow_eq_one_of_torus Nat.prime_five hRcard htN fun Y₀ hY₀ hY₀c => by
      simpa using hline 1 one_pos (by omega) Y₀ hY₀ hY₀c
  have hRpg : IsPGroup 5 (R : Subgroup X) := R.isPGroup'
  have hRne : (R : Subgroup X) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hRcard
    norm_num at hRcard
  have hNR : Subgroup.normalizer (R : Set X) ≤ N := hN.normalizer_le hRne hRpg hRN
  have hN_eq : N = Subgroup.normalizer (R : Set X) := by
    rcases hRmax N hNR with h | h
    · exact h
    · exact absurd h hN.1
  have hO_N : CFSG.pPrimeCore 5 ↥N = ⊥ :=
    pPrimeCore_eq_bot_of_centralizer_le hRN hRpg (le_of_eq hN_eq) hRC
  refine ⟨hO_N, ?_⟩
  intro x y hxN hyN hx1 hx5 hyprime hy2 hy5 hcomm
  have hRsubN_normal : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr (le_of_eq hN_eq)
  let PN : Sylow 5 ↥N := R.subtype hRN
  have hPNcoe : (PN : Subgroup ↥N) = R.subgroupOf N := Sylow.coe_subtype R hRN
  haveI : (PN : Subgroup ↥N).Normal := by rw [hPNcoe]; exact hRsubN_normal
  have hx5N : IsPGroup 5 (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) := by
    obtain ⟨k, hk⟩ := hx5.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    calc Nat.card (Subgroup.zpowers (⟨x, hxN⟩ : ↥N))
        = orderOf (⟨x, hxN⟩ : ↥N) := Nat.card_zpowers _
      _ = orderOf x := (Subgroup.orderOf_coe _).symm
      _ = Nat.card (Subgroup.zpowers x) := (Nat.card_zpowers x).symm
      _ = 5 ^ k := hk
  obtain ⟨Q, hxQ⟩ := hx5N.exists_le_sylow
  haveI : Unique (Sylow 5 ↥N) := Sylow.unique_of_normal PN (by rwa [hPNcoe])
  have hQeq : Q = PN := Subsingleton.elim Q PN
  have hxPN : (⟨x, hxN⟩ : ↥N) ∈ (PN : Subgroup ↥N) := by
    rw [← hQeq]
    exact hxQ (Subgroup.mem_zpowers _)
  have hxR : x ∈ (R : Subgroup X) := by
    have hxsub : (⟨x, hxN⟩ : ↥N) ∈ R.subgroupOf N := by
      rwa [← hPNcoe]
    exact (Subgroup.mem_subgroupOf).1 hxsub
  have hyNorm : y ∈ Subgroup.normalizer (R : Set X) := hN_eq ▸ hyN
  let xR : ↥(R : Subgroup X) := ⟨x, hxR⟩
  have hxR1 : xR ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  have hxR5 : orderOf xR = 5 := by
    have hxRpow : xR ^ 5 = 1 := by
      apply Subtype.ext
      have := hTpow x hxR
      simpa [xR] using this
    have hdvd : orderOf xR ∣ 5 := orderOf_dvd_iff_pow_eq_one.2 hxRpow
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hxR1
    · exact h5
  let D : Subgroup ↥(R : Subgroup X) := Subgroup.zpowers xR
  have hDcard : Nat.card D = 5 := by
    rw [show D = Subgroup.zpowers xR from rfl, Nat.card_zpowers, hxR5]
  haveI : IsMulCommutative ↥(R : Subgroup X) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hRcard
  have hDnormal : D.Normal := Subgroup.normal_of_comm D
  haveI : D.Normal := hDnormal
  let α : MulAut ↥(R : Subgroup X) :=
    Subgroup.normalizerMonoidHom (R : Subgroup X) ⟨y, hyNorm⟩
  have hαx : α xR = xR := by
    dsimp only [α]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change y * x * y⁻¹ = x
    rw [← hcomm]
    group
  have hαDfix : ∀ d ∈ D, α d = d := by
    intro d hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    rw [map_zpow, hαx]
  have hαDmap : Subgroup.map (α : ↥(R : Subgroup X) →* ↥(R : Subgroup X)) D = D := by
    rw [show D = Subgroup.zpowers xR from rfl, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hαx
  let β : MulAut (↥(R : Subgroup X) ⧸ D) := QuotientGroup.congr D D α hαDmap
  have hQcard : Nat.card (↥(R : Subgroup X) ⧸ D) = 5 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup D
    rw [hRcard, hDcard] at h
    omega
  have hαord : orderOf α ∣ orderOf y := by
    have h := orderOf_map_dvd (Subgroup.normalizerMonoidHom (R : Subgroup X)) ⟨y, hyNorm⟩
    rwa [Subgroup.orderOf_mk] at h
  have hβpow : β ^ orderOf y = 1 := by
    have hαpow : α ^ orderOf y = 1 := orderOf_dvd_iff_pow_eq_one.1 hαord
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H z =>
      have hβapply : ∀ n : ℕ, ∀ z : ↥(R : Subgroup X),
          (β ^ n) (QuotientGroup.mk z : ↥(R : Subgroup X) ⧸ D) =
          QuotientGroup.mk ((α ^ n) z) := by
        intro n
        induction n with
        | zero => intro z; simp
        | succ n ih =>
          intro z
          rw [pow_succ, MulAut.mul_apply]
          dsimp only [β]
          rw [QuotientGroup.congr_mk]
          rw [ih (α z)]
          rw [pow_succ, MulAut.mul_apply]
      rw [hβapply (orderOf y) z, hαpow]
      simp
  have hβord_r : orderOf β ∣ orderOf y := orderOf_dvd_of_pow_eq_one hβpow
  have hcyc : IsCyclic (↥(R : Subgroup X) ⧸ D) := isCyclic_of_prime_card hQcard
  have hMulAutCard : Nat.card (MulAut (↥(R : Subgroup X) ⧸ D)) = 4 := by
    rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime Nat.prime_five]
  have hβord_4 : orderOf β ∣ 4 := by
    have := orderOf_dvd_natCard β
    rwa [hMulAutCard] at this
  have hy5cop : Nat.Coprime (orderOf y) 5 := by
    have hnot5 : ¬ 5 ∣ orderOf y := by
      intro h
      rcases (Nat.dvd_prime hyprime).1 h with h1 | h5
      · norm_num at h1
      · exact hy5 h5.symm
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hnot5).symm
  have hy4cop : Nat.Coprime (orderOf y) 4 := by
    have hnot2 : ¬ 2 ∣ orderOf y := by
      intro h
      rcases (Nat.dvd_prime hyprime).1 h with h1 | h2
      · norm_num at h1
      · exact hy2 h2.symm
    have hcop24 : Nat.Coprime 2 (orderOf y) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnot2
    have hcop44 : Nat.Coprime 4 (orderOf y) := by
      simpa using hcop24.pow_left 2
    exact hcop44.symm
  have hβ1 : β = 1 := by
    have hgcd : orderOf β ∣ Nat.gcd (orderOf y) 4 := Nat.dvd_gcd hβord_r hβord_4
    rw [hy4cop.gcd_eq_one] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hdisp : ∀ z : ↥(R : Subgroup X), z⁻¹ * α z ∈ D := by
    intro z
    have hmk : QuotientGroup.mk (α z) = (QuotientGroup.mk z : ↥(R : Subgroup X) ⧸ D) := by
      have h := congrArg (fun f : MulAut (↥(R : Subgroup X) ⧸ D) => f (QuotientGroup.mk z)) hβ1
      dsimp only [β] at h
      rw [QuotientGroup.congr_mk] at h
      simpa using h
    exact QuotientGroup.eq.mp hmk.symm
  have hαcop : Nat.Coprime (orderOf α) 5 := Nat.Coprime.of_dvd_left hαord hy5cop
  have hα1 : α = 1 :=
    eq_one_of_fixed_displacement D α (orderOf α) (pow_orderOf_eq_one α)
      (by rw [hDcard]; exact hαcop) hαDfix hdisp
  have hyC : y ∈ Subgroup.centralizer (R : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hα1z : α ⟨z, hz⟩ = ⟨z, hz⟩ := by
      rw [hα1]
      rfl
    have hcoe := congrArg (fun w : ↥(R : Subgroup X) => (w : X)) hα1z
    dsimp only [α] at hcoe
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hcoe
    calc z * y = (y * z * y⁻¹) * y := by rw [hcoe]
      _ = y * z := by group
  have hyR : y ∈ (R : Subgroup X) := hRC hyC
  have hyRne : (⟨y, hyR⟩ : ↥(R : Subgroup X)) ≠ 1 := by
    intro h
    have hy1 : y = 1 := congrArg Subtype.val h
    rw [hy1, orderOf_one] at hyprime
    exact hyprime.ne_one rfl
  have h5dvd : 5 ∣ orderOf y := by
    have h := hRpg.dvd_orderOf hyRne
    rwa [← Subgroup.orderOf_coe] at h
  rcases (Nat.dvd_prime hyprime).1 h5dvd with h1 | h5
  · norm_num at h1
  · exact False.elim (hy5 h5.symm)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
