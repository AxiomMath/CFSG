module

public import CFSG.RankThree.PartTwo.Sec17.C174Base
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
public import CFSG.RankThree.PartTwo.Sec17.G1724J2
public import CFSG.Quasithin.H13.A7SectionRank
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement
open CFSG.Open

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem theta_eq_pCore_two_of_j2
    (h135 : Item135) (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L := by
  obtain ⟨φ⟩ := hJ
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    h135 G A c L h.toSec13Data h.hypS_or_hypT
  obtain ⟨-, -, -, -, -, -, hθp⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
  have hOθ : CFSG.pCore 2 ↥L ≤ aschbacherSolvableCore 3 ↥L :=
    hθp 2 Nat.prime_two (by norm_num)
  obtain ⟨π, hπ⟩ : ∃ π : (↥L ⧸ CFSG.pCore 2 ↥L) →* (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      ∀ x : ↥L, π (x : ↥L ⧸ CFSG.pCore 2 ↥L) = (x : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    ⟨QuotientGroup.lift (CFSG.pCore 2 ↥L) (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
      (by rw [QuotientGroup.ker_mk']; exact hOθ), fun x => rfl⟩
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), hπ x⟩
  have hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.center_nativeJ2_eq_bot
      CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
  have hcθ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    have hmap := Subgroup.map_center_eq φ
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  have hZπ : ∀ z ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L), π z = 1 := by
    intro z hz
    have hmem : π z ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := hπsurj g
      simpa only [map_mul] using congrArg π (Subgroup.mem_center_iff.mp hz q)
    rw [hcθ, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) →*
        (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, ψ (QuotientGroup.mk q) = π q :=
    ⟨QuotientGroup.lift (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) π
      (fun z hz => MonoidHom.mem_ker.mpr (hZπ z hz)), fun q => rfl⟩
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨q, rfl⟩ := hπsurj y
    exact ⟨QuotientGroup.mk q, hψ q⟩
  haveI : Nontrivial CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2.toNontrivial
  haveI : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := φ.symm.injective.nontrivial
  have hsimple :
      IsSimpleGroup ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    hq.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥L ⧸ aschbacherSolvableCore 3 ↥L)
      obtain ⟨q, rfl⟩ := hψsurj y
      have hq1 : q ∈ ψ.ker := by
        rw [h1]
        exact Subgroup.mem_top q
      exact hy (MonoidHom.mem_ker.mp hq1)
  have hiso : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      CFSG.Blueprint.NativeSporadic.J2 :=
    (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans φ
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    intro h3
    obtain ⟨z, hz⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) 3 h3
    have hzQ : orderOf (z : ↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      rw [Subgroup.orderOf_coe, hz]
    obtain ⟨t, ht⟩ :=
      QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) (z : ↥L ⧸ CFSG.pCore 2 ↥L)
    have ht' : (t : ↥L ⧸ CFSG.pCore 2 ↥L) = (z : ↥L ⧸ CFSG.pCore 2 ↥L) := ht
    have htθ : t ∈ aschbacherSolvableCore 3 ↥L := by
      have h1 : π (t : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
        rw [ht']
        exact hZπ _ z.2
      rw [hπ t, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h3t : 3 ∣ orderOf t := by
      have hd : orderOf (t : ↥L ⧸ CFSG.pCore 2 ↥L) ∣ orderOf t :=
        orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) t
      rw [ht', hzQ] at hd
      exact hd
    have hθ3 : 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) := by
      have hd := orderOf_dvd_natCard (⟨t, htθ⟩ : aschbacherSolvableCore 3 ↥L)
      rw [Subgroup.orderOf_mk] at hd
      exact h3t.trans hd
    exact three_not_dvd_card_aschbacherSolvableCore (G := ↥L) hθ3
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    intro h2
    obtain ⟨z, hz⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) 2 h2
    have hzQ : orderOf (z : ↥L ⧸ CFSG.pCore 2 ↥L) = 2 := by
      rw [Subgroup.orderOf_coe, hz]
    have hzc : (z : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := z.2
    have hnorm : (Subgroup.zpowers (z : ↥L ⧸ CFSG.pCore 2 ↥L)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    have hp : IsPGroup 2 (Subgroup.zpowers (z : ↥L ⧸ CFSG.pCore 2 ↥L)) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, hzQ, pow_one]⟩
    have hle : Subgroup.zpowers (z : ↥L ⧸ CFSG.pCore 2 ↥L) ≤
        CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) :=
      le_sSup (s := {K : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) | K.Normal ∧ IsPGroup 2 K})
        ⟨hnorm, hp⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff,
      Subgroup.zpowers_eq_bot] at hle
    rw [hle, orderOf_one] at hzQ
    exact absurd hzQ (by norm_num)
  have hcop : Nat.Coprime 6 (Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) :=
    (Nat.Coprime.mul_right (Nat.prime_two.coprime_iff_not_dvd.mpr hZ2).symm
      (Nat.prime_three.coprime_iff_not_dvd.mpr hZ3).symm).symm
  have hZbot : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.ks18Mult_j2 (↥L ⧸ CFSG.pCore 2 ↥L)
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) hq.1 le_rfl hcop ⟨hiso⟩
  exact CFSG.RankThree.PartTwo.Sec14.aschbacherSolvableCore_eq_pCore_two hq hZbot

theorem C5_not_five_dvd_of_isPGroup_two {H : Type} [Group H] [Finite H] (hH : IsPGroup 2 H) :
    ¬ 5 ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hH
  rw [hn]
  intro h5
  have h2 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h5
  norm_num at h2

theorem C5_isPGroup_of_isElemAbelian {H : Type} [Group H] {p : ℕ} {S : Subgroup H}
    (hS : CFSG.Open.IsElemAbelian p S) : IsPGroup p S := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact hS.2 g.1 g.2

theorem C5_lift {C : Type} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    (N : Subgroup C) [N.Normal] (hN : ¬ p ∣ Nat.card N) (Abar : Subgroup (C ⧸ N))
    (hA : CFSG.Open.IsElemAbelian p Abar) :
    ∃ F : Subgroup C, CFSG.Open.IsElemAbelian p F ∧ F.map (QuotientGroup.mk' N) = Abar ∧
      F ⊓ N = ⊥ ∧ Nat.card F = Nat.card Abar := by
  obtain ⟨F, -, hFmap, hFinf⟩ := CFSG.GH74.GLS.Stage1.Thm6.exists_lift_pSubgroup N hN Abar
    (C5_isPGroup_of_isElemAbelian hA)
  have hmemAb : ∀ x ∈ F, QuotientGroup.mk' N x ∈ Abar := by
    intro x hx
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hx
    rwa [hFmap] at this
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    have hab : QuotientGroup.mk' N a * QuotientGroup.mk' N b
        = QuotientGroup.mk' N b * QuotientGroup.mk' N a :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hmemAb a ha⟩ ⟨_, hmemAb b hb⟩)
    have hc : a * b * a⁻¹ * b⁻¹ ∈ F ⊓ N := by
      refine ⟨F.mul_mem (F.mul_mem (F.mul_mem ha hb) (F.inv_mem ha)) (F.inv_mem hb), ?_⟩
      have h1 : QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hab]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    rw [hFinf, Subgroup.mem_bot] at hc
    have h2 : (a * b) * (b * a)⁻¹ = 1 := by
      rw [mul_inv_rev, ← mul_assoc]
      exact hc
    exact mul_inv_eq_one.mp h2
  have hexp : ∀ x ∈ F, x ^ p = 1 := by
    intro x hx
    have h1 : x ^ p ∈ F ⊓ N := by
      refine ⟨F.pow_mem hx p, ?_⟩
      have h2 : QuotientGroup.mk' N (x ^ p) = 1 := by
        rw [map_pow]
        exact hA.2 _ (hmemAb x hx)
      exact (QuotientGroup.eq_one_iff _).mp h2
    rw [hFinf, Subgroup.mem_bot] at h1
    exact h1
  refine ⟨F, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩, hFmap, hFinf, ?_⟩
  have := a1_card_map_eq (QuotientGroup.mk' N) F (by rw [QuotientGroup.ker_mk']; exact hFinf)
  rw [hFmap] at this
  exact this.symm

theorem C5_nonab_of_simple_card {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hcard : Nat.card X = 604800) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra hne
    exact hcon ⟨a, b, hne⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [hcard]; norm_num)
  have hnorm : (Subgroup.zpowers g).Normal :=
    ⟨fun n hn x => by
      have h1 : x * n * x⁻¹ = n := by rw [hcomm x n, mul_inv_cancel_right]
      rw [h1]
      exact hn⟩
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with hbot | htop
  · have hg1 : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
    rw [hbot, Subgroup.mem_bot] at hg1
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  · have h1 : Nat.card (Subgroup.zpowers g) = Nat.card X := by
      rw [htop, Subgroup.card_top]
    rw [Nat.card_zpowers, hg, hcard] at h1
    norm_num at h1

theorem C5_alt10_center {z : alternatingGroup (Fin 10)}
    (hz : ∀ w : alternatingGroup (Fin 10), w * z = z * w) : z = 1 := by
  have hc : Subgroup.center (alternatingGroup (Fin 10)) = ⊥ :=
    alternatingGroup.center_eq_bot (α := Fin 10) (by simp [Nat.card_eq_fintype_card])
  have hmem : z ∈ Subgroup.center (alternatingGroup (Fin 10)) := Subgroup.mem_center_iff.mpr hz
  rw [hc, Subgroup.mem_bot] at hmem
  exact hmem

theorem C5_mem_cQuot (Y₀ : Subgroup G) {x : G} :
    x ∈ cQuot Y₀ ↔ x ∈ Subgroup.normalizer (Y₀ : Set G) ∧
      ∀ y ∈ Y₀, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
  Set.ext_iff.mp (coe_cQuot Y₀) x

theorem C5_false_of_elemAbelian (h : Sec17Std G A c L Y₀) (h5 : 5 ∣ Nat.card (cQuot Y₀))
    {F : Subgroup G} (hFel : CFSG.Open.IsElemAbelian 5 F) (hFcard : Nat.card F = 5 ^ 2)
    (hFY : F ≤ Y₀) (hFC : F ⊓ cQuot Y₀ = ⊥) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cQuot Y₀)) 5 h5
  have he : (x : G) ∈ cQuot Y₀ := x.2
  have hoe : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe, hx]
  have hEC : Subgroup.zpowers (x : G) ≤ cQuot Y₀ := Subgroup.zpowers_le.mpr he
  have hEcard : Nat.card (Subgroup.zpowers (x : G)) = 5 := by rw [Nat.card_zpowers, hoe]
  have hEel : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers (x : G)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hm, ← hn]
      exact ((Commute.refl (x : G)).zpow_zpow m n).eq
    · intro y hy
      have hdvd : orderOf y ∣ 5 := by
        have := orderOf_dvd_of_mem_zpowers hy
        rwa [hoe] at this
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hY0N : Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer
  have hCN : cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) :=
    fun y hy => ((C5_mem_cQuot Y₀).mp hy).1
  have hQN : CFSG.Open.pCoreOf 2 Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (pCoreOf_le_cQuot Y₀).trans hCN
  have hQr : ¬ 5 ∣ Nat.card (CFSG.Open.pCoreOf 2 Y₀) :=
    C5_not_five_dvd_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀)
  have hQE : Subgroup.zpowers (x : G) ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    (hEC.trans hCN).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hQF : F ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    (hFY.trans hY0N).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hcomm : ∀ e ∈ Subgroup.zpowers (x : G), ∀ f ∈ F,
      e * f * e⁻¹ * f⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
    fun e he' f hf => ((C5_mem_cQuot Y₀).mp (hEC he')).2 f (hFY hf)
  obtain ⟨R, hRle, hRel, hRcard⟩ :=
    exists_isElemAbelian_card_le_of_commute_mod (r := 5) hQr (pCoreOf_le_cQuot Y₀) hEC hFC
      hEel hFel hQE hQF hcomm
  rw [hEcard, hFcard] at hRcard
  have hRN : R ≤ Subgroup.normalizer (Y₀ : Set G) :=
    hRle.trans (sup_le (sup_le (hEC.trans hCN) (hFY.trans hY0N)) hQN)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 5)).mp (C5_isPGroup_of_isElemAbelian hRel)
  have hkR : k ≤ CFSG.Open.pRank 5 (Subgroup.normalizer (Y₀ : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hRN hRel hk
  have hk2 : k ≤ 2 := hkR.trans (pRank_le_two h Nat.prime_five (by norm_num) le_rfl)
  have h1 : 5 ^ k ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
  rw [← hk] at h1
  norm_num at hRcard h1
  omega

theorem not_five_dvd_cQuot_of_a10 (h : Sec17Std G A c L Y₀)
    (hA : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10))) :
    ¬ 5 ∣ Nat.card (cQuot Y₀) := by
  intro h5
  obtain ⟨eA⟩ := hA
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hk : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 10))) := by
    have h10 := CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank.1 10 5
      (by norm_num) (by norm_num)
    omega
  obtain ⟨E, -, hEel, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hk
  have hEbar_el : CFSG.Open.IsElemAbelian 5 (E.map eA.symm.toMonoidHom) :=
    a1_isElemAbelian_map hEel eA.symm.toMonoidHom
  have hEbar_card : Nat.card (E.map eA.symm.toMonoidHom) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := eA.symm.toMonoidHom) eA.symm.injective, hEcard]
  have hN2 : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥Y₀) :=
    C5_not_five_dvd_of_isPGroup_two (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀))
  obtain ⟨F₁, hF₁el, -, hF₁inf, hF₁card⟩ :=
    C5_lift (CFSG.pCore 2 ↥Y₀) hN2 _ hEbar_el
  have hFel : CFSG.Open.IsElemAbelian 5 (F₁.map Y₀.subtype) :=
    a1_isElemAbelian_map hF₁el Y₀.subtype
  have hFcard : Nat.card (F₁.map Y₀.subtype) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := Y₀.subtype) Y₀.subtype_injective, hF₁card,
      hEbar_card]
  have hFY : F₁.map Y₀.subtype ≤ Y₀ := Subgroup.map_subtype_le F₁
  have hFC : F₁.map Y₀.subtype ⊓ cQuot Y₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxC⟩
    obtain ⟨a, haF, rfl⟩ := Subgroup.mem_map.mp hxF
    have hcentY : ∀ w : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀,
        w * QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a
          = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a * w := by
      intro w
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) w
      have hk' : a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥Y₀ := by
        refine (CFSG.mem_openPCoreOf_iff (p := 2) _).mp ?_
        have := ((C5_mem_cQuot Y₀).mp hxC).2 (b : G) b.2
        simpa using this
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) (a * b * a⁻¹ * b⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hk'
      simp only [map_mul, map_inv] at h1
      have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a * QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) b)
          * (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) b * QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a)⁻¹
          = 1 := by
        rw [mul_inv_rev, ← mul_assoc]
        exact h1
      exact (mul_inv_eq_one.mp h2).symm
    have hz : QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a = 1 := by
      have hcentA : ∀ u : alternatingGroup (Fin 10),
          u * eA (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a)
            = eA (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a) * u := by
        intro u
        obtain ⟨w, rfl⟩ := eA.surjective u
        rw [← map_mul, ← map_mul, hcentY w]
      exact eA.injective ((C5_alt10_center hcentA).trans (map_one eA).symm)
    have ha1 : a = 1 := by
      have hmem : a ∈ F₁ ⊓ CFSG.pCore 2 ↥Y₀ := ⟨haF, (QuotientGroup.eq_one_iff a).mp hz⟩
      rw [hF₁inf, Subgroup.mem_bot] at hmem
      exact hmem
    rw [Subgroup.mem_bot, ha1, map_one]
  exact C5_false_of_elemAbelian h h5 hFel hFcard hFY hFC

theorem C5_quot_case (h : Sec17Std G A c L Y₀)
    (hN : ¬ 5 ∣ Nat.card (aschbacherSolvableCore 3 ↥L))
    (hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hna : ∃ a b : ↥L ⧸ aschbacherSolvableCore 3 ↥L, a * b ≠ b * a)
    {Q : Type} [Group Q] (eQ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* Q)
    {E : Subgroup Q} (hEel : CFSG.Open.IsElemAbelian 5 E) (hEcard : Nat.card E = 5 ^ 2) :
    ¬ 5 ∣ Nat.card (cQuot Y₀) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hEbar_el : CFSG.Open.IsElemAbelian 5 (E.map eQ.symm.toMonoidHom) :=
    a1_isElemAbelian_map hEel eQ.symm.toMonoidHom
  have hEbar_card : Nat.card (E.map eQ.symm.toMonoidHom) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := eQ.symm.toMonoidHom) eQ.symm.injective, hEcard]
  obtain ⟨F₁, hF₁el, -, hF₁inf, hF₁card⟩ :=
    C5_lift (aschbacherSolvableCore 3 ↥L) hN _ hEbar_el
  have hFel : CFSG.Open.IsElemAbelian 5 (F₁.map L.subtype) :=
    a1_isElemAbelian_map hF₁el L.subtype
  have hFcard : Nat.card (F₁.map L.subtype) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective, hF₁card, hEbar_card]
  have hFY : F₁.map L.subtype ≤ Y₀ := (Subgroup.map_subtype_le F₁).trans h.le_y0
  have hFC : F₁.map L.subtype ⊓ cQuot Y₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxC⟩
    obtain ⟨a, haF, rfl⟩ := Subgroup.mem_map.mp hxF
    have hxL : L.subtype a ∈ L ⊓ cQuot Y₀ := ⟨a.2, hxC⟩
    obtain ⟨b, hbθ, hb⟩ := Subgroup.mem_map.mp (inf_cQuot_le_theta h hs hna hxL)
    have hab : a = b := Subtype.ext hb.symm
    have ha1 : a = 1 := by
      have hmem : a ∈ F₁ ⊓ aschbacherSolvableCore 3 ↥L := ⟨haF, by rw [hab]; exact hbθ⟩
      rw [hF₁inf, Subgroup.mem_bot] at hmem
      exact hmem
    rw [Subgroup.mem_bot, ha1, map_one]
  exact C5_false_of_elemAbelian h h5 hFel hFcard hFY hFC

set_option maxHeartbeats 1000000 in
theorem C5_quot_simple
    (eJ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :
    IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
  have hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  refine ⟨?_, ?_⟩
  · haveI := hJs
    exact eJ.isSimpleGroup
  · rw [Nat.card_congr eJ.toEquiv, CFSG.Sporadic.J2.card_J2]

set_option maxHeartbeats 1000000 in
theorem not_five_dvd_cQuot_of_j2
    (h135 : Item135) (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ 5 ∣ Nat.card (cQuot Y₀) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    theta_eq_pCore_two_of_j2 h135 h.toSec14Std hJ
  have hN : ¬ 5 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) := by
    rw [hθ]
    exact C5_not_five_dvd_of_isPGroup_two (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  obtain ⟨eJ⟩ := hJ
  obtain ⟨hs, hcard⟩ := C5_quot_simple eJ
  haveI := hs
  have hna : ∃ a b : ↥L ⧸ aschbacherSolvableCore 3 ↥L, a * b ≠ b * a :=
    C5_nonab_of_simple_card hcard
  have hk2 := CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_J2
  obtain ⟨E, -, hEel, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hk2
  exact C5_quot_case h hN hs hna eJ hEel hEcard

theorem five_dvd_card_cQuot_of_suzuki (h166 : Item166 A (lB A))
    (h : Sec17Std G A c L Y₀) {X : Subgroup G} (hX : X = delta A (lB A) X)
    (h3 : ¬ 3 ∣ Nat.card X) {K : Subgroup G} (hK : K ∈ thetaComponentsIn X)
    (hSz : ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) :
    5 ∣ Nat.card (cQuot Y₀) := by
  have hE27 : Nat.card A = 27 := h.toSec14Std.isE27.2
  have h3A : 3 ∣ Nat.card A := by rw [hE27]; norm_num
  have hXY : X ∈ CFSG.RankThree.PartTwo.Sec14.scriptY A := by
    show X ≠ ⊤ ∧ A ≤ Subgroup.normalizer (X : Set G)
    refine ⟨?_, ?_⟩
    · intro htop
      apply h3
      rw [htop, Subgroup.card_top]
      exact h3A.trans (Subgroup.card_subgroup_dvd_card A)
    · have hN := CFSG.RankThree.PartTwo.Sec14.le_normalizer_delta (A := A) (LB := lB A) X
      rw [← hX] at hN
      exact hN
  have hsub := ((h166 Y₀ h.mem_y0Star).1 X hXY hX K hK hSz).2
  have hsubC : (K : Set G) ⊆ (cQuot Y₀ : Set G) := by
    rw [coe_cQuot]
    exact hsub
  have hKC : K ≤ cQuot Y₀ := SetLike.coe_subset_coe.mp hsubC
  obtain ⟨n, hn⟩ := hSz
  have h5K : 5 ∣ Nat.card K :=
    (CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hn).trans
      (Subgroup.card_quotient_dvd_card _)
  exact h5K.trans (Subgroup.card_dvd_of_le hKC)

theorem c6_isElemAbelian_of_map {H K : Type*} [Group H] [Group K] {p : ℕ}
    {S : Subgroup H} (f : H →* K) (hS : S ⊓ f.ker = ⊥)
    (hT : CFSG.Open.IsElemAbelian p (S.map f)) : CFSG.Open.IsElemAbelian p S := by
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have hfab : f (a * b) = f (b * a) := by
      have hc := hT.1.is_comm.comm (⟨f a, Subgroup.mem_map_of_mem f ha⟩ : ↥(S.map f))
        ⟨f b, Subgroup.mem_map_of_mem f hb⟩
      have hc' := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at hc'
      rw [map_mul, map_mul]
      exact hc'
    have hmem : (a * b)⁻¹ * (b * a) ∈ S ⊓ f.ker := by
      refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem (S.mul_mem ha hb)) (S.mul_mem hb ha), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfab, inv_mul_cancel]
    rw [hS, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  have hfx : f x ^ p = 1 := hT.2 (f x) (Subgroup.mem_map_of_mem f hx)
  have hmem : x ^ p ∈ S ⊓ f.ker := by
    refine Subgroup.mem_inf.mpr ⟨S.pow_mem hx p, ?_⟩
    rw [MonoidHom.mem_ker, map_pow, hfx]
  rw [hS, Subgroup.mem_bot] at hmem
  exact hmem

theorem c6_mem_sup_decomp {G : Type*} [Group G] (C T : Subgroup G)
    (hnorm : ∀ t ∈ T, ∀ u ∈ C, t * u * t⁻¹ ∈ C) {y : G} (hy : y ∈ C ⊔ T) :
    ∃ v ∈ C, ∃ t ∈ T, y = v * t := by
  let K : Subgroup G :=
    { carrier := {z : G | ∃ v ∈ C, ∃ t ∈ T, z = v * t}
      mul_mem' := by
        rintro _ _ ⟨v₁, hv₁, t₁, ht₁, rfl⟩ ⟨v₂, hv₂, t₂, ht₂, rfl⟩
        exact ⟨v₁ * (t₁ * v₂ * t₁⁻¹), C.mul_mem hv₁ (hnorm t₁ ht₁ v₂ hv₂), t₁ * t₂,
          T.mul_mem ht₁ ht₂, by group⟩
      one_mem' := ⟨1, C.one_mem, 1, T.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨v, hv, t, ht, rfl⟩
        exact ⟨t⁻¹ * v⁻¹ * t⁻¹⁻¹, hnorm t⁻¹ (T.inv_mem ht) v⁻¹ (C.inv_mem hv), t⁻¹,
          T.inv_mem ht, by group⟩ }
  have hCK : C ≤ K := fun v hv => ⟨v, hv, 1, T.one_mem, by simp⟩
  have hTK : T ≤ K := fun t ht => ⟨1, C.one_mem, t, ht, by simp⟩
  have hK : C ⊔ T ≤ K := sup_le hCK hTK
  have hyK : y ∈ {z : G | ∃ v ∈ C, ∃ t ∈ T, z = v * t} := hK hy
  obtain ⟨v, hv, t, ht, hyt⟩ := hyK
  exact ⟨v, hv, t, ht, hyt⟩

theorem c6_pow_decomp {G : Type*} [Group G] (C T : Subgroup G)
    (hnorm : ∀ t ∈ T, ∀ u ∈ C, t * u * t⁻¹ ∈ C) {v : G} (hv : v ∈ C) {t : G} (ht : t ∈ T)
    (n : ℕ) : ∃ w ∈ C, (v * t) ^ n = w * t ^ n := by
  induction n with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hwe⟩ := ih
    refine ⟨w * (t ^ n * v * (t ^ n)⁻¹), C.mul_mem hw (hnorm _ (T.pow_mem ht n) v hv), ?_⟩
    rw [pow_succ (v * t) n, hwe, pow_succ t n]
    group

theorem c6_cQuot_le_normalizer (Y₀ : Subgroup G) :
    cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := by
  intro x hx
  have hce : x ∈ Subgroup.normalizer (Y₀ : Set G) ∧
      ∀ y ∈ Y₀, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
    (Set.ext_iff.mp (coe_cQuot Y₀) x).mp hx
  exact hce.1

theorem c6_mem_cQuot_of_pow_three (h : Sec17Std G A c L Y₀) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) {x : G} (hx : x ∈ cQuot Y₀ ⊔ T) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x ∈ cQuot Y₀ := by
  have hT' : Maximal (· ∈ scriptQPi A (lB A) ⊤ (piOf 2)) T := hT
  have hTπ : T ∈ collectionIn (scriptQ A (lB A)) ⊤ ∧ IsPiSubgroup (piOf 2) T := hT'.prop
  have hT2 : IsPGroup 2 ↥T := (isPiSubgroup_piOf_iff Nat.prime_two T).1 hTπ.2
  have hTM : T ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le T hT
  have hnorm : ∀ t ∈ T, ∀ u ∈ cQuot Y₀, t * u * t⁻¹ ∈ cQuot Y₀ := by
    intro t ht u hu
    exact (Subgroup.mem_set_normalizer_iff.mp
      (normalizer_le_normalizer_cQuot Y₀ (hTM ht)) u).mp hu
  obtain ⟨v, hv, t, ht, rfl⟩ := c6_mem_sup_decomp (cQuot Y₀) T hnorm hx
  obtain ⟨j, hj⟩ : ∃ j : ℕ, t ^ 2 ^ j = 1 := by
    obtain ⟨j, hj⟩ := hT2 ⟨t, ht⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  obtain ⟨w, hw, hwe⟩ := c6_pow_decomp (cQuot Y₀) T hnorm hv ht (2 ^ j)
  have hxm : (v * t) ^ 2 ^ j ∈ cQuot Y₀ := by
    rw [hwe, hj, mul_one]
    exact hw
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow j k (by norm_num : Nat.Coprime 2 3)
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, ((2 ^ j : ℕ) : ℤ) * a + ((3 ^ k : ℕ) : ℤ) * b = 1 := by
    refine ⟨Nat.gcdA (2 ^ j) (3 ^ k), Nat.gcdB (2 ^ j) (3 ^ k), ?_⟩
    have hg := Nat.gcd_eq_gcd_ab (2 ^ j) (3 ^ k)
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    exact_mod_cast hg.symm
  have hX : v * t = (v * t) ^ (((2 ^ j : ℕ) : ℤ) * a + ((3 ^ k : ℕ) : ℤ) * b) := by
    rw [hab, zpow_one]
  rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hk, one_zpow, mul_one] at hX
  rw [hX]
  exact (cQuot Y₀).zpow_mem hxm a

theorem pRank_three_cQuot_le_one
    (h : Sec17Std G A c L Y₀) : CFSG.Open.pRank 3 (cQuot Y₀) ≤ 1 := by
  have hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (lBar_simple_and_pRank h.toSec14Std).1
  have hna := lBar_nonabelian h.toSec14Std
  obtain ⟨Eb, -, hEb, hEbcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2)
      (lBar_simple_and_pRank h.toSec14Std).2
  have hEbP : IsPGroup 3 ↥Eb := (IsPGroup.iff_card (p := 3)).2 ⟨2, hEbcard⟩
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore
  obtain ⟨F₁, -, hF₁map, hF₁inf⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.exists_lift_pSubgroup (aschbacherSolvableCore 3 ↥L) hN3 Eb hEbP
  have hS1 : F₁ ⊓ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact hF₁inf
  have hF₁el : CFSG.Open.IsElemAbelian 3 F₁ :=
    c6_isElemAbelian_of_map _ hS1 (by rw [hF₁map]; exact hEb)
  have hF₁card : Nat.card F₁ = 3 ^ 2 := by
    rw [← a1_card_map_eq _ F₁ hS1, hF₁map, hEbcard]
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup G, F = F₁.map L.subtype := ⟨_, rfl⟩
  have hFL : F ≤ L := by
    rw [hFdef]
    exact Subgroup.map_subtype_le F₁
  have hFel : CFSG.Open.IsElemAbelian 3 F := by
    rw [hFdef]
    exact a1_isElemAbelian_map hF₁el L.subtype
  have hFcard : Nat.card F = 3 ^ 2 := by
    rw [hFdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective L), hF₁card]
  have hFC : F ⊓ cQuot Y₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [hFdef] at hxF
    obtain ⟨f, hfF₁, rfl⟩ := Subgroup.mem_map.mp hxF
    have hxθ := inf_cQuot_le_theta h hs hna (Subgroup.mem_inf.mpr ⟨f.2, hxC⟩)
    obtain ⟨z, hz, hzf⟩ := Subgroup.mem_map.mp hxθ
    have hzf' : z = f := Subgroup.subtype_injective L hzf
    rw [hzf'] at hz
    have hf1 : f ∈ F₁ ⊓ aschbacherSolvableCore 3 ↥L := Subgroup.mem_inf.mpr ⟨hfF₁, hz⟩
    rw [hF₁inf, Subgroup.mem_bot] at hf1
    rw [Subgroup.mem_bot, hf1, map_one]
  by_contra hlt
  have h2 : 2 ≤ CFSG.Open.pRank 3 (cQuot Y₀) := by omega
  obtain ⟨E, hEC, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) h2
  have hQ2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Y₀) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hQr : ¬ 3 ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 Y₀) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hQ2
    rw [hn]
    intro h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hQC : CFSG.Open.pCoreOf 2 Y₀ ≤ cQuot Y₀ := pCoreOf_le_cQuot Y₀
  have hEM : E ≤ Subgroup.normalizer (Y₀ : Set G) := hEC.trans (c6_cQuot_le_normalizer Y₀)
  have hFY : F ≤ Y₀ := hFL.trans h.le_y0
  have hFM : F ≤ Subgroup.normalizer (Y₀ : Set G) := hFY.trans Subgroup.le_normalizer
  have hQE : E ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hQF : F ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    hFM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ * f⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    intro e he f hf
    have hce : e ∈ Subgroup.normalizer (Y₀ : Set G) ∧
        ∀ y ∈ Y₀, e * y * e⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
      (Set.ext_iff.mp (coe_cQuot Y₀) e).mp (hEC he)
    exact hce.2 f (hFY hf)
  obtain ⟨R, hRle, hR, hRcard⟩ :=
    exists_isElemAbelian_card_le_of_commute_mod (r := 3) hQr hQC hEC hFC hE hFel hQE hQF hcomm
  have hRM : R ≤ Subgroup.normalizer (Y₀ : Set G) :=
    hRle.trans (sup_le (sup_le hEM hFM) (hQC.trans (c6_cQuot_le_normalizer Y₀)))
  have hR81 : 81 ≤ Nat.card R := by
    rw [hEcard, hFcard] at hRcard
    norm_num at hRcard
    omega
  have hRP : IsPGroup 3 ↥R := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using hR.2 x.1 x.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hRP
  have h4 : 4 ≤ n := by
    have h34 : 3 ^ 4 ≤ 3 ^ n := by
      rw [← hn]
      norm_num
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h34
  have hnle : n ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Y₀ : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hRM hR hn
  have h3M := pRank_three_le_three h (le_refl (Subgroup.normalizer (Y₀ : Set G)))
  omega

theorem pRank_three_cQuot_sup_le_one
    (h : Sec17Std G A c L Y₀) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) : CFSG.Open.pRank 3 (cQuot Y₀ ⊔ T) ≤ 1 := by
  obtain ⟨E, hEle, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (cQuot Y₀ ⊔ T)
  have hEC : E ≤ cQuot Y₀ := by
    intro x hx
    exact c6_mem_cQuot_of_pow_three h hT (hEle hx) (k := 1)
      (by rw [pow_one]; exact hE.2 x hx)
  have hle := CFSG.SectionRank.le_pRank (by norm_num) hEC hE hEcard
  exact hle.trans (pRank_three_cQuot_le_one h)

theorem not_three_dvd_inf_cQuot_sup (h : Sec17Std G A c L Y₀)
    (hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hna : ∃ a b : ↥L ⧸ aschbacherSolvableCore 3 ↥L, a * b ≠ b * a) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    ¬ 3 ∣ Nat.card ↥(L ⊓ (cQuot Y₀ ⊔ T)) := by
  intro h3
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hgg : g ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  have hg3 : (g : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hgg
    simpa using this
  obtain ⟨hgL, hgCT⟩ := Subgroup.mem_inf.mp g.2
  have hgC : (g : G) ∈ cQuot Y₀ :=
    c6_mem_cQuot_of_pow_three h hT hgCT (k := 1) (by rw [pow_one]; exact hg3)
  obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp
    (inf_cQuot_le_theta h hs hna (Subgroup.mem_inf.mpr ⟨hgL, hgC⟩))
  have hzord : orderOf (⟨z, hz⟩ : ↥(aschbacherSolvableCore 3 ↥L)) = 3 := by
    rw [Subgroup.orderOf_mk, ← orderOf_injective L.subtype (Subgroup.subtype_injective L) z,
      hzg, Subgroup.orderOf_coe, hg]
  have hdvd := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(aschbacherSolvableCore 3 ↥L))
  rw [hzord] at hdvd
  exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore hdvd

end CFSG.RankThree.PartTwo.Sec17.C174
