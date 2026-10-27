module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Defs
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Inv

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC (swapNeg swapNeg_mem_slPi swapNeg_conj_diagTau)
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_three {M : Type*} [Group M] {d : M} (hd3 : d ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers d) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show orderOf d ∣ 3 ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hd3)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

theorem exists_inv_of_bar {L : Subgroup G} {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (h : ∃ tb : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      tb * QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ * tb⁻¹ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩)⁻¹) :
    ∃ t ∈ L, ∀ x ∈ Subgroup.zpowers d, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨tb, htb⟩ := h
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set S := Subgroup.zpowers d' with hS
  have hS3 : IsPGroup 3 S := isPGroup_zpowers_three hd'3
  set mk := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hmk
  have hSmap : S.map mk = Subgroup.zpowers (mk d') := by rw [hS, MonoidHom.map_zpowers]
  have htbN : tb ∈ Subgroup.normalizer ((S.map mk : Subgroup _) : Set (↥L ⧸ _)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hSmap, MonoidHom.map_zpowers]
    change Subgroup.zpowers (tb * mk d' * tb⁻¹) = _
    rw [htb, Subgroup.zpowers_inv]
  obtain ⟨n, hnS, hnn⟩ := (Sec13.normalizer_map_mk_eq hS3).le htbN
  have hmem : n * d' * n⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hnS d').mp (Subgroup.mem_zpowers d')
  have heq : mk (n * d' * n⁻¹) = mk d'⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
    change mk n * mk d' * (mk n)⁻¹ = _
    rw [hnn, htb]
  have hnd : n * d' * n⁻¹ = d'⁻¹ :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hS3 hmem
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers d')) heq
  have hnd' : (n : G) * d * (n : G)⁻¹ = d⁻¹ := congrArg Subtype.val hnd
  refine ⟨(n : G), n.2, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hnd', inv_zpow]

end Lift

section TypeOne

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem exists_inv_of_type_one (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {s z g : GL (Fin 3) K} (hz : z ∈ zPi π 3 (p ^ f) K)
    (hg : g ∈ glPi π 3 (p ^ f) K) (hD : g⁻¹ * (s * z) * g = diagTau hτ) :
    ∃ t ∈ slPi π 3 (p ^ f) K, ProjGenLinGroup.mk t * ProjGenLinGroup.mk s *
      (ProjGenLinGroup.mk t)⁻¹ = (ProjGenLinGroup.mk s)⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  refine ⟨g * swapNeg * g⁻¹, conj_mem_slPi hπ hg (swapNeg_mem_slPi hπ), ?_⟩
  have hzs : ProjGenLinGroup.mk z = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hsz : s * z = g * diagTau hτ * g⁻¹ := by
    rw [← hD]
    group
  have hgl : g * swapNeg * g⁻¹ * (s * z) * (g * swapNeg * g⁻¹)⁻¹ = (s * z)⁻¹ := by
    rw [hsz]
    calc g * swapNeg * g⁻¹ * (g * diagTau hτ * g⁻¹) * (g * swapNeg * g⁻¹)⁻¹ =
        g * (swapNeg * diagTau hτ * swapNeg⁻¹) * g⁻¹ := by group
      _ = (g * diagTau hτ * g⁻¹)⁻¹ := by rw [swapNeg_conj_diagTau hτ]; group
  have h1 := congrArg ProjGenLinGroup.mk hgl
  simp only [map_mul, map_inv, hzs, mul_one] at h1
  exact h1

end TypeOne

section Bar

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_bar_of_not_modNine {L : Subgroup G} {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p n)
    (h9 : ¬ (p ^ n % 9 = 1 ∨ p ^ n % 9 = 8)) :
    ∃ tb : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      tb * QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ * tb⁻¹ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩)⁻¹ := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_projImage_model hn hiso
  have hπ : π = false → UnitaryFieldData p n K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ n) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _) (Subgroup.one_mem _)
      (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
  have hsH : s ∈ glPi π 3 (p ^ n) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hdb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hdb3,
      map_one, Subgroup.coe_one]
  have hsZ' : s ∉ zPi π 3 (p ^ n) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ n) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  rcases (rank3II_4_10_two hK hq hτ hτ1 hsH hsZ' hs3').mp ⟨s, hs, fun m _ => rfl⟩ with
      ⟨y, ⟨z, hz, rfl⟩, g, hg, hD⟩ | ⟨-, hmod⟩
  · obtain ⟨t, ht, htinv⟩ := exists_inv_of_type_one hK hq hτ hτ1 hz hg hD
    refine ⟨e.symm (projOf _ ⟨t, ht⟩), ?_⟩
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_projOf]
    rw [← hse]
    exact htinv
  · exfalso
    apply h9
    cases π
    · exact Or.inr hmod
    · exact Or.inl hmod

theorem exists_inv_bar_of_type3 {a : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 a)
    {d x : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hxd : x * d = d * x)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx : Sec4.InducesTypeOn L x 3) :
    ∃ tb : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      tb * QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ * tb⁻¹ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩)⁻¹ := by
  obtain ⟨-, Fb, -, -, hdFb, -, tb, -, htb, -, -⟩ :=
    Sec12.KS128NotHJTC.exists_heis_bar hL hdL hd3 hd1 hxd hxN hx
  exact ⟨tb, htb _ hdFb⟩

end Bar

end CFSG.RankThree.PartTwo.Sec16.Proof1613Inv

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.RankThree.PartTwo.Sec16.Proof1613Inv CFSG.GH74.GLS

theorem ks1613Inv_of
    (h131 : Item131) (h138 : Item138N) : KS1613Inv := by
  intro G _ _ A c L h h11 D hDAL hD3
  obtain ⟨d, hdD, hd1, rfl⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three hD3
  have hdA : d ∈ A := (hDAL hdD).1
  have hdL : d ∈ L := (hDAL hdD).2
  have hd3 : d ^ 3 = 1 := h.isElemAbelian.2 d hdA
  apply exists_inv_of_bar hdL hd3
  rcases h11 with hPGL | ⟨n, hn1, hiso, hprod⟩
  ·
    have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
    obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    obtain ⟨hL3, -, -⟩ := facts_of_isZ3PGLThreePi h.toSec13Data hPGL
    obtain ⟨p, e, hp, -, hisoL⟩ := hL3
    rcases cases131 h131 sporadicModels131 slTwoCenter h.toSec13Data with
        ⟨-, -, ⟨ψ⟩, -⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, -, -, x, hxA, hx⟩ | ⟨hcL', -⟩
    · exact (false_of_pgl_of_prod kSPGLProper h.toSec13Data hPGL ψ).elim
    · exfalso
      rcases hMJ with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
      · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hM12p hM12z χ
        exact KFacts.KS14.not_isoLThreePi_M12 p e (isoLThreePi_of_mulEquiv χ' hisoL)
      · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hJ2p hJ2z χ
        exact KFacts.KS14.ks17J2NotList.1 p e (isoLThreePi_of_mulEquiv χ' hisoL)
    · exact exists_inv_bar_of_type3 h.mem_thetaComponentsAt hdL hd3 hd1 (h.commute hxA hdA)
        (h.le_normalizer hxA) hx
    · exact (hcL hcL').elim
  ·
    have h9 := not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn1 hiso hprod
    exact exists_inv_bar_of_not_modNine hdL hd3 hd1 hn1 hiso h9

end CFSG.RankThree.PartTwo.Sec16
