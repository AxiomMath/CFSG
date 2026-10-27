module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Odd
import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl
public import CFSG.Holt.H78.Defs
import CFSG.Holt.H78.StabilizerCore
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial
public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

namespace EpsIn

variable {h : G}

theorem oddCore_le_normalizer_oOf (hE : EpsIn M V h) :
    inSubgroup (pPrimeCore 2) (yOf h) ≤ Subgroup.normalizer (oOf M h : Set G) :=
  calc inSubgroup (pPrimeCore 2) (yOf h) ≤ oOf M h := (hE.oddCore_yOf_le).1
    _ ≤ rOf M h := oOf_le_rOf
    _ ≤ Subgroup.normalizer (oOf M h : Set G) :=
        le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h))

theorem orderOf_mk_eq_two_of_mem_V (hE : EpsIn M V h) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    orderOf (QuotientGroup.mk (⟨z, hE.le_yOf hz⟩ : ↥(yOf h)) : YBar h) = 2 := by
  have hz2 : z ^ 2 = 1 := hE.root.elem.2 z hz
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hordY : orderOf (⟨z, hE.le_yOf hz⟩ : ↥(yOf h)) = 2 := by
    simpa [Subgroup.orderOf_coe] using hzord
  have hdvd : orderOf (QuotientGroup.mk (⟨z, hE.le_yOf hz⟩ : ↥(yOf h)) : YBar h) ∣ 2 := by
    simpa [hordY] using
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
        (⟨z, hE.le_yOf hz⟩ : ↥(yOf h))
  have hne : orderOf (QuotientGroup.mk (⟨z, hE.le_yOf hz⟩ : ↥(yOf h)) : YBar h) ≠ 1 := by
    intro h1
    have hmem : (⟨z, hE.le_yOf hz⟩ : ↥(yOf h)) ∈ pPrimeCore 2 ↥(yOf h) :=
      (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
    have hzOY : z ∈ inSubgroup (pPrimeCore 2) (yOf h) :=
      ⟨⟨z, hE.le_yOf hz⟩, hmem, rfl⟩
    have hdisj : Disjoint V (inSubgroup (pPrimeCore 2) (yOf h)) := by
      have h := hE.disjoint_conj_oddCore (y := 1) (Subgroup.one_mem (yOf h))
      simpa [conjSubgroup_one] using h
    have hbot : z ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdisj]
      exact Subgroup.mem_inf.mpr ⟨hz, hzOY⟩
    exact hz1 (Subgroup.mem_bot.mp hbot)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne
  · exact h

theorem mk_mem_barY_iff_of_oddCore_le (hE : EpsIn M V h) {K : Subgroup G}
    (hK : inSubgroup (pPrimeCore 2) (yOf h) ≤ K) {y : G} (hy : y ∈ yOf h) :
    (QuotientGroup.mk (⟨y, hy⟩ : ↥(yOf h)) : YBar h) ∈ barY h K ↔ y ∈ K := by
  rw [barY, Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, hq⟩
    have hnK : (n : G) ∈ K := Subgroup.mem_subgroupOf.mp hn
    have hdiv : (n : ↥(yOf h)) / ⟨y, hy⟩ ∈ pPrimeCore 2 ↥(yOf h) :=
      (QuotientGroup.eq_iff_div_mem).mp hq
    have hmem : (n : G) * y⁻¹ ∈ inSubgroup (pPrimeCore 2) (yOf h) := by
      refine ⟨(n : ↥(yOf h)) / ⟨y, hy⟩, hdiv, ?_⟩
      simp [Subgroup.coe_div, div_eq_mul_inv]
    have hKmem : (n : G) * y⁻¹ ∈ K := hK hmem
    rw [show y = ((n : G) * y⁻¹)⁻¹ * n by group]
    exact K.mul_mem (K.inv_mem hKmem) hnK
  · intro hyK
    exact ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr hyK, rfl⟩

theorem exists_central_involution (hE : EpsIn M V h) :
    ∃ (z : G) (S : Sylow 2 ↥(yOf h)) (Sbar : Sylow 2 (YBar h)),
      z ∈ V ∧ z ≠ 1 ∧
      (Sbar : Subgroup (YBar h)) = barY h ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ∧
      z ∈ (S : Subgroup ↥(yOf h)).map (yOf h).subtype ∧
      (S : Subgroup ↥(yOf h)).map (yOf h).subtype ≤ Subgroup.centralizer {z} := by
  obtain ⟨S, Sbar, hSR, hP0S, hZS, hSbar_eq, hZbar⟩ := hE.exists_sylow
  let Sfun : Subgroup G := (S : Subgroup ↥(yOf h)).map (yOf h).subtype
  have hS2 : IsPGroup 2 Sfun := (S.isPGroup').map (yOf h).subtype
  have hSne : Sfun ≠ ⊥ := by
    intro hbot
    exact hE.root.ne_bot (le_bot_iff.mp (hE.le_p0.trans (hP0S.trans_eq hbot)))
  haveI : Nontrivial ↥Sfun := (Subgroup.nontrivial_iff_ne_bot Sfun).mpr hSne
  haveI : Nontrivial ↥(Subgroup.center ↥Sfun) := hS2.center_nontrivial
  obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥Sfun)
  let z : G := (((w : Subgroup.center ↥Sfun) : ↥Sfun) : G)
  have hzSfun : z ∈ Sfun := ((w : Subgroup.center ↥Sfun) : ↥Sfun).2
  have hzCent : z ∈ Subgroup.centralizer (Sfun : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg (fun x : ↥Sfun => (x : G))
      (Subgroup.mem_center_iff.mp w.2 (⟨t, ht⟩ : ↥Sfun))
  have hzV : z ∈ V := hZS ⟨hzSfun, hzCent⟩
  have hz1 : z ≠ 1 := by
    intro hz
    exact hw1 (Subtype.ext (Subtype.ext hz))
  refine ⟨z, S, Sbar, hzV, hz1, hSbar_eq, hzSfun, ?_⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (Subgroup.mem_centralizer_iff.mp hzCent t ht).symm

private theorem exists_mem_center_of_even_normal {K : Subgroup (YBar h)}
    (hKnormal : K.Normal) (hKeven : 2 ∣ Nat.card K) (Sbar : Sylow 2 (YBar h)) :
    ∃ u : YBar h, u ∈ K ∧ u ∈ (Sbar : Subgroup (YBar h)) ∧
      u ∈ Subgroup.centralizer (G := YBar h)
        ((Sbar : Subgroup (YBar h)) : Set (YBar h)) ∧ u ≠ (1 : YBar h) := by
  haveI : K.Normal := hKnormal
  have hTne : K.subgroupOf (Sbar : Subgroup (YBar h)) ≠ ⊥ := by
    intro hbot
    have hdisj : Disjoint K (Sbar : Subgroup (YBar h)) :=
      Subgroup.subgroupOf_eq_bot.mp hbot
    exact CFSG.LocalAnalysis.RankThreeTheoremC.inf_normal_ne_bot_of_dvd_card
      Sbar hKeven (by
        rw [inf_comm]
        exact disjoint_iff.mp hdisj)
  haveI hTnormal : (K.subgroupOf (Sbar : Subgroup (YBar h))).Normal :=
    hKnormal.subgroupOf (Sbar : Subgroup (YBar h))
  have hinf := CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
    Sbar.isPGroup' (K.subgroupOf (Sbar : Subgroup (YBar h))) hTne
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  let uS : ↥(Sbar : Subgroup (YBar h)) := (u : ↥(Sbar : Subgroup (YBar h)))
  let ubar : YBar h := (uS : YBar h)
  have huK : ubar ∈ K := by
    have huT : uS ∈ K.subgroupOf (Sbar : Subgroup (YBar h)) :=
      (Subgroup.mem_inf.mp (show uS ∈ K.subgroupOf (Sbar : Subgroup (YBar h)) ⊓
        Subgroup.center ↥(Sbar : Subgroup (YBar h)) from u.2)).1
    exact Subgroup.mem_subgroupOf.mp huT
  have huSbar : ubar ∈ (Sbar : Subgroup (YBar h)) := uS.2
  have huCent : ubar ∈
      Subgroup.centralizer (G := YBar h) ((Sbar : Subgroup (YBar h)) : Set (YBar h)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg (fun z : ↥(Sbar : Subgroup (YBar h)) => (z : YBar h))
      (Subgroup.mem_center_iff.mp
        (Subgroup.mem_inf.mp (show uS ∈ K.subgroupOf
          (Sbar : Subgroup (YBar h)) ⊓ Subgroup.center ↥(Sbar : Subgroup (YBar h))
          from u.2)).2 ⟨s, hs⟩)
  refine ⟨ubar, huK, huSbar, huCent, ?_⟩
  intro h1
  apply hu1
  have hS : uS = 1 := Subtype.ext h1
  exact Subtype.ext hS

theorem exists_mem_barY_V_of_even_normal (hE : EpsIn M V h) {K : Subgroup (YBar h)}
    (hKnormal : K.Normal) (hKeven : 2 ∣ Nat.card K) :
    ∃ u : YBar h, u ∈ K ∧ u ∈ barY h V ∧ u ≠ 1 := by
  obtain ⟨S, Sbar, hSR, hP0S, hZS, hSbar_eq, hZbar⟩ := hE.exists_sylow
  obtain ⟨u, huK, huSbar, huCent, hu1⟩ :=
    exists_mem_center_of_even_normal hKnormal hKeven Sbar
  exact ⟨u, huK, hZbar (Subgroup.mem_inf.mpr ⟨huSbar, huCent⟩), hu1⟩

theorem odd_normalCore_barY_normalizer (hE : EpsIn M V h)
    (hlt : ¬ yOf h ≤ Subgroup.normalizer (oOf M h : Set G)) :
    Odd (Nat.card (barY h (Subgroup.normalizer (oOf M h : Set G))).normalCore) := by
  set N : Subgroup G := Subgroup.normalizer (oOf M h : Set G) with hN
  set NB : Subgroup (YBar h) := barY h N with hNB
  let q : ↥(yOf h) →* YBar h := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  have hOYleN : inSubgroup (pPrimeCore 2) (yOf h) ≤ N := hE.oddCore_le_normalizer_oOf
  by_contra hodd
  have h2dvd : 2 ∣ Nat.card NB.normalCore := by
    rw [Nat.Prime.dvd_iff_not_coprime Nat.prime_two]
    intro hcop
    exact hodd (Nat.coprime_two_left.mp hcop)
  obtain ⟨u, huK, huVbar, hu1⟩ :=
    hE.exists_mem_barY_V_of_even_normal (Subgroup.normalCore_normal NB) h2dvd
  obtain ⟨v, hvbar⟩ := (mem_barY_iff h hE.le_yOf).mp huVbar
  have hvne : (v : G) ≠ 1 := by
    intro h1
    apply hu1
    rw [← hvbar]
    have : v = 1 := Subtype.ext h1
    rw [this]
    rfl
  have hYN : yOf h ≤ N := by
    intro g hg
    let gY : ↥(yOf h) := ⟨g, hg⟩
    have hconj : (q gY)⁻¹ * u * (q gY) ∈ NB.normalCore := by
      simpa using (Subgroup.normalCore_normal NB).conj_mem _ huK (q gY)⁻¹
    have hNBmem : (q gY)⁻¹ * u * (q gY) ∈ NB :=
      Subgroup.normalCore_le NB hconj
    have heq : (q gY)⁻¹ * u * (q gY) =
        q (gY⁻¹ * ⟨(v : G), hE.le_yOf v.2⟩ * gY) := by
      rw [show u = q ⟨(v : G), hE.le_yOf v.2⟩ by
        rw [← hvbar]
        rfl]
      simp only [map_mul, map_inv]
    rw [heq] at hNBmem
    have hmemN : g⁻¹ * (v : G) * g ∈ N :=
      (hE.mk_mem_barY_iff_of_oddCore_le hOYleN
        (show g⁻¹ * (v : G) * g ∈ yOf h from (yOf h).mul_mem
          ((yOf h).mul_mem ((yOf h).inv_mem hg) (hE.le_yOf v.2)) hg)).mp hNBmem
    exact (hE.conj_mem_normalizer_oOf_iff v.2 hvne hg).mp hmemN
  exact hlt hYN

theorem normalCore_barY_normalizer_eq_bot (hE : EpsIn M V h)
    (hlt : ¬ yOf h ≤ Subgroup.normalizer (oOf M h : Set G)) :
    (barY h (Subgroup.normalizer (oOf M h : Set G))).normalCore = ⊥ := by
  set NB : Subgroup (YBar h) := barY h (Subgroup.normalizer (oOf M h : Set G)) with hNB
  have hKodd : Odd (Nat.card NB.normalCore) := hE.odd_normalCore_barY_normalizer hlt
  have hKleO : NB.normalCore ≤ pPrimeCore 2 (YBar h) :=
    le_pPrimeCore_of_normal_coprime (Subgroup.normalCore_normal NB) hKodd.coprime_two_left
  have hObar : pPrimeCore 2 (YBar h) = ⊥ := by
    simpa [YBar] using (pPrimeCore_quotient_eq_bot (G := ↥(yOf h)) (p := 2) Nat.prime_two)
  exact eq_bot_iff.mpr (hKleO.trans_eq hObar)

theorem faithfulSMul_barY_quotient (hE : EpsIn M V h)
    (hlt : ¬ yOf h ≤ Subgroup.normalizer (oOf M h : Set G)) :
    FaithfulSMul (YBar h)
      (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) := by
  rw [faithfulSMul_iff]
  intro g hg
  have hker : g ∈ (MulAction.toPermHom (YBar h)
      (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G)))).ker := by
    rw [MonoidHom.mem_ker]
    ext a
    exact hg a
  rw [← Subgroup.normalCore_eq_ker] at hker
  rw [hE.normalCore_barY_normalizer_eq_bot hlt] at hker
  exact Subgroup.mem_bot.mp hker

theorem smul_eq_iff_barY (hE : EpsIn M V h) {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1) :
    ∀ ω : YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G)),
      (QuotientGroup.mk (⟨z, hE.le_yOf hzV⟩ : ↥(yOf h)) : YBar h) • ω = ω ↔
        ω = QuotientGroup.mk (1 : YBar h) := by
  set N : Subgroup G := Subgroup.normalizer (oOf M h : Set G) with hN
  set NB : Subgroup (YBar h) := barY h N with hNB
  let q : ↥(yOf h) →* YBar h := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  let zY : ↥(yOf h) := ⟨z, hE.le_yOf hzV⟩
  let zbar : YBar h := QuotientGroup.mk zY
  have hzbar_eq : zbar = q zY := rfl
  intro ω
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h)) x
  have hzx : zbar * q g = q (zY * g) := by
    rw [hzbar_eq, map_mul]
  have hsmul : zbar • (QuotientGroup.mk (q g) : YBar h ⧸ NB) =
      QuotientGroup.mk (q (zY * g)) := by
    rw [MulAction.Quotient.smul_mk]
    simpa [smul_eq_mul] using congrArg (QuotientGroup.mk (s := NB)) hzx
  have hfirst : (QuotientGroup.mk (q (zY * g)) : YBar h ⧸ NB) =
      QuotientGroup.mk (q g) ↔ q (g⁻¹ * zY * g) ∈ NB := by
    rw [eq_comm, QuotientGroup.eq (s := NB)]
    have hid : (q g)⁻¹ * q (zY * g) = q (g⁻¹ * zY * g) := by
      rw [← map_inv, ← map_mul]
      congr 1
      group
    rw [hid]
  have hyY : (g : G)⁻¹ * z * (g : G) ∈ yOf h :=
    (yOf h).mul_mem ((yOf h).mul_mem ((yOf h).inv_mem g.2) (hE.le_yOf hzV)) g.2
  have hsecond : q (g⁻¹ * zY * g) ∈ NB ↔ (g : G)⁻¹ * z * (g : G) ∈ N := by
    have hgY : g⁻¹ * zY * g = (⟨(g : G)⁻¹ * z * (g : G), hyY⟩ : ↥(yOf h)) := by
      apply Subtype.ext
      rfl
    rw [hgY]
    exact hE.mk_mem_barY_iff_of_oddCore_le (K := N)
      hE.oddCore_le_normalizer_oOf (y := (g : G)⁻¹ * z * (g : G)) (hy := hyY)
  have hfourth : (g : G) ∈ N ↔ q g ∈ NB := by
    exact (hE.mk_mem_barY_iff_of_oddCore_le (K := N)
      hE.oddCore_le_normalizer_oOf (y := (g : G)) (hy := g.2)).symm
  have hbase : (QuotientGroup.mk (q g) : YBar h ⧸ NB) =
      QuotientGroup.mk (1 : YBar h) ↔ q g ∈ NB := by
    rw [QuotientGroup.eq (s := NB)]
    simp [Subgroup.inv_mem_iff]
  rw [hsmul]
  exact (hfirst.trans (hsecond.trans
    ((hE.conj_mem_normalizer_oOf_iff hzV hz1 g.2).trans (hfourth.trans hbase.symm))))

theorem exists_isHoltTriple (hE : EpsIn M V h) :
    ∃ z : YBar h, CFSG.Holt.General.IsHoltTriple (YBar h)
      (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) z (QuotientGroup.mk 1) := by
  set N : Subgroup G := Subgroup.normalizer (oOf M h : Set G) with hN
  set NB : Subgroup (YBar h) := barY h N with hNB
  let q : ↥(yOf h) →* YBar h := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  obtain ⟨z, S, Sbar, hzV, hz1, hSbar, hzSfun, hcent⟩ := hE.exists_central_involution
  let zY : ↥(yOf h) := ⟨z, hE.le_yOf hzV⟩
  let zbar : YBar h := QuotientGroup.mk zY
  have hzbar_eq : zbar = q zY := rfl
  have hzSbar : zbar ∈ (Sbar : Subgroup (YBar h)) := by
    rw [hSbar]
    refine Subgroup.mem_map.mpr ⟨zY, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hzSfun
  have hSbarCent : (Sbar : Subgroup (YBar h)) ≤ Subgroup.centralizer {zbar} := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hSbar] at hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    have htS : (t : G) ∈ (S : Subgroup ↥(yOf h)).map (yOf h).subtype :=
      Subgroup.mem_subgroupOf.mp ht
    have hcomm : z * (t : G) = (t : G) * z :=
      Subgroup.mem_centralizer_iff.mp (hcent htS) z (Set.mem_singleton z)
    have htz : zY * t = t * zY := Subtype.ext hcomm
    calc zbar * q t = q zY * q t := rfl
      _ = q (zY * t) := (map_mul q zY t).symm
      _ = q (t * zY) := by rw [htz]
      _ = q t * q zY := map_mul q t zY
      _ = q t * zbar := rfl
  have horder : orderOf zbar = 2 := hE.orderOf_mk_eq_two_of_mem_V hzV hz1
  have hfix : ∀ ω : YBar h ⧸ NB, zbar • ω = ω ↔ ω = QuotientGroup.mk (1 : YBar h) :=
    hE.smul_eq_iff_barY hzV hz1
  refine ⟨zbar, ?_⟩
  exact ⟨MulAction.isPretransitive_quotient (YBar h) NB, horder, hfix,
    ⟨Sbar, hzSbar, hSbarCent⟩⟩

theorem holtTriple (hE : EpsIn M V h)
    (hlt : ¬ yOf h ≤ Subgroup.normalizer (oOf M h : Set G)) :
    FaithfulSMul (YBar h) (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) ∧
      ∃ z : YBar h, CFSG.Holt.General.IsHoltTriple (YBar h)
        (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) z (QuotientGroup.mk 1) :=
  ⟨hE.faithfulSMul_barY_quotient hlt, hE.exists_isHoltTriple⟩

theorem pCore_barY_normalizer_eq_bot (hE : EpsIn M V h) :
    pCore 2 ↥(barY h (Subgroup.normalizer (oOf M h : Set G))) = ⊥ := by
  set N : Subgroup G := Subgroup.normalizer (oOf M h : Set G) with hN
  set NB : Subgroup (YBar h) := barY h N with hNB
  have hRleN : rOf M h ≤ N :=
    le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h))
  by_contra hne
  have hle : NB ≤ barY h (rOf M h) :=
    hE.le_of_pCore_ne_bot (barY_mono h hRleN) hne
  obtain ⟨c, hcY, hcVne, hcVM⟩ := hE.moved
  have hcVnebot : conjSubgroup c V ≠ ⊥ := by
    intro hbot
    apply hE.root.ne_bot
    have h := congrArg (conjSubgroup c⁻¹) hbot
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
    rwa [conjSubgroup, Subgroup.map_bot] at h
  have hne_inf : conjSubgroup c V ⊓ M ≠ ⊥ := by
    rw [inf_eq_left.mpr hcVM]
    exact hcVnebot
  have hcomm : ∀ a ∈ V, ∀ b ∈ conjSubgroup c V, a * b = b * a :=
    hE.root.commute_of_conj_inf_ne_bot hE.root.rootType hne_inf
  have hcbot : ⁅V, conjSubgroup c V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have hcN : c ∈ N :=
    conjSubgroup_eq_self_iff.mp (hE.conj_oOf_eq hcY hcbot)
  have hqNB : (QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h)) : YBar h) ∈ NB := by
    rw [hNB, barY, Subgroup.mem_map]
    exact ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr hcN, rfl⟩
  have hqR : (QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h)) : YBar h) ∈
      barY h (rOf M h) := hle hqNB
  have hcR : c ∈ rOf M h := hE.mem_rOf_of_bar_mem hcY hqR
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hcR).1
  exact hcVne (conjSubgroup_eq_self_iff.mpr (hE.root.le_normalizer hcM))

theorem le_oddCore_of_pPrimeCore_barY_eq_bot (hE : EpsIn M V h)
    (hbot : pPrimeCore 2 (barY h (Subgroup.normalizer (oOf M h : Set G))) = ⊥) :
    oOf M h ≤ inSubgroup (pPrimeCore 2) (yOf h) := by
  set N : Subgroup G := Subgroup.normalizer (oOf M h : Set G) with hN
  set NB : Subgroup (YBar h) := barY h N with hNB
  let q : ↥(yOf h) →* YBar h := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  let NY : Subgroup ↥(yOf h) := N.subgroupOf (yOf h)
  let OY : Subgroup ↥(yOf h) := (oOf M h).subgroupOf (yOf h)
  let O' : Subgroup ↥NY := OY.subgroupOf NY
  have hOleN : oOf M h ≤ N :=
    oOf_le_rOf.trans (le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h)))
  have hOYle : OY ≤ NY := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hOleN (Subgroup.mem_subgroupOf.mp hx))
  have hO'normal : O'.Normal := by
    refine ⟨fun x hx n => ?_⟩
    apply Subgroup.mem_subgroupOf.mpr
    apply Subgroup.mem_subgroupOf.mpr
    have hnN : ((n : ↥(yOf h)) : G) ∈ N := Subgroup.mem_subgroupOf.mp n.2
    have hxO : ((x : ↥(yOf h)) : G) ∈ oOf M h :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
    simpa using (Subgroup.mem_normalizer_iff.mp hnN ((x : ↥(yOf h)) : G)).1 hxO
  have hcardOY : Nat.card OY = Nat.card (oOf M h) :=
    natCard_subgroupOf_eq (oOf M h) (yOf h) (oOf_le_rOf.trans rOf_le_yOf)
  have hO'odd : Odd (Nat.card O') := by
    rw [natCard_subgroupOf_eq OY NY hOYle, hcardOY]
    exact hE.odd_oOf
  have hO'le : O' ≤ pPrimeCore 2 NY :=
    le_pPrimeCore_of_normal_coprime hO'normal hO'odd.coprime_two_left
  let f : ↥NY →* ↥NB := (q.comp NY.subtype).codRestrict NB (by
    intro x
    exact Subgroup.mem_map.mpr ⟨(x : ↥(yOf h)), x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hNB, barY, Subgroup.mem_map] at hy
    obtain ⟨n, hnN, hqn⟩ := hy
    refine ⟨⟨n, Subgroup.mem_subgroupOf.mpr hnN⟩, ?_⟩
    apply Subtype.ext
    exact hqn
  have hmap : (pPrimeCore 2 NY).map f ≤ pPrimeCore 2 NB := map_pPrimeCore_le f hf
  intro o ho
  let oY : ↥(yOf h) := ⟨o, (oOf_le_rOf.trans rOf_le_yOf) ho⟩
  have hoN : o ∈ N := hOleN ho
  let oNY : ↥NY := ⟨oY, Subgroup.mem_subgroupOf.mpr hoN⟩
  have hoO' : oNY ∈ O' :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ho)
  have hfmem : f oNY ∈ (pPrimeCore 2 NY).map f := Subgroup.mem_map_of_mem f (hO'le hoO')
  have hbotmap : (pPrimeCore 2 NY).map f = ⊥ := le_bot_iff.mp (hmap.trans_eq hbot)
  have h1 : f oNY = 1 := by
    rw [hbotmap] at hfmem
    exact Subgroup.mem_bot.mp hfmem
  have hq1 : (QuotientGroup.mk oY : YBar h) = 1 := by
    simpa [f, q, oNY] using congrArg Subtype.val h1
  exact ⟨oY, (QuotientGroup.eq_one_iff _).mp hq1, rfl⟩

theorem oddCore_yOf_eq (hHolt : CFSG.Holt.H78.HoltTheorem1) (hE : EpsIn M V h) :
    inSubgroup (pPrimeCore 2) (yOf h) = oOf M h := by
  by_cases hlt : yOf h ≤ Subgroup.normalizer (oOf M h : Set G)
  · have hO_normal : ((oOf M h).subgroupOf (yOf h)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (oOf_le_rOf.trans rOf_le_yOf)).mpr hlt
    haveI : ((oOf M h).subgroupOf (yOf h)).Normal := hO_normal
    have hOleOY : oOf M h ≤ inSubgroup (pPrimeCore 2) (yOf h) :=
      subgroupOf_le_pPrimeCore_map (p := 2) (oOf_le_rOf.trans rOf_le_yOf)
        hE.odd_oOf.coprime_two_left
    exact le_antisymm (hE.oddCore_yOf_le).1 hOleOY
  · obtain ⟨hfaith, z, hT⟩ := hE.holtTriple hlt
    haveI : FaithfulSMul (YBar h)
        (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) := hfaith
    have h3 : 3 ≤ Nat.card
        (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) :=
      CFSG.Holt.H78.IsHoltTriple.three_le_card hT
    have hstar : CFSG.Holt.H78.IsStarGroup (YBar h)
        (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) :=
      CFSG.Holt.H78.IsHoltTriple.isStarGroup hT h3
    obtain ⟨D⟩ := hHolt (YBar h)
      (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) hstar
    have hO : CFSG.Holt.H78.jOddCore (YBar h)
        (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G))) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc CFSG.Holt.H78.jOddCore (YBar h)
            (YBar h ⧸ barY h (Subgroup.normalizer (oOf M h : Set G)))
          ≤ pPrimeCore 2 (YBar h) := CFSG.Holt.H78.jOddCore_le_pPrimeCore
        _ = ⊥ := by
            simpa [YBar] using (pPrimeCore_quotient_eq_bot (G := ↥(yOf h)) (p := 2)
              Nat.prime_two)
    have hHG := CFSG.Holt.H78.HoltData.pPrimeCore_stabilizer_eq_bot_or_pCore_ne_bot
      D hO (QuotientGroup.mk (1 : YBar h))
    rw [MulAction.stabilizer_quotient] at hHG
    rcases hHG with hA | hB
    · exact le_antisymm (hE.oddCore_yOf_le).1 (hE.le_oddCore_of_pPrimeCore_barY_eq_bot hA)
    · exact absurd hE.pCore_barY_normalizer_eq_bot hB

end EpsIn

variable {n f : ℕ}

theorem Sec7Hyp.oddCore_yOf (hS : Sec7Hyp M V n f)
    (hHolt : CFSG.Holt.H78.HoltTheorem1) (h72 : Sec7.Stmt72 M V n f)
    (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (h73d : Sec7.Stmt73delta M V) {A B : Subgroup G} {h : G} (hX : L2Datum M V A B h) :
    inSubgroup (pPrimeCore 2) (yOf h) = oOf M h ∧
      ∀ y ∈ yOf h, inSubgroup (pPrimeCore 2) (yOf h) ≤ cenOf (conjSubgroup y V) := by
  have h72' := h72 A B h hX
  have h73a' := h73a A B h hX
  have hO_le : V ≤ p0Of M V (A ⊔ B) := by
    calc V = ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ := h72'.2.2.1.symm
      _ ≤ p0Of M V (A ⊔ B) := Subgroup.commutator_le_self _
  let hE : EpsIn M V h :=
    { root := hS.sec5.toRootHyp
      le_p0 := h72'.1 ▸ hO_le
      cen := h72'.1 ▸ h73a'.2.2.2.1
      maxEA := (h73g A B h hX).2
      moved := by
        obtain ⟨H₀, hH₀Y, hP0H, hHnotM, hO2, c, hcH, hcVne, hcVM⟩ := h73d A B h hX
        exact ⟨c, hH₀Y hcH, hcVne, hcVM.trans inf_le_left⟩ }
  exact ⟨hE.oddCore_yOf_eq hHolt, (hE.oddCore_yOf_le).2⟩

end CFSG.RankThree.GF2n.Tim81
