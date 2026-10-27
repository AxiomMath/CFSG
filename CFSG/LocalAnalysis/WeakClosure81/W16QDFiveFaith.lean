module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDCfg
public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerCentralKernel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem w16q_odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) :=
  CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X

private theorem w16q_le_fusionOddCore {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ fusionOddCore X :=
  CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hN

private theorem w16q_le_normalizer_centralizer {K R : Subgroup G}
    (h : K ≤ normalizer (R : Set G)) :
    K ≤ normalizer (centralizer (R : Set G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro g hg c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro r hr
  have hr' : g⁻¹ * r * g ∈ R := by
    simpa using h g⁻¹ (K.inv_mem hg) r hr
  have hcr : (g⁻¹ * r * g) * c = c * (g⁻¹ * r * g) := hc _ hr'
  calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcr]
    _ = g * c * g⁻¹ * r := by group

private theorem w16q_le_normalizer_fusionOddCoreOf (L : Subgroup G) :
    L ≤ normalizer (fusionOddCoreOf L : Set G) := by
  have hnormal : ((fusionOddCoreOf L).subgroupOf L).Normal := by
    rw [fusionOddCoreOf, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)

private theorem w16q_le_fusionOddCoreOf {L N : Subgroup G} (hNL : N ≤ L)
    (hNnorm : L ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N ≤ fusionOddCoreOf L := by
  haveI : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hNnorm
  have hcard : Nat.card (N.subgroupOf L) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hle : N.subgroupOf L ≤ fusionOddCore ↥L := w16q_le_fusionOddCore (hcard ▸ hodd)
  calc N = (N.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hNL).symm
    _ ≤ (fusionOddCore ↥L).map L.subtype := Subgroup.map_mono hle
    _ = fusionOddCoreOf L := rfl

theorem Cfg1616.fusionOddCoreOf_eq_bot {M V₀ V U S H : Subgroup G} (c : Cfg1616 M V₀ V U S H) :
    fusionOddCoreOf H = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := c.cex.hyp.isPGroup.to_le c.cex.le
  have hN : CFSG.QuasithinUnique.CharTwo (normalizer (U : Set G)) :=
    c.std.charTwo _ ⟨U, c.cex.ne_bot, hU2, rfl⟩
  have hCh : CFSG.QuasithinUnique.CharTwo (centralizer (U : Set G)) := by
    have h1' := CFSG.QuasithinUnique.CharTwo.inf_centralizer hN
      (Subgroup.le_normalizer (H := U)) hU2
    rwa [inf_eq_right.2 (Subgroup.centralizer_le_normalizer (U : Set G))] at h1'
  have hF : Fam16 M U S (centralizer (U : Set G)) :=
    ⟨c.cex.S_le_centralizer, le_rfl, c.cex.not_le⟩
  have hOS : pCoreOf 2 (centralizer (U : Set G)) ≤ S := c.cex.pCoreOf_le_S c.one c.std hF
  have hR₀H : pCoreOf 2 (centralizer (U : Set G)) ≤ H := hOS.trans c.min.fam16.1
  have hNodd : Odd (Nat.card (fusionOddCoreOf H)) := by
    rw [fusionOddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
    exact w16q_odd_card_fusionOddCore ↥H
  have hHN : H ≤ normalizer (fusionOddCoreOf H : Set G) :=
    w16q_le_normalizer_fusionOddCoreOf H
  have hHR₀ : H ≤ normalizer (pCoreOf 2 (centralizer (U : Set G)) : Set G) :=
    c.min.fam16.2.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
      (centralizer (U : Set G)))
  have hbot : fusionOddCoreOf H ⊓ pCoreOf 2 (centralizer (U : Set G)) = ⊥ := by
    have hQp : IsPGroup 2 (pCoreOf 2 (centralizer (U : Set G))) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hQp.to_le
      (inf_le_right : _ ≤ pCoreOf 2 (centralizer (U : Set G))))
    have hdvd : Nat.card ↥(fusionOddCoreOf H ⊓ pCoreOf 2 (centralizer (U : Set G))) ∣
        Nat.card (fusionOddCoreOf H) := Subgroup.card_dvd_of_le inf_le_left
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ Nat.card (fusionOddCoreOf H) :=
        (dvd_pow_self 2 hk0).trans (hk ▸ hdvd)
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hNh : ∀ h ∈ H, ∀ k ∈ fusionOddCoreOf H, h * k * h⁻¹ ∈ fusionOddCoreOf H :=
    Subgroup.le_normalizer_iff.mp hHN
  have hR₀h : ∀ h ∈ H, ∀ k ∈ pCoreOf 2 (centralizer (U : Set G)),
      h * k * h⁻¹ ∈ pCoreOf 2 (centralizer (U : Set G)) :=
    Subgroup.le_normalizer_iff.mp hHR₀
  have hcomm : ∀ n ∈ fusionOddCoreOf H, ∀ q ∈ pCoreOf 2 (centralizer (U : Set G)),
      n * q = q * n := by
    intro n hn q hq
    have hmem : n * q * n⁻¹ * q⁻¹ ∈
        fusionOddCoreOf H ⊓ pCoreOf 2 (centralizer (U : Set G)) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : q * n⁻¹ * q⁻¹ ∈ fusionOddCoreOf H :=
          hNh q (hR₀H hq) n⁻¹ ((fusionOddCoreOf H).inv_mem hn)
        have h2 := (fusionOddCoreOf H).mul_mem hn h1
        simpa only [mul_assoc] using h2
      · have h1 : n * q * n⁻¹ ∈ pCoreOf 2 (centralizer (U : Set G)) :=
          hR₀h n (Subgroup.map_subtype_le (fusionOddCore H) hn) q hq
        have h2 := (pCoreOf 2 (centralizer (U : Set G))).mul_mem h1
          ((pCoreOf 2 (centralizer (U : Set G))).inv_mem hq)
        simpa only [mul_assoc] using h2
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : n * q * n⁻¹ = q := mul_inv_eq_one.mp hmem
    calc n * q = (n * q * n⁻¹) * n := by group
      _ = q * n := by rw [h1]
  have hle : fusionOddCoreOf H ≤ pCoreOf 2 (centralizer (U : Set G)) := fun n hn =>
    hCh (Subgroup.mem_inf.mpr
      ⟨c.min.fam16.2.1 (Subgroup.map_subtype_le (fusionOddCore H) hn),
        Subgroup.mem_centralizer_iff.mpr fun q hq => (hcomm n hn q hq).symm⟩)
  rw [← le_bot_iff, ← hbot]
  exact le_inf le_rfl hle

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

private theorem w16q_zpowers_eq_of_card_two {Z : Type} [Group Z] [Finite Z] {Y : Subgroup Z}
    (hY : Nat.card Y = 2) {y : Z} (hy : y ∈ Y) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = Y := by
  have hdvd : orderOf y ∣ 2 := by
    rw [← hY]
    exact Subgroup.orderOf_dvd_natCard Y hy
  have hle : orderOf y ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf y = 2 := by
    have := orderOf_pos y
    omega
  have hcard : Nat.card (Subgroup.zpowers y) = 2 := by rw [Nat.card_zpowers, hord]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) (by rw [hcard, hY])

theorem inf_centralizer_iSub16_le [Finite X] (d : DichCfg M V₀ V U S H φ) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p) :
    conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ iSub16 V H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup G := conjClosure V H ⊓ centralizer (iSub16 V H : Set G)
  let Y : Subgroup X := SevenK.barSub (conjClosure V H) φ V
  let C' : Subgroup X := (D.subgroupOf (conjClosure V H)).map φ
  have hIel : IsElemAbelian 2 (iSub16 V H) :=
    Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hIK : iSub16 V H ≤ conjClosure V H := d.cfg.iSub16_le_conjClosure
  have hKH : conjClosure V H ≤ H := d.cfg.conjClosure_le_H
  have hID : iSub16 V H ≤ D :=
    le_inf hIK (Subgroup.le_centralizer_iff_isMulCommutative.mpr hIel.1)
  have hHnormI : H ≤ normalizer (iSub16 V H : Set G) := by
    simpa only [iSub16] using le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hKnormI : conjClosure V H ≤ normalizer (iSub16 V H : Set G) := hKH.trans hHnormI
  have hKnormC : conjClosure V H ≤
      normalizer (centralizer (iSub16 V H : Set G) : Set G) :=
    w16q_le_normalizer_centralizer hKnormI
  have hKnormD : conjClosure V H ≤ normalizer (D : Set G) := by
    change conjClosure V H ≤
      normalizer (conjClosure V H ⊓ centralizer (iSub16 V H : Set G) : Set G)
    exact (le_inf (le_normalizer (H := conjClosure V H)) hKnormC).trans
      (inf_normalizer_le_normalizer_inf (H := conjClosure V H)
        (K := centralizer (iSub16 V H : Set G)))
  have hDKK : (D.subgroupOf (conjClosure V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_left : D ≤ conjClosure V H)).mpr hKnormD
  have hC'norm : C'.Normal := by
    change ((D.subgroupOf (conjClosure V H)).map φ).Normal
    exact hDKK.map φ d.bar.surjective
  have hmemC' : ∀ k : ↥(conjClosure V H), φ k ∈ C' ↔ (k : G) ∈ D := by
    intro k
    change φ k ∈ (D.subgroupOf (conjClosure V H)).map φ ↔ (k : G) ∈ D
    exact ⟨fun hk => d.mem_of_map_mem hID hk,
      fun hk => ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩⟩
  have hCY : C' ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    by_contra hy1
    have hYle : Y ≤ C' := by
      have hzy : Subgroup.zpowers y = Y :=
        w16q_zpowers_eq_of_card_two h.card_Y hy.2 hy1
      exact hzy.ge.trans (Subgroup.zpowers_le.mpr hy.1)
    have hnc : Subgroup.normalClosure (Y : Set X) ≤ C' :=
      Subgroup.normalClosure_le_normal hYle
    have htop : C' = ⊤ := le_antisymm le_top (h.gen ▸ hnc)
    have hKD : conjClosure V H ≤ D := by
      intro k hk
      have hkφ : φ ⟨k, hk⟩ ∈ C' := by rw [htop]; exact Subgroup.mem_top _
      exact (hmemC' ⟨k, hk⟩).mp hkφ
    have hKM : conjClosure V H ≤ M := by
      obtain ⟨⟨w, hwV₀⟩, hw1⟩ :=
        (Subgroup.ne_bot_iff_exists_ne_one).1 d.cfg.cex.hyp.ne_bot
      have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
      have hwI : w ∈ iSub16 V H := d.cfg.le_iSub16 (Subgroup.mem_sup_right hwV₀)
      refine ((hKD.trans (inf_le_right : D ≤ centralizer (iSub16 V H : Set G))).trans
        (Subgroup.centralizer_le (show ({w} : Set G) ⊆ (iSub16 V H : Set G) from ?_))).trans
        (d.cfg.cex.hyp.centralizer_le hwV₀ hw1')
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rwa [hx]
    exact d.cfg.not_conjClosure_le hKM
  have hp3odd : Odd (p ^ 3) := by
    rw [← h.card_O]
    exact w16q_odd_card_fusionOddCore X
  have hpodd : Odd p := (Nat.odd_pow_iff (by norm_num : 3 ≠ 0)).mp hp3odd
  have hYinfO : Y ⊓ fusionOddCore X = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [h.card_Y, h.card_O]
    exact Nat.coprime_two_left.mpr hpodd.pow
  have hcompl : Subgroup.IsComplement' Y (fusionOddCore X) :=
    isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hYinfO) (by
      rw [← Subgroup.mul_normal Y (fusionOddCore X), h.sup_eq, Subgroup.coe_top])
  have hXcard : Nat.card X = 2 * p ^ 3 := by
    have hc := hcompl.card_mul_card
    rw [h.card_Y, h.card_O] at hc
    exact hc.symm
  have hYindex : Y.index = p ^ 3 := by
    have hc := Subgroup.card_mul_index Y
    rw [h.card_Y, hXcard] at hc
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hc
  have hYp : IsPGroup 2 Y := IsPGroup.iff_card.mpr ⟨1, by rw [h.card_Y]; norm_num⟩
  have hC'odd : Odd (Nat.card C') := by
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    have hdvd : 2 ∣ Nat.card C' := even_iff_two_dvd.mp hnot
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 (G := ↥C') hdvd
    have hcX : (c : X) ∈ C' := c.2
    have hcord : orderOf (c : X) = 2 := (Subgroup.orderOf_coe c).trans hc
    let P : Subgroup X := Subgroup.zpowers (c : X)
    have hPcard : Nat.card P = 2 := by
      change Nat.card (Subgroup.zpowers (c : X)) = 2
      rw [Nat.card_zpowers, hcord]
    have hPindex : P.index = p ^ 3 := by
      have hc' := Subgroup.card_mul_index P
      rw [hPcard, hXcard] at hc'
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hc'
    have hPp : IsPGroup 2 P := IsPGroup.iff_card.mpr ⟨1, by rw [hPcard]; norm_num⟩
    have hYidx : ¬ 2 ∣ Y.index := by
      rw [hYindex]
      intro hd
      exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr hd)
    have hPidx : ¬ 2 ∣ P.index := by
      rw [hPindex]
      intro hd
      exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr hd)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X
      (hPp.toSylow hPidx) (hYp.toSylow hYidx)
    have hset : (MulAut.conj g : MulAut X) • (↑(hPp.toSylow hPidx) : Set X) =
        (↑(hYp.toSylow hYidx) : Set X) := by
      rw [← Sylow.coe_smul, hg]
    have hcP : (c : X) ∈ (↑(hPp.toSylow hPidx) : Set X) :=
      (IsPGroup.mem_toSylow hPp hPidx).mpr (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    have hgcYmem : (MulAut.conj g : MulAut X) (c : X) ∈
        (↑(hYp.toSylow hYidx) : Set X) := by
      rw [← hset]
      exact Set.mem_smul_set.mpr ⟨(c : X), hcP, rfl⟩
    have hgcY : g * (c : X) * g⁻¹ ∈ Y := by
      have h := (IsPGroup.mem_toSylow hYp hYidx).mp hgcYmem
      simpa [MulAut.conj_apply] using h
    have hgcC' : g * (c : X) * g⁻¹ ∈ C' := hC'norm.conj_mem (c : X) hcX g
    have hc1 : (c : X) ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hcord; norm_num at hcord
    have hne : g * (c : X) * g⁻¹ ≠ 1 := by
      intro h1
      apply hc1
      calc (c : X) = g⁻¹ * (g * (c : X) * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    have hmem : g * (c : X) * g⁻¹ ∈ C' ⊓ Y := Subgroup.mem_inf.mpr ⟨hgcC', hgcY⟩
    rw [hCY, Subgroup.mem_bot] at hmem
    exact hne hmem
  have hDK : D ≤ conjClosure V H := inf_le_left
  let ψ : ↥D →* X := φ.comp (Subgroup.inclusion hDK)
  have hψker : ψ.ker = (iSub16 V H).subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change φ (Subgroup.inclusion hDK x) = 1 ↔ (x : G) ∈ iSub16 V H
    rw [show (x : G) = ((Subgroup.inclusion hDK x : ↥(conjClosure V H)) : G) from rfl]
    exact d.bar.ker_iff (Subgroup.inclusion hDK x)
  have hψrange : ψ.range = C' := by
    change (φ.comp (Subgroup.inclusion hDK)).range =
      (D.subgroupOf (conjClosure V H)).map φ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hidx : ((iSub16 V H).subgroupOf D).index = Nat.card C' := by
    have h1 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
    rwa [hψker, hψrange] at h1
  have hidxodd : ¬ 2 ∣ ((iSub16 V H).subgroupOf D).index := by
    rw [hidx]
    exact fun hd => (Nat.not_even_iff_odd.mpr hC'odd) (even_iff_two_dvd.mpr hd)
  have hcenter : (iSub16 V H).subgroupOf D ≤ Subgroup.center ↥D := fun i hi =>
    Subgroup.mem_center_iff.mpr fun dd => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp dd.2).2 (i : G) hi).symm
  have hI2 : IsPGroup 2 ((iSub16 V H).subgroupOf D) := (hIel.subgroupOf D).isPGroup
  obtain ⟨R, hRnorm, hRodd, hRcomp, hRorder⟩ :=
    CFSG.ClassicalInvolution.Q3.exists_normal_complement_odd hcenter hI2 hidxodd
  have hDH : D ≤ H := hDK.trans hKH
  have hHnormD : H ≤ normalizer (D : Set G) := by
    change H ≤ normalizer (conjClosure V H ⊓ centralizer (iSub16 V H : Set G) : Set G)
    exact (le_inf (le_normalizer_conjClosure V H)
      (w16q_le_normalizer_centralizer hHnormI)).trans
      (inf_normalizer_le_normalizer_inf (H := conjClosure V H)
        (K := centralizer (iSub16 V H : Set G)))
  have hR'norm : H ≤ normalizer (R.map D.subtype : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun hh hhh x hx => ?_
    obtain ⟨dd, hdR, rfl⟩ := Subgroup.mem_map.mp hx
    have hdD : (dd : G) ∈ D := dd.2
    have hconjD : hh * (dd : G) * hh⁻¹ ∈ D :=
      Subgroup.le_normalizer_iff.mp hHnormD hh hhh (dd : G) hdD
    refine Subgroup.mem_map.mpr ⟨⟨hh * (dd : G) * hh⁻¹, hconjD⟩, ?_, rfl⟩
    rw [hRorder]
    have h1 : orderOf (⟨hh * (dd : G) * hh⁻¹, hconjD⟩ : ↥D) = orderOf dd := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe dd]
      exact orderOf_injective (MulAut.conj hh).toMonoidHom (MulAut.conj hh).injective (dd : G)
    rw [h1]
    exact (hRorder dd).mp hdR
  have hR'odd : Odd (Nat.card (R.map D.subtype)) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact Nat.not_even_iff_odd.mp fun hh => hRodd (even_iff_two_dvd.mp hh)
  have hR'H : R.map D.subtype ≤ H := (Subgroup.map_subtype_le R).trans hDH
  have hR'le : R.map D.subtype ≤ fusionOddCoreOf H :=
    w16q_le_fusionOddCoreOf hR'H hR'norm hR'odd
  have hRbot : R = ⊥ := by
    have h1 := hR'le
    rw [d.cfg.fusionOddCoreOf_eq_bot, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective R D.subtype_injective).mp h1
  have hIDtop : (iSub16 V H).subgroupOf D = ⊤ := by
    have h1 : Subgroup.IsComplement' (⊥ : Subgroup ↥D) ((iSub16 V H).subgroupOf D) :=
      hRbot ▸ hRcomp
    exact Subgroup.isComplement'_bot_left.mp h1
  intro x hx
  have h2 : (⟨x, hx⟩ : ↥D) ∈ (iSub16 V H).subgroupOf D := by
    rw [hIDtop]; exact Subgroup.mem_top _
  rwa [Subgroup.mem_subgroupOf] at h2

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
