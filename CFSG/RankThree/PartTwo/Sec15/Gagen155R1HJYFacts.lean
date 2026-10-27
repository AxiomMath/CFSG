module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJDefs
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PermutableOrderThree
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree.PartTwo.Sec15

open scoped Pointwise

noncomputable def sylowMap {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (U : Sylow 2 Y) : Sylow 2 Y' :=
  U.comapOfInjective (ϕ := e.symm.toMonoidHom) (by simpa using e.symm.injective)
    (by
      have hrange : (e.symm.toMonoidHom).range = ⊤ := MulEquiv.range_eq_top e.symm
      rw [hrange]
      exact le_top)

theorem coe_sylowMap {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (U : Sylow 2 Y) :
    (sylowMap e U : Subgroup Y') = (U : Subgroup Y).map e.toMonoidHom := by
  rw [sylowMap, Sylow.coe_comapOfInjective]
  exact (Subgroup.map_equiv_eq_comap_symm' e (U : Subgroup Y)).symm

theorem sylow_inf_eq_bot_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∀ U V : Sylow 2 Y', U ≠ V → (U : Subgroup Y') ⊓ V = ⊥) :
    ∀ U V : Sylow 2 Y, U ≠ V → (U : Subgroup Y) ⊓ V = ⊥ := by
  intro U V hUV
  let U' : Sylow 2 Y' := sylowMap e U
  let V' : Sylow 2 Y' := sylowMap e V
  have hU' : (U' : Subgroup Y') = (U : Subgroup Y).map e.toMonoidHom := coe_sylowMap e U
  have hV' : (V' : Subgroup Y') = (V : Subgroup Y).map e.toMonoidHom := coe_sylowMap e V
  have hUV' : U' ≠ V' := by
    intro hEq
    apply hUV
    have hcoe : (U : Subgroup Y).map e.toMonoidHom = (V : Subgroup Y).map e.toMonoidHom := by
      have h := congrArg (fun P : Sylow 2 Y' => (P : Subgroup Y')) hEq
      rwa [hU', hV'] at h
    exact Sylow.ext (Subgroup.map_injective (f := e.toMonoidHom) e.injective hcoe)
  have hTI' := h U' V' hUV'
  have hmap : ((U : Subgroup Y) ⊓ (V : Subgroup Y)).map e.toMonoidHom = ⊥ := by
    rw [Subgroup.map_inf _ _ _ e.injective, ← hU', ← hV']
    exact hTI'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_bot] using hmap

theorem mem_sup_zpowers_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∀ U : Sylow 2 Y', ∀ y z : Y',
      y ∈ Subgroup.normalizer ((U : Subgroup Y') : Set Y') →
      z ∈ Subgroup.normalizer ((U : Subgroup Y') : Set Y') →
      orderOf y = 3 → orderOf z = 3 →
      z ∈ (U : Subgroup Y') ⊔ Subgroup.zpowers y) :
    ∀ U : Sylow 2 Y, ∀ y z : Y,
      y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
      z ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
      orderOf y = 3 → orderOf z = 3 →
      z ∈ (U : Subgroup Y) ⊔ Subgroup.zpowers y := by
  intro U y z hy hz hy3 hz3
  let U' : Sylow 2 Y' := sylowMap e U
  have hU' : (U' : Subgroup Y') = (U : Subgroup Y).map e.toMonoidHom := coe_sylowMap e U
  have hnorm : (Subgroup.normalizer ((U : Subgroup Y) : Set Y)).map e.toMonoidHom =
      Subgroup.normalizer ((U' : Subgroup Y') : Set Y') := by
    rw [hU', Subgroup.map_equiv_normalizer_eq]
  have hy' : e y ∈ Subgroup.normalizer ((U' : Subgroup Y') : Set Y') := by
    have hmem : e y ∈ (Subgroup.normalizer ((U : Subgroup Y) : Set Y)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hy
    rwa [hnorm] at hmem
  have hz' : e z ∈ Subgroup.normalizer ((U' : Subgroup Y') : Set Y') := by
    have hmem : e z ∈ (Subgroup.normalizer ((U : Subgroup Y) : Set Y)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hz
    rwa [hnorm] at hmem
  have hmem := h U' (e y) (e z) hy' hz'
    (by rw [MulEquiv.orderOf_eq]; exact hy3)
    (by rw [MulEquiv.orderOf_eq]; exact hz3)
  have hmap : ((U : Subgroup Y) ⊔ Subgroup.zpowers y).map e.toMonoidHom =
      (U' : Subgroup Y') ⊔ Subgroup.zpowers (e y) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hU']
    rfl
  rw [← hmap] at hmem
  exact by simpa using (Subgroup.mem_map_equiv).mp hmem

theorem exists_commute_orderOf_five_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y']
    (e : Y ≃* Y')
    (h : ∀ U : Sylow 2 Y', ∀ y : Y',
      y ∈ Subgroup.normalizer ((U : Subgroup Y') : Set Y') →
      orderOf y = 3 →
      ∃ t ∈ Subgroup.normalizer ((U : Subgroup Y') : Set Y'), orderOf t = 5 ∧ Commute t y) :
    ∀ U : Sylow 2 Y, ∀ y : Y,
      y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
      orderOf y = 3 →
      ∃ t ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y), orderOf t = 5 ∧ Commute t y := by
  intro U y hy hy3
  let U' : Sylow 2 Y' := sylowMap e U
  have hU' : (U' : Subgroup Y') = (U : Subgroup Y).map e.toMonoidHom := coe_sylowMap e U
  have hnorm : (Subgroup.normalizer ((U : Subgroup Y) : Set Y)).map e.toMonoidHom =
      Subgroup.normalizer ((U' : Subgroup Y') : Set Y') := by
    rw [hU', Subgroup.map_equiv_normalizer_eq]
  have hy' : e y ∈ Subgroup.normalizer ((U' : Subgroup Y') : Set Y') := by
    have hmem : e y ∈ (Subgroup.normalizer ((U : Subgroup Y) : Set Y)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hy
    rwa [hnorm] at hmem
  obtain ⟨t', ht'norm, ht'5, ht'comm⟩ := h U' (e y) hy'
    (by rw [MulEquiv.orderOf_eq]; exact hy3)
  refine ⟨e.symm t', ?_, ?_, ?_⟩
  · have ht'map : t' ∈ (Subgroup.normalizer ((U : Subgroup Y) : Set Y)).map e.toMonoidHom := by
      rw [hnorm]
      exact ht'norm
    exact (Subgroup.mem_map_equiv).mp ht'map
  · rw [MulEquiv.orderOf_eq]
    exact ht'5
  · exact Commute.of_map (f := e) e.injective (by simpa using ht'comm)

theorem Res1HJYFacts.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : Res1HJYFacts Y') : Res1HJYFacts Y := by
  exact ⟨sylow_inf_eq_bot_of_mulEquiv e h.1, mem_sup_zpowers_of_mulEquiv e h.2.1,
    exists_commute_orderOf_five_of_mulEquiv e h.2.2⟩

private theorem pow_three_eq_one_of_component {Y : Type} [Group Y]
    {U D : Subgroup Y} (hbot : U ⊓ D = ⊥)
    (hsup : U ⊔ D = Subgroup.normalizer (U : Set Y))
    {y u d : Y} (hu : u ∈ U) (hd : d ∈ D) (hy : y = d * u) (hy3 : orderOf y = 3) :
    d ^ 3 = 1 := by
  have hd3D : d ^ 3 ∈ D := Subgroup.pow_mem D hd 3
  have hd3U : d ^ 3 ∈ U := by
    let H : Subgroup Y := U ⊔ D
    let NQ : Subgroup H := U.subgroupOf H
    haveI hNQ : NQ.Normal := by
      apply Subgroup.normal_subgroupOf_of_le_normalizer
      show U ⊔ D ≤ Subgroup.normalizer (U : Set Y)
      rw [hsup]
    have huH : u ∈ H := Subgroup.mem_sup_left hu
    have hdH : d ∈ H := Subgroup.mem_sup_right hd
    have hyH : y ∈ H := by
      rw [hy]
      simpa [H, sup_comm] using Subgroup.mul_mem_sup (S := D) (T := U) hd hu
    let uH : H := ⟨u, huH⟩
    let dH : H := ⟨d, hdH⟩
    let yH : H := ⟨y, hyH⟩
    have hπu : QuotientGroup.mk' NQ uH = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hu
    have hy_eq : yH = dH * uH := Subtype.ext hy
    have hπy : QuotientGroup.mk' NQ yH = QuotientGroup.mk' NQ dH := by
      calc
        QuotientGroup.mk' NQ yH = QuotientGroup.mk' NQ (dH * uH) := by rw [hy_eq]
        _ = QuotientGroup.mk' NQ dH * QuotientGroup.mk' NQ uH := map_mul _ dH uH
        _ = QuotientGroup.mk' NQ dH := by rw [hπu, mul_one]
    have hyH3 : yH ^ 3 = 1 := by
      apply Subtype.ext
      show y ^ 3 = 1
      rw [← hy3]
      exact pow_orderOf_eq_one y
    have hπd3 : QuotientGroup.mk' NQ dH ^ 3 = 1 := by
      rw [← hπy, ← map_pow, hyH3, map_one]
    have hd3N : dH ^ 3 ∈ NQ := by
      apply (QuotientGroup.eq_one_iff (dH ^ 3)).mp
      simpa [QuotientGroup.mk'_apply, map_pow] using hπd3
    exact Subgroup.mem_subgroupOf.mp (by simpa using hd3N)
  have hmem : d ^ 3 ∈ U ⊓ D := Subgroup.mem_inf.mpr ⟨hd3U, hd3D⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem orderOf_component_of_orderOf_eq_three {Y : Type} [Group Y]
    {U D : Subgroup Y} (hU : IsPGroup 2 U) (hbot : U ⊓ D = ⊥)
    (hsup : U ⊔ D = Subgroup.normalizer (U : Set Y))
    {y u d : Y} (hu : u ∈ U) (hd : d ∈ D) (hy : y = d * u) (hy3 : orderOf y = 3) :
    orderOf d = 3 := by
  have hyU : y ∉ U := by
    intro hyU
    have h2 : 2 ∣ orderOf (⟨y, hyU⟩ : ↥U) :=
      hU.dvd_orderOf (by
        intro h1
        have hy1 : y = 1 := congrArg Subtype.val h1
        rw [hy1] at hy3
        simp at hy3)
    rw [← Subgroup.orderOf_coe, hy3] at h2
    norm_num at h2
  have hd1 : d ≠ 1 := by
    intro hd1
    apply hyU
    rw [hy, hd1, one_mul]
    exact hu
  exact orderOf_eq_prime (pow_three_eq_one_of_component hbot hsup hu hd hy hy3) hd1

private theorem exists_component_of_mem_normalizer {Y : Type} [Group Y]
    {U D : Subgroup Y} (hU : IsPGroup 2 U) (hbot : U ⊓ D = ⊥)
    (hsup : U ⊔ D = Subgroup.normalizer (U : Set Y))
    {y : Y} (hy : y ∈ Subgroup.normalizer (U : Set Y)) (hy3 : orderOf y = 3) :
    ∃ d ∈ D, ∃ u ∈ U, y = d * u ∧ orderOf d = 3 := by
  have hDU : D ≤ Subgroup.normalizer (U : Set Y) := by
    rw [← hsup]
    exact le_sup_right
  have hyD : y ∈ (D : Set Y) * (U : Set Y) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D U hDU]
    have hyH : y ∈ U ⊔ D := by rw [hsup]; exact hy
    simpa [sup_comm] using hyH
  obtain ⟨d, hdD, u, huU, hdecomp⟩ := Set.mem_mul.mp hyD
  exact ⟨d, hdD, u, huU, hdecomp.symm,
    orderOf_component_of_orderOf_eq_three hU hbot hsup huU hdD hdecomp.symm hy3⟩

theorem card_sup_zpowers_eq_three_mul {Y : Type} [Group Y] [Finite Y]
    {U : Subgroup Y} (hU : IsPGroup 2 U) {y : Y}
    (hy : y ∈ Subgroup.normalizer (U : Set Y)) (hy3 : orderOf y = 3) :
    U ⊓ Subgroup.zpowers y = ⊥ ∧
      Nat.card ↥(U ⊔ Subgroup.zpowers y) = Nat.card U * 3 := by
  have hcard : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
  have hinf : U ⊓ Subgroup.zpowers y = ⊥ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.inf_eq_bot_of_isPGroup_two_of_card_three hU hcard
  refine ⟨hinf, ?_⟩
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U (Subgroup.zpowers y)
    (Subgroup.zpowers_le.mpr hy) (disjoint_iff.mpr hinf), hcard]

theorem exists_conj_eq_of_order_three_mem_sup_zpowers {Y : Type} [Group Y] [Finite Y]
    {U : Subgroup Y} (hU : IsPGroup 2 U) {y : Y}
    (hy : y ∈ Subgroup.normalizer (U : Set Y)) (hy3 : orderOf y = 3)
    {d : Y} (hdH0 : d ∈ U ⊔ Subgroup.zpowers y) (hd3 : orderOf d = 3) :
    ∃ g ∈ U ⊔ Subgroup.zpowers y, ∃ d' ∈ U ⊔ Subgroup.zpowers y,
      d' ∈ Subgroup.zpowers d ∧ y = g * d' * g⁻¹ := by
  let H0 : Subgroup Y := U ⊔ Subgroup.zpowers y
  have hPd : Subgroup.zpowers d ≤ H0 := Subgroup.zpowers_le.mpr hdH0
  have hPy : Subgroup.zpowers y ≤ H0 := le_sup_right
  have hPd_card : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd3]
  have hPy_card : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
  have hH0_card : Nat.card H0 = 3 * Nat.card U := by
    rw [(card_sup_zpowers_eq_three_mul hU hy hy3).2, mul_comm]
  have hUnot : ¬ 3 ∣ Nat.card U :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hU Nat.prime_three (by norm_num)
  obtain ⟨g, hgH0, hgP⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_conj_map_eq_of_card_three
      hPd hPy hPd_card hPy_card hH0_card hUnot
  have hy_mem : y ∈ (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom := by
    rw [hgP]
    exact Subgroup.mem_zpowers y
  obtain ⟨d', hd'P, hd'eq⟩ := Subgroup.mem_map.mp hy_mem
  exact ⟨g, hgH0, d', hPd hd'P, hd'P, by simpa [MulAut.conj_apply] using hd'eq.symm⟩

theorem mem_sup_zpowers_of_mul_eq_zpow {Y : Type} [Group Y] {U : Subgroup Y}
    {y d u z u' : Y} {n : ℤ} (hu : u ∈ U) (hu' : u' ∈ U)
    (hy : y = d * u) (hz : z = d ^ n * u') :
    z ∈ U ⊔ Subgroup.zpowers y := by
  have hmem_aux : z ∈ Subgroup.zpowers d ⊔ U := by
    rw [hz]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩) hu'
  have hmem : z ∈ U ⊔ Subgroup.zpowers d := by simpa [sup_comm] using hmem_aux
  have hy_mem_aux : y ∈ Subgroup.zpowers d ⊔ U := by
    rw [hy]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers d) hu
  have hy_mem : y ∈ U ⊔ Subgroup.zpowers d := by simpa [sup_comm] using hy_mem_aux
  have hd_mem_aux : d ∈ Subgroup.zpowers y ⊔ U := by
    have hd_eq : d = y * u⁻¹ := by
      rw [hy]
      group
    rw [hd_eq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers y) (Subgroup.inv_mem _ hu)
  have hd_mem : d ∈ U ⊔ Subgroup.zpowers y := by simpa [sup_comm] using hd_mem_aux
  have hsup_eq : U ⊔ Subgroup.zpowers d = U ⊔ Subgroup.zpowers y := by
    apply le_antisymm
    · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hd_mem)
    · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hy_mem)
  rwa [hsup_eq] at hmem

private theorem mem_sup_zpowers_of_borel {Y : Type} [Group Y] [Finite Y]
    (hB : ∀ U : Sylow 2 Y, ∃ D : Subgroup Y, IsCyclic D ∧ 5 ∣ Nat.card D ∧
      (U : Subgroup Y) ⊓ D = ⊥ ∧
      (U : Subgroup Y) ⊔ D = Subgroup.normalizer ((U : Subgroup Y) : Set Y))
    (U : Sylow 2 Y) (y z : Y)
    (hy : y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y))
    (hz : z ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y))
    (hy3 : orderOf y = 3) (hz3 : orderOf z = 3) :
    z ∈ (U : Subgroup Y) ⊔ Subgroup.zpowers y := by
  obtain ⟨D, hDcyc, h5D, hbot, hsup⟩ := hB U
  obtain ⟨dy, hdyD, uy, huyU, hdecomp_y, hdy3⟩ :=
    exists_component_of_mem_normalizer U.isPGroup' hbot hsup hy hy3
  obtain ⟨dz, hdzD, uz, huzU, hdecomp_z, hdz3⟩ :=
    exists_component_of_mem_normalizer U.isPGroup' hbot hsup hz hz3
  haveI : IsCyclic D := hDcyc
  have hzp_eq : Subgroup.zpowers (⟨dy, hdyD⟩ : D) =
      Subgroup.zpowers (⟨dz, hdzD⟩ : D) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hdy3, hdz3]
  have hdz_mem : (⟨dz, hdzD⟩ : D) ∈ Subgroup.zpowers (⟨dy, hdyD⟩ : D) := by
    rw [hzp_eq]
    exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hdz_mem
  have hdz_eq : dy ^ n = dz := by
    have hval := congrArg Subtype.val hn
    simpa using hval
  exact mem_sup_zpowers_of_mul_eq_zpow huyU huzU hdecomp_y (by rw [hdecomp_z, ← hdz_eq])

theorem exists_order_five_commute_of_conj {Y : Type} [Group Y] [Finite Y]
    {D N : Subgroup Y} (hDcyc : IsCyclic D) (h5D : 5 ∣ Nat.card D)
    {g d' y : Y} (hd'D : d' ∈ D) (hy : y = g * d' * g⁻¹)
    (hgN : g ∈ N) (hDN : D ≤ N) :
    ∃ t ∈ N, orderOf t = 5 ∧ Commute t y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨t0, ht05⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 h5D
  have ht0N : (t0 : Y) ∈ N := hDN t0.2
  let t : Y := MulAut.conj g (t0 : Y)
  have ht_eq : t = g * (t0 : Y) * g⁻¹ := by simp [t, MulAut.conj_apply]
  have htN : t ∈ N := by
    rw [ht_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN ht0N) (Subgroup.inv_mem _ hgN)
  have ht5 : orderOf t = 5 := by
    change orderOf (MulAut.conj g (t0 : Y)) = 5
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    exact ht05
  have hcomm_dt : d' * (t0 : Y) = (t0 : Y) * d' := by
    haveI : IsCyclic D := hDcyc
    letI : CommGroup D := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨d', hd'D⟩ : D) ⟨(t0 : Y), t0.2⟩)
  refine ⟨t, htN, ht5, (commute_iff_eq t y).mpr ?_⟩
  rw [ht_eq, hy]
  calc
    (g * (t0 : Y) * g⁻¹) * (g * d' * g⁻¹) = g * ((t0 : Y) * d') * g⁻¹ := by group
    _ = g * (d' * (t0 : Y)) * g⁻¹ := by rw [hcomm_dt]
    _ = (g * d' * g⁻¹) * (g * (t0 : Y) * g⁻¹) := by group

private theorem exists_commute_order_five_of_borel {Y : Type} [Group Y] [Finite Y]
    (hB : ∀ U : Sylow 2 Y, ∃ D : Subgroup Y, IsCyclic D ∧ 5 ∣ Nat.card D ∧
      (U : Subgroup Y) ⊓ D = ⊥ ∧
      (U : Subgroup Y) ⊔ D = Subgroup.normalizer ((U : Subgroup Y) : Set Y))
    (hBclause : ∀ (U : Sylow 2 Y) (y z : Y),
      y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
      z ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
      orderOf y = 3 → orderOf z = 3 →
      z ∈ (U : Subgroup Y) ⊔ Subgroup.zpowers y)
    (U : Sylow 2 Y) (y : Y)
    (hy : y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y)) (hy3 : orderOf y = 3) :
    ∃ t ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y), orderOf t = 5 ∧ Commute t y := by
  obtain ⟨D, hDcyc, h5D, hbot, hsup⟩ := hB U
  obtain ⟨d, hdD, u, huU, hdecomp, hd3⟩ :=
    exists_component_of_mem_normalizer U.isPGroup' hbot hsup hy hy3
  have hdN : d ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) := by
    rw [← hsup]
    exact Subgroup.mem_sup_right hdD
  have hdH0 : d ∈ (U : Subgroup Y) ⊔ Subgroup.zpowers y := hBclause U y d hy hdN hy3 hd3
  obtain ⟨g, hgH0, d', hd'H0, hd'z, hy_eq⟩ :=
    exists_conj_eq_of_order_three_mem_sup_zpowers U.isPGroup' hy hy3 hdH0 hd3
  have hd'D : d' ∈ D := Subgroup.zpowers_le.mpr hdD hd'z
  have hgN : g ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) :=
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hy)) hgH0
  have hDN : D ≤ Subgroup.normalizer ((U : Subgroup Y) : Set Y) := by
    rw [← hsup]
    exact le_sup_right
  exact exists_order_five_commute_of_conj hDcyc h5D hd'D hy_eq hgN hDN

theorem res1HJYFacts_of_borel {Y : Type} [Group Y] [Finite Y]
    (hTI : ∀ U V : Sylow 2 Y, U ≠ V → (U : Subgroup Y) ⊓ V = ⊥)
    (hB : ∀ U : Sylow 2 Y, ∃ D : Subgroup Y, IsCyclic D ∧ 5 ∣ Nat.card D ∧
      (U : Subgroup Y) ⊓ D = ⊥ ∧
      (U : Subgroup Y) ⊔ D = Subgroup.normalizer ((U : Subgroup Y) : Set Y)) :
    Res1HJYFacts Y := by
  have hBclause := mem_sup_zpowers_of_borel hB
  exact ⟨hTI, hBclause, exists_commute_order_five_of_borel hB hBclause⟩

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
