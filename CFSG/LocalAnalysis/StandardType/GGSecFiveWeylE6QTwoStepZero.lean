module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoStepZeroAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoStepZeroAux2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem pow_three_mem_centralizer_of_forall_fix (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (hfix : ∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z) :
    g ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
  have hc3 : Subgroup.normalizerMonoidHom L ⟨g, hg⟩ ^ 3 = 1 :=
    normalizerMonoidHom_pow_three_eq_one hK θ hperf hmap hg hfix
  have hc3' : Subgroup.normalizerMonoidHom L ⟨g, hg⟩ ^ 3 =
      Subgroup.normalizerMonoidHom L ⟨g ^ 3, Subgroup.pow_mem _ hg 3⟩ := by
    rw [← map_pow]
    congr 1
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : ((Subgroup.normalizerMonoidHom L ⟨g, hg⟩ ^ 3) ⟨x, hx⟩ : ↥L) = ⟨x, hx⟩ := by
    rw [hc3]
    rfl
  have hx'' : (Subgroup.normalizerMonoidHom L ⟨g ^ 3, Subgroup.pow_mem _ hg 3⟩) ⟨x, hx⟩ =
      ⟨x, hx⟩ := by
    rw [← hc3']
    exact hx'
  have hval : g ^ 3 * x * (g ^ 3)⁻¹ = x := by
    have := congrArg Subtype.val hx''
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
  calc x * g ^ 3 = (g ^ 3 * x * (g ^ 3)⁻¹) * g ^ 3 := by rw [hval]
    _ = g ^ 3 * x := by group

theorem relPPrimeCore_le_centralizer_L (hK : Nat.card K = 4) {b : G} {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal) :
    relPPrimeCore 3 (Subgroup.centralizer {b}) ≤ Subgroup.centralizer (L : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let O : Subgroup G := relPPrimeCore 3 C
  have hQle_center : (O ⊓ L).subgroupOf L ≤ Subgroup.center ↥L :=
    relPPrimeCore_inf_subgroupOf_le_center hK θ hLb hN
  have hOle : O ≤ C := AlmostSimple.relPPrimeCore_le (p := 3) C
  have hOnorm : (O.subgroupOf C).Normal :=
    AlmostSimple.relPPrimeCore_normal Nat.prime_three C
  have hCn : C ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLb).mp hN
  intro o ho
  have hoC : o ∈ C := hOle ho
  have hoN : o ∈ Subgroup.normalizer (L : Set G) := hCn hoC
  let c : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨o, hoN⟩
  have hcent : ∀ x : ↥L, c x * x⁻¹ ∈ Subgroup.center ↥L := by
    intro x
    have hxmem : ((c x * x⁻¹ : ↥L) : G) ∈ O ⊓ L := by
      constructor
      · have hconj : (x : G) * o⁻¹ * x⁻¹ ∈ O := by
          have hconj' : (⟨(x : G), hLb x.2⟩ : ↥C) * ⟨o⁻¹, hOle (O.inv_mem ho)⟩ *
              (⟨(x : G), hLb x.2⟩ : ↥C)⁻¹ ∈ O.subgroupOf C :=
            hOnorm.conj_mem ⟨o⁻¹, hOle (O.inv_mem ho)⟩ (O.inv_mem ho) ⟨(x : G), hLb x.2⟩
          exact Subgroup.mem_subgroupOf.mp hconj'
        have heq : ((c x * x⁻¹ : ↥L) : G) = o * ((x : G) * o⁻¹ * x⁻¹) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
          group
        rw [heq]
        exact O.mul_mem ho hconj
      · have hconjL : o * (x : G) * o⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp hoN (x : G)).mp x.2
        have heq : ((c x * x⁻¹ : ↥L) : G) = o * (x : G) * o⁻¹ * (x : G)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
        rw [heq]
        exact L.mul_mem hconjL (L.inv_mem x.2)
    exact hQle_center (Subgroup.mem_subgroupOf.mpr hxmem)
  have hc_one : c = 1 := mulAut_eq_one_of_forall_mul_inv_mem_center hperf c hcent
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : (c ⟨l, hl⟩ : ↥L) = ⟨l, hl⟩ := by rw [hc_one]; rfl
  have hval : o * l * o⁻¹ = l := by
    have := congrArg Subtype.val hl'
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
  calc l * o = (o * l * o⁻¹) * o := by rw [hval]
    _ = o * l := by group

theorem le_zpowers_of_isPGroup_three (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {b : G} {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hb : orderOf b = 3) (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * b * n⁻¹ ∈ L,
      θ (QuotientGroup.mk (⟨n * b * n⁻¹, h⟩ : L)) = USixTwo.threeA hω)
    {S : Subgroup G} (hS3 : IsPGroup 3 S)
    (hSR : S ≤ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G)) :
    S ≤ Subgroup.zpowers b := by
  classical
  by_contra hSnot
  obtain ⟨sG, -, hs3, -, hsBs⟩ :=
    exists_orderOf_nine_mem_sup hK θ hZ2 hb hLb hcyc hBs hbBs hcard hmap hS3 hSR hSnot
  exact false_of_pow_three_mem_centralizer hω θ hZ2 hb hLb hN hconj hbBs
    (fun g hg hfix => pow_three_mem_centralizer_of_forall_fix hK θ hperf hmap hg hfix)
    hs3 hsBs

theorem centralizer_inf_eq_relPPrimeCore_sup (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {b : G} {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hb : orderOf b = 3) (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * b * n⁻¹ ∈ L,
      θ (QuotientGroup.mk (⟨n * b * n⁻¹, h⟩ : L)) = USixTwo.threeA hω) :
    Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) =
      relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b := by
  classical
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let CL : Subgroup G := Subgroup.centralizer (L : Set G)
  let C : Subgroup G := Cb ⊓ CL
  let O : Subgroup G := relPPrimeCore 3 Cb
  let P : Subgroup G := Subgroup.zpowers b
  change C = O ⊔ P
  have hCb_le : C ≤ Cb := inf_le_left
  have hbC : b ∈ CL := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLb hl)
  have hbCb : b ∈ Cb := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  have hPC : P ≤ C := le_inf (Subgroup.zpowers_le.mpr hbCb) (Subgroup.zpowers_le.mpr hbC)
  have hP3 : IsPGroup 3 ↥P := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb, pow_one]
  let Pc : Sylow 3 ↥C :=
    { toSubgroup := P.subgroupOf C
      isPGroup' := hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
      is_maximal' := by
        intro Q hQ hle
        have hQle : Q ≤ P.subgroupOf C := by
          intro q hq
          refine Subgroup.mem_subgroupOf.mpr ?_
          have hQmap : Q.map C.subtype ≤ P := by
            refine le_zpowers_of_isPGroup_three hK hω θ hperf hZ2 hb hLb hN hcyc hBs hbBs
              hcard hmap hconj (hQ.map C.subtype) ?_
            rintro x ⟨q', hq', rfl⟩
            exact q'.2
          exact hQmap ⟨q, hq, rfl⟩
        exact le_antisymm hQle hle }
  have hPcent : Subgroup.normalizer (Pc : Set ↥C) ≤ Subgroup.centralizer (Pc : Set ↥C) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hxcomm : (x : G) * b = b * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hCb_le x.2)
    have hPle : P ≤ Subgroup.centralizer ({(x : G)} : Set G) :=
      Subgroup.zpowers_le.mpr (by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hxcomm.symm)
    refine Subtype.ext ?_
    show (p : G) * (x : G) = (x : G) * (p : G)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPle hpP)
  obtain ⟨Kc, hKn, hK3, hKidx, hKuniq, -, -, hKsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement Pc hPcent
  have hmap_eq : Kc.map C.subtype = O :=
    map_burnside_complement_eq_relPPrimeCore hb hLb hN
      (relPPrimeCore_le_centralizer_L hK θ hperf hLb hN)
      Pc (by rfl) Kc hKn hK3 hKidx hKuniq
  have htopmap : (⊤ : Subgroup ↥C).map C.subtype = C := by
    rw [← Subgroup.subgroupOf_self C]
    exact Subgroup.map_subgroupOf_eq_of_le le_rfl
  have hsupmap : (Kc ⊔ (Pc : Subgroup ↥C)).map C.subtype = C := by
    rw [hKsup, htopmap]
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPC, hmap_eq] at hsupmap
  exact hsupmap.symm

theorem relPPrimeCore_le_and_not_two_dvd_index (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {b : G} {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hb : orderOf b = 3) (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * b * n⁻¹ ∈ L,
      θ (QuotientGroup.mk (⟨n * b * n⁻¹, h⟩ : L)) = USixTwo.threeA hω) :
    relPPrimeCore 3 (Subgroup.centralizer {b}) ≤ Subgroup.centralizer (Bs : Set G) ∧
      ¬ 2 ∣ ((relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
        (Subgroup.centralizer (Bs : Set G))).index := by
  classical
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let CL : Subgroup G := Subgroup.centralizer (L : Set G)
  let C : Subgroup G := Cb ⊓ CL
  let O : Subgroup G := relPPrimeCore 3 Cb
  let P : Subgroup G := Subgroup.zpowers b
  let Cbs : Subgroup G := Subgroup.centralizer (Bs : Set G)
  have hbC : b ∈ CL := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLb hl)
  have hbCb : b ∈ Cb := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  have hCb_le : C ≤ Cb := inf_le_left
  have hPC : P ≤ C := le_inf (Subgroup.zpowers_le.mpr hbCb) (Subgroup.zpowers_le.mpr hbC)
  have hOleCb : O ≤ Cb :=
    AlmostSimple.relPPrimeCore_le
      (p := 3) Cb
  have hOleCL : O ≤ CL := relPPrimeCore_le_centralizer_L hK θ hperf hLb hN
  have hOleC : O ≤ C := le_inf hOleCb hOleCL
  have hOmain : O ≤ Cbs := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨p, hp, y, hy, hzy⟩ :=
      exists_mul_eq_of_mem_Bstar hK θ hZ2 hb hbC hBs hbBs hcard hmap hz
    have hop : o * p = p * o := by
      have hPle : P ≤ Subgroup.centralizer ({o} : Set G) := by
        refine Subgroup.zpowers_le.mpr ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hOleCb ho)).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hPle hp)).symm
    have hoy : o * y = y * o :=
      (Subgroup.mem_centralizer_iff.mp (hOleCL ho) y hy.2).symm
    rw [← hzy]
    calc (p * y) * o = p * (y * o) := by group
      _ = p * (o * y) := by rw [hoy]
      _ = (p * o) * y := by group
      _ = (o * p) * y := by rw [hop]
      _ = o * (p * y) := by group
  refine ⟨hOmain, ?_⟩
  let X : Sylow 2 ↥Cbs := Classical.choice (inferInstance : Nonempty (Sylow 2 ↥Cbs))
  have hXle : (X : Subgroup ↥Cbs) ≤ O.subgroupOf Cbs := by
    intro t ht
    have hX2 : IsPGroup 2 ↥(X : Subgroup ↥Cbs) := X.isPGroup'
    obtain ⟨n, hn⟩ := hX2 ⟨t, ht⟩
    have ht_ord : orderOf (t : ↥Cbs) ∣ 2 ^ n := by
      have h := (orderOf_dvd_iff_pow_eq_one).mpr hn
      rwa [Subgroup.orderOf_mk] at h
    have htb : (t : G) ∈ Cb := centralizer_Bstar_le_centralizer_b hbBs t.2
    have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) :=
      centralizer_b_le_normalizer hLb hN htb
    have htfix : ∀ z ∈ Bs ⊓ L, (t : G) * z * (t : G)⁻¹ = z := by
      intro z hz
      have hcomm : z * (t : G) = (t : G) * z := Subgroup.mem_centralizer_iff.mp t.2 z hz.1
      calc (t : G) * z * (t : G)⁻¹ = z * (t : G) * (t : G)⁻¹ := by rw [hcomm]
        _ = z := by group
    have ht3 : (t : G) ^ 3 ∈ CL :=
      pow_three_mem_centralizer_of_forall_fix hK θ hperf hmap htN htfix
    have htCL : (t : G) ∈ CL := by
      have hcop : Nat.Coprime (orderOf (t : ↥Cbs)) 3 :=
        (((by norm_num : Nat.Coprime 3 2).pow_right n).coprime_dvd_right ht_ord).symm
      have hcop' : Nat.Coprime (orderOf (t : G)) 3 := by
        simpa using hcop
      have hle : Subgroup.zpowers ((t : G) ^ 3) ≤ Subgroup.zpowers (t : G) :=
        Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩) 3)
      have hzeq : Subgroup.zpowers ((t : G) ^ 3) = Subgroup.zpowers (t : G) :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop'])
      have hmem : (t : G) ∈ Subgroup.zpowers ((t : G) ^ 3) := by
        rw [hzeq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
      exact Subgroup.zpowers_le.mpr ht3 hmem
    have htC : (t : G) ∈ C := ⟨htb, htCL⟩
    have ht_sup : (t : G) ∈ O ⊔ P := by
      have hCeq := centralizer_inf_eq_relPPrimeCore_sup hK hω θ hperf hZ2 hb hLb hN hcyc hBs hbBs
        hcard hmap hconj
      rw [← hCeq]
      exact htC
    haveI : (O.subgroupOf C).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hconj : (⟨(g : G), hCb_le g.2⟩ : ↥Cb) * ⟨x, hCb_le x.2⟩ *
          (⟨(g : G), hCb_le g.2⟩ : ↥Cb)⁻¹ ∈ O.subgroupOf Cb :=
        (AlmostSimple.relPPrimeCore_normal
          Nat.prime_three Cb).conj_mem ⟨x, hCb_le x.2⟩ hxO ⟨(g : G), hCb_le g.2⟩
      exact Subgroup.mem_subgroupOf.mp hconj
    have ht_sup' : (⟨(t : G), htC⟩ : ↥C) ∈ O.subgroupOf C ⊔ P.subgroupOf C := by
      rw [← Subgroup.subgroupOf_sup hOleC hPC]
      exact Subgroup.mem_subgroupOf.mpr ht_sup
    obtain ⟨o, hoO, p, hpP, hop⟩ := Subgroup.mem_sup_of_normal_left.mp ht_sup'
    let q : ↥C →* (↥C ⧸ O.subgroupOf C) := QuotientGroup.mk' (O.subgroupOf C)
    have hq : q ⟨(t : G), htC⟩ = q p := by
      rw [← hop, map_mul, show q o = 1 from (QuotientGroup.eq_one_iff o).mpr hoO, one_mul]
    have hp3 : ((p : ↥C) : G) ∈ P := Subgroup.mem_subgroupOf.mp hpP
    have hP3 : IsPGroup 3 ↥P := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hb, pow_one]
    obtain ⟨m, hm⟩ := hP3 ⟨(p : G), hp3⟩
    have hp_ord : orderOf (p : ↥C) ∣ 3 ^ m := by
      have h : orderOf (⟨(p : G), hp3⟩ : ↥P) ∣ 3 ^ m :=
        (orderOf_dvd_iff_pow_eq_one).mpr hm
      rw [Subgroup.orderOf_mk] at h
      simpa using h
    have h2n : orderOf (q ⟨(t : G), htC⟩) ∣ 2 ^ n := by
      have h1 : orderOf (q ⟨(t : G), htC⟩) ∣ orderOf (⟨(t : G), htC⟩ : ↥C) :=
        orderOf_map_dvd q _
      rw [Subgroup.orderOf_mk] at h1
      exact h1.trans (by simpa using ht_ord)
    have h3m : orderOf (q ⟨(t : G), htC⟩) ∣ 3 ^ m := by
      rw [hq]
      exact (orderOf_map_dvd q p).trans hp_ord
    have hcop : Nat.Coprime (2 ^ n) (3 ^ m) :=
      Nat.coprime_pow_primes n m Nat.prime_two Nat.prime_three (by norm_num)
    have h1 : orderOf (q ⟨(t : G), htC⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2n h3m
    have hq1 : q ⟨(t : G), htC⟩ = 1 := orderOf_eq_one_iff.mp h1
    have htO : (t : G) ∈ O := by
      have hmem : (⟨(t : G), htC⟩ : ↥C) ∈ O.subgroupOf C := (QuotientGroup.eq_one_iff _).mp hq1
      exact Subgroup.mem_subgroupOf.mp hmem
    exact Subgroup.mem_subgroupOf.mpr htO
  intro h2
  exact X.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hXle))

end CFSG.StandardType.E6QTwo

end
