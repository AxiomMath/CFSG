module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoStepZeroAux
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

abbrev centralizerInf (b : G) (L : Subgroup G) : Subgroup G :=
  Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G)

theorem exists_orderOf_nine_mem_sup (hK : Nat.card K = 4) {b : G} {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hb : orderOf b = 3)
    (hLb : L ≤ Subgroup.centralizer {b})
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    {S : Subgroup G} (hS3 : IsPGroup 3 S)
    (hSR : S ≤ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G))
    (hSnot : ¬ S ≤ Subgroup.zpowers b) :
    ∃ sG : G, orderOf sG = 9 ∧ (sG ^ 3 = b ∨ sG ^ 3 = b⁻¹) ∧
      sG ∈ Subgroup.centralizer ({b} : Set G) ∧
      ∀ z ∈ Bs, sG * z = z * sG := by
  classical
  have hbC : b ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLb hl)
  have hPL : Subgroup.zpowers b ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hbC
  have hbCb : b ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  have hP3 : IsPGroup 3 (Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb, pow_one]
  have hbCS : b ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp ((hSR hx).1)
  have hPT : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (S : Set G) hbCS)
  have hT3 : IsPGroup 3 ↥(S ⊔ Subgroup.zpowers b) := hS3.to_sup_of_normal_left' hP3 hPT
  have hTR : S ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) :=
    sup_le hSR (le_inf (Subgroup.zpowers_le.mpr hbCb) hPL)
  haveI hcycT : IsCyclic ↥(S ⊔ Subgroup.zpowers b) := hcyc _ hT3 (hTR.trans inf_le_right)
  have hcardP : Nat.card ↥(Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hb]
  obtain ⟨k, hk⟩ := hT3.exists_card_eq
  have hTne : Nat.card ↥(S ⊔ Subgroup.zpowers b) ≠ 3 := by
    intro h3
    have hEq : Subgroup.zpowers b = S ⊔ Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, hcardP])
    exact hSnot (fun x hx => hEq ▸ Subgroup.mem_sup_left hx)
  have h3dvdT : 3 ∣ Nat.card ↥(S ⊔ Subgroup.zpowers b) := by
    have h := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers b ≤ S ⊔ Subgroup.zpowers b)
    rwa [hcardP] at h
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [pow_zero] at hk
        rw [hk] at h3dvdT
        norm_num at h3dvdT
      · rw [pow_one] at hk
        exact absurd hk hTne
    · exact h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(S ⊔ Subgroup.zpowers b))
  have hgord : orderOf g = Nat.card ↥(S ⊔ Subgroup.zpowers b) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have h9dvd : 9 ∣ orderOf g := by
    rw [hgord, hk]
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 hk2
  let s : ↥(S ⊔ Subgroup.zpowers b) := g ^ (orderOf g / 9)
  let sG : G := (s : ↥(S ⊔ Subgroup.zpowers b))
  have hsord : orderOf s = 9 :=
    orderOf_pow_orderOf_div (x := g) (n := 9)
      (by rw [hgord, hk]; exact pow_ne_zero k (by norm_num)) h9dvd
  have hbT_mem : b ∈ S ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  let bT : ↥(S ⊔ Subgroup.zpowers b) := ⟨b, hbT_mem⟩
  have hbTord : orderOf bT = 3 := by
    rw [show bT = ⟨b, hbT_mem⟩ from rfl, Subgroup.orderOf_mk]
    exact hb
  have hs3ord : orderOf (s ^ 3) = 3 := by
    have h := orderOf_pow_orderOf_div (x := s) (n := 3)
      (by rw [hsord]; norm_num) (by rw [hsord]; norm_num)
    rwa [hsord] at h
  have hsubeq : Subgroup.zpowers (s ^ 3) = Subgroup.zpowers bT := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hs3ord, hbTord]
  have hs3eq : s ^ 3 = bT ∨ s ^ 3 = bT⁻¹ :=
    eq_or_inv_of_orderOf_eq_three_of_mem_zpowers hs3ord hbTord (by
      rw [← hsubeq]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hs3val : sG ^ 3 = b ∨ sG ^ 3 = b⁻¹ := by
    rcases hs3eq with h | h
    · left
      have := congrArg Subtype.val h
      simpa [sG] using this
    · right
      have := congrArg Subtype.val h
      simpa [sG] using this
  have hsCb : sG ∈ Subgroup.centralizer ({b} : Set G) := (hTR s.2).1
  have hsCL : sG ∈ Subgroup.centralizer (L : Set G) := (hTR s.2).2
  have hsBs : ∀ z ∈ Bs, sG * z = z * sG := by
    intro z hz
    obtain ⟨p, hp, y, hy, hzy⟩ :=
      exists_mul_eq_of_mem_Bstar hK θ hZ2 hb hbC hBs hbBs hcard hmap hz
    have hPle : Subgroup.zpowers b ≤ Subgroup.centralizer ({sG} : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hsCb).symm
    have hsp : sG * p = p * sG :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hPle hp)).symm
    have hys : sG * y = y * sG := (Subgroup.mem_centralizer_iff.mp hsCL y hy.2).symm
    rw [← hzy]
    calc sG * (p * y) = (sG * p) * y := by group
      _ = (p * sG) * y := by rw [hsp]
      _ = p * (sG * y) := by group
      _ = p * (y * sG) := by rw [hys]
      _ = (p * y) * sG := by group
  have hsGord : orderOf sG = 9 := by
    rw [← Subgroup.orderOf_mk (H := S ⊔ Subgroup.zpowers b) (a := sG) s.2]
    exact hsord
  exact ⟨sG, hsGord, hs3val, hsCb, hsBs⟩

theorem false_of_pow_three_mem_centralizer {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {b : G}
    {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hb : orderOf b = 3)
    (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal)
    (hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * b * n⁻¹ ∈ L,
      θ (QuotientGroup.mk (⟨n * b * n⁻¹, h⟩ : L)) = USixTwo.threeA hω)
    (hbBs : b ∈ Bs)
    (hpow3 : ∀ g ∈ Subgroup.normalizer (L : Set G),
      (∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z) → g ^ 3 ∈ Subgroup.centralizer (L : Set G))
    {sG : G} (hs3 : sG ^ 3 = b ∨ sG ^ 3 = b⁻¹)
    (hsBs : ∀ z ∈ Bs, sG * z = z * sG) : False := by
  classical
  obtain ⟨n, hnN, heL, -⟩ := hconj
  let e : G := n * b * n⁻¹
  have he_ord : orderOf e = 3 := by
    have h1 : e = MulAut.conj n b := by
      rw [MulAut.conj_apply]
    rw [h1, MulEquiv.orderOf_eq, hb]
  let s' : G := n * sG * n⁻¹
  have hs'pow : s' ^ 3 = n * sG ^ 3 * n⁻¹ := by
    have h3 : sG ^ 3 = sG * sG * sG := by rw [pow_succ, pow_succ, pow_one]
    rw [show s' = n * sG * n⁻¹ from rfl, h3, pow_succ, pow_succ, pow_one]
    group
  have hs'3eq : s' ^ 3 = e ∨ s' ^ 3 = e⁻¹ := by
    rcases hs3 with h | h
    · left
      rw [hs'pow, h]
    · right
      have h1 : n * b⁻¹ * n⁻¹ = e⁻¹ := by
        rw [show e = n * b * n⁻¹ from rfl]
        group
      rw [hs'pow, h, h1]
  have hconjBs : ∀ z ∈ Bs, s' * z * s'⁻¹ = z := by
    intro z hz
    have hz' : n⁻¹ * z * n ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) z).mp hz
      simpa using this
    have hsw : sG * (n⁻¹ * z * n) * sG⁻¹ = n⁻¹ * z * n := by
      have hcomm := hsBs (n⁻¹ * z * n) hz'
      calc sG * (n⁻¹ * z * n) * sG⁻¹ = (n⁻¹ * z * n) * sG * sG⁻¹ := by rw [hcomm]
        _ = n⁻¹ * z * n := by group
    calc s' * z * s'⁻¹ = n * (sG * (n⁻¹ * z * n) * sG⁻¹) * n⁻¹ := by
          show n * sG * n⁻¹ * z * (n * sG * n⁻¹)⁻¹ = _
          group
      _ = n * (n⁻¹ * z * n) * n⁻¹ := by rw [hsw]
      _ = z := by group
  have hs'Cb : s' ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hconjBs b hbBs
    calc s' * b = (s' * b * s'⁻¹) * s' := by group
      _ = b * s' := by rw [h]
  have hs'N : s' ∈ Subgroup.normalizer (L : Set G) :=
    centralizer_b_le_normalizer hLb hN hs'Cb
  have hs'3 : s' ^ 3 ∈ Subgroup.centralizer (L : Set G) :=
    hpow3 s' hs'N (fun z hz => hconjBs z hz.1)
  have hz_mem : s' ^ 3 ∈ L := by
    rcases hs'3eq with h | h
    · rw [h]; exact heL
    · rw [h]; exact L.inv_mem heL
  have hz_center : (⟨s' ^ 3, hz_mem⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hs'3 x x.2)
  have hz_ord : orderOf (⟨s' ^ 3, hz_mem⟩ : ↥L) = 3 := by
    rw [Subgroup.orderOf_mk]
    rcases hs'3eq with h | h
    · rw [h]; exact he_ord
    · rw [h, orderOf_inv]; exact he_ord
  let z : ↥(Subgroup.center ↥L) := ⟨⟨s' ^ 3, hz_mem⟩, hz_center⟩
  refine false_of_isPGroup_two_of_orderOf_eq_three hZ2 (z := z) ?_
  rw [Subgroup.orderOf_mk]
  exact hz_ord

theorem map_burnside_complement_eq_relPPrimeCore {b : G} {L : Subgroup G}
    (hb : orderOf b = 3) (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal)
    (hOleCL : relPPrimeCore 3 (Subgroup.centralizer {b}) ≤ Subgroup.centralizer (L : Set G))
    (Pc : Sylow 3 ↥(centralizerInf b L))
    (hPc : (Pc : Subgroup ↥(centralizerInf b L)) =
      (Subgroup.zpowers b).subgroupOf (centralizerInf b L))
    (Kc : Subgroup ↥(centralizerInf b L))
    (hKn : Kc.Normal) (hK3 : ¬ 3 ∣ Nat.card ↥Kc)
    (hKidx : Kc.index = Nat.card ↥(Pc : Subgroup ↥(centralizerInf b L)))
    (hKuniq : ∀ K' : Subgroup ↥(centralizerInf b L), K'.Normal → ¬ 3 ∣ Nat.card ↥K' →
      K'.index = Nat.card ↥(Pc : Subgroup ↥(centralizerInf b L)) → K' = Kc) :
    Kc.map (centralizerInf b L).subtype = relPPrimeCore 3 (Subgroup.centralizer {b}) := by
  classical
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let CL : Subgroup G := Subgroup.centralizer (L : Set G)
  let C : Subgroup G := Cb ⊓ CL
  let O : Subgroup G := relPPrimeCore 3 Cb
  let P : Subgroup G := Subgroup.zpowers b
  change Kc.map C.subtype = O
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
  have hPc_card : Nat.card ↥(Pc : Subgroup ↥(centralizerInf b L)) = 3 := by
    rw [hPc]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, Nat.card_zpowers, hb]
  have hKquot : IsPGroup 3 (↥C ⧸ Kc) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [← Subgroup.index_eq_card, hKidx, hPc_card, pow_one]
  have hOle : O ≤ C :=
    le_inf (AlmostSimple.relPPrimeCore_le (p := 3) Cb) hOleCL
  have hOnormC : (O.subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hx
    have hxC : (x : G) ∈ C := x.2
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hconj : (⟨(g : G), hCb_le g.2⟩ : ↥Cb) * ⟨x, hCb_le x.2⟩ *
        (⟨(g : G), hCb_le g.2⟩ : ↥Cb)⁻¹ ∈ O.subgroupOf Cb :=
      (AlmostSimple.relPPrimeCore_normal
        Nat.prime_three Cb).conj_mem ⟨x, hCb_le x.2⟩ hxO ⟨(g : G), hCb_le g.2⟩
    exact Subgroup.mem_subgroupOf.mp hconj
  have hOcop : Nat.Coprime 3 (Nat.card ↥O) :=
    AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three Cb
  have hOsub_3 : ¬ 3 ∣ Nat.card ↥(O.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv]
    intro h3
    have hgcd : 3 ∣ Nat.gcd 3 (Nat.card ↥O) := Nat.dvd_gcd dvd_rfl h3
    rw [show Nat.gcd 3 (Nat.card ↥O) = 1 from hOcop] at hgcd
    norm_num at hgcd
  have hOK : O.subgroupOf C ≤ Kc := by
    haveI := hKn
    exact CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient Kc (O.subgroupOf C)
      hKquot hOsub_3
  have hOleK : O ≤ Kc.map C.subtype := by
    intro x hx
    have hxC : x ∈ C := hOle hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hOK (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hNL : Cb ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLb).mp hN
  have hCLnorm : Cb ≤ Subgroup.normalizer (CL : Set G) :=
    hNL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (L : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (L : Set G)))
  have hCyN : Cb ≤ Subgroup.normalizer (C : Set G) := by
    intro y hy
    have h1 := hCLnorm hy
    have h2 : y ∈ Subgroup.normalizer (Cb : Set G) := Subgroup.le_normalizer hy
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro z
    change (z ∈ Cb ∧ z ∈ CL) ↔ (y * z * y⁻¹ ∈ Cb ∧ y * z * y⁻¹ ∈ CL)
    exact and_congr (h2 z) (h1 z)
  have hCnormal : (C.subgroupOf Cb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCb_le).mpr hCyN
  have hKconj : ∀ y ∈ Cb, ∀ z ∈ Kc.map C.subtype, y * z * y⁻¹ ∈ Kc.map C.subtype := by
    intro y hy z hz
    have hyN : y ∈ Subgroup.normalizer (C : Set G) := hCyN hy
    let ψ : MulAut ↥C := C.normalizerMonoidHom ⟨y, hyN⟩
    let ψh : ↥C →* ↥C := ψ.toMonoidHom
    have hψinj : Function.Injective ψh := ψ.injective
    have hψsurj : Function.Surjective ψh := ψ.surjective
    have hψbij : Function.Bijective ψh := ψ.bijective
    have hψmap : Kc.map ψh = Kc := by
      refine hKuniq _ (hKn.map ψh hψsurj) ?_ ?_
      · rw [Subgroup.card_map_of_injective (f := ψh) hψinj]
        exact hK3
      · rw [Subgroup.index_map_of_bijective (f := ψh) hψbij]
        exact hKidx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨ψh k, ?_, ?_⟩
    · rw [← hψmap]
      exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    · show ((ψh k : ↥C) : G) = y * (k : G) * y⁻¹
      rw [show ψh k = ψ k from rfl, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hKmap_le_Cb : Kc.map C.subtype ≤ Cb := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hCb_le c.2
  have hKmap_normal : ((Kc.map C.subtype).subgroupOf Cb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKmap_le_Cb]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hKconj y hy z hz
    · intro hz
      have h1 : y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ ∈ Kc.map C.subtype :=
        hKconj y⁻¹ (Cb.inv_mem hy) (y * z * y⁻¹) hz
      have h2 : y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ = z := by group
      rwa [h2] at h1
  have hK3map : ¬ 3 ∣ Nat.card ↥(Kc.map C.subtype) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hK3
  have hKO : Kc.map C.subtype ≤ O := by
    refine le_sSup ?_
    exact ⟨hKmap_le_Cb, hKmap_normal, Nat.prime_three.coprime_iff_not_dvd.mpr hK3map⟩
  have hKmap_eq_O : Kc.map C.subtype = O := le_antisymm hKO hOleK
  exact hKmap_eq_O

end CFSG.StandardType.E6QTwo

end
