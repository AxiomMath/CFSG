module

public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage12.McLRec
  CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly CFSG.ComponentClassification.StandardRecognition

theorem mem_centralizer_singleton_self {G : Type*} [Group G] (t : G) :
    t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

@[expose] def SylowData (E : Type) [Group E] (z : E) : Prop :=
  ∃ (T : Subgroup E) (f : E), IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ z ∈ T ∧
    (∀ x ∈ T, orderOf x = 2 → (∀ s ∈ T, s * x = x * s) → x = z) ∧
    (∀ x ∈ T, orderOf x = 2 → x ≠ z → IsConj x f)

theorem SylowData.of_mulEquiv {E F : Type} [Group E] [Group F] {z : E} (h : SylowData E z)
    (e : E ≃* F) : SylowData F (e z) := by
  obtain ⟨T, f, hp, hi, hz, hc, hf⟩ := h
  refine ⟨T.map e.toMonoidHom, e f, hp.map e.toMonoidHom, ?_, ⟨z, hz, rfl⟩, ?_, ?_⟩
  · rwa [show T.map e.toMonoidHom = T.map (e : E →* F) from rfl, Subgroup.index_map_equiv]
  · rintro _ ⟨y, hy, rfl⟩ hy2 hcen
    have hy2' : orderOf y = 2 := by rw [← MulEquiv.orderOf_eq e]; exact hy2
    have hyz : y = z := by
      refine hc y hy hy2' fun s hs => e.injective ?_
      have := hcen (e s) ⟨s, hs, rfl⟩
      simpa using this
    rw [hyz]
    rfl
  · rintro _ ⟨y, hy, rfl⟩ hy2 hne
    have hy2' : orderOf y = 2 := by rw [← MulEquiv.orderOf_eq e]; exact hy2
    exact e.toMonoidHom.map_isConj (hf y hy hy2' fun h => hne (by rw [h]; rfl))

section Model

theorem eq_one_or_zC_of_central
    {x : lyC} (hx : (x : J) ∈ lyS)
    (hcomm : ∀ s ∈ lyS, s * (x : J) = (x : J) * s) : x = 1 ∨ x = zC := by
  have hcen : (⟨(x : J), hx⟩ : lyS) ∈ Subgroup.center lyS := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcomm g g.2
  rw [center_lyS, mem_zpowers_zS] at hcen
  rcases hcen with h | h
  · left
    apply Subtype.ext
    have h0 : ((⟨(x : J), hx⟩ : lyS) : J) = ((1 : lyS) : J) := congrArg Subtype.val h
    exact h0
  · right
    apply Subtype.ext
    have h0 : ((⟨(x : J), hx⟩ : lyS) : J) = ((zS : lyS) : J) := congrArg Subtype.val h
    exact h0

theorem sylowData_lyC :
    SylowData lyC zC := by
  have hS2 : IsPGroup 2 lyS := IsPGroup.of_card (n := 8) (by rw [card_lyS]; norm_num)
  have hcardT : Nat.card (lyS.subgroupOf lyC) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyS_le_lyC).toEquiv, card_lyS]
  refine ⟨lyS.subgroupOf lyC, fC, hS2.of_equiv (Subgroup.subgroupOfEquivOfLe lyS_le_lyC).symm,
    ?_, Subgroup.mem_subgroupOf.2 lyz_mem_lyS, ?_, ?_⟩
  · have h := Subgroup.card_mul_index (lyS.subgroupOf lyC)
    rw [hcardT, card_lyC] at h
    have : (lyS.subgroupOf lyC).index = 155925 := by omega
    rw [this]
    norm_num
  · intro x hx hx2 hcen
    rw [Subgroup.mem_subgroupOf] at hx
    have hc : ∀ s ∈ lyS, s * (x : J) = (x : J) * s := by
      intro s hs
      have := hcen ⟨s, lyS_le_lyC hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      have h := congrArg Subtype.val this
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
      exact h
    rcases eq_one_or_zC_of_central hx hc with h | h
    · rw [h, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    · exact h
  · intro x hx hx2 hne
    rw [Subgroup.mem_subgroupOf] at hx
    have hnc : ¬∀ s ∈ lyS, s * (x : J) = (x : J) * s := by
      intro hc
      rcases eq_one_or_zC_of_central hx hc with h | h
      · rw [h, orderOf_one] at hx2
        exact absurd hx2 (by norm_num)
      · exact hne h
    have hx2' : orderOf (x : J) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
    obtain ⟨c, hc, hcf⟩ := conj_to_f hx hx2' hnc
    refine (isConj_comm.1 ?_)
    refine isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcf

end Model

section Local

variable {G : Type} [Group G] [Finite G]

theorem exists_central_involution_of_mem (S : Subgroup G) (hS : IsPGroup 2 S) {t : G}
    (htS : t ∈ S) (ht : orderOf t = 2) :
    ∃ u : G, u ∈ S ∧ orderOf u = 2 ∧ ∀ s ∈ S, s * u = u * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial S := by
    refine ⟨⟨⟨t, htS⟩, 1, fun h => ?_⟩⟩
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hcnt : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hZ
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 : Nat.card (Subgroup.center S) = 1 := by simpa using hk
      have := Finite.one_lt_card_iff_nontrivial.mpr hcnt
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdvd
  refine ⟨((y : S) : G), (y : S).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  · have := Subgroup.mem_center_iff.mp y.2 ⟨s, hs⟩
    exact congrArg Subtype.val this

theorem not_central_mod_oddCore (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2)
    (hcen : (QuotientGroup.mk t : G ⧸ CFSG.oddCore G) ∈ Subgroup.center (G ⧸ CFSG.oddCore G)) :
    False := by
  have hev : Even (Nat.card G) := by
    rw [even_iff_two_dvd, ← ht]
    exact orderOf_dvd_natCard t
  have hodd : CFSG.oddCore G = ⊥ := by
    refine Eq.trans ?_ (pPrimeCore_eq_bot_of_simple hs hev)
    simp only [CFSG.oddCore, CFSG.pPrimeCore, Nat.coprime_two_left]
  have hcomm : ∀ g : G, g * t = t * g := by
    intro g
    have h := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
      Subgroup.mem_bot] at h
    exact inv_inj.mp (mul_eq_one_iff_eq_inv.mp h)
  have htc : t ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => hcomm g
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at htc
    rw [htc, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem isCentralInvolution_and_isConj_of_sylowData (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hD : SylowData (centralizer ({t} : Set G)) ⟨t, mem_centralizer_singleton_self t⟩) :
    IsCentralInvolution t ∧ ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  set t' : C := ⟨t, mem_centralizer_singleton_self t⟩ with ht'
  obtain ⟨T, f, hTp, hTi, hzT, hcen, hconj⟩ := hD
  let PT : Sylow 2 C := hTp.toSylow hTi
  set TG : Subgroup G := T.map C.subtype with hTG
  have hTGp : IsPGroup 2 TG := hTp.map C.subtype
  have htTG : t ∈ TG := ⟨t', hzT, rfl⟩
  have hmemTG : ∀ x : C, x ∈ T → (x : G) ∈ TG := fun x hx => ⟨x, hx, rfl⟩
  obtain ⟨S, hTS⟩ := hTGp.exists_le_sylow
  have htS : t ∈ (S : Subgroup G) := hTS htTG
  have hQ : (S : Subgroup G).subgroupOf C = T := by
    have hQp : IsPGroup 2 ((S : Subgroup G).subgroupOf C) :=
      S.isPGroup'.comap_of_injective C.subtype C.subtype_injective
    have hTQ : (PT : Subgroup C) ≤ (S : Subgroup G).subgroupOf C := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hTS (hmemTG x hx))
    exact PT.3 hQp hTQ
  have hSC : ∀ s ∈ (S : Subgroup G), s ∈ C → ∃ x ∈ T, (x : G) = s := fun s hs hsC =>
    ⟨⟨s, hsC⟩, by rw [← hQ]; exact Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have htcen : ∀ s ∈ (S : Subgroup G), s * t = t * s := by
    obtain ⟨u, huS, hu2, hucen⟩ := exists_central_involution_of_mem (S : Subgroup G) S.isPGroup'
      htS ht
    have huC : u ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact (hucen t htS).symm
    obtain ⟨x, hxT, hxu⟩ := hSC u huS huC
    have hx2 : orderOf x = 2 := by
      rw [← Subgroup.orderOf_coe, hxu]; exact hu2
    have hxt : x = t' := by
      refine hcen x hxT hx2 fun s hs => ?_
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxu]
      exact hucen s (hTS (hmemTG s hs))
    have hut : u = t := by rw [← hxu, hxt]
    intro s hs
    have := hucen s hs
    rwa [hut] at this
  have hcentral : IsCentralInvolution t := ⟨ht, S, htS, htcen⟩
  have hz2 : orderOf (⟨t, htS⟩ : (S : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ht
  have hzZ : (⟨t, htS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact htcen s s.2
  obtain ⟨g, hgS, hgt⟩ : ∃ g : G, g⁻¹ * t * g ∈ (S : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
    by_contra hcon
    push Not at hcon
    have := glauberman_zStar_central_sylow_involution_univ S ⟨t, htS⟩ hzZ hz2 hcon
    exact not_central_mod_oddCore hs hnab ht this.2
  have htf : IsConj t (f : G) := by
    set t₁ : G := g⁻¹ * t * g with ht₁
    have hC1 : t₁ ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact htcen t₁ hgS
    obtain ⟨x, hxT, hxu⟩ := hSC t₁ hgS hC1
    have hx2 : orderOf x = 2 := by
      rw [← Subgroup.orderOf_coe, hxu, ht₁]
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
      rw [MulAut.conj_apply, inv_inv] at this
      rw [this, ht]
    have hxne : x ≠ t' := by
      intro h
      apply hgt
      rw [← hxu, h]
    have hxf : IsConj (x : G) (f : G) := C.subtype.map_isConj (hconj x hxT hx2 hxne)
    have htt1 : IsConj t t₁ := isConj_iff.2 ⟨g⁻¹, by rw [ht₁]; group⟩
    exact htt1.trans (by rw [← hxu]; exact hxf)
  have hall : ∀ u : G, orderOf u = 2 → IsConj u t := by
    intro u hu
    have hp : IsPGroup 2 (Subgroup.zpowers u) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one]
      exact hu
    obtain ⟨Q, hQ'⟩ := hp.exists_le_sylow
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G Q S
    have hmem := Subgroup.smul_mem_pointwise_smul u (MulAut.conj h) (Q : Subgroup G)
      (hQ' (Subgroup.mem_zpowers u))
    rw [← Sylow.coe_subgroup_smul, hh] at hmem
    have hb : h * u * h⁻¹ ∈ (S : Subgroup G) := by simpa [MulAut.smul_def] using hmem
    have hb2 : orderOf (h * u * h⁻¹) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj h) u
      rw [MulAut.conj_apply] at this
      rw [this, hu]
    have hbC : h * u * h⁻¹ ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact htcen _ hb
    obtain ⟨x, hxT, hxu⟩ := hSC _ hb hbC
    have hx2 : orderOf x = 2 := by
      rw [← Subgroup.orderOf_coe, hxu]; exact hb2
    have hub : IsConj u (h * u * h⁻¹) := isConj_iff.2 ⟨h, rfl⟩
    by_cases hxt : x = t'
    · have : h * u * h⁻¹ = t := by rw [← hxu, hxt]
      rw [this] at hub
      exact hub
    · have hxf : IsConj (x : G) (f : G) := C.subtype.map_isConj (hconj x hxT hx2 hxt)
      refine hub.trans ((hxu ▸ hxf).trans (isConj_comm.1 htf))
  refine ⟨hcentral, fun u v hu hv => (hall u hu).trans (isConj_comm.1 (hall v hv))⟩

end Local

end CFSG.Sporadic.Recognition.LyonsSims
