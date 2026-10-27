module

public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10SecDBasicZ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuL0_le_normalizer_L (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L ≤ Subgroup.normalizer (L : Set G) ∧
      fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  rw [SecA.fsuL0_eq_sup h37 h38 h ht htn]
  have hs := SecA.le_fsuM T L ht
  exact ⟨sup_le Subgroup.le_normalizer (SecA.conjugate_le_normalizer h.fsu.maximal.1 hs),
    sup_le (SecA.le_normalizer_conjugate h.fsu.maximal.1 hs) Subgroup.le_normalizer⟩

theorem fsuL0_le_normalizer_V12 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) ∧
      fsuL0 T L ≤ Subgroup.normalizer
        ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
  obtain ⟨h1, h2⟩ := fsuL0_le_normalizer_L h37 h38 h ht htn
  exact ⟨SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I) h1,
    SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I) h2⟩

theorem fsuL0_inf_centralizer_z_le (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥)
    {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    fsuL0 T L ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) ≤
      Subgroup.centralizer ((Subgroup.closure {v₁, v₂} : Subgroup G) : Set G) := by
  obtain ⟨ht, htn, hv1, -, hv2, -⟩ := hd
  obtain ⟨hN1, hN2⟩ := fsuL0_le_normalizer_V12 h37 h38 h ht htn
  have hV2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 ht).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I))
  obtain ⟨hcomm, -⟩ := h.three
  have hab : ∀ a ∈ fsuVM T L I, ∀ b ∈ fsuVM T L I, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h12 := V1_inf_V2 h37 h38 h hc ht htn
  intro l ⟨hlL0, hlz⟩
  set p := l * v₁ * l⁻¹ with hp
  set q := l * v₂ * l⁻¹ with hq
  have hp1 : p ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp (hN1 hlL0) v₁).mp hv1.1
  have hq2 : q ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    (Subgroup.mem_normalizer_iff.mp (hN2 hlL0) v₂).mp hv2.1
  have hpq : p * q = v₁ * v₂ := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hlz
    calc p * q = l * (v₁ * v₂) * l⁻¹ := by rw [hp, hq]; group
      _ = v₁ * v₂ := by rw [this]; group
  have hpV : p ∈ fsuVM T L I := V1_le_V hp1
  have hqV : q ∈ fsuVM T L I := hV2 hq2
  have hv1V : v₁ ∈ fsuVM T L I := V1_le_V hv1.1
  have hv2V : v₂ ∈ fsuVM T L I := hV2 hv2.1
  have hkey : p * v₁⁻¹ = v₂ * q⁻¹ := by
    have hpe : p = v₁ * (v₂ * q⁻¹) := by rw [← mul_assoc, ← hpq]; group
    have hc' := hab v₁ hv1V (v₂ * q⁻¹) ((fsuVM T L I).mul_mem hv2V ((fsuVM T L I).inv_mem hqV))
    rw [hpe, hc']
    group
  have hmem : p * v₁⁻¹ ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    ⟨(fsuUL T L I).mul_mem hp1 ((fsuUL T L I).inv_mem hv1.1),
      hkey ▸ Subgroup.mul_mem _ hv2.1 (Subgroup.inv_mem _ hq2)⟩
  rw [h12, Subgroup.mem_bot] at hmem
  have hpv : p = v₁ := mul_inv_eq_one.mp hmem
  have hqv : q = v₂ := by
    have : v₂ * q⁻¹ = 1 := hkey ▸ hmem
    exact (mul_inv_eq_one.mp this).symm
  have hpv' : l * v₁ * l⁻¹ = v₁ := hpv
  have hqv' : l * v₂ * l⁻¹ = v₂ := hqv
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · calc w * l = (l * w * l⁻¹) * l := by rw [hpv']
      _ = l * w := by group
  · calc w * l = (l * w * l⁻¹) * l := by rw [hqv']
      _ = l * w := by group

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {N S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hS : IsPGroup 2 S) {x : G} (hx : x ∈ N ⊔ S)
    (hxo : Odd (orderOf x)) : x ∈ N := by
  have hNS : N ⊔ S ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hSN
  set N' := N.subgroupOf (N ⊔ S) with hN'
  set S' := S.subgroupOf (N ⊔ S) with hS'
  have : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hNS
  have htop : N' ⊔ S' = ⊤ := by
    apply Subgroup.map_injective (N ⊔ S).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hS2 : IsPGroup 2 (S'.map (QuotientGroup.mk' N')) :=
    (hS.comap_of_injective _ (Subgroup.subtype_injective _)).map _
  have htop' : (⊤ : Subgroup (↥(N ⊔ S) ⧸ N')) ≤ S'.map (QuotientGroup.mk' N') := by
    rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N'), ← htop,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  obtain ⟨k, hk⟩ := hS2 ⟨QuotientGroup.mk' N' ⟨x, hx⟩, htop' (Subgroup.mem_top _)⟩
  have hk' : (QuotientGroup.mk' N' ⟨x, hx⟩) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hdvd1 : orderOf (QuotientGroup.mk' N' ⟨x, hx⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (QuotientGroup.mk' N' ⟨x, hx⟩) ∣ orderOf (⟨x, hx⟩ : ↥(N ⊔ S)) :=
    orderOf_map_dvd _ _
  rw [Subgroup.orderOf_mk] at hdvd2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
  have hodd := Odd.of_dvd_nat hxo hdvd2
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hj0, pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hj
  exact hj

omit [Finite G] in
theorem oTwoUpper_P_eq (hT : IsPGroup 2 T) {z : G} :
    oTwoUpper ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({z} : Set G)) = Xz T L z := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_)
    (oTwoUpper_mono (inf_le_inf_right _ le_sup_left))
  rintro x ⟨hx, hxo⟩
  exact mem_oTwoUpper_of_odd
    ⟨mem_of_odd_of_mem_sup (le_normalizer_conjClosure L T) hT hx.1 hxo, hx.2⟩ hxo

theorem not_case10_1_1Five (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) :
    ¬ Case10_1_1Five T L I := by
  rintro ⟨-, s, -, -, W, hWV1, -, hWs, hWW, ⟨_, hnat⟩, -⟩
  have hV1 := card_V1 h3 hc
  obtain ⟨D⟩ := hnat.toL3Coord
  have hW8 : Nat.card W = 8 := by
    have := D.card_U
    rwa [Subgroup.card_top, Subgroup.card_bot, mul_one] at this
  have hWs8 : Nat.card (CFSG.conjugate W s) = 8 := by
    rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective, hW8]
  have hWeq : W = fsuUL T L I := Subgroup.eq_of_le_of_card_ge hWV1 (by rw [hW8, hV1])
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hWs ▸ le_sup_right
  have hWseq : CFSG.conjugate W s = fsuUL T L I :=
    Subgroup.eq_of_le_of_card_ge hWsV1 (by rw [hWs8, hV1])
  rw [hWseq, hWeq, inf_idem] at hWW
  rw [hWW, Subgroup.card_bot] at hV1
  norm_num at hV1

theorem pCoreOf_Gz_ne_bot (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) :
    pCoreOf 2 (Subgroup.centralizer ({v₁ * v₂} : Set G)) ≠ ⊥ := by
  have hz1 := z_ne_one h37 h38 h hc hd
  have hzV : v₁ * v₂ ∈ fsuVM T L I := by
    obtain ⟨ht, -, hv1, -, hv2, -⟩ := hd
    exact (fsuVM T L I).mul_mem (V1_le_V hv1.1) (commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1)
  have hzp : IsPGroup 2 (Subgroup.zpowers (v₁ * v₂)) :=
    (SecA.isPGroup_fsuVM h).to_le (Subgroup.zpowers_le.mpr hzV)
  intro h0
  have := SecB.mem_pCoreOf_centralizer hzp
  rw [h0, Subgroup.mem_bot] at this
  exact hz1 this

end CFSG.Quasithin.Vol2.Ch10.SecD
