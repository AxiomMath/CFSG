module

public import CFSG.Quasithin.Vol2.Ch3zXLev
public import CFSG.Quasithin.Vol2.Ch3zCmp
public import CFSG.Quasithin.Vol2.Ch3y319

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ch3z

section Offender

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem chiefImg_eq_autOn {H L N K : Subgroup G} (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hKH : K ≤ H) :
    chiefImg hHL hHN K = autOn (secImg (Subgroup.normalizer (L : Set G)) L K) (chiefMod L N) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨secMk (Subgroup.normalizer (L : Set G)) L (Subgroup.inclusion hHL k),
      secMk_mem_normalizer_secImg (hHN k.2)⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (secMk_mem_secImg (A := Subgroup.normalizer (L : Set G))
      (B := L) (X := K) (x := Subgroup.inclusion hHL k) (Subgroup.mem_subgroupOf.mp hk))
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hkK, hky⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨(k : G), hKH hkK⟩, Subgroup.mem_subgroupOf.mpr hkK, ?_⟩
    show conjAct (chiefMod L N) _ = conjAct (chiefMod L N) y
    congr 1
    exact Subtype.ext hky

theorem card_le_autOn_fixV {K E B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hle : (centralizerMod K E B).relIndex E ≤ (centralizerMod K B E).relIndex B) :
    Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E) ≤
      Nat.card (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
          (secImg (Subgroup.normalizer (K : Set G)) K E)) *
        Nat.card (@fixV ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
          (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
            (secImg (Subgroup.normalizer (K : Set G)) K E))) := by
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  have c1 := card_autOn_secImg hBK hEK hBE
  have c2 := card_fixV_autOn_eq hE hn
  have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
  have hmul := Subgroup.relIndex_mul_card
    (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
      (secImg (Subgroup.normalizer (K : Set G)) K B :
        Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
    (secImg (Subgroup.normalizer (K : Set G)) K E)
  rw [inf_eq_left.mpr inf_le_left] at hmul
  rw [c1, c2]
  calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
      = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
          (secImg (Subgroup.normalizer (K : Set G)) K E) *
        Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
    _ ≤ (centralizerMod K B E).relIndex B *
        Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
      rw [c3]
      exact Nat.mul_le_mul_right _ hle

theorem relIndex_eq_of_count {A C N D : Subgroup G} (hCA : C ≤ A) (hDN : D ≤ N)
    (h : Nat.card A * Nat.card D = Nat.card C * Nat.card N) : D.relIndex N = C.relIndex A := by
  have e1 := Subgroup.relIndex_mul_card D N
  have e2 := Subgroup.relIndex_mul_card C A
  rw [inf_eq_left.mpr hDN] at e1
  rw [inf_eq_left.mpr hCA] at e2
  have hC : 0 < Nat.card C := Nat.card_pos
  have hD : 0 < Nat.card D := Nat.card_pos
  have h2 : (D.relIndex N) * (Nat.card C * Nat.card D) = (C.relIndex A) * (Nat.card C * Nat.card D) := by
    calc (D.relIndex N) * (Nat.card C * Nat.card D) = (D.relIndex N * Nat.card D) * Nat.card C := by ring
      _ = Nat.card N * Nat.card C := by rw [e1]
      _ = Nat.card C * Nat.card N := by ring
      _ = Nat.card A * Nat.card D := h.symm
      _ = (C.relIndex A * Nat.card C) * Nat.card D := by rw [e2]
      _ = (C.relIndex A) * (Nat.card C * Nat.card D) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hC hD) h2

end Offender

abbrev chiefCG {G : Type} [Group G] {L N : Subgroup G} (hE : IsElemAbelian 2 (chiefMod L N)) :
    CommGroup ↥(chiefMod L N) := commGroupOfElemAbelian hE

section Setting

variable {G : Type} [Group G] [Finite G]

structure Setting (H T M₂ U A : Subgroup G) : Prop where
  mp : MinParabolic H T M₂
  sqtk : IsSQTKSub H
  UT : U ≤ T
  Ue : IsElemAbelian 2 U
  AT : IsMaxElemAbelian T A
  An : ¬ A ≤ pCoreOf 2 H
  cnt : ∀ L N : Subgroup G, IsChiefStep H U L N → ¬ IsCentralStep H L N →
    cSecIn A L N = A ⊓ pCoreOf 2 H ∧
      Nat.card A * Nat.card (fixSecIn A L N) = Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) * Nat.card N

variable {H T M₂ U A L N : Subgroup G}

theorem Setting.UH (h : Setting H T M₂ U A) : U ≤ H := h.UT.trans h.mp.isSylow.1

theorem Setting.AH (h : Setting H T M₂ U A) : A ≤ H := h.AT.1.trans h.mp.isSylow.1

omit [Finite G] in
theorem Setting.hHL (hstep : IsChiefStep H U L N) : H ≤ Subgroup.normalizer (L : Set G) :=
  D14.le_normalizer_of_isNormalIn hstep.2.1

omit [Finite G] in
theorem Setting.hHN (hstep : IsChiefStep H U L N) : H ≤ Subgroup.normalizer (N : Set G) :=
  D14.le_normalizer_of_isNormalIn hstep.1

theorem Setting.hNL (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N) :
    N ≤ Subgroup.normalizer (L : Set G) :=
  ((hstep.1.1.trans h.UH)).trans (Setting.hHL hstep)

theorem Setting.hE (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N) :
    IsElemAbelian 2 (chiefMod L N) :=
  D15Proof.isElemAbelian_secImg_of_le (L := L) h.Ue hstep.1.1

theorem Setting.hnt (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) : ¬ ∀ b ∈ A, ∀ e ∈ N, b * e * b⁻¹ * e⁻¹ ∈ L := by
  have hAH : A ≤ H := h.AH
  have hAK : A ≤ Subgroup.normalizer (L : Set G) := hAH.trans (Setting.hHL hstep)
  obtain ⟨hc1, -⟩ := h.cnt L N hstep hnc
  have hcs : cSecIn A L N = centralizerMod L A N := cSecIn_eq_centralizerMod hAH hstep.2.1
  have hC : centralizerMod L A N = A ⊓ pCoreOf 2 H := hcs ▸ hc1
  intro hall
  have hCA : centralizerMod L A N = A :=
    le_antisymm (centralizerMod_le_left L A N) fun b hb => ⟨hb, hAK hb, hall b hb⟩
  rw [hCA] at hC
  exact h.An (hC ▸ inf_le_right)

theorem Setting.hle (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) :
    (centralizerMod L N A).relIndex N ≤ (centralizerMod L A N).relIndex A := by
  have hAH : A ≤ H := h.AH
  obtain ⟨hc1, hc2⟩ := h.cnt L N hstep hnc
  have hNH : N ≤ H := hstep.1.1.trans h.UH
  have hcs : cSecIn A L N = centralizerMod L A N := cSecIn_eq_centralizerMod hAH hstep.2.1
  have hfs : fixSecIn A L N = centralizerMod L N A := fixSecIn_eq_centralizerMod hNH hstep.2.1
  have hC : centralizerMod L A N = A ⊓ pCoreOf 2 H := hcs ▸ hc1
  refine (relIndex_eq_of_count (centralizerMod_le_left L A N) (centralizerMod_le_left L N A) ?_).le
  rw [hfs] at hc2
  rw [hC]
  exact hc2

theorem Setting.offender (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) :
    @IsElemAbelian2 ↥(chiefMod L N) (chiefCG (h.hE hstep))
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A) ∧
      chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A ≠ ⊥ ∧
      Nat.card ↥(chiefMod L N) ≤ Nat.card (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A) *
        Nat.card (@fixV ↥(chiefMod L N) (chiefCG (h.hE hstep))
          (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A)) := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hAH : A ≤ H := h.AH
  have hE := h.hE hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have hNL := h.hNL hstep
  have hAK : A ≤ Subgroup.normalizer (L : Set G) := hAH.trans hHL
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := hAH.trans hHN
  have hnt := h.hnt hstep hnc
  have hle := h.hle hstep hnc
  rw [chiefImg_eq_autOn hHL hHN hAH]
  have hBt : IsElemAbelian 2 (secImg (Subgroup.normalizer (L : Set G)) L A) :=
    isElemAbelian_secImg h.AT.2.1
  have hn := secImg_le_normalizer_secImg (K := L) (E := N) (X := A) hAN
  refine ⟨isElemAbelian2_autOn hE hBt hn, ?_, card_le_autOn_fixV hE hNL hAK hAN hle⟩
  refine autOn_ne_bot_of_not_le_centralizer hn ?_
  intro hle'
  apply hnt
  intro b hb e he
  have := Subgroup.mem_centralizer_iff.mp
    (hle' (secMk_mem_secImg (x := ⟨b, hAK hb⟩) hb))
    (secMk (Subgroup.normalizer (L : Set G)) L ⟨e, hNL he⟩)
    (secMk_mem_secImg (x := ⟨e, hNL he⟩) he)
  exact commutator_mem_of_secMk_commute (x := ⟨b, hAK hb⟩) (y := ⟨e, hNL he⟩) this.symm

theorem chiefAut_pCoreOf_top_eq_bot (hUH : U ≤ H) (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (chiefMod L N)) : pCoreOf 2 (⊤ : Subgroup ↥(chiefAut H L N)) = ⊥ := by
  set X := chiefAut H L N with hX
  set Q : Subgroup ↥X := pCoreOf 2 (⊤ : Subgroup ↥X) with hQdef
  have hQn : Q.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥X)))
  have hnorm : ((Q.map X.subtype).subgroupOf X).Normal := by
    have e : (Q.map X.subtype).subgroupOf X = Q :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
    rw [e]
    exact hQn
  have hQ : Q.map X.subtype = (⊥ : Subgroup (MulAut ↥(chiefMod L N))) :=
    D15Proof.normal_two_eq_bot hUH hstep hE (Q.map X.subtype) (Subgroup.map_subtype_le Q) hnorm
      ((pCoreOf_isPGroup 2 (⊤ : Subgroup ↥X)).map X.subtype)
  exact (Subgroup.map_eq_bot_iff_of_injective Q X.subtype_injective).mp hQ

omit [Finite G] in
theorem chiefMod_sq (hE : IsElemAbelian 2 (chiefMod L N)) (v : ↥(chiefMod L N)) : v ^ 2 = 1 :=
  Subtype.ext (hE.2 v v.2)

omit [Finite G] in
theorem exists_ne_one_chiefMod (hstep : IsChiefStep H U L N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    ∃ v : ↥(chiefMod L N), v ≠ 1 := by
  obtain ⟨n, hnN, hnL⟩ := IsConcreteLE.exists_of_lt hstep.2.2.1
  refine ⟨chiefIota hNL ⟨n, hnN⟩, fun h1 => hnL ?_⟩
  exact (chiefIota_eq_one_iff hNL ⟨n, hnN⟩).1 h1

theorem Setting.blkCtx (hB69 : B69Struct) (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) :
    ∃ 𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N))),
      @BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗 := by
  have hE := h.hE hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have hFF : IsFFModule (chiefAut H L N) :=
    ffModule_chiefAut h.UH hstep hE h.AH h.AT.2.1 (h.hnt hstep hnc) (h.hle hstep hnc)
  exact BlkCtx.of_struct hB69 (chiefMod_sq hE) (chiefAut_sqtk h.sqtk hstep)
    (chiefAut_minParabolic h.mp h.UT hstep hnc) (chiefAut_pCoreOf_eq_bot hstep h.UH hE) hFF
    (fun W hW => chiefMod_irr hstep h.UH W hW) (exists_ne_one_chiefMod hstep (h.hNL hstep))

theorem Setting.rank (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N) :
    IsRankTwoQuotient ↥(chiefAut H L N) := by
  obtain ⟨H₀, g, fin, hsq, -, f, hf⟩ := chiefAut_sqtk h.sqtk hstep
  exact ⟨H₀, g, fin, hsq, f, hf⟩

theorem Setting.noStrong (hB1 : B69One) (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) :
    ¬ @IsStrongFFModule ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N) := by
  have hE := h.hE hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  exact hB1 _ (chiefMod_sq hE) (chiefAut H L N) _ _ (chiefAut_sqtk h.sqtk hstep)
    (chiefAut_minParabolic_top h.mp h.UT hstep hnc) (chiefAut_pCoreOf_top_eq_bot h.UH hstep hE)

end Setting

section Good

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

omit [Finite G] in
theorem chiefImg_le_chiefAut (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (K : Subgroup G) :
    chiefImg hHL hHN K ≤ chiefAut H L N := by
  rintro _ ⟨x, -, rfl⟩
  exact chiefPsi_mem hHL hHN x

theorem exists_odd_lift (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) {d : MulAut ↥(chiefMod L N)}
    (hd : d ∈ chiefImg hHL hHN M₂) (hodd : Odd (orderOf d)) :
    ∃ g : ↥H, (g : G) ∈ M₂ ∧ Odd (orderOf (g : G)) ∧ chiefPsi hHL hHN g = d := by
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨n, hn, hψ⟩ := exists_odd_pow_eq (chiefPsi hHL hHN) (isOfFinOrder_of_finite x) hodd
  refine ⟨x ^ n, ?_, ?_, hψ⟩
  · have := Subgroup.mem_subgroupOf.mp hx
    exact M₂.pow_mem this n
  · rw [Subgroup.orderOf_coe]
    exact hn

omit [Finite G] in
theorem oTwoUpper_le_ker (χ : ↥H →* ℤˣ) : oTwoUpper H ≤ (MonoidHom.ker χ).map H.subtype := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxH, hodd⟩
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  show χ ⟨x, hxH⟩ = 1
  have h1 : orderOf (χ ⟨x, hxH⟩) ∣ orderOf (⟨x, hxH⟩ : ↥H) := orderOf_map_dvd χ _
  have h2 : Odd (orderOf (⟨x, hxH⟩ : ↥H)) := by
    rw [← Subgroup.orderOf_coe]
    exact hodd
  have h3 : orderOf (χ ⟨x, hxH⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_pow_two _)
  have hodd' : Odd (orderOf (χ ⟨x, hxH⟩)) := h2.of_dvd_nat h1
  have h4 : orderOf (χ ⟨x, hxH⟩) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  exact orderOf_eq_one_iff.mp h4

omit [Finite G] in
theorem exists_factor (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (χ₀ : ↥H →* ℤˣ) (hker : ∀ g : ↥H, (g : G) ∈ centralizerMod L H N → χ₀ g = 1) :
    ∃ χ : ↥(chiefAut H L N) →* ℤˣ, ∀ g : ↥H, χ (chiefHom hHL hHN g) = χ₀ g :=
  ⟨(chiefHom hHL hHN).liftOfSurjective (chiefHom_surjective hHL hHN)
    ⟨χ₀, fun g hg => hker g ((chiefHom_eq_one_iff hHL hHN hNL g).1 hg)⟩,
    fun g => by simp⟩

omit [Finite G] in
theorem chiefPsi_fix (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    {z : G} (hzN : z ∈ N) (g : ↥H) (hg : (g : G) * z * (g : G)⁻¹ * z⁻¹ ∈ L) :
    chiefPsi hHL hHN g (chiefIota hNL ⟨z, hzN⟩) = chiefIota hNL ⟨z, hzN⟩ := by
  have hgn : (g : G) * z * (g : G)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN g.2) z).mp hzN
  rw [chiefPsi_iota hHL hHN hNL g ⟨z, hzN⟩ hgn]
  have e : (⟨(g : G) * z * (g : G)⁻¹, hgn⟩ : ↥N) =
      ⟨(g : G) * z * (g : G)⁻¹ * z⁻¹, N.mul_mem hgn (N.inv_mem hzN)⟩ * ⟨z, hzN⟩ := by
    apply Subtype.ext
    simp
  rw [e, map_mul]
  have h1 : chiefIota hNL ⟨(g : G) * z * (g : G)⁻¹ * z⁻¹, N.mul_mem hgn (N.inv_mem hzN)⟩ = 1 :=
    (chiefIota_eq_one_iff hNL _).2 hg
  rw [h1, one_mul]

theorem Setting.good (hB69 : B69Struct) (hB1 : B69One) (h : Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) {z : G} (hzN : z ∈ N) (hzL : z ∉ L)
    (hT : ∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ L)
    (hM : ∀ d ∈ M₂, Odd (orderOf d) → d * z * d⁻¹ * z⁻¹ ∈ L) :
    ∃ χ₀ : ↥H →* ℤˣ, (∀ g : ↥H, (g : G) ∈ centralizerMod L H N → χ₀ g = 1) ∧
      ∃ a ∈ A, ∃ ha : a ∈ H, χ₀ ⟨a, ha⟩ = -1 := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  obtain ⟨𝓗, hctx⟩ := h.blkCtx hB69 hstep hnc
  have hstrong := h.noStrong hB1 hstep hnc
  obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
  set v : ↥(chiefMod L N) := chiefIota hNL ⟨z, hzN⟩ with hvdef
  have hv : v ≠ 1 := fun h1 => hzL ((chiefIota_eq_one_iff hNL ⟨z, hzN⟩).1 h1)
  have hvT : ∀ s ∈ chiefImg hHL hHN T, s v = v := by
    rintro _ ⟨x, hx, rfl⟩
    exact chiefPsi_fix hHL hHN hNL hzN x (hT _ (Subgroup.mem_subgroupOf.mp hx))
  have hvM : ∀ d ∈ chiefImg hHL hHN M₂, Odd (orderOf d) → d v = v := by
    intro d hd hodd
    obtain ⟨g, hgM, hgodd, rfl⟩ := exists_odd_lift hHL hHN hd hodd
    exact chiefPsi_fix hHL hHN hNL hzN g (hM _ hgM hgodd)
  have hsym := hctx.symBlk_of_fixed hv hvT hvM
  have hAX : chiefImg hHL hHN A ≤ chiefAut H L N := chiefImg_le_chiefAut hHL hHN A
  have hshape := hctx.shape_wit (h.rank hstep) hsym hstrong hAX hAe hA1 hoff
  have hhom : ∃ χ : ↥(chiefAut H L N) →* ℤˣ, ∃ a ∈ chiefImg hHL hHN A,
      ∃ ha : a ∈ chiefAut H L N, χ ⟨a, ha⟩ = -1 := by
    rcases hshape with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact hm.exists_hom
    · exact hm.exists_hom
  obtain ⟨χ, a', ha'A, ha'X, hχ⟩ := hhom
  obtain ⟨x, hxA, hxa⟩ := ha'A
  refine ⟨χ.comp (chiefHom hHL hHN), fun g hg => ?_, x.1, Subgroup.mem_subgroupOf.mp hxA, x.2, ?_⟩
  · show χ (chiefHom hHL hHN g) = 1
    rw [(chiefHom_eq_one_iff hHL hHN hNL g).2 hg, map_one]
  · show χ (chiefHom hHL hHN x) = -1
    have : chiefHom hHL hHN x = ⟨a', ha'X⟩ := Subtype.ext hxa
    rw [this]
    exact hχ

theorem Setting.symBlk_all (hB1 : B69One) (h : Setting H T M₂ U A) {L₀ N₀ : Subgroup G}
    (hstep₀ : IsChiefStep H U L₀ N₀) (hnc₀ : ¬ IsCentralStep H L₀ N₀)
    {χ₀ : ↥H →* ℤˣ} (hχC : ∀ g : ↥H, (g : G) ∈ centralizerMod L₀ H N₀ → χ₀ g = 1)
    {a : G} (haA : a ∈ A) (haH : a ∈ H) (hχa : χ₀ ⟨a, haH⟩ = -1)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗) :
    ∀ H' ∈ 𝓗, ∃ m, @SymBlk ↥(chiefMod L N) (chiefCG (h.hE hstep))
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) H' m := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  intro H' hH'
  rcases hctx.symBlk_or_bad hH' with hs | ⟨e, he, hN, -⟩
  · exact hs
  · exfalso
    have hker : (twoResidual H ⊔ centralizerMod L₀ H N₀ : Subgroup G) ≤
        (MonoidHom.ker χ₀).map H.subtype := by
      refine sup_le ?_ ?_
      · rw [F6.twoResidual_eq_oTwoUpper]
        exact oTwoUpper_le_ker χ₀
      · intro g hg
        exact ⟨⟨g, hg.1⟩, hχC ⟨g, hg.1⟩ hg, rfl⟩
    have hcmp₀ := twoResidual_sup_centralizerMod_eq h.mp h.UT hstep₀ hnc₀ (h.hE hstep₀)
    have hcmp := twoResidual_sup_centralizerMod_eq h.mp h.UT hstep hnc hE
    have hC : centralizerMod L H N ≤ (MonoidHom.ker χ₀).map H.subtype := by
      calc centralizerMod L H N ≤ twoResidual H ⊔ centralizerMod L H N := le_sup_right
        _ = twoResidual H ⊔ kerIn M₂ H := hcmp
        _ = twoResidual H ⊔ centralizerMod L₀ H N₀ := hcmp₀.symm
        _ ≤ _ := hker
    obtain ⟨χ, hχ⟩ := exists_factor hHL hHN hNL χ₀ (fun g hg => by
      obtain ⟨y, hy, hyg⟩ := hC hg
      have : y = g := Subtype.ext hyg
      rw [← this]
      exact hy)
    have hstrong := h.noStrong hB1 hstep hnc
    obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
    have hAJ : chiefImg hHL hHN A ≤ ffJ (chiefAut H L N) :=
      le_ffJ_of_offender hstrong (chiefImg_le_chiefAut hHL hHN A) hAe hA1 hoff
    have hmemA : chiefPsi hHL hHN ⟨a, haH⟩ ∈ chiefImg hHL hHN A :=
      ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    have h1 := hctx.kills_of_bad hH' he hN χ _ (hAJ hmemA) (chiefPsi_mem hHL hHN ⟨a, haH⟩)
    have h2 : χ (chiefHom hHL hHN ⟨a, haH⟩) = -1 := by
      rw [hχ]
      exact hχa
    have h3 : (1 : ℤˣ) = -1 := h1.symm.trans h2
    exact absurd h3 (by decide)

end Good

end Ch3z

end CFSG.Quasithin
