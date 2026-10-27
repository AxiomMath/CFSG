module

public import CFSG.Quasithin.EmptyFaithful.S14620D
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.C2Push CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

theorem nonempty_mulEquiv_sl_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL n 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  have hunits : ∀ c : Kˣ, c = 1 := fun c => by
    have h1 : Units.map ε.toMonoidHom c = 1 := Subsingleton.elim _ _
    exact (Units.map_injective ε.injective) (by simpa using h1)
  exact ⟨e.trans ((statedSLEquivProjectiveSL n K).trans
    ((slEquivProjectiveSL_two hunits n).symm.trans (slMulEquivOfRingEquiv ε n)))⟩


private theorem sl_center_trivial_of_card_two {n : ℕ} (hn : 3 ≤ n) :
    ∀ x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), (∀ y, y * x = x * y) → x = 1 := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two hK hn
  intro x hx
  have hxc : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Subgroup.mem_center_iff.mpr hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) with h | h
  · exact Subgroup.mem_bot.mp (h ▸ hxc)
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two hK hn
    have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := h ▸ trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

private theorem trivial_centre_of_mulEquiv' {Y : Type*} [Group Y] {L : Subgroup Y} {M : Type*} [Group M]
    (e : ↥L ≃* M) (hM : ∀ x : M, (∀ y, y * x = x * y) → x = 1) :
    ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1 := by
  intro x hx hc
  have h1 : e ⟨x, hx⟩ = 1 := by
    refine hM _ fun y => ?_
    have hy := hc (e.symm y : ↥L) (e.symm y).2
    have h2 : (e.symm y) * (⟨x, hx⟩ : ↥L) = (⟨x, hx⟩ : ↥L) * (e.symm y) := Subtype.ext hy
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  have : (⟨x, hx⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

section Lift

variable {G : Type} [Group G]

theorem mem_normalizer_preimageOTwoQuot {X : Subgroup G} {P : Subgroup (OTwoQuot X)} {s : G}
    (hs : s ∈ X) (h : (QuotientGroup.mk ⟨s, hs⟩ : OTwoQuot X) ∈
      Subgroup.normalizer (P : Set (OTwoQuot X))) :
    s ∈ Subgroup.normalizer (preimageOTwoQuot X P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  by_cases hx : x ∈ X
  · have hsx : s * x * s⁻¹ ∈ X := X.mul_mem (X.mul_mem hs hx) (X.inv_mem hs)
    rw [mem_preimageOTwoQuot_iff, mem_preimageOTwoQuot_iff]
    have e : (QuotientGroup.mk ⟨s * x * s⁻¹, hsx⟩ : OTwoQuot X) =
        QuotientGroup.mk ⟨s, hs⟩ * QuotientGroup.mk ⟨x, hx⟩ * (QuotientGroup.mk ⟨s, hs⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    constructor
    · rintro ⟨hx', hmem⟩
      exact ⟨hsx, e ▸ (Subgroup.mem_normalizer_iff.mp h _).mp hmem⟩
    · rintro ⟨hsx', hmem⟩
      exact ⟨hx, (Subgroup.mem_normalizer_iff.mp h _).mpr (e ▸ hmem)⟩
  · have hsx : s * x * s⁻¹ ∉ X := fun hh => hx (by
      have := X.mul_mem (X.mul_mem (X.inv_mem hs) hh) hs
      simpa [mul_assoc] using this)
    constructor
    · intro hmem
      exact absurd (preimageOTwoQuot_le X P hmem) hx
    · intro hmem
      exact absurd (preimageOTwoQuot_le X P hmem) hsx

end Lift

section Centralizer

variable {G : Type} [Group G] [Finite G]

theorem centralizer_imageOTwoQuot_trivial {K T : Subgroup G} (hsyl : IsSylowTwoOf T (K ⊔ T))
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKz : ∀ x ∈ imageOTwoQuot (K ⊔ T) K, (∀ y ∈ imageOTwoQuot (K ⊔ T) K, y * x = x * y) → x = 1) :
    ∀ y : OTwoQuot (K ⊔ T), (∀ k ∈ imageOTwoQuot (K ⊔ T) K, y * k = k * y) → y = 1 := by
  set X : Subgroup G := K ⊔ T with hXdef
  have hKX : K ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  set Kh : Subgroup (OTwoQuot X) := imageOTwoQuot X K with hKh
  set Th : Subgroup (OTwoQuot X) := imageOTwoQuot X T with hTh
  have hKhN : Kh.Normal := by
    refine ⟨fun u hu g => ?_⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
    have := mk_mem_normalizer_imageOTwoQuot_of_mem z.2 (hXK z.2)
    exact (Subgroup.mem_normalizer_iff.mp this u).mp hu
  have hTh2 : IsPGroup 2 ↥Th := isPGroup_imageOTwoQuot' hsyl.2.1
  set C : Subgroup (OTwoQuot X) := Subgroup.centralizer (Kh : Set (OTwoQuot X)) with hCdef
  have hmemC : ∀ c, c ∈ C ↔ ∀ k ∈ Kh, k * c = c * k := fun c => Subgroup.mem_centralizer_iff
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hmemC] at hc ⊢
    intro k hk
    have hk' : g⁻¹ * k * g ∈ Kh := by
      have := hKhN.conj_mem k hk g⁻¹
      simpa using this
    have h1 := hc _ hk'
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * k := by group
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (c : OTwoQuot X)
    have hzTK : (z : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, sup_comm]
      exact z.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T K hTK] at hzTK
    obtain ⟨t, ht, k, hk, hzt⟩ := Set.mem_mul.mp hzTK
    have htX : t ∈ X := hTX ht
    have hkX : k ∈ X := hKX hk
    have hct : (c : OTwoQuot X) =
        QuotientGroup.mk ⟨t, htX⟩ * QuotientGroup.mk ⟨k, hkX⟩ := by
      rw [← hz, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hzt.symm
    obtain ⟨b, hb⟩ := hTh2 ⟨QuotientGroup.mk ⟨t, htX⟩,
      mem_imageOTwoQuot_iff.mpr ⟨t, htX, ht, rfl⟩⟩
    refine ⟨b, ?_⟩
    have hπ : (QuotientGroup.mk' Kh : OTwoQuot X →* OTwoQuot X ⧸ Kh)
        ((c : OTwoQuot X) ^ 2 ^ b) = 1 := by
      rw [map_pow, hct, map_mul]
      have hk1 : (QuotientGroup.mk' Kh) (QuotientGroup.mk ⟨k, hkX⟩ : OTwoQuot X) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (mem_imageOTwoQuot_iff.mpr ⟨k, hkX, hk, rfl⟩)
      rw [hk1, mul_one, ← map_pow]
      have : (QuotientGroup.mk ⟨t, htX⟩ : OTwoQuot X) ^ 2 ^ b = 1 := by
        simpa using congrArg Subtype.val hb
      rw [this, map_one]
    have hmem : (c : OTwoQuot X) ^ 2 ^ b ∈ Kh := (QuotientGroup.eq_one_iff _).mp hπ
    have hcC : (c : OTwoQuot X) ^ 2 ^ b ∈ C := Subgroup.pow_mem C c.2 _
    have h1 : (c : OTwoQuot X) ^ 2 ^ b = 1 :=
      hKz _ hmem fun y hy => (hmemC _).mp hcC y hy
    exact Subtype.ext (by simpa using h1)
  have hCle : C ≤ CFSG.Open.pCore 2 (OTwoQuot X) := le_pCore 2 hCn hC2
  have hbot : CFSG.Open.pCore 2 (OTwoQuot X) = ⊥ :=
    (CFSG.pCore_eq_open (OTwoQuot X) 2).symm.trans (pCore_two_quot_eq_bot X)
  intro y hy
  have : y ∈ C := (hmemC y).mpr fun k hk => (hy k hk).symm
  exact Subgroup.mem_bot.mp (hbot ▸ hCle this)

end Centralizer

@[expose] def L45Core : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Kh T' : Subgroup Y), Kh.Normal →
    (IsPSL 4 2 1 ↥Kh ∨ IsPSL 5 2 1 ↥Kh) → (∀ x : Y, (∀ k ∈ Kh, x * k = k * x) → x = 1) →
    IsPGroup 2 ↥T' → ∃ P : Subgroup Y, P ≤ Kh ∧ T' ≤ Subgroup.normalizer (P : Set Y) ∧
      Group.IsSolvable ↥P ∧ 2 ≤ CFSG.Open.pRank 3 P

theorem input14620L45_of_core (hcore : L45Core) : Input14620L45 := by
  intro G _ _ K T hsyl hTK hL45
  set X : Subgroup G := K ⊔ T with hXdef
  have hKX : K ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hKnorm : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hsub : IsSubnormal K X := A3.subnormal_of_normal hKX hKnorm
  set Kh : Subgroup (OTwoQuot X) := imageOTwoQuot X K with hKh
  set Th : Subgroup (OTwoQuot X) := imageOTwoQuot X T with hTh
  have hKhN : Kh.Normal := by
    refine ⟨fun u hu g => ?_⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
    have := mk_mem_normalizer_imageOTwoQuot_of_mem z.2 (hXK z.2)
    exact (Subgroup.mem_normalizer_iff.mp this u).mp hu
  obtain ⟨eI⟩ := nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hsub
  let e' : KBar K ≃* ↥Kh := (kbarEquiv K).trans eI
  have hPSL : IsPSL 4 2 1 ↥Kh ∨ IsPSL 5 2 1 ↥Kh := by
    rcases hL45 with h | h
    · exact Or.inl (isPSL_congr e' h)
    · exact Or.inr (isPSL_congr e' h)
  have hKz : ∀ x ∈ Kh, (∀ y ∈ Kh, y * x = x * y) → x = 1 := by
    rcases hPSL with h | h
    · obtain ⟨e⟩ := nonempty_mulEquiv_sl_of_isPSL h
      exact trivial_centre_of_mulEquiv' e (sl_center_trivial_of_card_two (by norm_num))
    · obtain ⟨e⟩ := nonempty_mulEquiv_sl_of_isPSL h
      exact trivial_centre_of_mulEquiv' e (sl_center_trivial_of_card_two (by norm_num))
  have hC := centralizer_imageOTwoQuot_trivial hsyl hTK hKz
  have hTh2 : IsPGroup 2 ↥Th := isPGroup_imageOTwoQuot' hsyl.2.1
  obtain ⟨P', hPK, hTN, hPs, hPr⟩ := hcore (OTwoQuot X) Kh Th hKhN hPSL hC hTh2
  set P : Subgroup G := preimageOTwoQuot X P' ⊓ K with hPdef
  have hPX : P ≤ X := inf_le_right.trans hKX
  refine ⟨P, inf_le_right, ?_, ?_, ?_⟩
  · intro s hs
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨mem_normalizer_preimageOTwoQuot (hTX hs)
        (hTN (mem_imageOTwoQuot_iff.mpr ⟨s, hTX hs, hs, rfl⟩)), hTK hs⟩
  ·
    have hThs : Group.IsSolvable ↥Th := by
      have := hTh2.isNilpotent
      infer_instance
    have hY : Group.IsSolvable ↥(P' ⊔ Th) :=
      isSolvable_sup_of_le_normalizer_of_isSolvable hTN hPs hThs
    have hsolv : Group.IsSolvable ↥(preimageOTwoQuot X (P' ⊔ Th)) := isSolvable_preimageOTwoQuot hY
    have hle : P ⊔ T ≤ preimageOTwoQuot X (P' ⊔ Th) := by
      refine sup_le ?_ ?_
      · intro x hx
        obtain ⟨hxX, hmem⟩ := mem_preimageOTwoQuot_iff.mp hx.1
        exact mem_preimageOTwoQuot_iff.mpr ⟨hxX, (le_sup_left : P' ≤ P' ⊔ Th) hmem⟩
      · exact le_preimageOTwoQuot_of_imageOTwoQuot_le hTX le_sup_right
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hψP : ∀ x : ↥P, (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)) (Subgroup.inclusion hPX x) ∈ P' :=
      fun x => (mem_preimageOTwoQuot_iff.mp x.2.1).2
    let ψ : ↥P →* ↥P' :=
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)).comp (Subgroup.inclusion hPX)).codRestrict P' hψP
    have hsurj : Function.Surjective ψ := by
      rintro ⟨u, hu⟩
      obtain ⟨k, hkX, hkK, hku⟩ := mem_imageOTwoQuot_iff.mp (hPK hu)
      have hkP : k ∈ P := ⟨mem_preimageOTwoQuot_iff.mpr ⟨hkX, by rw [hku]; exact hu⟩, hkK⟩
      exact ⟨⟨k, hkP⟩, Subtype.ext hku⟩
    have hkerle : ψ.ker.map P.subtype ≤ pCoreOf 2 X := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : ψ x = 1 := hx
      have h2 : (QuotientGroup.mk (Subgroup.inclusion hPX x) : OTwoQuot X) = 1 :=
        congrArg Subtype.val h1
      exact (mk_eq_one_iff_mem_pCoreOf (Subgroup.inclusion hPX x)).mp h2
    have hker2 : IsPGroup 2 ↥ψ.ker :=
      ((pCoreOf_isPGroup 2 X).to_le hkerle).of_equiv
        (ψ.ker.equivMapOfInjective P.subtype P.subtype_injective).symm
    have hN3 : ¬ 3 ∣ Nat.card ↥ψ.ker := by
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hker2
      rw [hj]
      intro h3
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
    have : ψ.ker.Normal := MonoidHom.normal_ker ψ
    have h1 := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
      ψ.ker hN3
    have e : (↥P ⧸ ψ.ker) ≃* ↥P' := QuotientGroup.quotientKerEquivOfSurjective ψ hsurj
    have h2 : CFSG.pRank 3 (↥P ⧸ ψ.ker) = CFSG.pRank 3 ↥P' := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
    have h3 : CFSG.pRank 3 ↥P = CFSG.Open.pRank 3 P := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact pRank_top_subtype (p := 3) P
    have h4 : CFSG.pRank 3 ↥P' = CFSG.Open.pRank 3 P' := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact pRank_top_subtype (p := 3) P'
    rw [← h3, ← h1, h2, h4]
    exact hPr

end CFSG.Quasithin
