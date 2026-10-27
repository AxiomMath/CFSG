module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112A5
public import CFSG.Quasithin.EmptyFaithful.SBc5Three
public import CFSG.Quasithin.EmptyFaithful.T1515eD
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

section A318

variable {G : Type} [Group G] [Finite G]

theorem A318Exclusion.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : A318Exclusion Y) : A318Exclusion X := by
  have := h.simple
  refine ⟨e.isSimpleGroup, ?_, fun Z _ s p k hp hk hZ hmod f hf => ?_⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact h.rank
  · exact h.noImage Z s p k hp hk hZ hmod (e.toMonoidHom.comp f) (e.surjective.comp hf)

theorem a318Exclusion_of_a7j2m23
    {X : Type} [Group X] [Finite X]
    (h : IsAlt 7 X ∨ IsSporadic .J2 X ∨ IsSporadic .M23 X) : A318Exclusion X := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := (h : Nonempty (X ≃* alternatingGroup (Fin 7)))
    exact A318Exclusion.of_mulEquiv e a318Exclusion_alt7
  · exact a318Exclusion_j2 h
  · exact a318Exclusion_m23 h

omit [Finite G] in
theorem oPrimeResidualOf_three_eq (X : Subgroup G) :
    oPrimeResidualOf 3 X = oThreePrimeResidual X := by
  unfold oPrimeResidualOf oThreePrimeResidual
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    exact ⟨hx, k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
  · rintro ⟨hx, k, hk⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨hx, j, hj⟩

theorem exists_starImage_surj_o2q {X L : Subgroup G} (hLX : L ≤ X) (hs : IsSimpleGroup (O2Q L))
    (h3 : 3 ∣ Nat.card (O2Q L)) :
    ∃ ρ : ↥(starImage 3 (L.subgroupOf X)) →* O2Q L,
      Function.Surjective ρ ∧ ∀ y, ρ y = 1 → ¬ 3 ∣ orderOf y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e₀ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let ψ : ↥(L.subgroupOf X) →* ↥(starImage 3 (L.subgroupOf X)) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)).subgroupMap (L.subgroupOf X)
  have hψs : Function.Surjective ψ := MonoidHom.subgroupMap_surjective _ _
  let φ : ↥(L.subgroupOf X) →* O2Q L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp e₀.toMonoidHom
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp e₀.surjective
  let N₃ : Subgroup G := (CFSG.pPrimeCore 3 ↥X).map X.subtype
  let W : Subgroup ↥L := (N₃ ⊓ L).subgroupOf L
  have hWn : W.Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun w l hw hl => ⟨?_, ?_⟩
    · obtain ⟨n, hn, hnw⟩ := hw.1
      refine ⟨⟨l, hLX hl⟩ * n * ⟨l, hLX hl⟩⁻¹, ?_, ?_⟩
      · exact (CFSG.pPrimeCore_normal (p := 3) (G := ↥X)).conj_mem n hn _
      · subst hnw
        simp
    · exact L.mul_mem (L.mul_mem hl hw.2) (L.inv_mem hl)
  have hWcop : Nat.Coprime (Nat.card W) 3 := by
    have h1 : Nat.card W = Nat.card ↥(N₃ ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h2 : Nat.card ↥(N₃ ⊓ L) ∣ Nat.card N₃ := Subgroup.card_dvd_of_le inf_le_left
    have h3' : Nat.card N₃ = Nat.card (CFSG.pPrimeCore 3 ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    have h4 : Nat.Coprime (Nat.card (CFSG.pPrimeCore 3 ↥X)) 3 :=
      CFSG.pPrimeCore_coprime_card.symm
    rw [h1]
    exact Nat.Coprime.coprime_dvd_left (h3' ▸ h2) h4
  have hWle : W ≤ CFSG.pCore 2 ↥L := by
    have hIn : (W.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
      hWn.map _ (QuotientGroup.mk'_surjective _)
    rcases hs.eq_bot_or_eq_top_of_normal (W.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with
      hb | ht
    · intro w hw
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) w ∈
          W.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := ⟨w, hw, rfl⟩
      rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    · exfalso
      have h1 : Nat.card ↥(W.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ∣ Nat.card W :=
        Subgroup.card_map_dvd (H := W) (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      rw [ht, Subgroup.card_top] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hWcop.symm (h3.trans h1)
  have hle : ψ.ker ≤ φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have hy3 : (y : ↥X) ∈ CFSG.pPrimeCore 3 ↥X :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hy)
    have hyW : e₀ y ∈ W := ⟨⟨(y : ↥X), hy3, rfl⟩, y.2⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L) (e₀ y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hWle hyW
  let ρ : ↥(starImage 3 (L.subgroupOf X)) →* O2Q L :=
    (QuotientGroup.lift ψ.ker φ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.toMonoidHom
  have hρψ : ∀ x, ρ (ψ x) = φ x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm (ψ x) =
        (x : ↥(L.subgroupOf X) ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift ψ.ker φ hle
      ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm (ψ x)) = φ x
    rw [h1]
    rfl
  refine ⟨ρ, fun z => ?_, fun y hy h3y => ?_⟩
  · obtain ⟨x, rfl⟩ := hφs z
    exact ⟨ψ x, hρψ x⟩
  · obtain ⟨x, rfl⟩ := hψs y
    rw [hρψ] at hy
    have hx2 : e₀ x ∈ CFSG.pCore 2 ↥L := by
      have hy' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (e₀ x) = 1 := hy
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hx2⟩
    have hxa : x ^ 2 ^ a = 1 := by
      apply e₀.injective
      rw [map_pow, map_one]
      exact congrArg Subtype.val ha
    have hpow : (ψ x) ^ 2 ^ a = 1 := by rw [← map_pow, hxa, map_one]
    have h32 : 3 ∣ 2 ^ a := h3y.trans (orderOf_dvd_of_pow_eq_one hpow)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    omega

omit [Finite G] in
theorem not_a318Case2_of_surj {X : Type} [Group X] [Finite X] {S : Subgroup G}
    (hS : A318Exclusion X) (ρ : ↥S →* X) (hρ : Function.Surjective ρ) : ¬ A318Case2 S := by
  rintro ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩
  subst hq
  exact hS.noImage _ s r k hrp hk1 hPSL hmod ρ hρ

theorem not_a318Case3Group_of_surj {X : Type} [Group X] [Finite X] {S : Subgroup G}
    (hS : A318Exclusion X) (ρ : ↥S →* X) (hρ : Function.Surjective ρ)
    (hker : ∀ y, ρ y = 1 → ¬ 3 ∣ orderOf y) : ¬ A318Case3Group ↥S := by
  intro h3
  obtain ⟨z, hzcen, hz⟩ := exists_central_order_three_of_a318Case3Group1515e h3
  have hzc : ρ z ∈ Subgroup.center X := Subgroup.map_center_le_center hρ ⟨z, hzcen, rfl⟩
  rw [hS.center_eq_bot, Subgroup.mem_bot] at hzc
  exact hker z hzc (by rw [hz])

end A318

section Elem

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime_5113 {H : Subgroup G} {x : G} {a b : ℕ} (ha : x ^ a ∈ H)
    (hb : x ^ b ∈ H) (hab : Nat.Coprime a b) : x ∈ H := by
  have h1 : ((Nat.gcd a b : ℕ) : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h1
  have e : x = (x ^ a) ^ Nat.gcdA a b * (x ^ b) ^ Nat.gcdB a b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h1, zpow_one]
  rw [e]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

theorem exists_conj_eq_of_card_three {U V P : Subgroup G} (hU : Nat.card U = 3)
    (hV : Nat.card V = 3) (hP : IsPGroup 2 P) (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hVY : V ≤ U ⊔ P) : ∃ p ∈ P, V = U.map (MulAut.conj p).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := U ⊔ P with hY
  have hUP1 : P ⊓ U = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
    rw [hm, hU]
    exact Nat.Coprime.pow_left m (by norm_num)
  have hcardY : Nat.card Y = 3 * Nat.card P := by
    have h1 : P.relIndex (U ⊔ P) = P.relIndex U := A4.relIndex_sup_eq_of_le_normalizer' hUP
    have h2 := Subgroup.relIndex_mul_card P U
    rw [hUP1, Subgroup.card_bot, mul_one, hU] at h2
    have h3 := Subgroup.relIndex_mul_card P (U ⊔ P)
    rw [inf_eq_left.mpr le_sup_right, h1, h2] at h3
    exact h3.symm
  have hidx : ∀ W : Subgroup G, W ≤ Y → Nat.card W = 3 → ¬ 3 ∣ (W.subgroupOf Y).index := by
    intro W hWY hW h3
    have h1 : Nat.card (W.subgroupOf Y) * (W.subgroupOf Y).index = Nat.card Y :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (W.subgroupOf Y) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv).trans hW
    rw [h2, hcardY] at h1
    have h4 : (W.subgroupOf Y).index = Nat.card P := by omega
    rw [h4] at h3
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
    rw [hm] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have h3p : ∀ W : Subgroup G, W ≤ Y → Nat.card W = 3 → IsPGroup 3 (W.subgroupOf Y) := by
    intro W hWY hW
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv).trans hW
  have hUY : U ≤ Y := le_sup_left
  let S₁ : Sylow 3 ↥Y := (h3p U hUY hU).toSylow (hidx U hUY hU)
  let S₂ : Sylow 3 ↥Y := (h3p V hVY hV).toSylow (hidx V hVY hV)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y S₁ S₂
  have hS₁ : (S₁ : Subgroup ↥Y) = U.subgroupOf Y := IsPGroup.toSylow_coe _ _
  have hS₂ : (S₂ : Subgroup ↥Y) = V.subgroupOf Y := IsPGroup.toSylow_coe _ _
  have hmem : ∀ x : ↥Y, x ∈ V.subgroupOf Y ↔ ∃ y ∈ U.subgroupOf Y, g * y * g⁻¹ = x := by
    intro x
    rw [← hS₂, ← hg, Sylow.coe_subgroup_smul, hS₁, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hgY : (g : G) ∈ P ⊔ U := by
    rw [sup_comm]
    exact g.2
  obtain ⟨p, hp, u, hu, hgpu⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hUP).mp hgY
  refine ⟨p, hp, ?_⟩
  have hUu : U.map (MulAut.conj u).toMonoidHom = U :=
    A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hu)
  have hconj : U.map (MulAut.conj (g : G)).toMonoidHom = U.map (MulAut.conj p).toMonoidHom := by
    have e1 : (MulAut.conj (g : G)).toMonoidHom =
        (MulAut.conj p).toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
      ext x
      simp [hgpu, MulAut.conj_apply, mul_assoc]
    rw [e1, ← Subgroup.map_map, hUu]
  rw [← hconj]
  ext x
  constructor
  · intro hx
    have hxY : x ∈ Y := hVY hx
    obtain ⟨y, hy, hyx⟩ := (hmem ⟨x, hxY⟩).mp hx
    refine ⟨(y : G), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this
  · rintro ⟨y, hy, rfl⟩
    have hyY : y ∈ Y := hUY hy
    have h1 := (hmem ⟨(g : G) * y * (g : G)⁻¹, Y.mul_mem (Y.mul_mem g.2 hyY) (Y.inv_mem g.2)⟩).mpr
      ⟨⟨y, hyY⟩, hy, rfl⟩
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa [MulAut.conj_apply] using h2

end Elem

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem hat_eq_oThreePrimeResidual (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hS : A318Exclusion (O2Q Kh₁)) :
    Kh₁ = oThreePrimeResidual X := by
  have h := m.hyp.toHyp5_0_1
  have hKhc : Kh₁ ∈ cComp X := m.hat.1
  have hKhX : Kh₁ ≤ X := le_of_mem_cComp hKhc
  have hH : SQTKGroup ↥X := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian m.inH.2
  have : IsSimpleGroup (O2Q Kh₁) := hS.simple
  have : Group.IsPerfect ↥Kh₁ := Subgroup.isPerfect_iff.mpr hKhc.2.1
  have hQ : CFSG.IsQuasisimple (O2Q Kh₁) := isQuasisimple_o2q_of_simple
  have hr : 2 ≤ CFSG.Open.pRank 3 Kh₁ := by
    rw [R3c.pRank_three_eq_pCore_quotient Kh₁]
    exact hS.rank
  obtain ⟨ρ, hρ, hker⟩ := exists_starImage_surj_o2q hKhX hS.simple hS.three_dvd_card
  rw [← oPrimeResidualOf_three_eq]
  exact SBc5.eq_oPrimeResidualOf_of_a318 hF h36 h38 hH hKhc hQ hr
    (not_a318Case2_of_surj hS ρ hρ) (not_a318Case3Group_of_surj hS ρ hρ hker)

theorem type513_of_data
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hcl : conjClosure Kh₁ T = Kh₁)
    (hnot : ¬ modO2Image X (D ⊓ X) ≤
      Subgroup.normalizer ((modO2Image X (oTwoUpper H) : Subgroup (O2Q X)) : Set (O2Q X)))
    (hRQ : modO2Image X (oTwoUpper H) ≤ modO2Image X Kh₁)
    (hty : IsAlt 7 ↥(modO2Image X Kh₁) ∨ IsSporadic .J2 ↥(modO2Image X Kh₁) ∨
      IsSporadic .M23 ↥(modO2Image X Kh₁))
    (hexp : ∀ d ∈ modO2Image X (D ⊓ X),
      d ^ 3 ∈ Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)))
    (htb : ∃ t ∈ modO2Image X T ⊓ modO2Image X Kh₁, ∀ d ∈ modO2Image X (D ⊓ X),
      t * d * t⁻¹ * d ∈ Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) :
        Set (O2Q X))) :
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  rw [hcl]
  have hKhc : Kh₁ ∈ cComp X := m.hat.1
  have hKhX : Kh₁ ≤ X := le_of_mem_cComp hKhc
  have hHX : H ≤ X := m.inH.1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hTXs
  have hKX : oTwoUpper H ≤ X := (oTwoUpper_le H).trans hHX
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have hD := m.nota.2.1
  have hDcyc : IsCyclic ↥D := (h.isCyclic_card_of_isHall l2TorusFact hD).1
  have hDodd : Odd (Nat.card ↥D) := hD.2.1
  have hS : A318Exclusion ↥(modO2Image X Kh₁) := a318Exclusion_of_a7j2m23 hty
  obtain ⟨eH⟩ := modO2_mulEquiv hKhc
  have hSK : A318Exclusion (O2Q Kh₁) := A318Exclusion.of_mulEquiv eH hS
  have hZ : Subgroup.center ↥(modO2Image X Kh₁) = ⊥ := hS.center_eq_bot
  have hQC : ∀ q ∈ modO2Image X Kh₁,
      q ∈ Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)) → q = 1 := by
    intro q hq hqc
    have hmem : (⟨q, hq⟩ : ↥(modO2Image X Kh₁)) ∈ Subgroup.center ↥(modO2Image X Kh₁) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hqc y y.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hD2 : ∀ d ∈ D, d ∈ pCoreOf 2 X → d = 1 := by
    intro d hdD hd2
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 X) ⟨d, hd2⟩
    have hda : d ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hdvd2 : orderOf d ∣ Nat.card D := by
      have := orderOf_dvd_natCard (⟨d, hdD⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at this
    have hodd : Odd (orderOf d) := Odd.of_dvd_nat hDodd hdvd2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hda)
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exfalso
      rw [hj] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (by simp [Nat.even_pow])
  have hπ2 : ∀ (x : G) (hx : x ∈ X), QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ = 1 →
      x ∈ pCoreOf 2 X := by
    intro x hx h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
    exact ⟨_, h1, rfl⟩
  have hDb : ∀ (d : G) (hd : d ∈ D ⊓ X),
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hd.2⟩ ∈ modO2Image X (D ⊓ X) :=
    fun d hd => ⟨⟨d, hd.2⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have hQb : ∀ (x : G) (hx : x ∈ Kh₁),
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hKhX hx⟩ ∈ modO2Image X Kh₁ :=
    fun x hx => ⟨⟨x, hKhX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hKh3 : Kh₁ = oThreePrimeResidual X := m.hat_eq_oThreePrimeResidual hF h36 h38 hSK
  have h3el : ∀ d ∈ X, (∃ k : ℕ, d ^ 3 ^ k = 1) → d ∈ Kh₁ := by
    intro d hd hk
    rw [hKh3]
    exact Subgroup.subset_closure ⟨hd, hk⟩
  have hcent : ∀ (d : G) (hd : d ∈ D ⊓ X),
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hd.2⟩ ∈
        Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)) →
      d ∈ Subgroup.normalizer (oTwoUpper H : Set G) := by
    intro d hd hc
    refine mem_normalizer_of_modO2Image hKX hKperf (hOT.trans hTK) hd.2 ?_
    exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRQ)).trans
      (Subgroup.centralizer_le_normalizer _) hc
  set D₃ := D ⊓ Kh₁ with hD₃def
  have hD₃X : ∀ d ∈ D₃, d ∈ D ⊓ X := fun d hd => ⟨hd.1, hKhX hd.2⟩
  have hexp3 : ∀ d ∈ D₃, d ^ 3 = 1 := by
    intro d hd
    have h1 := hexp _ (hDb d (hD₃X d hd))
    have hd3X : d ^ 3 ∈ X := X.pow_mem (hKhX hd.2) 3
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d ^ 3, hd3X⟩ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hKhX hd.2⟩) ^ 3 := by
      rw [← map_pow]
      rfl
    have h3 := hQC _ (hQb (d ^ 3) (Kh₁.pow_mem hd.2 3)) (h2 ▸ h1)
    exact hD2 _ (D.pow_mem hd.1 3) (hπ2 _ hd3X h3)
  have hD₃cyc : IsCyclic ↥D₃ :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left : D₃ ≤ D)).toMonoidHom
      (MulEquiv.surjective _)
  have hcard_dvd : Nat.card D₃ ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hexp3 x.1 x.2)
  have hparts : ∀ d ∈ D ⊓ X, ∃ s r : ℕ, Nat.Coprime s r ∧ Nat.Coprime 3 r ∧ d ^ r ∈ D₃ ∧
      d ^ (s * r) = 1 := by
    intro d hd
    have ho : orderOf d ≠ 0 := (isOfFinOrder_of_finite d).orderOf_pos.ne'
    refine ⟨3 ^ (orderOf d).factorization 3, orderOf d / 3 ^ (orderOf d).factorization 3,
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_three ho),
      Nat.coprime_ordCompl Nat.prime_three ho, ⟨D.pow_mem hd.1 _, ?_⟩, ?_⟩
    · refine h3el _ (X.pow_mem hd.2 _) ⟨(orderOf d).factorization 3, ?_⟩
      rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
    · rw [Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  have hcop3 : ∀ (d : G) (hd : d ∈ D ⊓ X) (r : ℕ), Nat.Coprime 3 r →
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hd.2⟩ ^ r ∈
        Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hd.2⟩ ∈
        Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)) :=
    fun d hd r h3r hr => mem_of_pow_mem_of_coprime_5113 (hexp _ (hDb d hd)) hr h3r
  obtain ⟨y, hy, hyN⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨⟨d₀, hd₀X⟩, hd₀, rfl⟩ := hy
  have hd₀' : d₀ ∈ D ⊓ X := Subgroup.mem_subgroupOf.mp hd₀
  have hd₀C : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d₀, hd₀X⟩ ∉
      Subgroup.centralizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)) := fun hc =>
    hyN ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRQ)).trans
      (Subgroup.centralizer_le_normalizer _) hc)
  obtain ⟨s₀, r₀, -, h3r₀, hr₀D, -⟩ := hparts d₀ hd₀'
  have hd₁ : d₀ ^ r₀ ≠ 1 := by
    intro h1
    apply hd₀C
    refine hcop3 d₀ hd₀' r₀ h3r₀ ?_
    rw [← map_pow]
    have : (⟨d₀, hd₀X⟩ : ↥X) ^ r₀ = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hcard3 : Nat.card D₃ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard_dvd with h1 | h3
    · exfalso
      have hb : D₃ = ⊥ := Subgroup.eq_bot_of_card_eq D₃ h1
      have : d₀ ^ r₀ ∈ D₃ := hr₀D
      rw [hb, Subgroup.mem_bot] at this
      exact hd₁ this
    · exact h3
  have hD₃K : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    intro hle
    apply m.not_le
    intro d hd
    obtain ⟨s, r, hsr, h3r, hrD, hsr1⟩ := hparts d hd
    refine mem_of_pow_mem_of_coprime_5113 (a := s) (b := r) ?_ (hle hrD) hsr
    have hds : d ^ s ∈ D ⊓ X := ⟨D.pow_mem hd.1 s, X.pow_mem hd.2 s⟩
    refine hcent _ hds (hcop3 _ hds r h3r ?_)
    rw [← map_pow]
    have : (⟨d ^ s, hds.2⟩ : ↥X) ^ r = 1 := Subtype.ext (by simpa [← pow_mul] using hsr1)
    rw [this, map_one]
    exact Subgroup.one_mem _
  obtain ⟨tb, htb₁, hinv⟩ := htb
  rw [modO2Image_inf_of_pCoreOf_le hOT] at htb₁
  obtain ⟨t₀', ht₀', rfl⟩ := htb₁
  have ht₀ : (t₀' : G) ∈ T ⊓ Kh₁ := Subgroup.mem_subgroupOf.mp ht₀'
  set t₀ : G := (t₀' : G) with ht₀def
  set P := pCoreOf 2 X ⊓ Kh₁ with hPdef
  have hinvG : ∀ d ∈ D₃, t₀ * d * t₀⁻¹ * d ∈ P := by
    intro d hd
    have hdX : d ∈ X := hKhX hd.2
    have hwX : t₀ * d * t₀⁻¹ * d ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem t₀'.2 hdX) (X.inv_mem t₀'.2)) hdX
    have hwK : t₀ * d * t₀⁻¹ * d ∈ Kh₁ :=
      Kh₁.mul_mem (Kh₁.mul_mem (Kh₁.mul_mem ht₀.2 hd.2) (Kh₁.inv_mem ht₀.2)) hd.2
    have h1 := hinv _ (hDb d (hD₃X d hd))
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t₀ * d * t₀⁻¹ * d, hwX⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥X) t₀' * QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hdX⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥X) t₀')⁻¹ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hdX⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have h3 := hQC _ (hQb _ hwK) (h2 ▸ h1)
    exact ⟨hπ2 _ hwX h3, hwK⟩
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 X).to_le inf_le_left
  have hD₃P : D₃ ≤ Subgroup.normalizer (P : Set G) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 X (hKhX hd.2), Subgroup.le_normalizer hd.2⟩
  have hV : Nat.card ↥(D₃.map (MulAut.conj t₀).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t₀).injective, hcard3]
  have hVY : D₃.map (MulAut.conj t₀).toMonoidHom ≤ D₃ ⊔ P := by
    rintro _ ⟨d, hd, rfl⟩
    have e : (MulAut.conj t₀).toMonoidHom d = (t₀ * d * t₀⁻¹ * d) * d⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e]
    exact (D₃ ⊔ P).mul_mem (Subgroup.mem_sup_right (hinvG d hd))
      (Subgroup.mem_sup_left (D₃.inv_mem hd))
  obtain ⟨p, hp, hVp⟩ := exists_conj_eq_of_card_three hcard3 hV hP2 hD₃P hVY
  have hpT : p ∈ T := hOT hp.1
  refine ⟨Or.elim hty (fun h7 => Or.inl ?_) fun h => Or.inr (Or.elim h
    (fun hJ => Or.inl ?_) fun hM => Or.inr ?_), hKh3, D₃, le_rfl, hcard3, hD₃K, le_rfl,
    p⁻¹ * t₀, ⟨T.mul_mem (T.inv_mem hpT) ht₀.1, Kh₁.mul_mem (Kh₁.inv_mem hp.2) ht₀.2⟩, ?_⟩
  · obtain ⟨e⟩ := (h7 : Nonempty (↥(modO2Image X Kh₁) ≃* alternatingGroup (Fin 7)))
    exact ⟨eH.trans e⟩
  · obtain ⟨e⟩ := hJ
    exact ⟨eH.trans e⟩
  · obtain ⟨e⟩ := hM
    exact ⟨eH.trans e⟩
  ·
    intro d hd
    have hc : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ ∈ D₃ := by
      have hm : t₀ * d * t₀⁻¹ ∈ D₃.map (MulAut.conj p).toMonoidHom := by
        rw [← hVp]
        exact ⟨d, hd, rfl⟩
      obtain ⟨d', hd', hdd'⟩ := hm
      have hdd'' : p * d' * p⁻¹ = t₀ * d * t₀⁻¹ := hdd'
      have e : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ = d' := by
        calc p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ = p⁻¹ * (t₀ * d * t₀⁻¹) * p := by group
          _ = p⁻¹ * (p * d' * p⁻¹) * p := by rw [hdd'']
          _ = d' := by group
      rw [e]
      exact hd'
    have hw : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ * d ∈ D₃ := D₃.mul_mem hc hd
    have hwO : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ * d ∈ pCoreOf 2 X := by
      have h1 : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ * d =
          p⁻¹ * (t₀ * d * t₀⁻¹ * d) * (d⁻¹ * p * d) := by group
      rw [h1]
      have hdX : d ∈ X := hKhX hd.2
      have hn := le_normalizer_pCoreOf 2 X (X.inv_mem hdX)
      have h2 : d⁻¹ * p * d⁻¹⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp hn p).mp hp.1
      rw [inv_inv] at h2
      exact (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hp.1)
        (hinvG d hd).1) h2
    have h1 := hD2 _ hw.1 hwO
    exact eq_inv_of_mul_eq_one_left h1

theorem false_of_a314One (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (hM23 : FactM23L34) (h312 : A312ForSQTK) (h510 : Stmt5_1_10) (hlie : Stmt5_1_13_lieC)
    (hK4 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (heq : K₁ = oTwoUpper H)
    (hR2 : IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))) : False := by
  obtain ⟨k, hk⟩ := h510.exists_fieldParam m.hyp m.nota
  have e := m.toEmb512 hk
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  have hlie' := fun htype =>
    (hlie G T M L V H B D K₁ X Kh₁ n k m.hyp m.nota hk m.module m.comp m.closure m.inH m.hat m.lt
      htype).resolve_right fun h => h.not_lieModel_two hK4
  have hk2 : 2 ≤ k := e.field.1.1
  have hshape := e.shape heq
  rw [← heq] at hshape
  rcases hshape with (hL2 | hSz | ⟨hq, hU⟩) | ⟨hS, hD⟩
  · exact m.not_le (hlie' (Or.inr ⟨heq ▸ hL2, hR2⟩))
  · have h2 := e.twoF4_of_suzuki hM h312 heq hSz
    rw [← hcl] at h2
    exact m.not_le (hlie' (Or.inl ⟨heq ▸ hSz, h2⟩))
  · exact e.false_of_unitary hM h312 heq hk2 hq hU
  · rcases hS with hSL | hSp
    · rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · obtain rfl : k = 2 := by omega
        exact e.false_of_l34 hM hM23 h312 heq hSL hD
      · rcases hSL with hL3 | ⟨F, _, _, hF, ⟨eF⟩⟩
        · exact e.false_of_psl3 hM h312 heq hk3 hL3
        · exact e.false_of_sl3 hM h312 heq hk3 hF eF
    · exact e.false_of_psp4 hM h312 heq hk2 hSp

end Main513

theorem stmt5_1_13_type_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h36' : A36ForSQTK)
    (h38' : A38ForSQTK) (hF318 : A318Facts) (h510 : Stmt5_1_10) (hlie : Stmt5_1_13_lieC)
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34) (h312 : A312ForSQTK)
    (hnq : Stmt5_1_13_type_nq) (hj1 : Stmt5_1_13_type_j1) (hhat : Stmt5_1_13_type_hat7)
    (hTc : FactType513Aut) (hTe : FactType513Three) : Stmt5_1_13_type := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  obtain ⟨hst, hnot⟩ := m.star513 h37 h38 h510 heq hcl hL24
  have hj := hj1 G T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have hh7 := hhat G T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have hnq' := hnq G T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have h314 := hc5.2.2.2
  rw [hcl] at h314
  obtain ⟨eH⟩ := modO2_mulEquiv m.hat.1
  have hthree : (IsAlt 7 ↥(modO2Image X Kh₁) ∨
      IsHat ↥(modO2Image X Kh₁) (alternatingGroup (Fin 7)) ∨ IsSporadic .M22 ↥(modO2Image X Kh₁) ∨
      IsHat ↥(modO2Image X Kh₁) (NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥(modO2Image X Kh₁) ∨ IsSporadic .J1 ↥(modO2Image X Kh₁) ∨
      IsSporadic .J2 ↥(modO2Image X Kh₁) ∨ IsSporadic .J4 ↥(modO2Image X Kh₁) ∨
      IsSporadic .HS ↥(modO2Image X Kh₁) ∨ IsSporadic .Ru ↥(modO2Image X Kh₁)) →
      Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) := by
    intro hlist
    obtain ⟨hty, hexp, htb⟩ := hTe (O2Q X) _ _ _ _ _ hst hlist hj hnot
    have hty' : IsAlt 7 ↥(modO2Image X Kh₁) ∨ IsSporadic .J2 ↥(modO2Image X Kh₁) ∨
        IsSporadic .M23 ↥(modO2Image X Kh₁) := by
      rcases hty with h7 | h7h | hJ | hM'
      · exact Or.inl h7
      · exact absurd (IsHat.of_mulEquiv eH.symm h7h) (hh7 hexp)
      · exact Or.inr (Or.inl hJ)
      · exact Or.inr (Or.inr hM')
    exact m.type513_of_data hF318 h36' h38' hcl hnot hst.R_le hty' hexp htb
  have haut : ((∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      (IsPSL 2 p 1 ↥(modO2Image X Kh₁) ∨ IsSL2 p ↥(modO2Image X Kh₁))) ∨
      IsPSL 2 5 2 ↥(modO2Image X Kh₁) ∨
      ∃ s : Bool, IsPSLEps3 s 5 1 ↥(modO2Image X Kh₁) ∨ IsSLEps3 s 5 ↥(modO2Image X Kh₁)) →
      False :=
    fun hlist => hnot (hTc (O2Q X) _ _ _ _ _ hst hlist)
  unfold A314Statement at h314
  rcases h314 with ⟨-, -, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, h3⟩ | ⟨-, h4, -⟩ | ⟨-, h5, -⟩ |
      ⟨-, -, -, h6⟩ | ⟨-, -, -, h7⟩ | ⟨-, h8, -⟩ | ⟨-, h9, -⟩ | ⟨-, -, h10⟩ | ⟨-, h11, -⟩ |
      ⟨-, -, h12, -⟩ | h13 | h14
  · refine (m.false_of_a314One hM hM23 h312 h510 hlie hL24 heq ?_).elim
    rw [hcl]
    exact IsRank2LieChar2.of_mulEquiv eH.symm (isRank2LieChar2_of_a314One h1)
  · rcases h2 with h | h
    · exact hthree (Or.inl h)
    · exact hthree (Or.inr (Or.inl h))
  · rcases h3 with h | ⟨p, hp, hp5, hp8, h⟩
    · exact (haut (Or.inr (Or.inl h))).elim
    · exact (haut (Or.inl ⟨p, hp, hp5, hp8, Or.inl h⟩)).elim
  · exact (haut (Or.inr (Or.inr h4))).elim
  · rcases h5 with h | h
    · exact (haut (Or.inr (Or.inr ⟨true, Or.inl h⟩))).elim
    · exact (haut (Or.inr (Or.inr ⟨true, Or.inr h⟩))).elim
  · rcases h6 with h | h
    · exact hthree (Or.inr (Or.inr (Or.inl h)))
    · exact hthree (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h11)))))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h12)))))))))
  · exact (hnq' (Or.inl h13)).elim
  · exact (hnq' (Or.inr h14)).elim

end CFSG.Quasithin.H13
