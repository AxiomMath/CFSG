module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Gen
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Mult
public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSetting
public import CFSG.Quasithin.Background.A3Structure36AQuasi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isQuasisimple_o2q_of_open {K : Subgroup G}
    (h : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) : CFSG.IsQuasisimple (O2Q K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2).symm)
    (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr h)

theorem odd_card_center_o2q (K : Subgroup G) : Odd (Nat.card (Subgroup.center (O2Q K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (O2Q K))) 2 (even_iff_two_dvd.mp hev)
  have hzc : (z : O2Q K) ∈ Subgroup.center (O2Q K) := z.2
  have hPn : (Subgroup.zpowers (z : O2Q K)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzc m) g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ m
  have hzo : orderOf (z : O2Q K) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hPp : IsPGroup 2 (Subgroup.zpowers (z : O2Q K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hle : Subgroup.zpowers (z : O2Q K) ≤ CFSG.pCore 2 (O2Q K) := le_sSup ⟨hPn, hPp⟩
  rw [Setup.Campbell.pCore_quotient_pCore_eq_bot' 2] at hle
  have h1 : (z : O2Q K) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

theorem nonempty_mulEquiv_quot_center {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Nonempty (X ≃* X ⧸ Subgroup.center X) :=
  ⟨QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)⟩

namespace Set510

variable {T M L H B D K : Subgroup G} {n k : ℕ} (s : Set510 G T M L H B D K n k)
include s

theorem case_two_data (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    (∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
        ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
      (E2.IsBenderOf k ↥(E2.star (H ⊓ M) H K) ∨
        ((IsPSL 3 2 k ↥(E2.star (H ⊓ M) H K) ∨ IsPSp4 2 k ↥(E2.star (H ⊓ M) H K)) ∧
          E2.IsDiagramNontrivial (E2.star (H ⊓ M) H T) (E2.star (H ⊓ M) H K)
            (E2.star (H ⊓ M) H (T ⊓ K)))) := by
  have hc := s.cases
  dsimp only [E22FieldCases] at hc
  rcases hc with ⟨-, t, ht, hcj, -, -⟩ | ⟨-, hker, h2⟩
  · exact absurd (A38.map_conj_eq_iff.mpr (hT ht)) hcj
  · refine ⟨hker, ?_⟩
    rcases h2 with ⟨hBen, -⟩ | ⟨hk2, htype, hD, -⟩
    · exact Or.inl hBen
    · refine Or.inr ⟨?_, hD⟩
      rcases htype with h | h
      · exact Or.inl h
      · right
        rw [E2.IsSp4Prime] at h
        have hk1 : k ≠ 1 := by omega
        simpa only [hk1, ↓reduceIte] using h

theorem oTwoUpper_eq_K (hT : T ≤ Subgroup.normalizer (K : Set G)) : oTwoUpper H = K := by
  rw [s.oTwoUpper_eq]
  exact le_antisymm
    (conjClosure_le fun t ht k hk => (Subgroup.mem_normalizer_iff.mp (hT ht) k).mp hk)
    (le_conjClosure K T)

theorem kerIn_conj_mem (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    ∀ j ∈ K, j ∈ kerIn (H ⊓ M) H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K := by
  intro j hjK hjJ x hx
  have h1 := ((s.case_two_data hT).1 j).mp hjJ
  have h2 := h1.2 x (Subgroup.mem_sup_left hx.2)
  have h3 : j * x * j⁻¹ * x⁻¹ ∈ K ⊓ pCoreOf 2 H :=
    ⟨K.mul_mem (K.mul_mem (K.mul_mem hjK hx.2) (K.inv_mem hjK)) (K.inv_mem hx.2), h2⟩
  have h4 := (T ⊓ K).mul_mem (s.inf_pCoreOf_le h3) hx
  simpa using h4

theorem isBorelIn_two (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) := by
  refine s.isBorelIn_of fun x hx => ?_
  have h1 := s.inf_le_normalizer (s.kerIn_conj_mem hT) ⟨hx.1, s.oTwoUpper_eq_K hT ▸ hx.2⟩
  rwa [s.oTwoUpper_eq_K hT]

theorem o2q_quot_equiv_star (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    Nonempty ((O2Q K ⧸ Subgroup.center (O2Q K)) ≃* ↥(E2.star (H ⊓ M) H K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := (s.case_two_data hT).1
  set ρ := starRes (H ⊓ M) H K s.K_le_H with hρ
  have hmemO : ∀ x : ↥K, x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K := by
    intro x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx'⟩
      rwa [show x = x' from Subtype.ext hxx'.symm]
  have hOK : CFSG.pCore 2 ↥K ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hρ, starRes_eq_one_iff]
    exact s.pCoreOf_le_kerIn
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp s.comp) ((hmemO x).mp hx))
  set ψ : O2Q K →* ↥(E2.star (H ⊓ M) H K) := QuotientGroup.lift _ ρ hOK with hψ
  have hψk : ∀ x : ↥K, ψ (x : O2Q K) = ρ x := fun x => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := starRes_surjective s.K_le_H y
    exact ⟨x, hψk x⟩
  have hQn : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    s.K_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hker : ψ.ker = Subgroup.center (O2Q K) := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker, hψk, hρ, starRes_eq_one_iff, Subgroup.mem_center_iff]
    constructor
    · intro hxJ w
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply (hmemO _).mpr
      have h1 := ((hJ _).mp ((kerIn (H ⊓ M) H).inv_mem hxJ)).2 _
        (Subgroup.mem_sup_left (K.inv_mem y.2))
      have h2 : (((y * x)⁻¹ * (x * y) : ↥K) : G) =
          (x : G)⁻¹ * (y : G)⁻¹ * (x : G)⁻¹⁻¹ * (y : G)⁻¹⁻¹ := by simp [mul_assoc]
      rw [h2]
      refine Vol2.Ch11.SecB.inf_pCoreOf_le_pCoreOf s.K_le_H ⟨?_, h1⟩
      exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem x.2) (K.inv_mem y.2))
        (K.inv_mem (K.inv_mem x.2))) (K.inv_mem (K.inv_mem y.2))
    · intro hc
      have hca : ∀ a ∈ K, (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ pCoreOf 2 H := by
        intro a ha
        have h1 : ((x * ⟨a, ha⟩ * x⁻¹ * (⟨a, ha⟩ : ↥K)⁻¹ : ↥K) : O2Q K) = 1 := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hc]
          group
        rw [QuotientGroup.eq_one_iff] at h1
        exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp s.comp) ((hmemO _).mp h1)
      refine (hJ _).mpr ⟨Subgroup.mem_sup_left x.2, fun y hy => ?_⟩
      have hy' : y ∈ ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hy
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H) hQn] at hy'
      obtain ⟨a, ha, q, hq, rfl⟩ := hy'
      have hxH : (x : G) ∈ H := s.K_le_H x.2
      have haH : a ∈ H := s.K_le_H ha
      have hq1 : (x : G) * q * (x : G)⁻¹ * q⁻¹ ∈ pCoreOf 2 H :=
        (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hxH) q).mp hq)
          ((pCoreOf 2 H).inv_mem hq)
      have hq2 : a * ((x : G) * q * (x : G)⁻¹ * q⁻¹) * a⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H haH) _).mp
          hq1
      have e : (x : G) * (a * q) * (x : G)⁻¹ * (a * q)⁻¹ =
          ((x : G) * a * (x : G)⁻¹ * a⁻¹) * (a * ((x : G) * q * (x : G)⁻¹ * q⁻¹) * a⁻¹) := by
        group
      rw [e]
      exact (pCoreOf 2 H).mul_mem (hca a ha) hq2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

theorem card_center_o2q (h36 : A36ForSQTK) :
    Nat.card (Subgroup.center (O2Q K)) = 1 ∨ Nat.card (Subgroup.center (O2Q K)) = 3 := by
  have h := s.hyp.toHyp5_0_1
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian s.hyp.hStar.1.2
  have hL' := modO2Image_mem_cComp s.comp
  obtain ⟨-, -, hcases, -, -⟩ := (h36 _ hQ _ hL').2.1
  obtain ⟨e⟩ := modO2_mulEquiv s.comp
  have hqK : CFSG.IsQuasisimple ↥(modO2Image H K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_o2q_of_open s.quasi)
  have hcard : Nat.card (Subgroup.center ↥(modO2Image H K)) =
      Nat.card (Subgroup.center (O2Q K)) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.card_map_of_injective e.injective
  rcases hcases with ⟨hgF, -⟩ | ⟨hFZ, -, h13⟩
  · exfalso
    have htop : CFSG.fittingSubgroup ↥(modO2Image H K) = ⊤ := by
      rw [← hgF, A36A.generalizedFitting_eq_top hqK]
    have hsolv : Group.IsSolvable ↥(modO2Image H K) := by
      have : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image H K)) := inferInstance
      exact Group.isSolvable_of_surjective (f := (CFSG.fittingSubgroup ↥(modO2Image H K)).subtype)
        fun x => ⟨⟨x, htop ▸ Subgroup.mem_top x⟩, rfl⟩
    have : Group.IsPerfect ↥(modO2Image H K) := hqK.1
    have : Nontrivial ↥(modO2Image H K) := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      obtain ⟨-, -, a, b, hab⟩ := hqK
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (by rw [Subsingleton.elim a' b'])
    exact Group.IsPerfect.not_isSolvable ↥(modO2Image H K) hsolv
  · rw [← hcard, ← hFZ]
    exact h13

theorem diagram_of_star (hT : T ≤ Subgroup.normalizer (K : Set G))
    (hD : E2.IsDiagramNontrivial (E2.star (H ⊓ M) H T) (E2.star (H ⊓ M) H K)
      (E2.star (H ⊓ M) H (T ⊓ K))) :
    E2.IsDiagramNontrivial T K (T ⊓ K) := by
  set X := H ⊓ M with hX
  set π := starPi X H with hπ
  have hJK := s.kerIn_conj_mem hT
  have hJN : ∀ j ∈ K, j ∈ kerIn X H → j ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro j hjK hjJ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hJK j hjK hjJ x, fun hx => ?_⟩
    have h1 := hJK j⁻¹ (K.inv_mem hjK) ((kerIn X H).inv_mem hjJ) _ hx
    simpa [mul_assoc] using h1
  intro P hP hBP hTP
  have hPK : P ≤ K := hP.1.1
  have hJP : ∀ k ∈ K, k ∈ kerIn X H → k ∈ P := fun k hk hkJ => hBP ⟨hk, hJN k hk hkJ⟩
  have hpre : ∀ k ∈ K, ∀ (hkH : k ∈ H), π ⟨k, hkH⟩ ∈ E2.star X H P → k ∈ P := by
    intro k hk hkH hkP
    obtain ⟨p, hp, hpk⟩ := mem_star510_iff.mp hkP
    have h1 := starPi_eq_iff.mp hpk
    have h2 := hJP _ (K.mul_mem (K.inv_mem (hPK hp)) hk) h1
    have := P.mul_mem hp h2
    simpa using this
  have hBs : E2.star X H K ⊓ Subgroup.normalizer ((E2.star X H (T ⊓ K) : Subgroup _) :
      Set (E2.StarQuot X H)) ≤ E2.star X H P := by
    rintro y ⟨hyK, hyN⟩
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hyK
    have hxN := s.mem_normalizer_of_starPi hJK hx hyN
    exact starPi_mem_star (hBP ⟨hx, hxN⟩)
  have hPs_le : E2.star X H P ≤ E2.star X H K := Subgroup.map_mono fun x hx => hPK hx
  refine hD (E2.star X H P) ⟨⟨hPs_le, E2.star X H (T ⊓ K), s.sylowKs, hBs⟩, ?_, ?_⟩ hBs ?_
  ·
    intro heq
    apply hP.2.1
    refine le_antisymm hPK fun k hk => hpre k hk (s.K_le_H hk) ?_
    rw [heq]
    exact starPi_mem_star hk
  ·
    intro Q' hQ' hQ'K hPQ'
    set P₁ := K ⊓ (Q'.comap π).map H.subtype with hP₁
    have hPP₁ : P ≤ P₁ := fun p hp => ⟨hPK hp, ⟨⟨p, s.K_le_H (hPK hp)⟩, hPQ' (starPi_mem_star hp),
      rfl⟩⟩
    have hP₁par : IsParabolic2 K P₁ := ⟨inf_le_left, T ⊓ K, s.sylowK, hBP.trans hPP₁⟩
    have hP₁ne : P₁ ≠ K := by
      intro h
      apply hQ'K
      refine le_antisymm hQ'.1 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
      have hx' : (x : G) ∈ P₁ := by rw [h]; exact hx
      obtain ⟨x', hx'Q, hxx'⟩ := hx'.2
      rw [show x = x' from Subtype.ext hxx'.symm]
      exact hx'Q
    have hP₁eq := hP.2.2 P₁ hP₁par hP₁ne hPP₁
    refine le_antisymm (fun y hy => ?_) hPQ'
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp (hQ'.1 hy)
    have hxP₁ : (x : G) ∈ P₁ := ⟨hx, ⟨x, hy, rfl⟩⟩
    rw [hP₁eq] at hxP₁
    exact starPi_mem_star hxP₁
  ·
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_star510_iff.mp hy
    exact starPi_mem_normalizer (hTP ht)

theorem concl_two
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (h36 : A36ForSQTK)
    (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) ∧
      ((K = oTwoUpper H ∧ IsBenderCh5 k (O2Q (oTwoUpper H))) ∨
        (K = oTwoUpper H ∧
          (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
          E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H))) := by
  refine ⟨s.isBorelIn_two hT, ?_⟩
  have hRK := s.oTwoUpper_eq_K hT
  rw [hRK]
  obtain ⟨e⟩ := s.o2q_quot_equiv_star hT
  have hq := isQuasisimple_o2q_of_open s.quasi
  have hodd := odd_card_center_o2q K
  rcases (s.case_two_data hT).2 with ⟨-, hB | hB | hB⟩ | ⟨hS, hD⟩
  ·
    obtain ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ := hB
    have hZ := Mult5110.center_eq_bot_psl2 hGA hq hodd
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e.trans eF⟩⟩
    obtain ⟨e₁⟩ := nonempty_mulEquiv_quot_center hZ
    exact Or.inl ⟨rfl, Or.inl (Or.inl ⟨by simp [classicalTags],
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e₁.trans (e.trans eF)⟩⟩⟩)⟩
  ·
    obtain ⟨h2, a, ha, F, _, _, hf, hF, ⟨eF⟩⟩ := hB
    have hZ := Mult5110.center_eq_bot_sz hq (s.card_center_o2q h36)
      (k := k) ⟨h2, a, ha, F, inferInstance, inferInstance, hf, hF, ⟨e.trans eF⟩⟩
    obtain ⟨e₁⟩ := nonempty_mulEquiv_quot_center hZ
    exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨h2, a, ha, F, inferInstance, inferInstance, hf, hF,
      ⟨e₁.trans (e.trans eF)⟩⟩)⟩
  ·
    obtain ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ := hB
    exact Or.inl ⟨rfl, Or.inr (Or.inr ⟨hq, Or.inl ⟨by simp [classicalTags],
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e.trans eF⟩⟩⟩⟩)⟩
  · have hD' := s.diagram_of_star hT hD
    refine Or.inr ⟨rfl, ?_, hD'⟩
    rcases hS with ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ | ⟨hadm, F, _, _, hF, ⟨eF⟩⟩
    · exact Or.inl (Mult5110.isSL3Ch5_of_odd_center hGA hq hodd
        ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e.trans eF⟩⟩)
    · have hZ := Mult5110.center_eq_bot_psp4 hGA hq hodd
        ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e.trans eF⟩⟩
      obtain ⟨e₁⟩ := nonempty_mulEquiv_quot_center hZ
      exact Or.inr (Or.inl ⟨by simp [classicalTags],
        ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e₁.trans (e.trans eF)⟩⟩⟩)

end Set510

end CFSG.Quasithin.H13
