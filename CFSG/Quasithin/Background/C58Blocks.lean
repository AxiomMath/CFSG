module

public import CFSG.Quasithin.Background.C58Push
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.C58Sub
public import CFSG.Quasithin.Background.C58Local
public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMinParabolic
public import CFSG.Quasithin.Background.C58IndexTwo

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
  Subgroup

variable {G : Type} [Group G]

section Select

variable [Finite G]

omit [Finite G] in
theorem minParabolic_of_select {P R M : Subgroup G} (hR : IsSylowIn 2 R P)
    (hRn : ¬ P ≤ normalizer (R : Set G))
    (hM : P ⊓ M < P ∧ R ≤ P ⊓ M ∧ ∀ Y : Subgroup G, R ≤ Y → Y < P → Y ≤ P ⊓ M) :
    MinParabolic P R (P ⊓ M) := by
  obtain ⟨hlt, hRM, hmax⟩ := hM
  have hmax' : IsMaxSubgroupIn P (P ⊓ M) := by
    refine ⟨hlt, fun X hKX hXP => ?_⟩
    by_contra hne
    exact absurd (hmax X (hRM.trans hKX.le) (lt_of_le_of_ne hXP hne)) (not_le_of_gt hKX)
  refine ⟨hR, hRn, isUniqueMaxOver_iff.mpr ⟨hmax', hRM, fun N hN hRN => ?_⟩⟩
  have hNK : N ≤ P ⊓ M := hmax N hRN hN.1
  by_contra hne
  have hlt' : N < P ⊓ M := lt_of_le_of_ne hNK hne
  exact absurd (hN.2 (P ⊓ M) hlt' hlt.le) (ne_of_lt hlt)

omit [Finite G] in
theorem noCharNormal_baum {R X : Subgroup G} (h : NoCharNormal R X) :
    NoCharNormal (baum R) X := fun C hCS hC1 hCchar =>
  h C (hCS.trans (C1GN.baum_le R)) hC1
    (C1GN.characteristic_subgroupOf_trans (C1GN.baum_le R) hCS (C1GN.characteristic_baum R) hCchar)

theorem not_thompsonJ_le_centralizer {H₀ S M : Subgroup G} (hmin : MinParabolic H₀ S M)
    (hchar : CharTwo H₀) (hnc : NoCharNormal S H₀) :
    ¬ thompsonJ S ≤ centralizer (VZ S H₀ : Set G) ∧ IsTwoReducedIn H₀ (VZ S H₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hmin.isSylow
  have hSH : S ≤ H₀ := hS.1
  have hS2 : IsPGroup 2 S := hS.2.1
  have hS1 : S ≠ ⊥ := by
    intro h
    apply hmin.not_normal
    rw [h]
    intro g _
    rw [mem_normalizer_iff]
    intro x
    simp only [mem_bot]
    constructor
    · rintro rfl; group
    · intro hx
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, hx]; group
  have hred : IsTwoReducedIn H₀ (VZ S H₀) :=
    isTwoReducedIn_conjClosure_of_sylowIn hSH hS2 hS.2.2 hchar le_rfl
  refine ⟨fun h => ?_, hred⟩
  have hZ1 : quasithinOmegaOneCenter S ≠ ⊥ := quasithinOmegaOneCenter_ne_bot hS2 hS1
  have hZS : quasithinOmegaOneCenter S ≤ S := by
    rw [← omegaOneCenterOf_eq]
    exact C1GN.omegaOneCenterOf_le_self S
  have hHV : ¬ H₀ ≤ centralizer (VZ S H₀ : Set G) := by
    intro hH
    refine hnc _ hZS hZ1 (characteristic_omegaOneCenterOf S) fun g hg => ?_
    have hgc : g ∈ centralizer (quasithinOmegaOneCenter S : Set G) :=
      Subgroup.centralizer_le (le_conjClosure _ H₀) (hH hg)
    exact Subgroup.centralizer_le_normalizer _ hgc
  have hinf := hmin.inf_centralizer_eq_pCoreOf hred hHV
  have hJQ : thompsonJ S ≤ pCoreOf 2 H₀ := hinf ▸ le_inf (B6.thompsonJ_le S) h
  have hQS : pCoreOf 2 H₀ ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hS
  have hJeq : thompsonJ (pCoreOf 2 H₀) = thompsonJ S := B6.thompsonJ_eq_of_le hJQ hQS
  refine hnc (thompsonJ S) (B6.thompsonJ_le S) (thompsonJ_ne_bot hS2 hS1)
    (characteristic_thompsonJ S) ?_
  rw [← hJeq]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀).trans
    (normalizer_le_normalizer_thompsonJ _)

theorem exists_pushUp_data {T H R N : Subgroup G} (hminH : MinParabolic H T N)
    (hchar : CharTwo H) (hsolv : Group.IsSolvable H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hR1 : R ≠ ⊥) (hRT : R ≤ T) (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R))
    (hTR : T ≤ normalizer (R : Set G)) (hncH : NoCharNormal R H) :
    ∃ P H₀ : Subgroup G, P ≤ oTwoUpper H ⊔ R ∧ R ≤ P ∧ ¬ P ≤ N ∧ P ⊔ T = H ∧
      MinParabolic P R (P ⊓ N) ∧ CharTwo P ∧ NoCharNormal R P ∧
      IsSylowTwoOf (baum R) (oTwoUpper P ⊔ baum R) ∧
      H₀ ≤ oTwoUpper P ⊔ baum R ∧ baum R ≤ H₀ ∧ ¬ H₀ ≤ N ∧
      MinParabolic H₀ (baum R) (H₀ ⊓ (P ⊓ N)) ∧ CharTwo H₀ ∧
      IsShort2 (oTwoUpper H₀) ∧ IsAltType (oTwoUpper H₀) 3 ∧
      ⁅oTwoUpper H₀, thompsonJ R⁆ = oTwoUpper H₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsylH := hminH.isSylow
  have hTH : T ≤ H := hTsylH.1
  have hT2 : IsPGroup 2 T := hTsylH.2.1
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hTsylH
  obtain ⟨P, hPKR, hRP, hPN, hRsylP, hRnP, hPmax, hPT, -, hncP⟩ :=
    minimal_parabolic_subgroup_over_normal_Sylow_part (p := 2) hTsylH hminH.maximal.1 hminH.le
      (fun Y hTY hYH => hminH.le_of_lt hTY hYH) hKH (le_normalizer_oTwoUpper H) hKT
      (hasNoTwoQuotient_oddOrderSubgroup H) hR1 hRT hTR hRsyl hncH
  have hminP : MinParabolic P R (P ⊓ N) := minParabolic_of_select hRsylP hRnP hPmax
  have hPH : P ≤ H := hPKR.trans (sup_le hKH (hRT.trans hTH))
  have hsolvP : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPH)
  have hSQTP : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2 := fun p hp hp2 =>
    (CFSG.SectionRank.pRank_mono hp.one_lt hPH).trans (hSQT p hp hp2)
  have hKRn : H ≤ normalizer ((oTwoUpper H ⊔ R : Subgroup G) : Set G) := by
    calc H = oTwoUpper H ⊔ T := hKT.symm
      _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (fun t ht => C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht))
  have hcharKR : CharTwo (oTwoUpper H ⊔ R) :=
    A4.charTwo_of_normal (sup_le hKH (hRT.trans hTH)) hKRn hchar
  have hcharP : CharTwo P := C1GN.charTwo_of_le hcharKR hRsyl hRP.le hPKR
  obtain ⟨hJP, hredP⟩ := not_thompsonJ_le_centralizer hminP hcharP hncP
  have hVPe : IsElemAbelian 2 (VZ R P) := hredP.2.2.1
  obtain ⟨-, -, hSsyl, -, -⟩ := E2_3_two_of_isSolvable hVPe hminP hsolvP hSQTP hredP hJP
  rw [F6.twoResidual_eq_oTwoUpper] at hSsyl
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hS1 : baum R ≠ ⊥ := C1GN.baum_ne_bot hR2 hR1
  have hRS : R ≤ normalizer (baum R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum R)
  have hKPP : oTwoUpper P ≤ P := oTwoUpper_le P
  have hKPR : oTwoUpper P ⊔ R = P := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hminP.isSylow
  obtain ⟨H₀, hH₀KS, hSH₀, hH₀M, hSsylH₀, hSnH₀, hH₀max, -, -, hncH₀⟩ :=
    minimal_parabolic_subgroup_over_normal_Sylow_part (p := 2) hminP.isSylow hminP.maximal.1
      hminP.le (fun Y hRY hYP => hminP.le_of_lt hRY hYP) hKPP (le_normalizer_oTwoUpper P) hKPR
      (hasNoTwoQuotient_oddOrderSubgroup P) hS1 hSR hRS hSsyl (noCharNormal_baum hncP)
  have hminH₀ : MinParabolic H₀ (baum R) (H₀ ⊓ (P ⊓ N)) :=
    minParabolic_of_select hSsylH₀ hSnH₀ hH₀max
  have hH₀P : H₀ ≤ P := hH₀KS.trans (sup_le hKPP (hSR.trans hRP.le))
  have hH₀N : ¬ H₀ ≤ N := fun h => hH₀M (le_inf hH₀P h)
  have hsolvH₀ : Group.IsSolvable H₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hH₀P.trans hPH))
  have hSQTH₀ : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H₀ ≤ 2 := fun p hp hp2 =>
    (CFSG.SectionRank.pRank_mono hp.one_lt (hH₀P.trans hPH)).trans (hSQT p hp hp2)
  have hKSn : P ≤ normalizer ((oTwoUpper P ⊔ baum R : Subgroup G) : Set G) := by
    calc P = oTwoUpper P ⊔ R := hKPR.symm
      _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (fun r hr => C1.mem_normalizer_sup (le_normalizer_oTwoUpper P (hRP.le hr)) (hRS hr))
  have hcharKS : CharTwo (oTwoUpper P ⊔ baum R) :=
    A4.charTwo_of_normal (sup_le hKPP (hSR.trans hRP.le)) hKSn hcharP
  have hcharH₀ : CharTwo H₀ := C1GN.charTwo_of_le hcharKS hSsyl hSH₀.le hH₀KS
  obtain ⟨hshort, halt, hJ⟩ :=
    pushUp_block hminH₀ hsolvH₀ hSQTH₀ hcharH₀ (C1GN.baum_baum R) hncH₀
  have hJSR : thompsonJ (baum R) = thompsonJ R :=
    B6.thompsonJ_eq_of_le (thompsonJ_le_baum' R) hSR
  rw [hJSR] at hJ
  exact ⟨P, H₀, hPKR, hRP.le, hPN, hPT, hminP, hcharP, hncP, hSsyl, hH₀KS, hSH₀.le, hH₀N, hminH₀,
    hcharH₀, hshort, halt, hJ⟩

omit [Finite G] in
theorem oTwoUpper_le_of_le_sup {X A B : Subgroup G} (hXAB : X ≤ A ⊔ B) (hB : IsPGroup 2 B)
    (hBA : B ≤ normalizer (A : Set G)) : oTwoUpper X ≤ A :=
  oTwoUpper_le_of_pow_mem fun _ hx => C1.exists_pow_mem_of_mem_sup hB hBA (hXAB hx)

theorem pCoreOf_inf_le {X Y : Subgroup G} (hYX : Y ≤ X) :
    pCoreOf 2 X ⊓ Y ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)
  intro y hy
  exact mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hYX hy))
    (Subgroup.le_normalizer hy)

theorem isSubnormal_of_pCoreOf_le {K X A : Subgroup G} {p : ℕ} [Fact p.Prime] (hKX : K ≤ X)
    (hpow : ∀ k ∈ K, ∃ a : ℕ, k ^ p ^ a ∈ pCoreOf 2 X) (hQA : pCoreOf 2 K ≤ A) (hAK : A ≤ K) :
    (A.subgroupOf K).IsSubnormal := by
  refine isSubnormal_subgroupOf_of_pow_mem (p := p) hQA hAK
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) fun k hk => ?_
  obtain ⟨a, ha⟩ := hpow k hk
  refine ⟨a, pCoreOf_inf_le hKX ⟨ha, ?_⟩⟩
  exact pow_mem hk _

theorem isSubnormal_block {T H R N P H₀ : Subgroup G} (hminH : MinParabolic H T N)
    (hsolv : Group.IsSolvable H) (hRT : R ≤ T) (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R))
    (hPKR : P ≤ oTwoUpper H ⊔ R) (hRP : R ≤ P) (hminP : MinParabolic P R (P ⊓ N))
    (hSsyl : IsSylowTwoOf (baum R) (oTwoUpper P ⊔ baum R)) (hH₀KS : H₀ ≤ oTwoUpper P ⊔ baum R)
    (hSH₀ : baum R ≤ H₀) : ((oTwoUpper H₀).subgroupOf H).IsSubnormal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hminH.isSylow.1
  have hR2 : IsPGroup 2 R := hminH.isSylow.2.1.to_le hRT
  have hS2 : IsPGroup 2 (baum R) := hR2.to_le (C1GN.baum_le R)
  set K := oTwoUpper H with hK
  set KP := oTwoUpper P with hKP
  set L := oTwoUpper H₀ with hL
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hRK : R ≤ normalizer (K : Set G) := (hRT.trans hTH).trans hHK
  have hPH : P ≤ H := hPKR.trans (sup_le hKH (hRT.trans hTH))
  have hKPP : KP ≤ P := oTwoUpper_le P
  have hPKP : P ≤ normalizer (KP : Set G) := le_normalizer_oTwoUpper P
  have hSKP : baum R ≤ normalizer (KP : Set G) := ((C1GN.baum_le R).trans hRP).trans hPKP
  have hLKP : L ≤ KP := oTwoUpper_le_of_le_sup hH₀KS hS2 hSKP
  have hKPK : KP ≤ K := oTwoUpper_le_of_le_sup hPKR hR2 hRK
  have hsolvP : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPH)
  obtain ⟨p, hp, -, hpowP⟩ := hminP.exists_prime_pow_mem_pCoreOf hsolvP
  obtain ⟨q, hq, -, hpowH⟩ := hminH.exists_prime_pow_mem_pCoreOf hsolv
  rw [F6.twoResidual_eq_oTwoUpper] at hpowP hpowH
  have hQ₁S : pCoreOf 2 KP ≤ baum R := by
    refine le_trans ?_ (B6.pCoreOf_two_le_of_isSylowTwoOf hSsyl)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 KP).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 KP)
    exact (sup_le Subgroup.le_normalizer hSKP).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 KP)
  have hH₀L : H₀ ≤ normalizer (L : Set G) := le_normalizer_oTwoUpper H₀
  have h1 : (L.subgroupOf (L ⊔ pCoreOf 2 KP)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer le_sup_left
      (sup_le Subgroup.le_normalizer ((hQ₁S.trans hSH₀).trans hH₀L))
  have : Fact p.Prime := ⟨hp⟩
  have h2 : ((L ⊔ pCoreOf 2 KP).subgroupOf KP).IsSubnormal :=
    isSubnormal_of_pCoreOf_le hKPP hpowP le_sup_right
      (sup_le hLKP (CFSG.LieType.BorelTits.pCoreOf_le 2 KP))
  have h3 : (L.subgroupOf KP).IsSubnormal := isSubnormal_subgroupOf_trans le_sup_left h1 h2
  have hQ₂R : pCoreOf 2 K ≤ R := by
    refine le_trans ?_ (B6.pCoreOf_two_le_of_isSylowTwoOf hRsyl)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact (sup_le Subgroup.le_normalizer hRK).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have h4 : (KP.subgroupOf (KP ⊔ pCoreOf 2 K)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer le_sup_left
      (sup_le Subgroup.le_normalizer ((hQ₂R.trans hRP).trans hPKP))
  have : Fact q.Prime := ⟨hq⟩
  have h5 : ((KP ⊔ pCoreOf 2 K).subgroupOf K).IsSubnormal :=
    isSubnormal_of_pCoreOf_le hKH hpowH le_sup_right
      (sup_le hKPK (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  have h6 : (KP.subgroupOf K).IsSubnormal := isSubnormal_subgroupOf_trans le_sup_left h4 h5
  have h7 : (L.subgroupOf K).IsSubnormal := isSubnormal_subgroupOf_trans hLKP h3 h6
  exact isSubnormal_subgroupOf_trans (hLKP.trans hKPK) h7
    (isSubnormal_subgroupOf_of_le_normalizer hKH hHK)

end Select

section Blocks

theorem card_quotient_pCore_of_isAltType {L : Subgroup G} (h : IsAltType L 3) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  obtain ⟨α, hαs, hαk, -⟩ := h
  have e := QuotientGroup.quotientKerEquivOfSurjective α hαs
  rw [← hαk, Nat.card_congr e.toEquiv]
  have h6 := two_mul_nat_card_alternatingGroup (α := Fin 3)
  rw [Nat.card_perm, Nat.card_fin] at h6
  simp only [Nat.factorial] at h6
  omega

theorem isBlock2_conjSubgroup {H L : Subgroup G} (hL : IsBlock2 H L) {g : G} (hg : g ∈ H) :
    IsBlock2 H (conjSubgroup L g) := by
  obtain ⟨hs, hLH, hsub⟩ := hL
  refine ⟨Lin2.IsShort2.map_equiv hs (MulAut.conj g⁻¹), fun x hx => ?_, ?_⟩
  · rw [mem_conjSubgroup_iff] at hx
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hg) (hLH hx)) hg
  · have e : (conjSubgroup L g).subgroupOf H =
        (L.subgroupOf H).map (MulAut.conj (⟨g, hg⟩ : H)⁻¹).toMonoidHom := by
      ext x
      simp only [mem_subgroupOf, mem_conjSubgroup_iff]
      rw [Subgroup.mem_map_equiv]
      simp only [mem_subgroupOf, MulAut.conj_symm_apply, inv_inv, coe_mul, coe_inv]
    rw [e]
    exact hsub.map (MulAut.conj _).surjective

theorem card_quotient_pCore_conjSubgroup (L : Subgroup G) (g : G) :
    Nat.card (↥(conjSubgroup L g) ⧸ CFSG.pCore 2 ↥(conjSubgroup L g)) =
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
  card_quotient_pCore_map (MulAut.conj g⁻¹).injective L

theorem mem_normalizer_iSup {ι : Sort*} {A : ι → Subgroup G} {x : G}
    (h : ∀ i, x ∈ normalizer (A i : Set G)) : x ∈ normalizer ((⨆ i, A i : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.mp (h i)

theorem map_conj_conjSubgroup (A : Subgroup G) (g t : G) :
    (conjSubgroup A g).map (MulAut.conj t).toMonoidHom = conjSubgroup A (g * t⁻¹) := by
  unfold conjSubgroup
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem le_normalizer_iSup_conj (A T : Subgroup G) :
    T ≤ normalizer ((⨆ (g : G) (_ : g ∈ T), conjSubgroup A g : Subgroup G) : Set G) := by
  set X := ⨆ (g : G) (_ : g ∈ T), conjSubgroup A g with hX
  have hle : ∀ t ∈ T, X.map (MulAut.conj t).toMonoidHom ≤ X := by
    intro t ht
    rw [hX, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [map_conj_conjSubgroup]
    exact le_iSup₂_of_le (g * t⁻¹) (mul_mem hg (inv_mem ht)) le_rfl
  have hmem : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun t ht x hx =>
    hle t ht ⟨x, hx, by simp⟩
  intro t ht
  exact B6.mem_normalizer_of_forall_mem (hmem t ht) (fun x hx => by
    simpa using hmem t⁻¹ (inv_mem ht) x hx)

end Blocks

section Main

variable [Finite G]

theorem exists_blockConfig {T H R M₀ N : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) (hchar : CharTwo H) (hN : IsUniqueMaxOver H T N)
    (hTn : ¬ H ≤ normalizer (T : Set G)) (hsolv : Group.IsSolvable H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hR1 : R ≠ ⊥) (hRT : R ≤ T) (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R))
    (hTM₀ : T ≤ M₀) (hM₀R : M₀ ≤ normalizer (R : Set G)) (hNC : NoCommonNormal R H M₀) :
    ∃ K₁ : Subgroup G, BlockConfig H T R K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hT.1
  have hTsylH : IsSylowTwoOf T H :=
    ⟨hTH, hT2, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hminH : MinParabolic H T N := ⟨hTsylH, hTn, hN⟩
  have hTR : T ≤ normalizer (R : Set G) := hTM₀.trans hM₀R
  have hncH : NoCharNormal R H := fun C hCR hC1 hCchar hHC =>
    hNC C hCR hC1 hHC (hM₀R.trans (normalizer_le_normalizer_of_characteristic hCR hCchar))
  obtain ⟨P, H₀, hPKR, hRP, -, -, hminP, -, -, hSsyl, hH₀KS, hSH₀, hH₀N, hminH₀, -,
    hshort, halt, hJ⟩ := exists_pushUp_data hminH hchar hsolv hSQT hR1 hRT hRsyl hTR hncH
  have hsubH := isSubnormal_block hminH hsolv hRT hRsyl hPKR hRP hminP hSsyl hH₀KS hSH₀
  set L := oTwoUpper H₀ with hL
  have hA : IsA4Block L (blockU L) := IsA4Block.of_alt3 hshort halt
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hPH : P ≤ H := hPKR.trans (sup_le hKH (hRT.trans hTH))
  have hH₀H : H₀ ≤ H := (hH₀KS.trans (sup_le (oTwoUpper_le P)
    ((C1GN.baum_le R).trans hRP))).trans hPH
  have hLH : L ≤ H := (oTwoUpper_le H₀).trans hH₀H
  have hB : IsBlock2 H L := ⟨hshort, hLH, hsubH⟩
  have h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := card_quotient_pCore_of_isAltType halt
  have hcommute : ∀ g ∈ H, ∀ g' ∈ H, conjSubgroup L g ≠ conjSubgroup L g' →
      ⁅conjSubgroup L g, conjSubgroup L g'⁆ = ⊥ := fun g hg g' hg' hne =>
    C1Pack.commutator_eq_bot_of_card_three hchar (isBlock2_conjSubgroup hB hg)
      ((card_quotient_pCore_conjSubgroup L g).trans h3) (isBlock2_conjSubgroup hB hg')
      ((card_quotient_pCore_conjSubgroup L g').trans h3) hne
  have hcomm1 : ∀ g ∈ H, conjSubgroup L g ≠ L → ∀ a ∈ L, ∀ b ∈ conjSubgroup L g,
      a * b = b * a := by
    intro g hg hne a ha b hb
    have h1 := hcommute 1 (one_mem H) g hg (by rw [conjSubgroup_one]; exact hne.symm)
    rw [conjSubgroup_one, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    exact ((mem_centralizer_iff.mp (h1 ha)) b hb).symm
  have hLN : ¬ L ≤ N := by
    intro hle
    apply hH₀N
    have hS : baum R ⊔ twoResidual H₀ = H₀ := sup_twoResidual_eq hminH₀.isSylow
    rw [F6.twoResidual_eq_oTwoUpper] at hS
    rw [← hS]
    exact sup_le (((C1GN.baum_le R).trans hRT).trans hminH.le) hle
  set X := ⨆ (g : G) (_ : g ∈ T), conjSubgroup L g with hX
  have hLX : L ≤ X := le_iSup₂_of_le (1 : G) (one_mem T) (by rw [conjSubgroup_one])
  have hXH : X ≤ H := iSup₂_le fun g hg => (isBlock2_conjSubgroup hB (hTH hg)).2.1
  have hTX : T ≤ normalizer (X : Set G) := le_normalizer_iSup_conj L T
  have hXT : X ⊔ T = H := by
    by_contra hne
    have hlt : X ⊔ T < H := lt_of_le_of_ne (sup_le hXH hTH) hne
    exact hLN ((hLX.trans le_sup_left).trans (hminH.le_of_lt le_sup_right hlt))
  have hgen : oTwoUpper H ≤ X := oTwoUpper_le_of_le_sup hXT.ge hT2 hTX
  have hindex : (T ⊓ normalizer (L : Set G)).relIndex T ≤ 2 := by
    by_contra hlt
    push Not at hlt
    set N' : Subgroup T := (T ⊓ normalizer (L : Set G)).subgroupOf T with hN'
    have hcard : 2 < Nat.card (↥T ⧸ N') := hlt
    have : Fintype (↥T ⧸ N') := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hcard
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
    set ta : T := Quotient.out a
    set tb : T := Quotient.out b
    set tc : T := Quotient.out c
    have hta : (ta : ↥T ⧸ N') = a := Quotient.out_eq a
    have htb : (tb : ↥T ⧸ N') = b := Quotient.out_eq b
    have htc : (tc : ↥T ⧸ N') = c := Quotient.out_eq c
    have hdist : ∀ x y : T, (x : ↥T ⧸ N') ≠ (y : ↥T ⧸ N') →
        conjSubgroup L ((x : G))⁻¹ ≠ conjSubgroup L ((y : G))⁻¹ := by
      intro x y hxy heq
      apply hxy
      rw [QuotientGroup.eq]
      have h1 := congrArg (fun A => conjSubgroup A (y : G)) heq
      simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
      have h2 : ((x⁻¹ * y : T) : G) ∈ normalizer (L : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.mp (by simpa using h1)
      exact mem_subgroupOf.mpr ⟨(x⁻¹ * y).2, h2⟩
    have hab' := hdist ta tb (by rw [hta, htb]; exact hab)
    have hac' := hdist ta tc (by rw [hta, htc]; exact hac)
    have hbc' := hdist tb tc (by rw [htb, htc]; exact hbc)
    have hmemH : ∀ x : T, ((x : G))⁻¹ ∈ H := fun x => inv_mem (hTH x.2)
    set S₃ : Finset (Subgroup G) := {conjSubgroup L ((ta : G))⁻¹, conjSubgroup L ((tb : G))⁻¹,
      conjSubgroup L ((tc : G))⁻¹} with hS₃
    have hS₃card : S₃.card = 3 := Finset.card_eq_three.2 ⟨_, _, _, hab', hac', hbc', rfl⟩
    have hconj : ∀ K ∈ S₃, ∃ x : T, K = conjSubgroup L ((x : G))⁻¹ := by
      intro K hK
      simp only [hS₃, Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl | rfl
      exacts [⟨ta, rfl⟩, ⟨tb, rfl⟩, ⟨tc, rfl⟩]
    obtain ⟨E, hEle, hE, hEcard⟩ := C1GN.exists_elemAbelian_three_pow (fun K : Subgroup G => K)
      S₃
      (fun K hK => by
        obtain ⟨x, rfl⟩ := hconj K hK
        exact (isBlock2_conjSubgroup hB (hmemH x)).1.2.1)
      (fun K hK => by
        obtain ⟨x, rfl⟩ := hconj K hK
        rw [card_conjSubgroup, hA.card_L]
        norm_num)
      (fun K hK K' hK' hne => by
        obtain ⟨x, rfl⟩ := hconj K hK
        obtain ⟨y, rfl⟩ := hconj K' hK'
        exact hcommute _ (hmemH x) _ (hmemH y) hne)
    have hEH : E ≤ H := hEle.trans (iSup₂_le fun K hK => by
      obtain ⟨x, rfl⟩ := hconj K hK
      exact (isBlock2_conjSubgroup hB (hmemH x)).2.1)
    rw [hS₃card] at hEcard
    have h3r := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEH hE hEcard
    have := hSQT 3 Nat.prime_three (by norm_num)
    omega
  have hQU : blockQ L = blockU L :=
    le_antisymm (IsA4Block.le_U_of_isPGroup hA (C1.blockQ_le L)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)) (C1.blockU_le_blockQ hshort)
  have hQH : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ L, k * q * k⁻¹ * q⁻¹ ∈ blockU L := by
    intro q hq k hk
    have hqN : q ∈ normalizer (L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).mp
        (C1Pack.isBlock2_normal_sup_pCore hB).2 (mem_sup_right hq)
    have h1 : k * q * k⁻¹ * q⁻¹ ∈ L := by
      have : q * k⁻¹ * q⁻¹ ∈ L := (mem_normalizer_iff.mp hqN k⁻¹).mp (inv_mem hk)
      have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
      rw [e]; exact mul_mem hk this
    have h2 : k * q * k⁻¹ * q⁻¹ ∈ pCoreOf 2 H := by
      have : k * q * k⁻¹ ∈ pCoreOf 2 H :=
        (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hk)) q).mp
          hq
      exact mul_mem this (inv_mem hq)
    rw [← hQU, C1Pack.blockQ_eq_inf_pCoreOf hB]
    exact ⟨h1, h2⟩
  set U := ⨆ (g : G) (_ : g ∈ T), conjSubgroup (blockU L) g with hU
  have hUconj : ∀ g : G, conjSubgroup (blockU L) g ≤ conjSubgroup L g := fun g =>
    conjSubgroup_mono hA.le g
  have hXU : X ≤ normalizer (U : Set G) := by
    refine iSup₂_le fun g' hg' => ?_
    intro x hx
    refine mem_normalizer_iSup fun g => mem_normalizer_iSup fun hg => ?_
    by_cases heq : conjSubgroup L g' = conjSubgroup L g
    · rw [heq] at hx
      have h1 := conjSubgroup_mono (IsA4Block.le_normalizer_U hA) g
      rw [C5.conjSubgroup_normalizer] at h1
      exact h1 hx
    · have h1 := hcommute g' (hTH hg') g (hTH hg) heq
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
      refine Subgroup.centralizer_le_normalizer _ ?_
      exact Subgroup.centralizer_le (hUconj g) (h1 hx)
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hXT]; exact sup_le hXU (le_normalizer_iSup_conj (blockU L) T)
  have hCH : T ⊓ centralizer (U : Set G) ≤ pCoreOf 2 H := by
    set Y := H ⊓ centralizer (U : Set G) with hY
    have hYn : H ≤ normalizer (Y : Set G) := fun h hh =>
      mem_normalizer_inf (Subgroup.le_normalizer hh) (mem_normalizer_centralizer (hHU hh))
    rcases hminH.le_kerIn_or_twoResidual_le inf_le_left hYn with hYJ | hKY
    · have hJS := hminH.isSylowTwoOf_pCoreOf_kerIn
      refine le_of_isPGroup_of_normal hJS ?_ ((inf_le_inf_right _ hTH).trans hYJ)
        (hT2.to_le inf_le_left)
      exact hminH.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    · exfalso
      have hLK : L ≤ twoResidual H := by
        rw [F6.twoResidual_eq_oTwoUpper]; exact oTwoUpper_mono hH₀H
      have hUU : blockU L ≤ U := le_iSup₂_of_le (1 : G) (one_mem T) (by rw [conjSubgroup_one])
      obtain ⟨c, hcL, -, -, hcfp, -⟩ := hA.exists_c
      have hcC : c ∈ centralizer (U : Set G) := ((hLK.trans hKY) hcL).2
      obtain ⟨u, huU, hu1⟩ : ∃ u ∈ blockU L, u ≠ 1 := by
        by_contra h
        push Not at h
        have hbot : blockU L = ⊥ := eq_bot_iff.mpr fun u hu => mem_bot.mpr (h u hu)
        have h4 := hA.card_U
        rw [hbot, Subgroup.card_bot] at h4
        norm_num at h4
      apply hcfp u huU hu1
      have h1 : u * c = c * u := (mem_centralizer_iff.mp hcC) u (hUU huU)
      calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [h1]
        _ = u := by group
  refine ⟨L, ⟨hshort, halt, hLH, hJ, ?_, ?_, ?_, hindex, hgen, hQH, hCH⟩⟩
  ·
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 H₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (oTwoUpper_le H₀))
        ((le_normalizer_oTwoUpper H₀).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact (C1.blockU_le_blockQ hshort).trans (h1.trans
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hminH₀.isSylow).trans (C1GN.baum_le R)))
  · intro g hg
    by_cases heq : conjSubgroup L g = L
    · exact Or.inl heq
    · exact Or.inr (hcomm1 g (hTH hg) heq)
  · intro g hg hne
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    refine hA.center_L x hx.1 fun l hl => ?_
    exact (hcomm1 g (hTH hg) hne l hl x hx.2).symm

end Main

end CFSG.Quasithin.C58
