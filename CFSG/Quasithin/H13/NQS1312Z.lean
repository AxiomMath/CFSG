module

public import CFSG.Quasithin.H13.NQS1312Y
public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.EmptyFaithful.SBc17L45
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent1
public import CFSG.Quasithin.H13.NQS1312U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup_line {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem mem_normalizer_inf_centralizer_line {K W : Subgroup G} {g : G}
    (hK : g ∈ normalizer (K : Set G)) (hW : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer ((K ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ c : G, c ∈ centralizer (W : Set G) ↔ g * c * g⁻¹ ∈ centralizer (W : Set G) := by
    intro c
    simp only [mem_centralizer_iff]
    constructor
    · intro hc w hw
      have hw' : g⁻¹ * w * g ∈ W := by
        have := (mem_normalizer_iff.1 (inv_mem hW) w).1 hw
        simpa using this
      have h1 := hc _ hw'
      calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * w := by group
    · intro hc w hw
      have hw' : g * w * g⁻¹ ∈ W := (mem_normalizer_iff.1 hW w).1 hw
      have h1 := hc _ hw'
      have h2 : g * (w * c) * g⁻¹ = g * (c * w) * g⁻¹ := by
        calc g * (w * c) * g⁻¹ = g * w * g⁻¹ * (g * c * g⁻¹) := by group
          _ = g * c * g⁻¹ * (g * w * g⁻¹) := h1
          _ = g * (c * w) * g⁻¹ := by group
      simpa using h2
  rw [mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← key, ← mem_normalizer_iff.1 hK c]

omit [Finite G] in
theorem mem_normalizer_omegaV_line {K Q : Subgroup G} {g : G} (hK : g ∈ normalizer (K : Set G))
    (hQ : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G) :=
  A4.normalizer_le_normalizer_omegaOneCenterOf _
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_sup_line hK hQ))

omit [Finite G] in
theorem le_omegaOneCenterOf_line {V : Subgroup G} [IsElementaryAbelian 2 V] {K Q : Subgroup G}
    (hc : CharTwo (K ⊔ Q)) (hO : pCoreOf 2 (K ⊔ Q) ≤ Q) (hVQ : V ≤ Q)
    (hQC : Q ≤ centralizer (V : Set G)) : V ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) := by
  have hVO : V ≤ pCoreOf 2 (K ⊔ Q) := by
    refine fun v hv => hc ⟨mem_sup_right (hVQ hv), mem_centralizer_iff.2 fun q hq => ?_⟩
    exact (mem_centralizer_iff.1 (hQC (hO hq)) v hv).symm
  intro v hv
  refine Subgroup.subset_closure ⟨⟨hVO hv, mem_centralizer_iff.2 fun q hq => ?_⟩, ?_⟩
  · exact (mem_centralizer_iff.1 (hQC (hO hq)) v hv).symm
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) _ hv

theorem pCoreOf_le_centralizer_omegaV_line {K Q : Subgroup G}
    (hQK : Q ≤ normalizer (K : Set G)) :
    pCoreOf 2 K ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro v hv
  exact (mem_centralizer_iff.mp
    (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hv))
    q (SBc17.pCoreOf_le_pCoreOf_sup hQK hq)).symm

theorem le_pCoreOf_of_le_oTwoZIn (h36 : A36ForSQTK) {N K Y : Subgroup G} (hN : SQTKGroup ↥N)
    (hK : K ∈ cComp N) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hYZ : Y ≤ oTwoZIn K) (hY3 : ¬ 3 ∣ Nat.card Y) : Y ≤ pCoreOf 2 K := by
  intro y hy
  obtain ⟨hyK, hc⟩ := SBc17.mem_oTwoZIn_iff.1 (hYZ hy)
  have h3 : y ^ 3 ∈ pCoreOf 2 K := by
    refine SBc17.pow_three_mem_of_central hN (h36 _ (SQTKHyp.of_sqtkGroup ↥N hN)) hK hq hyK
      fun w hw => ?_
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⁅(⟨w, hw⟩ : ↥K), ⟨y, hyK⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hc _)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := (coe_mem_pCoreOf_iff_line K _).2 h1
    simpa [commutatorElement_def] using h2
  set yb : ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk ⟨y, hyK⟩ with hyb
  have hyb3 : yb ^ 3 = 1 := by
    rw [hyb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact (coe_mem_pCoreOf_iff_line K _).1 h3
  have hdvd : orderOf yb ∣ 3 := orderOf_dvd_of_pow_eq_one hyb3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
  · rw [orderOf_eq_one_iff, hyb, QuotientGroup.eq_one_iff] at h1
    exact (coe_mem_pCoreOf_iff_line K _).2 h1
  · exfalso
    apply hY3
    have h1 : orderOf yb ∣ orderOf (⟨y, hyK⟩ : ↥K) :=
      orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) _
    rw [h3', Subgroup.orderOf_mk] at h1
    have h2 := orderOf_dvd_natCard (⟨y, hy⟩ : ↥Y)
    rw [Subgroup.orderOf_mk] at h2
    exact h1.trans h2

theorem inf_centralizer_le_pCoreOf_line (h36 : A36ForSQTK) (hA3 : A3Orbits G) (h38 : A38ForSQTK)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hK3 : 3 ∣ Nat.card K)
    (hC1 : (K ⊔ pCoreOf 2 (L ⊔ T)) ⊓
      centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))) : Set G) ≤
        pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)) ⊔ oTwoZIn K)
    (hVV : V ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)))) :
    K ⊓ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))) : Set G) ≤
      pCoreOf 2 K := by
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hSQ : SQTKGroup ↥(lineN Φ) := isSQTKIn_lineN hH
  have hKN : K ∈ cComp (lineN Φ) := cComp_mem_of_subnormal isSubnormal_lineH hK
  have hKH : K ≤ lineH Φ := le_of_mem_cComp hK
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  have hxN := mem_lineN_of_tau_k2 (hLV hxL) hxτ
  have hxH := not_mem_lineH_of_tau_k2 (hLV hxL) hxτ
  obtain ⟨hk₁K, hNK⟩ := le_normalizer_of_commute_three hA3 h38 hSQ lineH_le_lineN
    lineN_le_normalizer_lineH hKN hKH hK3 hxN (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H hxH
  have hxQ : x ∈ normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (mem_sup_left hxL)
  have hxK : x ∈ normalizer (K : Set G) := hNK hxN
  have hxY := mem_normalizer_inf_centralizer_line hxK (mem_normalizer_omegaV_line hxK hxQ)
  have hk₁Y := mem_normalizer_inf_centralizer_line (Subgroup.le_normalizer hk₁K)
    (SBc17.le_normalizer_V K Q hk₁K)
  have hY3 : ¬ 3 ∣ Nat.card (K ⊓ centralizer (VK : Set G) : Subgroup G) := by
    intro h3
    have hk₁Y' := mem_of_commute_three (hSQ.1 3 Nat.prime_three (by norm_num)) lineH_le_lineN
      (inf_le_left.trans hKH) h3 hxN (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hxY hk₁Y hk₁H hxH
    have hk₁C : k₁ ∈ centralizer (V : Set G) :=
      Subgroup.centralizer_le hVV (Subgroup.mem_inf.1 hk₁Y').2
    have h1 : tau Φ ⟨k₁, hLV hk₁L⟩ = 1 := tau_eq_one_iff.2 hk₁C
    rw [hk₁τ] at h1
    exact kGL_spec.2 h1
  exact le_pCoreOf_of_le_oTwoZIn h36 hSQ hKN hq
    (fun y hy => SBc17.inf_centralizer_le_oTwoZIn hC1 hy) hY3

theorem ker_actOn_line {K Q : Subgroup G} (hQK : Q ≤ normalizer (K : Set G))
    (hle : K ⊓ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G) ≤ pCoreOf 2 K) :
    (SBc17.actOn (SBc17.le_normalizer_V K Q)).ker = CFSG.pCore 2 ↥K := by
  ext y
  rw [MonoidHom.mem_ker, SBc17.actOn_eq_one_iff, ← coe_mem_pCoreOf_iff_line]
  exact ⟨fun h => hle ⟨y.2, h⟩, fun h => pCoreOf_le_centralizer_omegaV_line hQK h⟩

omit [Finite G] in
theorem closure_orderOf_three_hat6 {X : Type} [Group X] [Finite X]
    (hHat : IsHat X (alternatingGroup (Fin 6))) :
    Subgroup.closure {y : X | orderOf y = 3} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have := R3c2.normal_closure_orderOf_eq (X := X) 3
  have hle := le_center_of_normal_ne_top hHat.1 hne
  obtain ⟨a, b, ha1, ha3, hb3, -, hba⟩ := FFC.threeRank2_hat hHat
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hac : a ∈ Subgroup.center X := hle (Subgroup.subset_closure hao)
  have hbc : b ∈ Subgroup.center X := hle (Subgroup.subset_closure hbo)
  have hz : Subgroup.zpowers a = Subgroup.center X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hac)
      (by rw [hHat.2.1, Nat.card_zpowers, hao])
  exact hba (hz ▸ hbc)

theorem false_of_hat6_line (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 6))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hSQ : SQTKGroup ↥(lineN Φ) := isSQTKIn_lineN hH
  have hKN : K ∈ cComp (lineN Φ) := cComp_mem_of_subnormal isSubnormal_lineH hK
  have hKH : K ≤ lineH Φ := le_of_mem_cComp hK
  have hKN' : K ≤ lineN Φ := le_of_mem_cComp hKN
  obtain ⟨-, -, x, hxL, -, hx3, -, -, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hxN := mem_lineN_of_tau_k2 (hLV hxL) hxτ
  have hxH := not_mem_lineH_of_tau_k2 (hLV hxL) hxτ
  have hX := R3c2.card_of_isHat_alt6 hHat
  have hX3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [hX]
    norm_num
  set ψ := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hψdef
  have hψ : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hker3 : ∀ y ∈ ψ.ker, orderOf y ≠ 3 := by
    intro y hy h3
    rw [hψdef, QuotientGroup.ker_mk'] at hy
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨y, hy⟩
    have h1 : y ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h3] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  have hθ : K ≤ thetaOf (lineN Φ) :=
    R3c2.le_thetaOf_of_surjection hKN' (perfect_of_mem_cComp hKN) hq ψ hψ hker3
      (closure_orderOf_three_hat6 hHat) hX3
  have hk : ∀ y : ↥K, ψ y = 1 → (⟨y, hKN' y.2⟩ : ↥(lineN Φ)) ∈ CFSG.pPrimeCore 3 ↥(lineN Φ) := by
    intro y hy
    rw [hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    have h1 : (y : G) ∈ pCoreOf 2 (lineN Φ) :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKN)
        ((coe_mem_pCoreOf_iff_line K y).2 hy)
    exact A318.pCore_two_le_pPrimeCore (by norm_num)
      ((coe_mem_pCoreOf_iff_line (lineN Φ) ⟨y, hKN' y.2⟩).1 h1)
  have hr : 2 ≤ CFSG.Open.pRank 3 K := by
    rw [R3c.pRank_three_eq_pCore_quotient K]
    exact (FFC.threeRank2_hat hHat).pRank_two_le
  obtain ⟨π, hπ⟩ := R3c2.exists_surjection_starImage hKN' ψ hψ hk
  have hcard := R3c2.card_quotient_hat hHat π hπ (R3c2.not_subsingleton_starImage hKN' (by omega))
  have hn2 : ¬ A318Case2 (starImage 3 (K.subgroupOf (lineN Φ))) := by
    rintro ⟨s, q, hmod, hPSL, -⟩
    exact R3c2.not_case2_of_card_hat6 hcard s q hmod hPSL
  have hn3 : ¬ A318Case3b (starImage 3 (K.subgroupOf (lineN Φ))) := by
    rintro ⟨s, q, y, hSL, -⟩
    exact R3c2.not_isSLEps3_of_card_hat6 hcard s q hSL
  have hKθ := R3c2.eq_thetaOf_of_a318_of_group hF318 h36 h38 hSQ hKN hq hr hn2 (fun _ => hn3) hθ
  have hxθ : x ∈ thetaOf (lineN Φ) := Subgroup.subset_closure ⟨hxN, hx3⟩
  rw [← hKθ] at hxθ
  exact hxH (hKH hxθ)

theorem false_of_c27Hat6_line (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    {R M W : Subgroup G} (h : SBc17.C27Hat6 (lineH Φ) R M K W) : False :=
  false_of_hat6_line hF318 h36 h38 hH hU3 hF hΦLs hK hq h.1.2.1

theorem false_of_autOn_statedSL_line
    (h1332 : Stmt13_3_2) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hA3 : A3Orbits G) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G))
    (hC1 : (K ⊔ pCoreOf 2 (L ⊔ T)) ⊓
      centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))) : Set G) ≤
        pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)) ⊔ oTwoZIn K)
    {d : ℕ} (hd : 3 ≤ d) (hd3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)))
    (hS : ∀ (X : Type) [Group X] [Finite X], IsPSL d 2 1 X → A318Exclusion X)
    (e : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, hVQ, -, -, -, -, -, hTC, -, -⟩ := id hF
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hyp : HypC23 (lineH Φ) Q (lineH Φ ⊓ normalizer (L : Set G)) :=
    hypC23_line h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  have hKQc : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hKc hQp hQK
  have hO : pCoreOf 2 (K ⊔ Q) ≤ Q :=
    c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hyp.radical hK hq hQK)
  have hVV : V ≤ VK := le_omegaOneCenterOf_line hKQc hO hVQ hQC
  set α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) :=
    e.toMonoidHom.comp (SBc17.actOn hKV) with hα
  have hαs : Function.Surjective α := e.surjective.comp (SBc17.actOn_surjective hKV)
  have h3X : 3 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL d (ZMod 2)).toEquiv]
    exact hd3
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3X
  have hK3 : 3 ∣ Nat.card K := three_dvd_card_of_surjective α hαs hg
  have hle := inf_centralizer_le_pCoreOf_line h36 hA3 h38 hH hU3 hF hΦLs hK hq hK3 hC1 hVV
  have hker : α.ker = CFSG.pCore 2 ↥K := by
    rw [hα, MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact ker_actOn_line hQK hle
  obtain ⟨e'⟩ := quotPCore_equiv_of_surjective hαs hker
  exact false_of_exclusion_line hF318 h36 h38 hH hU3 hF hΦLs hK hq (MulEquiv.refl _)
    (hS _ (R3c2.isPSL_two_of_statedSL hd e'))

theorem false_of_c27L45_line
    (h1332 : Stmt13_3_2) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hA3 : A3Orbits G) (hKF : KnownFacts15122Types) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G))
    (hC1 : (K ⊔ pCoreOf 2 (L ⊔ T)) ⊓
      centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))) : Set G) ≤
        pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)) ⊔ oTwoZIn K)
    {R M : Subgroup G}
    (h : SBc17.C27L45 (lineH Φ) R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))) :
    False := by
  obtain ⟨he | he, -, -⟩ := h
  · obtain ⟨e⟩ := he
    exact false_of_autOn_statedSL_line h1332 hF318 h36 h38 hA3 hH hU3 hF hΦLs hΦN hΦT hK hq hQK
      hC1 (by norm_num) (by rw [SBc17.card_sl_four]; norm_num) hKF.l42 e
  · obtain ⟨e⟩ := he
    exact false_of_autOn_statedSL_line h1332 hF318 h36 h38 hA3 hH hU3 hF hΦLs hΦN hΦT hK hq hQK
      hC1 (by norm_num) (by rw [SBc17.card_sl_five]; norm_num) hKF.l52 e

end CFSG.Quasithin.H13.U3.NLine
