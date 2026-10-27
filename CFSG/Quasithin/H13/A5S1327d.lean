module

public import CFSG.Quasithin.H13.A5S1327c
public import CFSG.Quasithin.H13.A5S1324a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem comm_c3p_of_not_InK4 : ∀ σ : Equiv.Perm (Fin 5), InD σ → ¬ InK4 σ →
    σ * c3p * σ⁻¹ * c3p⁻¹ ≠ 1 ∧ (σ * c3p * σ⁻¹ * c3p⁻¹) ^ 3 = 1 := by
  decide +kernel

theorem InK4_conj_of_InD : ∀ σ τ : Equiv.Perm (Fin 5), InD σ → InK4 τ → InK4 (σ * τ * σ⁻¹) := by
  decide +kernel

theorem InK4_of_comm_pb : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ * pb = pb * σ → InK4 σ := by
  decide +kernel

theorem perm3_cube_sq : ∀ σ : Equiv.Perm (Fin 3), (σ ^ 3) ^ 2 = 1 := by decide

theorem perm3_comm : ∀ σ τ : Equiv.Perm (Fin 3), σ * τ = τ * σ → σ ^ 2 = 1 → τ ^ 3 = 1 →
    τ ≠ 1 → σ = 1 := by
  decide

theorem perm3_cyclic : ∀ α β : Equiv.Perm (Fin 3), α ≠ 1 → α ^ 3 = 1 → β ^ 3 = 1 →
    β = 1 ∨ β = α ∨ β = α ^ 2 := by
  decide

theorem perm3_exists_sq_ne_one : ∃ γ : Equiv.Perm (Fin 3), γ ^ 2 ≠ 1 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩

theorem eq_one_of_pow_coprime {X : Type*} [Monoid X] {x : X} {m n : ℕ} (hm : x ^ m = 1)
    (hn : x ^ n = 1) (h : Nat.Coprime m n) : x = 1 := by
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
  rw [h.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem coprime_two_pow_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b a : ℕ) :
    Nat.Coprime (2 ^ b) (p ^ a) :=
  Nat.Coprime.pow b a ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem mem_of_two_pow_of_prime_pow {X : Type*} [Group X] {N : Subgroup X} {x : X}
    {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx2 : x ^ 2 ^ b = 1) (hxp : x ^ p ^ a ∈ N) :
    x ∈ N := by
  have hco : Nat.Coprime (p ^ a) (orderOf x) := by
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx2)
    rw [hc]
    exact (coprime_two_pow_prime_pow hp hp2 c a).symm
  exact (Subgroup.zpowers_le.mpr hxp) (A4.mem_zpowers_pow_of_coprime hco)

theorem perm3_cube_of_prime_pow {x : Equiv.Perm (Fin 3)} {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : x ^ p ^ a = 1) : x ^ 3 = 1 := by
  refine eq_one_of_pow_coprime (m := 2) (n := p ^ a) (perm3_cube_sq x) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  · exact Nat.Coprime.pow_right a ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem isSylowTwoOf_sup_of_two_elements {X : Type*} [Group X] [Finite X] {K R : Subgroup X}
    (hR : IsPGroup 2 R) (hRK : R ≤ Subgroup.normalizer (K : Set X))
    (h : ∀ k ∈ K, (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ R) : IsSylowTwoOf R (K ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPKR hP hRP => ?_⟩
  intro x hx
  have hx' : x ∈ ((K ⊔ R : Subgroup X) : Set X) := hPKR hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K R hRK] at hx'
  obtain ⟨k, hk, r, hr, rfl⟩ := hx'
  have hkP : k ∈ P := by
    have e : k = (k * r) * r⁻¹ := by group
    rw [e]
    exact P.mul_mem hx (P.inv_mem (hRP hr))
  obtain ⟨b, hb⟩ := hP ⟨k, hkP⟩
  have hb' : k ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  exact R.mul_mem (h k hk ⟨b, hb'⟩) hr

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem mem_R1_of_mem_pPrimeCore (H : Subgroup G) {w : ↥(S.H0 H)}
    (hw : w ∈ CFSG.pPrimeCore 3 ↥(S.H0 H)) (hwT : (w : G) ∈ T) : (w : G) ∈ S.R1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_c3p
  have hgH0 : (g : G) ∈ S.H0 H := Subgroup.mem_sup_left (S.L1_le_borel_L hgL1)
  set l0 : ↥(S.H0 H) := ⟨g, hgH0⟩ with hl0
  have hn : (CFSG.pPrimeCore 3 ↥(S.H0 H)).Normal := inferInstance
  have hcN : w * l0 * w⁻¹ * l0⁻¹ ∈ CFSG.pPrimeCore 3 ↥(S.H0 H) := by
    have h1 : l0 * w⁻¹ * l0⁻¹ ∈ CFSG.pPrimeCore 3 ↥(S.H0 H) :=
      hn.conj_mem _ (Subgroup.inv_mem _ hw) l0
    have e : w * l0 * w⁻¹ * l0⁻¹ = w * (l0 * w⁻¹ * l0⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hw h1
  have hco : Nat.Coprime 3 (orderOf (w * l0 * w⁻¹ * l0⁻¹)) := by
    have h1 := orderOf_dvd_natCard (⟨_, hcN⟩ : ↥(CFSG.pPrimeCore 3 ↥(S.H0 H)))
    rw [Subgroup.orderOf_mk] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  set t : ↥(Subgroup.normalizer (V : Set G)) := ⟨w, S.frame.T_le hwT⟩ with ht
  have hcG : ((w * l0 * w⁻¹ * l0⁻¹ : ↥(S.H0 H)) : G) =
      ((t * g * t⁻¹ * g⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) := rfl
  by_contra hR
  have hK : ¬ InK4 (S.frame.ρ t) := fun h => hR ((S.mem_R1 hwT).2 h)
  obtain ⟨hne, hcube⟩ := comm_c3p_of_not_InK4 _ (S.frame.T_D t hwT) hK
  have hρ : S.frame.ρ (t * g * t⁻¹ * g⁻¹) =
      S.frame.ρ t * c3p * (S.frame.ρ t)⁻¹ * c3p⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg]
  have h3 : orderOf (S.frame.ρ (t * g * t⁻¹ * g⁻¹)) = 3 := by
    rw [hρ]
    exact orderOf_eq_prime hcube hne
  have hdvd : orderOf (S.frame.ρ (t * g * t⁻¹ * g⁻¹)) ∣ orderOf (w * l0 * w⁻¹ * l0⁻¹) := by
    have h1 := orderOf_map_dvd S.frame.ρ (t * g * t⁻¹ * g⁻¹)
    rwa [← Subgroup.orderOf_coe (t * g * t⁻¹ * g⁻¹), ← hcG, Subgroup.orderOf_coe] at h1
  rw [h3] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hco hdvd

theorem mem_pPrimeCore_of_threeTop {H : Subgroup G} (h3 : ThreeTop (S.H0 H)) {x : G}
    (hx : x ∈ oTwoUpper H) {b : ℕ} (hx2 : x ^ 2 ^ b = 1) :
    ∃ w : ↥(S.H0 H), w ∈ CFSG.pPrimeCore 3 ↥(S.H0 H) ∧ (w : G) = x := by
  set N3 := CFSG.pPrimeCore 3 ↥(S.H0 H) with hN3
  set φ := QuotientGroup.mk' N3 with hφ
  have hle : oTwoUpper H ≤
      ((oTwoUpper (⊤ : Subgroup (↥(S.H0 H) ⧸ N3))).comap φ).map (S.H0 H).subtype := by
    show Subgroup.closure {x | x ∈ H ∧ Odd (orderOf x)} ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyH, hyo⟩
    have hyH0 : y ∈ S.H0 H := Subgroup.mem_sup_right hyH
    refine ⟨⟨y, hyH0⟩, ?_, rfl⟩
    show φ ⟨y, hyH0⟩ ∈ oTwoUpper ⊤
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_
    have h1 := orderOf_map_dvd φ ⟨y, hyH0⟩
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hyo h1
  obtain ⟨w, hw, rfl⟩ := hle hx
  refine ⟨w, ?_, rfl⟩
  obtain ⟨n, hn⟩ := h3 ⟨φ w, hw⟩
  have h1 : φ w ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hw2 : w ^ 2 ^ b = 1 := Subtype.ext (by simpa using hx2)
  have h2 : φ w ^ 2 ^ b = 1 := by rw [← map_pow, hw2, map_one]
  have h4 := eq_one_of_pow_coprime h2 h1
    (coprime_two_pow_prime_pow Nat.prime_three (by norm_num) b n)
  rwa [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4

theorem le_R1_of_threeTop {H : Subgroup G} (hTH : T ≤ H) (h3 : ThreeTop (S.H0 H)) :
    pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1 := by
  intro x hx
  have hxT : x ∈ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH) hx.1
  obtain ⟨b, hb⟩ := S.isPGroup_T ⟨x, hxT⟩
  have hb' : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  obtain ⟨w, hw, hwx⟩ := S.mem_pPrimeCore_of_threeTop h3 hx.2 hb'
  rw [← hwx] at hxT ⊢
  exact S.mem_R1_of_mem_pPrimeCore H hw hxT

theorem normalizer_thompsonJ_Q_le :
    Subgroup.normalizer (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hQ2 : IsPGroup 2 Q := S.isPGroup_T.to_le inf_le_left
  have hVQ : V ≤ Q := le_inf S.V_le_T fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian Q
  have hAJ : A ≤ thompsonJ Q := GammaExtra.le_thompsonJ hA
  have hJne : thompsonJ Q ≠ ⊥ := by
    intro hJ
    have hA1 : A = ⊥ := le_bot_iff.mp (hAJ.trans hJ.le)
    have h16 := hA.2.2 V hVQ S.elemAbelian_V
    rw [S.card_V, hA1, Subgroup.card_bot] at h16
    omega
  have hLT : L ⊔ T ≤ Subgroup.normalizer (thompsonJ Q : Set G) := by
    refine le_trans ?_ (GammaExtra.normalizer_le_normalizer_thompsonJ Q)
    rw [hQ, S.cT]
    exact le_normalizer_pCoreOf 2 _
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨thompsonJ Q, hJne, GammaExtra.isPGroup_thompsonJ hQ2, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (thompsonJ Q : Set G)))
  have h := S.uniqueM.2 M' ⟨hM', hLT.trans hM'le⟩
  exact h ▸ hM'le

theorem le_M_of_minParabolic (h311 : Theorem311Stmt)
    {X P H' : Subgroup G} (hsylX : IsSylowTwoOf S.R1 X)
    (hXM : ¬ X ≤ Subgroup.normalizer (L : Set G))
    (hmin : ∀ Y : Subgroup G, S.R1 ≤ Y → Y < X → Y ≤ Subgroup.normalizer (L : Set G))
    (hFX : CharTwo X) (hXZ : ¬ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolvX : Group.IsSolvable ↥X) (hSQTX : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q X ≤ 2)
    (hPX : P ≤ oTwoUpper X) (hPR : P ≤ S.R1) (hH' : InH T H')
    (hH'u : ∃ N : Subgroup G, IsUniqueMaxOver H' T N)
    (h2 : ∀ k ∈ oTwoUpper H', (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ P) :
    H' ≤ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hR1T : S.R1 ≤ T := S.R1_le_T
  have hR12 : IsPGroup 2 S.R1 := S.isPGroup_T.to_le hR1T
  have hR1M : S.R1 ≤ M := hR1T.trans S.T_le_NL
  have hQ2 : IsPGroup 2 Q := S.isPGroup_T.to_le inf_le_left
  obtain ⟨-, hJR1, hBR1⟩ := S.lemma_13_2_4_one
  have hNJ : Subgroup.normalizer (thompsonJ S.R1 : Set G) ≤ M := by
    rw [hJR1]
    exact S.normalizer_thompsonJ_Q_le
  have hXnorm : ¬ X ≤ Subgroup.normalizer (S.R1 : Set G) := fun h =>
    hXM (h.trans ((GammaExtra.normalizer_le_normalizer_thompsonJ S.R1).trans hNJ))
  have hMPX : MinParabolic X S.R1 (X ⊓ M) := by
    refine Setup.minParabolic_of_uniqueMax hsylX hXnorm (le_inf hsylX.1 hR1M)
      (lt_of_le_of_ne inf_le_left fun h => hXM (h ▸ inf_le_right)) fun Y hR1Y hYX => ?_
    exact le_inf hYX.le (hmin Y hR1Y hYX)
  have hZR1 : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter S.R1 := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨⟨hzT, hzC⟩, hz2⟩
    refine Subgroup.subset_closure ⟨⟨(S.mem_R1 hzT).2 ?_, ?_⟩, hz2⟩
    · obtain ⟨g₀, hg₀T, hg₀σ⟩ := S.frame.K4_T pb (Or.inr (Or.inr (Or.inl rfl)))
      have hc : z * (g₀ : G) = g₀ * z := (Subgroup.mem_centralizer_iff.mp hzC g₀ hg₀T).symm
      have hc' : (⟨z, S.frame.T_le hzT⟩ : ↥(Subgroup.normalizer (V : Set G))) * g₀ =
          g₀ * ⟨z, S.frame.T_le hzT⟩ := Subtype.ext hc
      refine InK4_of_comm_pb _ (S.frame.T_D _ hzT) ?_
      have := congrArg S.frame.ρ hc'
      rwa [map_mul, map_mul, hg₀σ] at this
    · exact Subgroup.centralizer_le hR1T hzC
  obtain ⟨-, hWel, hWred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsylX hFX hZR1
  set W := conjClosure (quasithinOmegaOneCenter T) X with hWdef
  have hXW : ¬ X ≤ Subgroup.centralizer (W : Set G) := fun h =>
    hXZ (h.trans (Subgroup.centralizer_le (le_conjClosure _ _)))
  have hJW : ¬ thompsonJ S.R1 ≤ Subgroup.centralizer (W : Set G) := by
    intro hJ
    have h1 := (hMPX.le_pCoreOf_iff_le_centralizer hWred hXW (thompsonJ S.R1)).mpr
      (le_inf (thompsonJ_le_self _) hJ)
    have h2 : thompsonJ S.R1 = thompsonJ (pCoreOf 2 X) :=
      thompsonJ_eq_of_le h1 (pCoreOf_two_le_of_isSylowTwoOf hsylX)
    have h3 : X ≤ Subgroup.normalizer (thompsonJ S.R1 : Set G) := by
      rw [h2]
      exact (le_normalizer_pCoreOf 2 X).trans
        (GammaExtra.normalizer_le_normalizer_thompsonJ (pCoreOf 2 X))
    exact hXM (h3.trans hNJ)
  obtain ⟨-, -, hBsyl, -, -⟩ := E2_3_two_of_isSolvable hWel hMPX hsolvX hSQTX hWred hJW
  rw [twoResidual_eq_oTwoUpper'] at hBsyl
  have hPB : P ≤ baum S.R1 := by
    have hBR : baum S.R1 ≤ S.R1 := inf_le_left
    have hmax := (A4.isSylowTwoOf_iff_maximal.mp hBsyl).2.2 (P ⊔ baum S.R1)
      (sup_le (hPX.trans le_sup_left) le_sup_right) (hR12.to_le (sup_le hPR hBR)) le_sup_right
    exact le_sup_left.trans hmax
  have hPQ : P ≤ Q := by
    rw [hBR1] at hPB
    exact hPB.trans inf_le_left
  have hQH' : Q ≤ Subgroup.normalizer (oTwoUpper H' : Set G) :=
    (inf_le_left.trans hH'.1).trans (le_normalizer_oTwoUpper H')
  have hsylQ : IsSylowTwoOf Q (oTwoUpper H' ⊔ Q) :=
    isSylowTwoOf_sup_of_two_elements hQ2 hQH' fun k hk hk2 => hPQ (h2 k hk hk2)
  rw [hQ, S.cT] at hsylQ
  obtain ⟨R0, hR0, hR0R, hN⟩ := h311 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow
    (L ⊔ T) H' (pCoreOf 2 (L ⊔ T)) ⟨le_sup_right, S.R_ne_bot⟩ hH' hH'u
    S.R_ne_bot S.pCoreOf_LT_le_T hsylQ (le_normalizer_pCoreOf 2 _)
  have hR02 : IsPGroup 2 R0 := (pCoreOf_isPGroup 2 _).to_le hR0R
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨R0, hR0, hR02, rfl⟩ : IsTwoLocal (Subgroup.normalizer (R0 : Set G)))
  have hM'M := S.uniqueM.2 M' ⟨hM', (le_sup_left.trans hN).trans hM'le⟩
  have hNR0 : Subgroup.normalizer (R0 : Set G) ≤ M := by
    rw [hM, ← hM'M]
    exact hM'le
  exact (le_sup_right.trans hN).trans hNR0

theorem false_of_P_le_R1 (h331 : Stmt3_3_1)
    (h311 : Theorem311Stmt) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hPR' : pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  set U := S.UH H with hUdef
  set LH := oTwoUpper H with hLH
  set P := pCoreOf 2 H ⊓ LH with hP
  have hLHH : LH ≤ H := oTwoUpper_le H
  have hHLH : H ≤ Subgroup.normalizer (LH : Set G) := le_normalizer_oTwoUpper H
  have hHeq : H = LH ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
  have hTLH : T ≤ Subgroup.normalizer (LH : Set G) := hTH.trans hHLH
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hZU : quasithinOmegaOneCenter T ≤ U := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (U : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  have hUO2 : U ≤ pCoreOf 2 H := hUO.trans inf_le_left
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_pCoreOf 2 H hh, hHLH hh⟩
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hLHM : ¬ LH ≤ M := fun h => hH.2.1 (hHeq ▸ sup_le h S.T_le_NL)
  obtain ⟨p, hp, hp2, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  have h2P : ∀ k ∈ LH, (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ P := by
    rintro k hk ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hpow k hk
    exact ⟨mem_of_two_pow_of_prime_pow hp hp2 hb ha, hk⟩
  have hPR : P ≤ S.R1 := hPR'
  obtain ⟨eS3⟩ := hS3
  have e3 : ↥(autI hUel H) ≃* Equiv.Perm (Fin 3) := eS3
  set f : ↥H →* MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel) :=
    convHom hUel H hHN with hf
  have hfmem : ∀ h : ↥H, f h ∈ autI hUel H := fun h => convI_mem_autI hUel h.2 (hHN h.2)
  set F : ↥H →* Equiv.Perm (Fin 3) :=
    e3.toMonoidHom.comp (f.codRestrict (autI hUel H) hfmem) with hFdef
  have hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (U : Set G) := by
    intro h
    have e1 : F h = 1 ↔ f h = 1 := by
      have : F h = e3 (f.codRestrict (autI hUel H) hfmem h) := rfl
      rw [this, MulEquiv.map_eq_one_iff]
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    rw [e1]
    have : f h = convI hUel ⟨h, hHN h.2⟩ := rfl
    rw [this]
    exact convI_eq_one_iff hUel _
  have hFsurj : Function.Surjective F := by
    intro σ
    obtain ⟨g, hgH, hg⟩ := (mem_autI hUel).1 (e3.symm σ).2
    refine ⟨⟨g, hgH⟩, ?_⟩
    have e : f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩ = e3.symm σ := by
      apply Subtype.ext
      exact hg
    have : F ⟨g, hgH⟩ = e3 (f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩) := rfl
    rw [this, e, MulEquiv.apply_symm_apply]
  have hFT : ∀ (t : G) (ht : t ∈ T), F ⟨t, hTH ht⟩ ^ 2 = 1 := by
    intro t ht
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨t, ht⟩
    have hb' : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ b = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hb)
    refine perm3_sq_of_two_pow (k := b) ?_
    rw [← map_pow, hb', map_one]
  have hFL : ∀ (k : G) (hk : k ∈ LH), F ⟨k, hLHH hk⟩ ^ 3 = 1 := by
    intro k hk
    obtain ⟨a, ha⟩ := hpow k hk
    refine perm3_cube_of_prime_pow (a := a) hp hp2 ?_
    rw [← map_pow]
    refine (hF1 _).2 ?_
    exact hO2U ha
  have hFne : ∃ (l : G) (hl : l ∈ LH), F ⟨l, hLHH hl⟩ ≠ 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨γ, hγ⟩ := perm3_exists_sq_ne_one
    obtain ⟨⟨h, hh⟩, hhγ⟩ := hFsurj γ
    have hh' : h ∈ ((LH ⊔ T : Subgroup G) : Set G) := by rw [← hHeq]; exact hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left LH T hTLH] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := hh'
    have e : (⟨k * t, hh⟩ : ↥H) = ⟨k, hLHH hk⟩ * ⟨t, hTH ht⟩ := rfl
    rw [e, map_mul, hne k hk, one_mul] at hhγ
    exact hγ (hhγ ▸ hFT t ht)
  have hcover : ∀ Y : Subgroup G, Y ≤ LH → ¬ Y ≤ Subgroup.centralizer (U : Set G) →
      LH ≤ Y ⊔ (H ⊓ Subgroup.centralizer (U : Set G)) := by
    intro Y hYL hYU
    obtain ⟨y, hyY, hyU⟩ := IsConcreteLE.not_le_iff_exists.1 hYU
    have hyL : y ∈ LH := hYL hyY
    have hy1 : F ⟨y, hLHH hyL⟩ ≠ 1 := fun h => hyU ((hF1 _).1 h)
    intro k hk
    have hmem : ∀ (c : G) (hc : c ∈ Y), F ⟨c, hLHH (hYL hc)⟩ = F ⟨k, hLHH hk⟩ →
        k ∈ Y ⊔ (H ⊓ Subgroup.centralizer (U : Set G)) := by
      intro c hc hck
      have hcH : c ∈ H := hLHH (hYL hc)
      have hck' : c⁻¹ * k ∈ H ⊓ Subgroup.centralizer (U : Set G) := by
        refine ⟨H.mul_mem (H.inv_mem hcH) (hLHH hk), ?_⟩
        have e : (⟨c⁻¹ * k, H.mul_mem (H.inv_mem hcH) (hLHH hk)⟩ : ↥H) =
            (⟨c, hcH⟩ : ↥H)⁻¹ * ⟨k, hLHH hk⟩ := rfl
        refine (hF1 ⟨c⁻¹ * k, H.mul_mem (H.inv_mem hcH) (hLHH hk)⟩).1 ?_
        rw [e, map_mul, map_inv, ← hck, inv_mul_cancel]
      have e : k = c * (c⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hc hck'
    rcases perm3_cyclic _ _ hy1 (hFL y hyL) (hFL k hk) with h1 | h1 | h1
    · exact Subgroup.mem_sup_right ⟨hLHH hk, (hF1 _).1 h1⟩
    · exact hmem y hyY h1.symm
    · refine hmem (y ^ 2) (Y.pow_mem hyY 2) ?_
      rw [h1, ← map_pow]
      rfl
  have hR1T : S.R1 ≤ T := S.R1_le_T
  have hTR1 : T ≤ Subgroup.normalizer (S.R1 : Set G) := by
    have key : ∀ t ∈ T, ∀ x ∈ S.R1, t * x * t⁻¹ ∈ S.R1 := by
      intro t ht x hx
      have hxT : x ∈ T := hR1T hx
      have htxT : t * x * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht)
      refine (S.mem_R1 htxT).2 ?_
      have e : (⟨t * x * t⁻¹, S.frame.T_le htxT⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨t, S.frame.T_le ht⟩ * ⟨x, S.frame.T_le hxT⟩ * (⟨t, S.frame.T_le ht⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact InK4_conj_of_InD _ _ (S.frame.T_D _ ht) ((S.mem_R1 hxT).1 hx)
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hR12 : IsPGroup 2 S.R1 := S.isPGroup_T.to_le hR1T
  have hR1LH : S.R1 ≤ Subgroup.normalizer (LH : Set G) := hR1T.trans hTLH
  have hR1M : S.R1 ≤ M := hR1T.trans S.T_le_NL
  set X := LH ⊔ S.R1 with hXdef
  have hXH : X ≤ H := sup_le hLHH (hR1T.trans hTH)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hHeq]
    refine sup_le ?_ ?_
    · intro k hk
      exact (le_sup_left : LH ≤ X).trans Subgroup.le_normalizer hk
    · intro t ht
      have fwd : ∀ s ∈ T, ∀ x ∈ X, s * x * s⁻¹ ∈ X := by
        intro s hs x hx
        have hle : X ≤ X.comap (MulAut.conj s).toMonoidHom := by
          refine sup_le (fun k hk => ?_) (fun r hr => ?_)
          · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTLH hs) k).mp hk)
          · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hTR1 hs) r).mp hr)
        have := hle hx
        simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fwd t ht x, fun hx => ?_⟩
      have := fwd t⁻¹ (T.inv_mem ht) _ hx
      simpa [mul_assoc] using this
  have hsylX : IsSylowTwoOf S.R1 X :=
    isSylowTwoOf_sup_of_two_elements hR12 hR1LH fun k hk hk2 => hPR (h2P k hk hk2)
  have hXM : ¬ X ≤ M := fun h => hLHM (le_sup_left.trans h)
  have hmin : ∀ Y : Subgroup G, S.R1 ≤ Y → Y < X → Y ≤ M := by
    intro Y hR1Y hYX
    by_cases hYU : Y ⊓ LH ≤ Subgroup.centralizer (U : Set G)
    · intro y hy
      have hy' : y ∈ ((LH ⊔ S.R1 : Subgroup G) : Set G) := hYX.le hy
      rw [Subgroup.coe_mul_of_right_le_normalizer_left LH S.R1 hR1LH] at hy'
      obtain ⟨k, hk, r, hr, rfl⟩ := hy'
      have hkY : k ∈ Y := by
        have e : k = (k * r) * r⁻¹ := by group
        rw [e]
        exact Y.mul_mem hy (Y.inv_mem (hR1Y hr))
      have hkJ : k ∈ kerIn (H ⊓ M) H :=
        hMP.inf_centralizer_le_kerIn hUred hHU ⟨hLHH hk, hYU ⟨hkY, hk⟩⟩
      exact M.mul_mem (kerIn_le hkJ).2 (hR1M hr)
    · exfalso
      have h1 := hcover (Y ⊓ LH) inf_le_right hYU
      have h2 : twoResidual H ≤ (Y ⊓ LH) ⊔ kerIn (H ⊓ M) H := by
        rw [twoResidual_eq_oTwoUpper']
        exact h1.trans (sup_le_sup_left (hMP.inf_centralizer_le_kerIn hUred hHU) _)
      have h3 := hMP.twoResidual_le_sup_pCoreOf hsolv (inf_le_right.trans hLHH) h2
      rw [twoResidual_eq_oTwoUpper'] at h3
      have hLY : LH ≤ Y := by
        intro k hk
        have hk' : k ∈ (((Y ⊓ LH) ⊔ pCoreOf 2 H : Subgroup G) : Set G) := h3 hk
        rw [Subgroup.coe_mul_of_left_le_normalizer_right (Y ⊓ LH) (pCoreOf 2 H)
          ((inf_le_right.trans hLHH).trans (le_normalizer_pCoreOf 2 H))] at hk'
        obtain ⟨y, hy, q, hq, rfl⟩ := hk'
        have hqL : q ∈ LH := by
          have e : q = y⁻¹ * (y * q) := by group
          rw [e]
          exact LH.mul_mem (LH.inv_mem hy.2) hk
        exact Y.mul_mem hy.1 (hR1Y (hPR ⟨hq, hqL⟩))
      exact hYX.not_ge (sup_le hLY hR1Y)
  have hFX : CharTwo X :=
    CharTwo.of_normal hF hXH ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX)
  have hXZ : ¬ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun h =>
    hHZ (hHeq ▸ sup_le (le_sup_left.trans h) (T_le_centralizer_omegaOneCenter T))
  have hsolvX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXH)
  have hSQTX : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q X ≤ 2 := fun q hq hq2 =>
    (CFSG.SectionRank.pRank_mono hq.one_lt hXH).trans (hSQT q hq hq2)
  have hLX : LH ≤ oTwoUpper X := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (Subgroup.subset_closure hx)) hx.2
  exact hH.2.1 (S.le_M_of_minParabolic h311 hsylX hXM hmin hFX hXZ hsolvX hSQTX
    (inf_le_right.trans hLX) hPR hH.1 ⟨_, hMP.uniqueMax⟩ h2P)

theorem not_threeTop (h331 : Stmt3_3_1) (h311 : Theorem311Stmt)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    ¬ ThreeTop (S.H0 H) := fun h3 =>
  S.false_of_P_le_R1 h331 h311 hH hHZ hsolv hS3 (S.le_R1_of_threeTop hH.1.1 h3)

end Setting

theorem lemma13213_of (h331 : Stmt3_3_1) (h311 : Theorem311Stmt) :
    Lemma13213 := fun _ _ _ _ _ _ S _ hH hHZ hsolv hS3 =>
  S.not_threeTop h331 h311 hH hHZ hsolv hS3

theorem stmt13_2_7_of_rest_ofNoN
    (h331 : Stmt3_3_1) (h311 : Theorem311Stmt) (h523 : Stmt5_2_3) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (hE22 : E2.E22StatementNoN) (hRes : Res1328a) (hS2 : CaseS2_1327)
    (hfin : Final1327) : Stmt13_2_7 :=
  stmt13_2_7_of_parts_ofNoN h331 h523 h1222 hE22 hRes (lemma13213_of h331 h311) hS2
    (o2H0One1327_of h331 h5172) hfin

end CFSG.Quasithin.H13.A5
