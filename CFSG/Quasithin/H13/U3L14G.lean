module

public import CFSG.Quasithin.SteinbergBMCoreQuotientCenterOdd
public import CFSG.Quasithin.EmptyFaithful.S152UGen2
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.H13.U3L14Q

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneCenterOf_le_centralizer (Y : Subgroup G) :
    omegaOneCenterOf Y ≤ centralizer (Y : Set G) := by
  unfold omegaOneCenterOf omegaOneOf
  rw [closure_le]
  exact fun _ hx => hx.1.2

theorem le_centralizer_of_normal_of_pow_two {K W N : Subgroup G}
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKp : K = oTwoUpper K)
    (hKW : K ≤ normalizer (W : Set G)) (hO : pCoreOf 2 K ≤ centralizer (W : Set G))
    (hNK : N ≤ K) (hKN : K ≤ normalizer (N : Set G))
    (h2 : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k ∈ centralizer (W : Set G)) :
    N ≤ centralizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set ρ := InternalSec.autOnHom hKW with hρ
  have hker : ∀ x : ↥K, x ∈ CFSG.pCore 2 ↥K → ρ x = 1 := fun x hx =>
    (InternalSec.mem_ker_autOnHom hKW x).2 (hO (coe_mem_pCoreOf_iff.2 hx))
  have hNn : (N.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hN'n : ((N.subgroupOf K).map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN'n with htop | hcen
  ·
    have hall : ∀ x ∈ K, ∃ j : ℕ, x ^ 2 ^ j ∈ centralizer (W : Set G) := by
      intro x hx
      have hmem : π ⟨x, hx⟩ ∈ (N.subgroupOf K).map π := htop ▸ mem_top _
      obtain ⟨n, hnN, hne⟩ := hmem
      obtain ⟨j, hj⟩ := h2 n (mem_subgroupOf.mp hnN)
      refine ⟨j, ?_⟩
      have h1 : n⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.mp hne
      have h3 : ρ ⟨x, hx⟩ = ρ n := by
        have h4 := hker _ h1
        rw [map_mul, map_inv, inv_mul_eq_one] at h4
        exact h4.symm
      have h5 : ρ (n ^ 2 ^ j) = 1 := (InternalSec.mem_ker_autOnHom hKW _).2 (by simpa using hj)
      have h6 : ρ (⟨x, hx⟩ ^ 2 ^ j) = 1 := by rw [map_pow, h3, ← map_pow, h5]
      simpa using (InternalSec.mem_ker_autOnHom hKW _).1 h6
    exact hNK.trans (hKp.le.trans (oTwoUpper_le_of_pow_mem hall))
  ·
    intro n hn
    have hnK := hNK hn
    have hz : π ⟨n, hnK⟩ ∈ center (↥K ⧸ CFSG.pCore 2 ↥K) := hcen ⟨⟨n, hnK⟩, hn, rfl⟩
    obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hKq
    set m := Nat.card (center (↥K ⧸ CFSG.pCore 2 ↥K)) with hm
    have hpm : π ⟨n, hnK⟩ ^ m = 1 := by
      have h := congrArg Subtype.val
        (pow_card_eq_one' (x := (⟨_, hz⟩ : ↥(center (↥K ⧸ CFSG.pCore 2 ↥K)))))
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      exact h
    have hm' : (⟨n, hnK⟩ : ↥K) ^ m ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hpm
    have hρm : ρ ⟨n, hnK⟩ ^ m = 1 := by rw [← map_pow]; exact hker _ hm'
    obtain ⟨k, hk⟩ := h2 n hn
    have hρk : ρ ⟨n, hnK⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      exact (InternalSec.mem_ker_autOnHom hKW _).2 (by simpa using hk)
    have hcop : Nat.Coprime m (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    have hord : orderOf (ρ ⟨n, hnK⟩) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hρm)
        (orderOf_dvd_of_pow_eq_one hρk)
    have := (InternalSec.mem_ker_autOnHom hKW ⟨n, hnK⟩).1 (orderOf_eq_one_iff.1 hord)
    exact this

theorem eq_sup_of_odd_index {D C S : Subgroup G} (hCD : C ≤ D) (hDC : D ≤ normalizer (C : Set G))
    (hSD : S ≤ D) (hS : ¬ 2 ∣ (S.subgroupOf D).index)
    (h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ C) : C ⊔ S = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := C ⊔ S with hE
  have hED : E ≤ D := sup_le hCD hSD
  have hodd : ¬ 2 ∣ (E.subgroupOf D).index := fun h =>
    hS (h.trans (index_dvd_of_le fun x hx =>
      mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hx))))
  have hCn : (C.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hCD).2 hDC
  have hp : IsPGroup 2 (↥D ⧸ C.subgroupOf D) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := h2 d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact mem_subgroupOf.mpr (by rw [SubgroupClass.coe_pow]; exact hk)
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have hdvd : (E.subgroupOf D).index ∣ 2 ^ a := by
    rw [← ha, ← index_eq_card]
    exact index_dvd_of_le fun x hx => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hb0 : b = 0 := by
    by_contra h0
    exact hodd (hb ▸ dvd_pow_self 2 h0)
  rw [hb0, pow_zero, index_eq_one, subgroupOf_eq_top] at hb
  exact le_antisymm hED hb

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem odd_pow_three {x : G} (hx : x ∈ Lp) (hxo : Odd (orderOf x)) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (pCoreOf 2 Lp).subgroupOf Lp with hN
  have hNn : N.Normal :=
    (normal_subgroupOf_iff_le_normalizer (LieType.BorelTits.pCoreOf_le 2 Lp)).2
      (LieType.BorelTits.le_normalizer_pCoreOf 2 Lp)
  have hidx : N.index = 3 := S.Lp3
  have h3 : (⟨x, hx⟩ : ↥Lp) ^ 3 ∈ N := hidx ▸ N.pow_index_mem _
  have h3' : x ^ 3 ∈ pCoreOf 2 Lp := by
    have := mem_subgroupOf.mp h3
    rwa [SubgroupClass.coe_pow] at this
  obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 Lp) ⟨_, h3'⟩
  have hk' : x ^ (3 * 2 ^ k) = 1 := by
    rw [pow_mul]
    simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 3 * 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxo)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

theorem mem_centralizer_V1 {g : G} (hg : g ∈ A6.g1 T V) : g ∈ centralizer (fsuV1 T V : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, mul_one, one_mul]
  · have hc : g * v * g⁻¹ ∈ fsuV1 T V := (mem_normalizer_iff.mp hg v).mp hv
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).1 S.card1
    have h1 : (⟨v, hv⟩ : ↥(fsuV1 T V)) = y := hy _ fun h => hv1 (congrArg Subtype.val h)
    have h2 : (⟨g * v * g⁻¹, hc⟩ : ↥(fsuV1 T V)) = y := hy _ fun h => by
      have h' : g * v * g⁻¹ = 1 := congrArg Subtype.val h
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    have heq : g * v * g⁻¹ = v := congrArg Subtype.val (h2.trans h1.symm)
    calc v * g = g * v * g⁻¹ * g := by rw [heq]
      _ = g * v := by group

theorem exists_odd_not_centralizer :
    ∃ x ∈ Lp, Odd (orderOf x) ∧ x ∉ centralizer (V₃ : Set G) := by
  by_contra hcon
  push Not at hcon
  have hLp : Lp ≤ centralizer (V₃ : Set G) := by
    rw [S.Lp_eq]
    show Subgroup.closure _ ≤ _
    exact (closure_le _).2 fun x hx => hcon x hx.1 hx.2
  apply S.V1_ne
  rw [← S.comm3]
  refine commutator_eq_bot_iff_le_centralizer.2 ?_
  intro v hv
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_iff.mp (hLp ((LieType.BorelTits.pCoreOf_le 2 Lp) hy)) v hv).symm

theorem Q1_le_centralizer_V3 (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) :
    pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₃ : Set G) := by
  have h1 : V₃ ≤ omegaOneCenterOf (pCoreOf 2 (A6.g1 T V)) := V3_U.trans (S.U_omega hQ)
  intro q hq
  rw [mem_centralizer_iff]
  intro v hv
  exact ((mem_centralizer_iff.mp ((omegaOneCenterOf_le_centralizer _) (h1 hv))) q hq).symm

theorem isTwoReducedIn_W3 (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G))
    {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hLpK : Lp ≤ K) :
    IsTwoReducedIn (K ⊔ T) (conjClosure V₃ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := conjClosure V₃ K with hW
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp hD.mem
  obtain ⟨hUQ, hQU, hUE⟩ := S.stepA hQ
  have hWU : W ≤ conjClosure V₃ (A6.g1 T V) := conjClosure_mono le_rfl hKH
  have hWT : W ≤ T := hWU.trans (hUQ.trans S.Q1_T)
  have hWE : IsElemAbelian 2 W := ⟨⟨⟨fun a b => Subtype.ext (by
    simpa using congrArg Subtype.val (hUE.1.is_comm.comm ⟨a, hWU a.2⟩ ⟨b, hWU b.2⟩))⟩⟩,
    fun x hx => hUE.2 x (hWU hx)⟩
  have hKWn : K ≤ normalizer (W : Set G) := le_normalizer_conjClosure V₃ K
  have hTW : T ≤ normalizer (W : Set G) := by
    have key : ∀ t ∈ T, W ≤ W.comap (MulAut.conj t).toMonoidHom := fun t ht =>
      conjClosure_le fun k hk v hv => by
        show t * (k * v * k⁻¹) * t⁻¹ ∈ W
        have hk' : t * k * t⁻¹ ∈ K := (mem_normalizer_iff.mp (hD.T_K ht) k).mp hk
        have hv' : t * v * t⁻¹ ∈ V₃ := (mem_normalizer_iff.mp (S.T_V3 ht) v).mp hv
        have := mem_conjClosure (Z := V₃) hk' hv'
        rwa [show t * k * t⁻¹ * (t * v * t⁻¹) * (t * k * t⁻¹)⁻¹ = t * (k * v * k⁻¹) * t⁻¹ by
          group] at this
    intro t ht
    rw [mem_normalizer_iff]
    intro w
    refine ⟨fun hw => key t ht hw, fun hw => ?_⟩
    have := key t⁻¹ (inv_mem ht) hw
    simpa [mul_assoc] using this
  have hNW : K ⊔ T ≤ normalizer (W : Set G) := sup_le hKWn hTW
  refine ⟨hWT.trans le_sup_right, hNW, hWE, fun D hDY hYD hD2 => ?_⟩
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).symm
      (A3.isQuasisimple_iff_open.2 hD.quasi)
  have hKp : K = oTwoUpper K :=
    le_antisymm (perfect_le_oTwoUpper le_rfl (Subgroup.isPerfect_iff.2
      (perfect_of_mem_cComp hD.mem))) (oTwoUpper_le K)
  have hO : pCoreOf 2 K ≤ centralizer (W : Set G) := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (A6.g1 T V) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K _ hKH
        ((normal_subgroupOf_iff_le_normalizer hKH).2 hD.G1_K)
    exact h1.trans (hQU.trans (centralizer_le hWU))
  have hDK : D ⊓ K ≤ centralizer (W : Set G) :=
    le_centralizer_of_normal_of_pow_two hKq hKp hKWn hO inf_le_right
      (fun k hk => mem_normalizer_inf (hYD (mem_sup_left hk)) (le_normalizer hk))
      (fun n hn => hD2 n hn.1)
  have hsub : CFSG.Open.IsSubnormal D (K ⊔ T) :=
    .step hDY ((normal_subgroupOf_iff_le_normalizer hDY).2 hYD) (.refl _)
  have hSyl : IsSylowTwoOf (T ⊓ D) D :=
    isSylowTwoOf_inf_of_le_normalizer (S.syl le_sup_right) hDY hYD
  have hfac : (D ⊓ centralizer (W : Set G)) ⊔ (T ⊓ D) = D :=
    eq_sup_of_odd_index inf_le_left
      (fun d hd => mem_normalizer_inf (le_normalizer hd)
        (mem_normalizer_centralizer (hNW (hDY hd))))
      inf_le_right hSyl.2.2 (fun d hd => by
        obtain ⟨k, hk⟩ := hD2 d hd
        exact ⟨k, mem_inf.mpr ⟨pow_mem hd _, hk⟩⟩)
  have hDV1 : D ≤ centralizer (fsuV1 T V : Set G) := by
    rw [← hfac]
    refine sup_le ((inf_le_right).trans (centralizer_le (S.le13.trans (le_conjClosure V₃ K))))
      fun d hd => ?_
    rw [mem_centralizer_iff]
    intro v hv
    have hvT : v ∈ centralizer (T : Set G) :=
      omegaOneCenterOf_le_centralizer T (hv.2 : v ∈ omegaOneCenterOf T)
    exact ((mem_centralizer_iff.mp hvT) d hd.1).symm
  set C := V₃ ⊓ centralizer (D : Set G) with hC
  have hV1C : fsuV1 T V ≤ C := by
    refine le_inf S.le13 fun v hv => ?_
    rw [mem_centralizer_iff]
    intro d hd
    exact ((mem_centralizer_iff.mp (hDV1 hd)) v hv).symm
  have hCn : Lp ⊔ T ≤ normalizer (C : Set G) := fun y hy =>
    mem_normalizer_inf (S.irred.2.1 hy) (mem_normalizer_centralizer
      (hYD ((sup_le (hLpK.trans le_sup_left) le_sup_right) hy)))
  have hDV3 : D ≤ centralizer (V₃ : Set G) := by
    rcases S.irred.2.2.2 C hV1C inf_le_left hCn with hC1 | hC3
    ·
      exfalso
      obtain ⟨x, hxLp, hxo, hxV⟩ := S.exists_odd_not_centralizer
      have hx3 : x ^ 3 = 1 := S.odd_pow_three hxLp hxo
      have hxZ : zpowers x ≤ normalizer (V₃ : Set G) := zpowers_le.2 (S.Lp_V3 hxLp)
      have hBV : T ⊓ D ≤ normalizer (V₃ : Set G) := inf_le_left.trans S.T_V3
      apply hxV
      have hpV : IsPGroup 2 ↥V₃ := S.isP_T.to_le (S.le3V.trans S.V_T)
      have hpB : IsPGroup 2 ↥(T ⊓ D) := S.isP_T.to_le inf_le_left
      have hA : ¬ 2 ∣ Nat.card ↥(zpowers x) := by
        rw [Nat.card_zpowers]
        have : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
        intro h
        have := Nat.dvd_trans h this
        omega
      set α : ↥(zpowers x) →* MulAut ↥V₃ := (conjAct V₃).comp (inclusion hxZ) with hα
      set β : ↥(T ⊓ D) →* MulAut ↥V₃ := (conjAct V₃).comp (inclusion hBV) with hβ
      have hconj : ∀ (y : G) (hy : y ∈ normalizer (V₃ : Set G)) (v : ↥V₃),
          ((conjAct V₃ ⟨y, hy⟩ v : ↥V₃) : G) = y * v * y⁻¹ := fun _ _ _ => rfl
      have hcomm : ∀ a b, α a * β b = β b * α a := by
        intro a b
        have haK : (a : G) ∈ K := hLpK ((zpowers_le.2 hxLp) a.2)
        have hab : ⁅(a : G), (b : G)⁆ ∈ centralizer (V₃ : Set G) := by
          refine centralizer_le (le_conjClosure V₃ K) (hDK (mem_inf.mpr ⟨?_, ?_⟩))
          · rw [commutatorElement_def]
            have h1 : (a : G) * b * (a : G)⁻¹ ∈ D :=
              (mem_normalizer_iff.mp (hYD (mem_sup_left haK)) b).mp (mem_inf.mp b.2).2
            exact mul_mem h1 (inv_mem (mem_inf.mp b.2).2)
          · rw [commutatorElement_def]
            have h1 : (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ K :=
              (mem_normalizer_iff.mp (hD.T_K (mem_inf.mp b.2).1) _).mp (inv_mem haK)
            have : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = a * ((b : G) * (a : G)⁻¹ * (b : G)⁻¹) := by
              group
            rw [this]
            exact mul_mem haK h1
        ext v
        show ((a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹) =
          (b : G) * ((a : G) * v * (a : G)⁻¹) * (b : G)⁻¹
        have hw : (b : G) * ((a : G) * v * (a : G)⁻¹) * (b : G)⁻¹ ∈ V₃ := by
          have h1 : (a : G) * v * (a : G)⁻¹ ∈ V₃ := (mem_normalizer_iff.mp (hxZ a.2) v).mp v.2
          exact (mem_normalizer_iff.mp (hBV b.2) _).mp h1
        have hc := (mem_centralizer_iff.mp hab) _ hw
        rw [commutatorElement_def] at hc
        calc (a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹
            = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) *
                ((b : G) * ((a : G) * v * (a : G)⁻¹) * (b : G)⁻¹) *
                ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹ := by group
          _ = (b : G) * ((a : G) * v * (a : G)⁻¹) * (b : G)⁻¹ := by
            rw [← hc]
            group
      have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
        intro a r hr
        have hrD : (r : G) ∈ centralizer (D : Set G) := by
          have hS : T ⊓ D ≤ centralizer ({(r : G)} : Set G) := by
            intro b hb
            rw [mem_centralizer_singleton_iff]
            have := congrArg Subtype.val (hr ⟨b, hb⟩)
            simp only [hβ, MonoidHom.comp_apply] at this
            rw [hconj] at this
            simp only [Subgroup.coe_inclusion] at this
            calc b * (r : G) = b * r * b⁻¹ * b := by group
              _ = r * b := by rw [this]
          have hCW : D ⊓ centralizer (W : Set G) ≤ centralizer ({(r : G)} : Set G) := by
            intro c hc
            rw [mem_centralizer_singleton_iff]
            exact ((mem_centralizer_iff.mp hc.2) r (le_conjClosure V₃ K r.2)).symm
          have hDr : D ≤ centralizer ({(r : G)} : Set G) := hfac ▸ sup_le hCW hS
          rw [mem_centralizer_iff]
          intro d hd
          exact (mem_centralizer_singleton_iff.mp (hDr hd))
        have hrC : (r : G) ∈ C := mem_inf.mpr ⟨r.2, hrD⟩
        rw [hC1] at hrC
        have hac : (a : G) ∈ centralizer (fsuV1 T V : Set G) :=
          S.mem_centralizer_V1 (S.Lp_G1 ((zpowers_le.2 hxLp) a.2))
        apply Subtype.ext
        simp only [hα, MonoidHom.comp_apply]
        rw [hconj]
        have := (mem_centralizer_iff.mp hac) r hrC
        calc (a : G) * r * (a : G)⁻¹ = r * a * (a : G)⁻¹ := by rw [this]
          _ = r := by group
      have htriv := GroupTheory.thompson_A_times_B hpV hA hpB α β hcomm hfix
      rw [mem_centralizer_iff]
      intro v hv
      have := congrArg (fun φ : MulAut ↥V₃ => ((φ ⟨v, hv⟩ : ↥V₃) : G))
        (htriv ⟨x, mem_zpowers x⟩)
      simp only [hα, MonoidHom.comp_apply, MulAut.one_apply] at this
      rw [hconj] at this
      simp only [Subgroup.coe_inclusion] at this
      calc v * x = x * v * x⁻¹ * x := by rw [this]
        _ = x * v := by group
    · intro d hd
      rw [mem_centralizer_iff]
      intro v hv
      have hvC : v ∈ C := hC3 ▸ hv
      exact ((mem_centralizer_iff.mp (mem_inf.mp hvC).2) d hd).symm
  have hWD : W ≤ centralizer (D : Set G) := conjClosure_le fun k hk v hv => by
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : k⁻¹ * d * k⁻¹⁻¹ ∈ D :=
      (mem_normalizer_iff.mp (hYD (mem_sup_left (inv_mem hk))) d).mp hd
    have h1 := (mem_centralizer_iff.mp (hDV3 hd')) v hv
    calc d * (k * v * k⁻¹) = k * ((k⁻¹ * d * k⁻¹⁻¹) * v) * k⁻¹ := by group
      _ = k * (v * (k⁻¹ * d * k⁻¹⁻¹)) * k⁻¹ := by rw [h1]
      _ = k * v * k⁻¹ * d := by group
  exact le_centralizer_iff.1 hWD

theorem V3_comm_Lp : ⁅V₃, Lp⁆ = V₃ := by
  have hle : ⁅V₃, Lp⁆ ≤ V₃ := by
    rw [commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp S.Lp_V3
  have hV1 : fsuV1 T V ≤ ⁅V₃, Lp⁆ := by
    rw [← S.comm3]
    exact commutator_mono le_rfl (LieType.BorelTits.pCoreOf_le 2 Lp)
  have hn : Lp ⊔ T ≤ normalizer ((⁅V₃, Lp⁆ : Subgroup G) : Set G) :=
    sup_le (fun l hl => mem_normalizer_commutator (S.Lp_V3 hl) (le_normalizer hl))
      (fun t ht => mem_normalizer_commutator (S.T_V3 ht) (S.T_Lp ht))
  rcases S.irred.2.2.2 _ hV1 hle hn with h1 | h3
  · exfalso
    have hV2 : Lp ⊔ T ≤ normalizer (V₂ : Set G) := by
      refine sup_le (fun l hl => ?_) S.v2.2.2.1
      rw [mem_normalizer_iff]
      have key : ∀ m ∈ Lp, ∀ v ∈ V₂, m * v * m⁻¹ ∈ V₂ := by
        intro m hm v hv
        have hc : ⁅v, m⁆ ∈ fsuV1 T V := h1 ▸ commutator_mem_commutator (S.le23 hv) hm
        have : m * v * m⁻¹ = (⁅v, m⁆)⁻¹ * v := by
          rw [commutatorElement_def]
          group
        rw [this]
        exact mul_mem (inv_mem (S.le12 hc)) hv
      intro v
      refine ⟨fun hv => key l hl v hv, fun hv => ?_⟩
      have := key l⁻¹ (inv_mem hl) _ hv
      simpa [mul_assoc] using this
    rcases S.irred.2.2.2 V₂ S.le12 S.le23 hV2 with h | h
    · have := S.v2.2.2.2
      rw [h, S.card1] at this
      exact absurd this (by norm_num)
    · have := S.v2.2.2.2
      rw [h, S.card3] at this
      exact absurd this (by norm_num)
  · exact h3

end Set14

end CFSG.Quasithin.H13.U3
