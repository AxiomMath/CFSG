module

public import CFSG.Quasithin.H13.A6S13821zl
public import CFSG.Quasithin.H13.A6S13821zz6
public import CFSG.Quasithin.H13.A6S13821zz8
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5Setup

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6S20

theorem ordA_two_of_odd {n : ℕ} (hn : Odd n) :
    ordA 2 (2 ^ n) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 := by
    have h3 : (2 ^ n - 1) % 3 = 1 := by
      obtain ⟨k, rfl⟩ := hn
      have h4 : (4 : ℕ) ^ k % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have e : (2 : ℕ) ^ (2 * k + 1) = 2 * 4 ^ k := by
        rw [pow_succ, pow_mul]
        norm_num
        ring
      rw [e]
      omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, show (2 : ℕ) + 1 = 3 by norm_num,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num), hg, Nat.div_one]

end A6S20

namespace Setting4

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem k_data_l3 {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (hnodd : Odd n)
    (hL3 : IsPSL 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) :
    commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ ∧
    IsSimpleGroup ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
    Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  obtain ⟨hS, hH, hK, -, -, -, -⟩ := hC
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  have h1 : IsPSL 3 2 n ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    IsPSL.of_mulEquiv (QuotientGroup.congr _ _ e₁.symm (Subgroup.map_center_eq e₁.symm)) hL3
  refine ⟨?_, (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n h1).2, ?_⟩
  · have hK' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
    have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.isPerfect_def.mp this
  · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h1).1 rfl, A6S20.ordA_two_of_odd hnodd]

theorem exists_ff_sl3_13820a
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (ha : S.Case13820aHyp H K)
    (hnodd : Odd n) (hL3 : IsPSL 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) :
    ∃ hF : HypF918 T V L (fsuV1 T V) S.V3 H K, ∃ I : Subgroup G, fsuV1 T V ≤ I ∧
      ∃ hIU : I ≤ conjClosure S.V3 H, IsIrrPlusTildeT hF hIU ∧
      T ≤ Subgroup.normalizer (I : Set G) ∧
      (haveI := factElem hF hIU
       ∃ m, 2 ≤ m ∧ BinaryNaturalSL (autSec (autSub (autIH (fsuV1 T V) I H K)
          (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
          ((subM (fsuV1 T V) (conjClosure I H) I ⊓
            fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
              (subM (fsuV1 T V) (conjClosure I H) I))) ⊤ ⊥ 3 m ∧
        qOf (autSec (autSub (autIH (fsuV1 T V) I H (conjClosure K T) ⊔
            autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
          ((subM (fsuV1 T V) (conjClosure I H) I ⊓
            fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
              (subM (fsuV1 T V) (conjClosure I H) I))) = ((1 / 2 : ℚ) : WithTop ℚ)) := by
  obtain ⟨hF, I, hV₁I, hIU, hirrT, hTI, hFF⟩ :=
    S.exists_ff_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hC ha
  obtain ⟨hperf, hs, hcardQ⟩ := S.k_data_l3 hC hnodd hL3
  obtain ⟨hS, hH, hK, hKn, -, hn, -⟩ := hC
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  refine ⟨hF, I, hV₁I, hIU, hirrT, hTI, ?_⟩
  have := factElem hF hIU
  obtain ⟨hB4, hexp, hFF2⟩ := A6S20.ff_data_gen hA21 (S.sqtkGroup_of_mem_Hz hH) hF hK₀
    hV₁I hIU hirrT hTI hFF
  obtain ⟨φ, hφr⟩ := A6S20.exists_surj_autSec (S.sqtkGroup_of_mem_Hz hH) hF hK₀ hV₁I hIU
    hirrT hTI
  have hnt := InternalSec.exists_noncomm_of_isQuasisimple hB4.2.2.1
  obtain ⟨a, b, hab⟩ := hnt
  have : Nontrivial ↥(autSec (autSub (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I))) :=
    ⟨⟨a * b, b * a, hab⟩⟩
  obtain ⟨hcard, hdvd⟩ := A6S20.card_quot_center_of_surjective hperf hs
    (MonoidHom.range_eq_top.mp hφr)
  have hoddQ : Odd (Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))) :=
    E1.ThinA5.odd_card_center_quot_pCore
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF2
  have hc := h42 _ hexp _ _ hB4 A hA
  have hn3 : 3 ≤ n := by
    obtain ⟨k, rfl⟩ := hnodd
    omega
  exact A6S20.natural_sl3_of_b42 hexp hB4 hA hc hn3 (hcard.trans hcardQ)
    (Odd.of_dvd_nat hoddQ hdvd)

end Setting4

end CFSG.Quasithin.H13.A6
