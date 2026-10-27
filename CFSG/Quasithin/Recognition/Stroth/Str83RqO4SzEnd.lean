module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Class
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4ZCentralizer
import CFSG.Quasithin.Vol2.Ch4Sec1Defs
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
import CFSG.Quasithin.Recognition.St84.EdgeStabB
import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Walter.W67.W2Cor32A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {X : Subgroup G}

private theorem Gw_zero_two : t.Gw 0 2 = t.Gv 0 ⊓ t.Gv 1 ⊓ t.Gv 2 := by
  have h := t.Gw_sub_one_add_one (c := 1)
  norm_num at h
  exact h

private theorem not_two_dvd_relIndex_oTwoPrime {X : Subgroup G} :
    ¬ 2 ∣ (oTwoPrime X).relIndex X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : ((oTwoPrime X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoPrime X)
  let Q := X ⧸ (oTwoPrime X).subgroupOf X
  have hodd : ∀ q : Q, Odd (orderOf q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hpos := orderOf_pos x
      obtain ⟨e, m, hm, hord⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 2 (by norm_num)
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [hord, mul_zero] at hpos
        exact Nat.lt_irrefl 0 hpos
      have hdiv : m ∣ orderOf x := ⟨2 ^ e, by rw [hord, mul_comm]⟩
      have ho : orderOf ((x : ↥X) ^ m) = 2 ^ e := by
        rw [orderOf_pow_of_dvd hm0 hdiv, hord, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
      have hxm : ((x : G) ^ m) ^ 2 ^ e = 1 := by
        have h1 : ((x : ↥X) ^ m) ^ 2 ^ e = 1 := by
          rw [← ho]
          exact pow_orderOf_eq_one _
        simpa using congrArg Subtype.val h1
      have hzp : IsPGroup 2 (Subgroup.zpowers ((x : G) ^ m)) :=
        CFSG.Quasithin.St84.isPGroup_zpowers_of_pow_two hxm
      have hxO : (x : G) ^ m ∈ oTwoPrime X := by
        refine Subgroup.zpowers_le.mp (le_oTwoPrime_of_isPGroup hzp ?_)
        exact Subgroup.zpowers_le.mpr (X.pow_mem x.2 m)
      have hmk : (QuotientGroup.mk x : Q) ^ m = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hxO
      have hmodd : Odd m :=
        Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
      exact Odd.of_dvd_nat hmodd (orderOf_dvd_of_pow_eq_one hmk)
  by_contra h2dvd
  haveI : Fintype Q := Fintype.ofFinite Q
  have h2' : 2 ∣ Fintype.card Q := by
    simpa [Q, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card] using h2dvd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card 2 h2'
  have hqodd := hodd q
  rw [hq] at hqodd
  norm_num at hqodd

private theorem normal_eq_bot_or_top_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) [IsSimpleGroup K] (N : Subgroup H) [N.Normal] : N = ⊥ ∨ N = ⊤ := by
  have h := Subgroup.Normal.eq_bot_or_eq_top (N.map e.toMonoidHom)
  rcases h with h | h
  · left
    ext x
    constructor
    · intro hx
      have hx' : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h] at hx'
      exact e.injective (by simpa using hx')
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact N.one_mem
  · right
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hx' : e x ∈ N.map e.toMonoidHom := by rw [h]; trivial
      obtain ⟨y, hy, hyx⟩ := hx'
      exact (e.injective hyx) ▸ hy

private noncomputable def quotientEqMulEquiv {A B : Subgroup G} (h : A = B) (N : Subgroup G)
    [hA : (N.subgroupOf A).Normal] [hB : (N.subgroupOf B).Normal] :
    (↥A ⧸ N.subgroupOf A) ≃* (↥B ⧸ N.subgroupOf B) := by
  cases h
  exact MulEquiv.refl _

private theorem ArcSz.le_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hX2 : IsPGroup 2 X) : X ≤ t.Qv 1 := by
  have hle : X ≤ t.Gw 0 2 := by
    rw [Gw_zero_two t]
    exact hX.le
  exact le_Qv_of_le_Gw t hfr (by norm_num) (by norm_num) hX2 hle

private theorem ArcSz.Zv_one_le_MX_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hX2 : IsPGroup 2 X) :
    t.Zv 1 ≤ t.MX X 0 := by
  have hXQ : X ≤ t.Qv 1 := ArcSz.le_Qv_one t hfr hX hX2
  have hcent : t.Zv 1 ≤ Subgroup.centralizer (X : Set G) :=
    (Zv_le_centralizer t 1).trans (Subgroup.centralizer_le hXQ)
  refine le_inf (hcent.trans (Subgroup.centralizer_le_normalizer (X : Set G))) ?_
  exact (Zv_le_Qv t 1).trans (Qv_le_Gv t hfr 1).1

private theorem ArcSz.pX_eq_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    t.Qv 1 ⊓ t.MX X 0 = pCoreOf 2 (t.MX X 0 ⊓ t.Gv 1) := by
  set A : Subgroup G := t.MX X 0 ⊓ t.Gv 1 with hA
  have hAMX : A ≤ t.MX X 0 := inf_le_left
  have hAG0 : A ≤ t.Gv 0 := hAMX.trans inf_le_right
  have hAG1 : A ≤ t.Gv 1 := inf_le_right
  have hPleA : t.Qv 1 ⊓ t.MX X 0 ≤ A :=
    le_inf inf_le_right (inf_le_left.trans (Qv_le_Gv_self t 1))
  have hPleS : t.Qv 1 ⊓ t.MX X 0 ≤ t.Gv 0 ⊓ t.Gv 1 :=
    le_inf (inf_le_left.trans (Qv_le_Gv t hfr 1).1)
      (inf_le_left.trans (Qv_le_Gv_self t 1))
  have hAleN : A ≤ Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) := by
    intro a ha
    obtain ⟨haM, haG⟩ := Subgroup.mem_inf.mp ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (t.Qv 1).map (MulAut.conj a).toMonoidHom = t.Qv 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Gv_le_normalizer_Qv t 1 haG)
    have h2 : (t.MX X 0).map (MulAut.conj a).toMonoidHom = t.MX X 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haM)
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective]
    change (t.Qv 1).map (MulAut.conj a).toMonoidHom ⊓
      (t.MX X 0).map (MulAut.conj a).toMonoidHom = t.Qv 1 ⊓ t.MX X 0
    rw [h1, h2]
  have hP2 : IsPGroup 2 ↥(t.Qv 1 ⊓ t.MX X 0 : Subgroup G) :=
    (isPGroup_Qv t 1).to_le (inf_le_left : t.Qv 1 ⊓ t.MX X 0 ≤ t.Qv 1)
  refine le_antisymm (le_pCoreOf_of_le_normalizer 2 hPleA hAleN hP2) ?_
  have hEA : pCoreOf 2 A ≤ A := pCoreOf_le 2 A
  have hEGw : pCoreOf 2 A ≤ t.Gw 0 2 := by
    rw [Gw_zero_two t]
    refine le_inf (le_inf (hEA.trans hAG0) (hEA.trans hAG1)) ?_
    intro z hz
    have hzA : z ∈ A := pCoreOf_le 2 A hz
    obtain ⟨hzM, hzG1⟩ := Subgroup.mem_inf.mp hzA
    obtain ⟨hzN, hzG0⟩ := Subgroup.mem_inf.mp hzM
    rcases hX.pair z (Subgroup.mem_inf.mpr ⟨hzN, hzG1⟩) with h | h
    · exact h.2
    · exfalso
      have hx₂ : t.x₂ ∈ t.Gv 0 := by
        have hm : z * (t.x₂⁻¹ * z)⁻¹ ∈ t.Gv 0 :=
          (t.Gv 0).mul_mem hzG0 ((t.Gv 0).inv_mem h.1)
        simpa [mul_assoc] using hm
      exact x₂_not_mem_Gv_zero t hx₂
  intro y hy
  exact Subgroup.mem_inf.mpr ⟨le_Qv_of_le_Gw t hfr (by norm_num) (by norm_num)
    (pCoreOf_isPGroup 2 A) hEGw hy, (hEA.trans hAMX) hy⟩

private theorem ArcSz.S_sylow_bigB {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    IsSylowTwoOf S (bigB L1 L2 S) ∧ S ⊓ t.K = ⊥ ∧ t.K ≤ bigB L1 L2 S := by
  have hBig : t.Gw 0 1 = bigB L1 L2 S := Gw_zero_one t hfr.hF
  have hSK : S ⊔ t.K = bigB L1 L2 S := by
    rw [← hBig, Gw_eq_sup t hfr (by norm_num), pCoreOf_Gw_zero_one t hfr]
  have hSbig : S ≤ bigB L1 L2 S := by rw [← hSK]; exact le_sup_left
  have hS2 : IsPGroup 2 S := by
    rw [← pCoreOf_Gw_zero_one t hfr]; exact pCoreOf_isPGroup 2 _
  have hKbig : t.K ≤ bigB L1 L2 S := by rw [← hSK]; exact le_sup_right
  have hSinfK : S ⊓ t.K = ⊥ := by rw [inf_comm]; exact K_inf_eq_bot t hfr
  have hKodd : Odd (Nat.card ↥(t.K)) := t.hHall.2.1
  have hcard : Nat.card ↥(bigB L1 L2 S) = Nat.card S * Nat.card t.K := by
    have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
      (A := S) (B := t.K) (hKbig.trans hfr.hN)
    rw [hSK] at h
    simpa [hSinfK, Subgroup.card_bot] using h
  have hSrel : S.relIndex (bigB L1 L2 S) = Nat.card t.K := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := bigB L1 L2 S)
    rw [inf_eq_left.mpr hSbig, hcard] at h
    rw [mul_comm (Nat.card ↥S) (Nat.card ↥(t.K))] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hoddS : ¬ 2 ∣ S.relIndex (bigB L1 L2 S) := by
    rw [hSrel]
    rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hKodd
    omega
  exact ⟨F7.isSylowTwoOf_of_relIndex hSbig hS2 hoddS, hSinfK, hKbig⟩

private theorem ArcSz.pX_eq_inf_A_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    t.Qv 1 ⊓ t.MX X 0 = (t.MX X 0 ⊓ t.Gv 1) ⊓ S := by
  obtain ⟨hSylS, hSinfK, hKbig⟩ := ArcSz.S_sylow_bigB t hfr
  have hbigE : t.Gv 0 ⊓ t.Gv 1 = bigB L1 L2 S := by
    rw [← Gw_zero_one t hfr.hF]
    have h := (Gw_add_one t 0).symm
    simpa using h
  have hP2 : IsPGroup 2 ↥(t.Qv 1 ⊓ t.MX X 0 : Subgroup G) :=
    (isPGroup_Qv t 1).to_le (inf_le_left : t.Qv 1 ⊓ t.MX X 0 ≤ t.Qv 1)
  have hPbig : t.Qv 1 ⊓ t.MX X 0 ≤ bigB L1 L2 S := by
    rw [← hbigE]
    exact le_inf (inf_le_left.trans (Qv_le_Gv t hfr 1).1)
      (inf_le_left.trans (Qv_le_Gv_self t 1))
  have hPS : t.Qv 1 ⊓ t.MX X 0 ≤ S :=
    CFSG.Quasithin.B6.le_of_isPGroup_of_odd_relIndex hPbig hP2 hSylS.1 hfr.hN
      (by simpa only [Subgroup.relIndex] using hSylS.2.2)
  have hP_A : t.Qv 1 ⊓ t.MX X 0 ≤ t.MX X 0 ⊓ t.Gv 1 :=
    le_inf inf_le_right (inf_le_left.trans (Qv_le_Gv_self t 1))
  have hP_inf : t.Qv 1 ⊓ t.MX X 0 ≤ (t.MX X 0 ⊓ t.Gv 1) ⊓ S := le_inf hP_A hPS
  have hAGw : t.MX X 0 ⊓ t.Gv 1 ≤ t.Gw 0 1 := by
    rw [Gw_zero_one t hfr.hF, ← hbigE]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hA_norm_S : t.MX X 0 ⊓ t.Gv 1 ≤ Subgroup.normalizer (S : Set G) :=
    hAGw.trans (by rw [Gw_zero_one t hfr.hF]; exact hfr.hN)
  have hinf_norm : t.MX X 0 ⊓ t.Gv 1 ≤
      Subgroup.normalizer (((t.MX X 0 ⊓ t.Gv 1) ⊓ S : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA_norm_S ha)]
  have hinfP : (t.MX X 0 ⊓ t.Gv 1) ⊓ S ≤ t.Qv 1 ⊓ t.MX X 0 := by
    have h := le_pCoreOf_of_le_normalizer 2 inf_le_left hinf_norm
      (hSylS.2.1.to_le (inf_le_right : (t.MX X 0 ⊓ t.Gv 1) ⊓ S ≤ S))
    rwa [← ArcSz.pX_eq_pCoreOf t hfr hX] at h
  exact le_antisymm hP_inf hinfP

private theorem ArcSz.pX_A_decomp {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    t.MX X 0 ⊓ t.Gv 1 = (t.Qv 1 ⊓ t.MX X 0) ⊔ t.K := by
  obtain ⟨hSylS, hSinfK, hKbig⟩ := ArcSz.S_sylow_bigB t hfr
  have hPAS : t.Qv 1 ⊓ t.MX X 0 = (t.MX X 0 ⊓ t.Gv 1) ⊓ S :=
    ArcSz.pX_eq_inf_A_S t hfr hX
  have hKA : t.K ≤ t.MX X 0 ⊓ t.Gv 1 :=
    le_inf (le_inf hX.K_le (K_le_Gv t 0)) (K_le_Gv t 1)
  have hBig : t.Gw 0 1 = bigB L1 L2 S := Gw_zero_one t hfr.hF
  have hAGw : t.MX X 0 ⊓ t.Gv 1 ≤ t.Gw 0 1 := by
    rw [hBig]
    have hbigE : t.Gv 0 ⊓ t.Gv 1 = bigB L1 L2 S := by
      rw [← hBig]
      have h := (Gw_add_one t 0).symm
      simpa using h
    rw [← hbigE]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hSK : S ⊔ t.K = bigB L1 L2 S := by
    rw [← hBig, Gw_eq_sup t hfr (by norm_num), pCoreOf_Gw_zero_one t hfr]
  refine le_antisymm ?_ (sup_le (by rw [hPAS]; exact inf_le_left) hKA)
  intro a ha
  have haB : a ∈ bigB L1 L2 S := hBig ▸ hAGw ha
  have haSK : a ∈ S ⊔ t.K := by rwa [hSK]
  obtain ⟨s, hs, k, hk, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes
      (H := S) (K := t.K) (hKbig.trans hfr.hN)).mp haSK
  have hkA : k ∈ t.MX X 0 ⊓ t.Gv 1 := hKA hk
  have hsA : s ∈ t.MX X 0 ⊓ t.Gv 1 := by
    have := (t.MX X 0 ⊓ t.Gv 1).mul_mem ha ((t.MX X 0 ⊓ t.Gv 1).inv_mem hkA)
    simpa using this
  have hsP : s ∈ t.Qv 1 ⊓ t.MX X 0 := hPAS.symm ▸ ⟨hsA, hs⟩
  exact Subgroup.mul_mem_sup hsP hk

private theorem ArcSz.pX_supplement
    (hX : t.ArcSz X)
    (hAdecomp : t.MX X 0 ⊓ t.Gv 1 = (t.Qv 1 ⊓ t.MX X 0) ⊔ t.K) :
    ∀ x ∈ t.MX X 0 ⊓ t.Gv 1,
      ∃ d ∈ t.K, ∃ c ∈ t.Qv 1 ⊓ t.MX X 0, x = d * c := by
  have hKN : t.K ≤ Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (t.Qv 1).map (MulAut.conj k).toMonoidHom = t.Qv 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (K_le_normalizer_Qv t 1 hk)
    have hkMX : k ∈ t.MX X 0 := ⟨hX.K_le hk, K_le_Gv t 0 hk⟩
    have h2 : (t.MX X 0).map (MulAut.conj k).toMonoidHom = t.MX X 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkMX)
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective]
    change (t.Qv 1).map (MulAut.conj k).toMonoidHom ⊓
      (t.MX X 0).map (MulAut.conj k).toMonoidHom = t.Qv 1 ⊓ t.MX X 0
    rw [h1, h2]
  intro x hx
  rw [hAdecomp, sup_comm] at hx
  exact (F1.mem_sup_iff_exists_mul_of_le_normalizer (H := t.K)
    (K := t.Qv 1 ⊓ t.MX X 0) hKN).mp hx

private theorem ArcSz.relIndex_pX_A {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    (t.Qv 1 ⊓ t.MX X 0).relIndex (t.MX X 0 ⊓ t.Gv 1) = Nat.card t.K := by
  obtain ⟨hSylS, hSinfK, hKbig⟩ := ArcSz.S_sylow_bigB t hfr
  have hPAS : t.Qv 1 ⊓ t.MX X 0 = (t.MX X 0 ⊓ t.Gv 1) ⊓ S :=
    ArcSz.pX_eq_inf_A_S t hfr hX
  have hKA : t.K ≤ t.MX X 0 ⊓ t.Gv 1 :=
    le_inf (le_inf hX.K_le (K_le_Gv t 0)) (K_le_Gv t 1)
  have hAdecomp := ArcSz.pX_A_decomp t hfr hX
  have hsupp := ArcSz.pX_supplement t hX hAdecomp
  have hPK : t.Qv 1 ⊓ t.MX X 0 ⊓ t.K = ⊥ := by
    rw [eq_bot_iff]
    have h : t.Qv 1 ⊓ t.MX X 0 ≤ S := hPAS.le.trans inf_le_right
    calc t.Qv 1 ⊓ t.MX X 0 ⊓ t.K ≤ S ⊓ t.K := inf_le_inf_right _ h
      _ = ⊥ := hSinfK
  have hrel : (t.Qv 1 ⊓ t.MX X 0).relIndex (t.MX X 0 ⊓ t.Gv 1) = Nat.card t.K := by
    have h1 := CFSG.Walter.W67.relIndex_eq_of_supplement (D := t.K)
      (H := t.Qv 1 ⊓ t.MX X 0) (M := t.MX X 0 ⊓ t.Gv 1) hKA hsupp
    rw [← h1]
    have h2 := Subgroup.relIndex_mul_card (H := t.Qv 1 ⊓ t.MX X 0) (K := t.K)
    rw [hPK, Subgroup.card_bot, mul_one] at h2
    exact h2
  exact hrel

private theorem ArcSz.pX_sylow_in_A {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0 ⊓ t.Gv 1) := by
  have hPAS : t.Qv 1 ⊓ t.MX X 0 = (t.MX X 0 ⊓ t.Gv 1) ⊓ S :=
    ArcSz.pX_eq_inf_A_S t hfr hX
  have hP_A : t.Qv 1 ⊓ t.MX X 0 ≤ t.MX X 0 ⊓ t.Gv 1 := hPAS.le.trans inf_le_left
  have hP2 : IsPGroup 2 ↥(t.Qv 1 ⊓ t.MX X 0 : Subgroup G) :=
    (isPGroup_Qv t 1).to_le (inf_le_left : t.Qv 1 ⊓ t.MX X 0 ≤ t.Qv 1)
  refine F7.isSylowTwoOf_of_relIndex hP_A hP2 ?_
  rw [ArcSz.relIndex_pX_A t hfr hX]
  have hKodd : Odd (Nat.card ↥(t.K)) := t.hHall.2.1
  rintro ⟨j, hj⟩
  obtain ⟨k, hk⟩ := hKodd
  omega

private theorem ArcSz.relIndex_A_MX_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    ¬ 2 ∣ (t.MX X 0 ⊓ t.Gv 1).relIndex (t.MX X 0) := by
  have hbigE : t.Gv 0 ⊓ t.Gv 1 = bigB L1 L2 S := by
    rw [← Gw_zero_one t hfr.hF]
    have h := (Gw_add_one t 0).symm
    simpa using h
  have hsupp : ∀ x ∈ t.Gv 0, ∃ d ∈ t.MX X 0, ∃ c ∈ bigB L1 L2 S, x = d * c := by
    intro x hx
    obtain ⟨n, hn, hnc⟩ := hX.trans₀ x hx
    refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
    rw [← hbigE]
    exact ⟨(t.Gv 0).mul_mem ((t.Gv 0).inv_mem hn.2) hx, hnc⟩
  have hrel1 : (bigB L1 L2 S).relIndex (t.MX X 0) = (bigB L1 L2 S).relIndex (t.Gv 0) :=
    CFSG.Walter.W67.relIndex_eq_of_supplement inf_le_right hsupp
  have hbigrel : (bigB L1 L2 S).relIndex (t.Gv 0) = 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [Gv_zero t]
    exact CFSG.Quasithin.Stroth.f112_relIndex_left_sz hfr.hF hfr.ha hfr.hSz
  have hAh : t.MX X 0 ⊓ t.Gv 1 = t.MX X 0 ⊓ bigB L1 L2 S := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxM, hx1⟩
      exact ⟨hxM, hbigE ▸ ⟨(inf_le_right : t.MX X 0 ≤ t.Gv 0) hxM, hx1⟩⟩
    · rintro ⟨hxM, hx⟩
      exact ⟨hxM, (hbigE.symm ▸ hx).2⟩
  rw [hAh, Subgroup.inf_relIndex_left, hrel1, hbigrel]
  intro h2
  have h2' : 2 ∣ 2 ^ (2 * (2 * a + 1)) := dvd_pow_self 2 (by omega)
  omega

private theorem ArcSz.isSylowTwoOf_pX_MX_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0) := by
  have hA := ArcSz.pX_sylow_in_A t hfr hX
  have hAodd := ArcSz.relIndex_A_MX_odd t hfr hX
  have hP2 : IsPGroup 2 ↥(t.Qv 1 ⊓ t.MX X 0 : Subgroup G) :=
    (isPGroup_Qv t 1).to_le (inf_le_left : t.Qv 1 ⊓ t.MX X 0 ≤ t.Qv 1)
  refine F7.isSylowTwoOf_of_relIndex
    (hA.1.trans (inf_le_left : t.MX X 0 ⊓ t.Gv 1 ≤ t.MX X 0)) hP2 ?_
  have hmul := (Subgroup.relIndex_mul_relIndex (H := t.Qv 1 ⊓ t.MX X 0)
    (K := t.MX X 0 ⊓ t.Gv 1) (L := t.MX X 0) hA.1
    (inf_le_left : t.MX X 0 ⊓ t.Gv 1 ≤ t.MX X 0)).symm
  rw [hmul]
  exact Nat.prime_two.not_dvd_mul (F7.isSylowTwoOf_odd_relIndex hA) hAodd

private theorem ArcSz.isSylowTwoOf_pX_LX_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.LX X 0) := by
  have hMX := ArcSz.isSylowTwoOf_pX_MX_zero t hfr hX
  have hPL : t.Qv 1 ⊓ t.MX X 0 ≤ t.LX X 0 :=
    le_oTwoPrime_of_isPGroup hMX.2.1 hMX.1
  exact F7.isSylowTwoOf_mono_right hMX hPL (oTwoPrime_le _)

private theorem ArcSz.LX_zero_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.LX X 0 ≤ L1 ⊔ t.Qv 0 := by
  rw [show t.LX X 0 = oTwoPrime (t.MX X 0) from rfl]
  exact (CFSG.Quasithin.St84.oTwoPrime_mono inf_le_right).trans
    (le_of_eq (oTwoPrime_Gv_zero t hfr))

private theorem pCoreOf_L1_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : pCoreOf 2 L1 = L1 ⊓ t.Qv 0 := by
  refine le_antisymm ?_ ?_
  · have hP1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) := by
      refine sup_le (le_normalizer_pCoreOf 2 L1) ?_
      exact ((bigB_le_normalizer_of_hyp111 hfr.hF.1).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (H := L1) (K := CFSG.pCore 2 ↥L1)))
    have hle : pCoreOf 2 L1 ≤ L1 ⊔ bigB L1 L2 S := by
      have h := pCoreOf_le 2 L1
      exact h.trans le_sup_left
    have h2 : pCoreOf 2 L1 ≤ t.Qv 0 := by
      have h := le_pCoreOf_of_le_normalizer 2 hle hP1
        (pCoreOf_isPGroup 2 L1)
      have hQ1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = t.Qv 0 := (Qv_zero t).symm
      rwa [hQ1] at h
    exact le_inf (pCoreOf_le 2 L1) h2
  · have hnorm : L1 ≤ Subgroup.normalizer ((L1 ⊓ t.Qv 0 : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h1 : (L1).map (MulAut.conj a).toMonoidHom = L1 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
      have h2 : (t.Qv 0).map (MulAut.conj a).toMonoidHom = t.Qv 0 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Gv_le_normalizer_Qv t 0)
          ((show L1 ≤ t.Gv 0 from (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge) ha))
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective]
      change (L1).map (MulAut.conj a).toMonoidHom ⊓
        (t.Qv 0).map (MulAut.conj a).toMonoidHom = L1 ⊓ t.Qv 0
      rw [h1, h2]
    have h2 : IsPGroup 2 ↥(L1 ⊓ t.Qv 0 : Subgroup G) :=
      (isPGroup_Qv t 0).to_le (inf_le_right : L1 ⊓ t.Qv 0 ≤ t.Qv 0)
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm h2

private theorem ArcSz.pCoreOf_LX_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) :
    pCoreOf 2 (t.LX X 0) = t.Qv 0 ⊓ t.MX X 0 := by
  rw [show t.LX X 0 = oTwoPrime (t.MX X 0) from rfl,
    CFSG.Quasithin.pCoreOf_oTwoPrime (t.MX X 0)]
  refine le_antisymm ?_ ?_
  · have hE := pCoreOf_isPGroup 2 (t.MX X 0)
    have hEnbr : pCoreOf 2 (t.MX X 0) ≤ t.Gnbr 0 := by
      refine le_gnbr_of_cosetTrans t hfr 0 hE (pCoreOf_le 2 _)
        (le_normalizer_pCoreOf 2 _) inf_le_right ?_
      intro g hg
      obtain ⟨n, hn, hnb⟩ := hX.trans₀ g hg
      exact ⟨n, ⟨hn, hn.2⟩, hnb⟩
    have hEL : pCoreOf 2 (t.MX X 0) ≤ L1 ⊔ t.Qv 0 := by
      have h := le_oTwoPrime_of_isPGroup hE
        ((pCoreOf_le 2 (t.MX X 0)).trans inf_le_right)
      rwa [oTwoPrime_Gv_zero t hfr] at h
    exact le_inf ((le_inf hEL hEnbr).trans (le_of_eq (sup_Qv_inf_Gnbr_zero t hfr)))
      (pCoreOf_le 2 _)
  · have hQ2 : IsPGroup 2 ↥(t.Qv 0 ⊓ t.MX X 0 : Subgroup G) :=
      (isPGroup_Qv t 0).to_le (inf_le_left : t.Qv 0 ⊓ t.MX X 0 ≤ t.Qv 0)
    have hnorm : t.MX X 0 ≤
        Subgroup.normalizer ((t.Qv 0 ⊓ t.MX X 0 : Subgroup G) : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h1 : (t.Qv 0).map (MulAut.conj m).toMonoidHom = t.Qv 0 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          ((Gv_le_normalizer_Qv t 0) (Subgroup.mem_inf.mp hm).2)
      have h2 : (t.MX X 0).map (MulAut.conj m).toMonoidHom = t.MX X 0 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj m).injective]
      change (t.Qv 0).map (MulAut.conj m).toMonoidHom ⊓
        (t.MX X 0).map (MulAut.conj m).toMonoidHom = t.Qv 0 ⊓ t.MX X 0
      rw [h1, h2]
    exact le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hQ2

private theorem ArcSz.isSimpleGroup_sz {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSimpleGroup ↥(Sz a) := by
  have hq := CFSG.Quasithin.Stroth.isQuasisimple_sz a hfr.ha
  have hc := CFSG.Quasithin.Stroth.center_sz a hfr.ha
  haveI : IsSimpleGroup (↥(Sz a) ⧸ Subgroup.center ↥(Sz a)) := hq.2.1
  have e0 : (↥(Sz a) ⧸ Subgroup.center ↥(Sz a)) ≃* (↥(Sz a) ⧸ ⊥) :=
    QuotientGroup.quotientMulEquivOfEq hc
  haveI : IsSimpleGroup (↥(Sz a) ⧸ ⊥) := MulEquiv.isSimpleGroup e0.symm
  exact MulEquiv.isSimpleGroup (QuotientGroup.quotientBot (G := ↥(Sz a))).symm

private theorem ArcSz.LX_zero_Y_data {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0)
    {Y : Subgroup G} (hY : Y = t.MX X 0 ⊓ (L1 ⊔ t.Qv 0)) :
    (L1 ⊔ t.Qv 0 = Y ⊔ t.Qv 0) ∧ t.LX X 0 ≤ Y ∧
      Y ⊓ t.Qv 0 = pCoreOf 2 (t.LX X 0) ∧
      ¬ 2 ∣ (t.LX X 0).relIndex Y ∧
      Y ≤ Subgroup.normalizer (t.Qv 0 : Set G) ∧
      L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) := by
  have hQleB : t.Qv 0 ≤ L1 ⊔ t.Qv 0 := le_sup_right
  have hcovB : L1 ⊔ t.Qv 0 ≤ t.MX X 0 ⊔ t.Qv 0 :=
    sup_le hcov (le_sup_right : t.Qv 0 ≤ t.MX X 0 ⊔ t.Qv 0)
  have hMXnorm : t.MX X 0 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    inf_le_right.trans (Gv_le_normalizer_Qv t 0)
  have hYB : L1 ⊔ t.Qv 0 = Y ⊔ t.Qv 0 := by
    refine le_antisymm ?_ (sup_le (by rw [hY]; exact inf_le_right) hQleB)
    intro b hb
    obtain ⟨m, hm, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer (H := t.MX X 0)
        (K := t.Qv 0) hMXnorm).mp (hcovB hb)
    have hmB : m ∈ L1 ⊔ t.Qv 0 := by
      have h := (L1 ⊔ t.Qv 0).mul_mem hb ((L1 ⊔ t.Qv 0).inv_mem (hQleB hq))
      simpa using h
    exact Subgroup.mul_mem_sup
      (hY.symm ▸ (show m ∈ t.MX X 0 ⊓ (L1 ⊔ t.Qv 0) from ⟨hm, hmB⟩)) hq
  have hLY : t.LX X 0 ≤ Y :=
    hY.symm ▸ le_inf (oTwoPrime_le (t.MX X 0)) (ArcSz.LX_zero_le_sup t hfr)
  have hYMX : Y ≤ t.MX X 0 := by rw [hY]; exact inf_le_left
  have hoddMX : ¬ 2 ∣ (t.LX X 0).relIndex (t.MX X 0) := by
    rw [show t.LX X 0 = oTwoPrime (t.MX X 0) from rfl]
    exact not_two_dvd_relIndex_oTwoPrime (X := t.MX X 0)
  have hodd : ¬ 2 ∣ (t.LX X 0).relIndex Y := by
    intro h2
    exact hoddMX ((Subgroup.relIndex_mul_relIndex (t.LX X 0) Y (t.MX X 0) hLY hYMX).symm ▸
      h2.mul_right _)
  have hYeq : Y ⊓ t.Qv 0 = pCoreOf 2 (t.LX X 0) := by
    rw [hY, inf_assoc, inf_eq_right.mpr (le_sup_right : t.Qv 0 ≤ L1 ⊔ t.Qv 0),
      ArcSz.pCoreOf_LX_zero t hfr hX, inf_comm]
  have hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge).trans
      (Gv_le_normalizer_Qv t 0)
  have hBnorm : L1 ⊔ t.Qv 0 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    sup_le hL1norm Subgroup.le_normalizer
  exact ⟨hYB, hLY, hYeq, hodd, (by rw [hY]; exact inf_le_right.trans hBnorm), hL1norm⟩

private theorem ArcSz.L1_sup_quot_equiv_sz {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    [hN : ((t.Qv 0).subgroupOf (L1 ⊔ t.Qv 0)).Normal] :
    Nonempty ((↥(L1 ⊔ t.Qv 0) ⧸
      (t.Qv 0).subgroupOf (L1 ⊔ t.Qv 0)) ≃* Sz a) := by
  have hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge).trans
      (Gv_le_normalizer_Qv t 0)
  haveI : ((t.Qv 0).subgroupOf L1).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hL1norm
  have hpc : (L1 ⊓ t.Qv 0).subgroupOf L1 = CFSG.pCore 2 ↥L1 := by
    rw [← pCoreOf_L1_eq t hfr, CFSG.openPCoreOf_subgroupOf]
  have hden : (L1 ⊓ t.Qv 0).subgroupOf L1 = (t.Qv 0).subgroupOf L1 := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  haveI hNpc : ((L1 ⊓ t.Qv 0).subgroupOf L1).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (L1).map (MulAut.conj a).toMonoidHom = L1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
    have h2 : (t.Qv 0).map (MulAut.conj a).toMonoidHom = t.Qv 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL1norm ha)
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective]
    change (L1).map (MulAut.conj a).toMonoidHom ⊓
      (t.Qv 0).map (MulAut.conj a).toMonoidHom = L1 ⊓ t.Qv 0
    rw [h1, h2]
  have epc : (↥L1 ⧸ (t.Qv 0).subgroupOf L1) ≃* oTwoQuot ↥L1 :=
    (QuotientGroup.quotientMulEquivOfEq hden.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hpc)
  have e3 : oTwoQuot ↥L1 ≃* Sz a := Classical.choice hfr.hSz
  exact ⟨(QuotientGroup.quotientInfEquivProdNormalizerQuotient L1 (t.Qv 0) hL1norm).symm.trans
    (epc.trans e3)⟩

private theorem ArcSz.LX_zero_quot_equiv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {Y : Subgroup G}
    (hYsup : L1 ⊔ t.Qv 0 = Y ⊔ t.Qv 0)
    (hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G))
    (hLnorm : t.LX X 0 ≤ Subgroup.normalizer (t.Qv 0 : Set G))
    (hYnorm : Y ≤ Subgroup.normalizer (t.Qv 0 : Set G))
    [hNY : ((t.Qv 0).subgroupOf Y).Normal] :
    Nonempty ((↥Y ⧸ (t.Qv 0).subgroupOf Y) ≃* Sz a) := by
  haveI : ((t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hLnorm Subgroup.le_normalizer)
  haveI : ((t.Qv 0).subgroupOf (Y ⊔ t.Qv 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hYnorm Subgroup.le_normalizer)
  haveI : ((t.Qv 0).subgroupOf (L1 ⊔ t.Qv 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hL1norm Subgroup.le_normalizer)
  obtain ⟨eB⟩ := ArcSz.L1_sup_quot_equiv_sz t hfr
  exact ⟨(QuotientGroup.quotientInfEquivProdNormalizerQuotient Y (t.Qv 0) hYnorm).trans
    ((quotientEqMulEquiv hYsup (t.Qv 0)).symm.trans eB)⟩

private theorem ArcSz.LX_zero_bot_case {a : ℕ}
    {Y : Subgroup G}
    [hNY : ((t.Qv 0).subgroupOf Y).Normal]
    (π : ↥Y →* (↥Y ⧸ (t.Qv 0).subgroupOf Y))
    (hπ : π = QuotientGroup.mk' ((t.Qv 0).subgroupOf Y))
    (N : Subgroup (↥Y ⧸ (t.Qv 0).subgroupOf Y))
    (hN : N = ((t.LX X 0).subgroupOf Y).map π) (hbot : N = ⊥)
    (hLY : t.LX X 0 ≤ Y) (hYeq : Y ⊓ t.Qv 0 = pCoreOf 2 (t.LX X 0))
    (hodd : ¬ 2 ∣ (t.LX X 0).relIndex Y)
    (e : (↥Y ⧸ (t.Qv 0).subgroupOf Y) ≃* Sz a) : False := by
  have hLQ : t.LX X 0 ≤ t.Qv 0 := by
    intro x hx
    have hxY : x ∈ Y := hLY hx
    have hxπ : π ⟨x, hxY⟩ = 1 := by
      have hmem : π ⟨x, hxY⟩ ∈ N := by
        rw [hN]
        exact Subgroup.mem_map.mpr ⟨⟨x, hxY⟩, hx, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    rw [hπ] at hxπ
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (⟨x, hxY⟩ : ↥Y)).mp hxπ)
  have hLeq : t.LX X 0 = Y ⊓ t.Qv 0 :=
    le_antisymm (le_inf hLY hLQ) (hYeq.le.trans (pCoreOf_le 2 _))
  have hsub : (t.LX X 0).subgroupOf Y = (t.Qv 0).subgroupOf Y := by
    rw [hLeq]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hYrel : (t.LX X 0).relIndex Y = Nat.card (↥Y ⧸ (t.Qv 0).subgroupOf Y) := by
    rw [show (t.LX X 0).relIndex Y = ((t.LX X 0).subgroupOf Y).index from rfl,
      Subgroup.index, hsub]
  have heven : 2 ∣ Nat.card (↥Y ⧸ (t.Qv 0).subgroupOf Y) := by
    have hc : Nat.card (↥Y ⧸ (t.Qv 0).subgroupOf Y) = Nat.card ↥(Sz a) :=
      Nat.card_congr e.toEquiv
    rw [hc, CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a, ← pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _) _
  exact hodd (hYrel ▸ heven)

private theorem ArcSz.LX_zero_top_case
    {Y : Subgroup G} [hNY : ((t.Qv 0).subgroupOf Y).Normal]
    (π : ↥Y →* (↥Y ⧸ (t.Qv 0).subgroupOf Y))
    (N : Subgroup (↥Y ⧸ (t.Qv 0).subgroupOf Y))
    (hN : N = ((t.LX X 0).subgroupOf Y).map π) (htop : N = ⊤)
    (hπ : π = QuotientGroup.mk' ((t.Qv 0).subgroupOf Y)) :
    Y ≤ t.LX X 0 ⊔ t.Qv 0 := by
  intro y hy
  have hyimg : π ⟨y, hy⟩ ∈ ((t.LX X 0).subgroupOf Y).map π := by
    rw [← hN, htop]
    trivial
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyimg
  have hq : (⟨z, z.2⟩ : ↥Y)⁻¹ * ⟨y, hy⟩ ∈ (t.Qv 0).subgroupOf Y := by
    have hz1 : π ((⟨z, z.2⟩ : ↥Y)⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, hzy, inv_mul_cancel]
    rw [hπ] at hz1
    exact (QuotientGroup.eq_one_iff _).mp hz1
  have hq' : (z : G)⁻¹ * y ∈ t.Qv 0 := Subgroup.mem_subgroupOf.mp hq
  have hzy' : y = z * ((z : G)⁻¹ * y) := by group
  rw [hzy']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hz) hq'

private theorem ArcSz.LX_zero_sup_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0) :
    t.LX X 0 ⊔ t.Qv 0 = L1 ⊔ t.Qv 0 := by
  classical
  let Y : Subgroup G := t.MX X 0 ⊓ (L1 ⊔ t.Qv 0)
  obtain ⟨hYB, hLY, hYeq, hodd, hYnorm, hL1norm⟩ :=
    ArcSz.LX_zero_Y_data t hfr hX hcov (Y := Y) rfl
  have hLnorm : t.LX X 0 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    (ArcSz.LX_zero_le_sup t hfr).trans (sup_le hL1norm Subgroup.le_normalizer)
  haveI hNY : ((t.Qv 0).subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
  have hYMX : Y ≤ t.MX X 0 := by
    rw [show Y = t.MX X 0 ⊓ (L1 ⊔ t.Qv 0) from rfl]
    exact inf_le_left
  haveI : ((t.LX X 0).subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hYMX.trans (le_normalizer_oTwoPrime (t.MX X 0)))
  haveI : IsSimpleGroup ↥(Sz a) := ArcSz.isSimpleGroup_sz hfr
  obtain ⟨e⟩ := ArcSz.LX_zero_quot_equiv t hfr hYB hL1norm hLnorm hYnorm
  let π : ↥Y →* (↥Y ⧸ (t.Qv 0).subgroupOf Y) :=
    QuotientGroup.mk' ((t.Qv 0).subgroupOf Y)
  let N : Subgroup (↥Y ⧸ (t.Qv 0).subgroupOf Y) := ((t.LX X 0).subgroupOf Y).map π
  haveI hNnormal : N.Normal := by
    dsimp only [N]
    infer_instance
  have hNimg : N = ⊥ ∨ N = ⊤ := normal_eq_bot_or_top_of_mulEquiv e N
  rcases hNimg with hbot | htop
  · exfalso
    exact ArcSz.LX_zero_bot_case (t := t) π rfl N rfl hbot hLY hYeq hodd e
  · have hYtop : Y ≤ t.LX X 0 ⊔ t.Qv 0 :=
      ArcSz.LX_zero_top_case (t := t) π N rfl htop rfl
    have hfin : L1 ⊔ t.Qv 0 ≤ t.LX X 0 ⊔ t.Qv 0 := by
      rw [hYB]
      exact sup_le hYtop le_sup_right
    exact le_antisymm (sup_le (ArcSz.LX_zero_le_sup t hfr) le_sup_right) hfin

private theorem ArcSz.LX_oTwoQuot_equiv_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X)
    [hN : ((t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0)).Normal] :
    Nonempty (oTwoQuot ↥(t.LX X 0) ≃*
      (↥(t.LX X 0 ⊔ t.Qv 0) ⧸
        (t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0))) := by
  have hE : CFSG.pCore 2 ↥(t.LX X 0) = (t.Qv 0).subgroupOf (t.LX X 0) := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (t.LX X 0), ArcSz.pCoreOf_LX_zero t hfr hX]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, oTwoPrime_le (t.MX X 0) x.2⟩⟩
  have hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge).trans
      (Gv_le_normalizer_Qv t 0)
  have hLnorm : t.LX X 0 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    (ArcSz.LX_zero_le_sup t hfr).trans (sup_le hL1norm Subgroup.le_normalizer)
  haveI : ((t.Qv 0).subgroupOf (t.LX X 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  haveI : ((t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hLnorm Subgroup.le_normalizer)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hE).trans
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient (t.LX X 0) (t.Qv 0) hLnorm)⟩

private theorem ArcSz.LX_sup_quot_equiv_sz
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X)
    (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0)
    [hN : ((t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0)).Normal] :
    Nonempty ((↥(t.LX X 0 ⊔ t.Qv 0) ⧸
      (t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0)) ≃* Sz a) := by
  have hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge).trans
      (Gv_le_normalizer_Qv t 0)
  haveI : ((t.Qv 0).subgroupOf L1).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hL1norm
  haveI : ((t.Qv 0).subgroupOf (L1 ⊔ t.Qv 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hL1norm Subgroup.le_normalizer)
  have hpc : (L1 ⊓ t.Qv 0).subgroupOf L1 = CFSG.pCore 2 ↥L1 := by
    rw [← pCoreOf_L1_eq t hfr, CFSG.openPCoreOf_subgroupOf]
  have hden : (L1 ⊓ t.Qv 0).subgroupOf L1 = (t.Qv 0).subgroupOf L1 := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  haveI hNpc : ((L1 ⊓ t.Qv 0).subgroupOf L1).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (L1).map (MulAut.conj a).toMonoidHom = L1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
    have h2 : (t.Qv 0).map (MulAut.conj a).toMonoidHom = t.Qv 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL1norm ha)
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective]
    change (L1).map (MulAut.conj a).toMonoidHom ⊓
      (t.Qv 0).map (MulAut.conj a).toMonoidHom = L1 ⊓ t.Qv 0
    rw [h1, h2]
  have epc : (↥L1 ⧸ (t.Qv 0).subgroupOf L1) ≃* oTwoQuot ↥L1 :=
    (QuotientGroup.quotientMulEquivOfEq hden.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hpc)
  have e3 : oTwoQuot ↥L1 ≃* Sz a := Classical.choice hfr.hSz
  have eB : (↥(L1 ⊔ t.Qv 0) ⧸ (t.Qv 0).subgroupOf (L1 ⊔ t.Qv 0)) ≃* Sz a :=
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient L1 (t.Qv 0) hL1norm).symm.trans
      (epc.trans e3)
  have hsup := ArcSz.LX_zero_sup_Qv_zero t hfr hX hcov
  exact ⟨(quotientEqMulEquiv hsup (t.Qv 0)).trans eB⟩

private theorem ArcSz.isSzQuot_LX_zero
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X)
    (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0) :
    Nonempty (oTwoQuot ↥(t.LX X 0) ≃* Sz a) := by
  have hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge).trans
      (Gv_le_normalizer_Qv t 0)
  have hLnorm : t.LX X 0 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    (ArcSz.LX_zero_le_sup t hfr).trans (sup_le hL1norm Subgroup.le_normalizer)
  haveI : ((t.Qv 0).subgroupOf (t.LX X 0 ⊔ t.Qv 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hLnorm Subgroup.le_normalizer)
  obtain ⟨e1⟩ := ArcSz.LX_oTwoQuot_equiv_sup t hfr hX
  obtain ⟨e2⟩ := ArcSz.LX_sup_quot_equiv_sz t hfr hX hcov
  exact ⟨e1.trans e2⟩

private theorem ArcSz.charTwo_normal :
    ((t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)).subgroupOf
      (t.LX X 0)).Normal := by
  have hNcent : t.LX X 0 ≤ Subgroup.normalizer
      (Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G) : Set G) :=
    (le_normalizer_pCoreOf 2 (t.LX X 0)).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (pCoreOf 2 (t.LX X 0) : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer
          (pCoreOf 2 (t.LX X 0) : Set G)))
  refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change ((t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G) : Subgroup G)).map
      (MulAut.conj l).toMonoidHom =
    t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj l).injective]
  change (t.LX X 0).map (↑(MulAut.conj l)) ⊓
      (Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)).map
        (↑(MulAut.conj l)) =
    t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)
  have h1 : (t.LX X 0).map (↑(MulAut.conj l)) = t.LX X 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)
  have h2 : (Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)).map
      (↑(MulAut.conj l)) = Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNcent hl)
  rw [h1, h2]

private theorem ArcSz.charTwo_top {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0)
    (hZ : ¬ L1 ≤ ((L1 ⊔ t.Qv 0) ⊓
      centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G)) ⊔ t.Qv 0)
    {C : Subgroup G} (hCsub : C ≤ t.LX X 0) (hCcent : C ≤
      Subgroup.centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G))
    (hCB : C ≤ L1 ⊔ t.Qv 0) (hCN : C ≤ Subgroup.normalizer (t.Qv 0 : Set G))
    (hLC : t.LX X 0 ≤ C ⊔ pCoreOf 2 (t.LX X 0)) : False := by
  have hB : L1 ⊔ t.Qv 0 = C ⊔ t.Qv 0 := by
    have hE : pCoreOf 2 (t.LX X 0) ≤ t.Qv 0 :=
      (ArcSz.pCoreOf_LX_zero t hfr hX).le.trans inf_le_left
    refine le_antisymm ?_ ?_
    · calc L1 ⊔ t.Qv 0 = t.LX X 0 ⊔ t.Qv 0 :=
            (ArcSz.LX_zero_sup_Qv_zero t hfr hX hcov).symm
        _ ≤ (C ⊔ pCoreOf 2 (t.LX X 0)) ⊔ t.Qv 0 := sup_le_sup hLC le_rfl
        _ = C ⊔ t.Qv 0 := by rw [sup_assoc, sup_eq_right.mpr hE]
    · calc C ⊔ t.Qv 0 ≤ t.LX X 0 ⊔ t.Qv 0 :=
          sup_le (hCsub.trans le_sup_left) le_sup_right
        _ = L1 ⊔ t.Qv 0 := ArcSz.LX_zero_sup_Qv_zero t hfr hX hcov
  have hle : L1 ≤ ((L1 ⊔ t.Qv 0) ⊓
      Subgroup.centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G)) ⊔ t.Qv 0 := by
    intro l hl
    have hlin : l ∈ t.Qv 0 ⊔ C := by rw [sup_comm, ← hB]; exact Subgroup.mem_sup_left hl
    obtain ⟨q, hq, c, hc, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (H := t.Qv 0) (K := C) hCN).mp hlin
    have hm : q * c ∈ t.Qv 0 ⊔ ((L1 ⊔ t.Qv 0) ⊓
        Subgroup.centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G)) :=
      Subgroup.mul_mem_sup hq ⟨hCB hc, hCcent hc⟩
    rwa [sup_comm] at hm
  exact hZ hle

private theorem ArcSz.charTwo_setup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hX2 : IsPGroup 2 X) :
    (t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)) ≤
      Subgroup.centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G) ∧
    (t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)) ≤
      L1 ⊔ t.Qv 0 ∧
    (t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)) ≤
      Subgroup.normalizer (t.Qv 0 : Set G) := by
  have hZL : t.Zv 1 ⊓ t.Qv 0 ≤ pCoreOf 2 (t.LX X 0) := by
    rw [ArcSz.pCoreOf_LX_zero t hfr hX]
    exact le_inf inf_le_right (inf_le_left.trans (ArcSz.Zv_one_le_MX_zero t hfr hX hX2))
  have hCcent : (t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)) ≤
      Subgroup.centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G) := by
    intro c hc
    exact (Subgroup.centralizer_le
      (s := ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G))
      (t := (pCoreOf 2 (t.LX X 0) : Set G)) hZL) hc.2
  have hCB : (t.LX X 0 ⊓ Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)) ≤
      L1 ⊔ t.Qv 0 := inf_le_left.trans (ArcSz.LX_zero_le_sup t hfr)
  have hL1norm : L1 ≤ Subgroup.normalizer (t.Qv 0 : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans (Gv_zero t).ge).trans
      (Gv_le_normalizer_Qv t 0)
  exact ⟨hCcent, hCB, hCB.trans (sup_le hL1norm Subgroup.le_normalizer)⟩

private theorem ArcSz.charTwo_top_case {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0)
    (hZ : ¬ L1 ≤ ((L1 ⊔ t.Qv 0) ⊓
      centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G)) ⊔ t.Qv 0)
    {C : Subgroup G} (hCsub : C ≤ t.LX X 0)
    (π : ↥(t.LX X 0) →* oTwoQuot ↥(t.LX X 0))
    (hπ : π = QuotientGroup.mk' (CFSG.pCore 2 ↥(t.LX X 0)))
    (N : Subgroup (oTwoQuot ↥(t.LX X 0)))
    (hN : N = (C.subgroupOf (t.LX X 0)).map π) (htop : N = ⊤)
    (hCcent : C ≤ Subgroup.centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G))
    (hCB : C ≤ L1 ⊔ t.Qv 0) (hCN : C ≤ Subgroup.normalizer (t.Qv 0 : Set G)) : False := by
  have hLC : t.LX X 0 ≤ C ⊔ pCoreOf 2 (t.LX X 0) := by
    intro l hl
    have hlπ : π ⟨l, hl⟩ ∈ (C.subgroupOf (t.LX X 0)).map π := by
      rw [← hN, htop]
      trivial
    obtain ⟨c, hc, hcl⟩ := Subgroup.mem_map.mp hlπ
    have hq : (⟨c, c.2⟩ : ↥(t.LX X 0))⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥(t.LX X 0) := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(t.LX X 0))
          ((⟨c, c.2⟩ : ↥(t.LX X 0))⁻¹ * ⟨l, hl⟩) = 1 := by
        rw [← hπ, map_mul, map_inv, hcl, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hq' : ((c : G))⁻¹ * l ∈ pCoreOf 2 (t.LX X 0) := by
      rw [← CFSG.openPCoreOf_subgroupOf] at hq
      exact Subgroup.mem_subgroupOf.mp hq
    have hl' : l = c * ((c : G)⁻¹ * l) := by group
    rw [hl']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hc) hq'
  exact ArcSz.charTwo_top t hfr hX hcov hZ hCsub hCcent hCB hCN hLC

private theorem ArcSz.charTwo_LX_zero
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hX2 : IsPGroup 2 X)
    (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0)
    (hZ : ¬ L1 ≤ ((L1 ⊔ t.Qv 0) ⊓ centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G)) ⊔ t.Qv 0) :
    CharTwo (t.LX X 0) := by
  classical
  obtain ⟨eSz⟩ := ArcSz.isSzQuot_LX_zero t hfr hX hcov
  haveI : IsSimpleGroup ↥(Sz a) := ArcSz.isSimpleGroup_sz hfr
  let C : Subgroup G := t.LX X 0 ⊓
    Subgroup.centralizer (pCoreOf 2 (t.LX X 0) : Set G)
  have hCnorm : (C.subgroupOf (t.LX X 0)).Normal := by
    simpa only [C] using ArcSz.charTwo_normal t
  let π : ↥(t.LX X 0) →* oTwoQuot ↥(t.LX X 0) :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥(t.LX X 0))
  let N : Subgroup (oTwoQuot ↥(t.LX X 0)) := (C.subgroupOf (t.LX X 0)).map π
  haveI hNnormal : N.Normal := by
    dsimp only [N]
    infer_instance
  have hNimg : N = ⊥ ∨ N = ⊤ := normal_eq_bot_or_top_of_mulEquiv eSz N
  obtain ⟨hCcent, hCB, hCN⟩ := by
    simpa only [C] using ArcSz.charTwo_setup t hfr hX hX2
  rcases hNimg with hbot | htop
  · intro x hx
    have hxL : x ∈ t.LX X 0 := hx.1
    have hxπ : π ⟨x, hxL⟩ = 1 := by
      have hmem : π ⟨x, hxL⟩ ∈ N := Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hx, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    have hxker : (⟨x, hxL⟩ : ↥(t.LX X 0)) ∈ CFSG.pCore 2 ↥(t.LX X 0) :=
      (QuotientGroup.eq_one_iff _).mp hxπ
    rw [← CFSG.openPCoreOf_subgroupOf 2 (t.LX X 0)] at hxker
    exact Subgroup.mem_subgroupOf.mp hxker
  · exfalso
    exact ArcSz.charTwo_top_case t hfr hX hcov hZ
      (inf_le_left : C ≤ t.LX X 0) π rfl N rfl htop hCcent hCB hCN

private theorem ArcSz.noCharNormal_pX_LX_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X)
    (hnc : NoCharNormal (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0)) :
    NoCharNormal (t.Qv 1 ⊓ t.MX X 0) (t.LX X 0) := by
  intro C hCP hCne hCchar hLXnorm
  apply hnc C hCP hCne hCchar
  have hP : IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.LX X 0) :=
    ArcSz.isSylowTwoOf_pX_LX_zero t hfr hX
  have hfratt := CFSG.Quasithin.H13.Ch4.sup_inf_normalizer_eq
    (M := t.MX X 0) (N := t.LX X 0) (P := t.Qv 1 ⊓ t.MX X 0)
    (oTwoPrime_le (t.MX X 0)) (le_normalizer_oTwoPrime (t.MX X 0)) hP
  have hcharN : Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    haveI : (C.subgroupOf (t.Qv 1 ⊓ t.MX X 0)).Characteristic := hCchar
    have hmap : (C.subgroupOf (t.Qv 1 ⊓ t.MX X 0)).map
        (t.Qv 1 ⊓ t.MX X 0).subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := t.Qv 1 ⊓ t.MX X 0) (K := C.subgroupOf (t.Qv 1 ⊓ t.MX X 0))
    rwa [hmap] at h
  rw [← hfratt]
  exact sup_le hLXnorm (inf_le_right.trans hcharN)

private theorem ArcSz.map_Gv_zero_conj_of_swap {s : G}
    (hs : t.x₂⁻¹ * s ∈ t.Gv 0) :
    (t.Gv 0).map (MulAut.conj s).toMonoidHom = t.Gv 2 := by
  have hu : t.x₂⁻¹ * s ∈ t.Gv 0 := hs
  have hmapu : (t.Gv 0).map (MulAut.conj (t.x₂⁻¹ * s)).toMonoidHom = t.Gv 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
  have hseq : s = t.x₂ * (t.x₂⁻¹ * s) := by group
  have hcomp : ((MulAut.conj t.x₂).toMonoidHom.comp
      (MulAut.conj (t.x₂⁻¹ * s)).toMonoidHom) = (MulAut.conj s).toMonoidHom := by
    rw [hseq]
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  calc (t.Gv 0).map (MulAut.conj s).toMonoidHom
      = (t.Gv 0).map ((MulAut.conj t.x₂).toMonoidHom.comp
          (MulAut.conj (t.x₂⁻¹ * s)).toMonoidHom) := by rw [hcomp]
    _ = ((t.Gv 0).map (MulAut.conj (t.x₂⁻¹ * s)).toMonoidHom).map
          (MulAut.conj t.x₂).toMonoidHom := by rw [Subgroup.map_map]
    _ = (t.Gv 0).map (MulAut.conj t.x₂).toMonoidHom := by rw [hmapu]
    _ = t.Gv 2 := t.map_Gv_x₂ 0

private theorem ArcSz.pair_of_hpair
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {R : Subgroup G} (hR : R ≠ ⊥)
    (hRw : R ≤ t.Gw 0 2)
    (htrans0 : CosetTrans (Subgroup.normalizer (R : Set G)) (t.Gv 0) (t.Gv 1))
    (hpair : (∀ g ∈ normIn R (t.Gv 1), g ∈ t.Gv 0 ⊓ t.Gv 2 ∨
        t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨ L2 ≤ normIn R (t.Gv 1) ⊔ t.Qv 1) :
    ∀ g ∈ normIn R (t.Gv 1), g ∈ t.Gv 0 ⊓ t.Gv 2 ∨
      t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2 := by
  rcases hpair with hp | hL2
  · exact hp
  · exfalso
    have hle : R ≤ t.Gv 0 ⊓ t.Gv 1 ⊓ t.Gv 2 := by
      rwa [Gw_zero_two t] at hRw
    have htrans1 : CosetTrans (Subgroup.normalizer (R : Set G)) (t.Gv 1) (t.Gv 0) :=
      (cosetTrans_one_of_le_sup t hfr inf_le_right hL2).mono inf_le_left
    have hRle : R ≤ t.Gv 0 ⊓ t.Gv 1 := by
      refine le_inf ?_ ?_
      · exact (hle.trans (inf_le_left : t.Gv 0 ⊓ t.Gv 1 ⊓ t.Gv 2 ≤ t.Gv 0 ⊓ t.Gv 1)).trans
          (inf_le_left : t.Gv 0 ⊓ t.Gv 1 ≤ t.Gv 0)
      · exact (hle.trans (inf_le_left : t.Gv 0 ⊓ t.Gv 1 ⊓ t.Gv 2 ≤ t.Gv 0 ⊓ t.Gv 1)).trans
          (inf_le_right : t.Gv 0 ⊓ t.Gv 1 ≤ t.Gv 1)
    exact hR (eq_bot_of_cosetTrans t hfr hRle htrans0 htrans1)

private theorem ArcSz.arcSz_of_le
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) {R : Subgroup G} (hR : R ≠ ⊥)
    (hRw : R ≤ t.Gw 0 2) (hM : t.MX X 0 ≤ normalizer (R : Set G))
    (hK : t.K ≤ normalizer (R : Set G)) {s : G} (hs1 : s ∈ normIn R (t.Gv 1))
    (hs : t.x₂⁻¹ * s ∈ t.Gv 0 ⊓ t.Gv 2)
    (hpair : (∀ g ∈ normIn R (t.Gv 1), g ∈ t.Gv 0 ⊓ t.Gv 2 ∨
        t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨ L2 ≤ normIn R (t.Gv 1) ⊔ t.Qv 1) :
    t.ArcSz R := by
  have hle : R ≤ t.Gv 0 ⊓ t.Gv 1 ⊓ t.Gv 2 := by
    rwa [Gw_zero_two t] at hRw
  have hsR : s ∈ Subgroup.normalizer (R : Set G) := hs1.1
  have htrans0 : CosetTrans (Subgroup.normalizer (R : Set G)) (t.Gv 0) (t.Gv 1) := by
    intro g hg
    obtain ⟨n, hn, hnb⟩ := hX.trans₀ g hg
    exact ⟨n, ⟨hM hn, hn.2⟩, hnb⟩
  have hmapR : (Subgroup.normalizer (R : Set G)).map (MulAut.conj s).toMonoidHom =
      Subgroup.normalizer (R : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsR)
  have hmap1 : (t.Gv 1).map (MulAut.conj s).toMonoidHom = t.Gv 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs1.2)
  have hmap0 : (t.Gv 0).map (MulAut.conj s).toMonoidHom = t.Gv 2 :=
    ArcSz.map_Gv_zero_conj_of_swap t hs.1
  have htrans2 : CosetTrans (Subgroup.normalizer (R : Set G)) (t.Gv 2) (t.Gv 1) := by
    have h := htrans0.map_conj s
    rwa [hmapR, hmap0, hmap1] at h
  refine ⟨hR, hle, hK, htrans0, htrans2, ?_, ⟨s, hs1, hs⟩⟩
  exact ArcSz.pair_of_hpair t hfr hR hRw htrans0 hpair

private theorem ArcSzMax.MX_eq_of_le (hX : t.ArcSzMax X) {R : Subgroup G} (hR : t.ArcSz R)
    (hR2 : IsPGroup 2 R) (hM : t.MX X 0 ≤ normalizer (R : Set G)) :
    t.MX R 0 = t.MX X 0 := by
  have hle : t.MX X 0 ≤ t.MX R 0 := le_inf hM inf_le_right
  exact le_antisymm (hX.2.2 R hR hR2 hle) hle

private theorem ArcSzMax.swap_mem_normalizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSzMax X)
    {C : Subgroup G} (hCP : C ≤ t.Qv 1 ⊓ t.MX X 0)
    (hCchar : (C.subgroupOf (t.Qv 1 ⊓ t.MX X 0)).Characteristic) :
    ∃ s : G, (s ∈ normIn C (t.Gv 1) ∧ t.x₂⁻¹ * s ∈ t.Gv 0 ⊓ t.Gv 2) ∧
      Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) ≤
        Subgroup.normalizer (C : Set G) := by
  have hQv1leG0 : t.Qv 1 ≤ t.Gv 0 := (t.Qv_le_Gv hfr 1).1
  have hQv1leG2 : t.Qv 1 ≤ t.Gv 2 := (t.Qv_le_Gv hfr 1).2
  have hcharN : Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    haveI : (C.subgroupOf (t.Qv 1 ⊓ t.MX X 0)).Characteristic := hCchar
    have hmap : (C.subgroupOf (t.Qv 1 ⊓ t.MX X 0)).map
        (t.Qv 1 ⊓ t.MX X 0).subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := t.Qv 1 ⊓ t.MX X 0) (K := C.subgroupOf (t.Qv 1 ⊓ t.MX X 0))
    rwa [hmap] at h
  obtain ⟨s, hs1X, hsX⟩ := hX.1.swap
  have hmapQ : (t.Qv 1).map (MulAut.conj s).toMonoidHom = t.Qv 1 := by
    rw [t.Qv_eq 1]
    change (pCoreOf 2 (t.Gv 1)).map (↑(MulAut.conj s)) = pCoreOf 2 (t.Gv 1)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((le_normalizer_pCoreOf 2 (t.Gv 1)) hs1X.2)
  have hmapN : (Subgroup.normalizer (X : Set G)).map
      (MulAut.conj s).toMonoidHom = Subgroup.normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs1X.1)
  have hmapG0 : (t.Gv 0).map (MulAut.conj s).toMonoidHom = t.Gv 2 :=
    ArcSz.map_Gv_zero_conj_of_swap t hsX.1
  have hsP : s ∈ Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (t.Qv 1 ⊓ t.MX X 0).map (MulAut.conj s).toMonoidHom =
      t.Qv 1 ⊓ t.MX X 0
    rw [show t.MX X 0 = Subgroup.normalizer (X : Set G) ⊓ t.Gv 0 from rfl,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective]
    change (t.Qv 1).map (MulAut.conj s).toMonoidHom ⊓
        ((Subgroup.normalizer (X : Set G)).map (MulAut.conj s).toMonoidHom ⊓
          (t.Gv 0).map (MulAut.conj s).toMonoidHom) =
      t.Qv 1 ⊓ (Subgroup.normalizer (X : Set G) ⊓ t.Gv 0)
    rw [hmapQ, hmapN, hmapG0]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxQ, hxN, _⟩
      exact ⟨hxQ, hxN, hQv1leG0 hxQ⟩
    · rintro ⟨hxQ, hxN, _⟩
      exact ⟨hxQ, hxN, hQv1leG2 hxQ⟩
  exact ⟨s, ⟨⟨hcharN hsP, hs1X.2⟩, hsX⟩, hcharN⟩

private theorem ArcSzMax.pX_sylow_contradiction {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcSzMax X)
    (hNleMX : Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) ⊓
      t.Gv 0 ≤ t.MX X 0) : False := by
  have hPsylMX : IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0) :=
    ArcSz.isSylowTwoOf_pX_MX_zero t hfr hX.1
  have hPsylOfMX : CFSG.ABGLocalTools.IsSylowOf 2 (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0) :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mp hPsylMX
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0 ⊓ t.Gv 0) := by
    rwa [inf_eq_left.mpr (inf_le_right : t.MX X 0 ≤ t.Gv 0)]
  have hPsylOfG0 : CFSG.ABGLocalTools.IsSylowOf 2 (t.Qv 1 ⊓ t.MX X 0) (t.Gv 0) :=
    CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le
      (H := t.MX X 0) (M := t.Gv 0) (T := t.Qv 1 ⊓ t.MX X 0) hT' hNleMX
  have hPsylG0 : IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.Gv 0) :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mpr hPsylOfG0
  have hSleG0 : S ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S)
  have hQv1leS : t.Qv 1 ≤ S := by
    rw [t.Qv_one]
    exact Q2_le_S hfr.hF
  have hQSrel : (t.Qv 1).relIndex S = 2 ^ f := by
    have h := (t.relIndex_Qv_pCoreOf hfr 1).1
    norm_num at h
    rwa [t.pCoreOf_Gw_zero_one hfr] at h
  have hf0 : f ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hfr.hf)
  have hPleQ : t.Qv 1 ⊓ t.MX X 0 ≤ t.Qv 1 := inf_le_left
  have hPleS : t.Qv 1 ⊓ t.MX X 0 ≤ S := hPleQ.trans hQv1leS
  have h2S : 2 ∣ (t.Qv 1 ⊓ t.MX X 0).relIndex S := by
    rw [← Subgroup.relIndex_mul_relIndex (t.Qv 1 ⊓ t.MX X 0) (t.Qv 1) S hPleQ hQv1leS]
    exact dvd_mul_of_dvd_right (by rw [hQSrel]; exact dvd_pow_self 2 hf0) _
  have h2G0 : 2 ∣ (t.Qv 1 ⊓ t.MX X 0).relIndex (t.Gv 0) := by
    rw [← Subgroup.relIndex_mul_relIndex (t.Qv 1 ⊓ t.MX X 0) S (t.Gv 0) hPleS hSleG0]
    exact dvd_mul_of_dvd_left h2S _
  have h2sub : 2 ∣ ((t.Qv 1 ⊓ t.MX X 0).subgroupOf (t.Gv 0)).index := by
    simpa only [Subgroup.relIndex] using h2G0
  exact hPsylG0.2.2 h2sub

theorem ArcSzMax.noCharNormal
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSzMax X)
    (hpair : ∀ R : Subgroup G, t.K ≤ normalizer (R : Set G) → (∃ s ∈ normIn R (t.Gv 1),
        t.x₂⁻¹ * s ∈ t.Gv 0 ⊓ t.Gv 2) → (∀ g ∈ normIn R (t.Gv 1), g ∈ t.Gv 0 ⊓ t.Gv 2 ∨
        t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨ L2 ≤ normIn R (t.Gv 1) ⊔ t.Qv 1) :
    NoCharNormal (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0) := by
  classical
  intro C hCP hCne hCchar hnorm
  have hQv1leG0 : t.Qv 1 ≤ t.Gv 0 := (t.Qv_le_Gv hfr 1).1
  have hQv1leG2 : t.Qv 1 ≤ t.Gv 2 := (t.Qv_le_Gv hfr 1).2
  have hQv1leG1 : t.Qv 1 ≤ t.Gv 1 := t.Qv_le_Gv_self 1
  have hQv1leGw : t.Qv 1 ≤ t.Gw 0 2 := by
    rw [Gw_zero_two t]
    exact le_inf (le_inf hQv1leG0 hQv1leG1) hQv1leG2
  have hCw : C ≤ t.Gw 0 2 := (hCP.trans inf_le_left).trans hQv1leGw
  have hKC : t.K ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf hX.1.K_le (t.K_le_Gv 0)).trans hnorm
  have hC2 : IsPGroup 2 C := (isPGroup_Qv t 1).to_le (hCP.trans inf_le_left)
  obtain ⟨s, ⟨hs1C, hsX⟩, hcharN⟩ := ArcSzMax.swap_mem_normalizer t hfr hX hCP hCchar
  have hCclass : t.ArcSz C :=
    ArcSz.arcSz_of_le t hfr hX.1 hCne hCw hnorm hKC hs1C hsX
      (hpair C hKC ⟨s, hs1C, hsX⟩)
  have hMXeq : t.MX C 0 = t.MX X 0 :=
    ArcSzMax.MX_eq_of_le t hX hCclass hC2 hnorm
  have hNleMX : Subgroup.normalizer ((t.Qv 1 ⊓ t.MX X 0 : Subgroup G) : Set G) ⊓
      t.Gv 0 ≤ t.MX X 0 := by
    intro x hx
    have hxMX : x ∈ t.MX C 0 := ⟨hcharN hx.1, hx.2⟩
    rwa [hMXeq] at hxMX
  exact ArcSzMax.pX_sylow_contradiction t hfr hX hNleMX

theorem ArcSz.structure_LX_zero
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSz X) (hX2 : IsPGroup 2 X)
    (hcov : L1 ≤ t.MX X 0 ⊔ t.Qv 0) :
    Nonempty (oTwoQuot ↥(t.LX X 0) ≃* Sz a) ∧ CharTwo (t.LX X 0) ∧
      IsSylowTwoOf (t.Qv 1 ⊓ t.MX X 0) (t.LX X 0) ∧
      (NoCharNormal (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0) →
        NoCharNormal (t.Qv 1 ⊓ t.MX X 0) (t.LX X 0)) := by
  exact ⟨ArcSz.isSzQuot_LX_zero t hfr hX hcov,
    ArcSz.charTwo_LX_zero t hfr hX hX2 hcov (t.not_le_centralizer_sup_zero hfr),
    ArcSz.isSylowTwoOf_pX_LX_zero t hfr hX,
    ArcSz.noCharNormal_pX_LX_zero t hfr hX⟩

theorem not_arcSz_QT {a f : ℕ}
    (hQ : t.ArcSz t.QT)
    (hmax : ∀ Y : Subgroup G, t.ArcSzMax Y → NoCharNormal (t.Qv 1 ⊓ t.MX Y 0) (t.MX Y 0))
    (hcov : ∀ Y : Subgroup G, t.ArcSz Y → L1 ≤ t.MX Y 0 ⊔ t.Qv 0)
    (hO : ∀ Y : Subgroup G, t.ArcSz Y → IsPGroup 2 Y → L1 ≤ t.MX Y 0 ⊔ t.Qv 0 →
      Nonempty (oTwoQuot ↥(t.LX Y 0) ≃* Sz a) ∧ CharTwo (t.LX Y 0) ∧
        IsSylowTwoOf (t.Qv 1 ⊓ t.MX Y 0) (t.LX Y 0) ∧
        (NoCharNormal (t.Qv 1 ⊓ t.MX Y 0) (t.MX Y 0) →
          NoCharNormal (t.Qv 1 ⊓ t.MX Y 0) (t.LX Y 0)))
    (hpush : ∀ H T : Subgroup G, Nonempty (oTwoQuot ↥H ≃* Sz a) → CharTwo H →
      IsSylowTwoOf T H → ¬ NoCharNormal T H) : False := by
  have hQT2 : IsPGroup 2 t.QT := pCoreOf_isPGroup 2 t.GT
  obtain ⟨Y, hYmax, hQY⟩ := exists_arcSzMax t hQ hQT2
  have hYclass : t.ArcSz Y := hYmax.1
  have hY2 : IsPGroup 2 Y := hYmax.2.1
  have hcovY : L1 ≤ t.MX Y 0 ⊔ t.Qv 0 := hcov Y hYclass
  obtain ⟨hSzY, hCharY, hSylY, hncY⟩ := hO Y hYclass hY2 hcovY
  exact hpush (t.LX Y 0) (t.Qv 1 ⊓ t.MX Y 0) hSzY hCharY hSylY
    (hncY (hmax Y hYmax))

end Track

end CFSG.Quasithin.Stroth.Rq

end
