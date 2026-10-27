module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5Setup
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Count
public import CFSG.GroupTheory.KleinFourCocycle
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5
public import CFSG.Quasithin.Background.SpecialPowCenter

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem isElemSec_bot_of_isElemAbelian {E : Subgroup H} (hE : IsElemAbelian 2 E) :
    IsElemSec (⊥ : Subgroup H) E :=
  ⟨bot_le, (F7.commutator_self_eq_bot hE).le, fun e he => by
    rw [hE.2 e he]; exact Subgroup.one_mem _⟩

private theorem f112sa_nontriv {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h2 : VA5 L2) {K₀ : Subgroup H}
    (hK₀c : ∀ z ∈ K₀, ∀ e ∈ f112saP2' L1 L2 S, z * e = e * z)
    (hK₀2 : ∀ z ∈ K₀, z ^ 2 = 1) :
    ∃ k ∈ oTwoRes L2, ∃ q ∈ pCoreOf 2 (f112saP2' L1 L2 S), ⁅k, q⁆ ∉ K₀ := by
  obtain ⟨k, hkX, -, hk3, -⟩ := f112sa_exists_k hF h2
  have hkR : k ∈ oTwoRes L2 := f112sa_X2_le_oTwoRes L1 L2 S hkX
  have hkE : k ∈ f112saP2' L1 L2 S := (le_sup_left : oTwoRes L2 ≤ f112saP2' L1 L2 S) hkR
  by_contra hall
  push Not at hall
  have hcomm : ∀ q ∈ pCoreOf 2 (f112saP2' L1 L2 S), k * q = q * k := fun q hq =>
    commutatorElement_eq_one_iff_mul_comm.mp
      (CFSG.GroupTheory.commutatorElement_eq_one_of_pow_three
        (by rw [← hk3]; exact pow_orderOf_eq_one k)
        (fun z hz => (hK₀c z hz k hkE).symm) hK₀2 (hall k hkR q hq))
  have hkQ : k ∈ pCoreOf 2 (f112saP2' L1 L2 S) :=
    f112sa_charTwo_P2' hF.toW
      ⟨hkE, Subgroup.mem_centralizer_iff.mpr fun q hq => (hcomm q hq).symm⟩
  obtain ⟨n, hn⟩ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP2' L1 L2 S)) ⟨k, hkQ⟩
  have h3 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg (fun x : ↥(pCoreOf 2 (f112saP2' L1 L2 S)) => (x : H)) hn)
  rw [hk3] at h3
  exact absurd (Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)

theorem f112sa_irred {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) {K₀ : Subgroup H}
    (hsec : IsElemSec K₀ (pCoreOf 2 (f112saP2' L1 L2 S)))
    (hidx : K₀.relIndex (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ 16)
    (hK₀n : f112saP2' L1 L2 S ≤ Subgroup.normalizer (K₀ : Set H))
    (hK₀c : ∀ z ∈ K₀, ∀ e ∈ f112saP2' L1 L2 S, z * e = e * z)
    (hK₀2 : ∀ z ∈ K₀, z ^ 2 = 1) :
    ∀ W : Subgroup H, K₀ ≤ W → W ≤ pCoreOf 2 (f112saP2' L1 L2 S) →
      f112saP2' L1 L2 S ≤ Subgroup.normalizer (W : Set H) →
        W = K₀ ∨ W = pCoreOf 2 (f112saP2' L1 L2 S) := by
  obtain ⟨k, hk, q, hq, hkq⟩ := f112sa_nontriv hF h2 hK₀c hK₀2
  exact (leafFaithfulA5 le_rfl Subgroup.le_normalizer
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hK₀n hsec hidx
    (f112sa_isL2Quot_P2' hF h1 h2)
    (fun q hq e he => hsec.2.1 (Subgroup.commutator_mem_commutator hq he))
    ⟨k, (le_sup_left : oTwoRes L2 ≤ f112saP2' L1 L2 S) hk, q, hq, hkq⟩).irred

theorem f112sa_indec_sup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) {K₀ : Subgroup H}
    (hsec : IsElemSec K₀ (pCoreOf 2 (f112saP2' L1 L2 S)))
    (hidx : K₀.relIndex (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ 16)
    (hK₀n : f112saP2' L1 L2 S ≤ Subgroup.normalizer (K₀ : Set H))
    (hK₀c : ∀ z ∈ K₀, ∀ e ∈ f112saP2' L1 L2 S, z * e = e * z)
    (hK₀2 : ∀ z ∈ K₀, z ^ 2 = 1) :
    ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoRes L2⁆ ⊔ K₀ =
      pCoreOf 2 (f112saP2' L1 L2 S) := by
  have hAQ : oTwoRes L2 ≤
      Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) :=
    (le_sup_left : oTwoRes L2 ≤ f112saP2' L1 L2 S).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hAK : oTwoRes L2 ≤ Subgroup.normalizer (K₀ : Set H) :=
    (le_sup_left : oTwoRes L2 ≤ f112saP2' L1 L2 S).trans hK₀n
  exact CFSG.GroupTheory.commutator_sup_eq_of_irreducible hsec.1 hsec.2.1 hAQ hAK
    (fun W hKW hWQ hWN => f112sa_irred hF h1 h2 hsec hidx hK₀n hK₀c hK₀2 W hKW hWQ
      ((f112sa_P2'_eq_oTwoRes_sup hF h1 h2).le.trans hWN))
    (f112sa_nontriv hF h2 hK₀c hK₀2)

theorem f112sa_two_elem_normalizer_QA
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) {c : H} (hcS : c ∈ S) :
    (∃ m : ℕ, c ^ 2 ^ m = 1) ∧
      c ∈ Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨m, by simpa using congrArg (fun x : ↥S => (x : H)) hm⟩
  · exact f112sa_P2_le_normalizer_QA hF
      (((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)) hcS)

private theorem f112sa_bot_sec_facts {L1 L2 S : Subgroup H}
    (hU : S3A5U42Hyp L1 L2 S) :
    IsElemSec (⊥ : Subgroup H) (pCoreOf 2 (f112saP2' L1 L2 S)) ∧
      f112saP2' L1 L2 S ≤ Subgroup.normalizer ((⊥ : Subgroup H) : Set H) ∧
      (⊥ : Subgroup H).relIndex (pCoreOf 2 (f112saP2' L1 L2 S)) ≤ 16 ∧
      (∀ z ∈ (⊥ : Subgroup H), ∀ e ∈ f112saP2' L1 L2 S, z * e = e * z) ∧
      (∀ z ∈ (⊥ : Subgroup H), z ^ 2 = 1) := by
  refine ⟨isElemSec_bot_of_isElemAbelian hU.elem_right, Subgroup.le_normalizer_of_normal,
    ?_, ?_, ?_⟩
  · rw [Subgroup.relIndex_bot_left, hU.card_right]
    norm_num
  · intro z hz e _
    rw [Subgroup.mem_bot.mp hz]
    rw [one_mul, mul_one]
  · intro z hz
    rw [Subgroup.mem_bot.mp hz, one_pow]

theorem f112sa_irred_of_u42Hyp {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hU : S3A5U42Hyp L1 L2 S)
    {W : Subgroup H} (hWQ : W ≤ pCoreOf 2 (f112saP2' L1 L2 S))
    (hWN : f112saP2' L1 L2 S ≤ Subgroup.normalizer (W : Set H)) :
    W = ⊥ ∨ W = pCoreOf 2 (f112saP2' L1 L2 S) := by
  obtain ⟨hbotsec, hbotnorm, hbotidx, hbotc, hbot2⟩ := f112sa_bot_sec_facts hU
  exact f112sa_irred hF h1 h2 hbotsec hbotidx hbotnorm hbotc hbot2 W bot_le hWQ hWN

private theorem f112sa_centralizes_QA_of_mem_S
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hU : S3A5U42Hyp L1 L2 S) {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ f112saP2' L1 L2 S, ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    ∀ q ∈ pCoreOf 2 (f112saP2' L1 L2 S), c * q = q * c := by
  have hirr : ∀ W : Subgroup H, (⊥ : Subgroup H) ≤ W →
      W ≤ pCoreOf 2 (f112saP2' L1 L2 S) →
      f112saP2' L1 L2 S ≤ Subgroup.normalizer (W : Set H) →
        W = ⊥ ∨ W = pCoreOf 2 (f112saP2' L1 L2 S) :=
    fun W _ hWQ hWN => f112sa_irred_of_u42Hyp hF h1 h2 hU hWQ hWN
  obtain ⟨hc2, hcQ⟩ := f112sa_two_elem_normalizer_QA hF hcS
  have hcK : c ∈ Subgroup.normalizer ((⊥ : Subgroup H) : Set H) :=
    Subgroup.le_normalizer_of_normal (K := S) hcS
  intro q hq
  have hmem : ⁅c, q⁆ ∈ (⊥ : Subgroup H) :=
    CFSG.GroupTheory.commutatorElement_mem_of_irreducible
      (L := f112saP2' L1 L2 S) (Q := pCoreOf 2 (f112saP2' L1 L2 S)) (K₀ := ⊥)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) bot_le
      (F7.commutator_self_eq_bot hU.elem_right).le
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) Subgroup.le_normalizer_of_normal hirr
      hc2 hcQ hcK hcL q hq
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

private theorem f112sa_exists_kleinFour_u42
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hU : S3A5U42Hyp L1 L2 S) {c : H}
    (hcentQ : ∀ q ∈ pCoreOf 2 (f112saP2' L1 L2 S), c * q = q * c)
    (hcL : ∀ l ∈ f112saP2' L1 L2 S, ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    ∃ y ∈ pCoreOf 2 (f112saP2' L1 L2 S),
      ∀ l ∈ f112saP2' L1 L2 S, (c * y) * l = l * (c * y) := by
  have hQL : pCoreOf 2 (f112saP2' L1 L2 S) ≤ f112saP2' L1 L2 S :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQT : pCoreOf 2 (f112saP2' L1 L2 S) ≤ S ⊓ f112saK L1 L2 S := f112sa_QA_le_T hF
  have hTL : S ⊓ f112saK L1 L2 S ≤ f112saP2' L1 L2 S := (f112sa_T_sylow_P2' hF.toW).1
  have hQnL : ((pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf
      (f112saP2' L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hcardQ : Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) = 16 := by
    rw [hU.card_right]
    norm_num
  have hTQ : (pCoreOf 2 (f112saP2' L1 L2 S)).relIndex (S ⊓ f112saK L1 L2 S) = 4 := by
    have h := Subgroup.relIndex_mul_card
      (H := pCoreOf 2 (f112saP2' L1 L2 S)) (K := S ⊓ f112saK L1 L2 S)
    rw [inf_eq_left.mpr hQT, f112sa_card_T_eq_QA hF h1 h2, hcardQ] at h
    omega
  have hfix : Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S) ⊓
      Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H)) ≤ 2 := by
    have hle : pCoreOf 2 (f112saP2' L1 L2 S) ⊓
        Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H) ≤
        centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) :=
      (le_inf (inf_le_left.trans hQT) inf_le_right).trans (f112sa_centerOf_T_le_P1' hF)
    calc Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S) ⊓
          Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H))
        ≤ Nat.card ↥(centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) :=
          Subgroup.card_le_of_le hle
      _ = 2 := (H13.commutator_eq_centerOf_of_isSpecialPow (by norm_num) le_rfl
        hU.special_left).2
  have hTodd : Odd ((S ⊓ f112saK L1 L2 S).subgroupOf (f112saP2' L1 L2 S)).index := by
    change Odd ((S ⊓ f112saK L1 L2 S).relIndex (f112saP2' L1 L2 S))
    have h := Subgroup.relIndex_mul_card
      (H := S ⊓ f112saK L1 L2 S) (K := f112saP2' L1 L2 S)
    rw [inf_eq_left.mpr hTL, f112sa_card_P2' hF h1 h2, f112sa_card_T_eq_QA hF h1 h2,
      hcardQ] at h
    have h15 : (S ⊓ f112saK L1 L2 S).relIndex (f112saP2' L1 L2 S) = 15 := by omega
    rw [h15]
    norm_num
  obtain ⟨y, hyQ, hyE⟩ :=
    CFSG.GroupTheory.exists_mul_commute_of_kleinFour_odd_index
      (L := f112saP2' L1 L2 S) (Q := pCoreOf 2 (f112saP2' L1 L2 S))
      (T := S ⊓ f112saK L1 L2 S)
      hQL hQT hTL hQnL hU.elem_right hcardQ hTQ (f112sa_sq_mem_QA hF h1 h2)
      hfix hTodd hcentQ hcL
  exact ⟨y, hyQ, hyE⟩

private theorem f112sa_mem_pCoreOf_of_mul_mem_centralizer
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (hU : S3A5U42Hyp L1 L2 S) {c y : H}
    (hcS : c ∈ S) (hyQ : y ∈ pCoreOf 2 (f112saP2' L1 L2 S))
    (hyE : ∀ l ∈ f112saP2' L1 L2 S, (c * y) * l = l * (c * y)) :
    c ∈ pCoreOf 2 (f112saP2' L1 L2 S) := by
  have hQT : pCoreOf 2 (f112saP2' L1 L2 S) ≤ S ⊓ f112saK L1 L2 S := f112sa_QA_le_T hF
  have hTL : S ⊓ f112saK L1 L2 S ≤ f112saP2' L1 L2 S := (f112sa_T_sylow_P2' hF.toW).1
  have hx0E : ∀ l ∈ f112saP2' L1 L2 S, (c * y) * l = l * (c * y) := hyE
  have hx0B : c * y ∈ bigB L1 L2 S :=
    (bigB L1 L2 S).mul_mem ((le_sup_right : S ≤ bigB L1 L2 S) hcS)
      (f112sa_K_le_bigB L1 L2 S (hQT hyQ).2)
  have hx0T : ∀ t ∈ S ⊓ f112saK L1 L2 S, (c * y) * t = t * (c * y) :=
    fun t ht => hx0E t (hTL ht)
  obtain ⟨z, hzT, hzE⟩ := f112sa_exists_center_conj_eq_P1' hF hx0B hx0T
  have hzQS : z ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) :=
    f112sa_centerOf_T_le_P1' hF hzT
  have hzcent : ∀ x ∈ f112saP1' L1 L2 S, z * x = x * z :=
    commute_of_mem_centerOf_of_card_two
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (H13.commutator_eq_centerOf_of_isSpecialPow (by norm_num) le_rfl
        hU.special_left).2 hzQS
  have hx0P1 : c * y ∈ Subgroup.centralizer (f112saP1' L1 L2 S : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have h1 : (c * y) * x * (c * y)⁻¹ = z * x * z⁻¹ := hzE x hx
      have h2 : z * x * z⁻¹ = x := by
        rw [hzcent x hx, mul_assoc, mul_inv_cancel, mul_one]
      have h3 : (c * y) * x * (c * y)⁻¹ = x := by rw [h1, h2]
      have h4 : (c * y) * x = x * (c * y) := by
        calc (c * y) * x = ((c * y) * x * (c * y)⁻¹) * (c * y) := by group
          _ = x * (c * y) := by rw [h3]
      exact h4.symm
  have hx0P2 : c * y ∈ Subgroup.centralizer (f112saP2' L1 L2 S : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hx0E x hx).symm
  have hx0bot : c * y ∈ (⊥ : Subgroup H) := by
    have h : c * y ∈ bigB L1 L2 S ⊓
        Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
        Subgroup.centralizer (f112saP2' L1 L2 S : Set H) := ⟨⟨hx0B, hx0P1⟩, hx0P2⟩
    rwa [f112sa_core_free hF] at h
  have hx0 : c * y = 1 := Subgroup.mem_bot.mp hx0bot
  rw [eq_inv_of_mul_eq_one_left hx0]
  exact (pCoreOf 2 (f112saP2' L1 L2 S)).inv_mem hyQ

theorem f112sa_ker_right_u42 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hU : S3A5U42Hyp L1 L2 S) {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ f112saP2' L1 L2 S, ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    c ∈ pCoreOf 2 (f112saP2' L1 L2 S) := by
  obtain ⟨y, hyQ, hyE⟩ := f112sa_exists_kleinFour_u42 hF h1 h2 hU
    (f112sa_centralizes_QA_of_mem_S hF h1 h2 hU hcS hcL) hcL
  exact f112sa_mem_pCoreOf_of_mul_mem_centralizer hF hU hcS hyQ hyE

theorem s3a5ModuleFacts_of_u42Hyp {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hU : S3A5U42Hyp L1 L2 S) : S3A5ModuleFacts L1 L2 S := by
  obtain ⟨hbotsec, hbotnorm, hbotidx, hbotc, hbot2⟩ := f112sa_bot_sec_facts hU
  refine ⟨fun c hc hcL => f112sa_ker_right_u42 hF h1 h2 hU hc hcL, ?_, ?_⟩
  · have h := f112sa_indec_sup hF h1 h2 (K₀ := ⊥) hbotsec hbotidx hbotnorm hbotc hbot2
    simpa using h
  · intro d hd hd3 e he hed
    have hc : e ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) :=
      hU.nat_left d hd hd3 e he (by
        rw [show ⁅e, d⁆ = 1 by rw [commutatorElement_def, hed]; group]
        exact Subgroup.one_mem _)
    exact ⟨(H13.commutator_eq_centerOf_of_isSpecialPow (by norm_num) le_rfl
      hU.special_left).1.ge hc, hc.2⟩

end CFSG.Quasithin.F112R.St84
