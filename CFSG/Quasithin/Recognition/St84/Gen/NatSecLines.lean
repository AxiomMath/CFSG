module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.Quasithin.Recognition.St84.PushUp
import CFSG.Quasithin.EmptyFaithful.R3c5Gen
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem relCent_le_of_normalizer {E Z A : Subgroup G} (hZE : Z ≤ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) : Z ≤ relCent E Z A := by
  intro z hz
  rw [mem_relCent hEZ]
  refine ⟨hZE hz, fun a ha => ?_⟩
  have h : a * z⁻¹ * a⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hAZ ha) z⁻¹).mp (Z.inv_mem hz)
  have e : ⁅z, a⁆ = z * (a * z⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Z.mul_mem hz h

private theorem commutator_sup_relCent_le {E Z T T' : Subgroup G}
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G))
    (hT'Z : T' ≤ Subgroup.normalizer (Z : Set G)) :
    ⁅T ⊔ T', relCent E Z T ⊓ relCent E Z T'⁆ ≤ Z := by
  have hT : ⁅T, relCent E Z T ⊓ relCent E Z T'⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro t ht x hx
    have hxt : ⁅x, t⁆ ∈ Z :=
      ((mem_relCent hEZ).mp (Subgroup.mem_inf.mp hx).1).2 t ht
    simpa [commutatorElement_inv] using Z.inv_mem hxt
  have hT' : ⁅T', relCent E Z T ⊓ relCent E Z T'⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro t ht x hx
    have hxt : ⁅x, t⁆ ∈ Z :=
      ((mem_relCent hEZ).mp (Subgroup.mem_inf.mp hx).2).2 t ht
    simpa [commutatorElement_inv] using Z.inv_mem hxt
  exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
    T T' (relCent E Z T ⊓ relCent E Z T') Z hT hT' hTZ hT'Z

private def omegaPreimage (E Z : Subgroup G) : Subgroup G where
  carrier := {e | e ∈ E ∧ e ∈ Subgroup.normalizer (Z : Set G) ∧
    (∀ x ∈ E, ⁅e, x⁆ ∈ Z) ∧ e ^ 2 ∈ Z}
  one_mem' := by
    refine ⟨E.one_mem, Subgroup.one_mem _, fun x _ => ?_, ?_⟩
    · rw [commutatorElement_def]
      simp
    · rw [one_pow]
      exact Z.one_mem
  mul_mem' := by
    rintro e f ⟨heE, heN, hec, he2⟩ ⟨hfE, hfN, hfc, hf2⟩
    refine ⟨E.mul_mem heE hfE, Subgroup.mul_mem _ heN hfN, fun x hx => ?_, ?_⟩
    · have h1 : e * ⁅f, x⁆ * e⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp heN ⁅f, x⁆).mp (hfc x hx)
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem h1 (hec x hx)
    · have h1 : e * ⁅f, e⁆ * e⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp heN ⁅f, e⁆).mp (hfc e heE)
      have hsq : (e * f) ^ 2 = (e * ⁅f, e⁆ * e⁻¹) * e ^ 2 * f ^ 2 := by
        rw [commutatorElement_def, pow_two, pow_two]
        group
      rw [hsq]
      exact Z.mul_mem (Z.mul_mem h1 he2) hf2
  inv_mem' := by
    rintro e ⟨heE, heN, hec, he2⟩
    refine ⟨E.inv_mem heE, Subgroup.inv_mem _ heN, fun x hx => ?_, ?_⟩
    · have h1 : ⁅x, e⁆ ∈ Z := by
        simpa [commutatorElement_inv] using Z.inv_mem (hec x hx)
      have h2 : e⁻¹ * ⁅x, e⁆ * e ∈ Z := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heN) ⁅x, e⁆).mp h1
      rwa [commutatorElement_inv_left]
    · have hsq : (e⁻¹) ^ 2 = (e ^ 2)⁻¹ := by
        group
      rw [hsq]
      exact Z.inv_mem he2

private theorem mem_omegaPreimage {E Z : Subgroup G} (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    {e : G} : e ∈ omegaPreimage E Z ↔ e ∈ E ∧ (∀ x ∈ E, ⁅e, x⁆ ∈ Z) ∧ e ^ 2 ∈ Z := by
  constructor
  · rintro ⟨heE, -, hec, he2⟩
    exact ⟨heE, hec, he2⟩
  · rintro ⟨heE, hec, he2⟩
    exact ⟨heE, hEZ heE, hec, he2⟩

private theorem z_le_omegaPreimage {E Z : Subgroup G} (hZE : Z ≤ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) : Z ≤ omegaPreimage E Z := by
  intro z hz
  rw [mem_omegaPreimage hEZ]
  refine ⟨hZE hz, fun x hx => ?_, by rw [pow_two]; exact Z.mul_mem hz hz⟩
  have hxz : x * z * x⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hEZ hx) z).mp hz
  have e : ⁅z, x⁆ = z * (x * z * x⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Z.mul_mem hz (Z.inv_mem hxz)

private theorem omegaPreimage_ne {E Z : Subgroup G} [Finite ↥E]
    (hZE : Z ≤ E) (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hE : IsPGroup 2 E) (hne : Z ≠ E) : omegaPreimage E Z ≠ Z := by
  classical
  let Q := ↥E ⧸ (Z.subgroupOf E)
  haveI hZn : (Z.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZE).mpr hEZ
  have hQp : IsPGroup 2 Q := hE.to_quotient (Z.subgroupOf E)
  have hcardQ : Nat.card Q ≠ 1 := by
    intro hcard
    have hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hcard).1
    have htop : Z.subgroupOf E = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
    exact hne (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hZE).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).mp hQp
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero] at hk
      exact (hcardQ hk).elim
    · exact hk0
  obtain ⟨j, hj0, hj⟩ := IsPGroup.card_center_eq_prime_pow (p := 2) (G := Q) hk hk0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2
    (by rw [hj]; exact dvd_pow_self 2 hj0.ne')
  have htQ : orderOf (t : Q) = 2 := (Subgroup.orderOf_coe t).trans ht
  have ht2 : (t : Q) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (t : Q)
    rwa [htQ] at h
  obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf E) (t : Q)
  have he1 : QuotientGroup.mk' (Z.subgroupOf E) e ≠ 1 := by
    rw [he]
    intro h1
    have ht1 : t = 1 := Subtype.ext h1
    rw [ht1, orderOf_one] at ht
    norm_num at ht
  have he_not : (e : G) ∉ Z := by
    intro hz
    apply he1
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf E) (x := e)).mpr
      (Subgroup.mem_subgroupOf.mpr hz)
  have he_sq : (e : G) ^ 2 ∈ Z := by
    have hsq : (QuotientGroup.mk' (Z.subgroupOf E) e) ^ 2 = 1 := by
      rw [he]
      exact ht2
    have h1 : QuotientGroup.mk' (Z.subgroupOf E) (e ^ 2) = 1 := by
      rw [map_pow]
      exact hsq
    have h2 : e ^ 2 ∈ Z.subgroupOf E :=
      (QuotientGroup.eq_one_iff (N := Z.subgroupOf E) (x := e ^ 2)).mp h1
    simpa using Subgroup.mem_subgroupOf.mp h2
  have he_cent : ∀ x ∈ E, ⁅(e : G), x⁆ ∈ Z := by
    intro x hx
    let x' : ↥E := ⟨x, hx⟩
    have h1 : QuotientGroup.mk' (Z.subgroupOf E) ⁅e, x'⁆ = 1 := by
      rw [map_commutatorElement, he]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp t.2 (QuotientGroup.mk' (Z.subgroupOf E) x')).symm)
    have h2 : ⁅e, x'⁆ ∈ Z.subgroupOf E := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((⁅e, x'⁆ : ↥E) : G) = ⁅(e : G), x⁆ :=
      map_commutatorElement (Subgroup.subtype E) e x'
    have h2' : ((⁅e, x'⁆ : ↥E) : G) ∈ Z := Subgroup.mem_subgroupOf.mp h2
    rwa [h3] at h2'
  intro hMZ
  have hmem : (e : G) ∈ omegaPreimage E Z := ⟨e.2, hEZ e.2, he_cent, he_sq⟩
  exact he_not (hMZ ▸ hmem)

private theorem le_normalizer_omegaPreimage {E Z L : Subgroup G}
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) :
    L ≤ Subgroup.normalizer (omegaPreimage E Z : Set G) := by
  have hconj : ∀ l ∈ L, ∀ m ∈ omegaPreimage E Z, l * m * l⁻¹ ∈ omegaPreimage E Z := by
    intro l hl m hm
    obtain ⟨hmE, hmN, hmc, hm2⟩ := hm
    have hmN' : l * m * l⁻¹ ∈ Subgroup.normalizer (Z : Set G) := by
      have h1 : l * m ∈ Subgroup.normalizer (Z : Set G) :=
        Subgroup.mul_mem _ (hLZ hl) hmN
      simpa [mul_assoc] using
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hLZ hl))
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hLE hl) m).mp hmE, hmN', fun x hx => ?_, ?_⟩
    · have hxl : l⁻¹ * x * l ∈ E := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hLE (L.inv_mem hl)) x).mp hx
      have hc := hmc (l⁻¹ * x * l) hxl
      have e : ⁅l * m * l⁻¹, x⁆ = l * ⁅m, l⁻¹ * x * l⁆ * l⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hLZ hl) ⁅m, l⁻¹ * x * l⁆).mp hc
    · have hsq : (l * m * l⁻¹) ^ 2 = l * m ^ 2 * l⁻¹ := by
        rw [pow_two, pow_two]
        group
      rw [hsq]
      exact (Subgroup.mem_normalizer_iff.mp (hLZ hl) (m ^ 2)).mp hm2
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact hconj l hl m
  · intro hm
    have h := hconj l⁻¹ (L.inv_mem hl) (l * m * l⁻¹) hm
    have heq : l⁻¹ * (l * m * l⁻¹) * (l⁻¹)⁻¹ = m := by group
    rwa [heq] at h

private theorem relCent_inf_eq {E Z T T' L : Subgroup G}
    (hZE : Z ≤ E) (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hT : T ≤ L) (hT' : T' ≤ L) (hcore : ⁅E, pCoreOf 2 L⁆ ≤ Z)
    (hgen : L ≤ (T ⊔ T') ⊔ pCoreOf 2 L) (hcent : relCent E Z L = Z) :
    relCent E Z T ⊓ relCent E Z T' = Z := by
  have hC : Z ≤ relCent E Z T := relCent_le_of_normalizer hZE hEZ (hT.trans hLZ)
  have hC' : Z ≤ relCent E Z T' := relCent_le_of_normalizer hZE hEZ (hT'.trans hLZ)
  have hTsupN : T ⊔ T' ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (hT.trans hLZ) (hT'.trans hLZ)
  have hcommTT' : ⁅T ⊔ T', relCent E Z T ⊓ relCent E Z T'⁆ ≤ Z :=
    commutator_sup_relCent_le hEZ (hT.trans hLZ) (hT'.trans hLZ)
  have hcoreComm : ⁅pCoreOf 2 L, relCent E Z T ⊓ relCent E Z T'⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    have hxE : x ∈ E := (Subgroup.mem_inf.mp hx).1.1
    have h1 : ⁅x, q⁆ ∈ Z := (Subgroup.commutator_le.mp hcore) x hxE q hq
    simpa [commutatorElement_inv] using Z.inv_mem h1
  have hQN : pCoreOf 2 L ≤ Subgroup.normalizer (Z : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLZ
  have hcommL : ⁅L, relCent E Z T ⊓ relCent E Z T'⁆ ≤ Z :=
    (Subgroup.commutator_mono hgen le_rfl).trans
      (CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
        (T ⊔ T') (pCoreOf 2 L) (relCent E Z T ⊓ relCent E Z T') Z
        hcommTT' hcoreComm hTsupN hQN)
  apply le_antisymm
  · intro x hx
    rw [← hcent, mem_relCent hEZ]
    refine ⟨(Subgroup.mem_inf.mp hx).1.1, fun l hl => ?_⟩
    have h1 : ⁅l, x⁆ ∈ Z := (Subgroup.commutator_le.mp hcommL) l hl x hx
    simpa [commutatorElement_inv] using Z.inv_mem h1
  · exact le_inf hC hC'

private theorem relIndex_pos {H K : Subgroup G} [Finite K] : 0 < H.relIndex K := by
  have hdvd := Subgroup.relIndex_dvd_card (H := H) (K := K)
  have hpos : 0 < Nat.card K := Nat.card_pos_iff.mpr ⟨⟨1, K.one_mem⟩, inferInstance⟩
  exact Nat.pos_of_dvd_of_pos hdvd hpos

private theorem isElemSec_omegaPreimage_subgroupOf {E Z H : Subgroup G}
    (hZE : Z ≤ E) (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) (hEH : E ≤ H) :
    IsElemSec (Z.subgroupOf H) ((omegaPreimage E Z).subgroupOf H) := by
  have hMH : omegaPreimage E Z ≤ H := fun _ hx => hEH hx.1
  refine ⟨Subgroup.subgroupOf_mono H (z_le_omegaPreimage hZE hEZ), ?_, ?_⟩
  · rw [CFSG.GroupTheory.commutator_subgroupOf_eq hMH hMH]
    exact Subgroup.subgroupOf_mono H (by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (mem_omegaPreimage hEZ).mp ha |>.2.1 b ((mem_omegaPreimage hEZ).mp hb).1)
  · intro e he
    have heM : (e : G) ∈ omegaPreimage E Z := Subgroup.mem_subgroupOf.mp he
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa using (mem_omegaPreimage hEZ).mp heM |>.2.2

private theorem two_pow_le_relIndex_omegaPreimage {L E Z : Subgroup G} [Finite ↥L] [Finite ↥E]
    {n : ℕ} (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L))
    (hZE : Z ≤ E) (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hLM : L ≤ Subgroup.normalizer (omegaPreimage E Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ omegaPreimage E Z, ⁅p, v⁆ ∈ Z)
    (hnt : ∃ l ∈ L, ∃ v ∈ omegaPreimage E Z, ⁅l, v⁆ ∉ Z) :
    2 ^ (2 * n) ≤ Z.relIndex (omegaPreimage E Z) := by
  classical
  let H := E ⊔ L
  have hEH : E ≤ H := le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hMH : omegaPreimage E Z ≤ H := fun _ hx => hEH hx.1
  have hZH : Z ≤ H := hZE.trans hEH
  haveI hHfin : Finite ↥H :=
    finite_sup_of_le_normalizer (X := E) (P := E) (A := L) le_rfl hLE
  let L' := L.subgroupOf H
  let V' := (omegaPreimage E Z).subgroupOf H
  let Z' := Z.subgroupOf H
  have hsec' : IsElemSec Z' V' := isElemSec_omegaPreimage_subgroupOf hZE hEZ hEH
  have hq' : IsL2Quot n (oTwoQuot ↥L') := by
    obtain ⟨eL⟩ := hq
    exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv
      (Subgroup.subgroupOfEquivOfLe hLH)).trans eL⟩
  have hnorm' : L' ≤ Subgroup.normalizer (V' : Set ↥H) ⊓
      Subgroup.normalizer (Z' : Set ↥H) := by
    refine le_inf ?_ ?_
    · have h := Subgroup.subgroupOf_mono H hLM
      rwa [Subgroup.subgroupOf_normalizer_eq hMH] at h
    · have h := Subgroup.subgroupOf_mono H hLZ
      rwa [Subgroup.subgroupOf_normalizer_eq hZH] at h
  have hpC : pCoreOf 2 L' = (pCoreOf 2 L).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [CFSG.Quasithin.R3c5.map_pCoreOf_subgroupOf hLH 2]
    exact (Subgroup.map_subgroupOf_eq_of_le
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)).symm
  have hQ' : ∀ p ∈ pCoreOf 2 L', ∀ v ∈ V', ⁅p, v⁆ ∈ Z' := by
    intro p hp v hv
    have hpL : (p : G) ∈ pCoreOf 2 L := by
      have h := hp
      rw [hpC] at h
      exact Subgroup.mem_subgroupOf.mp h
    have hvM : (v : G) ∈ omegaPreimage E Z := Subgroup.mem_subgroupOf.mp hv
    have h1 : ⁅(p : G), (v : G)⁆ ∈ Z := hQ (p : G) hpL (v : G) hvM
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h3 : ((⁅p, v⁆ : ↥H) : G) = ⁅(p : G), (v : G)⁆ :=
      map_commutatorElement (Subgroup.subtype H) p v
    rwa [h3]
  have hnt' : ∃ l ∈ L', ∃ v ∈ V', ⁅l, v⁆ ∉ Z' := by
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    let l' : ↥H := ⟨l, hLH hl⟩
    let v' : ↥H := ⟨v, hMH hv⟩
    refine ⟨l', Subgroup.mem_subgroupOf.mpr hl, v', Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    intro hmem
    apply hne
    have h2 : ((⁅l', v'⁆ : ↥H) : G) ∈ Z := Subgroup.mem_subgroupOf.mp hmem
    have h3 : ((⁅l', v'⁆ : ↥H) : G) = ⁅l, v⁆ :=
      map_commutatorElement (Subgroup.subtype H) l' v'
    rwa [h3] at h2
  have hbig := two_pow_le_relIndex_of_nontrivial (G := ↥H) hn hq' hsec' hnorm' hQ' hnt'
  have hrel : Z'.relIndex V' = Z.relIndex (omegaPreimage E Z) :=
    Subgroup.relIndex_subgroupOf (H := Z) (K := omegaPreimage E Z) (L := H) hMH
  rwa [hrel] at hbig

private theorem two_pow_mul_two_pow (n : ℕ) : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by
  rw [← pow_add]
  congr 1
  omega

theorem relIndex_eq_two_pow_of_lines {L E Z T T' : Subgroup G} [Finite ↥L] [Finite ↥E]
    {n : ℕ} (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hZE : Z ≤ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (hE : IsPGroup 2 E)
    (hcore : ⁅E, pCoreOf 2 L⁆ ≤ Z) (hT : T ≤ L) (hT' : T' ≤ L)
    (hgen : L ≤ (T ⊔ T') ⊔ pCoreOf 2 L) (hcent : relCent E Z L = Z) (hne : Z ≠ E)
    (hTq : (relCent E Z T).relIndex E ≤ 2 ^ n)
    (hTq' : (relCent E Z T').relIndex E ≤ 2 ^ n) :
    Z.relIndex E = 2 ^ (2 * n) ∧ Z.relIndex (relCent E Z T) = 2 ^ n := by
  classical
  have hMle : omegaPreimage E Z ≤ E := fun _ h => (mem_omegaPreimage hEZ).mp h |>.1
  have hZleM : Z ≤ omegaPreimage E Z := z_le_omegaPreimage hZE hEZ
  have hMne : omegaPreimage E Z ≠ Z := omegaPreimage_ne hZE hEZ hE hne
  have hLM : L ≤ Subgroup.normalizer (omegaPreimage E Z : Set G) :=
    le_normalizer_omegaPreimage hLE hLZ
  have hQM : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ omegaPreimage E Z, ⁅p, v⁆ ∈ Z := by
    intro p hp v hv
    have hvE : v ∈ E := (mem_omegaPreimage hEZ).mp hv |>.1
    have h1 : ⁅v, p⁆ ∈ Z := (Subgroup.commutator_le.mp hcore) v hvE p hp
    simpa [commutatorElement_inv] using Z.inv_mem h1
  have hntM : ∃ l ∈ L, ∃ v ∈ omegaPreimage E Z, ⁅l, v⁆ ∉ Z := by
    by_contra h
    push Not at h
    apply hMne
    apply le_antisymm ?_ hZleM
    intro v hv
    rw [← hcent, mem_relCent hEZ]
    refine ⟨hMle hv, fun l hl => ?_⟩
    have h1 : ⁅l, v⁆ ∈ Z := h l hl v hv
    simpa [commutatorElement_inv] using Z.inv_mem h1
  have hbig : 2 ^ (2 * n) ≤ Z.relIndex (omegaPreimage E Z) :=
    two_pow_le_relIndex_omegaPreimage hn hq hZE hEZ hLE hLZ hLM hQM hntM
  have hCinf : relCent E Z T ⊓ relCent E Z T' = Z :=
    relCent_inf_eq hZE hEZ hLZ hT hT' hcore hgen hcent
  have hupper : Z.relIndex E ≤ 2 ^ (2 * n) := by
    calc Z.relIndex E ≤ (relCent E Z T).relIndex E * (relCent E Z T').relIndex E := by
          simpa [hCinf] using Subgroup.relIndex_inf_le
            (H := relCent E Z T) (K := relCent E Z T') (L := E)
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hTq hTq'
      _ = 2 ^ (2 * n) := two_pow_mul_two_pow n
  have hZMle : Z.relIndex (omegaPreimage E Z) ≤ Z.relIndex E :=
    Subgroup.relIndex_le_of_le_right hMle (ne_of_gt (relIndex_pos (H := Z) (K := E)))
  have hZEq : Z.relIndex E = 2 ^ (2 * n) :=
    le_antisymm hupper (hbig.trans hZMle)
  have hC : Z ≤ relCent E Z T := relCent_le_of_normalizer hZE hEZ (hT.trans hLZ)
  have hC' : Z ≤ relCent E Z T' := relCent_le_of_normalizer hZE hEZ (hT'.trans hLZ)
  have hCle : relCent E Z T ≤ E := fun _ h => h.1
  have hC'le : relCent E Z T' ≤ E := fun _ h => h.1
  have hprod : (relCent E Z T).relIndex E * (relCent E Z T').relIndex E = 2 ^ (2 * n) := by
    apply le_antisymm
    · calc (relCent E Z T).relIndex E * (relCent E Z T').relIndex E ≤ 2 ^ n * 2 ^ n :=
            Nat.mul_le_mul hTq hTq'
        _ = 2 ^ (2 * n) := two_pow_mul_two_pow n
    · have h := Subgroup.relIndex_inf_le
        (H := relCent E Z T) (K := relCent E Z T') (L := E)
      rwa [hCinf, hZEq] at h
  have hbpos : 0 < (relCent E Z T').relIndex E := relIndex_pos
  have ha : (relCent E Z T).relIndex E = 2 ^ n := by
    apply le_antisymm hTq
    by_contra hlt
    push Not at hlt
    have h1 : (relCent E Z T).relIndex E * (relCent E Z T').relIndex E
        < 2 ^ n * (relCent E Z T').relIndex E :=
      Nat.mul_lt_mul_of_pos_right hlt hbpos
    have h2 : 2 ^ n * (relCent E Z T').relIndex E ≤ 2 ^ n * 2 ^ n :=
      Nat.mul_le_mul_left _ hTq'
    have h3 : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := two_pow_mul_two_pow n
    omega
  have hc : Z.relIndex (relCent E Z T) = 2 ^ n := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := Z) (K := relCent E Z T)
      (L := E) hC hCle
    rw [hZEq, ha] at hmul
    rw [← two_pow_mul_two_pow n] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul
  exact ⟨hZEq, hc⟩

end CFSG.Quasithin.St84
