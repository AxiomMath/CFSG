module

public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

private lemma w16l_orderOf_eq_two {L : Type*} [Group L] {t : L} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    orderOf t = 2 := by
  refine orderOf_eq_prime ?_ ht1
  simpa [pow_two] using ht2

private lemma w16l_card_zpowers_of_order_two {L : Type*} [Group L] {t : L}
    (ht : orderOf t = 2) : Nat.card (Subgroup.zpowers t) = 2 := by
  rw [Nat.card_zpowers, ht]

private lemma w16l_odd_card_fusionOddCore_aux (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (fusionOddCore H)) := by
  have h : fusionOddCore H = CFSG.pPrimeCore 2 H := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext N
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))

private lemma w16l_zpowers_eq_one_or {L : Type*} [Group L] {u : L} (hu : u * u = 1) {x : L}
    (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  let K : Subgroup L :=
    { carrier := {y : L | y = 1 ∨ y = u}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl hu
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (inv_eq_of_mul_eq_one_right hu) }
  exact (Subgroup.zpowers_le (g := u) (H := K)).mpr (Or.inr rfl) hx

private lemma w16l_eq_top_of_ker_le_of_map_eq_top {G H : Type*} [Group G] [Group H]
    (f : G →* H) {S : Subgroup G} (hker : f.ker ≤ S) (hmap : S.map f = ⊤) : S = ⊤ := by
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    exact top_le_iff.mp (hmap ▸ Subgroup.map_le_range (f := f) S)
  have htop : (⊤ : Subgroup G).map f = ⊤ := Subgroup.map_top_of_surjective f hsurj
  exact Subgroup.map_injective_of_ker_le (f := f) hker le_top (by rw [hmap, htop])

theorem w16l_one_structure {L X : Type} [Group L] [Finite L] [Group X] [Finite X] {t : L}
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hnc : Subgroup.normalClosure ({t} : Set L) = ⊤)
    (hO2 : ∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N ⊓ Subgroup.zpowers t = ⊥)
    (hne : Subgroup.zpowers t ≠ ⊤)
    (ψ : L →* X) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hX : Subgroup.zpowers (ψ t) ⊔ fusionOddCore X = ⊤) :
    Subgroup.zpowers t ⊔ fusionOddCore L = ⊤ ∧
      (∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      fusionOddCore L ≠ ⊥ ∧ fusionOddCore L ≤ ⁅fusionOddCore L, Subgroup.zpowers t⁆ := by
  classical
  let T : Subgroup L := Subgroup.zpowers t
  let OX : Subgroup X := fusionOddCore X
  let E0 : Subgroup L := OX.comap ψ
  have ht : orderOf t = 2 := w16l_orderOf_eq_two ht2 ht1
  have hTcard : Nat.card T = 2 := w16l_card_zpowers_of_order_two ht
  have hOodd : Odd (Nat.card (fusionOddCore L)) := w16l_odd_card_fusionOddCore_aux L
  have hOXodd : Odd (Nat.card OX) := w16l_odd_card_fusionOddCore_aux X
  have hE0normal : E0.Normal := inferInstance
  have hmapE0 : E0.map ψ = OX := by
    simpa [E0, OX] using Subgroup.map_comap_eq_self_of_surjective hψ OX
  have hmapTop : (T ⊔ E0).map ψ = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hmapE0, hX]
  have hker_le_E0 : ψ.ker ≤ E0 := by
    intro x hx
    have hx1 : ψ x = 1 := hx
    simp [E0, OX, hx1]
  have hTE0 : T ⊔ E0 = ⊤ :=
    w16l_eq_top_of_ker_le_of_map_eq_top ψ (hker_le_E0.trans le_sup_right) hmapTop
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥E0))
  have hPleK0 : ∀ x : ↥E0, x ∈ P → (x : L) ∈ ψ.ker := by
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
    have hxLpow : (x : L) ^ (2 ^ n) = 1 := by
      have := congrArg (fun y : ↥P => ((y : ↥E0) : L)) hn
      simpa using this
    have hdvd2 : orderOf (x : L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxLpow
    have hmemOX : ψ (x : L) ∈ OX := x.2
    have hdvdOX : orderOf (ψ (x : L)) ∣ Nat.card OX := by
      rw [← Subgroup.orderOf_mk (ψ (x : L)) hmemOX]
      exact orderOf_dvd_natCard _
    have hdvd2' : orderOf (ψ (x : L)) ∣ 2 ^ n := (orderOf_map_dvd ψ (x : L)).trans hdvd2
    have hcop : Nat.Coprime (2 ^ n) (Nat.card OX) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hOXodd)
    have hone : orderOf (ψ (x : L)) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2' hdvdOX
    exact orderOf_eq_one_iff.mp hone
  have hPleCenter : P ≤ Subgroup.center ↥E0 := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxK : (x : L) ∈ ψ.ker := hPleK0 x hx
    have hxZ : (x : L) ∈ Subgroup.center L := hker hxK
    exact (Subgroup.mem_center_iff.mp hxZ) (y : L)
  haveI hPnormal : P.Normal := Subgroup.normal_of_le_center hPleCenter
  have hPindexOdd : Odd (P : Subgroup ↥E0).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact P.not_dvd_index
  have hPcop : Nat.Coprime (Nat.card (P : Subgroup ↥E0)) (P : Subgroup ↥E0).index :=
    Sylow.card_coprime_index P
  obtain ⟨Esub, hcompl⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := (P : Subgroup ↥E0)) hPcop
  let K2 : Subgroup L := P.map E0.subtype
  let E : Subgroup L := Esub.map E0.subtype
  have hK2leE0 : K2 ≤ E0 := by
    intro x hx
    rcases hx with ⟨y, -, rfl⟩
    exact y.2
  have hEleE0 : E ≤ E0 := by
    intro x hx
    rcases hx with ⟨y, -, rfl⟩
    exact y.2
  have htopmapE0 : (⊤ : Subgroup ↥E0).map E0.subtype = E0 := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hE0sup : K2 ⊔ E = E0 := by
    have h := congrArg (Subgroup.map E0.subtype) hcompl.sup_eq_top
    rw [Subgroup.map_sup, htopmapE0] at h
    exact h
  have hEsubodd : Odd (Nat.card Esub) := by
    rw [← hcompl.symm.index_eq_card]
    exact hPindexOdd
  have hEodd : Odd (Nat.card E) := by
    rw [Subgroup.card_map_of_injective E0.subtype_injective]
    exact hEsubodd
  have hPdisjEsub : Disjoint (P : Subgroup ↥E0) Esub := hcompl.disjoint
  have hEvenOdd : ∀ x : ↥E0, (x : L) ∈ E ↔ Odd (orderOf (x : L)) := by
    intro x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hxy : y = x := E0.subtype_injective hyx
      subst hxy
      have hdvd : orderOf (y : ↥E0) ∣ Nat.card Esub := by
        rw [← Subgroup.orderOf_mk y hy]
        exact orderOf_dvd_natCard _
      have hodd : Odd (orderOf (y : ↥E0)) := Odd.of_dvd_nat hEsubodd hdvd
      simpa using hodd
    · intro hodd
      obtain ⟨pq, hpq, -⟩ := hcompl.existsUnique x
      obtain ⟨⟨p, hpP⟩, ⟨q, hqE⟩⟩ := pq
      have hpqL : (p : L) * (q : L) = (x : L) := by
        have := congrArg (fun y : ↥E0 => (y : L)) hpq
        simpa using this
      have hmemP : (p : L) ∈ K2 := ⟨(p : ↥E0), hpP, rfl⟩
      have hpK : (p : L) ∈ ψ.ker := hPleK0 (p : ↥E0) hpP
      have hpZ : (p : L) ∈ Subgroup.center L := hker hpK
      have hcomm : ∀ z : L, (p : L) * z = z * (p : L) := fun z =>
        (Subgroup.mem_center_iff.mp hpZ z).symm
      let m : ℕ := orderOf (x : L)
      have hmOdd : Odd m := hodd
      have hxm : (x : L) ^ m = 1 := pow_orderOf_eq_one _
      have hpqm : ((p : L) * (q : L)) ^ m = 1 := by
        rw [hpqL]; exact hxm
      have hcommute : Commute (p : L) (q : L) := hcomm (q : L)
      have hprod1 : (p : L) ^ m * (q : L) ^ m = 1 := by
        rw [← hcommute.mul_pow m]
        exact hpqm
      have hqmem : (q : L) ∈ E := ⟨(q : ↥E0), hqE, rfl⟩
      have hqpowE : ((q : L) ^ m) ∈ E := E.pow_mem hqmem m
      have hpPpow : ((p : L) ^ m) ∈ K2 := K2.pow_mem hmemP m
      have hp_eq_inv : (p : L) ^ m = ((q : L) ^ m)⁻¹ :=
        mul_eq_one_iff_eq_inv.mp hprod1
      have hmem_inf : (p : L) ^ m ∈ K2 ⊓ E := ⟨hpPpow, hp_eq_inv ▸ E.inv_mem hqpowE⟩
      have hK2disjE : K2 ⊓ E = ⊥ := by
        ext z
        constructor
        · intro hz
          rw [Subgroup.mem_inf] at hz
          rcases hz.1 with ⟨p', hp', hpz⟩
          rcases hz.2 with ⟨q', hq', hqz⟩
          have hpq' : p' = q' := E0.subtype_injective (hpz.trans hqz.symm)
          have hmem : p' ∈ (P : Subgroup ↥E0) ⊓ Esub := by
            rw [Subgroup.mem_inf]
            exact ⟨hp', hpq' ▸ hq'⟩
          rw [hPdisjEsub.eq_bot] at hmem
          have hp_one : p' = 1 := by simpa using hmem
          have hz1 : z = 1 := by rw [← hpz, hp_one]; rfl
          simp [hz1]
        · intro hz
          rw [Subgroup.mem_bot] at hz
          simp [hz]
      rw [hK2disjE] at hmem_inf
      have hp_pow_one : (p : L) ^ m = 1 := by simpa using hmem_inf
      have hp_one : (p : L) = 1 := by
        obtain ⟨n, hn⟩ := P.isPGroup' ⟨p, hpP⟩
        have hp_2 : (p : L) ^ (2 ^ n) = 1 := by
          have := congrArg (fun y : ↥P => ((y : ↥E0) : L)) hn
          simpa using this
        have hdvd1 : orderOf (p : L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hp_2
        have hdvd2 : orderOf (p : L) ∣ m := orderOf_dvd_of_pow_eq_one hp_pow_one
        have hcop : Nat.Coprime (2 ^ n) m :=
          Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hmOdd)
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
      have hxE : (x : L) = (q : L) := by
        rw [← hpqL, hp_one, one_mul]
      rwa [hxE]
  have hconj_mem : ∀ g : L, g⁻¹ * t * g ∈ T ⊔ E := by
    intro g
    have hg : g ∈ ((T : Set L) * (E0 : Set L)) := by
      have h := Subgroup.mul_normal T E0
      rw [← h, hTE0]
      exact trivial
    obtain ⟨t', ht', e, he, hge⟩ := hg
    have ht'case : t' = 1 ∨ t' = t := w16l_zpowers_eq_one_or ht2 ht'
    obtain ⟨pq, hpq, -⟩ := hcompl.existsUnique ⟨e, he⟩
    obtain ⟨⟨p, hpP⟩, ⟨q, hqE⟩⟩ := pq
    have hpqL : (p : L) * (q : L) = e := by
      have := congrArg (fun y : ↥E0 => (y : L)) hpq
      simpa using this
    have hpZ : (p : L) ∈ Subgroup.center L := hker (hPleK0 (p : ↥E0) hpP)
    have hp_comm : (p : L) * t = t * (p : L) :=
      (Subgroup.mem_center_iff.mp hpZ t).symm
    have hp_inv_comm : (p : L)⁻¹ * t * (p : L) = t := by
      have h := congrArg (fun z => (p : L)⁻¹ * z) hp_comm
      simpa [mul_assoc] using h.symm
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hcalc : g⁻¹ * t * g = (q : L)⁻¹ * t * (q : L) := by
      rw [← hge]
      rcases ht'case with h1 | h1
      · subst t'
        simp only [one_mul]
        rw [← hpqL]
        calc ((p : L) * (q : L))⁻¹ * t * ((p : L) * (q : L))
            = (q : L)⁻¹ * ((p : L)⁻¹ * t * (p : L)) * (q : L) := by
                rw [mul_inv_rev]; group
          _ = (q : L)⁻¹ * t * (q : L) := by rw [hp_inv_comm]
      · subst t'
        calc (t * e)⁻¹ * t * (t * e) = e⁻¹ * t * e := by
              rw [mul_inv_rev, htinv]
              calc e⁻¹ * t * t * (t * e) = e⁻¹ * (t * t) * (t * e) := by group
                _ = e⁻¹ * t * e := by rw [ht2]; group
          _ = ((p : L) * (q : L))⁻¹ * t * ((p : L) * (q : L)) := by rw [← hpqL]
          _ = (q : L)⁻¹ * t * (q : L) := by
              rw [mul_inv_rev]
              calc (q : L)⁻¹ * (p : L)⁻¹ * t * ((p : L) * (q : L))
                  = (q : L)⁻¹ * ((p : L)⁻¹ * t * (p : L)) * (q : L) := by
                      group
                _ = (q : L)⁻¹ * t * (q : L) := by rw [hp_inv_comm]
    rw [hcalc]
    have hqjoin : (q : L) ∈ T ⊔ E :=
      Subgroup.mem_sup_right ⟨(q : ↥E0), hqE, rfl⟩
    have htjoin : t ∈ T ⊔ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    exact (T ⊔ E).mul_mem ((T ⊔ E).mul_mem ((T ⊔ E).inv_mem hqjoin) htjoin) hqjoin
  have hconj_sub : Group.conjugatesOfSet ({t} : Set L) ⊆ (T ⊔ E : Subgroup L) := by
    rintro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    rw [isConj_iff] at hconj
    obtain ⟨c, rfl⟩ := hconj
    simpa using hconj_mem c⁻¹
  have hTE : T ⊔ E = ⊤ := by
    have hnc_le : Subgroup.normalClosure ({t} : Set L) ≤ T ⊔ E := by
      rw [Subgroup.normalClosure]
      exact (Subgroup.closure_le (K := T ⊔ E)).mpr hconj_sub
    rw [hnc] at hnc_le
    exact top_le_iff.mp hnc_le
  have hEO : E ≤ fusionOddCore L := by
    have hEnormal : E.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hnE0 : n ∈ E0 := hEleE0 hn
      have hconjE0 : g * n * g⁻¹ ∈ E0 := hE0normal.conj_mem n hnE0 g
      have hoddn : Odd (orderOf n) := (hEvenOdd ⟨n, hnE0⟩).mp hn
      have hsem : SemiconjBy g n (g * n * g⁻¹) := by
        unfold SemiconjBy
        group
      have hord : orderOf n = orderOf (g * n * g⁻¹) := SemiconjBy.orderOf_eq g hsem
      exact (hEvenOdd ⟨g * n * g⁻¹, hconjE0⟩).mpr (hord ▸ hoddn)
    exact le_sSup ⟨hEnormal, hEodd⟩
  have hTEsup : T ⊔ E = ⊤ := hTE
  have hTO : T ⊔ fusionOddCore L = ⊤ := by
    have hle : T ⊔ E ≤ T ⊔ fusionOddCore L := sup_le_sup_left hEO T
    rw [hTEsup] at hle
    exact top_le_iff.mp hle
  have hdisjTO : Disjoint T (fusionOddCore L) := by
    rw [disjoint_iff]
    apply Subgroup.eq_bot_of_card_eq
    have hdvd2 : Nat.card ↥(T ⊓ fusionOddCore L) ∣ 2 := by
      rw [← hTcard]
      exact Subgroup.card_dvd_of_le (inf_le_left : T ⊓ fusionOddCore L ≤ T)
    have hdvdO : Nat.card ↥(T ⊓ fusionOddCore L) ∣ Nat.card (fusionOddCore L) :=
      Subgroup.card_dvd_of_le (inf_le_right : T ⊓ fusionOddCore L ≤ fusionOddCore L)
    have hodd : Odd (Nat.card ↥(T ⊓ fusionOddCore L)) := Odd.of_dvd_nat hOodd hdvdO
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact h1
    · exfalso
      rw [h2] at hodd
      exact (by norm_num : ¬ Odd 2) hodd
  have hTOcomp : Subgroup.IsComplement' T (fusionOddCore L) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjTO ?_
    change (↑T : Set L) * ((fusionOddCore L : Subgroup L) : Set L) = Set.univ
    rw [← Subgroup.mul_normal T (fusionOddCore L)]
    simpa using congrArg (fun H : Subgroup L => (H : Set L)) hTO
  have hOindex : (fusionOddCore L).index = 2 := by
    rw [hTOcomp.index_eq_card, hTcard]
  have hcardL : Nat.card L = 2 * Nat.card (fusionOddCore L) := by
    rw [← hTOcomp.card_mul_card, hTcard]
  refine ⟨hTO, ?_, ?_, ?_⟩
  ·
    intro N hNnormal hNp
    let NO : Subgroup L := N ⊔ fusionOddCore L
    have hO_le_NO : fusionOddCore L ≤ NO := le_sup_right
    have hidx_dvd : NO.index ∣ (fusionOddCore L).index :=
      Subgroup.index_dvd_of_le hO_le_NO
    rw [hOindex] at hidx_dvd
    have hNOindex : NO.index = 1 ∨ NO.index = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hidx_dvd
    rcases hNOindex with h1 | h2
    ·
      have hNOtop : NO = ⊤ := Subgroup.index_eq_one.mp h1
      have hdisjNO : Disjoint N (fusionOddCore L) := by
        rw [disjoint_iff]
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := N)).mp hNp
        have hdvdN : Nat.card ↥(N ⊓ fusionOddCore L) ∣ 2 ^ k := by
          have h := Subgroup.card_dvd_of_le
            (inf_le_left : N ⊓ fusionOddCore L ≤ N)
          rwa [hk] at h
        have hdvdO : Nat.card ↥(N ⊓ fusionOddCore L) ∣ Nat.card (fusionOddCore L) :=
          Subgroup.card_dvd_of_le (inf_le_right : N ⊓ fusionOddCore L ≤ fusionOddCore L)
        have hcop : Nat.Coprime (2 ^ k) (Nat.card (fusionOddCore L)) :=
          Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd)
        exact Subgroup.eq_bot_of_card_eq (H := N ⊓ fusionOddCore L)
          (Nat.eq_one_of_dvd_coprimes hcop hdvdN hdvdO)
      have hNOcomp : Subgroup.IsComplement' N (fusionOddCore L) := by
        haveI : N.Normal := hNnormal
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjNO ?_
        change (↑N : Set L) * ((fusionOddCore L : Subgroup L) : Set L) = Set.univ
        rw [← Subgroup.normal_mul N (fusionOddCore L)]
        simpa using congrArg (fun H : Subgroup L => (H : Set L)) hNOtop
      have hcardN : Nat.card N = 2 := by
        have h := hNOcomp.card_mul_card
        rw [hcardL] at h
        exact Nat.mul_right_cancel Nat.card_pos h
      have htN : t ∈ N := by
        let q : L ⧸ N := QuotientGroup.mk' N t
        have hq2 : q * q = 1 := by
          change QuotientGroup.mk' N (t * t) = (1 : L ⧸ N)
          rw [ht2, map_one]
        have hdvd2 : orderOf q ∣ 2 := by
          apply orderOf_dvd_of_pow_eq_one
          simpa [pow_two] using hq2
        have hdvdq : orderOf q ∣ Nat.card (L ⧸ N) := orderOf_dvd_natCard _
        have hNindex : N.index = Nat.card (fusionOddCore L) := hNOcomp.symm.index_eq_card
        have hoddIndex : Odd N.index := by
          rw [hNindex]
          exact hOodd
        have hcardquot : Nat.card (L ⧸ N) = N.index := (Subgroup.index_eq_card (H := N)).symm
        have hcop : Nat.Coprime 2 (Nat.card (L ⧸ N)) := by
          rw [hcardquot]
          exact Nat.coprime_two_left.mpr hoddIndex
        have hq1 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdq
        exact (QuotientGroup.eq_one_iff (N := N) t).mp (orderOf_eq_one_iff.mp hq1)
      have hTleN : T ≤ N := by
        change Subgroup.zpowers t ≤ N
        exact Subgroup.zpowers_le.mpr htN
      have hTN : T = N :=
        Subgroup.eq_of_le_of_card_ge hTleN (by rw [hTcard, hcardN])
      have hTnormal : T.Normal := hTN ▸ hNnormal
      have hsub : ({t} : Set L) ⊆ T := by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact Subgroup.mem_zpowers t
      have hncT : Subgroup.normalClosure ({t} : Set L) = T := by
        apply le_antisymm
        · exact Subgroup.normalClosure_le_normal hsub
        · change Subgroup.zpowers t ≤ Subgroup.normalClosure ({t} : Set L)
          exact Subgroup.zpowers_le.mpr (Subgroup.subset_normalClosure (Set.mem_singleton t))
      rw [hncT] at hnc
      exfalso; exact hne hnc
    ·
      have hNOeq : NO = fusionOddCore L := by
        have hc1 : Nat.card NO * NO.index = Nat.card L := Subgroup.card_mul_index NO
        have hc2 : Nat.card (fusionOddCore L) * (fusionOddCore L).index = Nat.card L :=
          Subgroup.card_mul_index (fusionOddCore L)
        rw [h2] at hc1
        rw [hOindex] at hc2
        have hmul : Nat.card NO * 2 = Nat.card (fusionOddCore L) * 2 := by
          rw [hc1, hc2]
        have hcard : Nat.card NO = Nat.card (fusionOddCore L) :=
          Nat.mul_right_cancel (by norm_num : (0 : ℕ) < 2) hmul
        exact (Subgroup.eq_of_le_of_card_ge hO_le_NO (le_of_eq hcard)).symm
      have hNleO : N ≤ fusionOddCore L := hNOeq ▸ le_sup_left
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := N)).mp hNp
      have hdvdN : Nat.card N ∣ 2 ^ k := by rw [hk]
      have hdvdO : Nat.card N ∣ Nat.card (fusionOddCore L) :=
        Subgroup.card_dvd_of_le hNleO
      have hcop : Nat.Coprime (2 ^ k) (Nat.card (fusionOddCore L)) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd)
      exact Subgroup.eq_bot_of_card_eq (H := N) (Nat.eq_one_of_dvd_coprimes hcop hdvdN hdvdO)
  ·
    intro hO
    have hTtop : T = ⊤ := by
      rw [← hTO, hO, sup_bot_eq]
    exact hne hTtop
  ·
    let C : Subgroup L := ⁅fusionOddCore L, T⁆
    have hCleO : C ≤ fusionOddCore L :=
      Subgroup.commutator_le_left (H₁ := fusionOddCore L) (H₂ := T)
    have hCnormal : C.Normal := by
      have hle : fusionOddCore L ⊔ T ≤ Subgroup.normalizer (C : Set L) :=
        sup_le (Subgroup.normalizer_commutator_ge_left (H₁ := fusionOddCore L) (H₂ := T))
          (Subgroup.normalizer_commutator_ge_right (H₁ := fusionOddCore L) (H₂ := T))
      rw [sup_comm, hTO] at hle
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
    have hTdisjC : Disjoint T C := by
      rw [disjoint_iff]
      have h : T ⊓ C ≤ T ⊓ fusionOddCore L := inf_le_inf_left T hCleO
      rw [hdisjTO.eq_bot] at h
      exact le_bot_iff.mp h
    have hconjC : ∀ g : L, g⁻¹ * t * g ∈ T ⊔ C := by
      intro g
      have hg : g ∈ ((T : Set L) * (fusionOddCore L : Set L)) := by
        have h := Subgroup.mul_normal T (fusionOddCore L)
        rw [← h, hTO]
        exact trivial
      obtain ⟨t', ht', o, ho, hge⟩ := hg
      have ht'case : t' = 1 ∨ t' = t := w16l_zpowers_eq_one_or ht2 ht'
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have hformula : g⁻¹ * t * g = o⁻¹ * t * o := by
        rw [← hge]
        rcases ht'case with h1 | h1
        · subst t'
          simp only [one_mul]
        · subst t'
          rw [mul_inv_rev, htinv]
          calc o⁻¹ * t * t * (t * o) = o⁻¹ * (t * t) * (t * o) := by group
            _ = o⁻¹ * t * o := by rw [ht2]; group
      rw [hformula]
      have hcomm : o⁻¹ * t * o = ⁅o⁻¹, t⁆ * t := by
        simpa [MulAut.conj_apply] using
          (conj_eq_commutatorElement_mul (g₁ := o⁻¹) (g₂ := t))
      rw [hcomm]
      have hmemC : ⁅o⁻¹, t⁆ ∈ C :=
        Subgroup.commutator_mem_commutator ((fusionOddCore L).inv_mem ho)
          (Subgroup.mem_zpowers t)
      exact (T ⊔ C).mul_mem (Subgroup.mem_sup_right hmemC)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
    have hTCtop : T ⊔ C = ⊤ := by
      have hconj_subC : Group.conjugatesOfSet ({t} : Set L) ⊆ (T ⊔ C : Subgroup L) := by
        rintro x hx
        rw [Group.mem_conjugatesOfSet_iff] at hx
        obtain ⟨a, ha, hconj⟩ := hx
        simp only [Set.mem_singleton_iff] at ha
        subst ha
        rw [isConj_iff] at hconj
        obtain ⟨c, rfl⟩ := hconj
        simpa using hconjC c⁻¹
      have hnc_le : Subgroup.normalClosure ({t} : Set L) ≤ T ⊔ C := by
        rw [Subgroup.normalClosure]
        exact (Subgroup.closure_le (K := T ⊔ C)).mpr hconj_subC
      rw [hnc] at hnc_le
      exact top_le_iff.mp hnc_le
    have hCcomp : Subgroup.IsComplement' T C := by
      haveI : C.Normal := hCnormal
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTdisjC ?_
      change (↑T : Set L) * (C : Set L) = Set.univ
      rw [← Subgroup.mul_normal T C]
      simpa using congrArg (fun H : Subgroup L => (H : Set L)) hTCtop
    have hcardC : Nat.card C = Nat.card (fusionOddCore L) := by
      have h := hCcomp.card_mul_card
      rw [hTcard, hcardL] at h
      exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
    have hCeqO : C = fusionOddCore L :=
      Subgroup.eq_of_le_of_card_ge hCleO (le_of_eq hcardC.symm)
    change fusionOddCore L ≤ C
    rw [hCeqO]

end CFSG.LocalAnalysis.WeakClosure81

end
