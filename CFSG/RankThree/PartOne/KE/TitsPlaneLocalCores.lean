module

public import CFSG.RankThree.PartOne.KE.TitsFiveCentralizer
public import CFSG.Sporadic.Schreier.TitsInter
public import CFSG.RankThree.GroupTheory.SteinbergBMSmallTwoSylowOddKernel
public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.Sporadic.Schreier.Tits
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.GroupTheory.SteinbergBY (mul_comm_of_isMulCommutative
  normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore orderOf_eq_of_isElementaryAbelian)

section Actor

variable {J : Type*} [Group J] (T : Subgroup J) [T.Normal] (e : T ≃* titsD)

include e

@[expose] def titsActor : J →* MulAut titsD :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem titsActor_coe (t : T) : titsActor T e (t : J) = MulAut.conj (e t) := by
  rw [titsActor, MonoidHom.comp_apply, MulAut.conjNormal_val]
  exact congr_conj e t

theorem titsActor_injective (hC : Subgroup.centralizer (T : Set J) = ⊥) :
    Function.Injective (titsActor T e) := by
  rw [injective_iff_map_eq_one]
  intro j hj
  have h1 : MulAut.conjNormal j = (1 : MulAut T) := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hj
  have hjC : j ∈ Subgroup.centralizer (T : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := congrArg (fun φ : MulAut T => ((φ ⟨t, ht⟩ : T) : J)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc t * j = j * t * j⁻¹ * j := by rw [this]
      _ = j * t := by group
  rw [hC, Subgroup.mem_bot] at hjC
  exact hjC

@[expose] def titsOuterActor : J →* Outer titsD :=
  (QuotientGroup.mk' (inner titsD)).comp (titsActor T e)

theorem ker_titsOuterActor (hC : Subgroup.centralizer (T : Set J) = ⊥) :
    (titsOuterActor T e).ker = T := by
  have hinj := titsActor_injective T e hC
  ext j
  rw [MonoidHom.mem_ker, titsOuterActor, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    have : titsActor T e ((e.symm x : T) : J) = titsActor T e j := by
      rw [titsActor_coe, e.apply_symm_apply]
      exact hx
    rw [← hinj this]
    exact (e.symm x).2
  · intro hj
    exact ⟨e ⟨j, hj⟩, (titsActor_coe T e ⟨j, hj⟩).symm⟩

theorem titsActor_mem_of_orderOf_two (hC : Subgroup.centralizer (T : Set J) = ⊥) {v : J}
    (hv : orderOf v = 2) : v ∈ T := by
  have hinj := titsActor_injective T e hC
  have h2 : orderOf (titsActor T e v) = 2 := by
    rw [orderOf_injective _ hinj v]
    exact hv
  obtain ⟨x, -, hx⟩ := mem_inner_of_orderOf_two h2
  have : titsActor T e ((e.symm x : T) : J) = titsActor T e v := by
    rw [titsActor_coe, e.apply_symm_apply]
    exact hx
  rw [← hinj this]
  exact (e.symm x).2

theorem titsActor_relIndex_dvd_two (hC : Subgroup.centralizer (T : Set J) = ⊥) (C : Subgroup J) :
    T.relIndex C ∣ 2 := by
  have h1 : ((titsOuterActor T e).comp C.subtype).ker = T.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_titsOuterActor T e hC]
    rfl
  rw [Subgroup.relIndex, ← h1, Subgroup.index_ker]
  exact (Subgroup.card_subgroup_dvd_card _).trans (by rw [card_outer_titsD])

theorem titsActor_mem_of_pow_eq_one (hC : Subgroup.centralizer (T : Set J) = ⊥) {p : ℕ}
    (hp : ¬ 2 ∣ p) {x : J} (hx : x ^ p = 1) : x ∈ T := by
  have h1 : orderOf (titsOuterActor T e x) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (titsOuterActor T e x) ∣ 2 := by
    have := orderOf_dvd_natCard (titsOuterActor T e x)
    rwa [card_outer_titsD] at this
  have h3 : orderOf (titsOuterActor T e x) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hp) h2 h1
  rw [orderOf_eq_one_iff] at h3
  have : x ∈ (titsOuterActor T e).ker := h3
  rwa [ker_titsOuterActor T e hC] at this

end Actor

theorem tits_eq_five_of_sq_dvd_card_aut {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : p ^ 2 ∣ 35942400) : p = 5 := by
  have hp1 : p ∣ 35942400 := (dvd_pow_self p two_ne_zero).trans h
  have hfac : (35942400 : ℕ) = 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [hfac] at hp1 h
  rcases (Nat.Prime.dvd_mul hp).1 hp1 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h2)
  · have h13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h1
    subst h13
    exact absurd h (by norm_num)

theorem finite_mulAut_titsD : Finite (MulAut titsD) :=
  Finite.of_equiv titsA titsConjEquiv.toEquiv

theorem card_mulAut_titsD : Nat.card (MulAut titsD) = 35942400 := by
  rw [← Nat.card_congr titsConjEquiv.toEquiv, card_titsA]

theorem tits_eq_five_of_injective_hom_mulAut {M : Type*} [Group M] (e : M ≃* titsD) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {A : Type*} [Group A] (f : A →* MulAut M)
    (hf : Function.Injective f) (hA : Nat.card A = p ^ 2) : p = 5 := by
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [hA, Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_titsD] at hdvd
  exact tits_eq_five_of_sq_dvd_card_aut hp hp3 hdvd

theorem tits_le_zpowers_sup_zpowers {J : Type*} [Group J] [Finite J] {E : Subgroup J} {a b : J}
    (hE : Nat.card E = 25) (haE : a ∈ E) (hbE : b ∈ E) (ha5 : orderOf a = 5)
    (hb : b ∉ Subgroup.zpowers a) : E ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set S : Subgroup J := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hS
  have hSE : S ≤ E := sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hbE)
  have hdvd : Nat.card S ∣ 5 ^ 2 := by
    have := Subgroup.card_dvd_of_le hSE
    rw [hE] at this
    simpa using this
  have hzS : Nat.card (Subgroup.zpowers a) = 5 := by rw [Nat.card_zpowers, ha5]
  have ha_dvd : 5 ∣ Nat.card S := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers a ≤ S)
    rwa [hzS] at this
  obtain ⟨k, hk2, hkS⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hkS
    rw [hkS] at ha_dvd
    omega
  interval_cases k
  · exfalso
    have hSa : Subgroup.zpowers a = S :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by norm_num at hkS; omega)
    exact hb (hSa ▸ (le_sup_right : Subgroup.zpowers b ≤ S) (Subgroup.mem_zpowers b))
  · have hSE' : S = E := Subgroup.eq_of_le_of_card_ge hSE (by norm_num at hkS; omega)
    exact hSE'.ge

section Centralizer

variable {J : Type*} [Group J] [Finite J] (T : Subgroup J) [T.Normal] (e : T ≃* titsD)

include e

omit [Finite J] in
theorem tits_not_sixteen_dvd_card_centralizer (hC : Subgroup.centralizer (T : Set J) = ⊥) {a : J}
    (haT : a ∈ T) (ha5 : orderOf a = 5) :
    ¬ 16 ∣ Nat.card (Subgroup.centralizer ({a} : Set J)) := by
  have haT5 : orderOf (⟨a, haT⟩ : T) = 5 := by
    rw [Subgroup.orderOf_mk]
    exact ha5
  have h4 := tits_not_four_dvd_card_centralizer_of_mulEquiv e haT5
  have hcardTC : Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set J)) =
      Nat.card (Subgroup.centralizer ({(⟨a, haT⟩ : T)} : Set T)) := by
    have h := Subgroup.card_map_of_injective T.subtype_injective
      (K := Subgroup.centralizer ({(⟨a, haT⟩ : T)} : Set T))
    rw [map_subtype_centralizer] at h
    exact h
  have hmul := Subgroup.relIndex_mul_card (H := T) (K := Subgroup.centralizer ({a} : Set J))
  have hr := titsActor_relIndex_dvd_two T e hC (Subgroup.centralizer ({a} : Set J))
  intro h
  rw [← hmul, hcardTC] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 hr with h1 | h1
  · rw [h1] at h
    exact h4 (by omega)
  · rw [h1] at h
    exact h4 (by omega)

theorem tits_exists_sylow_two_card_le_eight (hC : Subgroup.centralizer (T : Set J) = ⊥) {a : J}
    (haT : a ∈ T) (ha5 : orderOf a = 5) :
    ∃ P : Sylow 2 ↥(Subgroup.centralizer ({a} : Set J)), Nat.card P ≤ 8 := by
  have h16 := tits_not_sixteen_dvd_card_centralizer T e hC haT ha5
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({a} : Set J))) := inferInstance
  refine ⟨P, ?_⟩
  by_contra hgt
  push Not at hgt
  have hgt' : 8 < Nat.card (P : Subgroup ↥(Subgroup.centralizer ({a} : Set J))) := hgt
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hk'
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 2 ^ 4 ∣ Nat.card (P : Subgroup ↥(Subgroup.centralizer ({a} : Set J))) := by
    rw [hk]
    exact pow_dvd_pow 2 hk4
  have h2 := h1.trans (Subgroup.card_subgroup_dvd_card _)
  norm_num at h2
  exact h16 h2

omit [Finite J] in
theorem tits_no_involution_centralizing_pair (hC : Subgroup.centralizer (T : Set J) = ⊥)
    {E : Subgroup J} (hE : Nat.card E = 25) (hET : E ≤ T) {a b : J}
    (hgen : E ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b) {v : J} (hv : orderOf v = 2)
    (hva : a * v = v * a) (hvb : b * v = v * b) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hvT : v ∈ T := titsActor_mem_of_orderOf_two T e hC hv
  have hEv : E ≤ Subgroup.centralizer ({v} : Set J) :=
    hgen.trans (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hva))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hvb)))
  set ET : Subgroup T := E.subgroupOf T with hETdef
  have hET25 : Nat.card ET = 25 := by
    rw [hETdef, card_subgroupOf_eq hET, hE]
  have hodd := tits_odd_card_centralizer_of_mulEquiv e hET25
  set vT : T := ⟨v, hvT⟩ with hvT_def
  have hvT2 : orderOf vT = 2 := by
    rw [hvT_def, Subgroup.orderOf_mk]
    exact hv
  have hvT_mem : vT ∈ Subgroup.centralizer (ET : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyE : (y : J) ∈ E := hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hEv hyE)
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (ET : Set T)) := by
    have := orderOf_dvd_natCard (⟨vT, hvT_mem⟩ : Subgroup.centralizer (ET : Set T))
    rwa [Subgroup.orderOf_mk, hvT2] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end Centralizer


theorem tits_almost_simple_faithful_plane_local_cores_odd {J : Type*} [Group J] [Finite J]
    (T : Subgroup J) [T.Normal] (e : T ≃* titsD) (hC : Subgroup.centralizer (T : Set J) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (E : Subgroup J) [IsElementaryAbelian p E]
    (hEcard : Nat.card E = p ^ 2) {a : J} (haE : a ∈ E) (ha1 : a ≠ 1) :
    p = 5 ∧
      (∀ K : Subgroup ↥(Subgroup.centralizer ({a} : Set J)), K.Normal → ¬ p ∣ Nat.card K →
        Odd (Nat.card K)) ∧
      Odd (Nat.card (aschbacherSolvableCore p ↥(Subgroup.centralizer ({a} : Set J)))) := by
  have hp2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hET : E ≤ T := fun x hx =>
    titsActor_mem_of_pow_eq_one T e hC hp2 (elemPow_eq_one_of_isElementaryAbelian x hx)
  have hp5 : p = 5 := by
    have h1 : p ^ 2 ∣ Nat.card T := by
      have := Subgroup.card_dvd_of_le hET
      rwa [hEcard] at this
    rw [Nat.card_congr e.toEquiv, card_titsD] at h1
    exact tits_eq_five_of_sq_dvd_card_aut hp hp3 (h1.trans (by norm_num))
  subst hp5
  have hE25 : Nat.card E = 25 := by rw [hEcard]; norm_num
  have key : ∀ K : Subgroup ↥(Subgroup.centralizer ({a} : Set J)), K.Normal → ¬ 5 ∣ Nat.card K →
      Odd (Nat.card K) := by
    intro K hK hpK
    have haT : a ∈ T := hET haE
    have ha5 : orderOf a = 5 :=
      orderOf_eq_of_isElementaryAbelian hp haE ha1
    obtain ⟨b, hbE, hb⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push Not at hcon
      have hle : E ≤ Subgroup.zpowers a := fun x hx => hcon x hx
      have := Subgroup.card_le_of_le hle
      rw [hE25, Nat.card_zpowers, ha5] at this
      omega
    have hb1 : b ≠ 1 := fun h => hb (by rw [h]; exact Subgroup.one_mem _)
    have hb5 : orderOf b = 5 :=
      orderOf_eq_of_isElementaryAbelian hp hbE hb1
    have hba : b * a = a * b :=
      mul_comm_of_isMulCommutative hbE haE
    have hbC : b ∈ Subgroup.centralizer ({a} : Set J) :=
      Subgroup.mem_centralizer_singleton_iff.2 hba
    have hgen := tits_le_zpowers_sup_zpowers hE25 haE hbE ha5 hb
    have hb'5 : orderOf (⟨b, hbC⟩ : ↥(Subgroup.centralizer ({a} : Set J))) = 5 := by
      rw [Subgroup.orderOf_mk]
      exact hb5
    have hodd : Odd (Nat.card (Subgroup.centralizer
        ({(⟨b, hbC⟩ : ↥(Subgroup.centralizer ({a} : Set J)))} :
          Set ↥(Subgroup.centralizer ({a} : Set J))))) := by
      by_contra hnodd
      have h2 := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hvJ : orderOf ((((v : ↥(Subgroup.centralizer ({a} : Set J))) : J))) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hv
      have hv1 := Subgroup.mem_centralizer_singleton_iff.1
        (((v : ↥(Subgroup.centralizer ({a} : Set J)))).2)
      have hv2 := congrArg (fun z : ↥(Subgroup.centralizer ({a} : Set J)) => (z : J))
        (Subgroup.mem_centralizer_singleton_iff.1 v.2)
      exact tits_no_involution_centralizing_pair T e hC hE25 hET hgen hvJ hv1.symm hv2.symm
    exact CFSG.RankThree.GroupTheory.SteinbergBM.small_two_sylow_normal_prime_complement_odd hp
      (by norm_num) (by norm_num) hb'5 hodd (tits_exists_sylow_two_card_le_eight T e hC haT ha5)
      hK hpK
  exact ⟨rfl, key, key _ inferInstance (solvable_prime_complement_core_characterization hp).2.2.1⟩

theorem planeLocalCoreOdd_tits (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    PlaneLocalCoreOdd p titsD := by
  intro B hB A hAB hA hAcard t htA ht1
  have : IsElementaryAbelian p A := hA
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut titsD) := finite_mulAut_titsD
  have hle : inner titsD ≤ B := hB
  set T : Subgroup B := (inner titsD).subgroupOf B with hT
  have : T.Normal := (inner_normal titsD).subgroupOf B
  let e : T ≃* titsD :=
    (Subgroup.subgroupOfEquivOfLe hle).trans (MonoidHom.ofInjective conj_titsD_injective).symm
  have hCT : Subgroup.centralizer (T : Set B) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine mulAut_eq_one_of_commute_conj_of_closure_eq_top conj_titsD_injective
      (S := Set.univ) (by simp) ?_
    intro x _
    have hx : (⟨MulAut.conj x, hle ⟨x, rfl⟩⟩ : B) ∈ T := Subgroup.mem_subgroupOf.2 ⟨x, rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hb _ hx)).symm
  set E : Subgroup B := A.subgroupOf B with hEdef
  have : IsElementaryAbelian p E := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card E = p ^ 2 := by
    rw [hEdef, card_subgroupOf_eq hAB, hAcard]
  set a : B := ⟨t, hAB htA⟩ with ha_def
  have haE : a ∈ E := htA
  have ha1 : a ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨-, -, hθ⟩ := tits_almost_simple_faithful_plane_local_cores_odd T e hCT hp hp3 E hEcard
    haE ha1
  set S := inSubgroup (aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({t} : Set (MulAut titsD))) with hS
  have hSodd : ¬ 2 ∣ Nat.card S := by
    have hmap : (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({a} : Set B))).map B.subtype = S :=
      map_subtype_theta_centralizer hp B a
    have h1 : Nat.card S =
        Nat.card (aschbacherSolvableCore p ↥(Subgroup.centralizer ({a} : Set B))) := by
      rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective, inSubgroup,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    rw [h1]
    exact fun h2 => (Nat.not_even_iff_odd.2 hθ) (even_iff_two_dvd.2 h2)
  have hAC : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut titsD)) := fun x hx =>
    Subgroup.mem_inf.2 ⟨hAB hx,
      Subgroup.mem_centralizer_singleton_iff.2 (mul_comm_of_isMulCommutative hx htA)⟩
  have hAS : A ≤ Subgroup.normalizer (S : Set (MulAut titsD)) := fun x hx =>
    normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore
      p _ (Subgroup.le_normalizer (hAC hx))
  have hSA : ⁅S, A⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hAS
  have hIS : autThetaT p B A ≤ S := fun x hx => by
    simp only [autThetaT, Subgroup.mem_iInf] at hx
    exact hx t htA ht1
  have hle' : autPlaneProduct p B A t ≤ S := sup_le hSA hIS
  intro h2
  exact hSodd (h2.trans (Subgroup.card_dvd_of_le hle'))

end CFSG.RankThree.PartOne.KE
