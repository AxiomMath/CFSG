module

public import CFSG.RankThree.PartOne.KE.TitsFiveCheck
public import CFSG.Sporadic.Schreier.TitsInv

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def titsFive : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsFiveWord

theorem titsFive_rep : Rep 1755 titsFiveArr titsFive :=
  rep_wordArr_titsT titsFive_check.1

theorem titsFive_mem_titsH : titsFive ∈ titsH :=
  mem_titsH_of_sift titsFive_rep titsFive_check.2.1

theorem titsFive_ne_one : titsFive ≠ 1 := by
  intro h
  have := (eqA_iff titsFive_rep rep_idA).2 h
  rw [titsFive_check.2.2.1] at this
  exact Bool.false_ne_true this

theorem titsFive_pow_five : titsFive ^ 5 = 1 := by
  have h := eq_of_eqA (rep_compA (rep_compA (rep_compA (rep_compA titsFive_rep titsFive_rep)
    titsFive_rep) titsFive_rep) titsFive_rep) rep_idA titsFive_check.2.2.2.1
  calc titsFive ^ 5 = titsFive * titsFive * titsFive * titsFive * titsFive := by
        simp [pow_succ]
    _ = 1 := h

theorem orderOf_titsFive : orderOf titsFive = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime titsFive_pow_five titsFive_ne_one

theorem titsCH5_facts {c : Array ℕ} (hc : c ∈ titsCH5) :
    isInvA 1755 c (invCand 1755 c) = true ∧ commA c titsFiveArr = true ∧ inH c = true := by
  have := List.all_eq_true.1 titsFive_check.2.2.2.2.2.2.1 c hc
  simpa [Bool.and_eq_true, and_assoc] using this

theorem titsCH5_eq :
    ((titsH ⊓ Subgroup.centralizer {titsFive} : Subgroup (Equiv.Perm (Fin 1755))) :
      Set (Equiv.Perm (Fin 1755))) = {g | g ∈ titsCH5.map (permOfArr 1755)} := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq,
    List.mem_map]
  constructor
  · rintro ⟨hgH, hgC⟩
    have hgQ : g ∈ titsQH.originalSubgroup := by rw [titsQH_facts.2.2.1]; exact hgH
    obtain ⟨a, ha, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.1 (by show (finList 1755 titsHBase).length = 5; simp [finList,
        titsCentral_check.2.1]) titsFive_check.2.2.2.2.1 hgQ
    have hcomm := (commA_iff ha titsFive_rep).2 (Subgroup.mem_centralizer_singleton_iff.1 hgC)
    simp only [hcomm, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
    obtain ⟨c, hc, hac⟩ := hp
    exact ⟨c, hc, (eq_of_eqA ha (rep_permOfArr (titsCH5_facts hc).1).1 hac).symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hinv, hcomm, hH⟩ := titsCH5_facts hc
    have hr := (rep_permOfArr hinv).1
    exact ⟨mem_titsH_of_sift hr hH,
      Subgroup.mem_centralizer_singleton_iff.2 ((commA_iff hr titsFive_rep).1 hcomm)⟩

theorem card_titsCH5 :
    Nat.card (titsH ⊓ Subgroup.centralizer {titsFive} : Subgroup (Equiv.Perm (Fin 1755))) = 10 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsCH5_eq,
    ncard_list_set (nodup_map_permOfArr (fun _ hc => (titsCH5_facts hc).1)
      titsFive_check.2.2.2.2.2.2.2), List.length_map, titsFive_check.2.2.2.2.2.1]

theorem tits_centralizer_singleton_eq_of_zpowers_eq {G : Type*} [Group G] {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  have key : ∀ {x y : G}, y ∈ Subgroup.zpowers x →
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro x y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact Commute.zpow_right hz k
  exact le_antisymm (key (h ▸ Subgroup.mem_zpowers y)) (key (h ▸ Subgroup.mem_zpowers x))

theorem tits_card_centralizer_eq_of_isConj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  rw [← hg, ← map_conj_centralizer g x,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem card_centralizer_titsFive_H :
    Nat.card (Subgroup.centralizer ({(⟨titsFive, titsFive_mem_titsH⟩ : titsH)} :
      Set titsH)) = 10 := by
  rw [← Subgroup.card_map_of_injective titsH.subtype_injective, map_subtype_centralizer]
  exact card_titsCH5

theorem card_centralizer_titsH_of_orderOf_five {x : titsH} (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set titsH)) = 10 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a : titsH := ⟨titsFive, titsFive_mem_titsH⟩ with ha_def
  have ha : orderOf a = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_titsFive
  have hP : IsPGroup 5 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hindex : ¬ 5 ∣ (Subgroup.zpowers a).index := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers a)
    rw [Nat.card_zpowers, ha, titsQH_facts.2.2.2] at h
    have h' : (Subgroup.zpowers a).index = 2048 := by omega
    rw [h']
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (hP.toSylow hindex) (x := x)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]))
  rw [IsPGroup.toSylow_coe] at hg
  have hyo : orderOf (g * x * g⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [MulAut.conj_apply, hx] using this
  have hzy : Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers a := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg)
    rw [Nat.card_zpowers, Nat.card_zpowers, hyo, ha]
  rw [tits_card_centralizer_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩ : IsConj x (g * x * g⁻¹)),
    tits_centralizer_singleton_eq_of_zpowers_eq hzy]
  exact card_centralizer_titsFive_H

theorem card_centralizer_inf_titsZD_of_orderOf_five {x : titsD} (hx : orderOf x = 5)
    (hz : x ∈ Subgroup.centralizer ({titsZD} : Set titsD)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set titsD) ⊓
      Subgroup.centralizer ({titsZD} : Set titsD)) = 10 := by
  have hxz : (x : Equiv.Perm (Fin 1755)) * titsZ = titsZ * x :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hz)
  have hxH : (x : Equiv.Perm (Fin 1755)) ∈ titsH := by
    rw [← titsD_centralizer_z]
    exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 hxz⟩
  set xH : titsH := ⟨(x : Equiv.Perm (Fin 1755)), hxH⟩ with hxH_def
  have hxHo : orderOf xH = 5 :=
    calc orderOf xH = orderOf (xH : Equiv.Perm (Fin 1755)) := (Subgroup.orderOf_coe xH).symm
      _ = orderOf (x : Equiv.Perm (Fin 1755)) := rfl
      _ = orderOf x := Subgroup.orderOf_coe x
      _ = 5 := hx
  have hmap : (Subgroup.centralizer ({x} : Set titsD) ⊓
      Subgroup.centralizer ({titsZD} : Set titsD)).map titsD.subtype =
      titsH ⊓ Subgroup.centralizer {(x : Equiv.Perm (Fin 1755))} := by
    rw [Subgroup.map_inf _ _ _ titsD.subtype_injective, map_subtype_centralizer,
      map_subtype_centralizer]
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hgD, hgx⟩, -, hgz⟩
      have hg : g ∈ titsD ⊓ Subgroup.centralizer {titsZ} := Subgroup.mem_inf.2 ⟨hgD, hgz⟩
      rw [titsD_centralizer_z] at hg
      exact ⟨hg, hgx⟩
    · rintro ⟨hgH, hgx⟩
      have hg := hgH
      rw [← titsD_centralizer_z] at hg
      exact ⟨⟨(Subgroup.mem_inf.1 hg).1, hgx⟩, Subgroup.mem_inf.1 hg⟩
  have h10 := card_centralizer_titsH_of_orderOf_five hxHo
  rw [← Subgroup.card_map_of_injective titsH.subtype_injective, map_subtype_centralizer] at h10
  rw [← Subgroup.card_map_of_injective titsD.subtype_injective, hmap]
  exact h10

theorem tits_card_centralizer_inf_of_order_five_two {a u : titsD} (ha : orderOf a = 5)
    (hu : orderOf u = 2) (hau : u ∈ Subgroup.centralizer ({a} : Set titsD)) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set titsD) ⊓
      Subgroup.centralizer ({u} : Set titsD)) = 10 := by
  rcases titsD_involution_conj u hu with hz | ht
  · obtain ⟨g, hg⟩ := isConj_iff.1 hz
    have hcomm : u * a = a * u := Subgroup.mem_centralizer_singleton_iff.1 hau
    have key : (g⁻¹ * a * g) * titsZD = titsZD * (g⁻¹ * a * g) := by
      have h1 : g⁻¹ * (u * a) * g = g⁻¹ * (a * u) * g := by rw [hcomm]
      rw [← hg] at h1
      calc (g⁻¹ * a * g) * titsZD = g⁻¹ * (a * (g * titsZD * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * titsZD * g⁻¹ * a) * g := h1.symm
        _ = titsZD * (g⁻¹ * a * g) := by group
    have ha' : orderOf (g⁻¹ * a * g) = 5 := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
      simpa [MulAut.conj_apply, ha] using this
    have hmap : (Subgroup.centralizer ({g⁻¹ * a * g} : Set titsD) ⊓
        Subgroup.centralizer ({titsZD} : Set titsD)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer ({a} : Set titsD) ⊓ Subgroup.centralizer ({u} : Set titsD) := by
      have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_centralizer,
        map_conj_centralizer, hg, e1]
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_centralizer_inf_titsZD_of_orderOf_five ha'
      (Subgroup.mem_centralizer_singleton_iff.2 key)
  · exfalso
    have hcard := tits_card_centralizer_eq_of_isConj ht
    rw [titsD_centralizer_t.2.1] at hcard
    have hau' : a ∈ Subgroup.centralizer ({u} : Set titsD) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hau ⊢
      exact hau.symm
    have hdvd := orderOf_dvd_natCard (⟨a, hau'⟩ : Subgroup.centralizer ({u} : Set titsD))
    rw [Subgroup.orderOf_mk, ha, ← hcard] at hdvd
    omega

theorem tits_card_le_two_of_isPGroup_le_centralizer {a : titsD} (ha : orderOf a = 5)
    {Q : Subgroup titsD} (hQ : IsPGroup 2 Q) (hQa : Q ≤ Subgroup.centralizer ({a} : Set titsD)) :
    Nat.card Q ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup (Subgroup.center Q)
  have h2Z : 2 ∣ Nat.card (Subgroup.center Q) := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    rcases n with _ | n
    · exfalso
      rw [pow_zero] at hn
      have := Finite.one_lt_card (α := Subgroup.center Q)
      omega
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
  set u : titsD := ((x : Q) : titsD) with hu_def
  have hu : orderOf u = 2 := by
    rw [hu_def, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  have huC : u ∈ Subgroup.centralizer ({a} : Set titsD) := hQa (x : Q).2
  have hcomm : ∀ r : Q, (r : titsD) * u = u * (r : titsD) := by
    intro r
    have := Subgroup.mem_center_iff.1 x.2 r
    exact congrArg (fun z : Q => (z : titsD)) this
  have hle : Q ≤ Subgroup.centralizer ({a} : Set titsD) ⊓
      Subgroup.centralizer ({u} : Set titsD) := fun y hy =>
    Subgroup.mem_inf.2 ⟨hQa hy, Subgroup.mem_centralizer_singleton_iff.2 (hcomm ⟨y, hy⟩)⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [tits_card_centralizer_inf_of_order_five_two ha hu huC] at hdvd
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk'
    have hk1 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 4 ∣ Nat.card Q := by
    rw [hk]
    exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  have := h4.trans hdvd
  omega

theorem tits_card_sylow_two_centralizer_le_two {a : titsD} (ha : orderOf a = 5)
    (R : Sylow 2 ↥(Subgroup.centralizer ({a} : Set titsD))) : Nat.card R ≤ 2 := by
  have hQ : IsPGroup 2 ((R : Subgroup ↥(Subgroup.centralizer ({a} : Set titsD))).map
      (Subgroup.centralizer ({a} : Set titsD)).subtype) := R.isPGroup'.map _
  have hle : (R : Subgroup ↥(Subgroup.centralizer ({a} : Set titsD))).map
      (Subgroup.centralizer ({a} : Set titsD)).subtype ≤
        Subgroup.centralizer ({a} : Set titsD) := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have h := tits_card_le_two_of_isPGroup_le_centralizer ha hQ hle
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h
  exact h

theorem tits_not_four_dvd_of_sylow_two_le_two {C : Type*} [Group C] [Finite C]
    (h : ∀ R : Sylow 2 C, Nat.card R ≤ 2) : ¬ 4 ∣ Nat.card C := by
  intro h4
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 (n := 2) (by simpa using h4)
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hK).exists_le_sylow
  have h1 := Subgroup.card_le_of_le hP
  have h2 := h P
  rw [hK] at h1
  omega

theorem tits_odd_card_centralizer_of_card_twentyfive {E : Subgroup titsD} (hE : Nat.card E = 25) :
    Odd (Nat.card ↥(Subgroup.centralizer (E : Set titsD))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer (E : Set titsD)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set u : titsD := (v : titsD) with hu_def
  have hu : orderOf u = 2 := by
    rw [hu_def, Subgroup.orderOf_coe]
    exact hv
  have hEu : E ≤ Subgroup.centralizer ({u} : Set titsD) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 v.2 y hy
  have h25 : 25 ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set titsD)) := by
    have := Subgroup.card_dvd_of_le hEu
    rwa [hE] at this
  rcases titsD_involution_conj u hu with hz | ht
  · rw [← tits_card_centralizer_eq_of_isConj hz, card_centralizer_titsZD] at h25
    omega
  · rw [← tits_card_centralizer_eq_of_isConj ht, titsD_centralizer_t.2.1] at h25
    omega

theorem tits_map_centralizer_mulEquiv {G M : Type*} [Group G] [Group M] (e : G ≃* M) (S : Set G) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    have := congrArg e (h s hs)
    simpa using this
  · intro h s hs
    apply e.injective
    have := h (e s) ⟨s, hs, rfl⟩
    simpa using this

theorem tits_card_centralizer_mulEquiv {G M : Type*} [Group G] [Group M] (e : G ≃* M) (S : Set G) :
    Nat.card (Subgroup.centralizer S) = Nat.card (Subgroup.centralizer (e '' S)) := by
  rw [← tits_map_centralizer_mulEquiv, Subgroup.card_map_of_injective e.injective]

theorem tits_not_four_dvd_card_centralizer_of_mulEquiv {G : Type*} [Group G]
    (e : G ≃* titsD) {a : G} (ha : orderOf a = 5) :
    ¬ 4 ∣ Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  rw [tits_card_centralizer_mulEquiv e, Set.image_singleton]
  exact tits_not_four_dvd_of_sylow_two_le_two fun R =>
    tits_card_sylow_two_centralizer_le_two (by rw [MulEquiv.orderOf_eq]; exact ha) R

theorem tits_odd_card_centralizer_of_mulEquiv {G : Type*} [Group G] (e : G ≃* titsD)
    {E : Subgroup G} (hE : Nat.card E = 25) :
    Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))) := by
  have hE' : Nat.card (E.map e.toMonoidHom) = 25 := by
    rw [Subgroup.card_map_of_injective e.injective, hE]
  have h := tits_odd_card_centralizer_of_card_twentyfive hE'
  have hset : e '' (E : Set G) = ((E.map e.toMonoidHom : Subgroup titsD) : Set titsD) := by
    rw [Subgroup.coe_map]
    rfl
  rw [tits_card_centralizer_mulEquiv e, hset]
  exact h

theorem tits_five_centralizer_two_part_and_plane_centralizer_odd :
    (∀ a u : titsD, orderOf a = 5 → orderOf u = 2 → u ∈ Subgroup.centralizer ({a} : Set titsD) →
      Nat.card ↥(Subgroup.centralizer ({a} : Set titsD) ⊓
        Subgroup.centralizer ({u} : Set titsD)) = 10) ∧
    (∀ a : titsD, orderOf a = 5 →
      ∀ R : Sylow 2 ↥(Subgroup.centralizer ({a} : Set titsD)), Nat.card R ≤ 2) ∧
    (∀ E : Subgroup titsD, IsElementaryAbelian 5 E → Nat.card E = 25 →
      Odd (Nat.card ↥(Subgroup.centralizer (E : Set titsD)))) :=
  ⟨fun _ _ ha hu hau => tits_card_centralizer_inf_of_order_five_two ha hu hau,
    fun _ ha R => tits_card_sylow_two_centralizer_le_two ha R,
    fun _ _ hE => tits_odd_card_centralizer_of_card_twentyfive hE⟩

end CFSG.RankThree.PartOne.KE
