module

public import CFSG.Sporadic.Co2I301.RowBasic

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271 CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301


private theorem locZ_mem_P : locZ ∈ co2P := locC_le_P (locQ_le_C locZ_mem_Q)

private theorem commute_locZ_of_mem_locQ {q : Equiv.Perm (Fin 2300)} (hq : q ∈ locQ) :
    Commute q locZ :=
  Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 locZ_mem_centerIn_Q).2 q hq

private theorem locC_le_normalizer :
    locC ≤ Subgroup.normalizer (locQ : Set (Equiv.Perm (Fin 2300))) :=
  Subgroup.le_normalizer_of_normal_subgroupOf locQ_le_C

private theorem K0_le_locC : K0 ≤ locC := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact gens_mem_locC.2.2.2.2.1
  · exact gens_mem_locC.2.2.2.2.2

private theorem K0_le_P : K0 ≤ co2P := K0_le_locC.trans locC_le_P

private theorem K0_le_U0 : K0 ≤ U0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact gens_mem_U0.1
  · exact gens_mem_U0.2.1

private theorem K0_le_centralizer_dP : K0 ≤ Subgroup.centralizer {dP} := by
  obtain ⟨-, -, -, h1, h2, -⟩ := commute_facts
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.2 h1.eq.symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 h2.eq.symm

private theorem K0_le_centralizer_locZ : K0 ≤ Subgroup.centralizer {locZ} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h1, h2⟩ := commute_facts
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.2 h1.eq.symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 h2.eq.symm

private theorem sP_conj_mem_K0 {h : Equiv.Perm (Fin 2300)} (hh : h ∈ K0) : sP * h * sP⁻¹ ∈ K0 := by
  have hle : K0 ≤ K0.comap (MulAut.conj sP).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl) <;>
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · exact mem_K0_facts.2.2.1
    · exact mem_K0_facts.2.2.2
  have h := hle hh
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

private theorem closure_dzs_le_normalizer :
    Subgroup.closure {dP, locZ, sP} ≤ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 2300))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.1 (K0_le_centralizer_dP hh)
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.1 (K0_le_centralizer_locZ hh)
  · refine Subgroup.mem_normalizer_iff.2 fun h => ⟨sP_conj_mem_K0, fun hh => ?_⟩
    have hs : sP * sP = 1 := by rw [← pow_two]; exact pow_facts.2.2.2.2
    have key : sP * (sP * h * sP⁻¹) * sP⁻¹ = h := by
      rw [inv_eq_of_mul_eq_one_right hs]
      calc sP * (sP * h * sP) * sP = sP * sP * h * (sP * sP) := by simp only [mul_assoc]
        _ = h := by rw [hs, one_mul, mul_one]
    rw [← key]
    exact sP_conj_mem_K0 hh

private theorem closure_dzs_le_P : Subgroup.closure {dP, locZ, sP} ≤ co2P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · exact locC_le_P gens_mem_locC.1
  · exact locZ_mem_P
  · exact locC_le_P gens_mem_locC.2.1

private theorem dzs_mem_closure (i j k : ℕ) :
    dP ^ i * locZ ^ j * sP ^ k ∈ Subgroup.closure {dP, locZ, sP} :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

private theorem closure_dzs_comm {a b : Equiv.Perm (Fin 2300)}
    (ha : a ∈ Subgroup.closure {dP, locZ, sP}) (hb : b ∈ Subgroup.closure {dP, locZ, sP}) :
    a * b = b * a := by
  obtain ⟨hds, -, -, -, -, -, hzd, hzs, -⟩ := commute_facts
  have hpw : ({dP, locZ, sP} : Set (Equiv.Perm (Fin 2300))).Pairwise Commute := by
    intro u hu v hv _
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    exacts [Commute.refl _, hzd.symm, hds, hzd, Commute.refl _, hzs, hds.symm, hzs.symm,
      Commute.refl _]
  have := Subgroup.isMulCommutative_closure hpw
  exact setLike_mul_comm ha hb

private theorem mem_normalizer_K0 {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P)
    (hd : Commute g dP) (hz : Commute g locZ) :
    g ∈ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 2300))) := by
  obtain ⟨i, j, k, -, -, -, hK⟩ := (centralizer_facts g hg hd hz).1
  have h := Subgroup.mul_mem _ (Subgroup.le_normalizer hK)
    (closure_dzs_le_normalizer (dzs_mem_closure i j k))
  rwa [inv_mul_cancel_right] at h

private theorem commute_locZ_of_conj {g : Equiv.Perm (Fin 2300)} (h1 : g * locZ * g⁻¹ ∈ locQ)
    (h2 : ∀ q ∈ locQ, g⁻¹ * q * g ∈ locQ) : Commute g locZ := by
  have hzc := locZ_mem_centerIn_Q
  have hw : g * locZ * g⁻¹ ∈ CFSG.centerIn locQ := by
    refine Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have hc : g⁻¹ * q * g * locZ = locZ * (g⁻¹ * q * g) := commute_locZ_of_mem_locQ (h2 q hq)
    calc q * (g * locZ * g⁻¹) = g * (g⁻¹ * q * g * locZ) * g⁻¹ := by group
      _ = g * (locZ * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = g * locZ * g⁻¹ * q := by group
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(CFSG.centerIn locQ))).1 card_centerIn_Q
  have hz1 : (⟨locZ, hzc⟩ : ↥(CFSG.centerIn locQ)) ≠ 1 := fun h =>
    locZ_ne_one (congrArg Subtype.val h)
  have hw1 : (⟨g * locZ * g⁻¹, hw⟩ : ↥(CFSG.centerIn locQ)) ≠ 1 := fun h =>
    locZ_ne_one (by simpa using congrArg Subtype.val h)
  have heq : locZ = g * locZ * g⁻¹ :=
    congrArg Subtype.val ((huniq _ hz1).trans (huniq _ hw1).symm)
  show g * locZ = locZ * g
  calc g * locZ = g * locZ * g⁻¹ * g := by group
    _ = locZ * g := by rw [← heq]

private theorem commute_dP_of_mem_U0 {g : Equiv.Perm (Fin 2300)} (hg : g ∈ U0) :
    Commute g dP := by
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hg
  have hlx : l * co2XB = co2XB * l :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (co2CaseB_spec.2.2.2.2.1 hl)).1
  show hP * l * hP⁻¹ * dP = dP * (hP * l * hP⁻¹)
  rw [dP_eq]
  calc hP * l * hP⁻¹ * (hP * co2XB * hP⁻¹) = hP * (l * co2XB) * hP⁻¹ := by group
    _ = hP * (co2XB * l) * hP⁻¹ := by rw [hlx]
    _ = hP * co2XB * hP⁻¹ * (hP * l * hP⁻¹) := by group

private theorem nonempty_mulEquiv_K0 : Nonempty (↥K0 ≃* alternatingGroup (Fin 6)) :=
  nonempty_mulEquiv_alternatingGroup_six o6P o6P_injective k1P_o6P k2P_o6P
    (Equiv.Perm.mem_alternatingGroup.2 (by decide)) (Equiv.Perm.mem_alternatingGroup.2 (by decide))
    eq_one_of_fix_o6P card_K0

private theorem isSimpleGroup_K0 : IsSimpleGroup ↥K0 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_K0
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact (MulEquiv.isSimpleGroup_congr e).2 this

private theorem k1P_mul_k2P_ne : k1P * k2P ≠ k2P * k1P := by
  intro h
  have h1 : (k1P * k2P) (o6P 0) = (k2P * k1P) (o6P 0) := by rw [h]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, k2P_o6P, k1P_o6P, k1P_o6P, k2P_o6P] at h1
  exact absurd (o6P_injective h1) (by decide)

private theorem nonempty_mulEquiv_K0' :
    Nonempty (↥(K0.subgroupOf co2P) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_K0
  exact ⟨(Subgroup.subgroupOfEquivOfLe K0_le_P).trans e⟩

private theorem isSimpleGroup_K0' : IsSimpleGroup ↥(K0.subgroupOf co2P) :=
  (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe K0_le_P)).2 isSimpleGroup_K0

private theorem card_K0' : Nat.card ↥(K0.subgroupOf co2P) = 360 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe K0_le_P).toEquiv).trans card_K0

private theorem exists_ne_K0' : ∃ a b : ↥(K0.subgroupOf co2P), a * b ≠ b * a := by
  have h1 : k1P ∈ K0 := Subgroup.subset_closure (by simp)
  have h2 : k2P ∈ K0 := Subgroup.subset_closure (by simp)
  refine ⟨⟨⟨k1P, K0_le_P h1⟩, Subgroup.mem_subgroupOf.2 h1⟩,
    ⟨⟨k2P, K0_le_P h2⟩, Subgroup.mem_subgroupOf.2 h2⟩, fun h => k1P_mul_k2P_ne ?_⟩
  exact congrArg (fun y : ↥(K0.subgroupOf co2P) => ((y : ↥co2P) : Equiv.Perm (Fin 2300))) h

private theorem catalogIs_isA6 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 6)) :
    catalogIs S isA6 :=
  ⟨TauCeti.CFSGIndex.alternating 6 (by norm_num), Or.inl rfl, ⟨e.trans (MulEquiv.refl _)⟩⟩

private theorem glaPLayer_eq_K0 {H : Subgroup ↥co2P} (hK0H : K0.subgroupOf co2P ≤ H)
    (hH : ∀ g ∈ H, Commute (g : Equiv.Perm (Fin 2300)) dP ∧
      Commute (g : Equiv.Perm (Fin 2300)) locZ) :
    GLAPLayer 3 H = K0.subgroupOf co2P := by
  have hnorm : ∀ g ∈ H, ∀ s ∈ K0.subgroupOf co2P, g * s * g⁻¹ ∈ K0.subgroupOf co2P :=
    fun g hg s hs => Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1
      (mem_normalizer_K0 g.2 (hH g hg).1 (hH g hg).2) _).1 (Subgroup.mem_subgroupOf.1 hs))
  refine glaPLayer_eq_of_isSimple_normal_commutator_le Nat.prime_three hK0H hnorm
    isSimpleGroup_K0' exists_ne_K0' (by rw [card_K0']; norm_num) ?_
  refine commutator_le_of_le_sup_of_commute
    (A := (Subgroup.closure {dP, locZ, sP}).subgroupOf co2P) (fun g hg => ?_)
    (fun a ha b hb => Subtype.ext (closure_dzs_comm (Subgroup.mem_subgroupOf.1 ha)
      (Subgroup.mem_subgroupOf.1 hb)))
    (fun a ha s hs => Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1
      (closure_dzs_le_normalizer (Subgroup.mem_subgroupOf.1 ha)) _).1
        (Subgroup.mem_subgroupOf.1 hs)))
  obtain ⟨i, j, k, -, -, -, hK⟩ := (centralizer_facts g g.2 (hH g hg).1 (hH g hg).2).1
  have haP := closure_dzs_le_P (dzs_mem_closure i j k)
  have hmem := Subgroup.mul_mem_sup (S := K0.subgroupOf co2P)
    (T := (Subgroup.closure {dP, locZ, sP}).subgroupOf co2P)
    (x := g * (⟨_, haP⟩ : ↥co2P)⁻¹) (y := ⟨_, haP⟩)
    (Subgroup.mem_subgroupOf.2 hK) (Subgroup.mem_subgroupOf.2 (dzs_mem_closure i j k))
  rwa [inv_mul_cancel_right] at hmem

private theorem eq_one_or_locZ {g : Equiv.Perm (Fin 2300)} (hgQ : g ∈ locQ)
    (hgd : Commute g dP) : g = 1 ∨ g = locZ := by
  have hNH : locQ ⊓ Subgroup.centralizer {dP} ≤
      co2P ⊓ Subgroup.centralizer {dP} ⊓ Subgroup.centralizer {locZ} := by
    intro n hn
    obtain ⟨hnQ, hnd⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨locC_le_P (locQ_le_C hnQ), hnd⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (commute_locZ_of_mem_locQ hnQ).eq⟩
  have hKH : K0 ≤ co2P ⊓ Subgroup.centralizer {dP} ⊓ Subgroup.centralizer {locZ} :=
    le_inf (le_inf K0_le_P K0_le_centralizer_dP) K0_le_centralizer_locZ
  have hNn : ∀ h ∈ co2P ⊓ Subgroup.centralizer {dP} ⊓ Subgroup.centralizer {locZ},
      ∀ n ∈ locQ ⊓ Subgroup.centralizer {dP}, h * n * h⁻¹ ∈ locQ ⊓ Subgroup.centralizer {dP} := by
    intro h hh n hn
    obtain ⟨hhPd, hhz⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hhP, hhd⟩ := Subgroup.mem_inf.1 hhPd
    obtain ⟨hnQ, hnd⟩ := Subgroup.mem_inf.1 hn
    have hhC : h ∈ locC := by
      rw [locC_eq_centralizer]
      exact Subgroup.mem_inf.2 ⟨hhP, hhz⟩
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (locC_le_normalizer hhC) n).1 hnQ,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhd hnd) (Subgroup.inv_mem _ hhd)⟩
  have hKn : ∀ h ∈ co2P ⊓ Subgroup.centralizer {dP} ⊓ Subgroup.centralizer {locZ},
      ∀ k ∈ K0, h * k * h⁻¹ ∈ K0 := by
    intro h hh k hk
    obtain ⟨hhPd, hhz⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hhP, hhd⟩ := Subgroup.mem_inf.1 hhPd
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_K0 hhP
      (Subgroup.mem_centralizer_singleton_iff.1 hhd)
      (Subgroup.mem_centralizer_singleton_iff.1 hhz)) k).1 hk
  have hN2 : IsPGroup 2 ↥(locQ ⊓ Subgroup.centralizer {dP}) :=
    (IsPGroup.of_card (p := 2) (n := 9) (by rw [card_locQ]; norm_num)).to_le inf_le_left
  have hK2 : ¬ IsPGroup 2 ↥K0 := by
    intro h
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h
    rw [card_K0] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hcent := le_centralizer_of_normal_two_simple hNH hKH hNn hKn hN2 isSimpleGroup_K0 hK2
  have hgK := hcent (Subgroup.mem_inf.2 ⟨hgQ, Subgroup.mem_centralizer_singleton_iff.2 hgd.eq⟩)
  have hk1 : Commute g k1P :=
    (Subgroup.mem_centralizer_iff.1 hgK k1P (Subgroup.subset_closure (by simp))).symm
  have hk2 : Commute g k2P :=
    (Subgroup.mem_centralizer_iff.1 hgK k2P (Subgroup.subset_closure (by simp))).symm
  obtain ⟨i, j, hi, hj, rfl⟩ := (centralizer_facts g (locC_le_P (locQ_le_C hgQ)) hgd
    (commute_locZ_of_mem_locQ hgQ)).2 hk1 hk2
  have h512 : (dP ^ i * locZ ^ j) ^ 512 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard locQ hgQ
    rw [card_locQ] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · interval_cases j <;> simp
  · exact absurd h512 (pow512_ne_one i j hi0 hi hj)

private theorem mem_rowR0Of_iff (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) (g : ↥co2P) :
    g ∈ rowR0Of x (locQ.subgroupOf co2P) ↔ g = 1 ∨ g = ⟨locZ, locZ_mem_P⟩ := by
  constructor
  · intro hg
    obtain ⟨hgQ, hgx⟩ := Subgroup.mem_inf.1 hg
    have hgd : Commute (g : Equiv.Perm (Fin 2300)) dP := by
      rw [← hx]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hgx)
    rcases eq_one_or_locZ (Subgroup.mem_subgroupOf.1 hgQ) hgd with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 locZ_mem_Q,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩
      show locZ * (x : Equiv.Perm (Fin 2300)) = (x : Equiv.Perm (Fin 2300)) * locZ
      rw [hx]
      exact commute_facts.2.2.2.2.2.2.1.eq

private theorem rowR0Of_eq (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    rowR0Of x (locQ.subgroupOf co2P) = Subgroup.zpowers ⟨locZ, locZ_mem_P⟩ := by
  refine le_antisymm (fun g hg => ?_)
    (Subgroup.zpowers_le.2 ((mem_rowR0Of_iff x hx _).2 (Or.inr rfl)))
  rcases (mem_rowR0Of_iff x hx g).1 hg with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem row_K (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    rowKOf Row.co2.prime x (locQ.subgroupOf co2P) = K0.subgroupOf co2P := by
  rw [rowKOf, row_I x hx]
  refine glaPLayer_eq_K0 (le_inf (Subgroup.subgroupOf_mono _ K0_le_U0) fun k hk => ?_)
    fun g hg => ?_
  · exact Subgroup.mem_normalizer_iff.2 fun q => Subgroup.mem_normalizer_iff.1
      (locC_le_normalizer (K0_le_locC (Subgroup.mem_subgroupOf.1 hk))) q
  · obtain ⟨hgU, hgN⟩ := Subgroup.mem_inf.1 hg
    refine ⟨commute_dP_of_mem_U0 (Subgroup.mem_subgroupOf.1 hgU), commute_locZ_of_conj ?_ ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hgN ⟨locZ, locZ_mem_P⟩).1
        (Subgroup.mem_subgroupOf.2 locZ_mem_Q)
    · intro q hq
      exact (Subgroup.mem_normalizer_iff''.1 hgN ⟨q, locC_le_P (locQ_le_C hq)⟩).1
        (Subgroup.mem_subgroupOf.2 hq)

theorem row_hK (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    RowK .co2 Row.co2.prime (rowKOf Row.co2.prime x (locQ.subgroupOf co2P)) := by
  rw [row_K x hx]
  obtain ⟨e⟩ := nonempty_mulEquiv_K0'
  exact isTypeWithCenter_of_isSimple Nat.prime_three isSimpleGroup_K0' exists_ne_K0'
    (by rw [card_K0']; norm_num) (catalogIs_isA6 e)

theorem row_hR0 (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    Nat.card (rowR0Of x (locQ.subgroupOf co2P)) = 2 ^ Row.co2.r0exp := by
  rw [rowR0Of_eq x hx, Nat.card_zpowers]
  have h : orderOf (⟨locZ, locZ_mem_P⟩ : ↥co2P) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using locZ_sq)) fun h =>
      locZ_ne_one (congrArg Subtype.val h)
  rw [h]
  rfl

theorem row_hK6 (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    rowKOf Row.co2.prime x (locQ.subgroupOf co2P) =
      GLAPLayer Row.co2.prime (Subgroup.centralizer ({x} : Set ↥co2P) ⊓
        Subgroup.centralizer (centerOf (rowR0Of x (locQ.subgroupOf co2P)) : Set ↥co2P)) := by
  have hzR : (⟨locZ, locZ_mem_P⟩ : ↥co2P) ∈ rowR0Of x (locQ.subgroupOf co2P) :=
    (mem_rowR0Of_iff x hx _).2 (Or.inr rfl)
  have hzc : (⟨locZ, locZ_mem_P⟩ : ↥co2P) ∈ centerOf (rowR0Of x (locQ.subgroupOf co2P)) := by
    refine Subgroup.mem_map.2 ⟨⟨_, hzR⟩, Subgroup.mem_center_iff.2 fun h => Subtype.ext ?_, rfl⟩
    rcases (mem_rowR0Of_iff x hx h).1 h.2 with h1 | h1 <;>
      simp only [Subgroup.coe_mul, h1, one_mul, mul_one]
  rw [row_K x hx]
  refine (glaPLayer_eq_K0 (le_inf (fun k hk => ?_) (fun k hk => ?_)) fun g hg => ?_).symm
  · refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    show (k : Equiv.Perm (Fin 2300)) * (x : Equiv.Perm (Fin 2300)) =
      (x : Equiv.Perm (Fin 2300)) * (k : Equiv.Perm (Fin 2300))
    rw [hx]
    exact Subgroup.mem_centralizer_singleton_iff.1
      (K0_le_centralizer_dP (Subgroup.mem_subgroupOf.1 hk))
  · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rcases (mem_rowR0Of_iff x hx h).1
      (Subgroup.map_subtype_le (Subgroup.center ↥(rowR0Of x (locQ.subgroupOf co2P))) hh)
      with rfl | rfl
    · simp
    · refine Subtype.ext ?_
      show locZ * (k : Equiv.Perm (Fin 2300)) = (k : Equiv.Perm (Fin 2300)) * locZ
      exact (Subgroup.mem_centralizer_singleton_iff.1
        (K0_le_centralizer_locZ (Subgroup.mem_subgroupOf.1 hk))).symm
  · obtain ⟨hgx, hgc⟩ := Subgroup.mem_inf.1 hg
    refine ⟨?_, ?_⟩
    · rw [← hx]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hgx)
    · exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hgc _ hzc)).symm

end CFSG.Sporadic.Co2I301
