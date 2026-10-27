module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Bar
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.H13.S125KG.J4

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Fam
open CFSG.Quasithin.J4M3 CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.A312M24 (G24)
open scoped commutatorElement

@[expose] def xOrb (c : ℕ) : List ℕ := (List.range 7).map fun k => (actT (wordT xWord))^[k] c

theorem xOrb_check : v0Masks.all (fun c => c == 0 || v0Masks.all fun v => v == 0 ||
    (xOrb c).contains v) = true := by
  decide +kernel

theorem v0mask_mem : ∀ c : Fin 3 → ZMod 2, v0mask c ∈ v0Masks := by decide

theorem exists_mask_of_mem_V0
    {v : J} (hv : v ∈ V0) : ∃ m ∈ v0Masks, v = eta uJ 11 m := by
  rw [← eSub_v0, KGC31.mem_eSub_iff] at hv
  obtain ⟨c, rfl⟩ := hv
  exact ⟨v0mask c, v0mask_mem c, eElt_v0 c⟩

theorem card_V0
    : Nat.card ↥V0 = 8 := by
  rw [← eSub_v0, KGC31.card_eSub]
  rfl

theorem xM_mem_NV
    : xM ∈ J4Rad.NV := ⟨xM_mem_Hj, xM_mem_normalizer⟩

theorem eq_V0
    {E : Subgroup J} (hNE : J4Rad.NV ≤ Subgroup.normalizer (E : Set J))
    (hc : Nat.card E = 8) : E = V0 := by
  have hM := j4Facts.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : Qg ≤ J4Rad.NV := Q_le_KL.trans KL_le_NV
  obtain ⟨e, heE, he1, heC⟩ := exists_ne_one_mem_centralizer (IsPGroup.of_card card_Q)
    (hQN.trans hNE) (by rw [hc]; norm_num)
  have heV : e ∈ V0 := centralizer_pCoreOf_M3_le (by rw [pCoreOf_M3_eq]; exact heC)
  obtain ⟨c, hcm, rfl⟩ := exists_mask_of_mem_V0 heV
  have hc0 : c ≠ 0 := fun h => he1 (by rw [h, eta_zero])
  have hcl : c < 2 ^ 11 := by
    simp only [v0Masks, List.mem_cons, List.not_mem_nil, or_false] at hcm
    omega
  have hacts : Acts xM (wordT xWord) := Acts_wordProd hM xWord xWord_letters
  have hiter : ∀ k, (actT (wordT xWord))^[k] c < 2 ^ 11 ∧
      eta uJ 11 ((actT (wordT xWord))^[k] c) ∈ E := by
    intro k
    induction k with
    | zero => exact ⟨hcl, heE⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨actT_lt hacts.1 _, ?_⟩
      rw [← hacts.2 _ ih.1]
      exact (Subgroup.mem_normalizer_iff.mp (hNE xM_mem_NV) _).mp ih.2
  have hV0E : V0 ≤ E := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := exists_mask_of_mem_V0 hv
    by_cases hm0 : m = 0
    · rw [hm0, eta_zero]
      exact E.one_mem
    have h1 := xOrb_check
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h1
    rcases h1 c hcm with h | h
    · exact absurd h hc0
    rcases h m hm with h' | h'
    · exact absurd h' hm0
    obtain ⟨k, -, hk⟩ := List.mem_map.mp h'
    rw [← hk]
    exact (hiter k).2
  exact (Subgroup.eq_of_le_of_card_ge hV0E (by rw [hc, card_V0])).symm

theorem M3_le_normalizer_C :
    M3 ≤ Subgroup.normalizer (Subgroup.centralizer (V0 : Set J) : Set J) := by
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun c hc => ?_
  have hc' : c ∈ Subgroup.centralizer (V0 : Set J) := hc
  show m * c * m⁻¹ ∈ Subgroup.centralizer (V0 : Set J)
  rw [Subgroup.mem_centralizer_iff] at hc' ⊢
  intro v hv
  have hv' : m⁻¹ * v * m ∈ V0 := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) v).mp hv
    simpa using this
  have h1 := hc' _ hv'
  calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
    _ = m * c * m⁻¹ * v := by group

theorem commutator_le_Q
    : ⁅Subgroup.centralizer (V0 : Set J), KL⁆ ≤ Qg := by
  rw [Subgroup.commutator_le]
  intro c hc k hk
  have hcM : c ∈ M3 := D_le_M3 hc
  have hkM : k ∈ M3 := KL_le_M3 hk
  have h1 : ⁅c, k⁆ ∈ Subgroup.centralizer (V0 : Set J) := by
    rw [commutatorElement_def]
    have : k * c⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V0 : Set J) :=
      (Subgroup.mem_normalizer_iff.mp (M3_le_normalizer_C hkM) _).mp (Subgroup.inv_mem _ hc)
    have h2 := Subgroup.mul_mem _ hc this
    simpa [mul_assoc] using h2
  have h2 : ⁅c, k⁆ ∈ KL := by
    rw [commutatorElement_def]
    have : c * k * c⁻¹ ∈ KL := (Subgroup.mem_normalizer_iff.mp (M3_le_normalizer_KL hcM) _).mp hk
    exact KL.mul_mem this (KL.inv_mem hk)
  rw [← K3_eq_Q, ← KL_inf_centralizer_eq_K3]
  exact ⟨h2, h1⟩

theorem perfectResidual_NV_le_KL
    : CFSG.inSubgroup CFSG.perfectResidual J4Rad.NV ≤ KL := by
  have hF : J4Facts := j4Facts
  set Ñ := J4Rad.NV.subgroupOf M3 with hÑ
  have hNM : J4Rad.NV ≤ M3 := inf_le_right
  have hcard : Nat.card ↥(Ñ.map (rho3 hF)) ∣ 24 := by
    have e1 : Nat.card ↥Ñ = 2 ^ 21 * 63 := by
      rw [hÑ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, card_NV]
    have h1 : Nat.card ↥(Ñ.map (rho3 hF)) ∣ 2 ^ 21 * 63 := e1 ▸ Subgroup.card_map_dvd Ñ _
    have h2 : Nat.card ↥(Ñ.map (rho3 hF)) ∣ 120 := by
      have := Subgroup.card_subgroup_dvd_card (Ñ.map (rho3 hF))
      rwa [Nat.card_perm, Nat.card_fin] at this
    have := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd (2 ^ 21 * 63) 120 = 24 by norm_num] at this
  have hsolv : Group.IsSolvable ↥(Ñ.map (rho3 hF)) := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have h24 : (Nat.card ↥(Ñ.map (rho3 hF))).primeFactors ⊆ {2, 3} := by
      refine (Nat.primeFactors_mono hcard (by norm_num)).trans ?_
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      rfl
    exact (Finset.card_le_card h24).trans (by decide)
  have hbot : (CFSG.inSubgroup CFSG.perfectResidual Ñ).map (rho3 hF) = ⊥ := by
    rw [map_inSubgroup_perfectResidual, CFSG.inSubgroup,
      (CFSG.perfect_residual_characterization (G := ↥(Ñ.map (rho3 hF)))).2.2.2.2.2.mpr hsolv,
      Subgroup.map_bot]
  have hmap := map_inSubgroup_perfectResidual M3.subtype Ñ
  rw [Subgroup.map_subgroupOf_eq_of_le hNM] at hmap
  rw [← hmap]
  rintro _ ⟨y, hy, rfl⟩
  have h1 : rho3 hF y = 1 := by
    have : rho3 hF y ∈ (CFSG.inSubgroup CFSG.perfectResidual Ñ).map (rho3 hF) := ⟨y, hy, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  exact (rho3_eq_one_iff y).mp h1

theorem mem_sup_of_odd
    {x : J} (hx : x ∈ Subgroup.centralizer (V0 : Set J))
    (hodd : Odd (orderOf x)) :
    x ∈ CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (V0 : Set J)) ⊔ Qg := by
  have hF : J4Facts := j4Facts
  set x' : ↥M3 := ⟨x, D_le_M3 hx⟩ with hx'
  have hxD : x' ∈ Dm := hx
  have hrange : Dm.map (rho3 hF) = ⊤ := by
    have h1 := Subgroup.card_mul_index ((rho3 hF).comp Dm.subtype).ker
    rw [Subgroup.index_ker, card_ker_rho3_Dm, card_Dm hF] at h1
    have h2 : Nat.card ↥((rho3 hF).comp Dm.subtype).range = 120 := by omega
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h2
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [h2, Nat.card_perm, Nat.card_fin]
    rfl
  have hsign : Equiv.Perm.sign (rho3 hF x') = 1 := by
    have h1 : Odd (orderOf (rho3 hF x')) :=
      Odd.of_dvd_nat (by rw [Subgroup.orderOf_mk]; exact hodd) (orderOf_map_dvd _ x')
    obtain ⟨n, hn⟩ := h1
    have h2 : Equiv.Perm.sign (rho3 hF x') ^ orderOf (rho3 hF x') = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hn, pow_succ, pow_mul] at h2
    rcases Int.units_eq_one_or (Equiv.Perm.sign (rho3 hF x')) with h | h
    · exact h
    · rw [h] at h2
      simp at h2
  have hA : rho3 hF x' ∈ (CFSG.inSubgroup CFSG.perfectResidual Dm).map (rho3 hF) := by
    rw [map_inSubgroup_perfectResidual, hrange]
    have hAle : alternatingGroup (Fin 5) ≤
        CFSG.inSubgroup CFSG.perfectResidual (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
      le_inSubgroup_perfectResidual_of_le le_top
        (commutator_alternatingGroup_eq_self (by rw [Nat.card_fin])).ge
    exact hAle (Equiv.Perm.mem_alternatingGroup.mpr hsign)
  obtain ⟨z, hz, hzx⟩ := hA
  have hzD : z ∈ Dm := Subgroup.map_subtype_le _ hz
  have hk : ((z⁻¹ * x' : ↥M3) : J) ∈ KL ⊓ Subgroup.centralizer (V0 : Set J) := by
    refine ⟨(rho3_eq_one_iff _).mp (by rw [map_mul, map_inv, hzx, inv_mul_cancel]), ?_⟩
    exact Subgroup.mul_mem Dm (Subgroup.inv_mem Dm hzD) hxD
  rw [KL_inf_centralizer_eq_K3, K3_eq_Q] at hk
  have hmap := map_inSubgroup_perfectResidual M3.subtype Dm
  rw [Subgroup.map_subgroupOf_eq_of_le D_le_M3] at hmap
  have hz' : (z : J) ∈
      CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (V0 : Set J)) := by
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  have e : x = (z : J) * ((z⁻¹ * x' : ↥M3) : J) := by simp [hx']
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz') (Subgroup.mem_sup_right hk)

theorem exists_mul_of_mem_sup {A B : Subgroup J} (hB : B ≤ Subgroup.normalizer (A : Set J))
    {x : J} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ ((A ⊔ B : Subgroup J) : Set J) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem P0_le_normalizer_CV
    : P0 ≤ Subgroup.normalizer (J4Rad.CV : Set J) := by
  intro p hp
  have hpN : p ∈ J4Rad.NV := H13.KGT3J4.P0_le_NV hp
  refine Subgroup.mem_normalizer_fintype fun c hc => ?_
  obtain ⟨hcH, hcC⟩ := hc
  exact ⟨Hj.mul_mem (Hj.mul_mem hpN.1 hcH) (Hj.inv_mem hpN.1),
    (Subgroup.mem_normalizer_iff.mp (M3_le_normalizer_C hpN.2) c).mp hcC⟩

theorem card_CV_sup_P0
    : Nat.card ↥(J4Rad.CV ⊔ P0) = 3 * 2 ^ 21 := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    P0_le_normalizer_CV
  rw [J4Rad.card_CV hF, card_P0 hM hF] at h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((IsPGroup.of_card (card_P0 hM hF)).to_le
    (inf_le_right : J4Rad.CV ⊓ P0 ≤ P0))
  have hle : J4Rad.CV ⊔ P0 ≤ J4Rad.NV :=
    sup_le (fun _ hc => ⟨hc.1, D_le_M3 hc.2⟩) H13.KGT3J4.P0_le_NV
  obtain ⟨i, hi⟩ := Subgroup.card_dvd_of_le (le_sup_right : P0 ≤ J4Rad.CV ⊔ P0)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [card_NV, hi, card_P0 hM hF] at hdvd
  have hi63 : i ∣ 63 := Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd
  rw [hi, card_P0 hM hF, hk] at h1
  have hik : i * 2 ^ k = 3 * 2 ^ 18 := by
    have : 2 ^ 21 * (i * 2 ^ k) = 2 ^ 21 * (3 * 2 ^ 18) := by rw [← mul_assoc, h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hodd : Odd i := Odd.of_dvd_nat (by decide) hi63
  have hi3 : i ∣ 3 := by
    have h2 : i ∣ 3 * 2 ^ 18 := ⟨2 ^ k, hik.symm⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_right 18 (Nat.coprime_two_right.mpr hodd)) h2)
  have h3i : 3 ∣ i := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hi3 with h | h
    · exfalso
      subst h
      have : 2 ^ k = 2 ^ 18 * 3 := by omega
      have h3 : 3 ∣ 2 ^ k := ⟨2 ^ 18, by rw [this]; ring⟩
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    · rw [h]
  have : i = 3 := Nat.dvd_antisymm hi3 h3i
  rw [hi, card_P0 hM hF, this]
  ring

theorem CV_sup_P0_not_le
    :
    ¬ J4Rad.CV ⊔ P0 ≤ CFSG.inSubgroup CFSG.perfectResidual J4Rad.NV ⊔ P0 := by
  have hF : J4Facts := j4Facts
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J4Rad.CV) 3
    (by rw [J4Rad.card_CV hF]; norm_num)
  have hyKP : (y : J) ∈ KL ⊔ P0 :=
    (sup_le_sup_right perfectResidual_NV_le_KL _) (h (Subgroup.mem_sup_left y.2))
  have hPKL : P0 ≤ Subgroup.normalizer (KL : Set J) := P0_le_M3.trans M3_le_normalizer_KL
  obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup hPKL hyKP
  have hyM : (y : J) ∈ M3 := D_le_M3 y.2.2
  have hpM : p ∈ M3 := P0_le_M3 hp
  have hkM : k ∈ M3 := KL_le_M3 hk
  have hr : rho3 hF ⟨y, hyM⟩ = rho3 hF ⟨p, hpM⟩ := by
    have e : (⟨y, hyM⟩ : ↥M3) = ⟨k, hkM⟩ * ⟨p, hpM⟩ := Subtype.ext hkp
    rw [e, map_mul, (rho3_eq_one_iff ⟨k, hkM⟩).mpr hk, one_mul]
  have hy3 : orderOf (rho3 hF ⟨y, hyM⟩) ∣ 3 := by
    have ho : orderOf (⟨y, hyM⟩ : ↥M3) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy]
    exact ho ▸ orderOf_map_dvd _ _
  obtain ⟨n, hn⟩ := (IsPGroup.of_card (card_P0 j4Facts.mat hF)) ⟨p, hp⟩
  have hp2 : orderOf (rho3 hF ⟨p, hpM⟩) ∣ 2 ^ n := by
    refine (orderOf_map_dvd _ _).trans ?_
    refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
    simpa using congrArg Subtype.val hn
  rw [← hr] at hp2
  have h1 : orderOf (rho3 hF ⟨y, hyM⟩) = 1 := by
    have h2 := Nat.dvd_gcd hy3 hp2
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num)), Nat.dvd_one] at h2
  rw [orderOf_eq_one_iff] at h1
  have hyK : (y : J) ∈ KL ⊓ Subgroup.centralizer (V0 : Set J) :=
    ⟨(rho3_eq_one_iff ⟨y, hyM⟩).mp h1, y.2.2⟩
  rw [KL_inf_centralizer_eq_K3, K3_eq_Q] at hyK
  obtain ⟨m, hm⟩ := (IsPGroup.of_card card_Q) ⟨y, hyK⟩
  have h3 : orderOf (y : J) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hm)
  rw [Subgroup.orderOf_coe, hy] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem D_eq
    {D : Subgroup J} (hc : Config63 P0 J4Rad.NV D) : D = J4Rad.CV ⊔ P0 := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have hNH : J4Rad.NV ≤ Hj := inf_le_left
  have hc2 : Config63 P0 J4Rad.NV (J4Rad.CV ⊔ P0) :=
    ⟨le_sup_right, sup_le (fun _ hc => ⟨hc.1, D_le_M3 hc.2⟩) H13.KGT3J4.P0_le_NV,
      by rw [card_NV, card_P0 hM hF]; ring, by rw [card_CV_sup_P0, card_P0 hM hF],
      CV_sup_P0_not_le⟩
  obtain ⟨ψ, hψ⟩ := M24.exists_equiv ⟨MulEquiv.refl G24⟩ isSylowTwoOf_bar_P0
  have h1 := M24.map_D ψ hψ (config63_bar hc hNH)
  have h2 := M24.map_D ψ hψ (config63_bar hc2 hNH)
  have hb : bar D = bar (J4Rad.CV ⊔ P0) :=
    Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (h1.trans h2.symm)
  have hE : Eg uJ 11 ≤ P0 := Eg_le_P0
  exact le_antisymm ((bar_le_iff (hE.trans le_sup_right) (hc.2.1.trans hNH)).mp hb.le)
    ((bar_le_iff (hE.trans hc.1) (hc2.2.1.trans hNH)).mp hb.ge)

theorem oTwoUpper_le_CV
    : oTwoUpper (J4Rad.CV ⊔ P0) ≤ J4Rad.CV := by
  have hM := j4Facts.mat
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, hodd⟩
  obtain ⟨c, hc, p, hp, rfl⟩ := exists_mul_of_mem_sup P0_le_normalizer_CV hx
  obtain ⟨n, hn⟩ := (IsPGroup.of_card (card_P0 hM j4Facts)) ⟨p, hp⟩
  have hpn : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have key : ∀ m : ℕ, ∃ c' ∈ J4Rad.CV, (c * p) ^ m = c' * p ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, J4Rad.CV.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨c', hc', he⟩ := ih
      refine ⟨c' * (p ^ m * c * (p ^ m)⁻¹), J4Rad.CV.mul_mem hc' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (P0_le_normalizer_CV hp) m)
          c).mp hc
      · rw [pow_succ, he, pow_succ]
        group
  obtain ⟨c', hc', he⟩ := key (2 ^ n)
  rw [hpn, mul_one] at he
  set m := orderOf (c * p) with hm
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have e : c * p = ((c * p) ^ 2 ^ n) ^ k := by
      rw [← pow_mul, ← pow_mod_orderOf, ← hm, hk, pow_one]
    rw [SetLike.mem_coe, e, he]
    exact J4Rad.CV.pow_mem hc' k
  · have hm1 : m = 1 := le_antisymm h1 (orderOf_pos (c * p))
    have e : c * p = 1 := by rw [← orderOf_eq_one_iff, ← hm, hm1]
    rw [SetLike.mem_coe, e]
    exact J4Rad.CV.one_mem

theorem beta_J
    {N D E : Subgroup J} (hc : Config63 P0 N D) (hEO : E ≤ pCoreOf 2 N)
    (hNE : N ≤ Subgroup.normalizer (E : Set J)) (hE : Nat.card E = 8) :
    ⁅CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set J)),
        CFSG.inSubgroup CFSG.perfectResidual N⁆ ≤
        pCoreOf 2 (Subgroup.normalizer (E : Set J)) ∧
      oTwoUpper D ≤ CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set J)) ⊔
        pCoreOf 2 (Subgroup.normalizer (E : Set J)) := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have hNV : N = J4Rad.NV := N_eq_NV (hc.1.trans hc.2.1) (by rw [hc.2.2.1, card_P0 hM hF]; ring)
  subst hNV
  have hEV : E = V0 := eq_V0 hNE hE
  subst hEV
  rw [show Subgroup.normalizer (V0 : Set J) = M3 from rfl, pCoreOf_M3_eq]
  refine ⟨(Subgroup.commutator_mono (Subgroup.map_subtype_le _)
    perfectResidual_NV_le_KL).trans commutator_le_Q, ?_⟩
  rw [D_eq hc, oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxD, hodd⟩
  exact mem_sup_of_odd (oTwoUpper_le_CV (mem_oTwoUpper_of_odd hxD hodd)).2 hodd

theorem kg125BetaJ4
    : KG125BetaJ4 := by
  intro X _ _ hX S N D E hS hc hEO hNE hE
  obtain ⟨e⟩ := hX
  exact beta_of_sylow isSylowTwoOf_P0 (fun N D E hc hEO hNE hE => beta_J hc hEO hNE hE)
    ⟨e.trans (seedEquiv j4Facts.mat)⟩ hS hc hEO hNE hE

end CFSG.Quasithin.H13.S125KG.J4
