module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SA6
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SBTwo
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SBRank
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SCop
import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section KP4


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}

theorem isSolvable_V (h : Cfg A c L R S J) :
    Group.IsSolvable ↥(J ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G))) ∧
      ¬ 3 ∣ Nat.card ↥(J ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G))) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  obtain ⟨hJM, hJ'⟩ := mem_thetaComponentsIn_iff.mp h.J_mem
  have h3' : 3 ∣ Nat.card (J.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv]
    exact h.three_dvd_card_J
  have heq := Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents hJ' h3'
  have hV : J ⊓ pPrimeCoreOf 3 M =
      (inSubgroup (aschbacherSolvableCore 3) (J.subgroupOf M)).map M.subtype := by
    rw [← heq, Subgroup.map_inf_eq _ _ _ M.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hJM]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hV]
    have hθ : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥(J.subgroupOf M)) :=
      (solvable_prime_complement_core_characterization (H := ↥(J.subgroupOf M))
        Nat.prime_three).1
    have h1 : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) (J.subgroupOf M)) :=
      Group.isSolvable_of_surjective
        (f := ((aschbacherSolvableCore 3 ↥(J.subgroupOf M)).equivMapOfInjective _
          (J.subgroupOf M).subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective
      (f := ((inSubgroup (aschbacherSolvableCore 3) (J.subgroupOf M)).equivMapOfInjective _
        M.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  · intro h3
    have h1 : Nat.card ↥(J ⊓ pPrimeCoreOf 3 M) ∣ Nat.card ↥(pPrimeCoreOf 3 M) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)
      (h3.trans h1)

theorem card_le_sq_of_le_M (h : Cfg A c L R S J) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {E : Subgroup G} (hEM : E ≤ Subgroup.normalizer (S : Set G))
    (hE : CFSG.Assembly.IsElemAbelian r E) : Nat.card E ≤ r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have hE2 : IsPGroup r E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hk1 : k ≤ CFSG.Open.pRank r (Subgroup.normalizer (S : Set G)) :=
    CFSG.SectionRank.le_pRank hr.one_lt hEM hE hk
  have hk2 := CFSG.RankThree.Classical.pRank_le_localRank hr.one_lt h.isTwoLocal_M
  have hk3 := h.pt.std.toTheoremFourHyp.localRank_lt r hr (by omega)
  rw [hk]
  exact Nat.pow_le_pow_right hr.pos (by omega)

theorem pPrimeCoreOf_le_normalizer_J (h : Cfg A c L R S J) :
    pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) ≤ Subgroup.normalizer (J : Set G) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  obtain ⟨hJM, hJ'⟩ := mem_thetaComponentsIn_iff.mp h.J_mem
  set J' := J.subgroupOf M with hJ'def
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) with hπ
  have hcomp : IsComponent (J'.map π) := isComponent_map_of_mem_thetaComponents Nat.prime_three hJ'
  set U := (CFSG.pPrimeCore 3 ↥M).map π with hU
  have hUn : U.Normal :=
    (CFSG.pPrimeCore_normal (p := 3) (G := ↥M)).map π (QuotientGroup.mk'_surjective _)
  have h3J' : 3 ∣ Nat.card J' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv]
    exact h.three_dvd_card_J
  have h3π : 3 ∣ Nat.card (J'.map π) := by
    obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hJ'.2.1
    rw [← Nat.card_congr η.toEquiv]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (aschbacherSolvableCore 3 ↥J')
    have h2 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥J') :=
      (solvable_prime_complement_core_characterization (H := ↥J') Nat.prime_three).2.2.1
    rw [h1] at h3J'
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp h3J' |>.resolve_right h2
  have hcomm : ⁅J'.map π, U⁆ = ⊥ := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hUn.isSubnormal with hle | hc
    · exfalso
      have h1 : Nat.card (J'.map π) ∣ Nat.card (CFSG.pPrimeCore 3 ↥M) :=
        (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _)
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M)) (h3π.trans h1)
    · exact hc
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hy
  set σ : ↥M ≃* ↥M := MulAut.conj y' with hσ
  have hσJ := map_mulEquiv_mem_thetaComponents Nat.prime_three σ hJ'
  have hπy : ∀ x ∈ J'.map π, π y' * x = x * π y' := by
    intro x hx
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact Subgroup.mem_centralizer_iff.mp this (π y') ⟨y', hy', rfl⟩
  have hmapeq : (J'.map σ.toMonoidHom).map π = J'.map π := by
    ext x
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : π j ∈ J'.map π := ⟨j, hj, rfl⟩
      have : π (σ j) = π j := by
        change π (y' * j * y'⁻¹) = π j
        rw [map_mul, map_mul, map_inv, hπy _ hj', mul_inv_cancel_right]
      rw [MulEquiv.coe_toMonoidHom, this]
      exact hj'
    · rintro ⟨j, hj, rfl⟩
      refine ⟨σ j, ⟨j, hj, rfl⟩, ?_⟩
      change π (y' * j * y'⁻¹) = π j
      rw [map_mul, map_mul, map_inv, hπy _ ⟨j, hj, rfl⟩, mul_inv_cancel_right]
  have heq : J'.map σ.toMonoidHom = J' :=
    (theta_component_quotient_correspondence Nat.prime_three).1.injOn hσJ hJ' hmapeq
  apply Subgroup.mem_normalizer_fintype
  intro j hj
  have hjJ' : (⟨j, hJM hj⟩ : ↥M) ∈ J' := Subgroup.mem_subgroupOf.mpr hj
  have hmem : σ ⟨j, hJM hj⟩ ∈ J' := heq ▸ ⟨_, hjJ', rfl⟩
  exact Subgroup.mem_subgroupOf.mp hmem

variable [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem isPGroup_two_V (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6)) :
    IsPGroup 2 ↥(J ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G))) := by
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, f, hf, hker⟩ := h.pt.K_kp4 h.R_mem
  obtain ⟨hRe, -, ⟨d, e, hdB, heB, hde⟩, -⟩ := h.pt.R_kp4 h.R_mem
  obtain ⟨hRL, hR2, hAR, -⟩ := h.pt.R_facts h.R_mem
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRe.1.is_comm.comm (⟨x, hx⟩ : ↥R) ⟨y, hy⟩)
  have hBK : A ⊓ L ≤ K := B_le_K hAR
  have hKp : Group.IsPerfect K := isPerfect_of_quot (R_le_K hRL) f hf hker hRc hR2 (hBK hdB)
    (hBK heB) (hA3 d hdB.1) (hA3 e heB.1) (hAc d hdB.1 e heB.1) (hAR hdB.1) (hAR heB.1) hde
  have hJp := isPerfect_of_mem_thetaComponentsIn h.J_mem
  obtain ⟨hVs, hV3⟩ := h.isSolvable_V
  have hJKV : J ≤ K ⊔ (J ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G))) := by
    intro j hj
    have hjM : j ∈ Subgroup.normalizer (S : Set G) ⊔ A := Subgroup.mem_sup_left (h.J_le_M hj)
    have hjJ : QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) ⟨j, hjM⟩ ∈
        img148 A (Subgroup.normalizer (S : Set G)) K := by
      rw [h.K_bar_eq ψ]
      exact mem_img148_iff.mpr ⟨j, hjM, hj, rfl⟩
    obtain ⟨k, hkM, hkK, hkj⟩ := mem_img148_iff.mp hjJ
    have hkj' := mk'_ker148_eq_iff.mp hkj
    have hkJ : k ∈ J := h.K_le hkK
    have hmem : k⁻¹ * j ∈ J ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) :=
      ⟨J.mul_mem (J.inv_mem hkJ) hj, hkj'⟩
    have : j = k * (k⁻¹ * j) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hkK hmem
  have hKV : K ≤ Subgroup.normalizer
      ((J ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (h.K_le.trans Subgroup.le_normalizer)
      (h.K_le_M.trans (le_normalizer_pPrimeCoreOf 3 _))
  obtain ⟨hh, hhK, hinv⟩ := exists_inverting_of_A6 hA6 (R_le_K hRL) f hf hker hR2 hBK
    h.pt.card_B (fun a ha b hb => hAc a ha.1 b hb.1)
  exact isPGroup_two_of_A6_ext
    (fun Q _ _ r hr hr5 hQ hrank E hEc hE3 hE9 g hg =>
      false_of_inverted_E9_of_rank_two hr hr5 hQ hrank E hEc hE3 hE9 g hg)
    h.K_le inf_le_left hKV hJKV hJp hVs hV3
    (fun r hr hr5 E hEV hE => h.card_le_sq_of_le_M hr hr5
      (hEV.trans (inf_le_left.trans h.J_le_M)) hE)
    (R_le_K hRL) hR2 hKp f hf hker hBK h.pt.card_B (fun a ha b hb => hAc a ha.1 b hb.1)
    (fun b hb => hA3 b hb.1) hhK hinv


omit [Finite G] in
theorem mem_normalizer_sup1422 {X Y : Subgroup G} {a : G}
    (hX : a ∈ Subgroup.normalizer (X : Set G)) (hY : a ∈ Subgroup.normalizer (Y : Set G)) :
    a ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  apply CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer1422 hX, map_conj_eq_of_mem_normalizer1422 hY]

theorem K_le_normalizer_T (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6))
    {T : Subgroup G} (hTM : T ≤ Subgroup.normalizer (S : Set G)) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hTmax : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → IsPGroup 2 U →
      A ≤ Subgroup.normalizer (U : Set G) → T ≤ U → U ≤ T) :
    L ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set O := pPrimeCoreOf 3 M with hO
  set V := J ⊓ O with hV
  have hTO := h.le_pPrimeCoreOf_of_two hA6 ψ hTM hT2 hAT
  have hV2 := h.isPGroup_two_V hA6 ψ
  have hON : O ≤ Subgroup.normalizer (J : Set G) := h.pPrimeCoreOf_le_normalizer_J
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 M
  have hTV : T ≤ Subgroup.normalizer (V : Set G) :=
    Late.le_normalizer_inf (hTO.trans hON) (hTM.trans hMO)
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    Late.le_normalizer_inf h.A_le (h.A_le_M.trans hMO)
  have hTV2 : IsPGroup 2 (T ⊔ V : Subgroup G) := IsPGroup.to_sup_of_normal_right' hT2 hV2 hTV
  have hVT : V ≤ T := by
    have := hTmax (T ⊔ V) (sup_le hTM (inf_le_left.trans h.J_le_M)) hTV2
      (fun a ha => mem_normalizer_sup1422 (hAT ha) (hAV ha)) le_sup_left
    exact le_sup_right.trans this
  intro k hk
  apply Subgroup.mem_normalizer_fintype
  intro t ht
  have hkJ : k ∈ J := h.K_le hk
  have hkM : k ∈ M := h.K_le_M hk
  have hx : t⁻¹ * k * t * k⁻¹ ∈ V := by
    refine ⟨?_, ?_⟩
    · have h1 : t⁻¹ * k * t⁻¹⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hON (O.inv_mem (hTO ht))) k).mp hkJ
      rw [inv_inv] at h1
      exact J.mul_mem h1 (J.inv_mem hkJ)
    · have h1 : k * t * k⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hMO hkM) t).mp (hTO ht)
      have h2 : t⁻¹ * (k * t * k⁻¹) ∈ O := O.mul_mem (O.inv_mem (hTO ht)) h1
      simpa [mul_assoc] using h2
  have h1 : k * t * k⁻¹ = t * (t⁻¹ * k * t * k⁻¹) := by group
  rw [h1]
  exact T.mul_mem ht (hVT hx)

theorem cond3_T (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6))
    {T : Subgroup G} (hTM : T ≤ Subgroup.normalizer (S : Set G)) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hTmax : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → IsPGroup 2 U →
      A ≤ Subgroup.normalizer (U : Set G) → T ≤ U → U ≤ T) :
    ∀ u ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ⊓
        Subgroup.normalizer (R : Set G),
      ∃ v ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ⊓
          Subgroup.normalizer (T : Set G),
        ∀ a ∈ A, u * a * u⁻¹ = v * a * v⁻¹ := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set O := pPrimeCoreOf 3 M with hO
  have hA : IsE27 A := h.pt.std.isE27
  have hA3' : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2)⟩
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 M
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := h.A_le_M.trans hMO
  have hTO := h.le_pPrimeCoreOf_of_two hA6 ψ hTM hT2 hAT
  obtain ⟨P, hTP, hPO, hAP, hP2, hPs⟩ :=
    exists_invariant_sylow_two_of_coprime hA3' hO3 hAO hTO hT2 hAT
  have hPT : P = T :=
    le_antisymm (hTmax P (hPO.trans (pPrimeCoreOf_le 3 M)) hP2 hAP hTP) hTP
  subst hPT
  intro u hu
  obtain ⟨v₀, hv₀, hact⟩ := h.S_mem.2.2.2 u hu
  obtain ⟨⟨hv₀c, hv₀A⟩, hv₀S⟩ := hv₀
  set T' := P.map (MulAut.conj v₀).toMonoidHom with hT'
  have hT'O : T' ≤ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMO hv₀S) t).mp (hPO ht)
  have hT'2 : IsPGroup 2 T' := hP2.map _
  have hAT' : A ≤ Subgroup.normalizer (T' : Set G) := by
    intro a ha
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨t, ht, rfl⟩
    have ha' : v₀⁻¹ * a * v₀ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hv₀A) a).mp ha
      simpa [mul_assoc] using this
    have ht' : (v₀⁻¹ * a * v₀) * t * (v₀⁻¹ * a * v₀)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hAP ha') t).mp ht
    refine ⟨_, ht', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcardT' : Nat.card T' = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj v₀).injective
  have hT's : ¬ 2 ∣ (T'.subgroupOf O).index := by
    have h1 := (T'.subgroupOf O).index_mul_card
    have h2 := (P.subgroupOf O).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'O).toEquiv, hcardT'] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPO).toEquiv] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : (T'.subgroupOf O).index = (P.subgroupOf O).index :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    rw [this]
    exact hPs
  obtain ⟨y, ⟨hyO, hyA⟩, hyT⟩ :=
    exists_conj_of_invariant_sylow_two hA3' hO3 hAO hPO hT'O hP2 hT'2 hPs hT's hAP hAT'
  have hyc : ∀ a ∈ A, a * y = y * a := fun a ha => Subgroup.mem_centralizer_iff.mp hyA a ha
  refine ⟨y⁻¹ * v₀, ⟨⟨?_, ?_⟩, ?_⟩, fun a ha => ?_⟩
  · apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : v₀ * c ^ k * v₀⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hv₀c _).mp (zpow_mem (Subgroup.mem_zpowers c) k)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hcj : y * c ^ j = c ^ j * y := (hyc _ (A.zpow_mem h.pt.mem_A j)).symm
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    calc c ^ j = y⁻¹ * (c ^ j) * y := by rw [mul_assoc, ← hcj]; group
      _ = y⁻¹ * v₀ * c ^ k * (y⁻¹ * v₀)⁻¹ := by rw [hj]; group
  · have hy' : y⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      inv_mem (Subgroup.centralizer_le_normalizer (A : Set G) hyA)
    exact mul_mem hy' hv₀A
  · apply Subgroup.mem_normalizer_fintype
    intro x hx
    have h1 : v₀ * x * v₀⁻¹ ∈ T' := ⟨x, hx, rfl⟩
    rw [hyT] at h1
    obtain ⟨p, hp, hpx⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hpx
    have : y⁻¹ * v₀ * x * (y⁻¹ * v₀)⁻¹ = p := by
      calc y⁻¹ * v₀ * x * (y⁻¹ * v₀)⁻¹ = y⁻¹ * (v₀ * x * v₀⁻¹) * y := by group
        _ = y⁻¹ * (y * p * y⁻¹) * y := by rw [hpx]
        _ = p := by group
    rw [this]
    exact hp
  · have hva : v₀ * a * v₀⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hv₀A a).mp ha
    rw [hact a ha]
    calc v₀ * a * v₀⁻¹ = y⁻¹ * (y * (v₀ * a * v₀⁻¹)) := by group
      _ = y⁻¹ * ((v₀ * a * v₀⁻¹) * y) := by rw [hyc _ hva]
      _ = y⁻¹ * v₀ * a * (y⁻¹ * v₀)⁻¹ := by group

theorem mem_star (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6))
    (hSmax : ∀ S' ∈ fam A c R (L ⊓ Subgroup.normalizer (R : Set G)), S ≤ S' → S' ≤ S) :
    S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  refine ⟨h.S_mem.1, fun S' hS' hSS' => ?_⟩
  by_contra hS'S
  have hS'2 : IsPGroup 2 S' := (isPiSubgroup_piOf_iff Nat.prime_two S').mp hS'.2
  have hAS' : A ≤ Subgroup.normalizer (S' : Set G) := hS'.1.1.1.2.2
  obtain ⟨x, hxS', hxM, hxS⟩ : ∃ x ∈ S', x ∈ M ∧ x ∉ S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥S' := hS'2.isNilpotent
    have hlt : S.subgroupOf S' < ⊤ := by
      refine lt_of_le_of_ne le_top fun htop => hS'S fun y hy => ?_
      have : (⟨y, hy⟩ : ↥S') ∈ S.subgroupOf S' := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨z, hzN, hzS⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
    refine ⟨z, z.2, ?_, fun h1 => hzS (Subgroup.mem_subgroupOf.mpr h1)⟩
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have hsS' : s ∈ S' := hSS' hs
      have := (Subgroup.mem_normalizer_iff.mp hzN ⟨s, hsS'⟩).mp (Subgroup.mem_subgroupOf.mpr hs)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hs
      have hsS' : s ∈ S' := by
        have := S'.mul_mem (S'.mul_mem (S'.inv_mem z.2) (hSS' hs)) z.2
        simpa [mul_assoc] using this
      have := (Subgroup.mem_normalizer_iff.mp hzN ⟨s, hsS'⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hs)
      simpa [Subgroup.mem_subgroupOf] using this
  set D := S' ⊓ M with hD
  have hDp : D ≤ M ∧ IsPGroup 2 D ∧ A ≤ Subgroup.normalizer (D : Set G) :=
    ⟨inf_le_right, hS'2.to_le inf_le_left, Late.le_normalizer_inf hAS' h.A_le_NM⟩
  obtain ⟨T, hDT, hTmax⟩ := Finite.exists_le_maximal (α := Subgroup G)
    (p := fun U => U ≤ M ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G)) hDp
  obtain ⟨hTM, hT2, hAT⟩ := hTmax.1
  have hTmax' : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U →
      A ≤ Subgroup.normalizer (U : Set G) → T ≤ U → U ≤ T :=
    fun U hUM hU2 hAU hTU => hTmax.2 ⟨hUM, hU2, hAU⟩ hTU
  have hST : S ≤ T := (le_inf hSS' Subgroup.le_normalizer).trans hDT
  have hTfam : T ∈ fam A c R (L ⊓ Subgroup.normalizer (R : Set G)) :=
    ⟨⟨⟨h.pt.iq T hT2 hAT, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2⟩,
      h.R_le_S.trans hST, h.K_le_normalizer_T hA6 ψ hTM hT2 hAT hTmax',
      h.cond3_T hA6 ψ hTM hT2 hAT hTmax'⟩
  exact hxS (hSmax T hTfam hST (hDT ⟨hxS', hxM⟩))

theorem normalizer_inf_le (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6)) :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  have hA : IsE27 A := h.pt.std.isE27
  intro w ⟨hwM, hwA⟩
  have hw : w ∈ M ⊔ A := Subgroup.mem_sup_left hwM
  set w' := QuotientGroup.mk' (ker148 A M) ⟨w, hw⟩ with hw'
  have hw'A : w' ∈ Subgroup.normalizer (img148 A M A : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer (Subgroup.zpowers_le.mpr hwA)
      (mem_img148_iff.mpr ⟨w, hw, Subgroup.mem_zpowers w, rfl⟩)
  have hKeq := h.K_bar_eq ψ
  have hw'K : w' ∈ Subgroup.normalizer
      (img148 A M (L ⊓ Subgroup.normalizer (R : Set G)) : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    rw [hKeq, Subgroup.normalizer_eq_top_iff.mpr h.normal_J]
    exact Subgroup.mem_top _
  have hw'C : w' ∈ Subgroup.normalizer (Subgroup.centralizer
      (img148 A M (L ⊓ Subgroup.normalizer (R : Set G)) : Set (↥(M ⊔ A) ⧸ ker148 A M)) :
        Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    apply Subgroup.mem_normalizer_fintype
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hz ⊢
    intro k hk
    have hk' : w'⁻¹ * k * w' ∈ img148 A M (L ⊓ Subgroup.normalizer (R : Set G)) := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw'K) k).mp hk
      simpa [mul_assoc] using this
    have h1 := hz _ hk'
    calc k * (w' * z * w'⁻¹) = w' * ((w'⁻¹ * k * w') * z) * w'⁻¹ := by group
      _ = w' * (z * (w'⁻¹ * k * w')) * w'⁻¹ := by rw [h1]
      _ = w' * z * w'⁻¹ * k := by group
  have hw'c : w' ∈ Subgroup.normalizer
      (Subgroup.zpowers (alpha148 A M c h.pt.mem_A) : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    rw [h.zpowers_eq_inf_centralizer_K]
    exact mem_normalizer_inf hw'A hw'C
  exact mem_normalizer_zpowers_of_alpha148 hA.1.2 hw hwA h.pt.mem_A hw'c

end Cfg

end KP4

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
