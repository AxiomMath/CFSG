module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof159NT
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
import CFSG.RankThree.PartTwo.Sec4.Item462ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Two
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofCentGen
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace KL3FactsProof

theorem sigTwo_map_equiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] (ψ : X ≃* Y)
    (a : X) : (sigTwo a).map ψ.toMonoidHom = sigTwo (ψ a) := by
  unfold sigTwo
  rw [KFacts.KP4.map_pCore_two, KFacts.KP4.map_theta, KFacts.KP4.map_centralizer_singleton]

theorem pCoreOf_le_sigTwo {X : Type} [Group X] [Finite X] (a : X) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set X)) ≤ sigTwo a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({a} : Set X) with hC
  have hO : CFSG.Open.pCoreOf 2 C = inSubgroup (CFSG.pCore 2) C := by
    rw [inSubgroup]
    rfl
  refine CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) C) ?_ ?_
  · rw [hO]
    exact Sec4.Item462Proof.inSubgroup_pCore_two_le_theta C
  · exact (Subgroup.map_subtype_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)

open CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec14.Res5TypesA7 in
theorem torusPair_alt7 {X : Type} [Group X] [Finite X]
    (φ : X ≃* ↥(alternatingGroup (Fin 7))) (D : Subgroup X) (hD9 : Nat.card D = 9) :
    ∃ a ∈ D, ∃ b ∈ D, ¬ IsPGroup 2 ↥(sigTwo a ⊔ sigTwo b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hfac : (Nat.card ↥(alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'⟩ := Res5Types.exists_equiv_map_eq φ card_P7 hD9 hfac
  have hmem : ∀ x ∈ P7, φ'.symm x ∈ D := by
    intro x hx
    rw [← hφ'] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    simpa using hd
  refine ⟨φ'.symm c1, hmem _ c1_mem_P7, φ'.symm c2, hmem _ c2_mem_P7, fun h2 => ?_⟩
  rw [← sigTwo_map_equiv, ← sigTwo_map_equiv, ← Subgroup.map_sup] at h2
  have h2' : IsPGroup 2 ↥(sigTwo c1 ⊔ sigTwo c2) :=
    h2.of_equiv ((sigTwo c1 ⊔ sigTwo c2).equivMapOfInjective _ φ'.symm.injective).symm
  have hV : ∀ (V : Subgroup ↥(alternatingGroup (Fin 7))) (c : ↥(alternatingGroup (Fin 7))),
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set _)) = V →
      Nat.card V = 4 → V ≤ sigTwo c := by
    intro V c hθ h4
    have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
    unfold sigTwo
    rw [hθ]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore hV2 le_rfl
      Subgroup.le_normalizer
  have hV1 : V1 ≤ sigTwo c1 := hV V1 c1 theta_c1 (by
    rw [V1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Res4A7.vOne_le_alternatingGroup).toEquiv,
      KFacts.KP2.card_vOne])
  have hV2 : V2 ≤ sigTwo c2 := hV V2 c2 theta_c2 (by
    rw [V2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Res4A7.vTwo_le_alternatingGroup).toEquiv,
      KFacts.KP2.card_vTwo])
  set g := v1 1 * v2 1 with hg
  have hgJ : g ∈ sigTwo c1 ⊔ sigTwo c2 :=
    mul_mem (Subgroup.mem_sup_left (hV1 ((mem_V1_iff _).mpr (Or.inr (Or.inl rfl)))))
      (Subgroup.mem_sup_right (hV2 ((mem_V2_iff _).mpr (Or.inr (Or.inl rfl)))))
  obtain ⟨h6, h2ne⟩ := KFacts.KP2.check_vOne_vTwo 1 1 (by decide) (by decide)
  obtain ⟨k, hk⟩ := h2' ⟨g, hgJ⟩
  have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h6' : g ^ 6 = 1 := Subtype.ext h6
  have hdvd : orderOf g ∣ Nat.gcd (2 ^ k) 6 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h6')
  have hg2 : orderOf g ∣ 2 := by
    refine hdvd.trans ?_
    obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ k) 6)
    rw [hj]
    have h6j : 2 ^ j ∣ 6 := hj ▸ Nat.gcd_dvd_right (2 ^ k) 6
    rcases j with _ | _ | j
    · norm_num
    · norm_num
    · exfalso
      have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ j + 2)).trans h6j
      norm_num at this
  apply h2ne
  have := orderOf_dvd_iff_pow_eq_one.mp hg2
  exact congrArg Subtype.val this

section Model

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem tM_mem_pCoreOf_centralizer (hK : PiField π p f K) (hp2 : p ≠ 2) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    tM hK hp2 _ isTInv_tOne ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {dM}) := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set t₁ := tM hK hp2 _ isTInv_tOne with ht₁
  set t₂ := tM hK hp2 _ isTInv_tTwo with ht₂
  have h12 : t₁ * t₂ = tM hK hp2 _ isTInv_tThree := tM_one_mul_tM_two hK hp2
  obtain ⟨hc1, hc2, -⟩ := cM_conj_tM hK hp2 hcM
  have hoff : ∀ t : GL (Fin 3) K, IsTInv t → ∀ i j : Fin 3, i ≠ j →
      (t : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro t ht i j hij
    obtain ⟨a, b, c, rfl⟩ := isTInv_diagUnits ht
    rw [coe_diagUnits]
    exact diagonal_apply_ne _ hij
  have hdt : t₁ * dM = dM * t₁ :=
    comm_of_offDiag (coe_tM hK hp2 isTInv_tOne).symm (hoff _ isTInv_tOne)
      (hdM.trans (by rw [diagTau_eq_diagUnits hτ (tau_ne_zero hτ)]))
  have ht12c : t₁ * t₂ = t₂ * t₁ :=
    comm_of_offDiag (coe_tM hK hp2 isTInv_tOne).symm (hoff _ isTInv_tOne)
      (coe_tM hK hp2 isTInv_tTwo)
  set R₀ := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hR₀
  have h1sq : t₁ ^ 2 = 1 := tM_sq hK hp2 isTInv_tOne
  have h2sq : t₂ ^ 2 = 1 := tM_sq hK hp2 isTInv_tTwo
  have hR2 : IsPGroup 2 R₀ := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup ht12c x.2
    rw [Subgroup.coe_pow, hij, pow_one, (Commute.zpow_zpow ht12c i j).mul_pow, ← zpow_natCast,
      ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      mul_comm (j : ℤ), _root_.zpow_mul]
    simp [h1sq, h2sq]
  have hcR : cM ∈ Subgroup.normalizer (R₀ : Set (projImage (slPi π 3 (p ^ f) K))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup ht12c hx
    have hc2' : cM * t₂ * cM⁻¹ = t₁ * t₂ := hc2.trans h12.symm
    rw [show cM * (t₁ ^ i * t₂ ^ j) * cM⁻¹ = (cM * t₁ * cM⁻¹) ^ i * (cM * t₂ * cM⁻¹) ^ j by
      rw [conj_zpow, conj_zpow]; group, hc1, hc2']
    exact mul_mem (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂)) i)
      (zpow_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂))) j)
  have ht₁R : t₁ ∈ R₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁)
  have ht₁C : t₁ ∈ Subgroup.centralizer (R₀ : Set (projImage (slPi π 3 (p ^ f) K))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup ht12c hx
    have h1 : Commute t₁ (t₁ ^ i) := Commute.zpow_right (Commute.refl t₁) i
    have h2 : Commute t₁ (t₂ ^ j) := Commute.zpow_right ht12c j
    exact ((h1.mul_right h2).eq).symm
  exact le_pCoreOf_centralizer_d hτ hτ1 hK hp2 hdM hcM hR2 hcR ht₁R ht₁C hdt
    (tM_ne_one hK hp2 isTInv_tOne) ht₁R

end Model

section Main

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)

theorem centralizer_inv_singleton {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * (x⁻¹ * g) * x := by group
      _ = x * (g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  · intro h
    calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
      _ = x⁻¹ * (g * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * g := by group

theorem torusPair_lThreePi {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8))
    (hiso : Sec4.IsoLThreePi X p e) (D : Subgroup X) (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) :
    ∃ a ∈ D, ∃ b ∈ D, ¬ IsPGroup 2 ↥(sigTwo a ⊔ sigTwo b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h9X : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso h9
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have h9M : (Nat.card (projImage (slPi π 3 (p ^ e) K))).factorization 3 = 2 := by
    rw [← Nat.card_congr ψ.toEquiv, h9X]
  have h9K : ¬ 9 ∣ Nat.card K - 1 := Sec15.Proof1513Res3.not_nine_dvd_card_sub_one' hK h9
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ := Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  set S₀ := Sylow.ofCard E (by rw [hE9, h9M]; norm_num) with hS₀
  have hD'card : Nat.card (D.map ψ.toMonoidHom) =
      3 ^ (Nat.card (projImage (slPi π 3 (p ^ e) K))).factorization 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hD9, h9M]
    norm_num
  set S' := Sylow.ofCard (D.map ψ.toMonoidHom) hD'card with hS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (projImage (slPi π 3 (p ^ e) K)) S₀ S'
  set Φ : projImage (slPi π 3 (p ^ e) K) ≃* X := (MulAut.conj k).trans ψ.symm with hΦ
  have hΦapp : ∀ m, Φ m = ψ.symm (k * m * k⁻¹) := fun m => rfl
  have hΦE : ∀ w ∈ E, Φ w ∈ D := by
    intro w hw
    have h1 : k * w * k⁻¹ ∈ ((k • S₀ : Sylow 3 _) : Subgroup _) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hk] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rw [hΦapp, ← hye]
    change ψ.symm (ψ y) ∈ D
    rw [MulEquiv.symm_apply_apply]
    exact hy
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hdc hx
    obtain ⟨i', j', rfl⟩ := exists_zpow_mul_of_mem_sup hdc hy
    have h1 : Commute (dM ^ i * cM ^ j) (dM ^ i') :=
      (Commute.zpow_zpow_self dM i i').mul_left (Commute.zpow_zpow hdc i' j).symm
    have h2 : Commute (dM ^ i * cM ^ j) (cM ^ j') :=
      (Commute.zpow_zpow hdc i j').mul_left (Commute.zpow_zpow_self cM j j')
    exact (h1.mul_right h2).eq
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hdc hx
    have hd3 : dM ^ 3 = 1 := by
      have := pow_orderOf_eq_one dM
      rwa [hdo] at this
    have hc3 : cM ^ 3 = 1 := by
      have := pow_orderOf_eq_one cM
      rwa [hco] at this
    rw [(Commute.zpow_zpow hdc i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, mul_comm (j : ℤ), _root_.zpow_mul]
    simp [hd3, hc3]
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hτ1
    · exact h
  set F : projImage (slPi π 3 (p ^ e) K) := ⟨ProjGenLinGroup.mk (fourierGL h3 hs),
    ⟨_, fourierGL_mem_slPi hK hq hτ h3 hs, rfl⟩⟩ with hF
  have hFd : F * dM * F⁻¹ = cM⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hdM, hcM]
    exact mk_fourier_diagTau hτ h3 hs)
  set ta := tM hK hp2 _ isTInv_tOne with hta_def
  have hta : ta ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {dM}) :=
    tM_mem_pCoreOf_centralizer hK hp2 hτ hτ1 hdM hcM
  have hta1 : ta ≠ 1 := tM_ne_one hK hp2 isTInv_tOne
  set tb := F * ta * F⁻¹ with htb_def
  have htb : tb ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {cM⁻¹}) := by
    have := map_pCoreOf_centralizer_le (MulAut.conj F) dM ⟨ta, hta, rfl⟩
    rwa [MulAut.conj_apply, hFd] at this
  have htb1 : tb ≠ 1 := by
    intro h
    apply hta1
    calc ta = F⁻¹ * tb * F := by rw [htb_def]; group
      _ = 1 := by rw [h]; group
  have hdE : dM ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  have hcE : cM⁻¹ ∈ E := Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers cM))
  refine ⟨Φ dM, hΦE dM hdE, Φ cM⁻¹, hΦE _ hcE, fun hJ => ?_⟩
  have hta' : Φ ta ∈ sigTwo (Φ dM) :=
    pCoreOf_le_sigTwo _ (map_pCoreOf_centralizer_le Φ dM ⟨ta, hta, rfl⟩)
  have htb' : Φ tb ∈ sigTwo (Φ cM⁻¹) :=
    pCoreOf_le_sigTwo _ (map_pCoreOf_centralizer_le Φ cM⁻¹ ⟨tb, htb, rfl⟩)
  have hDcent : ∀ x ∈ D, D ≤ Subgroup.centralizer ({x} : Set X) := by
    intro x hx d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd⟩ ⟨x, hx⟩)
  have hDJ : D ≤ Subgroup.normalizer
      ((sigTwo (Φ dM) ⊔ sigTwo (Φ cM⁻¹) : Subgroup X) : Set X) :=
    Sec14.le_normalizer_sup
      ((hDcent _ (hΦE dM hdE)).trans (Proof15Res3NT.centralizer_le_normalizer_sigTwo _))
      ((hDcent _ (hΦE _ hcE)).trans (Proof15Res3NT.centralizer_le_normalizer_sigTwo _))
  set R := (sigTwo (Φ dM) ⊔ sigTwo (Φ cM⁻¹)).map Φ.symm.toMonoidHom with hR
  have hR2 : IsPGroup 2 R := hJ.map _
  have hER : E ≤ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ e) K))) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨Φ w * r * (Φ w)⁻¹, (Subgroup.mem_normalizer_iff.mp (hDJ (hΦE w hw)) r).mp hr, ?_⟩
    change Φ.symm (Φ w * r * (Φ w)⁻¹) = w * Φ.symm r * w⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  obtain ⟨b', hb'E, hb'1, hRO⟩ := exists_le_pCoreOf_model hτ hτ1 hK hq hp2 hdM hcM hdc hdo hco
    hcd hR2 hER
  have hRC : R ≤ Subgroup.centralizer {b'} :=
    hRO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have htaR : ta ∈ R := ⟨Φ ta, Subgroup.mem_sup_left hta', Φ.symm_apply_apply ta⟩
  have htbR : tb ∈ R := ⟨Φ tb, Subgroup.mem_sup_right htb', Φ.symm_apply_apply tb⟩
  have htad : ta ∈ Subgroup.centralizer {dM} := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hta
  have htbc : tb ∈ Subgroup.centralizer {cM} := by
    have := CFSG.LieType.BorelTits.pCoreOf_le 2 _ htb
    rwa [centralizer_inv_singleton] at this
  have hb'3 : orderOf b' = 3 := orderOf_eq_prime (hE3 b' hb'E) hb'1
  obtain ⟨z, hzR, hz1, hzE⟩ : ∃ z ∈ R, z ≠ 1 ∧ E ≤ Subgroup.centralizer {z} := by
    by_cases hb' : b' ∈ Subgroup.zpowers dM
    · refine ⟨tb, htbR, htb1, ?_⟩
      have hzb : Subgroup.zpowers b' = Subgroup.zpowers dM :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb')
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hb'3, hdo])
      have hdb : dM ∈ Subgroup.zpowers b' := hzb ▸ Subgroup.mem_zpowers dM
      have h1 : Subgroup.zpowers b' ≤ Subgroup.centralizer {tb} := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hRC htbR)).symm
      refine sup_le (Subgroup.zpowers_le.mpr (h1 hdb)) (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp htbc).symm
    · refine ⟨ta, htaR, hta1, ?_⟩
      have hEb : Subgroup.zpowers dM ⊔ Subgroup.zpowers b' = E := by
        refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hdE)
          (Subgroup.zpowers_le.mpr hb'E)) ?_
        rw [Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hb'3 hb' (fun z hz =>
          hEcomm z (Subgroup.zpowers_le.mpr hdE hz) b' hb'E), Nat.card_zpowers, hdo, hE9]
      rw [← hEb]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp htad).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hRC htaR)).symm
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (hEcomm x x.2 y y.2)⟩⟩, hE3⟩
  have hz2 : Nat.Coprime 3 (orderOf (z : ProjGenLinGroup (Fin 3) K)) := by
    obtain ⟨n, hn⟩ := hR2 ⟨z, hzR⟩
    have hn' : z ^ 2 ^ n = 1 := congrArg Subtype.val hn
    rw [Subgroup.orderOf_coe]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn')
      (Nat.Coprime.pow_right n (by norm_num))
  have h1 := Sec16.ProofHess.eq_one_of_mem_centralizer hK hq h9K
    (E := E.map (projImage (slPi π 3 (p ^ e) K)).subtype) (Subgroup.map_subtype_le _)
    (CFSG.SectionRank.isElemAbelian_map hEab _)
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE9])
    (x := (z : ProjGenLinGroup (Fin 3) K)) z.2 (by
      rintro _ ⟨w, hw, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp (hzE hw)
      exact congrArg Subtype.val this) hz2
  exact hz1 (Subtype.ext h1)

end Main

end KL3FactsProof

open KL3FactsProof

theorem ks159TorusPair : KS159TorusPair := by
  intro X _ _ _ hX D hD hD9
  rcases hX with ⟨p, e, hp, hp2, he, h9, hiso⟩ | ⟨⟨φ⟩⟩
  · exact torusPair_lThreePi hp2 he h9 hiso D hD hD9
  · exact torusPair_alt7 φ D hD9

theorem step159Y0NotTrans_of'
    (h135 : Item135) (h138 : Item138N) (h142 : Item142R) : Step159Y0NotTrans :=
  step159Y0NotTrans_of h135 h138 h142 ks159TorusPair

end CFSG.RankThree.PartTwo.Sec15
