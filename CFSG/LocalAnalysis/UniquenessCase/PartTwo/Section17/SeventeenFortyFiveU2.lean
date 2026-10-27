module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveBExist
public import CFSG.GroupTheory.Commutator.SubgroupOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_45_abtStructure_holds (D : Data G) : Gap17_45_ABTStructure D := by
  intro V₀ V L X p n l r C Dc Gamma x A₀ A y ctx h8100 hc hAsyl hAT hy hAB hANT hdata
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := X ⊔ F08.CentOverO2 D.M X
  let H : Subgroup G := A ⊔ Subgroup.zpowers y ⊔ D.T
  let P : Subgroup G := D.T ⊓ N
  have hXM : X ≤ D.M := by
    rw [ctx.X_eq]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) ctx.mem_calC.1.le
  have hCM : F08.CentOverO2 D.M X ≤ D.M := by
    unfold F08.CentOverO2
    exact (Subgroup.closure_le (K := D.M)).mpr (fun z hz => hz.1)
  have hNM : N ≤ D.M := sup_le hXM hCM
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [ctx.X_eq]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hphi : ∃ φ : ↥D.M →* DihedralGroup p, Function.Surjective φ ∧
      φ.ker = N.subgroupOf D.M := by
    rcases hc with ⟨-, -, hp3, -, φ, hφ, hker⟩ | ⟨-, -, hp5, -, φ, hφ, hker⟩
    · subst hp3
      exact ⟨φ, hφ, hker⟩
    · subst hp5
      exact ⟨φ, hφ, hker⟩
  obtain ⟨φ, hφsurj, hker⟩ := hphi
  have hNnormal : (N.subgroupOf D.M).Normal := by
    rw [← hker]
    exact MonoidHom.normal_ker φ
  have hMN : D.M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNnormal
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  let φy : DihedralGroup p := φ ⟨y, hy.1⟩
  have hordy : orderOf (⟨y, hy.1⟩ : ↥D.M) = p := by
    rw [Subgroup.orderOf_mk]
    exact hy.2.2.1
  have hy_dvd : orderOf φy ∣ p := by
    have h := orderOf_map_dvd φ ⟨y, hy.1⟩
    rwa [hordy] at h
  have hy_ne : φy ≠ 1 := by
    intro h1
    have hmem : ⟨y, hy.1⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact hy.2.1 (Subgroup.mem_subgroupOf.mp hmem)
  have hy_ord : orderOf φy = p := by
    rcases (Nat.dvd_prime hp).mp hy_dvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hy_ne
    · exact h1
  have hφy_rot : φy ∈ TauCeti.dihedralRotations p := by
    rw [TauCeti.mem_dihedralRotations_iff]
    by_contra h
    push Not at h
    rcases hd : φy with i | i
    · exact h i hd
    · rw [hd] at hy_ord
      rw [DihedralGroup.orderOf_sr] at hy_ord
      exact hp2 hy_ord.symm
  have hTH : D.T ≤ H := le_sup_right
  have hAH : A ≤ H := le_sup_left.trans le_sup_left
  have hyH : y ∈ H :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hHM : H ≤ D.M :=
    sup_le (sup_le (hAsyl.le.trans hXM) (Subgroup.zpowers_le.mpr hy.1)) hTM
  have hPH : P ≤ H := inf_le_left.trans hTH
  have hT_P : D.T ≤ Subgroup.normalizer (P : Set G) := by
    intro t ht
    exact CFSG.ABGLocalTools.mem_normalizer_inf (Subgroup.le_normalizer ht) (hMN (hTM ht))
  have hzp_P : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hy.2.2.2.1
  have hNT_P : Subgroup.normalizer (D.T : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    intro g hg
    exact CFSG.ABGLocalTools.mem_normalizer_inf hg (hMN (D.normalizer_le hg))
  have hA_P : A ≤ Subgroup.normalizer (P : Set G) :=
    hANT.trans (sup_le hzp_P hNT_P)
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := sup_le (sup_le hA_P hzp_P) hT_P
  have hP2 : IsPGroup 2 P := hT2.to_le inf_le_left
  have hPsub_normal : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hHP
  let K : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype
  have hK_le_H : K ≤ H := Subgroup.map_subtype_le _
  have hKsub : K.subgroupOf H = CFSG.pCore 2 ↥H := by
    change (((CFSG.pCore 2 ↥H).map H.subtype).comap H.subtype) = CFSG.pCore 2 ↥H
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hKnormal : (K.subgroupOf H).Normal := by
    rw [hKsub]; exact CFSG.pCore_normal
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_H).mp hKnormal
  have hK_le_T : K ≤ D.T := by
    have hTHsyl : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowM.of_le hTH hHM
    obtain ⟨QH, hQH⟩ := hTHsyl.exists_sylow_eq_subgroupOf
    have hpc : CFSG.pCore 2 ↥H ≤ QH :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal QH
    have h := Subgroup.map_mono (f := H.subtype) hpc
    rwa [hQH, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH] at h
  have hP_le_K : P ≤ K := by
    have hsub : P.subgroupOf H ≤ CFSG.pCore 2 ↥H :=
      le_sSup ⟨hPsub_normal, hP2.comap_subtype⟩
    have h := Subgroup.map_mono (f := H.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hPH] at h

  have hA_X : A ≤ X := hAsyl.le
  have hT_N_AP : D.T ≤ Subgroup.normalizer ((A ⊔ P : Subgroup G) : Set G) := by
    intro t ht
    have hTA_sub : A.map (MulAut.conj t).toMonoidHom ≤ A ⊔ P := by
      rintro _ ⟨a, ha, rfl⟩
      change t * a * t⁻¹ ∈ A ⊔ P
      have hta_X : t * a * t⁻¹ ∈ X := by
        have htNX : t ∈ Subgroup.normalizer (X : Set G) := hMX (hTM ht)
        exact (Subgroup.mem_normalizer_iff.mp htNX a).mp (hA_X ha)
      have hta_AT : t * a * t⁻¹ ∈ (A : Set G) * (D.T : Set G) := by
        have hta_TA : t * a ∈ (D.T : Set G) * (A : Set G) := Set.mul_mem_mul ht ha
        rw [hAT.symm] at hta_TA
        obtain ⟨a', ha', t', ht', hat⟩ := Set.mem_mul.mp hta_TA
        refine Set.mem_mul.mpr ⟨a', ha', t' * t⁻¹,
          D.T.mul_mem ht' (D.T.inv_mem ht), ?_⟩
        rw [← hat]
        group
      obtain ⟨a', ha', t', ht', hat⟩ := Set.mem_mul.mp hta_AT
      have ht'X : t' ∈ X := by
        have ha'X : a' ∈ X := hA_X ha'
        have hEq : t' = a'⁻¹ * (t * a * t⁻¹) := by rw [← hat]; group
        rw [hEq]
        exact X.mul_mem (X.inv_mem ha'X) hta_X
      have ht'P : t' ∈ P := ⟨ht', (le_sup_left : X ≤ N) ht'X⟩
      rw [← hat]
      exact (A ⊔ P).mul_mem (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right ht'P)
    have hTP_map : P.map (MulAut.conj t).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hT_P ht)
    have hmap_le : (A ⊔ P).map (MulAut.conj t).toMonoidHom ≤ A ⊔ P := by
      rw [Subgroup.map_sup, hTP_map]
      exact sup_le hTA_sub le_sup_right
    have hmap_eq : (A ⊔ P).map (MulAut.conj t).toMonoidHom = A ⊔ P :=
      Subgroup.eq_of_le_of_card_ge hmap_le
        (by rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq
  have hyA : y ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mp
      ((Subgroup.le_normalizer_iff_commutator_le_left).mpr (le_of_eq hAB))
  have hy_N_AP : y ∈ Subgroup.normalizer ((A ⊔ P : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A P ⟨hyA, hy.2.2.2.1⟩
  have hH_N_AP : H ≤ Subgroup.normalizer ((A ⊔ P : Subgroup G) : Set G) :=
    sup_le (sup_le ((le_sup_left : A ≤ A ⊔ P).trans Subgroup.le_normalizer)
      (Subgroup.zpowers_le.mpr hy_N_AP)) hT_N_AP
  have hK_le_N : K ≤ N := by
    intro s hs
    by_contra hsN
    have hsT : s ∈ D.T := hK_le_T hs
    have hsM : s ∈ D.M := hTM hsT
    let φs : DihedralGroup p := φ ⟨s, hsM⟩
    have hK2 : IsPGroup 2 K := hT2.to_le hK_le_T
    obtain ⟨kk, hkk⟩ := IsPGroup.iff_card.mp hK2
    have hφs_ne : φs ≠ 1 := by
      intro h1
      apply hsN
      have hmem : ⟨s, hsM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have hφs_not_rot : φs ∉ TauCeti.dihedralRotations p := by
      intro hmem
      have hdvd : orderOf (φs) ∣ p := by
        have h := Subgroup.orderOf_dvd_natCard (TauCeti.dihedralRotations p) hmem
        rwa [TauCeti.card_dihedralRotations] at h
      have h2dvd : orderOf (φs) ∣ 2 ^ kk := by
        have h1 : orderOf (⟨s, hsM⟩ : ↥D.M) ∣ 2 ^ kk := by
          rw [Subgroup.orderOf_mk]
          rw [← hkk]
          exact Subgroup.orderOf_dvd_natCard K hs
        exact dvd_trans (orderOf_map_dvd φ ⟨s, hsM⟩) h1
      have hcop : Nat.Coprime p (2 ^ kk) :=
        Nat.Coprime.pow_right kk ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by
          intro h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
      have hone := Nat.eq_one_of_dvd_coprimes hcop hdvd h2dvd
      exact hφs_ne (orderOf_eq_one_iff.mp hone)
    have hconj : φs * φy * (φs)⁻¹ = (φy)⁻¹ :=
      TauCeti.conj_eq_inv_of_notMem_dihedralRotations hφs_not_rot hφy_rot
    have hyK : y * s * y⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHK hyH) s).mp hs
    have hcK : ⁅y, s⁆ ∈ K := by
      have := K.mul_mem hyK (K.inv_mem hs)
      simpa [commutatorElement_def] using this
    have hcM : ⁅y, s⁆ ∈ D.M := hTM (hK_le_T hcK)
    have hφc : φ ⟨⁅y, s⁆, hcM⟩ = (φy) ^ 2 := by
      have hc_eq : (⟨⁅y, s⁆, hcM⟩ : ↥D.M) =
          ⁅(⟨y, hy.1⟩ : ↥D.M), (⟨s, hsM⟩ : ↥D.M)⁆ := by
        apply Subtype.ext
        rfl
      rw [hc_eq, map_commutatorElement, commutatorElement_def, pow_two]
      exact CFSG.GH74.Uniqueness.commutator_eq_sq_of_inverts hconj
    have hr2_ne : (φy) ^ 2 ≠ 1 := by
      intro h2
      have hdvd : orderOf (φy) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hy_ord] at hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    have hφc_ord : orderOf (φ ⟨⁅y, s⁆, hcM⟩) = p := by
      have hpow : (φy) ^ p = 1 := by
        simpa [hy_ord] using pow_orderOf_eq_one (φy)
      have h2 : ((φy) ^ 2) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
      rw [hφc]
      exact orderOf_eq_prime h2 hr2_ne
    have hcK2 : orderOf (φ ⟨⁅y, s⁆, hcM⟩) ∣ 2 ^ kk := by
      have h1 : orderOf (⟨⁅y, s⁆, hcM⟩ : ↥D.M) ∣ 2 ^ kk := by
        rw [Subgroup.orderOf_mk]
        rw [← hkk]
        exact Subgroup.orderOf_dvd_natCard K hcK
      exact dvd_trans (orderOf_map_dvd φ ⟨⁅y, s⁆, hcM⟩) h1
    have hp_dvd : p ∣ 2 ^ kk := by
      rw [← hφc_ord]
      exact hcK2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp_dvd))
  have hK_eq_P : K = P := le_antisymm (le_inf hK_le_T hK_le_N) hP_le_K
  have hfac2p : (2 * p).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by norm_num) hp.ne_zero,
      Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization hp]
    simp [hp2]
  have hcardN : Nat.card ↥D.M = 2 * p * Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card N D.M
    rw [inf_eq_left.mpr hNM] at h
    have hidx : N.relIndex D.M = 2 * p := by
      have h1 : N.relIndex D.M = (N.subgroupOf D.M).index := rfl
      rw [h1, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφsurj,
        Subgroup.card_top, DihedralGroup.nat_card]
    rw [hidx] at h
    exact h.symm
  have hfacM : (Nat.card ↥D.M).factorization 2 = (Nat.card ↥N).factorization 2 + 1 := by
    rw [hcardN, Nat.factorization_mul (mul_ne_zero (by norm_num) hp.ne_zero)
      (Nat.card_pos.ne'), Nat.factorization_mul (by norm_num) hp.ne_zero,
      Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization hp]
    simp [hp2, add_comm]
  have hTN_syl : CFSG.ABGLocalTools.IsSylowOf 2 P N :=
    D.sylowM.inf_of_le_normalizer hNM hMN
  have hcardT : Nat.card ↥D.T = 2 * Nat.card ↥P := by
    rw [D.sylowM.card_eq, hTN_syl.card_eq, hfacM, pow_succ]
    ring
  have hidxTTN : P.relIndex D.T = 2 := by
    have h := Subgroup.relIndex_mul_card P D.T
    rw [inf_eq_left.mpr inf_le_left, hcardT] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  obtain ⟨τ, hτT, hτP⟩ : ∃ τ ∈ D.T, τ ∉ P := by
    by_contra h
    push Not at h
    have hle : D.T ≤ P := fun t ht => h t ht
    have heq : P = D.T := le_antisymm inf_le_left hle
    have h1 := hidxTTN
    rw [heq, Subgroup.relIndex_self] at h1
    omega
  have hτN : τ ∉ N := fun h => hτP ⟨hτT, h⟩
  have hτM : τ ∈ D.M := hTM hτT
  have hτH : τ ∈ H := hTH hτT
  let φτ : DihedralGroup p := φ ⟨τ, hτM⟩
  have hφτ_ne : φτ ≠ 1 := by
    intro h1
    have hmem : ⟨τ, hτM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact hτN (Subgroup.mem_subgroupOf.mp hmem)
  obtain ⟨kkτ, hkkτ⟩ : ∃ kk, orderOf (φτ) ∣ 2 ^ kk := by
    have hzp : Subgroup.zpowers τ ≤ D.T := Subgroup.zpowers_le.mpr hτT
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers τ) := hT2.to_le hzp
    obtain ⟨kk, hkk⟩ := IsPGroup.iff_card.mp h2
    refine ⟨kk, dvd_trans (orderOf_map_dvd φ ⟨τ, hτM⟩) ?_⟩
    rw [Subgroup.orderOf_mk]
    rw [← Nat.card_zpowers]
    rw [hkk]
  have hφτ_ord : orderOf (φτ) = 2 := by
    rcases hd : φτ with i | i
    · exfalso
      have hdp : orderOf (DihedralGroup.r i) ∣ p := by
        apply orderOf_dvd_of_pow_eq_one
        rw [DihedralGroup.r_pow]
        have : i * (p : ZMod p) = 0 := by simp
        rw [this, DihedralGroup.r_zero]
      have hd2 : orderOf (DihedralGroup.r i) ∣ 2 ^ kkτ := by
        rw [← hd]
        exact hkkτ
      have hcop : Nat.Coprime p (2 ^ kkτ) :=
        Nat.Coprime.pow_right kkτ ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by
          intro h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
      have hone := Nat.eq_one_of_dvd_coprimes hcop hdp hd2
      exact hφτ_ne (by rw [hd]; exact orderOf_eq_one_iff.mp hone)
    · exact DihedralGroup.orderOf_sr i
  have hφτ_sq : φτ * φτ = 1 := by
    have h := pow_orderOf_eq_one φτ
    rw [hφτ_ord] at h
    simpa [pow_two] using h
  have hφτ_not_rot : φτ ∉ TauCeti.dihedralRotations p := by
    intro hmem
    have hdvd : orderOf (φτ) ∣ p := by
      have h := Subgroup.orderOf_dvd_natCard (TauCeti.dihedralRotations p) hmem
      rwa [TauCeti.card_dihedralRotations] at h
    rw [hφτ_ord] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  have hτ_conj : φτ * φy * (φτ)⁻¹ = (φy)⁻¹ :=
    TauCeti.conj_eq_inv_of_notMem_dihedralRotations hφτ_not_rot hφy_rot
  let cτ : G := τ * y * τ⁻¹ * y
  have hcτ_sup : cτ ∈ Subgroup.zpowers y ⊔ P := by
    have hTnorm : D.T ≤ Subgroup.normalizer
        ((Subgroup.zpowers y ⊔ P : Subgroup G) : Set G) := by
      simpa [P, N] using hy.2.2.2.2
    have hτyτ : τ * y * τ⁻¹ ∈ Subgroup.zpowers y ⊔ P :=
      (Subgroup.mem_normalizer_iff.mp (hTnorm hτT) y).mp
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
    exact (Subgroup.zpowers y ⊔ P).mul_mem hτyτ
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
  have hτyτ_phi : φ ⟨τ * y * τ⁻¹, D.M.mul_mem (D.M.mul_mem hτM hy.1) (D.M.inv_mem hτM)⟩ =
      (φy)⁻¹ := by
    have h1 : (⟨τ * y * τ⁻¹, D.M.mul_mem (D.M.mul_mem hτM hy.1) (D.M.inv_mem hτM)⟩ : ↥D.M) =
        ⟨τ, hτM⟩ * ⟨y, hy.1⟩ * ⟨τ, hτM⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hτ_conj
  have hcτM : cτ ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hτM hy.1) (D.M.inv_mem hτM)) hy.1
  have hcτ_phi : φ ⟨cτ, hcτM⟩ = 1 := by
    have hsplit : (⟨cτ, hcτM⟩ : ↥D.M) =
        ⟨τ * y * τ⁻¹, D.M.mul_mem (D.M.mul_mem hτM hy.1) (D.M.inv_mem hτM)⟩ *
          ⟨y, hy.1⟩ := Subtype.ext rfl
    rw [hsplit, map_mul, hτyτ_phi, inv_mul_cancel]
  have hcτN : cτ ∈ N := by
    have hmem : ⟨cτ, hcτM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr hcτ_phi
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hzp_inf_N : Subgroup.zpowers y ⊓ N = ⊥ := by
    refine le_bot_iff.mp ?_
    intro z hz
    obtain ⟨hzy, hzN⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzy
    have hzM : z ∈ D.M := hNM hzN
    have hkM : y ^ k ∈ D.M := D.M.zpow_mem hy.1 k
    have hzphi : φ ⟨z, hzM⟩ = 1 := by
      have hmem : ⟨z, hzM⟩ ∈ φ.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr hzN
      exact MonoidHom.mem_ker.mp hmem
    have hkphi : φ ⟨y ^ k, hkM⟩ = (φy) ^ k := by
      rw [show (⟨y ^ k, hkM⟩ : ↥D.M) = ⟨y, hy.1⟩ ^ k from Subtype.ext rfl, map_zpow]
    have hz_eq' : (⟨z, hzM⟩ : ↥D.M) = ⟨y ^ k, hkM⟩ := Subtype.ext hk.symm
    rw [hz_eq'] at hzphi
    have hphi_pow : (φy) ^ k = 1 := by
      rw [← hkphi]
      exact hzphi
    have hdvd : (orderOf (φy) : ℤ) ∣ k :=
      orderOf_dvd_iff_zpow_eq_one.mpr hphi_pow
    rw [hy_ord] at hdvd
    have hdvd' : (orderOf y : ℤ) ∣ k := by simpa [hy.2.2.1] using hdvd
    have h1 : y ^ k = 1 := (orderOf_dvd_iff_zpow_eq_one (x := y)).mp hdvd'
    rw [← hk]
    exact h1
  have hzp_normP : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hy.2.2.2.1
  have hcτ_prod : cτ ∈ (Subgroup.zpowers y : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) P hzp_normP]
    exact hcτ_sup
  obtain ⟨z, hzY, p', hpP, hprod⟩ := Set.mem_mul.mp hcτ_prod
  have hzN : z ∈ N := by
    have hp'N : p' ∈ N := (inf_le_right : P ≤ N) hpP
    have hz_eq : z = cτ * p'⁻¹ := by rw [← hprod]; group
    rw [hz_eq]
    exact N.mul_mem hcτN (N.inv_mem hp'N)
  have hz1 : z = 1 := by
    have hmem : z ∈ Subgroup.zpowers y ⊓ N := ⟨hzY, hzN⟩
    rw [hzp_inf_N, Subgroup.mem_bot] at hmem
    exact hmem
  have hcτP : cτ ∈ P := by
    have hcτ_eq : cτ = p' := by rw [← hprod, hz1, one_mul]
    rwa [hcτ_eq]
  have hcτK : cτ ∈ K := hP_le_K hcτP
  let q : ↥H →* Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let b : Bar2 H := q ⟨y, hyH⟩
  let t : Bar2 H := q ⟨τ, hτH⟩
  let R : Subgroup (Bar2 H) := (A.subgroupOf H).map q
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq_one : ∀ (w : G) (hwH : w ∈ H), q ⟨w, hwH⟩ = 1 ↔ w ∈ K := by
    intro w hwH
    rw [show q ⟨w, hwH⟩ = QuotientGroup.mk ⟨w, hwH⟩ from rfl, QuotientGroup.eq_one_iff,
      ← hKsub, Subgroup.mem_subgroupOf]
  have hb_ord : orderOf b = p := by
    have hdvd : orderOf b ∣ p := by
      have h := orderOf_map_dvd q ⟨y, hyH⟩
      rw [Subgroup.orderOf_mk, hy.2.2.1] at h
      exact h
    have hb_ne : b ≠ 1 := by
      intro h1
      exact hy.2.1 (hK_le_N ((hq_one y hyH).mp h1))
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hb_ne
    · exact h1
  have hτ2N : τ ^ 2 ∈ N := by
    have hphi2 : φ ⟨τ ^ 2, D.M.pow_mem hτM 2⟩ = 1 := by
      have h1 : (⟨τ ^ 2, D.M.pow_mem hτM 2⟩ : ↥D.M) = ⟨τ, hτM⟩ ^ 2 := Subtype.ext rfl
      rw [h1, map_pow, pow_two]
      exact hφτ_sq
    have hmem : ⟨τ ^ 2, D.M.pow_mem hτM 2⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr hphi2
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have ht_sq : t ^ 2 = 1 := by
    have hτ2P : τ ^ 2 ∈ P := ⟨D.T.pow_mem hτT 2, hτ2N⟩
    have hτ2K : τ ^ 2 ∈ K := hP_le_K hτ2P
    have h1 : t ^ 2 = q ⟨τ ^ 2, H.pow_mem hτH 2⟩ := by
      rw [show t = q ⟨τ, hτH⟩ from rfl, ← map_pow]
      congr 1
    rw [h1]
    exact (hq_one (τ ^ 2) (H.pow_mem hτH 2)).mpr hτ2K
  have ht_ne : t ≠ 1 := by
    intro h1
    exact hτN (hK_le_N ((hq_one τ hτH).mp h1))
  have ht_ord : orderOf t = 2 := orderOf_eq_prime ht_sq ht_ne
  have hcardPfac : (Nat.card ↥D.T).factorization 2 = 1 + (Nat.card ↥P).factorization 2 := by
    rw [hcardT, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
      Nat.Prime.factorization Nat.prime_two]
    simp
  have hfacH : (Nat.card ↥H).factorization 2 = 1 + (Nat.card ↥P).factorization 2 := by
    have h1 : (Nat.card ↥D.T).factorization 2 = (Nat.card ↥H).factorization 2 := by
      have hTHsyl : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowM.of_le hTH hHM
      rw [hTHsyl.card_eq, Nat.factorization_pow]
      simp [Nat.Prime.factorization Nat.prime_two]
    rw [← h1, hcardPfac]
  have hfacQ : (Nat.card (Bar2 H)).factorization 2 = 1 := by
    have hcardH : Nat.card ↥H = Nat.card (Bar2 H) * Nat.card ↥(CFSG.pCore 2 ↥H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
    have hKcard : Nat.card K = Nat.card ↥(CFSG.pCore 2 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    have h := congrArg (fun m => m.factorization 2) hcardH
    rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply] at h
    rw [hfacH] at h
    have hKfac : (Nat.card ↥(CFSG.pCore 2 ↥H)).factorization 2 =
        (Nat.card ↥P).factorization 2 := by
      rw [← hKcard, hK_eq_P]
    rw [hKfac] at h
    omega
  have hSyl_t : CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Nat.card_zpowers, ht_ord, Subgroup.card_top, hfacQ]
    norm_num
  have hR_normal : R.Normal := by
    have hAPH : A ⊔ P ≤ H := sup_le hAH hPH
    have hAP_normal : ((A ⊔ P).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAPH).mpr hH_N_AP
    have hmap_eq : ((A ⊔ P).subgroupOf H).map q = R := by
      have hsub : (A ⊔ P).subgroupOf H = (A.subgroupOf H) ⊔ (P.subgroupOf H) :=
        Subgroup.subgroupOf_sup hAH hPH
      rw [hsub, Subgroup.map_sup]
      have hPle_ker : (P.subgroupOf H) ≤ q.ker := by
        intro w hw
        rw [MonoidHom.mem_ker]
        exact (hq_one (w : G) w.2).mpr
          (hP_le_K (Subgroup.mem_subgroupOf.mp hw))
      have hPmap : (P.subgroupOf H).map q = ⊥ :=
        (Subgroup.map_eq_bot_iff (P.subgroupOf H)).mpr hPle_ker
      rw [hPmap, sup_bot_eq]
    rw [← hmap_eq]
    exact hAP_normal.map q hq_surj
  have hhr : r.Prime := h8100.2.2.2.1
  have hXfac : (Nat.card ↥X).factorization r = 2 := hdata.1.2.2.2
  have hR_r : IsPGroup r R := by
    have : Fact r.Prime := ⟨hhr⟩
    have h1 : IsPGroup r (A.subgroupOf H) := hAsyl.isPGroup.comap_subtype
    exact h1.map q
  have hR_abel : IsMulCommutative R := by
    have : Fact r.Prime := ⟨hhr⟩
    have hAc : Nat.card A = r ^ 2 := by
      rw [hAsyl.card_eq, hXfac]
    have : IsPGroup r A := hAsyl.isPGroup
    have hAcomm : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hAc
    have : IsMulCommutative A := hAcomm
    have : IsMulCommutative (A.subgroupOf H) := inferInstance
    change IsMulCommutative ((A.subgroupOf H).map q)
    exact inferInstance
  have hcommR : ⁅R, Subgroup.zpowers b⁆ = R := by
    have hAB' : ⁅Subgroup.zpowers y, A⁆ = A := by
      rw [commutator_comm]
      exact hAB
    have h1 := CFSG.GroupTheory.commutator_zpowers_map_subgroupOf_eq q hyH hAH hAB'
    rw [commutator_comm]
    exact h1
  have htb : t * b * t⁻¹ = b⁻¹ := by
    have h1 : (⟨τ, hτH⟩ : ↥H) * ⟨y, hyH⟩ * (⟨τ, hτH⟩ : ↥H)⁻¹ =
        ⟨cτ * y⁻¹, H.mul_mem (hK_le_H hcτK) (H.inv_mem hyH)⟩ := by
      apply Subtype.ext
      simp [cτ]
    have hmul : q ((⟨τ, hτH⟩ : ↥H) * ⟨y, hyH⟩) =
        q ⟨τ, hτH⟩ * q ⟨y, hyH⟩ := map_mul q _ _
    have hinv : q ((⟨τ, hτH⟩ : ↥H)⁻¹) = (q ⟨τ, hτH⟩)⁻¹ := map_inv q _
    calc t * b * t⁻¹
        = q ⟨τ, hτH⟩ * q ⟨y, hyH⟩ * (q ⟨τ, hτH⟩)⁻¹ := by
            rw [show t = q ⟨τ, hτH⟩ from rfl, show b = q ⟨y, hyH⟩ from rfl]
      _ = q ((⟨τ, hτH⟩ : ↥H) * ⟨y, hyH⟩) * q ((⟨τ, hτH⟩ : ↥H)⁻¹) := by
            rw [← hmul, ← hinv]
      _ = q ((⟨τ, hτH⟩ : ↥H) * ⟨y, hyH⟩ * (⟨τ, hτH⟩ : ↥H)⁻¹) := by
            rw [← map_mul]
      _ = q ⟨cτ * y⁻¹, H.mul_mem (hK_le_H hcτK) (H.inv_mem hyH)⟩ := by rw [h1]
      _ = q (⟨cτ, hK_le_H hcτK⟩ * ⟨y, hyH⟩⁻¹) := by
            congr 1
      _ = q ⟨cτ, hK_le_H hcτK⟩ * (q ⟨y, hyH⟩)⁻¹ := by rw [map_mul, map_inv]
      _ = 1 * b⁻¹ := by rw [(hq_one cτ (hK_le_H hcτK)).mpr hcτK]
      _ = b⁻¹ := one_mul _
  have hzpY_image : ((Subgroup.zpowers y).subgroupOf H).map q = Subgroup.zpowers b := by
    have hsub : (Subgroup.zpowers y).subgroupOf H =
        Subgroup.zpowers (⟨y, hyH⟩ : ↥H) := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hyH),
        MonoidHom.map_zpowers]
      rfl
    rw [hsub, MonoidHom.map_zpowers]
  have hP_image : (P.subgroupOf H).map q = ⊥ := by
    have hPle_ker : (P.subgroupOf H) ≤ q.ker := by
      intro w hw
      rw [MonoidHom.mem_ker]
      exact (hq_one (w : G) w.2).mpr
        (hP_le_K (Subgroup.mem_subgroupOf.mp hw))
    exact (Subgroup.map_eq_bot_iff (P.subgroupOf H)).mpr hPle_ker
  have hT_eq : D.T = P ⊔ Subgroup.zpowers τ := by
    have hle : P ⊔ Subgroup.zpowers τ ≤ D.T :=
      sup_le inf_le_left (Subgroup.zpowers_le.mpr hτT)
    have hrel := Subgroup.relIndex_mul_relIndex P (P ⊔ Subgroup.zpowers τ) D.T le_sup_left hle
    have h1 : P.relIndex (P ⊔ Subgroup.zpowers τ) ≠ 1 := by
      intro h1
      have hle' : P ⊔ Subgroup.zpowers τ ≤ P := Subgroup.relIndex_eq_one.mp h1
      exact hτP (hle' (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)))
    have h2 : P.relIndex (P ⊔ Subgroup.zpowers τ) *
        (P ⊔ Subgroup.zpowers τ).relIndex D.T = 2 := by
      rw [hrel, hidxTTN]
    have h3 : P.relIndex (P ⊔ Subgroup.zpowers τ) ∣ 2 := ⟨_, h2.symm⟩
    have h4 : P.relIndex (P ⊔ Subgroup.zpowers τ) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact absurd h h1
      · exact h
    have h5 : (P ⊔ Subgroup.zpowers τ).relIndex D.T = 1 := by
      rw [h4] at h2
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h5) hle
  have hτ_sub : (Subgroup.zpowers τ).subgroupOf H =
      Subgroup.zpowers (⟨τ, hτH⟩ : ↥H) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hτH),
      MonoidHom.map_zpowers]
    rfl
  have hT_image : (D.T.subgroupOf H).map q = Subgroup.zpowers t := by
    have hsub : D.T.subgroupOf H =
        (P.subgroupOf H) ⊔ (Subgroup.zpowers τ).subgroupOf H := by
      rw [hT_eq, Subgroup.subgroupOf_sup hPH (Subgroup.zpowers_le.mpr hτH)]
    rw [hsub, Subgroup.map_sup, hP_image, bot_sup_eq, hτ_sub, MonoidHom.map_zpowers]
  have hgen_H : ((A.subgroupOf H) ⊔ (Subgroup.zpowers y).subgroupOf H ⊔
      D.T.subgroupOf H) = ⊤ := by
    have hHsup : A ⊔ Subgroup.zpowers y ⊔ D.T = H := rfl
    have h1 : (A ⊔ Subgroup.zpowers y ⊔ D.T).subgroupOf H = ⊤ := by
      rw [hHsup, Subgroup.subgroupOf_self]
    have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
      ext x
      constructor
      · intro hx
        obtain ⟨y₀, -, rfl⟩ := Subgroup.mem_map.mp hx
        exact y₀.2
      · intro hx
        exact Subgroup.mem_map_of_mem H.subtype (Subgroup.mem_top ⟨x, hx⟩)
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hAH,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hyH),
      Subgroup.map_subgroupOf_eq_of_le hTH, htop]
  have hgenR : R ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers t = ⊤ := by
    have hmapgen : ((A.subgroupOf H) ⊔ (Subgroup.zpowers y).subgroupOf H ⊔
        D.T.subgroupOf H).map q = ⊤ := by
      rw [hgen_H, Subgroup.map_top_of_surjective q hq_surj]
    rw [Subgroup.map_sup, Subgroup.map_sup, hzpY_image, hT_image] at hmapgen
    exact hmapgen
  exact ⟨R, b, t, hR_normal, hR_abel, hR_r, hb_ord, ht_ord, hSyl_t, htb, hcommR, hgenR⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
