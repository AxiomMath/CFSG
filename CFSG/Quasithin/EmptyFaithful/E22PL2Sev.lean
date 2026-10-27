module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.Quasithin.EmptyFaithful.E22PD1
import CFSG.Quasithin.EmptyFaithful.E22PS4
import CFSG.Quasithin.EmptyFaithful.E22PDick
import CFSG.Dihedral.PerfectDihedralFourgroupAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.GorensteinWalter

theorem e22pl2s_isOddPrimePower {K : Type} (hK : Nat.card K = 7) :
    IsOddPrimePower (Nat.card K) :=
  ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK, pow_one]⟩

theorem e22pl2s_card_psl2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    Nat.card (PSL2 K) = 168 := by
  have h := psl2_card_formula K (e22pl2s_isOddPrimePower hK)
  rw [hK] at h
  omega

theorem e22pl2s_sylow {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7)
    {T : Subgroup (PSL2 K)} (hT : IsSylowIn 2 T ⊤) :
    ∃ S : Sylow 2 (PSL2 K), (S : Subgroup (PSL2 K)) = T ∧ Nat.card T = 8 ∧
      Nonempty (↥(S : Subgroup (PSL2 K)) ≃* DihedralGroup (2 ^ 2)) := by
  have hodd := e22pl2s_isOddPrimePower hK
  have hindex : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]; exact hT.not_dvd_relIndex
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 (PSL2 K) := hT.isPGroup.toSylow hindex
  obtain ⟨m, -, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd S
  have hST : (S : Subgroup (PSL2 K)) = T := rfl
  have hcardS : Nat.card S = 2 ^ (Nat.card (PSL2 K)).factorization 2 :=
    Sylow.card_eq_multiplicity S
  have hfac : (Nat.card (PSL2 K)).factorization 2 = 3 := by
    rw [e22pl2s_card_psl2 hK]
    have h0 : (168 : ℕ) ≠ 0 := by norm_num
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).mp
      (by norm_num : 2 ^ 3 ∣ 168)
    have h2 : ¬ 4 ≤ (168 : ℕ).factorization 2 := fun h =>
      absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).mpr h) (by norm_num)
    omega
  have h8 : Nat.card S = 8 := by rw [hcardS, hfac]; norm_num
  have hcardD : Nat.card S = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hm : m = 2 := by
    have h4 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h4
  subst hm
  exact ⟨S, hST, h8, ⟨e⟩⟩

theorem e22pl2s_normalizer_pCore_solvable {H : Type} [Group H] [Finite H] {V : Subgroup H}
    (hV : IsKleinFour ↥V) (hcent : Subgroup.centralizer (V : Set H) = V)
    (hsurj : Function.Surjective V.normalizerMonoidHom) :
    pCoreOf 2 (Subgroup.normalizer (V : Set H)) = V ∧
      Group.IsSolvable ↥(Subgroup.normalizer (V : Set H)) := by
  obtain ⟨Φ, hΦs, hΦk⟩ := e22ps4_exists_phi hV hcent hsurj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcV : Nat.card V = 4 := IsKleinFour.card_four
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hcV]; norm_num)
  have hVN : V ≤ Subgroup.normalizer (V : Set H) := Subgroup.le_normalizer
  have hker : IsPGroup 2 Φ.ker := by
    rw [hΦk]
    exact hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
  refine ⟨?_, ?_⟩
  · unfold pCoreOf
    rw [e22ps4_pCore_eq_ker Φ hΦs hker, hΦk]
    exact Subgroup.map_subgroupOf_eq_of_le hVN
  · have h1 : Group.IsSolvable ↥Φ.ker := by
      have := IsPGroup.isNilpotent hker
      infer_instance
    have h2 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact Group.isSolvable_of_ker_le_range Φ.ker.subtype Φ (by rw [Subgroup.range_subtype])

theorem e22pl2s_le_normalizer {H : Type} [Group H] {T V : Subgroup H} (hVT : V ≤ T)
    (hT : Nat.card T = 8) (hV : Nat.card V = 4) : T ≤ Subgroup.normalizer (V : Set H) := by
  have h := Subgroup.relIndex_mul_card V T
  rw [inf_eq_left.mpr hVT, hV, hT] at h
  have hidx : (V.subgroupOf T).index = 2 := by
    have : V.relIndex T = 2 := by omega
    exact this
  have hn : (V.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  have key : ∀ (g : T) (x : H), x ∈ V → (g : H) * x * (g : H)⁻¹ ∈ V := fun g x hx =>
    hn.conj_mem (⟨x, hVT hx⟩ : T) hx g
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key ⟨t, ht⟩ x, fun hx => ?_⟩
  have := key ⟨t⁻¹, T.inv_mem ht⟩ _ hx
  simpa [mul_assoc] using this

theorem e22pl2s_normalizer_facts
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) (S : Sylow 2 (PSL2 K))
    (hS8 : Nat.card (S : Subgroup (PSL2 K)) = 8)
    (e : ↥(S : Subgroup (PSL2 K)) ≃* DihedralGroup (2 ^ 2))
    {V : Subgroup (PSL2 K)} (hVS : V ≤ (S : Subgroup (PSL2 K))) (hV : IsKleinFour ↥V) :
    Nat.card (Subgroup.normalizer (V : Set (PSL2 K))) = 24 ∧
      pCoreOf 2 (Subgroup.normalizer (V : Set (PSL2 K))) = V ∧
      Group.IsSolvable ↥(Subgroup.normalizer (V : Set (PSL2 K))) ∧
      (S : Subgroup (PSL2 K)) ≤ Subgroup.normalizer (V : Set (PSL2 K)) := by
  have hodd := e22pl2s_isOddPrimePower hK
  have hperf : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K (by omega)
  have hcent : Subgroup.centralizer (V : Set (PSL2 K)) = V :=
    psl2_kleinFour_centralizer_eq_self K hodd V hV
  have hsurj := perfect_dihedral_fourgroup_normalizer_surjective S (le_refl 2) e V hVS hV
  obtain ⟨hpc, hsolv⟩ := e22pl2s_normalizer_pCore_solvable hV hcent hsurj
  exact ⟨e22ps4_card_normalizer hV hcent hsurj, hpc, hsolv,
    e22pl2s_le_normalizer hVS hS8 IsKleinFour.card_four⟩

theorem e22pl2s_isCoatom_of_card_eq {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7) {M : Subgroup (PSL2 K)} (hM : Nat.card M = 24) : IsCoatom M := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK1 : Nat.card K = 7 ^ 1 := by rw [hK, pow_one]
  have hodd := e22pl2s_isOddPrimePower hK
  have hL : Nat.card (PSL2 K) = 168 := e22pl2s_card_psl2 hK
  have e3 : (Nat.card K - 1) / (Nat.card K - 1).gcd 2 = 3 := by rw [hK]; norm_num
  have e4 : (Nat.card K + 1) / (Nat.card K - 1).gcd 2 = 4 := by rw [hK]; norm_num
  have hdv : ∀ k : ℕ, (k ∣ (Nat.card K - 1) / (Nat.card K - 1).gcd 2 ∨
      k ∣ (Nat.card K + 1) / (Nat.card K - 1).gcd 2) → k ≤ 4 := by
    intro k hk
    rw [e3, e4] at hk
    rcases hk with hk | hk
    · exact (Nat.le_of_dvd (by norm_num) hk).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) hk
  refine ⟨?_, fun H hMH => ?_⟩
  · intro htop
    rw [htop, Subgroup.card_top, hL] at hM
    omega
  have hle : M ≤ H := hMH.le
  have hdvd : 24 ∣ Nat.card H := hM ▸ Subgroup.card_dvd_of_le hle
  have hlt : 24 < Nat.card H := by
    rcases (Nat.le_of_dvd Nat.card_pos hdvd).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hM, h])) hMH.ne
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK1 H with
    hEl | ⟨k, hk, hHk, -⟩ | ⟨k, hk, hHk, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨h5, -⟩ |
      ⟨m, s, -, hs, N, D, hN, hNel, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmf, ⟨eP⟩⟩ |
      ⟨m, hm, hmf, -⟩
  ·
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 7 H).exists_card_eq
    rw [hk] at hdvd
    have h2 : 2 ∣ 7 := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) hdvd)
    omega
  ·
    have := hdv k hk
    rw [hHk] at hdvd hlt
    omega
  ·
    have := hdv k hk
    rw [hHk] at hdvd hlt
    omega
  ·
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr eA4.toEquiv, Nat.card_eq_fintype_card]
      rfl
    omega
  ·
    have h24 : Nat.card H = 24 := by
      rw [Nat.card_congr eS4.toEquiv]
      exact e22pd_card_perm_four
    omega
  ·
    norm_num at h5
  ·
    have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hHcard : Nat.card H = 7 ^ m * s := by
      rw [← hcompl.card_mul_card, hNcard, hDcard]
    rw [hHcard] at hdvd
    have hcop : Nat.Coprime 24 7 := by norm_num
    have hds : 24 ∣ s := (Nat.Coprime.pow_right m hcop).dvd_of_dvd_mul_left hdvd
    have hs3 : s ∣ 3 := by norm_num at hs; exact hs
    have := Nat.le_of_dvd (by norm_num) (dvd_trans hds hs3)
    omega
  ·
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr eP.toEquiv,
      psl2_card_formula _ (CFSG.Walter.isOddPrimePower_of_card (GaloisField.card 7 1 hm)
        (by decide) one_pos),
      GaloisField.card 7 1 hm, psl2_card_formula K hodd, hK, pow_one]
  ·
    have := Nat.le_of_dvd one_pos hmf
    omega

theorem e22pl2s_inEFor_of_isSolvable {G : Type*} [Group G] [Finite G] {T D : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hTD : T ≤ D) (hD : Group.IsSolvable ↥D) : InEFor 1 D T := by
  have h1 : InE 1 D := (nParam_le_iff (H := D) (n := 1) Nat.one_pos).mp
    (by simpa using solvable_nParam_le_one hD)
  exact h1 T (B6.isSylowTwoOf_mono hT hTD le_top)

theorem inEFor_psl2_seven
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7)
    {T : Subgroup (PSL2 K)} (hT : IsSylowIn 2 T ⊤) : InEFor 1 ⊤ T := by
  obtain ⟨S, hST, hT8, ⟨e⟩⟩ := e22pl2s_sylow hK hT
  subst hST
  obtain ⟨V₀, hV₀T, hV₀⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup (PSL2 K)) (by norm_num : 1 ≤ 2) e
  obtain ⟨V₁, hV₁T, hV₁, hne, -⟩ := dihedral_kleinFour_partner (le_refl 2) e hV₀T hV₀
  obtain ⟨hc₀, hp₀, hs₀, hTN₀⟩ := e22pl2s_normalizer_facts hK S hT8 e hV₀T hV₀
  obtain ⟨hc₁, hp₁, hs₁, hTN₁⟩ := e22pl2s_normalizer_facts hK S hT8 e hV₁T hV₁
  have hcoatom := e22pl2s_isCoatom_of_card_eq hK hc₀
  have hMne : Subgroup.normalizer (V₀ : Set (PSL2 K)) ≠ Subgroup.normalizer (V₁ : Set (PSL2 K)) :=
    fun h => hne (calc V₁ = pCoreOf 2 (Subgroup.normalizer (V₁ : Set (PSL2 K))) := hp₁.symm
      _ = pCoreOf 2 (Subgroup.normalizer (V₀ : Set (PSL2 K))) := by rw [h]
      _ = V₀ := hp₀)
  have hnle : ¬ Subgroup.normalizer (V₁ : Set (PSL2 K)) ≤
      Subgroup.normalizer (V₀ : Set (PSL2 K)) := fun h =>
    hMne (Subgroup.eq_of_le_of_card_ge h (by rw [hc₀, hc₁])).symm
  have hsup : Subgroup.normalizer (V₀ : Set (PSL2 K)) ⊔ Subgroup.normalizer (V₁ : Set (PSL2 K)) =
      ⊤ := hcoatom.2 _ (lt_of_le_of_ne le_sup_left fun h => hnle (le_sup_right.trans h.symm.le))
  refine inEFor_of_generated hT
    (Δ := {Subgroup.normalizer (V₀ : Set (PSL2 K)), Subgroup.normalizer (V₁ : Set (PSL2 K))})
    ?_ ?_ ?_
  · rw [iSup_insert, iSup_singleton]
    exact hsup
  · intro D hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact hTN₀
    · exact hTN₁
  · intro D hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact e22pl2s_inEFor_of_isSolvable hT hTN₀ hs₀
    · exact e22pl2s_inEFor_of_isSolvable hT hTN₁ hs₁

end CFSG.Quasithin.E22L2
