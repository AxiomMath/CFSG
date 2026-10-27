module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17AutIface
public import CFSG.Quasithin.EmptyFaithful.S1421QA17GenSylow
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification
  CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.M12Cover
  (centralizerInConjEquiv card_centralizer_eq_centralizerIn)
open CFSG.EvenSporadicStandard.Fin76b.J2 (TX TX_le_R card_TX)

namespace S1421QA17

theorem card_le_thirty_two_of_isPGroup {A : Type*} [Group A] [Finite A] {C K : Subgroup A}
    (hC : Nat.card C = 672) (hK : K ≤ C) (hK2 : IsPGroup 2 K) : Nat.card K ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hK2.exists_card_dvd_pow
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn
  have hdvd : Nat.card K ∣ 672 := hC ▸ Subgroup.card_dvd_of_le hK
  rw [hm] at hdvd ⊢
  by_contra h
  have h6 : 6 ≤ m := by
    by_contra h'
    have h5 : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact h (by simpa using h5)
  have : 2 ^ 6 ∣ 672 := (pow_dvd_pow 2 h6).trans hdvd
  norm_num at this

theorem card_centralizer_outer_involution
    {t : ↥R}
    (ht2 : t ^ 2 = 1) (htP : (t : Equiv.Perm (Fin 315)) ∉ P) :
    Nat.card (Subgroup.centralizer ({t} : Set ↥R)) = 672 := by
  have h2 : orderOf (t : Equiv.Perm (Fin 315)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg Subtype.val ht2
      simpa using this
    · intro h1
      exact htP (h1 ▸ P.one_mem)
  obtain ⟨-, -, -, hA, hTwoA, -, -, -, -, -, -, -, hcls, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, c, hc, hrc⟩ := hcls (t : Equiv.Perm (Fin 315)) t.2 h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [card_centralizer_eq_centralizerIn]
  rcases hr with rfl | rfl | rfl
  · exact absurd (hrc ▸ P.mul_mem (P.mul_mem hc hA) (P.inv_mem hc)) htP
  · exact absurd (hrc ▸ P.mul_mem (P.mul_mem hc hTwoA) (P.inv_mem hc)) htP
  · rw [hrc, ← Nat.card_congr (centralizerInConjEquiv R (P_le_R hc) permU).toEquiv]
    exact Kernel.centralizerIn_R_permU.2.1

theorem twoPart_eq_pow_of_card_odd {G : Type*} [Group G] {H : Subgroup G} {n m : ℕ}
    (hm : ¬ 2 ∣ m) (hc : Nat.card H = 2 ^ n * m) : twoPart H = 2 ^ n := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  unfold twoPart
  rw [hc, Nat.factorization_mul (pow_ne_zero n two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem index_P_subgroupOf_R :
    (P.subgroupOf R).index = 2 := by
  have h := (P.subgroupOf R).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_R).toEquiv, card_P, card_R] at h
  omega

theorem isSylowTwoOf_TX :
    IsSylowTwoOf (TX.subgroupOf R) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (TX.subgroupOf R) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe TX_le_R).toEquiv]
    exact card_TX
  refine isSylowTwoOf_of_card_eq le_top (IsPGroup.of_card (n := 8) (by rw [hc]; norm_num)) ?_
  rw [hc, twoPart_eq_pow_of_card_odd (n := 8) (m := 4725) (by norm_num)
    (by rw [Subgroup.card_top, card_R]; norm_num)]
  norm_num

theorem outerInvolutionData_TX :
    OuterInvolutionData (TX.subgroupOf R) (P.subgroupOf R) := by
  refine ⟨TXCode.eC TXCode.jCode, TXCode.eC_mem_T _, TXCode.eC_jCode_not_mem_P,
    TXCode.eC_jCode_sq, TXCode.natCard_T_inf_centralizer_j, TXCode.w_clause, ?_,
    TXCode.emb_clause⟩
  intro K hK hK2
  exact card_le_thirty_two_of_isPGroup (card_centralizer_outer_involution TXCode.eC_jCode_sq
    (TXCode.permC_not_mem_P (c := TXCode.jCode) (by decide))) hK hK2

@[expose] noncomputable def mulAutQuasithinJ2EquivNative :
    MulAut quasithinJ2 ≃* MulAut CFSG.Blueprint.NativeSporadic.J2 :=
  @MulAut.congr quasithinJ2 inferInstance CFSG.Blueprint.NativeSporadic.J2 inferInstance
    quasithinJ2MulEquivNative

@[expose] noncomputable def mulAutQuasithinJ2EquivR :
    MulAut quasithinJ2 ≃* ↥R :=
  mulAutQuasithinJ2EquivNative.trans ((MulAut.congr nativeEquivP).trans rAutEquiv.symm)

theorem autJ2OuterInvolution_holds :
    AutJ2OuterInvolution := by
  intro Y _ T N ⟨e⟩ hT hN _
  have hnorm : (P.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two index_P_subgroupOf_R
  exact outerInvolutionData_of_concrete (T₀ := TX.subgroupOf R) (J := P.subgroupOf R)
    (e.trans mulAutQuasithinJ2EquivR) isSylowTwoOf_TX hnorm index_P_subgroupOf_R
    outerInvolutionData_TX hT hN

end S1421QA17

end CFSG.Quasithin
