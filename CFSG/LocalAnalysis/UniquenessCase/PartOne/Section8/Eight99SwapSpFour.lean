module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99SwapPowFour
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99OrbitFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Sp
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3W
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Cyc
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Frat
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Sz
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3SzT
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.GroupTheory.BarImageConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem r899_sp_of_facts_swap {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig)
    (hswap : ∃ τ ∈ D.M, ∃ K ∈ conjSetOf D.M L, K.map (MulAut.conj τ).toMonoidHom = K ∧
      ∃ K' ∈ conjSetOf D.M L, K'.map (MulAut.conj τ).toMonoidHom ≠ K')
    {A₀ : Subgroup G} (hA₀M : A₀ ≤ D.M) (hA₀ : IsElemAbelian p A₀) (hA₀c : Nat.card A₀ = p ^ 4)
    (hA₀N : ∀ K ∈ conjSetOf D.M L, A₀ ≤ normalizer (K : Set G))
    (hcyc : ∀ K ∈ conjSetOf D.M L, ∀ S : Subgroup (Bar2 D.M),
      CFSG.ABGLocalTools.IsSylowOf r S (barImage D.M K) → IsCyclic S)
    (hKS : ∀ K ∈ conjSetOf D.M L, ∀ S : Subgroup (Bar2 D.M),
      CFSG.ABGLocalTools.IsSylowOf r S (barImage D.M K) →
      ∀ y ∈ barImage D.M K, y ∈ normalizer (S : Set (Bar2 D.M)) → orderOf y ≠ p)
    (hinf : ∀ K ∈ conjSetOf D.M L, ∀ B : Subgroup (Bar2 D.M), IsElemAbelian p B →
      Nat.card (B ⊓ barImage D.M K : Subgroup (Bar2 D.M)) ≤ p)
    (hpK : ∀ K ∈ conjSetOf D.M L, p ∣ Nat.card (barImage D.M K)) :
    IsStronglyPEmbedded r D.M := by
  refine uc22r899c4_sp_of_scalar hSg h614 h76 hL hc3 hLS hs hsn hr hrs hp ?_
  intro K₁ h1S K₂ h2S hne a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  obtain ⟨K₃, h3S, h31, h32⟩ := uc22r899c3_exists_third (K₁ := K₁) (K₂ := K₂) hc3
  set Kf : Fin 3 → Subgroup G := ![K₁, K₂, K₃] with hKf
  have hKfS : ∀ i, Kf i ∈ conjSetOf D.M L := by
    intro i
    fin_cases i
    exacts [h1S, h2S, h3S]
  have hKfne : ∀ i j, i ≠ j → Kf i ≠ Kf j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    exacts [hne, h31.symm, hne.symm, h32.symm, h31, h32]
  have hKfC : ∀ i, Kf i ∈ calC D.M := fun i => uc22p2214_calC_of_mem_conjSetOf hL (hKfS i)
  have hKfM : ∀ i, Kf i ≤ D.M := fun i => uc22p22a_le_of_isSubnormal (hKfC i).1
  set Kb : Fin 3 → Subgroup (Bar2 D.M) := fun i => barImage D.M (Kf i) with hKb
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Kb i, ∀ y ∈ Kb j, x * y = y * x := fun i j hij =>
    uc22p22l_barImage_commute (hKfC i) (hKfC j) (hKfne i j hij)
  obtain ⟨w, hwM, hw1, hw2, hw3⟩ :=
    uc22r899c4_exists_cycle hc3 h1S h2S h3S hne h31.symm h32.symm
  obtain ⟨τ, hτM, hτ1, hτ2, hτ3⟩ :=
    r899_exists_swap_pair hc3 hswap h1S h2S h3S hne h31.symm h32.symm
  have hwK : ∀ i, (Kf i).map (MulAut.conj w).toMonoidHom = Kf (i + 1) := by
    intro i
    fin_cases i
    exacts [hw1, hw2, hw3]
  have hwKb : ∀ i,
      (Kb i).map (MulAut.conj (uc22p21cPi D.M ⟨w, hwM⟩)).toMonoidHom = Kb (i + 1) := by
    intro i
    have h := CFSG.GroupTheory.barImage_map_conj D.M (Kf i) (hKfM i) hwM
    rw [hwK i] at h
    exact h.symm
  have hτK : ∀ i, (Kf i).map (MulAut.conj τ).toMonoidHom = Kf (Equiv.swap 0 1 i) := by
    intro i
    fin_cases i
    · change (Kf 0).map (MulAut.conj τ).toMonoidHom = Kf (Equiv.swap 0 1 (0 : Fin 3))
      rw [show (Equiv.swap 0 1) (0 : Fin 3) = 1 from by decide]
      exact hτ1
    · change (Kf 1).map (MulAut.conj τ).toMonoidHom = Kf (Equiv.swap 0 1 (1 : Fin 3))
      rw [show (Equiv.swap 0 1) (1 : Fin 3) = 0 from by decide]
      exact hτ2
    · change (Kf 2).map (MulAut.conj τ).toMonoidHom = Kf (Equiv.swap 0 1 (2 : Fin 3))
      rw [show (Equiv.swap 0 1) (2 : Fin 3) = 2 from by decide]
      exact hτ3
  have hτKb : ∀ i, (Kb i).map (MulAut.conj (uc22p21cPi D.M ⟨τ, hτM⟩)).toMonoidHom =
      Kb (Equiv.swap 0 1 i) := by
    intro i
    have h := CFSG.GroupTheory.barImage_map_conj D.M (Kf i) (hKfM i) hτM
    rw [hτK i] at h
    exact h.symm
  have hord : ∀ x : ↥D.M, orderOf (x : G) = r → orderOf (uc22p21cPi D.M x) = r := by
    intro x hx
    rw [Subgroup.orderOf_coe] at hx
    have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    refine orderOf_eq_prime (by rw [← map_pow, hxr, map_one]) fun h1 => ?_
    have h2 := uc22r8100b_eq_one_of_mem_pCore ((QuotientGroup.eq_one_iff _).1 h1)
      (hr.odd_of_ne_two hr2) hxr
    rw [h2, orderOf_one] at hx
    exact hr.one_lt.ne hx
  have ht₁ : uc22p21cPi D.M a₁ ∈ Kb 0 := uc22p21c_mem_barImage.2 ⟨a₁, ha₁, rfl⟩
  have ht₂ : uc22p21cPi D.M a₂ ∈ Kb 1 := uc22p21c_mem_barImage.2 ⟨a₂, ha₂, rfl⟩
  obtain ⟨S₀, hS₀, ht₀S⟩ := uc22r8100b_exists_sylow_mem ht₁ (hord a₁ ha₁o)
  obtain ⟨S₁, hS₁, ht₁S⟩ := uc22r8100b_exists_sylow_mem ht₂ (hord a₂ ha₂o)
  obtain ⟨S₂, hS₂⟩ := CFSG.ABGLocalTools.exists_isSylowOf r (Kb 2)
  set Sf : Fin 3 → Subgroup (Bar2 D.M) := ![S₀, S₁, S₂] with hSf
  have hSfS : ∀ i, CFSG.ABGLocalTools.IsSylowOf r (Sf i) (Kb i) := by
    intro i
    fin_cases i
    exacts [hS₀, hS₁, hS₂]
  obtain ⟨w', hw'K, hw'S⟩ := uc22r899c4_exists_shift hSfS hcomm hwKb
  obtain ⟨τ', hτ'K, hτ'S⟩ := r899_exists_shift_perm hSfS hcomm (Equiv.swap 0 1) hτKb
  set tf : Fin 3 → Bar2 D.M :=
    ![uc22p21cPi D.M a₁, uc22p21cPi D.M a₂, w' * uc22p21cPi D.M a₂ * w'⁻¹] with htf
  have htS : ∀ i, tf i ∈ Sf i := by
    intro i
    fin_cases i
    · exact ht₀S
    · exact ht₁S
    · have h : (Sf 1).map (MulAut.conj w').toMonoidHom = Sf 2 := by
        have h1 := hw'S 1
        rwa [show (1 : Fin 3) + 1 = 2 from by decide] at h1
      show w' * uc22p21cPi D.M a₂ * w'⁻¹ ∈ Sf 2
      rw [← h]
      exact ⟨_, ht₁S, rfl⟩
  have hto : ∀ i, orderOf (tf i) = r := by
    intro i
    fin_cases i
    · exact hord a₁ ha₁o
    · exact hord a₂ ha₂o
    · exact (MulEquiv.orderOf_eq (MulAut.conj w') _).trans (hord a₂ ha₂o)
  have hdisj : Disjoint (A₀.subgroupOf D.M) (uc22p21cPi D.M).ker := by
    refine Subgroup.disjoint_def.2 fun {x} hxA hxk => ?_
    exact uc22r8100b_eq_one_of_mem_pCore
      ((QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hxk)) (hpp.odd_of_ne_two hp2)
      (Subtype.ext (hA₀.2 (x : G) hxA))
  have hA₀el : IsElemAbelian p (barImage D.M A₀) := (hA₀.subgroupOf D.M).map (uc22p21cPi D.M)
  have hA₀card : Nat.card (barImage D.M A₀) = p ^ 4 := by
    rw [← hA₀c, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv]
    exact UC6S846.card_map_of_disjoint_ker (uc22p21cPi D.M) (A₀.subgroupOf D.M) hdisj
  have hKSf : ∀ i, ∀ y ∈ Kb i, y ∈ normalizer (Sf i : Set (Bar2 D.M)) → orderOf y ≠ p :=
    fun i => hKS (Kf i) (hKfS i) (Sf i) (hSfS i)
  obtain ⟨d, hdo, hdN⟩ := uc22r899c4_exists_frattini3 hpp hr hSfS hKSf
    (fun i B hB => hinf (Kf i) (hKfS i) B hB) hcomm hA₀el hA₀card
    (fun i => uc22r8100b_barImage_le_normalizer (hA₀N (Kf i) (hKfS i)))
  obtain ⟨g, hg, hgo, k, hk0, hk1⟩ := r899_exists_common_pow_swap hpp hp2 hr
    (fun i => hcyc (Kf i) (hKfS i) (Sf i) (hSfS i)) htS hto hw'K hw'S hτ'K hτ'S hdo
    (fun i => (hdN i).1) (fun i => (hdN i).2)
  obtain ⟨B, hBel, hBc, hBpow, z, hzB, hz1, hzc⟩ :=
    r899_exists_scalar_of_common_pow hpp (K := Kb) (S := Sf) (t := tf) (fun i => (hSfS i).le)
      htS hcomm (hKSf 2) (hpK K₃ h3S) hg hgo hk0 hk1
  have e0 : tf 0 = uc22p21cPi D.M a₁ := rfl
  have e1 : tf 1 = uc22p21cPi D.M a₂ := rfl
  rw [e0, e1] at hBpow hzc
  exact ⟨B, hBel, hBc, hBpow, z, hzB, hz1, hzc⟩

theorem r899_sp_of_swap {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n s r : ℕ}
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig)
    (hp3 : p ≠ 3)
    (hpn : (IsL2 (Bar2 L) n ∧ p ∣ 2 ^ n + 1) ∨ (IsSz (Bar2 L) n ∧ p ∣ 2 ^ (2 * n) + 1))
    (hswap : ∃ τ ∈ D.M, ∃ K ∈ conjSetOf D.M L, K.map (MulAut.conj τ).toMonoidHom = K ∧
      ∃ K' ∈ conjSetOf D.M L, K'.map (MulAut.conj τ).toMonoidHom ≠ K') :
    IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hfour p hp)
  have hA₀N : ∀ K ∈ conjSetOf D.M L, A₀ ≤ normalizer (K : Set G) := fun K hK g hg =>
    uc22r899_mem_normalizer_of_fix hc3 (hA₀M hg) hpp hp2 (k := 1)
      (by rw [pow_one]; exact hA₀.2 g hg) (fun h => absurd h hp3) K hK
  rcases hpn with ⟨hL2, hpn⟩ | ⟨hSz, hpn⟩
  ·
    have hX : ∀ K ∈ conjSetOf D.M L, IsL2 (barImage D.M K) n := by
      intro K hK
      obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
      exact CFSG.Blueprint.LieModel.of_mulEquiv e (uc22s21r899_isL2_of_mem hK hL2)
    refine r899_sp_of_facts_swap hSg h614 h76 hL hc3 (Or.inl hL2) hs hsn hr hrs hp hswap
      hA₀M hA₀ hA₀c hA₀N (fun K hK S hS => ?_)
      (fun K hK S hS => uc22r8100b_not_dvd_normalizer_of_le (hX K hK) hpp hp2 hpn hr hrn hS)
      (fun K hK B hB => uc22r8100b_card_inf_le hpp hp2 (hX K hK) hB) (fun K hK => ?_)
    ·
      have := P22y.isCyclic_of_isPGroup_of_isL2Ev (P22fin.isL2Ev_of_isL2 (hX K hK)).1 hr
        hr2 (S.subgroupOf (barImage D.M K))
        (hS.isPGroup.comap_of_injective (barImage D.M K).subtype
          (barImage D.M K).subtype_injective)
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS.le) (MulEquiv.surjective _)
    ·
      obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
      have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have h := Nat.sq_sub_sq (2 ^ n) 1
        rwa [one_pow] at h
      rw [← Nat.card_congr e.toEquiv, uc22p22r_L2_card (uc22s21r899_isL2_of_mem hK hL2), h1]
      exact (hpn.mul_right _).mul_left _
  ·
    have hY : ∀ K ∈ conjSetOf D.M L, IsSz (Bar2 K) n := by
      rintro K ⟨g, -, rfl⟩
      obtain ⟨e⟩ := uc22p20d_bar2_conj g L
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz
    have hX : ∀ K ∈ conjSetOf D.M L, IsSz (barImage D.M K) n := by
      intro K hK
      obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
      exact CFSG.Blueprint.LieModel.of_mulEquiv e (hY K hK)
    refine r899_sp_of_facts_swap hSg h614 h76 hL hc3 (Or.inr hSz) hs hsn hr hrs hp hswap
      hA₀M hA₀ hA₀c hA₀N (fun K hK S hS => ?_)
      (fun K hK S hS => uc22r899c3_not_dvd_normalizer_Sz (hX K hK) hpp hp2 hpn hr hr2 hrn hS)
      (fun K hK B hB => uc22r899c3_card_inf_le_Sz hpp hp2 (hX K hK) hB) (fun K hK => ?_)
    ·
      obtain ⟨Q, rfl⟩ := hS
      obtain ⟨a, F, _, _, e, -, -, -, hQT, -⟩ :=
        uc22r899c3_suzuki_torus_frame (hX K hK) hr2 hrn Q
      have := CFSG.ShultStronglyClosedTI.SuzukiModel.isCyclic_suzukiT (a := a) (K := F)
      have : IsCyclic ((Q : Subgroup (barImage D.M K)).map e.toMonoidHom) :=
        Subgroup.isCyclic_of_le hQT
      have : IsCyclic (Q : Subgroup (barImage D.M K)) := isCyclic_of_injective
        ((Q : Subgroup (barImage D.M K)).equivMapOfInjective e.toMonoidHom
          e.injective).toMonoidHom (MulEquiv.injective _)
      exact isCyclic_of_surjective ((Q : Subgroup (barImage D.M K)).equivMapOfInjective _
        (barImage D.M K).subtype_injective) (MulEquiv.surjective _)
    ·
      obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
      obtain ⟨a, ha, hna, ⟨e'⟩⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 (hY K hK)
      rw [← Nat.card_congr e.toEquiv, Nat.card_congr
        (e'.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
        CFSG.SectionRank.card_suzukiMatrixGroup a ha, ← hna]
      have h5 : p ∣ (2 ^ n) ^ 2 + 1 := by
        rw [← pow_mul, mul_comm]
        exact hpn
      exact (h5.mul_right _).mul_right _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
