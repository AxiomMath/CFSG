module

public import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProof
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofKernel
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.KFacts.K71bCentList
import CFSG.RankThree.GroupTheory.SteinbergBYAutCentralizerTheta

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1119ResProof

section Generic

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_thetaQuotCentralizer_map {L : Subgroup G} {t : G} (k : G)
    (ht : t ∈ Sec4.thetaQuotCentralizer L) :
    k * t * k⁻¹ ∈ Sec4.thetaQuotCentralizer (L.map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨htN, htl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp ht
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN l).mp hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← GroupTheory.SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv Nat.prime_three
      (MulAut.conj k) L]
    refine Subgroup.mem_map.mpr ⟨_, htl l hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite G] in
theorem not_mem_closure_pair_swap {c d e : G} (hed : e * d = d * e) (he3 : e ^ 3 = 1)
    (hcnd : c ∉ Subgroup.zpowers d)
    (he : e ∉ Subgroup.closure ({c, d} : Set G)) :
    c ∉ Subgroup.closure ({e, d} : Set G) := by
  intro hc
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hed hc
  set T := Subgroup.closure ({c, d} : Set G)
  have hcT : c ∈ T := Subgroup.subset_closure (by simp)
  have hdT : d ∈ T := Subgroup.subset_closure (by simp)
  have he3' : e ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, he3]
  have hei : e ^ i = c * (d ^ j)⁻¹ := by rw [hij]; group
  have heiT : e ^ i ∈ T := by rw [hei]; exact T.mul_mem hcT (T.inv_mem (T.zpow_mem hdT j))
  rw [zpow_eq_zpow_emod i he3'] at heiT hij
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero, one_mul] at hij
    apply hcnd
    rw [hij]
    exact Subgroup.zpow_mem_zpowers d j
  · rw [h1, zpow_one] at heiT
    exact he heiT
  · rw [h2] at heiT
    apply he
    have e2 : e = (e ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, he3', zpow_one, mul_one]
    rw [e2]
    exact T.zpow_mem heiT 2

theorem commutator_mem_theta_of_le {K M : Subgroup G} (hKM : K ≤ M) {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (htM : t ∈ Sec4.thetaQuotCentralizer M) :
    ∀ z ∈ K, t * z * t⁻¹ * z⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  intro z hz
  have h1 : t * z * t⁻¹ * z⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp htK z).mp hz) (K.inv_mem hz)
  have h2 : t * z * t⁻¹ * z⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) M := by
    have h3 := (Sec6.mem_thetaQuotCentralizer_iff.mp htM).2 z (hKM hz)
    have e : t * z * t⁻¹ * z⁻¹ = z * (z⁻¹ * (t * z * t⁻¹)) * z⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta M (hKM hz)) _).mp h3
  exact Sec13.inf_inSubgroup_theta_le hKM ⟨h1, h2⟩

end Generic

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem mem_R_of_commute_c (hbig : Sec11Big G A c L a R Y d x s r g) {y : G}
    (hyP : y ∈ sec11P R g) (hyc : y * c = c * y) : y ∈ R := by
  have h := hbig.toSec11Data
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr h.g_mem_normalizer
  have hyP' : y ∈ ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := hyP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hyP'
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hyP'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hg3 : g ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hbig.orderOf_g, pow_orderOf_eq_one]
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le
  have hyH : u * g ^ m ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hyc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hgmH : g ^ m ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    have e : g ^ m = u⁻¹ * (u * g ^ m) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hRH hu)) hyH
  rw [zpow_eq_zpow_emod m hg3] at hgmH ⊢
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero, mul_one]
    exact hu
  · rw [h1, zpow_one] at hgmH
    exact absurd hgmH h.g_not_mem
  · rw [h2] at hgmH
    have e2 : g = (g ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, hg3, zpow_one, mul_one]
    have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      rw [e2]
      exact Subgroup.zpow_mem _ hgmH 2
    exact absurd hgH h.g_not_mem

theorem s_le_centralizer_A (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsa : s * a = a * s) :
    A ≤ Subgroup.centralizer ({s} : Set G) := by
  have hsR := (Item1116Proof.mem_R h).2.2
  have hsc : s * c = c * s :=
    Subgroup.mem_centralizer_singleton_iff.mp (Item1119Proof.R_le_centralizer_c h hsR)
  have hsd : s * d = d * s := Item1119Proof.commute_d h113 h117 h (Item1119Proof.R_le_P R g hsR)
  rw [h.closure_eq, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hy with rfl | rfl | rfl
  exacts [hsc.symm, hsa.symm, hsd.symm]

theorem sec11K_le_map_conj (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h : Sec11Std G A c L a R Y) (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) {k : G} (hkA : k * c * k⁻¹ ∈ A)
    (hkcd : k * c * k⁻¹ ∉ Subgroup.closure ({c, d} : Set G)) :
    sec11K L (k * c * k⁻¹) ≤ L.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨Ye, hYe, hKY⟩ := exists_mem_thetaComponentsAt_sec11K_le h45 h48 h hdL hA hkA hkcd
  rw [← eq_map_conj_of_sec11K_le h45 h48 h hdL hA hkA hkcd hYe hKY]
  exact hKY

end Data

end Item1119ResProof

section Provers

theorem step1119SymS_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) : Step1119SymS := by
  intro G _ _ A c L a R Y d x s r g hbig _ _ hNA hNd _ hsa hN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  have hstd := hbig.toSec11Std
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have hdA : d ∈ A := (Item1115Proof.d_mem h).1
  obtain ⟨-, -, hsR⟩ := Item1116Proof.mem_R h
  have hcs := h.c_mem_zpowers_s
  have hcnd : c ∉ Subgroup.zpowers d := by
    intro hc
    apply h.zpowers_ne
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, (Item1115Proof.orderOf_c_d h).1,
        (Item1115Proof.orderOf_c_d h).2])
  obtain ⟨h₀, hhP, heA, hecd⟩ :=
    Item1119StepsProof.exists_conj_not_mem (P := sec11P R g) hcA hNA hNd hN
  obtain ⟨k, rfl⟩ : ∃ k : G, h₀ = k⁻¹ := ⟨h₀⁻¹, (inv_inv h₀).symm⟩
  rw [inv_inv] at heA hecd
  have hkP : k ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) := by
    simpa using Subgroup.inv_mem _ hhP
  have hkA : k ∈ Subgroup.normalizer (A : Set G) := hNA hkP
  have he'A : k * c * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hkA c).mp hcA
  have he'cd : k * c * k⁻¹ ∉ Subgroup.closure ({c, d} : Set G) := by
    intro he'cd
    have hhd : k⁻¹ * d * k⁻¹⁻¹ ∈ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp (hNd hhP) d).mp (Subgroup.mem_zpowers d)
    have hmap : (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj k⁻¹).toMonoidHom ≤
        Subgroup.closure ({k⁻¹ * c * k, d} : Set G) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le, Set.image_pair]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · refine Subgroup.subset_closure (Or.inl ?_)
        show k⁻¹ * c * k⁻¹⁻¹ = k⁻¹ * c * k
        rw [inv_inv]
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hhd
    have hc : c ∈ Subgroup.closure ({k⁻¹ * c * k, d} : Set G) := by
      refine hmap ⟨k * c * k⁻¹, he'cd, ?_⟩
      show k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c
      group
    exact Item1119ResProof.not_mem_closure_pair_swap (hcomm _ heA d hdA) (hexp _ heA) hcnd
      hecd hc
  have hAs := Item1119ResProof.s_le_centralizer_A h113 h117 h hsa
  have hs'A : ∀ y ∈ A, (k * s * k⁻¹) * y = y * (k * s * k⁻¹) := by
    intro y hy
    have hy' : k⁻¹ * y * k⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkA) y).mp hy
    rw [inv_inv] at hy'
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hAs hy')
    calc (k * s * k⁻¹) * y = k * (s * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * s) * k⁻¹ := by rw [← h1]
      _ = y * (k * s * k⁻¹) := by group
  have hs'P : k * s * k⁻¹ ∈ sec11P R g :=
    (Subgroup.mem_normalizer_iff.mp hkP s).mp (Item1119Proof.R_le_P R g hsR)
  have hs'R : k * s * k⁻¹ ∈ R := Item1119ResProof.mem_R_of_commute_c hbig hs'P (hs'A c hcA)
  obtain ⟨-, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  have hs'N : k * s * k⁻¹ ∈ Subgroup.normalizer (L : Set G) := hRL hs'R
  have hKk := Item1119ResProof.sec11K_le_map_conj h45 h48 hstd h.inf_eq h.closure_eq he'A he'cd
  have hsC : s ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rw [← h.inf_centralizer_eq] at h1
    exact h1.2
  have hs'C := Item1119ResProof.conj_mem_thetaQuotCentralizer_map k hsC
  have hs'e' : (k * s * k⁻¹) * (k * c * k⁻¹) = (k * c * k⁻¹) * (k * s * k⁻¹) := hs'A _ he'A
  have hs'K : k * s * k⁻¹ ∈ Subgroup.normalizer (sec11K L (k * c * k⁻¹) : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (GroupTheory.SteinbergBY.mem_normalizer_inf hs'N
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hs'e')))
  have htK := Item1119ResProof.commutator_mem_theta_of_le hKk hs'K hs'C
  have he'N : k * c * k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 hcA
      h.ne_one L h.mem_thetaComponentsAt he'A
  have hout : Sec4.InducesOuterTheta (k * c * k⁻¹) L :=
    ⟨he'N, not_isInnerAut_of_not_mem_closure h.toHyp91 h.inf_eq h.closure_eq he'A he'cd he'N⟩
  obtain ⟨i, hi⟩ := KFacts.exists_mul_pow_mem_thetaQuotCentralizer_of_list hstd.isList1016 hout
    (hexp _ he'A) hs'N (Item1116Proof.exists_pow_eq_one_of_mem h hs'R) hs'e' htK
  have hconj : k⁻¹ * ((k * s * k⁻¹) * (k * c * k⁻¹) ^ i) * k⁻¹⁻¹ = s * c ^ i := by
    rw [conj_pow]
    group
  have hsci : s * c ^ i ∈ Sec4.thetaQuotCentralizer (L.map (MulAut.conj k⁻¹).toMonoidHom) := by
    rw [← hconj]
    exact Item1119ResProof.conj_mem_thetaQuotCentralizer_map k⁻¹ hi
  have hcLh : c ∉ Sec4.thetaQuotCentralizer (L.map (MulAut.conj k⁻¹).toMonoidHom) := by
    have hmap : (Subgroup.zpowers c).map (MulAut.conj k⁻¹).toMonoidHom =
        Subgroup.zpowers (k⁻¹ * c * k) := by
      rw [MonoidHom.map_zpowers]
      show Subgroup.zpowers (k⁻¹ * c * k⁻¹⁻¹) = _
      rw [inv_inv]
    refine item111First_of h45 h48 G A c L a R Y hstd k⁻¹ ?_ ?_
    · rw [hmap, Subgroup.zpowers_le]
      exact heA
    · rw [hmap]
      intro hec
      apply hecd
      have : k⁻¹ * c * k ∈ Subgroup.zpowers c := hec ▸ Subgroup.mem_zpowers _
      exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) this
  have hsc1 : s * c ^ i = 1 := by
    by_contra hne
    have hus : s * c ^ i ∈ Subgroup.zpowers s :=
      Subgroup.mul_mem _ (Subgroup.mem_zpowers s) (Subgroup.pow_mem _ hcs i)
    have hc := Item1119StepsProof.mem_zpowers_c_of_mem_zpowers_s h hus hne
    exact hcLh (Subgroup.zpowers_le.mpr hsci hc)
  have hsc' : s ∈ Subgroup.zpowers c := by
    rw [eq_inv_of_mul_eq_one_left hsc1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i)
  exact le_antisymm (Subgroup.zpowers_le.mpr hsc') (Subgroup.zpowers_le.mpr hcs)

end Provers

end CFSG.RankThree.PartTwo.Sec11
