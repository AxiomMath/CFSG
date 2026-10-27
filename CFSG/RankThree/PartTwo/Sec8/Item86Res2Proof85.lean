module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofField
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofCenter
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Standing

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_dvd_mul_of_le_normalizer (N I : Subgroup G)
    (hI : I ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hH, Subgroup.mem_normalizer_iff_map_conj_eq.mp hK]

theorem inf_theta_le_theta {K H : Subgroup G} (hKH : K ≤ H) :
    K ⊓ inSubgroup (aschbacherSolvableCore 3) H ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  obtain ⟨hθHs, -, hθH3, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  set N := (aschbacherSolvableCore 3 H).comap (Subgroup.inclusion hKH) with hN
  set ι : N →* aschbacherSolvableCore 3 H :=
    { toFun := fun x => ⟨Subgroup.inclusion hKH x, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  have hιinj : Function.Injective ι := by
    intro u v huv
    have h := congrArg (fun w : aschbacherSolvableCore 3 H => ((w : H) : G)) huv
    exact Subtype.ext (Subtype.ext h)
  have hNs : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hιinj
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    hθH3 (h3.trans (Subgroup.card_dvd_of_injective ι hιinj))
  have hNθ : N ≤ aschbacherSolvableCore 3 K :=
    hθmax N (Subgroup.Normal.comap inferInstance _) hNs hN3
  rintro x ⟨hxK, ⟨y, hy, hyx⟩⟩
  refine ⟨⟨x, hxK⟩, hNθ ?_, rfl⟩
  have hy' : (⟨x, hKH hxK⟩ : H) = y := Subtype.ext hyx.symm
  change (⟨x, hKH hxK⟩ : H) ∈ aschbacherSolvableCore 3 H
  rw [hy']
  exact hy

theorem le_theta_of_commutator_le {K T : Subgroup G} (hTK : T ≤ K) (hT2 : IsPGroup 2 T)
    (hNT : NoThetaNormal (K ⧸ aschbacherSolvableCore 3 K))
    (hKT : ⁅K, T⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K) :
    T ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hq
  set T' := imageModTheta K T with hT'
  have hcent : ∀ x ∈ T', ∀ k : K ⧸ aschbacherSolvableCore 3 K, k * x = x * k := by
    rintro _ ⟨t, ht, rfl⟩ k
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have htK : ((t : K) : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hc : ⁅(k : G), (t : G)⁆ ∈ inSubgroup (aschbacherSolvableCore 3) K :=
      hKT (Subgroup.commutator_mem_commutator k.2 htK)
    obtain ⟨w, hw, hwc⟩ := hc
    have hw' : w = k * t * k⁻¹ * t⁻¹ := by
      apply Subtype.ext
      have hwc' : (w : G) = (k : G) * t * (k : G)⁻¹ * (t : G)⁻¹ := by
        rw [← commutatorElement_def]
        exact hwc
      rw [hwc']
      simp
    have h1 : ((k * t * k⁻¹ * t⁻¹ : K) : K ⧸ aschbacherSolvableCore 3 K) = 1 := by
      rw [← hw', QuotientGroup.eq_one_iff]
      exact hw
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.mk'_apply]
    calc (k : K ⧸ aschbacherSolvableCore 3 K) * (t : K ⧸ aschbacherSolvableCore 3 K) =
          ((k : K ⧸ aschbacherSolvableCore 3 K) * t * (k : K ⧸ aschbacherSolvableCore 3 K)⁻¹ *
            (t : K ⧸ aschbacherSolvableCore 3 K)⁻¹) * t * k := by group
      _ = t * k := by rw [h1, one_mul]
  have hTn : T'.Normal := ⟨fun t ht g => by
    rw [hcent t ht g, mul_inv_cancel_right]
    exact ht⟩
  have hT'2 : IsPGroup 2 T' := by
    have hT'' : IsPGroup 2 (T.subgroupOf K) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
    exact hT''.map q
  have hTs : Group.IsSolvable T' := by
    have := hT'2.isNilpotent
    infer_instance
  have hT3 : ¬ 3 ∣ Nat.card T' := by
    obtain ⟨k, hk⟩ := hT'2.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hbot := hNT T' hTn hTs hT3
  intro t ht
  have hmem : q ⟨t, hTK ht⟩ ∈ T' := ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  rw [hbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

theorem eq_bot_of_isPGroup_two_of_le {T M : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ M)
    (hM : Odd (Nat.card M)) : T = ⊥ := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hdvd : Nat.card T ∣ Nat.card M := Subgroup.card_dvd_of_le hTM
  rw [hk] at hdvd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq T hk
  · exfalso
    have h2 : 2 ∣ Nat.card M := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h2)

theorem mem_thetaQuotCentralizer_of_eq_sup {X K : Subgroup G} {c : G}
    (hcX : c ∈ Subgroup.normalizer (X : Set G)) (hKc : ∀ k ∈ K, c * k = k * c) (hKX : K ≤ X)
    (hX : X = K ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    c ∈ Sec4.thetaQuotCentralizer X := by
  have hKN : K ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    hKX.trans (Sec6.le_normalizer_theta X)
  have hcθ := Sec6.normalizer_le_normalizer_theta X hcX
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcX, fun l hl => ?_⟩
  rw [hX, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right K _ hKN] at hl
  obtain ⟨k, hk, t, ht, rfl⟩ := hl
  have hct : c * t * c⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X :=
    (Subgroup.mem_normalizer_iff.mp hcθ t).mp ht
  have e : (k * t)⁻¹ * (c * (k * t) * c⁻¹) = t⁻¹ * (c * t * c⁻¹) := by
    calc (k * t)⁻¹ * (c * (k * t) * c⁻¹) = t⁻¹ * k⁻¹ * ((c * k) * t * c⁻¹) := by group
      _ = t⁻¹ * k⁻¹ * ((k * c) * t * c⁻¹) := by rw [hKc k hk]
      _ = t⁻¹ * (c * t * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hct

theorem not_mem_closure_triple {K : Subgroup G} {c a d y : G}
    (hcK : ∀ k ∈ K, c * k = k * c) (hdK : ∀ k ∈ K, d * k = k * d) (hac : a * c = c * a)
    (had : a * d = d * a) (ha3 : a ^ 3 = 1) (hout : Sec4.InducesOuterTheta a K) (hyK : y ∈ K)
    (hyc : MulAut.conj ((⟨y, hyK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ≠ 1) :
    y ∉ Subgroup.closure ({c, a, d} : Set G) := by
  intro hy
  obtain ⟨haN, hout'⟩ := hout
  set ψ : Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec4.thetaQuotMulAut K).comp (Sec4.compAction K) with hψ
  have hset : ({c, a, d} : Set G) = {a} ∪ {c, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  have hcl : Subgroup.closure ({c, a, d} : Set G) =
      Subgroup.zpowers a ⊔ Subgroup.closure ({c, d} : Set G) := by
    rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
  have haCD : Subgroup.zpowers a ≤
      Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hac.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr had.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx))
  rw [hcl, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ haCD] at hy
  obtain ⟨w, hw, u, hu, hwu⟩ := hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have huK : u ∈ Subgroup.centralizer (K : Set G) := by
    have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcK x hx).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hdK x hx).symm
    exact hle hu
  have huN : u ∈ Subgroup.normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ huK
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hyK
  have hψu : ψ ⟨u, huN⟩ = 1 :=
    KFacts.thetaQuotMulAut_compAction_eq_one huN fun x hx =>
      (Subgroup.mem_centralizer_iff.mp huK x hx).symm
  have hψy : ψ ⟨y, hyN⟩ = MulAut.conj ((⟨y, hyK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) :=
    KFacts.thetaQuotMulAut_compAction_eq_conj hyK hyN
  have hsplit : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set G)) = ⟨a, haN⟩ ^ k * ⟨u, huN⟩ :=
    Subtype.ext (by simp [hwu])
  have hψa : ψ ⟨a, haN⟩ ^ k = MulAut.conj ((⟨y, hyK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := by
    rw [← hψy, hsplit, map_mul, map_zpow, hψu, mul_one]
  have hψa3 : ψ ⟨a, haN⟩ ^ 3 = 1 := by
    have : (⟨a, haN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [← map_pow, this, map_one]
  have hinn : ψ ⟨a, haN⟩ ^ k ∈ (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
      MulAut (K ⧸ aschbacherSolvableCore 3 K)).range := ⟨_, hψa.symm⟩
  have hk : ψ ⟨a, haN⟩ ^ k = ψ ⟨a, haN⟩ ^ ((k % 3 : ℤ)) := by
    have hke : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hke, zpow_add, zpow_mul]
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hψa3, one_zpow, mul_one]
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [hk, h0, zpow_zero] at hψa
    exact hyc hψa.symm
  · rw [hk, h1, zpow_one] at hinn
    exact hout' hinn
  · rw [hk, h2] at hinn
    have e : ψ ⟨a, haN⟩ = (ψ ⟨a, haN⟩ ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add,
        show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hψa3, one_mul, zpow_one]
    have h' : ψ ⟨a, haN⟩ ∈ (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
        MulAut (K ⧸ aschbacherSolvableCore 3 K)).range := by
      rw [e]
      exact Subgroup.zpow_mem _ hinn 2
    exact hout' h'

end Helpers


theorem pair85Exists_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hKB : KF83KBarTwo)
    (hInd : KF83Indep) (hO : KF84OuterL2) (hR : KF84FieldReeStd) : Pair85Exists := by
  intro G _ _ A c L a d n h _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd := h.data83
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := h.mem_A
  have haA : a ∈ A := h.a_mem
  have hdA : d ∈ A := hd.d_mem
  have hcL : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    (Item87Proof.residual_le _).trans inf_le_right
  have hcK : ∀ k ∈ K, c * k = k * c := fun k hk => hcy k (hKL hk)
  have hdK : ∀ k ∈ K, d * k = k * d := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKd hk)).symm
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA h.ne_one L h.mem_thetaComponentsAt
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx d hdA))
    have hxLd : x ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp (hAL hx) y),
        (Subgroup.mem_normalizer_iff.mp hxC y)]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ hxLd
  obtain ⟨T, hT, hT1, hTK⟩ := exists_invariant_two_of_sec8Std hKB h
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.2.1
  have hET : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (T : Set G) := hT.2.2
  have hdΓ := isGammaIndex_of_data83 hd
  have hn1 : 1 ≤ n := hdΓ.2.2.1
  have hdc : d ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hdΓ
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hBA : B ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact hdA
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hAe hBA
  have hB9 : 9 ≤ Nat.card B :=
    (CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (h3 c hcA) (h3 d hdA)
      (hcomm c hcA d hdA) h.ne_one hdc).ge
  have hBT : B ≤ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht => (hcK t (hTK ht)).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht => (hdK t (hTK ht)).symm
  have hcB : Subgroup.zpowers c ≤ B := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hc1' : Subgroup.zpowers c ≠ ⊥ := fun h1 => h.ne_one (by
    have := Subgroup.mem_zpowers c
    rwa [h1, Subgroup.mem_bot] at this)
  obtain ⟨b, hbB, hb1, hV⟩ := Sec6.exists_commutator_inf_centralizer_ne_bot hG.charTwoType hT2
    hT1 hBe hB9 hBT hcB hc1'
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T : Set G)) with hQ
  set R := Q ⊓ Subgroup.centralizer ({b} : Set G) with hRdef
  set V := ⁅R, Subgroup.zpowers c⁆ with hVdef
  obtain ⟨i, j, hi, hj, hbij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair
    (hcomm c hcA d hdA) (h3 c hcA) (h3 d hdA) hbB
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hbij
    have hi0 : ¬ 3 ∣ i := by
      intro hi3
      have : i = 0 := by omega
      apply hb1
      rw [hbij, this, pow_zero]
    have hcmem : c ∈ Subgroup.zpowers b :=
      hbij ▸ Item82OneProof.mem_zpowers_pow_of_not_three_dvd (h3 c hcA) hi0
    apply hV
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hrb : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp hr.2
    obtain ⟨m, hm⟩ := hcmem
    have hrc : Commute r c := by
      rw [← hm]
      exact Commute.zpow_right hrb m
    exact (hrc.zpow_right k).eq.symm
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) = L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hbij]
    exact inf_centralizer_mul_pow_eq hcy (h3 d hdA) i (by omega)
  have hbA : b ∈ A := hBA hbB
  have hbΓ : IsGammaIndex A L b n := by
    obtain ⟨-, -, -, hcases⟩ := hdΓ
    exact ⟨hbA, hb1, hn1, by rw [hLb]; exact hcases⟩
  obtain ⟨hKmem, -, -⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  rw [hLb] at hKmem
  have hKmem' : K ∈ thetaComponentsIn
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) := by
    rwa [inf_comm]
  obtain ⟨X, hX, hKX⟩ := Item87Proof.exists_mem_thetaComponentsAt_of_mem_inf h48 hG hAe
    ⟨4, by norm_num, by rw [hA81]; norm_num⟩ hbA hcA hb1 h.ne_one hKmem'
  refine ⟨b, hbB, hb1, X, mem_pairOmega_of_sec8Std hKB hInd h, ⟨n, hbΓ⟩, hX, ?_, ?_⟩
  · rw [hLb]
    exact hKX
  rw [hLb]
  intro hXeq
  have hb3 : b ^ 3 = 1 := h3 b hbA
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbA)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hb3 hb1 hA3 hAb X hX
  have hloc : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 := hG.localRank_three.le
  have hθ3 : ∀ Y : Subgroup G, ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) Y) := by
    intro Y
    rw [inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore Y
  have hθKodd := odd_card_of_le_normalizer hloc hAe hA81 (hθ3 K)
    (hAK.trans (Sec6.normalizer_le_normalizer_theta K))
  have hNT : NoThetaNormal (K ⧸ aschbacherSolvableCore 3 K) := by
    rcases Item87Res2Proof.quot_cases_of_isGammaIndex hdΓ with ⟨-, F, hF, hFf, hFc, ⟨φ⟩⟩ | hφ
    · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
        (Item87Proof.noThetaNormal_statedSU hFc (by omega))
    · obtain ⟨φ⟩ := hφ
      exact Item87Proof.NoThetaNormal.of_mulEquiv φ
        (Item87Proof.noThetaNormal_projSL_two (by omega))
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    (Item87Proof.residual_le _).trans (hLb ▸ inf_le_right)
  have hKTK : ⁅K, T⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk t ht
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk (hTK ht)) (K.inv_mem hk)) (K.inv_mem (hTK ht))
  have hKT : ¬ ⁅K, T⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
    intro hle
    have h1 : ⁅K, T⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
      (le_inf hKTK hle).trans (inf_theta_le_theta hKb)
    exact hT1 (eq_bot_of_isPGroup_two_of_le hT2 (le_theta_of_commutator_le hTK hT2 hNT h1)
      hθKodd)
  have hcθ : c ∈ Sec4.thetaQuotCentralizer X :=
    mem_thetaQuotCentralizer_of_eq_sup (hAX hcA) hcK hKX hXeq
  have hQT : Q ≤ Subgroup.centralizer (T : Set G) := Subgroup.map_subtype_le _
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    have hgb : g ∈ Subgroup.centralizer ({b} : Set G) := hg.2
    have hgT : g ∈ Subgroup.centralizer (T : Set G) := hQT hg.1
    have hX' := Sec6.map_conj_mem_thetaComponentsAt hgb hX
    have hTX' : T ≤ X.map (MulAut.conj g).toMonoidHom := by
      intro t ht
      have hgt : t * g = g * t := Subgroup.mem_centralizer_iff.mp hgT t ht
      refine ⟨t, hKX (hTK ht), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hgt, mul_inv_cancel_right]
    have heq := Item87Proof.eq_of_not_commutator_le hX hX' hKX hTX' hKT
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  have hVX : V ≤ Sec4.thetaQuotCentralizer X := by
    rw [hVdef, Subgroup.commutator_le]
    intro r hr z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hck : c ^ k ∈ Sec4.thetaQuotCentralizer X := Subgroup.zpow_mem _ hcθ k
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Sec6.conj_mem_thetaQuotCentralizer hck (hRX hr))
      (Subgroup.inv_mem _ hck)
  have hVθ : V ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    fun v hv => Sec6.normalizer_le_normalizer_theta X (Sec6.mem_thetaQuotCentralizer_iff.mp
      (hVX hv)).1
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := hBT (Subgroup.subset_closure (by simp))
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := by
    have hcQ : c ∈ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T : Set G))) (Subgroup.le_normalizer hcT)
    have hcb : c ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (hAb hcA)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcQ, hcb⟩
  have hVR : V ≤ R :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcR)
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hV2 : IsPGroup 2 V := hQ2.to_le (hVR.trans inf_le_left)
  set P := inSubgroup (aschbacherSolvableCore 3) X ⊔ V with hPdef
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3P
    have h1 := h3P.trans (card_sup_dvd_mul_of_le_normalizer _ V hVθ)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · exact hθ3 X h2
    · obtain ⟨k, hk⟩ := hV2.exists_card_eq
      rw [hk] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
  have hP2 : 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hV (Subgroup.eq_bot_of_card_eq V hk)
    have h1 := Subgroup.card_dvd_of_le (le_sup_right : V ≤ P)
    rw [hk] at h1
    exact (dvd_pow_self 2 hk0).trans h1
  obtain ⟨hout, y, hya, hy3, hyc⟩ :=
    exists_pow_three_noncentral_of hO hR h.toHyp81 (lt_card_of_sec8Std h) hd
  set E := Subgroup.closure ({c, a, d} : Set G) with hEdef
  have hyE : (y : G) ∉ E :=
    not_mem_closure_triple hcK hdK (hcomm a haA c hcA) (hcomm a haA d hdA) (h3 a haA) hout y.2
      hyc
  have hE27 : Nat.card E = 27 := card_closure_of_sec8Std hInd h
  have hEA : E ≤ A := closure_le_of_sec8Std h
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := Sec5.isElemAbelian_of_le hAe hEA
  have hEy : E ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
    rw [hEdef, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcK y y.2)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hya.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hdK y y.2)
  have hy3' : (y : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hy3]
    rfl
  have hy1 : (y : G) ≠ 1 := fun h1 => hyE (h1 ▸ E.one_mem)
  set E' := E ⊔ Subgroup.zpowers (y : G) with hE'def
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
    Item82OneProof.isElemAbelian_sup_zpowers hEe hy3' fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hEy hx)
  have hyN : Subgroup.zpowers (y : G) ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEy hx)
  have hoy : orderOf (y : G) = 3 := orderOf_eq_prime hy3' hy1
  have hdisj : Disjoint E (Subgroup.zpowers (y : G)) := by
    have hI : Nat.card (Subgroup.zpowers (y : G) ⊓ E : Subgroup G) ∣ 3 := by
      rw [← hoy, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hI with h1 | h1
    · rw [disjoint_comm, disjoint_iff]
      exact (Subgroup.eq_bot_of_card_eq _ h1)
    · exfalso
      apply hyE
      have heq : Subgroup.zpowers (y : G) ⊓ E = Subgroup.zpowers (y : G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hoy])
      have hmem : (y : G) ∈ Subgroup.zpowers (y : G) ⊓ E := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact hmem.2
  have hE'81 : Nat.card E' = 81 := by
    rw [hE'def, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hyN hdisj,
      hE27, Nat.card_zpowers, hoy]
  have hEN : E ≤ Subgroup.normalizer (P : Set G) := by
    intro e he
    have heA : e ∈ A := hEA he
    have heθ := Sec6.normalizer_le_normalizer_theta X (hAX heA)
    have heCT : e ∈ Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) :=
      Source.mem_normalizer_centralizer (hET he)
    have heQ : e ∈ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T : Set G))) heCT
    have heCb : e ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (hAb heA)
    have heR : e ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨heQ, heCb⟩
    have hec : e ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (hcomm c hcA e heA) k).eq
    exact mem_normalizer_sup heθ (Source.mem_normalizer_commutator heR hec)
  have hyP : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    have hyX : (y : G) ∈ X := hKX y.2
    have hyθ := Sec6.le_normalizer_theta X hyX
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hle : P ≤ P.comap (MulAut.conj (y : G)).toMonoidHom := by
      refine sup_le (fun t ht => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hyθ t).mp ht)
      · obtain ⟨-, hvθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hVX hv)
        have h1 := hvθ (y : G)⁻¹ (X.inv_mem hyX)
        have e : (MulAut.conj (y : G)).toMonoidHom v =
            ((y : G)⁻¹⁻¹ * (v * (y : G)⁻¹ * v⁻¹)) * v := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [Subgroup.mem_comap, e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hv)
    exact hle hp
  have hE'N : E' ≤ Subgroup.normalizer (P : Set G) := sup_le hEN (Subgroup.zpowers_le.mpr hyP)
  have hodd := odd_card_of_le_normalizer hloc hE'e hE'81 hP3 hE'N
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hP2)

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
