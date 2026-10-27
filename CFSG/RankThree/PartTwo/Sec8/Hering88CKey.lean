module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOrders
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88C

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem normal_subgroupOf_theta (X : Subgroup G) :
    ((inSubgroup (aschbacherSolvableCore 3) X).subgroupOf (Subgroup.normalizer (X : Set G))).Normal
    := by
  refine ⟨fun n hn g => ?_⟩
  have hNP : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.le_normalizer_theta_of_le_normalizer Nat.prime_three le_rfl
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hNP g.2) (n : G)).mp hn
  simpa using this

theorem exists_invariant_two_of_isType419 (hAut : Sec4.K419AutThree)
    {X J : Subgroup G} (hJX : J ≤ X) (htype : Sec4.IsType419 (imageModTheta X J))
    (h2 : 2 ∣ Nat.card (imageModTheta X J))
    {F C : Subgroup G} {e : G} (hF3 : IsPGroup 3 F)
    (hFX : F ≤ Subgroup.normalizer (X : Set G)) (hFJ : F ≤ Subgroup.normalizer (J : Set G))
    (hCF : C ≤ F) (heF : e ∈ F) (he3 : e ^ 3 = 1) (hFe : F ≤ C ⊔ Subgroup.zpowers e)
    (hC : ∀ g ∈ C, ∀ j ∈ J, g * j * g⁻¹ * j⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X) :
    ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ F ≤ Subgroup.normalizer (S : Set G) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN
  set P : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X with hP
  have hXN : X ≤ N := Subgroup.le_normalizer
  have hPX : P ≤ X := Subgroup.map_subtype_le _
  haveI hPn : (P.subgroupOf N).Normal := normal_subgroupOf_theta X
  set π : N →* N ⧸ P.subgroupOf N := QuotientGroup.mk' (P.subgroupOf N) with hπ
  set ι : (X ⧸ aschbacherSolvableCore 3 X) →* (N ⧸ P.subgroupOf N) :=
    QuotientGroup.map (aschbacherSolvableCore 3 X) (P.subgroupOf N) (Subgroup.inclusion hXN)
      (by
        intro z hz
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
        exact ⟨z, hz, rfl⟩) with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    have h1 : ι (x : X ⧸ aschbacherSolvableCore 3 X) =
        (Subgroup.inclusion hXN x : N ⧸ P.subgroupOf N) := rfl
    rw [h1, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    obtain ⟨z, hz, hzx⟩ := hq
    have : z = x := Subtype.ext hzx
    rwa [← this]
  set K : Subgroup (N ⧸ P.subgroupOf N) := (imageModTheta X J).map ι with hK
  have htypeK : Sec4.IsType419 K :=
    Sec4.Item419Res3.isType419_of_mulEquiv
      ((imageModTheta X J).equivMapOfInjective ι hιinj).symm htype
  have h2K : 2 ∣ Nat.card K := by
    rw [← Nat.card_congr ((imageModTheta X J).equivMapOfInjective ι hιinj).toEquiv]
    exact h2
  have hKmem : ∀ t ∈ K, ∃ j : N, (j : G) ∈ J ∧ π j = t := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨x, hx, rfl⟩ := hr
    exact ⟨Subgroup.inclusion hXN x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hjK : ∀ j : N, (j : G) ∈ J → π j ∈ K := by
    intro j hj
    exact ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨j, hJX hj⟩,
      ⟨⟨j, hJX hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩, rfl⟩
  have hFK : ∀ (f : G) (hf : f ∈ F), π ⟨f, hFX hf⟩ ∈ Subgroup.normalizer (K : Set _) := by
    intro f hf
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨j, hjJ, rfl⟩ := hKmem k hk
    have h1 : f * (j : G) * f⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hFJ hf) j).mp hjJ
    have h2 : π ⟨f, hFX hf⟩ * π j * (π ⟨f, hFX hf⟩)⁻¹ =
        π (⟨f, hFX hf⟩ * j * ⟨f, hFX hf⟩⁻¹) := by simp
    rw [h2]
    exact hjK _ h1
  have hCcent : ∀ (g : G) (hg : g ∈ C), π ⟨g, hFX (hCF hg)⟩ ∈
      Subgroup.centralizer (K : Set (N ⧸ P.subgroupOf N)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨j, hjJ, rfl⟩ := hKmem k hk
    have h1 : g * (j : G) * g⁻¹ * (j : G)⁻¹ ∈ P := hC g hg j hjJ
    have h2 : (⟨g, hFX (hCF hg)⟩ * j * ⟨g, hFX (hCF hg)⟩⁻¹ * j⁻¹ : N) ∈ P.subgroupOf N := h1
    have h3 : π (⟨g, hFX (hCF hg)⟩ * j * ⟨g, hFX (hCF hg)⟩⁻¹ * j⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)).symm
  have he3' : (π ⟨e, hFX heF⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨e, hFX heF⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using he3)
    rw [this, map_one]
  obtain ⟨T, hTK, hT2, hTne, hTe⟩ : ∃ T : Subgroup (N ⧸ P.subgroupOf N), T ≤ K ∧ IsPGroup 2 T ∧
      T ≠ ⊥ ∧ π ⟨e, hFX heF⟩ ∈ Subgroup.normalizer (T : Set (N ⧸ P.subgroupOf N)) := by
    by_cases hcen : π ⟨e, hFX heF⟩ ∈ Subgroup.centralizer (K : Set (N ⧸ P.subgroupOf N))
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2K
      have ht2 : orderOf (t : N ⧸ P.subgroupOf N) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
      refine ⟨Subgroup.zpowers (t : N ⧸ P.subgroupOf N), (Subgroup.zpowers_le).mpr t.2, ?_, ?_, ?_⟩
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
      · intro h
        rw [Subgroup.zpowers_eq_bot] at h
        rw [h, orderOf_one] at ht2
        norm_num at ht2
      · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
        have hc : (t : N ⧸ P.subgroupOf N) * π ⟨e, hFX heF⟩ = π ⟨e, hFX heF⟩ * t :=
          Subgroup.mem_centralizer_iff.mp hcen t t.2
        have hc' : π ⟨e, hFX heF⟩ * (t : N ⧸ P.subgroupOf N) * (π ⟨e, hFX heF⟩)⁻¹ = t := by
          rw [← hc, mul_assoc]
          simp
        rw [show π ⟨e, hFX heF⟩ * (t : N ⧸ P.subgroupOf N) ^ k * (π ⟨e, hFX heF⟩)⁻¹ =
          (π ⟨e, hFX heF⟩ * (t : N ⧸ P.subgroupOf N) * (π ⟨e, hFX heF⟩)⁻¹) ^ k by
            rw [conj_zpow]]
        rw [hc']
        exact Subgroup.zpow_mem_zpowers _ k
    · obtain ⟨T, hTK, hT2, hTe, hTc⟩ := hAut (N ⧸ P.subgroupOf N) K htypeK
        (π ⟨e, hFX heF⟩) (hFK e heF) he3' hcen
      refine ⟨T, hTK, hT2, ?_, hTe⟩
      rintro rfl
      exact hTc bot_le
  have hCN : ∀ u ∈ Subgroup.centralizer (K : Set (N ⧸ P.subgroupOf N)),
      u ∈ Subgroup.normalizer (T : Set (N ⧸ P.subgroupOf N)) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTK hu)
  set Mg : Subgroup G :=
    ((Subgroup.normalizer (T : Set (N ⧸ P.subgroupOf N))).comap π).map N.subtype with hMg
  have hCMg : C ≤ Mg := fun g hg => ⟨⟨g, hFX (hCF hg)⟩, hCN _ (hCcent g hg), rfl⟩
  have heMg : e ∈ Mg := ⟨⟨e, hFX heF⟩, hTe, rfl⟩
  have hFMg : F ≤ Mg := hFe.trans (sup_le hCMg ((Subgroup.zpowers_le).mpr heMg))
  have hFT : ∀ f ∈ F, ∃ m : N, (m : G) = f ∧ π m ∈ Subgroup.normalizer
      (T : Set (N ⧸ P.subgroupOf N)) := by
    intro f hf
    obtain ⟨m, hm, rfl⟩ := hFMg hf
    exact ⟨m, rfl, hm⟩
  set W' : Subgroup N := T.comap π ⊓ J.subgroupOf N with hW'
  set W : Subgroup G := W'.map N.subtype with hW
  have hWJ : W ≤ J := by
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hn.2
  have hFW : ∀ f ∈ F, ∀ y ∈ W, f * y * f⁻¹ ∈ W := by
    intro f hf y hy
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨m, rfl, hm⟩ := hFT f hf
    have hn1 : π n ∈ T := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hn).1
    have hn2 : (n : G) ∈ J := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hn).2
    refine ⟨m * n * m⁻¹, Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr ?_,
      Subgroup.mem_subgroupOf.mpr ?_⟩, by simp⟩
    · rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hm (π n)).mp hn1
    · have := (Subgroup.mem_normalizer_iff.mp (hFJ hf) (n : G)).mp hn2
      simpa using this
  have hFnormW : F ≤ Subgroup.normalizer (W : Set G) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hFW f hf y
    · intro hy
      have := hFW f⁻¹ (F.inv_mem hf) _ hy
      simpa [mul_assoc] using this
  have hP'card : ¬ 3 ∣ Nat.card (P.subgroupOf N) := by
    have h1 : Nat.card (P.subgroupOf N) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPX.trans hXN)).toEquiv
    have h2 : Nat.card P = Nat.card (aschbacherSolvableCore 3 X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [h1, h2]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hT2
  have hWdvd : Nat.card W' ∣ Nat.card (P.subgroupOf N) * Nat.card T := by
    have h1 : Nat.card W' ∣ Nat.card (T.comap π) := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (T.comap π) = Nat.card (P.subgroupOf N) * Nat.card T :=
      QuotientGroup.card_preimage_mk (P.subgroupOf N) (T : Set (N ⧸ P.subgroupOf N))
    exact h2 ▸ h1
  have hWcop : Nat.Coprime 3 (Nat.card W) := by
    have hcardW : Nat.card W = Nat.card W' := Subgroup.card_map_of_injective N.subtype_injective
    rw [hcardW]
    refine Nat.Coprime.coprime_dvd_right hWdvd ?_
    refine Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP'card) ?_
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h2W : 2 ∣ Nat.card W := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hTne
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq T hk
    have h2T : 2 ∣ Nat.card T := by rw [hk]; exact dvd_pow_self 2 hk0
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2T
    obtain ⟨j, hjJ, hjt⟩ := hKmem t (hTK t.2)
    have hjW : (j : G) ∈ W :=
      ⟨j, Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hjt]; exact t.2),
        Subgroup.mem_subgroupOf.mpr hjJ⟩, rfl⟩
    have hojt : orderOf (π j) = 2 := by rw [hjt, Subgroup.orderOf_coe]; exact ht
    have hdvd1 : orderOf (π j) ∣ orderOf j := orderOf_map_dvd π j
    have hdvd2 : orderOf (j : G) ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hjW
    have hoj : orderOf (j : G) = orderOf j := Subgroup.orderOf_coe j
    rw [hojt] at hdvd1
    exact hdvd1.trans (by rw [← hoj]; exact hdvd2)
  obtain ⟨sylow, hsyl, hsylne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two F W hF3 hFnormW hWcop h2W
  exact ⟨(sylow : Subgroup W).map W.subtype, (Subgroup.map_subtype_le _).trans hWJ, hsylne,
    sylow.isPGroup'.map W.subtype, hsyl⟩

end Hering88C

end CFSG.RankThree.PartTwo.Sec8
