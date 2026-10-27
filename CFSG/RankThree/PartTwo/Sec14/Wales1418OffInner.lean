module

public import CFSG.RankThree.PartTwo.KFacts.KFOut3
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQBUnique
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1418Off

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem relIndex_sup_eq {H N : Subgroup G} (h : H ≤ Subgroup.normalizer (N : Set G)) :
    N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

private theorem eq_one_of_dvd_odd_of_dvd_two_pow {d m n : ℕ} (hm : d ∣ m) (hm2 : ¬ 2 ∣ m)
    (hn : d ∣ 2 ^ n) : d = 1 := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  rcases j with _ | j
  · rfl
  · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans hm) hm2

private theorem le_sup_of_not_two_dvd_relIndex {M S C : Subgroup G} {n : ℕ}
    (hS : ¬ 2 ∣ S.relIndex M) (hC : C.relIndex M ∣ 2 ^ n) : M ≤ S ⊔ C :=
  Subgroup.relIndex_eq_one.mp (eq_one_of_dvd_odd_of_dvd_two_pow
    (Subgroup.relIndex_dvd_of_le_left M le_sup_left) hS
    ((Subgroup.relIndex_dvd_of_le_left M le_sup_right).trans hC))

private theorem le_of_isPGroup_two_of_relIndex {M Q P : Subgroup G} (hQM : Q ≤ M)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hQ : ¬ 2 ∣ Q.relIndex M)
    (hP : IsPGroup 2 P) (hPM : P ≤ M) : P ≤ Q := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have h1 : Q.relIndex (P ⊔ Q) ∣ Q.relIndex M :=
    ⟨_, (Subgroup.relIndex_mul_relIndex Q (P ⊔ Q) M le_sup_right (sup_le hPM hQM)).symm⟩
  have h2 : Q.relIndex (P ⊔ Q) ∣ 2 ^ k := by
    rw [relIndex_sup_eq (hPM.trans hMQ), ← hk]
    exact Subgroup.relIndex_dvd_card Q P
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp (eq_one_of_dvd_odd_of_dvd_two_pow h1 hQ h2))

private theorem conj_mem_sup_of_mem_normalizer {H L : Subgroup G} {g x : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hL : g ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ H ⊔ L) : g * x * g⁻¹ ∈ H ⊔ L := by
  have hle : H ⊔ L ≤ (H ⊔ L).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun h hh => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hH h).mp hh))
      (fun l hl => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hL l).mp hl))
  exact hle hx

private theorem inf_sup_eq_of_le_sup {K R C : Subgroup G}
    (hKC : K ≤ Subgroup.normalizer (C : Set G)) (hRKC : R ≤ K ⊔ C) :
    (R ⊔ C) ⊓ K ⊔ C = R ⊔ C := by
  refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le (fun r hr => ?_) le_sup_right)
  have hr' : r ∈ ((K ⊔ C : Subgroup G) : Set G) := hRKC hr
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K C hKC] at hr'
  obtain ⟨k, hk, c, hc, rfl⟩ := hr'
  have hkM : k ∈ (R ⊔ C) ⊓ K := by
    refine ⟨?_, hk⟩
    have h := (R ⊔ C).mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right (inv_mem hc))
    rwa [mul_inv_cancel_right] at h
  exact ((R ⊔ C) ⊓ K ⊔ C).mul_mem (Subgroup.mem_sup_left hkM) (Subgroup.mem_sup_right hc)

private theorem relIndex_dvd_card_of_le_sup {K R C : Subgroup G}
    (hKC : K ≤ Subgroup.normalizer (C : Set G)) (hRC : R ≤ Subgroup.normalizer (C : Set G))
    (hRKC : R ≤ K ⊔ C) : C.relIndex ((R ⊔ C) ⊓ K) ∣ Nat.card R := by
  rw [← relIndex_sup_eq (inf_le_right.trans hKC), inf_sup_eq_of_le_sup hKC hRKC,
    relIndex_sup_eq hRC]
  exact Subgroup.relIndex_dvd_card C R

theorem thetaQuotCentralizer_le_normalizer_of_theta_le {K Q : Subgroup G}
    (hθQ : inSubgroup (aschbacherSolvableCore 3) K ≤ Q) (hQK : Q ≤ K) :
    thetaQuotCentralizer K ≤ Subgroup.normalizer (Q : Set G) := fun c hc =>
  Subgroup.mem_normalizer_fintype fun x hx => by
    have h := Q.mul_mem hx (hθQ ((mem_thetaQuotCentralizer_iff.mp hc).2 x (hQK hx)))
    rwa [mul_inv_cancel_left] at h

theorem not_three_dvd_card_sup_theta {K S : Subgroup G} (hS : IsPGroup 2 S) (hSK : S ≤ K) :
    ¬ 3 ∣ Nat.card (S ⊔ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) := by
  have hc := Subgroup.relIndex_mul_card (inSubgroup (aschbacherSolvableCore 3) K)
    (S ⊔ inSubgroup (aschbacherSolvableCore 3) K)
  rw [inf_of_le_left le_sup_right, relIndex_sup_eq (hSK.trans (le_normalizer_theta K))] at hc
  rw [← hc]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  refine Nat.prime_three.not_dvd_mul (fun h => ?_) (theta_solvable_and_not_dvd K).2
  have h2 : 3 ∣ 2 ^ k := hk ▸ h.trans (Subgroup.relIndex_dvd_card _ S)
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h2) (by norm_num)


theorem exists_invariant_twoSubgroup_cover {K R A : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hRKC : R ≤ K ⊔ thetaQuotCentralizer K) :
    ∃ R₁ : Subgroup G, R₁ ≤ K ∧ IsPGroup 2 R₁ ∧ A ≤ Subgroup.normalizer (R₁ : Set G) ∧
      R ≤ R₁ ⊔ thetaQuotCentralizer K := by
  have hNC := normalizer_le_normalizer_thetaQuotCentralizer K
  have hKC : K ≤ Subgroup.normalizer (thetaQuotCentralizer K : Set G) :=
    Subgroup.le_normalizer.trans hNC
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
  set M := (R ⊔ thetaQuotCentralizer K) ⊓ K
  have hMK : M ≤ K := inf_le_right
  have hMC : (thetaQuotCentralizer K).relIndex M ∣ 2 ^ n :=
    (relIndex_dvd_card_of_le_sup hKC (hRK.trans hNC) hRKC).trans (dvd_of_eq hn)
  have hθM : inSubgroup (aschbacherSolvableCore 3) K ≤ M :=
    le_inf ((theta_le_thetaQuotCentralizer K).trans le_sup_right) (theta_le K)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun x hx =>
      ⟨conj_mem_sup_of_mem_normalizer (hAR ha) (hNC (hAK ha)) hx.1,
        (Subgroup.mem_normalizer_iff.mp (hAK ha) x).mp hx.2⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  set S : Subgroup G := (P : Subgroup M).map M.subtype
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := P.isPGroup'.map _
  have hSi : ¬ 2 ∣ S.relIndex M := by
    have h : S.subgroupOf M = (P : Subgroup M) :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [Subgroup.relIndex, h]
    exact P.not_dvd_index
  have hMSC : M ≤ S ⊔ thetaQuotCentralizer K := le_sup_of_not_two_dvd_relIndex hSi hMC
  set Q := S ⊔ inSubgroup (aschbacherSolvableCore 3) K
  have hQM : Q ≤ M := sup_le hSM hθM
  have hQK : Q ≤ K := hQM.trans hMK
  have hQ3 : ¬ 3 ∣ Nat.card Q := not_three_dvd_card_sup_theta hS2 (hSM.trans hMK)
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    hMSC.trans (sup_le (le_sup_left.trans Subgroup.le_normalizer)
      (thetaQuotCentralizer_le_normalizer_of_theta_le le_sup_right hQK))
  have hQi : ¬ 2 ∣ Q.relIndex M := fun h =>
    hSi (h.trans (Subgroup.relIndex_dvd_of_le_left M le_sup_left))
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := by
    intro a ha
    have hle : Q ≤ Q.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (fun s hs => ?_) (fun t ht => ?_)
      · have hPM : S.map (MulAut.conj a).toMonoidHom ≤ M := by
          rintro _ ⟨s', hs', rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp (hAM ha) s').mp (hSM hs')
        exact le_of_isPGroup_two_of_relIndex hQM hMQ hQi (hS2.map _) hPM ⟨s, hs, rfl⟩
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (normalizer_le_normalizer_theta K (hAK ha)) t).mp ht)
    exact Subgroup.mem_normalizer_fintype fun x hx => hle hx
  obtain ⟨R₁, hR₁Q, hR₁2, hAR₁, hR₁card⟩ :=
    Ronan1422IQB.exists_invariant_sylow_of_three hA3 hQ3 hAQ Nat.prime_two
  have hR₁i : ¬ 2 ∣ R₁.relIndex M := by
    rw [← Subgroup.relIndex_mul_relIndex R₁ Q M hR₁Q hQM]
    refine Nat.prime_two.not_dvd_mul (fun h => ?_) hQi
    have hc := Subgroup.relIndex_mul_card R₁ Q
    rw [inf_of_le_left hR₁Q, hR₁card] at hc
    refine Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := ↥Q)).ne' Nat.prime_two ?_
    calc 2 ^ ((Nat.card Q).factorization 2 + 1)
        = 2 ^ (Nat.card Q).factorization 2 * 2 := pow_succ _ _
      _ ∣ 2 ^ (Nat.card Q).factorization 2 * R₁.relIndex Q := mul_dvd_mul_left _ h
      _ = Nat.card Q := by rw [mul_comm]; exact hc
  have hMR₁C : M ≤ R₁ ⊔ thetaQuotCentralizer K := le_sup_of_not_two_dvd_relIndex hR₁i hMC
  refine ⟨R₁, hR₁Q.trans hQK, hR₁2, hAR₁, ?_⟩
  calc R ≤ R ⊔ thetaQuotCentralizer K := le_sup_left
    _ = M ⊔ thetaQuotCentralizer K := (inf_sup_eq_of_le_sup hKC hRKC).symm
    _ ≤ R₁ ⊔ thetaQuotCentralizer K := sup_le hMR₁C le_sup_right

theorem le_thetaQuotCentralizer_of_le_sup {K R R₁ : Subgroup G} {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hR₁K : R₁ ≤ K)
    (hRb : ⁅R, Subgroup.zpowers b⁆ = R) (hRR₁ : R ≤ R₁ ⊔ thetaQuotCentralizer K)
    (hR₁b : ⁅R₁, Subgroup.zpowers b⁆ ≤ thetaQuotCentralizer K) :
    R ≤ thetaQuotCentralizer K := by
  have hR₁C : R₁ ≤ Subgroup.normalizer (thetaQuotCentralizer K : Set G) :=
    (hR₁K.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_thetaQuotCentralizer K)
  rw [← hRb, Subgroup.commutator_le]
  intro r hr y hy
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hbK hy
  have hr' : r ∈ ((R₁ ⊔ thetaQuotCentralizer K : Subgroup G) : Set G) := hRR₁ hr
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hR₁C] at hr'
  obtain ⟨x, hx, c, hc, rfl⟩ := hr'
  have hcy : ⁅c, y⁆ ∈ thetaQuotCentralizer K := by
    have h := (thetaQuotCentralizer K).mul_mem hc
      (conj_mem_thetaQuotCentralizer (inv_mem hc) hyN)
    rwa [commutatorElement_def, show c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) by group]
  have hxy : ⁅x, y⁆ ∈ thetaQuotCentralizer K := hR₁b (Subgroup.commutator_mem_commutator hx hy)
  have e : ⁅x * c, y⁆ = x * ⁅c, y⁆ * x⁻¹ * ⁅x, y⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (thetaQuotCentralizer K).mul_mem
    (conj_mem_thetaQuotCentralizer hcy (Subgroup.le_normalizer (hR₁K hx))) hxy

theorem exists_inner_twoSubgroup {K R A : Subgroup G} {b : G}
    (hA3 : IsPGroup 3 A) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hbA : b ∈ A)
    (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRb : ⁅R, Subgroup.zpowers b⁆ = R)
    (hRθ : ¬ R ≤ thetaQuotCentralizer K) (hRKC : R ≤ K ⊔ thetaQuotCentralizer K) :
    ∃ R' ∈ invariantPiSubgroups K A (piOf 2), R' ≠ ⊥ ∧ ⁅R', Subgroup.zpowers b⁆ = R' ∧
      ¬ R' ≤ thetaQuotCentralizer K := by
  obtain ⟨R₁, hR₁K, hR₁2, hAR₁, hRR₁⟩ :=
    exists_invariant_twoSubgroup_cover hA3 hAK hR2 hAR hRK hRKC
  have hbR₁ : Subgroup.zpowers b ≤ Subgroup.normalizer (R₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hAR₁ hbA)
  have hR'R₁ : ⁅R₁, Subgroup.zpowers b⁆ ≤ R₁ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hbR₁
  have hR₁3 : ¬ 3 ∣ Nat.card R₁ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR₁2
    rw [hk]
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hR'C : ¬ ⁅R₁, Subgroup.zpowers b⁆ ≤ thetaQuotCentralizer K := fun h =>
    hRθ (le_thetaQuotCentralizer_of_le_sup (hAK hbA) hR₁K hRb hRR₁ h)
  have hAR' : A ≤ Subgroup.normalizer ((⁅R₁, Subgroup.zpowers b⁆ : Subgroup G) : Set G) := by
    intro a ha
    have hle : ⁅R₁, Subgroup.zpowers b⁆ ≤
        (⁅R₁, Subgroup.zpowers b⁆ : Subgroup G).comap (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hay : a * y * a⁻¹ = y := by
        rw [hAc a ha y (Subgroup.zpowers_le.mpr hbA hy), mul_inv_cancel_right]
      show a * ⁅x, y⁆ * a⁻¹ ∈ ⁅R₁, Subgroup.zpowers b⁆
      rw [show a * ⁅x, y⁆ * a⁻¹ = ⁅a * x * a⁻¹, a * y * a⁻¹⁆ by
        simp only [commutatorElement_def]; group, hay]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hAR₁ ha) x).mp hx) hy
    exact Subgroup.mem_normalizer_fintype fun x hx => hle hx
  refine ⟨⁅R₁, Subgroup.zpowers b⁆, (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
    ⟨hR'R₁.trans hR₁K, hR₁2.to_le hR'R₁, hAR'⟩, fun h => hR'C (by rw [h]; exact bot_le), ?_,
    hR'C⟩
  exact CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
    (Subgroup.zpowers b) R₁ (hA3.to_le (Subgroup.zpowers_le.mpr hbA)) hR₁3 hbR₁

theorem exists_inner_twoSubgroup_of_kfOut3 (hOut : KFacts.KFOut3) {K R A : Subgroup G} {b : G}
    (hKp : Group.IsPerfect K) (hKq : CFSG.IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (hK46 : IsList46 (K ⧸ aschbacherSolvableCore 3 K))
    (hA3 : IsPGroup 3 A) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hbA : b ∈ A)
    (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRb : ⁅R, Subgroup.zpowers b⁆ = R)
    (hRθ : ¬ R ≤ thetaQuotCentralizer K) :
    ∃ R' ∈ invariantPiSubgroups K A (piOf 2), R' ≠ ⊥ ∧ ⁅R', Subgroup.zpowers b⁆ = R' ∧
      ¬ R' ≤ thetaQuotCentralizer K :=
  exists_inner_twoSubgroup hA3 hAc hAK hbA hR2 hAR hRK hRb hRθ
    (hOut G K hKp hKq hK46 b (hAK hbA) (hA3.to_le (Subgroup.zpowers_le.mpr hbA)) R hR2 hRK
      (hAR hbA) hRb)

end CFSG.RankThree.PartTwo.Sec14.Wales1418Off
