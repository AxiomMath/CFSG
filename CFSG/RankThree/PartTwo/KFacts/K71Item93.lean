module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3Normal
public import CFSG.RankThree.PartTwo.Sec9.Notation
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.KFacts.K73Lines
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.Asc83Table.E9

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem forall_of_thetaQuotMulAut_compAction_eq_one {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : thetaQuotMulAut L (compAction L ⟨x, hx⟩) = 1) :
    ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype := by
  intro y hy
  have h1 := DFunLike.congr_fun h ((⟨y, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
  rw [thetaQuotMulAut_mk, MulAut.one_apply] at h1
  refine ⟨_, QuotientGroup.eq_iff_div_mem.mp h1, ?_⟩
  rw [map_div, div_eq_mul_inv]
  rfl

theorem exists_mem_of_fixed_of_pow_three {A : Subgroup G}
    (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {x : L ⧸ aschbacherSolvableCore 3 L}
    (hx3 : x ^ 3 = 1)
    (hfix : ∀ y (hy : y ∈ A), thetaQuotMulAut L (compAction L ⟨y, hAL hy⟩) x = x) :
    ∃ (d : G) (hdL : d ∈ L), d ∈ A ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩ = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) x
  have hx3' : (l : L ⧸ aschbacherSolvableCore 3 L) ^ 3 = 1 := hx3
  set φ : A →* MulAut L := (compAction L).comp (Subgroup.inclusion hAL) with hφ
  have hP : IsPGroup 3 A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hAel.2 g g.2)⟩
  have hφN : ∀ g, ∀ n ∈ aschbacherSolvableCore 3 L, φ g n ∈ aschbacherSolvableCore 3 L := by
    intro g n hn
    rw [← map_aschbacherSolvableCore (φ g)]
    exact ⟨n, hn, rfl⟩
  have hy : ∀ g, ((φ g l : L) : L ⧸ aschbacherSolvableCore 3 L) =
      (l : L ⧸ aschbacherSolvableCore 3 L) := by
    intro g
    have h1 := hfix g g.2
    rw [QuotientGroup.mk'_apply, thetaQuotMulAut_mk] at h1
    exact h1
  obtain ⟨l', hl'q, hl'fix⟩ := exists_fixed_of_coprime hP φ (aschbacherSolvableCore 3 L)
    (not_three_dvd_card_aschbacherSolvableCore L) hφN l hy
  have hn3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    not_three_dvd_card_aschbacherSolvableCore L
  have hnn : Nat.card (aschbacherSolvableCore 3 L) ^ 2 % 3 = 1 := by
    have : Nat.card (aschbacherSolvableCore 3 L) % 3 = 1 ∨
        Nat.card (aschbacherSolvableCore 3 L) % 3 = 2 := by omega
    rcases this with h1 | h1 <;> rw [Nat.pow_mod, h1]
  obtain ⟨d, hd⟩ : ∃ d : L, d = l' ^ (Nat.card (aschbacherSolvableCore 3 L) ^ 2) := ⟨_, rfl⟩
  have hdq : (d : L ⧸ aschbacherSolvableCore 3 L) = (l : L ⧸ aschbacherSolvableCore 3 L) := by
    rw [hd, QuotientGroup.mk_pow, hl'q, pow_eq_pow_mod _ hx3', hnn, pow_one]
  have hd3 : d ^ 3 = 1 := by
    have h1 : l' ^ 3 ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hl'q]
      exact hx3'
    have h2 : (l' ^ 3) ^ Nat.card (aschbacherSolvableCore 3 L) = 1 := by
      have h3 := congrArg Subtype.val
        (pow_card_eq_one' (G := aschbacherSolvableCore 3 L) (x := ⟨l' ^ 3, h1⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [hd, ← pow_mul, mul_comm _ 3, pow_mul, sq, pow_mul, h2, one_pow]
  have hdfix : ∀ g : A, φ g d = d := fun g => by rw [hd, map_pow, hl'fix g]
  have hdA : ∀ g ∈ A, g * (d : G) = (d : G) * g := by
    intro g hg
    have h1 := congrArg Subtype.val (hdfix ⟨g, hg⟩)
    change g * (d : G) * g⁻¹ = d at h1
    calc g * (d : G) = g * (d : G) * g⁻¹ * g := by rw [inv_mul_cancel_right]
      _ = (d : G) * g := by rw [h1]
  set D := Subgroup.zpowers (d : G) with hD
  have hDN : D ≤ Subgroup.normalizer (A : Set G) := by
    rw [hD, Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => hdA g hg)
  have hdecomp : ∀ z ∈ A ⊔ D, ∃ w ∈ D, ∃ u ∈ A, w * u = z := by
    intro z hz
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D A hDN] at hz
    obtain ⟨w, hw, u, hu, rfl⟩ := hz
    exact ⟨w, hw, u, hu, rfl⟩
  have hcommD : ∀ w ∈ D, ∀ u ∈ A, w * u = u * w := by
    intro w hw u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((show Commute (d : G) u from (hdA u hu).symm).zpow_left k).eq
  have hdG3 : (d : G) ^ 3 = 1 := by
    have h1 := congrArg Subtype.val hd3
    simpa using h1
  have hDexp : ∀ w ∈ D, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdG3, one_zpow]
  have hDcomm : ∀ w ∈ D, ∀ w' ∈ D, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    exact (Commute.zpow_zpow_self (d : G) k k').eq
  have hAcomm : ∀ u ∈ A, ∀ u' ∈ A, u * u' = u' * u := fun u hu u' hu' =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
  have hel : CFSG.Assembly.IsElemAbelian 3 (A ⊔ D) := by
    refine ⟨⟨⟨fun z z' => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨w, hw, u, hu, hwu⟩ := hdecomp z z.2
      obtain ⟨w', hw', u', hu', hwu'⟩ := hdecomp z' z'.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hwu, ← hwu']
      have h1 : Commute (w * u) (w' * u') := by
        apply Commute.mul_left
        · exact (show Commute w w' from hDcomm w hw w' hw').mul_right
            (show Commute w u' from hcommD w hw u' hu')
        · exact (show Commute u w' from (hcommD w' hw' u hu).symm).mul_right
            (show Commute u u' from hAcomm u hu u' hu')
      exact h1.eq
    · obtain ⟨w, hw, u, hu, rfl⟩ := hdecomp z hz
      rw [(show Commute w u from hcommD w hw u hu).mul_pow, hDexp w hw, hAel.2 u hu, one_mul]
  have hAD := hAmax _ hel le_sup_left
  have hdAmem : (d : G) ∈ A := by
    rw [← hAD]
    exact (le_sup_right : D ≤ A ⊔ D) (Subgroup.mem_zpowers _)
  exact ⟨d, d.2, hdAmem, hdq⟩

theorem mulAut_pow_apply_eq {S : Type*} [Group S] {φ : MulAut S} {x : S} (hx : φ x = x)
    (n : ℕ) : (φ ^ n) x = x := by
  induction n with
  | zero => rw [pow_zero, MulAut.one_apply]
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

theorem mem_zpowers_of_thetaQuotMulAut_eq_one {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) {y : G} (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hyA : y ∈ A) (h1 : thetaQuotMulAut L (compAction L ⟨y, hy⟩) = 1) :
    y ∈ Subgroup.zpowers c := by
  have h2 : y ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [Late.sectionCentralizer]
    exact ⟨hyA, forall_of_thetaQuotMulAut_compAction_eq_one hy h1⟩
  rw [hyp.sectionCentralizer_eq] at h2
  exact h2

theorem thetaQuotMulAut_compAction_eq_one_of_hyp81 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (hcN : c ∈ Subgroup.normalizer (L : Set G)) :
    thetaQuotMulAut L (compAction L ⟨c, hcN⟩) = 1 := by
  have h2 : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [hyp.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  rw [Late.sectionCentralizer] at h2
  obtain ⟨-, h2'⟩ := h2
  exact thetaQuotMulAut_compAction_eq_one_of_forall hcN h2'

theorem exists_su38_model_of_hyp92_one {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp92 G A c L a R 1) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 3 K)
      (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3) (σ : K ≃+* K)
      (B : unitaryIsom3 h) (b : G) (hbA : b ∈ A),
      orderOf σ = 3 ∧ inducedAutHom L e ⟨b, hAL hbA⟩ = suConj h B ∧
      suConj h B * suField h σ = suField h σ * suConj h B ∧ suConj h B ^ 3 = 1 ∧
      suConj h B ≠ 1 ∧ ∀ y (hy : y ∈ A), ∃ i j : ℕ,
        inducedAutHom L e ⟨y, hAL hy⟩ = suConj h B ^ i * suField h σ ^ j := by
  have hAel := hyp.mem_partTwoF.1
  have hA3 : ∀ y ∈ A, y ^ 3 = 1 := hAel.2
  have hAcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := hyp.mem_A
  have haA := hyp.a_mem
  have hcN := hAL hcA
  have haN := hAL haA
  have hc3 := hA3 c hcA
  have ha3 := hA3 a haA
  have hL : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ 3) := by
    obtain ⟨K₀, _, _, h1 | h1⟩ := hyp.isSLThreePiAt
    · exact absurd h1.2.1 (by norm_num)
    · exact ⟨K₀, inferInstance, inferInstance, h1.1, h1.2.2⟩
  have hm3 : 3 ∣ 2 ^ 3 + 1 := by norm_num
  have ha : InducesStdKind L a .field := by
    rcases hyp.inducesStdKind with h1 | h1
    · exact h1
    · exact absurd h1 (not_inducesStdKind_graphField_of_isoSUThree le_rfl hm3 hL)
  obtain ⟨K, _, h, hq, e, haN', hfield⟩ := inducesKindSU3_of_inducesStdKind le_rfl hm3 hL ha
  have := h.finite
  have hβ3 : inducedAutHom L e ⟨a, haN'⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e haN' ha3
  have hα3 : suDescend h hq (inducedAutHom L e ⟨a, haN'⟩) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hD : suDescend h hq (inducedAutHom L e ⟨a, haN'⟩) ∉ (psuConj h).range :=
    (stdPinnedPSU3_separated h).not_mem_inndiag_of_isField hfield
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq _ hα3 hD
  have hlift : inducedAutHom L e ⟨a, haN'⟩ = suConj h H * suField h σ * (suConj h H)⁻¹ := by
    apply eq_of_suDescend_eq h hq
    rw [hαH, map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suField]
  set e' := e.trans (suConj h H).symm with he'
  have hee' : e.symm.trans e' = (suConj h H)⁻¹ := by
    refine MulEquiv.ext fun m => ?_
    rw [he', MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hγ : ∀ y, inducedAutHom L e' y = (suConj h H)⁻¹ * inducedAutHom L e y * suConj h H := by
    intro y
    rw [inducedAutHom_eq_conj L e e' y, hee', inv_inv]
  have hγa : inducedAutHom L e' ⟨a, haN⟩ = suField h σ := by
    rw [hγ, hlift]
    group
  have hcτ := thetaQuotMulAut_compAction_eq_one_of_hyp81 hyp.toHyp81 hcN
  set S := Subgroup.closure ({c, a} : Set G) with hS
  have hca : c * a = a * c := hAcomm c hcA a haA
  have hcS : c ∈ S := Subgroup.subset_closure (by simp)
  have haS : a ∈ S := Subgroup.subset_closure (by simp)
  have hS9 : Nat.card S ≤ 9 := by
    have hsurj : Function.Surjective (fun ij : Fin 3 × Fin 3 =>
        (⟨c ^ (ij.1 : ℕ) * a ^ (ij.2 : ℕ), mul_mem (pow_mem hcS _) (pow_mem haS _)⟩ : S)) := by
      rintro ⟨z, hz⟩
      obtain ⟨i, j, hi, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hz
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
    calc Nat.card S ≤ Nat.card (Fin 3 × Fin 3) := Nat.card_le_card_of_surjective _ hsurj
      _ = 9 := by simp
  have hSA : S ≤ A := by
    rw [hS, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact haA
  obtain ⟨b, hbA, hbS⟩ : ∃ b ∈ A, b ∉ S := by
    by_contra hcon
    have h0 : A ≤ S := fun y hy => by
      by_contra hyS
      exact hcon ⟨y, hy, hyS⟩
    have h1 := Subgroup.card_le_of_le h0
    rw [hyp.card_eq] at h1
    omega
  have hbN := hAL hbA
  have hγb3 : inducedAutHom L e' ⟨b, hbN⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e' hbN (hA3 b hbA)
  have hγba : inducedAutHom L e' ⟨b, hbN⟩ * suField h σ =
      suField h σ * inducedAutHom L e' ⟨b, hbN⟩ := by
    rw [← hγa, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm b hbA a haA)
  obtain ⟨B, k, -, hγbB, hBcomm, hB3⟩ := exists_suConj_mul_suField_pow h hq hσ3 hγb3 hγba
  obtain ⟨b', hb'⟩ : ∃ b' : G, b' = b * (a ^ k)⁻¹ := ⟨_, rfl⟩
  have hbb' : b = b' * a ^ k := by rw [hb', inv_mul_cancel_right]
  have hb'A : b' ∈ A := by rw [hb']; exact mul_mem hbA (inv_mem (pow_mem haA k))
  have hb'N := hAL hb'A
  have hγb' : inducedAutHom L e' ⟨b', hb'N⟩ = suConj h B := by
    have h1 : (⟨b', hb'N⟩ : Subgroup.normalizer (L : Set G)) = ⟨b, hbN⟩ * (⟨a, haN⟩ ^ k)⁻¹ :=
      Subtype.ext (by simp [hb'])
    rw [h1, map_mul, map_inv, map_pow, hγa, hγbB, mul_inv_cancel_right]
  have hb'S : b' ∉ S := fun h1 => hbS (by rw [hbb']; exact mul_mem h1 (pow_mem haS k))
  have hB1 : suConj h B ≠ 1 := by
    intro h1
    have h2 : thetaQuotMulAut L (compAction L ⟨b', hb'N⟩) = 1 := by
      have h3 : inducedAutHom L e' ⟨b', hb'N⟩ = 1 := hγb'.trans h1
      rw [inducedAutHom_apply] at h3
      exact (MulAut.congr e').injective (h3.trans (map_one _).symm)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_thetaQuotMulAut_eq_one hyp.toHyp81 hb'N hb'A h2)
    apply hb'S
    rw [← hm]
    exact zpow_mem hcS m
  have hac : a ∉ Subgroup.zpowers c := by
    intro h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hD
    have h2 : inducedAutHom L e ⟨a, haN'⟩ = 1 := by
      have h3 : (⟨a, haN'⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ m :=
        Subtype.ext (by simp [hm])
      rw [h3, map_zpow, inducedAutHom_apply, hcτ, map_one, one_zpow]
    rw [h2, map_one]
    exact Subgroup.one_mem _
  have hS9' : Nat.card S = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca hyp.ne_one hac
  set T := S ⊔ Subgroup.zpowers b' with hT
  have hTA : T ≤ A := sup_le hSA (Subgroup.zpowers_le.mpr hb'A)
  have hST : S ≤ T := le_sup_left
  have hb'T : b' ∈ T := (le_sup_right : Subgroup.zpowers b' ≤ T) (Subgroup.mem_zpowers b')
  have hTeq : T = A := by
    have h1 : Nat.card S ∣ Nat.card T := Subgroup.card_dvd_of_le hST
    have h2 : Nat.card T ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hyp.card_eq]
      exact Subgroup.card_dvd_of_le hTA
    have h3 : Nat.card T ≠ 9 := by
      intro h4
      apply hb'S
      have h5 : S = T := Subgroup.eq_of_le_of_card_ge hST (by rw [h4, hS9'])
      rw [h5]
      exact hb'T
    rw [hS9'] at h1
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    have hT27 : Nat.card T = 27 := by
      rw [hj'] at h1 h3 ⊢
      interval_cases j
      · norm_num at h1
      · norm_num at h1
      · exact absurd (by norm_num) h3
      · norm_num
    exact Subgroup.eq_of_le_of_card_ge hTA (by rw [hT27, hyp.card_eq])
  set Q : Subgroup G := ((Subgroup.closure ({suConj h B, suField h σ} :
      Set (MulAut (unitarySU 2 3 K 3)))).comap (inducedAutHom L e')).map
      (Subgroup.normalizer (L : Set G)).subtype with hQ
  have hmemQ : ∀ y (hy : y ∈ Subgroup.normalizer (L : Set G)), inducedAutHom L e' ⟨y, hy⟩ ∈
      Subgroup.closure ({suConj h B, suField h σ} : Set (MulAut (unitarySU 2 3 K 3))) →
      y ∈ Q := fun y hy h1 => ⟨⟨y, hy⟩, h1, rfl⟩
  have hcQ : c ∈ Q := hmemQ c hcN (by rw [inducedAutHom_apply, hcτ, map_one]; exact one_mem _)
  have haQ : a ∈ Q := hmemQ a haN (by rw [hγa]; exact Subgroup.subset_closure (by simp))
  have hb'Q : b' ∈ Q := hmemQ b' hb'N (by rw [hγb']; exact Subgroup.subset_closure (by simp))
  have hAQ : A ≤ Q := by
    rw [← hTeq, hT]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hb'Q)
    rw [hS, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcQ
    · exact haQ
  have hσ3' : suField h σ ^ 3 = 1 := by
    rw [← map_pow, show σ ^ 3 = 1 by rw [← hσ3]; exact pow_orderOf_eq_one σ, map_one]
  refine ⟨K, inferInstance, h, e', σ, B, b', hb'A, hσ3, hγb', hBcomm, hB3, hB1, fun y hy => ?_⟩
  obtain ⟨⟨y', hy'N⟩, hy'Q, rfl⟩ := hAQ hy
  have hy'Q' : inducedAutHom L e' ⟨y', hy'N⟩ ∈
      Subgroup.closure ({suConj h B, suField h σ} : Set (MulAut (unitarySU 2 3 K 3))) := hy'Q
  obtain ⟨i, j, -, -, hij⟩ := exists_pow_mul_pow_of_mem_closure_pair hBcomm hB3 hσ3' hy'Q'
  exact ⟨i, j, hij⟩

theorem exists_mem_inducedAutHom_eq_conj_of_fixed {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp92 G A c L a R 1) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] {h : UnitaryFieldData 2 3 K}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3) {σ : K ≃+* K} {B : unitaryIsom3 h}
    (hA : ∀ y (hy : y ∈ A), ∃ i j : ℕ,
      inducedAutHom L e ⟨y, hAL hy⟩ = suConj h B ^ i * suField h σ ^ j)
    {x : unitarySU 2 3 K 3} (hx3 : x ^ 3 = 1) (hσx : suField h σ x = x)
    (hBx : suConj h B x = x) :
    ∃ (d : G) (hdA : d ∈ A), inducedAutHom L e ⟨d, hAL hdA⟩ = MulAut.conj x := by
  obtain ⟨xbar, hxbar⟩ : ∃ xbar, xbar = e.symm x := ⟨_, rfl⟩
  have hxbar3 : xbar ^ 3 = 1 := by rw [hxbar, ← map_pow, hx3, map_one]
  have hfix : ∀ y (hy : y ∈ A), thetaQuotMulAut L (compAction L ⟨y, hAL hy⟩) xbar = xbar := by
    intro y hy
    obtain ⟨i, j, hij⟩ := hA y hy
    have h1 : inducedAutHom L e ⟨y, hAL hy⟩ x = x := by
      rw [hij, MulAut.mul_apply, mulAut_pow_apply_eq hσx, mulAut_pow_apply_eq hBx]
    rw [inducedAutHom_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply] at h1
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    rw [hxbar]
    exact h2
  obtain ⟨d, hdL, hdA, hdx⟩ :=
    exists_mem_of_fixed_of_pow_three hyp.mem_partTwoF.1 hyp.mem_partTwoF.2.1 hAL hxbar3 hfix
  refine ⟨d, hdA, ?_⟩
  rw [inducedAutHom_eq_conj_of_mem e hdL (hAL hdA), hdx, hxbar, MulEquiv.apply_symm_apply]

theorem not_invTwoBarNontrivial_of_hyp92_one {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp92 G A c L a R 1) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ¬ Sec8.InvTwoBarNontrivial A L := by
  obtain ⟨K, _, h, e, σ, B, b, hbA, hσ3, hγb, hBσ, hB3, hB1, hA⟩ :=
    exists_su38_model_of_hyp92_one hyp hAL
  have hPi : PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [h.card]; rfl⟩
  have hq3 : ModThree false (2 ^ 3) := by
    show 2 ^ 3 % 3 = 2
    norm_num
  rcases su38_dichotomy h hσ3 B hBσ hB3 hB1 with ⟨w, hw3, hws, hBw⟩ | ⟨x, hx3, hxs, hσx, hBx⟩
  ·
    exact not_invTwoBarNontrivial_of_inducedAutHom_eq_conj hPi hq3 e hbA (hAL hbA) w hw3 hws
      (hγb.trans hBw)
  ·
    obtain ⟨d, hdA, hγd⟩ := exists_mem_inducedAutHom_eq_conj_of_fixed hyp hAL e hA hx3 hσx hBx
    exact not_invTwoBarNontrivial_of_inducedAutHom_eq_conj hPi hq3 e hdA (hAL hdA) x hx3 hxs hγd

end CFSG.RankThree.PartTwo.KFacts
