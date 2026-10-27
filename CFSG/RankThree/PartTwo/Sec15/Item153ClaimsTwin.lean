module

public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

theorem four_le_pRank_of_noncomm {H : Type*} [Group H] [Finite H] (x k : Fin 4 → H)
    (hx3 : ∀ i, x i ^ 3 = 1) (hxx : ∀ i j, Commute (x i) (x j))
    (hkx : ∀ i j, i ≠ j → Commute (k i) (x j)) (hkn : ∀ i, ¬ Commute (k i) (x i)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : ∀ i, x i ≠ 1 := fun i h => hkn i (h ▸ Commute.one_right _)
  have hord : ∀ i, Nat.card (Subgroup.zpowers (x i)) = 3 := fun i => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hx3 i) (hx1 i)]
  have hcomm : Pairwise fun i j : Fin 4 => ∀ a b : H,
      a ∈ Subgroup.zpowers (x i) → b ∈ Subgroup.zpowers (x j) → Commute a b := by
    intro i j _ a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hxx i j).zpow_zpow m n
  have hind : iSupIndep fun i => Subgroup.zpowers (x i) := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨hzi, hzj⟩
    rw [Subgroup.mem_bot]
    have hle : (⨆ (j) (_ : j ≠ i), Subgroup.zpowers (x j)) ≤
        Subgroup.centralizer ({k i} : Set H) :=
      iSup₂_le fun j hj => Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (hkx i j (Ne.symm hj)).eq.symm)
    have hzk : Commute (k i) z := (Subgroup.mem_centralizer_singleton_iff.mp (hle hzj)).symm
    by_contra hz1
    have hzz : Subgroup.zpowers z = Subgroup.zpowers (x i) := by
      have hle' : Subgroup.zpowers z ≤ Subgroup.zpowers (x i) := Subgroup.zpowers_le.mpr hzi
      have hcard : Nat.card (Subgroup.zpowers z) = 3 := by
        have hdvd := Subgroup.card_dvd_of_le hle'
        rw [hord i] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd (Subgroup.zpowers_eq_bot.mp (Subgroup.eq_bot_of_card_eq _ h1)) hz1
        · exact h3
      exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hcard, hord i])
    have hxz : x i ∈ Subgroup.zpowers z := hzz ▸ Subgroup.mem_zpowers (x i)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxz
    exact hkn i (hm ▸ hzk.zpow_right m)
  have hf := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_
    (Subgroup.noncommPiCoprod hcomm) hf le_top
  · intro a b
    funext i
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (a i).2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (b i).2
    change ((a i : H)) * (b i : H) = (b i : H) * (a i : H)
    rw [← hm, ← hn]
    exact ((Commute.refl (x i)).zpow_zpow m n).eq
  · intro a
    funext i
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (a i).2
    change (a i : H) ^ 3 = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3 i, one_zpow]
  · rw [Nat.card_pi]
    simp only [hord]
    norm_num

theorem four_le_pRank_of_thetaComponents {H : Type*} [Group H] [Finite H]
    (Y : Fin 4 → Subgroup H) (hY : ∀ i, Y i ∈ thetaComponents 3 H)
    (hne : ∀ i j, i ≠ j → Y i ≠ Y j) (x k : Fin 4 → H) (hxY : ∀ i, x i ∈ Y i)
    (hkY : ∀ i, k i ∈ Y i) (hx3 : ∀ i, x i ^ 3 = 1)
    (hxk : ∀ i, ⁅x i, k i⁆ ∉ aschbacherSolvableCore 3 H) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have : (aschbacherSolvableCore 3 H).Normal := Subgroup.normal_of_characteristic _
  rw [← CFSG.SectionRank.pRank_quotient_eq _ hθ3]
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hc : ∀ i j, i ≠ j → ∀ u ∈ Y i, ∀ v ∈ Y j, Commute (π u) (π v) := by
    intro i j hij u hu v hv
    have h1 : π ⁅u, v⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
      (commutator_le_of_mem_thetaComponents (hY i) (hY j) (hne i j hij)
        (Subgroup.commutator_mem_commutator hu hv))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  refine four_le_pRank_of_noncomm (fun i => π (x i)) (fun i => π (k i)) (fun i => ?_)
    (fun i j => ?_) (fun i j hij => (hc i j hij _ (hkY i) _ (hxY j))) (fun i hik => ?_)
  · rw [← map_pow, hx3 i, map_one]
  · by_cases hij : i = j
    · rw [hij]
    · exact hc i j hij _ (hxY i) _ (hxY j)
  · apply hxk i
    have h1 : π ⁅x i, k i⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hik.eq.symm
    exact (QuotientGroup.eq_one_iff _).mp h1

variable {G : Type} [Group G] [Finite G]

@[expose] def HasNonCentralThree (Y : Subgroup G) : Prop :=
  ∃ x ∈ Y, x ^ 3 = 1 ∧ ∃ y ∈ Y,
    x * y * x⁻¹ * y⁻¹ ∉ (aschbacherSolvableCore 3 ↥Y).map Y.subtype

omit [Group G] [Finite G] in
theorem vec_four_ne {α : Type*} {a b c d : α} (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d)
    (h12 : b ≠ c) (h13 : b ≠ d) (h23 : c ≠ d) :
    ∀ i j : Fin 4, i ≠ j → ![a, b, c, d] i ≠ ![a, b, c, d] j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

section Twin

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem le_normalizer_map_conj_of_hasNonCentralThree (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) {t : G}
    (ht : t ∈ M) :
    A ≤ Subgroup.normalizer ((Y.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYM, hAM, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.toSec13Data.isElemAbelian.2
  intro a ha
  by_contra haZ
  set Z := Y.map (MulAut.conj t).toMonoidHom with hZ
  have hconj : ∀ (u : G), u ∈ A → Y.map (MulAut.conj u).toMonoidHom = Y := fun u hu =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAY hu)
  have hZa : Z.map (MulAut.conj a).toMonoidHom ≠ Z := fun he =>
    haZ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hYZ : Y ≠ Z := fun he => haZ (he ▸ hAY ha)
  have hmapinj : ∀ (u : G) (P Q : Subgroup G), P.map (MulAut.conj u).toMonoidHom =
      Q.map (MulAut.conj u).toMonoidHom → P = Q := fun u P Q he =>
    Subgroup.map_injective (MulAut.conj u).injective he
  have ha2 : a * a ∈ A := A.mul_mem ha ha
  have hYZb : ∀ b ∈ A, Y ≠ Z.map (MulAut.conj b).toMonoidHom := by
    intro b hb he
    apply hYZ
    apply hmapinj b
    rw [← he, hconj b hb]
  set g : Fin 4 → G := ![1, t, a * t, a * a * t] with hg
  have hgM : ∀ i, g i ∈ M := by
    intro i
    fin_cases i
    · exact M.one_mem
    · exact ht
    · exact M.mul_mem (hAM ha) ht
    · exact M.mul_mem (M.mul_mem (hAM ha) (hAM ha)) ht
  have hYg : ∀ i, Y.map (MulAut.conj (g i)).toMonoidHom =
      ![Y, Z, Z.map (MulAut.conj a).toMonoidHom,
        Z.map (MulAut.conj (a * a)).toMonoidHom] i := by
    intro i
    fin_cases i
    · exact Late.map_conj_one Y
    · rfl
    · exact (Late.map_conj_map_conj Y a t).symm
    · exact (Late.map_conj_map_conj Y (a * a) t).symm
  have hZa2 : Z.map (MulAut.conj (a * a)).toMonoidHom ≠ Z := by
    intro he
    apply hZa
    have h3 : a * (a * a) = 1 := by rw [← pow_three]; exact hA3 a ha
    calc Z.map (MulAut.conj a).toMonoidHom
        = (Z.map (MulAut.conj (a * a)).toMonoidHom).map (MulAut.conj a).toMonoidHom := by rw [he]
      _ = Z := by rw [Late.map_conj_map_conj, h3, Late.map_conj_one]
  have hZaa : Z.map (MulAut.conj (a * a)).toMonoidHom ≠ Z.map (MulAut.conj a).toMonoidHom := by
    intro he
    apply hZa
    apply hmapinj a
    rw [Late.map_conj_map_conj, ← he]
  have hdist : ∀ i j : Fin 4, i ≠ j → Y.map (MulAut.conj (g i)).toMonoidHom ≠
      Y.map (MulAut.conj (g j)).toMonoidHom := by
    intro i j hij
    rw [hYg i, hYg j]
    exact vec_four_ne hYZ (hYZb a ha) (hYZb (a * a) ha2) hZa.symm hZa2.symm hZaa.symm i j hij
  obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_item152 h h152 hY hM
  change Y'.map M.subtype = Y at hYY'
  set σ : Fin 4 → (↥M ≃* ↥M) := fun i => MulAut.conj (⟨g i, hgM i⟩ : M) with hσ
  have hσY : ∀ i, (Y'.map (σ i).toMonoidHom).map M.subtype =
      Y.map (MulAut.conj (g i)).toMonoidHom := by
    intro i
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨x, hxY, hx3, y, hyY, hxy⟩ := hN
  have hxY0 := hxY
  have hyY0 := hyY
  rw [← hYY'] at hxY0 hyY0
  obtain ⟨x', hxY', rfl⟩ := hxY0
  obtain ⟨y', hyY', rfl⟩ := hyY0
  obtain ⟨hθN, hθs, hθ3⟩ := map_aschbacherSolvableCore_facts M
  obtain ⟨-, hθc, hθ3', -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hxyM : ⁅x', y'⁆ ∉ aschbacherSolvableCore 3 ↥M := by
    intro hmem
    apply hxy
    have hmemG : (x' : G) * y' * (x' : G)⁻¹ * (y' : G)⁻¹ ∈
        (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y := by
      refine ⟨?_, Y.mul_mem (Y.mul_mem (Y.mul_mem hxY hyY) (Y.inv_mem hxY)) (Y.inv_mem hyY)⟩
      have := Subgroup.mem_map_of_mem M.subtype hmem
      rwa [commutatorElement_def] at this
    exact inf_le_map_aschbacherSolvableCore (hYM.trans hθN) hθs hθ3 hmemG
  have h4 := four_le_pRank_of_thetaComponents (fun i => Y'.map (σ i).toMonoidHom)
    (fun i => map_mulEquiv_mem_thetaComponents Nat.prime_three (σ i) hY')
    (fun i j hij he => hdist i j hij (by rw [← hσY i, ← hσY j, he]))
    (fun i => σ i x') (fun i => σ i y')
    (fun i => Subgroup.mem_map_of_mem _ hxY') (fun i => Subgroup.mem_map_of_mem _ hyY')
    (fun i => by
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one])
    (fun i hmem => by
      apply hxyM
      rw [← map_commutatorElement] at hmem
      have hchar : (aschbacherSolvableCore 3 ↥M).map (σ i).toMonoidHom =
          aschbacherSolvableCore 3 ↥M :=
        Subgroup.characteristic_iff_map_eq.mp hθc (σ i)
      have := Subgroup.mem_map_of_mem (σ i).symm.toMonoidHom hmem
      rw [← hchar, Subgroup.map_map] at this
      simpa using this)
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem oPrimeResidualOf_delta_le_of_hasNonCentralThree (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (h152 : Item152 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    oPrimeResidualOf 3 (delta A (lB A) M) ≤
      oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) :=
  oPrimeResidualOf_delta_le_of_forall_conj h149
    (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1.1
    fun _ ht => le_normalizer_map_conj_of_hasNonCentralThree h h152 hY hN hM ht

theorem oPrimeResidualOf_delta_eq_iff (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    (h152 : Item152 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    oPrimeResidualOf 3 (delta A (lB A) M) =
        oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ↔
      Subgroup.normalizer (Y : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := oPrimeResidualOf_delta_le_of_hasNonCentralThree h h149 h152 hY hN hM
  have hMY : M ∈ scriptY A := (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1.1
  obtain ⟨hNX, -, -, hX2⟩ := facts153 h h149 hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  constructor
  · intro heq
    have hMX : M ≤ Subgroup.normalizer (X : Set G) := by
      rw [← heq]
      exact normalizer_le_normalizer_oPrimeResidualOf_delta h149 hMY
    have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :=
      CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
    have hNXle : Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
    have hMeq : M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
      by_contra hne
      exact hM.1.2 _ (lt_of_le_of_ne (hMX.trans hNXle) hne) hloc
    rw [hMeq]
    exact hNX.trans hNXle
  · intro hNM
    exact le_antisymm hle (oPrimeResidualOf_mono 3 (delta_mono hNM))

end Twin

@[expose] def Claim153TwinN (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, ¬ HasFaithfulE9 Y →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) → Subgroup.normalizer (Y : Set G) ≤ M

theorem claim153TwinX_of_twinN {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (h152 : Item152 A (lB A)) (htn : Claim153TwinN A (lB A))
    (hnc : ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y → HasNonCentralThree Y) :
    Claim153TwinX A (lB A) := fun Y hY hE M hM hMY =>
  (oPrimeResidualOf_delta_eq_iff h h149 h152 hY (hnc Y hY hE) hM).mpr (htn Y hY hE M hM hMY)

end CFSG.RankThree.PartTwo.Sec15
