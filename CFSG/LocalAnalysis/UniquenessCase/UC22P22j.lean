module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.Goldschmidt.BasicG
public import Certificates.Certificate43
public import Certificates.Certificate113
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.GH74.KGroups.CoverEven
import CFSG.GH74.KGroups.PSL2
import CFSG.Blueprint.LieModelAPI
import CFSG.LieType.BorelTits.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.Goldschmidt
open scoped commutatorElement MatrixGroups Pointwise

section Abstract

theorem uc22p22j_card_sup_dvd {Γ : Type*} [Group Γ] {P Q : Subgroup Γ}
    (hQP : Q ≤ normalizer (P : Set Γ)) :
    Nat.card ↥(P ⊔ Q) ∣ Nat.card ↥P * Nat.card ↥Q := by
  have hn : (P.subgroupOf (P ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQP)
  have hsurj : Function.Surjective ((QuotientGroup.mk' (P.subgroupOf (P ⊔ Q))).comp
      (Subgroup.inclusion (le_sup_right : Q ≤ P ⊔ Q))) := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf (P ⊔ Q)) z
    have hy' : y ∈ (P : Set Γ) * (Q : Set Γ) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left P Q hQP]
      exact hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hy'
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_normalizer_iff''.mp (hQP hv) u).mp hu
    simpa [mul_assoc] using h
  have h1 := Subgroup.card_ker_mul_card_of_surjective
    (QuotientGroup.mk'_surjective (P.subgroupOf (P ⊔ Q)))
  rw [QuotientGroup.ker_mk',
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ P ⊔ Q)).toEquiv] at h1
  have h3 : Nat.card (↥(P ⊔ Q) ⧸ P.subgroupOf (P ⊔ Q)) ∣ Nat.card ↥Q :=
    Subgroup.card_dvd_of_surjective hsurj
  rw [← h1]
  exact Nat.mul_dvd_mul_left _ h3

theorem uc22p22j_comm_mul_central {X : Type*} [Group X] {x z : X} (hz : z ∈ center X) (y : X) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h : z * y * z⁻¹ = y := by
    rw [← (Subgroup.mem_center_iff.1 hz y)]
    group
  simp only [commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem uc22p22j_comm_central_mul {X : Type*} [Group X] {x z : X} (hz : z ∈ center X) (y : X) :
    ⁅y, x * z⁆ = ⁅y, x⁆ := by
  have h : z * y⁻¹ * z⁻¹ = y⁻¹ := by
    rw [← (Subgroup.mem_center_iff.1 hz y⁻¹)]
    group
  simp only [commutatorElement_def]
  calc y * (x * z) * y⁻¹ * (x * z)⁻¹ = y * x * (z * y⁻¹ * z⁻¹) * x⁻¹ := by group
    _ = y * x * y⁻¹ * x⁻¹ := by rw [h]

@[expose] def OddAbelianProper (X : Type) [Group X] : Prop :=
  ∀ (S : Sylow 2 X) (Y : Subgroup X), (S : Subgroup X) ≤ Y → Y ≠ ⊤ → ∀ W : Subgroup X, W ≤ Y →
    Odd (Nat.card W) → ∀ a ∈ W, ∀ b ∈ W, a * b = b * a

theorem uc22p22j_odd_abelian
    {X H : Type} [Group X] [Finite X] [Group H] [IsSimpleGroup H] (hI : IsGoldTypeI H)
    (hperf : _root_.commutator X = ⊤) (q : X →* H) (hq : Function.Surjective q)
    (hker : q.ker ≤ center X) (S : Sylow 2 X) {Y : Subgroup X} (hSY : (S : Subgroup X) ≤ Y)
    (hY : Y ≠ ⊤) {W : Subgroup X} (hWY : W ≤ Y) (hW : Odd (Nat.card W)) {a b : X}
    (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite H := Finite.of_surjective q hq
  let S' : Sylow 2 H := S.mapSurjective hq
  obtain ⟨D, hDN, hDcyc, -, -, hsup, -, -, -, -, -, -, -, -, -, -, -, -, hmax⟩ :=
    G32 H hI S'
  have hYq : Y.map q ≠ ⊤ := by
    intro htop
    apply hY
    rw [eq_top_iff]
    have hcomm : _root_.commutator X ≤ Y := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      obtain ⟨y₁, hy₁, e₁⟩ : q g₁ ∈ Y.map q := htop ▸ Subgroup.mem_top _
      obtain ⟨y₂, hy₂, e₂⟩ : q g₂ ∈ Y.map q := htop ▸ Subgroup.mem_top _
      have hz₁ : y₁⁻¹ * g₁ ∈ center X := hker (by simp [MonoidHom.mem_ker, e₁])
      have hz₂ : y₂⁻¹ * g₂ ∈ center X := hker (by simp [MonoidHom.mem_ker, e₂])
      have e : ⁅g₁, g₂⁆ = ⁅y₁, y₂⁆ := by
        have h1 : g₁ = y₁ * (y₁⁻¹ * g₁) := by group
        have h2 : g₂ = y₂ * (y₂⁻¹ * g₂) := by group
        calc ⁅g₁, g₂⁆ = ⁅y₁ * (y₁⁻¹ * g₁), g₂⁆ := by rw [← h1]
          _ = ⁅y₁, g₂⁆ := uc22p22j_comm_mul_central hz₁ g₂
          _ = ⁅y₁, y₂ * (y₂⁻¹ * g₂)⁆ := by rw [← h2]
          _ = ⁅y₁, y₂⁆ := uc22p22j_comm_central_mul hz₂ y₁
      rw [e]
      simp only [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)
    exact hperf.symm.le.trans hcomm
  have hSq : (S' : Subgroup H) ≤ Y.map q := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSY
  have hYN : Y.map q ≤ (S' : Subgroup H) ⊔ D := by
    rw [hsup]
    exact hmax _ hSq hYq
  set N : Subgroup H := (S' : Subgroup H) ⊔ D with hNdef
  haveI hnorm : ((S' : Subgroup H).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hDN)
  have hsurjD : Function.Surjective ((QuotientGroup.mk' ((S' : Subgroup H).subgroupOf N)).comp
      (Subgroup.inclusion (le_sup_right : D ≤ N))) := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective ((S' : Subgroup H).subgroupOf N) z
    have hy' : y ∈ ((S' : Subgroup H) : Set H) * (D : Set H) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (S' : Subgroup H) D hDN]
      exact hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hy'
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_normalizer_iff''.mp (hDN hv) u).mp hu
    simpa [mul_assoc] using h
  haveI : IsCyclic ↥D := hDcyc
  haveI : IsCyclic (↥N ⧸ (S' : Subgroup H).subgroupOf N) := isCyclic_of_surjective _ hsurjD
  have hWN : ∀ w : W, q (w : X) ∈ N := fun w => hYN ⟨w, hWY w.2, rfl⟩
  let g : W →* N := (q.comp W.subtype).codRestrict N hWN
  let f : W →* ↥N ⧸ (S' : Subgroup H).subgroupOf N := (QuotientGroup.mk' _).comp g
  have hfker : f.ker ≤ center W := by
    intro w hw
    have h1 : q (w : X) ∈ (S' : Subgroup H) := by
      have : g w ∈ (S' : Subgroup H).subgroupOf N := (QuotientGroup.eq_one_iff _).1 hw
      exact this
    have h2 : Odd (orderOf (q (w : X))) := by
      have h3 : Odd (orderOf (w : X)) := hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W w.2)
      exact h3.of_dvd_nat (orderOf_map_dvd q _)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S'.isPGroup') ⟨q (w : X), h1⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at h2
      exact (Nat.not_even_iff_odd.2 h2) (Nat.even_pow.2 ⟨even_two, hk0⟩)
    have h4 : q (w : X) = 1 := by
      rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
    have h5 : (w : X) ∈ center X := hker (by simpa [MonoidHom.mem_ker] using h4)
    rw [Subgroup.mem_center_iff]
    intro v
    exact Subtype.ext (Subgroup.mem_center_iff.1 h5 v)
  exact congrArg Subtype.val (commutative_of_cyclic_center_quotient f hfker ⟨a, ha⟩ ⟨b, hb⟩)

theorem uc22p22j_typeI_quot {X : Type} [Group X] [Finite X] (hperf : _root_.commutator X = ⊤)
    (h : (∃ n : ℕ, 3 ≤ n ∧ Nonempty (X ⧸ center X ≃* PSL(2, GaloisField 2 n))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ⧸ center X ≃* Sz n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (X ⧸ center X ≃* PSU3 2 n))) :
    IsSimpleGroup (X ⧸ center X) ∧ IsGoldTypeI (X ⧸ center X) := by
  haveI : Group.IsPerfect X := ⟨hperf⟩
  have hB : fusionIsBenderGroup (X ⧸ center X) := by
    rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
    · exact Or.inl ⟨n, by omega, e⟩
    · exact Or.inr (Or.inr ⟨n, hn, e⟩)
    · exact Or.inr (Or.inl ⟨n, hn, e⟩)
  refine ⟨CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB, ?_⟩
  have hZ : center (X ⧸ center X) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot X
  let e0 : (X ⧸ center X) ⧸ center (X ⧸ center X) ≃* X ⧸ center X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e0.trans e⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e0.trans e⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨e0.trans e⟩⟩)

theorem uc22p22j_center_bot {X : Type} [Group X] [Finite X] (hperf : _root_.commutator X = ⊤)
    (hB : fusionIsBenderGroup X) : center X = ⊥ := by
  haveI : Group.IsPerfect X := ⟨hperf⟩
  haveI := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.RankOneRecog.exists_noncommuting_of_perfect hB
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem uc22p22j_typeI_of_shape {X : Type} [Group X] [Finite X] (hperf : _root_.commutator X = ⊤)
    {n : ℕ} (h : IsSz X n ∨ (IsL2 X n ∧ 3 ≤ n) ∨ IsSU3 X n) :
    IsSimpleGroup (X ⧸ center X) ∧ IsGoldTypeI (X ⧸ center X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with hSz | ⟨hL2, hn3⟩ | ⟨-, hU⟩
  ·
    obtain ⟨-, a, ha, K, _, _, hf, hcard, ⟨e⟩⟩ := (CFSG.Blueprint.LieModel.suzukiModel hSz).2
    have hcard' : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hcard
    let E : X ≃* Sz a :=
      e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
        (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard'))
    have hB : fusionIsBenderGroup X := Or.inr (Or.inr ⟨a, ha, ⟨E⟩⟩)
    have hZ : center X = ⊥ := uc22p22j_center_bot hperf hB
    let e1 : X ⧸ center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact uc22p22j_typeI_quot hperf (Or.inr (Or.inl ⟨a, ha, ⟨e1.trans E⟩⟩))
  ·
    obtain ⟨E⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 n) 2 n
      (by omega) (GaloisField.card 2 n (by omega)) hL2
    have hB : fusionIsBenderGroup X := Or.inl ⟨n, by omega, ⟨E⟩⟩
    have hZ : center X = ⊥ := uc22p22j_center_bot hperf hB
    let e1 : X ⧸ center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact uc22p22j_typeI_quot hperf (Or.inl ⟨n, hn3, ⟨e1.trans E⟩⟩)
  ·
    have hadm := CFSG.Blueprint.LieModel.admissible hU
    have hn2 : 2 ≤ n := by
      obtain ⟨-, h1n, -, hne⟩ := hadm
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hne rfl
    obtain ⟨E⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hn2 hU
    exact uc22p22j_typeI_quot hperf (Or.inr (Or.inr ⟨n, hn2, ⟨E⟩⟩))

theorem uc22p22j_oddAbelianProper_of_typeI_shape
    {X : Type} [Group X] [Finite X]
    (hperf : _root_.commutator X = ⊤) {n : ℕ}
    (h : IsSz X n ∨ (IsL2 X n ∧ 3 ≤ n) ∨ IsSU3 X n) : OddAbelianProper X := by
  obtain ⟨hsimple, hI⟩ := uc22p22j_typeI_of_shape hperf h
  haveI := hsimple
  intro S Y hSY hY W hWY hW a ha b hb
  exact uc22p22j_odd_abelian hI hperf (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le S hSY hY hWY hW ha hb

theorem uc22p22j_oddAbelianProper_sixty {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) : OddAbelianProper X := by
  intro S Y hSY hY W hWY hW a ha b hb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card (S : Subgroup X) = 4 := by
    rw [Sylow.card_eq_multiplicity, hX]
    have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    have hf : (Nat.factorization 60) 2 = 2 := by
      rw [h60, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [hf]
    norm_num
  have h4 : 4 ∣ Nat.card Y := hS ▸ Subgroup.card_dvd_of_le hSY
  have h60 : Nat.card Y ∣ 60 := hX ▸ Subgroup.card_subgroup_dvd_card Y
  have hne60 : Nat.card Y ≠ 60 := fun h =>
    hY ((Subgroup.card_eq_iff_eq_top Y).1 (h.trans hX.symm))
  have hne20 : Nat.card Y ≠ 20 := by
    intro h20
    have hidx : Y.index = 3 := by
      have := Subgroup.card_mul_index Y
      rw [h20, hX] at this
      omega
    haveI : Y.FiniteIndex := ⟨by omega⟩
    have hcore : Y.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with h | h
      · exact h
      · exact absurd (eq_top_iff.2 (h ▸ Y.normalCore_le)) hY
    have h1 := Subgroup.index_normalCore_dvd_factorial_index Y
    rw [hcore, Subgroup.index_bot, hX, hidx] at h1
    norm_num [Nat.factorial] at h1
  have hm : Nat.card Y = 4 ∨ Nat.card Y = 12 := by
    have hmem : Nat.card Y ∈ Nat.divisors 60 := Nat.mem_divisors.2 ⟨h60, by norm_num⟩
    have hdiv : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hW12 : Nat.card W ∣ 12 := by
    have := Subgroup.card_dvd_of_le hWY
    rcases hm with h | h <;> rw [h] at this <;> exact this.trans (by norm_num)
  have hW13 : Nat.card W = 1 ∨ Nat.card W = 3 := by
    have hmem : Nat.card W ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨hW12, by norm_num⟩
    have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    obtain ⟨k, hk⟩ := hW
    omega
  have hcyc : IsCyclic W := by
    rcases hW13 with h | h
    · haveI : Subsingleton W := (Nat.card_eq_one_iff_unique.1 h).1
      infer_instance
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact isCyclic_of_prime_card h
  exact congrArg Subtype.val
    (commutative_of_cyclic_center_quotient (MonoidHom.id W) (by simp) ⟨a, ha⟩ ⟨b, hb⟩)

theorem uc22p22j_oddAbelianProper_L2_four {X : Type} [Group X] [Finite X] (h : IsL2 X 2) :
    OddAbelianProper X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 2) 2 2
    (by omega) (GaloisField.card 2 2 (by omega)) h
  have hB : fusionIsBenderGroup X := Or.inl ⟨2, le_rfl, ⟨E⟩⟩
  haveI := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hX : Nat.card X = 60 := by
    rw [Nat.card_congr E.toEquiv, CFSG.Walter.psl2_even_card (by omega)]
    norm_num
  exact uc22p22j_oddAbelianProper_sixty hX

theorem uc22p22j_oddAbelianProper_of_shape
    {X : Type} [Group X] [Finite X]
    (hperf : _root_.commutator X = ⊤) {n : ℕ} (h : IsSz X n ∨ IsL2 X n ∨ IsSU3 X n) :
    OddAbelianProper X := by
  rcases h with hSz | hL2 | hU
  · exact uc22p22j_oddAbelianProper_of_typeI_shape hperf (Or.inl hSz)
  · have hn2 : 2 ≤ n := by
      obtain ⟨-, h1n, -, hne, -⟩ := CFSG.Blueprint.LieModel.admissible hL2
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hne rfl
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact uc22p22j_oddAbelianProper_L2_four hL2
    · exact uc22p22j_oddAbelianProper_of_typeI_shape hperf (Or.inr (Or.inl ⟨hL2, h3⟩))
  · exact uc22p22j_oddAbelianProper_of_typeI_shape hperf (Or.inr (Or.inr hU))

theorem uc22p22j_odd_abelian_lift {Λ : Type} [Group Λ] [Finite Λ]
    (hX : OddAbelianProper (Λ ⧸ CFSG.pCore 2 Λ)) (T₁ : Sylow 2 Λ) {Ω : Subgroup Λ}
    (hTΩ : (T₁ : Subgroup Λ) ≤ Ω) (hΩ : Ω ≠ ⊤) {V : Subgroup Λ} (hVΩ : V ≤ Ω)
    (hV : Odd (Nat.card V)) {a b : Λ} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup Λ := CFSG.pCore 2 Λ with hO
  let π : Λ →* Λ ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hOT : O ≤ (T₁ : Subgroup Λ) := (CFSG.pCore_isPGroup (p := 2) (G := Λ)).le_sylow_of_normal T₁
  have hOΩ : O ≤ Ω := hOT.trans hTΩ
  let S : Sylow 2 (Λ ⧸ O) := T₁.mapSurjective hπ
  have hSY : (S : Subgroup (Λ ⧸ O)) ≤ Ω.map π := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hTΩ
  have hY : Ω.map π ≠ ⊤ := by
    intro h
    apply hΩ
    have h1 := Subgroup.comap_map_eq π Ω
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hOΩ] at h1
    exact h1.symm
  have hW : Odd (Nat.card (V.map π)) := by
    have hsurj : Function.Surjective (π.subgroupMap V) := MonoidHom.subgroupMap_surjective _ _
    exact hV.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)
  have habel := hX S (Ω.map π) hSY hY (V.map π) (Subgroup.map_mono hVΩ) hW (π a) ⟨a, ha, rfl⟩
    (π b) ⟨b, hb, rfl⟩
  have hκO : ⁅a, b⁆ ∈ O := by
    have h1 : π ⁅a, b⁆ = ⁅π a, π b⁆ := map_commutatorElement π a b
    rw [commutatorElement_eq_one_iff_mul_comm.2 habel] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hκV : ⁅a, b⁆ ∈ V := by
    simp only [commutatorElement_def]
    exact V.mul_mem (V.mul_mem (V.mul_mem ha hb) (V.inv_mem ha)) (V.inv_mem hb)
  have hodd : Odd (orderOf ⁅a, b⁆) := hV.of_dvd_nat (Subgroup.orderOf_dvd_natCard V hκV)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 2) (G := Λ)))
    ⟨⁅a, b⁆, hκO⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact commutatorElement_eq_one_iff_mul_comm.1 hk

end Abstract

section Main

variable {G : Type} [Group G] [Finite G]

theorem uc22p22j_perfect_bar2 (L : Subgroup G) (hperf : ⁅L, L⁆ = L) :
    _root_.commutator (Bar2 L) = ⊤ := by
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  haveI : Group.IsPerfect (Bar2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
  exact Group.IsPerfect.commutator_eq_top

@[expose] def S2010RankOne (L : Subgroup G) : Prop :=
  ∃ n : ℕ, IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n

@[expose] def S2010Product (D : Data G) (L : Subgroup G) : Prop :=
  ∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ ∧
    (∃ t ∈ D.T, L₂ = L₁.map (MulAut.conj t).toMonoidHom) ∧
    ∃ n : ℕ, ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
      IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3)

@[expose] def S2010Graph (D : Data G) (L : Subgroup G) : Prop :=
  ∃ n : ℕ, (IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) ∧ ∃ t ∈ D.T, ActsNontrivOnDiagram L t

@[expose] def OddAbelianL0 (D : Data G) (L : Subgroup G) : Prop :=
  ∀ V : Subgroup G, V ≤ L → V ≤ D.M → Odd (Nat.card V) → ∀ a ∈ V, ∀ b ∈ V, a * b = b * a

theorem uc22p22j_oddAbelianL0_rankOne
    (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) (hsh : S2010RankOne L) :
    OddAbelianL0 D L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hVL hVM hVodd a ha b hb
  obtain ⟨hTN, hperf, hLT, -⟩ := hL
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLM : ¬ L ≤ D.M := fun h => hLT.2.1 (sup_le h hTM)
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 D.T (L ⊔ D.T) := D.sylowG.of_le le_sup_right le_top
  have h2 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    h1.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨T₁, hT₁⟩ := h2.exists_sylow_eq_subgroupOf
  have hT₁M : (T₁ : Subgroup L) ≤ D.M.subgroupOf L := by
    intro x hx
    rw [hT₁] at hx
    exact hTM (Subgroup.mem_inf.1 hx).1
  have hΩ : D.M.subgroupOf L ≠ ⊤ := by
    intro h
    apply hLM
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ D.M.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨n, hn⟩ := hsh
  have hX : OddAbelianProper (Bar2 L) :=
    uc22p22j_oddAbelianProper_of_shape (uc22p22j_perfect_bar2 L hperf) hn
  have hVodd' : Odd (Nat.card (V.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv]
    exact hVodd
  exact congrArg Subtype.val (uc22p22j_odd_abelian_lift hX T₁ hT₁M hΩ
    (V := V.subgroupOf L) (fun y hy => hVM hy) hVodd' (a := ⟨a, hVL ha⟩) (b := ⟨b, hVL hb⟩) ha hb)

theorem uc22p22j_cent2010_of_oddAbelian (D : Data G) (Ch : Choice2011 G) (c : Ctx21 D Ch)
    (hL : OddAbelianL0 D c.L0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hPp : IsPGroup p ↥P) (hPL : P ≤ c.L0) (hPM : P ≤ D.M)
    (hBP : c.B ≤ normalizer (P : Set G)) : ⁅c.B, P⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBL : c.B ≤ c.L0 := c.hB.1
  have hBM : c.B ≤ D.M := c.hle.trans c.hBM
  set V : Subgroup G := P ⊔ c.B with hV
  have hVodd : Odd (Nat.card V) := by
    have hPodd : Odd (Nat.card P) := by
      obtain ⟨k, hk⟩ := hPp.exists_card_eq
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    exact (hPodd.mul (uc22p22f_odd_card_B c)).of_dvd_nat (uc22p22j_card_sup_dvd hBP)
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.2 fun b hb x hx => ?_
  have hcomm := hL V (sup_le hPL hBL) (sup_le hPM hBM) hVodd x ((le_sup_left : P ≤ V) hx) b
    ((le_sup_right : c.B ≤ V) hb)
  exact commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm

theorem uc22p22j_cent2010_rankOne_all
    (D : Data G) (Ch : Choice2011 G) (c : Ctx21 D Ch) (hsh : S2010RankOne c.L0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPL : P ≤ c.L0)
    (hPM : P ≤ D.M) (hBP : c.B ≤ normalizer (P : Set G)) : ⁅c.B, P⁆ = ⊥ :=
  uc22p22j_cent2010_of_oddAbelian D Ch c
    (uc22p22j_oddAbelianL0_rankOne D c.hL0.1 hsh) hp hp2 hPp hPL hPM hBP

@[expose] def Cent2010Rest (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, (S2010Product D c.L0 ∨ S2010Graph D c.L0) → ∀ p : ℕ, p.Prime →
    p ≠ 2 → ∀ P : Subgroup G, IsPGroup p ↥P → P ≤ c.L0 → P ≤ D.M → c.B ≤ normalizer (P : Set G) →
    ⁅c.B, P⁆ = ⊥

@[expose] def OddAbelianRest (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, (S2010Product D c.L0 ∨ S2010Graph D c.L0) → OddAbelianL0 D c.L0

theorem uc22p22j_centRest_of_oddAbelianRest (D : Data G) (Ch : Choice2011 G)
    (h : OddAbelianRest D Ch) : Cent2010Rest D Ch :=
  fun h1930 c hc _ hp hp2 _ hPp hPL hPM hBP =>
    uc22p22j_cent2010_of_oddAbelian D Ch c (h h1930 c hc) hp hp2 hPp hPL hPM hBP

theorem uc22p22j_cent2010_of
    (D : Data G) (Ch : Choice2011 G) (h20_10 : S20_10 D) (hrest : Cent2010Rest D Ch) :
    Cent2010 D Ch := by
  intro h1930 c p hp hp2 P hPp hPL hPM hBP
  rcases h20_10 h1930 c.L0 c.hL0 with h1 | h2 | h3
  · exact uc22p22j_cent2010_rankOne_all D Ch c h1 hp hp2 hPp hPL hPM hBP
  · exact hrest h1930 c (Or.inl h2) p hp hp2 P hPp hPL hPM hBP
  · exact hrest h1930 c (Or.inr h3) p hp hp2 P hPp hPL hPM hBP

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
