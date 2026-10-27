module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Odd
import CFSG.GroupTheory.SubgroupTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCoreSmall
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (DerInf8)
open CFSG.RankThree.PartTwo

structure R891D4Layer {X : Type} [Group X] (n : ℕ) (z : X) (R : Subgroup X) : Prop where
  mem : z ∈ R
  le_centralizer : R ≤ centralizer ({z} : Set X)
  commutator_mem : ∀ a ∈ centralizer ({z} : Set X), ∀ b ∈ centralizer ({z} : Set X),
    a * b * a⁻¹ * b⁻¹ ∈ R
  sl3Two : R891SL3Two ↥R n
  slThreePi : Sec4.IsSLThreePiAt ↥R (2 ^ n)
  opp_eq : n = 1 → Opp 2 (centralizer ({z} : Set X)) = R

structure R891D4Setup {X : Type} [Group X] (n : ℕ) (S B : Subgroup X) : Prop where
  one_le : 1 ≤ n
  sl2S : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 3 ∧
    Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) K)
  sl2B : ∃ (L : Type) (_ : Field L) (_ : Finite L), Nat.card L = 2 ^ n ∧
    Nonempty (↥B ≃* Matrix.SpecialLinearGroup (Fin 2) L)
  cent : B = centralizer (S : Set X)
  card : Nat.card X = ordTrialityD4 (2 ^ n)
  conj : ∀ z : X, z ^ 3 = 1 → z ≠ 1 → ∃ g : X, g * z * g⁻¹ ∈ S ∨ g * z * g⁻¹ ∈ B
  bcomm : ∀ t ∈ B, t ^ 3 = 1 → t ≠ 1 → ∀ a ∈ centralizer ({t} : Set X),
    ∀ b ∈ centralizer ({t} : Set X), a * b * a⁻¹ * b⁻¹ ∈ S
  sylow : ∀ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ → ∀ t ∈ B, t ^ 3 = 1 → t ≠ 1 →
    ¬ P ≤ centralizer ({t} : Set X)
  norm : ∀ y ∈ S, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 → ∀ g : X,
    g * y * g⁻¹ ∈ zpowers y → g ∈ Subgroup.normalizer (B : Set X)
  layer : ∀ z ∈ S, z ^ 3 = 1 → z ≠ 1 → ∃ R : Subgroup X, R891D4Layer n z R

private theorem r891_Opp_map_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (p : ℕ) (H : Subgroup X) :
    (Opp p H).map e.toMonoidHom = Opp p (H.map e.toMonoidHom) := by
  rw [Opp, Opp, CFSG.RankThree.PartOne.pElementSubgroup,
    CFSG.RankThree.PartOne.pElementSubgroup, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]⟩
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk

theorem R891D4Layer.map {X Y : Type} [Group X] [Group Y] {n : ℕ} {z : X} {R : Subgroup X}
    (h : R891D4Layer n z R) (e : X ≃* Y) : R891D4Layer n (e z) (R.map e.toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem e.toMonoidHom h.mem
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hrz : r * z = z * r :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hr)
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg e hrz
  · intro a ha b hb
    have hC := CFSG.centralizer_singleton_map e z
    have ha' : e.symm a ∈ Subgroup.centralizer ({z} : Set X) := by
      rw [← hC] at ha
      exact Subgroup.mem_map_equiv.mp ha
    have hb' : e.symm b ∈ Subgroup.centralizer ({z} : Set X) := by
      rw [← hC] at hb
      exact Subgroup.mem_map_equiv.mp hb
    have hcomm := h.commutator_mem (e.symm a) ha' (e.symm b) hb'
    have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hcomm
    simpa [map_mul] using hmem
  · exact R891SL3Two.of_mulEquiv
      (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective) h.sl3Two
  · obtain ⟨K, hKf, hKfin, hcase⟩ := h.slThreePi
    refine ⟨K, hKf, hKfin, ?_⟩
    rcases hcase with ⟨hcard, hmod, ⟨eK⟩⟩ | ⟨hcard, hmod, ⟨eK⟩⟩
    · exact Or.inl ⟨hcard, hmod,
        ⟨(Subgroup.equivMapOfInjective R e.toMonoidHom e.injective).symm.trans eK⟩⟩
    · exact Or.inr ⟨hcard, hmod,
        ⟨(Subgroup.equivMapOfInjective R e.toMonoidHom e.injective).symm.trans eK⟩⟩
  · intro hn
    rw [← h.opp_eq hn, ← CFSG.centralizer_singleton_map e z, r891_Opp_map_mulEquiv]

theorem R891D4Setup.map {X Y : Type} [Group X] [Group Y] {n : ℕ} {S B : Subgroup X}
    (h : R891D4Setup n S B) (e : X ≃* Y) :
    R891D4Setup n (S.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  have hord : 0 < ordTrialityD4 (2 ^ n) := by
    have hq2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.one_le
    have h6 : 1 < (2 ^ n) ^ 6 := by
      calc 1 < 2 ^ 6 := by norm_num
        _ ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq2 6
    have h2 : 1 < (2 ^ n) ^ 2 := by
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq2 2
    unfold ordTrialityD4
    have h6pos : 0 < (2 ^ n) ^ 6 - 1 := by omega
    have h2pos : 0 < (2 ^ n) ^ 2 - 1 := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity)) h6pos) h2pos
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [h.card]; exact ne_of_gt hord)
  have : Finite Y := Finite.of_equiv X e.toEquiv
  refine ⟨h.one_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := h.sl2S
    exact ⟨K, hKf, hKfin, hKcard,
      ⟨(Subgroup.equivMapOfInjective S e.toMonoidHom e.injective).symm.trans eK⟩⟩
  · obtain ⟨L, hLf, hLfin, hLcard, ⟨eL⟩⟩ := h.sl2B
    exact ⟨L, hLf, hLfin, hLcard,
      ⟨(Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).symm.trans eL⟩⟩
  · rw [h.cent]
    exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.map_centralizer_eq e S
  · rw [← Nat.card_congr e.toEquiv]
    exact h.card
  · intro z hz3 hz1
    obtain ⟨g, hg⟩ := h.conj (e.symm z) (e.injective (by simpa using hz3)) (by
      intro h1
      exact hz1 (by rw [← e.apply_symm_apply z, h1, map_one]))
    refine ⟨e g, ?_⟩
    rcases hg with hg | hg
    · left
      have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hg
      simpa [map_mul] using hmem
    · right
      have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hg
      simpa [map_mul] using hmem
  · intro t ht ht3 ht1 a ha b hb
    obtain ⟨t₀, ht₀B, rfl⟩ := Subgroup.mem_map.mp ht
    have ht₀3 : t₀ ^ 3 = 1 := e.injective (by simpa using ht3)
    have ht₀1 : t₀ ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
    have hC : (Subgroup.centralizer ({t₀} : Set X)).map e.toMonoidHom =
        Subgroup.centralizer ({e.toMonoidHom t₀} : Set Y) := by
      simpa only [MulEquiv.coe_toMonoidHom] using CFSG.centralizer_singleton_map e t₀
    have ha' : e.symm a ∈ Subgroup.centralizer ({t₀} : Set X) := by
      rw [← hC] at ha
      exact Subgroup.mem_map_equiv.mp ha
    have hb' : e.symm b ∈ Subgroup.centralizer ({t₀} : Set X) := by
      rw [← hC] at hb
      exact Subgroup.mem_map_equiv.mp hb
    have hcomm := h.bcomm t₀ ht₀B ht₀3 ht₀1 (e.symm a) ha' (e.symm b) hb'
    have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hcomm
    simpa [map_mul] using hmem
  · intro P hP t ht ht3 ht1
    obtain ⟨t₀, ht₀B, rfl⟩ := Subgroup.mem_map.mp ht
    have ht₀3 : t₀ ^ 3 = 1 := e.injective (by simpa using ht3)
    have ht₀1 : t₀ ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
    have hP' : CFSG.ABGLocalTools.IsSylowOf 3 (P.map e.symm.toMonoidHom) ⊤ := by
      have h := (CFSG.GroupTheory.isSylowOf_map_mulEquiv e.symm (P := P) (K := ⊤)).mpr hP
      rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h
    intro hle
    apply h.sylow (P.map e.symm.toMonoidHom) hP' t₀ ht₀B ht₀3 ht₀1
    intro x hx
    have hxP : e x ∈ P := Subgroup.mem_map_equiv.mp hx
    have hxe : e x ∈ Subgroup.centralizer ({e t₀} : Set Y) := hle hxP
    have hC : (Subgroup.centralizer ({t₀} : Set X)).map e.toMonoidHom =
        Subgroup.centralizer ({e t₀} : Set Y) := CFSG.centralizer_singleton_map e t₀
    rw [← hC] at hxe
    simpa using Subgroup.mem_map_equiv.mp hxe
  · intro y hy hyodd hy3 g hg
    obtain ⟨y₀, hy₀S, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := hyodd
    have hk₀ : y₀ ^ 3 ^ k = 1 := e.injective (by simpa using hk)
    have h3₀ : y₀ ^ 3 ≠ 1 := fun h1 => hy3 (by rw [← map_pow, h1, map_one])
    obtain ⟨g₀, rfl⟩ := e.surjective g
    have hg₀ : g₀ * y₀ * g₀⁻¹ ∈ zpowers y₀ := by
      have hgmap : e (g₀ * y₀ * g₀⁻¹) ∈ (zpowers y₀).map e.toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        simpa [map_mul] using hg
      simpa using (Subgroup.mem_map_equiv.mp hgmap :
        e.symm (e (g₀ * y₀ * g₀⁻¹)) ∈ zpowers y₀)
    have hnorm := h.norm y₀ hy₀S ⟨k, hk₀⟩ h3₀ g₀ hg₀
    have hnormmap : (Subgroup.normalizer (B : Set X)).map e.toMonoidHom =
        Subgroup.normalizer ((B.map e.toMonoidHom : Subgroup Y) : Set Y) :=
      Subgroup.map_normalizer_eq_of_bijective B e.bijective
    rw [← hnormmap]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hnorm
  · intro z hzS hz3 hz1
    have hzS' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hzS
    have hz3' : (e.symm z) ^ 3 = 1 := e.injective (by simpa using hz3)
    have hz1' : e.symm z ≠ 1 := by
      intro h1
      exact hz1 (by rw [← e.apply_symm_apply z, h1, map_one])
    obtain ⟨R, hR⟩ := h.layer (e.symm z) hzS' hz3' hz1'
    exact ⟨R.map e.toMonoidHom, by simpa using hR.map e⟩

namespace R891D4Setup

variable {X : Type} [Group X] {n : ℕ} {S B : Subgroup X}

theorem inf_eq_bot (h : R891D4Setup n S B) : S ⊓ B = ⊥ := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eS⟩⟩ := h.sl2S
  let := hKf
  let := hKfin
  have : Fintype K := Fintype.ofFinite K
  have hKpow : Fintype.card K = 2 ^ (3 * n) := by
    rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul, mul_comm]
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3 * n) hKpow
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
    apply Subtype.ext
    ext i j
    simp [Matrix.neg_apply, CharTwo.neg_eq]
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    have hset : (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :
        Set (Matrix.SpecialLinearGroup (Fin 2) K)) = {1} := by
      rw [CFSG.LinearGroups.center_specialLinearGroup_two, hneg]
      simp
    ext x
    rw [Subgroup.mem_bot]
    constructor
    · intro hx
      have hx' : x ∈ ({1} : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := hset ▸ hx
      simpa using hx'
    · intro hx
      rw [hx]
      exact Subgroup.one_mem _
  rw [h.cent]
  apply le_antisymm _ bot_le
  intro x hx
  have hxcenter : (⟨x, hx.1⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hx.2 (y : X) y.2
  have hmap : eS ⟨x, hx.1⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y₀, rfl⟩ := eS.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg eS (Subgroup.mem_center_iff.mp hxcenter y₀)
  rw [hcenter] at hmap
  have hx1 : eS ⟨x, hx.1⟩ = 1 := by simpa using hmap
  have hsub : (⟨x, hx.1⟩ : ↥S) = 1 := eS.injective (by simpa using hx1)
  exact Subtype.ext_iff.mp hsub

theorem card_S (h : R891D4Setup n S B) :
    Nat.card S = (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h.sl2S
  let := hKf
  let := hKfin
  calc Nat.card S = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
        Nat.card_congr e.toEquiv
    _ = Nat.card K * (Nat.card K ^ 2 - 1) :=
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
    _ = (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1) := by rw [hKcard]

theorem card_B (h : R891D4Setup n S B) : Nat.card B = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨L, hLf, hLfin, hLcard, ⟨e⟩⟩ := h.sl2B
  let := hLf
  let := hLfin
  calc Nat.card B = Nat.card (Matrix.SpecialLinearGroup (Fin 2) L) :=
        Nat.card_congr e.toEquiv
    _ = Nat.card L * (Nat.card L ^ 2 - 1) :=
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two L
    _ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by rw [hLcard]

theorem commutator_S (h : R891D4Setup n S B) : ⁅S, S⁆ = S := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h.sl2S
  let := hKf
  let := hKfin
  have : Fintype K := Fintype.ofFinite K
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    have h3 : 3 ≤ 3 * n := by
      calc 3 = 3 * 1 := by norm_num
        _ ≤ 3 * n := Nat.mul_le_mul_left 3 h.one_le
    calc (4 : ℕ) ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) h3
      _ = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have h4' : 4 ≤ (Finset.univ : Finset K).card := by
    simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  have : Group.IsPerfect ↥S :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp inferInstance

private theorem r891_S_le_centralizer (h : R891D4Setup n S B) {t : X} (ht : t ∈ B) :
    S ≤ Subgroup.centralizer ({t} : Set X) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have htC : t ∈ Subgroup.centralizer (S : Set X) := by
    rw [← h.cent]
    exact ht
  exact Subgroup.mem_centralizer_iff.mp htC s hs

theorem commutator_centralizer_eq (h : R891D4Setup n S B) {t : X} (ht : t ∈ B)
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ = S := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    simpa [commutatorElement_def] using h.bcomm t ht ht3 ht1 a ha b hb
  · calc S = ⁅S, S⁆ := (commutator_S h).symm
      _ ≤ ⁅Subgroup.centralizer ({t} : Set X), Subgroup.centralizer ({t} : Set X)⁆ :=
          Subgroup.commutator_mono (r891_S_le_centralizer h ht) (r891_S_le_centralizer h ht)

theorem derInf8_centralizer_eq (h : R891D4Setup n S B) {t : X} (ht : t ∈ B) (ht3 : t ^ 3 = 1)
    (ht1 : t ≠ 1) : DerInf8 (centralizer ({t} : Set X)) = S := by
  exact derInf8_eq_of_perfect (r891_S_le_centralizer h ht) (commutator_S h)
    (h.bcomm t ht ht3 ht1)

private lemma r891_card_layer_lt_card_S {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℤ) ^ (3 * n) * ((2 : ℤ) ^ (2 * n) - 1) *
        ((2 : ℤ) ^ (3 * n) - R891Pi n) <
      (2 : ℤ) ^ (3 * n) * (((2 : ℤ) ^ (3 * n)) ^ 2 - 1) := by
  set A : ℤ := 2 ^ (3 * n) with hA
  set B : ℤ := 2 ^ (2 * n) with hB
  have hlt : B < A := by
    rw [hA, hB]
    apply pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2)
    omega
  have hA2 : (2 : ℤ) ≤ A := by
    rw [hA]
    have h3 : 1 ≤ 3 * n := by omega
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * n) := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h3
  have hpos : (0 : ℤ) < A := by linarith
  have hpi : R891Pi n = 1 ∨ R891Pi n = -1 := by
    rw [R891Pi]
    rcases Nat.even_or_odd n with h | h
    · exact Or.inl (Even.neg_one_pow h)
    · exact Or.inr (Odd.neg_one_pow h)
  rcases hpi with hpi | hpi
  · rw [hpi]
    have h1 : B - 1 < A + 1 := by linarith
    have h3 : (0 : ℤ) < A - 1 := by linarith
    calc A * (B - 1) * (A - 1)
        < A * (A + 1) * (A - 1) := by
          exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 hpos) h3
      _ = A * (A ^ 2 - 1) := by ring
  · rw [hpi]
    have h1 : B - 1 < A - 1 := by linarith
    have h3 : (0 : ℤ) < A + 1 := by linarith
    calc A * (B - 1) * (A + 1)
        < A * (A - 1) * (A + 1) := by
          exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 hpos) h3
      _ = A * (A ^ 2 - 1) := by ring

private lemma r891_card_S_int {Y : Type} [Group Y] {n : ℕ} {T : Subgroup Y}
    (hT : Nat.card T = 2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1)) :
    (Nat.card T : ℤ) = (2 : ℤ) ^ (3 * n) * (((2 : ℤ) ^ (3 * n)) ^ 2 - 1) := by
  rw [hT, Nat.cast_mul]
  have hle : (1 : ℕ) ≤ ((2 : ℕ) ^ (3 * n)) ^ 2 := Nat.one_le_pow 2 _ (by positivity)
  rw [Nat.cast_sub hle]
  push_cast
  ring

variable [Finite X]

theorem map_zpowers_ne (h : R891D4Setup n S B) {s t : X} (hs : s ∈ S) (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) (ht : t ∈ B) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (φ : MulAut X) :
    (zpowers s).map φ.toMonoidHom ≠ zpowers t := by
  intro hmap
  have hφs_mem : φ s ∈ zpowers t := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom (Subgroup.mem_zpowers s)
  have ht_mem : t ∈ zpowers (φ s) := by
    have ht' : t ∈ (zpowers s).map φ.toMonoidHom := by
      rw [hmap]
      exact Subgroup.mem_zpowers t
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp ht'
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    change (φ.toMonoidHom s) ^ k = t
    rw [← map_zpow φ.toMonoidHom s k, hk, hxeq]
  have hzp : zpowers (φ s) = zpowers t :=
    le_antisymm (Subgroup.zpowers_le.mpr hφs_mem) (Subgroup.zpowers_le.mpr ht_mem)
  have hcent_eq : Subgroup.centralizer ({φ s} : Set X) =
      Subgroup.centralizer ({t} : Set X) := by
    have h1 : Subgroup.centralizer ({φ s} : Set X) =
        Subgroup.centralizer (↑(zpowers (φ s)) : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : Subgroup.centralizer ({t} : Set X) =
        Subgroup.centralizer (↑(zpowers t) : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h1, h2, hzp]
  have hCmap : (Subgroup.centralizer ({s} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ s} : Set X) := CFSG.centralizer_singleton_map φ s
  obtain ⟨R, hR⟩ := h.layer s hs hs3 hs1
  have hcomm_le : ⁅Subgroup.centralizer ({t} : Set X),
      Subgroup.centralizer ({t} : Set X)⁆ ≤ R.map φ.toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [← hcent_eq] at ha hb
    have ha₀ : φ.symm a ∈ Subgroup.centralizer ({s} : Set X) := by
      have ha' : a ∈ (Subgroup.centralizer ({s} : Set X)).map φ.toMonoidHom := by
        rw [hCmap]
        exact ha
      exact Subgroup.mem_map_equiv.mp ha'
    have hb₀ : φ.symm b ∈ Subgroup.centralizer ({s} : Set X) := by
      have hb' : b ∈ (Subgroup.centralizer ({s} : Set X)).map φ.toMonoidHom := by
        rw [hCmap]
        exact hb
      exact Subgroup.mem_map_equiv.mp hb'
    have hc := hR.commutator_mem (φ.symm a) ha₀ (φ.symm b) hb₀
    have hmem := Subgroup.mem_map_of_mem φ.toMonoidHom hc
    simpa [commutatorElement_def] using hmem
  have hS_le_R : S ≤ R.map φ.toMonoidHom := by
    rw [← commutator_centralizer_eq h ht ht3 ht1]
    exact hcomm_le
  have hcard_le : Nat.card S ≤ Nat.card R := by
    calc Nat.card S ≤ Nat.card (R.map φ.toMonoidHom) := Subgroup.card_le_of_le hS_le_R
      _ = Nat.card R := Subgroup.card_map_of_injective φ.injective
  have hRcard : (Nat.card R : ℤ) =
      2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - R891Pi n) :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core.primeCore_sl3Two hR.sl3Two
  have hScard' : Nat.card S = 2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) := by
    rw [card_S h]
    rw [show (2 ^ n) ^ 3 = 2 ^ (3 * n) by rw [← pow_mul, mul_comm]]
  have hlt : Nat.card R < Nat.card S := by
    have hlt' : (Nat.card R : ℤ) < (Nat.card S : ℤ) := by
      rw [hRcard, r891_card_S_int hScard']
      exact r891_card_layer_lt_card_S h.one_le
    exact_mod_cast hlt'
  exact (not_le_of_gt hlt) hcard_le

end R891D4Setup

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
