module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveB
import CFSG.GroupTheory.CoprimeCommutatorSelf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_45_BorelData (D : Data G) (X : Subgroup G) (p r : ℕ) : Prop :=
  (¬ p ∣ Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ∧
    (D.T ⊓ X).relIndex
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2 ∧
    (Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))).factorization r = 2 ∧
    (Nat.card ↥X).factorization r = 2) ∧
  ∀ y : G, GapWitness D X p y →
    Subgroup.centralizer (Subgroup.zpowers y : Set G) ⊓
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤ D.T ⊓ X

theorem s17_45_le_zpowers_sup_normalizer {D : Data G} {X A : Subgroup G} {p r : ℕ} {y : G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (φ : ↥D.M →* DihedralGroup p)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    (hy : GapWitness D X p y)
    (hAK : CFSG.ABGLocalTools.IsSylowOf r A
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)))
    (hKrel : (D.T ⊓ X).relIndex
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2)
    (hKfact : (Nat.card ↥(X ⊓ Subgroup.normalizer
      ((D.T ⊓ X : Subgroup G) : Set G))).factorization r = 2)
    (hAy : Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G))
    (hAc : A ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G) = ⊥) :
    A ≤ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) := by
  classical
  obtain ⟨hyM, hyN, hyord, hyTN, hyT⟩ := hy
  set Q : Subgroup G := D.T ⊓ X with hQ
  set C : Subgroup G := F08.CentOverO2 D.M X with hC
  set N : Subgroup G := X ⊔ C with hN
  set K : Subgroup G := X ⊓ Subgroup.normalizer (Q : Set G) with hK
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hT2 : IsPGroup 2 ↥D.T := D.sylowM.isPGroup
  have hCM : C ≤ D.M := fun x hx => (mem_centOverO2_iff.mp hx).1
  have hCN : C ≤ Subgroup.normalizer (X : Set G) := hCM.trans hMX
  have hNM : N ≤ D.M := sup_le hXM hCM
  have hAK' : CFSG.ABGLocalTools.IsSylowOf r A K := by
    rw [hK, hQ]; exact hAK
  have hKrel' : Q.relIndex K = r ^ 2 := by
    rw [hK, hQ]; exact hKrel
  have hKfact' : (Nat.card ↥K).factorization r = 2 := by
    rw [hK, hQ]; exact hKfact
  have hAKle : A ≤ K := hAK'.le
  have hAsyl : IsPGroup r ↥A := hAK'.isPGroup
  have hAcard : Nat.card ↥A = r ^ 2 := by
    have h := @CFSG.ABGLocalTools.IsSylowOf.card_eq G _ r _ ⟨hr⟩ A K hAK'
    rw [h, hKfact']
  have hKleNQ : K ≤ Subgroup.normalizer (Q : Set G) := inf_le_right
  have hKleX : K ≤ X := inf_le_left
  have hAQle : A ≤ Subgroup.normalizer (Q : Set G) := hAKle.trans hKleNQ
  have hQK : Q ≤ K := le_inf inf_le_right Subgroup.le_normalizer
  have hQleT : Q ≤ D.T := inf_le_left
  have hQ2 : IsPGroup 2 ↥Q := hT2.to_le hQleT
  have hAQ : A ⊓ Q = ⊥ :=
    (IsPGroup.disjoint_of_ne (p₁ := r) (p₂ := 2) (hp₁ := ⟨hr⟩)
      (hp₂ := ⟨Nat.prime_two⟩) hr2 A Q hAsyl hQ2).eq_bot
  have hTK : D.T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK, hQ]
    exact s17_45_normalizes_borel hXM hMX
  have hTQ : D.T ≤ Subgroup.normalizer (Q : Set G) := by
    have hTX : D.T ≤ Subgroup.normalizer (X : Set G) := hTM.trans hMX
    intro t ht
    exact CFSG.ABGLocalTools.mem_normalizer_inf (Subgroup.le_normalizer ht) (hTX ht)
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := by
    have hyX : y ∈ Subgroup.normalizer (X : Set G) := hMX hyM
    have hQeq : Q = (D.T ⊓ N) ⊓ X := by
      rw [hQ, hN]
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxT, hxX⟩
        exact ⟨⟨hxT, Subgroup.mem_sup_left hxX⟩, hxX⟩
      · rintro ⟨⟨hxT, -⟩, hxX⟩
        exact ⟨hxT, hxX⟩
    rw [hQeq]
    exact CFSG.ABGLocalTools.mem_normalizer_inf hyTN hyX
  have hTinfK : D.T ⊓ K = Q :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans hKleX)) (le_inf hQleT hQK)
  have hAab : ∀ u v : ↥A, u * v = v * u := fun u v =>
    @IsPGroup.commutative_of_card_eq_prime_sq r ↥A _ ⟨hr⟩ hAcard u v
  have hO2_le_Q : CFSG.Open.pCoreOf 2 X ≤ Q := by
    have hO2leX : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
    have hO2leM : CFSG.Open.pCoreOf 2 X ≤ D.M := hO2leX.trans hXM
    have hO2p : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 X) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hMN : D.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
      hMX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
    have hTn : D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := hTM.trans hMN
    have hsup2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 X ⊔ D.T) :=
      hO2p.to_sup_of_normal_left' hT2 hTn
    have heq : CFSG.Open.pCoreOf 2 X ⊔ D.T = D.T :=
      @CFSG.ABGLocalTools.IsSylowOf.eq_of_le G _ 2 _ ⟨Nat.prime_two⟩ D.T
        (CFSG.Open.pCoreOf 2 X ⊔ D.T) D.M D.sylowM le_sup_right
        (sup_le hO2leM hTM) hsup2
    exact le_inf (le_sup_left.trans (le_of_eq heq)) hO2leX
  have hKcard : r ^ 2 * Nat.card ↥Q = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card Q K
    rw [inf_eq_left.mpr hQK, hKrel'] at h
    exact h
  have hK_eq : K = A ⊔ Q := by
    have hcard : Nat.card ↥(A ⊔ Q) * Nat.card ↥(A ⊓ Q) =
        Nat.card ↥A * Nat.card ↥Q :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hAQle
    rw [hAQ, Subgroup.card_bot, mul_one, hAcard] at hcard
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hAKle hQK) ?_).symm
    rw [← hKcard]
    exact hcard.ge
  have hKmem : ∀ x : G, x ∈ K ↔ ∃ b ∈ A, ∃ q ∈ Q, b * q = x := by
    intro x
    have hmem : x ∈ (A ⊔ Q : Subgroup G) ↔ ∃ b ∈ A, ∃ q ∈ Q, b * q = x := by
      show x ∈ ((A ⊔ Q : Subgroup G) : Set G) ↔ _
      rw [Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQle]
      exact Set.mem_mul
    rw [hK_eq]
    exact hmem
  have hNmem : ∀ x : G, x ∈ N ↔ ∃ a ∈ X, ∃ c ∈ C, a * c = x := by
    intro x
    have hmem : x ∈ (X ⊔ C : Subgroup G) ↔ ∃ a ∈ X, ∃ c ∈ C, a * c = x := by
      show x ∈ ((X ⊔ C : Subgroup G) : Set G) ↔ _
      rw [Subgroup.coe_mul_of_right_le_normalizer_left X C hCN]
      exact Set.mem_mul
    rw [hN]
    exact hmem
  have hS3 : ∀ s ∈ D.T, s ∈ N → ∀ b : ↥A, ⁅s, (b:G)⁆ ∈ Q := by
    intro s hsT hsN b
    obtain ⟨x, hxX, c, hcC, hxc⟩ := (hNmem s).mp hsN
    have hc_comm : ∀ l ∈ X, ⁅c, l⁆ ∈ CFSG.Open.pCoreOf 2 X := by
      intro l hl
      simpa [commutatorElement_def] using (mem_centOverO2_iff.mp hcC).2 l hl
    have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmap : Q.map (MulAut.conj c).toMonoidHom ≤ Q := by
        intro z hz
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
        change (MulAut.conj c) q ∈ Q
        rw [MulAut.conj_apply]
        have hqX : q ∈ X := (Subgroup.mem_inf.mp hq).2
        have hcq : ⁅c, q⁆ ∈ Q := hO2_le_Q (hc_comm q hqX)
        have heq : c * q * c⁻¹ = ⁅c, q⁆ * q := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact Q.mul_mem hcq hq
      have hcard : Nat.card ↥(Q.map (MulAut.conj c).toMonoidHom) = Nat.card ↥Q :=
        Subgroup.card_map_of_injective (MulAut.conj c).injective
      exact Subgroup.eq_of_le_of_card_ge hmap hcard.ge
    have hsQ : s ∈ Subgroup.normalizer (Q : Set G) := hTQ hsT
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := by
      have hxeq : x = s * c⁻¹ := by rw [← hxc]; group
      rw [hxeq]
      exact Subgroup.mul_mem _ hsQ (Subgroup.inv_mem _ hcQ)
    have hxK : x ∈ K := by
      rw [hK]
      exact Subgroup.mem_inf.mpr ⟨hxX, hxQ⟩
    have hcb : ⁅c, (b:G)⁆ ∈ Q := by
      have hbX : (b:G) ∈ X := hKleX (hAKle b.2)
      exact hO2_le_Q (hc_comm (b:G) hbX)
    have hxb : ⁅x, (b:G)⁆ ∈ Q := by
      obtain ⟨a, haA, q, hqQ, haq⟩ := (hKmem x).mp hxK
      have hcomm : ⁅x, (b:G)⁆ = a * ⁅q, (b:G)⁆ * a⁻¹ * ⁅a, (b:G)⁆ := by
        rw [← haq, commutatorElement_def, commutatorElement_def]; group
      rw [hcomm]
      have hbq : ⁅(b:G), q⁆ ∈ Q := by
        have h1 : (b:G) * q * (b:G)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hKleNQ (hAKle b.2)) q).mp hqQ
        have heq : ⁅(b:G), q⁆ = ((b:G) * q * (b:G)⁻¹) * q⁻¹ := by
          rw [commutatorElement_def]
        rw [heq]
        exact Q.mul_mem h1 (Q.inv_mem hqQ)
      have hqb : ⁅q, (b:G)⁆ ∈ Q := by
        have heq : ⁅q, (b:G)⁆ = ⁅(b:G), q⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact Q.inv_mem hbq
      have hab : ⁅a, (b:G)⁆ = 1 := by
        have hcomm' : a * (b:G) = (b:G) * a :=
          congrArg Subtype.val (hAab ⟨a, haA⟩ b)
        rw [commutatorElement_def, hcomm']
        group
      have haq_mem : a * ⁅q, (b:G)⁆ * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hKleNQ (hAKle haA)) ⁅q, (b:G)⁆).mp hqb
      rw [hab, mul_one]
      exact haq_mem
    have hcomm : ⁅x * c, (b:G)⁆ = x * ⁅c, (b:G)⁆ * x⁻¹ * ⁅x, (b:G)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [← hxc, hcomm]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hxQ ⁅c, (b:G)⁆).mp hcb) hxb
  have hcomm_mem_K : ∀ b : ↥A, ∀ t ∈ D.T, ⁅(b:G), t⁆ ∈ K := by
    intro b t ht
    have hbK : (b:G) ∈ K := hAKle b.2
    have htK : t * (b:G) * t⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK ht) (b:G)).mp hbK
    have heq : ⁅(b:G), t⁆ = (b:G) * (t * (b:G) * t⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact K.mul_mem hbK (K.inv_mem htK)
  have hNT_fwd : ∀ b : ↥A, (b:G) ∈ Subgroup.normalizer (D.T : Set G) →
      ∀ t ∈ D.T, ⁅(b:G), t⁆ ∈ Q := by
    intro b hb t ht
    rw [← hTinfK]
    refine Subgroup.mem_inf.mpr ⟨?_, hcomm_mem_K b t ht⟩
    have hbt : (b:G) * t * (b:G)⁻¹ ∈ D.T :=
      (Subgroup.mem_normalizer_iff.mp hb t).mp ht
    have heq : ⁅(b:G), t⁆ = ((b:G) * t * (b:G)⁻¹) * t⁻¹ := by
      rw [commutatorElement_def]
    rw [heq]
    exact D.T.mul_mem hbt (D.T.inv_mem ht)
  have hnt_of_comm : ∀ b : ↥A, (∀ t ∈ D.T, ⁅(b:G), t⁆ ∈ Q) →
      (b:G) ∈ Subgroup.normalizer (D.T : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : D.T.map (MulAut.conj (b:G)).toMonoidHom ≤ D.T := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
      change (MulAut.conj (b:G)) t ∈ D.T
      rw [MulAut.conj_apply]
      have hq : ⁅(b:G), t⁆ ∈ Q := hb t ht
      have heq : (b:G) * t * (b:G)⁻¹ = ⁅(b:G), t⁆ * t := by
        rw [commutatorElement_def]; group
      rw [heq]
      exact D.T.mul_mem (hQleT hq) ht
    have hcard : Nat.card ↥(D.T.map (MulAut.conj (b:G)).toMonoidHom) = Nat.card ↥D.T :=
      Subgroup.card_map_of_injective (MulAut.conj (b:G)).injective
    exact Subgroup.eq_of_le_of_card_ge hmap hcard.ge
  by_cases hTN : D.T ≤ N
  · have hAle : A ≤ Subgroup.normalizer (D.T : Set G) := by
      intro a ha
      let ab : ↥A := ⟨a, ha⟩
      have hab : (ab : G) = a := rfl
      refine hnt_of_comm ab ?_
      intro t ht
      have hq : ⁅t, (ab : G)⁆ ∈ Q := hS3 t ht (hTN ht) ab
      have heq : ⁅(ab : G), t⁆ = ⁅t, (ab : G)⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [heq]
      exact Q.inv_mem hq
    exact hAle.trans le_sup_right
  · obtain ⟨τ, hτT, hτN⟩ := Set.not_subset.mp hTN
    have hτM : τ ∈ D.M := hTM hτT
    have hTKmem : τ ∈ Subgroup.normalizer (K : Set G) := hTK hτT
    let ψ : ↥D.T →* DihedralGroup p := φ.comp (Subgroup.inclusion hTM)
    have hψ_apply : ∀ w : ↥D.T, ψ w = φ ⟨(w:G), hTM w.2⟩ := fun w => rfl
    have hψ2 : ∀ w : ↥D.T, ∃ k, (ψ w) ^ 2 ^ k = 1 := by
      intro w
      obtain ⟨k, hk⟩ := hT2 w
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hcases : ∀ d : DihedralGroup p, (∃ i, d = DihedralGroup.r i) ∨
        (∃ i, d = DihedralGroup.sr i) := by
      intro d
      cases d with
      | r i => exact Or.inl ⟨i, rfl⟩
      | sr i => exact Or.inr ⟨i, rfl⟩
    have h_two : ∀ z : DihedralGroup p, z ≠ 1 → (∃ k, z ^ 2 ^ k = 1) →
        ∃ i, z = DihedralGroup.sr i := by
      intro z hz h2
      rcases hcases z with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨k, hk⟩ := h2
        have hdvdp : orderOf (DihedralGroup.r i) ∣ p :=
          orderOf_dvd_iff_pow_eq_one.mpr (by
            rw [DihedralGroup.r_pow, ZMod.natCast_self, mul_zero, DihedralGroup.r_zero])
        have hdvd2 : orderOf (DihedralGroup.r i) ∣ 2 ^ k :=
          orderOf_dvd_iff_pow_eq_one.mpr hk
        rcases (Nat.dvd_prime hp).mp hdvdp with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hz
        · rw [h1] at hdvd2
          have hp2dvd : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hdvd2
          exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd) hp2
      · exact ⟨i, rfl⟩
    have hφτ_ne : ψ ⟨τ, hτT⟩ ≠ 1 := by
      intro h1
      have h1' : φ ⟨τ, hτM⟩ = 1 := by
        rw [← hψ_apply ⟨τ, hτT⟩]
        exact h1
      have hmem : (⟨τ, hτM⟩ : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr h1'
      rw [hker] at hmem
      exact hτN (Subgroup.mem_subgroupOf.mp hmem)
    have hφτ_ord2 : orderOf (ψ ⟨τ, hτT⟩) = 2 := by
      obtain ⟨i, hi⟩ := h_two _ hφτ_ne (hψ2 ⟨τ, hτT⟩)
      rw [hi, DihedralGroup.orderOf_sr]
    have hφτ_ord2' : orderOf (φ ⟨τ, hτM⟩) = 2 := by
      rw [← hψ_apply ⟨τ, hτT⟩]
      exact hφτ_ord2
    have hφy_ne : φ ⟨y, hyM⟩ ≠ 1 := by
      intro h1
      have hmem : (⟨y, hyM⟩ : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      rw [hker] at hmem
      exact hyN (Subgroup.mem_subgroupOf.mp hmem)
    have hφy_ord : orderOf (φ ⟨y, hyM⟩) = p := by
      have hdvd : orderOf (φ ⟨y, hyM⟩) ∣ orderOf (⟨y, hyM⟩ : ↥D.M) :=
        orderOf_map_dvd φ _
      have hyord' : orderOf (⟨y, hyM⟩ : ↥D.M) = p := by
        rw [← Subgroup.orderOf_coe]
        exact hyord
      rw [hyord'] at hdvd
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hφy_ne
      · exact h1
    obtain ⟨j, hjy⟩ : ∃ j, φ ⟨y, hyM⟩ = DihedralGroup.r j := by
      rcases hcases (φ ⟨y, hyM⟩) with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, hi⟩
      · rw [hi, DihedralGroup.orderOf_sr] at hφy_ord
        exact absurd hφy_ord.symm hp2
    have hφconj : φ ⟨τ * y * τ⁻¹,
        D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM)⟩ =
        (φ ⟨y, hyM⟩)⁻¹ := by
      have hτy_eq : (⟨τ * y * τ⁻¹,
          D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM)⟩ : ↥D.M) =
          ⟨τ, hτM⟩ * ⟨y, hyM⟩ * ⟨τ, hτM⟩⁻¹ := Subtype.ext (by simp)
      rw [hτy_eq, map_mul, map_mul, map_inv]
      obtain ⟨i, hi⟩ := h_two (ψ ⟨τ, hτT⟩) hφτ_ne (hψ2 ⟨τ, hτT⟩)
      have hi' : φ ⟨τ, hτM⟩ = DihedralGroup.sr i := by
        rw [← hψ_apply ⟨τ, hτT⟩]
        exact hi
      rw [hi', hjy, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
    have hφ_eq_of_notMem : ∀ t (ht : t ∈ D.T), t ∉ N → ψ ⟨t, ht⟩ = ψ ⟨τ, hτT⟩ := by
      intro t ht htN
      have hψt_ne : ψ ⟨t, ht⟩ ≠ 1 := by
        intro h1
        have h2 : φ ⟨t, hTM ht⟩ = 1 := by
          rw [← hψ_apply ⟨t, ht⟩]
          exact h1
        exact htN (by
          have hker' : (⟨t, hTM ht⟩ : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr h2
          rw [hker] at hker'
          exact Subgroup.mem_subgroupOf.mp hker')
      obtain ⟨i, hi⟩ := h_two _ hψt_ne (hψ2 ⟨t, ht⟩)
      obtain ⟨i', hi'⟩ := h_two _ hφτ_ne (hψ2 ⟨τ, hτT⟩)
      have hprod2 : ∃ k, (ψ ⟨t, ht⟩ * (ψ ⟨τ, hτT⟩)⁻¹) ^ 2 ^ k = 1 := by
        obtain ⟨k, hk⟩ := hψ2 (⟨t, ht⟩ * ⟨τ, hτT⟩⁻¹)
        refine ⟨k, ?_⟩
        rwa [map_mul, map_inv] at hk
      have hz_rot : ψ ⟨t, ht⟩ * (ψ ⟨τ, hτT⟩)⁻¹ = DihedralGroup.r (i' - i) := by
        rw [hi, hi', DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
      by_cases hz : ψ ⟨t, ht⟩ * (ψ ⟨τ, hτT⟩)⁻¹ = 1
      · have heqψ : ψ ⟨t, ht⟩ = ψ ⟨τ, hτT⟩ := by
          calc ψ ⟨t, ht⟩ = ψ ⟨t, ht⟩ * (ψ ⟨τ, hτT⟩)⁻¹ * ψ ⟨τ, hτT⟩ := by group
            _ = 1 * ψ ⟨τ, hτT⟩ := by rw [hz]
            _ = ψ ⟨τ, hτT⟩ := one_mul _
        exact heqψ
      · obtain ⟨i'', hi''⟩ := h_two _ hz hprod2
        rw [hz_rot] at hi''
        exact absurd hi'' (by intro h; cases h)
    have hcoset : ∀ t (ht : t ∈ D.T), (∃ s ∈ D.T ⊓ N, t = s) ∨
        (∃ s ∈ D.T ⊓ N, t = τ * s) := by
      intro t ht
      by_cases htN : t ∈ N
      · exact Or.inl ⟨t, Subgroup.mem_inf.mpr ⟨ht, htN⟩, rfl⟩
      · have hφt : ψ ⟨t, ht⟩ = ψ ⟨τ, hτT⟩ := hφ_eq_of_notMem t ht htN
        have hmemT : τ⁻¹ * t ∈ D.T := D.T.mul_mem (D.T.inv_mem hτT) ht
        have hmemM : τ⁻¹ * t ∈ D.M := hTM hmemT
        have h1 : φ ⟨τ⁻¹ * t, hmemM⟩ = 1 := by
          have h2 : (⟨τ⁻¹ * t, hmemM⟩ : ↥D.M) = ⟨τ, hτM⟩⁻¹ * ⟨t, hTM ht⟩ :=
            Subtype.ext (by simp)
          rw [h2, map_mul, map_inv, ← hψ_apply ⟨τ, hτT⟩, ← hψ_apply ⟨t, ht⟩, hφt,
            inv_mul_cancel]
        have hsN : τ⁻¹ * t ∈ N := by
          have hker' : (⟨τ⁻¹ * t, hmemM⟩ : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
          rw [hker] at hker'
          exact Subgroup.mem_subgroupOf.mp hker'
        exact Or.inr ⟨τ⁻¹ * t, Subgroup.mem_inf.mpr ⟨hmemT, hsN⟩, by group⟩
    have hNT_iff : ∀ b : ↥A, (b:G) ∈ Subgroup.normalizer (D.T : Set G) ↔
        ⁅(b:G), τ⁆ ∈ Q := by
      intro b
      constructor
      · intro hb
        exact hNT_fwd b hb τ hτT
      · intro hbτ
        refine hnt_of_comm b ?_
        intro t ht
        rcases hcoset t ht with ⟨s, hs, hts⟩ | ⟨s, hs, hts⟩
        · rw [hts]
          have hqs : ⁅(b:G), s⁆ ∈ Q := by
            have heq : ⁅(b:G), s⁆ = ⁅s, (b:G)⁆⁻¹ := by
              rw [commutatorElement_def, commutatorElement_def]; group
            rw [heq]
            exact Q.inv_mem (hS3 s hs.1 hs.2 b)
          exact hqs
        · rw [hts]
          have hqs : ⁅(b:G), s⁆ ∈ Q := by
            have heq : ⁅(b:G), s⁆ = ⁅s, (b:G)⁆⁻¹ := by
              rw [commutatorElement_def, commutatorElement_def]; group
            rw [heq]
            exact Q.inv_mem (hS3 s hs.1 hs.2 b)
          have h1 : ⁅(b:G), τ * s⁆ = ⁅(b:G), τ⁆ * (τ * ⁅(b:G), s⁆ * τ⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]; group
          rw [h1]
          exact Q.mul_mem hbτ
            ((Subgroup.mem_normalizer_iff.mp (hTQ hτT) ⁅(b:G), s⁆).mp hqs)
    have hstep5 : ∃ s ∈ D.T ⊓ N, τ * y * τ⁻¹ = y⁻¹ * s := by
      have hHmem : τ * y * τ⁻¹ ∈ Subgroup.zpowers y ⊔ (D.T ⊓ N) := by
        have hyH : y ∈ Subgroup.zpowers y ⊔ (D.T ⊓ N) :=
          Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
        exact (Subgroup.mem_normalizer_iff.mp (hyT hτT) y).mp hyH
      have hHmul : ((Subgroup.zpowers y ⊔ (D.T ⊓ N) : Subgroup G) : Set G) =
          (Subgroup.zpowers y : Set G) * ((D.T ⊓ N) : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (Subgroup.zpowers_le.mpr hyTN)
      have hHmemS : τ * y * τ⁻¹ ∈
          ((Subgroup.zpowers y ⊔ (D.T ⊓ N) : Subgroup G) : Set G) := hHmem
      obtain ⟨g, hg, s, hs, hgs⟩ := Set.mem_mul.mp (hHmul ▸ hHmemS)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hgM : g ∈ D.M := Subgroup.zpowers_le.mpr hyM hg
      have hsM : s ∈ D.M := hNM hs.2
      have hτyM : τ * y * τ⁻¹ ∈ D.M :=
        D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM)
      have helem : (⟨τ * y * τ⁻¹, hτyM⟩ : ↥D.M) = ⟨g * s, D.M.mul_mem hgM hsM⟩ :=
        Subtype.ext hgs.symm
      have h1 : φ ⟨τ * y * τ⁻¹, hτyM⟩ = (φ ⟨y, hyM⟩)⁻¹ := hφconj
      have hs_ker : φ ⟨s, hsM⟩ = 1 := by
        have hmem : (⟨s, hsM⟩ : ↥D.M) ∈ φ.ker := by
          rw [hker]
          exact Subgroup.mem_subgroupOf.mpr hs.2
        exact MonoidHom.mem_ker.mp hmem
      have h3 : φ ⟨g, hgM⟩ = (φ ⟨y, hyM⟩) ^ k := by
        have h2 : (⟨g, hgM⟩ : ↥D.M) = ⟨y, hyM⟩ ^ k := by
          apply Subtype.ext
          change g = y ^ k
          exact hk.symm
        rw [h2, map_zpow]
      have h4 : (φ ⟨y, hyM⟩) ^ k = (φ ⟨y, hyM⟩)⁻¹ := by
        have h5 : φ (⟨g, hgM⟩ * ⟨s, hsM⟩) = (φ ⟨y, hyM⟩)⁻¹ := by
          have h5' : φ ⟨g * s, D.M.mul_mem hgM hsM⟩ = (φ ⟨y, hyM⟩)⁻¹ := by
            rw [← helem]
            exact h1
          simpa using h5'
        rw [map_mul, hs_ker, mul_one] at h5
        rw [← h3]
        exact h5
      have hkp1 : (φ ⟨y, hyM⟩) ^ (k + 1) = 1 := by
        rw [zpow_add_one, h4, inv_mul_cancel]
      have hpdvd : (p : ℤ) ∣ k + 1 := by
        rw [← hφy_ord]
        exact (orderOf_dvd_iff_zpow_eq_one (x := φ ⟨y, hyM⟩) (i := k + 1)).mpr hkp1
      have hyp1 : y ^ (k + 1) = 1 := by
        have h : (↑(orderOf y) : ℤ) ∣ k + 1 := by
          rwa [hyord]
        exact (orderOf_dvd_iff_zpow_eq_one (x := y) (i := k + 1)).mp h
      have hyk : y ^ k = y⁻¹ := by
        have h1' : y ^ k * y = 1 := by
          rw [← zpow_add_one]
          exact hyp1
        calc y ^ k = y ^ k * y * y⁻¹ := by group
          _ = 1 * y⁻¹ := by rw [h1']
          _ = y⁻¹ := one_mul _
      refine ⟨s, hs, ?_⟩
      calc τ * y * τ⁻¹ = g * s := hgs.symm
        _ = y ^ k * s := by rw [← hk]
        _ = y⁻¹ * s := by rw [hyk]
    have hσ_exists : ∀ a : ↥A, ∃ b : ↥A, ∃ q ∈ Q, τ * (a:G) * τ⁻¹ = (b:G) * q := by
      intro a
      have hmemK : τ * (a:G) * τ⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hTKmem (a:G)).mp (hAKle a.2)
      obtain ⟨b, hbA, q, hqQ, hbq⟩ := (hKmem (τ * (a:G) * τ⁻¹)).mp hmemK
      exact ⟨⟨b, hbA⟩, q, hqQ, hbq.symm⟩
    let σ : ↥A → ↥A := fun a => Classical.choose (hσ_exists a)
    have hσ_spec : ∀ a : ↥A, ∃ q ∈ Q, τ * (a:G) * τ⁻¹ = (σ a : G) * q :=
      fun a => Classical.choose_spec (hσ_exists a)
    have hσ_uniq : ∀ (b₁ b₂ : ↥A) (q₁ q₂ : G), q₁ ∈ Q → q₂ ∈ Q →
        (b₁:G) * q₁ = (b₂:G) * q₂ → b₁ = b₂ := by
      intro b₁ b₂ q₁ q₂ hq₁ hq₂ h
      have hmem : (b₂:G)⁻¹ * (b₁:G) ∈ Q := by
        have h' : (b₂:G)⁻¹ * (b₁:G) = q₂ * q₁⁻¹ := by
          calc (b₂:G)⁻¹ * (b₁:G) = (b₂:G)⁻¹ * ((b₂:G) * q₂ * q₁⁻¹) := by rw [← h]; group
            _ = q₂ * q₁⁻¹ := by group
        rw [h']
        exact Q.mul_mem hq₂ (Q.inv_mem hq₁)
      have hA : (b₂:G)⁻¹ * (b₁:G) ∈ A := A.mul_mem (A.inv_mem b₂.2) b₁.2
      have hbot : (b₂:G)⁻¹ * (b₁:G) ∈ (⊥ : Subgroup G) := by
        rw [← hAQ]
        exact Subgroup.mem_inf.mpr ⟨hA, hmem⟩
      have h1 : (b₂:G)⁻¹ * (b₁:G) = 1 := Subgroup.mem_bot.mp hbot
      apply Subtype.ext
      calc (b₁:G) = (b₂:G) * ((b₂:G)⁻¹ * (b₁:G)) := by group
        _ = (b₂:G) * 1 := by rw [h1]
        _ = (b₂:G) := mul_one _
    have hσ_eq : ∀ (a : ↥A) {b : ↥A} {q : G}, q ∈ Q →
        τ * (a:G) * τ⁻¹ = (b:G) * q → σ a = b := by
      intro a b q hq h
      obtain ⟨q', hq', h'⟩ := hσ_spec a
      exact hσ_uniq (σ a) b q' q hq' hq (h'.symm.trans h)
    have hσ_mul : ∀ a b : ↥A, σ (a * b) = σ a * σ b := by
      intro a b
      obtain ⟨qa, hqa, hqa'⟩ := hσ_spec a
      obtain ⟨qb, hqb, hqb'⟩ := hσ_spec b
      refine hσ_eq (a * b) (b := σ a * σ b)
        (q := (σ b : G)⁻¹ * qa * (σ b : G) * qb) ?_ ?_
      · have h1 : (σ b : G)⁻¹ * qa * (σ b : G) ∈ Q := by
          simpa using
            (Subgroup.mem_normalizer_iff.mp (hKleNQ (hAKle (A.inv_mem (σ b).2))) qa).mp hqa
        exact Q.mul_mem h1 hqb
      · have hsplit : τ * ((a:G) * (b:G)) * τ⁻¹ =
            (τ * (a:G) * τ⁻¹) * (τ * (b:G) * τ⁻¹) := by group
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hsplit, hqa', hqb']
        group
    have hσ_one : σ (1 : ↥A) = 1 :=
      hσ_eq (1 : ↥A) (q := 1) Q.one_mem (by rw [Subgroup.coe_one]; group)
    have hσ_inv : ∀ a : ↥A, σ a⁻¹ = (σ a)⁻¹ := by
      intro a
      have h1 : σ a * σ a⁻¹ = 1 := by
        rw [← hσ_mul, mul_inv_cancel, hσ_one]
      exact eq_inv_of_mul_eq_one_right h1
    have hτ2T : τ ^ 2 ∈ D.T := by
      rw [pow_two]
      exact D.T.mul_mem hτT hτT
    have hτ2N : τ ^ 2 ∈ N := by
      have hφτ2 : φ ⟨τ ^ 2, hTM hτ2T⟩ = 1 := by
        have h2 : (⟨τ ^ 2, hTM hτ2T⟩ : ↥D.M) = ⟨τ, hτM⟩ ^ 2 := Subtype.ext (by simp)
        rw [h2, map_pow, ← hφτ_ord2']
        exact pow_orderOf_eq_one _
      have hmem : (⟨τ ^ 2, hTM hτ2T⟩ : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr hφτ2
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have hσ_sq : ∀ a : ↥A, σ (σ a) = a := by
      intro a
      obtain ⟨qa, hqa, hqa'⟩ := hσ_spec a
      have hqs : ∃ q ∈ Q, τ ^ 2 * (a:G) * (τ ^ 2)⁻¹ = (a:G) * q := by
        have h1 : ⁅τ ^ 2, (a:G)⁆ ∈ Q := hS3 (τ ^ 2) hτ2T hτ2N a
        refine ⟨(a:G)⁻¹ * ⁅τ ^ 2, (a:G)⁆ * (a:G), ?_, ?_⟩
        · simpa using
            (Subgroup.mem_normalizer_iff.mp (hKleNQ (hAKle (A.inv_mem a.2))) _).mp h1
        · rw [commutatorElement_def]; group
      obtain ⟨q3, hq3, h3⟩ := hqs
      have hσa : (σ a : G) = τ * (a:G) * τ⁻¹ * qa⁻¹ := by
        rw [hqa']; group
      have h3' : (τ * τ) * (a:G) * (τ * τ)⁻¹ = (a:G) * q3 := by
        rw [← pow_two]
        exact h3
      have h4 : τ * (σ a : G) * τ⁻¹ = (a:G) * (q3 * (τ * qa * τ⁻¹)⁻¹) := by
        rw [hσa]
        rw [show τ * (τ * (a:G) * τ⁻¹ * qa⁻¹) * τ⁻¹ =
            (τ * τ) * (a:G) * (τ * τ)⁻¹ * (τ * qa * τ⁻¹)⁻¹ by group]
        rw [h3']
        group
      have hqτ : τ * qa * τ⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hTQ hτT) qa).mp hqa
      exact hσ_eq (σ a) (Q.mul_mem hq3 (Q.inv_mem hqτ)) h4
    have hσ_fix : ∀ a : ↥A, σ a = a ↔ (a:G) ∈ Subgroup.normalizer (D.T : Set G) := by
      intro a
      let a' : ↥A := a⁻¹
      have ha' : (a' : G) = (a:G)⁻¹ := rfl
      have hanti : ∀ x : ↥A, ⁅(x:G), τ⁆ = (x:G) * τ * (x:G)⁻¹ * τ⁻¹ :=
        fun x => commutatorElement_def _ _
      constructor
      · intro h
        obtain ⟨q, hq, hspec⟩ := hσ_spec a
        rw [h] at hspec
        have hqeq : q = ⁅(a' : G), τ⁆ := by
          rw [hanti, ha']
          simp only [inv_inv]
          calc q = (a:G)⁻¹ * ((a:G) * q) := by group
            _ = (a:G)⁻¹ * (τ * (a:G) * τ⁻¹) := by rw [← hspec]
            _ = (a:G)⁻¹ * τ * (a:G) * τ⁻¹ := by group
        have hq' : ⁅(a' : G), τ⁆ ∈ Q := by rw [← hqeq]; exact hq
        have hainv : (a' : G) ∈ Subgroup.normalizer (D.T : Set G) := (hNT_iff a').mpr hq'
        have : (a:G)⁻¹ ∈ Subgroup.normalizer (D.T : Set G) := by rwa [← ha']
        simpa using Subgroup.inv_mem _ this
      · intro h
        have hainv : (a' : G) ∈ Subgroup.normalizer (D.T : Set G) := by
          rw [ha']
          exact Subgroup.inv_mem _ h
        have hq : ⁅(a' : G), τ⁆ ∈ Q := (hNT_iff a').mp hainv
        have heq : τ * (a:G) * τ⁻¹ = (a:G) * ⁅(a' : G), τ⁆ := by
          rw [hanti, ha']; group
        exact hσ_eq a hq heq
    have hyNA : y ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mp hAy
    let η : MulAut ↥A := A.normalizerMonoidHom ⟨y, hyNA⟩
    have hη_apply : ∀ b : ↥A, ((η b : ↥A) : G) = y * (b:G) * y⁻¹ :=
      fun b => Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨y, hyNA⟩ b
    have hηinv_apply : ∀ b : ↥A, ((η⁻¹ b : ↥A) : G) = y⁻¹ * (b:G) * y := by
      intro b
      have h1 : ((η (η⁻¹ b) : ↥A) : G) = y * ((η⁻¹ b : ↥A) : G) * y⁻¹ := hη_apply _
      have h2 : η (η⁻¹ b) = b := by simp
      rw [h2] at h1
      calc ((η⁻¹ b : ↥A) : G) = y⁻¹ * (y * ((η⁻¹ b : ↥A) : G) * y⁻¹) * y := by group
        _ = y⁻¹ * (b:G) * y := by rw [h1]
    have hηpow : η ^ p = 1 := by
      rw [show η = A.normalizerMonoidHom ⟨y, hyNA⟩ from rfl, ← map_pow]
      have h1 : (⟨y, hyNA⟩ : ↥(Subgroup.normalizer (A : Set G))) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyord]
        exact pow_orderOf_eq_one y
      rw [h1, map_one]
    have hη_fix_sq : ∀ a : ↥A, η (η a) = a → η a = a := by
      intro a ha
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
      have h2 : (η ^ 2) ^ ((p + 1) / 2) = η := by
        rw [← pow_mul, show 2 * ((p + 1) / 2) = p + 1 by omega, pow_succ, hηpow, one_mul]
      have hα : (η ^ 2) a = a := by simpa [pow_two] using ha
      have h3 : ∀ m : ℕ, ((η ^ 2) ^ m) a = a := by
        intro m
        induction m with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, MulAut.mul_apply, hα, ih]
      have h4 : ((η ^ 2) ^ ((p + 1) / 2)) a = a := h3 _
      rw [h2] at h4
      exact h4
    have hkey : ∀ b : ↥A, σ (η (σ b)) = η⁻¹ b := by
      intro b
      obtain ⟨qb, hqb, hqb'⟩ := hσ_spec (σ b)
      rw [hσ_sq] at hqb'
      obtain ⟨s, hs, hτys⟩ := hstep5
      have hsT : s ∈ D.T := hs.1
      have hsN : s ∈ N := hs.2
      have hsbq : ∃ qs ∈ Q, s * (b:G) * s⁻¹ = (b:G) * qs := by
        have h1 : ⁅s, (b:G)⁆ ∈ Q := hS3 s hsT hsN b
        refine ⟨(b:G)⁻¹ * ⁅s, (b:G)⁆ * (b:G), ?_, ?_⟩
        · simpa using
            (Subgroup.mem_normalizer_iff.mp (hKleNQ (hAKle (A.inv_mem b.2))) _).mp h1
        · rw [commutatorElement_def]; group
      obtain ⟨qs, hqs, hsbq'⟩ := hsbq
      have htQ : τ * y * τ⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
        rw [hτys]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyQ) (hTQ hsT)
      have ht_b : τ * y * τ⁻¹ * (b:G) * (τ * y * τ⁻¹)⁻¹ =
          (η⁻¹ b : G) * (y⁻¹ * qs * y) := by
        rw [hτys]
        rw [show y⁻¹ * s * (b:G) * (y⁻¹ * s)⁻¹ =
            y⁻¹ * (s * (b:G) * s⁻¹) * y by group]
        rw [hsbq', hηinv_apply]
        group
      have hq1 : y⁻¹ * qs * y ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyQ) qs).mp hqs
      have ht_qb : τ * y * τ⁻¹ * qb * (τ * y * τ⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp htQ qb).mp hqb
      have hfin : τ * (η (σ b) : G) * τ⁻¹ = (η⁻¹ b : G) *
          ((y⁻¹ * qs * y) * (τ * y * τ⁻¹ * qb * (τ * y * τ⁻¹)⁻¹)) := by
        have hησ : (η (σ b) : G) = y * (σ b : G) * y⁻¹ := hη_apply (σ b)
        rw [hησ]
        rw [show τ * (y * (σ b : G) * y⁻¹) * τ⁻¹ =
            (τ * y * τ⁻¹) * (τ * (σ b : G) * τ⁻¹) * (τ * y * τ⁻¹)⁻¹ by group]
        rw [hqb']
        rw [show (τ * y * τ⁻¹) * ((b:G) * qb) * (τ * y * τ⁻¹)⁻¹ =
            (τ * y * τ⁻¹ * (b:G) * (τ * y * τ⁻¹)⁻¹) *
              (τ * y * τ⁻¹ * qb * (τ * y * τ⁻¹)⁻¹) by group]
        rw [ht_b]
        group
      exact hσ_eq (η (σ b)) (Q.mul_mem hq1 ht_qb) hfin
    set A₀ : Subgroup G := A ⊓ Subgroup.normalizer (D.T : Set G) with hA₀
    have hFix : ∀ a : ↥A, σ a = a ↔ (a:G) ∈ A₀ := by
      intro a
      rw [hA₀]
      constructor
      · intro h
        exact Subgroup.mem_inf.mpr ⟨a.2, (hσ_fix a).mp h⟩
      · intro h
        exact (hσ_fix a).mpr (Subgroup.mem_inf.mp h).2
    have hA₀_sub : A₀ ≤ A := inf_le_left
    have hstep7 : ∀ a : ↥A, (a:G) ∈ A₀ → (η a : G) ∈ A₀ → a = 1 := by
      intro a haA₀ hηaA₀
      have ha_fix : σ a = a := (hFix a).mpr haA₀
      have hηa_fix : σ (η a) = η a := (hFix (η a)).mpr hηaA₀
      have hkey_a : σ (η (σ a)) = η⁻¹ a := hkey a
      rw [ha_fix, hηa_fix] at hkey_a
      have h2 : η (η a) = a := by
        have := congrArg η hkey_a
        simpa using this
      have hηa : η a = a := hη_fix_sq a h2
      have hcomm : (a:G) ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hya : y * (a:G) = (a:G) * y := by
          have h5 : ((η a : ↥A) : G) = y * (a:G) * y⁻¹ := hη_apply a
          rw [hηa] at h5
          calc y * (a:G) = (y * (a:G) * y⁻¹) * y := by group
            _ = (a:G) * y := by rw [← h5]
        rw [← hk]
        exact ((show Commute y (a:G) from hya).zpow_left k).eq
      have hbot : (a:G) ∈ (⊥ : Subgroup G) := by
        rw [← hAc]
        exact Subgroup.mem_inf.mpr ⟨a.2, hcomm⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    have hA₀_ne : A₀ ≠ ⊥ := by
      intro hbot
      have hσinv : ∀ a : ↥A, σ a = a⁻¹ := by
        intro a
        have hfix : σ (a * σ a) = a * σ a := by
          rw [hσ_mul, hσ_sq, hAab (σ a) a]
        have hmem : ((a * σ a : ↥A) : G) ∈ A₀ := (hFix (a * σ a)).mp hfix
        rw [hbot] at hmem
        have h1 : a * σ a = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
        exact eq_inv_of_mul_eq_one_right h1
      have htriv : ∀ a : ↥A, a = 1 := by
        intro a
        have h1 : σ (η (σ a)) = η⁻¹ a := hkey a
        have h2 : η (σ a) = (η a)⁻¹ := by
          rw [hσinv a]
          exact map_inv η a
        rw [h2, hσinv ((η a)⁻¹), inv_inv] at h1
        have h3 : η (η a) = a := by
          calc η (η a) = η (η⁻¹ a) := by rw [h1]
            _ = a := by simp
        have h4 : η a = a := hη_fix_sq a h3
        have hcomm : (a:G) ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
          have hya : y * (a:G) = (a:G) * y := by
            have h5 : ((η a : ↥A) : G) = y * (a:G) * y⁻¹ := hη_apply a
            rw [h4] at h5
            calc y * (a:G) = (y * (a:G) * y⁻¹) * y := by group
              _ = (a:G) * y := by rw [← h5]
          rw [← hk]
          exact ((show Commute y (a:G) from hya).zpow_left k).eq
        have hbot' : (a:G) ∈ (⊥ : Subgroup G) := by
          rw [← hAc]
          exact Subgroup.mem_inf.mpr ⟨a.2, hcomm⟩
        exact Subtype.ext (Subgroup.mem_bot.mp hbot')
      have hA_bot : A = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have h1 : (⟨z, hz⟩ : ↥A) = 1 := htriv ⟨z, hz⟩
        have h2 : z = 1 := congrArg Subtype.val h1
        simpa [h2]
      have hcard : Nat.card ↥A = 1 := by rw [hA_bot, Subgroup.card_bot]
      rw [hAcard] at hcard
      nlinarith [hr.two_le]
    by_cases hA₀top : A₀ = A
    · have hAle : A ≤ Subgroup.normalizer (D.T : Set G) := by
        rw [← hA₀top]
        exact inf_le_right
      exact hAle.trans le_sup_right
    · have hA₀card : Nat.card ↥A₀ = r := by
        have hdvd : Nat.card ↥A₀ ∣ r ^ 2 := by
          have h1 : Nat.card ↥A₀ ∣ Nat.card ↥A := by
            have h := Subgroup.card_subgroup_dvd_card (A₀.subgroupOf A)
            rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀_sub).toEquiv] at h
          rwa [hAcard] at h1
        obtain ⟨m, hm, hmr⟩ := (Nat.dvd_prime_pow hr).mp hdvd
        interval_cases m
        · rw [pow_zero] at hmr
          exact absurd (Subgroup.card_eq_one.mp hmr) hA₀_ne
        · rwa [pow_one] at hmr
        · rw [pow_two] at hmr
          exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_left (by
            rw [hmr, hAcard, pow_two])) hA₀top
      let A₀y : Subgroup G := A₀.map (MulAut.conj y).toMonoidHom
      have hA₀y_le_A : A₀y ≤ A := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
        change (MulAut.conj y) x ∈ A
        rw [MulAut.conj_apply]
        have hxA : x ∈ A := hA₀_sub hx
        have hyA : y ∈ Subgroup.normalizer (A : Set G) := hyNA
        exact (Subgroup.mem_normalizer_iff.mp hyA x).mp hxA
      have hA₀y_card : Nat.card ↥A₀y = r := by
        rw [show A₀y = A₀.map (MulAut.conj y).toMonoidHom from rfl,
          Subgroup.card_map_of_injective (MulAut.conj y).injective, hA₀card]
      have hA₀y_ne : A₀y ≠ A₀ := by
        intro heq
        have hinv : ∀ a : ↥A, (a:G) ∈ A₀ → (η a : G) ∈ A₀ := by
          intro a ha
          have hηa : (η a : G) = y * (a:G) * y⁻¹ := hη_apply a
          rw [hηa]
          have hmem : y * (a:G) * y⁻¹ ∈ A₀y := by
            rw [show A₀y = A₀.map (MulAut.conj y).toMonoidHom from rfl]
            exact Subgroup.mem_map.mpr ⟨(a:G), ha, by
              change (MulAut.conj y) (a:G) = y * (a:G) * y⁻¹
              rw [MulAut.conj_apply]⟩
          rwa [heq] at hmem
        have hle : A₀ ≤ ⊥ := by
          intro z hz
          have hzA : z ∈ A := hA₀_sub hz
          have hηz : (η ⟨z, hzA⟩ : G) ∈ A₀ := by
            have := hinv ⟨z, hzA⟩ hz
            simpa using this
          have h1 : (⟨z, hzA⟩ : ↥A) = 1 := hstep7 ⟨z, hzA⟩ hz hηz
          have h2 : z = 1 := congrArg Subtype.val h1
          simpa [h2]
        exact hA₀_ne (le_bot_iff.mp hle)
      have hA₀_inf : A₀ ⊓ A₀y = ⊥ := by
        by_contra hne
        have hdvd : Nat.card ↥(A₀ ⊓ A₀y) ∣ r := by
          have h1 : Nat.card ↥(A₀ ⊓ A₀y) ∣ Nat.card ↥A₀ := by
            have h := Subgroup.card_subgroup_dvd_card ((A₀ ⊓ A₀y).subgroupOf A₀)
            rwa [Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (inf_le_left : A₀ ⊓ A₀y ≤ A₀)).toEquiv] at h
          rwa [hA₀card] at h1
        rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
        · exact hne (Subgroup.card_eq_one.mp h1)
        · have hcardeq : Nat.card ↥(A₀ ⊓ A₀y) = Nat.card ↥A₀ := by
            rw [h1, hA₀card]
          have heq1 : A₀ ⊓ A₀y = A₀ :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardeq])
          have hAle : A₀ ≤ A₀y := by rw [← heq1]; exact inf_le_right
          have heq2 : A₀ = A₀y :=
            Subgroup.eq_of_le_of_card_ge hAle (by rw [hA₀y_card, hA₀card])
          exact hA₀y_ne heq2.symm
      have hsup_eq : A₀ ⊔ A₀y = A := by
        have hnorm : A₀ ≤ Subgroup.normalizer (A₀y : Set G) := by
          rw [Subgroup.le_normalizer_iff]
          intro a ha x hx
          have haA : a ∈ A := hA₀_sub ha
          have hxA : x ∈ A := hA₀y_le_A hx
          have hcomm : a * x = x * a :=
            congrArg Subtype.val (hAab ⟨a, haA⟩ ⟨x, hxA⟩)
          have : a * x * a⁻¹ = x := by rw [hcomm]; group
          rw [this]
          exact hx
        have hcard : Nat.card ↥(A₀ ⊔ A₀y) * Nat.card ↥(A₀ ⊓ A₀y) =
            Nat.card ↥A₀ * Nat.card ↥A₀y :=
          CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
            hnorm
        rw [hA₀_inf, Subgroup.card_bot, mul_one, hA₀card, hA₀y_card] at hcard
        exact Subgroup.eq_of_le_of_card_ge (sup_le hA₀_sub hA₀y_le_A) (by
          rw [hcard, hAcard, pow_two])
      have hA₀_le : A₀ ≤ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) :=
        inf_le_right.trans le_sup_right
      have hA₀y_le : A₀y ≤ Subgroup.zpowers y ⊔
          Subgroup.normalizer (D.T : Set G) := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
        change (MulAut.conj y) x ∈
          Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G)
        rw [MulAut.conj_apply]
        have hy_mem : y ∈ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) :=
          Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
        have hx_mem : x ∈ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) :=
          hA₀_le hx
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ hy_mem hx_mem) (Subgroup.inv_mem _ hy_mem)
      rw [← hsup_eq]
      exact sup_le hA₀_le hA₀y_le

theorem s17_45_exists_B_le {D : Data G} {X : Subgroup G} {p r : ℕ}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (φ : ↥D.M →* DihedralGroup p) (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    (hrank : CFSG.Open.pRank p (F08.CentOverO2 D.M X) ≤ 1)
    (hpK : ¬ p ∣ Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)))
    (hy : ∃ y ∈ D.M, y ∉ X ⊔ F08.CentOverO2 D.M X ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup ↥D.M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hKrel : (D.T ⊓ X).relIndex
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2)
    (hKfact : (Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))).factorization r = 2)
    (hXfact : (Nat.card ↥X).factorization r = 2)
    (hcentK : ∀ y : G, GapWitness D X p y →
      Subgroup.centralizer (Subgroup.zpowers y : Set G) ⊓
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤ D.T ⊓ X) :
    ∃ A : Subgroup G, ∃ y : G, CFSG.ABGLocalTools.IsSylowOf r A X ∧ Permutes A D.T ∧
      GapWitness D X p y ∧ Nat.card (Subgroup.zpowers y) = p ∧
      Subgroup.zpowers y ≤ D.M ∧ Permutes (Subgroup.zpowers y) D.T ∧
      ⁅A, Subgroup.zpowers y⁆ = A ∧
      A ≤ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) := by
  classical
  obtain ⟨y, hy⟩ := gap17_45_cyclicS_holds hp hp2 hXM hMX φ hφ hker hrank hpK hy hK hKF
  have hA : S17_45A D X p r y :=
    s17_45_exists_A hp hr hr2 hy hXM hMX hpK hKrel hKfact hXfact (hcentK y hy)
  obtain ⟨A, hAsylB, hAsylX, hperm, hinv, hcent⟩ := hA
  have hBcard : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, hy.2.2.1]
  have hBM : Subgroup.zpowers y ≤ D.M := Subgroup.zpowers_le.mpr hy.1
  have hBperm : Permutes (Subgroup.zpowers y) D.T := by
    refine TwelveNineteen.permutes_of_le_normalizer_sup (X := Subgroup.zpowers y)
      (R := D.T ⊓ (X ⊔ F08.CentOverO2 D.M X)) (T := D.T) inf_le_left hy.2.2.2.2 ?_
    exact Subgroup.zpowers_le.mpr hy.2.2.2.1
  have hBp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [hBcard, pow_one])
  have hcomm : ⁅A, Subgroup.zpowers y⁆ = A :=
    CFSG.GroupTheory.commutator_eq_self_of_inf_centralizer_eq_bot hp hr hrp hAsylX.isPGroup hBp
      hinv hcent
  have hANT : A ≤ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) :=
    s17_45_le_zpowers_sup_normalizer hXM hMX hp hp2 hr hr2 φ hker hy hAsylB hKrel hKfact
      hinv hcent
  exact ⟨A, y, hAsylX, hperm, hy, hBcard, hBM, hBperm, hcomm, hANT⟩

theorem s17_45_exists_B_le' {D : Data G} {X L : Subgroup G} {p r n l : ℕ}
    {V₀ V : Subgroup G} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hshape : (IsL2 (Bar2 L) 3 ∧ p = 3 ∧ r = 7) ∨
      (IsSz (Bar2 L) 5 ∧ p = 5 ∧ r = 31))
    (φ : ↥D.M →* DihedralGroup p) (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    (hrank : CFSG.Open.pRank p (F08.CentOverO2 D.M X) ≤ 1)
    (hy : ∃ y ∈ D.M, y ∉ X ⊔ F08.CentOverO2 D.M X ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup ↥D.M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hdata : Gap17_45_BorelData D X p r) :
    ∃ A : Subgroup G, ∃ y : G, CFSG.ABGLocalTools.IsSylowOf r A X ∧ Permutes A D.T ∧
      GapWitness D X p y ∧ Nat.card (Subgroup.zpowers y) = p ∧
      Subgroup.zpowers y ≤ D.M ∧ Permutes (Subgroup.zpowers y) D.T ∧
      ⁅A, Subgroup.zpowers y⁆ = A ∧
      A ≤ Subgroup.zpowers y ⊔ Subgroup.normalizer (D.T : Set G) := by
  have hXM : X ≤ D.M := by
    rw [ctx.X_eq]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) ctx.mem_calC.1.le
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [ctx.X_eq]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hp : p.Prime := by
    rcases hshape with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> norm_num
  have hp2 : p ≠ 2 := by
    rcases hshape with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> norm_num
  have hr : r.Prime := by
    rcases hshape with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> norm_num
  have hr2 : r ≠ 2 := by
    rcases hshape with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> norm_num
  have hrp : r ≠ p := by
    rcases hshape with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> norm_num
  obtain ⟨⟨hpK, hKrel, hKfact, hXfact⟩, hcent⟩ := hdata
  exact s17_45_exists_B_le hXM hMX hp hp2 hr hr2 hrp φ hφ hker hrank hpK hy hK hKF
    hKrel hKfact hXfact hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
