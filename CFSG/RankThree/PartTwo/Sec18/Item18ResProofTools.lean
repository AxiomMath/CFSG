module

import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
public import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)
open scoped Pointwise

namespace Item18ResProof

variable {G : Type} [Group G] [Finite G]

theorem false_of_le_iSup_sup_pCoreOf {X K : Subgroup G} (hK : K ∈ oTwoComponentsIn X)
    (𝓢 : Set (Subgroup G)) (h𝓢 : ∀ S ∈ 𝓢, S ∈ oTwoComponentsIn X) (hK𝓢 : K ∉ 𝓢)
    (hle : K ≤ (⨆ S ∈ 𝓢, S) ⊔ CFSG.Open.pCoreOf 2 X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  let Z : Subgroup G :=
    { carrier := {w | w ∈ X ∧ ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ Q}
      mul_mem' := by
        rintro w₁ w₂ ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩
        refine ⟨X.mul_mem hw₁ hw₂, fun k hk => ?_⟩
        have e : w₁ * w₂ * k * (w₁ * w₂)⁻¹ * k⁻¹ =
            (w₁ * (w₂ * k * w₂⁻¹ * k⁻¹) * w₁⁻¹) * (w₁ * k * w₁⁻¹ * k⁻¹) := by group
        rw [e]
        exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXQ hw₁) _).mp (h₂ k hk)) (h₁ k hk)
      one_mem' := ⟨X.one_mem, fun k _ => by simp⟩
      inv_mem' := by
        rintro w ⟨hw, h⟩
        refine ⟨X.inv_mem hw, fun k hk => ?_⟩
        have e : w⁻¹ * k * w⁻¹⁻¹ * k⁻¹ = w⁻¹ * (w * k * w⁻¹ * k⁻¹)⁻¹ * w⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hXQ (X.inv_mem hw)) _).mp (Q.inv_mem (h k hk)) }
  have hSZ : ∀ S ∈ 𝓢, S ≤ Z := by
    intro S hS s hs
    refine ⟨le_of_mem_oTwoComponentsIn (h𝓢 S hS) hs, fun k hk => ?_⟩
    exact Sec19.Step1910Proof.commutator_mem_pCoreOf (h𝓢 S hS) hK
      (fun h => hK𝓢 (h ▸ hS)) hs hk
  have hQZ : Q ≤ Z := by
    intro q hq
    refine ⟨hQX hq, fun k hk => ?_⟩
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hXQ (hKX hk)) _).mp (Q.inv_mem hq))
  have hKZ : K ≤ Z := hle.trans (sup_le (iSup₂_le hSZ) hQZ)
  have hKK : ⁅K, K⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro k hk k' hk'
    exact (hKZ hk).2 k' hk'
  rw [commutator_eq_of_mem_oTwoComponentsIn hK] at hKK
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr (ne_bot_of_mem_oTwoComponentsIn hK)
  have : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hK
  exact Group.IsPerfect.not_isNilpotent K
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hKK).isNilpotent

theorem false_of_le_sup_pCoreOf {X K L : Subgroup G} (hK : K ∈ oTwoComponentsIn X)
    (eK : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2))
    (hLK : L ≤ K ⊔ CFSG.Open.pCoreOf 2 X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  set N := K ⊔ Q with hN
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (hKX.trans hXQ) Subgroup.le_normalizer
  obtain ⟨⟨ψ⟩, -⟩ := Claim184LcProof.quotient_mulEquiv_of_le_sup (L := K) (R := Q) (N := N)
    le_sup_left le_rfl (hKX.trans hXQ) hNQ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  set φ : L →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    eK.toMonoidHom.comp (ψ.symm.toMonoidHom.comp
      ((QuotientGroup.mk' (CFSG.pCore 2 N)).comp (Subgroup.inclusion hLK))) with hφ
  have hker : φ.ker ≤ CFSG.pCore 2 L := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have himg : φ.ker.map L.subtype ≤ CFSG.Open.pCoreOf 2 N := by
      rintro _ ⟨l, hl, rfl⟩
      have h1 : φ l = 1 := hl
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 N) (Subgroup.inclusion hLK l) = 1 := by
        rw [hφ] at h1
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
        have h3 := congrArg ψ ((map_eq_one_iff eK eK.injective).mp h1)
        simpa using h3
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h2
      exact h2
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le himg).of_equiv
      (φ.ker.equivMapOfInjective _ L.subtype_injective).symm
  exact (KFacts.KS14.ks18SL34 L φ (CFSG.pCore 2 L) CFSG.pCore_isPGroup hker).false eL

theorem isSimpleGroup_projSL_three_four : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
  CFSG.RankThree.PartTwo.Sec4.isSimpleGroup_projSL

omit [Finite G] in
theorem card_pCoreOf_eq (K : Subgroup G) :
    Nat.card (CFSG.Open.pCoreOf 2 K) = Nat.card (CFSG.pCore 2 K) := by
  rw [← inSubgroup_pCore_eq_pCoreOf]
  exact Subgroup.card_map_of_injective K.subtype_injective

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_mem_center {K : Subgroup G} (hKp : ⁅K, K⁆ = K) {y : G}
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hz : ∀ k ∈ K, ∀ m ∈ K, (y * k * y⁻¹ * k⁻¹) * m * (y * k * y⁻¹ * k⁻¹)⁻¹ * m⁻¹ ∈
      CFSG.Open.pCoreOf 2 K) :
    ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  set π : K →* K ⧸ CFSG.pCore 2 K := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hcK : ∀ k : K, y * (k : G) * y⁻¹ * (k : G)⁻¹ ∈ K := fun k =>
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hyK k).mp k.2) (K.inv_mem k.2)
  set c : K → K := fun k => ⟨y * k * y⁻¹ * (k : G)⁻¹, hcK k⟩ with hc
  have hπ1 : ∀ x : K, π x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 K := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  have hcent : ∀ k : K, ∀ m : K, π m * π (c k) = π (c k) * π m := by
    intro k m
    have h1 : π (c k * m * (c k)⁻¹ * m⁻¹) = 1 := (hπ1 _).mpr (by simpa [hc] using hz k k.2 m m.2)
    simp only [map_mul, map_inv] at h1
    calc π m * π (c k)
        = (π (c k) * π m * (π (c k))⁻¹ * (π m)⁻¹)⁻¹ * (π (c k) * π m) := by group
      _ = π (c k) * π m := by rw [h1, inv_one, one_mul]
  have hcmul : ∀ k₁ k₂ : K, c (k₁ * k₂) = c k₁ * (k₁ * c k₂ * k₁⁻¹) := by
    intro k₁ k₂
    apply Subtype.ext
    simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  let f : K →* Subgroup.center (K ⧸ CFSG.pCore 2 K) :=
    { toFun := fun k => ⟨π (c k), Subgroup.mem_center_iff.mpr fun q => by
        obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
        exact hcent k m⟩
      map_one' := by
        apply Subtype.ext
        have h : c 1 = 1 := Subtype.ext (by simp [hc])
        simp [h]
      map_mul' := fun k₁ k₂ => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hcmul, map_mul, map_mul, map_mul, map_inv, hcent k₂ k₁, mul_inv_cancel_right] }
  have : Group.IsPerfect K := (Subgroup.isPerfect_iff).mpr hKp
  intro k hk
  have h1 := KFacts.KS14.eq_one_of_isPerfect_of_comm f
    (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)) ⟨k, hk⟩
  have h2 : π (c ⟨k, hk⟩) = 1 := congrArg Subtype.val h1
  exact (hπ1 _).mp h2

theorem commutator_mem_pCoreOf_of_diag {K J L : Subgroup G}
    (hJK : J ≤ Subgroup.normalizer (K : Set G)) (hKJ : K ≤ Subgroup.normalizer (J : Set G))
    (hJKc : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKp : ⁅K, K⁆ = K) (hLKJ : L ≤ K ⊔ J) (hLp : ⁅L, L⁆ = L)
    (eK : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2))
    (hLJ : ¬ L ≤ J ⊔ CFSG.Open.pCoreOf 2 K)
    {y : G} (hyK : y ∈ Subgroup.normalizer (K : Set G)) (hyJ : y ∈ Subgroup.normalizer (J : Set G))
    (hyc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 K with hQ
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hNKQ : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  set π : K →* K ⧸ CFSG.pCore 2 K := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hπ1 : ∀ x : K, π x = 1 ↔ (x : G) ∈ Q := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  set Zc : Subgroup K := (Subgroup.center (K ⧸ CFSG.pCore 2 K)).comap π with hZc
  set Zh : Subgroup G := Zc.map K.subtype with hZh
  have hmemZ : ∀ x, x ∈ Zh ↔ x ∈ K ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ Q := by
    intro x
    constructor
    · rintro ⟨x', hx', rfl⟩
      refine ⟨x'.2, fun k hk => ?_⟩
      have hcen := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx') (π ⟨k, hk⟩)
      have h1 : π (x' * ⟨k, hk⟩ * x'⁻¹ * (⟨k, hk⟩ : K)⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcen]
        group
      simpa using (hπ1 _).mp h1
    · rintro ⟨hxK, h⟩
      refine ⟨⟨x, hxK⟩, Subgroup.mem_comap.mpr (Subgroup.mem_center_iff.mpr fun q => ?_), rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
      have h1 : π (⟨x, hxK⟩ * k * (⟨x, hxK⟩ : K)⁻¹ * k⁻¹) = 1 :=
        (hπ1 _).mpr (by simpa using h k k.2)
      simp only [map_mul, map_inv] at h1
      change π k * π ⟨x, hxK⟩ = π ⟨x, hxK⟩ * π k
      calc π k * π ⟨x, hxK⟩
          = (π ⟨x, hxK⟩ * π k * (π ⟨x, hxK⟩)⁻¹ * (π k)⁻¹)⁻¹ * (π ⟨x, hxK⟩ * π k) := by group
        _ = π ⟨x, hxK⟩ * π k := by rw [h1, inv_one, one_mul]
  have hZK : Zh ≤ K := fun x hx => ((hmemZ x).mp hx).1
  have hQZ : Q ≤ Zh := fun q hq => (hmemZ q).mpr ⟨hQK hq, fun k hk => by
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hKQ hk) _).mp (Q.inv_mem hq))⟩
  have hconjZ : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ Zh, g * x * g⁻¹ ∈ Zh := by
    intro g hg x hx
    obtain ⟨hxK, hx⟩ := (hmemZ x).mp hx
    refine (hmemZ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxK, fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
    have e : g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ * k⁻¹ =
        g * (x * (g⁻¹ * k * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * k * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hNKQ hg) _).mp (hx _ hk')
  have hnormZ : ∀ g ∈ Subgroup.normalizer (K : Set G), g ∈ Subgroup.normalizer (Zh : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjZ g hg x, fun h => ?_⟩
    have h2 := hconjZ g⁻¹ (Subgroup.inv_mem _ hg) _ h
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h2
  set N := Zh ⊔ J with hN
  have hnormN : ∀ g, g ∈ Subgroup.normalizer (K : Set G) → g ∈ Subgroup.normalizer (J : Set G) →
      g ∈ Subgroup.normalizer (N : Set G) := fun g h1 h2 =>
    Subgroup.inf_normalizer_le_normalizer_sup Zh J ⟨hnormZ g h1, h2⟩
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := fun k hk =>
    hnormN k (Subgroup.le_normalizer hk) (hKJ hk)
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := fun j hj =>
    hnormN j (hJK hj) (Subgroup.le_normalizer hj)
  have hyN : y ∈ Subgroup.normalizer (N : Set G) := hnormN y hyK hyJ
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := hLKJ.trans (sup_le hKN hJN)
  have hNKJ : N ≤ K ⊔ J := sup_le (hZK.trans le_sup_left) le_sup_right
  have hJZ : J ≤ Subgroup.normalizer (Zh : Set G) := fun j hj => hnormZ j (hJK hj)
  have hKNZ : K ⊓ N = Zh := by
    apply le_antisymm
    · rintro x ⟨hxK, hxN⟩
      have hx : x ∈ ((Zh : Set G) * (J : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Zh J hJZ]
        exact hxN
      obtain ⟨z, hz, j, hj, rfl⟩ := hx
      have hjK : j ∈ K := by
        have e : j = z⁻¹ * (z * j) := by group
        rw [e]
        exact K.mul_mem (K.inv_mem (hZK hz)) hxK
      exact Zh.mul_mem hz ((hmemZ j).mpr ⟨hjK, fun k hk => hJKc j hj k hk⟩)
    · exact le_inf hZK le_sup_left
  have hKcard : Nat.card K = 60480 * Nat.card Q := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K),
      Nat.card_congr eK.toEquiv, KFacts.KS14.card_SL_three_four, card_pCoreOf_eq]
  have hZcard : Nat.card Zh = 3 * Nat.card Q := by
    have hcen : Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)) = 3 := by
      rw [← KFacts.L34.card_center_specialLinearGroup KFacts.L34.card_galoisField_two_two]
      exact Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    have h1 : Nat.card Zh = Nat.card Zc := Subgroup.card_map_of_injective K.subtype_injective
    have h2 := Zc.card_mul_index
    have h3 := (Subgroup.center (K ⧸ CFSG.pCore 2 K)).card_mul_index
    have h4 : Zc.index = (Subgroup.center (K ⧸ CFSG.pCore 2 K)).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K)
    rw [h4] at h2
    have hidx : 0 < (Subgroup.center (K ⧸ CFSG.pCore 2 K)).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← card_pCoreOf_eq, ← h3, hcen] at h5
    rw [h5] at h2
    rw [h1]
    have : Nat.card Zc * (Subgroup.center (K ⧸ CFSG.pCore 2 K)).index =
        3 * Nat.card Q * (Subgroup.center (K ⧸ CFSG.pCore 2 K)).index := by
      rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hidx this
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hKJcard : Nat.card (K ⊔ J : Subgroup G) = 20160 * Nat.card N := by
    have h1 := Sec6.card_sup_mul_card_inf hKN
    have hKN' : K ⊔ N = K ⊔ J :=
      le_antisymm (sup_le le_sup_left hNKJ) (sup_le le_sup_left (le_sup_right.trans le_sup_right))
    rw [hKN', hKNZ, hKcard, hZcard] at h1
    have : Nat.card (K ⊔ J : Subgroup G) * (3 * Nat.card Q) =
        20160 * Nat.card N * (3 * Nat.card Q) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have hLcard : Nat.card L = 20160 * Nat.card (CFSG.Open.pCoreOf 2 L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L),
      Nat.card_congr eL.toEquiv, KFacts.L34.card_projSL, card_pCoreOf_eq]
  have hLN2 := Sec6.card_sup_mul_card_inf hLN
  have hLNle : Nat.card (L ⊔ N : Subgroup G) ≤ Nat.card (K ⊔ J : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le hLKJ hNKJ)
  have hO2le : Nat.card (CFSG.Open.pCoreOf 2 L) ≤ Nat.card (L ⊓ N : Subgroup G) := by
    rw [hLcard] at hLN2
    rw [hKJcard] at hLNle
    have h1 : 20160 * Nat.card (CFSG.Open.pCoreOf 2 L) * Nat.card N ≤
        20160 * Nat.card N * Nat.card (L ⊓ N : Subgroup G) := by
      rw [← hLN2]
      exact Nat.mul_le_mul_right _ hLNle
    have h2 : Nat.card (CFSG.Open.pCoreOf 2 L) * (20160 * Nat.card N) ≤
        Nat.card (L ⊓ N : Subgroup G) * (20160 * Nat.card N) := by
      calc Nat.card (CFSG.Open.pCoreOf 2 L) * (20160 * Nat.card N)
          = 20160 * Nat.card (CFSG.Open.pCoreOf 2 L) * Nat.card N := by ring
        _ ≤ 20160 * Nat.card N * Nat.card (L ⊓ N : Subgroup G) := h1
        _ = Nat.card (L ⊓ N : Subgroup G) * (20160 * Nat.card N) := by ring
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) :=
    haveI := isSimpleGroup_projSL_three_four
    eL.isSimpleGroup
  set πL : L →* L ⧸ CFSG.pCore 2 L := QuotientGroup.mk' (CFSG.pCore 2 L) with hπL
  have hπL1 : ∀ x : L, πL x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 L := fun x => by
    rw [hπL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  set M' : Subgroup L := (L ⊓ N).subgroupOf L with hM'
  have hLLN : L ≤ Subgroup.normalizer ((L ⊓ N : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hLN hl⟩
  have hM'n : M'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hLLN
  have hM'map : (M'.map πL).Normal := hM'n.map πL (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M'.map πL) with hbot | htop
  ·
    have hLNO : L ⊓ N ≤ CFSG.Open.pCoreOf 2 L := by
      intro x hx
      have h1 : πL ⟨x, hx.1⟩ ∈ M'.map πL := ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (hπL1 _).mp h1
    have hLNeq : L ⊓ N = CFSG.Open.pCoreOf 2 L := Subgroup.eq_of_le_of_card_ge hLNO hO2le
    have hO2N : CFSG.Open.pCoreOf 2 L ≤ N := hLNeq ▸ inf_le_right
    have hLNKJ : L ⊔ N = K ⊔ J := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hLKJ hNKJ) ?_
      rw [hLNeq, hLcard] at hLN2
      rw [hKJcard]
      have hO2pos : 0 < Nat.card (CFSG.Open.pCoreOf 2 L) := Nat.card_pos
      have h1 : Nat.card (L ⊔ N : Subgroup G) * Nat.card (CFSG.Open.pCoreOf 2 L) =
          20160 * Nat.card N * Nat.card (CFSG.Open.pCoreOf 2 L) := by rw [hLN2]; ring
      exact (Nat.eq_of_mul_eq_mul_right hO2pos h1).ge
    have hyZ : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ Zh := by
      intro k hk
      have hkLN : k ∈ ((L : Set G) * (N : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right L N hLN, hLNKJ]
        exact Subgroup.mem_sup_left hk
      obtain ⟨l, hl, n, hn, hln⟩ := hkLN
      rw [← hKNZ]
      refine ⟨K.mul_mem ((Subgroup.mem_normalizer_iff.mp hyK k).mp hk) (K.inv_mem hk), ?_⟩
      rw [← hln]
      have e : y * (l * n) * y⁻¹ * (l * n)⁻¹ =
          (y * l * y⁻¹ * l⁻¹) * (l * ((y * n * y⁻¹) * n⁻¹) * l⁻¹) := by group
      rw [e]
      refine N.mul_mem (hO2N (hyc l hl)) ?_
      have hyn : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hyN n).mp hn
      exact (Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp (N.mul_mem hyn (N.inv_mem hn))
    exact commutator_mem_pCoreOf_of_mem_center hKp hyK fun k hk m hm =>
      ((hmemZ _).mp (hyZ k hk)).2 m hm
  ·
    exfalso
    apply hLJ
    have hq2 : IsPGroup 2 (L ⧸ M') := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective M' q
      have h1 : πL l ∈ M'.map πL := htop ▸ Subgroup.mem_top _
      obtain ⟨m, hm, hml⟩ := h1
      have ho : m⁻¹ * l ∈ CFSG.pCore 2 L := by
        rw [hπL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hml
        exact QuotientGroup.eq.mp hml
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := L) ⟨_, ho⟩
      have hn' : (m⁻¹ * l) ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      refine ⟨n, ?_⟩
      have hl : l = m * (m⁻¹ * l) := by group
      rw [hl, map_mul, QuotientGroup.mk'_apply M' m, (QuotientGroup.eq_one_iff m).mpr hm, one_mul,
        ← map_pow, hn', map_one]
    have hqs : Group.IsSolvable (L ⧸ M') := by
      have := hq2.isNilpotent
      infer_instance
    have hLleN : L ≤ N := by
      have h1 := inSubgroup_perfectResidual_le_of_isSolvable (N := L ⊓ N) (U := L) inf_le_left hqs
      exact ((le_inSubgroup_perfectResidual hLp le_rfl).trans h1).trans inf_le_right
    set W := J ⊔ Q with hW
    have hWN : W ≤ N := sup_le le_sup_right (hQZ.trans le_sup_left)
    have hNW : N ≤ Subgroup.normalizer (W : Set G) := by
      refine sup_le (fun z hz => ?_) (fun j hj => ?_)
      · exact Subgroup.inf_normalizer_le_normalizer_sup J Q ⟨hKJ (hZK hz), hKQ (hZK hz)⟩
      · exact Subgroup.inf_normalizer_le_normalizer_sup J Q
          ⟨Subgroup.le_normalizer hj, hNKQ (hJK hj)⟩
    have hWn : (W.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mpr hNW
    have hrep : ∀ x : N, ∃ z ∈ Zh, ∃ hzN : z ∈ N,
        QuotientGroup.mk' (W.subgroupOf N) x = QuotientGroup.mk' (W.subgroupOf N) ⟨z, hzN⟩ := by
      intro x
      have hx : (x : G) ∈ ((Zh : Set G) * (J : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Zh J hJZ]
        exact x.2
      obtain ⟨z, hz, j, hj, hzj⟩ := hx
      refine ⟨z, hz, (le_sup_left : Zh ≤ N) hz, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hzj]
      have e : (z * j)⁻¹ * z = j⁻¹ * (z⁻¹ * z) := by group
      rw [e, inv_mul_cancel, mul_one]
      exact W.inv_mem ((le_sup_left : J ≤ W) hj)
    have hcomm : ∀ a b : N ⧸ W.subgroupOf N, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) a
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) b
      obtain ⟨z, hz, hzN, hx⟩ := hrep x
      obtain ⟨z', hz', hz'N, hx'⟩ := hrep x'
      rw [hx, hx', ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hc := ((hmemZ z).mp hz).2 z' (hZK hz')
      have hzz : (z * z')⁻¹ ∈ K := K.inv_mem (K.mul_mem (hZK hz) (hZK hz'))
      have e : (z * z')⁻¹ * (z' * z) =
          (z * z')⁻¹ * (z * z' * z⁻¹ * z'⁻¹)⁻¹ * ((z * z')⁻¹)⁻¹ := by group
      rw [e]
      exact (le_sup_right : Q ≤ W)
        ((Subgroup.mem_normalizer_iff.mp (hKQ hzz) _).mp (Q.inv_mem hc))
    have hNs : Group.IsSolvable (N ⧸ W.subgroupOf N) := Group.isSolvable_of_comm hcomm
    have h1 := inSubgroup_perfectResidual_le_of_isSolvable (N := W) (U := N) hWN hNs
    exact (le_inSubgroup_perfectResidual hLp hLleN).trans h1

theorem exists_mem_inf_centralizer {K : Subgroup G} {c : G}
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 = 1)
    (hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) {k : G} (hk : k ∈ K) :
    ∃ w ∈ K ⊓ Subgroup.centralizer ({c} : Set G), w⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 K with hQ
  set NK := Subgroup.normalizer (K : Set G) with hNK
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKNK : K ≤ NK := Subgroup.le_normalizer
  have hNKQ : NK ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  set Q' : Subgroup NK := Q.subgroupOf NK with hQ'
  have hQ'n : Q'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQK.trans hKNK)).mpr hNKQ
  set π : NK →* NK ⧸ Q' := QuotientGroup.mk' Q' with hπ
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (hQ2.comap_subtype (K := NK)).exists_card_eq
    have hn' : Nat.card Q' = 2 ^ n := hn
    rw [hn']
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  set y : NK := ⟨c, hcK⟩ with hy
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa [hy] using hc3)
  have hact : IsPGroup 3 (Subgroup.zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  set kk : NK := ⟨k, hKNK hk⟩ with hkk
  have hck : π y * π kk = π kk * π y := by
    have h1 : π (y * kk * y⁻¹ * kk⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [hy, hkk] using hcc k hk
    simp only [map_mul, map_inv] at h1
    calc π y * π kk = π y * π kk * (π y)⁻¹ * (π kk)⁻¹ * (π kk * π y) := by group
      _ = π kk * π y := by rw [h1, one_mul]
  have htarget : π kk ∈ Subgroup.centralizer ((Subgroup.zpowers y).map π : Set (NK ⧸ Q')) := by
    rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left hck i)).eq
  obtain ⟨w, hw, hwk⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel
    3 Nat.prime_three π (QuotientGroup.mk'_surjective _) hker _ hact _ htarget
  have hwk' : (w : G)⁻¹ * k ∈ Q := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hwk
    simpa [hkk] using hwk
  have hwK : (w : G) ∈ K := by
    have e : (w : G) = k * ((w : G)⁻¹ * k)⁻¹ := by group
    rw [e]
    exact K.mul_mem hk (K.inv_mem (hQK hwk'))
  have hwc : (w : G) * c = c * w := by
    have h1 := Subgroup.mem_centralizer_iff.mp hw y (Subgroup.mem_zpowers y)
    exact (congrArg Subtype.val h1).symm
  exact ⟨w, ⟨hwK, Subgroup.mem_centralizer_singleton_iff.mpr hwc⟩, hwk'⟩

theorem le_perfectResidual_inf_centralizer_sup {K : Subgroup G} {c : G} (hKp : ⁅K, K⁆ = K)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 = 1)
    (hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    K ≤ inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K := by
  set P := K ⊓ Subgroup.centralizer ({c} : Set G) with hP
  set φ : P →* K ⧸ CFSG.pCore 2 K :=
    (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion (inf_le_left : P ≤ K)) with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
    obtain ⟨w, hw, hwk⟩ := exists_mem_inf_centralizer hcK hc3 hcc k.2
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf]
    simpa using hwk
  have : Group.IsPerfect K := (Subgroup.isPerfect_iff).mpr hKp
  obtain ⟨⟨n, hn, -⟩, -, -, -⟩ := CFSG.perfect_residual_characterization (G := P)
  have hmap : (perfectResidual P).map φ = ⊤ := by
    rw [hn, map_derivedSeries_eq hsurj, Group.IsPerfect.derivedSeries_eq_top]
  intro k hk
  have hq : QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hk⟩ ∈ (perfectResidual P).map φ :=
    hmap ▸ Subgroup.mem_top _
  obtain ⟨x, hx, hxk⟩ := hq
  have hxk' : (x : G)⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf] at hxk
    simpa using hxk
  have e : k = (x : G) * ((x : G)⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ⟨x, hx, rfl⟩ hxk'

theorem mem_thetaComponentsAt_perfectResidual {X K : Subgroup G} {c : G}
    (hK : K ∈ oTwoComponentsIn X) (hCX : Subgroup.centralizer ({c} : Set G) ≤ X)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 = 1)
    (hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) ∈ thetaComponentsAt 3 c ∧
      Nonempty (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) ⧸
        CFSG.pCore 2 (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))) ≃*
          K ⧸ CFSG.pCore 2 K) ∧
      K = inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
        CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set P := K ⊓ C with hP
  set Kc := inSubgroup perfectResidual P with hKc
  set Q := CFSG.Open.pCoreOf 2 K with hQ
  have hKp := commutator_eq_of_mem_oTwoComponentsIn hK
  have hKcP : Kc ≤ P := Subgroup.map_subtype_le _
  have hKcK : Kc ≤ K := hKcP.trans inf_le_left
  have hKcC : Kc ≤ C := hKcP.trans inf_le_right
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hle := le_perfectResidual_inf_centralizer_sup hKp hcK hc3 hcc
  have hKeq : K = Kc ⊔ Q := le_antisymm hle (sup_le hKcK hQK)
  obtain ⟨⟨e⟩, -⟩ := Claim184LcProof.quotient_mulEquiv_of_le_sup (L := Kc) (R := Q) (N := K)
    hKcK hle (hKcK.trans hKQ) hKQ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  refine ⟨?_, ⟨e⟩, hKeq⟩
  obtain ⟨-, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  have hPsn : (P.subgroupOf C).IsSubnormal := by
    have h := hsn.comap (Subgroup.inclusion hCX)
    convert h using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion, hP,
      Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  set S := P.subgroupOf C with hS
  have : (perfectResidual S).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  have hRsn : (inSubgroup perfectResidual S).IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hPsn
  have hSmap : S.map C.subtype = P := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hKcS : Kc.subgroupOf C = inSubgroup perfectResidual S := by
    have h1 : Kc = (inSubgroup perfectResidual S).map C.subtype := by
      rw [hKc, ← hSmap, inSubgroup_perfectResidual_map C.subtype C.subtype_injective]
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hKcsn : (Kc.subgroupOf C).IsSubnormal := hKcS ▸ hRsn
  have hq : CFSG.IsQuasisimple (Kc ⧸ CFSG.pCore 2 Kc) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_of_mem_oTwoComponentsIn hK)
  have hmem : Kc ∈ oTwoComponentsIn C :=
    mem_oTwoComponentsIn_of_quasisimple hKcC hKcsn (commutator_inSubgroup_perfectResidual P) hq
  rw [thetaComponentsAt_eq_thetaComponentsIn]
  exact Claim184LcProof.mem_thetaComponentsIn_of_mem_oTwoComponentsIn hmem

end Item18ResProof

end CFSG.RankThree.PartTwo.Sec18
