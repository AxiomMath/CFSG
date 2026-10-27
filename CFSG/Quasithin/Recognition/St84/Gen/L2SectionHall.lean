module

public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Quasithin.Recognition.St84.Gen.SL2TorusAut
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

section CoordinateFree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

section UtriEntry

theorem utriElt_one_mulVec_zero {F : Type} [Field F] (v : Fin 2 → F) :
    (((utriElt (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 0 = v 0 + v 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [utriElt_apply_00, utriElt_apply_01, one_mul, one_mul]

end UtriEntry

theorem mulVec_apply_one_eq_zero {G : Type*} [Group G] {L S : Subgroup G}
    {F : Type} [Field F] {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) {v : Fin 2 → F}
    (hfix : ∀ x : ↥L, (x : G) ∈ S → (α x : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) :
    v 1 = 0 := by
  obtain ⟨x₁, hx₁⟩ := hα (utriElt (1 : F))
  have hx₁S : (x₁ : G) ∈ S := (hmem x₁).mpr (by rw [hx₁]; exact utriElt_mem_utri 1)
  have h0 : v 0 + v 1 = v 0 := by
    have h := congrFun (hfix x₁ hx₁S) 0
    rw [hx₁, utriElt_one_mulVec_zero] at h
    simpa using h
  have h2 : v 1 = v 0 - v 0 := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact h0
  simpa using h2

theorem mem_utri_of_mulVec_eq_self {F : Type} [Field F] {A : SL(2, F)}
    {v : Fin 2 → F} (hfix : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) (hv0 : v 0 ≠ 0)
    (hv1 : v 1 = 0) : A ∈ utri F := by
  refine mem_utri_entries.mpr ⟨?_, ?_⟩
  · have h1 := congrFun hfix 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    rw [hv1, mul_zero, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hv0
  · have h0 := congrFun hfix 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    rw [hv1, mul_zero, add_zero] at h0
    exact mul_right_cancel₀ hv0 (by rw [h0, one_mul])

theorem mem_utri_conj_iff {F : Type} [Field F] {u : SL(2, F)} (hu : u ∈ utri F)
    {y : SL(2, F)} : u * y * u⁻¹ ∈ utri F ↔ y ∈ utri F :=
  (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hu) y).symm

theorem map_subgroupOf_eq_utri {G : Type*} [Group G] {L S : Subgroup G}
    {F : Type} [Field F] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) :
    (S.subgroupOf L).map α = utri F := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact (hmem x).mp (Subgroup.mem_subgroupOf.mp hx)
  · intro y hy
    obtain ⟨x, rfl⟩ := hα y
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ((hmem x).mpr hy), rfl⟩

theorem card_map_subgroupOf_of_inf_eq_bot {G : Type*} [Group G] {L T Q : Subgroup G}
    {F : Type} [Field F] (hTL : T ≤ L) (α : ↥L →* SL(2, F))
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (hTQ : T ⊓ Q = ⊥) :
    Nat.card ((T.subgroupOf L).map α) = Nat.card T := by
  let φ : ↥(T.subgroupOf L) →* SL(2, F) := α.comp (T.subgroupOf L).subtype
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : φ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : (((x * y⁻¹ : ↥(T.subgroupOf L)) : ↥L) : G) ∈ T ⊓ Q := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (x * y⁻¹).2
      · exact (hker _).mp h1
    rw [hTQ, Subgroup.mem_bot] at h2
    have h3 : x * y⁻¹ = 1 := Subtype.ext (Subtype.ext h2)
    rwa [mul_inv_eq_one] at h3
  have hrange : φ.range = (T.subgroupOf L).map α := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard : Nat.card ((T.subgroupOf L).map α) = Nat.card ↥(T.subgroupOf L) := by
    rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj,
      Subgroup.card_top]
  rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv]

theorem hall_inf_card {G : Type*} [Group G] [Finite G] {L H U B : Subgroup G} {a c : ℕ}
    (hUL : U ≤ L) (hHB : H ≤ B) (hUH : U ⊔ H = B) (hBLeB : borelOf L U ≤ B)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) (hUinfH : U ⊓ H = ⊥)
    (hcardB : Nat.card (borelOf L U) = a * c) (hcardU : Nat.card U = a) (ha : 0 < a) :
    borelOf L U = U ⊔ (H ⊓ L) ∧ (H ⊓ L) ⊓ U = ⊥ ∧ Nat.card ↥(H ⊓ L) = c := by
  classical
  set T : Subgroup G := H ⊓ L with hTdef
  have hTH : T ≤ H := inf_le_left
  have hTL : T ≤ L := inf_le_right
  have hUB : U ≤ borelOf L U := by
    rw [borelOf_eq_inf_of_le hUL]
    exact le_inf hUL Subgroup.le_normalizer
  have hTB : T ≤ borelOf L U := by
    rw [borelOf_eq_inf_of_le hUL]
    exact le_inf hTL (hTH.trans (hHB.trans hBU))
  have hHT : H ⊓ borelOf L U = T := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hx.1, borelOf_le L U hx.2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hTH hx, hTB hx⟩
  have hBLeq : borelOf L U = U ⊔ T := by
    have hded := Subgroup.inf_sup_assoc_of_le (H := H) (K := borelOf L U) (N := U)
      (hHB.trans hBU) hUB
    rw [sup_comm H U, hUH, inf_eq_left.mpr hBLeB, inf_comm (borelOf L U) H, hHT,
      sup_comm T U] at hded
    exact hded.symm
  have hTU : T ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ U ⊓ H := ⟨hx.2, hTH hx.1⟩
    rwa [hUinfH, Subgroup.mem_bot] at hx'
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := T) (B := U) (hTH.trans (hHB.trans hBU))
  rw [sup_comm T U, ← hBLeq, hTU, Subgroup.card_bot, mul_one, hcardB, hcardU] at hprod
  have hprod' : Nat.card T * a = c * a := by
    rw [← hprod, mul_comm a c]
  exact ⟨hBLeq, hTU, Nat.eq_of_mul_eq_mul_right ha hprod'⟩

theorem exists_hall_cover_of_torus {L H T : Subgroup G} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hHB : H ≤ bigB L1 L2 S)
    (hNB : bigB L1 L2 S ≤ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (pCoreOf 2 L : Set G) ⊓ Subgroup.normalizer (S : Set G))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hTH : T ≤ H) (hTL : T ≤ L)
    {α' : ↥L →* SL(2, F)} (hα' : Function.Surjective α')
    (hkerEq : α'.ker = (pCoreOf 2 L).subgroupOf L)
    (hU' : (S.subgroupOf L).map α' = utri F)
    (hT'map : (T.subgroupOf L).map α' = torus F) (hF4 : 4 ≤ Nat.card F) :
    ∀ h ∈ H, ∃ t ∈ T, t⁻¹ * h ∈ H ⊓ trivOTwoQuot L := by
  intro h hh
  have hhB : h ∈ bigB L1 L2 S := hHB hh
  have hhNL : h ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hNB hhB)).1).1
  have hhNQ : h ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hNB hhB)).1).2
  have hhNS : h ∈ Subgroup.normalizer (S : Set G) :=
    (Subgroup.mem_inf.mp (hNB hhB)).2
  have hhTc : ∀ t ∈ T, h * t * h⁻¹ = t := by
    intro t ht
    rw [hHcomm h hh t (hTH ht)]
    group
  obtain ⟨t, htT, htprop⟩ := exists_mem_torus_conj_mem_of_normalizes hF4 α' hα' hkerEq
    hU' hTL hT'map hhNL hhNQ hhNS hhTc
  exact ⟨t, htT, Subgroup.mem_inf.mpr
    ⟨H.mul_mem (H.inv_mem (hTH htT)) hh,
      mem_trivOTwoQuot.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _
        (Subgroup.le_normalizer (hTL htT))) hhNL, htprop⟩⟩⟩

theorem exists_hall_cover {L H : Subgroup G} {F : Type} [Field F] [Fintype F]
    [CharP F 2] {k : ℕ} (hSle : S ≤ L) (hHB : H ≤ bigB L1 L2 S)
    (hUinfH : S ⊓ H = ⊥) (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hNB : bigB L1 L2 S ≤ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (pCoreOf 2 L : Set G) ⊓ Subgroup.normalizer (S : Set G))
    (hQS : pCoreOf 2 L ≤ S) (hBLeq : borelOf L S = S ⊔ (H ⊓ L))
    (hcardT : Nat.card ↥(H ⊓ L) = k) (hkF : Nat.card F - 1 = k)
    (hF4 : 4 ≤ Nat.card F) (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) :
    ∀ h ∈ H, ∃ t ∈ H ⊓ L, t⁻¹ * h ∈ H ⊓ trivOTwoQuot L := by
  classical
  set T : Subgroup G := H ⊓ L with hTdef
  have hTH : T ≤ H := inf_le_left
  have hTL : T ≤ L := inf_le_right
  have hTB : T ≤ borelOf L S := by rw [hBLeq]; exact le_sup_right
  have hTQ : T ⊓ pCoreOf 2 L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ S ⊓ H := ⟨hQS hx.2, hTH hx.1⟩
    rwa [hUinfH, Subgroup.mem_bot] at hx'
  let TF : Subgroup SL(2, F) := (T.subgroupOf L).map α
  have hTFcardT : Nat.card TF = Nat.card T :=
    card_map_subgroupOf_of_inf_eq_bot hTL α hker hTQ
  have hTFcard : Nat.card TF = Nat.card F - 1 := by
    rw [hTFcardT, hcardT, ← hkF]
  have hTFborel : TF ≤ borel F := by
    rintro y ⟨x, hx, rfl⟩
    exact (mem_borelOf_iff_alpha_mem_borel hSle α hα hmem x).mp
      (hTB (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨u, hu, hTFmap⟩ := exists_utri_conj_eq_torus hTFborel hTFcard
  let α' : ↥L →* SL(2, F) := (MulAut.conj u).toMonoidHom.comp α
  have hα'app : ∀ x, α' x = u * α x * u⁻¹ := fun _ => rfl
  have hα' : Function.Surjective α' := (MulAut.conj u).surjective.comp hα
  have hmemS' : ∀ x : ↥L, (x : G) ∈ S ↔ α' x ∈ utri F := by
    intro x
    rw [hα'app, hmem x]
    exact (mem_utri_conj_iff hu).symm
  have hker' : ∀ x : ↥L, α' x = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
    intro x
    have h1' : α' x = 1 ↔ α x = 1 := by
      rw [hα'app]
      constructor
      · intro h
        calc α x = u⁻¹ * (u * α x * u⁻¹) * u := by group
          _ = 1 := by rw [h]; group
      · intro h
        rw [h]
        group
    rw [h1']
    exact hker x
  have hkerEq : α'.ker = (pCoreOf 2 L).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker' x
  have hU' : (S.subgroupOf L).map α' = utri F :=
    map_subgroupOf_eq_utri α' hα' hmemS'
  have hT'map : (T.subgroupOf L).map α' = torus F := by
    have hmap : (T.subgroupOf L).map α' = TF.map (MulAut.conj u).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmap]
    exact hTFmap
  exact exists_hall_cover_of_torus hHB hNB hHcomm hTH hTL (α' := α') hα' hkerEq hU' hT'map hF4

theorem exists_torus_of_hall {L H : Subgroup G} {F : Type} [Field F] [Fintype F]
    [CharP F 2] {k m : ℕ} (hSle : S ≤ L) (hHB : H ≤ bigB L1 L2 S)
    (hUinfH : S ⊓ H = ⊥) (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hNB : bigB L1 L2 S ≤ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (pCoreOf 2 L : Set G) ⊓ Subgroup.normalizer (S : Set G))
    (hQS : pCoreOf 2 L ≤ S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hBLeq : borelOf L S = S ⊔ (H ⊓ L))
    (hcardT : Nat.card ↥(H ⊓ L) = k) (hHcard : Nat.card H = k * m) (hkpos : 0 < k)
    (hkF : Nat.card F - 1 = k) (hF4 : 4 ≤ Nat.card F) (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) :
    Nat.card ↥(H ⊓ L) = k ∧ Nat.card ↥(H ⊓ trivOTwoQuot L) = m ∧
      (H ⊓ L) ⊔ (H ⊓ trivOTwoQuot L) = H ∧ (H ⊓ trivOTwoQuot L) ⊓ L = ⊥ ∧
      L ⊔ bigB L1 L2 S = L ⊔ (H ⊓ trivOTwoQuot L) := by
  classical
  have hcover := exists_hall_cover (L := L) (H := H) (F := F) (k := k) hSle hHB hUinfH
    hHcomm hNB hQS hBLeq hcardT hkF hF4 α hα hker hmem
  set T : Subgroup G := H ⊓ L with hTdef
  have hTH : T ≤ H := inf_le_left
  have hTL : T ≤ L := inf_le_right
  let H₀ : Subgroup G := H ⊓ trivOTwoQuot L
  have hH₀H : H₀ ≤ H := inf_le_left
  have hHsup : H = T ⊔ H₀ := by
    refine le_antisymm ?_ (sup_le hTH hH₀H)
    intro h hh
    obtain ⟨t, htT, hth⟩ := hcover h hh
    rw [show h = t * (t⁻¹ * h) by group]
    exact Subgroup.mul_mem_sup htT hth
  have hTH0 : T ⊓ H₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_mem_trivOTwoQuot α hα hker (Subgroup.mem_inf.mp hx.2).2 (hTL hx.1)
    have hx' : x ∈ S ⊓ H := ⟨hQS hxQ, hTH hx.1⟩
    rwa [hUinfH, Subgroup.mem_bot] at hx'
  have hH0card : Nat.card H₀ = m := by
    have hcommTH₀ : T ≤ Subgroup.centralizer (H₀ : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hHcomm t (hTH ht) x (hH₀H hx)).symm
    have hnorm : T ≤ Subgroup.normalizer (H₀ : Set G) :=
      hcommTH₀.trans (Subgroup.centralizer_le_normalizer (H₀ : Set G))
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (A := T) (B := H₀) hnorm
    rw [← hHsup, hTH0, Subgroup.card_bot, mul_one, hHcard, hcardT] at hprod
    exact (Nat.eq_of_mul_eq_mul_left hkpos hprod).symm
  have hH0infL : H₀ ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_mem_trivOTwoQuot α hα hker (Subgroup.mem_inf.mp hx.1).2 hx.2
    have hx' : x ∈ S ⊓ H := ⟨hQS hxQ, hH₀H hx.1⟩
    rwa [hUinfH, Subgroup.mem_bot] at hx'
  have hsupeq : L ⊔ bigB L1 L2 S = L ⊔ H₀ := by
    refine le_antisymm ?_ ?_
    · refine sup_le le_sup_left ?_
      rw [← hSH]
      refine sup_le (hSle.trans le_sup_left) ?_
      rw [hHsup]
      exact sup_le (hTL.trans le_sup_left) le_sup_right
    · exact sup_le le_sup_left ((hH₀H.trans hHB).trans le_sup_right)
  exact ⟨hcardT, hH0card, hHsup.symm, hH0infL, hsupeq⟩
end CoordinateFree

section Counting

variable {G : Type} [Group G]

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h2 : Even (2 ^ k) := (show Even 2 by norm_num).pow_of_ne_zero (by omega)
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 (by norm_num)

theorem twoPart_of_card {X : Subgroup G} {a u : ℕ} (hu : Odd u)
    (hcard : Nat.card ↥X = 2 ^ a * u) : twoPart X = 2 ^ a := by
  have hnot : ¬ 2 ∣ u := fun hdvd => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr hdvd)
  unfold twoPart
  rw [hcard, Nat.factorization_mul (by positivity) hu.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot, add_zero, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
  simp

theorem card_eq_card_oTwoQuot_mul (L : Subgroup G) :
    Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCoreOf 2 L) := by
  have hpc : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) := by
    rw [CFSG.Open.pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
  rw [hpc]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)

theorem twoPart_of_isL2Quot {L : Subgroup G} {a f : ℕ} (hf : 1 ≤ f)
    (h : IsL2Quot f (oTwoQuot ↥L)) (hc : Nat.card (pCoreOf 2 L) = 2 ^ a) :
    twoPart L = 2 ^ (a + f) := by
  refine twoPart_of_card (a := a + f) (u := 4 ^ f - 1) ?_ ?_
  · rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact odd_two_pow_sub_one (by omega)
  · rw [card_eq_card_oTwoQuot_mul, IsL2Quot.card hf h, hc, pow_add]
    ring

end Counting

section BorelNormalizer

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

theorem _root_.CFSG.Quasithin.Hyp111.bigB_le_normalizer_pCoreOf_left (hH : Hyp111 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (borelOf_le L1 S).trans (le_normalizer_pCoreOf 2 L1)
  · exact hH.h1.borel_le.trans (normalizer_le_normalizer_pCoreOf 2 L1)
  · exact hH.h1.normalizes.trans (normalizer_le_normalizer_pCoreOf 2 L1)

theorem _root_.CFSG.Quasithin.Hyp111.bigB_le_normalizer_pCoreOf_right (hH : Hyp111 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact hH.h2.borel_le.trans (normalizer_le_normalizer_pCoreOf 2 L2)
  · exact (borelOf_le L2 S).trans (le_normalizer_pCoreOf 2 L2)
  · exact hH.h2.normalizes.trans (normalizer_le_normalizer_pCoreOf 2 L2)

end BorelNormalizer

end CFSG.Quasithin.F112R.St84

end
