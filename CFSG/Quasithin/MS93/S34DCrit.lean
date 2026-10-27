module

import CFSG.Quasithin.MS93.S33SL
import CFSG.Quasithin.MS93.S36SpFaith
import CFSG.Quasithin.MS93.S5AKer
public import CFSG.Quasithin.MS93.S34

public section

namespace CFSG.Quasithin.MS93.S34D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement
open Matrix

section Criterion

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem mem_sup_of_mem_centralizer (h : PUHyp M T L) {c : G} (hcM : c ∈ M)
    (hcU : c ∈ Subgroup.centralizer (Uq M T L : Set G)) : c ∈ L ⊔ pCoreOf 2 M := by
  set K := M ⊓ Subgroup.centralizer (Uq M T L : Set G) with hK
  have hKn : M ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
  have hLK : ¬ L ≤ K := by
    intro hle
    apply h.Uq_ne_bot
    rw [← h.commutator_uq, eq_bot_iff, Subgroup.commutator_le]
    intro u hu l hl
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hle hl).2 u hu
  have hcK : c ∈ K := ⟨hcM, hcU⟩
  refine S5.mem_of_two_odd (fun y hy2 hyc => ?_) (fun y hyo hyc => ?_)
  · have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hcK) hyc
    refine Subgroup.mem_sup_right (h.mem_pCoreOf_of_rel hKn hLK hyK.1 hy2 fun l hl => ?_)
    have hl' : l * y⁻¹ * l⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKn (h.L_le hl)) _).1 (K.inv_mem hyK)
    rw [commutatorElement_def]
    have e : y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
    rw [e]
    exact K.mul_mem hyK hl'
  · obtain ⟨n, hn, hyn⟩ := hyo
    have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hcK) hyc
    exact Subgroup.mem_sup_left (S5.mem_L_of_odd h hyK.1 hn hyn)

omit [Finite G] in
theorem conj_mul_inv_mem_of_coord_id {ι : Type} {F : Type} [Field F] {V Z : Subgroup G}
    {β : ↥V →* Multiplicative (Fin 1 → ι → F)} (hβker : β.ker = Z.subgroupOf V) {c : G}
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) {f : (ι → F) → (ι → F)} (hf : IsCoordAct β c f)
    (hid : ∀ x, f x = x) {u : G} (hu : u ∈ V) : c * u * c⁻¹ * u⁻¹ ∈ Z := by
  set u' : ↥V := ⟨u, hu⟩
  set v : ↥V := ⟨c * u * c⁻¹, conj_mem_of_mem_normalizer hcV u'⟩
  have h1 := hf u' v rfl
  rw [hid] at h1
  have h2 : β v = β u' := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact h1
  have h3 : v * u'⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  rw [hβker, Subgroup.mem_subgroupOf] at h3
  exact h3

omit [Finite G] in
theorem mem_centralizer_of_coord_id {ι : Type} {F : Type} [Field F] {V : Subgroup G}
    {β : ↥V →* Multiplicative (Fin 1 → ι → F)} (hβker : β.ker = (⊥ : Subgroup G).subgroupOf V)
    {c : G} (hcV : c ∈ Subgroup.normalizer (V : Set G)) {f : (ι → F) → (ι → F)}
    (hf : IsCoordAct β c f) (hid : ∀ x, f x = x) : c ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hmem := conj_mul_inv_mem_of_coord_id hβker hcV hf hid hu
  rw [Subgroup.mem_bot] at hmem
  have e2 : c * u * c⁻¹ = u := by
    rw [← mul_inv_eq_one]
    exact hmem
  calc u * c = c * u * c⁻¹ * c := by rw [e2]
    _ = c * u := by group

theorem mem_centralizer_of_coord_id_sp (h : PUHyp M T L) {ι : Type} {F : Type} [Field F]
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → ι → F)}
    (hβker : β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L))
    {c : G} (hcM : c ∈ M) {f : (ι → F) → (ι → F)} (hf : IsCoordAct β c f)
    (hid : ∀ x, f x = x) : c ∈ Subgroup.centralizer (Uq M T L : Set G) := by
  refine S36SP.mem_centralizer_of_mem_trivW h ((S36SP.mem_trivW h).2 ⟨hcM, fun u hu => ?_⟩)
  have hmem := conj_mul_inv_mem_of_coord_id hβker (le_normalizer_Uq h.le_normalizer hcM) hf hid hu
  rw [← h.Uq_inf_Zq] at hmem
  exact hmem.2

theorem pCoreOf_le_charCore_of_mem (h : PUHyp M T L) {K : Subgroup G}
    (hK : ∀ φ : MulAut ↥T, ∀ x : ↥T, (x : G) ∈ pCoreOf 2 M → ((φ x : ↥T) : G) ∈ K) :
    pCoreOf 2 M ≤ charCore T K := by
  intro q hq
  refine ⟨⟨q, h.pCore_le hq⟩, Subgroup.mem_iInf.2 fun φ => ?_, rfl⟩
  refine ⟨φ.symm ⟨q, h.pCore_le hq⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (hK φ.symm ⟨q, h.pCore_le hq⟩ hq)
  · simp

end Criterion

section SL3

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSL 3 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)}

theorem mem_sup_of_isCoordAct_sl (h : PUHyp M T L) {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (ha : Function.Surjective a) (hβ : Function.Surjective β)
    (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    {t : G} (ht : t ∈ T) {γ : GL (Fin 3) F}
    (hγ : IsCoordAct β t (γ : Matrix (Fin 3) (Fin 3) F).mulVec) : t ∈ L ⊔ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
  have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hdet := det_eq_one_of_isCoordAct hβ (hTV ht) he' hγ
  obtain ⟨l, hl⟩ := ha ⟨γ, Subgroup.subset_closure hdet⟩
  have hlact : IsCoordAct β (l : G) (γ : Matrix (Fin 3) (Fin 3) F).mulVec := by
    have := S33.isCoordAct_of_nat hβα l
    rw [hl] at this
    exact this
  have hc := hlact.inv.mul (hTV ht) hγ
  have hcV : (l : G)⁻¹ * t ∈ Subgroup.normalizer (Uq M T L : Set G) :=
    mul_mem (inv_mem (hLV l.2)) (hTV ht)
  have hcM : (l : G)⁻¹ * t ∈ M := M.mul_mem (M.inv_mem (h.L_le l.2)) (h.le ht)
  have hcU := mem_centralizer_of_coord_id hβker hcV hc fun x => by simp [Matrix.mulVec_mulVec]
  have e3 : t = (l : G) * ((l : G)⁻¹ * t) := by group
  rw [e3]
  exact (L ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left l.2)
    (mem_sup_of_mem_centralizer h hcM hcU)

end SL3

section Sp4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSp 2 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}

theorem mem_sup_of_isCoordAct_sp (h : PUHyp M T L) {k : ℕ} (hcard : Fintype.card F = 2 ^ k)
    (ha : Function.Surjective a) (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i))
    {t : G} (ht : t ∈ T) {γ : GL (Fin 2 ⊕ Fin 2) F}
    (hγ : IsCoordAct β t (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec) :
    t ∈ L ⊔ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  have hβα' : ∀ l : ↥L, IsCoordAct β l ((a l : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec := fun l u v huv => by
    simpa [moduleAct] using hβα l u v huv 0
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
  have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨g, hg⟩ := exists_sp4_of_gl ha hLV hβ hβα' (hTV ht) (h.le_normalizer (h.le ht)) he' hγ
  obtain ⟨l, hl⟩ := ha g
  have hlact := hβα' l
  rw [hl] at hlact
  have hc := hlact.inv.mul (hTV ht) hg
  have hcM : (l : G)⁻¹ * t ∈ M := M.mul_mem (M.inv_mem (h.L_le l.2)) (h.le ht)
  have hcU := mem_centralizer_of_coord_id_sp h hβker hcM hc fun x => by
    simp [Matrix.mulVec_mulVec]
  have e3 : t = (l : G) * ((l : G)⁻¹ * t) := by group
  rw [e3]
  exact (L ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left l.2)
    (mem_sup_of_mem_centralizer h hcM hcU)

end Sp4

end CFSG.Quasithin.MS93.S34D
