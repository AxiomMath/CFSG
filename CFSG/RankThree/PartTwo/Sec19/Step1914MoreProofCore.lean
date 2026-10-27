module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProofMat
public import CFSG.RankThree.PartTwo.Sec19.Statements
public import CFSG.RankThree.PartTwo.Sec12.Coordinates
public import CFSG.RankThree.PartTwo.KFacts.K74Bloom
public import Certificates.Certificate8171
public import Certificates.Certificate8172
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec11.Item116Coords
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section General

variable {Y : Type*} [Group Y]

theorem conj_mem_oUpperThreePrime {X : Subgroup Y} {x : Y} (hx : x ∈ X) {σ : Y}
    (hσ : σ ∈ oUpperThreePrime X) : x * σ * x⁻¹ ∈ oUpperThreePrime X := by
  induction hσ using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hyX, k, hk⟩ := hy
    refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx), k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact (oUpperThreePrime X).one_mem
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem isExtOf_of_mulEquiv' {X Z S T : Type*} [Group X] [Group Z] [Group S] [Group T]
    (e : X ≃* Z) (h : Sec4.IsExtOf Z S T) : Sec4.IsExtOf X S T := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have hmap : (K.comap e.toMonoidHom).map e.toMonoidHom = K :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective K
  refine ⟨K.comap e.toMonoidHom, hK.comap _, ⟨?_⟩, ⟨?_⟩⟩
  · exact ((K.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hmap).trans eK)
  · exact (QuotientGroup.congr _ _ e hmap).trans eQ

theorem inv_eq_sq_of_pow_three {x : Y} (hx : x ^ 3 = 1) : x⁻¹ = x ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', hx]

end General

section MatGen

theorem conj_pow_mem {M : Type*} [Group M] {O : Subgroup M} {q : M}
    (hq : ∀ x ∈ O, q * x * q⁻¹ ∈ O) (n : ℕ) : ∀ x ∈ O, q ^ n * x * (q ^ n)⁻¹ ∈ O := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have e : q ^ (n + 1) * x * (q ^ (n + 1))⁻¹ = q * (q ^ n * x * (q ^ n)⁻¹) * q⁻¹ := by group
    rw [e]
    exact hq _ (ih x hx)

theorem mem_of_blk_eq {O : Subgroup GL33} (hT : ∀ a b : ZMod 3, tMat a b ∈ O) {N D : yStd}
    (hN : (N : GL33) ∈ O) (hb : blk D = blk N) : (D : GL33) ∈ O := by
  have hker : blk (D * N⁻¹) = 1 := by rw [map_mul, map_inv, hb, mul_inv_cancel]
  have hT' := eq_tMat_of_blk_eq_one _ hker
  have hDN : (D : GL33) = ((D * N⁻¹ : yStd) : GL33) * (N : GL33) := by simp
  rw [hDN, hT']
  exact mul_mem (hT _ _) hN

theorem dOne_dTwo_mem {O : Subgroup GL33} (hOY : O ≤ yStd) (hT : ∀ a b : ZMod 3, tMat a b ∈ O)
    (hn₁ : ∀ x ∈ O, qHatOne * x * qHatOne⁻¹ ∈ O) (hn₂ : ∀ x ∈ O, qHatTwo * x * qHatTwo⁻¹ ∈ O)
    {S : GL33} (hSO : S ∈ O) (hu3 : blk ⟨S, hOY hSO⟩ ^ 3 = 1) (hu1 : blk ⟨S, hOY hSO⟩ ≠ 1) :
    dOne ∈ O ∧ dTwo ∈ O := by
  set q₁ : yStd := ⟨qHatOne, qHatOne_mem_yStd⟩ with hq₁
  set q₂ : yStd := ⟨qHatTwo, qHatTwo_mem_yStd⟩ with hq₂
  set SY : yStd := ⟨S, hOY hSO⟩ with hSY
  have hconj : ∀ (i j : ℕ) (x : GL33), x ∈ O →
      (qHatOne ^ i * qHatTwo ^ j) * x * (qHatOne ^ i * qHatTwo ^ j)⁻¹ ∈ O := by
    intro i j x hx
    have e : (qHatOne ^ i * qHatTwo ^ j) * x * (qHatOne ^ i * qHatTwo ^ j)⁻¹ =
        qHatOne ^ i * (qHatTwo ^ j * x * (qHatTwo ^ j)⁻¹) * (qHatOne ^ i)⁻¹ := by group
    rw [e]
    exact conj_pow_mem hn₁ i _ (conj_pow_mem hn₂ j x hx)
  have key : ∀ (t : SL23) (D : yStd), blk D = t →
      (∃ i : Fin 4, ∃ j : Fin 2, ∃ e : Fin 3, qOne ^ (i : ℕ) * qTwo ^ (j : ℕ) * blk SY ^ (e : ℕ) =
        t * (qOne ^ (i : ℕ) * qTwo ^ (j : ℕ))) → (D : GL33) ∈ O := by
    rintro t D hD ⟨i, j, e, he⟩
    set NY : yStd := (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ)) * SY ^ (e : ℕ) * (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ))⁻¹
      with hNY
    have hNO : (NY : GL33) ∈ O := by
      rw [hNY]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact hconj i j _ (pow_mem hSO _)
    refine mem_of_blk_eq hT hNO ?_
    rw [hD, hNY, map_mul, map_mul, map_inv, map_mul, map_pow, map_pow, map_pow, blk_qHatOne,
      blk_qHatTwo, he, mul_inv_cancel_right]
  refine ⟨key tOne ⟨dOne, dOne_mem_yStd⟩ (blk_liftGL tOne) (exists_conj_eq_tOne _ hu3 hu1),
    key tTwo ⟨dTwo, dTwo_mem_yStd⟩ (blk_liftGL tTwo) (exists_conj_eq_tTwo _ hu3 hu1)⟩

end MatGen

structure BasisData {G : Type} [Group G] (E B : Subgroup G) (c X₁ X₂ : G) : Prop where
  elemAbelian : CFSG.Assembly.IsElemAbelian 3 E
  card_eq : Nat.card E = 27
  mem_c : c ∈ E
  eq_sup : E = Subgroup.zpowers c ⊔ B
  not_mem_c : c ∉ B
  card_B : Nat.card B = 9
  ne_one : X₁ ≠ 1
  eq_B : B = Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂

structure CoreData {G : Type} [Group G] (E B : Subgroup G) (c X₁ X₂ M₁ M₂ : G) : Prop
    extends BasisData E B c X₁ X₂ where
  mem_norm₁ : M₁ ∈ Subgroup.normalizer (B : Set G)
  mem_norm₂ : M₂ ∈ Subgroup.normalizer (B : Set G)
  comm₁ : M₁ * c = c * M₁
  comm₂ : M₂ * c = c * M₂
  r1 : M₁ * X₁ * M₁⁻¹ = X₂⁻¹
  r2 : M₁ * X₂ * M₁⁻¹ = X₁
  r3 : M₂ * X₁ * M₂⁻¹ = X₂⁻¹ * X₁⁻¹
  r4 : M₂ * X₂ * M₂⁻¹ = X₁ * X₂ * X₁

@[expose] def IsAdapted {G : Type} [Group G] {E : Subgroup G}
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* E) (X₁ X₂ c : G) : Prop :=
  ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) = X₁ ^ (v 0).val * X₂ ^ (v 1).val *
    c ^ (v 2).val

variable {G : Type} [Group G] [Finite G] {E B : Subgroup G} {c X₁ X₂ M₁ M₂ : G}

omit [Finite G] in
theorem coords_apply {f : Multiplicative (Fin 3 → ZMod 3) ≃* E} (hf : IsAdapted f X₁ X₂ c)
    (a b d : ZMod 3) :
    (f (Multiplicative.ofAdd ![a, b, d]) : G) = X₁ ^ a.val * X₂ ^ b.val * c ^ d.val :=
  hf _

theorem single_zero : (Pi.single 0 1 : Fin 3 → ZMod 3) = ![1, 0, 0] := by
  funext i
  fin_cases i <;> rfl

theorem single_one : (Pi.single 1 1 : Fin 3 → ZMod 3) = ![0, 1, 0] := by
  funext i
  fin_cases i <;> rfl

theorem single_two : (Pi.single 2 1 : Fin 3 → ZMod 3) = ![0, 0, 1] := by
  funext i
  fin_cases i <;> rfl

omit [Finite G] in
theorem f_zero {f : Multiplicative (Fin 3 → ZMod 3) ≃* E} (hf : IsAdapted f X₁ X₂ c) :
    (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) = X₁ := by
  rw [single_zero, coords_apply hf]
  simp [show (1 : ZMod 3).val = 1 from rfl]

omit [Finite G] in
theorem f_one {f : Multiplicative (Fin 3 → ZMod 3) ≃* E} (hf : IsAdapted f X₁ X₂ c) :
    (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) = X₂ := by
  rw [single_one, coords_apply hf]
  simp [show (1 : ZMod 3).val = 1 from rfl]

omit [Finite G] in
theorem f_two {f : Multiplicative (Fin 3 → ZMod 3) ≃* E} (hf : IsAdapted f X₁ X₂ c) :
    (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) = c := by
  rw [single_two, coords_apply hf]
  simp [show (1 : ZMod 3).val = 1 from rfl]

namespace BasisData

variable (h : BasisData E B c X₁ X₂)
include h

omit [Finite G] in
theorem le_E : B ≤ E := h.eq_sup ▸ le_sup_right

omit [Finite G] in
theorem X₁_mem : X₁ ∈ B := h.eq_B ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers X₁)

omit [Finite G] in
theorem X₂_mem : X₂ ∈ B := h.eq_B ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)

omit [Finite G] in
theorem comm {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

omit [Finite G] in
theorem pow_three {x : G} (hx : x ∈ E) : x ^ 3 = 1 := h.elemAbelian.2 x hx

omit [Finite G] in
theorem elemAbelian_B : CFSG.Assembly.IsElemAbelian 3 B :=
  ⟨⟨⟨fun x y => Subtype.ext (h.comm (h.le_E x.2) (h.le_E y.2))⟩⟩,
    fun _ hx => h.pow_three (h.le_E hx)⟩

omit [Finite G] in
theorem closure_eq : Subgroup.closure ({X₁, X₂, c} : Set G) = E := by
  have e : ({X₁, X₂, c} : Set G) = {X₁} ∪ ({X₂} ∪ {c}) := by
    rw [Set.insert_eq, Set.insert_eq]
  rw [e, Subgroup.closure_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, h.eq_sup, h.eq_B,
    sup_comm (Subgroup.zpowers c), sup_assoc]

theorem exists_adapted : ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* E, IsAdapted f X₁ X₂ c := by
  obtain ⟨f, -, -, -, hfv⟩ := Sec11.exists_coords_triple (A := E)
    (fun u hu v hv => h.comm hu hv) (fun u hu => h.pow_three hu) h.card_eq (h.le_E h.X₁_mem)
    (h.le_E h.X₂_mem) h.mem_c h.closure_eq
  exact ⟨f, hfv⟩

theorem mem_normalizer_E {w : G} (hwc : w * c = c * w)
    (hwB : w ∈ Subgroup.normalizer (B : Set G)) : w ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])
  conv_lhs => rw [h.eq_sup]
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp hwB, MonoidHom.map_zpowers]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) h.le_E
  change w * c * w⁻¹ ∈ E
  rw [hwc, mul_inv_cancel_right]
  exact h.mem_c

omit [Finite G] in
theorem comm₁₂ : X₁ * X₂ = X₂ * X₁ := h.comm (h.le_E h.X₁_mem) (h.le_E h.X₂_mem)

variable {f : Multiplicative (Fin 3 → ZMod 3) ≃* E}

omit [Finite G] in
theorem mem_B_iff (hf : IsAdapted f X₁ X₂ c) (x : E) :
    (x : G) ∈ B ↔ Sec12.coordVec f x 2 = 0 := by
  set v := Sec12.coordVec f x with hv
  have hx : (x : G) = X₁ ^ (v 0).val * X₂ ^ (v 1).val * c ^ (v 2).val := by
    rw [← hf v, hv]
    simp [Sec12.coordVec]
  have hXB : X₁ ^ (v 0).val * X₂ ^ (v 1).val ∈ B :=
    mul_mem (pow_mem h.X₁_mem _) (pow_mem h.X₂_mem _)
  constructor
  · intro hxB
    by_contra hv2
    have hcpow : c ^ (v 2).val ∈ B := by
      have e : c ^ (v 2).val = (X₁ ^ (v 0).val * X₂ ^ (v 1).val)⁻¹ * x := by
        rw [hx]
        group
      rw [e]
      exact mul_mem (inv_mem hXB) hxB
    have hval : (v 2).val = 1 ∨ (v 2).val = 2 := by
      have hlt := ZMod.val_lt (v 2)
      have hne : (v 2).val ≠ 0 := fun h0 => hv2 ((ZMod.val_eq_zero _).mp h0)
      omega
    have hc3 : c ^ 3 = 1 := h.pow_three h.mem_c
    rcases hval with h1 | h2
    · rw [h1, pow_one] at hcpow
      exact h.not_mem_c hcpow
    · rw [h2] at hcpow
      apply h.not_mem_c
      have e : c = (c ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
      rw [e]
      exact pow_mem hcpow 2
  · intro hv2
    rw [hx, hv2, ZMod.val_zero, pow_zero, mul_one]
    exact hXB

end BasisData

section Matrices

omit [Finite G] in
theorem glHom_entry (f : Multiplicative (Fin 3 → ZMod 3) ≃* E) (σ : MulAut E) (i j : Fin 3) :
    ((KFacts.glHom f σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j =
      Sec12.coordVec f (σ (f (Multiplicative.ofAdd (Pi.single j 1)))) i := by
  have h1 := Sec13.glHom_mulVec_coordVec f σ (f (Multiplicative.ofAdd (Pi.single j 1)))
  have h2 : Sec12.coordVec f (f (Multiplicative.ofAdd (Pi.single j 1))) = Pi.single j 1 := by
    simp [Sec12.coordVec]
  rw [h2, Matrix.mulVec_single_one] at h1
  rw [← h1]
  rfl

omit [Finite G] in
theorem glHom_eq_of_cols (f : Multiplicative (Fin 3 → ZMod 3) ≃* E) (σ : MulAut E)
    (a₀ a₁ a₂ b₀ b₁ b₂ d₀ d₁ d₂ : ZMod 3)
    (h₀ : (σ (f (Multiplicative.ofAdd (Pi.single 0 1))) : G) =
      (f (Multiplicative.ofAdd ![a₀, a₁, a₂]) : G))
    (h₁ : (σ (f (Multiplicative.ofAdd (Pi.single 1 1))) : G) =
      (f (Multiplicative.ofAdd ![b₀, b₁, b₂]) : G))
    (h₂ : (σ (f (Multiplicative.ofAdd (Pi.single 2 1))) : G) =
      (f (Multiplicative.ofAdd ![d₀, d₁, d₂]) : G)) :
    ((KFacts.glHom f σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      !![a₀, b₀, d₀; a₁, b₁, d₁; a₂, b₂, d₂] := by
  have e₀ : Sec12.coordVec f (σ (f (Multiplicative.ofAdd (Pi.single 0 1)))) = ![a₀, a₁, a₂] := by
    rw [Subtype.ext h₀]
    simp [Sec12.coordVec]
  have e₁ : Sec12.coordVec f (σ (f (Multiplicative.ofAdd (Pi.single 1 1)))) = ![b₀, b₁, b₂] := by
    rw [Subtype.ext h₁]
    simp [Sec12.coordVec]
  have e₂ : Sec12.coordVec f (σ (f (Multiplicative.ofAdd (Pi.single 2 1)))) = ![d₀, d₁, d₂] := by
    rw [Subtype.ext h₂]
    simp [Sec12.coordVec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glHom_entry, e₀, e₁, e₂]

end Matrices

namespace BasisData

variable (h : BasisData E B c X₁ X₂) {f : Multiplicative (Fin 3 → ZMod 3) ≃* E}
include h

omit [Finite G] in
theorem row_two_eq_zero (hf : IsAdapted f X₁ X₂ c) {σ : MulAut E}
    (hσ : ∀ x : E, (x : G) ∈ B → (σ x : G) ∈ B) :
    ((KFacts.glHom f σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 = 0 ∧
      ((KFacts.glHom f σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1 = 0 := by
  rw [glHom_entry, glHom_entry]
  refine ⟨(h.mem_B_iff hf _).mp (hσ _ ?_), (h.mem_B_iff hf _).mp (hσ _ ?_)⟩
  · rw [f_zero hf]
    exact h.X₁_mem
  · rw [f_one hf]
    exact h.X₂_mem

end BasisData

omit [Finite G] in
theorem fixes_of_glHom_eq_tMat {f : Multiplicative (Fin 3 → ZMod 3) ≃* E}
    (hf : IsAdapted f X₁ X₂ c) {σ : MulAut E} {a b : ZMod 3}
    (hσ : KFacts.glHom f σ = tMat a b) :
    (σ (f (Multiplicative.ofAdd (Pi.single 0 1))) : G) = X₁ ∧
      (σ (f (Multiplicative.ofAdd (Pi.single 1 1))) : G) = X₂ := by
  have hcol : ∀ j : Fin 3, j ≠ 2 →
      Sec12.coordVec f (σ (f (Multiplicative.ofAdd (Pi.single j 1)))) =
        Sec12.coordVec f (f (Multiplicative.ofAdd (Pi.single j 1))) := by
    intro j hj
    funext i
    have he := glHom_entry f σ i j
    rw [hσ, coe_tMat] at he
    rw [← he]
    simp only [Sec12.coordVec, MulEquiv.symm_apply_apply, toAdd_ofAdd]
    fin_cases i <;> fin_cases j <;> simp at hj ⊢
  refine ⟨?_, ?_⟩
  · rw [← f_zero hf]
    exact congrArg Subtype.val (KFacts.coordVec_injective f (hcol 0 (by decide)))
  · rw [← f_one hf]
    exact congrArg Subtype.val (KFacts.coordVec_injective f (hcol 1 (by decide)))

namespace CoreData

variable (h : CoreData E B c X₁ X₂ M₁ M₂) {f : Multiplicative (Fin 3 → ZMod 3) ≃* E}
include h

theorem mem_normalizer_E₁ : M₁ ∈ Subgroup.normalizer (E : Set G) :=
  h.mem_normalizer_E h.comm₁ h.mem_norm₁

theorem mem_normalizer_E₂ : M₂ ∈ Subgroup.normalizer (E : Set G) :=
  h.mem_normalizer_E h.comm₂ h.mem_norm₂

theorem glHom_M₁ (hf : IsAdapted f X₁ X₂ c) :
    KFacts.glHom f (E.normalizerMonoidHom ⟨M₁, h.mem_normalizer_E₁⟩) = qHatOne := by
  apply Units.ext
  rw [coe_qHatOne]
  have hX₂3 : X₂ ^ 3 = 1 := h.pow_three (h.le_E h.X₂_mem)
  refine glHom_eq_of_cols f _ 0 2 0 1 0 0 0 0 1 ?_ ?_ ?_
  · rw [Sec13.normalizerMonoidHom_apply_val, f_zero hf, h.r1, coords_apply hf,
      inv_eq_sq_of_pow_three hX₂3]
    simp [show (2 : ZMod 3).val = 2 from rfl]
  · rw [Sec13.normalizerMonoidHom_apply_val, f_one hf, h.r2, coords_apply hf]
    simp [show (1 : ZMod 3).val = 1 from rfl]
  · rw [Sec13.normalizerMonoidHom_apply_val, f_two hf, h.comm₁, mul_inv_cancel_right,
      coords_apply hf]
    simp [show (1 : ZMod 3).val = 1 from rfl]

theorem glHom_M₂ (hf : IsAdapted f X₁ X₂ c) :
    KFacts.glHom f (E.normalizerMonoidHom ⟨M₂, h.mem_normalizer_E₂⟩) = qHatTwo := by
  apply Units.ext
  rw [coe_qHatTwo]
  have hX₁3 : X₁ ^ 3 = 1 := h.pow_three (h.le_E h.X₁_mem)
  have hX₂3 : X₂ ^ 3 = 1 := h.pow_three (h.le_E h.X₂_mem)
  refine glHom_eq_of_cols f _ 2 2 0 2 1 0 0 0 1 ?_ ?_ ?_
  · rw [Sec13.normalizerMonoidHom_apply_val, f_zero hf, h.r3, coords_apply hf,
      inv_eq_sq_of_pow_three hX₂3, inv_eq_sq_of_pow_three hX₁3]
    simp only [show (2 : ZMod 3).val = 2 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_zero,
      mul_one]
    have hc : Commute X₂ X₁ := h.comm₁₂.symm
    exact (hc.pow_pow 2 2).eq
  · rw [Sec13.normalizerMonoidHom_apply_val, f_one hf, h.r4, coords_apply hf]
    simp only [show (2 : ZMod 3).val = 2 from rfl, show (1 : ZMod 3).val = 1 from rfl,
      show (0 : ZMod 3).val = 0 from rfl, pow_zero, pow_one, mul_one]
    rw [mul_assoc, ← h.comm₁₂, ← mul_assoc, ← sq]
  · rw [Sec13.normalizerMonoidHom_apply_val, f_two hf, h.comm₂, mul_inv_cancel_right,
      coords_apply hf]
    simp [show (1 : ZMod 3).val = 1 from rfl]

theorem isIrreducibleOn_K :
    Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.normalizer (B : Set G)) B) := by
  have hX₁3 : X₁ ^ 3 = 1 := h.pow_three (h.le_E h.X₁_mem)
  have hX₂3 : X₂ ^ 3 = 1 := h.pow_three (h.le_E h.X₂_mem)
  obtain ⟨Q1, Q2, -, -, -, -⟩ :=
    Sec13.Item138Proof.q8_rel_facts h.comm₁₂ hX₁3 hX₂3 h.r1 h.r2 h.r3 h.r4
  set τ : MulAut B := B.normalizerMonoidHom ⟨M₁, h.mem_norm₁⟩ with hτ
  have hτmem : τ ∈ Sec4.autIn (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.normalizer (B : Set G)) B :=
    Sec4.mem_autIn_iff.mpr ⟨M₁, h.mem_norm₁,
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr h.comm₁, h.mem_norm₁⟩, rfl⟩
  have hX1inv : X₁⁻¹ ≠ X₁ := by
    intro h1
    apply h.ne_one
    have hsq : X₁ * X₁ = 1 := by
      calc X₁ * X₁ = X₁ * X₁⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel X₁
    calc X₁ = X₁ ^ 3 * (X₁ * X₁)⁻¹ := by group
      _ = 1 := by rw [hX₁3, hsq]; group
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : MulAut B => ((σ ⟨X₁, h.X₁_mem⟩ : B) : G)) h1
    simp only [hτ, Sec13.Item138Proof.normalizerMonoidHom_pow_coe, MulAut.one_apply] at h2
    exact hX1inv (Q1.symm.trans h2)
  have hτ4 : τ ^ 4 = 1 := by
    ext y
    rw [hτ, Sec13.Item138Proof.normalizerMonoidHom_pow_coe]
    change M₁ ^ 4 * y * (M₁ ^ 4)⁻¹ = y
    have hW : ∀ {Z : G}, M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹ = Z⁻¹ → M₁ ^ 4 * Z * (M₁ ^ 4)⁻¹ = Z := by
      intro Z hZ
      rw [show M₁ ^ 4 = M₁ ^ 2 * M₁ ^ 2 by group]
      calc M₁ ^ 2 * M₁ ^ 2 * Z * (M₁ ^ 2 * M₁ ^ 2)⁻¹ =
          M₁ ^ 2 * (M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹) * (M₁ ^ 2)⁻¹ := by group
        _ = M₁ ^ 2 * Z⁻¹ * (M₁ ^ 2)⁻¹ := by rw [hZ]
        _ = (M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹)⁻¹ := by group
        _ = Z := by rw [hZ, inv_inv]
    have hle : Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ ≤
        Subgroup.centralizer ({M₁ ^ 4} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Sec13.Item138Proof.commute_of_conj_eq (hW Q1)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Sec13.Item138Proof.commute_of_conj_eq (hW Q2)).symm
    have hy := Subgroup.mem_centralizer_singleton_iff.mp (hle (h.eq_B.le y.2))
    rw [← hy, mul_inv_cancel_right]
  have : Finite B := inferInstance
  exact Sec13.isIrreducibleOn_of_order_four h.elemAbelian_B h.card_B hτmem hτ4 hτ2

omit [Finite G] in
theorem map_le_yStd (hf : IsAdapted f X₁ X₂ c) :
    (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E)).map (KFacts.glHom f) ≤
      yStd := by
  rw [oUpperThreePrime, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, ⟨hσX, k, hk⟩, rfl⟩
  obtain ⟨w, hwN, hwB, rfl⟩ := Sec4.mem_autIn_iff.mp hσX
  have hrow := h.row_two_eq_zero hf (σ := E.normalizerMonoidHom ⟨w, hwN⟩) fun x hx => by
    rw [Sec13.normalizerMonoidHom_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp hwB x).mp hx
  exact mem_yStd_of_pow hrow.1 hrow.2 (k := k) (by rw [← map_pow, hk, map_one])

theorem tMat_mem_of_le (hf : IsAdapted f X₁ X₂ c)
    (hWB : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hs : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (a b : ZMod 3) :
    tMat a b ∈ (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E)).map
      (KFacts.glHom f) := by
  set K := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.normalizer (B : Set G) with hK
  have hKa : ∀ k ∈ K, k * c = c * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp hk.1
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := inf_le_right
  have hKA : K ≤ Subgroup.normalizer (E : Set G) := fun k hk =>
    h.mem_normalizer_E (hKa k hk) hk.2
  set b₀ := X₁ ^ a.val * X₂ ^ b.val with hb₀
  have hb₀B : b₀ ∈ B := mul_mem (pow_mem h.X₁_mem _) (pow_mem h.X₂_mem _)
  obtain ⟨w, hw, hwT, hwc⟩ := Sec13.exists_transv_of_irreducible h.elemAbelian h.mem_c h.eq_sup
    h.card_B hKa h.isIrreducibleOn_K hKA hKB hWB hs hb₀B
  set σ := E.normalizerMonoidHom ⟨w, hw⟩ with hσ
  have hσX : σ ∈ Sec4.autIn (Subgroup.normalizer (B : Set G)) E :=
    Sec4.mem_autIn_iff.mpr ⟨w, hw, hWB hw, rfl⟩
  have hσ3 : σ ^ 3 = 1 := Sec13.transvAxis_pow_three h.elemAbelian hwT
  refine ⟨σ, Subgroup.subset_closure ⟨hσX, 1, by simpa using hσ3⟩, ?_⟩
  apply Units.ext
  rw [coe_tMat]
  refine glHom_eq_of_cols f σ 1 0 0 0 1 0 a b 1 ?_ ?_ ?_
  · have e := hwT.1 (f (Multiplicative.ofAdd (Pi.single 0 1)))
      (by rw [f_zero hf]; exact h.X₁_mem)
    rw [e, ← single_zero]
  · have e := hwT.1 (f (Multiplicative.ofAdd (Pi.single 1 1)))
      (by rw [f_one hf]; exact h.X₂_mem)
    rw [e, ← single_one]
  · rw [hσ, Sec13.normalizerMonoidHom_apply_val, f_two hf, hwc, coords_apply hf]
    simp only [show (1 : ZMod 3).val = 1 from rfl, pow_one]
    exact h.comm h.mem_c (h.le_E hb₀B)

theorem dOne_dTwo_mem_of_le (hf : IsAdapted f X₁ X₂ c)
    (hWB : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hs : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hy : ∃ y ∈ Subgroup.normalizer (B : Set G), y * c = c * y ∧
      (∀ b ∈ B, y ^ 3 * b * (y ^ 3)⁻¹ = b) ∧ ∃ b ∈ B, y * b * y⁻¹ ≠ b) :
    dOne ∈ (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E)).map
        (KFacts.glHom f) ∧
      dTwo ∈ (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E)).map
        (KFacts.glHom f) := by
  set X := Sec4.autIn (Subgroup.normalizer (B : Set G)) E with hX
  set O := (oUpperThreePrime X).map (KFacts.glHom f) with hO
  have hOY : O ≤ yStd := h.map_le_yStd hf
  have hT := h.tMat_mem_of_le hf hWB hs
  have hn : ∀ σ ∈ X, ∀ x ∈ O, KFacts.glHom f σ * x * (KFacts.glHom f σ)⁻¹ ∈ O := by
    rintro σ hσ _ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ * σ⁻¹, conj_mem_oUpperThreePrime hσ hτ, by simp only [map_mul, map_inv]⟩
  have hn₁ : ∀ x ∈ O, qHatOne * x * qHatOne⁻¹ ∈ O := by
    rw [← h.glHom_M₁ hf]
    exact hn _ (Sec4.mem_autIn_iff.mpr ⟨M₁, h.mem_normalizer_E₁, h.mem_norm₁, rfl⟩)
  have hn₂ : ∀ x ∈ O, qHatTwo * x * qHatTwo⁻¹ ∈ O := by
    rw [← h.glHom_M₂ hf]
    exact hn _ (Sec4.mem_autIn_iff.mpr ⟨M₂, h.mem_normalizer_E₂, h.mem_norm₂, rfl⟩)
  obtain ⟨y, hyB, hyc, hy3, b₁, hb₁B, hb₁⟩ := hy
  have hyE := h.mem_normalizer_E hyc hyB
  set σ := E.normalizerMonoidHom ⟨y, hyE⟩ with hσ
  have hσX : σ ∈ X := Sec4.mem_autIn_iff.mpr ⟨y, hyE, hyB, rfl⟩
  have hσ3 : σ ^ 3 = 1 := by
    ext x
    rw [hσ, Sec13.Item138Proof.normalizerMonoidHom_pow_coe, MulAut.one_apply]
    obtain ⟨i, -, b, hb, hx⟩ := Sec13.exists_pow_mul_of_mem h.elemAbelian h.mem_c h.eq_sup x.2
    have hyc3 : y ^ 3 * c ^ i * (y ^ 3)⁻¹ = c ^ i := by
      rw [((Commute.pow_left hyc 3).pow_right i).eq, mul_inv_cancel_right]
    change y ^ 3 * (x : G) * (y ^ 3)⁻¹ = x
    rw [hx]
    calc y ^ 3 * (c ^ i * b) * (y ^ 3)⁻¹ =
        (y ^ 3 * c ^ i * (y ^ 3)⁻¹) * (y ^ 3 * b * (y ^ 3)⁻¹) := by group
      _ = c ^ i * b := by rw [hyc3, hy3 b hb]
  have hσO : σ ∈ oUpperThreePrime X := Subgroup.subset_closure ⟨hσX, 1, by simpa using hσ3⟩
  set S := KFacts.glHom f σ with hS
  have hSO : S ∈ O := ⟨σ, hσO, rfl⟩
  have hu3 : blk ⟨S, hOY hSO⟩ ^ 3 = 1 := by
    have e : (⟨S, hOY hSO⟩ : yStd) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, hS, ← map_pow, hσ3, map_one]
    rw [← map_pow, e, map_one]
  have hu1 : blk ⟨S, hOY hSO⟩ ≠ 1 := by
    intro h1
    have hS' := eq_tMat_of_blk_eq_one _ h1
    obtain ⟨h₀, h₁⟩ := fixes_of_glHom_eq_tMat hf hS'
    rw [hσ, Sec13.normalizerMonoidHom_apply_val, f_zero hf] at h₀
    rw [hσ, Sec13.normalizerMonoidHom_apply_val, f_one hf] at h₁
    apply hb₁
    have hle : Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ ≤
        Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Sec13.Item138Proof.commute_of_conj_eq h₀).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Sec13.Item138Proof.commute_of_conj_eq h₁).symm
    have hyb := Subgroup.mem_centralizer_singleton_iff.mp (hle (h.eq_B.le hb₁B))
    rw [← hyb, mul_inv_cancel_right]
  exact dOne_dTwo_mem hOY hT hn₁ hn₂ hSO hu3 hu1

theorem mem_map_of_not_le
    (hf : IsAdapted f X₁ X₂ c)
    (hWB : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hs : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {M : GL33} (hMY : M ∈ yStd) (hM3 : M ^ 3 = 1) :
    M ∈ (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E)).map
      (KFacts.glHom f) := by
  set K := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.normalizer (B : Set G) with hK
  have hKa : ∀ k ∈ K, k * c = c * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp hk.1
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := inf_le_right
  have hKA : K ≤ Subgroup.normalizer (E : Set G) := fun k hk =>
    h.mem_normalizer_E (hKa k hk) hk.2
  have hirrW := Sec13.isIrreducibleOn_wStar_of h.elemAbelian h.card_eq h.mem_c h.eq_sup
    h.not_mem_c h.card_B hKa h.isIrreducibleOn_K hKA hKB hs hWB
  set H := (Sec13.wStar E).map (KFacts.glHom f) with hH
  have hHirr := KFacts.isIrreducibleOn_map_glHom f hirrW
  have hq₁ : qHatOne ∈ H := ⟨_, Sec4.mem_autIn_iff.mpr ⟨M₁, h.mem_normalizer_E₁,
    Subgroup.mem_top _, rfl⟩, h.glHom_M₁ hf⟩
  have hq₂ : qHatTwo ∈ H := ⟨_, Sec4.mem_autIn_iff.mpr ⟨M₂, h.mem_normalizer_E₂,
    Subgroup.mem_top _, rfl⟩, h.glHom_M₂ hf⟩
  obtain ⟨r4, r2, r3, rne⟩ := qHat_rel
  have h4 : 4 ∣ Nat.card H := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (⟨qHatOne, hq₁⟩ : H) = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · intro h2
        exact rne (by simpa using congrArg Subtype.val h2)
      · exact Subtype.ext (by simpa using r4)
    rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num, ← hord]
    exact orderOf_dvd_natCard _
  have hSL : CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ H := by
    by_contra hSL
    obtain ⟨ψ, hψ⟩ := KFacts.exists_injective_of_caseC (KFacts.bloomCaseC_of hHirr h4 hSL)
    have hsq := Sec13.sq_eq_one_of_q8_rel hψ (x := (⟨qHatOne, hq₁⟩ : H))
      (y := (⟨qHatTwo, hq₂⟩ : H)) (Subtype.ext (by simpa using r4))
      (Subtype.ext (by simpa using r2)) (Subtype.ext (by simpa using r3))
    exact rne (by simpa using congrArg Subtype.val hsq)
  obtain ⟨σ, hσW, hσM⟩ := hSL (Subgroup.subset_closure (mem_yStd_iff.mp hMY).2.2.2)
  obtain ⟨w, hw, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσW
  have hwB : w ∈ Subgroup.normalizer (B : Set G) := by
    have h₀ : ((E.normalizerMonoidHom ⟨w, hw⟩ (f (Multiplicative.ofAdd (Pi.single 0 1))) : E) :
        G) ∈ B := by
      rw [h.mem_B_iff hf, ← glHom_entry f _ 2 0, hσM]
      exact (mem_yStd_iff.mp hMY).1
    have h₁ : ((E.normalizerMonoidHom ⟨w, hw⟩ (f (Multiplicative.ofAdd (Pi.single 1 1))) : E) :
        G) ∈ B := by
      rw [h.mem_B_iff hf, ← glHom_entry f _ 2 1, hσM]
      exact (mem_yStd_iff.mp hMY).2.1
    rw [Sec13.normalizerMonoidHom_apply_val, f_zero hf] at h₀
    rw [Sec13.normalizerMonoidHom_apply_val, f_one hf] at h₁
    rw [h.eq_B] at h₀ h₁ ⊢
    exact Sec13.Item138Proof.mem_normalizer_sup_zpowers h₀ h₁
  have hσX : E.normalizerMonoidHom ⟨w, hw⟩ ∈ Sec4.autIn (Subgroup.normalizer (B : Set G)) E :=
    Sec4.mem_autIn_iff.mpr ⟨w, hw, hwB, rfl⟩
  have hσ3 : E.normalizerMonoidHom ⟨w, hw⟩ ^ 3 = 1 :=
    KFacts.glHom_injective f (by rw [map_pow, hσM, hM3, map_one])
  exact ⟨_, Subgroup.subset_closure ⟨hσX, 1, by simpa using hσ3⟩, hσM⟩

end CoreData

theorem isExtOf_of_coreData
    (h : CoreData E B c X₁ X₂ M₁ M₂)
    (hy : ∃ y ∈ Subgroup.normalizer (B : Set G), y * c = c * y ∧
      (∀ b ∈ B, y ^ 3 * b * (y ^ 3)⁻¹ = b) ∧ ∃ b ∈ B, y * b * y⁻¹ ≠ b)
    (hs : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Sec4.IsExtOf (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E)) SL23
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) := by
  obtain ⟨f, hf⟩ := h.exists_adapted
  set O := oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (B : Set G)) E) with hO
  have hOY := h.map_le_yStd hf
  have hYO : yStd ≤ O.map (KFacts.glHom f) := by
    by_cases hWB : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (B : Set G)
    · obtain ⟨h₁, h₂⟩ := h.dOne_dTwo_mem_of_le hf hWB hs hy
      exact yStd_le_of_mem (h.tMat_mem_of_le hf hWB hs) h₁ h₂
    · exact yStd_le_of_mem
        (fun a b => h.mem_map_of_not_le hf hWB hs (tMat_mem_yStd a b) (tMat_pow_three a b))
        (h.mem_map_of_not_le hf hWB hs dOne_mem_yStd dOne_pow_three)
        (h.mem_map_of_not_le hf hWB hs dTwo_mem_yStd dTwo_pow_three)
  have heq : O.map (KFacts.glHom f) = yStd := le_antisymm hOY hYO
  exact isExtOf_of_mulEquiv' ((O.equivMapOfInjective _ (KFacts.glHom_injective f)).trans
    (MulEquiv.subgroupCongr heq)) isExtOf_yStd

end CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof
