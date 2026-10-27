module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs
public import CFSG.Quasithin.Background.A4Four
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Quasithin.EmptyFaithful.S1422Quot
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.C5 CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem isTwoNatType_card_quot {L : Subgroup G} {n : ℕ} (h : IsTwoNatType L n) :
    Nat.card (OTwoQuot L) = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨F, _, hFin, hF, α, hα, hker, -⟩ := h
  have hker' : α.ker = CFSG.Open.pCore 2 ↥L := hker.trans (CFSG.pCore_eq_open _ _)
  have h1 : Nat.card (↥L ⧸ α.ker) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv
  rw [hker'] at h1
  have h2 : Nat.card (OTwoQuot L) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := h1
  rw [h2, card_sl_two_of_fintype F, hF]
  have : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]

theorem isOmega4MinusType_card_quot {L : Subgroup G} {n : ℕ} (h : IsOmega4MinusType L n) :
    Nat.card (OTwoQuot L) = 4 ^ n * (16 ^ n - 1) := by
  obtain ⟨F, _, hFin, hF, α, hα, hker, -⟩ := h
  have hker' : α.ker = CFSG.Open.pCore 2 ↥L := hker.trans (CFSG.pCore_eq_open _ _)
  have h1 : Nat.card (↥L ⧸ α.ker) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv
  rw [hker'] at h1
  have h2 : Nat.card (OTwoQuot L) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := h1
  rw [h2, card_sl_two_of_fintype F, hF]
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have h16 : (16 : ℕ) ^ n = (2 ^ (2 * n)) ^ 2 := by
    rw [← pow_mul, show 2 * n * 2 = 4 * n by ring, pow_mul]; norm_num
  rw [h4, h16]

variable [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qLocalData.one_le (hD : U4qLocalData L1 L2 S f) : 1 ≤ f := by
  obtain ⟨F, hField, hFintype, hFcard, -⟩ := hD.twoNat_left
  letI := hField
  letI := hFintype
  have htwo : 2 ≤ Fintype.card F := Fintype.one_lt_card
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hFcard
  omega

theorem U4qLocalData.twoPart_left (hD : U4qLocalData L1 L2 S f) :
    twoPart L1 = 2 ^ (6 * f) := by
  have hf := hD.one_le
  refine twoPart_of_card (u := 4 ^ f - 1) ?_ ?_
  · rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact odd_two_pow_sub_one (by omega)
  · rw [card_eq_card_oTwoQuot_mul, isTwoNatType_card_quot hD.twoNat_left, hD.card_left]
    rw [show 6 * f = f + 5 * f by ring, pow_add]
    ring

theorem U4qLocalData.twoPart_right (hD : U4qLocalData L1 L2 S f) :
    twoPart L2 = 2 ^ (6 * f) := by
  have hf := hD.one_le
  refine twoPart_of_card (u := 16 ^ f - 1) ?_ ?_
  · rw [show (16 : ℕ) ^ f = 2 ^ (4 * f) by rw [pow_mul]; norm_num]
    exact odd_two_pow_sub_one (by omega)
  · rw [card_eq_card_oTwoQuot_mul, isOmega4MinusType_card_quot hD.omega_right, hD.card_right]
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num,
      show 6 * f = 2 * f + 4 * f by ring, pow_add]
    ring

theorem U4qLocalData.le_left (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : S ≤ L1 := by
  have hcard : Nat.card ↥(S ⊓ L1) = Nat.card ↥S := by
    rw [IsSylowTwoOf.card_eq hH.h1.sylow, hD.twoPart_left, hS]
  exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]))

theorem U4qLocalData.le_right (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : S ≤ L2 := by
  have hcard : Nat.card ↥(S ⊓ L2) = Nat.card ↥S := by
    rw [IsSylowTwoOf.card_eq hH.h2.sylow, hD.twoPart_right, hS]
  exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]))

private theorem U4qLocalData.commutator_eq_center_left (hD : U4qLocalData L1 L2 S f) :
    commutator ↥(pCoreOf 2 L1) = Subgroup.center ↥(pCoreOf 2 L1) := by
  rcases hD.special_left.1.2 with ⟨hab, -⟩ | ⟨hc, -, -⟩
  · exfalso
    have hcen : Subgroup.center ↥(pCoreOf 2 L1) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun x =>
        Subgroup.mem_center_iff.mpr fun g => hab.is_comm.comm g x
    have hZ := hD.special_left.2.2
    rw [hcen, Subgroup.card_top, hD.special_left.2.1] at hZ
    have hf := hD.one_le
    have hlt : 2 ^ f < (2 ^ f) ^ (1 + 2 * 2) := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ (1 + 2 * 2) :=
          Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)
    omega
  · exact hc

private theorem U4qLocalData.card_center_left (hD : U4qLocalData L1 L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L1)) = 2 ^ f := by
  have he : centerOf (pCoreOf 2 L1) = (Subgroup.center ↥(pCoreOf 2 L1)).map
      (pCoreOf 2 L1).subtype := by
    ext z
    constructor
    · intro hz
      refine ⟨⟨z, hz.1⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2), rfl⟩
    · rintro ⟨z', hz', rfl⟩
      exact ⟨z'.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨y, hy⟩)⟩
  rw [he, Subgroup.card_map_of_injective (pCoreOf 2 L1).subtype_injective]
  exact hD.special_left.2.2

private theorem U4qLocalData.center_le_blockZ_left (hD : U4qLocalData L1 L2 S f) :
    centerOf (pCoreOf 2 L1) ≤ blockZ L1 := by
  refine le_inf ?_ (Subgroup.le_centralizer_iff.mp hD.center_left)
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥(pCoreOf 2 L1)) ∈ commutator ↥(pCoreOf 2 L1) := by
    rw [hD.commutator_eq_center_left]
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 y y.2)
  have key : commutator ↥(pCoreOf 2 L1) ≤ (blockU L1).comap (pCoreOf 2 L1).subtype := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact Subgroup.commutator_mem_commutator (show (a : G) ∈ blockQ L1 from a.2)
      (pCoreOf_le 2 L1 b.2)
  exact key hzc

private theorem U4qLocalData.card_blockU_left (hD : U4qLocalData L1 L2 S f) :
    Nat.card (blockU L1) = Nat.card (blockZ L1) * 2 ^ (4 * f) := by
  obtain ⟨F, hField, hFintype, hFcard, α, -, -, β, hβsurj, hβker, -⟩ := hD.twoNat_left
  letI := hField
  letI := hFintype
  have hcardrange : Nat.card β.range = 2 ^ (4 * f) := by
    rw [MonoidHom.range_eq_top.mpr hβsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd]
    show Nat.card (Fin 2 → Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, hFcard,
      ← pow_mul, ← pow_mul]
    ring_nf
  have hkerZ : Nat.card β.ker = Nat.card (blockZ L1) := by
    rw [hβker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ L1 ≤ blockU L1)).toEquiv
  rw [← Subgroup.card_ker_mul_card_range β, hkerZ, hcardrange]

theorem U4qLocalData.blockU_left (hD : U4qLocalData L1 L2 S f) :
    blockU L1 = pCoreOf 2 L1 := by
  have hle : blockU L1 ≤ pCoreOf 2 L1 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L1)
  have hge : 2 ^ f ≤ Nat.card (blockZ L1) :=
    hD.card_center_left ▸ Subgroup.card_le_of_le hD.center_le_blockZ_left
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hD.card_left, hD.card_blockU_left]
  calc 2 ^ (5 * f) = 2 ^ f * 2 ^ (4 * f) := by rw [← pow_add]; ring_nf
    _ ≤ Nat.card (blockZ L1) * 2 ^ (4 * f) := Nat.mul_le_mul_right _ hge

theorem U4qLocalData.blockZ_left (hD : U4qLocalData L1 L2 S f) :
    blockZ L1 = centerOf (pCoreOf 2 L1) := by
  have h := hD.card_blockU_left
  rw [hD.blockU_left, hD.card_left,
    show 2 ^ (5 * f) = 2 ^ f * 2 ^ (4 * f) by rw [← pow_add]; ring_nf] at h
  have hZ : Nat.card (blockZ L1) = 2 ^ f :=
    (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm
  exact (Subgroup.eq_of_le_of_card_ge hD.center_le_blockZ_left
    (by rw [hZ, hD.card_center_left])).symm

private theorem card_le_herm {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ (2 * n)) {P : Matrix (Fin 2) (Fin 2) F → Prop}
    (hP : ∀ X, P X ↔ X.map (· ^ 2 ^ n) = X.transpose) :
    2 ^ (4 * n) ≤ Nat.card {X // P X} := by
  have hU : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn, by rw [Nat.card_eq_fintype_card, hF]⟩
  have hbb : ∀ b : F, (b ^ 2 ^ n) ^ 2 ^ n = b := fun b => by
    have := hU.bar_bar b
    rwa [hU.bar_apply, hU.bar_apply] at this
  let g : hU.fixedField × hU.fixedField × F → {X // P X} := fun p =>
    ⟨!![(p.1 : F), p.2.2; p.2.2 ^ 2 ^ n, (p.2.1 : F)], (hP _).mpr (by
      have h1 : ((p.1 : F)) ^ 2 ^ n = p.1 := by
        rw [← hU.bar_apply]; exact (hU.mem_fixedField).mp p.1.2
      have h2 : ((p.2.1 : F)) ^ 2 ^ n = p.2.1 := by
        rw [← hU.bar_apply]; exact (hU.mem_fixedField).mp p.2.1.2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, hbb])⟩
  have hg : Function.Injective g := by
    rintro ⟨a, d, b⟩ ⟨a', d', b'⟩ hab
    have hX := congrArg Subtype.val hab
    have e11 := congrFun (congrFun hX 0) 0
    have e12 := congrFun (congrFun hX 0) 1
    have e22 := congrFun (congrFun hX 1) 1
    simp only [g, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e11 e12 e22
    exact Prod.ext (Subtype.ext e11) (Prod.ext (Subtype.ext e22) e12)
  have hcard : Nat.card (hU.fixedField × hU.fixedField × F) = 2 ^ (4 * n) := by
    rw [Nat.card_prod, Nat.card_prod, hU.card_fixedField, Nat.card_eq_fintype_card, hF,
      ← pow_add, ← pow_add]
    ring_nf
  rw [← hcard]
  exact Nat.card_le_card_of_injective g hg

private theorem U4qLocalData.card_range_right (hD : U4qLocalData L1 L2 S f) :
    ∃ (k : ℕ), Nat.card (blockU L2) = Nat.card (blockZ L2) * k ∧ 2 ^ (4 * f) ≤ k := by
  obtain ⟨F, hField, hFintype, hFcard, α, -, -, β, hβrange, hβker, -⟩ := hD.omega_right
  letI := hField
  letI := hFintype
  have hkerZ : Nat.card β.ker = Nat.card (blockZ L2) := by
    rw [hβker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ L2 ≤ blockU L2)).toEquiv
  refine ⟨Nat.card β.range, by rw [← Subgroup.card_ker_mul_card_range β, hkerZ], ?_⟩
  have hle := card_le_herm (P := fun X => ∃ u, Multiplicative.toAdd (β u) = X) hD.one_le
    hFcard hβrange
  refine hle.trans (Nat.card_le_card_of_injective
    (fun X => ⟨Multiplicative.ofAdd X.1, ?_⟩) ?_)
  · obtain ⟨u, hu⟩ := X.2
    exact ⟨u, by rw [← hu]; rfl⟩
  · intro X Y hXY
    exact Subtype.ext (Multiplicative.ofAdd.injective (congrArg Subtype.val hXY))

theorem U4qLocalData.blockU_right (hD : U4qLocalData L1 L2 S f) :
    blockU L2 = pCoreOf 2 L2 := by
  have hle : blockU L2 ≤ pCoreOf 2 L2 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L2)
  obtain ⟨k, hk, hk4⟩ := hD.card_range_right
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hD.card_right, hk]
  calc 2 ^ (4 * f) ≤ k := hk4
    _ = 1 * k := (one_mul k).symm
    _ ≤ Nat.card (blockZ L2) * k := Nat.mul_le_mul_right _ Nat.card_pos

theorem U4qLocalData.blockZ_right (hD : U4qLocalData L1 L2 S f) : blockZ L2 = ⊥ := by
  obtain ⟨k, hk, hk4⟩ := hD.card_range_right
  have hU : Nat.card (blockU L2) = 2 ^ (4 * f) := by rw [hD.blockU_right, hD.card_right]
  have hpos : 0 < k := lt_of_lt_of_le (by positivity) hk4
  have h1 : Nat.card (blockZ L2) * k ≤ 1 * k := by
    rw [← hk, hU, one_mul]; exact hk4
  have hZ1 : Nat.card (blockZ L2) ≤ 1 := Nat.le_of_mul_le_mul_right h1 hpos
  exact Subgroup.card_eq_one.mp (le_antisymm hZ1 Nat.card_pos)

theorem U4qLocalData.isElemAbelian_right (hD : U4qLocalData L1 L2 S f) :
    IsElemAbelian 2 (pCoreOf 2 L2) := by
  rw [← hD.blockU_right]
  obtain ⟨F, hField, hFintype, hFcard, α, -, -, β, -, hβker, -⟩ := hD.omega_right
  letI := hField
  letI := hFintype
  have hker : β.ker = ⊥ := by
    rw [hβker, hD.blockZ_right]
    simp
  have hβinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hker
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hcomm : ∀ a b : ↥(blockU L2), a * b = b * a := by
    intro a b
    exact hβinj (by rw [map_mul, map_mul, mul_comm])
  have hsq : ∀ a : ↥(blockU L2), a ^ 2 = 1 := by
    intro a
    apply hβinj
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    simpa using CharTwo.two_nsmul (Multiplicative.toAdd (β a))
  refine ⟨IsMulCommutative.of_comm hcomm, ?_⟩
  intro x hx
  simpa using congrArg Subtype.val (hsq ⟨x, hx⟩)

private theorem charTwo_vertex_right (hH : Hyp111 L1 L2 S) : CharTwo L2 := by
  have hle : L2 ≤ L2 ⊔ S ⊔ borelOf L1 S := le_sup_left.trans le_sup_left
  refine CharTwo.of_normal hH.h2.charTwo hle ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  exact sup_le (sup_le Subgroup.le_normalizer hH.h2.normalizes) hH.h2.borel_le

theorem U4qLocalData.center_le_right (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : centerOf (pCoreOf 2 L1) ≤ pCoreOf 2 L2 := by
  intro z hz
  have hzL2 : z ∈ L2 := hD.le_right hH hS (hH.pCoreOf_le_left hz.1)
  have hzc : z ∈ Subgroup.centralizer (L1 : Set G) :=
    (Subgroup.le_centralizer_iff.mp hD.center_left) hz
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 L2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hzc y (hD.le_left hH hS (hH.pCoreOf_le_right hy))
  exact charTwo_vertex_right hH ⟨hzL2, hzC⟩

end CFSG.Quasithin.F112R.St84

end
