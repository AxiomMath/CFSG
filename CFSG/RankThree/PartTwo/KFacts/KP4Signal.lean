module

public import CFSG.RankThree.PartTwo.KFacts.KP4Basic
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizer
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.WittDesign
open CFSG.LocalAnalysis.ComponentInitial MulAction
open CFSG.RankThree.PartTwo (invariantPiSubgroups maxInvariantPiSubgroups piCompl piOf
  mem_invariantPiSubgroups_iff mem_maxInvariantPiSubgroups_iff isPiSubgroup_piCompl_iff
  isPiSubgroup_piOf_iff)
open CFSG.RankThree.Asc83Table.M22 (x y X Y E)
open scoped Pointwise

theorem P0_comm {a b : G22} (ha : a ∈ P0) (hb : b ∈ P0) : a * b = b * a := by
  obtain ⟨i, j, -, -, rfl⟩ := E.exists_pow_mul_pow ha
  obtain ⟨k, l, -, -, rfl⟩ := E.exists_pow_mul_pow hb
  have hXY : Commute E.a E.b := E.hab
  have h1 : Commute (E.a ^ i) (E.a ^ k * E.b ^ l) :=
    ((Commute.refl E.a).pow_pow i k).mul_right (hXY.pow_pow i l)
  have h2 : Commute (E.b ^ j) (E.a ^ k * E.b ^ l) :=
    (hXY.symm.pow_pow j k).mul_right ((Commute.refl E.b).pow_pow j l)
  exact (h1.mul_left h2).eq

theorem P0_le_centralizer
    (i : Fin 4) : P0 ≤ centralizer ({lineE i} : Set G22) := fun _ hg =>
  mem_centralizer_singleton_iff.2 (P0_comm hg (lineE_mem_P0 i))

instance : IsElementaryAbelian 3 P0 := E.isElementaryAbelian

section Invariant

variable {Q : Subgroup G22}

theorem P0_le_normalizer_inf
    (hP : P0 ≤ normalizer (Q : Set G22)) (i : Fin 4) :
    P0 ≤ normalizer ((Q ⊓ centralizer ({lineE i} : Set G22) : Subgroup G22) : Set G22) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  have hgC := P0_le_centralizer i hg
  have hQ := mem_normalizer_iff.1 (hP hg) h
  have hC : h ∈ centralizer ({lineE i} : Set G22) ↔
      g * h * g⁻¹ ∈ centralizer ({lineE i} : Set G22) := by
    constructor
    · intro hh
      exact mul_mem (mul_mem hgC hh) (inv_mem hgC)
    · intro hh
      have := mul_mem (mul_mem (inv_mem hgC) hh) hgC
      rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at this
  rw [mem_inf, mem_inf, hQ, hC]

theorem inf_centralizer_cases
    (h3 : ¬ 3 ∣ Nat.card Q) (hP : P0 ≤ normalizer (Q : Set G22))
    (i : Fin 4) : Q ⊓ centralizer ({lineE i} : Set G22) = ⊥ ∨
      Q ⊓ centralizer ({lineE i} : Set G22) = V i := by
  have hle : Q ⊓ centralizer ({lineE i} : Set G22) ≤ V i :=
    le_V_of_not_dvd inf_le_right fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact V_minimal i hle (P0_le_normalizer_inf hP i)

theorem le_iSup_inf
    (h3 : ¬ 3 ∣ Nat.card Q) (hP : P0 ≤ normalizer (Q : Set G22)) :
    Q ≤ ⨆ i : Fin 4, Q ⊓ centralizer ({lineE i} : Set G22) := by
  classical
  let φ : P0 →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hP)
  let _ : MulDistribMulAction P0 Q := MulDistribMulAction.compHom Q φ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := P0) (H := Q) (p := 3)
    (by rw [card_P0]; norm_num) h3
  have hfix : ∀ (a : P0) (q : Q), q ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q →
      (q : G22) * a = a * q := by
    intro a q hq
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hq
    have h := congrArg Subtype.val hq
    change (a : G22) * q * (a : G22)⁻¹ = q at h
    nth_rewrite 1 [← h]
    group
  have hle : (⨆ (a : P0) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q) ≤
      (⨆ i : Fin 4, Q ⊓ centralizer ({lineE i} : Set G22)).comap Q.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro r hr
    obtain ⟨i, hi⟩ := exists_centralizer_eq a.2 fun h => ha (Subtype.ext h)
    have hrC : (r : G22) ∈ centralizer ({lineE i} : Set G22) := by
      rw [← hi]
      exact mem_centralizer_singleton_iff.2 (hfix a r hr)
    exact le_iSup (fun i : Fin 4 => Q ⊓ centralizer ({lineE i} : Set G22)) i ⟨r.2, hrC⟩
  intro q hq
  have hq' : (⟨q, hq⟩ : Q) ∈ (⊤ : Subgroup Q) := mem_top _
  rw [← hgen] at hq'
  exact hle hq'

end Invariant

theorem pair_facts : ∀ k : Fin 4, ((vA (pairFst k) * vA (pairSnd k)) ^ 2) ^ 3 = 1 ∧
    (vA (pairFst k) * vA (pairSnd k)) ^ 2 ≠ 1 := by
  decide +kernel

theorem three_dvd_card_pair (k : Fin 4) :
    3 ∣ Nat.card (V (pairFst k) ⊔ V (pairSnd k) : Subgroup G22) := by
  set g : G22 := (vAE (pairFst k) * vAE (pairSnd k)) ^ 2
  have hg : g ∈ V (pairFst k) ⊔ V (pairSnd k) :=
    pow_mem (mul_mem (mem_sup_left FourGroup.left_mem_kleinFourOf)
      (mem_sup_right FourGroup.left_mem_kleinFourOf)) 2
  have ho : orderOf g = 3 := orderOf_eq_prime (Subtype.ext (pair_facts k).1)
    fun h => (pair_facts k).2 (congrArg Subtype.val h)
  rw [← ho, ← Subgroup.orderOf_mk g hg]
  exact orderOf_dvd_natCard _

@[expose] def hexFst : Fin 2 → Fin 4 := ![0, 2]

@[expose] def hexSnd : Fin 2 → Fin 4 := ![1, 3]

@[expose] def hexad : Fin 2 → Finset (Fin 22) := ![hexOne, hexTwo]

@[expose] def R
    (j : Fin 2) : Subgroup G22 := V (hexFst j) ⊔ V (hexSnd j)

theorem le_R_cases
    {Q : Subgroup G22} (h3 : ¬ 3 ∣ Nat.card Q)
    (hP : P0 ≤ normalizer (Q : Set G22)) : Q ≤ R 0 ∨ Q ≤ R 1 := by
  set C : Fin 4 → Subgroup G22 := fun i => Q ⊓ centralizer ({lineE i} : Set G22) with hCdef
  have hcases : ∀ i, C i = ⊥ ∨ C i = V i := inf_centralizer_cases h3 hP
  have hpair : ∀ k : Fin 4, C (pairFst k) = ⊥ ∨ C (pairSnd k) = ⊥ := by
    intro k
    rcases hcases (pairFst k) with h1 | h1
    · exact Or.inl h1
    rcases hcases (pairSnd k) with h2 | h2
    · exact Or.inr h2
    exfalso
    apply h3
    have hle : V (pairFst k) ⊔ V (pairSnd k) ≤ Q :=
      sup_le (h1 ▸ inf_le_left) (h2 ▸ inf_le_left)
    exact (three_dvd_card_pair k).trans (Subgroup.card_dvd_of_le hle)
  have hQ : Q ≤ ⨆ i, C i := le_iSup_inf h3 hP
  have hbound : ∀ i, C i ≤ V i := fun i =>
    (hcases i).elim (fun h => h ▸ bot_le) fun h => h.le
  by_cases h01 : C 0 = ⊥ ∧ C 1 = ⊥
  · right
    refine hQ.trans (iSup_le fun i => ?_)
    fin_cases i
    · exact h01.1.le.trans bot_le
    · exact h01.2.le.trans bot_le
    · exact (hbound 2).trans le_sup_left
    · exact (hbound 3).trans le_sup_right
  · left
    have h23 : C 2 = ⊥ ∧ C 3 = ⊥ := by
      rcases not_and_or.1 h01 with h0 | h1
      · exact ⟨(hpair 0).resolve_left h0, (hpair 1).resolve_left h0⟩
      · exact ⟨(hpair 2).resolve_left h1, (hpair 3).resolve_left h1⟩
    refine hQ.trans (iSup_le fun i => ?_)
    fin_cases i
    · exact (hbound 0).trans le_sup_left
    · exact (hbound 1).trans le_sup_right
    · exact h23.1.le.trans bot_le
    · exact h23.2.le.trans bot_le

theorem hex_facts : ∀ j : Fin 2, (∀ p ∈ hexad j, vA (hexFst j) p = p ∧ vB (hexFst j) p = p ∧
      vA (hexSnd j) p = p ∧ vB (hexSnd j) p = p) ∧
    (∀ k l : Fin 4, k ≠ 0 → l ≠ 0 → vElem (hexFst j) k ≠ vElem (hexSnd j) l) := by
  decide +kernel

theorem hex_inv : ∀ j : Fin 2, ∀ p ∈ hexad j, x p ∈ hexad j ∧ y p ∈ hexad j := by
  decide +kernel

theorem hexad_mem (j : Fin 2) : hexad j ∈ hexads := by
  obtain ⟨-, -, -, -, -, h1, h2⟩ := kp4_counts
  fin_cases j
  · exact mem_hexads.2 h1
  · exact mem_hexads.2 h2

theorem V_le_kernelSubgroup_fst
    (j : Fin 2) : V (hexFst j) ≤ kernelSubgroup (hexad j) := by
  rw [← V_eq_closure, closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_kernelSubgroup] <;> intro p hp
  · exact ((hex_facts j).1 p hp).1
  · exact ((hex_facts j).1 p hp).2.1

theorem V_le_kernelSubgroup_snd
    (j : Fin 2) : V (hexSnd j) ≤ kernelSubgroup (hexad j) := by
  rw [← V_eq_closure, closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_kernelSubgroup] <;> intro p hp
  · exact ((hex_facts j).1 p hp).2.2.1
  · exact ((hex_facts j).1 p hp).2.2.2

theorem R_le_kernelSubgroup
    (j : Fin 2) : R j ≤ kernelSubgroup (hexad j) :=
  sup_le (V_le_kernelSubgroup_fst j) (V_le_kernelSubgroup_snd j)

theorem V_inf_V (j : Fin 2) : V (hexFst j) ⊓ V (hexSnd j) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  rw [mem_bot]
  by_contra hne
  have h1 : ∃ k : Fin 4, k ≠ 0 ∧ (g : Perm (Fin 22)) = vElem (hexFst j) k := by
    rcases mem_V_iff.1 hg1 with h | h | h | h
    · exact absurd h hne
    · exact ⟨1, by decide, congrArg Subtype.val h⟩
    · exact ⟨2, by decide, congrArg Subtype.val h⟩
    · exact ⟨3, by decide, congrArg Subtype.val h⟩
  have h2 : ∃ l : Fin 4, l ≠ 0 ∧ (g : Perm (Fin 22)) = vElem (hexSnd j) l := by
    rcases mem_V_iff.1 hg2 with h | h | h | h
    · exact absurd h hne
    · exact ⟨1, by decide, congrArg Subtype.val h⟩
    · exact ⟨2, by decide, congrArg Subtype.val h⟩
    · exact ⟨3, by decide, congrArg Subtype.val h⟩
  obtain ⟨k, hk, hgk⟩ := h1
  obtain ⟨l, hl, hgl⟩ := h2
  exact (hex_facts j).2 k l hk hl (hgk.symm.trans hgl)

theorem sixteen_le_card_R (j : Fin 2) : 16 ≤ Nat.card (R j) := by
  let f : V (hexFst j) × V (hexSnd j) → R j := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    have h' : (v : G22) * w = v' * w' := congrArg Subtype.val h
    have hmem : (v' : G22)⁻¹ * v = w' * (w : G22)⁻¹ := by
      calc (v' : G22)⁻¹ * v = (v' : G22)⁻¹ * (v * w) * (w : G22)⁻¹ := by group
        _ = (v' : G22)⁻¹ * (v' * w') * (w : G22)⁻¹ := by rw [h']
        _ = w' * (w : G22)⁻¹ := by group
    have hbot : (v' : G22)⁻¹ * v ∈ V (hexFst j) ⊓ V (hexSnd j) :=
      ⟨(V (hexFst j)).mul_mem ((V (hexFst j)).inv_mem v'.2) v.2,
        hmem ▸ (V (hexSnd j)).mul_mem w'.2 ((V (hexSnd j)).inv_mem w.2)⟩
    rw [V_inf_V, mem_bot] at hbot
    have hv : (v : G22) = v' := by
      rw [inv_mul_eq_one] at hbot
      exact hbot.symm
    have hw : (w : G22) = w' := by
      rw [hv] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hv) (Subtype.ext hw)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, card_V, card_V] at this

theorem R_eq_kernelSubgroup
    (j : Fin 2) : R j = kernelSubgroup (hexad j) :=
  Subgroup.eq_of_le_of_card_ge (R_le_kernelSubgroup j)
    (by rw [card_kernelSubgroup (hexad_mem j)]; exact sixteen_le_card_R j)

theorem card_R
    (j : Fin 2) : Nat.card (R j) = 16 := by
  rw [R_eq_kernelSubgroup, card_kernelSubgroup (hexad_mem j)]

theorem isElementaryAbelian_of_sq {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ g ∈ H, g * g = 1) : IsElementaryAbelian 2 H := by
  have hinv : ∀ g ∈ H, g⁻¹ = g := fun g hg => inv_eq_of_mul_eq_one_right (h g hg)
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    calc a * b = (a * b)⁻¹ := (hinv _ (mul_mem ha hb)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv b hb, hinv a ha]
  exact { is_comm := ⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
            Subtype.ext (by rw [Subgroup.coe_pow, sq, h a a.2, Subgroup.coe_one]) }

theorem R_sq
    (j : Fin 2) {g : G22} (hg : g ∈ R j) : g * g = 1 := by
  rw [R_eq_kernelSubgroup] at hg
  exact kernelSubgroup_sq (hexad_mem j) hg

theorem isElementaryAbelian_R
    (j : Fin 2) : IsElementaryAbelian 2 (R j) :=
  isElementaryAbelian_of_sq fun _ hg => R_sq j hg

theorem not_three_dvd_card_R
    (j : Fin 2) : ¬ 3 ∣ Nat.card (R j) := by
  rw [card_R]
  norm_num

theorem isPGroup_R
    (j : Fin 2) : IsPGroup 2 (R j) :=
  IsPGroup.of_card (n := 4) (by rw [card_R]; norm_num)

theorem R_inf_centralizer_fst
    (j : Fin 2) :
    R j ⊓ centralizer ({lineE (hexFst j)} : Set G22) = V (hexFst j) :=
  le_antisymm (le_V_of_not_dvd inf_le_right fun h =>
      not_three_dvd_card_R j (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
    (le_inf le_sup_left (V_le_centralizer _))

theorem R_inf_centralizer_snd
    (j : Fin 2) :
    R j ⊓ centralizer ({lineE (hexSnd j)} : Set G22) = V (hexSnd j) :=
  le_antisymm (le_V_of_not_dvd inf_le_right fun h =>
      not_three_dvd_card_R j (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
    (le_inf le_sup_right (V_le_centralizer _))

theorem stabilizer_le_normalizer {B : Finset (Fin 22)} :
    stabilizer NativeSporadic.M22 B ≤ normalizer (kernelSubgroup B : Set G22) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro n
  have hB : h⁻¹ • B = B := by
    have := inv_mem hh
    rwa [mem_stabilizer_iff] at this
  have key := mem_kernelSubgroup_smul (h := h⁻¹) (g := n) (B := B)
  rw [hB, inv_inv] at key
  exact key

theorem exists_kernel_move
    {B : Finset (Fin 22)} (hB : B ∈ hexads) {p : Fin 22} (hp : p ∉ B) :
    ∃ k ∈ kernelSubgroup B, (k : Perm (Fin 22)) p ≠ p := by
  have hcard : 2 ≤ (Bᶜ).card := by
    rw [Finset.card_compl, card_of_mem_hexads hB, Fintype.card_fin]
    norm_num
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ Bᶜ, q ≠ p := Finset.exists_mem_ne hcard p
  obtain ⟨k, ⟨hk, hkp⟩, -⟩ := kernelSubgroup_regular hB hp (Finset.mem_compl.1 hq)
  exact ⟨k, hk, hkp ▸ hqp⟩

theorem normalizer_R
    (j : Fin 2) :
    normalizer (R j : Set G22) = stabilizer NativeSporadic.M22 (hexad j) := by
  rw [R_eq_kernelSubgroup]
  refine le_antisymm ?_ stabilizer_le_normalizer
  intro g hg
  rw [mem_stabilizer_finset_iff]
  intro p hp
  by_contra hgp
  obtain ⟨k, hk, hkp⟩ := exists_kernel_move (hexad_mem j) hgp
  have hk' : g⁻¹ * k * g ∈ kernelSubgroup (hexad j) := by
    have := (mem_normalizer_iff.1 (inv_mem hg) k).1 hk
    rwa [inv_inv] at this
  have hfix := mem_kernelSubgroup.1 hk' p hp
  apply hkp
  have := congrArg (g : Perm (Fin 22)) hfix
  simpa using this

theorem P0_le_normalizer_R
    (j : Fin 2) : P0 ≤ normalizer (R j : Set G22) := by
  rw [normalizer_R]
  rw [closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_stabilizer_finset_iff] <;> intro p hp
  · exact (hex_inv j p hp).1
  · exact (hex_inv j p hp).2

theorem card_normalizer_R
    (j : Fin 2) : Nat.card (normalizer (R j : Set G22)) = 5760 := by
  rw [normalizer_R, card_stabilizer_hexad (hexad_mem j)]

theorem nonempty_normalizer_quotient_equiv
    (j : Fin 2) :
    Nonempty (normalizer (R j : Set G22) ⧸ (R j).subgroupOf (normalizer (R j : Set G22)) ≃*
      alternatingGroup (Fin 6)) := by
  set B := hexad j
  have hN := normalizer_R j
  have hker : (resHexad B).ker = (R j).subgroupOf (stabilizer NativeSporadic.M22 B) := by
    ext g
    rw [mem_ker_resHexad, mem_subgroupOf, R_eq_kernelSubgroup]
  let e₁ : normalizer (R j : Set G22) ≃* stabilizer NativeSporadic.M22 B :=
    MulEquiv.subgroupCongr hN
  have hmap : ((R j).subgroupOf (normalizer (R j : Set G22))).map e₁.toMonoidHom =
      (R j).subgroupOf (stabilizer NativeSporadic.M22 B) := by
    ext g
    simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hg
      exact ⟨e₁.symm g, hg, e₁.apply_symm_apply g⟩
  let e₂ := QuotientGroup.congr _ _ e₁ (hmap.trans hker.symm)
  exact ⟨e₂.trans ((QuotientGroup.quotientKerEquivRange (resHexad B)).trans
    ((MulEquiv.subgroupCongr (range_resHexad (hexad_mem j))).trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq (card_hexad_type (hexad_mem j))))))⟩

theorem mem_invariant_threePrime_iff {Q : Subgroup G22} :
    Q ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) ↔
      ¬ 3 ∣ Nat.card Q ∧ P0 ≤ normalizer (Q : Set G22) := by
  rw [mem_invariantPiSubgroups_iff, isPiSubgroup_piCompl_iff Nat.prime_three]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

theorem mem_invariant_two_iff {Q : Subgroup G22} :
    Q ∈ invariantPiSubgroups ⊤ P0 (piOf 2) ↔ IsPGroup 2 Q ∧ P0 ≤ normalizer (Q : Set G22) := by
  rw [mem_invariantPiSubgroups_iff, isPiSubgroup_piOf_iff Nat.prime_two]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

theorem R_mem_invariant_threePrime
    (j : Fin 2) :
    R j ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) :=
  mem_invariant_threePrime_iff.2 ⟨not_three_dvd_card_R j, P0_le_normalizer_R j⟩

theorem R_mem_invariant_two
    (j : Fin 2) : R j ∈ invariantPiSubgroups ⊤ P0 (piOf 2) :=
  mem_invariant_two_iff.2 ⟨isPGroup_R j, P0_le_normalizer_R j⟩

theorem not_pair_le_R
    (k : Fin 4) (j : Fin 2) : ¬ V (pairFst k) ⊔ V (pairSnd k) ≤ R j :=
  fun h => not_three_dvd_card_R j ((three_dvd_card_pair k).trans (Subgroup.card_dvd_of_le h))

theorem R_le_R
    {j j' : Fin 2} (h : R j ≤ R j') : j = j' := by
  fin_cases j <;> fin_cases j'
  · rfl
  · exact absurd (sup_le (le_sup_left.trans h) ((le_sup_left : V 2 ≤ R 1))) (not_pair_le_R 0 1)
  · exact absurd (sup_le ((le_sup_left : V 0 ≤ R 0)) (le_sup_left.trans h)) (not_pair_le_R 0 0)
  · rfl

theorem R_ne :
    R 0 ≠ R 1 := fun h => absurd (R_le_R h.le) (by decide)

theorem le_R_of_mem
    {Q : Subgroup G22} (hQ : Q ∈ invariantPiSubgroups ⊤ P0 (piCompl 3)) :
    ∃ j, Q ≤ R j := by
  obtain ⟨h3, hP⟩ := mem_invariant_threePrime_iff.1 hQ
  rcases le_R_cases h3 hP with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem isPGroup_of_mem_invariant
    {Q : Subgroup G22}
    (hQ : Q ∈ invariantPiSubgroups ⊤ P0 (piCompl 3)) : IsPGroup 2 Q := by
  obtain ⟨j, hj⟩ := le_R_of_mem hQ
  exact (isPGroup_R j).to_le hj

theorem maxInvariant_threePrime :
    maxInvariantPiSubgroups ⊤ P0 (piCompl 3) = {R 0, R 1} := by
  ext Q
  rw [mem_maxInvariantPiSubgroups_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hQ, hmax⟩
    obtain ⟨j, hj⟩ := le_R_of_mem hQ
    have := hmax _ (R_mem_invariant_threePrime j) hj
    fin_cases j
    · exact Or.inl this.symm
    · exact Or.inr this.symm
  · have key : ∀ j : Fin 2, Q = R j → Q ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) ∧
        ∀ Y ∈ invariantPiSubgroups ⊤ P0 (piCompl 3), Q ≤ Y → Y = Q := by
      rintro j rfl
      refine ⟨R_mem_invariant_threePrime j, fun Y hY hle => ?_⟩
      obtain ⟨j', hj'⟩ := le_R_of_mem hY
      have := R_le_R (hle.trans hj')
      subst this
      exact le_antisymm hj' hle
    rintro (h | h)
    · exact key 0 h
    · exact key 1 h

theorem maxInvariant_two :
    maxInvariantPiSubgroups ⊤ P0 (piOf 2) = {R 0, R 1} := by
  have hsub : ∀ {Q : Subgroup G22}, Q ∈ invariantPiSubgroups ⊤ P0 (piOf 2) →
      Q ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) := by
    intro Q hQ
    obtain ⟨h2, hP⟩ := mem_invariant_two_iff.1 hQ
    refine mem_invariant_threePrime_iff.2 ⟨fun h => ?_, hP⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    rw [hn] at h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  ext Q
  rw [mem_maxInvariantPiSubgroups_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hQ, hmax⟩
    obtain ⟨j, hj⟩ := le_R_of_mem (hsub hQ)
    have := hmax _ (R_mem_invariant_two j) hj
    fin_cases j
    · exact Or.inl this.symm
    · exact Or.inr this.symm
  · have key : ∀ j : Fin 2, Q = R j → Q ∈ invariantPiSubgroups ⊤ P0 (piOf 2) ∧
        ∀ Y ∈ invariantPiSubgroups ⊤ P0 (piOf 2), Q ≤ Y → Y = Q := by
      rintro j rfl
      refine ⟨R_mem_invariant_two j, fun Y hY hle => ?_⟩
      obtain ⟨j', hj'⟩ := le_R_of_mem (hsub hY)
      have := R_le_R (hle.trans hj')
      subst this
      exact le_antisymm hj' hle
    rintro (h | h)
    · exact key 0 h
    · exact key 1 h

theorem line_ne_facts : line 1 ≠ line 0 ∧ line 1 ≠ line 0 ^ 2 ∧ line 3 ≠ line 2 ∧
    line 3 ≠ line 2 ^ 2 := by
  decide +kernel

theorem lineE_ne_facts : lineE 1 ≠ lineE 0 ∧ lineE 1 ≠ lineE 0 ^ 2 ∧ lineE 3 ≠ lineE 2 ∧
    lineE 3 ≠ lineE 2 ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := line_ne_facts
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, fun h => h3 ?_, fun h => h4 ?_⟩ <;>
    have := congrArg Subtype.val h <;> simpa only [Subgroup.coe_pow, coe_lineE] using this

theorem hex_cases : ∀ j : Fin 2,
    (hexFst j = 0 ∧ hexSnd j = 1) ∨ (hexFst j = 2 ∧ hexSnd j = 3) := by
  decide

theorem closure_hex_eq (j : Fin 2) :
    closure ({lineE (hexFst j), lineE (hexSnd j)} : Set G22) = P0 := by
  have hle : closure ({lineE (hexFst j), lineE (hexSnd j)} : Set G22) ≤ P0 := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact lineE_mem_P0 _
    · exact lineE_mem_P0 _
  have hne : lineE (hexSnd j) ≠ lineE (hexFst j) ∧
      lineE (hexSnd j) ≠ lineE (hexFst j) ^ 2 := by
    obtain ⟨h1, h2, h3, h4⟩ := lineE_ne_facts
    rcases hex_cases j with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨h1, h2⟩
    · exact ⟨h3, h4⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_P0]
  exact (CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (lineE_cube _) (lineE_cube _)
    (P0_comm (lineE_mem_P0 _) (lineE_mem_P0 _)) (lineE_ne_one _)
    (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne (lineE_cube _) (lineE_ne_one _) hne.1
      hne.2)).ge

end CFSG.RankThree.PartTwo.KFacts.KP4
