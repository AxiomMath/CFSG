module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import Certificates.Certificate899101
public import Certificates.Certificate899102
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Sporadic.Suz.Simple
import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79

section Transport

variable {X X' : Type} [Group X] [Group X']

def TransvS (L : Subgroup X) (b₁ b₃ s : X) : Prop :=
  Nat.card ↥(L ⊓ Cen s) = 23040 ∧
    ∀ R : Subgroup X, R ≤ L ⊓ Cen s → IsPGroup 2 R → L ⊓ Cen s ≤ Nor R →
      R ≤ Subgroup.zpowers s ∨
        (Nat.card R = 32 ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ (∀ x ∈ R, x * x = 1) ∧
          Nat.card ↥(R ⊓ Cen b₁) = 8 ∧ Nat.card ↥(R ⊓ Cen b₃) = 8 ∧
          Nat.card ↥(R ⊓ Cen b₁ ⊓ Cen b₃) = 2 ∧ Nat.card ↥(R ⊓ Cen (b₁ * b₃)) = 2 ∧
          Nat.card ↥(R ⊓ Cen (b₁ * b₃⁻¹)) = 2 ∧ s ∈ ⁅R, L ⊓ Cen s⁆)

def TransvConcl (L : Subgroup X) (b₁ b₂ b₃ : X) : Prop :=
  Nat.card ↥(L ⊓ Cen b₂) = 2160 ∧
    (∀ x ∈ L, orderOf x = 3 → Nat.card ↥(L ⊓ Cen x) = 2160 → ∃ m ∈ L, m * x * m⁻¹ = b₂) ∧
    ∀ s ∈ L, orderOf s = 2 → s * b₁ = b₁ * s → s * b₃ = b₃ * s → s * b₂ * s⁻¹ = b₂⁻¹ →
      TransvS L b₁ b₃ s

theorem map_inf_cen {f : X →* X'} (hf : Function.Injective f) (R : Subgroup X) (b : X) :
    (R ⊓ Cen b).map f = R.map f ⊓ Cen (f b) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hxR, hxb⟩, rfl⟩
    exact ⟨⟨x, hxR, rfl⟩, by rw [← map_mul, ← map_mul, hxb]⟩
  · rintro ⟨⟨x, hxR, rfl⟩, hxb⟩
    exact ⟨x, ⟨hxR, hf (by rw [map_mul, map_mul]; exact hxb)⟩, rfl⟩

theorem card_map_inf_cen {f : X →* X'} (hf : Function.Injective f) (R : Subgroup X) (b : X) :
    Nat.card ↥(R.map f ⊓ Cen (f b)) = Nat.card ↥(R ⊓ Cen b) := by
  rw [← map_inf_cen hf, Subgroup.card_map_of_injective hf]

theorem TransvS.map {f : X →* X'} (hf : Function.Injective f) {L : Subgroup X} {b₁ b₃ s : X}
    (h : TransvS L b₁ b₃ s) : TransvS (L.map f) (f b₁) (f b₃) (f s) := by
  obtain ⟨hc, hR⟩ := h
  refine ⟨by rw [card_map_inf_cen hf, hc], fun R' hR'le hR'2 hR'n => ?_⟩
  have hle : R' ≤ (L ⊓ Cen s).map f := by rw [map_inf_cen hf]; exact hR'le
  have hRR : (R'.comap f).map f = R' :=
    Subgroup.map_comap_eq_self (hle.trans (Subgroup.map_le_range _ _))
  have hRle : R'.comap f ≤ L ⊓ Cen s := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_comap.mp hx)
    rwa [← hf hyx]
  have hR2 : IsPGroup 2 (R'.comap f) := hR'2.comap_of_injective f hf
  have hRn : L ⊓ Cen s ≤ Nor (R'.comap f) := by
    intro x hx
    refine Subgroup.le_normalizer_comap f (Subgroup.mem_comap.mpr (hR'n ?_))
    rw [← map_inf_cen hf]
    exact Subgroup.mem_map_of_mem f hx
  rcases hR _ hRle hR2 hRn with h1 | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · left
    rw [← hRR, ← MonoidHom.map_zpowers]
    exact Subgroup.map_mono h1
  · right
    set R := R'.comap f
    rw [← hRR]
    refine ⟨by rw [Subgroup.card_map_of_injective hf, h1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h2 x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, h3 x hx, map_one]
    · rw [card_map_inf_cen hf, h4]
    · rw [card_map_inf_cen hf, h5]
    · rw [← map_inf_cen hf, card_map_inf_cen hf, h6]
    · rw [← map_mul, card_map_inf_cen hf, h7]
    · rw [← map_inv, ← map_mul, card_map_inf_cen hf, h8]
    · rw [← map_inf_cen hf, ← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem f h9

theorem TransvConcl.map {f : X →* X'} (hf : Function.Injective f) {L : Subgroup X}
    {b₁ b₂ b₃ : X} (h : TransvConcl L b₁ b₂ b₃) : TransvConcl (L.map f) (f b₁) (f b₂) (f b₃) := by
  obtain ⟨hc, hx, hs⟩ := h
  refine ⟨by rw [card_map_inf_cen hf, hc], ?_, ?_⟩
  · rintro _ ⟨x, hxL, rfl⟩ hx3 hxc
    rw [orderOf_injective f hf] at hx3
    rw [card_map_inf_cen hf] at hxc
    obtain ⟨m, hmL, hm⟩ := hx x hxL hx3 hxc
    exact ⟨f m, Subgroup.mem_map_of_mem f hmL, by rw [← map_inv, ← map_mul, ← map_mul, hm]⟩
  · rintro _ ⟨s, hsL, rfl⟩ hs2 hs1 hs3 hs2'
    rw [orderOf_injective f hf] at hs2
    refine (hs s hsL hs2 (hf ?_) (hf ?_) (hf ?_)).map hf
    · rw [map_mul, map_mul, hs1]
    · rw [map_mul, map_mul, hs3]
    · rw [map_mul, map_mul, map_inv, map_inv, hs2']

end Transport

section Vectors

private def actE (ε : Fin 3 → ZMod 3) (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := fun i => ε i * v i

private def shiftV (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := ![v 2, v 0, v 1]

private def mono16 (k : Fin 16) (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  shiftV^[k.val / 8] ((actE ![2, 1, 1])^[k.val % 2] ((actE ![1, 2, 1])^[k.val / 2 % 2]
    ((actE ![1, 1, 2])^[k.val / 4 % 2] v)))

set_option maxRecDepth 10000 in
private theorem mono16_card : ∀ a b c : ZMod 3, (a ≠ 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ c ≠ 0) ∨ (b ≠ 0 ∧ c ≠ 0) →
    7 ≤ (Finset.univ.image fun k : Fin 16 => mono16 k ![a, b, c]).card := by
  decide

private def wv : Fin 7 → Fin 3 → ZMod 3 :=
  ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 2, 0], ![0, 0, 1], ![0, 0, 2]]

private def shiftL : Fin 7 → Fin 7 := ![0, 3, 4, 5, 6, 1, 2]

private def negL : Fin 7 → Fin 7 := ![0, 2, 1, 4, 3, 6, 5]

private def planeL : Fin 7 → Fin 3 := ![0, 0, 0, 1, 1, 2, 2]

private def coefL : Fin 7 → ZMod 3 := ![0, 1, 2, 1, 2, 1, 2]

private theorem wv_of_weight : ∀ a b c : ZMod 3,
    ¬((a ≠ 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ c ≠ 0) ∨ (b ≠ 0 ∧ c ≠ 0)) → ∃ k, ![a, b, c] = wv k := by
  decide

private theorem shiftV_wv : ∀ k, shiftV (wv k) = wv (shiftL k) := by
  decide

private theorem neg_wv : ∀ k, -wv k = wv (negL k) := by
  decide

private theorem wv_inj : ∀ k k', wv k = wv k' → k = k' := by
  decide

private theorem wv_eq_single : ∀ k, wv k = Pi.single (planeL k) (coefL k) := by
  decide

private theorem coefL_ne_zero : ∀ k, k ≠ 0 → coefL k ≠ 0 := by
  decide

private theorem labels_spec : ∀ k₁ k₂ k₃ : Fin 7,
    (∀ k ∈ [k₁, k₂, k₃], shiftL k ∈ [k₁, negL k₁, k₂, negL k₂, k₃, negL k₃]) →
    (k₁ ≠ 0 ∨ k₂ ≠ 0 ∨ k₃ ≠ 0) →
    k₁ ≠ 0 ∧ k₂ ≠ 0 ∧ k₃ ≠ 0 ∧ planeL k₁ ≠ planeL k₂ ∧ planeL k₁ ≠ planeL k₃ ∧
      planeL k₂ ≠ planeL k₃ := by
  decide

private theorem eta3 (v : Fin 3 → ZMod 3) : v = ![v 0, v 1, v 2] := by
  ext i; fin_cases i <;> rfl

private theorem iterate_mem {S : Finset (Fin 3 → ZMod 3)} {φ : (Fin 3 → ZMod 3) → Fin 3 → ZMod 3}
    (h : ∀ w ∈ S, φ w ∈ S) : ∀ n, ∀ w ∈ S, φ^[n] w ∈ S := by
  intro n
  induction n with
  | zero => exact fun w hw => hw
  | succ n ih =>
    intro w hw
    rw [Function.iterate_succ_apply']
    exact h _ (ih w hw)

end Vectors

section Facts

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit

theorem cert899101_facts : Sp6TransvFacts :=
  Certificates.certificate899101

private noncomputable def s0H : H6 :=
  Classical.choose cert899101_facts.1.1

private noncomputable def fl0H : H6 :=
  Classical.choose cert899101_facts.1.2.1

private noncomputable def fl2H : H6 :=
  Classical.choose cert899101_facts.1.2.2.1

private noncomputable def qH (i : Fin 5) : H6 :=
  Classical.choose (cert899101_facts.1.2.2.2 i)

private noncomputable def qSub : Subgroup H6 :=
  Subgroup.closure (Set.range qH)

private theorem at_spec : Sp6TransvAt zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH s0H fl0H fl2H qSub :=
  cert899101_facts.2 zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH s0H fl0H fl2H qH mat6_zH mat6_tH
    (Classical.choose_spec cert899101_facts.1.1) (Classical.choose_spec cert899101_facts.1.2.1)
    (Classical.choose_spec cert899101_facts.1.2.2.1)
    (fun i => Classical.choose_spec (cert899101_facts.1.2.2.2 i))

private theorem s0H_mul_self : s0H * s0H = 1 := at_spec.1.1

private theorem s0H_ne_one : s0H ≠ 1 := at_spec.1.2.1

private theorem s0H_comm_z0 : s0H * zH 0 = zH 0 * s0H := at_spec.1.2.2.1

private theorem s0H_comm_z2 : s0H * zH 2 = zH 2 * s0H := at_spec.1.2.2.2.1

private theorem s0H_conj_z1 : s0H * zH 1 * s0H⁻¹ = (zH 1)⁻¹ := at_spec.1.2.2.2.2.1

private theorem fl0H_mul_self : fl0H * fl0H = 1 := at_spec.1.2.2.2.2.2.1

private theorem fl0H_conj_z0 : fl0H * zH 0 * fl0H⁻¹ = (zH 0)⁻¹ := at_spec.1.2.2.2.2.2.2.1

private theorem fl0H_comm_z1 : fl0H * zH 1 = zH 1 * fl0H := at_spec.1.2.2.2.2.2.2.2.1

private theorem fl0H_comm_z2 : fl0H * zH 2 = zH 2 * fl0H := at_spec.1.2.2.2.2.2.2.2.2.1

private theorem fl2H_mul_self : fl2H * fl2H = 1 := at_spec.1.2.2.2.2.2.2.2.2.2.1

private theorem fl2H_conj_z2 : fl2H * zH 2 * fl2H⁻¹ = (zH 2)⁻¹ :=
  at_spec.1.2.2.2.2.2.2.2.2.2.2.1

private theorem fl2H_comm_z0 : fl2H * zH 0 = zH 0 * fl2H := at_spec.1.2.2.2.2.2.2.2.2.2.2.2.1

private theorem fl2H_comm_z1 : fl2H * zH 1 = zH 1 * fl2H := at_spec.1.2.2.2.2.2.2.2.2.2.2.2.2

private theorem s0H_inv : s0H⁻¹ = s0H := inv_eq_of_mul_eq_one_right s0H_mul_self

private theorem fl0H_inv : fl0H⁻¹ = fl0H := inv_eq_of_mul_eq_one_right fl0H_mul_self

private theorem fl2H_inv : fl2H⁻¹ = fl2H := inv_eq_of_mul_eq_one_right fl2H_mul_self

private theorem orderOf_s0H : orderOf s0H = 2 :=
  orderOf_eq_prime (by rw [sq, s0H_mul_self]) s0H_ne_one

private theorem card_cen_s0H : Nat.card (Subgroup.centralizer {s0H}) = 23040 := at_spec.2.1

private theorem normal_cases {R : Subgroup H6} (hR : R ≤ Subgroup.centralizer {s0H})
    (h2 : IsPGroup 2 R) (hN : Subgroup.centralizer {s0H} ≤ Subgroup.normalizer (R : Set H6)) :
    R ≤ Subgroup.zpowers s0H ∨ R = qSub :=
  at_spec.2.2.1 R hR h2 hN

private theorem card_qSub : Nat.card qSub = 32 := at_spec.2.2.2.2.1

private theorem qSub_comm : ∀ x ∈ qSub, ∀ y ∈ qSub, x * y = y * x := at_spec.2.2.2.2.2.1

private theorem qSub_sq : ∀ x ∈ qSub, x * x = 1 := at_spec.2.2.2.2.2.2.1

private theorem card_q_z0 : Nat.card ↥(qSub ⊓ Cen (zH 0)) = 8 := at_spec.2.2.2.2.2.2.2.1

private theorem card_q_z2 : Nat.card ↥(qSub ⊓ Cen (zH 2)) = 8 := at_spec.2.2.2.2.2.2.2.2.1

private theorem card_q_z0z2 : Nat.card ↥(qSub ⊓ Cen (zH 0) ⊓ Cen (zH 2)) = 2 :=
  at_spec.2.2.2.2.2.2.2.2.2.1

private theorem card_q_z0mz2 : Nat.card ↥(qSub ⊓ Cen (zH 0 * zH 2)) = 2 :=
  at_spec.2.2.2.2.2.2.2.2.2.2.1

private theorem card_q_z0mz2i : Nat.card ↥(qSub ⊓ Cen (zH 0 * zH 2 ^ 2)) = 2 :=
  at_spec.2.2.2.2.2.2.2.2.2.2.2.1

private theorem s0H_mem_commutator : s0H ∈ ⁅qSub, Subgroup.centralizer {s0H}⁆ :=
  at_spec.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem s_cases {s : H6} (h0 : s * zH 0 = zH 0 * s) (h2 : s * zH 2 = zH 2 * s)
    (hss : s * s = 1) (hne : s ≠ 1) (hinv : s * zH 1 * s⁻¹ = (zH 1)⁻¹) :
    s = s0H ∨ s = zH 1 * s0H * (zH 1)⁻¹ ∨ s = (zH 1)⁻¹ * s0H * zH 1 :=
  at_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s h0 h2 hss hne hinv

private theorem vecElt_111 : vecElt zH ![1, 1, 1] = zH 0 * zH 1 * zH 2 := by
  change zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 1 = _
  rw [pow_one, pow_one, pow_one]

private theorem aElt_three : aElt 3 = zH 0 * zH 1 := by
  change zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 0 = _
  rw [pow_zero, pow_one, pow_one, mul_one]

theorem conj_rep_of_wreath {v : Fin 3 → ZMod 3} {j : Fin 3}
    (h3 : (vecElt zH v * Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) ^ 3 = 1) (h1 : vecElt zH v * Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) ≠ 1) :
    (∃ g : H6, vecElt zH v * Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) = g * zH 1 * g⁻¹) ∨
      (∃ g : H6, vecElt zH v * Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) = g * (zH 0 * zH 1) * g⁻¹) ∨
      ∃ g : H6, vecElt zH v * Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) = g * vecElt zH ![1, 1, 1] * g⁻¹ := by
  rw [vecElt_111]
  exact at_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _
    (ZMod.val_lt (v 2)) _ j.2 h3 h1

private theorem order_three_wreath {v : Fin 3 → ZMod 3} {j : Fin 3}
    (h : orderOf (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) = 3) :
    (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) ^ 3 = 1 ∧ vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) ≠ 1 := by
  have h3 := pow_orderOf_eq_one (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
  rw [h] at h3
  refine ⟨h3, fun e => ?_⟩
  rw [e, orderOf_one] at h
  exact absurd h (by norm_num)

private theorem aElt_zero : aElt 0 = zH 0 := by
  simp only [aElt, aVec, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, mul_one, mul_one]

theorem card_cen_conj (g x : H6) :
    Nat.card (Subgroup.centralizer {g * x * g⁻¹}) = Nat.card (Subgroup.centralizer {x}) := by
  have e : Subgroup.centralizer {g * x * g⁻¹} =
      (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
    constructor
    · intro h
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
        _ = x * (g⁻¹ * y * g) := by group
    · intro h
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * y := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem wreathW_le_cen :
    wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ≤ Subgroup.centralizer {vecElt zH ![1, 1, 1]} := by
  have hz : ∀ i, zH i ∈ Subgroup.centralizer {vecElt zH ![1, 1, 1]} := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := vecElt_add wreathFacts_zH (Pi.single i 1) ![1, 1, 1]
    rw [add_comm, vecElt_add wreathFacts_zH, vecElt_single_one] at h
    exact h.symm
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact (Subgroup.zpowers_le).mpr (hz 0)
  · exact (Subgroup.zpowers_le).mpr (hz 1)
  · exact (Subgroup.zpowers_le).mpr (hz 2)
  · refine (Subgroup.zpowers_le).mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := conj_vecElt wreathFacts_zH ![1, 1, 1]
    have e : (![(![1, 1, 1] : Fin 3 → ZMod 3) 2, (![1, 1, 1] : Fin 3 → ZMod 3) 0,
        (![1, 1, 1] : Fin 3 → ZMod 3) 1] : Fin 3 → ZMod 3) = ![1, 1, 1] := by
      ext i; fin_cases i <;> rfl
    rw [e] at h
    calc CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * vecElt zH ![1, 1, 1] = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * vecElt zH ![1, 1, 1] * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := by group
      _ = vecElt zH ![1, 1, 1] * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := by rw [h]

theorem conj_z1_of_card {x : H6} (hx : orderOf x = 3)
    (hc : Nat.card (Subgroup.centralizer {x}) = 2160) : ∃ m : H6, m * x * m⁻¹ = zH 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hp
  obtain ⟨w, hw, hgw⟩ := hg (Subgroup.mem_zpowers x)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgw
  have hcw : Nat.card (Subgroup.centralizer {w}) = 2160 := by rw [← card_cen_conj g w, hgw, hc]
  obtain ⟨v, j, rfl⟩ := mem_wreathW wreathFacts_zH hw
  have hw3 : orderOf (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) = 3 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgw, hx] at h
    exact h.symm
  obtain ⟨h3, h1⟩ := order_three_wreath hw3
  rcases conj_rep_of_wreath h3 h1 with ⟨h, hh⟩ | ⟨h, hh⟩ | ⟨h, hh⟩
  · refine ⟨(g * h)⁻¹, ?_⟩
    rw [← hgw, hh]
    group
  · exfalso
    rw [hh, card_cen_conj, ← aElt_three, ← centSub_eq, card_centSub] at hcw
    exact absurd hcw (by decide)
  · exfalso
    rw [hh, card_cen_conj] at hcw
    have hdvd := Subgroup.card_dvd_of_le wreathW_le_cen
    rw [card_wreathW_zH, hcw] at hdvd
    exact absurd hdvd (by decide)

private theorem val_eq_one_or_two {a : ZMod 3} (ha : a ≠ 0) : a.val = 1 ∨ a.val = 2 := by
  fin_cases a
  · exact absurd rfl ha
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem inv_eq_sq_zH (i : Fin 3) : (zH i)⁻¹ = zH i ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact zH_pow_three i)

private theorem conj_z1_of_single (p : Fin 3) {a : ZMod 3} (ha : a ≠ 0) :
    ∃ h : H6, zH p ^ a.val = h * zH 1 * h⁻¹ := by
  rcases val_eq_one_or_two ha with h | h <;> rw [h]
  · rw [pow_one]
    exact (at_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p).1
  · rw [← inv_eq_sq_zH]
    exact (at_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p).2

private theorem pow_val_mul_of {x : H6} (hx : x ^ 3 = 1) (a b : ZMod 3) :
    (x ^ a.val) ^ b.val = x ^ (a * b).val := by
  rw [← pow_mul, ZMod.val_mul]
  conv_lhs => rw [← Nat.mod_add_div (a.val * b.val) 3, pow_add, pow_mul, hx, one_pow, mul_one]

private theorem conj_vecElt_of {n : H6} (ε : Fin 3 → ZMod 3)
    (hn : ∀ i, n * zH i * n⁻¹ = zH i ^ (ε i).val) (v : Fin 3 → ZMod 3) :
    n * vecElt zH v * n⁻¹ = vecElt zH (actE ε v) := by
  have hc : ∀ y : H6, n * y * n⁻¹ = MulAut.conj n y := fun y => rfl
  rw [hc, vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc, ← hc, ← hc, hn 0, hn 1,
    hn 2, pow_val_mul_of (zH_pow_three 0), pow_val_mul_of (zH_pow_three 1),
    pow_val_mul_of (zH_pow_three 2), vecElt]
  rfl

private theorem conj_of_comm {n z : H6} (h : n * z = z * n) : n * z * n⁻¹ = z := by
  rw [h, mul_inv_cancel_right]

private theorem fl0H_conj : ∀ i, fl0H * zH i * fl0H⁻¹ = zH i ^ ((![2, 1, 1] : Fin 3 → ZMod 3) i).val := by
  intro i
  fin_cases i
  · show fl0H * zH 0 * fl0H⁻¹ = zH 0 ^ 2
    rw [fl0H_conj_z0, inv_eq_sq_zH]
  · show fl0H * zH 1 * fl0H⁻¹ = zH 1 ^ 1
    rw [pow_one]
    exact conj_of_comm fl0H_comm_z1
  · show fl0H * zH 2 * fl0H⁻¹ = zH 2 ^ 1
    rw [pow_one]
    exact conj_of_comm fl0H_comm_z2

private theorem fl2H_conj : ∀ i, fl2H * zH i * fl2H⁻¹ = zH i ^ ((![1, 1, 2] : Fin 3 → ZMod 3) i).val := by
  intro i
  fin_cases i
  · show fl2H * zH 0 * fl2H⁻¹ = zH 0 ^ 1
    rw [pow_one]
    exact conj_of_comm fl2H_comm_z0
  · show fl2H * zH 1 * fl2H⁻¹ = zH 1 ^ 1
    rw [pow_one]
    exact conj_of_comm fl2H_comm_z1
  · show fl2H * zH 2 * fl2H⁻¹ = zH 2 ^ 2
    rw [fl2H_conj_z2, inv_eq_sq_zH]

private theorem s0H_conj : ∀ i, s0H * zH i * s0H⁻¹ = zH i ^ ((![1, 2, 1] : Fin 3 → ZMod 3) i).val := by
  intro i
  fin_cases i
  · show s0H * zH 0 * s0H⁻¹ = zH 0 ^ 1
    rw [pow_one]
    exact conj_of_comm s0H_comm_z0
  · show s0H * zH 1 * s0H⁻¹ = zH 1 ^ 2
    rw [s0H_conj_z1]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact zH_pow_three 1)
  · show s0H * zH 2 * s0H⁻¹ = zH 2 ^ 1
    rw [pow_one]
    exact conj_of_comm s0H_comm_z2

private theorem mem_normalizer_of_act {n : H6} (hn : n⁻¹ = n) {φ : (Fin 3 → ZMod 3) → Fin 3 → ZMod 3}
    (h : ∀ v, n * vecElt zH v * n⁻¹ = vecElt zH (φ v)) :
    n ∈ Subgroup.normalizer (baseA zH : Set H6) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hmap : ∀ y ∈ baseA zH, n * y * n⁻¹ ∈ baseA zH := by
    intro y hy
    obtain ⟨v, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp hy
    rw [h]
    exact vecElt_mem_baseA wreathFacts_zH _
  have hnn : n * n = 1 := by
    calc n * n = n * n⁻¹ := by rw [hn]
      _ = 1 := mul_inv_cancel n
  refine ⟨hmap x, fun hx => ?_⟩
  have := hmap _ hx
  rwa [hn, show n * (n * x * n) * n = (n * n) * x * (n * n) by group, hnn, one_mul,
    mul_one] at this

private theorem vecElt_neg (v : Fin 3 → ZMod 3) : (vecElt zH v)⁻¹ = vecElt zH (-v) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← vecElt_add wreathFacts_zH, show v + -v = 0 from add_neg_cancel v]
  simp [vecElt]

private theorem shape {d₁ d₂ d₃ : H6} (hcl : Subgroup.closure {d₁, d₂, d₃} = baseA zH)
    (hmono : ∀ n ∈ Subgroup.normalizer (baseA zH : Set H6), ∀ x ∈ ({d₁, d₂, d₃} : Set H6),
      n * x * n⁻¹ ∈ ({d₁, d₁⁻¹, d₂, d₂⁻¹, d₃, d₃⁻¹} : Set H6)) :
    ∃ (p₁ p₂ p₃ : Fin 3) (a₁ a₂ a₃ : ZMod 3), p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      a₃ ≠ 0 ∧ d₁ = zH p₁ ^ a₁.val ∧ d₂ = zH p₂ ^ a₂.val ∧ d₃ = zH p₃ ^ a₃.val := by
  classical
  have hmem : ∀ x ∈ ({d₁, d₂, d₃} : Set H6), x ∈ baseA zH := fun x hx =>
    hcl ▸ Subgroup.subset_closure hx
  obtain ⟨v₁, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp (hmem d₁ (by simp))
  obtain ⟨v₂, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp (hmem d₂ (by simp))
  obtain ⟨v₃, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp (hmem d₃ (by simp))
  set S : Finset (Fin 3 → ZMod 3) := {v₁, -v₁, v₂, -v₂, v₃, -v₃} with hS
  have hSneg : ∀ w ∈ S, -w ∈ S := by
    intro w hw
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> rw [h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (neg_neg v₁)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl (neg_neg v₂)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (neg_neg v₃)))))
  have hmemS : ∀ u, vecElt zH u ∈ ({vecElt zH v₁, (vecElt zH v₁)⁻¹, vecElt zH v₂,
      (vecElt zH v₂)⁻¹, vecElt zH v₃, (vecElt zH v₃)⁻¹} : Set H6) → u ∈ S := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, vecElt_neg] at hu
    simp only [hS, Finset.mem_insert, Finset.mem_singleton]
    rcases hu with h | h | h | h | h | h <;>
      simp only [vecElt_injective wreathFacts_zH h, true_or, or_true]
  have hinv : ∀ (n : H6) (φ : (Fin 3 → ZMod 3) → Fin 3 → ZMod 3),
      n ∈ Subgroup.normalizer (baseA zH : Set H6) →
      (∀ v, n * vecElt zH v * n⁻¹ = vecElt zH (φ v)) → (∀ v, φ (-v) = -φ v) →
      ∀ w ∈ S, φ w ∈ S := by
    intro n φ hn hφ hneg
    have key : ∀ v ∈ [v₁, v₂, v₃], φ v ∈ S := by
      intro v hv
      refine hmemS _ ?_
      rw [← hφ]
      apply hmono n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> simp
    intro w hw
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact key _ (by simp)
    · rw [hneg]; exact hSneg _ (key _ (by simp))
    · exact key _ (by simp)
    · rw [hneg]; exact hSneg _ (key _ (by simp))
    · exact key _ (by simp)
    · rw [hneg]; exact hSneg _ (key _ (by simp))
  have hnegE : ∀ ε : Fin 3 → ZMod 3, ∀ v, actE ε (-v) = -actE ε v := fun ε v =>
    funext fun i => mul_neg (ε i) (v i)
  have h0 := hinv fl0H (actE ![2, 1, 1])
    (mem_normalizer_of_act fl0H_inv (conj_vecElt_of _ fl0H_conj))
    (conj_vecElt_of _ fl0H_conj) (hnegE _)
  have h1 := hinv s0H (actE ![1, 2, 1]) (mem_normalizer_of_act s0H_inv (conj_vecElt_of _ s0H_conj))
    (conj_vecElt_of _ s0H_conj) (hnegE _)
  have h2 := hinv fl2H (actE ![1, 1, 2])
    (mem_normalizer_of_act fl2H_inv (conj_vecElt_of _ fl2H_conj))
    (conj_vecElt_of _ fl2H_conj) (hnegE _)
  have ht := hinv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH shiftV (t_mem_normalizer wreathFacts_zH) (conj_vecElt wreathFacts_zH)
    (fun v => by ext i; fin_cases i <;> rfl)
  have hweight : ∀ v ∈ S, ∃ k, v = wv k := by
    intro v hv
    have hsub : (Finset.univ.image fun k : Fin 16 => mono16 k v) ⊆ S := by
      intro w hw
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
      exact iterate_mem ht _ _ (iterate_mem h0 _ _ (iterate_mem h1 _ _ (iterate_mem h2 _ _ hv)))
    have hle := (Finset.card_le_card hsub).trans Finset.card_le_six
    rw [eta3 v] at hle ⊢
    by_contra hne
    have hw : (v 0 ≠ 0 ∧ v 1 ≠ 0) ∨ (v 0 ≠ 0 ∧ v 2 ≠ 0) ∨ (v 1 ≠ 0 ∧ v 2 ≠ 0) := by
      by_contra hw
      exact hne (wv_of_weight _ _ _ hw)
    have := mono16_card _ _ _ hw
    omega
  obtain ⟨k₁, hk₁⟩ := hweight v₁ (by simp [hS])
  obtain ⟨k₂, hk₂⟩ := hweight v₂ (by simp [hS])
  obtain ⟨k₃, hk₃⟩ := hweight v₃ (by simp [hS])
  subst hk₁ hk₂ hk₃
  have hlab : ∀ k ∈ [k₁, k₂, k₃], shiftL k ∈ [k₁, negL k₁, k₂, negL k₂, k₃, negL k₃] := by
    intro k hk
    have hk' : wv k ∈ S := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [hS]
    have hs := ht _ hk'
    rw [shiftV_wv] at hs
    simp only [hS, Finset.mem_insert, Finset.mem_singleton, neg_wv] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hs with h | h | h | h | h | h <;> simp only [wv_inj _ _ h, true_or, or_true]
  have hnz : k₁ ≠ 0 ∨ k₂ ≠ 0 ∨ k₃ ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hone : vecElt zH (wv 0) = 1 := by simp [wv, vecElt]
    have hcard := card_baseA wreathFacts_zH
    rw [← hcl, hone, Set.insert_eq_of_mem (Set.mem_singleton _), Set.pair_eq_singleton,
      Subgroup.closure_singleton_one, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨n₁, n₂, n₃, p12, p13, p23⟩ := labels_spec k₁ k₂ k₃ hlab hnz
  refine ⟨planeL k₁, planeL k₂, planeL k₃, coefL k₁, coefL k₂, coefL k₃, p12, p13, p23,
    coefL_ne_zero _ n₁, coefL_ne_zero _ n₂, coefL_ne_zero _ n₃, ?_, ?_, ?_⟩ <;>
    rw [wv_eq_single, vecElt_single]

private theorem cen_sq {z : H6} (hz : z ^ 3 = 1) : Cen (z ^ 2) = Cen z := by
  have h4 : (z ^ 2) ^ 2 = z := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hz, one_mul]
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h := (show Commute g (z ^ 2) from hg).pow_right 2
    rw [h4] at h
    exact h
  · intro hg
    exact (show Commute g z from hg).pow_right 2

private theorem cen_pow_val {z : H6} (hz : z ^ 3 = 1) {a : ZMod 3} (ha : a ≠ 0) :
    Cen (z ^ a.val) = Cen z := by
  rcases val_eq_one_or_two ha with h | h <;> rw [h]
  · rw [pow_one]
  · exact cen_sq hz

private theorem inv_pow_val {z : H6} (hz : z ^ 3 = 1) (a : ZMod 3) :
    (z ^ a.val)⁻¹ = z ^ (-a).val := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_val_add hz, show a + -a = 0 from add_neg_cancel a, ZMod.val_zero, pow_zero]

private theorem comm_of_comm_pow {s z : H6} (hz : z ^ 3 = 1) {a : ZMod 3} (ha : a ≠ 0)
    (h : s * z ^ a.val = z ^ a.val * s) : s * z = z * s := by
  have h' : s ∈ Cen (z ^ a.val) := Subgroup.mem_centralizer_singleton_iff.mpr h
  rw [cen_pow_val hz ha, Subgroup.mem_centralizer_singleton_iff] at h'
  exact h'

private theorem inv_of_inv_pow {s z : H6} (hz : z ^ 3 = 1) {a : ZMod 3} (ha : a ≠ 0)
    (h : s * z ^ a.val * s⁻¹ = (z ^ a.val)⁻¹) : s * z * s⁻¹ = z⁻¹ := by
  have hc : ∀ y : H6, s * y * s⁻¹ = MulAut.conj s y := fun y => rfl
  rcases val_eq_one_or_two ha with h1 | h1 <;> rw [h1] at h
  · simpa only [pow_one] using h
  · rw [hc, map_pow, ← hc] at h
    have hy : (s * z * s⁻¹) ^ 3 = 1 := by
      rw [hc, ← map_pow, hz, map_one]
    have hw : (z⁻¹) ^ 3 = 1 := by rw [inv_pow, hz, inv_one]
    have e4 : ∀ y : H6, y ^ 3 = 1 → (y ^ 2) ^ 2 = y := fun y hy' => by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hy', one_mul]
    rw [← e4 _ hy, h, ← inv_pow, e4 _ hw]

private theorem card_q_prod {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card ↥(qSub ⊓ Cen (zH 0 ^ a.val * zH 2 ^ b.val)) = 2 := by
  have hc02 : Commute (zH 0) (zH 2) := zH_comm 0 2
  have h4 : zH 2 ^ (2 * 2) = zH 2 := by
    rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, zH_pow_three, one_mul]
  have hcube : ∀ x y : H6, Commute x y → x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1 :=
    fun x y hxy hx hy => by rw [hxy.mul_pow, hx, hy, one_mul]
  rcases val_eq_one_or_two ha with h1 | h1 <;> rcases val_eq_one_or_two hb with h2 | h2 <;>
    rw [h1, h2]
  · rw [pow_one, pow_one]
    exact card_q_z0mz2
  · rw [pow_one]
    exact card_q_z0mz2i
  · have e : zH 0 ^ 2 * zH 2 ^ 1 = (zH 0 * zH 2 ^ 2) ^ 2 := by
      rw [(hc02.pow_right 2).mul_pow, ← pow_mul, h4, pow_one]
    rw [e, cen_sq (hcube _ _ (hc02.pow_right 2) (zH_pow_three 0)
      (by rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, zH_pow_three, one_pow]))]
    exact card_q_z0mz2i
  · have e : zH 0 ^ 2 * zH 2 ^ 2 = (zH 0 * zH 2) ^ 2 := by rw [hc02.mul_pow]
    rw [e, cen_sq (hcube _ _ hc02 (zH_pow_three 0) (zH_pow_three 2))]
    exact card_q_z0mz2

private theorem transvS_s0 {q₁ q₃ : Fin 3} (hq : (q₁ = 0 ∧ q₃ = 2) ∨ (q₁ = 2 ∧ q₃ = 0))
    {a₁ a₃ : ZMod 3} (ha₁ : a₁ ≠ 0) (ha₃ : a₃ ≠ 0) :
    TransvS (⊤ : Subgroup H6) (zH q₁ ^ a₁.val) (zH q₃ ^ a₃.val) s0H := by
  refine ⟨by rw [top_inf_eq, card_cen_s0H], fun R hR h2 hN => ?_⟩
  rw [top_inf_eq] at hR hN
  rcases normal_cases hR h2 hN with h | rfl
  · exact Or.inl h
  · right
    have hn3 : -a₃ ≠ 0 := neg_ne_zero.mpr ha₃
    rw [top_inf_eq, cen_pow_val (zH_pow_three _) ha₁, cen_pow_val (zH_pow_three _) ha₃,
      inv_pow_val (zH_pow_three _)]
    refine ⟨card_qSub, qSub_comm, qSub_sq, ?_, ?_, ?_, ?_, ?_, s0H_mem_commutator⟩
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact card_q_z0
      · exact card_q_z2
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact card_q_z2
      · exact card_q_z0
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact card_q_z0z2
      · rw [inf_right_comm]
        exact card_q_z0z2
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact card_q_prod ha₁ ha₃
      · rw [((show Commute (zH 2) (zH 0) from zH_comm 2 0).pow_pow _ _).eq]
        exact card_q_prod ha₃ ha₁
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact card_q_prod ha₁ hn3
      · rw [((show Commute (zH 2) (zH 0) from zH_comm 2 0).pow_pow _ _).eq]
        exact card_q_prod hn3 ha₁

private theorem conj_tpow (μ p : Fin 3) : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ μ.val * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ μ.val)⁻¹ = zH (p + μ) := by
  fin_cases μ
  · simp
  · show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 1 * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 1)⁻¹ = zH (p + 1)
    rw [pow_one, tH_conj]
  · show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2 * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2)⁻¹ = zH (p + 2)
    rw [sq, mul_inv_rev, show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹) = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * zH p * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹) * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ by
      group, tH_conj, tH_conj, add_assoc]
    rfl

private theorem aElt_one : aElt 1 = zH 1 := by
  simp only [aElt, aVec, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, one_mul, mul_one]

private theorem aElt_two : aElt 2 = zH 2 := by
  simp only [aElt, aVec, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, one_mul, one_mul]

private theorem card_cen_zH (p : Fin 3) : Nat.card (Subgroup.centralizer {zH p}) = 2160 := by
  fin_cases p
  · show Nat.card (Subgroup.centralizer {zH 0}) = 2160
    rw [← aElt_zero, ← centSub_eq, card_centSub]; rfl
  · show Nat.card (Subgroup.centralizer {zH 1}) = 2160
    rw [← aElt_one, ← centSub_eq, card_centSub]; rfl
  · show Nat.card (Subgroup.centralizer {zH 2}) = 2160
    rw [← aElt_two, ← centSub_eq, card_centSub]; rfl

private theorem transvS_of_conj (g : H6) {x y s : H6}
    (h : TransvS (⊤ : Subgroup H6) (g * x * g⁻¹) (g * y * g⁻¹) (g * s * g⁻¹)) :
    TransvS (⊤ : Subgroup H6) x y s := by
  have hm := h.map (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at hm
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hm
  convert hm using 1 <;> group

private theorem planes_02 : ∀ q₁ q₃ : Fin 3, q₁ ≠ 1 → q₃ ≠ 1 → q₁ ≠ q₃ →
    (q₁ = 0 ∧ q₃ = 2) ∨ (q₁ = 2 ∧ q₃ = 0) := by
  decide

private theorem transvS_of_basis {p₁ p₂ p₃ : Fin 3} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃)
    (h23 : p₂ ≠ p₃) {a₁ a₂ a₃ : ZMod 3} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0) {s : H6}
    (hs2 : orderOf s = 2) (hs1 : s * zH p₁ ^ a₁.val = zH p₁ ^ a₁.val * s)
    (hs3 : s * zH p₃ ^ a₃.val = zH p₃ ^ a₃.val * s)
    (hs2' : s * zH p₂ ^ a₂.val * s⁻¹ = (zH p₂ ^ a₂.val)⁻¹) :
    TransvS (⊤ : Subgroup H6) (zH p₁ ^ a₁.val) (zH p₃ ^ a₃.val) s := by
  have c1 := comm_of_comm_pow (zH_pow_three _) ha₁ hs1
  have c3 := comm_of_comm_pow (zH_pow_three _) ha₃ hs3
  have i2 := inv_of_inv_pow (zH_pow_three _) ha₂ hs2'
  set μ : Fin 3 := 1 - p₂ with hμ
  set τ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ μ.val with hτ
  have hτz : ∀ p, τ * zH p * τ⁻¹ = zH (p + μ) := fun p => conj_tpow μ p
  have hc : ∀ (g y : H6), g * y * g⁻¹ = MulAut.conj g y := fun g y => rfl
  have hconj_comm : ∀ (g a b : H6), a * b = b * a → (g * a * g⁻¹) * (g * b * g⁻¹) =
      (g * b * g⁻¹) * (g * a * g⁻¹) := fun g a b h => by
    rw [hc, hc, ← map_mul, ← map_mul, h]
  set s' := τ * s * τ⁻¹ with hs'
  have q2 : p₂ + μ = 1 := by rw [hμ]; abel
  have q1 : p₁ + μ ≠ 1 := by
    rw [← q2]; exact fun h => h12 (add_right_cancel h)
  have q3 : p₃ + μ ≠ 1 := by
    rw [← q2]; exact fun h => h23 (add_right_cancel h).symm
  have q13 : p₁ + μ ≠ p₃ + μ := fun h => h13 (add_right_cancel h)
  have s'1 : s' * zH (p₁ + μ) = zH (p₁ + μ) * s' := by
    rw [← hτz, hs']; exact hconj_comm τ s (zH p₁) c1
  have s'3 : s' * zH (p₃ + μ) = zH (p₃ + μ) * s' := by
    rw [← hτz, hs']; exact hconj_comm τ s (zH p₃) c3
  have s'2 : s' * zH 1 * s'⁻¹ = (zH 1)⁻¹ := by
    rw [← q2, ← hτz, hs', show τ * s * τ⁻¹ * (τ * zH p₂ * τ⁻¹) * (τ * s * τ⁻¹)⁻¹ =
      τ * (s * zH p₂ * s⁻¹) * τ⁻¹ by group, i2]
    group
  have s'0 : s' * zH 0 = zH 0 * s' ∧ s' * zH 2 = zH 2 * s' := by
    rcases planes_02 _ _ q1 q3 q13 with ⟨e1, e3⟩ | ⟨e1, e3⟩
    · rw [e1] at s'1; rw [e3] at s'3; exact ⟨s'1, s'3⟩
    · rw [e1] at s'1; rw [e3] at s'3; exact ⟨s'3, s'1⟩
  have hs'2 : orderOf s' = 2 := by
    have h := orderOf_injective (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective s
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [hs', h, hs2]
  have hss : s' * s' = 1 := by
    have h := pow_orderOf_eq_one s'
    rwa [hs'2, sq] at h
  have hne : s' ≠ 1 := fun h => by rw [h, orderOf_one] at hs'2; exact absurd hs'2 (by norm_num)
  obtain ⟨ρ, hρ, hρz⟩ : ∃ ρ : H6, ρ * s' * ρ⁻¹ = s0H ∧ ∀ i, ρ * zH i * ρ⁻¹ = zH i := by
    have hz1 : ∀ i, zH 1 * zH i * (zH 1)⁻¹ = zH i := fun i => by
      rw [zH_comm 1 i, mul_inv_cancel_right]
    have hz1' : ∀ i, (zH 1)⁻¹ * zH i * (zH 1)⁻¹⁻¹ = zH i := fun i => by
      rw [inv_inv, mul_assoc, zH_comm i 1, ← mul_assoc, inv_mul_cancel, one_mul]
    rcases s_cases s'0.1 s'0.2 hss hne s'2 with e | e | e
    · exact ⟨1, by rw [e]; group, fun i => by group⟩
    · exact ⟨(zH 1)⁻¹, by rw [e]; group, hz1'⟩
    · exact ⟨zH 1, by rw [e]; group, hz1⟩
  set h := ρ * τ with hh
  have hhz : ∀ p (a : ZMod 3), h * zH p ^ a.val * h⁻¹ = zH (p + μ) ^ a.val := by
    intro p a
    rw [hc, map_pow, ← hc, hh, mul_inv_rev,
      show ρ * τ * zH p * (τ⁻¹ * ρ⁻¹) = ρ * (τ * zH p * τ⁻¹) * ρ⁻¹ by group, hτz, hρz]
  refine transvS_of_conj h ?_
  rw [hhz, hhz, show h * s * h⁻¹ = s0H by rw [hh, mul_inv_rev,
    show ρ * τ * s * (τ⁻¹ * ρ⁻¹) = ρ * (τ * s * τ⁻¹) * ρ⁻¹ by group, ← hs', hρ]]
  exact transvS_s0 (planes_02 _ _ q1 q3 q13) ha₁ ha₃

private theorem transvConcl_A0 {d₁ d₂ d₃ : H6} (hcl : Subgroup.closure {d₁, d₂, d₃} = baseA zH)
    (hmono : ∀ n ∈ Subgroup.normalizer (baseA zH : Set H6), ∀ x ∈ ({d₁, d₂, d₃} : Set H6),
      n * x * n⁻¹ ∈ ({d₁, d₁⁻¹, d₂, d₂⁻¹, d₃, d₃⁻¹} : Set H6)) :
    TransvConcl (⊤ : Subgroup H6) d₁ d₂ d₃ := by
  obtain ⟨p₁, p₂, p₃, a₁, a₂, a₃, h12, h13, h23, ha₁, ha₂, ha₃, rfl, rfl, rfl⟩ := shape hcl hmono
  refine ⟨?_, ?_, ?_⟩
  · rw [top_inf_eq, cen_pow_val (zH_pow_three _) ha₂]
    exact card_cen_zH p₂
  · intro x _ hx3 hxc
    rw [top_inf_eq] at hxc
    obtain ⟨m, hm⟩ := conj_z1_of_card hx3 hxc
    obtain ⟨g, hg⟩ := conj_z1_of_single p₂ ha₂
    refine ⟨g * m, Subgroup.mem_top _, ?_⟩
    rw [hg, ← hm]
    group
  · intro s _ hs2 hs1 hs3 hs2'
    exact transvS_of_basis h12 h13 h23 ha₁ ha₂ ha₃ hs2 hs1 hs3 hs2'

private theorem mono_conj {B : Subgroup H6} (g : H6) {c₁ c₂ c₃ : H6}
    (hB : B.map (MulAut.conj g⁻¹).toMonoidHom = baseA zH)
    (hmono : ∀ n ∈ Subgroup.normalizer (B : Set H6), ∀ x ∈ ({c₁, c₂, c₃} : Set H6),
      n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set H6)) :
    ∀ n ∈ Subgroup.normalizer (baseA zH : Set H6),
      ∀ x ∈ ({g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} : Set H6),
      n * x * n⁻¹ ∈ ({g⁻¹ * c₁ * g, (g⁻¹ * c₁ * g)⁻¹, g⁻¹ * c₂ * g, (g⁻¹ * c₂ * g)⁻¹,
        g⁻¹ * c₃ * g, (g⁻¹ * c₃ * g)⁻¹} : Set H6) := by
  intro n hn x hx
  have hN : g * n * g⁻¹ ∈ Subgroup.normalizer (B : Set H6) := by
    have hB' : B = (baseA zH).map (MulAut.conj g).toMonoidHom := by
      rw [← hB]
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · intro hy
        exact ⟨g⁻¹ * y * g⁻¹⁻¹, ⟨y, hy, rfl⟩, by group⟩
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        convert hw using 1
        group
    rw [hB', ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨n, hn, rfl⟩
  have hinv : ∀ c : H6, (g⁻¹ * c * g)⁻¹ = g⁻¹ * c⁻¹ * g := fun c => by group
  have main : ∀ c ∈ ({c₁, c₂, c₃} : Set H6), n * (g⁻¹ * c * g) * n⁻¹ ∈
      ({g⁻¹ * c₁ * g, (g⁻¹ * c₁ * g)⁻¹, g⁻¹ * c₂ * g, (g⁻¹ * c₂ * g)⁻¹,
        g⁻¹ * c₃ * g, (g⁻¹ * c₃ * g)⁻¹} : Set H6) := by
    intro c hc
    rw [show n * (g⁻¹ * c * g) * n⁻¹ = g⁻¹ * ((g * n * g⁻¹) * c * (g * n * g⁻¹)⁻¹) * g by group]
    have h := hmono _ hN c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    simp only [hinv]
    rcases h with h | h | h | h | h | h <;> rw [h] <;> simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact main c₁ (by simp)
  · exact main c₂ (by simp)
  · exact main c₃ (by simp)

private theorem exists_conj_baseA {c₁ c₂ c₃ : H6}
    (hB : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure {c₁, c₂, c₃}))
    (hBc : Nat.card (Subgroup.closure {c₁, c₂, c₃}) = 27)
    (hmono : ∀ n ∈ Subgroup.normalizer (Subgroup.closure {c₁, c₂, c₃} : Set H6),
      ∀ x ∈ ({c₁, c₂, c₃} : Set H6),
      n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set H6)) :
    ∃ g : H6, Subgroup.closure {g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} = baseA zH ∧
      ∀ n ∈ Subgroup.normalizer (baseA zH : Set H6),
        ∀ x ∈ ({g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} : Set H6),
        n * x * n⁻¹ ∈ ({g⁻¹ * c₁ * g, (g⁻¹ * c₁ * g)⁻¹, g⁻¹ * c₂ * g, (g⁻¹ * c₂ * g)⁻¹,
          g⁻¹ * c₃ * g, (g⁻¹ * c₃ * g)⁻¹} : Set H6) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Subgroup.closure ({c₁, c₂, c₃} : Set H6) with hBdef
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 3) (by rw [hBc]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hBp
  have hPg : B.map (MulAut.conj g⁻¹).toMonoidHom = baseA zH :=
    eq_baseA_of_le_wreathW wreathFacts_zH card_wreathW_zH
      (CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ B hB)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hBc])
  have hcl : Subgroup.closure {g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} = baseA zH := by
    rw [← hPg, hBdef, MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  exact ⟨g, hcl, mono_conj g hPg hmono⟩

theorem exists_conj_zH_pow {c₁ c₂ c₃ : H6}
    (hB : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure {c₁, c₂, c₃}))
    (hBc : Nat.card (Subgroup.closure {c₁, c₂, c₃}) = 27)
    (hmono : ∀ n ∈ Subgroup.normalizer (Subgroup.closure {c₁, c₂, c₃} : Set H6),
      ∀ x ∈ ({c₁, c₂, c₃} : Set H6),
      n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set H6)) :
    ∃ g : H6, ∃ (p₁ p₂ p₃ : Fin 3) (a₁ a₂ a₃ : ZMod 3), p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧ g⁻¹ * c₁ * g = zH p₁ ^ a₁.val ∧
      g⁻¹ * c₂ * g = zH p₂ ^ a₂.val ∧ g⁻¹ * c₃ * g = zH p₃ ^ a₃.val := by
  obtain ⟨g, hcl, hmono'⟩ := exists_conj_baseA hB hBc hmono
  obtain ⟨p₁, p₂, p₃, a₁, a₂, a₃, h12, h13, h23, ha₁, ha₂, ha₃, e₁, e₂, e₃⟩ := shape hcl hmono'
  exact ⟨g, p₁, p₂, p₃, a₁, a₂, a₃, h12, h13, h23, ha₁, ha₂, ha₃, e₁, e₂, e₃⟩

private theorem transvConcl_H6 {c₁ c₂ c₃ : H6}
    (hB : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure {c₁, c₂, c₃}))
    (hBc : Nat.card (Subgroup.closure {c₁, c₂, c₃}) = 27)
    (hmono : ∀ n ∈ Subgroup.normalizer (Subgroup.closure {c₁, c₂, c₃} : Set H6),
      ∀ x ∈ ({c₁, c₂, c₃} : Set H6),
      n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set H6)) :
    TransvConcl (⊤ : Subgroup H6) c₁ c₂ c₃ := by
  obtain ⟨g, hcl, hmono'⟩ := exists_conj_baseA hB hBc hmono
  have h := (transvConcl_A0 hcl hmono').map
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  convert h using 2 <;> group

end Facts

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79 Sp6Transv
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH)

private theorem exists_H6_basis {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 3 2 1) {b₁ b₂ b₃ : X}
    (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L) (hB : IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) :
    ∃ f : H6 →* X, Function.Injective f ∧ (⊤ : Subgroup H6).map f = L ∧ ∃ c₁ c₂ c₃ : H6,
      f c₁ = b₁ ∧ f c₂ = b₂ ∧ f c₃ = b₃ ∧
      CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) ∧
      Nat.card (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) = 27 ∧
      ∀ n ∈ Subgroup.normalizer (Subgroup.closure ({c₁, c₂, c₃} : Set H6) : Set H6),
        ∀ x ∈ ({c₁, c₂, c₃} : Set H6),
        n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set H6) := by
  classical
  obtain ⟨θ⟩ := nonempty_mulEquiv_H6_of_stated hL
  set f : H6 →* X := L.subtype.comp θ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.symm.injective
  have hfa : ∀ y : X, ∀ hy : y ∈ L, f (θ ⟨y, hy⟩) = y := fun y hy => by
    simp [hfdef]
  have hfL : (⊤ : Subgroup H6).map f = L := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (θ.symm x).2
    · intro hy
      exact ⟨θ ⟨y, hy⟩, Subgroup.mem_top _, hfa y hy⟩
  have hfL' : ∀ x, f x ∈ L := fun x => (θ.symm x).2
  set c₁ := θ ⟨b₁, hb₁⟩
  set c₂ := θ ⟨b₂, hb₂⟩
  set c₃ := θ ⟨b₃, hb₃⟩
  have e₁ : f c₁ = b₁ := hfa _ _
  have e₂ : f c₂ = b₂ := hfa _ _
  have e₃ : f c₃ = b₃ := hfa _ _
  have hcl : (Subgroup.closure ({c₁, c₂, c₃} : Set H6)).map f =
      Subgroup.closure ({b₁, b₂, b₃} : Set X) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, e₁, e₂, e₃]
  have hBc : Nat.card (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) = 27 := by
    rw [← Subgroup.card_map_of_injective hf, hcl, hB.2]
    norm_num
  have hBe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) := by
    have hB0 : CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({b₁, b₂, b₃} : Set X)) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hB.1
    obtain ⟨hcomm, hpow⟩ := hB0
    have hmemf : ∀ x ∈ Subgroup.closure ({c₁, c₂, c₃} : Set H6),
        f x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set X) := fun x hx => by
      rw [← hcl]; exact Subgroup.mem_map_of_mem f hx
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · have := congrArg Subtype.val (hcomm.is_comm.comm ⟨f a, hmemf a a.2⟩ ⟨f b, hmemf b b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · rw [map_pow, hpow _ (hmemf x hx), map_one]
  have hmono' : ∀ n ∈ Subgroup.normalizer (Subgroup.closure ({c₁, c₂, c₃} : Set H6) : Set H6),
      ∀ x ∈ ({c₁, c₂, c₃} : Set H6),
      n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set H6) := by
    intro n hn x hx
    have hnN : f n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set X)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      by_cases hyL : y ∈ L
      · obtain ⟨y', rfl⟩ : ∃ y', f y' = y := ⟨θ ⟨y, hyL⟩, hfa y hyL⟩
        rw [← map_inv, ← map_mul, ← map_mul, ← hcl, Subgroup.mem_map_iff_mem hf,
          Subgroup.mem_map_iff_mem hf]
        exact Subgroup.mem_normalizer_iff.mp hn y'
      · have h1 : y ∉ Subgroup.closure ({b₁, b₂, b₃} : Set X) := fun h =>
          hyL ((Subgroup.closure_le L).mpr (by
            rintro _ (rfl | rfl | rfl) <;> assumption) h)
        have h2 : f n * y * (f n)⁻¹ ∉ Subgroup.closure ({b₁, b₂, b₃} : Set X) := fun h => by
          have hL' : f n * y * (f n)⁻¹ ∈ L := (Subgroup.closure_le L).mpr (by
            rintro _ (rfl | rfl | rfl) <;> assumption) h
          apply hyL
          have := L.mul_mem (L.mul_mem (L.inv_mem (hfL' n)) hL') (hfL' n)
          simpa [mul_assoc] using this
        exact iff_of_false h1 h2
    have hxm : f x ∈ ({b₁, b₂, b₃} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact Or.inl e₁
      · exact Or.inr (Or.inl e₂)
      · exact Or.inr (Or.inr e₃)
    have h0 := hmono (f n) (hfL' n) hnN (f x) hxm
    have h : f (n * x * n⁻¹) ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X) := by
      rw [map_mul, map_mul, map_inv]
      exact h0
    have i₁ : b₁⁻¹ = f c₁⁻¹ := by rw [map_inv, e₁]
    have i₂ : b₂⁻¹ = f c₂⁻¹ := by rw [map_inv, e₂]
    have i₃ : b₃⁻¹ = f c₃⁻¹ := by rw [map_inv, e₃]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h | h | h
    · exact Or.inl (hf (h.trans e₁.symm))
    · exact Or.inr (Or.inl (hf (h.trans i₁)))
    · exact Or.inr (Or.inr (Or.inl (hf (h.trans e₂.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hf (h.trans i₂)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hf (h.trans e₃.symm))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hf (h.trans i₃))))))
  exact ⟨f, hf, hfL, c₁, c₂, c₃, e₁, e₂, e₃, hBe, hBc, hmono'⟩

theorem kf_sp6Transv : KF_Sp6Transv := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB _ hmono
  obtain ⟨f, hf, hfL, c₁, c₂, c₃, e₁, e₂, e₃, hBe, hBc, hmono'⟩ :=
    exists_H6_basis hL hb₁ hb₂ hb₃ hB hmono
  have key := (transvConcl_H6 hBe hBc hmono').map hf
  rw [hfL, e₁, e₂, e₃] at key
  exact key

theorem Sp6Transv.exists_hom_zH_pow {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 3 2 1) {b₁ b₂ b₃ : X}
    (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L) (hB : IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) :
    ∃ f : H6 →* X, Function.Injective f ∧ (⊤ : Subgroup H6).map f = L ∧
      ∃ (p₁ p₂ p₃ : Fin 3) (a₁ a₂ a₃ : ZMod 3), p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ a₁ ≠ 0 ∧
        a₂ ≠ 0 ∧ a₃ ≠ 0 ∧ f (zH p₁ ^ a₁.val) = b₁ ∧ f (zH p₂ ^ a₂.val) = b₂ ∧
        f (zH p₃ ^ a₃.val) = b₃ := by
  obtain ⟨f, hf, hfL, c₁, c₂, c₃, e₁, e₂, e₃, hBe, hBc, hmono'⟩ :=
    exists_H6_basis hL hb₁ hb₂ hb₃ hB hmono
  obtain ⟨g, p₁, p₂, p₃, a₁, a₂, a₃, h12, h13, h23, ha₁, ha₂, ha₃, g₁, g₂, g₃⟩ :=
    exists_conj_zH_pow hBe hBc hmono'
  have hc : ∀ c : H6, (f.comp (MulAut.conj g).toMonoidHom) (g⁻¹ * c * g) = f c := fun c => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show g * (g⁻¹ * c * g) * g⁻¹ = c by group]
  refine ⟨f.comp (MulAut.conj g).toMonoidHom, hf.comp (MulAut.conj g).injective, ?_, p₁, p₂, p₃,
    a₁, a₂, a₃, h12, h13, h23, ha₁, ha₂, ha₃, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective, hfL]
  · rw [← g₁, hc, e₁]
  · rw [← g₂, hc, e₂]
  · rw [← g₃, hc, e₃]

end CFSG.RankThree.PartTwo.Sec21.FF81

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

section Torus

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit

theorem cert899102_parts :
    (∃ p : H6, p * zH 0 * p⁻¹ = zH 1 ∧ p * zH 1 * p⁻¹ = zH 0 ∧ p * zH 2 * p⁻¹ = zH 2) ∧
    (∃ p : H6, p * zH 0 * p⁻¹ = zH 0 ∧ p * zH 1 * p⁻¹ = zH 2 ∧ p * zH 2 * p⁻¹ = zH 1) ∧
    Subgroup.centralizer (baseA zH : Set H6) = baseA zH ∧
    (∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 2 →
      ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1) * g⁻¹) ∧
    (∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 3 →
      ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1 * zH 2) * g⁻¹) :=
  Certificates.certificate899102

private noncomputable def p01H : H6 := cert899102_parts.1.choose

private noncomputable def p12H : H6 := cert899102_parts.2.1.choose

private theorem p01_z0 : p01H * zH 0 * p01H⁻¹ = zH 1 := cert899102_parts.1.choose_spec.1
private theorem p01_z1 : p01H * zH 1 * p01H⁻¹ = zH 0 := cert899102_parts.1.choose_spec.2.1
private theorem p01_z2 : p01H * zH 2 * p01H⁻¹ = zH 2 := cert899102_parts.1.choose_spec.2.2
private theorem p12_z1 : p12H * zH 1 * p12H⁻¹ = zH 2 := cert899102_parts.2.1.choose_spec.2.1
private theorem p12_z2 : p12H * zH 2 * p12H⁻¹ = zH 1 := cert899102_parts.2.1.choose_spec.2.2
private theorem p12_z0 : p12H * zH 0 * p12H⁻¹ = zH 0 := cert899102_parts.2.1.choose_spec.1

private theorem fl0_z0 : fl0H * zH 0 * fl0H⁻¹ = (zH 0)⁻¹ := by
  rw [fl0H_conj 0, inv_eq_sq_zH]; rfl
private theorem fl0_z1 : fl0H * zH 1 * fl0H⁻¹ = zH 1 := by
  rw [fl0H_conj 1]; exact pow_one _
private theorem fl0_z2 : fl0H * zH 2 * fl0H⁻¹ = zH 2 := by
  rw [fl0H_conj 2]; exact pow_one _
private theorem fl2_z0 : fl2H * zH 0 * fl2H⁻¹ = zH 0 := by
  rw [fl2H_conj 0]; exact pow_one _
private theorem fl2_z1 : fl2H * zH 1 * fl2H⁻¹ = zH 1 := by
  rw [fl2H_conj 1]; exact pow_one _
private theorem fl2_z2 : fl2H * zH 2 * fl2H⁻¹ = (zH 2)⁻¹ := by
  rw [fl2H_conj 2, inv_eq_sq_zH]; rfl
private theorem s0_z0 : s0H * zH 0 * s0H⁻¹ = zH 0 := conj_of_comm s0H_comm_z0
private theorem s0_z2 : s0H * zH 2 * s0H⁻¹ = zH 2 := conj_of_comm s0H_comm_z2

private theorem closure_zH : Subgroup.closure {zH 0, zH 1, zH 2} = baseA zH := by
  rw [Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
    baseA, sup_assoc]

private theorem cen_baseA : Subgroup.centralizer (baseA zH : Set H6) = baseA zH :=
  cert899102_parts.2.2.1

private theorem vecElt_one_one_one : vecElt zH ![1, 1, 1] = zH 0 * zH 1 * zH 2 := by
  change zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 1 = _
  rw [pow_one, pow_one, pow_one]

private theorem single_of_card {y : H6} (hy : y ∈ baseA zH)
    (hc : Nat.card (Subgroup.centralizer {y}) = 2160) :
    ∃ (p : Fin 3) (k : ℕ), (k = 1 ∨ k = 2) ∧ y = zH p ^ k := by
  obtain ⟨v, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp hy
  have hv : vecElt zH v = zH 0 ^ (v 0).val * zH 1 ^ (v 1).val * zH 2 ^ (v 2).val := rfl
  have hval : ∀ i, (v i).val < 3 := fun i => ZMod.val_lt _
  set a := (v 0).val
  set b := (v 1).val
  set c := (v 2).val
  have h2 : ([a, b, c].filter (· != 0)).length ≠ 2 := by
    intro h2
    obtain ⟨g, hg⟩ := cert899102_parts.2.2.2.1 a (hval 0) b (hval 1) c (hval 2) h2
    rw [hv, hg, card_cen_conj, ← aElt_three, ← centSub_eq, card_centSub] at hc
    exact absurd hc (by decide)
  have h3 : ([a, b, c].filter (· != 0)).length ≠ 3 := by
    intro h3
    obtain ⟨g, hg⟩ := cert899102_parts.2.2.2.2 a (hval 0) b (hval 1) c (hval 2) h3
    rw [hv, hg, card_cen_conj, ← vecElt_one_one_one] at hc
    have hdvd := Subgroup.card_dvd_of_le wreathW_le_cen
    rw [card_wreathW_zH, hc] at hdvd
    exact absurd hdvd (by decide)
  rw [hv] at hc ⊢
  have h0 : ([a, b, c].filter (· != 0)).length ≠ 0 := by
    intro h0
    have ha : a = 0 ∧ b = 0 ∧ c = 0 := by
      simp only [List.filter_cons, List.filter_nil] at h0
      split_ifs at h0 with h1 h2 h3 <;> simp_all
    obtain ⟨ha, hb, hc'⟩ := ha
    rw [ha, hb, hc', pow_zero, pow_zero, pow_zero, one_mul, one_mul,
      Subgroup.centralizer_singleton_one, Subgroup.card_top, card_H6] at hc
    exact absurd hc (by decide)
  have key : ∀ a' < 3, ∀ b' < 3, ∀ c' < 3, ([a', b', c'].filter (· != 0)).length ≠ 0 →
      ([a', b', c'].filter (· != 0)).length ≠ 2 → ([a', b', c'].filter (· != 0)).length ≠ 3 →
      (b' = 0 ∧ c' = 0 ∧ (a' = 1 ∨ a' = 2)) ∨ (a' = 0 ∧ c' = 0 ∧ (b' = 1 ∨ b' = 2)) ∨
        (a' = 0 ∧ b' = 0 ∧ (c' = 1 ∨ c' = 2)) := by
    intro a' ha' b' hb' c' hc'
    interval_cases a' <;> interval_cases b' <;> interval_cases c' <;> decide
  rcases key a (hval 0) b (hval 1) c (hval 2) h0 h2 h3 with ⟨hb, hc', ha⟩ | ⟨ha, hc', hb⟩ |
    ⟨ha, hb, hc'⟩
  · exact ⟨0, a, ha, by rw [hb, hc', pow_zero, pow_zero, mul_one, mul_one]⟩
  · exact ⟨1, b, hb, by rw [ha, hc', pow_zero, pow_zero, one_mul, mul_one]⟩
  · exact ⟨2, c, hc', by rw [ha, hb, pow_zero, pow_zero, one_mul, one_mul]⟩

private theorem conj_into_baseA {x : H6} (hx : orderOf x = 3) :
    ∃ m : H6, m * x * m⁻¹ ∈ baseA zH := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hp
  obtain ⟨w, hw, hgw⟩ := hg (Subgroup.mem_zpowers x)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgw
  obtain ⟨v, j, rfl⟩ := mem_wreathW wreathFacts_zH hw
  have hw3 : orderOf (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) = 3 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgw, hx] at h
    exact h.symm
  obtain ⟨h3, h1⟩ := order_three_wreath hw3
  have fin : ∀ x₀ : H6, x₀ ∈ baseA zH → ∀ h : H6,
      vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) = h * x₀ * h⁻¹ → ∃ m : H6, m * x * m⁻¹ ∈ baseA zH := by
    intro x₀ hx₀ h hh
    refine ⟨(g * h)⁻¹, ?_⟩
    rw [← hgw, hh, show (g * h)⁻¹ * (g * (h * x₀ * h⁻¹) * g⁻¹) * (g * h)⁻¹⁻¹ = x₀ by group]
    exact hx₀
  rcases conj_rep_of_wreath h3 h1 with ⟨h, hh⟩ | ⟨h, hh⟩ | ⟨h, hh⟩
  · exact fin _ (z_mem_baseA 1) h hh
  · exact fin _ (mul_mem (z_mem_baseA 0) (z_mem_baseA 1)) h hh
  · exact fin _ (vecElt_mem_baseA wreathFacts_zH _) h hh

private theorem wreathW_not_comm : ¬ ∀ x ∈ wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH, ∀ y ∈ wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH, x * y = y * x := by
  intro h
  have e := h CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH t_mem_wreathW (zH 0) (Subgroup.mem_sup_left (z_mem_baseA 0))
  have : zH 1 = zH 0 := by
    have h1 := tH_conj 0
    rw [e, mul_inv_cancel_right] at h1
    exact h1.symm
  have hv := vecElt_injective wreathFacts_zH (v := Pi.single 1 1) (w := Pi.single 0 1)
    (by rw [vecElt_single_one, vecElt_single_one, this])
  exact absurd (congrFun hv 1) (by decide)

private theorem card_le_27 {E : Subgroup H6} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hp
  have hdvd : Nat.card E ∣ 81 := by
    have := Subgroup.card_dvd_of_le hg
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_wreathW_zH] at this
  have hne : Nat.card E ≠ 81 := by
    intro h81
    have heq : E = (wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH).map (MulAut.conj g).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hg (by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_wreathW_zH, h81])
    apply wreathW_not_comm
    intro x hx y hy
    have hx' : g * x * g⁻¹ ∈ E := heq ▸ ⟨x, hx, rfl⟩
    have hy' : g * y * g⁻¹ ∈ E := heq ▸ ⟨y, hy, rfl⟩
    have := hc _ hx' _ hy'
    have e : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := this
        _ = g * (y * x) * g⁻¹ := by group
    simpa using e
  have key : ∀ n ≤ 81, n ∣ 81 → n ≠ 81 → n ≤ 27 := by decide
  exact key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hne

private theorem e27_unique {Q E₁ E₂ : Subgroup H6} (hQ : IsPGroup 3 Q) (h₁ : E₁ ≤ Q) (h₂ : E₂ ≤ Q)
    (he₁ : CFSG.Assembly.IsElemAbelian 3 E₁) (hc₁ : Nat.card E₁ = 27)
    (he₂ : CFSG.Assembly.IsElemAbelian 3 E₂) (hc₂ : Nat.card E₂ = 27) : E₁ = E₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hQ
  have hb : ∀ {E : Subgroup H6}, E ≤ Q → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      E.map (MulAut.conj g⁻¹).toMonoidHom = baseA zH := fun hEQ he hc =>
    eq_baseA_of_le_wreathW wreathFacts_zH card_wreathW_zH
      (CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le (hEQ.trans hg))
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ he)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hc])
  exact Subgroup.map_injective (MulAut.conj g⁻¹).injective
    ((hb h₁ he₁ hc₁).trans (hb h₂ he₂ hc₂).symm)

end Torus

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79 Sp6Transv
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit

theorem kf_sp6Torus : KF_Sp6Torus := by
  intro X _ _ L hL
  classical
  obtain ⟨θ⟩ := nonempty_mulEquiv_H6_of_stated hL
  set f : H6 →* X := L.subtype.comp θ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.symm.injective
  have hfa : ∀ y : X, ∀ hy : y ∈ L, f (θ ⟨y, hy⟩) = y := fun y hy => by simp [hfdef]
  have hfL' : ∀ x, f x ∈ L := fun x => (θ.symm x).2
  have hpre : ∀ y ∈ L, ∃ x, f x = y := fun y hy => ⟨θ ⟨y, hy⟩, hfa y hy⟩
  have hconj : ∀ n x : H6, f n * f x * (f n)⁻¹ = f (n * x * n⁻¹) := fun n x => by
    rw [map_mul, map_mul, map_inv]
  set B := (baseA zH).map f with hBdef
  have hcl : Subgroup.closure ({f (zH 0), f (zH 1), f (zH 2)} : Set X) = B := by
    rw [hBdef, ← closure_zH, MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton]
  have hBL : B ≤ L := by rintro _ ⟨x, -, rfl⟩; exact hfL' x
  have hmemB : ∀ x : H6, f x ∈ B ↔ x ∈ baseA zH := fun x => Subgroup.mem_map_iff_mem hf
  refine ⟨f (zH 0), f (zH 1), f (zH 2), hfL' _, hfL' _, hfL' _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  ·
    rw [hcl]
    refine ⟨?_, by rw [hBdef, Subgroup.card_map_of_injective hf, card_baseA wreathFacts_zH]; rfl⟩
    exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp
      (CFSG.Open.IsElemAbelian.map (isElemAbelian_baseA wreathFacts_zH) f)
  ·
    rw [hcl]
    ext y
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨hyL, hyC⟩
      obtain ⟨x, rfl⟩ := hpre y hyL
      rw [hmemB, ← cen_baseA, Subgroup.mem_centralizer_iff]
      intro a ha
      have := Subgroup.mem_centralizer_iff.mp hyC (f a) ((hmemB a).mpr ha)
      exact hf (by rw [map_mul, map_mul]; exact this)
    · intro hy
      refine ⟨hBL hy, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      obtain ⟨u, hu, rfl⟩ := ha
      obtain ⟨v, hv, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_iff.mp (cen_baseA.symm ▸ hv : v ∈ _) u hu
  ·
    rw [hcl]
    intro n hnL hnN x hx
    obtain ⟨n', rfl⟩ := hpre n hnL
    have hn' : n' ∈ Subgroup.normalizer (baseA zH : Set H6) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      rw [← hmemB, ← hmemB, ← hconj]
      exact Subgroup.mem_normalizer_iff.mp hnN (f a)
    have key : ∀ i : Fin 3, f n' * f (zH i) * (f n')⁻¹ ∈
        ({f (zH 0), (f (zH 0))⁻¹, f (zH 1), (f (zH 1))⁻¹, f (zH 2), (f (zH 2))⁻¹} : Set X) := by
      intro i
      rw [hconj]
      have hy : n' * zH i * n'⁻¹ ∈ baseA zH :=
        (Subgroup.mem_normalizer_iff.mp hn' (zH i)).mp (z_mem_baseA i)
      have hc : Nat.card (Subgroup.centralizer {n' * zH i * n'⁻¹}) = 2160 := by
        rw [card_cen_conj, card_cen_zH]
      obtain ⟨p, k, hk, e⟩ := single_of_card hy hc
      rw [e]
      have hinv : f (zH p ^ 2) = (f (zH p))⁻¹ := by
        rw [← inv_eq_sq_zH, map_inv]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hk with rfl | rfl
      · rw [pow_one]
        fin_cases p <;> simp
      · rw [hinv]
        fin_cases p <;> simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact key 0
    · exact key 1
    · exact key 2
  ·
    refine ⟨f fl0H, hfL' _, ?_, ?_, ?_⟩ <;> rw [hconj]
    · rw [fl0_z0, map_inv]
    · rw [fl0_z1]
    · rw [fl0_z2]
  ·
    refine ⟨f p01H, hfL' _, ?_, ?_, ?_⟩ <;> rw [hconj]
    · rw [p01_z0]
    · rw [p01_z1]
    · rw [p01_z2]
  ·
    refine ⟨f CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH, hfL' _, ?_, ?_, ?_⟩ <;> rw [hconj, tH_conj] <;> rfl
  ·
    refine ⟨f p12H, hfL' _, ?_, ?_, ?_⟩ <;> rw [hconj]
    · rw [p12_z0]
    · rw [p12_z1]
    · rw [p12_z2]
  ·
    refine ⟨f (fl0H * s0H * fl2H), hfL' _, ?_, ?_, ?_⟩ <;> rw [hconj, mul_inv_rev, mul_inv_rev]
    · rw [show fl0H * s0H * fl2H * zH 0 * (fl2H⁻¹ * (s0H⁻¹ * fl0H⁻¹)) =
        fl0H * (s0H * (fl2H * zH 0 * fl2H⁻¹) * s0H⁻¹) * fl0H⁻¹ by group, fl2_z0, s0_z0, fl0_z0,
        map_inv]
    · rw [show fl0H * s0H * fl2H * zH 1 * (fl2H⁻¹ * (s0H⁻¹ * fl0H⁻¹)) =
        fl0H * (s0H * (fl2H * zH 1 * fl2H⁻¹) * s0H⁻¹) * fl0H⁻¹ by group, fl2_z1, s0H_conj_z1,
        show fl0H * (zH 1)⁻¹ * fl0H⁻¹ = (fl0H * zH 1 * fl0H⁻¹)⁻¹ by group, fl0_z1, map_inv]
    · rw [show fl0H * s0H * fl2H * zH 2 * (fl2H⁻¹ * (s0H⁻¹ * fl0H⁻¹)) =
        fl0H * (s0H * (fl2H * zH 2 * fl2H⁻¹) * s0H⁻¹) * fl0H⁻¹ by group, fl2_z2,
        show s0H * (zH 2)⁻¹ * s0H⁻¹ = (s0H * zH 2 * s0H⁻¹)⁻¹ by group, s0_z2,
        show fl0H * (zH 2)⁻¹ * fl0H⁻¹ = (fl0H * zH 2 * fl0H⁻¹)⁻¹ by group, fl0_z2, map_inv]
  ·
    rw [hcl]
    intro x hxL hx3
    obtain ⟨x', rfl⟩ := hpre x hxL
    rw [orderOf_injective f hf] at hx3
    obtain ⟨m, hm⟩ := conj_into_baseA hx3
    exact ⟨f m, hfL' m, by rw [hconj]; exact (hmemB _).mpr hm⟩
  ·
    intro E hEL hc h3
    have hEm : (E.comap f).map f = E :=
      Subgroup.map_comap_eq_self (fun y hy => by
        obtain ⟨x, hx⟩ := hpre y (hEL hy); exact ⟨x, hx⟩)
    rw [← hEm, Subgroup.card_map_of_injective hf]
    refine card_le_27 (fun a ha b hb => hf ?_) (fun a ha => hf ?_)
    · rw [map_mul, map_mul]; exact hc _ ha _ hb
    · rw [map_pow, map_one]; exact h3 _ ha
  ·
    intro Q hQL hQ E₁ E₂ h₁ h₂ he₁ he₂
    have hsurj : ∀ {K : Subgroup X}, K ≤ L → (K.comap f).map f = K := fun hK =>
      Subgroup.map_comap_eq_self (fun y hy => by
        obtain ⟨x, hx⟩ := hpre y (hK hy); exact ⟨x, hx⟩)
    have hE : ∀ {E : Subgroup X}, E ≤ L → IsElemAb 3 3 E →
        CFSG.Assembly.IsElemAbelian 3 (E.comap f) ∧ Nat.card (E.comap f) = 27 := by
      intro E hEL he
      have hc : Nat.card (E.comap f) = 27 := by
        rw [← Subgroup.card_map_of_injective hf, hsurj hEL, he.2]; rfl
      have h0 : CFSG.Open.IsElemAbelian 3 E :=
        CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr he.1
      obtain ⟨hcomm, hpow⟩ := h0
      refine ⟨⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩, hc⟩
      · have := congrArg Subtype.val (hcomm.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
        simpa only [Subgroup.coe_mul, map_mul] using this
      · rw [map_pow, hpow _ hx, map_one]
    obtain ⟨he₁', hc₁⟩ := hE (h₁.trans hQL) he₁
    obtain ⟨he₂', hc₂⟩ := hE (h₂.trans hQL) he₂
    have hQ' : IsPGroup 3 (Q.comap f) := hQ.comap_of_injective f hf
    have heq := e27_unique hQ' (Subgroup.comap_mono h₁) (Subgroup.comap_mono h₂) he₁' hc₁ he₂' hc₂
    rw [← hsurj (h₁.trans hQL), ← hsurj (h₂.trans hQL), heq]
  ·
    refine ⟨f s0H, hfL' _, by rw [orderOf_injective f hf]; exact orderOf_s0H, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, s0H_comm_z0]
    · rw [← map_mul, ← map_mul, s0H_comm_z2]

end CFSG.RankThree.PartTwo.Sec21.FF81

end
