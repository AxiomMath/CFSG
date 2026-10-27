module

public import CFSG.LocalAnalysis.WeakClosure81.W172Class2
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem w172_minInv_class_two {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : (⁅⁅Y, Y⁆, Y⁆ : Subgroup Γ) = ⊥ := by
  set γ₂ : Subgroup Γ := ⁅Y, Y⁆ with hγ₂
  set γ₃ : Subgroup Γ := ⁅γ₂, Y⁆ with hγ₃
  set γ₄ : Subgroup Γ := ⁅γ₃, Y⁆ with hγ₄
  have hγ₂Y : γ₂ ≤ Y := by
    rw [hγ₂]
    exact Subgroup.commutator_le_of_le le_rfl le_rfl
  have hγ₃γ₂ : γ₃ ≤ γ₂ := by
    rw [hγ₃]
    refine (Subgroup.le_normalizer_iff_commutator_le_left (H := Y) (K := γ₂)).mp ?_
    rw [hγ₂]
    exact Subgroup.normalizer_commutator_ge_left Y Y
  have hγ₄γ₃ : γ₄ ≤ γ₃ := by
    rw [hγ₄]
    refine (Subgroup.le_normalizer_iff_commutator_le_left (H := Y) (K := γ₃)).mp ?_
    rw [hγ₃]
    exact Subgroup.normalizer_commutator_ge_right γ₂ Y
  have hYγ₂ : ⁅Y, γ₂⁆ ≤ γ₂ := by
    refine (Subgroup.le_normalizer_iff_commutator_le_right (H := Y) (K := γ₂)).mp ?_
    rw [hγ₂]
    exact Subgroup.normalizer_commutator_ge_left Y Y
  have hdγ₂ : ∀ z ∈ γ₂, d * z * d⁻¹ = z := by
    intro z hz
    exact (w172_minInv_centralizer h z (hγ₂Y hz)).mpr (hγ₂ ▸ hz)
  have hγ₂γ₂ : ⁅γ₂, γ₂⁆ ≤ γ₄ := by
    let T : Subgroup ↥Y := ⊤
    let K2 : Subgroup ↥Y := ⁅T, T⁆
    let K3 : Subgroup ↥Y := ⁅K2, T⁆
    let K4 : Subgroup ↥Y := ⁅K3, T⁆
    have hTmap : T.map Y.subtype = Y := by
      show (⊤ : Subgroup ↥Y).map Y.subtype = Y
      rw [← MonoidHom.range_eq_map Y.subtype, Subgroup.range_subtype]
    have hK2 : K2.map Y.subtype = γ₂ := by
      show (⁅T, T⁆).map Y.subtype = γ₂
      rw [Subgroup.map_commutator]
      show ⁅T.map Y.subtype, T.map Y.subtype⁆ = γ₂
      rw [hTmap, hγ₂]
    have hK3 : K3.map Y.subtype = γ₃ := by
      show (⁅K2, T⁆).map Y.subtype = γ₃
      rw [Subgroup.map_commutator]
      show ⁅K2.map Y.subtype, T.map Y.subtype⁆ = γ₃
      rw [hK2, hTmap, hγ₃]
    have hK4 : K4.map Y.subtype = γ₄ := by
      show (⁅K3, T⁆).map Y.subtype = γ₄
      rw [Subgroup.map_commutator]
      show ⁅K3.map Y.subtype, T.map Y.subtype⁆ = γ₄
      rw [hK3, hTmap, hγ₄]
    have hthree : ⁅K2, K2⁆ ≤ K4 := by
      refine CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal (M := ⊤) (A := T)
        (B := K2) (N := K4) le_top le_top le_top
        (le_of_eq (Subgroup.normalizer_eq_top (H := K4)).symm) ?_ ?_
      · exact le_of_eq (by rw [Subgroup.commutator_comm T K2])
      · exact le_of_eq rfl
    rw [← hK2, ← hK4, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hthree
  have hw_mem : ∀ y ∈ Y, (d * y * d⁻¹) * y ∈ γ₂ := by
    intro y hy
    obtain ⟨i, ⟨hiI, hic⟩, -⟩ := w172_minInv_transversal h y hy
    have hiY : i ∈ Y := hiI.1
    have hii : d * i * d⁻¹ = i⁻¹ := hiI.2
    set c : Γ := i⁻¹ * y with hc
    have hcγ₂ : c ∈ γ₂ := hic
    have hy_eq : y = i * c := by rw [hc]; group
    have hdy : d * y * d⁻¹ = i⁻¹ * c := by
      rw [hy_eq,
        show d * (i * c) * d⁻¹ = (d * i * d⁻¹) * (d * c * d⁻¹) by group,
        hii, hdγ₂ c hcγ₂]
    have hconj_mem : i⁻¹ * c * i ∈ γ₂ := by
      have heq : i⁻¹ * c * i = ⁅i⁻¹, c⁆ * c := by
        simp only [commutatorElement_def]; group
      rw [heq]
      exact γ₂.mul_mem (hYγ₂ (Subgroup.commutator_mem_commutator (Y.inv_mem hiY) hcγ₂)) hcγ₂
    rw [hdy, hy_eq, show (i⁻¹ * c) * (i * c) = (i⁻¹ * c * i) * c by group]
    exact γ₂.mul_mem hconj_mem hcγ₂
  have hsq : ∀ z ∈ γ₂, ∀ y ∈ Y, (⁅z, y⁆ : Γ) ^ 2 ∈ γ₄ := by
    intro z hz y hy
    have hcommγ₃ : ⁅z, y⁆ ∈ γ₃ := by
      rw [hγ₃]
      exact Subgroup.commutator_mem_commutator hz hy
    have hcommγ₂ : ⁅z, y⁆ ∈ γ₂ := hγ₃γ₂ hcommγ₃
    have hdz : d * z * d⁻¹ = z := hdγ₂ z hz
    have hdcomm : d * ⁅z, y⁆ * d⁻¹ = ⁅z, y⁆ := hdγ₂ _ hcommγ₂
    have hzy : ⁅z, y⁆ = ⁅z, d * y * d⁻¹⁆ := by
      rw [← hdcomm, conjugate_commutatorElement, hdz]
    set w : Γ := (d * y * d⁻¹) * y with hw
    have hwγ₂ : w ∈ γ₂ := hw_mem y hy
    have hdy : d * y * d⁻¹ = w * y⁻¹ := by rw [hw]; group
    have hA : ⁅z, w⁆ ∈ γ₄ := hγ₂γ₂ (Subgroup.commutator_mem_commutator hz hwγ₂)
    have hzyinv_γ₃ : ⁅z, y⁻¹⁆ ∈ γ₃ := by
      rw [hγ₃]
      exact Subgroup.commutator_mem_commutator hz (Y.inv_mem hy)
    have hB : ⁅w, ⁅z, y⁻¹⁆⁆ ∈ γ₄ :=
      (Subgroup.commutator_mono le_rfl hγ₃γ₂).trans hγ₂γ₂
        (Subgroup.commutator_mem_commutator hwγ₂ hzyinv_γ₃)
    have hC : ⁅y⁻¹, ⁅z, y⁆⁻¹⁆ ∈ γ₄ := by
      have hmem : ⁅y⁻¹, ⁅z, y⁆⁻¹⁆ ∈ ⁅Y, γ₃⁆ :=
        Subgroup.commutator_mem_commutator (Y.inv_mem hy) (γ₃.inv_mem hcommγ₃)
      rw [Subgroup.commutator_comm Y γ₃, ← hγ₄] at hmem
      exact hmem
    have hconjw : w * ⁅z, y⁻¹⁆ * w⁻¹ = ⁅w, ⁅z, y⁻¹⁆⁆ * ⁅z, y⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have hzyinv : ⁅z, y⁻¹⁆ = ⁅y⁻¹, ⁅z, y⁆⁻¹⁆ * ⁅z, y⁆⁻¹ := by
      rw [commutatorElement_inv_right, commutatorElement_inv]
      simp only [commutatorElement_def]; group
    have hmul : ⁅z, w * y⁻¹⁆ = ⁅z, w⁆ * (w * ⁅z, y⁻¹⁆ * w⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]; group
    have hzy2 : ⁅z, y⁆ = ⁅z, w * y⁻¹⁆ := by rw [hzy, hdy]
    have heq : ⁅z, y⁆ = (⁅z, w⁆ * (⁅w, ⁅z, y⁻¹⁆⁆ * ⁅y⁻¹, ⁅z, y⁆⁻¹⁆)) * ⁅z, y⁆⁻¹ := by
      calc ⁅z, y⁆ = ⁅z, w * y⁻¹⁆ := hzy2
        _ = ⁅z, w⁆ * (w * ⁅z, y⁻¹⁆ * w⁻¹) := hmul
        _ = ⁅z, w⁆ * (⁅w, ⁅z, y⁻¹⁆⁆ * ⁅z, y⁻¹⁆) := by rw [hconjw]
        _ = ⁅z, w⁆ * (⁅w, ⁅z, y⁻¹⁆⁆ * (⁅y⁻¹, ⁅z, y⁆⁻¹⁆ * ⁅z, y⁆⁻¹)) := by rw [hzyinv]
        _ = (⁅z, w⁆ * (⁅w, ⁅z, y⁻¹⁆⁆ * ⁅y⁻¹, ⁅z, y⁆⁻¹⁆)) * ⁅z, y⁆⁻¹ := by group
    have hprod : ⁅z, w⁆ * (⁅w, ⁅z, y⁻¹⁆⁆ * ⁅y⁻¹, ⁅z, y⁆⁻¹⁆) ∈ γ₄ :=
      γ₄.mul_mem hA (γ₄.mul_mem hB hC)
    have hsqeq : (⁅z, y⁆ : Γ) ^ 2 = ⁅z, w⁆ * (⁅w, ⁅z, y⁻¹⁆⁆ * ⁅y⁻¹, ⁅z, y⁆⁻¹⁆) := by
      have h := congrArg (· * ⁅z, y⁆) heq
      rw [sq, h]; group
    rw [hsqeq]; exact hprod
  have hcomm : ∀ z ∈ γ₂, ∀ y ∈ Y, ⁅z, y⁆ ∈ γ₄ := by
    intro z hz y hy
    have hmemγ₂ : ⁅z, y⁆ ∈ γ₂ := hγ₃γ₂ (by
      rw [hγ₃]; exact Subgroup.commutator_mem_commutator hz hy)
    have hmemY : ⁅z, y⁆ ∈ Y := hγ₂Y hmemγ₂
    have hsqzy : (⁅z, y⁆ : Γ) ^ 2 ∈ γ₄ := hsq z hz y hy
    obtain ⟨k, hk⟩ := (h.pgroup.to_le h.le).exists_pow_pow_eq_one ⟨⁅z, y⁆, hmemY⟩
    have hk' : (⁅z, y⁆ : Γ) ^ p ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hodd : Odd (p ^ k) := (h.prime.odd_of_ne_two h.odd).pow
    obtain ⟨m, hm⟩ := hodd
    have hx : ⁅z, y⁆ = ((⁅z, y⁆ : Γ) ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = p ^ k + 1 by omega, pow_succ, hk', one_mul]
    rw [hx]
    exact γ₄.pow_mem hsqzy (m + 1)
  have hγ₃γ₄ : γ₃ ≤ γ₄ := by
    rw [hγ₃, Subgroup.commutator_def, Subgroup.closure_le]
    rintro x ⟨z, hz, y, hy, rfl⟩
    exact hcomm z hz y hy
  have hγ₃eq : γ₃ = γ₄ := le_antisymm hγ₃γ₄ hγ₄γ₃
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hnil : Group.IsNilpotent ↥Y := (h.pgroup.to_le h.le).isNilpotent
  have hstep : ∀ n, Y.lowerCentralSeries (n + 2) = γ₃ := by
    intro n
    induction n with
    | zero =>
      show Y.lowerCentralSeries 2 = γ₃
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
        Subgroup.lowerCentralSeries_zero, ← hγ₂, ← hγ₃]
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Subgroup.lowerCentralSeries_succ, ih,
        ← hγ₄]
      exact hγ₃eq.symm
  obtain ⟨N, hN⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Y).mp hnil
  have hle : Y.lowerCentralSeries (N + 2) ≤ Y.lowerCentralSeries N :=
    Subgroup.lowerCentralSeries_antitone Y (by omega)
  rw [hstep N, hN] at hle
  exact le_bot_iff.mp hle

theorem w172_minInv_exp {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : ∀ y ∈ Y, y ^ p = 1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hInv : ∀ i ∈ W172Inv d Y, i ^ p = 1 := by
    intro i hi
    have hiY : i ∈ Y := hi.1
    have hii : d * i * d⁻¹ = i⁻¹ := hi.2
    have hfix : d * i ^ p * d⁻¹ = i ^ p := w172_minInv_pow_fixed h i hiY
    have hinv : d * i ^ p * d⁻¹ = (i ^ p)⁻¹ := by
      calc d * i ^ p * d⁻¹ = (d * i * d⁻¹) ^ p := by rw [conj_pow]
        _ = (i⁻¹) ^ p := by rw [hii]
        _ = (i ^ p)⁻¹ := by rw [inv_pow]
    have heq : i ^ p = (i ^ p)⁻¹ := hfix.symm.trans hinv
    have h2 : (i ^ p) ^ 2 = 1 := by
      rw [sq]
      exact (congrArg (fun x => i ^ p * x) heq).trans (mul_inv_cancel _)
    obtain ⟨k, hk⟩ := (h.pgroup.to_le h.le).exists_pow_pow_eq_one ⟨i, hiY⟩
    have hk' : i ^ p ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hodd : Odd (p ^ k) := (h.prime.odd_of_ne_two h.odd).pow
    have hdvd2 : orderOf (i ^ p) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hdvdp : orderOf (i ^ p) ∣ p ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, mul_comm, pow_mul, hk', one_pow]
    have hcop : Nat.Coprime 2 (p ^ k) := Nat.coprime_two_left.mpr hodd
    have hdvd1 : orderOf (i ^ p) ∣ 1 := by
      have := Nat.dvd_gcd hdvd2 hdvdp
      rwa [show Nat.gcd 2 (p ^ k) = 1 from hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hclosure : Subgroup.closure {y : Γ | y ∈ Y ∧ y ^ p = 1} = Y := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun y hy => hy.1
    · calc Y = Subgroup.closure (W172Inv d Y) := (w172_minInv_gen h).symm
        _ ≤ Subgroup.closure {y : Γ | y ∈ Y ∧ y ^ p = 1} :=
          Subgroup.closure_mono fun y hy => ⟨hy.1, hInv y hy⟩
  have hTmap : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [← MonoidHom.range_eq_map Y.subtype, Subgroup.range_subtype]
  have himg : Y.subtype '' {x : ↥Y | x ^ p = 1} = {y : Γ | y ∈ Y ∧ y ^ p = 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
    · rintro ⟨hy, hyp⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyp), rfl⟩
  have hgen : Subgroup.closure {x : ↥Y | x ^ p = 1} = ⊤ := by
    refine (Subgroup.map_subtype_inj (H := Y) (L := ⊤)).mp ?_
    rw [MonoidHom.map_closure, himg, hclosure, hTmap]
  have hcl : CFSG.Quasithin.ClassLeTwo (⊤ : Subgroup ↥Y) := by
    rw [CFSG.Quasithin.ClassLeTwo]
    refine (Subgroup.map_subtype_inj (H := Y) (L := ⊥)).mp ?_
    rw [Subgroup.map_bot, Subgroup.map_commutator, Subgroup.map_commutator, hTmap]
    exact w172_minInv_class_two h
  intro y hy
  have hpow : (⟨y, hy⟩ : ↥Y) ^ p = 1 :=
    CFSG.Quasithin.pow_eq_one_of_classLeTwo (P := ↥Y) h.odd hcl hgen ⟨y, hy⟩
  simpa using congrArg Subtype.val hpow

end CFSG.LocalAnalysis.WeakClosure81

end
