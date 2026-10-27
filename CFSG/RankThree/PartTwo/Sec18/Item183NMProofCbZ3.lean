module

public import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item183NMProof

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_eq_card_map_mul_card_inf_ker {R Q : Type*} [Group R] [Group Q] (φ : R →* Q)
    (K : Subgroup R) : Nat.card K = Nat.card (K.map φ) * Nat.card (K ⊓ φ.ker : Subgroup R) := by
  let ψ : K →* Q := φ.comp K.subtype
  have hrange : ψ.range = K.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (K ⊓ φ.ker : Subgroup R) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : K) : R), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

variable {Y : Type} [Group Y] [Finite Y] {k : Type} [Field k] {X : Subgroup Y}

theorem exists_conj_not_mem_of_prod (hk : Nat.card k = 4)
    (e : X ≃* Multiplicative (ZMod 3) × projectiveSL 3 k) {B D : Subgroup Y}
    (hB27 : Nat.card B = 27) (hBX : B ≤ X) (hDB : D ≤ B) (hD3 : Nat.card D = 3)
    (hD : ¬ D ≤ Subgroup.centralizer ((KFacts.KS18.inrY e).range : Set Y)) :
    ∃ w ∈ (KFacts.KS18.inrY e).range, (∀ β ∈ B, w * β * w⁻¹ ∈ B) ∧
      ∃ x ∈ D, w * x * w⁻¹ ∉ D := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  set q : X →* projectiveSL 3 k := (MonoidHom.snd _ _).comp e.toMonoidHom with hqdef
  have hq : ∀ x : X, q x = (e x).2 := fun x => rfl
  have hqsurj : Function.Surjective q := fun p => ⟨e.symm (1, p), by rw [hq]; simp⟩
  have hker : ∀ x : X, x ∈ q.ker → (x : Y) ∈ (KFacts.KS18.inlY e).range := by
    intro x hx
    rw [MonoidHom.mem_ker, hq] at hx
    refine ⟨(e x).1, ?_⟩
    rw [KFacts.KS18.inlY_apply]
    congr 1
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact Prod.ext rfl hx.symm
  have hXcard : Nat.card X = 3 * Nat.card (projectiveSL 3 k) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Multiplicative _),
      Fintype.card_multiplicative, ZMod.card]
  have hkercard : Nat.card q.ker = 3 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hqsurj
    rw [hXcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  set B' := B.subgroupOf X with hB'def
  set D' := D.subgroupOf X with hD'def
  have hB'27 : Nat.card B' = 27 := by
    rw [← hB27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  set E := B'.map q with hEdef
  have h1 : Nat.card B' = Nat.card E * Nat.card (B' ⊓ q.ker : Subgroup X) :=
    card_eq_card_map_mul_card_inf_ker q B'
  rw [hB'27] at h1
  have hEdvd : Nat.card E ∣ 9 := by
    have h2 : Nat.card E ∣ 27 := ⟨_, h1⟩
    have h3 : Nat.card E ∣ 20160 := by
      rw [← KFacts.L34.card_projectiveSL hk]
      exact Subgroup.card_subgroup_dvd_card E
    have h4 := Nat.dvd_gcd h2 h3
    rwa [show Nat.gcd 27 20160 = 9 by norm_num] at h4
  have hK3 : Nat.card (B' ⊓ q.ker : Subgroup X) ≤ 3 :=
    (Subgroup.card_le_of_le inf_le_right).trans hkercard.le
  have hE9 : Nat.card E = 9 ∧ Nat.card (B' ⊓ q.ker : Subgroup X) = 3 := by
    have hEle : Nat.card E ≤ 9 := Nat.le_of_dvd (by norm_num) hEdvd
    rcases Nat.lt_or_ge (Nat.card E) 9 with hlt | hge
    · exfalso
      have : Nat.card E * Nat.card (B' ⊓ q.ker : Subgroup X) ≤ 8 * 3 :=
        Nat.mul_le_mul (by omega) hK3
      omega
    · have hE : Nat.card E = 9 := le_antisymm hEle hge
      rw [hE] at h1
      exact ⟨hE, by omega⟩
  have hkerB : q.ker ≤ B' := by
    have heq : B' ⊓ q.ker = q.ker :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hE9.2, hkercard])
    rw [← heq]
    exact inf_le_left
  have hBE : ∀ x : X, q x ∈ E → x ∈ B' := by
    rintro x ⟨y, hy, hyx⟩
    have hyx' : y⁻¹ * x ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have := B'.mul_mem hy (hkerB hyx')
    rwa [mul_inv_cancel_left] at this
  have hD'K : Nat.card (D' ⊓ q.ker : Subgroup X) = 1 := by
    have hD'3 : Nat.card D' = 3 := by
      rw [← hD3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDB.trans hBX)).toEquiv
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : D' ⊓ q.ker ≤ D')
    rw [hD'3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : D' ⊓ q.ker = D' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hD'3])
      apply hD
      intro d hd
      have hdX : d ∈ X := hBX (hDB hd)
      have hdK : (⟨d, hdX⟩ : X) ∈ q.ker := by
        have : (⟨d, hdX⟩ : X) ∈ D' ⊓ q.ker := by
          rw [heq]
          exact Subgroup.mem_subgroupOf.mpr hd
        exact this.2
      obtain ⟨z, hz⟩ := hker _ hdK
      have hz' : KFacts.KS18.inlY e z = d := hz
      rw [← hz']
      exact KFacts.KS18.inlY_mem_centralizer e z
  set D'' := D'.map q with hD''def
  have hD''3 : Nat.card D'' = 3 := by
    have h2 : Nat.card D' = Nat.card D'' * Nat.card (D' ⊓ q.ker : Subgroup X) :=
      card_eq_card_map_mul_card_inf_ker q D'
    rw [hD'K, mul_one] at h2
    rw [← h2, ← hD3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDB.trans hBX)).toEquiv
  have hD''E : D'' ≤ E := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDB (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨n, hn, x, hx, hxn⟩ :=
    KFacts.L34.exists_mem_normalizer_conj_not_mem hk hE9.1 hD''E hD''3
  set g : X := e.symm (1, n) with hgdef
  have hqg : q g = n := by rw [hq, hgdef, MulEquiv.apply_symm_apply]
  have hw : KFacts.KS18.inrY e n = (g : Y) := KFacts.KS18.inrY_apply e n
  refine ⟨KFacts.KS18.inrY e n, ⟨n, rfl⟩, ?_, ?_⟩
  · intro β hβ
    have hβX : β ∈ X := hBX hβ
    have hmem : g * ⟨β, hβX⟩ * g⁻¹ ∈ B' := by
      refine hBE _ ?_
      rw [map_mul, map_mul, map_inv, hqg]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp ⟨⟨β, hβX⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩
    rw [hw]
    exact Subgroup.mem_subgroupOf.mp hmem
  · obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨x', Subgroup.mem_subgroupOf.mp hx', fun hmem => hxn ?_⟩
    rw [hw] at hmem
    have hmem' : g * x' * g⁻¹ ∈ D' := Subgroup.mem_subgroupOf.mpr hmem
    have h2 : q (g * x' * g⁻¹) ∈ D'' := ⟨_, hmem', rfl⟩
    rwa [map_mul, map_mul, map_inv, hqg] at h2

end CFSG.RankThree.PartTwo.Sec18.Item183NMProof
