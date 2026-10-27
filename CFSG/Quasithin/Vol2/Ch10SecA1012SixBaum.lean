module

public import CFSG.Quasithin.Vol2.Ch10SecA1012SixE23
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem card_conjAut {V : Type*} [CommGroup V] (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card ↥(B1.conjAut g A) = Nat.card ↥A := by
  have hf : ∀ a : ↥A, g * (a : MulAut V) * g⁻¹ ∈ B1.conjAut g A := fun a =>
    B1.mem_conjAut.mpr (by simp [mul_assoc])
  let e : ↥A ≃ ↥(B1.conjAut g A) :=
    { toFun := fun a => ⟨g * (a : MulAut V) * g⁻¹, hf a⟩
      invFun := fun x => ⟨g⁻¹ * (x : MulAut V) * g, B1.mem_conjAut.mp x.2⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  exact (Nat.card_congr e).symm

theorem two_pow_mul_ne_120 (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 120 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h64 : 64 ≤ 4 ^ n := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have : 63 ≤ 4 ^ n - 1 := by omega
    nlinarith

section Module

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}

theorem card_of_isL2Natural {C : Subgroup W} {n : ℕ} (h : E2.IsL2Natural L C n) :
    Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  rw [Nat.card_congr e.toEquiv, card_SL_two_pow (by rw [Nat.card_eq_fintype_card, hF])]

theorem card_of_isA5Module (h : E2.IsA5Module L) : Nat.card ↥L = 120 := by
  obtain ⟨θ, -⟩ := h
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

end Module

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem autI_baum_eq_of_e23Concl {H T V : Subgroup Γ} {hV : IsElemAbelian 2 V}
    (hE : E2.E23Concl H T V hV) : autI hV (baum T) = autI hV (thompsonJ T) := by
  obtain ⟨-, I, -, -, -, -, hconj, htype, -, -, h2, h3⟩ := hE
  by_cases hall : ∀ L ∈ I, ∃ n, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n
  · exact (h2 hall).1
  · push Not at hall
    obtain ⟨L₀, hL₀, hnot⟩ := hall
    have hA5 : E2.IsA5Module L₀ :=
      (htype L₀ hL₀).resolve_left fun ⟨n, hn⟩ => hnot n hn
    refine (h3 fun L' hL' => ?_).1
    obtain ⟨t, -, ht⟩ := hconj L₀ hL₀ L' hL'
    have hc : Nat.card ↥L' = 120 := by rw [← ht, card_conjAut, card_of_isA5Module hA5]
    rcases htype L' hL' with ⟨n, hn⟩ | h
    · exact absurd ((card_of_isL2Natural hn).symm.trans hc) (two_pow_mul_ne_120 n)
    · exact h

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem baum_le_T1
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4)
    (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight) (hyp : Ch10.Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    baum T ≤ Ch10.T1 T L := by
  have hel := isElemAbelian_fsuVM hyp
  have heq := autI_baum_eq_of_e23Concl (e23Concl_L0T he23 h37 h38 hshape h3228 hyp h12 hJ)
  have hJT1 := thompsonJ_le_T1 h37 h38 h322 h154 hyp
  have hCT1 := inf_centralizer_le_T1 h37 h38 hyp
  intro s hs
  have hsT : s ∈ T := hs.1
  have hsN : s ∈ Subgroup.normalizer (fsuVM T L I : Set G) := le_normalizer_fsuVM T L I hsT
  have hmem : convI hel ⟨s, hsN⟩ ∈ autI hel (thompsonJ T) := heq ▸ convI_mem_autI hel hs hsN
  obtain ⟨g, hgJ, hge⟩ := (mem_autI hel).mp hmem
  have hk : convI hel (g⁻¹ * ⟨s, hsN⟩) = 1 := by
    rw [map_mul, map_inv, hge, inv_mul_cancel]
  rw [convI_eq_one_iff] at hk
  have hgT : (g : G) ∈ T := thompsonJ_le_self T hgJ
  have h1 : (g : G)⁻¹ * s ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) :=
    ⟨T.mul_mem (T.inv_mem hgT) hsT, hk⟩
  have := (Ch10.T1 T L).mul_mem (hJT1 hgJ) (hCT1 h1)
  simpa using this

end CFSG.Quasithin.Vol2.Ch10.SecA
