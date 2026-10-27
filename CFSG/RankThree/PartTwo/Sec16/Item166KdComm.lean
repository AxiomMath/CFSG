module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open Subgroup CFSG.LocalAnalysis.EvenBN.Tits.N

open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

private lemma mem_centralizerMod_of_mem_X {O X Ob J : Subgroup G}
    (hNOb : O ⊔ X ≤ Subgroup.normalizer (Ob : Set G))
    {s : G} (hs : s ∈ X) (hsJ : ∀ l ∈ J, ⁅s, l⁆ ∈ Ob) :
    s ∈ centralizerMod (O ⊔ X) Ob J := by
  refine ⟨Subgroup.mem_sup_right hs, hNOb (Subgroup.mem_sup_right hs), fun l hl => ?_⟩
  exact hsJ l hl

private lemma mem_centralizerMod_of_mem_O {O X Ob J : Subgroup G}
    (hNOb : O ⊔ X ≤ Subgroup.normalizer (Ob : Set G))
    (hOOb : O ≤ Ob) (hJX : J ≤ X) {n : G} (hn : n ∈ O) :
    n ∈ centralizerMod (O ⊔ X) Ob J := by
  have hnOb : n ∈ Ob := hOOb hn
  have hnK : n ∈ O ⊔ X := Subgroup.mem_sup_left hn
  refine ⟨hnK, hNOb hnK, fun l hl => ?_⟩
  have hlN : l ∈ Subgroup.normalizer (Ob : Set G) :=
    hNOb (Subgroup.mem_sup_right (hJX hl))
  have h2 : l * n⁻¹ * l⁻¹ ∈ Ob :=
    (Subgroup.mem_normalizer_iff.mp hlN n⁻¹).1 (Ob.inv_mem hnOb)
  simpa [commutatorElement_def, mul_assoc] using Ob.mul_mem hnOb h2

private lemma exists_mem_J_mem_centralizerMod {O X Ob J : Subgroup G}
    (hOX : O ≤ Subgroup.normalizer (X : Set G))
    (hNOb : O ⊔ X ≤ Subgroup.normalizer (Ob : Set G))
    (hOOb : O ≤ Ob) (hJX : J ≤ X)
    (hsupp : ∀ x ∈ X, ∃ j ∈ J, ∃ s ∈ X, x = j * s ∧ ∀ l ∈ J, ⁅s, l⁆ ∈ Ob)
    {h : G} (hh : h ∈ O ⊔ X) :
    ∃ j ∈ J, ∃ t ∈ centralizerMod (O ⊔ X) Ob J, h = j * t := by
  have hh' : h ∈ (X : Set G) * (O : Set G) := by
    have hh'' := hh
    rw [sup_comm] at hh''
    change h ∈ ((X ⊔ O : Subgroup G) : Set G) at hh''
    rwa [Subgroup.coe_mul_of_right_le_normalizer_left X O hOX] at hh''
  obtain ⟨x, hx, n, hn, hxn⟩ := Set.mem_mul.mp hh'
  obtain ⟨j, hj, s, hs, rfl, hsJ⟩ := hsupp x hx
  refine ⟨j, hj, s * n, ?_, ?_⟩
  · exact (centralizerMod (O ⊔ X) Ob J).mul_mem
      (mem_centralizerMod_of_mem_X hNOb hs hsJ)
      (mem_centralizerMod_of_mem_O hNOb hOOb hJX hn)
  · rw [← hxn]
    group

private lemma conj_mem_centralizerMod_of_mem_Z {O X Ob J Z : Subgroup G}
    (hZN : Z ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G))
    (hZOb : Z ≤ Subgroup.normalizer (Ob : Set G))
    (hJZ : J ≤ Subgroup.centralizer (Z : Set G))
    {z : G} (hz : z ∈ Z) {g : G}
    (hg : g ∈ centralizerMod (O ⊔ X) Ob J) :
    z * g * z⁻¹ ∈ centralizerMod (O ⊔ X) Ob J := by
  obtain ⟨hgK, hgN, hgJ⟩ := hg
  have hzN : z ∈ Subgroup.normalizer (Ob : Set G) := hZOb hz
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hZN hz) g).1 hgK
  · exact (Subgroup.normalizer (Ob : Set G)).mul_mem
      ((Subgroup.normalizer (Ob : Set G)).mul_mem hzN hgN)
      ((Subgroup.normalizer (Ob : Set G)).inv_mem hzN)
  · intro l hl
    have hzl : z⁻¹ * l * z = l := by
      have hcomm : l * z = z * l :=
        ((Subgroup.mem_centralizer_iff.mp (hJZ hl)) z hz).symm
      calc z⁻¹ * l * z = z⁻¹ * (l * z) := by group
        _ = z⁻¹ * (z * l) := by rw [hcomm]
        _ = l := by group
    have hconj := conjugate_commutatorElement (g₁ := g) (g₂ := z⁻¹ * l * z) (g₃ := z)
    have e : z * (z⁻¹ * l * z) * z⁻¹ = l := by group
    rw [e] at hconj
    change ⁅z * g * z⁻¹, l⁆ ∈ Ob
    rw [← hconj, hzl]
    exact (Subgroup.mem_normalizer_iff.mp hzN ⁅g, l⁆).1 (hgJ l hl)

private lemma conj_mem_centralizerMod_of_mem_J {O X Ob J : Subgroup G}
    (hNOb : O ⊔ X ≤ Subgroup.normalizer (Ob : Set G))
    (hJX : J ≤ X) {j : G} (hj : j ∈ J) {g : G}
    (hg : g ∈ centralizerMod (O ⊔ X) Ob J) :
    j * g * j⁻¹ ∈ centralizerMod (O ⊔ X) Ob J := by
  have hJN : J ≤ Subgroup.normalizer (Ob : Set G) :=
    fun l hl => hNOb (Subgroup.mem_sup_right (hJX hl))
  obtain ⟨hgK, hgN, hgJ⟩ := hg
  have hjK : j ∈ O ⊔ X := Subgroup.mem_sup_right (hJX hj)
  refine ⟨?_, ?_, ?_⟩
  · exact (O ⊔ X).mul_mem ((O ⊔ X).mul_mem hjK hgK) ((O ⊔ X).inv_mem hjK)
  · exact (Subgroup.normalizer (Ob : Set G)).mul_mem
      ((Subgroup.normalizer (Ob : Set G)).mul_mem (hJN hj) hgN)
      ((Subgroup.normalizer (Ob : Set G)).inv_mem (hJN hj))
  · intro l hl
    have hcomm : ⁅g, j⁻¹ * l * j⁆ ∈ Ob :=
      hgJ _ (J.mul_mem (J.mul_mem (J.inv_mem hj) hl) hj)
    have hconj := conjugate_commutatorElement (g₁ := g) (g₂ := j⁻¹ * l * j) (g₃ := j)
    have e : j * (j⁻¹ * l * j) * j⁻¹ = l := by group
    rw [e] at hconj
    change ⁅j * g * j⁻¹, l⁆ ∈ Ob
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hJN hj) ⁅g, j⁻¹ * l * j⁆).1 hcomm

private lemma commutator_centralizerMod_le {O X Ob J : Subgroup G}
    (hOX : O ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X) :
    ⁅centralizerMod (O ⊔ X) Ob J, J⁆ ≤ X ⊓ Ob := by
  rw [Subgroup.commutator_le]
  intro t ht l hl
  obtain ⟨htK, -, htJ⟩ := ht
  have hN : O ⊔ X ≤ Subgroup.normalizer (X : Set G) :=
    sup_le hOX Subgroup.le_normalizer
  have htNX : t ∈ Subgroup.normalizer (X : Set G) := hN htK
  refine ⟨?_, htJ l hl⟩
  rw [commutatorElement_def]
  exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp htNX l).1 (hJX hl))
    (X.inv_mem (hJX hl))

theorem commutator_commutator_le_of_supplement {U W O X Ob J Z : Subgroup G}
    (hU : U ≤ O ⊔ W ⊔ X)
    (hWN : W ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G))
    (hWZ : W ≤ Subgroup.centralizer (Z : Set G))
    (hZN : Z ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G))
    (hZOb : Z ≤ Subgroup.normalizer (Ob : Set G))
    (hNOb : O ⊔ X ≤ Subgroup.normalizer (Ob : Set G))
    (hOX : O ≤ Subgroup.normalizer (X : Set G)) (hOOb : O ≤ Ob)
    (hJX : J ≤ X) (hJZ : J ≤ Subgroup.centralizer (Z : Set G))
    (hsupp : ∀ x ∈ X, ∃ j ∈ J, ∃ s ∈ X, x = j * s ∧ ∀ l ∈ J, ⁅s, l⁆ ∈ Ob) :
    ⁅⁅U, Z⁆, J⁆ ≤ X ⊓ Ob := by
  have hUZ : ⁅U, Z⁆ ≤ centralizerMod (O ⊔ X) Ob J := by
    rw [Subgroup.commutator_le]
    intro u hu z hz
    have hsup : O ⊔ W ⊔ X = (O ⊔ X) ⊔ W := by ac_rfl
    have huK : u ∈ O ⊔ W ⊔ X := hU hu
    have hu' : u ∈ (O ⊔ X) ⊔ W := by rwa [hsup] at huK
    have hu'' : u ∈ ((O ⊔ X : Subgroup G) : Set G) * (W : Set G) := by
      have h := hu'
      change u ∈ (((O ⊔ X) ⊔ W : Subgroup G) : Set G) at h
      rwa [Subgroup.coe_mul_of_right_le_normalizer_left (O ⊔ X) W hWN] at h
    obtain ⟨h, hh, w, hw, huw⟩ := Set.mem_mul.mp hu''
    obtain ⟨j, hj, t, ht, hjt⟩ :=
      exists_mem_J_mem_centralizerMod hOX hNOb hOOb hJX hsupp hh
    have hwz : ⁅w, z⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr
        ((Subgroup.mem_centralizer_iff.mp (hWZ hw)) z hz).symm
    have hjz : ⁅j, z⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr
        ((Subgroup.mem_centralizer_iff.mp (hJZ hj)) z hz).symm
    have htz : ⁅t, z⁆ ∈ centralizerMod (O ⊔ X) Ob J := by
      have h1 : z * t⁻¹ * z⁻¹ ∈ centralizerMod (O ⊔ X) Ob J :=
        conj_mem_centralizerMod_of_mem_Z hZN hZOb hJZ hz
          ((centralizerMod (O ⊔ X) Ob J).inv_mem ht)
      have e : ⁅t, z⁆ = t * (z * t⁻¹ * z⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (centralizerMod (O ⊔ X) Ob J).mul_mem ht h1
    have hmem : j * ⁅t, z⁆ * j⁻¹ ∈ centralizerMod (O ⊔ X) Ob J :=
      conj_mem_centralizerMod_of_mem_J hNOb hJX hj htz
    rw [← huw, commutatorElement_mul_left_eq_conj_mul, hwz, hjt,
      commutatorElement_mul_left_eq_conj_mul, hjz]
    simpa [mul_assoc] using hmem
  have hTJ : ⁅centralizerMod (O ⊔ X) Ob J, J⁆ ≤ X ⊓ Ob :=
    commutator_centralizerMod_le hOX hJX
  exact (Subgroup.commutator_mono hUZ le_rfl).trans hTJ

end CFSG.RankThree.PartTwo.Sec16.Kd166
