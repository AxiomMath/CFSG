module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_sup_of_ne {K H H' : Subgroup G} (hK : IsElemAbelian 2 K)
    (hH : H ≤ K) (hH' : H' ≤ K)
    (hmH : E3.mQuot K H = 1) (hmH' : E3.mQuot K H' = 1) (hne : H ≠ H') :
    H ⊔ H' = K := by
  have hKp : IsPGroup 2 K :=
    isPGroup_two_of_sq_eq_one fun v : K => Subtype.ext (by simpa using hK.2 v v.2)
  have hH2 : H.relIndex K = 2 := by
    rw [E3.relIndex_eq_two_pow hKp H, hmH, pow_one]
  have hH'2 : H'.relIndex K = 2 := by
    rw [E3.relIndex_eq_two_pow hKp H', hmH', pow_one]
  have hdvd : (H ⊔ H').relIndex K ∣ H.relIndex K :=
    Subgroup.relIndex_dvd_of_le_left (L := K) (le_sup_left : H ≤ H ⊔ H')
  rw [hH2] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact le_antisymm (sup_le hH hH') (Subgroup.relIndex_eq_one.1 h)
  · exfalso
    have hcard : ∀ E : Subgroup G, E ≤ K → E.relIndex K = 2 → Nat.card E * 2 = Nat.card K := by
      intro E hE hE2
      have h := Subgroup.relIndex_mul_card (H := E) (K := K)
      rw [inf_eq_left.mpr hE, hE2] at h
      rw [mul_comm]
      exact h
    have h1 : Nat.card (H ⊔ H' : Subgroup G) * 2 = Nat.card K := hcard _ (sup_le hH hH') h
    have h2 : Nat.card H * 2 = Nat.card K := hcard H hH hH2
    have h3 : Nat.card H' * 2 = Nat.card K := hcard H' hH' hH'2
    have e1 : H = H ⊔ H' :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : H ≤ H ⊔ H') (by
        have := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h1.trans h2.symm)
        exact this.le)
    have e2 : H' = H ⊔ H' :=
      Subgroup.eq_of_le_of_card_ge (le_sup_right : H' ≤ H ⊔ H') (by
        have := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h1.trans h3.symm)
        exact this.le)
    exact hne (e1.trans e2.symm)

theorem s16c167_twenty_uniq {A Vg J J' B B' : Subgroup G} {u u' : G}
    (hJ : J ≤ Vg) (hJ' : J' ≤ Vg) (hne : J ≠ J') (hsup : J ⊔ J' = Vg)
    (hJel : IsElemAbelian 2 J) (hJel' : IsElemAbelian 2 J')
    (hB : B ≤ A) (hB' : B' ≤ A)
    (hBu : Vg ⊓ centralizer ({u} : Set G) = B) (hBu' : Vg ⊓ centralizer ({u'} : Set G) = B')
    (hBs : B = (B ⊓ J) ⊔ (B ⊓ J')) (hBs' : B' = (B' ⊓ J) ⊔ (B' ⊓ J'))
    (hm : E3.mQuot J (B ⊓ J) = 1 ∧ E3.mQuot J' (B ⊓ J') = 1)
    (hm' : E3.mQuot J (B' ⊓ J) = 1 ∧ E3.mQuot J' (B' ⊓ J') = 1)
    (hX : ∀ K ∈ ({J, J'} : Set (Subgroup G)), ∃ x : G,
      conjSubgroup K x ∈ ({J, J'} : Set (Subgroup G)) ∧ conjSubgroup K x ≠ K ∧
        conjSubgroup (K ⊓ centralizer ({u} : Set G)) x =
          conjSubgroup K x ⊓ centralizer ({u} : Set G) ∧
        conjSubgroup (K ⊓ centralizer ({u'} : Set G)) x =
          conjSubgroup K x ⊓ centralizer ({u'} : Set G)) :
    B = B' ∨ Vg ≤ A := by
  by_cases hBB : B = B'
  · exact Or.inl hBB
  · refine Or.inr ?_
    have hmem : ∀ {K : Subgroup G}, K ∈ ({J, J'} : Set (Subgroup G)) → K = J ∨ K = J' := by
      intro K hK
      simpa using hK
    have hex : ∃ K ∈ ({J, J'} : Set (Subgroup G)), B ⊓ K ≠ B' ⊓ K := by
      by_contra h
      rw [not_exists] at h
      apply hBB
      have hJeq : B ⊓ J = B' ⊓ J := by
        by_contra hne'
        exact h J ⟨by simp, hne'⟩
      have hJ'eq : B ⊓ J' = B' ⊓ J' := by
        by_contra hne'
        exact h J' ⟨by simp, hne'⟩
      rw [hBs, hBs', hJeq, hJ'eq]
    obtain ⟨K, hK, hneqK⟩ := hex
    obtain ⟨x, hKx_mem, hKx_ne, hx_u, hx_u'⟩ := hX K hK
    set K' : Subgroup G := conjSubgroup K x with hK'def
    have hK'le : K' ≤ Vg := by
      rcases hmem hKx_mem with h | h
      · rw [h]; exact hJ
      · rw [h]; exact hJ'
    have hKle : K ≤ Vg := by
      rcases hmem hK with h | h
      · rw [h]; exact hJ
      · rw [h]; exact hJ'
    have hBK : B ⊓ K = K ⊓ centralizer ({u} : Set G) := by
      rw [← hBu, inf_assoc, inf_comm (centralizer ({u} : Set G)) K, ← inf_assoc,
        inf_eq_right.mpr hKle]
    have hB'K : B' ⊓ K = K ⊓ centralizer ({u'} : Set G) := by
      rw [← hBu', inf_assoc, inf_comm (centralizer ({u'} : Set G)) K, ← inf_assoc,
        inf_eq_right.mpr hKle]
    have hconjB : conjSubgroup (B ⊓ K) x = B ⊓ K' := by
      rw [hBK, hx_u, ← hBu]
      rw [inf_assoc, inf_comm (centralizer ({u} : Set G)) K', ← inf_assoc,
        inf_eq_right.mpr hK'le]
    have hconjB' : conjSubgroup (B' ⊓ K) x = B' ⊓ K' := by
      rw [hB'K, hx_u', ← hBu']
      rw [inf_assoc, inf_comm (centralizer ({u'} : Set G)) K', ← inf_assoc,
        inf_eq_right.mpr hK'le]
    have hneqK' : B ⊓ K' ≠ B' ⊓ K' := by
      intro heq
      apply hneqK
      have h1 : conjSubgroup (B ⊓ K) x = conjSubgroup (B' ⊓ K) x := by
        rw [hconjB, hconjB', heq]
      have h2 := congrArg (fun S : Subgroup G => conjSubgroup S x⁻¹) h1
      rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_conj_inv] at h2
    have hK'mem : K' ∈ ({J, J'} : Set (Subgroup G)) := hKx_mem
    have hK'ne : K' ≠ K := hKx_ne
    have helK : IsElemAbelian 2 K := by
      rcases hmem hK with h | h
      · rw [h]; exact hJel
      · rw [h]; exact hJel'
    have helK' : IsElemAbelian 2 K' := by
      rcases hmem hK'mem with h | h
      · rw [h]; exact hJel
      · rw [h]; exact hJel'
    have hmK : E3.mQuot K (B ⊓ K) = 1 := by
      rcases hmem hK with h | h
      · rw [h]; exact hm.1
      · rw [h]; exact hm.2
    have hm'K : E3.mQuot K (B' ⊓ K) = 1 := by
      rcases hmem hK with h | h
      · rw [h]; exact hm'.1
      · rw [h]; exact hm'.2
    have hmK' : E3.mQuot K' (B ⊓ K') = 1 := by
      rcases hmem hK'mem with h | h
      · rw [h]; exact hm.1
      · rw [h]; exact hm.2
    have hm'K' : E3.mQuot K' (B' ⊓ K') = 1 := by
      rcases hmem hK'mem with h | h
      · rw [h]; exact hm'.1
      · rw [h]; exact hm'.2
    have hsupK : (B ⊓ K) ⊔ (B' ⊓ K) = K :=
      s16c167_twenty_sup_of_ne helK inf_le_right inf_le_right hmK hm'K hneqK
    have hsupK' : (B ⊓ K') ⊔ (B' ⊓ K') = K' :=
      s16c167_twenty_sup_of_ne helK' inf_le_right inf_le_right hmK' hm'K' hneqK'
    have hKB : K ≤ B ⊔ B' := by
      rw [← hsupK]
      exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
    have hK'B : K' ≤ B ⊔ B' := by
      rw [← hsupK']
      exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
    have hKK'sup : K ⊔ K' = Vg := by
      rcases hmem hK with hKJ | hKJ'
      · rcases hmem hK'mem with hK'J | hK'J'
        · exact absurd (hK'J.trans hKJ.symm) hK'ne
        · rw [hKJ, hK'J', hsup]
      · rcases hmem hK'mem with hK'J | hK'J'
        · rw [hKJ', hK'J, sup_comm, hsup]
        · exact absurd (hK'J'.trans hKJ'.symm) hK'ne
    have hKKA : K ⊔ K' ≤ A := (sup_le hKB hK'B).trans (sup_le hB hB')
    exact hKK'sup ▸ hKKA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
