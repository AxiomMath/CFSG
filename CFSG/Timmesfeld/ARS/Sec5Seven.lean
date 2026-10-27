module

public import CFSG.Timmesfeld.ARS.Sec3PlaneGroup
public import CFSG.Timmesfeld.ARS.Sec5Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem conjSub_M (hR : IsRootClass R) (X : Subgroup G) (g : G) :
    conjSub (M R X) g = M R (conjSub X g) := by
  have key : ∀ (Y : Subgroup G) (x : G), conjSub (M R Y) x ≤ M R (conjSub Y x) := by
    intro Y x
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ (iSup₂_le fun W hW => ?_)
    · rw [← Subgroup.map_le_iff_le_comap]
      exact QD.le_M_self
    · rw [← Subgroup.map_le_iff_le_comap]
      exact QD.le_M (conjSub_mem_lambdaSet hR hW x)
  refine le_antisymm (key X g) ?_
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (key (conjSub X g) g⁻¹)
  change conjSub (conjSub (M R (conjSub X g)) g⁻¹) g ≤
    conjSub (M R (conjSub (conjSub X g) g⁻¹)) g at h1
  rwa [Plane.conjSub_inv_conjSub, Plane.conjSub_conjSub_inv] at h1

theorem exists_swap (hR : IsRootClass R) {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R)
    (hAB : Opposite A B) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ w ∈ conjSub B a, w ≠ 1 ∧ w ∈ A ⊔ B ∧ conjSub A w = B ∧
      conjSub B w = A := by
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  obtain ⟨b, hb, hb1, hab⟩ := hAB.2.1 a ha ha1
  have ha2 : a * a = 1 := hR.mul_self A hA a ha
  have hb2 : b * b = 1 := hR.mul_self B hB b hb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  refine ⟨a, ha, ha1, a * b * a, ?_, ?_, ?_, ?_, ?_⟩
  · have := conj_mem_conjSub a hb
    rwa [hainv] at this
  · intro h1
    apply hb1
    calc b = a * (a * b * a) * a := by rw [← mul_assoc, ← mul_assoc, ha2, one_mul, mul_assoc,
          ha2, mul_one]
      _ = 1 := by rw [h1, mul_one, ha2]
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right hb)) (Subgroup.mem_sup_left ha)
  · rw [show a * b * a = a * (b * a) by group, conjSub_mul, conjSub_mul, conjSub_of_mem ha, hab,
      ← conjSub_mul B a a, ha2, conjSub_one]
  · rw [show a * b * a = a * (b * a) by group, conjSub_mul, conjSub_mul, ← hab,
      ← conjSub_mul A b b, hb2, conjSub_one, conjSub_of_mem ha]

section Seven

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
include hR hiso hnd hΩ

theorem centralizer_eq_bot_or_mem {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R)
    (hAB : Opposite A B) (hBC : C ∈ psiSet R B) (hAC : Commuting A C) {N W Z : Subgroup G}
    (hN : N = ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) (hW : W = C ⊔ N)
    (hZ : Z = W ⊓ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G)) :
    Z = ⊥ ∨ (Z ∈ R ∧ C ∈ lambdaSet R Z) := by
  have hCR : C ∈ R := hBC.1
  have hZ' : Z = (C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) ⊓
      Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by rw [hZ, hW, hN]
  obtain ⟨⟨hDl, hDp, -, hNx, -⟩, ⟨-, -, hWx, -, -, -, hNZ⟩, ⟨-, hFZ, -⟩⟩ :=
    natural_module_of_commuting hR hiso hA hB hAB hBC hAC hN hW hZ
  have hDR : ⁅B, C⁆ ∈ R := hDl.1.1
  have hER : ⁅A, ⁅B, C⁆⁆ ∈ R := hDp.2.1
  by_cases hZ0 : Z = ⊥
  · exact Or.inl hZ0
  right
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  have hZCE : Z ≤ C ⊔ ⁅A, ⁅B, C⁆⁆ := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Sec3.exists_eq_mul_inv_of_mem_centralizer hR hiso hA hB hAB hBC hAC
      hZ' ha hb hb1 hab hz
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.inv_mem _ (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator ha (Subgroup.commutator_mem_commutator hb hc))))
  have hEl : ⁅A, ⁅B, C⁆⁆ ∈ lambdaSet R A := mem_lambdaSet_comm hER
    (mem_lambdaSet_commutator hR hiso hA hDR hDp.2).1
  have hDlE : ⁅B, C⁆ ∈ lambdaSet R ⁅A, ⁅B, C⁆⁆ := (mem_lambdaSet_commutator hR hiso hA hDR hDp.2).2
  have hBE : ⁅B, ⁅A, ⁅B, C⁆⁆⁆ = ⁅B, C⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      exact Sec3.commutatorElement_mem_of_mem_sup hR hiso hB hA hAB.symm hDl hDp hx
        (Subgroup.mem_sup_right hy)
    · intro d hd
      obtain ⟨a', ha', -, hba'⟩ := hAB.symm.2.1 b hb hb1
      rw [← Sec3.commutatorElement_commutatorElement_eq hR hiso hB hA hAB.symm hDl hDp hb hb1 ha'
        hba' hd]
      exact Subgroup.commutator_mem_commutator hb (Subgroup.commutator_mem_commutator ha' hd)
  have hBEs : Special R B ⁅A, ⁅B, C⁆⁆ := by
    refine ⟨by rw [hBE]; exact hDR, ?_, ?_⟩
    · rw [hBE]
      exact hDl.1.2.2.symm
    · rw [hBE]
      exact hDlE.1.2.2.symm
  have hEψ : ⁅A, ⁅B, C⁆⁆ ∈ psiSet R B := ⟨hER, hBEs⟩
  obtain ⟨-, -, -, w, -, -, hwX, hAw, hBw⟩ := exists_swap hR hA hB hAB
  have hwN : conjSub N w = N := hNx w (Subgroup.mem_sup_left hwX)
  have hDw : conjSub ⁅B, C⁆ w = ⁅A, ⁅B, C⁆⁆ := by
    refine QD.eq_of_le_of_mem hR hiso (hR.conjSub_mem hDR w) hER fun x hx => ?_
    have hxN : x ∈ ⁅A, ⁅B, C⁆⁆ ⊔ ⁅B, ⁅A, ⁅B, C⁆⁆⁆ := by
      have h1 : x ∈ conjSub N w := Subgroup.map_mono (le_sup_left.trans hN.ge) hx
      rw [hwN, hN] at h1
      rw [hBE, sup_comm]
      exact h1
    refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hEl hEψ hxN fun a' ha' => ?_
    have h1 := hDl.1.2.2.conjSub w
    rw [hBw] at h1
    exact h1 a' ha' x hx
  have hMD : W ≤ M R ⁅B, C⁆ := by
    rw [hW, hN]
    exact sup_le (QD.le_M (mem_lambdaSet_commutator hR hiso hB hCR hBC.2).2)
      (sup_le QD.le_M_self (QD.le_M (mem_lambdaSet_comm hER hDlE)))
  have hME : W ≤ M R ⁅A, ⁅B, C⁆⁆ := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj w).toMonoidHom) hMD
    rwa [← conjSub, ← conjSub, hWx w (Subgroup.mem_sup_left hwX),
      conjSub_M hR, hDw] at h1
  have hZW : Z ≤ W := hZ.le.trans inf_le_left
  have hCE : C ≠ ⁅A, ⁅B, C⁆⁆ := by
    intro e
    apply hZ0
    have hWN : W = N := by
      rw [hW, e, hN]
      exact sup_eq_right.2 le_sup_right
    rw [eq_bot_iff, ← hNZ]
    exact le_inf (hWN ▸ hZW) le_rfl
  have hCl : C ∈ lambdaSet R ⁅A, ⁅B, C⁆⁆ := mem_lambdaSet_of_le_M hR hiso hnd hΩ hER hCR
    ((le_sup_left.trans hW.ge).trans hME) hCE
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ0
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨F, hF, hFle, hzF⟩ := hCl.2 z (by rw [sup_comm]; exact hZCE hz) hz1'
  have hFM : F ≤ W := hFle.trans (sup_le ((le_sup_right.trans hN.ge).trans
    (le_sup_right.trans hW.ge)) (le_sup_left.trans hW.ge))
  rcases hFZ F hF hFM with h | h
  · have : z ∈ F ⊓ Z := ⟨hzF, hz⟩
    rw [h, Subgroup.mem_bot] at this
    exact absurd this hz1'
  · subst h
    have hCZ : C ≠ F := by
      intro e
      apply hBC.2.not_commuting hR
      intro x hx y hy
      have hy' : y ∈ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) :=
        (hZ.le (e ▸ hy)).2
      exact Subgroup.mem_centralizer_iff.1 hy' x
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
    exact ⟨hF, mem_lambdaSet_comm hCR (mem_lambdaSet_of_le_sup hR hiso hER hCl hCR le_sup_right hF
      hFle hCZ).1⟩

end Seven

end Sec5

end CFSG.Timmesfeld.ARS
