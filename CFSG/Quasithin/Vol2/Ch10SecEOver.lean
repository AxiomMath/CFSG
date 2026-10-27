module

public import CFSG.Quasithin.Vol2.Ch10SecE21A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_sup_of_le {A B C : Subgroup G} (hA : C ≤ Subgroup.normalizer (A : Set G))
    (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g ∈ C, (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
    intro g hg
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hA hg) a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hB hg) b).mp hb
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key g hg ⟨h, hh, rfl⟩
  · intro hh
    have h1 := key g⁻¹ (C.inv_mem hg) ⟨_, hh, rfl⟩
    have e : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) = h := by
      simp [mul_assoc]
    rwa [e] at h1

variable [Finite G] {T L I : Subgroup G}

theorem fsuVM_le_T0 (hyp : Hyp10 G T L I) : fsuVM T L I ≤ Ch10.T0 T L := by
  refine le_inf (SecA.fsuVM_le_T hyp) ?_
  rw [SecA.fsuVM_eq_commutator hyp.fsu]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((SecA.fsuVM_le_T hyp).trans (SecA.le_fsuM T L))

theorem isSylowTwoOf_sup_of_T0_le (hyp : Hyp10 G T L I) {R : Subgroup G}
    (h0 : Ch10.T0 T L ≤ R) (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    IsSylowTwoOf R (fsuL0 T L ⊔ R) := by
  have hTN : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := SecA.le_fsuM T L
  have hT : IsSylowTwoOf T (fsuL0 T L ⊔ T) :=
    ⟨le_sup_right, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow le_sup_right⟩
  have hnorm : fsuL0 T L ⊔ T ≤ Subgroup.normalizer ((fsuL0 T L ⊔ R : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) (le_normalizer_sup_of_le hTN hTR)
  have h := B6.isSylowTwoOf_inf_normal hT (sup_le_sup_left hRT _) hnorm
  have heq : T ⊓ (fsuL0 T L ⊔ R) = R := by
    refine le_antisymm (fun x hx => ?_) (le_inf hRT le_sup_right)
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (fsuL0 T L) R (hRT.trans hTN)
    have hx' : x ∈ ((fsuL0 T L : Set G) * (R : Set G)) := by
      rw [← hcoe]
      exact hx.2
    obtain ⟨a, ha, r, hr, rfl⟩ := Set.mem_mul.mp hx'
    have haT : a ∈ T := by
      have h1 := T.mul_mem hx.1 (T.inv_mem (hRT hr))
      simpa using h1
    exact R.mul_mem (h0 ⟨haT, ha⟩) hr
  rwa [heq] at h

theorem normalizer_le_fsuM_of_T0_le
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (hyp : Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) {R : Subgroup G}
    (h0 : Ch10.T0 T L ≤ R) (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ fsuM T L := by
  have hR : R ≠ ⊥ := fun h =>
    SecA.fsuVM_ne_bot hyp.fsu (le_bot_iff.mp (h ▸ (fsuVM_le_T0 hyp).trans h0))
  exact normalizer_le_fsuM_of_sylow h311 h331 h37 h38 hyp
    (exists_isUniqueMaxOver_L0T h37 h38 hshape hyp h12) hR hRT hTR
    (isSylowTwoOf_sup_of_T0_le hyp h0 hRT hTR)

theorem le_normalizer_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : T ≤ Subgroup.normalizer (Ch10.T1 T L : Set G) := by
  have hn : ((Ch10.T1 T L).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two (SecA.index_T1 h37 h38 hyp)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := hn.conj_mem ⟨y, hy.1⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hy
    have hyT : y ∈ T := by
      have h1 := T.mul_mem (T.mul_mem (T.inv_mem hx) hy.1) hx
      simpa [mul_assoc] using h1
    have h1 := hn.conj_mem ⟨x * y * x⁻¹, hy.1⟩ (Subgroup.mem_subgroupOf.mpr hy)
      ⟨x⁻¹, T.inv_mem hx⟩
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa [mul_assoc] using h2

theorem normalizer_T1_le
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (hyp : Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    Subgroup.normalizer (Ch10.T1 T L : Set G) ≤ fsuM T L :=
  normalizer_le_fsuM_of_T0_le h311 h331 h37 h38 hshape hyp h12
    (SecA.T0_le_T1 hyp.fsu.maximal.1) inf_le_left (le_normalizer_T1 h37 h38 hyp)

end CFSG.Quasithin.Vol2.Ch10.SecE
