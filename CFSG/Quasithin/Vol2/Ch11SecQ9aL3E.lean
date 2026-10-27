module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {F : Type} [Field F]

abbrev PGL3 (F : Type) [Field F] : Type := Matrix.ProjGenLinGroup (Fin 3) F

@[expose] noncomputable def thetaP (F : Type) [Field F] : projectiveSL 3 F →* PGL3 F :=
  QuotientGroup.lift (scalars 3 F) SpecialLinearGroup.toPGL
    ((scalars_eq_center 3 F).trans SpecialLinearGroup.toPGL_ker.symm).le

theorem thetaP_proj (A : SpecialLinearGroup (Fin 3) F) :
    thetaP F (proj 3 F A) = ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) := rfl

theorem thetaP_injective : Function.Injective (thetaP F) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    ((scalars_eq_center 3 F).trans SpecialLinearGroup.toPGL_ker.symm)

noncomputable abbrev S0P (F : Type) [Field F] : Subgroup (PGL3 F) :=
  (projUnitriangular 3 F).map (thetaP F)

noncomputable abbrev Ptheta (F : Type) [Field F] (j : Fin 2) : Subgroup (PGL3 F) :=
  (parab34 F j).map (thetaP F)

theorem mk_mem_range_thetaP {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F).det = 1) :
    ProjGenLinGroup.mk g ∈ (thetaP F).range := by
  let A : SpecialLinearGroup (Fin 3) F := ⟨g, hg⟩
  have hA : SpecialLinearGroup.toGL A = g := Units.ext rfl
  exact ⟨proj 3 F A, (thetaP_proj A).trans (congrArg _ hA)⟩

variable [Finite F]

omit [Finite F] in
theorem pow_three_mem_range (hF : Nat.card F = 4) (x : PGL3 F) : x ^ 3 ∈ (thetaP F).range := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [← map_pow]
  apply mk_mem_range_thetaP
  have h3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have h1 : GeneralLinearGroup.det g ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := GeneralLinearGroup.det g)
    rwa [h3] at h
  rw [← GeneralLinearGroup.val_det_apply, map_pow, h1, Units.val_one]

omit [Finite F] in
theorem le_range_of_isPGroup (hF : Nat.card F = 4) {S : Subgroup (PGL3 F)} (hS : IsPGroup 2 S) :
    S ≤ (thetaP F).range := by
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hco : Nat.Coprime 3 (orderOf s) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    rw [hj]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
  rw [← hm]
  exact Subgroup.pow_mem _ (pow_three_mem_range hF s) m

omit [Finite F] in
theorem commutator_le_range : ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ ≤
    (thetaP F).range := by
  rw [Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective y
  rw [← map_commutatorElement]
  apply mk_mem_range_thetaP
  have h1 : GeneralLinearGroup.det ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [← GeneralLinearGroup.val_det_apply, h1, Units.val_one]

theorem range_thetaP_eq [CharP F 2] (hF : Nat.card F = 4) :
    (thetaP F).range = ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ := by
  refine le_antisymm ?_ commutator_le_range
  rw [MonoidHom.range_eq_map, ← commutator_top_projectiveSL hF, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

theorem exists_conj_S0P [CharP F 2] (hF : Nat.card F = 4) {S : Subgroup (PGL3 F)}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ c : PGL3 F, S = (S0P F).map (MulAut.conj c).toMonoidHom := by
  have hle := le_range_of_isPGroup hF hS.2.1
  have hS'map : (S.comap (thetaP F)).map (thetaP F) = S := Subgroup.map_comap_eq_self hle
  have hS' : QuasithinUnique.IsSylowTwoOf (S.comap (thetaP F)) ⊤ := by
    refine ⟨le_top, hS.2.1.comap_of_injective _ thetaP_injective, ?_⟩
    rw [show ((S.comap (thetaP F)).subgroupOf ⊤).index = (S.comap (thetaP F)).index from
      Subgroup.relIndex_top_right _, Subgroup.index_comap]
    intro h2
    apply hS.2.2
    rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _]
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le hle)
  obtain ⟨g, hg⟩ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf isSylowTwoOf_projU hS'
  refine ⟨thetaP F g, ?_⟩
  rw [← hS'map, ← hg, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
