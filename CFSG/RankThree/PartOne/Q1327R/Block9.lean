module

public import CFSG.RankThree.PartOne.Q1327R.KEq
public import CFSG.RankThree.PartOne.Q1327R.Frame9

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  have h1 : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
    Subgroup.map_center_eq e
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center B := by
    rw [← h1]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (e.injective (hx'.trans (map_one e).symm))

namespace U4Frame

variable {G : Type} [Group G] {p f : ℕ} {K : Type} [Field K] {X F : Subgroup G}
  (C : U4Frame p f K X F)

@[expose] noncomputable def blkG {a b : Fin 4} (hab : a ≠ b) : Subgroup G :=
  ((blk C.hU hab).subgroupOf (unitarySU 2 f K 4)).map C.phi

theorem blkG_le_X {a b : Fin 4} (hab : a ≠ b) : C.blkG hab ≤ X := by
  rintro _ ⟨g, -, rfl⟩
  exact C.phi_mem_X g

noncomputable def blkGEquiv {a b : Fin 4} (hab : a ≠ b) : ↥(C.blkG hab) ≃* ↥(blk C.hU hab) :=
  (Subgroup.equivMapOfInjective _ C.phi C.phi_injective).symm.trans
    (Subgroup.subgroupOfEquivOfLe (blk_le_unitarySU hab))

structure Refl (C : U4Frame p f K X F) where
  w : G
  hwF : w ∈ Subgroup.normalizer (F : Set G)
  g : unitarySU 2 f K 4
  hg : C.phi g = w
  a : Fin 4
  b : Fin 4
  hab : a ≠ b
  hτ : NormPerm p (g : GL (Fin 4) K) (Equiv.swap a b)

namespace Refl

variable {C} (R : C.Refl)

@[expose] def t : MulAut F := F.normalizerMonoidHom ⟨R.w, R.hwF⟩

theorem coe_t_apply (e : F) : ((R.t e : F) : G) = R.w * e * R.w⁻¹ := rfl

theorem conj_phi (x : unitarySU 2 f K 4) :
    R.w * C.phi x * R.w⁻¹ = C.phi (R.g * x * R.g⁻¹) := by
  rw [← R.hg]
  exact C.conj_phi R.g x

theorem mem_fixed_iff {e : G} : e ∈ autFixedInG F R.t ↔ ∃ _ : e ∈ F, R.w * e * R.w⁻¹ = e := by
  unfold autFixedInG autFixed
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨e', he', rfl⟩
    refine ⟨e'.2, ?_⟩
    have hfix : R.t e' = e' := he'
    exact congrArg Subtype.val hfix
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, Subtype.ext h, rfl⟩

theorem phi_mem_fixed_iff {x : unitarySU 2 f K 4} (hx : (x : GL (Fin 4) K) ∈ torusSU p 4 K) :
    C.phi x ∈ autFixedInG F R.t ↔
      ent (x : GL (Fin 4) K) R.a R.a = ent (x : GL (Fin 4) K) R.b R.b := by
  rw [mem_fixed_iff]
  constructor
  · rintro ⟨-, h⟩
    rw [R.conj_phi] at h
    have h2 : R.g * x * R.g⁻¹ = x := C.phi_injective h
    have h3 := R.hτ.2 (x : GL (Fin 4) K) hx R.a
    have h4 : ((R.g * x * R.g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) = (x : GL (Fin 4) K) :=
      congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    rw [h4, Equiv.swap_apply_left] at h3
    exact h3.symm
  · intro h
    refine ⟨C.phi_mem_F_of_torus hx, ?_⟩
    rw [R.conj_phi]
    have h2 : R.g * x * R.g⁻¹ = x := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine R.hτ.conj_eq hx hx fun m => ?_
      by_cases hma : m = R.a
      · subst hma
        rw [Equiv.symm_swap, Equiv.swap_apply_left]
        exact h
      · by_cases hmb : m = R.b
        · subst hmb
          rw [Equiv.symm_swap, Equiv.swap_apply_right]
          exact h.symm
        · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hma hmb]
    rw [h2]

theorem exists_diag_of_fixed {x : unitarySU 2 f K 4} (hx : (x : GL (Fin 4) K) ∈ torusSU p 4 K)
    (hxab : ent (x : GL (Fin 4) K) R.a R.a = ent (x : GL (Fin 4) K) R.b R.b) :
    ∃ v : Fin 4 → Kˣ, (x : GL (Fin 4) K) = diagU v ∧ v R.a = v R.b := by
  obtain ⟨v, -, -, hv⟩ := mem_torusSU_iff.mp hx
  refine ⟨v, hv.symm, ?_⟩
  rw [← hv] at hxab
  simp only [ent, diagU_val, Matrix.diagonal_apply_eq] at hxab
  exact Units.ext hxab

theorem blkG_le_centralizer :
    C.blkG R.hab ≤ Subgroup.centralizer (autFixedInG F R.t : Set G) := by
  rintro _ ⟨h', hh', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨huF, -⟩ := R.mem_fixed_iff.mp hu
  obtain ⟨x, hx, rfl⟩ := C.exists_decomp huF
  have hxab := (R.phi_mem_fixed_iff hx).mp hu
  obtain ⟨v, hvx, hvab⟩ := R.exists_diag_of_fixed hx hxab
  have hh'b : (h' : GL (Fin 4) K) ∈ blk C.hU R.hab := hh'
  have hcomm : x * h' = h' * x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hvx]
    exact (blk_comm_diagU R.hab hvab hh'b).symm
  rw [← map_mul, ← map_mul, hcomm]

theorem blkG_normalized :
    ∀ y ∈ X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G), ∀ b' ∈ C.blkG R.hab,
      y * b' * y⁻¹ ∈ C.blkG R.hab := by
  rintro y ⟨hyX, hyC⟩ _ ⟨h', hh', rfl⟩
  obtain ⟨gy, rfl⟩ := C.exists_phi_eq hyX
  have hh'b : (h' : GL (Fin 4) K) ∈ blk C.hU R.hab := hh'
  have hcomm : ∀ x ∈ torusSU p 4 K, ent x R.a R.a = ent x R.b R.b →
      (gy : GL (Fin 4) K) * x = x * (gy : GL (Fin 4) K) := by
    intro x hx hxab
    have hxΓ := C.torus_le x hx
    have hu : C.phi ⟨x, hxΓ⟩ ∈ autFixedInG F R.t :=
      (R.phi_mem_fixed_iff (x := ⟨x, hxΓ⟩) hx).mpr hxab
    have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hu
    have h2 : C.phi (⟨x, hxΓ⟩ * gy) = C.phi (gy * ⟨x, hxΓ⟩) := by
      rw [map_mul, map_mul]
      exact h1
    exact (congrArg Subtype.val (C.phi_injective h2)).symm
  have hU : (gy : GL (Fin 4) K) ∈ primeFormUnitary C.hU (idGram K 4) :=
    unitarySU_le_primeFormUnitary (n := 4) C.hU gy.2
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have h3 := C.hp5
  have hmem := conj_mem_blk_of_centralizes (h := C.hU) (by omega) hζ R.hab hU hcomm hh'b
  exact ⟨gy * h' * gy⁻¹, hmem, by simp [map_mul, map_inv]⟩

theorem autMovedInG_le_blkG : autMovedInG F R.t ≤ C.blkG R.hab := by
  rw [autMovedInG_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨e, rfl⟩
  obtain ⟨x, hx, hxe⟩ := C.exists_decomp e.2
  obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
  have hv : v ∈ torusVec p 4 K := ⟨hv1, hv2⟩
  set η : Kˣ := v R.b * (v R.a)⁻¹ with hη
  have hηp : η ^ p = 1 := by
    rw [hη, mul_pow, inv_pow, hv1 R.b, hv1 R.a]
    simp
  have hvec : (v ∘ Equiv.swap R.a R.b) * v⁻¹ = torusElt R.a R.b η := by
    funext m
    by_cases hma : m = R.a
    · subst hma
      simp [torusElt_apply_left R.hab, hη]
    · by_cases hmb : m = R.b
      · subst hmb
        simp [torusElt_apply_right R.hab, hη]
      · simp [torusElt_apply_other hma hmb, Equiv.swap_apply_of_ne_of_ne hma hmb]
  have hgen : ((R.t e : F) : G) * (e : G)⁻¹ = C.phi (R.g * x * R.g⁻¹ * x⁻¹) := by
    rw [R.coe_t_apply, hxe, R.conj_phi]
    simp only [map_mul, map_inv]
  show ((R.t e : F) : G) * (e : G)⁻¹ ∈ C.blkG R.hab
  rw [hgen]
  refine ⟨R.g * x * R.g⁻¹ * x⁻¹, ?_, rfl⟩
  show (((R.g * x * R.g⁻¹ * x⁻¹ : unitarySU 2 f K 4)) : GL (Fin 4) K) ∈ blk C.hU R.hab
  have hcoe : ((R.g * x * R.g⁻¹ * x⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) =
      diagU (torusElt R.a R.b η) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hvx, R.hτ.conj_diagU hv, Equiv.symm_swap, ← diagU_inv, diagU_mul, hvec]
  rw [hcoe]
  refine diagU_torusElt_mem_blk R.hab ?_
  have : (η : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hηp, Units.val_one]
  exact bar_eq_inv_of_pow_eq_one C.hU C.hpq this

theorem eq_blkG [Finite G] (hrefl : IsAutReflection p F R.t) {Kg : Subgroup G}
    (hKC : Kg ≤ X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G))
    (hK : Kg.subgroupOf (X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G)) ∈
      thetaComponents p ↥(X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G)))
    (hmov : autMovedInG F R.t ≤ Kg) : Kg = C.blkG R.hab := by
  obtain ⟨hqs, hzc, -⟩ := blk_model C.hU C.hf2 R.hab
  have hBq : CFSG.IsQuasisimple ↥(C.blkG R.hab) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (C.blkGEquiv R.hab).symm hqs
  have hBz : Subgroup.center ↥(C.blkG R.hab) = ⊥ :=
    center_eq_bot_of_mulEquiv (C.blkGEquiv R.hab) hzc
  have hBM : C.blkG R.hab ≤ X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G) :=
    le_inf (C.blkG_le_X R.hab) R.blkG_le_centralizer
  have hne : autMoved F R.t ≠ ⊥ := by
    intro h0
    have := hrefl.2
    rw [h0, Subgroup.card_bot] at this
    exact C.hp.one_lt.ne this
  obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hmz : (m : G) ∈ autMovedInG F R.t := ⟨m, hm, rfl⟩
  have hz1 : (m : G) ≠ 1 := fun h1 => hm1 (Subtype.ext (Subtype.ext h1))
  exact eq_of_mem_thetaComponents_of_simple C.hp hKC hBM hK R.blkG_normalized hBq hBz
    (hmov hmz) (R.autMovedInG_le_blkG hmz) hz1

theorem model [Finite G] (hrefl : IsAutReflection p F R.t) {Kg : Subgroup G}
    (hKC : Kg ≤ X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G))
    (hK : Kg.subgroupOf (X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G)) ∈
      thetaComponents p ↥(X ⊓ Subgroup.centralizer (autFixedInG F R.t : Set G)))
    (hmov : autMovedInG F R.t ≤ Kg) : StatedClassicalModel ↥Kg .PSL 2 2 f := by
  have hKB := R.eq_blkG hrefl hKC hK hmov
  obtain ⟨-, -, hmodel⟩ := blk_model C.hU C.hf2 R.hab
  subst hKB
  exact Equivariance.statedClassicalModel_of_mulEquiv (C.blkGEquiv R.hab).symm hmodel

end Refl

end U4Frame

end CFSG.RankThree.PartOne.Q1327R
