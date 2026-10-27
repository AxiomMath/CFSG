module

public import CFSG.Monster.Visible.Irreducible
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Monster.Visible CFSG.Monster.SpinLattice
open scoped IsMulCommutative

noncomputable def latOfRho (x : rhoQvis) : L2 :=
  visModLat (Additive.ofMul (QuotientGroup.mk x))

theorem latOfRho_mul (x y : rhoQvis) :
    latOfRho (x * y) = latOfRho x + latOfRho y := by
  unfold latOfRho
  rw [QuotientGroup.mk_mul, ofMul_mul, visModLat.map_add]

theorem latOfRho_one : latOfRho (1 : rhoQvis) = 0 := by
  simp only [latOfRho, QuotientGroup.mk_one, ofMul_one]
  exact visModLat.map_zero

noncomputable def latSubmodule (K : Subgroup rhoQvis) : Submodule (ZMod 2) L2 where
  carrier := {v | ∃ x ∈ K, latOfRho x = v}
  add_mem' := by
    rintro v w ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, K.mul_mem hx hy, latOfRho_mul x y⟩
  zero_mem' := ⟨1, K.one_mem, latOfRho_one⟩
  smul_mem' := by
    intro c v hv
    rcases zmod_two_cases c with rfl | rfl
    · exact ⟨1, K.one_mem, by rw [zero_smul, latOfRho_one]⟩
    · simpa using hv

noncomputable def latAddHom (K : Subgroup rhoQvis) :
    Additive K →+ latSubmodule K where
  toFun x := ⟨latOfRho (Additive.toMul (α := K) x),
    ⟨Additive.toMul (α := K) x, (Additive.toMul (α := K) x).2, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    change latOfRho (Additive.toMul (α := K) (0 : Additive K)) = 0
    rw [toMul_zero]
    simpa using latOfRho_one
  map_add' x y := by
    apply Subtype.ext
    change latOfRho (Additive.toMul (α := K) (x + y)) =
      latOfRho (Additive.toMul (α := K) x) + latOfRho (Additive.toMul (α := K) y)
    rw [toMul_add]
    exact latOfRho_mul _ _

theorem mem_zRho_of_mem_latAddHom_ker {K : Subgroup rhoQvis} {x : Additive K}
    (hx : x ∈ (latAddHom K).ker) : ((Additive.toMul (α := K) x) : rhoQvis) ∈ zRho := by
  have h0 : latOfRho (Additive.toMul (α := K) x) = 0 := by
    have h := congrArg (fun y : latSubmodule K => y.1) (AddMonoidHom.mem_ker.mp hx)
    simpa [latAddHom] using h
  have h1 : Additive.ofMul
      (QuotientGroup.mk (Additive.toMul (α := K) x) : VisMod) = 0 := by
    apply visModLat.injective
    simpa [latOfRho] using h0
  exact (QuotientGroup.eq_one_iff _).1 ((ofMul_eq_zero).1 h1)

theorem latAddHom_surjective (K : Subgroup rhoQvis) :
    Function.Surjective (latAddHom K) := by
  intro y
  obtain ⟨x, hxK, hx⟩ := y.2
  refine ⟨Additive.ofMul ⟨x, hxK⟩, ?_⟩
  apply Subtype.ext
  simpa [latAddHom] using hx

theorem natCard_latSubmodule (K : Subgroup rhoQvis) :
    Nat.card K = Nat.card (latAddHom K).ker * Nat.card (latSubmodule K) := by
  have h := (AddSubgroup.card_ker_mul_card_range (latAddHom K)).symm
  have hdom : Nat.card (Additive K) = Nat.card K := Nat.card_congr Additive.toMul
  have hrange : Nat.card (latAddHom K).range = Nat.card (latSubmodule K) := by
    rw [AddMonoidHom.range_eq_top.mpr (latAddHom_surjective K), AddSubgroup.card_top]
  rw [hdom, hrange] at h
  exact h

theorem natCard_ker_latAddHom_le_two (K : Subgroup rhoQvis) :
    Nat.card (latAddHom K).ker ≤ 2 := by
  have hsq : (rhoN (CFSG.Monster.Spin.zQ)) ^ 2 = 1 := by
    have hzQ : CFSG.Monster.Spin.zQ ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, CFSG.Monster.Spin.orderOf_zQ]
    rw [pow_two, ← rhoN_mul, ← pow_two, hzQ, rhoN_one]
  have hzle : Nat.card zRho ≤ 2 := by
    change Nat.card (Subgroup.zpowers (rhoN (CFSG.Monster.Spin.zQ))) ≤ 2
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hsq
  have hfin : Finite zRho := by
    change Finite (Subgroup.zpowers (rhoN (CFSG.Monster.Spin.zQ)))
    exact finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, hsq⟩)
  have hinj : Function.Injective
      (fun x : (latAddHom K).ker =>
        (⟨((Additive.toMul (α := K) x) : rhoQvis),
          mem_zRho_of_mem_latAddHom_ker x.2⟩ : zRho)) := by
    intro x y hxy
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : zRho => (z : rhoQvis)) hxy
  exact (@Nat.card_le_card_of_injective _ _ hfin _ hinj).trans hzle

theorem latSubmodule_fixed {A : Subgroup Gvis} (hA : CFSG.Open.IsElemAbelian 2 A) :
    ∀ a ∈ A, ∀ w ∈ latSubmodule (A.subgroupOf rhoQvis),
      visModLat (((repVis a :
          LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
        Additive VisMod →ₗ[ZMod 2] Additive VisMod) (visModLat.symm w)) = w := by
  intro a ha w hw
  obtain ⟨x, hxK, rfl⟩ := hw
  have hxG : ((x : rhoQvis) : Gvis) ∈ A := Subgroup.mem_subgroupOf.1 hxK
  have hconj : MulAut.conjNormal a x = x := by
    apply Subtype.ext
    have hcomm : (⟨a, ha⟩ : A) * ⟨((x : rhoQvis) : Gvis), hxG⟩ =
        ⟨((x : rhoQvis) : Gvis), hxG⟩ * ⟨a, ha⟩ := hA.1.is_comm.comm _ _
    have hxa : a * ((x : rhoQvis) : Gvis) = ((x : rhoQvis) : Gvis) * a :=
      congrArg Subtype.val hcomm
    rw [MulAut.conjNormal_apply, hxa]
    group
  calc
    visModLat (((repVis a :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) (visModLat.symm (latOfRho x))) =
        visModLat (((repVis a :
          LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
            Additive VisMod →ₗ[ZMod 2] Additive VisMod)
              (Additive.ofMul (QuotientGroup.mk x))) := by
          simp only [latOfRho, LinearEquiv.symm_apply_apply]
    _ = visModLat (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal a x))) := by
          rw [repVis_apply]
    _ = latOfRho x := by
      rw [hconj]
      rfl

theorem latSubmodule_singular {A : Subgroup Gvis} (hA : CFSG.Open.IsElemAbelian 2 A) :
    ∀ w ∈ latSubmodule (A.subgroupOf rhoQvis), qL w = 0 := by
  intro w hw
  obtain ⟨x, hxK, rfl⟩ := hw
  have hxG : ((x : rhoQvis) : Gvis) ∈ A := Subgroup.mem_subgroupOf.1 hxK
  obtain ⟨r, rfl⟩ := rhoN_surjective x
  have hx2G : (((rhoN r : rhoQvis) : Gvis)) ^ 2 = 1 := hA.2 _ hxG
  have hx2 : (rhoN r) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx2G
  have h1 : rhoN (r ^ 2) = 1 := by
    calc rhoN (r ^ 2) = (rhoN r) ^ 2 := by rw [pow_two, rhoN_mul, ← pow_two]
      _ = 1 := hx2
  have hr2 : r ^ 2 = 1 := rhoN_injective (h1.trans (rhoN_one).symm)
  have hr2' : r ^ 2 = CFSG.Monster.Spin.zQ ^ ((0 : ZMod 2).val) := by
    simpa using hr2
  have hq := qL_phi_of_sq (r := r) (e := 0) hr2'
  unfold latOfRho
  rw [visModLat_mk]
  exact hq

theorem exists_fixed_singular_card_le_Gvis {A : Subgroup Gvis}
    (hA : CFSG.Open.IsElemAbelian 2 A) :
    ∃ D : Submodule (ZMod 2) L2,
      (∀ a ∈ A, ∀ w ∈ D,
        visModLat (((repVis a : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) (visModLat.symm w)) = w) ∧
      (∀ w ∈ D, qL w = 0) ∧
      Nat.card A ≤ 2 * Nat.card (A.map repVis) * Nat.card D := by
  refine ⟨latSubmodule (A.subgroupOf rhoQvis), latSubmodule_fixed hA,
    latSubmodule_singular hA, ?_⟩
  have hAcard : Nat.card A =
      Nat.card (A.map repVis) * Nat.card (A.subgroupOf rhoQvis) := by
    have h := (Subgroup.card_ker_mul_card_range (repVis.comp A.subtype)).symm
    have hker : (repVis.comp A.subtype).ker = rhoQvis.subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_repVis,
        Subgroup.mem_subgroupOf]
      rfl
    have hrange : (repVis.comp A.subtype).range = A.map repVis := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact Subgroup.mem_map_of_mem repVis x.2
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hker, hrange] at h
    have hKA : Nat.card (rhoQvis.subgroupOf A) = Nat.card (A.subgroupOf rhoQvis) := by
      have h1 : Nat.card (rhoQvis.subgroupOf A) =
          Nat.card (rhoQvis ⊓ A : Subgroup Gvis) := by
        rw [← Subgroup.inf_subgroupOf_right rhoQvis A]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      have h2 : Nat.card (A.subgroupOf rhoQvis) =
          Nat.card (A ⊓ rhoQvis : Subgroup Gvis) := by
        rw [← Subgroup.inf_subgroupOf_right A rhoQvis]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [h1, h2, inf_comm]
    rw [hKA, mul_comm] at h
    exact h
  have hKcard : Nat.card (A.subgroupOf rhoQvis) =
      Nat.card (latAddHom (A.subgroupOf rhoQvis)).ker *
        Nat.card (latSubmodule (A.subgroupOf rhoQvis)) :=
    natCard_latSubmodule (A.subgroupOf rhoQvis)
  have hker2 : Nat.card (latAddHom (A.subgroupOf rhoQvis)).ker ≤ 2 :=
    natCard_ker_latAddHom_le_two (A.subgroupOf rhoQvis)
  have hKle : Nat.card (A.subgroupOf rhoQvis) ≤
      2 * Nat.card (latSubmodule (A.subgroupOf rhoQvis)) := by
    rw [hKcard]
    exact Nat.mul_le_mul_right _ hker2
  calc
    Nat.card A = Nat.card (A.map repVis) * Nat.card (A.subgroupOf rhoQvis) := hAcard
    _ ≤ Nat.card (A.map repVis) *
        (2 * Nat.card (latSubmodule (A.subgroupOf rhoQvis))) :=
      Nat.mul_le_mul_left _ hKle
    _ = 2 * Nat.card (A.map repVis) *
        Nat.card (latSubmodule (A.subgroupOf rhoQvis)) := by ring

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
