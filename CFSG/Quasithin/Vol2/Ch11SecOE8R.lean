module

public import CFSG.Quasithin.EmptyFaithful.S153MDiag
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6

variable {G : Type} [Group G]

@[expose] def actHom {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P) :
    G →* MulAut P where
  toFun x := (e.symm.trans (MulAut.conjNormal x)).trans e
  map_one' := by
    ext p
    simp
  map_mul' x y := by
    ext p
    simp [map_mul]

theorem actHom_apply {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P) (x : G)
    (p : P) : actHom e x p = e (MulAut.conjNormal x (e.symm p)) := rfl

theorem actHom_of_mem {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P) {ℓ : G}
    (hℓ : ℓ ∈ L) : actHom e ℓ = MulAut.conj (e ⟨ℓ, hℓ⟩) := by
  ext p
  rw [actHom_apply, MulAut.conj_apply]
  have h : MulAut.conjNormal ℓ (e.symm p) = ⟨ℓ, hℓ⟩ * e.symm p * (⟨ℓ, hℓ⟩ : ↥L)⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem actHom_injective {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) : Function.Injective (actHom e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    have h1 := congrArg (fun φ : MulAut P => φ (e ⟨ℓ, hℓ⟩)) hx
    simp only [actHom_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    simp only [MulAut.conjNormal_apply] at h2
    calc ℓ * x = (x * ℓ * x⁻¹) * x := by rw [h2]
      _ = x * ℓ := by group
  rw [hC] at hxC
  exact Subgroup.mem_bot.mp hxC

theorem conjSub_map_iota {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P)
    (x : G) (H : Subgroup P) :
    A1b.conjSub x (H.map (L.subtype.comp e.symm.toMonoidHom)) =
      (H.map (actHom e x).toMonoidHom).map (L.subtype.comp e.symm.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp [actHom_apply, MulAut.conjNormal_apply]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp [actHom_apply, MulAut.conjNormal_apply]

theorem mem_normalizer_map_iota {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P)
    {x : G} {H : Subgroup P} (hx : H.map (actHom e x).toMonoidHom = H) :
    x ∈ Subgroup.normalizer
      ((H.map (L.subtype.comp e.symm.toMonoidHom) : Subgroup G) : Set G) := by
  rw [← A1b.conjSub_eq_iff_mem_normalizer, conjSub_map_iota, hx]

theorem eq_iota_of_actHom_eq {L : Subgroup G} [L.Normal] {P : Type*} [Group P] (e : ↥L ≃* P)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) {x : G} {p : P}
    (hx : actHom e x = MulAut.conj p) : x = ((e.symm p : ↥L) : G) := by
  apply actHom_injective e hC
  rw [hx, actHom_of_mem e (e.symm p).2]
  simp

variable [Finite G]

theorem exists_equiv_map_eq_U {L T : Subgroup G} [hLn : L.Normal] (hT : IsSylowIn 2 T ⊤)
    {K : Type} [Field K] [Finite K] [CharP K 2] (e : ↥L ≃* projectiveSL 3 K) :
    ∃ e' : ↥L ≃* projectiveSL 3 K,
      ((T ⊓ L).subgroupOf L).map e'.toMonoidHom = projUnitriangular 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hS ▸ isSylowTwoOf_top_of_sylow S
  set U := (T ⊓ L).subgroupOf L with hUdef
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hU : IsSylowTwoOf U ⊤ := S153M.isSylowTwoOf_subgroupOf_top' hTL
  have hU₁ := B113Lie.isSylowTwoOf_map_top e.symm hU₀
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : ((projUnitriangular 3 K).map e.symm.toMonoidHom).map
      (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  refine ⟨(e.symm.trans (MulAut.conj k)).symm, ?_⟩
  rw [← hconj, Subgroup.map_map, Subgroup.map_map]
  convert Subgroup.map_id (projUnitriangular 3 K)
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_trans_apply, MonoidHom.id_apply]
  simp
  group

omit [Finite G] in
theorem actHom_mem_U {L T : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
    (e : ↥L ≃* projectiveSL 3 K)
    (he : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K) {t : G} (ht : t ∈ T)
    (u : projectiveSL 3 K) (hu : u ∈ projUnitriangular 3 K) :
    actHom e t u ∈ projUnitriangular 3 K := by
  rw [← he] at hu ⊢
  obtain ⟨v, hv, rfl⟩ := hu
  refine ⟨MulAut.conjNormal t v, ?_, ?_⟩
  · have hv' : (v : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hv
    show MulAut.conjNormal t v ∈ (T ⊓ L).subgroupOf L
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact ⟨T.mul_mem (T.mul_mem ht hv'.1) (T.inv_mem ht), hLn.conj_mem _ hv'.2 t⟩
  · simp [actHom_apply]

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
