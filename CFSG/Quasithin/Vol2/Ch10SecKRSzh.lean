module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzg
public import CFSG.Quasithin.Vol2.Ch10SecKRSza

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

variable {G : Type} [Group G]

namespace MultiCoord

variable {J W : Subgroup G} {k : ℕ} (C : MultiCoord J W k)

theorem conj_eq_iff (hall : ∀ i, C.dual i = false) {e : G} (he : e ∈ W)
    (hcomp : ∀ i, C.E e i = 0 ∨ C.E e i = Pi.single 0 1) (he1 : e ≠ 1) (j : ↥J) :
    (j : G) * e * (j : G)⁻¹ = e ↔
      (C.ρ j : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, C.E e i₁ = Pi.single 0 1 := by
    by_contra h
    simp only [not_exists] at h
    exact he1 (C.eq_one_of_E he (funext fun i => (hcomp i).resolve_right (h i)))
  constructor
  · intro hj
    have h1 := C.conj j e he i₁
    rw [hj, hall, tw_false, hi₁] at h1
    exact h1.symm
  · intro hj
    refine C.inj _ (C.conj_mem j he) e he (funext fun i => ?_)
    rw [C.conj j e he i, hall, tw_false]
    rcases hcomp i with h | h <;> rw [h]
    · exact Matrix.mulVec_zero _
    · exact hj

end MultiCoord

variable [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_multi_E3_nat3 (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : FactK7L5)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hall : ∀ i, C.dual i = false)
    (hU : ∀ j : ↥J, C.ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (h3 : InvStd (piL C.ρ c.le).range 3)
    (htriv : ∀ x ∈ (piL C.ρ c.le).range, ∀ v, x • v + v ∈ stdE 5 3)
    (hqX : Nonempty (↥(piL C.ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL C.ρ c.le).range ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hUN : uniSL 5 ≤ Subgroup.normalizer ((piL C.ρ c.le).range : Set SL5)) : False := by
  have huW := Conf.u_mem_VI c hTw h37 h38
  have hfixu : ∀ j : ↥J, C.ρ j ∈ uniSL 5 → (j : G) * (t * w * t⁻¹) * (j : G)⁻¹ = t * w * t⁻¹ :=
    fun j hj => conj_eq_of_mem_centralizer (X := Subgroup.zpowers (t * w * t⁻¹))
      (Subgroup.mem_centralizer_iff.mpr fun h hh => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
          (Conf.Tw_le_centralizer_u c hTw h37 h38 ((hU j).mp hj))).symm n).eq)
      (Subgroup.mem_zpowers _)
  have hcomp : ∀ i, C.E (t * w * t⁻¹) i = 0 ∨ C.E (t * w * t⁻¹) i = Pi.single 0 1 := fun i =>
    fix_vec_of_uniSL fun g hg => by
      obtain ⟨j, rfl⟩ := C.ρ_surj g
      have h1 := C.conj j _ huW i
      rw [hfixu j hg, hall, tw_false] at h1
      exact h1.symm
  have hcen : ∀ j : ↥J, (j : G) ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ↔
      C.ρ j ∈ Q1 := fun j => by
    rw [← mem_Q1_iff_mulVec, ← C.conj_eq_iff hall huW hcomp (Conf.u_ne_one c) j,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc (j : G) * (t * w * t⁻¹) = (j : G) * (t * w * t⁻¹) * (j : G)⁻¹ * (j : G) := by group
        _ = t * w * t⁻¹ * (j : G) := by rw [h]
  have hker' : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, j ^ 2 ^ m = 1 := fun j hj => by
    obtain ⟨m, hm⟩ := C.ker_two hCJ hj
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  exact Conf.false_of_rho c hTw h37 h38 h318 h36' hE hK7L5 hVe hq e5 eJ C.ρ C.ρ_surj hker' hU
    hcen h3 htriv hqX hUN

theorem Conf.exists_TL_of_uniSL (c : Conf T L I t w J) (ρ : ↥J →* SL5)
    (hU : ∀ j : ↥J, ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    {g : SL5} (hgU : g ∈ uniSL 5) (hgX : g ∈ (piL ρ c.le).range) :
    ∃ l : ↥L, (l : G) ∈ T ∧ piL ρ c.le l = g := by
  have hSyl := image_isSylowTwoOf (SecA.isSylowTwoOf_inf c.hyp.fsu.maximal.1)
    (piL ρ c.le).rangeRestrict (piL ρ c.le).rangeRestrict_surjective
  have hQ2 : IsPGroup 2 ((uniSL 5).subgroupOf (piL ρ c.le).range) := fun x => by
    obtain ⟨n, hn⟩ := isPGroup_uniSL_five ⟨((x : ↥(piL ρ c.le).range) : SL5),
      Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hPQ : ((T ⊓ L).subgroupOf L).map (piL ρ c.le).rangeRestrict ≤
      (uniSL 5).subgroupOf (piL ρ c.le).range := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact (hU ⟨l, c.le l.2⟩).mpr ⟨(Subgroup.mem_subgroupOf.mp hl).1, c.J_le (c.le l.2)⟩
  rw [A4.isSylowTwoOf_iff_maximal] at hSyl
  obtain ⟨l, hl, hlg⟩ := hSyl.2.2 _ le_top hQ2 hPQ
    (show (⟨g, hgX⟩ : ↥(piL ρ c.le).range) ∈ (uniSL 5).subgroupOf (piL ρ c.le).range from hgU)
  exact ⟨l, (Subgroup.mem_subgroupOf.mp hl).1, congrArg Subtype.val hlg⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
