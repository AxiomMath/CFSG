module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoQs
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoCent
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

theorem glTwoSol_perfect_hom_central {G : Type*} [Group G] [Group.IsPerfect G]
    (f : G →* G) (hf : ∀ g, f g ∈ Subgroup.center G) (g : G) : f g = 1 := by
  have hker : commutator G ≤ f.ker := by
    unfold commutator
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hf a) (f b)).symm
  have htop : g ∈ commutator G := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.1 (hker htop)

theorem glTwoSol_comm_mul {A : Type*} [Group A] (x a b : A) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def, mul_inv_rev]
  group

theorem glTwoSol_solvable_of_le {A : Type*} [Group A] {G : Subgroup A} (N : Subgroup G)
    [Group.IsSolvable N] {L : Subgroup A} (hLN : L ≤ N.map G.subtype) :
    Group.IsSolvable L := by
  let phi0 : L →* N.map G.subtype :=
    L.subtype.codRestrict (N.map G.subtype) fun x => hLN x.2
  let e : N ≃* N.map G.subtype :=
    Subgroup.equivMapOfInjective N G.subtype (Subgroup.subtype_injective G)
  let phi : L →* N := e.symm.toMonoidHom.comp phi0
  have hphi : Function.Injective phi := by
    intro x y hxy
    have hxy' : e.symm (phi0 x) = e.symm (phi0 y) := hxy
    have h1 : phi0 x = phi0 y := e.symm.injective hxy'
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  exact Group.isSolvable_of_isSolvable_injective (f := phi) hphi

theorem glTwoSol_conj_map {A : Type*} [Group A] {G : Subgroup A} (N : Subgroup G) [N.Normal]
    {x y : A} (hx : x ∈ G) (hy : y ∈ N.map G.subtype) : x * y * x⁻¹ ∈ N.map G.subtype := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
  have h := Subgroup.mem_map_of_mem G.subtype
    ((inferInstance : N.Normal).conj_mem n hn ⟨x, hx⟩)
  simpa using h

theorem glTwoSol_det_conj {K : Type} [Field K] (g a : GL (Fin 2) K) :
    (g * a * g⁻¹ : GL (Fin 2) K).val.det = a.val.det := by
  have h : (g⁻¹ : GL (Fin 2) K).val.det * g.val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  calc g.val.det * a.val.det * (g⁻¹ : GL (Fin 2) K).val.det
      = a.val.det * ((g⁻¹ : GL (Fin 2) K).val.det * g.val.det) := by ring
    _ = a.val.det := by rw [h, mul_one]

theorem glTwoSol_conj_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    {g a : GL (Fin 2) K} (hg : g ∈ glPi π 2 (p ^ f) K) (ha : a ∈ slPi π 2 (p ^ f) K) :
    g * a * g⁻¹ ∈ slPi π 2 (p ^ f) K := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  rw [mem_slPi_iff hπ] at ha ⊢
  exact ⟨(glPi π 2 (p ^ f) K).mul_mem ((glPi π 2 (p ^ f) K).mul_mem hg ha.1)
    ((glPi π 2 (p ^ f) K).inv_mem hg), by rw [glTwoSol_det_conj]; exact ha.2⟩

theorem glTwoSol_comm_trivial {B : Type*} [Group B] (L : Subgroup B) [Group.IsPerfect L]
    (y : B) (hsub : ∀ a : L, ⁅y, (a : B)⁆ ∈ L)
    (hcen : ∀ a : L, (⟨⁅y, (a : B)⁆, hsub a⟩ : ↥L) ∈ Subgroup.center ↥L) (a : L) :
    ⁅y, (a : B)⁆ = 1 := by
  let f : L →* L := MonoidHom.mk' (fun a : L => (⟨⁅y, (a : B)⁆, hsub a⟩ : ↥L)) (by
    intro a b
    apply Subtype.ext
    show ⁅y, (a : B) * (b : B)⁆ = ⁅y, (a : B)⁆ * ⁅y, (b : B)⁆
    have hz : (a : B) * ⁅y, (b : B)⁆ * (a : B)⁻¹ = ⁅y, (b : B)⁆ := by
      have h : (a : B) * ⁅y, (b : B)⁆ = ⁅y, (b : B)⁆ * (a : B) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.1 (hcen b) a)
      rw [h, mul_inv_cancel_right]
    rw [glTwoSol_comm_mul, hz])
  have hf : ∀ g : ↥L, f g ∈ Subgroup.center ↥L := hcen
  exact congrArg Subtype.val (glTwoSol_perfect_hom_central f hf a)

theorem glTwoSol_centralizes {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq3 : 3 < p ^ f) (N : Subgroup (glPi π 2 (p ^ f) K)) [N.Normal] (hN : Group.IsSolvable N)
    {x : GL (Fin 2) K} (hx : x ∈ N.map (glPi π 2 (p ^ f) K).subtype) :
    x ∈ Subgroup.centralizer (slPi π 2 (p ^ f) K : Set (GL (Fin 2) K)) := by
  haveI := hN
  have hqs : CFSG.IsQuasisimple (slPi π 2 (p ^ f) K) := isQuasisimple_slPi_two hK hq3
  haveI : Group.IsPerfect ↥(slPi π 2 (p ^ f) K) := hqs.1
  haveI : Nontrivial ↥(slPi π 2 (p ^ f) K) := CFSG.LocalCores.isQuasisimple_nontrivial hqs
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hLG : ∀ a : GL (Fin 2) K, a ∈ slPi π 2 (p ^ f) K → a ∈ glPi π 2 (p ^ f) K :=
    fun a ha => slPi_le_glPi hπ ha
  have hN'G : ∀ y ∈ N.map (glPi π 2 (p ^ f) K).subtype, y ∈ glPi π 2 (p ^ f) K := by
    intro y hy
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact n.2
  let M : Subgroup ↥(slPi π 2 (p ^ f) K) :=
    (N.map (glPi π 2 (p ^ f) K).subtype).subgroupOf (slPi π 2 (p ^ f) K)
  have hMmem : ∀ m : ↥(slPi π 2 (p ^ f) K),
      m ∈ M ↔ (m : GL (Fin 2) K) ∈ N.map (glPi π 2 (p ^ f) K).subtype :=
    fun m => Subgroup.mem_subgroupOf
  have hMnorm : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hMmem] at hm ⊢
    have hcoe : ((g * m * g⁻¹ : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) =
        (g : GL (Fin 2) K) * (m : GL (Fin 2) K) * (g : GL (Fin 2) K)⁻¹ := by
      simp
    rw [hcoe]
    exact glTwoSol_conj_map N (hLG _ g.2) hm
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hMnorm with hMtop | hMcen
  ·
    exfalso
    have hLN : slPi π 2 (p ^ f) K ≤ N.map (glPi π 2 (p ^ f) K).subtype := by
      intro y hy
      have hmem : (⟨y, hy⟩ : ↥(slPi π 2 (p ^ f) K)) ∈ M := by
        rw [hMtop]
        exact Subgroup.mem_top _
      exact (hMmem _).1 hmem
    exact Group.IsPerfect.not_isSolvable _ (glTwoSol_solvable_of_le N hLN)
  ·
    have hcommL : ∀ y : GL (Fin 2) K, y ∈ N.map (glPi π 2 (p ^ f) K).subtype →
        ∀ a : ↥(slPi π 2 (p ^ f) K), ⁅y, (a : GL (Fin 2) K)⁆ ∈ slPi π 2 (p ^ f) K := by
      intro y hy a
      rw [commutatorElement_def]
      exact (slPi π 2 (p ^ f) K).mul_mem (glTwoSol_conj_slPi hK (hN'G y hy) a.2)
        ((slPi π 2 (p ^ f) K).inv_mem a.2)
    have hcommN : ∀ y : GL (Fin 2) K, y ∈ N.map (glPi π 2 (p ^ f) K).subtype →
        ∀ a : ↥(slPi π 2 (p ^ f) K),
          ⁅y, (a : GL (Fin 2) K)⁆ ∈ N.map (glPi π 2 (p ^ f) K).subtype := by
      intro y hy a
      have e : ⁅y, (a : GL (Fin 2) K)⁆ =
          y * ((a : GL (Fin 2) K) * y⁻¹ * (a : GL (Fin 2) K)⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [e]
      exact (N.map (glPi π 2 (p ^ f) K).subtype).mul_mem hy
        (glTwoSol_conj_map N (hLG _ a.2) ((N.map (glPi π 2 (p ^ f) K).subtype).inv_mem hy))
    have hcen : ∀ a : ↥(slPi π 2 (p ^ f) K),
        (⟨⁅x, (a : GL (Fin 2) K)⁆, hcommL x hx a⟩ : ↥(slPi π 2 (p ^ f) K)) ∈
          Subgroup.center ↥(slPi π 2 (p ^ f) K) :=
      fun a => hMcen ((hMmem ⟨⁅x, (a : GL (Fin 2) K)⁆, hcommL x hx a⟩).2 (hcommN x hx a))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := glTwoSol_comm_trivial (slPi π 2 (p ^ f) K) x (hcommL x hx) hcen
      (⟨h, hh⟩ : ↥(slPi π 2 (p ^ f) K))
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

theorem glPi_two_solvable_normal_cyclic {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq3 : 3 < p ^ f) (N : Subgroup (glPi π 2 (p ^ f) K)) [N.Normal]
    (hN : Group.IsSolvable N) : IsCyclic N := by
  haveI : Finite K := hK.finite
  have hS : IsCyclic (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) :=
    isCyclic_of_surjective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  haveI := hS
  have hsub : ∀ n : N, ((n : glPi π 2 (p ^ f) K) : GL (Fin 2) K) ∈
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K := by
    intro n
    have hmem : ((n : glPi π 2 (p ^ f) K) : GL (Fin 2) K) ∈
        N.map (glPi π 2 (p ^ f) K).subtype :=
      Subgroup.mem_map_of_mem (glPi π 2 (p ^ f) K).subtype n.2
    have hc := glTwoSol_centralizes hK hq3 N hN hmem
    rwa [centralizer_slPi_two hK hq3] at hc
  let ψ : N →* CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K :=
    MonoidHom.codRestrict ((glPi π 2 (p ^ f) K).subtype.comp N.subtype)
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) hsub
  have hinj : Function.Injective ψ := by
    intro a b hab
    have hab2 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext hab2)
  exact isCyclic_of_injective ψ hinj

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
