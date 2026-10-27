module

public import CFSG.LocalAnalysis.SteinbergCCCComponentSubnormalSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped commutatorElement

theorem le_center_of_isSolvable_of_isQuasisimple {J : Type*} [Group J]
    (hJ : CFSG.IsQuasisimple J) (B : Subgroup J) [B.Normal] (hB : Group.IsSolvable B) :
    B ≤ center J := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hJ B with h | h
  · exact h
  · exfalso
    obtain ⟨hperf, hsimple, -⟩ := hJ
    have : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
    have hsolv : Group.IsSolvable J := by
      subst h
      exact Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup J) ≃* J).toMonoidHom)
        topEquiv.surjective
    exact Group.IsPerfect.not_isSolvable J hsolv

theorem mk_mul_comm_of_commutator_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {a b : G} (h : ⁅a, b⁆ ∈ N) : (a : G ⧸ N) * b = b * a := by
  rw [commutatorElement_def] at h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have e : (a * b)⁻¹ * (b * a) = (a * b)⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * ((a * b)⁻¹)⁻¹ := by group
  rw [e]
  exact (inferInstance : N.Normal).conj_mem _ (inv_mem h) _

theorem common_critical_kernels {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (hL : CFSG.IsCComponent L) {I : Type*} [Finite I] [Nonempty I] {J : I → Type*}
    [∀ i, Group (J i)] (ρ : ∀ i, L →* J i) (hρ : ∀ i, Function.Surjective (ρ i))
    (hJ : ∀ i, CFSG.IsQuasisimple (J i)) (hZ : ∀ i, Nat.card (center (J i)) = 2)
    (s : I → ℕ) (hs : ∀ i, (s i).Prime) (hs5 : ∀ i, 5 ≤ s i)
    (ψ : ∀ i, J i ⧸ center (J i) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod (s i))) :
    (∀ i j, (ρ i).ker = (ρ j).ker) ∧
      ∀ i, (ρ i).ker ≤ CFSG.solvableRadical L ∧
        (CFSG.solvableRadical L).map (ρ i) = center (J i) ∧
        Nonempty (↥(CFSG.solvableRadical L) ⧸ (ρ i).ker.subgroupOf (CFSG.solvableRadical L) ≃*
          center (J i)) ∧
        (ρ i).ker.relIndex (CFSG.solvableRadical L) = 2 := by
  classical
  set R := CFSG.solvableRadical L with hRdef
  obtain ⟨hRchar, hRsolv, hRmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  have hRnorm : R.Normal := normal_of_characteristic R
  have hLperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hL.2.1
  have hJnt : ∀ i, Nontrivial (J i) := fun i => by
    have := (hJ i).2.1
    exact (QuotientGroup.mk'_surjective (center (J i))).nontrivial
  have hKsolv : ∀ i, Group.IsSolvable (ρ i).ker := by
    intro i
    set U := (ρ i).ker.map L.subtype with hU
    have hUL : U < L := by
      refine lt_of_le_of_ne (map_subtype_le _) fun h => ?_
      have hker : (ρ i).ker = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : (x : G) ∈ U := by rw [h]; exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [← Subtype.ext hyx]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (J i)
      obtain ⟨x, rfl⟩ := hρ i a
      obtain ⟨y, rfl⟩ := hρ i b
      have hx : x ∈ (ρ i).ker := by rw [hker]; exact mem_top x
      have hy : y ∈ (ρ i).ker := by rw [hker]; exact mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      exact hab (hx.trans hy.symm)
    have hUs : (U.subgroupOf L).IsSubnormal := by
      rw [hU, ← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]
      exact (inferInstance : ((ρ i).ker).Normal).isSubnormal
    have hsolvU := CFSG.LocalAnalysis.Ccomponent_proper_subnormal_solvable hL hUL hUs
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((ρ i).ker.equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
      (MulEquiv.injective _)
  have hKR : ∀ i, (ρ i).ker ≤ R := fun i => hRmax _ inferInstance (hKsolv i)
  have hRcen : ∀ j, R.map (ρ j) ≤ center (J j) := by
    intro j
    have : (R.map (ρ j)).Normal := hRnorm.map (ρ j) (hρ j)
    refine le_center_of_isSolvable_of_isQuasisimple (hJ j) _ ?_
    exact Group.isSolvable_of_surjective (f := (ρ j).subgroupMap R)
      ((ρ j).subgroupMap_surjective R)
  have hTR : ∀ i, (center (J i)).comap (ρ i) ≤ R := by
    intro i
    set T := (center (J i)).comap (ρ i) with hT
    have hTnorm : T.Normal := (inferInstance : (center (J i)).Normal).comap (ρ i)
    have hKT : (ρ i).ker ≤ T := fun x hx => by
      rw [hT, mem_comap, (MonoidHom.mem_ker).mp hx]
      exact one_mem _
    have := hKsolv i
    let g : T →* center (J i) :=
      ((ρ i).comp T.subtype).codRestrict (center (J i)) fun x => x.2
    have hTsolv : Group.IsSolvable T := by
      refine Group.isSolvable_of_ker_le_range (inclusion hKT) g fun x hx => ?_
      have hx' : (x : L) ∈ (ρ i).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    exact hRmax T hTnorm hTsolv
  have hRmap : ∀ i, R.map (ρ i) = center (J i) := by
    intro i
    refine le_antisymm (hRcen i) fun z hz => ?_
    obtain ⟨x, rfl⟩ := hρ i z
    exact ⟨x, hTR i hz, rfl⟩
  have hiso : ∀ i, Nonempty (↥R ⧸ (ρ i).ker.subgroupOf R ≃* center (J i)) := by
    intro i
    set g := (ρ i).comp R.subtype with hg
    have hgker : g.ker = (ρ i).ker.subgroupOf R := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
      rfl
    have hgrange : g.range = center (J i) := by
      rw [hg, MonoidHom.range_comp, range_subtype, hRmap i]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
      ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hgrange))⟩
  have hindex : ∀ i, (ρ i).ker.relIndex R = 2 := by
    intro i
    obtain ⟨e⟩ := hiso i
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr e.toEquiv, hZ i]
  refine ⟨fun i j => ?_, fun i => ⟨hKR i, hRmap i, hiso i, hindex i⟩⟩
  by_contra hne
  have : Fact (s i).Prime := ⟨hs i⟩
  set M := (ρ j).ker ⊓ (ρ i).ker with hM
  have hMnorm : M.Normal := by rw [hM]; infer_instance
  have hnle : ¬ (ρ i).ker ≤ (ρ j).ker := by
    intro hle
    apply hne
    have h1 := relIndex_mul_relIndex _ _ _ hle (hKR j)
    rw [hindex i, hindex j] at h1
    have h2 : (ρ i).ker.relIndex (ρ j).ker = 1 := by omega
    exact le_antisymm hle (relIndex_eq_one.mp h2)
  have hMR : 4 ≤ M.relIndex R := by
    have h1 := relIndex_inf_mul_relIndex (ρ j).ker (ρ i).ker R
    rw [inf_of_le_left (hKR i), hindex i] at h1
    have h2 : (ρ j).ker.relIndex (ρ i).ker ≠ 1 := fun h => hnle (relIndex_eq_one.mp h)
    have h3 : (ρ j).ker.relIndex (ρ i).ker ≠ 0 := index_ne_zero_of_finite
    rw [hM, ← h1]
    omega
  set π := QuotientGroup.mk' M with hπ
  set f : L ⧸ M →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod (s i)) :=
    ((CFSG.QuasithinUnique.Setup.Family.p2Equiv (ZMod (s i))).symm.toMonoidHom.comp
      (ψ i).toMonoidHom).comp ((QuotientGroup.mk' (center (J i))).comp
        (QuotientGroup.lift M (ρ i) inf_le_right)) with hf
  have hfmk : ∀ x : L, f (x : L ⧸ M) = 1 ↔ ρ i x ∈ center (J i) := by
    intro x
    rw [hf]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.lift_mk,
      QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hfs : Function.Surjective f :=
    (CFSG.QuasithinUnique.Setup.Family.p2Equiv (ZMod (s i))).symm.surjective.comp
      ((ψ i).surjective.comp ((QuotientGroup.mk'_surjective _).comp (by
        intro z
        obtain ⟨x, rfl⟩ := hρ i z
        exact ⟨(x : L ⧸ M), rfl⟩)))
  have hkercen : f.ker ≤ center (L ⧸ M) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hfmk] at hq
    have hxR : x ∈ R := hTR i hq
    rw [mem_center_iff]
    intro q'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q'
    refine (mk_mul_comm_of_commutator_mem M ?_).symm
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hRcen j ⟨x, hxR, rfl⟩) (ρ j y)).symm
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp hq (ρ i y)).symm
  have hbound := CFSG.QuasithinUnique.Setup.Family.p2_central_kernel_bound (hs5 i) f hfs hkercen
  have hRker : R.map π ≤ f.ker := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, hπ, QuotientGroup.mk'_apply, hfmk]
    exact hRcen i ⟨x, hx, rfl⟩
  have hcardRM : Nat.card (R.map π) = M.relIndex R := by
    set g := π.comp R.subtype with hg
    have hgker : g.ker = M.subgroupOf R := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, hg, MonoidHom.comp_apply, hπ,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    have hgrange : g.range = R.map π := by
      rw [hg, MonoidHom.range_comp, range_subtype]
    rw [← hgrange, ← index_ker, hgker]
    rfl
  have h1 := card_le_of_le hRker
  omega

end CFSG.Quasithin.H13.NQBlock
