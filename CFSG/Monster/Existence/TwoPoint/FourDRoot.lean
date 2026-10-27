module

public import CFSG.Monster.B.E6.StdF4Points
public import CFSG.Monster.B.E6.GStarStructure
public import CFSG.Monster.Existence.TwoPoint.FourDGroup
import Mathlib.Tactic.Group
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Monster.B.E6
  CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem fd_centralizer_rootInv_ne_top :
    Subgroup.centralizer ({rootInv} : Set stdGroup) ≠ ⊤ := by
  intro h
  have hcen : rootInv ∈ Subgroup.center stdGroup := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({rootInv} : Set stdGroup) := by
      rw [h]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  rw [CFSG.Monster.B.E6.StdF4.center_stdGroup, Subgroup.mem_bot] at hcen
  exact rootInv_ne_one hcen

theorem fd_isCoatom_centralizer_rootInv :
    IsCoatom (Subgroup.centralizer ({rootInv} : Set stdGroup)) := by
  refine ⟨fd_centralizer_rootInv_ne_top, fun H hH => ?_⟩
  rw [centralizer_rootInv] at hH
  set A : Subgroup (ModGL Tag.E6 K) := H.map stdGroup.subtype with hA
  have hPA : nativeParabolic firstJ ≤ A := fun x hx =>
    ⟨⟨x, nativeParabolic_le_stdGroup _ hx⟩, hH.le (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hAS : A ≤ stdGroup := Subgroup.map_subtype_le H
  obtain ⟨I, hI⟩ := exists_eq_nativeParabolic ((stdBorel_le_nativeParabolic firstJ).trans hPA)
    hAS
  have hJI : firstJ ⊆ I := fun i hi => by
    rw [← nativeRep_mem_nativeParabolic_iff, ← hI]
    exact hPA (nativeRep_mem_nativeParabolic_iff firstJ i |>.2 hi)
  by_cases h0 : (0 : Fin 4) ∈ I
  · have hIu : I = Set.univ := Set.eq_univ_of_forall fun i => by
      rcases fin4_cases i with rfl | rfl | rfl | rfl
      · exact h0
      all_goals exact hJI (by simp [firstJ])
    rw [hIu, nativeParabolic_univ] at hI
    refine eq_top_iff.2 fun h _ => ?_
    have hh : (h : ModGL Tag.E6 K) ∈ A := by rw [hI]; exact h.2
    obtain ⟨h', hh', he⟩ := hh
    exact (Subtype.ext he : h' = h) ▸ hh'
  · exfalso
    have hIJ : I = firstJ := Set.Subset.antisymm (fun i hi => by
      rcases fin4_cases i with rfl | rfl | rfl | rfl
      · exact absurd hi h0
      all_goals simp [firstJ]) hJI
    rw [hIJ] at hI
    refine hH.not_ge fun h hh => ?_
    have : (h : ModGL Tag.E6 K) ∈ nativeParabolic firstJ := by
      rw [← hI]; exact ⟨h, hh, rfl⟩
    exact Subgroup.mem_subgroupOf.2 this

theorem fd_isCoatom_centralizer_of_mem_rootClass
    {p : stdGroup} (hp : p ∈ rootClass) :
    IsCoatom (Subgroup.centralizer ({p} : Set stdGroup)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hp
  have hmem : ∀ c : stdGroup, g * c * g⁻¹ ∈ Subgroup.centralizer ({g * rootInv * g⁻¹} :
      Set stdGroup) ↔ c ∈ Subgroup.centralizer ({rootInv} : Set stdGroup) := fun c => by
    rw [mem_centralizer_conj_iff g rootInv (g * c * g⁻¹), show g⁻¹ * (g * c * g⁻¹) * g = c by group]
  refine ⟨fun h => fd_centralizer_rootInv_ne_top (eq_top_iff.2 fun c _ => ?_), fun H hH => ?_⟩
  · exact (hmem c).1 (h ▸ Subgroup.mem_top _)
  · set H' : Subgroup stdGroup := H.comap (MulAut.conj g).toMonoidHom with hH'
    have hmemH' : ∀ c, c ∈ H' ↔ g * c * g⁻¹ ∈ H := fun c => Iff.rfl
    have hlt : Subgroup.centralizer ({rootInv} : Set stdGroup) < H' := by
      refine lt_of_le_of_ne (fun c hc => (hmemH' c).2 (hH.le ((hmem c).2 hc))) fun he => ?_
      obtain ⟨h, hhH, hhn⟩ := IsConcreteLE.exists_of_lt hH
      have h1 : g⁻¹ * h * g ∈ H' := (hmemH' _).2 (by
        rw [show g * (g⁻¹ * h * g) * g⁻¹ = h by group]; exact hhH)
      rw [← he] at h1
      exact hhn (by
        have := (hmem (g⁻¹ * h * g)).2 h1
        rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group] at this)
    have htop := fd_isCoatom_centralizer_rootInv.2 _ hlt
    refine eq_top_iff.2 fun h _ => ?_
    have h1 : g⁻¹ * h * g ∈ H' := by rw [htop]; trivial
    have := (hmemH' _).1 h1
    rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group] at this

theorem fd_ncard_rootClass :
    rootClass.ncard = 3968055 := by
  obtain ⟨q, hq, hcov, hsize, -⟩ := fiveOrbits_rootInv
  have hfin : ∀ i, (conjOrbit (Subgroup.centralizer {rootInv}) (q i)).Finite := fun i =>
    Set.finite_of_ncard_ne_zero (by rw [hsize i]; fin_cases i <;> decide)
  have hdisj : Pairwise (Function.onFun Disjoint fun i =>
      conjOrbit (Subgroup.centralizer {rootInv}) (q i)) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    apply hij
    apply repSize_injective
    rw [← hsize i, ← hsize j, ← conjOrbit_eq_of_mem hzi, ← conjOrbit_eq_of_mem hzj]
  have hunion : rootClass = ⋃ i, conjOrbit (Subgroup.centralizer {rootInv}) (q i) := by
    ext y
    rw [Set.mem_iUnion]
    constructor
    · exact hcov y
    · rintro ⟨i, c, -, rfl⟩
      exact (hq i).trans (isConj_iff.2 ⟨c, rfl⟩)
  rw [hunion, Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype, Fin.sum_univ_five]
  simp only [hsize]
  rfl

theorem fd_card_rootClass_mul_card_centralizer
    {p : stdGroup} (hp : p ∈ rootClass) :
    3968055 * Nat.card ↥(Subgroup.centralizer ({p} : Set stdGroup)) =
      76532479683774853939200 := by
  have h := fd_card_isConj_mul_card_centralizer p
  have e : {x : stdGroup | IsConj p x} = rootClass := by
    ext x
    exact ⟨fun hx => hp.trans hx, fun hx => hp.symm.trans hx⟩
  rw [e, Nat.card_coe_set_eq, fd_ncard_rootClass, card_stdGroup] at h
  exact h

theorem fd_not_seventeen_dvd_card_centralizer
    {p : stdGroup} (hp : p ∈ rootClass) :
    ¬ 17 ∣ Nat.card ↥(Subgroup.centralizer ({p} : Set stdGroup)) := by
  rintro ⟨k, hk⟩
  have h := fd_card_rootClass_mul_card_centralizer hp
  rw [hk] at h
  omega

theorem fd_eq_Ginl_of_lt_map_inl
    {p : stdGroup} (hp : p ∈ rootClass) {B : Subgroup GStar}
    (hlt : (Subgroup.centralizer ({p} : Set stdGroup)).map SemidirectProduct.inl < B)
    (hB : B ≤ Ginl) : B = Ginl := by
  have hlt' : Subgroup.centralizer ({p} : Set stdGroup) < B.comap SemidirectProduct.inl := by
    refine lt_of_le_of_ne (fun q hq => hlt.le ⟨q, hq, rfl⟩) fun he => ?_
    obtain ⟨b, hbB, hbn⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨q, rfl⟩ := hB hbB
    have : q ∈ B.comap SemidirectProduct.inl := hbB
    rw [← he] at this
    exact hbn ⟨q, this, rfl⟩
  have htop := (fd_isCoatom_centralizer_of_mem_rootClass hp).2 _ hlt'
  refine le_antisymm hB fun x hx => ?_
  obtain ⟨q, rfl⟩ := hx
  have : q ∈ B.comap SemidirectProduct.inl := by rw [htop]; trivial
  exact this

end CFSG.Monster.Existence
