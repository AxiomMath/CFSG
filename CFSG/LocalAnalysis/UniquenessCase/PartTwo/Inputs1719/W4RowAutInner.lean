module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem exists_l_eq_conj_on_center_quotient {G : Type} [Group G] {L : Subgroup G}
    {S : Type*} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹)
    (α : MulAut ↥L) :
    ∃ l : ↥L, ∀ x : ↥L,
      QuotientGroup.mk (s := Subgroup.center ↥L) (α x) =
        QuotientGroup.mk (s := Subgroup.center ↥L) (l * x * l⁻¹) := by
  classical
  let qα : MulAut (↥L ⧸ Subgroup.center ↥L) :=
    ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
  let φ : S ≃* S := e.symm.trans (qα.trans e)
  obtain ⟨s, hs⟩ := hAut φ
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm s)
  refine ⟨l, fun x => ?_⟩
  have hqα_mk : qα (QuotientGroup.mk (s := Subgroup.center ↥L) x) =
      QuotientGroup.mk (s := Subgroup.center ↥L) (α x) :=
    ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α x
  apply e.injective
  calc e (QuotientGroup.mk (s := Subgroup.center ↥L) (α x))
      = e (qα (QuotientGroup.mk x)) := by rw [hqα_mk]
    _ = φ (e (QuotientGroup.mk x)) := by simp [φ, MulEquiv.trans_apply]
    _ = s * e (QuotientGroup.mk x) * s⁻¹ := hs _
    _ = e (QuotientGroup.mk l) * e (QuotientGroup.mk x) * (e (QuotientGroup.mk l))⁻¹ := by
        rw [hl, MulEquiv.apply_symm_apply]
    _ = e (QuotientGroup.mk (s := Subgroup.center ↥L) (l * x * l⁻¹)) := by simp

private theorem centralizes_of_eq_conj_on_center_quotient {G : Type} [Group G]
    {Y L : Subgroup G} {y : ↥Y} {α : MulAut ↥L} {l : ↥L} (hq : IsQuasisimple ↥L)
    (hα : ∀ x : ↥L, (α x : G) = (y : G) * (x : G) * (y : G)⁻¹)
    (hαq : ∀ x : ↥L,
      QuotientGroup.mk (s := Subgroup.center ↥L) (α x) =
        QuotientGroup.mk (s := Subgroup.center ↥L) (l * x * l⁻¹)) :
    ∀ x : ↥L, (l : G)⁻¹ * (y : G) * (x : G) =
      (x : G) * ((l : G)⁻¹ * (y : G)) := by
  classical
  let hPerf : Group.IsPerfect ↥L := hq.1
  let β : MulAut ↥L := (MulAut.conj l)⁻¹ * α
  have hβx : ∀ x : ↥L, β x = l⁻¹ * α x * l := by
    intro x
    dsimp only [β]
    rw [MulAut.mul_apply, MulAut.conj_inv_apply]
  have hβmk : ∀ x : ↥L,
      QuotientGroup.mk (s := Subgroup.center ↥L) (β x) =
        QuotientGroup.mk (s := Subgroup.center ↥L) x := by
    intro x
    rw [hβx x, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hαq x, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    group
  have hβcentral : ∀ x : ↥L, x⁻¹ * β x ∈ Subgroup.center ↥L :=
    fun x => (QuotientGroup.eq).mp (hβmk x).symm
  have hβ : β = 1 := by
    have hhom := ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      β.toMonoidHom hβcentral
    ext x
    simpa using congrArg (fun f : ↥L →* ↥L => f x) hhom
  have hβxG : ∀ x : ↥L, (l : G)⁻¹ * (α x : G) * (l : G) = (x : G) := by
    intro x
    have h1 : β x = x := by
      have h := congrArg (fun f : MulAut ↥L => f x) hβ
      simpa using h
    rw [hβx x] at h1
    simpa using congrArg (fun t : ↥L => (t : G)) h1
  intro x
  have hconj : (y : G) * (x : G) * (y : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹ := by
    rw [← hα x]
    calc (α x : G) = (l : G) * ((l : G)⁻¹ * (α x : G) * (l : G)) * (l : G)⁻¹ := by
          group
      _ = (l : G) * (x : G) * (l : G)⁻¹ := by rw [hβxG x]
  calc (l : G)⁻¹ * (y : G) * (x : G)
      = (l : G)⁻¹ * ((y : G) * (x : G) * (y : G)⁻¹) * (y : G) := by group
    _ = (l : G)⁻¹ * ((l : G) * (x : G) * (l : G)⁻¹) * (y : G) := by rw [hconj]
    _ = (x : G) * ((l : G)⁻¹ * (y : G)) := by group

private theorem exists_centralizing_of_forall_aut_inner {G : Type} [Group G] {Y L : Subgroup G}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hq : IsQuasisimple ↥L)
    {S : Type*} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) (y : ↥Y) :
    ∃ l : ↥L, ∀ x : ↥L, (l : G)⁻¹ * (y : G) * (x : G) =
      (x : G) * ((l : G)⁻¹ * (y : G)) := by
  classical
  let H : Subgroup ↥Y := L.subgroupOf Y
  let hHn : H.Normal := hLn
  let eH : ↥H ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  let α : MulAut ↥L := eH.symm.trans ((MulAut.conjNormal y).trans eH)
  have hα : ∀ x : ↥L, (α x : G) = (y : G) * (x : G) * (y : G)⁻¹ := by
    intro x
    dsimp only [α, eH]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
      Subgroup.subgroupOfEquivOfLe_apply_coe, MulAut.conjNormal_apply]
    have hx : ((Subgroup.subgroupOfEquivOfLe hLY).symm x : ↥Y) =
        ⟨(x : G), hLY x.2⟩ :=
      Subtype.ext (Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe hLY x)
    rw [hx]
    simp
  obtain ⟨l, hαq⟩ := exists_l_eq_conj_on_center_quotient e hAut α
  exact ⟨l, centralizes_of_eq_conj_on_center_quotient hq hα hαq⟩

private theorem mem_of_centralizes_fstar {G : Type} [Group G] [Finite G] {Y L : Subgroup G}
    (hLY : L ≤ Y) (hF : Fstar Y = L) {y : ↥Y} {l : ↥L}
    (hcent : ∀ x : ↥L, (l : G)⁻¹ * (y : G) * (x : G) =
      (x : G) * ((l : G)⁻¹ * (y : G))) :
    (y : G) ∈ L := by
  let lY : ↥Y := ⟨l, hLY l.2⟩
  let g : ↥Y := lY⁻¹ * y
  have hgG : (g : G) = (l : G)⁻¹ * (y : G) := by
    simp [g, lY]
  have hgC : g ∈ Subgroup.centralizer (genFittingFStar ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzL : (z : G) ∈ L := by
      have hz' : (z : G) ∈ Fstar Y := Subgroup.mem_map_of_mem Y.subtype hz
      simpa [hF] using hz'
    have hcomm := hcent ⟨(z : G), hzL⟩
    apply Subtype.ext
    simpa [hgG] using hcomm.symm
  have hgF : g ∈ genFittingFStar ↥Y :=
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le ↥Y hgC
  have hgL : (g : G) ∈ L := by
    have hg' : (g : G) ∈ Fstar Y := Subgroup.mem_map_of_mem Y.subtype hgF
    simpa [hF] using hg'
  have hlL : (lY : G) ∈ L := by simp [lY]
  have hy : (y : G) = (lY : G) * (g : G) := by
    have h1 : y = lY * g := by simp [g]
    simpa using congrArg (fun t : ↥Y => (t : G)) h1
  rw [hy]
  exact L.mul_mem hlL hgL

theorem eq_of_fstar_eq_of_autInner {G : Type} [Group G] [Finite G] {Y L : Subgroup G}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hq : IsQuasisimple ↥L)
    {S : Type*} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) : Y = L := by
  refine le_antisymm ?_ hLY
  intro y hy
  obtain ⟨l, hcent⟩ :=
    exists_centralizing_of_forall_aut_inner hLY hLn hq e hAut ⟨y, hy⟩
  simpa using mem_of_centralizes_fstar hLY hF hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
