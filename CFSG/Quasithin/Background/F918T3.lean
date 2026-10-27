module

public import CFSG.Quasithin.Background.F918N0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Z35Lemmas

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X}

theorem z35_conj_mem (h : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) {s : MulAut X} (hs : s ∈ Tb)
    {l : MulAut X} (hl : l ∈ Lb) : s * l * s⁻¹ ∈ Lb := by
  have hn := le_normalizer_conjClosure Lb Tb hs
  rw [← h.Mp_eq, hML] at hn
  exact (Subgroup.mem_normalizer_iff.mp hn l).mp hl

theorem z35_le_stabSub (h : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) : Lb ≤ stabSub V₁ := by
  subst hML
  intro g hg u
  refine ⟨fun hu => ?_, fun hu => h.irr.1 ⟨g, hg⟩ u hu⟩
  have h1 : g⁻¹ (g u) ∈ V₁ := h.irr.1 ⟨g⁻¹, Mb.inv_mem hg⟩ (g u) hu
  rwa [MulAut.inv_apply_self] at h1

theorem z35_central_of_trivial (h : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) {k : MulAut X} (hk : k ∈ Lb)
    (hkV : ∀ v ∈ V₁, k v = v) : ∀ x ∈ Lb, k * x = x * k := by
  have hLV := z35_le_stabSub h hML
  let K : Subgroup ↥Lb := (centSub V₁).subgroupOf Lb
  have hKn : K.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, mem_centSub] at hn ⊢
    intro v hv
    have hv' : (g : MulAut X)⁻¹ v ∈ V₁ := (hLV (Lb.inv_mem g.2) v).2 hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
    rw [hn _ hv', MulAut.apply_inv_self]⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple h.quasi K with hK | hK
  · intro x hx
    have hkc : (⟨k, hk⟩ : ↥Lb) ∈ Subgroup.center ↥Lb :=
      hK (Subgroup.mem_subgroupOf.mpr (mem_centSub.mpr hkV))
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hkc ⟨x, hx⟩)).symm
  ·
    exfalso
    obtain ⟨l, hl, v, hv, hlv⟩ := h.nontriv 1 Tb.one_mem
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
    have hmem : (⟨l', hl'⟩ : ↥Lb) ∈ K := by
      rw [hK]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, mem_centSub] at hmem
    apply hlv
    simpa [MulAut.conj_apply] using hmem v hv

theorem z35_centralizes (h : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) {a l : MulAut X} (ha : a ∈ Tb)
    (hl : l ∈ Lb) (hagree : ∀ v ∈ V₁, a v = l v) : ∀ x ∈ Lb, (l⁻¹ * a) * x = x * (l⁻¹ * a) := by
  have hLV := z35_le_stabSub h hML
  set z := l⁻¹ * a with hz
  have hzV : ∀ v ∈ V₁, z v = v := fun v hv => by
    rw [hz, MulAut.mul_apply, hagree v hv, MulAut.inv_apply_self]
  have hzV' : ∀ v ∈ V₁, z⁻¹ v = v := fun v hv => by
    calc z⁻¹ v = z⁻¹ (z v) := by rw [hzV v hv]
      _ = v := by rw [MulAut.inv_apply_self]
  have hzL : ∀ x ∈ Lb, z * x * z⁻¹ ∈ Lb := fun x hx => by
    have e : z * x * z⁻¹ = l⁻¹ * (a * x * a⁻¹) * l := by
      rw [hz]
      group
    rw [e]
    exact Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) (z35_conj_mem h hML ha hx)) hl
  have hcL : ∀ x ∈ Lb, z * x * z⁻¹ * x⁻¹ ∈ Lb := fun x hx =>
    Lb.mul_mem (hzL x hx) (Lb.inv_mem hx)
  have hcV : ∀ x ∈ Lb, ∀ v ∈ V₁, (z * x * z⁻¹ * x⁻¹) v = v := fun x hx v hv => by
    have hxv : x⁻¹ v ∈ V₁ := (hLV (Lb.inv_mem hx) v).2 hv
    simp only [MulAut.mul_apply]
    rw [hzV' _ hxv, MulAut.apply_inv_self, hzV v hv]
  have hcZ : ∀ x ∈ Lb, ∀ y ∈ Lb, (z * x * z⁻¹ * x⁻¹) * y = y * (z * x * z⁻¹ * x⁻¹) :=
    fun x hx => z35_central_of_trivial h hML (hcL x hx) (hcV x hx)
  let φ : ↥Lb →* ↥(Subgroup.center ↥Lb) :=
    { toFun := fun x => ⟨⟨z * x * z⁻¹ * (x : MulAut X)⁻¹, hcL x x.2⟩,
        Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcZ x x.2 y y.2).symm⟩
      map_one' := Subtype.ext <| Subtype.ext <| by
        show z * 1 * z⁻¹ * (1 : MulAut X)⁻¹ = 1
        group
      map_mul' := fun x y => Subtype.ext <| Subtype.ext <| by
        show z * ((x : MulAut X) * y) * z⁻¹ * ((x : MulAut X) * y)⁻¹ =
          z * x * z⁻¹ * (x : MulAut X)⁻¹ * (z * y * z⁻¹ * (y : MulAut X)⁻¹)
        have hy := hcZ y y.2 (x : MulAut X)⁻¹ (Lb.inv_mem x.2)
        calc z * ((x : MulAut X) * y) * z⁻¹ * ((x : MulAut X) * y)⁻¹
            = z * x * z⁻¹ * ((z * y * z⁻¹ * (y : MulAut X)⁻¹) * (x : MulAut X)⁻¹) := by group
          _ = z * x * z⁻¹ * ((x : MulAut X)⁻¹ * (z * y * z⁻¹ * (y : MulAut X)⁻¹)) := by rw [hy]
          _ = z * x * z⁻¹ * (x : MulAut X)⁻¹ * (z * y * z⁻¹ * (y : MulAut X)⁻¹) := by group }
  intro x hx
  have hφ : φ ⟨x, hx⟩ = 1 := by
    have hmem : (⟨x, hx⟩ : ↥Lb) ∈ commutator ↥Lb := by
      rw [Group.isPerfect_def.mp h.quasi.1]
      exact Subgroup.mem_top _
    exact Abelianization.commutator_subset_ker φ hmem
  have hc1 : z * x * z⁻¹ * x⁻¹ = 1 :=
    congrArg (fun w : ↥(Subgroup.center ↥Lb) => ((w : ↥Lb) : MulAut X)) hφ
  calc z * x = (z * x * z⁻¹ * x⁻¹) * (x * z) := by group
    _ = x * z := by rw [hc1, one_mul]

end Z35Lemmas

end CFSG.Quasithin
