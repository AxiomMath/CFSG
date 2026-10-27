module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Img
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {R Y T L : Subgroup (LGL 2 V)}

structure SimpleCore (R L : Subgroup (LGL 2 V)) : Prop where
  le : L ≤ R
  normal : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L
  simple : IsSimpleGroup ↥L
  nonab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a
  cent : ∀ y ∈ R, (∀ l ∈ L, y * l = l * y) → y = 1

theorem Br2OneComp.core (h : Br2OneComp Y T L) : SimpleCore Y L :=
  ⟨h.le, h.normal, h.simple, h.nonab, h.cent⟩

@[expose] def psiOf (R L : Subgroup (LGL 2 V)) (hn : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L) :
    ↥R →* MulAut ↥L where
  toFun r :=
    { toFun := fun l => ⟨(r : LGL 2 V) * l * (r : LGL 2 V)⁻¹, hn r r.2 l l.2⟩
      invFun := fun l => ⟨(r : LGL 2 V)⁻¹ * l * (r : LGL 2 V), by
        simpa using hn (r : LGL 2 V)⁻¹ (R.inv_mem r.2) l l.2⟩
      left_inv := fun l => by ext; simp [mul_assoc]
      right_inv := fun l => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]

theorem psiOf_apply (hn : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (r : ↥R) (l : ↥L) :
    ((psiOf R L hn r l : ↥L) : LGL 2 V) = (r : LGL 2 V) * l * (r : LGL 2 V)⁻¹ :=
  rfl

theorem psiOf_injective (h : SimpleCore R L) : Function.Injective (psiOf R L h.normal) := by
  intro r₁ r₂ hr
  have h1 : psiOf R L h.normal (r₁⁻¹ * r₂) = 1 := by
    rw [map_mul, map_inv, hr, inv_mul_cancel]
  have h2 : ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) = 1 := by
    refine h.cent ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) (r₁⁻¹ * r₂).2 (fun l hl => ?_)
    have h3 : ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) * l * ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V)⁻¹ = l := by
      have h4 : ((psiOf R L h.normal (r₁⁻¹ * r₂)) ⟨l, hl⟩ : LGL 2 V)
          = ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) * l
            * ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V)⁻¹ :=
        psiOf_apply h.normal (r₁⁻¹ * r₂) ⟨l, hl⟩
      have h5 := congrArg (fun f : MulAut ↥L => (f ⟨l, hl⟩ : LGL 2 V)) h1
      rw [h4] at h5
      simpa using h5
    calc ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) * l
        = ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) * l * ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V)⁻¹
            * ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) := by group
      _ = l * ((r₁⁻¹ * r₂ : ↥R) : LGL 2 V) := by rw [h3]
  have hrr : r₁⁻¹ * r₂ = 1 := Subtype.coe_injective h2
  exact inv_mul_eq_one.mp hrr

theorem psiOf_eq_conj (h : SimpleCore R L) {l : LGL 2 V} (hl : l ∈ L) :
    psiOf R L h.normal ⟨l, h.le hl⟩ = MulAut.conj (⟨l, hl⟩ : ↥L) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  ext v
  simp [psiOf_apply, MulAut.conj_apply]

theorem imgOf_psiOf_L (h : SimpleCore R L) :
    imgOf (psiOf R L h.normal) L = innAutOf ↥L := by
  apply le_antisymm
  · intro x hx
    rw [imgOf, Subgroup.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hr
    rw [innAutOf, MonoidHom.mem_range]
    exact ⟨⟨(r : LGL 2 V), hr⟩, (psiOf_eq_conj h hr).symm⟩
  · intro x hx
    rw [innAutOf, MonoidHom.mem_range] at hx
    obtain ⟨l, rfl⟩ := hx
    rw [imgOf, Subgroup.mem_map]
    exact ⟨⟨(l : LGL 2 V), h.le l.2⟩, by rw [Subgroup.mem_subgroupOf]; exact l.2,
      psiOf_eq_conj h l.2⟩

theorem exists_psiOf_eq_of_mem_innAutOf (h : SimpleCore R L) {g : MulAut ↥L}
    (hg : g ∈ innAutOf ↥L) : ∃ (l : LGL 2 V) (hl : l ∈ L), psiOf R L h.normal ⟨l, h.le hl⟩ = g := by
  rw [← imgOf_psiOf_L h] at hg
  rw [imgOf, Subgroup.mem_map] at hg
  obtain ⟨r, hr, hrg⟩ := hg
  rw [Subgroup.mem_subgroupOf] at hr
  exact ⟨(r : LGL 2 V), hr, by simpa using hrg⟩

theorem psiOf_conj_mem_innAutOf (h : SimpleCore R L) (r : ↥R) {x : MulAut ↥L}
    (hx : x ∈ innAutOf ↥L) :
    psiOf R L h.normal r * x * (psiOf R L h.normal r)⁻¹ ∈ innAutOf ↥L := by
  rw [innAutOf, MonoidHom.mem_range] at hx
  obtain ⟨l, rfl⟩ := hx
  rw [innAutOf, MonoidHom.mem_range]
  refine ⟨psiOf R L h.normal r l, ?_⟩
  ext a
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv]
  rw [MulEquiv.apply_symm_apply]

theorem psiOf_dynkin (h : SimpleCore R L) {t : LGL 2 V} (ht : t ∈ R)
    (hd : ActsOnDynkinMod ⊥ L t) :
    ActsOnDynkinMod ⊥ (innAutOf ↥L) (psiOf R L h.normal ⟨t, ht⟩) := by
  have h' := imgOf_actsOnDynkin (ψ := psiOf R L h.normal) (psiOf_injective h) h.le ht hd
  rwa [imgOf_psiOf_L h] at h'

theorem SimpleCore.not_isPGroup (h : SimpleCore R L) : ¬ IsPGroup 2 ↥R := by
  intro hR
  have hL2 : IsPGroup 2 ↥L :=
    hR.of_injective (Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le)
  haveI : Finite ↥L := Subtype.finite
  haveI : IsSimpleGroup ↥L := h.simple
  haveI : Group.IsNilpotent ↥L := hL2.isNilpotent
  have hcomm : ∀ a b : ↥L, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable ↥L)
  obtain ⟨a, ha, b, hb, hab⟩ := h.nonab
  exact hab (by simpa using hcomm ⟨a, ha⟩ ⟨b, hb⟩)

theorem SimpleCore.ne_of_isSylowIn (h : SimpleCore R L) {S : Subgroup (LGL 2 V)}
    (hS : IsSylowIn 2 S R) : S ≠ R := by
  intro hSR
  exact h.not_isPGroup (hSR ▸ hS.isPGroup)

theorem w183b2_normalizer_sylow_ne (hL : Br2OneComp Y T L) (hT : IsSylowIn 2 T Y) :
    ¬ Y ≤ Subgroup.normalizer ((T ⊓ L : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  intro hN
  have hLnorm : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hL.le).mpr (fun h k hh hk => hL.normal k hk h hh)
  have hSylowTL : IsSylowIn 2 (T ⊓ L) L := hT.inf_normal hL.le hLnorm
  have hnormTL : ((T ⊓ L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr (le_trans hL.le hN)
  obtain ⟨τ, hτT, hdyn⟩ := hL.dynkin
  unfold ActsOnDynkinMod at hdyn
  obtain ⟨-, P, hMP, -⟩ := hdyn
  unfold IsMaxParabolicMod at hMP
  obtain ⟨-, hPL, -, S, -, hSL, hpow, hodd, hSupP⟩ := hMP
  have hSpgroup : IsPGroup 2 S := by
    intro s
    obtain ⟨k, hk⟩ := hpow s s.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hSylowS : IsSylowIn 2 S L := ⟨hSL, hSpgroup, hodd⟩
  haveI : Finite ↥L := Subtype.finite
  haveI : Finite (Sylow 2 ↥L) := Sylow.finite_of_finiteIndex hSylowTL.toSylow
  have hP₁norm : hSylowTL.toSylow.Normal := by
    rw [IsSylowIn.coe_toSylow]
    exact hnormTL
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := ↥L) hSylowTL.toSylow hSylowS.toSylow
  have hEqSylow : hSylowS.toSylow = hSylowTL.toSylow := by
    rw [← hg, Sylow.smul_eq_of_normal (g := g) (P := hSylowTL.toSylow) (h := hP₁norm)]
  have hsub : S.subgroupOf L = (T ⊓ L).subgroupOf L := by
    have := congrArg (fun Q : Sylow 2 ↥L => (Q : Subgroup ↥L)) hEqSylow
    simpa only [IsSylowIn.coe_toSylow] using this
  have hSnorm : (S.subgroupOf L).Normal := by
    rw [hsub]
    exact hnormTL
  haveI : (S.subgroupOf L).Normal := hSnorm
  have hLSnorm : L ≤ Subgroup.normalizer (S : Set (LGL 2 V)) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hSL
  have hLP : L ≤ P := le_trans (le_inf le_rfl hLSnorm) hSupP
  exact (not_le_of_gt hPL) hLP

end CFSG.LocalAnalysis.WeakClosure81

end
