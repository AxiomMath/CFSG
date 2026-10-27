module

public import CFSG.Quasithin.Vol2.Ch3T326E
public import CFSG.Quasithin.Background.F918M7

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative
open T325 (V₀_le_V V_le_VM M_le_NVM)
open CFSG.Quasithin.Vol2.Ch10.SecA (conjugate_conjugate conjugate_eq_self_iff)

section Basic

variable {G : Type} [Group G]

theorem conjugate_commutator (A B : Subgroup G) (g : G) :
    CFSG.conjugate ⁅A, B⁆ g = ⁅CFSG.conjugate A g, CFSG.conjugate B g⁆ := by
  unfold CFSG.conjugate
  rw [Subgroup.map_commutator]

theorem map_conjAct_subgroupOf {W X : Subgroup G} (hX : X ≤ W)
    (g : Subgroup.normalizer (W : Set G)) :
    (X.subgroupOf W).map (conjAct W g).toMonoidHom =
      (CFSG.conjugate X (g : G)⁻¹).subgroupOf W := by
  ext v
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, Setup.coe_conjAct_apply]
    exact Subgroup.mem_map.2 ⟨(u : G), hu, by simp [MulAut.conj_apply]⟩
  · intro hv
    obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.1 hv
    refine ⟨⟨x, hX hx⟩, hx, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom, Setup.coe_conjAct_apply, ← hxv]
    simp [MulAut.conj_apply]

end Basic

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

omit c in
theorem conjugate_VM (_c : Ctx T L V₀) {g : G}
    (hg : g ∈ Subgroup.normalizer (conjClosure L T : Set G)) :
    CFSG.conjugate (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) g =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  unfold CFSG.conjugate
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (M_le_NVM T (conjClosure L T) V₀ (Subgroup.inv_mem _ hg))

theorem conjugate_U {g : G} (hg : g ∈ Subgroup.normalizer (conjClosure L T : Set G)) :
    CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ g =
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)),
        CFSG.conjugate L g⁆ := by
  rw [conjugate_commutator, c.conjugate_VM hg]

theorem conjugate_eq_of (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    {s t : G} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) : CFSG.conjugate L t = CFSG.conjugate L s := by
  rcases Vol2.Ch10.SecA.conjugate_eq_or_of_fsu hA37 hA38 c.fsu c.not_le_normalizer hs hsn
      (c.T_le_M ht) with h | h
  · exact absurd (conjugate_eq_self_iff.mp h) htn
  · exact h

theorem twoSummands (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hdir : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
        CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
        CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t = ⊥) :
    TwoSummands (autOn (Subgroup.normalizer (conjClosure L T : Set G))
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      ((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      ((CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  set M := Subgroup.normalizer (conjClosure L T : Set G) with hM
  set VM := conjClosure (conjClosure V₀ T) M with hVM
  set U := ⁅VM, L⁆ with hU
  have hUVM : U ≤ VM := Subgroup.le_normalizer_iff_commutator_le_left.mp c.L_le_NVM
  have hUtVM : CFSG.conjugate U t ≤ VM :=
    le_of_le_of_eq (Subgroup.map_mono hUVM) (c.conjugate_VM (c.T_le_M ht))
  have key : ∀ m ∈ M, (CFSG.conjugate U m⁻¹ = U ∧
      CFSG.conjugate (CFSG.conjugate U t) m⁻¹ = CFSG.conjugate U t) ∨
      (CFSG.conjugate U m⁻¹ = CFSG.conjugate U t ∧
      CFSG.conjugate (CFSG.conjugate U t) m⁻¹ = U) := by
    intro m hm
    have hm' : m⁻¹ ∈ M := M.inv_mem hm
    have htm : t * m⁻¹ ∈ M := M.mul_mem (c.T_le_M ht) hm'
    rw [conjugate_conjugate, c.conjugate_U hm', c.conjugate_U htm, c.conjugate_U (c.T_le_M ht)]
    have hne : CFSG.conjugate L (t * m⁻¹) ≠ CFSG.conjugate L m⁻¹ := by
      intro h
      rw [← conjugate_conjugate] at h
      have h2 := congrArg (fun Y => CFSG.conjugate Y m) h
      simp only [conjugate_conjugate, inv_mul_cancel, inv_mul_cancel_right,
        Vol2.Ch10.SecA.conjugate_one] at h2
      exact Vol2.Ch10.SecA.ne_conjugate htn h2.symm
    rcases Vol2.Ch10.SecA.conjugate_eq_or_of_fsu hA37 hA38 c.fsu c.not_le_normalizer ht htn hm'
      with h1 | h1 <;>
    rcases Vol2.Ch10.SecA.conjugate_eq_or_of_fsu hA37 hA38 c.fsu c.not_le_normalizer ht htn htm
      with h2 | h2
    · exact absurd (h2.trans h1.symm) hne
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
    · exact absurd (h2.trans h1.symm) hne
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hx hy
    have : (x : G) ∈ U ⊓ CFSG.conjugate U t := ⟨hx, hy⟩
    rw [hdir.2, Subgroup.mem_bot] at this
    exact Subtype.ext this
  · rw [← Subgroup.subgroupOf_sup hUVM hUtVM, hdir.1, Subgroup.subgroupOf_self]
  · intro g hg
    obtain ⟨m, hmM, rfl⟩ := Setup.mem_autOn_iff.1 hg
    rw [map_conjAct_subgroupOf hUVM, map_conjAct_subgroupOf hUtVM]
    rcases key m hmM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

theorem qhatStar_acts_of_direct (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hdir : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
        CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
        CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t = ⊥)
    (hrk : 2 < rk ↥((⁅conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))) :
    ∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
        ((a u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
          ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ := by
  intro A hA a ha u hu
  have hexp : ∀ w : ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using c.elemVM.2 w w.2)
  have hle := d29_six hexp (c.twoSummands hA37 hA38 ht htn hdir) hrk
    (Setup.pCoreOf_autOn_eq_bot c.redVM) A hA
  exact ((hle ha) u).2 hu

end Ctx


end CFSG.Quasithin.H13.T326
