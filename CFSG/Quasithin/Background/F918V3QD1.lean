module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem v3qd_realizesVia_autQuot {D : FFModel} {X : Subgroup (MulAut W)} {C U Z : Subgroup W}
    (hXC : X ≤ stabSub C) {π : D.Gam →* ↥X} (h : D.RealizesVia X U Z π) (hUC : U ⊓ C ≤ Z) :
    ∃ π' : D.Gam →* ↥(autQuot X C),
      D.RealizesVia (autQuot X C) (U.map (QuotientGroup.mk' C)) (Z.map (QuotientGroup.mk' C))
        π' := by
  obtain ⟨hπs, hZU, hkerr, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  let φ : ↥X →* ↥(autQuot X C) :=
    ((quotHom C).comp (Subgroup.inclusion hXC)).codRestrict (autQuot X C)
      (fun g => mem_autQuot.2 ⟨⟨(g : MulAut W), hXC g.2⟩, g.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hgX, rfl⟩ := mem_autQuot.1 hy
    exact ⟨⟨(g : MulAut W), hgX⟩, rfl⟩
  have hinv : ∀ S : Subgroup W, (∀ k : ↥X, ∀ u ∈ S, (k : MulAut W) u ∈ S) →
      ∀ k' : ↥(autQuot X C), ∀ u ∈ S.map (QuotientGroup.mk' C),
        (k' : MulAut (W ⧸ C)) u ∈ S.map (QuotientGroup.mk' C) := by
    rintro S hS ⟨k', hk'⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := mem_autQuot.1 hk'
    exact ⟨(g : MulAut W) w, hS ⟨(g : MulAut W), hgX⟩ w hw, rfl⟩
  let f : ↥U →* ↥(U.map (QuotientGroup.mk' C)) := (QuotientGroup.mk' C).subgroupMap U
  have hfs : Function.Surjective f := (QuotientGroup.mk' C).subgroupMap_surjective U
  have hfk : f.ker ≤ β.ker := by
    intro u hu
    have hu1 : (QuotientGroup.mk' C) (u : W) = 1 := congrArg Subtype.val hu
    exact (hβk u).2 (hUC ⟨u.2, (QuotientGroup.eq_one_iff _).1 hu1⟩)
  let β' := (MonoidHom.liftOfSurjective f hfs) ⟨β, hfk⟩
  have hβ'f : ∀ u, β' (f u) = β u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨β, hfk⟩ u
  refine ⟨φ.comp π, hφs.comp hπs, Subgroup.map_mono hZU, hkerr, hinv U hHU, hinv Z hHZ, hsec,
    hker, β', ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, rfl⟩ := hβs y
    exact ⟨f u, hβ'f u⟩
  · intro u'
    obtain ⟨u, rfl⟩ := hfs u'
    rw [hβ'f, hβk]
    constructor
    · intro hu
      exact ⟨u, hu, rfl⟩
    · rintro ⟨z, hz, hzu⟩
      have h1 : (z : W) * (u : W)⁻¹ ∈ C := (mk_eq_mk_iff (U := C) _ _).1 hzu
      have h2 : (z : W) * (u : W)⁻¹ ∈ U := U.mul_mem (hZU hz) (U.inv_mem u.2)
      have h3 : (z : W) * (u : W)⁻¹ ∈ Z := hUC ⟨h2, h1⟩
      have h4 : (u : W) = ((z : W) * (u : W)⁻¹)⁻¹ * z := by simp
      rw [h4]
      exact Z.mul_mem (Z.inv_mem h3) hz
  · intro γ u' m hu hm hβu
    obtain ⟨u, rfl⟩ := hfs u'
    rw [hβ'f] at hβu
    have hu₀ : ((π γ : ↥X) : MulAut W) (u : W) ∈ U := hHU (π γ) u u.2
    have key : (⟨_, hu⟩ : ↥(U.map (QuotientGroup.mk' C))) = f ⟨_, hu₀⟩ := Subtype.ext rfl
    rw [key, hβ'f]
    exact hβe γ u m hu₀ hm hβu

end CFSG.Quasithin
