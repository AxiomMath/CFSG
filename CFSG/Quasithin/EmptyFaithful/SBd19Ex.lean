module

public import CFSG.Quasithin.EmptyFaithful.SBd19Dc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23

public section

namespace CFSG.Quasithin.SBd19

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239.Covers

theorem m23NoDoubleCover_holds :
    M23NoDoubleCover := by
  intro X _ _ hX Z _ hZ h2 hspor
  obtain ⟨e⟩ := hspor
  let π : X →* M23g := (e.toMonoidHom).comp (QuotientGroup.mk' Z)
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' Z x) = 1 ↔ x ∈ Z
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hz : ∀ z, π z = 1 → z ∈ Subgroup.center X := fun z hz =>
    hZ (hker ▸ (MonoidHom.mem_ker.mpr hz))
  have hexp : ∀ z, π z = 1 → z * z = 1 := by
    intro z hz'
    have hzZ : z ∈ Z := hker ▸ (MonoidHom.mem_ker.mpr hz')
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hzZ⟩)
    rw [h2] at h
    have := congrArg Subtype.val h
    simpa [pow_two] using this
  have hbot := m23_cover_exp2 π hπ hz hexp hX.commutator_eq_top
  rw [hker] at hbot
  rw [hbot, Subgroup.card_bot] at h2
  omega

end CFSG.Quasithin.SBd19
